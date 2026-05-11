import CatRw.Attributes
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatIso
import Mathlib.Tactic
import Lean.Elab.Tactic

open CategoryTheory Limits
open Lean Meta Elab Tactic
open Parser.Tactic (optConfig location getConfigItems rwRuleSeq)

namespace CatRw

initialize registerTraceClass `CatRw

/--
Information about a binary relation supported by `cat_rw`.
Contains names of lemmas for basic properties.
-/
structure RelInfo where
  /-- The name of the relation (e.g., ``CategoryTheory.Iso``). -/
  name : Name
  /-- The name of the reflexivity lemma (e.g., ``CategoryTheory.Iso.refl``). -/
  refl : Name
  /-- The name of the symmetry lemma (e.g., ``CategoryTheory.Iso.symm``). -/
  symm : Option Name
  /-- The name of the transitivity lemma (e.g., ``CategoryTheory.Iso.trans``). -/
  trans : Option Name
  deriving Inhabited, Repr

namespace RelInfo

/-- Creates a reflexivity proof for the relation. -/
def mkRefl (info : RelInfo) (e : Expr) : MetaM Expr :=
  mkAppM info.refl #[e]

/-- Applies symmetry to a proof, if supported. Performs basic optimizations. -/
def applySymm (info : RelInfo) (p : Expr) : MetaM Expr := do
  let some symmName := info.symm | return p
  let p ← instantiateMVars p
  -- Optimization: symm (symm p) -> p
  if p.isAppOf symmName then
    return p.appArg!
  -- Optimization: symm refl -> refl
  if p.isAppOf info.refl then
    return p
  mkAppM symmName #[p]

/-- Applies transitivity to two proofs, if supported. Performs basic optimizations. -/
def applyTrans (info : RelInfo) (p1 p2 : Expr) : MetaM Expr := do
  let some transName := info.trans | throwError "Relation {info.name} is not transitive"
  let p1 ← instantiateMVars p1
  let p2 ← instantiateMVars p2
  -- Optimization: refl ≫ p -> p, p ≫ refl -> p
  if p1.isAppOf info.refl then return p2
  if p2.isAppOf info.refl then return p1
  mkAppM transName #[p1, p2]

/-- Checks if an expression is a reflexivity proof for this relation. -/
def isRefl (info : RelInfo) (p : Expr) : MetaM Bool := do
  let p ← instantiateMVars p
  return p.isAppOf info.refl

end RelInfo

private def initialRelMap : NameMap RelInfo :=
  let m : NameMap RelInfo := {}
  let m := m.insert ``CategoryTheory.Iso (RelInfo.mk ``CategoryTheory.Iso ``CategoryTheory.Iso.refl
    (some ``CategoryTheory.Iso.symm) (some ``CategoryTheory.Iso.trans))
  let m := m.insert ``Eq (RelInfo.mk ``Eq ``Eq.refl (some ``Eq.symm) (some ``Eq.trans))
  let m := m.insert ``Iff (RelInfo.mk ``Iff ``Iff.refl (some ``Iff.symm) (some ``Iff.trans))
  m

/--
A register for relations. Used to determine which relations the tactic can reason about.
-/
initialize relExt : SimpleScopedEnvExtension RelInfo (NameMap RelInfo) ←
  registerSimpleScopedEnvExtension {
    name := `cat_rw_rel_ext
    initial := initialRelMap
    addEntry := fun map rel => map.insert rel.name rel
  }

/-- Registers a new binary relation for use with `cat_rw`. -/
def registerRel (info : RelInfo) : CoreM Unit := do
  modifyEnv fun env => relExt.addEntry env info

/--
A `Rule` represents a single rewrite rule (e.g., an isomorphism or equality).
-/
structure RuleV2 where
  /-- The raw expression of the rule (e.g., a proof of `X ≅ Y`). -/
  proof : Expr
  /-- The relation of the rule (e.g., `CategoryTheory.Iso`). -/
  rel : Name
  /-- The LHS of the rule. -/
  lhs : Expr
  /-- The RHS of the rule. -/
  rhs : Expr

/-- Result of a generalized rewrite. -/
structure Rewrote where
  /-- The new expression. -/
  expr' : Expr
  /-- The proof of `r expr expr'`. -/
  proof : Expr

/-- Configuration for `cat_rw`. -/
structure Config where
  occs : Occurrences := .pos [1]
  deriving Inhabited

/-- State for the `grw` algorithm. -/
structure StateV2 where
  occCount : Nat := 0

/-- Context for the `grw` algorithm. -/
structure ContextV2 where
  rule : RuleV2
  isoMakerLemmas : Array Name
  relations : NameMap RelInfo
  config : Config
  occCountRef : IO.Ref StateV2
  depth : Nat := 0

abbrev CatRwM2 := ReaderT ContextV2 MetaM

instance : MonadBacktrack Meta.SavedState CatRwM2 where
  saveState := liftM (saveState : MetaM _)
  restoreState s := liftM (restoreState s : MetaM _)

/--
Extracts the relation and endpoints from a type.
Supports `X ≅ Y`, `X = Y`, `P ↔ Q` and any registered binary relations.
Assumes the relation name is registered and the endpoints are the last two arguments.
-/
def getRelInfo? (relations : NameMap RelInfo) (type : Expr) :
    MetaM (Option (Name × Expr × Expr)) := do
  let type ← whnf type
  let rel := type.getAppFn.constName?
  let some r := rel | return none
  if relations.contains r && type.getAppNumArgs >= 2 then
    let args := type.getAppArgs
    return some (r, args[args.size - 2]!, args[args.size - 1]!)
  return none

/-- Instantiates a lemma with fresh level metavariables and performs a telescope. -/
private def withLemma (lemmaName : Name) (k : Array Expr → Expr → CatRwM2 (Option α)) :
    CatRwM2 (Option α) := do
  let info ← getConstInfo lemmaName
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let type := info.instantiateTypeLevelParams levels
  let (args, _, resultType) ← forallMetaTelescope type
  k args resultType

/-- Attempts to resolve all instance metavariables within an expression. -/
private def solveInstances (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let mvars ← getMVars e
  for mvarId in mvars do
    if !(← mvarId.isAssigned) then
      let type ← instantiateMVars (← mvarId.getType)
      if (← isClass? type).isSome then
        try
          let inst ← synthInstance type
          mvarId.assign inst
        catch _ => pure ()
  instantiateMVars e

/-- Finalizes the arguments for a lemma by synthesizing instances and solving metavariables. -/
private def finalizeLemmaArgs (args : Array Expr) : MetaM (Array (Option Expr)) := do
  for arg in args do
    let mvarId := arg.mvarId!
    if !(← mvarId.isAssigned) then
      let argType ← instantiateMVars (← mvarId.getType)
      if (← isClass? argType).isSome then
        try mvarId.assign (← synthInstance argType) catch _ => pure ()
  args.mapM fun arg => do
    let argInst ← solveInstances arg
    if argInst.hasExprMVar then return none else return some argInst

/-- Tries to match the user-provided rule directly against the expression. -/
private def tryMatchRule (r_out : Name) (expr : Expr) : CatRwM2 (Option Rewrote) := do
  let ctx ← read
  if r_out == ctx.rule.rel then
    if ← withReducible (isDefEq ctx.rule.lhs expr) then
      let s ← ctx.occCountRef.get
      ctx.occCountRef.set { s with occCount := s.occCount + 1 }
      let s ← ctx.occCountRef.get
      if ctx.config.occs.contains s.occCount then
        let proof ← instantiateMVars (← solveInstances ctx.rule.proof)
        let rhs ← instantiateMVars (← solveInstances ctx.rule.rhs)
        trace[CatRw] m!"matched rule: {ctx.rule.lhs} -> {rhs} (occ {s.occCount})"
        return some { expr' := rhs, proof }
      else
        trace[CatRw] m!"matched rule but skipped (occ {s.occCount})"
  return none

mutual
/--
The generalized rewrite function.
`grw r_out expr` returns a proof of `r_out expr expr'`.
Traverses the expression tree and applies rules or lifting lemmas.
-/
partial def grw (r_out : Name) (expr : Expr) : CatRwM2 (Option Rewrote) := do
  let expr ← instantiateMVars expr
  if expr.isMVar then return none
  withTraceNode `CatRw (fun _ => do
    return m!"grw {r_out} on {expr}") do
    let ctx ← read
    if ctx.depth > 20 then return none
    -- 1. Try if rule matches expr
    if let some res ← tryMatchRule r_out expr then return some res
    -- 2. Try lifting lemmas
    for lemmaName in ctx.isoMakerLemmas do
      let state ← saveState
      try
        if let some res ← tryApplyLemma lemmaName r_out expr then return some res
        restoreState state
      catch _ => restoreState state
    return none

/-- Attempts to apply a specific lifting lemma to the expression. -/
private partial def tryApplyLemma (lemmaName : Name) (r_out : Name) (expr : Expr) :
    CatRwM2 (Option Rewrote) := do
  let ctx ← read
  withLemma lemmaName fun args resultType => do
    let some (r_res, lhs, rhs) ← getRelInfo? ctx.relations resultType | return none
    if r_res != r_out then return none
    let relInfo := ctx.relations.find? r_res |>.get!

    let mut matchedLhs := ← withReducible (isDefEq lhs expr)
    let mut matchedRhs := false
    if !matchedLhs && relInfo.symm.isSome then
      matchedRhs := ← withReducible (isDefEq rhs expr)

    if !matchedLhs && !matchedRhs then return none

    let mut rewrote := false
    for arg in args do
      if ← processArg arg then rewrote := true

    if rewrote then
      let optArgs ← finalizeLemmaArgs args
      let mut proof ← mkAppOptM lemmaName optArgs
      let rhsFinal := if matchedLhs then rhs else lhs
      if matchedRhs then
        proof ← relInfo.applySymm proof
      let rhsInst ← instantiateMVars (← solveInstances rhsFinal)
      let proofInst ← instantiateMVars proof
      trace[CatRw] m!"applied {lemmaName}: {expr} -> {rhsInst}"
      return some { expr' := rhsInst, proof := proofInst }
    return none

/-- Processes a single argument of a lifting lemma, attempting to rewrite it. -/
private partial def processArg (arg : Expr) : CatRwM2 Bool := do
  let ctx ← read
  let argType ← whnf (← instantiateMVars (← inferType arg))
  let some (r_arg, argLhs, argRhs) ← getRelInfo? ctx.relations argType | return false
  let relInfoArg := ctx.relations.find? r_arg |>.get!

  let nextCtx := { ctx with depth := ctx.depth + 1 }
  let tryRw (e : Expr) (useSymm : Bool) : CatRwM2 Bool := do
    if let some res ← withReader (fun _ => nextCtx) (grw r_arg e) then
      let mut proof := res.proof
      if useSymm then proof ← relInfoArg.applySymm proof
      if ← isDefEq argType (← inferType proof) then
        arg.mvarId!.assign proof
        return true
    return false

  if ← tryRw argLhs false then return true
  if relInfoArg.symm.isSome then
    if ← tryRw argRhs true then return true

  -- Fallback: assign reflexivity
  let reflProof ← relInfoArg.mkRefl argLhs
  if ← isDefEq argType (← inferType reflProof) then
    arg.mvarId!.assign reflProof
  return false
end

/-- Performs a rewrite on both sides of a relation. -/
private def rewriteTarget (r : Name) (lhs rhs : Expr) :
    CatRwM2 (Expr × Expr × Option Expr × Option Expr × Bool) := do
  let ctx ← read
  let relInfo := (ctx.relations.find? r).get!
  let mut lhsrw := none
  -- We only rewrite LHS if the relation is symmetric, as we'll need to use symm on the proof.
  if relInfo.symm.isSome then
    lhsrw ← grw r lhs
  let rhsrw ← grw r rhs
  let newLhs := if let some l := lhsrw then l.expr' else lhs
  let newRhs := if let some r := rhsrw then r.expr' else rhs
  let rewrote := lhsrw.isSome || rhsrw.isSome
  return (newLhs, newRhs, lhsrw.map (·.proof), rhsrw.map (·.proof), rewrote)

/-- Dispatches the rewrite based on whether it's the goal or a hypothesis. -/
def evalRewrite (goal : MVarId) (fvarId? : Option FVarId) :
    CatRwM2 (Array MVarId × Option FVarId × Bool) := do
  let target ← if let some fvarId := fvarId? then fvarId.getType else goal.getType
  let target ← instantiateMVars target
  let loc := fvarId?.map mkFVar |>.getD (mkConst ``none)
  withTraceNode `CatRw (fun _ => return m!"evalRewrite at {loc}: {target}") do
    let ctx ← read
    if let some (r, lhs, rhs) ← getRelInfo? ctx.relations target then
      let relInfo := ctx.relations.find? r |>.get!
      let (newLhs, newRhs, lp?, rp?, rewrote) ← rewriteTarget r lhs rhs
      if !rewrote then return (#[goal], fvarId?, false)
      if let some fvarId := fvarId? then
        -- Hypothesis case: h : lhs ≅ rhs
        -- We replace it with: lp.symm ≫ h ≫ rp : newLhs ≅ newRhs
        let mut proof := mkFVar fvarId
        if let some rp := rp? then proof ← relInfo.applyTrans proof rp
        if let some lp := lp? then
          let lp_symm ← relInfo.applySymm lp
          proof ← relInfo.applyTrans lp_symm proof
        let newTarget ← mkAppM r #[newLhs, newRhs]
        let res ← goal.replace fvarId proof newTarget
        return (#[res.mvarId], some res.fvarId, true)
      else
        -- Goal case: ⊢ lhs ≅ rhs
        -- We replace it with: ⊢ newLhs ≅ newRhs
        -- The proof for the old goal is: lp ≫ new_goal ≫ rp.symm
        if ← withReducible (isDefEq newLhs newRhs) then
          let mut proof ← relInfo.mkRefl newLhs
          if let some lp := lp? then proof ← relInfo.applyTrans lp proof
          if let some rp := rp? then
            let rp_symm ← relInfo.applySymm rp
            proof ← relInfo.applyTrans proof rp_symm
          goal.assign (← solveInstances proof)
          return (#[], none, true)
        else
          let newTarget ← mkAppM r #[newLhs, newRhs]
          let newGoal ← mkFreshExprMVar (← instantiateMVars newTarget)
          let mut proof := newGoal
          if let some rp := rp? then
            let rp_symm ← relInfo.applySymm rp
            proof ← relInfo.applyTrans proof rp_symm
          if let some lp := lp? then
            proof ← relInfo.applyTrans lp proof
          goal.assign (← solveInstances proof)
          return (#[newGoal.mvarId!], none, true)
    else
      -- Prop case: Goal ⊢ P or Hyp h : P. We use Iff to transform.
      let r_iff := ``Iff
      let relInfo := ctx.relations.find? r_iff |>.get!
      if let some res ← grw r_iff target then
        if ← relInfo.isRefl res.proof then return (#[goal], fvarId?, false)
        if let some fvarId := fvarId? then
          -- Hyp case: h : P, res.proof : P ↔ Q. New hyp: res.proof.mp h : Q
          let newProof ← mkAppM ``Iff.mp #[res.proof, mkFVar fvarId]
          let res ← goal.replace fvarId newProof res.expr'
          return (#[res.mvarId], some res.fvarId, true)
        else
          -- Goal case: ⊢ P, res.proof : P ↔ Q. New goal: ⊢ Q
          if ← withReducible (isDefEq (← instantiateMVars res.expr') (mkConst ``True)) then
            let proof ← mkAppM ``Iff.mpr #[res.proof, mkConst ``True.intro]
            goal.assign (← solveInstances proof)
            return (#[], none, true)
          let newGoal ← mkFreshExprMVar (← instantiateMVars res.expr')
          let proof ← mkAppM ``Iff.mpr #[res.proof, newGoal]
          goal.assign (← solveInstances proof)
          return (#[newGoal.mvarId!], none, true)
      return (#[goal], fvarId?, false)

/-- Parses a user-provided rewrite rule. -/
private def parseRuleV2 (stx : Syntax) : TacticM RuleV2 := do
  let raw ← Term.elabTerm stx[1]! none
  let rawType ← inferType raw
  let (args, _, _) ← forallMetaTelescopeReducing rawType
  let proof := mkAppN raw args
  let type ← inferType proof
  let env ← getEnv
  let relations := relExt.getState env
  let some (rel, lhs, rhs) ← getRelInfo? relations type
    | throwError "Rule must be a binary relation: {type}"
  if stx[0]!.isNone then
    -- Forward rewrite: lhs -> rhs
    return { proof, rel, lhs, rhs }
  else
    -- Backward rewrite: rhs -> lhs
    let relInfo := (relations.find? rel).get!
    let some symm := relInfo.symm | throwError "Relation {rel} is not symmetric"
    let symmProof ← mkAppM symm #[proof]
    let newLhs ← instantiateMVars rhs
    let newRhs ← instantiateMVars lhs
    return { proof := symmProof, rel, lhs := newLhs, rhs := newRhs }

declare_config_elab elabConfig Config

/-- The main entry point for the `cat_rw` tactic. -/
def evalCatRwV2 (stx : Syntax) (rulesStx : TSyntax `Lean.Parser.Tactic.rwRuleSeq)
    (loc : Location) (config : Config) : TacticM Unit := do
  let lbrak := rulesStx.raw[0]!
  let rulesAndSeps := rulesStx.raw[1]!.getArgs
  let numRules := (rulesAndSeps.size + 1) / 2
  withTacticInfoContext (mkNullNode #[stx[0]!, lbrak]) (pure ())
  let env ← getEnv
  let isoMakerLemmas := catRwIsoAttr.getDecls env ++ catRwAttr.getDecls env
  let relations := relExt.getState env
  let occCountRef ← IO.mkRef {}
  let originalGoal? ← try some <$> getMainGoal catch _ => pure none
  for i in [:numRules] do
    let ruleStx := rulesAndSeps[i * 2]!
    let sep := rulesAndSeps.getD (i * 2 + 1) Syntax.missing
    withTacticInfoContext (mkNullNode #[ruleStx, sep]) do
      withRef ruleStx do
        let rule ← withMainContext <| parseRuleV2 ruleStx
        withEnableInfoTree false do
          withMainContext do
            if (← getGoals).isEmpty then
              throwError "all goals have already been solved"
            let anyRewroteRef ← IO.mkRef false
            let rewrite (fvarId? : Option FVarId) : TacticM Unit := do
              let goal ← getMainGoal
              occCountRef.set {}
              let ctx := { rule, isoMakerLemmas, relations, config, occCountRef }
              let (gs, _, rewrote) ← liftMetaM <| ReaderT.run (evalRewrite goal fvarId?) ctx
              replaceMainGoal gs.toList
              if rewrote then anyRewroteRef.set true
            withLocation loc
              (fun fvarId => rewrite (some fvarId))
              (rewrite none)
              (fun _ => throwError "failed to rewrite")
            if !(← anyRewroteRef.get) then
              throwTacticEx `cat_rw (← getMainGoal)
                m!"tactic 'cat_rw' failed, rule {rule.lhs} -> {rule.rhs} did not match any location"
  if CatRw.trace_iso_expr.get <| ← getOptions then
    if let some originalGoal := originalGoal? then
      let val ← liftMetaM <| instantiateMVars (mkMVar originalGoal)
      Lean.logInfo m!"iso := {val}"

end CatRw

attribute [cat_rw_iso] congrArg

/--
`cat_rw [rules]` performs generalized rewriting using registered relations.
It propagates rewrites through expressions using congruence/lifting lemmas.
Supports `at` location and `config := { occs := ... }`.
-/
elab stx:"cat_rw " cfg:Parser.Tactic.optConfig rules:Parser.Tactic.rwRuleSeq
    loc:(Parser.Tactic.location)? : tactic => do
  let cfg ← CatRw.elabConfig cfg
  let loc := match loc with
    | some stx => expandLocation stx
    | none => Location.targets #[] true
  CatRw.evalCatRwV2 stx rules loc cfg
