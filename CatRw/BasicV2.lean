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
open Lean.Parser.Tactic (rwRuleSeq)

namespace CatRw

initialize registerTraceClass `CatRw

/--
Information about a binary relation supported by `cat_rw`.
Contains names of lemmas for basic properties.
-/
structure RelInfo where
  name : Name
  refl : Name
  symm : Option Name
  trans : Option Name
  deriving Inhabited, Repr

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

/-- Context for the `grw` algorithm. -/
structure ContextV2 where
  rule : RuleV2
  isoMakerLemmas : Array Name
  relations : NameMap RelInfo
  depth : Nat := 0

abbrev CatRwM2 := ReaderT ContextV2 MetaM

instance : MonadBacktrack Meta.SavedState CatRwM2 where
  saveState := liftM (saveState : MetaM _)
  restoreState s := liftM (restoreState s : MetaM _)

/--
Extracts the relation and endpoints from a type.
Supports `X ≅ Y`, `X = Y`, `P ↔ Q` and any registered binary relations.
-/
def getRelInfo? (relations : NameMap RelInfo) (type : Expr) :
    MetaM (Option (Name × Expr × Expr)) := do
  let type ← whnf type
  let res ← match_expr type with
  | CategoryTheory.Iso _ _ X Y => pure <| some (``CategoryTheory.Iso, X, Y)
  | Eq _ X Y => pure <| some (``Eq, X, Y)
  | Iff P Q => pure <| some (``Iff, P, Q)
  | _ =>
    if type.isApp && type.getAppNumArgs >= 2 then
      let args := type.getAppArgs
      let rel := type.getAppFn.constName?
      if let some r := rel then
        let lhs := args[args.size - 2]!
        let rhs := args[args.size - 1]!
        pure <| some (r, lhs, rhs)
      else pure none
    else pure none
  if let some (r, x, y) := res then
    if relations.contains r then return some (r, x, y)
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
      let proof ← instantiateMVars (← solveInstances ctx.rule.proof)
      let rhs ← instantiateMVars (← solveInstances ctx.rule.rhs)
      trace[CatRw] m!"matched rule: {ctx.rule.lhs} -> {rhs}"
      return some { expr' := rhs, proof }
  return none

mutual
/--
The generalized rewrite function.
`grw r_out expr` returns a proof of `r_out expr expr'`.
Traverses the expression tree and applies rules or lifting lemmas.
-/
partial def grw (r_out : Name) (expr : Expr) : CatRwM2 (Option Rewrote) := do
  let ctx ← read
  if ctx.depth > 20 then return none
  let expr ← instantiateMVars expr
  if expr.isMVar then return none
  withTraceNode `CatRw (fun _ => return m!"grw {r_out} on {expr}") do
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
    let resultTypeWhnf ← whnf (← instantiateMVars resultType)
    let some (r_res, lhs, rhs) ← getRelInfo? ctx.relations resultTypeWhnf | return none
    if r_res != r_out then return none
    let relInfo := ctx.relations.find? r_res
    let mut matchedLhs := ← withReducible (isDefEq lhs expr)
    let mut matchedRhs := false
    if !matchedLhs then
      if let some ri := relInfo then
        if let some _ := ri.symm then
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
        proof ← mkAppM relInfo.get!.symm.get! #[proof]
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
  -- Try rewriting LHS
  let nextCtx := { ctx with depth := ctx.depth + 1 }
  if let some res ← withReader (fun _ => nextCtx) (grw r_arg argLhs) then
    if ← isDefEq argType (← inferType res.proof) then
      arg.mvarId!.assign res.proof
      return true
  -- Try rewriting RHS if relation is symmetric
  if let some relInfoArg := ctx.relations.find? r_arg then
    if let some symmName := relInfoArg.symm then
      if let some res ← withReader (fun _ => nextCtx) (grw r_arg argRhs) then
        let proof ← mkAppM symmName #[res.proof]
        if ← isDefEq argType (← inferType proof) then
          arg.mvarId!.assign proof
          return true
  -- Fallback: assign reflexivity
  if let some relInfoArg := ctx.relations.find? r_arg then
    let reflProof ← mkAppM relInfoArg.refl #[argLhs]
    if ← isDefEq argType (← inferType reflProof) then
      arg.mvarId!.assign reflProof
  return false
end

/-- Handles goals that are registered binary relations (e.g., `X ≅ Y`). -/
private def evalRelationGoal (goal : MVarId) (r_goal : Name) (lhs rhs : Expr) :
    CatRwM2 (Array MVarId) := do
  let ctx ← read
  let relInfo := (ctx.relations.find? r_goal).get!
  -- Rewrite both sides
  let rhsrw ← grw r_goal rhs
  let mut lhsrw := none
  if relInfo.symm.isSome then
    lhsrw ← grw r_goal lhs
  if rhsrw.isNone && lhsrw.isNone then return #[goal]
  let newLhs ← instantiateMVars (if let some l := lhsrw then l.expr' else lhs)
  let newRhs ← instantiateMVars (if let some r := rhsrw then r.expr' else rhs)
  trace[CatRw] m!"new goal sides: {newLhs}, {newRhs}"
  let newTarget ← mkAppM r_goal #[newLhs, newRhs]
  let newGoal ← mkFreshExprMVar (← instantiateMVars newTarget)
  -- Assemble the final proof: lhs_proof . new_goal . rhs_proof.symm
  let mut finalProof := newGoal
  if let some r_res := rhsrw then
    let isoR_symm ← mkAppM relInfo.symm.get! #[r_res.proof]
    finalProof ← mkAppM relInfo.trans.get! #[finalProof, isoR_symm]
  if let some l_res := lhsrw then
    finalProof ← mkAppM relInfo.trans.get! #[l_res.proof, finalProof]
  goal.assign (← solveInstances finalProof)
  -- Check if result is defeq
  if ← withReducible (isDefEq newLhs newRhs) then
    let reflProof ← mkAppM relInfo.refl #[newLhs]
    if ← isDefEq (← inferType newGoal) (← inferType reflProof) then
      newGoal.mvarId!.assign reflProof
      return #[]
  return #[newGoal.mvarId!]

/-- Handles goals that are predicates (using `Iff` to transform them). -/
private def evalPropGoal (goal : MVarId) (target : Expr) : CatRwM2 (Array MVarId) := do
  let r_goal := ``Iff
  if let some res ← grw r_goal target then
    let newGoal ← mkFreshExprMVar (← instantiateMVars res.expr')
    let proof ← mkAppM ``Iff.mpr #[res.proof, newGoal]
    goal.assign (← solveInstances proof)
    if ← withReducible (isDefEq (← instantiateMVars res.expr') (mkConst ``True)) then
      newGoal.mvarId!.assign (mkConst ``True.intro)
      return #[]
    return #[newGoal.mvarId!]
  return #[goal]

/--
Dispatches the tactic based on the goal type.
If the goal is a known relation, it rewrites both sides.
Otherwise, it attempts to rewrite the goal itself as a proposition.
-/
def evalTargetV2 (goal : MVarId) (target : Expr) : CatRwM2 (Array MVarId) := do
  let ctx ← read
  let target ← instantiateMVars target
  if let some (r_goal, lhs, rhs) ← getRelInfo? ctx.relations target then
    evalRelationGoal goal r_goal lhs rhs
  else
    evalPropGoal goal target

/-- Parses a user-provided rewrite rule. -/
private def parseRuleV2 (stx : Syntax) : TacticM RuleV2 := do
  let raw ← Term.elabTerm stx[1]! none
  let rawType ← inferType raw
  let (args, _, _) ← forallMetaTelescopeReducing rawType
  let proof := mkAppN raw args
  let type ← inferType proof
  let env ← getEnv
  let relations := relExt.getState env
  if let some (rel, lhs, rhs) ← getRelInfo? relations type then
    if stx[0]!.isNone then
      return { proof, rel, lhs, rhs }
    else
      let relInfo := (relations.find? rel).get!
      if let some symm := relInfo.symm then
        let symmProof ← mkAppM symm #[proof]
        let newLhs ← instantiateMVars rhs
        let newRhs ← instantiateMVars lhs
        return { proof := symmProof, rel, lhs := newLhs, rhs := newRhs }
      throwError "Relation {rel} is not symmetric"
  throwError "Rule must be a binary relation"

/-- The main entry point for the `cat_rwv2` tactic. -/
def evalCatRwV2 (rulesStx : TSyntax `Lean.Parser.Tactic.rwRuleSeq) :
    TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let rules ← match rulesStx with
    | `(rwRuleSeq| [$rules,*]) => rules.getElems.mapM parseRuleV2
    | _ => throwUnsupportedSyntax
  let env ← getEnv
  let isoMakerLemmas := catRwIsoAttr.getDecls env ++ catRwAttr.getDecls env
  let relations := relExt.getState env
  let mut currentGoals := #[goal]
  for rule in rules do
    let mut nextGoals := #[]
    for g in currentGoals do
      if ← g.isAssigned then continue
      let t ← g.getType
      let ctx := { rule, isoMakerLemmas, relations }
      let newGs ← liftMetaM <| ReaderT.run (evalTargetV2 g t) ctx
      nextGoals := nextGoals ++ newGs
    currentGoals := nextGoals
  if CatRw.trace_iso_expr.get <| ← getOptions then
    let val ← instantiateMVars (mkMVar goal)
    Lean.logInfo m!"iso := {val}" -- {← goal.getType}
  replaceMainGoal currentGoals.toList

/--
`cat_rwv2 [rules]` performs generalized rewriting using registered relations.
It propagates rewrites through expressions using congruence/lifting lemmas.
-/
elab "cat_rwv2 " rules:rwRuleSeq : tactic => evalCatRwV2 rules

attribute [cat_rw_iso] congrArg

end CatRw
