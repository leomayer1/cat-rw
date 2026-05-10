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
A register for relations.
-/
initialize relExt : SimpleScopedEnvExtension RelInfo (NameMap RelInfo) ←
  registerSimpleScopedEnvExtension {
    name := `cat_rw_rel_ext
    initial := initialRelMap
    addEntry := fun map rel => map.insert rel.name rel
  }

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

/--
Result of a generalized rewrite.
-/
structure Rewrote where
  /-- The new expression. -/
  expr' : Expr
  /-- The proof of `r expr expr'`. -/
  proof : Expr

/--
Context for the `grw` algorithm.
-/
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
Supports `X ≅ Y`, `X = Y`, `P ↔ Q`.
Only returns if the relation is registered.
-/
def getRelInfo? (relations : NameMap RelInfo) (type : Expr) : MetaM (Option (Name × Expr × Expr)) := do
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
        pure <| some (r, args[args.size - 2]!, args[args.size - 1]!)
      else pure none
    else pure none
  if let some (r, x, y) := res then
    if relations.contains r then return some (r, x, y)
  return none

/--
Instantiates a lemma with fresh level metavariables and performs a telescope.
-/
private def withLemma (lemmaName : Name) (k : Array Expr → Expr → CatRwM2 (Option α)) :
    CatRwM2 (Option α) := do
  let info ← getConstInfo lemmaName
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let type := info.instantiateTypeLevelParams levels
  let (args, _, resultType) ← forallMetaTelescope type
  k args resultType

/--
Attempts to resolve all instance metavariables within an expression.
-/
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

/--
Finalizes the arguments for a lemma by synthesizing instances and solving metavariables.
-/
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

/--
The generalized rewrite function.
`grw r_out expr` returns a proof of `r_out expr expr'`.
-/
partial def grw (r_out : Name) (expr : Expr) : CatRwM2 (Option Rewrote) := do
  let ctx ← read
  if ctx.depth > 20 then
    trace[CatRw] m!"grw: maximum depth reached"
    return none
  let expr ← instantiateMVars expr
  if expr.isMVar then return none
  trace[CatRw] m!"grw {r_out} on {expr}"
  -- 1. Try if rule matches expr
  if r_out == ctx.rule.rel then
    if ← withReducible (isDefEq ctx.rule.lhs expr) then
      let proof ← instantiateMVars (← solveInstances ctx.rule.proof)
      let rhs ← instantiateMVars (← solveInstances ctx.rule.rhs)
      trace[CatRw] m!"grw: matched rule {ctx.rule.lhs} -> {rhs}"
      return some { expr' := rhs, proof }
  -- 2. Try lifting lemmas.
  for lemmaName in ctx.isoMakerLemmas do
    let state ← saveState
    try
      let res ← withLemma lemmaName fun args resultType => do
        let resultTypeWhnf ← whnf (← instantiateMVars resultType)
        if let some (r_res, lhs, rhs) ← getRelInfo? ctx.relations resultTypeWhnf then
          if r_res == r_out && (← withReducible (isDefEq lhs expr)) then
             let mut rewrote := false
             for arg in args do
               let argType ← whnf (← instantiateMVars (← inferType arg))
               if let some (r_arg, argLhs, _) ← getRelInfo? ctx.relations argType then
                 let inner := grw r_arg argLhs
                 if let some res ← withReader (fun c => { c with depth := c.depth + 1 }) inner then
                   if ← isDefEq argType (← inferType res.proof) then
                      arg.mvarId!.assign res.proof
                      rewrote := true
                   else
                      if let some relInfo := ctx.relations.find? r_arg then
                         let reflProof ← mkAppM relInfo.refl #[argLhs]
                         if ← isDefEq argType (← inferType reflProof) then
                            arg.mvarId!.assign reflProof
                 else
                    if let some relInfo := ctx.relations.find? r_arg then
                       let reflProof ← mkAppM relInfo.refl #[argLhs]
                       if ← isDefEq argType (← inferType reflProof) then
                          arg.mvarId!.assign reflProof
             if rewrote then
               let optArgs ← finalizeLemmaArgs args
               let proof ← mkAppOptM lemmaName optArgs
               let rhsInst ← instantiateMVars (← solveInstances rhs)
               let proofInst ← instantiateMVars proof
               trace[CatRw] m!"grw: applied {lemmaName}, newExpr := {rhsInst}"
               return some { expr' := rhsInst, proof := proofInst }
        return none
      if let some r := res then return some r
      restoreState state
    catch _ => restoreState state
  return none

/--
Dispatches the tactic based on the goal type.
-/
def evalTargetV2 (goal : MVarId) (target : Expr) : CatRwM2 (Array MVarId) := do
  let ctx ← read
  let target ← instantiateMVars target
  if let some (r_goal, lhs, rhs) ← getRelInfo? ctx.relations target then
    if let some relInfo := ctx.relations.find? r_goal then
      let rhsrw ← grw r_goal rhs
      let mut lhsrw := none
      if relInfo.symm.isSome then
        if let some res ← grw r_goal lhs then
          lhsrw := some res
      if rhsrw.isNone && lhsrw.isNone then
         return #[goal]
      let newLhs ← instantiateMVars (if let some l := lhsrw then l.expr' else lhs)
      let newRhs ← instantiateMVars (if let some r := rhsrw then r.expr' else rhs)
      trace[CatRw] m!"evalTargetV2: newLhs := {newLhs}, newRhs := {newRhs}"
      let newTarget ← mkAppM r_goal #[newLhs, newRhs]
      let newGoal ← mkFreshExprMVar (← instantiateMVars newTarget)
      let mut finalProof := newGoal
      if let some r_res := rhsrw then
        let symm := relInfo.symm.get!
        let trans := relInfo.trans.get!
        let isoR_symm ← mkAppM symm #[r_res.proof]
        finalProof ← mkAppM trans #[finalProof, isoR_symm]
      if let some l_res := lhsrw then
        let trans := relInfo.trans.get!
        finalProof ← mkAppM trans #[l_res.proof, finalProof]
      let finalProofInst ← solveInstances finalProof
      goal.assign (← instantiateMVars finalProofInst)
      if ← withReducible (isDefEq newLhs newRhs) then
         trace[CatRw] m!"evalTargetV2: newLhs and newRhs are defeq"
         let reflProof ← mkAppM relInfo.refl #[newLhs]
         if ← isDefEq (← inferType newGoal) (← inferType reflProof) then
            newGoal.mvarId!.assign reflProof
         return #[]
      else
         return #[newGoal.mvarId!]
  let r_goal := ``Iff
  if let some res ← grw r_goal target then
     let newGoal ← mkFreshExprMVar (← instantiateMVars res.expr')
     let proof ← mkAppM ``Iff.mpr #[res.proof, newGoal]
     let proofInst ← solveInstances proof
     goal.assign (← instantiateMVars proofInst)
     if ← withReducible (isDefEq (← instantiateMVars res.expr') (mkConst ``True)) then
        newGoal.mvarId!.assign (mkConst ``True.intro)
        return #[]
     return #[newGoal.mvarId!]
  return #[goal]

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
      if let some relInfo := relations.find? rel then
        if let some symm := relInfo.symm then
          let symmProof ← mkAppM symm #[proof]
          let lhsInst ← instantiateMVars lhs
          let rhsInst ← instantiateMVars rhs
          return { proof := symmProof, rel, lhs := rhsInst, rhs := lhsInst }
      throwError "Relation {rel} is not symmetric"
  throwError "Rule must be a binary relation"

def evalCatRwV2 (rulesStx : TSyntax `Lean.Parser.Tactic.rwRuleSeq) : TacticM Unit := withMainContext do
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
  replaceMainGoal currentGoals.toList

elab "cat_rwv2 " rules:rwRuleSeq : tactic => evalCatRwV2 rules

attribute [cat_rw_iso] congrArg

end CatRw
