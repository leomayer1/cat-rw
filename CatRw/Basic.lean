import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic

open CategoryTheory Limits
open Lean Meta Elab Tactic
open Lean.Parser.Tactic (rwRuleSeq)

namespace CatRw

structure Rule where
  iso : Expr
  src : Expr
  dst : Expr

structure RewriteResult where
  newExpr : Expr
  iso : Expr

structure IffRewriteResult where
  newTarget : Expr
  mkProof : Expr → MetaM Expr

private def isoIffLemmas : Array Name := #[
  ``CategoryTheory.Iso.isZero_iff,
  ``CategoryTheory.Functor.preservesMonomorphisms.iso_iff,
  ``CategoryTheory.Functor.preservesEpimorphisms.iso_iff,
  ``CategoryTheory.Functor.isEquivalence_iff_of_iso,
  ``CategoryTheory.Functor.initial_natIso_iff
]

private def isoEndpoints (e : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType e)
  match_expr type with
  | CategoryTheory.Iso _ _ X Y => return (X, Y)
  | _ => throwError "cat_rw expected an isomorphism, but{indentExpr e}\nhas type{indentExpr type}"

private def parseRule (stx : Syntax) : TacticM Rule := do
  let raw ← Term.elabTerm stx[1]! none
  let raw ← instantiateMVars raw
  let (src, dst) ← isoEndpoints raw
  if stx[0]!.isNone then
    return { iso := raw, src, dst }
  else
    return { iso := ← mkAppM ``CategoryTheory.Iso.symm #[raw], src := dst, dst := src }

private def parseRules : TSyntax `Lean.Parser.Tactic.rwRuleSeq → TacticM (Array Rule)
  | `(rwRuleSeq| [$rules,*]) => rules.getElems.mapM fun ruleStx => parseRule ruleStx
  | _ => throwUnsupportedSyntax

private def tryWhole (rule : Rule) (e : Expr) : MetaM (Option RewriteResult) := do
  let state ← saveState
  try
    if ← withReducibleAndInstances <| isDefEq e rule.src then
      return some { newExpr := ← instantiateMVars rule.dst, iso := ← instantiateMVars rule.iso }
    else
      restoreState state
      return none
  catch _ =>
    restoreState state
    return none

private def mkReflIso (e : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Iso.refl #[e]

private def mkFunctorObj (F X : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Functor.obj #[F, X]

private def mkProd (X Y : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Limits.prod #[X, Y]

private partial def rewriteOnce (rule : Rule) (e : Expr) : MetaM (Option RewriteResult) := do
  if let some result ← tryWhole rule e then
    return some result
  let args := e.getAppArgs
  if e.isAppOfArity ``CategoryTheory.Functor.obj 6 then
    let F := args[4]!
    let X := args[5]!
    if let some result ← tryWhole rule F then
      return some {
        newExpr := ← mkFunctorObj result.newExpr X
        iso := ← mkAppM ``CategoryTheory.Iso.app #[result.iso, X]
      }
    if let some result ← rewriteOnce rule X then
      return some {
        newExpr := ← mkFunctorObj F result.newExpr
        iso := ← mkAppM ``CategoryTheory.Functor.mapIso #[F, result.iso]
      }
  if e.isAppOfArity ``CategoryTheory.Limits.prod 5 then
    let X := args[2]!
    let Y := args[3]!
    if let some result ← rewriteOnce rule X then
      return some {
        newExpr := ← mkProd result.newExpr Y
        iso := ← mkAppM ``CategoryTheory.Limits.prod.mapIso #[result.iso, ← mkReflIso Y]
      }
    if let some result ← rewriteOnce rule Y then
      return some {
        newExpr := ← mkProd X result.newExpr
        iso := ← mkAppM ``CategoryTheory.Limits.prod.mapIso #[← mkReflIso X, result.iso]
      }
  return none

private def rewriteMany (rules : Array Rule) (lhs : Expr) : TacticM RewriteResult := do
  let mut current := lhs
  let mut iso ← mkReflIso lhs
  for rule in rules do
    let some result ← rewriteOnce rule current
      | throwError
          "cat_rw could not apply an isomorphism with source{indentExpr rule.src}\n\
          to{indentExpr current}"
    iso ← mkAppM ``CategoryTheory.Iso.trans #[iso, result.iso]
    current := result.newExpr
  return { newExpr := current, iso }

private def closeIfRefl (goal : MVarId) (lhs rhs : Expr) : TacticM Bool := do
  let state ← saveState
  if ← withReducibleAndInstances <| isDefEq lhs rhs then
    goal.assign (← mkReflIso rhs)
    return true
  else
    restoreState state
    return false

private partial def subexpressions (e : Expr) : Array Expr :=
  let rec visit (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := acc.push e
    match e with
    | .app f a => visit a (visit f acc)
    | .lam _ t b _ => visit b (visit t acc)
    | .forallE _ t b _ => visit b (visit t acc)
    | .letE _ t v b _ => visit b (visit v (visit t acc))
    | .mdata _ b => visit b acc
    | .proj _ _ b => visit b acc
    | _ => acc
  visit e #[]

private def tryIsoIffLemma
    (target iso : Expr) (lemmaName : Name) : TacticM (Option IffRewriteResult) := do
  let state ← saveState
  try
    let iff ← mkAppM lemmaName #[iso]
    let iffType ← whnf (← inferType iff)
    match_expr iffType with
    | Iff lhs rhs =>
        let lhsState ← saveState
        if ← withReducibleAndInstances <| isDefEq lhs target then
          let iff ← instantiateMVars iff
          let newTarget ← instantiateMVars rhs
          return some {
            newTarget
            mkProof := fun newProof => mkAppM ``Iff.mpr #[iff, newProof]
          }
        else
          restoreState lhsState
          if ← withReducibleAndInstances <| isDefEq rhs target then
            let iff ← instantiateMVars iff
            let newTarget ← instantiateMVars lhs
            return some {
              newTarget
              mkProof := fun newProof => mkAppM ``Iff.mp #[iff, newProof]
            }
          else
            restoreState state
            return none
    | _ =>
        restoreState state
        return none
  catch _ =>
    restoreState state
    return none

private def tryIsoIffLemmas (target iso : Expr) : TacticM (Option IffRewriteResult) := do
  for lemmaName in isoIffLemmas do
    if let some result ← tryIsoIffLemma target iso lemmaName then
      return some result
  return none

private def tryIffGoalRewrite
    (target : Expr) (rules : Array Rule) : TacticM (Option IffRewriteResult) := do
  for candidate in subexpressions target do
    let state ← saveState
    try
      let result ← rewriteMany rules candidate
      if let some iffResult ← tryIsoIffLemmas target result.iso then
        return some iffResult
      else
        restoreState state
    catch _ =>
      restoreState state
  return none

private def evalIsoGoal (goal : MVarId) (rules : Array Rule) (lhs rhs : Expr) : TacticM Unit := do
  let result ← rewriteMany rules lhs
  let newTarget ← mkAppM ``CategoryTheory.Iso #[result.newExpr, rhs]
  let newGoal ← mkFreshExprMVar newTarget
  goal.assign (← mkAppM ``CategoryTheory.Iso.trans #[result.iso, newGoal])
  let newGoalId := newGoal.mvarId!
  if ← closeIfRefl newGoalId result.newExpr rhs then
    replaceMainGoal []
  else
    replaceMainGoal [newGoalId]

private def evalIffGoal (goal : MVarId) (rules : Array Rule) (target : Expr) : TacticM Unit := do
  let some result ← tryIffGoalRewrite target rules
    | throwError
        "cat_rw could not rewrite the goal using the registered iso-iff lemmas. \
        The goal is{indentExpr target}"
  let newGoal ← mkFreshExprMVar result.newTarget
  goal.assign (← result.mkProof newGoal)
  replaceMainGoal [newGoal.mvarId!]

private def evalTarget (goal : MVarId) (rules : Array Rule) (target : Expr) : TacticM Unit := do
  match_expr target with
  | CategoryTheory.Iso _ _ X Y => evalIsoGoal goal rules X Y
  | _ =>
      let targetWhnf ← whnf target
      match_expr targetWhnf with
      | CategoryTheory.Iso _ _ X Y => evalIsoGoal goal rules X Y
      | _ => evalIffGoal goal rules target

def evalCatRw
    (rulesStx : TSyntax `Lean.Parser.Tactic.rwRuleSeq) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← getMainTarget)
  let rules ← parseRules rulesStx
  evalTarget goal rules target

end CatRw

elab "cat_rw " rules:rwRuleSeq : tactic => CatRw.evalCatRw rules
