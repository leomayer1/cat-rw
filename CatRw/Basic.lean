import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
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

def evalCatRw
    (rulesStx : TSyntax `Lean.Parser.Tactic.rwRuleSeq) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← whnf (← getMainTarget)
  let (lhs, rhs) ←
    match_expr target with
    | CategoryTheory.Iso _ _ X Y => pure (X, Y)
    | _ => throwError
        "cat_rw expected a goal of the form `X ≅ Y`, but the goal is{indentExpr target}"
  let rules ← parseRules rulesStx
  let result ← rewriteMany rules lhs
  let newTarget ← mkAppM ``CategoryTheory.Iso #[result.newExpr, rhs]
  let newGoal ← mkFreshExprMVar newTarget
  goal.assign (← mkAppM ``CategoryTheory.Iso.trans #[result.iso, newGoal])
  let newGoalId := newGoal.mvarId!
  if ← closeIfRefl newGoalId result.newExpr rhs then
    replaceMainGoal []
  else
    replaceMainGoal [newGoalId]

end CatRw

elab "cat_rw " rules:rwRuleSeq : tactic => CatRw.evalCatRw rules
