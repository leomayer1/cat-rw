import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Lean.Elab.Tactic

open CategoryTheory Limits
open Lean Meta Elab Tactic
open Lean.Parser.Tactic (rwRuleSeq)

/-
The `CatRw` namespace contains the core logic for the `cat_rw` tactic,
which performs rewriting using isomorphisms in category theory.
-/
namespace CatRw

/--
A `Rule` represents a single isomorphism that can be used for rewriting.
It captures the isomorphism itself, its source object, and its destination object.
-/
structure Rule where
  /-- The isomorphism expression. -/
  iso : Expr
  /-- The source object of the isomorphism. -/
  src : Expr
  /-- The destination object of the isomorphism. -/
  dst : Expr

/--
The result of a single rewrite operation.
-/
structure RewriteResult where
  /-- The new expression after the rewrite. -/
  newExpr : Expr
  /-- The isomorphism between the original expression and the `newExpr`. -/
  iso : Expr

/--
Extracts the source and destination objects from an isomorphism's type.
Expected type: `X ≅ Y`.
-/
private def isoEndpoints (e : Expr) : MetaM (Expr × Expr) := do
  let type ← whnf (← inferType e)
  match_expr type with
  | CategoryTheory.Iso _ _ X Y => return (X, Y)
  | _ => throwError "cat_rw expected an isomorphism, but{indentExpr e}\nhas type{indentExpr type}"

/--
Parses a single rewrite rule syntax into a `Rule` structure.
Handles both forward and backward (using `←`) directions.
-/
private def parseRule (stx : Syntax) : TacticM Rule := do
  let raw ← Term.elabTerm stx[1]! none
  let (args, _, _) ← forallMetaTelescopeReducing (← inferType raw)
  let raw := mkAppN raw args
  let raw ← instantiateMVars raw
  let (src, dst) ← isoEndpoints raw -- src, dst : Expr (objects)
  if stx[0]!.isNone then
    return { iso := raw, src, dst }
  else
    return { iso := ← mkAppM ``CategoryTheory.Iso.symm #[raw], src := dst, dst := src }

/--
Parses a sequence of rewrite rules from a `rwRuleSeq` syntax.
-/
private def parseRules : TSyntax `Lean.Parser.Tactic.rwRuleSeq → TacticM (Array Rule)
  | `(rwRuleSeq| [$rules,*]) => rules.getElems.mapM fun ruleStx => parseRule ruleStx
  | _ => throwUnsupportedSyntax

/--
Attempts to apply a `Rule` to the entire expression `e` if they are definitionally equal.
-/
private def tryWhole (rule : Rule) (e : Expr) : MetaM (Option RewriteResult) := do
  let state ← saveState
  try
    let sameType ← isDefEq (← inferType e) (← inferType rule.src)
    if sameType && (← isDefEq e rule.src) then
      return some { newExpr := ← instantiateMVars rule.dst, iso := ← instantiateMVars rule.iso }
    else
      restoreState state
      return none
  catch _ =>
    restoreState state
    return none

/-- Creates a reflexive isomorphism `Iso.refl e`. -/
private def mkReflIso (e : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Iso.refl #[e]

/-- Creates a functor application `F.obj X`. -/
private def mkFunctorObj (F X : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Functor.obj #[F, X]

/-- Creates a product of two objects `X ⨯ Y`. -/
private def mkProd (X Y : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Limits.prod #[X, Y]

/--
Recursively attempts to apply a rewrite rule to an expression `e`.
It checks:
1. The expression itself.
2. If it's a functor application `F.obj X`, it tries to rewrite `F` or `X`.
3. If it's a binary product `X ⨯ Y`, it tries to rewrite `X` or `Y`.
-/
private partial def rewriteOnce (rule : Rule) (e : Expr) : MetaM (Option RewriteResult) := do
  Lean.logInfo m!"rewrite rule ({rule.src} -> {rule.dst}) on {e}"
  if let some result ← tryWhole rule e then
    return some result
  let args := e.getAppArgs
  /-
    Check if `e` is an application of `CategoryTheory.Functor.obj`.
    Arity 6:
    0: {C : Type u}
    1: [Category C]
    2: {D : Type v}
    3: [Category D]
    4: (F : C ⥤ D)
    5: (X : C)
  -/
  if e.isAppOfArity ``CategoryTheory.Functor.obj 6 then
    let F := args[4]! -- F : C ⥤ D
    let X := args[5]! -- X : C
    if let some result ← tryWhole rule F then
      Lean.logInfo m!"Functor.app {result.iso} {X}"
      return some {
        newExpr := ← mkFunctorObj result.newExpr X
        iso := ← mkAppM ``CategoryTheory.Iso.app #[result.iso, X]
      }
    if let some result ← rewriteOnce rule X then
      Lean.logInfo m!"Functor.mapIso {F} {result.iso}"
      return some {
        newExpr := ← mkFunctorObj F result.newExpr
        iso := ← mkAppM ``CategoryTheory.Functor.mapIso #[F, result.iso]
      }
  /-
    Check if `e` is an application of `CategoryTheory.Limits.prod`.
    Arity 5:
    0: {C : Type u}
    1: [Category C]
    2: (X : C)
    3: (Y : C)
    4: [HasBinaryProduct X Y]
  -/
  if e.isAppOfArity ``CategoryTheory.Limits.prod 5 then
    let X := args[2]! -- X : C
    let Y := args[3]! -- Y : C
    if let some result ← rewriteOnce rule X then
      Lean.logInfo m!"prod.mapIso {result.iso} rfl({Y})"
      return some {
        newExpr := ← mkProd result.newExpr Y
        iso := ← mkAppM ``CategoryTheory.Limits.prod.mapIso #[result.iso, ← mkReflIso Y]
      }
    if let some result ← rewriteOnce rule Y then
      Lean.logInfo m!"prod.mapIso rfl({X}) {result.iso}"
      return some {
        newExpr := ← mkProd X result.newExpr
        iso := ← mkAppM ``CategoryTheory.Limits.prod.mapIso #[← mkReflIso X, result.iso]
      }
  return none

/--
Applies a sequence of rules to the left-hand side of an isomorphism.
Transitions from `lhs` to a new expression by composing the isomorphisms.
-/
private def rewriteMany (rules : Array Rule) (lhs : Expr) : TacticM RewriteResult := do
  let mut current := lhs -- current : Expr (the object being rewritten)
  let mut iso := none -- iso : Option Expr (the accumulated isomorphism)
  for rule in rules do
    let some result ← rewriteOnce rule current
      | throwError
          "cat_rw could not apply an isomorphism with source{indentExpr rule.src}\n\
          to{indentExpr current}"
    if let some i := iso then
      iso := some <| ← mkAppM ``CategoryTheory.Iso.trans #[i, result.iso]
    else
      iso := some <| result.iso
    current := result.newExpr
  Lean.logInfo m!"iso = {iso}"
  return { newExpr := current, iso := iso.getD (← mkReflIso lhs) }

/--
The implementation of the `cat_rw` tactic.
It parses the rules, applies them to the LHS of the current goal `X ≅ Y`,
and then either closes the goal if the new LHS matches `Y` or leaves
a new goal `new_X ≅ Y`.
-/
def evalCatRw
    (rulesStx : TSyntax `Lean.Parser.Tactic.rwRuleSeq) : TacticM Unit := withMainContext do
  let goal ← getMainGoal -- goal : MVarId
  let target ← whnf (← getMainTarget) -- target : Expr (the goal type, expected X ≅ Y)
  let (lhs, rhs) ←
    match_expr target with
    | CategoryTheory.Iso _ _ X Y => pure (X, Y) -- X, Y : Expr (objects)
    | _ => throwError
        "cat_rw expected a goal of the form `X ≅ Y`, but the goal is{indentExpr target}"
  let rules ← parseRules rulesStx
  let result ← rewriteMany rules lhs
  -- If the rewritten LHS is definitionally equal to the RHS, we can close the goal directly.
  -- This avoids adding an unnecessary composition with `Iso.refl`.
  if ← isDefEq rhs result.newExpr then
    goal.assign (result.iso)
    replaceMainGoal []
  else
    -- Otherwise, we create a new goal `new_X ≅ Y` and assign `iso.trans result.iso new_goal`
    -- to the original goal.
    let newTarget ← mkAppM ``CategoryTheory.Iso #[result.newExpr, rhs]
    -- newGoal : Expr (the new goal metavariable)
    let newGoal ← mkFreshExprMVar newTarget 
    goal.assign (← mkAppM ``CategoryTheory.Iso.trans #[result.iso, newGoal])
    replaceMainGoal [newGoal.mvarId!]

end CatRw

/--
`cat_rw [rules]` performs rewriting using isomorphisms in category theory.
It works on goals of the form `X ≅ Y` by rewriting `X` using the provided
isomorphisms and composing them.
-/
elab "cat_rw " rules:rwRuleSeq : tactic => CatRw.evalCatRw rules
