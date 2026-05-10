

/-!
# Generalized Rewriting Principles

This file explores the theoretical foundations of the `cat_rw` tactic and its relation
to other rewriting tactics in Lean 4, such as `rw`, `grewrite` (`grw`), and `simp`.

## Operating Principles Comparison

### 1. Term-level Rewriting (`rw`, `grewrite`)
Tactics like `rw` and `grewrite` typically follow a **Search-and-Replace** pattern:
1.  **Search**: Use `kabstract` or a similar mechanism to find occurrences of the rewrite rule's
    LHS in the target expression.
2.  **Replace**: Substitute the found occurrence with the rule's RHS.
3.  **Justify**: Generate a proof that the overall expression's value (or truth value) is
    preserved.
    - `rw` uses `Eq.rec` (equality substitution).
    - `grewrite` uses `gcongr` lemmas to propagate a general relation through the expression tree.

### 2. Structural Rewriting (`simp`, `cat_rw`)
Tactics like `simp` and `cat_rw` follow a **Recursive Structural** pattern:
1.  **Traverse**: Walk down the expression tree (top-down or bottom-up).
2.  **Match**: At each node, check if any rewrite rules (or `simp` lemmas) apply to the whole node.
3.  **Recurse**: If no rule applies, use "congruence" lemmas to move into the subterms.
    - `simp` uses `congr` lemmas for equality.
    - `cat_rw` uses `iso_maker` lemmas (tagged `@[cat_rw_iso]`) to lift isomorphisms through
      functors, products, etc.
4.  **Transfer**: For goals that are not isomorphisms, `cat_rw` uses `iso_iff` lemmas
    (tagged `@[cat_rw]`) to transform the goal into an equivalent one.

## Generalized Congruence

The core abstraction shared by these tactics is the **Generalized Congruence Lemma**.
If we have a collection of relations $R_T$ indexed by types $T$, a congruence lemma
for a function $f$ specifies how $f$ preserves these relations.

-/

/--
An abstract transitive relation with reflexivity, generalizing `Eq` and `Iso`.
-/
class NPTrans (A : Type) (r : A → A → Type) : Type where
  trans {X Y Z : A} : r X Y → r Y Z → r X Z
  refl : (X : A) → r X X

/--
A generalized congruence lemma for a unary function `f`.
-/
def GenCongr1 {A B : Type}
    (r_a : A → A → Type) (r_b : B → B → Type)
    (f : B → A) : Type :=
  ∀ {x x' : B}, r_b x x' → r_a (f x) (f x')

/--
A generalized congruence lemma for a binary function `f`.
It states that if the arguments are related, the results are related.
-/
def GenCongr2 {A B₁ B₂ : Type}
    (r_a : A → A → Type) (r_b₁ : B₁ → B₁ → Type) (r_b₂ : B₂ → B₂ → Type)
    (f : B₁ → B₂ → A) : Type :=
  ∀ {x x' : B₁} {y y' : B₂}, r_b₁ x x' → r_b₂ y y' → r_a (f x y) (f x' y')

/-
A generalized transfer lemma (iso-iff).
It states that a predicate `P` is invariant under the relation `r`.

NOTE: `GenTransfer` is a special case of `GenCongr1` where:
- The codomain `A` is `Prop`.
- The output relation `r_a` is `Iff`.
-/
-- def GenTransfer {A : Type} (r : A → A → Type) (P : A → Prop) : Prop :=
  -- GenCongr1 Iff r P



/-
Core algorithm:

grw (r₂) (rule : r₁ X X') (expr) : Option (r₂ expr expr') :=
  if rule.lhs matches expr
    return some (rule)

  for each (
    lemma (h₁ : r₃ A A') (h₂ : r₃ B B') ... :
      r₂ (f A B ...) (f A' B' ...)
  ) {
    if (lemma.lhs matches expr) {
      intro metavars for h₁ h₂ ...
      let mut rewrote := false
      for each hᵢ {
        if let some(e) := grw r₃ rule hᵢ.lhs
          hᵢ = e; rewrote = true
        else
          hᵢ = refl on r₃
      }

      if rewrote
        return some (lemma h₁ h₂ ...)
    } else
      -- consider bailing out here instead of keep trying.
  }
  return none


tactic_impl (rule : r₁ X X') (goal) :=
  if goal matches some r₂ A B
    rhsrw := grw r₂ rule B
    lhsrw := if (r₂ is symmetric) then
      (grw r₂ rule A).symm else none
    if (rhsrw and lhsrw are both none)
      throw error
    newGoal ← intro new mvar
    goal.assign (rhsrw ∘ newgoal ∘ lhsrw)
    return [newGoal]

  if r₂ is not symmetric
    throw error
  for every relation r₂
    if let some(e) := grw r₂ rule goal
      newGoal ← intro new mvar
      goal.assign (e.symm newGoal)
      return [newGoal]
  throw error
-/
