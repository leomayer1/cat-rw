import Mathlib

/-!
# `cat_rw`

A first small version of a category-theoretic rewrite tactic.

For now, the rewrite families known to `cat_rw` are:

* `CategoryTheory.Iso.isZero_iff`;
* `CategoryTheory.Functor.preservesMonomorphisms.iso_iff`.
-/

namespace CatRw

/-- The current list of category-theoretic rewrite lemmas used by `cat_rw`.

This is deliberately tiny for the first version; more lemmas can be added here
as the tactic grows past `IsZero`.
-/
syntax (name := catRwIsoIsZeroIff) "cat_rw_iso_isZero_iff " term : term
syntax (name := catRwPreservesMonomorphismsIsoIff)
  "cat_rw_preservesMonomorphisms_iso_iff " term : term

macro_rules
  | `(cat_rw_iso_isZero_iff $e) => `(CategoryTheory.Iso.isZero_iff $e)
  | `(cat_rw_preservesMonomorphisms_iso_iff $e) =>
    `(CategoryTheory.Functor.preservesMonomorphisms.iso_iff $e)

/-- Rewrite using category-theoretic isomorphism lemmas.

Currently supports single rewrites of the form `cat_rw [e]`, where `e : X ≅ Y`,
by trying the current list of category-theoretic rewrite lemmas.
-/
macro "cat_rw " "[" e:term "]" : tactic =>
  `(tactic| first
    | rw [cat_rw_iso_isZero_iff $e]
    | rw [cat_rw_preservesMonomorphisms_iso_iff $e])

/-- The symmetric form of `cat_rw [e]`. -/
macro "cat_rw " "[" "←" e:term "]" : tactic =>
  `(tactic| first
    | rw [← cat_rw_iso_isZero_iff $e]
    | rw [← cat_rw_preservesMonomorphisms_iso_iff $e])

end CatRw
