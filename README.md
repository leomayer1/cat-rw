# cat-rw

`cat-rw` is a Lean 4 project providing `cat_rw`, a category-theoretic rewrite tactic.
It rewrites objects and goals using isomorphisms, playing a role similar to `rw` for
equalities but with rules of type `X ≅ Y`.

## Basic Use

```lean
import CatRw

open CategoryTheory Limits

variable {C : Type*} [Category* C]
variable (a b c : C)

example (h : a ≅ b) (h' : b ≅ c) : a ≅ c := by
  cat_rw [h, h']
```

The tactic also accepts reversed rules:

```lean
example (φ : a ≅ b) : b ≅ a := by
  cat_rw [← φ]
```

## Capabilities

`cat_rw` can recursively lift isomorphisms through registered categorical
constructions. Out of the box this includes functor application, natural
isomorphism components, binary products, binary coproducts, product categories,
comma projections, and monoidal tensoring.

For example:

```lean
variable {C : Type*} [Category* C] [HasProducts C]
variable (a b c : C)

noncomputable example (φ : a ≅ b) : a ⨯ c ≅ c ⨯ b := by
  cat_rw [φ, prod.braiding b c]
```

`cat_rw` can also rewrite proposition goals using registered iff lemmas, such as
`IsZero`, preservation of monos/epis, equivalences, limits, colimits, projective
objects, injective objects, and simple objects.

```lean
example {X Y : C} (φ : X ≅ Y) (h : IsZero Y) : IsZero X := by
  cat_rw [φ]
  exact h
```

## Extending `cat_rw`

There are two attributes:

* `@[cat_rw]` registers iff lemmas used to rewrite proposition goals.
* `@[cat_rw_iso]` registers lemmas or definitions that lift isomorphisms through
  larger expressions.

For instance, a lemma of the form `P X ↔ P Y` can be tagged with `@[cat_rw]`,
while a construction of type `F X ≅ F Y` from `X ≅ Y` can be tagged with
`@[cat_rw_iso]`.

## Debugging

Use tracing to inspect the search:

```lean
set_option trace.CatRw true
```

The project is built with Lake:

```bash
lake build
```
