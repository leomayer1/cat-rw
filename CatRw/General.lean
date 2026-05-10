

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
## Robustness vs. Control: Two Paradigms

There is a fundamental trade-off between the two rewriting paradigms:

### 1. Search-and-Replace + Repair (`grw`, `rw`)
- **Robustness**: **Lower**. It performs a "blind" substitution first and then
  tries to justify it using a "repair" tactic (`gcongr`). If the substitution
  creates an ill-typed term, it fails early.
- **Control**: **Higher**. Because it uses `kabstract`, it can target specific
  occurrences of a subterm (e.g., "only the 2nd `x`").
- **Performance**: Can be faster for large terms where only a small, deep subterm
  is changed, as the "repair" phase (`gcongr`) can be optimized to skip
  unaffected branches.

### 2. Recursive Structural (`cat_rw`, `simp`)
- **Robustness**: **Higher**. The tactic is "type-aware" throughout the process.
  It only enters a subterm if it has a `GenCongr` lemma that guarantees the
  final result will be well-typed and related. It builds the proof term
  incrementally.
- **Control**: **Lower**. It traditionally applies rewrites everywhere it can.
  Adding "occurrence control" to a recursive walker is more complex (requiring
  stateful counting during the walk).
- **Performance**: Can be slower on extremely large terms because it must
  re-verify the structure of the entire expression to ensure congruence.

### Which is better?
For **Category Theory**, the **Recursive Structural** approach (used by `cat_rw`)
is generally superior. Category-theoretic terms are highly dependent (functors
on objects depend on the category, etc.), and "blind" substitution is very
likely to result in difficult-to-debug type errors. Building the isomorphism
structurally ensures that every step is valid data.

## Mixing Relations in `grw` and `cat_rw`

Both tactics can be extended to handle "Mixed Relations."

### Mixed Relations in `grw`
`grw` already supports a form of mixed relations via `gcongr`. If you have a
goal $x \leq z$ and a rewrite $y = z$, `grw` can use the equality. If you have
$x < y$ and $y \leq z$, `grw` can conclude $x < z$ *if* there are transitivity
lemmas registered for $(\leq, <)$.
- **Mechanism**: `gcongr` searches for lemmas that match the specific
  combination of relations at each node.

### Mixed Relations in `cat_rw`
A generalized `cat_rw` could handle mixed relations (e.g., `Iso` and `≤`) by:
1.  **Relation Tracking**: The walker carries the "current required relation"
    as it descends.
2.  **Lifting Lemmas**: Registering lemmas like `GenCongr (≤) (Iso) (Iso) f`,
    which says that if inputs are isomorphic, the outputs are related by `≤`.
3.  **Coercion/Transitivity**: Automatic application of lemmas like
    $X \cong Y \to X \leq Y$ to switch between relation types during the walk.

## Formalized Algorithm: Generalized `cat_rw`

The following pseudo-code formalizes the recursive structural rewrite algorithm for
arbitrary relations.

```text
/--
  Attempts to rewrite `expr` using `rule` to produce a result of type `r_goal expr expr'`.
  `r_goal`: The relation required by the parent context (e.g., ≤, ≅).
  `rule`:   The rewrite rule provided by the user (e.g., h : X ≅ X').
  `expr`:   The current sub-expression being traversed.
-/
algorithm grw(r_goal, rule, expr):
  -- 1. Try to apply the rule directly to the whole expression
  if expr matches rule.lhs:
    let proof := rule.proof
    if type(proof) matches r_goal expr expr':
      return some(proof)
    else if can_coerce(type(proof), r_goal):
      return some(coerce(proof, r_goal))

  -- 2. Recursive Descent using GenCongr lemmas
  -- Fetch all lemmas tagged with @[gcongr] or similar that result in `r_goal`
  for each lemma L in find_congruence_lemmas(r_goal, expr.head):
    -- Example L: ∀ {A A' B B'}, r_α A A' → r_β B B' → r_goal (f A B) (f A' B')

    -- Attempt to match the lemma's LHS with the current expression
    if L.lhs matches expr:
      -- Create metavariables for the lemma's arguments (A, A', B, B'...)
      -- and the relation proofs (h₁, h₂...)
      let (args, relations) := instantiate_lemma(L)
      let mut rewrote := false

      -- Try to rewrite each argument relation
      for each h_i in relations:
        let r_sub := type(h_i).relation -- The relation type required for this argument
        let sub_expr := get_corresponding_subterm(expr, h_i)

        -- Recurse
        if let some(sub_proof) := grw(r_sub, rule, sub_expr):
          h_i.assign(sub_proof)
          rewrote := true
        else:
          -- If we can't rewrite this subterm, we must use reflexivity
          if let some(refl_proof) := try_refl(r_sub, sub_expr):
            h_i.assign(refl_proof)
          else:
            -- Bail out: this lemma requires a rewrite or refl that we can't provide
            rewrote := false
            break

      if rewrote:
        return some(instantiate_mvars(L.proof))

  return none
```

### Key Refinements over the Basic Algorithm:

1.  **Multimodality**: The algorithm is parameterized by `r_goal`. The relation
    required for a sub-expression (`r_sub`) may differ from `r_goal` depending on
    the `GenCongr` lemma (e.g., a lemma might lift an `Iso` into a `≤`).
2.  **Bailing Out**: The user's suggestion to "bail out" is implemented in the
    inner loop. If an argument of a congruence lemma cannot be either rewritten
    or satisfied by reflexivity, the entire lemma application is invalid and
    we must try the next one or fail.
3.  **Coercion**: Includes a `can_coerce` check. This allows the tactic to use
    an `Iso` rule even when the goal is a `≤`, provided a proof of $X \cong Y \to X \leq Y$
    exists.
4.  **Reflexivity Fallback**: For structural congruence to work, we must be able
    to "pass through" arguments that aren't being rewritten. This requires
    each relation involved to have a `refl` implementation (captured by `NPTrans`).

This algorithm is significantly more robust than "Search-and-Replace" because it
never constructs a term without having the `GenCongr` lemma to justify its
well-typedness and its relationship to the original term.
-/



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
          hᵢ = refl
      }

      if rewrote
        return some (lemma h₁ h₂ ...)
    } else
      -- consider bailing out here instead of keep trying.
  }
  return none
-/
