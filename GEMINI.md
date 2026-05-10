# GEMINI.md - Project Context

## Project Overview
`cat-rw` is a Lean 4 project that implements a generalized category-theoretic rewrite tactic (`cat_rwv2`). This tactic allows users to perform rewrites using not only isomorphisms in category theory (`X ≅ Y`) but any registered binary relation (e.g., `=`, `↔`).

### Key Features
- **Generalized Rewriting**: Rewrites objects or goals using any registered relation.
- **RelInfo Registration**: Support for relations is managed via `RelInfo`, which specifies the relation name, reflexivity, and optional symmetry and transitivity proofs.
- **Recursive Structural Traversal**: Automatically propagates relations through expressions using "iso-maker" lemmas (tagged `@[cat_rw_iso]`) or general congruence lemmas.
- **Goal Rewriting**: Supports goals that are binary relations by rewriting both sides, or non-relation goals by using transformation lemmas (tagged `@[cat_rw]`).
- **Symmetric Relation Handling**: Automatically handles symmetry for registered relations, allowing rules to be applied in reverse (using `←`).
- **Direction Awareness**: The direction of the rewrite rule is strictly respected and handled correctly.
- **Hierarchical Tracing**: Provides detailed trace output for debugging the `grw` algorithm.

### Architecture
- `CatRw/Attr.lean`: Defines the `@[cat_rw]` and `@[cat_rw_iso]` attributes.
- `CatRw/Attributes.lean`: Registers standard Mathlib lemmas for isomorphisms and functors.
- `CatRw/BasicV2.lean`: The core implementation of the V2 tactic.
    - **`RelInfo`**: Structure for registering binary relations and their properties.
    - **`relExt`**: Environment extension for managing the map of registered relations.
    - **`grw`**: The core generalized rewrite function that recursively applies rules and lifting lemmas.
    - **`evalTargetV2`**: Dispatches the tactic based on the goal type (Relation vs. Prop).
- `CatRw.lean`: The main library entry point.

## Building and Running
The project uses the `lake` build system.

- **Build**: `lake build` (this also runs all tests)
- **Clean**: `lake clean`
- **Update Dependencies**: `lake update`

## Development Conventions

### Coding Style
- Follows standard Lean 4 and Mathlib conventions.
- Uses the `CatRw` namespace.
- Uses `elab` for the main tactic implementation.

### Rewriting Logic
- **Generalized Congruence**: The tactic follows the principles outlined in `CatRw/General.lean`, treating isomorphisms as a special case of a transitive relation.
- **Bidirectional Relation Rewriting**: For goals of the form `R A B` where `R` is a registered relation, the tactic attempts to rewrite both `A` and `B` independently.
- **Prop Rewriting**: For goals that are not registered relations, it treats the goal as a predicate and attempts to rewrite it using `Iff`.
- **Symmetry and Transitivity**: The tactic uses the `symm` and `trans` proofs provided in `RelInfo` to assemble the final proof of the rewrite.

### Testing and Debugging
- Tests are located in `CatRw/V2Tests.lean` and `CatRw/ComprehensiveTests.lean`.
- Use `set_option trace.CatRw true` to see the `grw` search process.

### Registering New Relations
- Use `CatRw.registerRel` or modify `initialRelMap` in `BasicV2.lean` to add support for new relations.
- Relations must at least provide a reflexivity lemma.

### Adding New Rewrite Rules
- **Lifting Lemmas**: Tag with `@[cat_rw_iso]` if the lemma lifts a relation from subterms to the whole term (e.g., `prod.mapIso`).
- **Transformation Lemmas**: Tag with `@[cat_rw]` if the lemma provides an `Iff` between two different predicates based on a relation between their arguments (e.g., `IsZero.iso_iff`).

## Key Dependencies
- **Mathlib**: Specifically `CategoryTheory.*` and `Tactic.*`.
