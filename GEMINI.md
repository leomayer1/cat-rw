# GEMINI.md - Project Context

## Project Overview
`cat-rw` is a Lean 4 project that implements a category-theoretic rewrite tactic (`cat_rw`). This tactic allows users to perform rewrites using isomorphisms in category theory, similar to how the standard `rw` tactic works for equalities.

### Key Features
- **Isomorphism-based Rewriting**: Rewrites objects or goals using isomorphisms (`X ≅ Y`).
- **Recursive Traversal**: Automatically lifts isomorphisms through functors (`F.obj`), binary products (`X ⨯ Y`), and binary coproducts (`X ⨿ Y`).
- **Goal Rewriting**: Supports goals that are not isomorphisms (e.g., `IsZero X`) by using "iso-iff" lemmas (e.g., `IsZero X ↔ IsZero Y`).
- **Extensibility**: Uses attributes `@[cat_rw]` for registering new `iso_iff` lemmas and `@[cat_rw_iso]` for registering lemmas that lift isomorphisms through other structures.
- **Efficient State Management**: Uses a custom monad `CatRwM` to cache lemma lookups and minimize environment accesses.
- **Hierarchical Tracing**: Provides detailed, structured trace output for debugging complex rewrite chains.

### Architecture
- `CatRw/Attr.lean`: Defines the `@[cat_rw]` and `@[cat_rw_iso]` attributes.
- `CatRw/Basic.lean`: The core implementation.
    - **`CatRwM`**: A `ReaderT` monad that threads the execution context (rules, cached lemmas) and supports backtracking for speculative matching.
    - **Recursive Rewriting**: Logic for traversing expressions and applying isomorphisms or lifting lemmas.
    - **Goal Dispatch**: Handles `Iso` goals via bidirectional rewriting and non-`Iso` goals via top-down `iso-iff` application.
- `CatRw.lean`: The main library entry point, importing all components.

## Building and Running
The project uses the `lake` build system.

- **Build**: `lake build` (this also runs all tests)
- **Clean**: `lake clean`
- **Update Dependencies**: `lake update`

## Development Conventions

### Coding Style
- Follows standard Lean 4 and Mathlib conventions.
- Uses the `CatRw` namespace for tactic implementation.
- Uses `elab` for the main tactic implementation to allow for complex matching and error reporting.

### Rewriting Logic
- **Bidirectional Rewriting**: For goals of the form `X ≅ Y`, the tactic attempts to apply rules to both the LHS and RHS, effectively joining them in the middle.
- **Top-Down Goal Rewriting**: For non-isomorphism goals, it searches for registered `iso_iff` lemmas that can transform the goal into an equivalent one involving a rewritable object.
- **Instance Resolution**: Proactively resolves category-theoretic instances (e.g., `HasBinaryProduct`) during the rewrite process to ensure concrete results.

### Testing and Debugging
- Tests are located in the `CatRw/` directory.
- To debug the tactic, use `set_option trace.CatRw true`. This provides a hierarchical view of the search process, showing which lemmas were attempted and where rewrites succeeded (✅️) or failed (❌️).

### Adding New Rewrite Rules
- **Goal Rewrites**: Tag lemmas with `@[cat_rw]` if they have the form `P X ↔ P Y` where the main argument is an isomorphism `X ≅ Y`.
- **Iso Lifting**: Tag definitions with `@[cat_rw_iso]` if they lift an isomorphism between "smaller" objects to an isomorphism between "larger" objects (e.g., `F.mapIso`).

## Key Dependencies
- **Mathlib**: The project heavily relies on Lean's Mathlib, specifically the Category Theory library (`CategoryTheory.*`).
