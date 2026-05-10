# GEMINI.md - Project Context

## Project Overview
`cat-rw` is a Lean 4 project that implements a category-theoretic rewrite tactic (`cat_rw`). This tactic allows users to perform rewrites using isomorphisms in category theory, similar to how the standard `rw` tactic works for equalities.

### Key Features
- **Isomorphism-based Rewriting**: Rewrites objects or goals using isomorphisms (`X ≅ Y`).
- **Recursive Traversal**: Automatically lifts isomorphisms through functors (`F.obj`), binary products (`X ⨯ Y`), and binary coproducts (`X ⨿ Y`).
- **Goal Rewriting**: Supports goals that are not isomorphisms (e.g., `IsZero X`) by using "iso-iff" lemmas (e.g., `IsZero X ↔ IsZero Y`).
- **Extensibility**: Uses attributes `@[cat_rw]` for registering new `iso_iff` lemmas and `@[cat_rw_iso]` for registering lemmas that lift isomorphisms through other structures.

### Architecture
- `CatRw/Attr.lean`: Defines the `@[cat_rw]` and `@[cat_rw_iso]` attributes.
- `CatRw/Basic.lean`: The core implementation. Contains the elaborator, recursive rewriting logic, goal-matching logic, and the `cat_rw` syntax definition.
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

### Testing and Debugging
- Tests are located in the `CatRw/` directory.
- To debug the tactic, use `set_option trace.CatRw true`. This provides detailed logs of the search process, including rule application and isomorphism lifting.

### Adding New Rewrite Rules
- **Goal Rewrites**: Tag lemmas with `@[cat_rw]` if they have the form `P X ↔ P Y` where the main argument is an isomorphism `X ≅ Y`.
- **Iso Lifting**: Tag definitions with `@[cat_rw_iso]` if they lift an isomorphism between "smaller" objects to an isomorphism between "larger" objects (e.g., `F.mapIso`).

## Key Dependencies
- **Mathlib**: The project heavily relies on Lean's Mathlib, specifically the Category Theory library (`CategoryTheory.*`).
