import CatRw.Attr
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic
import Lean.Elab.Tactic

open CategoryTheory Limits
open Lean Meta Elab Tactic
open Lean.Parser.Tactic (rwRuleSeq)

/-
The `CatRw` namespace contains the core logic for the `cat_rw` tactic,
which performs rewriting using isomorphisms in category theory.
-/
namespace CatRw

initialize registerTraceClass `CatRw

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
The result of an `Iff` rewrite.
It contains the new goal expression and a function to construct the proof of the
original goal from a proof of the new goal.
-/
structure IffRewriteResult where
  /-- The new goal expression (e.g., `IsZero Y`). -/
  newTarget : Expr
  /--
  A function that, given a proof of `newTarget`, returns a proof of the original target.
  Proof constructor : `newTarget_proof → originalTarget_proof`.
  -/
  mkProof : Expr → MetaM Expr

/--
A `PropRewriteResult` is used when rewriting a proposition into an equivalent one.
-/
structure PropRewriteResult where
  /-- The new proposition. -/
  newProp : Expr
  /-- The proof of `e ↔ newProp`. -/
  iff : Expr

/--
The lemmas tagged with `@[cat_rw]`.

Each tagged lemma should accept an isomorphism as its main explicit argument
and return an iff whose left or right side is the current goal.
-/
private def defaultIsoIffLemmas : Array Name := #[
  ``CategoryTheory.Iso.isZero_iff,
  ``CategoryTheory.Functor.preservesMonomorphisms.iso_iff,
  ``CategoryTheory.Functor.preservesEpimorphisms.iso_iff,
  ``CategoryTheory.Functor.isEquivalence_iff_of_iso,
  ``CategoryTheory.Functor.initial_natIso_iff,
]

private def getIsoIffLemmas : TacticM (Array Name) := do
  return defaultIsoIffLemmas ++ catRwAttr.getDecls (← getEnv)

/-- The lemmas tagged with `@[cat_rw_iso]`. -/
private def getIsoMakerLemmas : MetaM (Array Name) := do
  return catRwIsoAttr.getDecls (← getEnv)

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
  catch err =>
    trace[CatRw] m!"tryWhole {rule.src} -> {rule.dst} on {e} failed: {err.toMessageData}"
    restoreState state
    return none

/-- Creates a reflexive isomorphism `Iso.refl e`. -/
private def mkReflIso (e : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Iso.refl #[e]

/-- Creates a functor application `F.obj X`. -/
private def mkFunctorObj (F X : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Functor.obj #[F, X]

private def getProdInst (X Y : Expr) : MetaM Expr := do
  withReducibleAndInstances <|
    synthInstance (← mkAppM ``CategoryTheory.Limits.HasBinaryProduct #[X, Y])

private def getCoprodInst (X Y : Expr) : MetaM Expr := do
  withReducibleAndInstances <|
    synthInstance (← mkAppM ``CategoryTheory.Limits.HasBinaryCoproduct #[X, Y])

/-- Creates a product of two objects `X ⨯ Y`. -/
private def mkProd (X Y : Expr) : MetaM Expr := do
  let inst ← getProdInst X Y
  mkAppOptM ``CategoryTheory.Limits.prod #[none, none, some X, some Y, some inst]

/-- Creates a coproduct of two objects `X ⨿ Y`. -/
private def mkCoprod (X Y : Expr) : MetaM Expr := do
  let inst ← getCoprodInst X Y
  mkAppOptM ``CategoryTheory.Limits.coprod #[none, none, some X, some Y, some inst]

/--
Try a tagged iso-maker lemma on a recursively produced isomorphism.

The lemma is accepted only when applying it to `result.iso` produces an isomorphism
whose source is definitionally equal to the expression currently being rewritten.
If the lemma produces the opposite direction, we use its symmetry.
-/
private def tryIsoMakerLemma
    (e : Expr) (result : RewriteResult) (lemmaName : Name) :
    MetaM (Option RewriteResult) := do
  let state ← saveState
  try
    let iso ← mkAppM lemmaName #[result.iso]
    let (src, dst) ← isoEndpoints iso
    let endpointState ← saveState
    if ← withReducibleAndInstances <| isDefEq src e then
      return some {
        newExpr := ← instantiateMVars dst
        iso := ← instantiateMVars iso
      }
    else
      restoreState endpointState
      if ← withReducibleAndInstances <| isDefEq dst e then
        return some {
          newExpr := ← instantiateMVars src
          iso := ← mkAppM ``CategoryTheory.Iso.symm #[← instantiateMVars iso]
        }
      else
        restoreState state
        return none
  catch err =>
    trace[CatRw] m!"tryIsoMaker {lemmaName} failed on {e}: {err.toMessageData}"
    restoreState state
    return none

private def tryIsoMakerLemmas (e : Expr) (result : RewriteResult) :
    MetaM (Option RewriteResult) := do
  for lemmaName in ← getIsoMakerLemmas do
    if let some lifted ← tryIsoMakerLemma e result lemmaName then
      return some lifted
  return none

/--
Recursively attempts to apply a rewrite rule to an expression `e`.
It checks:
1. The expression itself.
2. If it's a functor application `F.obj X`, it tries to rewrite `F` or `X`.
3. If a tagged `@[cat_rw_iso]` lemma can lift an iso through the expression.
4. If it's a binary product `X ⨯ Y`, it tries to rewrite `X` or `Y`.
5. If it's a binary coproduct `X ⨿ Y`, it tries to rewrite `X` or `Y`.
-/
private partial def rewriteOnce
    (rule : Rule) (e : Expr) : MetaM (Option RewriteResult) := do
  trace[CatRw] m!"rewrite rule ({rule.src} -> {rule.dst}) on {e}"
  if let some result ← tryWhole rule e then
    return some result
  let args := e.getAppArgs
  /-
    Check if `e` is an application of `CategoryTheory.Functor.obj`.
  -/
  if e.isAppOfArity ``CategoryTheory.Functor.obj 6 then
    let F := args[4]! -- F : C ⥤ D
    let X := args[5]! -- X : C
    if let some result ← tryWhole rule F then
      trace[CatRw] m!"Functor.app {result.iso} {X}"
      return some {
        newExpr := ← mkFunctorObj result.newExpr X
        iso := ← mkAppM ``CategoryTheory.Iso.app #[result.iso, X]
      }
    if let some result ← rewriteOnce rule X then
      trace[CatRw] m!"Functor.mapIso {F} {result.iso}"
      return some {
        newExpr := ← mkFunctorObj F result.newExpr
        iso := ← mkAppM ``CategoryTheory.Functor.mapIso #[F, result.iso]
      }
  /-
    Check if `e` is an application of `CategoryTheory.Limits.prod`.
  -/
  if e.isAppOfArity ``CategoryTheory.Limits.prod 5 then
    let X := args[2]! -- X : C
    let Y := args[3]! -- Y : C
    let sourceInst := args[4]!
    if let some result ← rewriteOnce rule X then
      trace[CatRw] m!"prod.mapIso {result.iso} rfl({Y})"
      let targetInst ← getProdInst result.newExpr Y
      let reflY ← mkReflIso Y
      return some {
        newExpr := ← mkProd result.newExpr Y
        iso := ← mkAppOptM ``CategoryTheory.Limits.prod.mapIso
          #[none, none, some X, some Y, some result.newExpr, some Y,
            some sourceInst, some targetInst, some result.iso, some reflY]
      }
    if let some result ← rewriteOnce rule Y then
      trace[CatRw] m!"prod.mapIso rfl({X}) {result.iso}"
      let targetInst ← getProdInst X result.newExpr
      let reflX ← mkReflIso X
      return some {
        newExpr := ← mkProd X result.newExpr
        iso := ← mkAppOptM ``CategoryTheory.Limits.prod.mapIso
          #[none, none, some X, some Y, some X, some result.newExpr,
            some sourceInst, some targetInst, some reflX, some result.iso]
      }
  /-
    Check if `e` is an application of `CategoryTheory.Limits.coprod`.
  -/
  if e.isAppOfArity ``CategoryTheory.Limits.coprod 5 then
    let X := args[2]! -- X : C
    let Y := args[3]! -- Y : C
    let sourceInst := args[4]!
    if let some result ← rewriteOnce rule X then
      trace[CatRw] m!"coprod.mapIso {result.iso} rfl({Y})"
      let targetInst ← getCoprodInst result.newExpr Y
      let reflY ← mkReflIso Y
      return some {
        newExpr := ← mkCoprod result.newExpr Y
        iso := ← mkAppOptM ``CategoryTheory.Limits.coprod.mapIso
          #[none, none, some X, some Y, some result.newExpr, some Y,
            some sourceInst, some targetInst, some result.iso, some reflY]
      }
    if let some result ← rewriteOnce rule Y then
      trace[CatRw] m!"coprod.mapIso rfl({X}) {result.iso}"
      let targetInst ← getCoprodInst X result.newExpr
      let reflX ← mkReflIso X
      return some {
        newExpr := ← mkCoprod X result.newExpr
        iso := ← mkAppOptM ``CategoryTheory.Limits.coprod.mapIso
          #[none, none, some X, some Y, some X, some result.newExpr,
            some sourceInst, some targetInst, some reflX, some result.iso]
      }
  if !(e.isAppOfArity ``CategoryTheory.Functor.obj 6) &&
      !(e.isAppOfArity ``CategoryTheory.Limits.prod 5) &&
      !(e.isAppOfArity ``CategoryTheory.Limits.coprod 5) then
    if let some arg := args.back? then
      let state ← saveState
      try
        if let some result ← rewriteOnce rule arg then
          if let some lifted ← tryIsoMakerLemmas e result then
            return some lifted
        restoreState state
      catch err =>
        trace[CatRw]
          m!"tagged iso-maker search failed for argument {arg} of {e}: {err.toMessageData}"
        restoreState state
  trace[CatRw] m!"rwOnce return none"
  return none

/--
Applies a sequence of rules to the left-hand side of an isomorphism.
Transitions from `lhs` to a new expression by composing the isomorphisms.
-/
private def rewriteManyRaw (rules : Array Rule) (lhs : Expr) :
    TacticM (RewriteResult × (Array <| Option <| Rule × Expr)) := do
  let mut current := lhs -- current : Expr (the object being rewritten)
  let mut iso := none -- iso : Option Expr (the accumulated isomorphism)
  let mut errs := #[]
  for rule in rules do
    if let some result ← rewriteOnce rule current then
      if let some i := iso then
        iso := some <| ← mkAppM ``CategoryTheory.Iso.trans #[i, result.iso]
      else
        iso := some <| result.iso
      current := result.newExpr
      errs := errs.push none
    else
      errs := errs.push <| some ⟨rule, current⟩
  trace[CatRw] m!"iso = {iso}"
  return ⟨{ newExpr := current, iso := iso.getD (← mkReflIso lhs) }, errs⟩

private def rethrowFirst (arr : Array <| Option <| (Rule × Expr)) : TacticM Unit := do
  for err in arr do
    if let some (rule, current) := err then
      throwError
          "cat_rw could not apply an isomorphism with source{indentExpr rule.src}\n\
          to{indentExpr current}"
  return ()

private def rewriteMany (rules : Array Rule) (lhs : Expr) :
    TacticM RewriteResult := do
  let result ← rewriteManyRaw rules lhs
  rethrowFirst result.snd
  return result.fst

/--
Attempts to apply a specific `iso_iff` lemma to the `target` goal in a top-down fashion.
It unifies the target with one side of the `Iff` and then tries to rewrite the "subject"
of the isomorphism argument.
-/
private def tryIsoIffLemmaTopDown
    (target : Expr) (rules : Array Rule) (lemmaName : Name) : TacticM (Option IffRewriteResult) := do
  let state ← saveState
  try
    let info ← getConstInfo lemmaName
    let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
    let type := info.instantiateTypeLevelParams levels
    let (args, _, resultType) ← forallMetaTelescope type
    let resultType ← instantiateMVars resultType
    let resultType ← whnf resultType
    let res ← match_expr resultType with
    | Iff lhs rhs =>
        let trySide (goalSide targetSide : Expr) (mkP : Expr → Expr → MetaM Expr) : TacticM (Option IffRewriteResult) := do
          let sideState ← saveState
          let goalSide ← instantiateMVars goalSide
          if ← isDefEq goalSide target then
            trace[CatRw] m!"matched {lemmaName} with {target}"
            for arg in args do
              let argType ← instantiateMVars (← inferType arg)
              let argType ← whnf argType
              let resInner ← match_expr argType with
              | CategoryTheory.Iso _ _ X _ =>
                  let X ← instantiateMVars X
                  trace[CatRw] m!"attempting to rewrite subject {X}"
                  let resultMany ← rewriteManyRaw rules X
                  if resultMany.snd.all Option.isNone then
                    trace[CatRw] m!"subject rewritten to {resultMany.fst.newExpr}"
                    if ← isDefEq arg resultMany.fst.iso then
                      let iff := mkAppN (Lean.mkConst lemmaName levels) args
                      let iff ← instantiateMVars iff
                      let newTarget ← instantiateMVars targetSide
                      pure (some {
                        newTarget
                        mkProof := fun newProof => mkP iff newProof
                      })
                    else pure none
                  else
                    trace[CatRw] m!"failed to rewrite subject {X}"
                    pure none
              | _ => pure none
              if let some r := resInner then return some r
            restoreState sideState
            return none
          else
            restoreState sideState
            return none
        if let some resSide ← trySide lhs rhs (fun iff np => mkAppM ``Iff.mpr #[iff, np]) then pure (some resSide)
        else if let some resSide ← trySide rhs lhs (fun iff np => mkAppM ``Iff.mp #[iff, np]) then pure (some resSide)
        else pure none
    | _ => pure none
    if let some r := res then return some r
    restoreState state
    return none
  catch e =>
    trace[CatRw] m!"tryIsoIffTopDown {lemmaName} failed with error: {e.toMessageData}"
    restoreState state
    return none

/--
Iterates through all registered `iso_iff` lemmas to see if any can be used to
rewrite the current `target` in a top-down fashion.
-/
private def tryIsoIffLemmasTopDown (target : Expr) (rules : Array Rule) : TacticM (Option IffRewriteResult) := do
  for lemmaName in ← getIsoIffLemmas do
    if let some result ← tryIsoIffLemmaTopDown target rules lemmaName then
      return some result
  return none

/--
Recursively attempts to rewrite a proposition `e` using `iso_iff` lemmas.
Handles logical connectives and applies top-down isomorphism matching.
-/
private partial def rewriteProp (rules : Array Rule) (e : Expr) : TacticM (Option PropRewriteResult) := do
  if (← tryIsoIffLemmasTopDown e rules).isSome then
    -- For now, we only support top-level evalIffGoal which uses tryIsoIffLemmasTopDown directly.
    return none
  -- Recurse into logical connectives
  let result ← match_expr e with
    | And P Q =>
      if let some resP ← rewriteProp rules P then
        pure (some {
          newProp := ← mkAppM ``And #[resP.newProp, Q]
          iff := ← mkAppM ``and_congr_left #[resP.iff]
        })
      else if let some resQ ← rewriteProp rules Q then
        pure (some {
          newProp := ← mkAppM ``And #[P, resQ.newProp]
          iff := ← mkAppM ``and_congr_right #[resQ.iff]
        })
      else
        pure none
    | _ => pure none
  return result

/--
Handles the case where the goal is an isomorphism `X ≅ Y`.
Rewrites both `X` and `Y` using the provided rules and updates the goal.
Bidirectional rewriting is supported: rules that cannot be applied to the LHS
are tried on the RHS. The two rewrites are then joined in the middle.
-/
private def evalIsoGoal (goal : MVarId) (rules : Array Rule) (lhs rhs : Expr) : TacticM Unit := do
  -- Rewrite the left-hand side and right-hand side independently.
  let resultLhs ← rewriteManyRaw rules lhs
  let resultRhs ← rewriteManyRaw rules rhs
  -- Check for consistency: a rule must apply to at least one side.
  -- We traverse the error lists (which match the sequence of rules).
  for (errL, errR) in resultLhs.snd.zip resultRhs.snd do
    if let (some (rule, currentL), some (_, currentR)) := (errL, errR) then
      throwError
        "cat_rw could not apply an isomorphism with source{indentExpr rule.src}\n\
        to either{indentExpr currentL}\n\
        or{indentExpr currentR}"
  let (newL, isoL) := (resultLhs.fst.newExpr, resultLhs.fst.iso)
  let (newR, isoR) := (resultRhs.fst.newExpr, resultRhs.fst.iso)
  -- Optimization: helper to avoid composing with `Iso.refl`.
  let mkTrans (i1 i2 : Expr) : MetaM Expr := do
    if i1.isAppOfArity ``CategoryTheory.Iso.refl 3 then return i2
    if i2.isAppOfArity ``CategoryTheory.Iso.refl 3 then return i1
    mkAppM ``CategoryTheory.Iso.trans #[i1, i2]
  -- Optimization: helper to avoid `Iso.symm` of `Iso.refl`.
  let mkSymm (i : Expr) : MetaM Expr := do
    if i.isAppOfArity ``CategoryTheory.Iso.refl 3 then return i
    mkAppM ``CategoryTheory.Iso.symm #[i]
  -- If the rewritten objects are definitionally equal, we can close the goal.
  -- The proof is `isoL ≪≫ isoR.symm`.
  if ← isDefEq newL newR then
    let isoR_symm ← mkSymm isoR
    goal.assign (← mkTrans isoL isoR_symm)
    replaceMainGoal []
  else
    -- Otherwise, we create a intermediate goal `newL ≅ newR`.
    -- The original goal `lhs ≅ rhs` is solved by `isoL ≪≫ (newGoal ≪≫ isoR.symm)`.
    let newTarget ← mkAppM ``CategoryTheory.Iso #[newL, newR]
    let newGoal ← mkFreshExprMVar newTarget
    let isoR_symm ← mkSymm isoR
    let mid ← mkTrans newGoal isoR_symm
    goal.assign (← mkTrans isoL mid)
    replaceMainGoal [newGoal.mvarId!]

/--
Handles the case where the goal is NOT an isomorphism (e.g., `IsZero X`).
Attempts to find a rewrite using `iso_iff` lemmas.
-/
private def evalIffGoal (goal : MVarId) (rules : Array Rule) (target : Expr) : TacticM Unit := do
  if let some result ← tryIsoIffLemmasTopDown target rules then
    let newGoal ← mkFreshExprMVar result.newTarget
    goal.assign (← result.mkProof newGoal)
    replaceMainGoal [newGoal.mvarId!]
    return
  -- Fallback to recursive Prop rewriting (e.g. for And)
  if let some result ← rewriteProp rules target then
    let newGoal ← mkFreshExprMVar result.newProp
    goal.assign (← mkAppM ``Iff.mpr #[result.iff, newGoal])
    replaceMainGoal [newGoal.mvarId!]
    return
  throwError
    "cat_rw could not rewrite the goal using the registered iso-iff lemmas. \
    The goal is{indentExpr target}"

/--
Dispatches the tactic based on whether the goal is an isomorphism or
another type of expression that might be rewritable via `iso_iff`.
-/
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

/--
`cat_rw [rules]` performs rewriting using isomorphisms in category theory.
It works on goals of the form `X ≅ Y` by rewriting `X` using the provided
isomorphisms and composing them.
-/
elab "cat_rw " rules:rwRuleSeq : tactic => CatRw.evalCatRw rules
