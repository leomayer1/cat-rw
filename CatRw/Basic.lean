import CatRw.Attr
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.NatIso
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
It captures the raw isomorphism expression and whether it is reversed.
-/
structure Rule where
  /-- The raw isomorphism expression. -/
  raw : Expr
  /-- Whether to use the symmetry of the isomorphism. -/
  isReverse : Bool
  /-- A representative source object for error messages. -/
  src_hint : Expr

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
-/
structure IffRewriteResult where
  /-- The new goal expression (e.g., `IsZero Y`). -/
  newTarget : Expr
  /--
  A function that, given a proof of `newTarget`, returns a proof of the original target.
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
-/
private def defaultIsoIffLemmas : Array Name := #[
  ``CategoryTheory.Iso.isZero_iff,
  ``CategoryTheory.Functor.preservesMonomorphisms.iso_iff,
  ``CategoryTheory.Functor.preservesEpimorphisms.iso_iff,
  ``CategoryTheory.Functor.isEquivalence_iff_of_iso,
  ``CategoryTheory.Functor.initial_natIso_iff
]

private def getIsoIffLemmas : TacticM (Array Name) := do
  let env ← getEnv
  return defaultIsoIffLemmas ++ catRwAttr.getDecls env

/-- The lemmas tagged with `@[cat_rw_iso]`. -/
private def defaultIsoMakerLemmas : Array Name := #[
  ``CategoryTheory.Functor.mapIso,
  ``CategoryTheory.Iso.app,
  ``CategoryTheory.Limits.prod.mapIso,
  ``CategoryTheory.Limits.coprod.mapIso
]

private def getIsoMakerLemmas : MetaM (Array Name) := do
  let env ← getEnv
  return defaultIsoMakerLemmas ++ catRwIsoAttr.getDecls env

/--
Extracts the source and destination objects from an isomorphism's type.
Expected type: `X ≅ Y`.
-/
private def isoEndpoints (e : Expr) : MetaM (Expr × Expr) := do
  let eType ← inferType e
  let type ← whnf eType
  match_expr type with
  | CategoryTheory.Iso _ _ X Y => return (X, Y)
  | _ => throwError "cat_rw expected an isomorphism, but{indentExpr e}\nhas type{indentExpr type}"

/--
Parses a single rewrite rule syntax into a `Rule` structure.
Handles both forward and backward (using `←`) directions.
-/
private def parseRule (stx : Syntax) : TacticM Rule := do
  let raw ← Term.elabTerm stx[1]! none
  let rawType ← inferType raw
  let (args, _, _) ← forallMetaTelescopeReducing rawType
  let rawIso := mkAppN raw args
  let (src, dst) ← isoEndpoints rawIso
  if stx[0]!.isNone then
    let src_hint ← instantiateMVars src
    return { raw, isReverse := false, src_hint }
  else
    let dst_hint ← instantiateMVars dst
    return { raw, isReverse := true, src_hint := dst_hint }

/--
Parses a sequence of rewrite rules from a `rwRuleSeq` syntax.
-/
private def parseRules : TSyntax `Lean.Parser.Tactic.rwRuleSeq → TacticM (Array Rule)
  | `(rwRuleSeq| [$rules,*]) => rules.getElems.mapM fun ruleStx => parseRule ruleStx
  | _ => throwUnsupportedSyntax

/--
Attempts to resolve all instance metavariables within an expression.
-/
private def solveInstances (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  let mvars ← getMVars e
  for mvarId in mvars do
    if !(← mvarId.isAssigned) then
      let type ← instantiateMVars (← mvarId.getType)
      if (← isClass? type).isSome then
        try
          let inst ← synthInstance type
          mvarId.assign inst
        catch _ => pure ()
  instantiateMVars e

/--
Attempts to apply a `Rule` to the entire expression `e` by creating fresh MVars.
-/
private def tryWhole (rule : Rule) (e : Expr) : MetaM (Option RewriteResult) := do
  let state ← saveState
  try
    let rawType ← inferType rule.raw
    let (args, _, _) ← forallMetaTelescopeReducing rawType
    let iso := mkAppN rule.raw args
    let type ← whnf (← inferType iso)
    match_expr type with
    | CategoryTheory.Iso _ _ X Y =>
      let (src, dst) := if rule.isReverse then (Y, X) else (X, Y)
      if ← isDefEq src e then
        let _ ← solveInstances iso
        let finalIso ← if rule.isReverse then mkAppM ``CategoryTheory.Iso.symm #[iso] else pure iso
        let finalIsoInst ← solveInstances finalIso
        let newExprInst ← solveInstances dst
        trace[CatRw] m!"tryWhole: matched {src} -> {dst}"
        return some { newExpr := newExprInst, iso := finalIsoInst }
    | _ => pure ()
    restoreState state
    return none
  catch _ =>
    restoreState state
    return none

/-- Creates a reflexive isomorphism `Iso.refl e`. -/
private def mkReflIso (e : Expr) : MetaM Expr :=
  mkAppM ``CategoryTheory.Iso.refl #[e]

/--
Tries to fill the isomorphism arguments of a lemma.
Returns true if at least one argument was rewritten.
-/
private def fillIsoArgs
    (args : Array Expr)
    (rewriter : Expr → MetaM (Option RewriteResult))
    (multi : Bool) :
    MetaM Bool := do
  let mut rewrote := false
  for arg in args do
    let argTypeRaw ← inferType arg
    let argTypeInst ← instantiateMVars argTypeRaw
    let argType ← whnf argTypeInst
    match_expr argType with
    | CategoryTheory.Iso _ _ A B =>
      let A ← instantiateMVars A
      let B ← instantiateMVars B
      if !rewrote || multi then
        if !A.isMVar then
          if let some res ← rewriter A then
            let argTypeMVar ← inferType arg
            let resIsoType ← inferType res.iso
            if ← isDefEq argTypeMVar resIsoType then
              arg.mvarId!.assign res.iso
              rewrote := true
              continue
        if !B.isMVar then
          if let some res ← rewriter B then
            let symm ← mkAppM ``CategoryTheory.Iso.symm #[res.iso]
            let argTypeMVar ← inferType arg
            let symmType ← inferType symm
            if ← isDefEq argTypeMVar symmType then
              arg.mvarId!.assign symm
              rewrote := true
              continue
      -- Fallback to refl if possible
      if !A.isMVar then
        let refl ← mkReflIso A
        let argTypeMVar ← inferType arg
        let reflType ← inferType refl
        if ← isDefEq argTypeMVar reflType then
          arg.mvarId!.assign refl
      else if !B.isMVar then
        let refl ← mkReflIso B
        let argTypeMVar ← inferType arg
        let reflType ← inferType refl
        if ← isDefEq argTypeMVar reflType then
          arg.mvarId!.assign refl
    | _ => pure ()
  return rewrote

/--
Recursively attempts to apply a rewrite rule to an expression `e`.
-/
private partial def rewriteOnce
    (rule : Rule) (e : Expr) : MetaM (Option RewriteResult) := do
  trace[CatRw] m!"rewriteOnce: rule hint ({rule.src_hint}) on {e}"
  if let some result ← tryWhole rule e then
    return some result
  for lemmaName in ← getIsoMakerLemmas do
    let state ← saveState
    try
      let info ← getConstInfo lemmaName
      let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
      let type := info.instantiateTypeLevelParams levels
      let (args, _, resultType) ← forallMetaTelescope type
      let resultTypeInst ← instantiateMVars resultType
      let resultTypeWhnf ← whnf resultTypeInst
      match_expr resultTypeWhnf with
      | CategoryTheory.Iso _ _ lhs _ =>
        if ← isDefEq lhs e then
          if ← fillIsoArgs args (rewriteOnce rule) (multi := false) then
            for arg in args do
              let mvarId := arg.mvarId!
              if !(← mvarId.isAssigned) then
                let argType ← instantiateMVars (← mvarId.getType)
                if (← isClass? argType).isSome then
                  try mvarId.assign (← synthInstance argType) catch _ => pure ()
            let optArgs ← args.mapM fun arg => do
              let argInst ← solveInstances arg
              if argInst.hasExprMVar then return none else return some argInst
            try
              let iso ← mkAppOptM lemmaName optArgs
              let endpoints ← isoEndpoints iso
              let newExprInst ← solveInstances endpoints.2
              trace[CatRw] m!"rewriteOnce: applied {lemmaName}"
              return some { newExpr := newExprInst, iso }
            catch err =>
              trace[CatRw] m!"rewriteOnce: {lemmaName} mkAppOptM failed: {err.toMessageData}"
      | _ => pure ()
      restoreState state
    catch _ => restoreState state
  trace[CatRw] m!"rewriteOnce: no rewrite found for {e}"
  return none

/--
Applies a sequence of rules to an object.
-/
private def rewriteManyRaw (rules : Array Rule) (lhs : Expr) :
    MetaM (RewriteResult × (Array <| Option <| Rule × Expr)) := do
  let mut current := lhs
  let mut iso := none
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
  let finalIso ← match iso with | some i => pure i | none => mkReflIso lhs
  trace[CatRw] m!"rewriteManyRaw: finished with newExpr = {current}, iso = {finalIso}"
  return ⟨{ newExpr := current, iso := finalIso }, errs⟩

/--
Attempts to apply a specific `iso_iff` lemma to the `target` goal in a top-down fashion.
-/
private def tryIsoIffLemmaTopDown
    (target : Expr) (rules : Array Rule) (lemmaName : Name) :
    TacticM (Option IffRewriteResult) := do
  let state ← saveState
  try
    let info ← getConstInfo lemmaName
    let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
    let type := info.instantiateTypeLevelParams levels
    let (args, _, resultType) ← forallMetaTelescope type
    let resultTypeInst ← instantiateMVars resultType
    let resultTypeWhnf ← whnf resultTypeInst
    match_expr resultTypeWhnf with
    | Iff lhs rhs =>
      let trySide (goalSide targetSide : Expr) (mkP : Expr → Expr → MetaM Expr) :
          TacticM (Option IffRewriteResult) := do
        let sideState ← saveState
        if ← isDefEq goalSide target then
          trace[CatRw] m!"matched {lemmaName} with {target}"
          let rewriter (x : Expr) : MetaM (Option RewriteResult) := do
             let (res, errs) ← rewriteManyRaw rules x
             if errs.all Option.isNone then return some res else return none
          if ← fillIsoArgs args rewriter (multi := true) then
            for arg in args do
              let mvarId := arg.mvarId!
              if !(← mvarId.isAssigned) then
                let argType ← instantiateMVars (← mvarId.getType)
                if (← isClass? argType).isSome then
                  try mvarId.assign (← synthInstance argType) catch _ => pure ()
            let optArgs ← args.mapM fun arg => do
              let argInst ← solveInstances arg
              if argInst.hasExprMVar then return none else return some argInst
            let iff ← mkAppOptM lemmaName optArgs
            let newTarget ← solveInstances targetSide
            return some { newTarget, mkProof := fun np => mkP iff np }
        restoreState sideState
        return none
      if let some res ← trySide lhs rhs (fun iff np => mkAppM ``Iff.mpr #[iff, np]) then
        return some res
      if let some res ← trySide rhs lhs (fun iff np => mkAppM ``Iff.mp #[iff, np]) then
        return some res
    | _ => pure ()
    restoreState state
    return none
  catch e =>
    trace[CatRw] m!"tryIsoIffTopDown {lemmaName} failed with error: {e.toMessageData}"
    restoreState state
    return none

/--
Iterates through all registered `iso_iff` lemmas.
-/
private def tryIsoIffLemmasTopDown (target : Expr) (rules : Array Rule) :
    TacticM (Option IffRewriteResult) := do
  for lemmaName in ← getIsoIffLemmas do
    if let some result ← tryIsoIffLemmaTopDown target rules lemmaName then
      return some result
  return none

/--
Recursively attempts to rewrite a proposition `e` using `iso_iff` lemmas.
-/
private partial def rewriteProp (rules : Array Rule) (e : Expr) :
    TacticM (Option PropRewriteResult) := do
  if (← tryIsoIffLemmasTopDown e rules).isSome then
    return none
  let result ← match_expr e with
    | And P Q =>
      if let some resP ← rewriteProp rules P then
        let newProp ← mkAppM ``And #[resP.newProp, Q]
        let iff ← mkAppM ``and_congr_left #[resP.iff]
        pure (some { newProp, iff })
      else if let some resQ ← rewriteProp rules Q then
        let newProp ← mkAppM ``And #[P, resQ.newProp]
        let iff ← mkAppM ``and_congr_right #[resQ.iff]
        pure (some { newProp, iff })
      else
        pure none
    | _ => pure none
  return result

/--
Handles the case where the goal is an isomorphism `X ≅ Y`.
-/
private def evalIsoGoal (goal : MVarId) (rules : Array Rule) (lhs rhs : Expr) : TacticM Unit := do
  trace[CatRw] m!"evalIsoGoal: rewriting {lhs} ≅ {rhs}"
  let resultLhs ← rewriteManyRaw rules lhs
  let resultRhs ← rewriteManyRaw rules rhs
  for (errL, errR) in resultLhs.snd.zip resultRhs.snd do
    if let (some (rule, currentL), some (_, currentR)) := (errL, errR) then
      throwError
        "cat_rw could not apply an isomorphism with source{indentExpr rule.src_hint}\n\
        to either{indentExpr currentL}\n\
        or{indentExpr currentR}"
  let (newL, isoL) := (resultLhs.fst.newExpr, resultLhs.fst.iso)
  let (newR, isoR) := (resultRhs.fst.newExpr, resultRhs.fst.iso)
  let mkTrans (i1 i2 : Expr) : MetaM Expr := do
    if i1.isAppOfArity ``CategoryTheory.Iso.refl 3 then return i2
    if i2.isAppOfArity ``CategoryTheory.Iso.refl 3 then return i1
    mkAppM ``CategoryTheory.Iso.trans #[i1, i2]
  let mkSymm (i : Expr) : MetaM Expr := do
    if i.isAppOfArity ``CategoryTheory.Iso.refl 3 then return i
    mkAppM ``CategoryTheory.Iso.symm #[i]
  if ← isDefEq newL newR then
    trace[CatRw] m!"evalIsoGoal: LHS and RHS matched after rewrite"
    let isoR_symm ← mkSymm isoR
    goal.assign (← mkTrans isoL isoR_symm)
    replaceMainGoal []
  else
    trace[CatRw] m!"evalIsoGoal: creating intermediate goal {newL} ≅ {newR}"
    let newTarget ← mkAppM ``CategoryTheory.Iso #[newL, newR]
    let newGoal ← mkFreshExprMVar newTarget
    let isoR_symm ← mkSymm isoR
    let mid ← mkTrans newGoal isoR_symm
    goal.assign (← mkTrans isoL mid)
    replaceMainGoal [newGoal.mvarId!]

/--
Handles the case where the goal is NOT an isomorphism.
-/
private def evalIffGoal (goal : MVarId) (rules : Array Rule) (target : Expr) : TacticM Unit := do
  trace[CatRw] m!"evalIffGoal: attempting to rewrite goal {target}"
  if let some result ← tryIsoIffLemmasTopDown target rules then
    trace[CatRw] m!"evalIffGoal: matched top-level iff lemma"
    let newGoal ← mkFreshExprMVar result.newTarget
    let proof ← result.mkProof newGoal
    goal.assign proof
    replaceMainGoal [newGoal.mvarId!]
    return
  if let some result ← rewriteProp rules target then
    trace[CatRw] m!"evalIffGoal: matched recursive prop rewrite"
    let newGoal ← mkFreshExprMVar result.newProp
    let mpr ← mkAppM ``Iff.mpr #[result.iff, newGoal]
    goal.assign mpr
    replaceMainGoal [newGoal.mvarId!]
    return
  throwError
    "cat_rw could not rewrite the goal using the registered iso-iff lemmas. \
    The goal is{indentExpr target}"

/--
Dispatches the tactic based on the goal type.
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
  let target ← getMainTarget
  let targetInst ← instantiateMVars target
  let rules ← parseRules rulesStx
  trace[CatRw] m!"evalCatRw: starting with {rules.size} rules on target {targetInst}"
  evalTarget goal rules targetInst

end CatRw

/--
`cat_rw [rules]` performs rewriting using isomorphisms in category theory.
-/
elab "cat_rw " rules:rwRuleSeq : tactic => CatRw.evalCatRw rules
