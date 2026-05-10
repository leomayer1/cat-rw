import CatRw.Attributes
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
  /-- The underlying proof of `OriginalTarget ↔ newTarget`. -/
  iffProof : Expr
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
Context for the `CatRw` tactic, threading rules and cached lemmas.
-/
structure Context where
  /-- The rewrite rules provided by the user. -/
  rules : Array Rule
  /-- Lemmas for lifting isomorphisms (tagged with `@[cat_rw_iso]`). -/
  isoMakerLemmas : Array Name
  /-- Lemmas for rewriting goals (tagged with `@[cat_rw]`). -/
  isoIffLemmas : Array Name

/-- Monad for the `CatRw` tactic. -/
abbrev CatRwM := ReaderT Context MetaM

instance : MonadBacktrack Meta.SavedState CatRwM where
  saveState := liftM (saveState : MetaM _)
  restoreState s := liftM (restoreState s : MetaM _)

/-- Fetches all `iso_iff` lemmas from the environment. -/
private def fetchIsoIffLemmas : TacticM (Array Name) := do
  let env ← getEnv
  return catRwAttr.getDecls env

/-- Fetches all `iso_maker` lemmas from the environment. -/
private def fetchIsoMakerLemmas : MetaM (Array Name) := do
  let env ← getEnv
  return catRwIsoAttr.getDecls env

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
Instantiates a lemma with fresh level metavariables and performs a telescope,
passing the arguments and the resulting type to the callback.
-/
private def withLemma (lemmaName : Name) (k : Array Expr → Expr → CatRwM (Option α)) :
    CatRwM (Option α) := do
  let info ← getConstInfo lemmaName
  let levels ← info.levelParams.mapM fun _ => mkFreshLevelMVar
  let type := info.instantiateTypeLevelParams levels
  let (args, _, resultType) ← forallMetaTelescope type
  let resultTypeWhnf ← whnf (← instantiateMVars resultType)
  k args resultTypeWhnf

/--
Finalizes the arguments for a lemma by synthesizing instances and solving metavariables.
Returns an array of optional expressions suitable for `mkAppOptM`.
-/
private def finalizeLemmaArgs (args : Array Expr) : MetaM (Array (Option Expr)) := do
  for arg in args do
    let mvarId := arg.mvarId!
    if !(← mvarId.isAssigned) then
      let argType ← instantiateMVars (← mvarId.getType)
      if (← isClass? argType).isSome then
        try mvarId.assign (← synthInstance argType) catch _ => pure ()
  args.mapM fun arg => do
    let argInst ← solveInstances arg
    if argInst.hasExprMVar then return none else return some argInst

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
    (rewriter : Expr → CatRwM (Option RewriteResult))
    (multi : Bool) :
    CatRwM Bool := do
  let mut rewrote := false
  for arg in args do
    let argType ← whnf (← instantiateMVars (← inferType arg))
    match_expr argType with
    | CategoryTheory.Iso _ _ A B =>
      let endpoints := [(A, false), (B, true)]
      for (e, reverse) in endpoints do
        let e ← instantiateMVars e
        if (!rewrote || multi) && !e.isMVar then
          if let some res ← rewriter e then
            let iso ← if reverse then mkAppM ``CategoryTheory.Iso.symm #[res.iso] else pure res.iso
            if ← isDefEq (← inferType arg) (← inferType iso) then
              arg.mvarId!.assign iso
              rewrote := true
              break
      -- Fallback to refl if no rewrite occurred for this argument
      if !(← arg.mvarId!.isAssigned) then
        let A ← instantiateMVars A
        if !A.isMVar then
          let refl ← mkReflIso A
          if ← isDefEq (← inferType arg) (← inferType refl) then
            arg.mvarId!.assign refl
        else
          let B ← instantiateMVars B
          if !B.isMVar then
            let refl ← mkReflIso B
            if ← isDefEq (← inferType arg) (← inferType refl) then
              arg.mvarId!.assign refl
    | _ => pure ()
  return rewrote

/--
Recursively attempts to apply a rewrite rule to an expression `e`.
-/
private partial def rewriteOnce
    (rule : Rule) (e : Expr) : CatRwM (Option RewriteResult) := do
  withTraceNode `CatRw (fun _ => return m!"rewriteOnce: rule hint ({rule.src_hint}) on {e}") do
  if let some result ← tryWhole rule e then
    return some result
  let ctx ← read
  for lemmaName in ctx.isoMakerLemmas do
    let state ← saveState
    try
      let res ← withLemma lemmaName fun args resultType => do
        match_expr resultType with
        | CategoryTheory.Iso _ _ lhs _ =>
          if ← isDefEq lhs e then
            if ← fillIsoArgs args (rewriteOnce rule) (multi := false) then
              let optArgs ← finalizeLemmaArgs args
              let iso ← mkAppOptM lemmaName optArgs
              let endpoints ← isoEndpoints iso
              let newExpr ← solveInstances endpoints.2
              trace[CatRw] m!"rewriteOnce: applied {lemmaName}"
              return some { newExpr, iso }
          return none
        | _ => return none
      if res.isSome then return res
      restoreState state
    catch _ => restoreState state
  trace[CatRw] m!"rewriteOnce: no rewrite found for {e}"
  return none

/--
Applies a sequence of rules to an object.
-/
private def rewriteManyRaw (lhs : Expr) :
    CatRwM (RewriteResult × (Array <| Option <| Rule × Expr)) := do
  let mut current := lhs
  let mut iso := none
  let mut errs := #[]
  let ctx ← read
  for rule in ctx.rules do
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
    (target : Expr) (lemmaName : Name) :
    CatRwM (Option IffRewriteResult) := do
  let state ← saveState
  try
    let res ← withLemma lemmaName fun args resultTypeWhnf => do
      match_expr resultTypeWhnf with
      | Iff lhs rhs =>
        let sides := [(lhs, rhs, true), (rhs, lhs, false)]
        for (goalSide, targetSide, isMpr) in sides do
          let sideState ← saveState
          if ← isDefEq goalSide target then
            trace[CatRw] m!"matched {lemmaName} with {target}"
            let rewriter (x : Expr) : CatRwM (Option RewriteResult) := do
               let (res, errs) ← rewriteManyRaw x
               if errs.all Option.isNone then return some res else return none
            if ← fillIsoArgs args rewriter (multi := true) then
              let optArgs ← finalizeLemmaArgs args
              let iffProof ← mkAppOptM lemmaName optArgs
              let newTarget ← solveInstances targetSide
              let mkProof := fun np =>
                if isMpr then mkAppM ``Iff.mpr #[iffProof, np] else mkAppM ``Iff.mp #[iffProof, np]
              return some { newTarget, iffProof, mkProof }
          restoreState sideState
        return none
      | _ => return none
    if res.isSome then return res
    restoreState state
    return none
  catch e =>
    trace[CatRw] m!"tryIsoIffTopDown {lemmaName} failed with error: {e.toMessageData}"
    restoreState state
    return none

/--
Iterates through all registered `iso_iff` lemmas.
-/
private def tryIsoIffLemmasTopDown (target : Expr) : CatRwM (Option IffRewriteResult) := do
  let ctx ← read
  for lemmaName in ctx.isoIffLemmas do
    if let some result ← tryIsoIffLemmaTopDown target lemmaName then
      return some result
  return none

/--
Recursively attempts to rewrite a proposition `e` using `iso_iff` lemmas.
-/
private partial def rewriteProp (e : Expr) : CatRwM (Option PropRewriteResult) := do
  withTraceNode `CatRw (fun _ => return m!"rewriteProp: {e}") do
  if let some res ← tryIsoIffLemmasTopDown e then
    return some { newProp := res.newTarget, iff := res.iffProof }
  match_expr e with
  | And P Q =>
    if let some resP ← rewriteProp P then
      let newProp ← mkAppM ``And #[resP.newProp, Q]
      let iff ← mkAppM ``and_congr_left #[resP.iff]
      return some { newProp, iff }
    else if let some resQ ← rewriteProp Q then
      let newProp ← mkAppM ``And #[P, resQ.newProp]
      let iff ← mkAppM ``and_congr_right #[resQ.iff]
      return some { newProp, iff }
    else
      return none
  | Or P Q =>
    if let some resP ← rewriteProp P then
      let newProp ← mkAppM ``Or #[resP.newProp, Q]
      let iff ← mkAppM ``or_congr_left #[resP.iff]
      return some { newProp, iff }
    else if let some resQ ← rewriteProp Q then
      let newProp ← mkAppM ``Or #[P, resQ.newProp]
      let iff ← mkAppM ``or_congr_right #[resQ.iff]
      return some { newProp, iff }
    else
      return none
  | Iff P Q =>
    if let some resP ← rewriteProp P then
      let newProp ← mkAppM ``Iff #[resP.newProp, Q]
      let reflQ ← mkAppM ``Iff.refl #[Q]
      let iff ← mkAppM ``iff_congr #[resP.iff, reflQ]
      return some { newProp, iff }
    else if let some resQ ← rewriteProp Q then
      let newProp ← mkAppM ``Iff #[P, resQ.newProp]
      let reflP ← mkAppM ``Iff.refl #[P]
      let iff ← mkAppM ``iff_congr #[reflP, resQ.iff]
      return some { newProp, iff }
    else
      return none
  | _ => return none

/--
Handles the case where the goal is an isomorphism `X ≅ Y`.
Returns a list of new goals.
-/
private def evalIsoGoal (goal : MVarId) (lhs rhs : Expr) : CatRwM (Array MVarId) := do
  trace[CatRw] m!"evalIsoGoal: rewriting {lhs} ≅ {rhs}"
  let resultLhs ← rewriteManyRaw lhs
  let resultRhs ← rewriteManyRaw rhs
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
    return #[]
  else
    trace[CatRw] m!"evalIsoGoal: creating intermediate goal {newL} ≅ {newR}"
    let newTarget ← mkAppM ``CategoryTheory.Iso #[newL, newR]
    let newGoal ← mkFreshExprMVar newTarget
    let isoR_symm ← mkSymm isoR
    let mid ← mkTrans newGoal isoR_symm
    goal.assign (← mkTrans isoL mid)
    return #[newGoal.mvarId!]

/--
Handles the case where the goal is NOT an isomorphism.
Returns a list of new goals.
-/
private def evalIffGoal (goal : MVarId) (target : Expr) : CatRwM (Array MVarId) := do
  trace[CatRw] m!"evalIffGoal: attempting to rewrite goal {target}"
  if let some result ← tryIsoIffLemmasTopDown target then
    trace[CatRw] m!"evalIffGoal: matched top-level iff lemma"
    let newGoal ← mkFreshExprMVar result.newTarget
    let proof ← result.mkProof newGoal
    goal.assign proof
    return #[newGoal.mvarId!]
  if let some result ← rewriteProp target then
    trace[CatRw] m!"evalIffGoal: matched recursive prop rewrite"
    let newGoal ← mkFreshExprMVar result.newProp
    let mpr ← mkAppM ``Iff.mpr #[result.iff, newGoal]
    goal.assign mpr
    return #[newGoal.mvarId!]
  throwError
    "cat_rw could not rewrite the goal using the registered iso-iff lemmas. \
    The goal is{indentExpr target}"

/--
Dispatches the tactic based on the goal type.
Returns a list of new goals.
-/
private def evalTarget (goal : MVarId) (target : Expr) : CatRwM (Array MVarId) := do
  match_expr target with
  | CategoryTheory.Iso _ _ X Y => evalIsoGoal goal X Y
  | _ =>
      let targetWhnf ← whnf target
      match_expr targetWhnf with
      | CategoryTheory.Iso _ _ X Y => evalIsoGoal goal X Y
      | _ => evalIffGoal goal target

def evalCatRw
    (rulesStx : TSyntax `Lean.Parser.Tactic.rwRuleSeq) : TacticM Unit := withMainContext do
  let goal ← getMainGoal
  let target ← getMainTarget
  let targetInst ← instantiateMVars target
  let rules ← parseRules rulesStx
  let isoMakerLemmas ← fetchIsoMakerLemmas
  let isoIffLemmas ← fetchIsoIffLemmas
  let ctx := { rules, isoMakerLemmas, isoIffLemmas }
  trace[CatRw] m!"evalCatRw: starting with {rules.size} rules on target {targetInst}"
  let newGoals ← liftMetaM <| ReaderT.run (evalTarget goal targetInst) ctx
  replaceMainGoal newGoals.toList

end CatRw

/--
`cat_rw [rules]` performs rewriting using isomorphisms in category theory.
-/
elab "cat_rw " rules:rwRuleSeq : tactic => CatRw.evalCatRw rules
