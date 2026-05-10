import Lean.Attributes
import Lean.ScopedEnvExtension

open Lean

/--
A `simp`-style attribute for collecting declaration names.

This is backed by a `SimpleScopedEnvExtension`, like `simp`, rather than by
Lean's built-in `TagAttribute`. The latter is intentionally limited to tagging
declarations in the module where they are defined, but `cat_rw` should support
project-local attributes on imported mathlib declarations.
-/
structure CatRwAttribute where
  attr : AttributeImpl
  ext : SimpleScopedEnvExtension Name NameSet
  deriving Inhabited

def mkCatRwAttribute (attrName : Name) (attrDescr : String)
    (ext : SimpleScopedEnvExtension Name NameSet)
    (validate : Name → AttrM Unit := fun _ => pure ())
    (ref : Name := by exact decl_name%) : IO AttributeImpl := do
  let attrImpl : AttributeImpl := {
    ref := ref
    name := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterCompilation
    add := fun decl stx kind => do
      Attribute.Builtin.ensureNoArgs stx
      discard <| getConstInfo decl
      validate decl
      ext.add decl kind
    erase := fun decl => do
      modifyEnv fun env => ext.modifyState env fun decls => decls.erase decl
  }
  registerBuiltinAttribute attrImpl
  return attrImpl

def registerCatRwAttribute (attrName : Name) (attrDescr : String)
    (validate : Name → AttrM Unit := fun _ => pure ())
    (ref : Name := by exact decl_name%) : IO CatRwAttribute := do
  let ext : SimpleScopedEnvExtension Name NameSet ← registerSimpleScopedEnvExtension {
    name := attrName
    initial := {}
    addEntry := fun decls decl => decls.insert decl
  }
  let attrImpl ← mkCatRwAttribute attrName attrDescr ext validate ref
  return { attr := attrImpl, ext := ext }

namespace CatRwAttribute

def getDecls (attr : CatRwAttribute) (env : Environment) : Array Name :=
  attr.ext.getState env |>.toArray.qsort Name.quickLt

end CatRwAttribute

initialize catRwAttr : CatRwAttribute ←
  registerCatRwAttribute `cat_rw
    "lemmas used by the `cat_rw` tactic to rewrite goals across isomorphisms"

initialize catRwIsoAttr : CatRwAttribute ←
  registerCatRwAttribute `cat_rw_iso
    "lemmas used by the `cat_rw` tactic to lift isomorphisms through expressions"
