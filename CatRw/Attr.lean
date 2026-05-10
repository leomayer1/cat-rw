import Batteries.Lean.TagAttribute

open Lean

initialize catRwAttr : TagAttribute ←
  registerTagAttribute `cat_rw
    "lemmas used by the `cat_rw` tactic to rewrite goals across isomorphisms"

initialize catRwIsoAttr : TagAttribute ←
  registerTagAttribute `cat_rw_iso
    "lemmas used by the `cat_rw` tactic to lift isomorphisms through expressions"

register_option CatRw.trace_iso_expr : Bool := {
  defValue := false
  descr := "print the isomorphism produced by cat_rw"
}
