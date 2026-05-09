import Batteries.Lean.TagAttribute

open Lean

initialize catRwAttr : TagAttribute ←
  registerTagAttribute `cat_rw
    "lemmas used by the `cat_rw` tactic to rewrite goals across isomorphisms"

initialize catRwIsoAttr : TagAttribute ←
  registerTagAttribute `cat_rw_iso
    "lemmas used by the `cat_rw` tactic to lift isomorphisms through expressions"
