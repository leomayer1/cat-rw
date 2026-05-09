import Batteries.Lean.TagAttribute

open Lean

initialize catRwAttr : TagAttribute ←
  registerTagAttribute `cat_rw
    "lemmas used by the `cat_rw` tactic to rewrite goals across isomorphisms"
