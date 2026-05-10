import CatRw.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products

open CategoryTheory Limits

/- The current implementation of CatRw is rather ad-hoc.
It tries to match the left-hand-side with a number of special cases.
First it checks if LHS is of the form F.obj x.
Then it checks if LHS is of the form x ⨯ y.
Then it checks if LHS is of the form x ⨿ y.
Finally it tests a list of known lemmas.
The goal is to replace the first three steps, and to have the tactic be flexible enough
to cover the first three cases by the tagged lemmas. -/
set_option trace.CatRw true

/-
Tagging this lemma results in terms with somewhat bad definitional equalities.
Ideally, Functor.mapIso should be tagged. We aren't tagging it here because we don't
want to mess with mathlib.
-/
@[cat_rw_iso]
def obj_iso {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {x x' : C} (φ : x ≅ x') :
    F.obj x ≅ F.obj x' := F.mapIso φ

/- This example currently works by CatRw automatically testing for functor application.
The goal is to make it work because obj_iso has been tagged. -/
example {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) {x y z : C}
    (φ : x ≅ y) (ψ : y ≅ z) : F.obj x ≅ F.obj z := by
  cat_rw [φ, ψ]

@[cat_rw_iso]
def obj_iso' {C D : Type*} [Category* C] [Category* D] (F G : C ⥤ D) {x : C} (φ : F ≅ G) :
    F.obj x ≅ G.obj x := φ.app x

/- This example currently works by CatRw automatically testing for functor application and
applying natural isomorphisms. The goal is to make it work because obj_iso' has been tagged. -/
example {C D E : Type*} [Category* C] [Category* D] [Category* E] (F F' : C ⥤ D) (G G' : D ⥤ E)
    {x : C} (φ : F ≅ F') (ψ : G ≅ G') : G.obj (F.obj x) ≅ G'.obj (F'.obj x) := by
  cat_rw [φ, ψ]

@[cat_rw_iso]
noncomputable
def iso_prod_right {C : Type*} [Category* C] (x x' y : C) (φ : x ≅ x')
    [HasBinaryProduct x y] [HasBinaryProduct x' y] : x ⨯ y ≅ x' ⨯ y :=
  prod.mapIso φ (Iso.refl y)

@[cat_rw_iso]
noncomputable
def iso_prod_left {C : Type*} [Category* C] (x y y' : C) (φ : y ≅ y')
    [HasBinaryProduct x y] [HasBinaryProduct x y'] : x ⨯ y ≅ x ⨯ y' :=
  prod.mapIso (Iso.refl x) φ

@[cat_rw_iso]
noncomputable
def iso_coprod_right {C : Type*} [Category* C] (x x' y : C) (φ : x ≅ x')
    [HasBinaryCoproduct x y] [HasBinaryCoproduct x' y] : x ⨿ y ≅ x' ⨿ y :=
  coprod.mapIso φ (Iso.refl y)

@[cat_rw_iso]
noncomputable
def iso_coprod_left {C : Type*} [Category* C] (x y y' : C) (φ : y ≅ y')
    [HasBinaryCoproduct x y] [HasBinaryCoproduct x y'] : x ⨿ y ≅ x ⨿ y' :=
  coprod.mapIso (Iso.refl x) φ

/-
The tactic should recursively look for an expression matching the conclusion of the tagged lemma
in both the LHS and the RHS
-/

example {C : Type*} [Category* C] (a b c : C) (f : a ≅ b) (g : c ≅ b) : a ≅ c := by
  cat_rw [g, ←f]
