import CatRw.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.ObjectProperty.Basic

open CategoryTheory Limits

variable {C : Type*} [Category* C] [HasProducts C]
variable {D : Type*} [Category* D]
variable {F G : C ⥤ D}
variable (a a' b b' c : C)

#check a ⨯ a'
#check prod.mapIso
#check prod.braiding
#check prod.associator

/- An example of what we would want cat-rw to be able to solve -/
noncomputable
example (ha : a ≅ a') (hb : b ≅ b') : (a ⨯ b) ⨯ c ≅ (b' ⨯ c) ⨯ a' := by
  let φ₁ : (a ⨯ b) ⨯ c ≅ (a' ⨯ b) ⨯ c :=
    prod.mapIso (prod.mapIso ha (Iso.refl _)) (Iso.refl _)
  let φ₂ : (a' ⨯ b) ⨯ c ≅ (a' ⨯ b') ⨯ c :=
    prod.mapIso (prod.mapIso (Iso.refl _) hb) (Iso.refl _)
  let φ₃ : (a' ⨯ b') ⨯ c ≅ (b' ⨯ a') ⨯ c :=
    prod.mapIso (prod.braiding _ _) (Iso.refl _)
  let φ₄ : (b' ⨯ a') ⨯ c ≅ b' ⨯ (a' ⨯ c) :=
    prod.associator _ _ _
  let φ₅ : b' ⨯ (a' ⨯ c) ≅ b' ⨯ (c ⨯ a') :=
    prod.mapIso (Iso.refl _) (prod.braiding _ _)
  let φ₆ : b' ⨯ (c ⨯ a') ≅ (b' ⨯ c) ⨯ a' :=
    (prod.associator _ _ _).symm
  exact φ₁ ≪≫ φ₂ ≪≫ φ₃ ≪≫ φ₄ ≪≫ φ₅ ≪≫ φ₆

/- Want to simply be able to call
noncomputable
example (ha : a ≅ a') (hb : b ≅ b') : (a ⨯ b) ⨯ c ≅ (b' ⨯ c) ⨯ a' := by
  cat_rw [ha, hb, prod.braiding a' b', prod.associator, prod.braiding a' c, ←prod.associator]
-/

/- A more basic example of what we want cat-rw to do -/
example (ha : a ≅ a') : F.obj a ≅ F.obj a' := by
  exact F.mapIso ha

/-
example (ha : a ≅ a') : F.obj a ≅ F.obj a' := by
  cat_rw [ha]
-/

example (ha : a ≅ a') : F.obj a ≅ F.obj a' := by
  cat_rw [ha]

example (h : F ≅ G) : F.obj a ≅ G.obj a := by
  exact h.app a
/-
example (h : F ≅ G) : F.obj a ≅ G.obj a := by
  cat_rw [h]
-/

example (h : F ≅ G) : F.obj a ≅ G.obj a := by
  cat_rw [h]

example (ha : a ≅ a') (h : F ≅ G) : F.obj a ≅ G.obj a' := by
  cat_rw [h, ha]

def iso₁ (ha : a ≅ a') (h : F ≅ G) : F.obj a ≅ G.obj a' := by
  cat_rw [h, ha]

def iso₂ (ha : a ≅ a') (h : F ≅ G) : F.obj a ≅ G.obj a' := by
  cat_rw [ha, h]

example (ha : a ≅ a') (h : F ≅ G) : iso₁ a a' ha h = iso₂ a a' ha h := by
  delta iso₁ iso₂
  ext
  simp

@[gcongr]
def gcong_obj (ha : a ≅ a') : F.obj a ≅ F.obj a' := by
  cat_rw [ha]

#check Mathlib.Tactic.GCongr.rel_imp_rel
