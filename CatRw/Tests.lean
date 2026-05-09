import CatRw.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.ObjectProperty.Basic

open CategoryTheory Limits

variable (C : Type*) [Category* C] [HasProducts C]
variable (D : Type*) [Category* D] [HasProducts D]
variable (E : Type*) [Category* E] [HasProducts E]
variable (F G : C ⥤ D) (H K : D ⥤ E)
variable (a a' b b' c : C)
variable (x y z : D)

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
  cat_rw [ha]

example (h : F ≅ G) : F.obj a ≅ G.obj a := by
  cat_rw [h]

example (ha : a ≅ a') (h : F ≅ G) : F.obj a ≅ G.obj a' := by
  cat_rw [ha, h]

example (h : a ≅ b) (h' : b ≅ c) : a ≅ c := by
  cat_rw [h, h']

example (ha : a ≅ a') (hb : b ≅ b') : a ≅ b := by
  symm
  cat_rw [hb]
  symm
  sorry

/- Still doesn't work with cat_rw -/
noncomputable
example : (a ⨯ b) ⨯ c ≅ (c ⨯ b) ⨯ a := by
  --cat_rw [prod.associator, prod.braiding a b, prod.braiding a' c, ←prod.associator]
  sorry


/-
  Wish list:
  1) Work with the notation ←h, so that if the goal is a ≅ c, and h : b ≅ c, after cat_rw [←h] the
    goal should be a ≅ b
-/

example (h₁ : F ≅ G) (h₂ : H ≅ K) (h : a ≅ a') : K.obj (G.obj a') ≅ H.obj (F.obj a) := by
  cat_rw [h.symm, h₁.symm, h₂.symm]

example (h₁ : F ≅ G) (h₂ : F.obj a ≅ x) (h₃ : F.obj b ≅ x) (h₄ : H ≅ K) : (H.obj (F.obj a)) ≅ K.obj (G.obj b) := by
  let h : G ≅ F := h₁.symm
  cat_rw [h₁]

def iso₁ (ha : a ≅ a') (h : F ≅ G) : F.obj a ≅ G.obj a' := by
  cat_rw [h, ha]

def iso₂ (ha : a ≅ a') (h : F ≅ G) : F.obj a ≅ G.obj a' := by
  cat_rw [ha, h]

example (ha : a ≅ a') (h : F ≅ G) : iso₁ C D F G a a' ha h = iso₂ C D F G a a' ha h := by
  delta iso₁ iso₂
  ext
  simp

infix:10 " === " => CategoryTheory.IsIsomorphic

#check CategoryTheory.IsIsomorphic

@[gcongr]
def objIso (ha : a === a') : F.obj a === F.obj a' := sorry

@[gcongr]
def appIso (h : F === G) : F.obj a === G.obj a := sorry


variable {a b c d n : ℤ}
