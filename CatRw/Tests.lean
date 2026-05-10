import CatRw.TagTests

open CategoryTheory Limits

variable {C : Type*} [Category* C] [HasProducts C]
variable {D : Type*} [Category* D] [HasProducts D]
variable {E : Type*} [Category* E]
variable {F G : C ⥤ D} {H K : D ⥤ E}
variable (a a' b b' c : C)

/-
  Very basic tests
-/
example (f : a ≅ b) (g : b ≅ c) : a ≅ c := by
  cat_rw [f, g]

example (f : a ≅ b) (g : b ≅ c) : a ≅ c := by
  cat_rw? [f, g]

noncomputable example (φ : a ≅ b) : a ⨯ c ≅ c ⨯ b := by
  cat_rw [φ, prod.braiding b c]

/- An example of what we would want cat-rw to be able to solve -/
noncomputable
example (f : a ≅ a') (g : b ≅ b') : (a ⨯ b) ⨯ c ≅ (b' ⨯ c) ⨯ a' :=
  let φ₁ : (a ⨯ b) ⨯ c ≅ (a' ⨯ b) ⨯ c :=
    prod.mapIso (prod.mapIso f (Iso.refl _)) (Iso.refl _)
  let φ₂ : (a' ⨯ b) ⨯ c ≅ (a' ⨯ b') ⨯ c :=
    prod.mapIso (prod.mapIso (Iso.refl _) g) (Iso.refl _)
  let φ₃ : (a' ⨯ b') ⨯ c ≅ (b' ⨯ a') ⨯ c :=
    prod.mapIso (prod.braiding _ _) (Iso.refl _)
  let φ₄ : (b' ⨯ a') ⨯ c ≅ b' ⨯ (a' ⨯ c) :=
    prod.associator _ _ _
  let φ₅ : b' ⨯ (a' ⨯ c) ≅ b' ⨯ (c ⨯ a') :=
    prod.mapIso (Iso.refl _) (prod.braiding _ _)
  let φ₆ : b' ⨯ (c ⨯ a') ≅ (b' ⨯ c) ⨯ a' :=
    (prod.associator _ _ _).symm
  φ₁ ≪≫ φ₂ ≪≫ φ₃ ≪≫ φ₄ ≪≫ φ₅ ≪≫ φ₆

noncomputable
example (f : a ≅ a') (g : b ≅ b') : (a ⨯ b) ⨯ c ≅ (b' ⨯ c) ⨯ a' := by
  cat_rw [← f, ← g, prod.braiding a b, prod.associator, prod.braiding a c]

example (f : a ≅ a') (α : F ≅ G) (β : H ≅ K) (g : G.obj a' ≅ G.obj b) :
    K.obj (G.obj a) ≅ H.obj (F.obj b) := by
  cat_rw [f, α, β, g]
