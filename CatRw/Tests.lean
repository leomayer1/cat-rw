import CatRw.TagTests

open CategoryTheory Limits

set_option linter.style.setOption false
set_option trace.CatRw false
set_option CatRw.trace_iso_expr true
set_option warn.sorry false

variable {C : Type*} [Category* C] [HasProducts C]
variable {D : Type*} [Category* D] [HasProducts D]
variable {E : Type*} [Category* E]
variable {F G : C ⥤ D} {H K : D ⥤ E}
variable (a a' b b' c : C)

/-
  Very basic tests
-/
example (h : a ≅ b) (h' : b ≅ c) : a ≅ c := by
  cat_rw [h, h']


/- An example of what we would want cat-rw to be able to solve -/
noncomputable
example (ha : a ≅ a') (hb : b ≅ b') : (a ⨯ b) ⨯ c ≅ (b' ⨯ c) ⨯ a' :=
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
  φ₁ ≪≫ φ₂ ≪≫ φ₃ ≪≫ φ₄ ≪≫ φ₅ ≪≫ φ₆

noncomputable
example (ha : a ≅ a') (hb : b ≅ b') : (a ⨯ b) ⨯ c ≅ (b' ⨯ c) ⨯ a' := by
  cat_rw [← ha, ← hb, prod.braiding a b, prod.associator, prod.braiding a c, prod.associator]

example (ha : a ≅ a') (hF : F ≅ G) (hH : H ≅ K) (h₂ : G.obj a' ≅ G.obj b) :
    K.obj (G.obj a) ≅ H.obj (F.obj b) := by
  cat_rw [ha, h₂, hF, hH]

/-- Test `at` location. -/
noncomputable
example (X Y Z : C) (h : X ≅ Y) (hl : X ⨯ Z ≅ Z) : Y ⨯ Z ≅ Z := by
  cat_rw [h] at hl
  exact hl

/-- Test `occs`. -/
noncomputable
example (X Y : C) (h : X ≅ Y) : (X ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X := by
  -- Should rewrite only the first X on the LHS
  cat_rw (config := { occs := .pos [3] }) [h]
  guard_target = (Y ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X
  admit

noncomputable
example (X Y : C) (h : X ≅ Y) : (X ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X := by
  -- Should rewrite only the second X on the LHS
  cat_rw (config := { occs := .pos [2] }) [h]
  guard_target = (X ⨯ Y) ⨯ X ≅ (X ⨯ X) ⨯ X
  admit

noncomputable
example (X Y : C) (h : X ≅ Y) : (X ⨯ X) ⨯ X ≅ (X ⨯ X) ⨯ X := by
  -- Should rewrite only the third X on the LHS
  cat_rw (config := { occs := .pos [1] }) [h]
  guard_target = (X ⨯ X) ⨯ Y ≅ (X ⨯ X) ⨯ X
  admit


/--
error: Tactic `cat_rw` failed: tactic 'cat_rw' failed, rule Z -> X did not match any location

C : Type u_1
inst✝⁴ : Category.{v_1, u_1} C
inst✝³ : HasProducts C
D : Type u_2
inst✝² : Category.{v_2, u_2} D
inst✝¹ : HasProducts D
E : Type u_3
inst✝ : Category.{v_3, u_3} E
F G : C ⥤ D
H K : D ⥤ E
a a' b b' c X Y Z : C
fail : Z ≅ X
⊢ X ≅ Y
-/
#guard_msgs in
example (X Y Z : C) (fail : Z ≅ X) : X ≅ Y := by
  cat_rw [← fail, fail, fail, ← fail]
