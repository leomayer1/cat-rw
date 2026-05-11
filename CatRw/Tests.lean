import CatRw.TagTests

open CategoryTheory Limits

set_option linter.style.setOption false
set_option trace.CatRw false
set_option CatRw.trace_iso_expr true
set_option warn.sorry false

variable {C : Type*} [Category* C] [HasProducts C] [HasBinaryCoproducts C]
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
inst✝⁵ : Category.{v_1, u_1} C
inst✝⁴ : HasProducts C
inst✝³ : HasBinaryCoproducts C
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

/-- Basic isomorphism rewrite. -/
noncomputable
example (X Y Z : C) (h : X ≅ Y) : X ⨯ Z ≅ Y ⨯ Z := by
  cat_rw [h]

/-- Goal rewrite. -/
example (X Y : C) (h : X ≅ Y) (hz : IsZero X) : IsZero Y := by
  cat_rw [← h]
  exact hz

/-- Equality rewrite (generalized). -/
example (n m : Nat) (h : n = m) : 0 + n = m := by
  cat_rw [h]
  rw [Nat.zero_add]

/-- Deeply nested binary product and coproduct rewrite. -/
noncomputable
example (X Y Z W : C) (h : X ≅ Y) (k : Z ≅ W) :
    (X ⨯ Z) ⨿ (W ⨯ Y) ≅ (Y ⨯ W) ⨿ (Z ⨯ X) := by
  cat_rw [h, h, k, k]

/-- Nested functorial rewrite. -/
example (F G : C ⥤ D) (X Y : C) (η : F ≅ G) (e : X ≅ Y) :
    F.obj X ≅ G.obj Y := by
  cat_rw [η, e]

/-- Goal rewriting with `IsZero`. -/
example (X Y : C) (h : X ≅ Y) (hz : IsZero X) : IsZero Y := by
  have : IsZero X ↔ IsZero Y := by
    cat_rw [h]
  exact this.mp hz

/-- Goal rewriting with `PreservesMonomorphisms`. -/
example (F G : C ⥤ D) (h : F ≅ G) (hm : F.PreservesMonomorphisms) : G.PreservesMonomorphisms := by
  have : F.PreservesMonomorphisms ↔ G.PreservesMonomorphisms := by
    cat_rw [h]
  exact this.mp hm

/-- Multiple rule application in a single call. -/
example (X Y Z : C) (h1 : X ≅ Y) (h2 : Y ≅ Z) : X ≅ Z := by
  cat_rw [h1, h2]

/-- Rewriting with natural isomorphisms and app. -/
example (F G : C ⥤ D) (X : C) (η : F ≅ G) : F.obj X ≅ G.obj X := by
  cat_rw [η]

/-- Complex composition of products and symmetry. -/
noncomputable
example (X Y Z : C) : (X ⨯ Y) ⨯ Z ≅ Z ⨯ (Y ⨯ X) := by
  cat_rw [prod.associator]
  -- Target: X ⨯ (Y ⨯ Z) ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.braiding X (Y ⨯ Z)]
  -- Target: (Y ⨯ Z) ⨯ X ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.associator]
  -- Target: Y ⨯ Z ⨯ X ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.braiding Y (Z ⨯ X)]
  -- Target: (Z ⨯ X) ⨯ Y ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.associator]
  -- Target: Z ⨯ X ⨯ Y ≅ Z ⨯ (Y ⨯ X)
  cat_rw [prod.braiding X Y]

/-- Testing symmetry flag in rules. -/
example (X Y : C) (h : X ≅ Y) : Y ≅ X := by
  cat_rw [← h]

/-- Mixed products and coproducts with instances. -/
noncomputable
example (X Y Z : C) : (X ⨿ Y) ⨯ Z ≅ (Y ⨿ X) ⨯ Z := by
  cat_rw [coprod.braiding X Y]

/-- Test case from FlashyExample.lean (making it concrete) -/
noncomputable
example (G : C ⥤ D) (X Y : C) [PreservesLimit (pair X Y) G] :
    G.obj (X ⨯ Y) ≅ G.obj X ⨯ G.obj Y := by
  cat_rw [PreservesLimitPair.iso G X Y]

/-- Double negation (symm of symm). -/
example (X Y : C) (h : X ≅ Y) : X ≅ Y := by
  cat_rw [← (h.symm)]

/-- Identity functor test. -/
example (X : C) : (𝟭 C).obj X ≅ X := by
  apply Iso.refl

example (ha : a ≅ a') : IsZero (a ⨿ b) := by
  cat_rw [ha]
  guard_target = IsZero (a' ⨿ b)
  sorry

noncomputable example (ha : a ≅ a') (hb : b ≅ b') : a ⨯ b ⨯ c ≅ a' ⨯ b' ⨯ c := by
  cat_rw [ha, hb]

example (φ : F ≅ G) (ha : a ≅ a') :
    IsZero (F.obj (a ⨯ b ⨯ a)) := by
  cat_rw [ha, ha]
  guard_target =  IsZero (F.obj (a' ⨯ b ⨯ a'))
  sorry


section ZeroTest
variable (X Y : C) (φ : X ≅ Y)

example (h : Limits.IsZero Y) : Limits.IsZero X := by
    cat_rw [φ]
    exact h

example (h : IsZero Y) : IsZero X := by
    rw [Iso.isZero_iff φ]
    exact h

example (F G : C ⥤ D) (φ : F ≅ G) [G.PreservesMonomorphisms] :
        F.PreservesMonomorphisms := by
    cat_rw [φ]

example (h : IsZero (F.obj Y)) : IsZero (F.obj X) := by
    let φ : F.obj X ≅ F.obj Y := F.mapIso φ
    rw [Iso.isZero_iff φ]
    exact h

example {E : Type*} [Category* E] (G : D ⥤ E) (h : IsZero (G.obj (F.obj Y))) :
        IsZero (G.obj (F.obj X)) := by
    let φ : G.obj (F.obj X) ≅ G.obj (F.obj Y) := G.mapIso (F.mapIso φ)
    rw [Iso.isZero_iff φ]
    exact h

example (G : C ⥤ D) (h : IsZero (G.obj X)) (ψ : F ≅ G) : IsZero (F.obj X) := by
    let φ : F.obj X ≅ G.obj X := ψ.app X
    rw [Iso.isZero_iff φ]
    exact h

end ZeroTest
