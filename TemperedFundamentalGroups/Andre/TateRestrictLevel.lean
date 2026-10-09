/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.RamifiedQuadraticGal
import TemperedFundamentalGroups.Andre.QuadraticLevel
import TemperedFundamentalGroups.Andre.TateRestrictSigma
import TemperedFundamentalGroups.Tempered.Category

/-!
# The level of the restricted Tate object (Blueprint §10.3.8, `v(q) = 1`, B3e)

Let `(x, y) ∈ R²` satisfy `y² + xy = x³ + ϖ b₄ x + ϖ b₆` (`b₄, b₆ ∈ O`, `ϖ` a uniformizer). Over
`K' = K(√ϖ)` this is a Tate equation with `π = √ϖ`. The **restricted level** has:

* the level `B = R[t]/(t² - ϖ)` with `H = ⟨σ⟩`, `σ(t) = -t` (`QuadraticLevel.level`);
* the model `modelO`: the Tate model over `O'` presented over `O`;
* `j = jO`: the point `[x : y : t]` (`κ : K(√ϖ) → B`, `√ϖ ↦ t`);
* `ρ(σ)`: the involution `ρ'` of the Tate model transported to `modelO`.
-/

universe u

open CategoryTheory AlgebraicGeometry Polynomial IsLocalRing SemistableReduction.ProjScheme

namespace TemperedFundamentalGroups.TateRestrict

open RamifiedQuadratic SemistableReduction.W10Apply Pi1.Orbifold

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)
  (R : Type u) [CommRing R] [Algebra K R]

/-- `c = ϖ ∈ R`. -/
abbrev cR : R := algebraMap K R ϖ

/-- The level ring `R[t]/(t² - ϖ)`. -/
abbrev BR : Type u := QuadraticLevel.B (cR (ϖ := ϖ) R)

example : IsScalarTower K R (BR (ϖ := ϖ) R) := inferInstance

lemma t_sq : QuadraticLevel.x (cR (ϖ := ϖ) R) ^ 2 = algebraMap K (BR (ϖ := ϖ) R) ϖ := by
  rw [QuadraticLevel.x_sq, IsScalarTower.algebraMap_apply K R (BR (ϖ := ϖ) R)]

/-- **`κ : K(√ϖ) → B`, `√ϖ ↦ t`.** -/
def κ : K' ϖ →ₐ[K] BR (ϖ := ϖ) R := liftK' hϖ _ (t_sq R)

lemma κ_s : κ hϖ R (s ϖ) = QuadraticLevel.x (cR (ϖ := ϖ) R) := liftK'_s hϖ _ _

/-! ### The involution of `B` -/

lemma σB_x : QuadraticLevel.σ (cR (ϖ := ϖ) R) (QuadraticLevel.x (cR (ϖ := ϖ) R)) =
    -QuadraticLevel.x (cR (ϖ := ϖ) R) := QuadraticLevel.σ_x _

lemma σB_κ (z : K' ϖ) :
    QuadraticLevel.σ (cR (ϖ := ϖ) R) (κ hϖ R z) = κ hϖ R (σK hϖ z) := by
  have : ((QuadraticLevel.σ (cR (ϖ := ϖ) R)).toAlgHom.restrictScalars K).comp (κ hϖ R) =
      (κ hϖ R).comp (σK hϖ).toAlgHom := by
    refine RamifiedQuadratic.algHom_ext ?_
    change QuadraticLevel.σ _ (κ hϖ R (s ϖ)) = κ hϖ R (σK hϖ (s ϖ))
    rw [κ_s, σK_s, map_neg, κ_s, σB_x]
  exact AlgHom.congr_fun this z

lemma σB_symm (b : BR (ϖ := ϖ) R) :
    (QuadraticLevel.σ (cR (ϖ := ϖ) R)).symm b = QuadraticLevel.σ (cR (ϖ := ϖ) R) b := by
  apply (QuadraticLevel.σ (cR (ϖ := ϖ) R)).injective
  rw [AlgEquiv.apply_symm_apply, QuadraticLevel.σ_σ]

include hϖ in
lemma isUnit_t : IsUnit (QuadraticLevel.x (cR (ϖ := ϖ) R)) := by
  have hϖ0 : (ϖ : K) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
  have : IsUnit (QuadraticLevel.x (cR (ϖ := ϖ) R) ^ 2) := by
    rw [t_sq]
    exact (isUnit_iff_ne_zero.2 hϖ0).map _
  exact (isUnit_pow_iff two_ne_zero).1 this

variable [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]

/-- `O' → B`. -/
def φB : O' ϖ →+* BR (ϖ := ϖ) R := (κ hϖ R : K' ϖ →+* BR (ϖ := ϖ) R).comp (O' ϖ).subtype

lemma φB_sO : φB hϖ R (sO ϖ) = QuadraticLevel.x (cR (ϖ := ϖ) R) := κ_s hϖ R

lemma φB_algebraMap (o : O) :
    φB hϖ R (algebraMap O (O' ϖ) o) = algebraMap K (BR (ϖ := ϖ) R) o :=
  (κ hϖ R).commutes (o : K)

lemma σB_φB (o : O' ϖ) :
    QuadraticLevel.σ (cR (ϖ := ϖ) R) (φB hϖ R o) = φB hϖ R (σO hϖ o) :=
  σB_κ hϖ R o

variable (b₄ b₆ : O) {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))

include heqR in
lemma equation_B :
    algebraMap R (BR (ϖ := ϖ) R) y ^ 2 + algebraMap R (BR (ϖ := ϖ) R) x *
        algebraMap R (BR (ϖ := ϖ) R) y =
      algebraMap R (BR (ϖ := ϖ) R) x ^ 3 +
        φB hϖ R (sO ϖ ^ 2 * algebraMap O (O' ϖ) b₄) * algebraMap R (BR (ϖ := ϖ) R) x +
        φB hϖ R (sO ϖ ^ 2 * algebraMap O (O' ϖ) b₆) := by
  have h := congrArg (algebraMap R (BR (ϖ := ϖ) R)) heqR
  simp only [map_add, map_mul, map_pow] at h ⊢
  rw [φB_sO, φB_algebraMap, φB_algebraMap, t_sq]
  simp only [IsScalarTower.algebraMap_apply K R (BR (ϖ := ϖ) R)] at h ⊢
  exact h

/-! ### Generators of `O'` over `O` -/

variable [CharZero K]

instance : IsDiscreteValuationRing (O' ϖ) := isDiscreteValuationRing_OE O _

variable (ϖ) in
/-- The number of generators of `O'` over `O`. -/
def rG : ℕ := (exists_generators O (K' ϖ)).choose

variable (ϖ) in
/-- Generators of `O'` over `O`. -/
def θG : Fin (rG ϖ) → O' ϖ := fun i ↦
  ⟨(exists_generators O (K' ϖ)).choose_spec.choose i,
    (exists_generators O (K' ϖ)).choose_spec.choose_spec.2.1 i⟩

lemma θG_ne_zero (i : Fin (rG ϖ)) : ((θG ϖ i : O' ϖ) : K' ϖ) ≠ 0 :=
  (exists_generators O (K' ϖ)).choose_spec.choose_spec.1 i

lemma θG_isIntegral (i : Fin (rG ϖ)) : IsIntegral O (θG ϖ i) := by
  have h := (exists_generators O (K' ϖ)).choose_spec.choose_spec.2.2.1 i
  let f : O' ϖ →ₐ[O] K' ϖ :=
    { (O' ϖ).subtype with commutes' := fun _ ↦ rfl }
  exact (isIntegral_algHom_iff f Subtype.val_injective).1 h

lemma θG_gen (y : O' ϖ) :
    y ∈ Subring.closure (((algebraMap O (O' ϖ)).range : Set (O' ϖ)) ∪ Set.range (θG ϖ)) := by
  have h := (exists_generators O (K' ϖ)).choose_spec.choose_spec.2.2.2 y.2
  have hmap : (Subring.closure (((algebraMap O (O' ϖ)).range : Set (O' ϖ)) ∪
      Set.range (θG ϖ))).map (O' ϖ).subtype =
      Subring.closure (Set.range (algebraMap O (K' ϖ)) ∪
        Set.range (exists_generators O (K' ϖ)).choose_spec.choose) := by
    rw [RingHom.map_closure, Set.image_union]
    congr 1
    congr 1
    · ext z
      constructor
      · rintro ⟨_, ⟨o, rfl⟩, rfl⟩; exact ⟨o, rfl⟩
      · rintro ⟨o, rfl⟩; exact ⟨_, ⟨o, rfl⟩, rfl⟩
    · ext z
      constructor
      · rintro ⟨_, ⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨_, ⟨i, rfl⟩, rfl⟩
  rw [← hmap] at h
  obtain ⟨y', hy', e⟩ := h
  rwa [show y' = y from Subtype.ext e] at hy'


/-! ### The level with the model -/

variable [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄)
  (algebraMap O (O' ϖ) b₆)))]

include hϖ in
lemma sO_ne_zero : sO ϖ ≠ 0 := (irreducible_sqrt hϖ).ne_zero

/-- **The model**: the Tate model over `O'` with `π = √ϖ`, presented over `O`. -/
abbrev modelR : TemperedFundamentalGroups.ModelCode O :=
  modelO O (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (θG ϖ) θG_ne_zero
    (sO_ne_zero hϖ)

/-- The isomorphism of the model with the projective `O'`-model. -/
abbrev isoR := modelIsoO O (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (θG ϖ)
  θG_ne_zero θG_isIntegral θG_gen (sO_ne_zero hϖ)

include heqR in
/-- **The point** `j = [x : y : t] : Spec B ⟶` (model). -/
def jR : Spec (CommRingCat.of (BR (ϖ := ϖ) R)) ⟶ (modelR hϖ b₄ b₆).scheme :=
  jO O (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (θG ϖ) θG_ne_zero
    θG_isIntegral θG_gen (sO_ne_zero hϖ) (φB hϖ R) (equation_B hϖ R b₄ b₆ heqR)
    (by rw [φB_sO]; exact isUnit_t hϖ R)

/-- The involution of the `O'`-model. -/
abbrev ρR' := ρ' (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (σO hϖ) (σO_sO hϖ)
  (σO_algebraMap hϖ b₄) (σO_algebraMap hϖ b₆) (σO_σO hϖ) (sO_ne_zero hϖ)

/-- **The involution of the model** over `O`. -/
def ρσ : Aut (modelR hϖ b₄ b₆).scheme where
  hom := (isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ ≫ (isoR hϖ b₄ b₆).inv
  inv := (isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ ≫ (isoR hϖ b₄ b₆).inv
  hom_inv_id := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% ρ'_ρ', Iso.hom_inv_id]
  inv_hom_id := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% ρ'_ρ', Iso.hom_inv_id]

lemma ρσ_mul : ρσ hϖ b₄ b₆ * ρσ hϖ b₄ b₆ = 1 := by
  ext1
  rw [Aut.Aut_mul_def, Iso.trans_hom]
  change (ρσ hϖ b₄ b₆).hom ≫ (ρσ hϖ b₄ b₆).inv = 𝟙 _
  exact (ρσ hϖ b₄ b₆).hom_inv_id

lemma ρσ_toSpec : (ρσ hϖ b₄ b₆).hom ≫ (modelR hϖ b₄ b₆).toSpec = (modelR hϖ b₄ b₆).toSpec := by
  have h := modelIsoO_toSpec O (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (θG ϖ)
    θG_ne_zero θG_isIntegral θG_gen (sO_ne_zero hϖ)
  dsimp only [ρσ]
  simp only [Category.assoc]
  have hs : (σO hϖ).comp (algebraMap O (O' ϖ)) = algebraMap O (O' ϖ) :=
    RingHom.ext (σO_algebraMap hϖ)
  rw [← h, Iso.inv_hom_id_assoc, reassoc_of% ρ'_toSpec, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hs]

include heqR in
lemma ρσ_j : Spec.map (CommRingCat.ofHom
      ((QuadraticLevel.σ (cR (ϖ := ϖ) R)).toRingEquiv.symm : BR (ϖ := ϖ) R →+* BR (ϖ := ϖ) R)) ≫
        jR hϖ R b₄ b₆ heqR = jR hϖ R b₄ b₆ heqR ≫ (ρσ hϖ b₄ b₆).hom := by
  have e : ((QuadraticLevel.σ (cR (ϖ := ϖ) R)).toRingEquiv.symm :
      BR (ϖ := ϖ) R →+* BR (ϖ := ϖ) R) = (QuadraticLevel.σ (cR (ϖ := ϖ) R) : _ →+* _) :=
    RingHom.ext (σB_symm R)
  rw [e]
  change Spec.map _ ≫ TateNormal.jChart _ _ _ _ _ _ _ ≫ _ =
    (TateNormal.jChart _ _ _ _ _ _ _ ≫ _) ≫ (isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ ≫ _
  rw [Category.assoc, Iso.inv_hom_id_assoc, ← Category.assoc,
    SpecMap_σB_jChart (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (σO hϖ)
      (σO_sO hϖ) (σO_algebraMap hϖ b₄) (σO_algebraMap hϖ b₆) (σO_σO hϖ) (sO_ne_zero hϖ)
      (φB hϖ R) (equation_B hϖ R b₄ b₆ heqR) (by rw [φB_sO]; exact isUnit_t hϖ R)
      (QuadraticLevel.σ (cR (ϖ := ϖ) R) : _ →+* _) (σB_φB hϖ R)
      ((QuadraticLevel.σ _).commutes x) ((QuadraticLevel.σ _).commutes y), Category.assoc]

/-! ### The level -/

variable (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A]

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] in
include K in
lemma isUnit_two : IsUnit (2 : R) := by
  have h : IsUnit (2 : K) := isUnit_iff_ne_zero.2 two_ne_zero
  have := h.map (algebraMap K R)
  rwa [map_ofNat] at this

omit [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero K] in
include hϖ in
lemma isUnit_cR : IsUnit (cR (ϖ := ϖ) R) :=
  (isUnit_iff_ne_zero.2 fun h ↦ hϖ.ne_zero (Subtype.ext h)).map _

/-- The level `(R[t]/(t² - ϖ), ⟨σ⟩)`. -/
abbrev levelR : FiniteLevel R A :=
  QuadraticLevel.level (isUnit_two (K := K) R) (isUnit_cR hϖ R) A

open Classical in
/-- The action on `{1, σ}`. -/
def ρfun (g : SemilinearAut R A (BR (ϖ := ϖ) R)) : Aut (modelR hϖ b₄ b₆).scheme :=
  if g = 1 then 1 else ρσ hϖ b₄ b₆

lemma ρfun_mul {g g' : SemilinearAut R A (BR (ϖ := ϖ) R)}
    (hg : g = 1 ∨ g = QuadraticLevel.σS (cR (ϖ := ϖ) R) A)
    (hg' : g' = 1 ∨ g' = QuadraticLevel.σS (cR (ϖ := ϖ) R) A) :
    ρfun hϖ R b₄ b₆ A (g * g') = ρfun hϖ R b₄ b₆ A g * ρfun hϖ R b₄ b₆ A g' := by
  classical
  have hss := QuadraticLevel.σS_mul_self (cR (ϖ := ϖ) R) A
  by_cases hσ : QuadraticLevel.σS (cR (ϖ := ϖ) R) A = 1
  · have h1 : g = 1 := hg.elim id (fun h ↦ h.trans hσ)
    have h1' : g' = 1 := hg'.elim id (fun h ↦ h.trans hσ)
    simp [ρfun, h1, h1']
  · rcases hg with rfl | rfl <;> rcases hg' with rfl | rfl
    · simp [ρfun]
    · simp [ρfun]
    · simp [ρfun]
    · simp only [ρfun, hss, hσ, ↓reduceIte]
      exact (ρσ_mul hϖ b₄ b₆).symm

/-- **The action of `H = ⟨σ⟩` on the model.** -/
def ρH : (levelR (hϖ := hϖ) (R := R) (A := A)).H →* Aut (modelR hϖ b₄ b₆).scheme where
  toFun g := ρfun hϖ R b₄ b₆ A g.1
  map_one' := if_pos rfl
  map_mul' g g' := ρfun_mul hϖ R b₄ b₆ A (QuadraticLevel.eq_one_or_eq_σS _ A g.2)
    (QuadraticLevel.eq_one_or_eq_σS _ A g'.2)

omit [Subsingleton A] in
lemma ρfun_toSpec (g : SemilinearAut R A (BR (ϖ := ϖ) R)) :
    (ρfun hϖ R b₄ b₆ A g).hom ≫ (modelR hϖ b₄ b₆).toSpec = (modelR hϖ b₄ b₆).toSpec := by
  classical
  unfold ρfun
  split_ifs
  · exact Category.id_comp _
  · exact ρσ_toSpec hϖ b₄ b₆

omit [Subsingleton A] in
include heqR in
lemma ρfun_j {g : SemilinearAut R A (BR (ϖ := ϖ) R)}
    (hg : g = 1 ∨ g = QuadraticLevel.σS (cR (ϖ := ϖ) R) A) :
    Spec.map (CommRingCat.ofHom (g.σ.symm : BR (ϖ := ϖ) R →+* BR (ϖ := ϖ) R)) ≫
      jR hϖ R b₄ b₆ heqR = jR hϖ R b₄ b₆ heqR ≫ (ρfun hϖ R b₄ b₆ A g).hom := by
  classical
  rcases hg with rfl | rfl
  · simp only [ρfun, ↓reduceIte]
    change Spec.map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
    rw [Spec.map_id, Category.id_comp, Category.comp_id]
  · unfold ρfun
    split_ifs with h
    · have h2 := congrArg SemilinearAut.σ h
      change (QuadraticLevel.σ (cR (ϖ := ϖ) R)).toRingEquiv = RingEquiv.refl _ at h2
      have e : ((QuadraticLevel.σS (cR (ϖ := ϖ) R) A).σ.symm :
          BR (ϖ := ϖ) R →+* BR (ϖ := ϖ) R) = RingHom.id _ := by
        change ((QuadraticLevel.σ (cR (ϖ := ϖ) R)).toRingEquiv.symm :
          BR (ϖ := ϖ) R →+* BR (ϖ := ϖ) R) = _
        rw [h2]; rfl
      rw [e]
      change Spec.map (𝟙 _) ≫ _ = _ ≫ 𝟙 _
      rw [Spec.map_id, Category.id_comp, Category.comp_id]
    · exact ρσ_j hϖ R b₄ b₆ heqR

include heqR in
lemma jR_toSpec : jR hϖ R b₄ b₆ heqR ≫ (modelR hϖ b₄ b₆).toSpec =
    Spec.map (CommRingCat.ofHom
      (levelStructureMap O R A (levelR (hϖ := hϖ) (R := R) (A := A)))) := by
  rw [jR, jO_toSpec]
  congr 2
  refine RingHom.ext fun o ↦ ?_
  rw [RingHom.comp_apply, φB_algebraMap, IsScalarTower.algebraMap_apply K R]
  rfl

include heqR in
/-- **The level of the restricted Tate object.** -/
def levelM : Level O R A where
  L := levelR (hϖ := hϖ) (R := R) (A := A)
  c := modelR hϖ b₄ b₆
  j := jR hϖ R b₄ b₆ heqR
  j_toSpec := jR_toSpec hϖ R b₄ b₆ heqR A
  ρ := ρH hϖ R b₄ b₆ A
  ρ_toSpec g := ρfun_toSpec hϖ R b₄ b₆ A g.1
  ρ_j g := ρfun_j hϖ R b₄ b₆ heqR A (QuadraticLevel.eq_one_or_eq_σS _ A g.2)

end

end TemperedFundamentalGroups.TateRestrict
