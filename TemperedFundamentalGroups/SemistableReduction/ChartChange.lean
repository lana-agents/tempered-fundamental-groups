/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeCount

/-!
# Changes of coordinates of `C(x)` preserving the Gauss point

Blueprint §9.12, O12 / R5. Let `K₁`, `K₂` be finite extensions of `C(x)` and `φ : K₁ ≃+* K₂` a ring
isomorphism which is semilinear over a `C`-automorphism `σ` of `C(x)` preserving the Gauss
valuation `w_{0,1}` (`φ (σ ψ • 1) = ψ • 1`). Then:

* `extEquiv`: the extensions of `w_{0,1}` correspond (`(extEquiv w) ∘ φ = w`);
* `card_ext_eq`, `gsum_eq`, `card_zeros_eq`: their number, the genera of their residue curves and
  the numbers of zeros of corresponding reductions agree;
* if moreover the coordinates are related by `x₂ = φ (u x₁ + β)` (`|u| = 1`, `|β| ≤ 1`), the reduced
  charts at `x` agree (`isLocalIso_one`), with the same local `δ`-invariants at corresponding
  points (`tot0_eq`, `mem_iff_mem_trI_red`).

Instances: compositions of affine twists (`Aff 0 c' (Aff b d F)` and `Aff b (d c') F`), translations
(`K` and `Aff β 1 K`, `|β| ≤ 1`), and the inversion (`Inv c K` and `Aff 0 c K`).
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal

namespace SemistableReduction

namespace ChartChange

open GaussFibre ChartLocal DeltaCount FundamentalInequality GaussStability AffineTwist

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-! ### Zeros along isomorphisms of function fields -/

section Zeros

variable {κ κ' : Type*} [Field κ] [Field κ']
  [Algebra (IsLocalRing.ResidueField (HenselComplete.integers C)) κ]
  [Algebra (IsLocalRing.ResidueField (HenselComplete.integers C)) κ']
  [IsCurveFunctionField (IsLocalRing.ResidueField (HenselComplete.integers C)) κ]
  [IsCurveFunctionField (IsLocalRing.ResidueField (HenselComplete.integers C)) κ']

lemma card_zeros_map (e : κ ≃ₐ[𝓀] κ') (x : κ) :
    (PlaceNorm.zeros 𝓀 (e x)).card = (PlaceNorm.zeros 𝓀 x).card := by
  refine Finset.card_bij (fun Q _ ↦ Q.map e.symm) (fun Q hQ ↦ ?_) (fun Q _ Q' _ h ↦
    CurvePlace.map_injective e.symm h) (fun Q hQ ↦ ⟨Q.map e, ?_, ?_⟩)
  · rw [PlaceNorm.mem_zeros] at hQ ⊢
    rwa [CurvePlace.mem_map_V, AlgEquiv.symm_symm, map_inv₀]
  · rw [PlaceNorm.mem_zeros] at hQ ⊢
    rwa [CurvePlace.mem_map_V, ← map_inv₀, AlgEquiv.symm_apply_apply]
  · exact CurvePlace.map_symm_map e Q

end Zeros

/-! ### Automorphisms of `C(x)` preserving the Gauss point -/

section Ext

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra (RatFunc C) K₁] [Algebra (RatFunc C) K₂]
  (σ : RatFunc C ≃ₐ[C] RatFunc C) (hσ : ∀ ψ, gauss1 C (σ ψ) = gauss1 C ψ) (φ : K₁ ≃+* K₂)
  (he : ∀ ψ, φ (algebraMap (RatFunc C) K₁ (σ ψ)) = algebraMap (RatFunc C) K₂ ψ)

include hσ he in
omit [IsAlgClosed C] hσ [IsUltrametricDist C] in
lemma he_symm (ψ : RatFunc C) :
    φ.symm (algebraMap (RatFunc C) K₂ ψ) = algebraMap (RatFunc C) K₁ (σ ψ) := by
  rw [← he, RingEquiv.symm_apply_apply]

/-- The extensions of `w_{0,1}` correspond. -/
noncomputable def extEquiv : Ext C K₁ ≃ Ext C K₂ where
  toFun w := ⟨w.1.comap φ.symm.toRingHom, Valuation.ext fun ψ ↦ by
    rw [Valuation.comap_apply, Valuation.comap_apply]
    change w.1 (φ.symm (algebraMap (RatFunc C) K₂ ψ)) = _
    rw [he_symm σ φ he, ← Valuation.comap_apply, w.2, hσ]⟩
  invFun w := ⟨w.1.comap φ.toRingHom, Valuation.ext fun ψ ↦ by
    rw [Valuation.comap_apply, Valuation.comap_apply]
    change w.1 (φ (algebraMap (RatFunc C) K₁ ψ)) = _
    have h := he (σ.symm ψ)
    rw [AlgEquiv.apply_symm_apply] at h
    rw [h, ← Valuation.comap_apply, w.2, ← hσ (σ.symm ψ), AlgEquiv.apply_symm_apply]⟩
  left_inv w := Subtype.ext (Valuation.ext fun f ↦ by
    change w.1 (φ.symm (φ f)) = w.1 f
    rw [RingEquiv.symm_apply_apply])
  right_inv w := Subtype.ext (Valuation.ext fun f ↦ by
    change w.1 (φ (φ.symm f)) = w.1 f
    rw [RingEquiv.apply_symm_apply])

omit [IsAlgClosed C] in
lemma extEquiv_apply (w : Ext C K₁) (f : K₁) : (extEquiv σ hσ φ he w).1 (φ f) = w.1 f := by
  change w.1 (φ.symm (φ f)) = _
  rw [RingEquiv.symm_apply_apply]

variable [Algebra C K₁] [IsScalarTower C (RatFunc C) K₁] [Algebra C K₂]
  [IsScalarTower C (RatFunc C) K₂]

include he in
omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma φ_algebraMap_C (b : C) : φ (algebraMap C K₁ b) = algebraMap C K₂ b := by
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) K₁, ← AlgEquiv.commutes σ, he,
    ← IsScalarTower.algebraMap_apply]

/-- The residue curves correspond. -/
noncomputable def resEq (w : Ext C K₁) :
    ResidueField w.1.valuationSubring ≃ₐ[𝓀]
      ResidueField (extEquiv σ hσ φ he w).1.valuationSubring :=
  resAlgEquiv φ (φ_algebraMap_C σ φ he) (extEquiv_apply σ hσ φ he w)

omit [IsAlgClosed C] in
lemma resEq_red (w : Ext C K₁) (f : K₁) :
    resEq σ hσ φ he w (red C f w) = red C (φ f) (extEquiv σ hσ φ he w) :=
  resAlgEquiv_red _ _ _ f

variable [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂]
  [Fintype (Ext C K₁)] [Fintype (Ext C K₂)]

include σ hσ φ he in
omit [IsAlgClosed C] [Algebra C K₁] [IsScalarTower C (RatFunc C) K₁] [Algebra C K₂]
  [IsScalarTower C (RatFunc C) K₂] in
omit [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂] in
lemma card_ext_eq : Fintype.card (Ext C K₁) = Fintype.card (Ext C K₂) :=
  Fintype.card_congr (extEquiv σ hσ φ he)

include σ hσ φ he in
lemma gsum_eq : LocalFormula.gsum C K₁ = LocalFormula.gsum C K₂ := by
  rw [LocalFormula.gsum, LocalFormula.gsum, ← (extEquiv σ hσ φ he).sum_comp]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [CurvePlace.genus_congr (resEq σ hσ φ he w)]

omit [Fintype (GaussFibre.Ext C K₁)] [Fintype (GaussFibre.Ext C K₂)] in
lemma card_zeros_eq (w : Ext C K₁) (f : K₁) :
    (PlaceNorm.zeros 𝓀 (red C (φ f) (extEquiv σ hσ φ he w))).card =
      (PlaceNorm.zeros 𝓀 (red C f w)).card := by
  rw [← resEq_red, card_zeros_map]

end Ext

/-! ### The reduced charts at `x` -/

section Chart

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra (RatFunc C) K₁] [Algebra (RatFunc C) K₂]
  (σ : RatFunc C ≃ₐ[C] RatFunc C) (hσ : ∀ ψ, gauss1 C (σ ψ) = gauss1 C ψ) (φ : K₁ ≃+* K₂)
  (he : ∀ ψ, φ (algebraMap (RatFunc C) K₁ (σ ψ)) = algebraMap (RatFunc C) K₂ ψ)
  [Algebra C K₁] [IsScalarTower C (RatFunc C) K₁] [Algebra C K₂]
  [IsScalarTower C (RatFunc C) K₂]

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) K₁]
  [IsScalarTower C (RatFunc C) K₂] in
omit [Algebra (RatFunc C) K₁] [Algebra (RatFunc C) K₂] in
/-- Integrality over coordinate rings along a `C`-isomorphism. -/
lemma isIntegral_map (φA : K₁ ≃ₐ[C] K₂) {x₁ : K₁} {x₂ : K₂}
    (h : φA x₁ ∈ Algebra.adjoin C {x₂}) {f : K₁} (hf : IsIntegral (Algebra.adjoin C {x₁}) f) :
    IsIntegral (Algebra.adjoin C {x₂}) (φA f) := by
  have hle : (Algebra.adjoin C {x₁}).map φA.toAlgHom ≤ Algebra.adjoin C {x₂} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.2 h)
  let ρ : Algebra.adjoin C {x₁} →+* Algebra.adjoin C {x₂} :=
    { toFun := fun a ↦ ⟨φA a, hle ⟨a, a.2, rfl⟩⟩
      map_one' := Subtype.ext (map_one φA)
      map_mul' := fun a b ↦ Subtype.ext (map_mul φA _ _)
      map_zero' := Subtype.ext (map_zero φA)
      map_add' := fun a b ↦ Subtype.ext (map_add φA _ _) }
  exact IsIntegral.map_of_comp_eq ρ φA.toRingHom (RingHom.ext fun _ ↦ rfl) hf

variable [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂]
  [Fintype (Ext C K₁)] [Fintype (Ext C K₂)]
  {u β : C} (hu : ‖u‖ = 1) (hβ : ‖β‖ ≤ 1)
  (hx : xF C K₂ = φ (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β))

include σ he

/-- `φ` as a `C`-algebra isomorphism. -/
noncomputable def φA : K₁ ≃ₐ[C] K₂ := AlgEquiv.ofRingEquiv (f := φ) (φ_algebraMap_C σ φ he)

include hu hx in
omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) K₁]
  [FiniteDimensional (RatFunc C) K₂] [Fintype (Ext C K₁)] [Fintype (Ext C K₂)] in
lemma isIntegral_iff (f : K₁) :
    IsIntegral (Algebra.adjoin C {xF C K₂}) (φ f) ↔ IsIntegral (Algebra.adjoin C {xF C K₁}) f := by
  have hu0 : u ≠ 0 := by rintro rfl; simp at hu
  constructor
  · intro h
    have h' := isIntegral_map (φA σ φ he).symm (x₁ := xF C K₂) (x₂ := xF C K₁) ?_ h
    · simpa [φA] using h'
    · rw [hx]
      change φ.symm (φ _) ∈ _
      rw [RingEquiv.symm_apply_apply]
      exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ u)
        (Algebra.self_mem_adjoin_singleton C _)) (Subalgebra.algebraMap_mem _ β)
  · intro h
    refine isIntegral_map (φA σ φ he) ?_ h
    have e : φA σ φ he (xF C K₁) =
        algebraMap C K₂ u⁻¹ * (xF C K₂ - algebraMap C K₂ β) := by
      change φ (xF C K₁) = _
      rw [hx, map_add, map_mul, φ_algebraMap_C σ φ he, φ_algebraMap_C σ φ he, add_sub_cancel_right,
        ← mul_assoc, ← map_mul, inv_mul_cancel₀ hu0, map_one, one_mul]
    rw [e]
    exact mul_mem (Subalgebra.algebraMap_mem _ _)
      (sub_mem (Algebra.self_mem_adjoin_singleton C _) (Subalgebra.algebraMap_mem _ _))

include hσ in
omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂]
  [Algebra C K₁] [IsScalarTower C (RatFunc C) K₁] [Algebra C K₂] [IsScalarTower C (RatFunc C) K₂] in
lemma gnorm_map (f : K₁) : gnorm C (φ f) = gnorm C f := by
  refine le_antisymm (gnorm_le_iff.2 fun w' ↦ ?_) (gnorm_le_iff.2 fun w ↦ ?_)
  · obtain ⟨w, rfl⟩ := (extEquiv σ hσ φ he).surjective w'
    rw [extEquiv_apply]
    exact le_gnorm w f
  · rw [← extEquiv_apply σ hσ φ he w f]
    exact le_gnorm _ _

include hσ hu hx in
omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂] in
lemma mem_intRing_iff (f : K₁) :
    φ f ∈ intRing C K₂ (xF C K₂) ↔ f ∈ intRing C K₁ (xF C K₁) := by
  change IsIntegral _ (φ f) ∧ gnorm C (φ f) ≤ 1 ↔ IsIntegral _ f ∧ gnorm C f ≤ 1
  rw [isIntegral_iff σ φ he hu hx, gnorm_map σ hσ φ he]

include hσ in
/-- The chart comparison. -/
noncomputable abbrev E :=
  extEmb φ (φ_algebraMap_C σ φ he) (extEquiv σ hσ φ he) (extEquiv_apply σ hσ φ he)

include hσ hu hx in
/-- **The reduced charts at `x` agree** (with nothing inverted). -/
theorem isLocalIso_one
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂))) :
    IsLocalIso hΛ₁ hΛ₂ (E σ hσ φ he) (fun w ↦ red C (1 : K₁) w) (fun w' ↦ red C (1 : K₂) w') := by
  refine isLocalIso_of φ (φ_algebraMap_C σ φ he) (extEquiv σ hσ φ he) (extEquiv_apply σ hσ φ he)
    hΛ₁ hΛ₂ (one_mem _) (one_mem _) (fun f hf ↦ ⟨0, ?_, fun w' hw' ↦ ?_⟩) (fun g hg ↦ ⟨0, ?_⟩)
    (fun w Q _ _ ↦ ?_) (fun w' Q _ _ ↦ ?_)
  · rw [pow_zero, one_mul]
    exact (mem_intRing_iff σ hσ φ he hu hx f).2 hf
  · exact absurd ((extEquiv σ hσ φ he).surjective w') hw'
  · rw [pow_zero, one_mul]
    rw [← mem_intRing_iff σ hσ φ he hu hx, RingEquiv.apply_symm_apply]
    exact hg
  · rw [map_one, red_one, map_one]
  · exact ⟨(extEquiv σ hσ φ he).surjective w', by rw [map_one, red_one, map_one]⟩

include hσ hu hx in
/-- **Total `δ` along a change of coordinates.** -/
theorem tot0_eq
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂)))
    (P₁ : Ideal (redRing C K₁ (xF C K₁)) → Prop) (P₂ : Ideal (redRing C K₂ (xF C K₂)) → Prop)
    (hP : ∀ 𝔫 : Ideal (redRing C K₁ (xF C K₁)), 𝔫.IsMaximal →
      (P₁ 𝔫 ↔ P₂ (trI hΛ₁ hΛ₂ (E σ hσ φ he) 𝔫))) :
    tot0 C K₂ hΛ₂ P₂ = tot0 C K₁ hΛ₁ P₁ := by
  have H := isLocalIso_one σ hσ φ he hu hx hΛ₁ hΛ₂
  have h := H.finsum_dinf_eq P₁ P₂ fun 𝔫 h1 _ ↦ hP 𝔫 h1
  rw [tot0, tot0]
  have e₁ : {𝔫 : Ideal (redRing C K₁ (xF C K₁)) | 𝔫.IsMaximal ∧ P₁ 𝔫} =
      {𝔫 | 𝔫.IsMaximal ∧ (⟨fun w ↦ red C (1 : K₁) w, H.mem_u⟩ : redRing C K₁ (xF C K₁)) ∉ 𝔫 ∧
        P₁ 𝔫} := by
    ext 𝔫
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h ↦ ⟨h.1, LocalFormula.notMem_of_red_eq_one (one_mem _) (fun _ ↦ red_one)
      h.1.ne_top, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  have e₂ : {𝔫 : Ideal (redRing C K₂ (xF C K₂)) | 𝔫.IsMaximal ∧ P₂ 𝔫} =
      {𝔫 | 𝔫.IsMaximal ∧ (⟨fun w ↦ red C (1 : K₂) w, H.mem_u'⟩ : redRing C K₂ (xF C K₂)) ∉ 𝔫 ∧
        P₂ 𝔫} := by
    ext 𝔫
    simp only [Set.mem_setOf_eq]
    exact ⟨fun h ↦ ⟨h.1, LocalFormula.notMem_of_red_eq_one (one_mem _) (fun _ ↦ red_one)
      h.1.ne_top, h.2⟩, fun h ↦ ⟨h.1, h.2.2⟩⟩
  rw [e₁, e₂]
  exact h.symm

include hσ hu hx in
/-- Corresponding reductions lie in corresponding points. -/
theorem mem_trI_iff
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂)))
    {𝔫 : Ideal (redRing C K₁ (xF C K₁))} (h𝔫 : 𝔫.IsMaximal) {g : K₁}
    (hg : g ∈ intRing C K₁ (xF C K₁)) :
    (⟨fun w ↦ red C g w, red_mem_redRing hg⟩ : redRing C K₁ (xF C K₁)) ∈ 𝔫 ↔
      (⟨fun w' ↦ red C (φ g) w', red_mem_redRing ((mem_intRing_iff σ hσ φ he hu hx g).2 hg)⟩ :
        redRing C K₂ (xF C K₂)) ∈ trI hΛ₁ hΛ₂ (E σ hσ φ he) 𝔫 := by
  have H := isLocalIso_one σ hσ φ he hu hx hΛ₁ hΛ₂
  refine H.mem_iff_mem_trI h𝔫 (LocalFormula.notMem_of_red_eq_one (one_mem _) (fun _ ↦ red_one)
    h𝔫.ne_top) _ _ fun b _ _ ↦ ?_
  obtain ⟨w, Q⟩ := b
  change Q.valuation (red C g w) < 1 ↔ (Q.map ((E σ hσ φ he).e w)).valuation
    (red C (φ g) ((E σ hσ φ he).ι w)) < 1
  have h := CurvePlace.valuation_map_apply ((E σ hσ φ he).e w) Q (red C g w)
  rw [extEmb_e_red] at h
  exact (iff_of_eq (congrArg (· < 1) h)).symm

include hσ hu hx in
/-- The coordinate of `K₂` lies in the transport of a point iff `u x₁ + β` lies in the point. -/
theorem mem_trI_iff_x
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂)))
    {𝔫 : Ideal (redRing C K₁ (xF C K₁))} (h𝔫 : 𝔫.IsMaximal)
    (hg : algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β ∈ intRing C K₁ (xF C K₁)) :
    (⟨fun w ↦ red C (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β) w, red_mem_redRing hg⟩ :
        redRing C K₁ (xF C K₁)) ∈ 𝔫 ↔
      (⟨fun w' ↦ red C (xF C K₂) w', hΛ₂.mem⟩ : redRing C K₂ (xF C K₂)) ∈
        trI hΛ₁ hΛ₂ (E σ hσ φ he) 𝔫 := by
  rw [mem_trI_iff σ hσ φ he hu hx hΛ₁ hΛ₂ h𝔫 hg]
  have e : (⟨fun w' ↦ red C (xF C K₂) w', hΛ₂.mem⟩ : redRing C K₂ (xF C K₂)) =
      ⟨fun w' ↦ red C (φ (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β)) w',
        red_mem_redRing ((mem_intRing_iff σ hσ φ he hu hx _).2 hg)⟩ :=
    Subtype.ext (funext fun w' ↦ congrArg (fun f ↦ red C f w') hx)
  rw [e]

include hσ hu hx in
/-- **Total `δ` over the residue point** along a change of coordinates. -/
theorem tot0_x_eq
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂)))
    (hg : algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β ∈ intRing C K₁ (xF C K₁)) :
    tot0 C K₂ hΛ₂ (fun 𝔫 ↦ (⟨fun w' ↦ red C (xF C K₂) w', hΛ₂.mem⟩ :
      redRing C K₂ (xF C K₂)) ∈ 𝔫) =
    tot0 C K₁ hΛ₁ (fun 𝔫 ↦ (⟨fun w ↦ red C (algebraMap C K₁ u * xF C K₁ + algebraMap C K₁ β) w,
      red_mem_redRing hg⟩ : redRing C K₁ (xF C K₁)) ∈ 𝔫) :=
  tot0_eq σ hσ φ he hu hx hΛ₁ hΛ₂ _ _ fun _ h𝔫 ↦
    mem_trI_iff_x σ hσ φ he hu hx hΛ₁ hΛ₂ h𝔫 hg

include hσ hu hx in
/-- **Total `δ` of the chart** along a change of coordinates. -/
theorem tot0_true_eq
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂))) :
    tot0 C K₂ hΛ₂ (fun _ ↦ True) = tot0 C K₁ hΛ₁ (fun _ ↦ True) :=
  tot0_eq σ hσ φ he hu hx hΛ₁ hΛ₂ _ _ fun _ _ ↦ Iff.rfl

end Chart

/-! ### Instances -/

section Instances

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- `C`-algebra endomorphisms of `C(x)` agreeing on `x` are equal. -/
lemma ratFunc_algHom_ext {f g : RatFunc C →ₐ[C] RatFunc C} (h : f RatFunc.X = g RatFunc.X) :
    f = g := by
  ext φ
  have hp (p : C[X]) : f (algebraMap C[X] (RatFunc C) p) = g (algebraMap C[X] (RatFunc C) p) := by
    rw [← RatFunc.aeval_X_left_eq_algebraMap, ← Polynomial.aeval_algHom_apply,
      ← Polynomial.aeval_algHom_apply, h]
  rw [← RatFunc.num_div_denom φ, map_div₀, map_div₀, hp, hp]

omit [IsAlgClosed C] in
/-- `x ↦ ((x - b)/d - a)/c = (x - (b + d a))/(d c)`. -/
lemma aff_aff {a b c d : C} (hd : d ≠ 0) (hc : c ≠ 0) (φ : RatFunc C) :
    aff b d hd (aff a c hc φ) = aff (b + d * a) (d * c) (mul_ne_zero hd hc) φ := by
  have := ratFunc_algHom_ext (f := (aff b d hd).toAlgHom.comp (aff a c hc).toAlgHom)
    (g := (aff (b + d * a) (d * c) (mul_ne_zero hd hc)).toAlgHom) (by
      change aff b d hd (aff a c hc RatFunc.X) = aff (b + d * a) (d * c) _ RatFunc.X
      simp only [aff_apply]
      have hd' : algebraMap C (RatFunc C) d ≠ 0 := by simpa using hd
      have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
      rw [affHom_X, affHom_gaussCoord, affHom_X, gaussCoord_eq, gaussCoord_eq]
      simp only [map_inv₀, map_mul, map_add]
      field_simp
      ring)
  exact congrArg (fun f : RatFunc C →ₐ[C] RatFunc C ↦ f φ) this

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F]

/-- **Composition of affine twists**: `Aff a c (Aff b d F) = Aff (b + d a) (d c) F`. -/
noncomputable def compEquiv {a b c d : C} (hd : d ≠ 0) (hc : c ≠ 0) :
    Aff a c hc (Aff b d hd F) ≃+* Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F :=
  ((toAff hc).symm.trans (toAff hd).symm).trans (toAff (mul_ne_zero hd hc))

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma compEquiv_he {a b c d : C} (hd : d ≠ 0) (hc : c ≠ 0) (ψ : RatFunc C) :
    compEquiv (F := F) hd hc (algebraMap (RatFunc C) (Aff a c hc (Aff b d hd F))
      ((AlgEquiv.refl : RatFunc C ≃ₐ[C] RatFunc C) ψ)) =
      algebraMap (RatFunc C) (Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F) ψ := by
  change algebraMap (RatFunc C) F (aff b d hd (aff a c hc ψ)) = _
  rw [aff_aff]
  rfl

omit [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
lemma compEquiv_x {a b c d : C} (hd : d ≠ 0) (hc : c ≠ 0) :
    xF C (Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F) =
      compEquiv (F := F) hd hc (algebraMap C (Aff a c hc (Aff b d hd F)) (1 : C) *
        xF C (Aff a c hc (Aff b d hd F)) + algebraMap C (Aff a c hc (Aff b d hd F)) (0 : C)) := by
  rw [map_one, one_mul, map_zero, add_zero, xF, xF, ← compEquiv_he hd hc]
  rfl

lemma gauss1_aff_one {β : C} (hβ : ‖β‖ ≤ 1) (ψ : RatFunc C) :
    gauss1 C (aff β 1 one_ne_zero ψ) = gauss1 C ψ := by
  have h := gaussRat_aff (C := C) (a := β) (c := 1) one_ne_zero ψ
  have h1 : Units.mk0 ‖(1 : C)‖₊ (nnnorm_ne_zero_iff.2 one_ne_zero) = 1 := by ext; simp
  rw [h1, Splitting.gaussRat_eq_of_le (b := 0)] at h
  · exact h
  · rw [sub_zero, NormedField.valuation_apply, Units.val_one]
    exact_mod_cast hβ

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma shift_he {β : C} (ψ : RatFunc C) :
    toAff (a := β) (c := 1) one_ne_zero (algebraMap (RatFunc C) F (aff β 1 one_ne_zero ψ)) =
      algebraMap (RatFunc C) (Aff β 1 one_ne_zero F) ψ := rfl

omit [IsAlgClosed C] in
lemma shift_x {β : C} :
    xF C (Aff β 1 one_ne_zero F) =
      toAff one_ne_zero (algebraMap C F (1 : C) * xF C F + algebraMap C F (-β)) := by
  change toAff one_ne_zero (algebraMap (RatFunc C) F (aff β 1 one_ne_zero RatFunc.X)) = _
  rw [aff_apply, affHom_X, gaussCoord_eq, inv_one, map_one, one_mul, sub_eq_add_neg, map_add,
    map_neg, map_one, one_mul, map_neg, ← IsScalarTower.algebraMap_apply]

/-- The inversion `Inv c K` and the twist `Aff 0 c K`. -/
noncomputable def invEquiv {c : C} (hc : c ≠ 0) : GaussTube.Inv c hc F ≃+* Aff (0 : C) c hc F :=
  (GaussTube.toInv hc).symm.trans (toAff hc)

/-- The change of coordinates `x/c ↦ c/x`. -/
noncomputable def σInv {c : C} (hc : c ≠ 0) : RatFunc C ≃ₐ[C] RatFunc C :=
  (aff 0 c hc).trans (GaussTube.inv hc).symm

lemma gauss1_σInv {c : C} (hc : c ≠ 0) (ψ : RatFunc C) : gauss1 C (σInv hc ψ) = gauss1 C ψ := by
  change gaussRat _ 0 1 ((GaussTube.inv hc).symm (aff 0 c hc ψ)) = _
  have hs : (GaussTube.inv hc).symm (aff 0 c hc ψ) =
      GaussTube.inv hc (aff 0 c hc ψ) := by
    apply (GaussTube.inv hc).injective
    rw [AlgEquiv.apply_symm_apply, GaussTube.inv_inv_apply]
  rw [hs, GaussTube.gaussRat_inv]
  have h1 : GaussTube.invRad hc 1 = Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc) := by
    ext; simp [GaussTube.coe_invRad]
  rw [h1, gaussRat_aff]

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma invEquiv_he {c : C} (hc : c ≠ 0) (ψ : RatFunc C) :
    invEquiv (F := F) hc (algebraMap (RatFunc C) (GaussTube.Inv c hc F) (σInv hc ψ)) =
      algebraMap (RatFunc C) (Aff (0 : C) c hc F) ψ := by
  change algebraMap (RatFunc C) F (GaussTube.inv hc ((GaussTube.inv hc).symm (aff 0 c hc ψ))) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma invEquiv_x {c : C} (hc : c ≠ 0) :
    invEquiv (F := F) hc (xF C (GaussTube.Inv c hc F)) = (xF C (Aff (0 : C) c hc F))⁻¹ := by
  change algebraMap (RatFunc C) F (GaussTube.inv hc RatFunc.X) =
    (algebraMap (RatFunc C) F (aff 0 c hc RatFunc.X))⁻¹
  rw [GaussTube.inv_apply, GaussTube.invHom_X, aff_apply, affHom_X, gaussCoord_eq, map_zero,
    sub_zero, ← map_inv₀]
  congr 1
  rw [mul_inv, map_inv₀, inv_inv, div_eq_mul_inv]

end Instances

end ChartChange

end SemistableReduction
