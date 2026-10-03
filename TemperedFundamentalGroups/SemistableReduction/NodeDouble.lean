/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeSide
import TemperedFundamentalGroups.SemistableReduction.ConductorLocal

/-!
# Ordinary double points of the normalized node over `C`

Blueprint §9.9, S7.8 over `C`. Let `R' = Rint c F'` be the integral closure of the node chart
`O_C[x, c/x]`, `P'` a maximal ideal of `R'` over the node with exactly one outer branch `(v₁, Q₁)`
(a zero of `x̄` on the residue curve of an extension `v₁` of `w_{0,1}`) and one inner branch
`(w₂, Q₂)` (a zero of the residue of `c/x` on the residue curve of an extension of `w_{0,|c|}`,
seen through the inversion `Inv c F'`). Write `ρ₁`, `ρ₂` for the reductions of `R'` at `v₁`, `w₂`.

* `exists_fp`: if `R'_{P'}` reaches the fibre product `{(a, b) ∈ O_{Q₁} × O_{Q₂} | a(Q₁) = b(Q₂)}`
  modulo every power of the maximal ideals (`δ' = 0` from the δ-count, S7.6), it reaches it
  exactly (`ConductorLocal.exists_eq_of_jets`, with the conductor of `NodeSide`);
* **`exists_sub_mem_ker`** (the ordinary double point over `C`): then for `u', v' ∈ R'` with
  `ρ₂ u' = 0`, `ord_{Q₁} ρ₁ u' = 1`, `ρ₁ v' = 0`, `ord_{Q₂} ρ₂ v' = 1`, every `z ∈ P'` satisfies
  `ρⱼ(s z - a u' - b v') = 0` (`j = 1, 2`) for some `a, b ∈ R'` and `s ∉ P'`.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)

include hc0 in
omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma rintEquiv_xR : rintEquiv hc0 (xR c : Rint c F') = yR c := by
  apply Subtype.ext
  change toInv hc0 (algebraMap (RatFunc C) F' RatFunc.X) =
    algebraMap (RatFunc C) (Inv c hc0 F') (algebraMap C (RatFunc C) c / RatFunc.X)
  rw [algebraMap_inv_apply, inv_apply, map_div₀, AlgHom.commutes, invHom_X,
    div_div_cancel₀ (by simpa using hc0)]

include hc0 in
omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma rintEquiv_yR : rintEquiv hc0 (yR c : Rint c F') = xR c := by
  apply Subtype.ext
  change toInv hc0 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) c / RatFunc.X)) =
    algebraMap (RatFunc C) (Inv c hc0 F') RatFunc.X
  rw [algebraMap_inv_apply, inv_apply, invHom_X]

/-- The reduction at an inner vertex, through the inversion. -/
noncomputable def redHomInv (w₂ : Ext C (Inv c hc0 F')) :
    Rint c F' →+* ResidueField w₂.1.valuationSubring :=
  (redHom hc w₂).comp (rintEquiv hc0).toRingHom

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **The local ring reaches the fibre product exactly.** -/
theorem exists_fp (v₁ : Ext C F') {Q₁ : CurvePlace 𝓀 (ResidueField v₁.1.valuationSubring)}
    (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C F') v₁)) (w₂ : Ext C (Inv c hc0 F'))
    {Q₂ : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)}
    (hQ₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂))
    (hP : placeIdeal hc w₂ hQ₂ = (placeIdeal hc v₁ hQ₁).comap (rintEquiv hc0).symm.toRingHom)
    (hoth₁ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v₁)), R ≠ Q₁ →
      placeIdeal hc v₁ hR ≠ placeIdeal hc v₁ hQ₁)
    (hoth₂ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂)), R ≠ Q₂ →
      placeIdeal hc w₂ hR ≠ placeIdeal hc w₂ hQ₂)
    (hjet : ∀ a ∈ Q₁.V, ∀ b ∈ Q₂.V, Q₁.res a = Q₂.res b → ∀ M : ℕ, ∃ y s : Rint c F',
      s ∉ placeIdeal hc v₁ hQ₁ ∧
      Q₁.valuation (redHom hc v₁ y / redHom hc v₁ s - a) ≤ exp (-(M : ℤ)) ∧
      Q₂.valuation (redHomInv hc hc0 w₂ y / redHomInv hc hc0 w₂ s - b) ≤ exp (-(M : ℤ)))
    {a : ResidueField v₁.1.valuationSubring} (ha : a ∈ Q₁.V)
    {b : ResidueField w₂.1.valuationSubring} (hb : b ∈ Q₂.V) (hab : Q₁.res a = Q₂.res b) :
    ∃ y s : Rint c F', s ∉ placeIdeal hc v₁ hQ₁ ∧ redHom hc v₁ y = a * redHom hc v₁ s ∧
      redHomInv hc hc0 w₂ y = b * redHomInv hc hc0 w₂ s := by
  classical
  set P' := placeIdeal hc v₁ hQ₁
  haveI : P'.IsMaximal := placeIdeal_isMaximal hc v₁ hQ₁
  set ρ₁ := redHom hc v₁
  set ρ₂ := redHomInv hc hc0 w₂
  have hρ₂ (r : Rint c F') : ρ₂ r = redHom hc w₂ (rintEquiv hc0 r) := rfl
  -- the normalizations
  set Ã₁ := (integralClosure (Algebra.adjoin 𝓀 {red C (xF C F') v₁})
    (ResidueField v₁.1.valuationSubring)).toSubring
  set Ã₂ := (integralClosure (Algebra.adjoin 𝓀 {red C (xF C (Inv c hc0 F')) w₂})
    (ResidueField w₂.1.valuationSubring)).toSubring
  -- the conductor
  obtain ⟨G₁, hG₁, hsp₁⟩ := exists_span hc v₁
  obtain ⟨G₂, hG₂, hsp₂⟩ := exists_span hc w₂
  obtain ⟨σ, hσ₁, hσ₂, hσ⟩ := ConductorLocal.exists_conductor ρ₁ ρ₂ Ã₁ Ã₂ G₁ G₂
    hG₁ hG₂ (fun α hα ↦ hsp₁ α hα)
    (fun α hα ↦ by
      obtain ⟨r, hr⟩ := hsp₂ α hα
      exact ⟨fun g ↦ (rintEquiv hc0).symm (r g), by
        rw [hr]; exact Finset.sum_congr rfl fun g _ ↦ by rw [hρ₂, RingEquiv.apply_symm_apply]⟩)
    (fun α _ ↦ exists_frac hp hp1 hc hc0 v₁ α)
    (fun α _ ↦ by
      obtain ⟨p', q', hq', hpq⟩ := exists_frac (F' := Inv c hc0 F') hp hp1 hc hc0 w₂ α
      exact ⟨(rintEquiv hc0).symm p', (rintEquiv hc0).symm q', by
        rwa [hρ₂, RingEquiv.apply_symm_apply], by
        rw [hρ₂, hρ₂, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, hpq]⟩)
    (x₀ := xR c) (y₀ := yR c) (by rw [redHom_xR]; exact red_xF_ne_zero' v₁)
    (by rw [hρ₂, rintEquiv_xR, redHom_yR]) (redHom_yR hc v₁)
    (by rw [hρ₂, rintEquiv_yR, redHom_xR]; exact red_xF_ne_zero' w₂)
  -- the point and the branches
  have hmem₂ (r : Rint c F') : r ∈ P' ↔ rintEquiv hc0 r ∈ placeIdeal hc w₂ hQ₂ := by
    rw [hP, Ideal.mem_comap]
    change _ ↔ (rintEquiv hc0).symm (rintEquiv hc0 r) ∈ P'
    rw [RingEquiv.symm_apply_apply]
  have hP₁ (r : Rint c F') (hr : r ∉ P') : ρ₁ r ≠ 0 := fun h ↦ hr <| by
    rw [mem_placeIdeal_iff]
    change Q₁.res (ρ₁ r) = 0
    rw [h, CurvePlace.res_zero]
  have hP₂ (r : Rint c F') (hr : r ∉ P') : ρ₂ r ≠ 0 := fun h ↦ hr <| by
    rw [hmem₂, mem_placeIdeal_iff]
    change Q₂.res (ρ₂ r) = 0
    rw [h, CurvePlace.res_zero]
  refine ConductorLocal.exists_eq_of_jets ρ₁ ρ₂ Q₁ Q₂ Ã₁ Ã₂ P' hP₁ hP₂ hσ₁ hσ₂
    (red_mem_V hc v₁ σ hQ₁) (red_mem_V hc w₂ _ hQ₂) hσ (fun g₁ hg₁ g₂ hg₂ ↦ ?_)
    (hjet a ha b hb hab)
  obtain ⟨τ₁, hτ₁P, hτ₁⟩ := exists_tau hc v₁ hQ₁ hoth₁ hg₁
  obtain ⟨τ₂', hτ₂P, hτ₂⟩ := exists_tau hc w₂ hQ₂ hoth₂ hg₂
  set τ₂ := (rintEquiv hc0).symm τ₂'
  have hτ₂P' : τ₂ ∉ P' := by
    rw [hmem₂, RingEquiv.apply_symm_apply]
    exact hτ₂P
  refine ⟨τ₁ * τ₂, Ideal.IsPrime.mul_notMem inferInstance hτ₁P hτ₂P', ?_, ?_⟩
  · rw [map_mul, mul_comm (ρ₁ τ₁), mul_assoc]
    exact mul_mem ((mem_integralClosure_iff _ _).2 (redHom_isIntegral hc v₁ τ₂))
      ((mem_integralClosure_iff _ _).2 hτ₁)
  · rw [map_mul, mul_assoc, hρ₂ τ₂, RingEquiv.apply_symm_apply]
    exact mul_mem ((mem_integralClosure_iff _ _).2 (redHom_isIntegral hc w₂ _))
      ((mem_integralClosure_iff _ _).2 hτ₂)

include hp hp1 in
/-- **The ordinary double point over `C`.** Under the hypotheses of `exists_fp`, for `u', v' ∈ R'`
with `ρ₂ u' = 0`, `ord_{Q₁} ρ₁ u' = 1`, `ρ₁ v' = 0`, `ord_{Q₂} ρ₂ v' = 1`, every `z ∈ P'` satisfies
`ρⱼ (s z - a u' - b v') = 0` for some `a, b ∈ R'` and `s ∉ P'`. -/
theorem exists_sub_mem_ker (v₁ : Ext C F')
    {Q₁ : CurvePlace 𝓀 (ResidueField v₁.1.valuationSubring)}
    (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C F') v₁)) (w₂ : Ext C (Inv c hc0 F'))
    {Q₂ : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)}
    (hQ₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂))
    (hP : placeIdeal hc w₂ hQ₂ = (placeIdeal hc v₁ hQ₁).comap (rintEquiv hc0).symm.toRingHom)
    (hoth₁ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v₁)), R ≠ Q₁ →
      placeIdeal hc v₁ hR ≠ placeIdeal hc v₁ hQ₁)
    (hoth₂ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂)), R ≠ Q₂ →
      placeIdeal hc w₂ hR ≠ placeIdeal hc w₂ hQ₂)
    (hjet : ∀ a ∈ Q₁.V, ∀ b ∈ Q₂.V, Q₁.res a = Q₂.res b → ∀ M : ℕ, ∃ y s : Rint c F',
      s ∉ placeIdeal hc v₁ hQ₁ ∧
      Q₁.valuation (redHom hc v₁ y / redHom hc v₁ s - a) ≤ exp (-(M : ℤ)) ∧
      Q₂.valuation (redHomInv hc hc0 w₂ y / redHomInv hc hc0 w₂ s - b) ≤ exp (-(M : ℤ)))
    {u' v' : Rint c F'} (hu₁ : Q₁.valuation (redHom hc v₁ u') = exp (-1))
    (hu₂ : redHomInv hc hc0 w₂ u' = 0) (hv₁ : redHom hc v₁ v' = 0)
    (hv₂ : Q₂.valuation (redHomInv hc hc0 w₂ v') = exp (-1))
    {z : Rint c F'} (hz : z ∈ placeIdeal hc v₁ hQ₁) :
    ∃ a b s : Rint c F', s ∉ placeIdeal hc v₁ hQ₁ ∧
      redHom hc v₁ (s * z - a * u' - b * v') = 0 ∧
      redHomInv hc hc0 w₂ (s * z - a * u' - b * v') = 0 := by
  haveI : (placeIdeal hc v₁ hQ₁).IsMaximal := placeIdeal_isMaximal hc v₁ hQ₁
  have hz₁ : Q₁.valuation (redHom hc v₁ z) < 1 := by
    rw [mem_placeIdeal_iff] at hz
    have := Q₁.valuation_sub_res_lt_one (red_mem_V hc v₁ z hQ₁)
    rwa [hz, map_zero, sub_zero] at this
  have hz₂ : Q₂.valuation (redHomInv hc hc0 w₂ z) < 1 := by
    have hz' : rintEquiv hc0 z ∈ placeIdeal hc w₂ hQ₂ := by
      rw [hP, Ideal.mem_comap]
      change (rintEquiv hc0).symm (rintEquiv hc0 z) ∈ _
      rwa [RingEquiv.symm_apply_apply]
    rw [mem_placeIdeal_iff] at hz'
    have := Q₂.valuation_sub_res_lt_one (red_mem_V hc w₂ (rintEquiv hc0 z) hQ₂)
    rw [hz', map_zero, sub_zero] at this
    exact this
  exact ConductorLocal.exists_sub_mem_ker (redHom hc v₁) (redHomInv hc hc0 w₂) Q₁ Q₂
    (placeIdeal hc v₁ hQ₁)
    (fun a ha b hb hab ↦ exists_fp hc hc0 hp hp1 v₁ hQ₁ w₂ hQ₂ hP hoth₁ hoth₂ hjet ha hb hab)
    hu₁ hu₂ hv₁ hv₂ hz₁ hz₂

end GaussTube

end SemistableReduction
