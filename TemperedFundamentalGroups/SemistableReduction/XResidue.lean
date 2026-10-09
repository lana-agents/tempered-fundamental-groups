/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XGauss

/-!
# Residue transcendence over different constant fields (Blueprint §9.7, X1)

Let `U` be a valuation subring of a field `E` lying over valuation subrings `O₁ ⊆ K₁` and
`O₂ ⊆ K₂` of two subfields of constants, with the constants of `K₂` algebraic over `K₁`. If `z`
has transcendental residue over `κ(O₁)`, it has transcendental residue over `κ(O₂)`
(`IsResidueTranscendental.of_algebraic`): the residues of `O₂` are algebraic over `κ(O₁)`
(normalised minimal polynomials, `exists_poly_residue_ne_zero`), so an algebraic relation of `z̄`
over `κ(O₂)` would make `z̄` algebraic over `κ(O₁)`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

variable {E K₁ K₂ : Type*} [Field E] [Field K₁] [Field K₂] [Algebra K₁ E] [Algebra K₂ E]
  {O₁ : ValuationSubring K₁} {O₂ : ValuationSubring K₂} {U : ValuationSubring E}

/-- **Residue transcendence descends to smaller residue fields of constants.** -/
theorem IsResidueTranscendental.of_algebraic (h₁ : U.comap (algebraMap K₁ E) = O₁)
    (h₂ : U.comap (algebraMap K₂ E) = O₂)
    (halg : ∀ k : K₂, IsAlgebraic K₁ (algebraMap K₂ E k)) {z : E}
    (h : IsResidueTranscendental O₁ U z) : IsResidueTranscendental O₂ U z := by
  classical
  have hz := h.1
  rw [isResidueTranscendental_iff h₁ hz] at h
  rw [isResidueTranscendental_iff h₂ hz]
  letI A₁ := residueAlgebra h₁
  set ι₂ := ResidueField.map (toVal h₂)
  -- the residues of `O₂` are algebraic over `κ(O₁)`
  have hres : ∀ c : ResidueField O₂, IsAlgebraic (ResidueField O₁) (ι₂ c) := by
    intro c
    obtain ⟨c, rfl⟩ := residue_surjective c
    obtain ⟨M, hM, hMc⟩ := exists_poly_residue_ne_zero (O := O₁) (halg c)
    have hcU : algebraMap K₂ E c ∈ U := by
      rw [← ValuationSubring.mem_comap, h₂]; exact c.2
    refine ⟨M.map (residue O₁), hM, ?_⟩
    have e : ι₂ (residue O₂ c) = residue U ⟨_, hcU⟩ := by
      simp only [ι₂, ResidueField.map_residue]; rfl
    rw [e, aeval_residue h₁ hcU M]
    have : eval₂ (toVal h₁) ⟨_, hcU⟩ M = 0 := by
      apply Subtype.ext
      rw [coe_eval₂_toVal h₁ hcU M, hMc]; rfl
    rw [this, map_zero]
  -- hence so is everything algebraic over them
  set S := IntermediateField.adjoin (ResidueField O₁) (Set.range ι₂)
  haveI : Algebra.IsAlgebraic (ResidueField O₁) S :=
    IntermediateField.isAlgebraic_adjoin fun x ⟨c, hc⟩ ↦ hc ▸ (hres c).isIntegral
  letI A₂ := residueAlgebra h₂
  intro halgz
  apply h
  obtain ⟨Q, hQ0, hQz⟩ := halgz
  let φ : ResidueField O₂ →+* S := ι₂.codRestrict S.toSubring fun c ↦
    IntermediateField.subset_adjoin _ _ ⟨c, rfl⟩
  have hz' : IsAlgebraic S (residue U ⟨z, hz⟩) := by
    refine ⟨Q.map φ, (Polynomial.map_ne_zero_iff φ.injective).mpr hQ0, ?_⟩
    rw [aeval_def, eval₂_map]
    have : (algebraMap S (ResidueField U)).comp φ =
        algebraMap (ResidueField O₂) (ResidueField U) := by ext; rfl
    rw [this, ← aeval_def]
    exact hQz
  exact hz'.restrictScalars (ResidueField O₁)

/-- Residue transcendence of a power implies residue transcendence. -/
theorem IsResidueTranscendental.of_pow {K : Type*} [Field K] [Algebra K E]
    {O : ValuationSubring K} (hU : U.comap (algebraMap K E) = O) {w : E} (hw : w ∈ U) {M : ℕ}
    (h : IsResidueTranscendental O U (w ^ M)) : IsResidueTranscendental O U w := by
  rw [isResidueTranscendental_iff hU hw]
  rw [isResidueTranscendental_iff hU (U.pow_mem hw M)] at h
  letI := residueAlgebra hU
  intro halg
  apply h
  have : residue U ⟨w ^ M, U.pow_mem hw M⟩ = residue U ⟨w, hw⟩ ^ M := by
    rw [← map_pow]; rfl
  rw [this]
  exact halg.pow M

/-- Residue transcendence restricts to subfields. -/
theorem IsResidueTranscendental.comap {F K : Type*} [Field F] [Field K] [Algebra F E]
    [Algebra K F] [Algebra K E] [IsScalarTower K F E] {O : ValuationSubring K} {z : F}
    (h : IsResidueTranscendental O U (algebraMap F E z)) :
    IsResidueTranscendental O (U.comap (algebraMap F E)) z := by
  refine ⟨h.1, fun P hP ↦ ?_⟩
  have h1 := h.2 P hP
  rw [aeval_algebraMap_apply] at h1
  rw [valuation_eq_one_iff_mem_and_inv_mem] at h1 ⊢
  obtain ⟨h0, hm, hi⟩ := h1
  refine ⟨fun h' ↦ h0 (by rw [h', map_zero]), hm, ?_⟩
  rw [ValuationSubring.mem_comap, map_inv₀]
  exact hi

/-- `IsLogValue` descends to subfields. -/
theorem IsLogValue.comap {F : Type*} [Field F] [Algebra F E] {a b : F} (ha : a ≠ 0) {q : ℚ}
    (h : IsLogValue U (algebraMap F E a) (algebraMap F E b) q) :
    IsLogValue (U.comap (algebraMap F E)) a b q := by
  unfold IsLogValue at h ⊢
  by_cases hb : b = 0
  · subst hb
    rw [map_zero, map_zero, zero_pow q.den_nz] at h
    exact absurd h.symm (zpow_ne_zero _ (by simpa using ha))
  have hz : b ^ q.den / a ^ q.num ≠ 0 := div_ne_zero (pow_ne_zero _ hb) (zpow_ne_zero _ ha)
  have h1 : U.valuation (algebraMap F E (b ^ q.den / a ^ q.num)) = 1 := by
    rw [map_div₀, map_pow, map_zpow₀, map_div₀, map_pow, map_zpow₀, h,
      div_self (zpow_ne_zero _ (by simpa using ha))]
  have h2 : (U.comap (algebraMap F E)).valuation (b ^ q.den / a ^ q.num) = 1 := by
    rw [valuation_eq_one_iff_mem_and_inv_mem] at h1 ⊢
    obtain ⟨-, hm, hi⟩ := h1
    exact ⟨hz, hm, by rw [ValuationSubring.mem_comap, map_inv₀]; exact hi⟩
  rw [map_div₀, map_pow, map_zpow₀, div_eq_one_iff_eq (zpow_ne_zero _ (by simpa using ha))] at h2
  exact h2

end SemistableReduction
