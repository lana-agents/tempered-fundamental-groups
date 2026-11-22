/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspKummerTame

/-!
# The DVR bridge for the tame Kummer lemma (S6h)

If `C_P` is a discrete valuation ring at a prime `P` of the Noetherian `R`-algebra `C` over `𝔪`,
and `s` generates `𝔪` locally (`g s`-form) and is regular on `C`, then the element data of
`FormalKummer.exists_cuspLoc_of_tame` hold at `P` with `e = e(P | 𝔪)` the ramification index
(Mathlib's `Ideal.ramificationIdx`, the length of `C_P / 𝔪 C_P`):
**`FormalKummer.uniformizer_data_of_dvr`**. Hence
(**`FormalKummer.exists_cuspLoc_of_tame_of_dvr`**) the tame Kummer lemma holds if all `C_P`
(`P` over `𝔪`) are DVRs with ramification indices dividing `N`.
-/

open Polynomial IsLocalRing TensorProduct

universe u

namespace SemistableReduction

namespace FormalKummer

/-- **Uniformizer data from a DVR**: `π ∈ P` with `P C_P = π C_P` and `s = unit · π^{e(P|𝔪)}` in
`C_P`, all witnessed by elements of `C`. -/
theorem uniformizer_data_of_dvr {R C : Type*} [CommRing R] [CommRing C] [Algebra R C]
    [IsNoetherianRing C] (𝔪 : Ideal R) {s : R} (hs : s ∈ 𝔪)
    (hU : ∃ g ∉ 𝔪, ∀ r ∈ 𝔪, ∃ r', g * r = s * r')
    (hsC : IsSMulRegular C (algebraMap R C s)) (P : Ideal C) [P.IsPrime] [P.LiesOver 𝔪]
    [IsDomain (Localization.AtPrime P)] [IsDiscreteValuationRing (Localization.AtPrime P)] {N : ℕ}
    (hN : P.ramificationIdx R ∣ N) :
    ∃ (π : C) (e : ℕ), 0 < e ∧ e ∣ N ∧ π ∈ P ∧
      (∃ g ∉ P, ∀ x ∈ P, ∃ c, g * x = π * c) ∧
      (∃ a ∉ P, ∃ w ∉ P, w * algebraMap R C s = a * π ^ e) := by
  classical
  set Sq := Localization.AtPrime P
  let φ := algebraMap C Sq
  have hunit (x : C) : IsUnit (φ x) ↔ x ∉ P := IsLocalization.AtPrime.isUnit_to_map_iff Sq P x
  have hmaxm (x : C) : φ x ∈ maximalIdeal Sq ↔ x ∈ P :=
    IsLocalization.AtPrime.to_map_mem_maximal_iff Sq P x
  have hP𝔪 (r : R) : algebraMap R C r ∈ P ↔ r ∈ 𝔪 := by
    rw [Ideal.over_def P 𝔪]
    exact Iff.rfl
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Sq
  obtain ⟨⟨π, t⟩, hπt⟩ := IsLocalization.surj P.primeCompl ϖ
  have hπirr : Irreducible (φ π) := by
    change Irreducible (algebraMap C Sq π)
    rw [← hπt]
    exact (irreducible_mul_isUnit (IsLocalization.map_units Sq t)).mpr hϖ
  have hmaxπ : maximalIdeal Sq = Ideal.span {φ π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hπirr
  have hπP : π ∈ P := (hmaxm π).mp (hmaxπ ▸ Ideal.mem_span_singleton_self _)
  have hs0 : φ (algebraMap R C s) ≠ 0 := by
    intro h
    rw [← map_zero φ, IsLocalization.eq_iff_exists P.primeCompl] at h
    obtain ⟨c, hc⟩ := h
    have hc0 : (c : C) = 0 := hsC (by
      change algebraMap R C s * (c : C) = algebraMap R C s * 0
      rw [mul_zero, mul_comm, hc, mul_zero])
    exact c.2 (hc0 ▸ P.zero_mem)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hπirr
  have hsq : algebraMap R Sq s = ↑u * φ π ^ n := by
    rw [IsScalarTower.algebraMap_apply R C Sq]
    exact hu
  have hmap : 𝔪.map (algebraMap R Sq) = maximalIdeal Sq ^ n := by
    rw [hmaxπ, Ideal.span_singleton_pow]
    refine le_antisymm ?_ ((Ideal.span_singleton_le_iff_mem _).mpr ?_)
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      obtain ⟨g, hg, hgr⟩ := hU
      obtain ⟨r', hr'⟩ := hgr r hr
      rw [Ideal.mem_comap, Ideal.mem_span_singleton']
      have hgu : IsUnit (algebraMap R Sq g) := by
        rw [IsScalarTower.algebraMap_apply R C Sq, hunit, hP𝔪]
        exact hg
      refine ⟨↑hgu.unit⁻¹ * algebraMap R Sq r' * ↑u, ?_⟩
      have h1 : algebraMap R Sq g * algebraMap R Sq r = algebraMap R Sq s * algebraMap R Sq r' := by
        rw [← map_mul, hr', map_mul]
      have h2 : ↑hgu.unit⁻¹ * algebraMap R Sq g = 1 := IsUnit.val_inv_mul _
      linear_combination (-(↑hgu.unit⁻¹ : Sq)) * h1 -
        (↑hgu.unit⁻¹ : Sq) * algebraMap R Sq r' * hsq + algebraMap R Sq r * h2
    · have : φ π ^ n = ↑u⁻¹ * algebraMap R Sq s := by
        rw [hsq, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hs)
  have he : P.ramificationIdx R = n := by
    rw [Ideal.ramificationIdx_eq 𝔪 P, hmap,
      IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    rfl
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, mul_one] at hu
      have h1 : IsUnit (φ (algebraMap R C s)) := hu ▸ u.isUnit
      exact (hunit _).mp h1 ((hP𝔪 s).mpr hs)
    · exact h
  -- the unit
  obtain ⟨⟨a, w'⟩, haw'⟩ := IsLocalization.surj P.primeCompl (↑u : Sq)
  have haP : a ∉ P := by
    rw [← hunit]
    change IsUnit (algebraMap C Sq a)
    rw [← haw']
    exact u.isUnit.mul (IsLocalization.map_units Sq w')
  have hrel : φ (w' * algebraMap R C s) = φ (a * π ^ n) := by
    change algebraMap C Sq (w' * algebraMap R C s) = algebraMap C Sq (a * π ^ n)
    rw [map_mul, map_mul, map_pow, ← haw']
    change algebraMap C Sq w' * φ (algebraMap R C s) = _
    rw [hu]
    ring
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists P.primeCompl Sq).mp hrel
  have hnotmul {x y : C} (hx : x ∉ P) (hy : y ∉ P) : x * y ∉ P := fun h ↦
    (Ideal.IsPrime.mem_or_mem ‹_› h).elim hx hy
  refine ⟨π, n, hn, he ▸ hN, hπP, ?_, ⟨↑c * a, hnotmul (x := ↑c) c.2 haP, ↑c * ↑w',
    hnotmul (x := ↑c) (y := ↑w') c.2 w'.2, by linear_combination hc⟩⟩
  -- the generator data
  have key (x : C) (hx : x ∈ P) : ∃ h ∉ P, ∃ c, h * x = π * c := by
    have hφx : φ x ∈ Ideal.span {φ π} := hmaxπ ▸ (hmaxm x).mpr hx
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hφx
    obtain ⟨⟨c', t'⟩, hct⟩ := IsLocalization.surj P.primeCompl y
    have h1 : φ (t' * x) = φ (π * c') := by
      change algebraMap C Sq (t' * x) = algebraMap C Sq (π * c')
      rw [map_mul, map_mul, ← hct]
      change algebraMap C Sq ↑t' * φ x = φ π * (y * algebraMap C Sq ↑t')
      rw [← hy]
      ring
    obtain ⟨m, hm⟩ := (IsLocalization.eq_iff_exists P.primeCompl Sq).mp h1
    exact ⟨↑m * ↑t', hnotmul (x := ↑m) (y := ↑t') m.2 t'.2, ↑m * c', by linear_combination hm⟩
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian P : P.FG)
  choose! h hhP cx hcx using key
  have hSP : ∀ x ∈ S, x ∈ P := fun x hx ↦ hS ▸ Submodule.subset_span hx
  refine ⟨∏ x ∈ S, h x, ?_, fun x hx ↦ ?_⟩
  · refine Finset.prod_induction _ (fun z ↦ z ∉ P) (fun _ _ ha hb ↦ hnotmul ha hb) ?_
      fun x hx ↦ hhP x (hSP x hx)
    exact fun h1 ↦ Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).mpr h1)
  · rw [← hS] at hx
    induction hx using Submodule.span_induction with
    | mem x hxS =>
      refine ⟨(∏ y ∈ S.erase x, h y) * cx x, ?_⟩
      rw [← Finset.mul_prod_erase S h hxS]
      linear_combination (∏ y ∈ S.erase x, h y) * hcx x (hSP x hxS)
    | zero => exact ⟨0, by rw [mul_zero, mul_zero]⟩
    | add x y _ _ h1 h2 =>
      obtain ⟨c1, hc1⟩ := h1
      obtain ⟨c2, hc2⟩ := h2
      exact ⟨c1 + c2, by rw [mul_add, hc1, hc2, mul_add]⟩
    | smul a x _ h1 =>
      obtain ⟨c1, hc1⟩ := h1
      exact ⟨a * c1, by rw [smul_eq_mul, mul_left_comm, hc1]; ring⟩

/-- **The tame Kummer lemma, DVR form**: if `C` is finite flat over `R` and at every prime `P`
over `𝔪` the localization `C_P` is a DVR with ramification index `e(P|𝔪) ∣ N`, `N` invertible in
`k`, then `R̂_𝔪 ⊗_R C ≅ ∏ᵢ R̂_𝔪[t]/(t^{dᵢ} − s)` with `0 < dᵢ ∣ N`. -/
theorem exists_cuspLoc_of_tame_of_dvr {k : Type*} {R C : Type u} [Field k] [IsAlgClosed k]
    [CommRing R] [Algebra k R] [IsNoetherianRing R] [CommRing C] [Algebra R C]
    [Module.Finite R C] [Module.Flat R C] (𝔪 : Ideal R) [𝔪.IsMaximal]
    (hres : Function.Surjective ((Ideal.Quotient.mk 𝔪).comp (algebraMap k R)))
    {s : R} (hs : s ∈ 𝔪) (hsreg : IsSMulRegular R s)
    (hU : ∃ g ∉ 𝔪, ∀ r ∈ 𝔪, ∃ r', g * r = s * r')
    {N : ℕ} (hN : (N : k) ≠ 0)
    (hP : ∀ (P : Ideal C) [P.IsPrime] [P.LiesOver 𝔪], ∃ _ : IsDomain (Localization.AtPrime P),
      IsDiscreteValuationRing (Localization.AtPrime P) ∧ P.ramificationIdx R ∣ N) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (∀ i, 0 < d i) ∧ (∀ i, d i ∣ N) ∧
      Nonempty (AdicCompletion 𝔪 R ⊗[R] C ≃ₐ[AdicCompletion 𝔪 R]
        ∀ i, AdjoinRoot (X ^ d i - Polynomial.C (algebraMap R (AdicCompletion 𝔪 R) s))) := by
  haveI : IsNoetherianRing C := IsNoetherianRing.of_finite R C
  refine exists_cuspLoc_of_tame 𝔪 hres hs hsreg hU hN fun P hP' ↦ ?_
  haveI : P.IsPrime := hP'.1
  haveI : P.LiesOver 𝔪 := hP'.2
  obtain ⟨_, hdvr, hdiv⟩ := hP P
  exact uniformizer_data_of_dvr 𝔪 hs hU hsreg.of_flat P hdiv

end FormalKummer

end SemistableReduction
