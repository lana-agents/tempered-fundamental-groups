/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.UniqueExtDVR
import TemperedFundamentalGroups.SemistableReduction.HenselComplete

/-!
# Finite extensions of complete DVRs (setting of `Statement.ZariskiConnected`)

Let `K` be a field, `O ⊆ K` a complete discrete valuation ring, `K' / K` a finite extension and
`O' ⊆ K'` a valuation subring lying over `O` which is a discrete valuation ring.

* `mem_iff_spectralNorm_le_one`: `O'` is the closed unit ball of the spectral norm on `K'` (for
  the norm `DVRNorm.normedField O` on `K`), by uniqueness of the extension
  (`CrossingAux.eq_of_comap_eq_dvr`).
* `algebra`, `mem_iff_isIntegral`, `isIntegralClosure`, `finite`: with the `O`-algebra structure
  induced by `K → K'`, `O'` is the integral closure of `O` in `K'` and a finite `O`-module.
* `isAdicComplete_maximalIdeal`: `O'` is complete for its maximal ideal: `𝔪'`-adic Cauchy
  sequences are Cauchy for the (complete) spectral norm and the unit ball is closed.
-/

open IsLocalRing Filter Topology

namespace TemperedFundamentalGroups.SemistableReduction.ZariskiDVR

variable {K : Type*} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  [IsAdicComplete (maximalIdeal O) O] {K' : Type*} [Field K'] [Algebra K K']
  [FiniteDimensional K K'] {O' : ValuationSubring K'}

/-- **Unit ball.** A valuation subring `O'` of `K'` lying over `O` is the closed unit ball of the
spectral norm. -/
theorem mem_iff_spectralNorm_le_one (h : O'.comap (algebraMap K K') = O) (x : K') :
    letI := DVRNorm.normedField O; x ∈ O' ↔ spectralNorm K K' x ≤ 1 := by
  letI := DVRNorm.normedField O
  haveI := DVRNorm.isUltrametricDist O
  haveI := DVRNorm.completeSpace O
  letI : NontriviallyNormedField K' := spectralNorm.nontriviallyNormedField K K'
  haveI : IsUltrametricDist K' :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm isNonarchimedean_spectralNorm
  have hV : (_root_.SemistableReduction.HenselComplete.integers K').comap (algebraMap K K') =
      O := by
    ext y
    rw [ValuationSubring.mem_comap, _root_.SemistableReduction.HenselComplete.mem_integers_iff,
      ← DVRNorm.norm_le_one_iff O]
    change spectralNorm K K' _ ≤ 1 ↔ _
    rw [spectralNorm_extends]
  rw [CrossingAux.eq_of_comap_eq_dvr O h hV,
    _root_.SemistableReduction.HenselComplete.mem_integers_iff]
  rfl

/-- The `O`-algebra structure on `O'` given by restricting `algebraMap K K'`. -/
@[implicit_reducible]
noncomputable def algebra (h : O'.comap (algebraMap K K') = O) : Algebra O O' :=
  ((algebraMap K K').restrict O O' fun x hx ↦ by
    rw [← h] at hx
    exact hx).toAlgebra

/-- The composite `O`-algebra structure on `K'`. -/
@[implicit_reducible]
noncomputable def algebraTop : Algebra O K' :=
  ((algebraMap K K').comp (algebraMap O K)).toAlgebra

/-- **Integral closure.** `O'` is the integral closure of `O` in `K'`. -/
theorem mem_iff_isIntegral (h : O'.comap (algebraMap K K') = O) (x : K') :
    letI := algebraTop O (K' := K'); x ∈ O' ↔ IsIntegral O x := by
  letI := algebraTop O (K' := K')
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI := DVRNorm.normedField O
  rw [mem_iff_spectralNorm_le_one O h, spectralNorm,
    spectralValue_le_one_iff (minpoly.monic (Algebra.IsIntegral.isIntegral x))]
  simp only [DVRNorm.norm_le_one_iff]
  constructor
  · intro hc
    have hl : minpoly K x ∈ Polynomial.lifts (algebraMap O K) := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      exact fun n ↦ ⟨⟨_, hc n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl
      (minpoly.monic (Algebra.IsIntegral.isIntegral x))
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap K, hq, minpoly.aeval]
  · intro hi n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hi, Polynomial.coeff_map]
    exact ((minpoly O x).coeff n).2

theorem isIntegralClosure (h : O'.comap (algebraMap K K') = O) :
    letI := algebra O h; letI := algebraTop O (K' := K'); IsIntegralClosure O' O K' := by
  letI := algebra O h
  letI := algebraTop O (K' := K')
  exact ⟨Subtype.val_injective, fun {x} ↦ by
    rw [← mem_iff_isIntegral O h]
    exact ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ ↦ hy ▸ y.2⟩⟩

/-- **Finiteness.** `O'` is a finite `O`-module (`K` has characteristic `0`, so `K' / K` is
separable). -/
theorem finite [CharZero K] (h : O'.comap (algebraMap K K') = O) :
    letI := algebra O h; Module.Finite O O' := by
  letI := algebra O h
  letI := algebraTop O (K' := K')
  haveI : IsScalarTower O K K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower O O' K' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := isIntegralClosure O h
  exact IsIntegralClosure.finite O K K' O'

/-- **Completeness.** A discrete valuation ring `O'` lying over a complete DVR `O` in a finite
extension is `𝔪'`-adically complete. -/
theorem isAdicComplete_maximalIdeal (h : O'.comap (algebraMap K K') = O)
    [IsDiscreteValuationRing O'] : IsAdicComplete (maximalIdeal O') O' := by
  letI := DVRNorm.normedField O
  haveI := DVRNorm.isUltrametricDist O
  haveI := DVRNorm.completeSpace O
  letI : NontriviallyNormedField K' := spectralNorm.nontriviallyNormedField K K'
  haveI : CompleteSpace K' := spectralNorm.completeSpace K K'
  have hmem (x : K') : x ∈ O' ↔ ‖x‖ ≤ 1 := mem_iff_spectralNorm_le_one O h x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hϖ0' : (ϖ : K') ≠ 0 := fun h0 ↦ hϖ.ne_zero (Subtype.ext h0)
  have hϖ0 : 0 < ‖(ϖ : K')‖ := norm_pos_iff.2 hϖ0'
  have hϖ1 : ‖(ϖ : K')‖ < 1 := by
    refine lt_of_le_of_ne ((hmem _).1 ϖ.2) fun h1 ↦ hϖ.not_isUnit ?_
    have hinv : (ϖ : K')⁻¹ ∈ O' := (hmem _).2 (by rw [norm_inv, h1, inv_one])
    exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O') (Subtype.ext (mul_inv_cancel₀ hϖ0'))
  have hpow (a : O') (n : ℕ) :
      a ∈ (maximalIdeal O' ^ n • ⊤ : Submodule O' O') ↔ ‖(a : K')‖ ≤ ‖(ϖ : K')‖ ^ n := by
    have hpos : 0 < ‖(ϖ : K')‖ ^ n := pow_pos hϖ0 n
    rw [smul_eq_mul, Ideal.mul_top, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      have hc : ‖(c : K')‖ ≤ 1 := (hmem _).1 c.2
      calc ‖((ϖ ^ n * c : O') : K')‖ = ‖(ϖ : K')‖ ^ n * ‖(c : K')‖ := by
            rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow]
        _ ≤ ‖(ϖ : K')‖ ^ n := mul_le_of_le_one_right hpos.le hc
    · intro ha
      have hc : (a : K') / (ϖ : K') ^ n ∈ O' := (hmem _).2 (by
        rw [norm_div, norm_pow]
        exact (div_le_one hpos).2 ha)
      refine ⟨⟨_, hc⟩, Subtype.ext ?_⟩
      rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      field_simp
  refine { toIsHausdorff := inferInstance, toIsPrecomplete := ⟨fun f hf ↦ ?_⟩ }
  have hf' {m n : ℕ} (hmn : m ≤ n) : ‖(f m : K') - f n‖ ≤ ‖(ϖ : K')‖ ^ m := by
    have := (hpow _ m).1 (SModEq.sub_mem.1 (hf hmn))
    simpa using this
  set u : ℕ → K' := fun n ↦ f n
  have hcauchy : CauchySeq u := by
    refine Metric.cauchySeq_iff'.2 fun ε hε ↦ ?_
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hϖ1
    refine ⟨N, fun n hn ↦ ?_⟩
    rw [dist_eq_norm, norm_sub_rev]
    exact (hf' hn).trans_lt hN
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hy1 : ‖y‖ ≤ 1 :=
    le_of_tendsto' ((continuous_norm.tendsto y).comp hy) fun n ↦ (hmem _).1 (f n).2
  refine ⟨⟨y, (hmem y).2 hy1⟩, fun n ↦ SModEq.sub_mem.2 ((hpow _ n).2 ?_)⟩
  have hlim : Tendsto (fun m ↦ ‖(f n : K') - u m‖) atTop (𝓝 ‖(f n : K') - y‖) :=
    (continuous_norm.tendsto _).comp (tendsto_const_nhds.sub hy)
  simpa using le_of_tendsto hlim (eventually_atTop.2 ⟨n, fun m hm ↦ hf' hm⟩)

end TemperedFundamentalGroups.SemistableReduction.ZariskiDVR
