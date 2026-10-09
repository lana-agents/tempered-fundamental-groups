/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.WModel
import TemperedFundamentalGroups.SemistableReduction.GaussTreeNormal

/-!
# Local rings of W-models at generic points of the special fibre (Blueprint §10.3.8, I4)

Let `A = R[g j / g i] ⊆ L` be a chart of the projective model `projModel R g` of a family of
functions `g` of a field `L` over the image `R` of a noetherian ring, and `𝔭` a prime of `A`.

* `LocalSubring.ofPrime_mem_or_inv_mem`: if `A` is noetherian, `𝔭` is minimal over a nonzero
  principal ideal `(a)` and the local ring `A_𝔭 ⊆ L` is integrally closed in `L` with fraction
  field `L`, then `A_𝔭` is a valuation subring of `L` (Krull's principal ideal theorem: `A_𝔭` has
  dimension one, so it is a discrete valuation ring);
* `localSubring_props`: if the points of `projModel R g` are those of the normalization in `L`
  of a Gauss-tree model `gaussJoinModel O' a b` of `K'(x)` (`L` algebraic over `K'(x)`), the local
  rings `A_𝔭` are integrally closed in `L` (local rings of integrally closed charts) and have
  fraction field `L` (every function is a quotient of integral functions over a Gauss chart);
* `isNoetherianRing_projChart`: the charts are noetherian.

`projChart_mem_or_inv_mem` combines them: for a W-model (`ModelCode.IsWModelOf`), the local ring
of a chart at a prime minimal over the uniformizer is a valuation subring of the function field.
-/

universe u

open IsLocalRing SemistableReduction ZariskiModel

namespace TemperedFundamentalGroups

/-- **A local ring of a noetherian subring at a prime minimal over a nonzero principal ideal is a
valuation ring** if it is integrally closed in `F` with fraction field `F`. -/
theorem LocalSubring.ofPrime_mem_or_inv_mem {F : Type*} [Field F] (A : Subring F)
    [IsNoetherianRing A] (p : Ideal A) [p.IsPrime] {a : A} (ha : (a : F) ≠ 0)
    (hmin : p ∈ (Ideal.span {a}).minimalPrimes)
    (hint : ∀ x : F, IsIntegral (LocalSubring.ofPrime A p).toSubring x →
      x ∈ (LocalSubring.ofPrime A p).toSubring)
    (hfrac : ∀ x : F, ∃ y ∈ (LocalSubring.ofPrime A p).toSubring,
      ∃ z ∈ (LocalSubring.ofPrime A p).toSubring, x = y / z) (x : F) :
    x ∈ (LocalSubring.ofPrime A p).toSubring ∨ x⁻¹ ∈ (LocalSubring.ofPrime A p).toSubring := by
  set S := (LocalSubring.ofPrime A p).toSubring
  haveI : IsNoetherianRing S := IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  haveI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  haveI : IsFractionRing S F := IsFractionRing.of_field _ _ fun x ↦ by
    obtain ⟨y, hy, z, hz, rfl⟩ := hfrac x
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, rfl⟩
  haveI : IsIntegrallyClosed S := (isIntegrallyClosed_iff F).2 fun {x} hx ↦ ⟨⟨x, hint x hx⟩, rfl⟩
  set a' := algebraMap A S a
  have hmap : p.map (algebraMap A S) = maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal p S
  have hcomap : (maximalIdeal S).comap (algebraMap A S) = p :=
    IsLocalization.AtPrime.under_maximalIdeal S p
  have ha'0 : a' ≠ 0 := fun h ↦ ha (congrArg Subtype.val h)
  have ha'm : a' ∈ maximalIdeal S := by
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ (hmin.1.2 (Ideal.mem_span_singleton_self a))
  have hmmin : maximalIdeal S ∈ (Ideal.span {a'}).minimalPrimes := by
    refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 ha'm⟩, ?_⟩
    rintro P ⟨hP, haP⟩ hPm
    have hq : p ≤ P.comap (algebraMap A S) := by
      refine hmin.2 ⟨Ideal.comap_isPrime _ _, (Ideal.span_singleton_le_iff_mem _).2 ?_⟩ ?_
      · change a' ∈ P
        exact (Ideal.span_singleton_le_iff_mem _).1 haP
      · exact (Ideal.comap_mono hPm).trans hcomap.le
    rw [← hmap, ← IsLocalization.map_under p.primeCompl S P]
    exact Ideal.map_mono hq
  have hht : (maximalIdeal S).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmmin
  have hm0 : maximalIdeal S ≠ ⊥ := fun h ↦ ha'0 (by rw [h] at ha'm; exact ha'm)
  have hnf : ¬ IsField S := fun h ↦ hm0 ((isField_iff_maximalIdeal_eq).1 h)
  have hval : ValuationRing S := by
    have key : IsIntegrallyClosed S ∧ ∃! P : Ideal S, P ≠ ⊥ ∧ P.IsPrime := by
      refine ⟨inferInstance, maximalIdeal S, ⟨hm0, inferInstance⟩, ?_⟩
      rintro P ⟨hP0, hP⟩
      have hPm : P ≤ maximalIdeal S := le_maximalIdeal hP.ne_top
      by_contra hne
      have hlt : P < maximalIdeal S := lt_of_le_of_ne hPm hne
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h0 : P.height = 0 := by
        by_contra h
        have : 1 ≤ P.height := Order.one_le_iff_ne_zero.2 h
        have : (2 : ℕ∞) ≤ 1 :=
          le_trans (by simpa [one_add_one_eq_two] using add_le_add_left this 1) (h1.trans hht)
        exact absurd this (by decide)
      exact hP0 (Ideal.height_eq_zero_iff_eq_bot.1 h0)
    exact ((IsDiscreteValuationRing.TFAE S hnf).out 3 1).1 key
  rcases ValuationRing.isInteger_or_isInteger S x with ⟨y, hy⟩ | ⟨y, hy⟩
  · left; rw [← hy]; exact y.2
  · right; rw [← hy]; exact y.2

/-- Every chart of the join of the Gauss lines has fraction field `K(X)`. -/
lemma isFractionRing_gaussJoinModel_chart {K : Type u} [Field K] {Γ₀ : Type*}
    [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {ι : Type*} [Fintype ι]
    [Nonempty ι] {a c : ι → K} (hc : ∀ i, c i ≠ 0) {G : Subring (RatFunc K)}
    (hG : G ∈ (gaussJoinModel v a c).charts) : IsFractionRing G (RatFunc K) := by
  obtain ⟨f, hf, rfl⟩ := mem_iJoin_charts.1 hG
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hle : f i ≤ baseRing (RatFunc K) v.valuationSubring ⊔ ⨆ i, f i :=
    le_sup_of_le_right (le_iSup f i)
  have h := isGaussCoord_gaussCoord (v := v) (a := a i) (c := c i)
    (r := Units.mk0 (v (c i)) ((v.ne_zero_iff).2 (hc i))) rfl
  rcases mem_line_charts.1 (hf i) with h' | h'
  · exact h.isFractionRing_of_le (h' ▸ hle)
  · exact h.inv.isFractionRing_of_le (h' ▸ hle)

/-- **Local rings of a projective model with the points of a normalized Gauss-tree model** are
integrally closed in `L` and have fraction field `L`. -/
theorem localSubring_props {K' L : Type u} [Field K'] [Field L] [Algebra K' L]
    [Algebra (RatFunc K') L] [IsScalarTower K' (RatFunc K') L]
    [Algebra.IsAlgebraic (RatFunc K') L] (O' : ValuationSubring K') {ι : Type} [Fintype ι]
    [Nonempty ι] (a b : ι → K') (hb : ∀ i, b i ≠ 0) {κ : Type*} [Fintype κ] (g : κ → L)
    (hpts : (projModel (baseRing L O'.valuation.valuationSubring) g).points =
      ((gaussJoinModel O'.valuation a b).normalization L).points)
    (i : κ) (p : Ideal (projChart (baseRing L O'.valuation.valuationSubring) g i)) [p.IsPrime] :
    (∀ x : L, IsIntegral (LocalSubring.ofPrime _ p).toSubring x →
      x ∈ (LocalSubring.ofPrime _ p).toSubring) ∧
    (∀ x : L, ∃ y ∈ (LocalSubring.ofPrime _ p).toSubring,
      ∃ z ∈ (LocalSubring.ofPrime _ p).toSubring, x = y / z) := by
  obtain ⟨W, hAW, hcen⟩ := exists_centerIdeal_eq _ p
  subst hcen
  rw [← localAt_eq_localSubringOfPrime hAW]
  have hpt : localAt (projChart (baseRing L O'.valuation.valuationSubring) g i) W ∈
      (projModel (baseRing L O'.valuation.valuationSubring) g).points :=
    ⟨_, mem_projModel_charts.2 ⟨i, rfl⟩, W, hAW, rfl⟩
  rw [hpts] at hpt
  obtain ⟨C, hC, W', hCW', hloc⟩ := hpt
  rw [← hloc]
  obtain ⟨G, hG, rfl⟩ := mem_normalization_charts.1 hC
  refine ⟨fun x hx ↦ isIntegral_mem_localAt (fun y hy ↦ normChart_isIntegral G hy) hx,
    fun u ↦ ?_⟩
  haveI := isFractionRing_gaussJoinModel_chart hb hG
  haveI : IsScalarTower G (RatFunc K') L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have halg : IsAlgebraic G u :=
    (IsFractionRing.isAlgebraic_iff G (RatFunc K') L).2 (Algebra.IsAlgebraic.isAlgebraic u)
  obtain ⟨y, hy0, hyint⟩ := halg.exists_integral_multiple
  let φ : G →+* G.map (algebraMap (RatFunc K') L) :=
    ((algebraMap (RatFunc K') L).comp G.subtype).codRestrict _ fun z ↦ ⟨z, z.2, rfl⟩
  have hint : IsIntegral (G.map (algebraMap (RatFunc K') L)) (y • u) :=
    IsIntegral.map_of_comp_eq φ (RingHom.id L) rfl hyint
  have hyC : algebraMap G L y ∈ normChart L G := map_le_normChart G ⟨y, y.2, rfl⟩
  have hyuC : y • u ∈ normChart L G := hint
  have hy0' : algebraMap G L y ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply G (RatFunc K') L]
    exact (map_ne_zero _).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_of_ne_zero hy0))
  refine ⟨_, le_localAt hyuC, _, le_localAt hyC, ?_⟩
  rw [Algebra.smul_def, mul_div_cancel_left₀ _ hy0']

/-- The charts `R[g j / g i]` over the image `R` of a noetherian ring are noetherian. -/
lemma isNoetherianRing_projChart {O F : Type*} [CommRing O] [IsNoetherianRing O] [Field F]
    [Algebra O F] {R : Subring F} (hR : (algebraMap O F).range = R) {κ : Type*} [Finite κ]
    (g : κ → F) (i : κ) : IsNoetherianRing (projChart R g i) := by
  have h : projChart R g i = (MvPolynomial.aeval (R := O) fun j ↦ g j / g i).toRingHom.range := by
    rw [projChart, ← hR, RingHom.coe_range, ← Algebra.adjoin_eq_ring_closure,
      Algebra.adjoin_range_eq_range_aeval]
    rfl
  rw [h]
  exact isNoetherianRing_range _

end TemperedFundamentalGroups
