/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalFormula
import TemperedFundamentalGroups.SemistableReduction.W7Statement

/-!
# Smooth points of the vertex chart and the local `δ`-invariants

Blueprint §9.12, O12 / R5. Let `R' = DRint 0 1 K` be the integral closure of the vertex chart
`O_C[x]` in `K` and `Λ = redRing C K x ⊆ Π_w κ(w)` the reduced chart (`ChartLocal`). The
reduction `R' → Λ` is surjective (maximum principle `SmoothVertex.isIntegral_of_le`) and its
kernel lies in every maximal ideal over the residue point `(𝔪_C, x)`. Hence:

* `exists_forall_dl_eq_dinf_x`: the jet-order `δ`-invariants of the chart stabilize;
* **`isDiscSmooth_of_dinf`**: a point of `R'` over the residue point whose image `𝔫` has
  `δ_𝔫 = 0` is smooth (`SmoothVertex.IsDiscSmooth`);
* **`dinf_eq_zero_of_isDiscSmooth`**: conversely;
* **`tot0_eq_zero_iff`**: the total `δ` over `x̄ = 0` vanishes iff every point of `R'` over the
  residue point is smooth.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal

namespace SemistableReduction

namespace DiscBridge

open GaussFibre ChartLocal DeltaCount SmoothVertex DiscCount FundamentalInequality GaussStability
  LocalFormula

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

attribute [local instance] isCurveFunctionField isCurveFunctionField_F
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]

/-! ### Stabilization of the jet-order `δ`-invariants -/

include hp hp1 in
/-- The `δ`-invariants of the chart at `x` stabilize uniformly. -/
theorem exists_forall_dl_eq_dinf_x
    (hΛ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K))) :
    ∃ M₁ : ℕ, ∀ M, M₁ ≤ M → ∀ 𝔫 : Ideal (redRing C K (xF C K)), 𝔫.IsMaximal →
      dl 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛ 𝔫 M =
        dinf 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛ 𝔫 := by
  classical
  have hsum := sum_inertiaDeg_eq (F := K) hp hp1
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (F := K) ramificationIdx_eq_one hsum
  obtain ⟨σ₀, hσ₀, hσ₀0, hσ₀c⟩ := exists_conductor_x hb hsum
  obtain ⟨σi, hσi, hσi0, hσic⟩ := exists_conductor_x_inv hb hsum
  obtain ⟨M₀, hM₀⟩ := genus_eq_sum_delta_of_conductor hb hsum hσ₀ hσ₀0 hσ₀c hσi hσi0 hσic
  set B := (genus C K : ℕ) + Fintype.card (Ext C K)
  have hB₀ (M : ℕ) (hM : M₀ ≤ M) :
      ∑ y ∈ (points hΛ σ₀).filter (fun _ ↦ True), delta 𝓀 _ hΛ σ₀ y M ≤ B := by
    have h := hM₀ M hM
    rw [Finset.filter_true_of_mem fun _ _ ↦ trivial]
    have hG : 0 ≤ ∑ w : Ext C K, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ) :=
      Finset.sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
    have h1 : (0 : ℤ) ≤ ∑ y ∈ (points (isChart_x_inv hb) σi).filter (fun y ↦
        (⟨_, (isChart_x_inv hb).mem⟩ : redRing C K (xF C K)⁻¹) ∈ y),
        (delta 𝓀 _ (isChart_x_inv hb) σi y M : ℤ) :=
      Finset.sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
    have h2 : ((∑ y ∈ points hΛ σ₀, delta 𝓀 _ hΛ σ₀ y M : ℕ) : ℤ) ≤ B := by
      push_cast; simp only [B]; push_cast; linarith
    exact_mod_cast h2
  obtain ⟨M₁, hM₁⟩ := exists_forall_dl_eq_dinf hΛ hσ₀ hσ₀0 hσ₀c (fun _ ↦ True) hB₀
  exact ⟨M₁, fun M hM 𝔫 h𝔫 ↦ hM₁ M hM 𝔫 h𝔫 trivial⟩

include hp hp1 in
/-- `δ_𝔫 = 0` means `δ` vanishes at every jet order. -/
theorem dl_eq_zero_of_dinf
    (hΛ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)))
    {𝔫 : Ideal (redRing C K (xF C K))} (h𝔫 : 𝔫.IsMaximal)
    (h0 : dinf 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛ 𝔫 = 0) (M : ℕ) :
    dl 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛ 𝔫 M = 0 := by
  obtain ⟨M₁, hM₁⟩ := exists_forall_dl_eq_dinf_x hp hp1 hΛ
  have h := hM₁ (max M M₁) (le_max_right _ _) 𝔫 h𝔫
  rw [h0] at h
  exact Nat.eq_zero_of_le_zero (h ▸ dl_mono hΛ h𝔫.ne_top (le_max_left _ _))

/-! ### The reduction of the vertex chart onto the reduced chart -/

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)] in
/-- Elements integral over `O_C[x]` are integral over `C[x]`. -/
lemma isIntegral_adjoin_of_discRing' {y : K} (hy : IsIntegral (discRing (0 : C) 1) y) :
    IsIntegral (Algebra.adjoin C {xF C K}) y := by
  have hmem : ∀ f : discRing (0 : C) 1,
      algebraMap (RatFunc C) K f ∈ Algebra.adjoin C {xF C K} := by
    rintro ⟨f, hf⟩
    obtain ⟨Q, -, rfl⟩ := mem_discRing_iff.1 hf
    change algebraMap (RatFunc C) K (algebraMap C[X] (RatFunc C) Q) ∈ _
    rw [← aeval_xF, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨Q, rfl⟩
  let ψ : discRing (0 : C) 1 →+* Algebra.adjoin C {xF C K} :=
    { toFun := fun f ↦ ⟨algebraMap (RatFunc C) K f, hmem f⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b ↦ Subtype.ext (by simp) }
  exact IsIntegral.map_of_comp_eq ψ (RingHom.id K) (RingHom.ext fun _ ↦ rfl) hy

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) K] in
lemma coe_mem_intRing (y : DRint (0 : C) 1 K) : (y : K) ∈ intRing C K (xF C K) :=
  ⟨isIntegral_adjoin_of_discRing' y.2, gnorm_le_iff.2 fun w ↦ valuation_le_one_D w y⟩

variable (K) in
/-- The reduction `R' → Λ`. -/
noncomputable def redΛ : DRint (0 : C) 1 K →+* redRing C K (xF C K) where
  toFun y := ⟨fun w ↦ red C (y : K) w, red_mem_redRing (coe_mem_intRing y)⟩
  map_one' := Subtype.ext (funext fun w ↦ map_one (redD w))
  map_mul' a b := Subtype.ext (funext fun w ↦ map_mul (redD w) a b)
  map_zero' := Subtype.ext (funext fun w ↦ map_zero (redD w))
  map_add' a b := Subtype.ext (funext fun w ↦ map_add (redD w) a b)

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) K] in
lemma redΛ_apply (y : DRint (0 : C) 1 K) (w : Ext C K) : (redΛ K y).1 w = redD w y := rfl

include hp hp1 in
lemma redΛ_surjective : Function.Surjective (redΛ (C := C) K) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, isIntegral_of_le hp hp1 hf.1 (valuation_le_one_of_mem_intRing hf)⟩, rfl⟩

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]
  [Algebra C K] [IsScalarTower C (RatFunc C) K] in
lemma constD_mem_of_lt {P' : Ideal (DRint (0 : C) 1 K)}
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K)) = discIdeal (0 : C) 1)
    (b : HenselComplete.integers C) (hb : ‖(b : C)‖ < 1) : constD b ∈ P' := by
  change algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K) _ ∈ P'
  rw [← Ideal.mem_comap, hP']
  refine ⟨Polynomial.C (b : C), fun i ↦ ?_, ?_, ?_⟩
  · rw [coeff_C]
    split_ifs
    · exact_mod_cast (HenselComplete.mem_integers_iff _).1 b.2
    · simp
  · simp [gaussCoord_zero_one]
  · rw [coeff_C_zero]
    exact_mod_cast hb

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]
  [Algebra C K] [IsScalarTower C (RatFunc C) K] in
lemma xD_mem {P' : Ideal (DRint (0 : C) 1 K)}
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K)) =
      discIdeal (0 : C) 1) : (xD : DRint (0 : C) 1 K) ∈ P' := by
  change algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K) _ ∈ P'
  rw [← Ideal.mem_comap, hP']
  refine ⟨X, fun i ↦ ?_, by simp [gaussCoord_zero_one], by simp⟩
  rw [coeff_X]
  split_ifs <;> simp

include hp hp1 in
/-- **The kernel of `R' → Λ` lies in every point over the residue point.** -/
lemma ker_le {P' : Ideal (DRint (0 : C) 1 K)} [hP'm : P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K)) =
      discIdeal (0 : C) 1) : RingHom.ker (redΛ (C := C) K) ≤ P' := by
  intro y hy
  have hy0 : ∀ w : Ext C K, w.1 (y : K) < 1 := fun w ↦ by
    have := congrArg (fun a : redRing C K (xF C K) ↦ a.1 w) (RingHom.mem_ker.1 hy)
    exact (red_eq_zero_iff (valuation_le_one_D w y)).1 this
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpn : (0 : ℝ≥0) < ‖(p : C)‖₊ := nnnorm_pos.2 hp0
  have hg : gnorm C (y : K) < 1 := (gnorm_lt_iff one_pos).2 hy0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpn hg
  set z : K := algebraMap C K (p : C)⁻¹ * (y : K) ^ n
  have hzint : IsIntegral (Algebra.adjoin C {xF C K}) z :=
    (isIntegral_algebraMap (x := (⟨algebraMap C K (p : C)⁻¹, Subalgebra.algebraMap_mem _ _⟩ :
      Algebra.adjoin C {xF C K}))).mul ((isIntegral_adjoin_of_discRing' y.2).pow n)
  have hz : ∀ w : Ext C K, w.1 z ≤ 1 := fun w ↦ by
    simp only [z, map_mul, map_pow, valuation_algebraMap_C', nnnorm_inv]
    have h1 : w.1 (y : K) ^ n ≤ gnorm C (y : K) ^ n := pow_le_pow_left₀ zero_le (le_gnorm w _) n
    calc ‖(p : C)‖₊⁻¹ * w.1 (y : K) ^ n ≤ ‖(p : C)‖₊⁻¹ * ‖(p : C)‖₊ :=
          mul_le_mul_right (h1.trans hn.le) _
      _ = 1 := inv_mul_cancel₀ hpn.ne'
  set zD : DRint (0 : C) 1 K := ⟨z, isIntegral_of_le hp hp1 hzint hz⟩
  have hpint : ‖((p : C))‖ ≤ 1 := hp1.le
  set pD : HenselComplete.integers C := ⟨(p : C), (HenselComplete.mem_integers_iff _).2 hpint⟩
  have heq : y ^ n = constD pD * zD := by
    apply Subtype.ext
    change (y : K) ^ n = algebraMap (RatFunc C) K (algebraMap C (RatFunc C) (p : C)) * z
    rw [← IsScalarTower.algebraMap_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0, map_one,
      one_mul]
  have : y ^ n ∈ P' := heq ▸ P'.mul_mem_right _ (constD_mem_of_lt hP' pD hp1)
  exact hP'm.isPrime.mem_of_pow_mem n this

/-! ### Points and branches -/

section Points

omit [CharZero C] in
lemma mem_zeros_of_lt {κ : Type*} [Field κ] [Algebra 𝓀 κ] [IsCurveFunctionField 𝓀 κ]
    {Q : CurvePlace 𝓀 κ} {x : κ}
    (hx : x ≠ 0) (h : Q.valuation x < 1) : Q ∈ PlaceNorm.zeros 𝓀 x := by
  rw [PlaceNorm.mem_zeros, ← Q.valuation_le_one_iff, map_inv₀, not_le,
    one_lt_inv₀ ((Valuation.pos_iff _).2 hx)]
  exact h

/-- The element `x̄` of the reduced chart. -/
noncomputable abbrev xbar
    (hΛ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K))) :
    redRing C K (xF C K) := ⟨fun w ↦ red C (xF C K) w, hΛ.mem⟩

variable (hΛ : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
  (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)))
include hΛ

omit [CharZero C] in
/-- The centre of a branch, pulled back to `R'`, is the point of the branch. -/
lemma comap_center (v : Ext C K) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C K) v)) :
    (center hΛ Q (xbar_mem_V v hQ)).comap (redΛ K) = placeIdealD v hQ := by
  ext y
  rw [Ideal.mem_comap, mem_center, mem_placeIdealD_iff, redΛ_apply,
    CurvePlace.res_eq_zero_iff Q (redD_mem_V v y (xbar_mem_V v hQ))]

omit [CharZero C] [FiniteDimensional (RatFunc C) K] [IsAlgClosed C] in
lemma redΛ_xD : redΛ K (xD : DRint (0 : C) 1 K) = xbar hΛ := rfl

variable {P' : Ideal (DRint (0 : C) 1 K)} [hP'm : P'.IsMaximal]
  (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K)) = discIdeal (0 : C) 1)
include hP'

omit hΛ in
include hp hp1 in
lemma comap_map : (P'.map (redΛ K)).comap (redΛ K) = P' := by
  rw [Ideal.comap_map_of_surjective _ (redΛ_surjective hp hp1), ← RingHom.ker_eq_comap_bot,
    sup_eq_left]
  exact ker_le hp hp1 hP'

omit hΛ in
include hp hp1 in
lemma map_isMaximal : (P'.map (redΛ K)).IsMaximal :=
  (Ideal.map_eq_top_or_isMaximal_of_surjective _ (redΛ_surjective hp hp1) hP'm).resolve_left
    fun h ↦ hP'm.ne_top (by rw [← comap_map hp hp1 hP', h, Ideal.comap_top])

omit [CharZero C] [FiniteDimensional (RatFunc C) K] hP'm [IsAlgClosed C] in
lemma xbar_mem_map : xbar hΛ ∈ P'.map (redΛ K) := by
  rw [← redΛ_xD hΛ]
  exact Ideal.mem_map_of_mem _ (xD_mem hP')

include hp hp1 in
/-- A branch of `𝔫 = ρ(P')` is a zero of `x̄` whose point is `P'`. -/
lemma of_mem_brs {b : Branch 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring)}
    (hb : b ∈ brs hΛ (P'.map (redΛ K))) :
    ∃ hQ : b.2 ∈ PlaceNorm.zeros 𝓀 (red C (xF C K) b.1), placeIdealD b.1 hQ = P' := by
  obtain ⟨v, Q⟩ := b
  have hne := (map_isMaximal hp hp1 hP').ne_top
  have hz := mem_V_of_mem_brs hΛ hne hb
  have hlt : Q.valuation (red C (xF C K) v) < 1 :=
    (mem_iff_of_mem_brs hΛ hne hb (xbar hΛ)).1 (xbar_mem_map hΛ hP')
  have hx0 : red C (xF C K) v ≠ 0 := fun h ↦ hΛ.tr v (h ▸ isAlgebraic_zero)
  have hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C K) v) := mem_zeros_of_lt hx0 hlt
  refine ⟨hQ, ?_⟩
  have hc : center hΛ Q (xbar_mem_V v hQ) = P'.map (redΛ K) := by
    rw [← centerOf_eq hΛ hz]; exact hb
  rw [← comap_center hΛ v hQ, hc, comap_map hp hp1 hP']

omit hP'm hP' in
include hp hp1 in
/-- A branch whose point is `P'` is a branch of `𝔫 = ρ(P')`. -/
lemma mem_brs_of (v : Ext C K) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C K) v)) (h : placeIdealD v hQ = P') :
    (⟨v, Q⟩ : Branch 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring)) ∈
      brs hΛ (P'.map (redΛ K)) := by
  have h2 := (comap_center hΛ v hQ).trans h
  have h1 := Ideal.map_comap_of_surjective (redΛ K) (redΛ_surjective hp hp1)
    (center hΛ Q (xbar_mem_V v hQ))
  rw [h2] at h1
  rw [mem_brs, centerOf_eq hΛ (b := ⟨v, Q⟩) (xbar_mem_V v hQ), ← h1]

include hp hp1 in
/-- **Smoothness from `δ = 0`**: if `δ` vanishes at every jet order at `ρ(P')`, then `P'` is a
smooth point (`SmoothVertex.IsDiscSmooth`). -/
theorem isDiscSmooth_of_dl
    (h0 : ∀ M, dl 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛ
      (P'.map (redΛ K)) M = 0) :
    IsDiscSmooth P' := by
  classical
  set 𝔫 := P'.map (redΛ K) with h𝔫def
  haveI h𝔫 : 𝔫.IsMaximal := map_isMaximal hp hp1 hP'
  have hne := h𝔫.ne_top
  obtain ⟨b₀, hb₀⟩ := exists_mem_brs hΛ h𝔫
  have hcard : (brsF hΛ 𝔫).card ≤ 1 := by
    have := card_sub_one_le_dl hΛ (𝔫 := 𝔫) (M := 1) le_rfl
    rw [h0] at this
    omega
  have huniq : ∀ b ∈ brs hΛ 𝔫, b = b₀ := fun b hb ↦
    Finset.card_le_one.1 hcard b ((mem_brsF hΛ hne).2 hb) b₀ ((mem_brsF hΛ hne).2 hb₀)
  obtain ⟨hQ, hPQ⟩ := of_mem_brs hp hp1 hΛ hP' hb₀
  obtain ⟨v, Q⟩ := b₀
  refine ⟨⟨v, Q, hQ⟩, ?_, fun α hα ↦ ?_⟩
  · ext ⟨v', Q', hQ'⟩
    simp only [Set.mem_singleton_iff]
    constructor
    · intro h
      have := huniq _ (mem_brs_of hp hp1 hΛ v' hQ' h)
      cases this
      rfl
    · intro h
      cases h
      exact hPQ
  · have hoth : ∀ R (hR : R ∈ PlaceNorm.zeros 𝓀 (red C (xF C K) v)), R ≠ Q →
        placeIdealD v hR ≠ placeIdealD v hQ := fun R hR hRQ heq ↦ by
      have := huniq _ (mem_brs_of hp hp1 hΛ v hR (heq.trans hPQ))
      cases this
      exact hRQ rfl
    have hb₀F : (⟨v, Q⟩ : Branch 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring)) ∈
        brsF hΛ 𝔫 := (mem_brsF hΛ hne).2 hb₀
    change ∃ y, ∃ s ∉ P', redD v y = α * redD v s
    rw [← hPQ]
    refine exists_eq_of_jets hp hp1 v hQ hoth fun M ↦ ?_
    haveI := finiteDimensional_regAt_quot hΛ.tr (fun b hb ↦ mem_V_of_mem_brsF hΛ hne hb) M
      (locSpace 𝓀 𝔫)
    have hall := (finrank_zero_iff_forall_zero).1 (h0 M)
    set a : Π w : Ext C K, ResidueField w.1.valuationSubring := Pi.single v α with ha_def
    have ha : a ∈ regAt 𝓀 _ (brsF hΛ 𝔫) := fun b hb ↦ by
      have := huniq b ((mem_brsF hΛ hne).1 hb)
      subst this
      simpa [a] using hα
    have hmem : a ∈ locSpace 𝓀 𝔫 ⊔ jetKer 𝓀 _ M (brsF hΛ 𝔫) := by
      have := (Submodule.Quotient.mk_eq_zero _).1 (hall (Submodule.Quotient.mk ⟨a, ha⟩))
      simpa using this
    obtain ⟨o, ho, kk, hk, hok⟩ := Submodule.mem_sup.1 hmem
    obtain ⟨s, hs𝔫, hso⟩ := mem_locSet_of_mem_locSpace hΛ ho
    obtain ⟨s', rfl⟩ := redΛ_surjective hp hp1 s
    obtain ⟨y', hy'⟩ := redΛ_surjective hp hp1 ⟨_, hso⟩
    refine ⟨y', s', fun hs' ↦ hs𝔫 (Ideal.mem_map_of_mem _ (hPQ ▸ hs')), ?_⟩
    have hy'v : redD v y' = redD v s' * o v := congrArg (fun z ↦ z.1 v) hy'
    have hs0 : redD v s' ≠ 0 := fun h ↦ hs𝔫 <| by
      rw [mem_iff_of_mem_brs hΛ hne hb₀, redΛ_apply, h, map_zero]
      exact zero_lt_one
    rw [hy'v, mul_div_cancel_left₀ _ hs0]
    have hov : o v - α = -kk v := by
      have := congrFun hok v
      simp only [Pi.add_apply, a, Pi.single_eq_same] at this
      rw [← this]
      ring
    rw [hov, Valuation.map_neg]
    exact hk _ hb₀F

include hp hp1 in
/-- **`δ = 0` at smooth points.** -/
theorem dl_eq_zero_of_isDiscSmooth (hs : IsDiscSmooth P') (M : ℕ) :
    dl 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛ (P'.map (redΛ K)) M = 0 := by
  classical
  set 𝔫 := P'.map (redΛ K) with h𝔫def
  haveI h𝔫 : 𝔫.IsMaximal := map_isMaximal hp hp1 hP'
  have hne := h𝔫.ne_top
  obtain ⟨⟨v, Q, hQ⟩, hbr, hloc⟩ := hs
  have hPQ : placeIdealD v hQ = P' := by
    have : (⟨v, Q, hQ⟩ : GaussTube.OuterBranch C K) ∈ discBranches P' := by rw [hbr]; rfl
    exact this
  have huniq : ∀ b ∈ brs hΛ 𝔫, b = ⟨v, Q⟩ := fun b hb ↦ by
    obtain ⟨hQb, hPb⟩ := of_mem_brs hp hp1 hΛ hP' hb
    have : (⟨b.1, b.2, hQb⟩ : GaussTube.OuterBranch C K) ∈ discBranches P' := hPb
    rw [hbr] at this
    obtain ⟨b1, b2⟩ := b
    cases this
    rfl
  have htop : (locSpace 𝓀 𝔫 ⊔ jetKer 𝓀 _ M (brsF hΛ 𝔫)).comap
      (regAt 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) (brsF hΛ 𝔫)).subtype =
        ⊤ := by
    refine eq_top_iff.2 fun a _ ↦ ?_
    rw [Submodule.mem_comap, Submodule.coe_subtype]
    have hb₀ := mem_brs_of hp hp1 hΛ v hQ hPQ
    have hα : (a : Π w : Ext C K, ResidueField w.1.valuationSubring) v ∈ Q.V :=
      a.2 ⟨v, Q⟩ ((mem_brsF hΛ hne).2 hb₀)
    obtain ⟨y, s, hsP, hys⟩ := hloc _ hα
    have hs0 : redD v s ≠ 0 := redD_ne_zero_of_notMem v hQ (by rwa [hPQ])
    obtain ⟨o, ho_def⟩ : ∃ o : Π w : Ext C K, ResidueField w.1.valuationSubring,
        o = fun w ↦ redD w y / redD w s := ⟨_, rfl⟩
    have hoL : o ∈ locSpace 𝓀 𝔫 := by
      refine subset_locSpace 𝔫 ⟨redΛ K (s * s), fun h ↦ ?_, ?_⟩
      · rw [map_mul] at h
        have hs𝔫 : redΛ K s ∈ 𝔫 := (h𝔫.isPrime.mem_or_mem h).elim id id
        apply hsP
        rw [← comap_map hp hp1 hP']
        exact hs𝔫
      · have : (redΛ K (s * s)).1 * o = (redΛ K (s * y)).1 := by
          funext w
          change redD w (s * s) * o w = redD w (s * y)
          rw [map_mul, map_mul, ho_def]
          by_cases h : redD w s = 0
          · rw [h]; ring
          · field_simp
        rw [this]
        exact (redΛ K (s * y)).2
    have hov : o v = (a : Π w : Ext C K, ResidueField w.1.valuationSubring) v := by
      rw [ho_def]
      change redD v y / redD v s = _
      rw [hys, mul_div_cancel_right₀ _ hs0]
    have hsplit : (a : Π w : Ext C K, ResidueField w.1.valuationSubring) = o + (a - o) := by
      ring
    rw [hsplit]
    refine add_mem (Submodule.mem_sup_left hoL) (Submodule.mem_sup_right fun b hb ↦ ?_)
    have := huniq b ((mem_brsF hΛ hne).1 hb)
    subst this
    simp [hov]
  rw [dl, htop]
  haveI : Subsingleton (regAt 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring)
      (brsF hΛ 𝔫) ⧸ (⊤ : Submodule 𝓀 (regAt 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring)
        (brsF hΛ 𝔫)))) :=
    Submodule.Quotient.subsingleton_iff.2 rfl
  exact Module.finrank_zero_of_subsingleton

end Points

/-! ### All points over the residue point -/

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)] in
/-- A finsum of natural numbers with finite support vanishes iff all its terms do. -/
lemma finsum_mem_eq_zero_iff_nat {α : Type*} {s : Set α} {f : α → ℕ}
    (h : (s ∩ Function.support f).Finite) : ∑ᶠ x ∈ s, f x = 0 ↔ ∀ x ∈ s, f x = 0 := by
  rw [← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ h, Finset.sum_eq_zero_iff]
  refine ⟨fun H x hx ↦ ?_, fun H x hx ↦ H x ((h.mem_toFinset.1 hx).1)⟩
  by_contra hne
  exact hne (H x (h.mem_toFinset.2 ⟨hx, hne⟩))

variable (hΛ : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
  (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)))
include hΛ

omit [CharZero C] [FiniteDimensional (RatFunc C) K] [IsAlgClosed C] in
/-- A maximal ideal containing `x̄` pulls back to a point over the residue point. -/
lemma comap_comap_eq {𝔫 : Ideal (redRing C K (xF C K))} [h𝔫 : 𝔫.IsMaximal]
    (hx : xbar hΛ ∈ 𝔫) :
    (𝔫.comap (redΛ K)).comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K)) =
      discIdeal (0 : C) 1 := by
  refine ((discIdeal_isMaximal one_ne_zero).eq_of_le ?_ ?_).symm
  · intro h
    apply h𝔫.ne_top
    rw [Ideal.eq_top_iff_one] at h ⊢
    simpa using h
  · rintro ⟨f, hf⟩ ⟨Q, hQ, hQf, hQ0⟩
    rw [Ideal.mem_comap, Ideal.mem_comap]
    have hdiv : ∀ i, ‖(Polynomial.divX Q).coeff i‖ ≤ 1 := fun i ↦ by
      rw [coeff_divX]; exact_mod_cast hQ (i + 1)
    have hc0 : ‖Q.coeff 0‖ ≤ 1 := by exact_mod_cast hQ 0
    set b0 : HenselComplete.integers C := ⟨Q.coeff 0, (HenselComplete.mem_integers_iff _).2 hc0⟩
    have he : algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K) ⟨f, hf⟩ =
        constD b0 + xD * polyD (Polynomial.divX Q) hdiv := by
      apply Subtype.ext
      rw [Subalgebra.coe_add, Subalgebra.coe_mul, coe_polyD]
      change algebraMap (RatFunc C) K f = algebraMap (RatFunc C) K
          (algebraMap C (RatFunc C) (Q.coeff 0)) + xF C K * aeval (xF C K) (Polynomial.divX Q)
      have hQf' : aeval (gaussCoord (0 : C) 1) Q = f := hQf
      rw [← hQf', gaussCoord_zero_one, RatFunc.aeval_X_left_eq_algebraMap, ← aeval_xF,
        ← IsScalarTower.algebraMap_apply]
      conv_lhs => rw [← Polynomial.X_mul_divX_add Q]
      rw [map_add, map_mul, aeval_X, aeval_C, add_comm]
    rw [he, map_add, map_mul]
    refine add_mem ?_ (Ideal.mul_mem_right _ _ (by rw [redΛ_xD]; exact hx))
    convert 𝔫.zero_mem
    apply Subtype.ext
    funext w
    change redD w (constD b0) = 0
    rw [redD_constD, (IsLocalRing.residue_eq_zero_iff _).2, map_zero]
    exact (HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).2 (by exact_mod_cast hQ0)

include hp hp1 in
/-- **`δ_𝔫 = 0` iff the corresponding point of `R'` is smooth**, for a closed point `𝔫 ∋ x̄`. -/
theorem dinf_eq_zero_iff {𝔫 : Ideal (redRing C K (xF C K))} [h𝔫 : 𝔫.IsMaximal]
    (hx : xbar hΛ ∈ 𝔫) :
    dinf 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛ 𝔫 = 0 ↔
      IsDiscSmooth (𝔫.comap (redΛ K)) := by
  haveI : (𝔫.comap (redΛ K)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (redΛ_surjective hp hp1)
  have hc := comap_comap_eq hΛ hx
  have e : (𝔫.comap (redΛ K)).map (redΛ K) = 𝔫 :=
    Ideal.map_comap_of_surjective _ (redΛ_surjective hp hp1) 𝔫
  constructor
  · intro h0
    refine isDiscSmooth_of_dl hp hp1 hΛ hc fun M ↦ ?_
    rw [e]
    exact dl_eq_zero_of_dinf hp hp1 hΛ h𝔫 h0 M
  · intro hs
    have h := dl_eq_zero_of_isDiscSmooth hp hp1 hΛ hc hs
    rw [e] at h
    rw [dinf]
    simp [h]

include hp hp1 in
/-- **The total `δ` over the residue point vanishes iff every point of the normalized vertex
chart over the residue point is smooth.** -/
theorem tot0_eq_zero_iff :
    tot0 C K hΛ (fun 𝔫 ↦ xbar hΛ ∈ 𝔫) = 0 ↔
      ∀ P' : Ideal (DRint (0 : C) 1 K), P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K)) = discIdeal (0 : C) 1 →
          IsDiscSmooth P' := by
  rw [tot0, finsum_mem_eq_zero_iff_nat ((finite_dinf₀ hp hp1 hΛ).subset fun 𝔫 h ↦ ⟨h.1.1, h.2⟩)]
  constructor
  · intro H P' hP'm hP'
    haveI := hP'm
    have hm := map_isMaximal hp hp1 hP'
    have h0 := H _ ⟨hm, xbar_mem_map hΛ hP'⟩
    have := (dinf_eq_zero_iff hp hp1 hΛ (𝔫 := P'.map (redΛ K)) (xbar_mem_map hΛ hP')).1 h0
    rwa [comap_map hp hp1 hP'] at this
  · rintro H 𝔫 ⟨h𝔫, hx⟩
    haveI := h𝔫
    exact (dinf_eq_zero_iff hp hp1 hΛ hx).2 (H _ (Ideal.comap_isMaximal_of_surjective _
      (redΛ_surjective hp hp1)) (comap_comap_eq hΛ hx))

end DiscBridge

end SemistableReduction
