/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartTwist
import TemperedFundamentalGroups.SemistableReduction.SmoothVertex

/-!
# Clearing denominators and bounding values of integral elements

Blueprint §9.12, O12 / R5, step (1)(b) (field-level tools for the locality of reduced charts).

* `exists_pow_mul_isIntegral`: if `u ∈ S` and `u g ∈ S`, an element integral over `R[g]` becomes
  integral over `S` after multiplication by a power of `u`;
* `valuation_le_of_monic`: a root of a monic polynomial whose coefficients have value `≤ B`
  (`B ≥ 1`) has value `≤ B`;
* `exists_pow_mul_le_one`: for `y` integral over `O_C[x]` (the disc chart `discRing 0 1`) there is
  `d` such that `v(u^N y) ≤ 1` for all `N ≥ d` and all valuations `v` (bounded by the norm on `C`)
  with `v(u) · max(1, v(x)) ≤ 1`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace ChartBounds

/-! ### Clearing denominators -/

section Scale

variable {R L : Type*} [CommRing R] [Field L] [Algebra R L] {g u : L} {S : Subalgebra R L}

lemma exists_pow_mul_mem (hu : u ∈ S) (hug : u * g ∈ S) {a : L}
    (ha : a ∈ Algebra.adjoin R {g}) : ∃ d : ℕ, ∀ d', d ≤ d' → u ^ d' * a ∈ S := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    refine ⟨1, fun d' hd' ↦ ?_⟩
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd'
    have : u ^ (1 + e) * g = u ^ e * (u * g) := by ring
    rw [this]
    exact mul_mem (pow_mem hu _) hug
  | algebraMap r => exact ⟨0, fun d' _ ↦ mul_mem (pow_mem hu _) (S.algebraMap_mem r)⟩
  | add x y _ _ hx hy =>
    obtain ⟨d₁, h₁⟩ := hx
    obtain ⟨d₂, h₂⟩ := hy
    refine ⟨max d₁ d₂, fun d' hd' ↦ ?_⟩
    rw [mul_add]
    exact add_mem (h₁ _ ((le_max_left _ _).trans hd')) (h₂ _ ((le_max_right _ _).trans hd'))
  | mul x y _ _ hx hy =>
    obtain ⟨d₁, h₁⟩ := hx
    obtain ⟨d₂, h₂⟩ := hy
    refine ⟨d₁ + d₂, fun d' hd' ↦ ?_⟩
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hd'
    have : u ^ (d₁ + d₂ + e) * (x * y) = (u ^ d₁ * x) * (u ^ (d₂ + e) * y) := by ring
    rw [this]
    exact mul_mem (h₁ _ le_rfl) (h₂ _ (Nat.le_add_right _ _))

/-- **Clearing denominators**: if `u ∈ S` and `u g ∈ S`, an element integral over `R[g]` becomes
integral over `S` after multiplication by a power of `u`. -/
theorem exists_pow_mul_isIntegral (hu : u ∈ S) (hug : u * g ∈ S) {y : L}
    (hy : IsIntegral (Algebra.adjoin R {g}) y) : ∃ N : ℕ, IsIntegral S (u ^ N * y) := by
  classical
  obtain ⟨p, hpm, hp⟩ := hy
  set P : L[X] := p.map (algebraMap (Algebra.adjoin R {g}) L)
  have hPm : P.Monic := hpm.map _
  set n := P.natDegree
  have hcoeff (i : ℕ) : ∃ d : ℕ, ∀ d', d ≤ d' → u ^ d' * P.coeff i ∈ S := by
    rw [coeff_map]
    exact exists_pow_mul_mem hu hug (p.coeff i).2
  choose d hd using hcoeff
  set D := (Finset.range (n + 1)).sup d
  have hD (i : ℕ) (hi : i ≤ n) : d i ≤ D := Finset.le_sup (f := d) (Finset.mem_range.2 (by omega))
  set Q := P.scaleRoots (u ^ D)
  have hQ : (Q.coeffs : Set L) ⊆ S.toSubring := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
    change Q.coeff i ∈ S
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i n with hi | rfl | hi
    · have hle : D ≤ D * (n - i) := Nat.le_mul_of_pos_right D (by omega)
      rw [← pow_mul, mul_comm]
      exact hd i _ ((hD i hi.le).trans hle)
    · rw [Nat.sub_self, pow_zero, mul_one, hPm.coeff_natDegree]
      exact one_mem _
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact zero_mem _
  have hQm : Q.Monic := by
    rw [Monic, leadingCoeff, natDegree_scaleRoots, coeff_scaleRoots, Nat.sub_self, pow_zero,
      mul_one, hPm.coeff_natDegree]
  refine ⟨D, Q.toSubring S.toSubring hQ, (monic_toSubring _ _ _).2 hQm, ?_⟩
  have h1 : eval₂ (algebraMap S L) (u ^ D * y) (Q.toSubring S.toSubring hQ) =
      eval₂ (RingHom.id L) (u ^ D * y) Q := by
    conv_rhs => rw [← map_toSubring Q S.toSubring hQ]
    rw [eval₂_map]
    rfl
  rw [h1]
  have h2 := scaleRoots_eval₂_mul (p := P) (RingHom.id L) y (u ^ D)
  simp only [RingHom.id_apply] at h2
  rw [h2]
  have h3 : eval₂ (RingHom.id L) y P = 0 := by
    rw [eval₂_map]
    exact hp
  rw [h3, mul_zero]

/-- **Clearing denominators**, integrality form: if `u` and `u g` are integral over `A`, an element
integral over `R[g]` becomes integral over `A` after multiplication by a power of `u`. -/
theorem exists_pow_mul_isIntegral' {A : Subalgebra R L} (hu : IsIntegral A u)
    (hug : IsIntegral A (u * g)) {y : L} (hy : IsIntegral (Algebra.adjoin R {g}) y) :
    ∃ N : ℕ, IsIntegral A (u ^ N * y) := by
  obtain ⟨N, h⟩ :=
    exists_pow_mul_isIntegral (S := (integralClosure A L).restrictScalars R) hu hug hy
  refine ⟨N, ?_⟩
  have h' : IsIntegral (integralClosure A L) (u ^ N * y) := h
  exact isIntegral_trans _ h'

end Scale

/-! ### Bounds for roots of monic polynomials -/

section Bound

variable {L : Type*} [Field L] (v : Valuation L ℝ≥0)

/-- **A root bound**: a root of a monic polynomial whose coefficients have value `≤ B`, `B ≥ 1`,
has value `≤ B`. -/
theorem valuation_le_of_monic {p : L[X]} (hp : p.Monic) {y : L} (hy : aeval y p = 0) {B : ℝ≥0}
    (hB : 1 ≤ B) (hc : ∀ i, v (p.coeff i) ≤ B) : v y ≤ B := by
  by_contra hlt
  push Not at hlt
  set n := p.natDegree
  have hy1 : 1 < v y := hB.trans_lt hlt
  have hn : n ≠ 0 := by
    intro h
    have : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp h
    rw [this, map_one] at hy
    exact one_ne_zero hy
  have hsum : aeval y p = y ^ n + ∑ i ∈ Finset.range n, p.coeff i * y ^ i := by
    conv_lhs => rw [hp.as_sum]
    simp [map_add, map_sum, n]
  rw [hsum, add_eq_zero_iff_eq_neg] at hy
  have hlt' : v (∑ i ∈ Finset.range n, p.coeff i * y ^ i) < v y ^ n := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans hy1))) fun i hi ↦ ?_
    have hi' := Finset.mem_range.1 hi
    rw [map_mul, map_pow]
    calc v (p.coeff i) * v y ^ i ≤ B * v y ^ i := mul_le_mul_of_nonneg_right (hc i) zero_le
      _ < v y * v y ^ i := mul_lt_mul_of_pos_right hlt (pow_pos (zero_lt_one.trans hy1) _)
      _ = v y ^ (i + 1) := by ring
      _ ≤ v y ^ n := pow_le_pow_right₀ hy1.le hi'
  have := congrArg v hy
  rw [Valuation.map_neg, map_pow] at this
  exact lt_irrefl _ (this ▸ hlt')

end Bound

/-! ### Elements integral over the disc chart -/

section Disc

open GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G] [IsScalarTower C (RatFunc C) G]

omit [IsUltrametricDist C] in
/-- The value of a polynomial with integral coefficients in `x`. -/
lemma valuation_aeval_le (v : Valuation G ℝ≥0)
    (hv : ∀ c : C, v (algebraMap (RatFunc C) G (algebraMap C (RatFunc C) c)) ≤ ‖c‖₊)
    {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) :
    v (algebraMap (RatFunc C) G (algebraMap C[X] (RatFunc C) Q)) ≤
      max 1 (v (xF C G)) ^ Q.natDegree := by
  rw [← RatFunc.aeval_X_left_eq_algebraMap, ← aeval_algebraMap_apply, aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i hi ↦ ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  have h1 : v (algebraMap C G (Q.coeff i)) ≤ 1 := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) G]
    exact (hv _).trans (by exact_mod_cast hQ i)
  calc v (algebraMap C G (Q.coeff i)) * v (algebraMap (RatFunc C) G RatFunc.X) ^ i
      ≤ 1 * max 1 (v (xF C G)) ^ i := mul_le_mul' h1 (pow_le_pow_left₀ zero_le (le_max_right _ _) _)
    _ ≤ max 1 (v (xF C G)) ^ Q.natDegree := by
        rw [one_mul]
        exact pow_le_pow_right₀ (le_max_left _ _) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))

/-- **Values of elements integral over `O_C[x]`**: there is `d` such that `v(u^N y) ≤ 1` for
`N ≥ d`, for every valuation `v` bounded by the norm on `C` with `v(u) · max(1, v(x)) ≤ 1`. -/
theorem exists_pow_mul_le_one {y : G} (hy : IsIntegral (DiscCount.discRing (0 : C) 1) y) :
    ∃ d : ℕ, ∀ (v : Valuation G ℝ≥0),
      (∀ c : C, v (algebraMap (RatFunc C) G (algebraMap C (RatFunc C) c)) ≤ ‖c‖₊) →
      ∀ u : G, v u * max 1 (v (xF C G)) ≤ 1 → ∀ N, d ≤ N → v (u ^ N * y) ≤ 1 := by
  classical
  obtain ⟨p, hpm, hp⟩ := hy
  have hQ (i : ℕ) : ∃ Q : C[X], (∀ j, ‖Q.coeff j‖ ≤ 1) ∧
      algebraMap C[X] (RatFunc C) Q = (p.coeff i : RatFunc C) := by
    obtain ⟨Q, hQ, hQe⟩ := SmoothVertex.mem_discRing_iff.1 (p.coeff i).2
    refine ⟨Q, fun j ↦ ?_, hQe⟩
    have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) Q j).trans hQ
    simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply] at this
    exact_mod_cast this
  choose Q hQ1 hQe using hQ
  set n := p.natDegree
  set d := (Finset.range (n + 1)).sup fun i ↦ (Q i).natDegree
  refine ⟨d, fun v hv u hu N hN ↦ ?_⟩
  set m := max 1 (v (xF C G))
  have hm : 1 ≤ m := le_max_left _ _
  set P : G[X] := p.map (algebraMap (DiscCount.discRing (0 : C) 1) G)
  have hPm : P.Monic := hpm.map _
  have hcoeff (i : ℕ) : v (P.coeff i) ≤ m ^ d := by
    rw [coeff_map]
    by_cases hi : i ≤ n
    · change v (algebraMap (RatFunc C) G (p.coeff i : RatFunc C)) ≤ m ^ d
      rw [← hQe i]
      exact (valuation_aeval_le v hv (hQ1 i)).trans (pow_le_pow_right₀ hm
        (Finset.le_sup (f := fun i ↦ (Q i).natDegree) (Finset.mem_range.2 (by omega))))
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), map_zero, map_zero]
      exact zero_le
  have hroot : aeval y P = 0 := by
    rw [aeval_map_algebraMap]
    exact hp
  have hyv := valuation_le_of_monic v hPm hroot (one_le_pow₀ hm) hcoeff
  rw [map_mul, map_pow]
  calc v u ^ N * v y ≤ v u ^ N * m ^ N :=
        mul_le_mul_of_nonneg_left (hyv.trans (pow_le_pow_right₀ hm hN)) zero_le
    _ = (v u * m) ^ N := (mul_pow _ _ _).symm
    _ ≤ 1 := pow_le_one₀ zero_le hu

end Disc

end ChartBounds

end SemistableReduction
