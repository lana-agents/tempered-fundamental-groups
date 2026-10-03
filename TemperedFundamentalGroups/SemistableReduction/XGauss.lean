/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.MonomialPoint

/-!
# Gauss points over the algebraic closure of the constants (Blueprint §9.7, XL3)

Let `O ⊆ K` be a valuation subring with uniformizer `ϖ`, `E / K` a field extension with an
algebraically closed subfield `K̄ ⊇ K` algebraic over `K` (in the application `E = F̄`, the
algebraic closure of the function field, and `K̄` the algebraic closure of `K` in it), and `U` a
valuation subring of `E` over `O`. If `y ∈ E` has `U(y) ^ d = U(c)` for a constant `c ∈ K ∖ 0`
(e.g. `c = ϖ ^ m`) and `y ^ d / c` has transcendental residue over `κ(O)`, then `U` restricts on
`K̄[y]` to the Gauss valuation of radius `U(y)` (`valuation_aeval_eq_sup_of_residue`):

  `U(Q(y)) = max_i U(qᵢ) U(y) ^ i` for `Q ∈ K̄[X]`.

Proof: for `β ∈ K̄`, `U(y - β) = max(U(y), U(β))` — if `U(β) = U(y)` and `U(y - β) < U(y)`, the
residue of `y ^ d / c` would equal that of the algebraic element `β ^ d / c`
(`exists_poly_residue_ne_zero`, a normalised minimal polynomial). Then `Q` splits over `K̄` and the
Gauss norm is multiplicative (`Gauss.sup_mul`).
-/

open Polynomial

namespace SemistableReduction

variable {K E : Type*} [Field K] [Field E] [Algebra K E] {O : ValuationSubring K}

/-- An element algebraic over `K` is a root of a polynomial over `O` with nonzero reduction. -/
lemma exists_poly_residue_ne_zero {z : E} (hz : IsAlgebraic K z) :
    ∃ P : O[X], P.map (IsLocalRing.residue O) ≠ 0 ∧ aeval z (P.map (algebraMap O K)) = 0 := by
  classical
  obtain ⟨M, hM0, hMz⟩ := hz
  have hne : M.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hM0)
  obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image M.support (fun i ↦ O.valuation (M.coeff i))
    hne
  have hc0 : M.coeff i₀ ≠ 0 := by simpa using hi₀
  set N := C (M.coeff i₀)⁻¹ * M with hN
  have hNcoeff : ∀ i, N.coeff i ∈ O := fun i ↦ by
    rw [hN, coeff_C_mul, ← O.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hi : i ∈ M.support
    · rw [inv_mul_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hc0))]
      exact hmax i hi
    · rw [notMem_support_iff.mp hi, map_zero, mul_zero]; exact zero_le
  have hsub : (↑N.coeffs : Set K) ⊆ O.toSubring := fun q hq ↦ by
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.mp hq
    exact hNcoeff i
  set P : O[X] := N.toSubring O.toSubring hsub
  have hPmap : P.map (algebraMap O K) = N := by
    ext i
    rw [coeff_map]
    exact coeff_toSubring' ..
  refine ⟨P, fun h ↦ ?_, ?_⟩
  · have := congrArg (fun R ↦ R.coeff i₀) h
    simp only [coeff_map, coeff_zero] at this
    have h1 : P.coeff i₀ = 1 := by
      apply Subtype.ext
      rw [coeff_toSubring', hN, coeff_C_mul, inv_mul_cancel₀ hc0]; rfl
    rw [h1, map_one] at this
    exact one_ne_zero this
  · rw [hPmap, hN, map_mul, hMz, mul_zero]

/-- Polynomials over `O` are `1`-Lipschitz on the valuation subring `U ⊇ O`. -/
lemma valuation_aeval_sub_le {U : ValuationSubring E}
    (hO : ∀ o : O, algebraMap K E (o : K) ∈ U) {γ z : E} (hγ : γ ∈ U) (hz : z ∈ U)
    (P : O[X]) :
    U.valuation (aeval γ (P.map (algebraMap O K)) - aeval z (P.map (algebraMap O K))) ≤
      U.valuation (γ - z) := by
  have hpow : ∀ n : ℕ, U.valuation (γ ^ n - z ^ n) ≤ U.valuation (γ - z) := fun n ↦ by
    rw [← geom_sum₂_mul, map_mul]
    refine mul_le_of_le_one_left zero_le ?_
    refine Valuation.map_sum_le _ fun i _ ↦ ?_
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one₀ zero_le ((U.valuation_le_one_iff _).mpr hγ))
      (pow_le_one₀ zero_le ((U.valuation_le_one_iff _).mpr hz))
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    rw [Polynomial.map_add, map_add, map_add, add_sub_add_comm]
    exact (Valuation.map_add _ _ _).trans (max_le hP hQ)
  | monomial n o =>
    rw [Polynomial.map_monomial, aeval_monomial, aeval_monomial, ← mul_sub, map_mul]
    exact (mul_le_of_le_one_left zero_le ((U.valuation_le_one_iff _).mpr (hO o))).trans
      (hpow n)

variable {Kb : Type*} [Field Kb] [Algebra K Kb] [Algebra Kb E] [IsScalarTower K Kb E]

/-- **Distances to algebraic constants**: if `U(y) ^ d = U(c)` (`c ∈ K ∖ 0`) and `y ^ d / c` has
transcendental residue over `κ(O)`, then `U(y - β) = max(U(y), U(β))` for every `β` algebraic over
`K`. -/
theorem valuation_sub_algebraic_eq_max {U : ValuationSubring E}
    (hU : U.comap (algebraMap K E) = O) {c : K} (hc0 : c ≠ 0) {y : E} {d : ℕ}
    (hd : 0 < d) (hy : U.valuation y ^ d = U.valuation (algebraMap K E c))
    (htr : IsResidueTranscendental O U (y ^ d / algebraMap K E c)) {β : E}
    (hβ : IsAlgebraic K β) :
    U.valuation (y - β) = max (U.valuation y) (U.valuation β) := by
  set w := U.valuation
  set p := algebraMap K E c
  have hp0 : p ≠ 0 := by simpa [p] using hc0
  have hwp0 : w p ≠ 0 := by simpa [w] using hp0
  have hwy0 : w y ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hy
    exact hwp0 hy.symm
  have hO : ∀ o : O, algebraMap K E (o : K) ∈ U := fun o ↦ by
    rw [← ValuationSubring.mem_comap, hU]; exact o.2
  rcases lt_trichotomy (w β) (w y) with hlt | heq | hgt
  · rw [Valuation.map_sub_eq_of_lt_left _ hlt, max_eq_left hlt.le]
  · by_contra hne
    have hle : w (y - β) ≤ w y := (Valuation.map_sub _ _ _).trans (by rw [heq, max_self])
    have hlt : w (y - β) < w y := lt_of_le_of_ne hle (by rwa [heq, max_self] at hne)
    set γ := y ^ d / p
    set z := β ^ d / p
    have hz : IsAlgebraic K z := by
      have : z = β ^ d * algebraMap K E c⁻¹ := by
        simp [z, p, div_eq_mul_inv]
      rw [this]
      exact (hβ.pow d).mul (isAlgebraic_algebraMap _)
    have hwz : w z = 1 := by
      rw [map_div₀, map_pow, heq, hy, div_self hwp0]
    have hγz : w (γ - z) < 1 := by
      have hdiff : γ - z = (∑ i ∈ Finset.range d, y ^ i * β ^ (d - 1 - i)) * (y - β) / p := by
        rw [geom_sum₂_mul, sub_div]
      rw [hdiff, map_div₀, div_lt_one₀ (zero_lt_iff.mpr hwp0), ← hy, map_mul]
      have hsum : w (∑ i ∈ Finset.range d, y ^ i * β ^ (d - 1 - i)) ≤ w y ^ (d - 1) := by
        refine Valuation.map_sum_le _ fun i hi ↦ ?_
        rw [map_mul, map_pow, map_pow, heq, ← pow_add]
        rw [Finset.mem_range] at hi
        rw [show i + (d - 1 - i) = d - 1 by omega]
      calc w (∑ i ∈ Finset.range d, y ^ i * β ^ (d - 1 - i)) * w (y - β)
          ≤ w y ^ (d - 1) * w (y - β) := mul_le_mul_left hsum _
        _ < w y ^ (d - 1) * w y := mul_lt_mul_of_pos_left hlt (pow_pos (zero_lt_iff.mpr hwy0) _)
        _ = w y ^ d := by rw [← pow_succ, Nat.sub_add_cancel hd]
    obtain ⟨P, hP, hPz⟩ := exists_poly_residue_ne_zero (O := O) hz
    have h1 := htr.2 P hP
    have hzU : z ∈ U := (U.valuation_le_one_iff _).mp hwz.le
    have h2 := valuation_aeval_sub_le hO htr.1 hzU P
    rw [hPz, sub_zero, h1] at h2
    exact absurd (h2.trans_lt hγz) (lt_irrefl _)
  · rw [Valuation.map_sub_eq_of_lt_right _ hgt, max_eq_right hgt.le]

/-- **Gauss centres are centres of minimal distance**: if `(x - a) ^ d / c` has transcendental
residue (`U(x - a) ^ d = U(c)`), then `U(x - a) ≤ U(x - b)` for every `b` with `b - a` algebraic
over `K`. In particular two such centres (over possibly different constant fields) give the same
radius. -/
theorem valuation_sub_le_of_residue {U : ValuationSubring E} (hU : U.comap (algebraMap K E) = O)
    {c : K} (hc0 : c ≠ 0) {x a b : E} {d : ℕ} (hd : 0 < d)
    (hy : U.valuation (x - a) ^ d = U.valuation (algebraMap K E c))
    (htr : IsResidueTranscendental O U ((x - a) ^ d / algebraMap K E c))
    (hab : IsAlgebraic K (b - a)) : U.valuation (x - a) ≤ U.valuation (x - b) := by
  have h := valuation_sub_algebraic_eq_max hU hc0 hd hy htr hab
  rw [show x - a - (b - a) = x - b by ring] at h
  rw [h]
  exact le_max_left _ _

/-- The Gauss norm of `X - β`. -/
lemma Gauss.sup_X_sub_C {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]
    {v : Valuation F Γ₀} {r : Γ₀ˣ} (β : F) :
    Gauss.sup v r (X - C β) = max (v β) r := by
  apply le_antisymm
  · refine Gauss.sup_le_iff.2 fun i ↦ ?_
    rcases i with _ | _ | i
    · simp [Gauss.term]
    · simp [Gauss.term]
    · simp [Gauss.term, coeff_X]
  · refine max_le ?_ ?_
    · have := Gauss.term_le_sup (v := v) (r := r) (X - C β) 0
      simpa only [Gauss.term, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, Valuation.map_neg,
        pow_zero, mul_one] using this
    · have := Gauss.term_le_sup (v := v) (r := r) (X - C β) 1
      simpa only [Gauss.term, coeff_sub, coeff_X_one, coeff_C_succ, sub_zero, map_one, pow_one,
        one_mul] using this

/-- **Gauss formula over the algebraic closure of the constants** (XL3): if `U(y) ^ d = U(c)`
(`c ∈ K ∖ 0`) and `y ^ d / c` has transcendental residue over `κ(O)`, then for `Q` over an
algebraically closed `K̄ ⊇ K` algebraic over `K`, `U(Q(y)) = max_i U(qᵢ yⁱ)`. -/
theorem valuation_aeval_eq_sup_of_residue [IsAlgClosed Kb] [Algebra.IsAlgebraic K Kb]
    {U : ValuationSubring E} (hU : U.comap (algebraMap K E) = O) {c : K} (hc0 : c ≠ 0)
    {y : E} {d : ℕ} (hd : 0 < d) (hy : U.valuation y ^ d = U.valuation (algebraMap K E c))
    (htr : IsResidueTranscendental O U (y ^ d / algebraMap K E c)) (Q : Kb[X]) :
    U.valuation (aeval y Q) =
      Q.support.sup fun i ↦ U.valuation (algebraMap Kb E (Q.coeff i) * y ^ i) := by
  have hwy0 : U.valuation y ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at hy
    exact (by simpa using hc0 : U.valuation (algebraMap K E c) ≠ 0) hy.symm
  set v := U.valuation.comap (algebraMap Kb E)
  set r : U.ValueGroupˣ := Units.mk0 _ hwy0
  have hconv : Gauss.sup v r Q =
      Q.support.sup fun i ↦ U.valuation (algebraMap Kb E (Q.coeff i) * y ^ i) := by
    refine Finset.sup_congr rfl fun i _ ↦ ?_
    simp [Gauss.term, v, r, map_mul, map_pow]
  rw [← hconv]
  clear hconv
  suffices H : ∀ n, ∀ Q : Kb[X], Q.natDegree = n → U.valuation (aeval y Q) = Gauss.sup v r Q from
    H _ Q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Q h
    by_cases hdeg : Q.degree ≤ 0
    · rw [eq_C_of_degree_le_zero hdeg, aeval_C, Gauss.sup_C]
      rfl
    · obtain ⟨β, hβ⟩ := IsAlgClosed.exists_root Q (fun h0 ↦ hdeg (le_of_eq h0))
      set Q₁ := Q /ₘ (X - C β)
      have hQ : Q = (X - C β) * Q₁ := (mul_divByMonic_eq_iff_isRoot.mpr hβ).symm
      have hdeg₁ : Q₁.natDegree < n := by
        rw [← h, natDegree_divByMonic _ (monic_X_sub_C β), natDegree_X_sub_C]
        have : 0 < Q.natDegree := natDegree_pos_iff_degree_pos.mpr (not_le.mp hdeg)
        omega
      have ih₁ := ih Q₁.natDegree hdeg₁ Q₁ rfl
      rw [hQ, map_mul, map_mul, Gauss.sup_mul, ih₁, aeval_sub, aeval_X, aeval_C,
        Gauss.sup_X_sub_C, valuation_sub_algebraic_eq_max hU hc0 hd hy htr
          ((Algebra.IsAlgebraic.isAlgebraic β).algebraMap)]
      simp [v, r, max_comm]

end SemistableReduction
