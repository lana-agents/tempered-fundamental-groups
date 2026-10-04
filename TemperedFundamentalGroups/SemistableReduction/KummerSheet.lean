/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerResidue
import TemperedFundamentalGroups.SemistableReduction.DiscGerm
import TemperedFundamentalGroups.SemistableReduction.AffineTwist

/-!
# The sheet of a degree-one disc point inside a smaller disc

Blueprint §9.10, L4 (K6, setting). Let `P'` be a point of disc degree one of the integral closure
`R' = DRint a c L` of the disc chart `O_C[t]`, `t = (x - a)/c`, and `0 < ‖l‖ < 1`. The residue class
`U' = {|t| < ‖l‖}` of the Gauss point `w_{a,|c l|}` is the base of the Kummer analysis (K6 is proved
for `U'`, see the decision in Blueprint §9.10).

* `discRing_le`, `drint_le`: `O_C[t] ⊆ O_C[t/l]`, hence `DRint a c L ⊆ DRint a (c l) L`.
-/

open Polynomial NNReal

namespace SemistableReduction

namespace KummerSheet

open DiscCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

/-! ### The inclusion of disc charts -/

section Charts

variable {a c l : C}

omit [IsUltrametricDist C] in
lemma gaussCoord_mul (hl : l ≠ 0) :
    gaussCoord a c = algebraMap C (RatFunc C) l * gaussCoord a (c * l) := by
  rw [AffineTwist.gaussCoord_eq, AffineTwist.gaussCoord_eq, ← mul_assoc, ← map_mul,
    mul_inv, mul_comm c⁻¹ l⁻¹, ← mul_assoc, mul_inv_cancel₀ hl, one_mul]

/-- `O_C[t] ⊆ O_C[t/l]` for `‖l‖ ≤ 1`. -/
theorem discRing_le (_hc : c ≠ 0) (hl : l ≠ 0) (hl1 : ‖l‖ ≤ 1) :
    discRing a c ≤ discRing a (c * l) := by
  intro f hf
  obtain ⟨Q, hQ, rfl⟩ := mem_polyChart_iff.1 hf
  refine mem_polyChart_iff.2 ⟨Q.comp (Polynomial.C l * X), ?_, ?_⟩
  · refine Gauss.sup_le_iff.2 fun i ↦ ?_
    simp only [Gauss.term, comp_C_mul_X_coeff, Units.val_one, one_pow, mul_one,
      NormedField.valuation_apply, nnnorm_mul, nnnorm_pow]
    have h1 := coeff_le_one_of_sup_le_one hQ i
    rw [NormedField.valuation_apply] at h1
    exact mul_le_one' h1 (pow_le_one₀ zero_le (by exact_mod_cast hl1))
  · rw [aeval_comp, map_mul, aeval_C, aeval_X, ← gaussCoord_mul hl]

omit [NontriviallyNormedField C] [IsUltrametricDist C] in
/-- Integrality over a subring passes to larger subrings. -/
lemma isIntegral_of_subring_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A B : Subring K} (hAB : A ≤ B) {y : L} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨P, hm, hP⟩ := hy
  refine ⟨P.map (Subring.inclusion hAB), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hP

variable (L : Type*) [Field L] [Algebra (RatFunc C) L]

/-- `DRint a c L ⊆ DRint a (c l) L`. -/
theorem drint_le (hc : c ≠ 0) (hl : l ≠ 0) (hl1 : ‖l‖ ≤ 1) {y : L}
    (hy : IsIntegral (discRing a c) y) : IsIntegral (discRing a (c * l)) y :=
  isIntegral_of_subring_le (discRing_le hc hl hl1) hy

end Charts

/-! ### Uniqueness of the extension when the residue degree is full -/

section Unique

open LocalGlobal FundamentalInequality

/-- **A full residue extension forces a unique extension.** If every extension of the norm
valuation of `F` to `F'` has inertia degree `≥ [F' : F]`, there is at most one extension. -/
theorem subsingleton_extension {F F' K : Type*} [NormedField F] [IsUltrametricDist F]
    [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
    [hd : Fact (DenseRange (algebraMap F K))] [Field F'] [Algebra F F'] [FiniteDimensional F F']
    [Algebra.IsSeparable F F']
    (h : ∀ w : Extension F F', Module.finrank F F' ≤
      inertiaDeg (NormedField.valuation (K := F)) w.1) :
    Subsingleton (Extension F F') := by
  classical
  have hn : 0 < Module.finrank F F' := Module.finrank_pos
  -- every factor has degree `≥ n`
  have hdeg : ∀ g : Factor F K F', Module.finrank F F' ≤ g.1.natDegree := by
    intro g
    have h1 := h (extension g)
    change _ ≤ inertiaDeg _ (extValuation g) at h1
    rw [inertiaDeg_extValuation] at h1
    have h2 := ramificationIdx_mul_inertiaDeg_le (K := K) (L := Local K g.1)
      (v := NormedField.valuation (K := K)) (w := NormedField.valuation (K := Local K g.1))
    have h3 := ramificationIdx_ne_zero (K := K) (NormedField.valuation (K := Local K g.1))
    rw [finrank_local] at h2
    calc Module.finrank F F' ≤ _ := h1
      _ ≤ ramificationIdx K (NormedField.valuation (K := Local K g.1)) *
          inertiaDeg (NormedField.valuation (K := K))
            (NormedField.valuation (K := Local K g.1)) :=
          Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h3)
      _ ≤ _ := h2
  refine ⟨fun w₁ w₂ ↦ ?_⟩
  by_contra hne
  obtain ⟨g₁, hg₁⟩ := (extensionEquiv (K := K)).surjective w₁
  obtain ⟨g₂, hg₂⟩ := (extensionEquiv (K := K)).surjective w₂
  have hg : g₁ ≠ g₂ := by rintro rfl; exact hne (hg₁.symm.trans hg₂)
  have hsum := sum_natDegree_factors (F := F) (K := K) (F' := F')
  have hsub : ({g₁.1, g₂.1} : Finset K[X]) ⊆ factors F K F' := by
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact g₁.2
    · rw [Finset.mem_singleton.1 hx]; exact g₂.2
  have hle := Finset.sum_le_sum_of_subset (f := natDegree) hsub
  have hne' : g₁.1 ≠ g₂.1 := fun h ↦ hg (Subtype.ext h)
  rw [Finset.sum_pair hne', hsum] at hle
  have := hdeg g₁
  have := hdeg g₂
  omega

end Unique

/-! ### Reductions of polynomials: `p`-th powers have vanishing derivative -/

section NoRoot

open KummerNormalForm

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- The reduction of a polynomial (meaningful for integral coefficients). -/
noncomputable def redP (P : C[X]) : 𝓀[X] :=
  ∑ i ∈ Finset.range (P.natDegree + 1), monomial i (rd (P.coeff i))

lemma coeff_redP (P : C[X]) (i : ℕ) : (redP P).coeff i = rd (P.coeff i) := by
  rw [redP, finsetSum_coeff]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [Finset.mem_range] at h; omega)]
    exact (rd_eq_zero (x := (0 : C)) (by rw [norm_zero]; exact zero_lt_one)).symm

/-- Integral polynomials: all coefficients of norm `≤ 1`. -/
def IntP (P : C[X]) : Prop := ∀ i, ‖P.coeff i‖ ≤ 1

lemma IntP.mul {P Q : C[X]} (hP : IntP P) (hQ : IntP Q) : IntP (P * Q) := fun n ↦ by
  rw [coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ ↦ ?_
  rw [norm_mul]
  exact mul_le_one₀ (hP _) (norm_nonneg _) (hQ _)

lemma IntP.sub {P Q : C[X]} (hP : IntP P) (hQ : IntP Q) : IntP (P - Q) := fun n ↦ by
  rw [coeff_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP n) (by rw [norm_neg]; exact hQ n))

lemma IntP.pow {P : C[X]} (hP : IntP P) (n : ℕ) : IntP (P ^ n) := by
  induction n with
  | zero => intro i; rw [pow_zero, coeff_one]; split_ifs <;> simp
  | succ n ih => rw [pow_succ]; exact ih.mul hP

lemma redP_mul {P Q : C[X]} (hP : IntP P) (hQ : IntP Q) : redP (P * Q) = redP P * redP Q := by
  ext n
  rw [coeff_redP, coeff_mul, coeff_mul, rd_sum _ _ fun x _ ↦ by
    rw [norm_mul]; exact mul_le_one₀ (hP _) (norm_nonneg _) (hQ _)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [rd_mul (hP _) (hQ _), coeff_redP, coeff_redP]

lemma redP_sub {P Q : C[X]} (hP : IntP P) (hQ : IntP Q) : redP (P - Q) = redP P - redP Q := by
  ext n
  rw [coeff_redP, coeff_sub, coeff_sub, coeff_redP, coeff_redP, sub_eq_add_neg,
    rd_add (hP n) (by rw [norm_neg]; exact hQ n), rd_neg, ← sub_eq_add_neg]

lemma redP_pow {P : C[X]} (hP : IntP P) (n : ℕ) : redP (P ^ n) = redP P ^ n := by
  induction n with
  | zero =>
    ext i; rw [coeff_redP, pow_zero, pow_zero, coeff_one, coeff_one]
    split_ifs
    · exact rd_one
    · exact rd_eq_zero (by simp)
  | succ n ih => rw [pow_succ, pow_succ, redP_mul (hP.pow n) hP, ih]

lemma redP_eq_zero_iff {P : C[X]} (hP : IntP P) : redP P = 0 ↔ ∀ i, ‖P.coeff i‖ < 1 := by
  constructor
  · intro h i
    have := congrArg (coeff · i) h
    simp only [coeff_redP, coeff_zero] at this
    exact (rd_eq_zero_iff (hP i)).1 this
  · intro h
    ext i
    rw [coeff_redP, coeff_zero]
    exact rd_eq_zero (h i)

variable (p : ℕ) [hp : Fact p.Prime]

/-- **No `p`-th roots of a reduction with a coefficient prime to `p`.** If `Ĝ` is integral with
`‖Ĝₘ‖ = 1`, `p ∤ m`, and `Q` is integral with some coefficient of norm `1`, then `P^p - Ĝ Q^p`
has a coefficient of norm `1` for every integral `P`: the reduction of `Ĝ` is not a `p`-th power
of a rational function, since its derivative does not vanish. -/
theorem exists_norm_coeff_eq_one (hp1 : ‖(p : C)‖ < 1) {Ĝ : C[X]} (hĜ : IntP Ĝ) {m : ℕ}
    (hm : ‖Ĝ.coeff m‖ = 1) (hpm : ¬ p ∣ m) {P Q : C[X]} (hP : IntP P) (hQ : IntP Q)
    {i₀ : ℕ} (hQ1 : ‖Q.coeff i₀‖ = 1) : ∃ i, ‖(P ^ p - Ĝ * Q ^ p).coeff i‖ = 1 := by
  haveI := charP_residueField hp.out hp1
  by_contra! H
  have hint : IntP (P ^ p - Ĝ * Q ^ p) := (hP.pow p).sub (hĜ.mul (hQ.pow p))
  have h0 : redP (P ^ p - Ĝ * Q ^ p) = 0 :=
    (redP_eq_zero_iff hint).2 fun i ↦ lt_of_le_of_ne (hint i) (H i)
  rw [redP_sub (hP.pow p) (hĜ.mul (hQ.pow p)), redP_mul hĜ (hQ.pow p), redP_pow hP,
    redP_pow hQ, sub_eq_zero] at h0
  -- differentiate
  have hd := congrArg derivative h0
  rw [derivative_mul, derivative_pow, derivative_pow, CharP.cast_eq_zero, map_zero, zero_mul,
    zero_mul, zero_mul, zero_mul, mul_zero, add_zero] at hd
  have hQ0 : redP Q ≠ 0 := by
    intro h
    have := congrArg (coeff · i₀) h
    simp only [coeff_redP, coeff_zero] at this
    exact absurd ((rd_eq_zero_iff (hQ i₀)).1 this) (by rw [hQ1]; exact lt_irrefl _)
  have hG' : derivative (redP Ĝ) = 0 := by
    rcases mul_eq_zero.1 hd.symm with h | h
    · exact h
    · exact absurd (pow_eq_zero_iff hp.out.ne_zero |>.1 h) hQ0
  have hm0 : m ≠ 0 := fun h ↦ hpm (h ▸ dvd_zero p)
  have := congrArg (coeff · (m - 1)) hG'
  simp only [coeff_derivative, coeff_zero, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hm0),
    coeff_redP] at this
  have hrd : rd (Ĝ.coeff m) ≠ 0 := fun h ↦ by
    rw [rd_eq_zero_iff (hĜ m), hm] at h; exact lt_irrefl _ h
  have hmk : ((m - 1 : ℕ) : 𝓀) + 1 ≠ 0 := by
    rw [show ((m - 1 : ℕ) : 𝓀) + 1 = ((m : ℕ) : 𝓀) by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hm0)]; push_cast; ring]
    rw [Ne, CharP.cast_eq_zero_iff 𝓀 p]
    exact hpm
  exact mul_ne_zero hrd hmk this

end NoRoot

/-! ### The sheet extension of an interior Gauss point -/

section Sheet

open LocalGlobal DiscGerm DenseCompletion Filter Topology

variable {L : Type*} [Field L] [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  {a c : C} (hc : c ≠ 0) (ν₀ : DiscVal a c) (P' : Ideal (DRint a c L)) [P'.IsMaximal]
  (h1 : discDegree ν₀ P' = 1) {l : C} (hl0 : l ≠ 0) (hl1 : ‖l‖ < 1)

/-- The factor of the Gauss point `w_{a,|l c|}` centred at the degree-one point `P'`. -/
noncomputable def sheetFactor :
    Factor (DiscField (gaussDiscVal (a := a) hc hl0 hl1))
      (UniformSpace.Completion (DiscField (gaussDiscVal (a := a) hc hl0 hl1))) L :=
  (existsUnique_of_discDegree_eq_one hc ν₀ (gaussDiscVal hc hl0 hl1) P' h1).exists.choose

lemma sheetFactor_spec :
    center (isDiscVal_comap_extValuation (sheetFactor hc ν₀ P' h1 hl0 hl1)) = P' ∧
      (sheetFactor hc ν₀ P' h1 hl0 hl1).1.natDegree = 1 :=
  (existsUnique_of_discDegree_eq_one hc ν₀ (gaussDiscVal hc hl0 hl1) P' h1).exists.choose_spec

omit [IsUltrametricDist C] in
lemma comap_extValuation {ν : DiscVal a c}
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) L) :
    (extValuation g).comap (algebraMap (RatFunc C) L) = ν.val := by
  have h := extValuation_comap g
  refine Valuation.ext fun φ ↦ ?_
  have := congrArg (fun v : Valuation (DiscField ν) ℝ≥0 ↦ v (WithAbs.toAbs _ φ)) h
  simp only [Valuation.comap_apply, valuation_withAbs] at this
  rw [Valuation.comap_apply]
  exact this

/-- **The sheet extension** of the Gauss point `w_{a,|l c|}`: the extension centred at `P'`. -/
noncomputable def sheetExt :
    GaussStability.GaussExtension a (Units.mk0 ‖l * c‖₊ (nnnorm_ne_zero_iff.2 (mul_ne_zero hl0 hc)))
      L :=
  ⟨extValuation (sheetFactor hc ν₀ P' h1 hl0 hl1), comap_extValuation _⟩

/-- **Polynomial approximation at the sheet**: every element of `R'` is approximated by
polynomials in `t` with integral coefficients at the sheet extension. -/
theorem exists_poly_approx (y : DRint a c L) {ε : ℝ} (hε : 0 < ε) :
    ∃ Q : C[X], (∀ i, ‖Q.coeff i‖₊ ≤ 1) ∧
      ((sheetExt hc ν₀ P' h1 hl0 hl1).1
        ((y : L) - algebraMap (RatFunc C) L (aeval (gaussCoord a c) Q)) : ℝ) < ε := by
  obtain ⟨G, Q, -, hQ1, -, hconv⟩ := exists_germ hc ν₀ P' h1 y
  have h := (hconv (gaussDiscVal hc hl0 hl1) (sheetFactor hc ν₀ P' h1 hl0 hl1)
    (sheetFactor_spec hc ν₀ P' h1 hl0 hl1).1)
  have h2 := (tendsto_iff_norm_sub_tendsto_zero.1 h).eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := h2.exists
  refine ⟨Q n, hQ1 n, ?_⟩
  change ‖toLocal _ ((y : L) - _)‖ < ε
  rw [map_sub, norm_sub_rev]
  exact hn

end Sheet

end KummerSheet

end SemistableReduction
