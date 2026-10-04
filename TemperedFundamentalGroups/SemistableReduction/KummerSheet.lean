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

/-! ### A residue `p`-th root of a non-`p`-th power -/

section ResidueRoot

open IsLocalRing FundamentalInequality

variable {M N : Type*} [Field M] [Field N] [Algebra M N]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {u : Valuation M Γ₀} {w : Valuation N Γ₁} [u.HasExtension w]

omit [NontriviallyNormedField C] [IsUltrametricDist C] in
/-- If the residue field of `w` contains a `p`-th root of `ā`, where `X^p - ā` is irreducible
over the residue field of `u`, then `f(w | u) ≥ p`. -/
theorem le_inertiaDeg_of_residue_pow [FiniteDimensional M N] {p : ℕ} (hp : 0 < p)
    {a : ResidueField u.valuationSubring}
    (hirr : Irreducible (X ^ p - Polynomial.C a : (ResidueField u.valuationSubring)[X]))
    {y : ResidueField w.valuationSubring} (hy : y ^ p = algebraMap _ _ a) :
    p ≤ inertiaDeg u w := by
  have : Module.Finite (ResidueField u.valuationSubring) (ResidueField w.valuationSubring) :=
    finite_residueField
  have hint : IsIntegral (ResidueField u.valuationSubring) y := Algebra.IsIntegral.isIntegral _
  have hmin : minpoly (ResidueField u.valuationSubring) y = X ^ p - Polynomial.C a := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C a hp.ne')).symm
    rw [map_sub, map_pow, aeval_X, aeval_C, hy, sub_self]
  have hdeg : (X ^ p - Polynomial.C a : (ResidueField u.valuationSubring)[X]).natDegree = p :=
    natDegree_X_pow_sub_C
  rw [← hdeg, ← hmin, ← IntermediateField.adjoin.finrank hint, inertiaDeg]
  exact IntermediateField.finrank_le_of_le_right le_top |>.trans_eq
    IntermediateField.finrank_top'

end ResidueRoot

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

/-- **Density at the sheet**: since the local degree is one, `C(x)` is dense in `L` for the sheet
extension. -/
theorem exists_ratFunc_approx (z : L) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : RatFunc C,
      ((sheetExt hc ν₀ P' h1 hl0 hl1).1 (z - algebraMap (RatFunc C) L φ) : ℝ) < ε := by
  set ν := gaussDiscVal (a := a) hc hl0 hl1
  set g := sheetFactor hc ν₀ P' h1 hl0 hl1
  have hdeg := (sheetFactor_spec hc ν₀ P' h1 hl0 hl1).2
  set K := UniformSpace.Completion (DiscField ν)
  set τ : K := Algebra.trace K (Local K g.1) (toLocal g z)
  have hτ : algebraMap K (Local K g.1) τ = toLocal g z :=
    algebraMap_trace_of_natDegree_eq_one hdeg _
  obtain ⟨φ', hφ'⟩ := exists_norm_sub_lt _ (denseRange_algebraMap_completion (DiscField ν)) τ hε
  refine ⟨WithAbs.ofAbs φ', ?_⟩
  change ‖toLocal g (z - algebraMap (RatFunc C) L (WithAbs.ofAbs φ'))‖ < ε
  rw [map_sub, toLocal_algebraMap_ratFunc, ← hτ, ← map_sub, norm_algebraMap_local, norm_sub_rev]
  exact hφ'

lemma norm_coeff_le_of_sup {R : C[X]} {r : ℝ≥0}
    (h : Gauss.sup (NormedField.valuation (K := C)) 1 R ≤ r) (i : ℕ) : ‖R.coeff i‖₊ ≤ r := by
  have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) R i).trans h
  simpa [Gauss.term] using this

lemma norm_coeff_lt_of_sup {R : C[X]} {r : ℝ≥0}
    (h : Gauss.sup (NormedField.valuation (K := C)) 1 R < r) (i : ℕ) : ‖R.coeff i‖₊ < r := by
  have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) R i).trans_lt h
  simpa [Gauss.term] using this

/-- `σ = (aff a (l c))⁻¹` maps `t = (x - a)/c` to `l x`. -/
lemma aff_symm_aeval (Q : C[X]) :
    (AffineTwist.aff a (l * c) (mul_ne_zero hl0 hc)).symm (aeval (gaussCoord a c) Q) =
      algebraMap C[X] (RatFunc C) (Q.comp (Polynomial.C l * X)) := by
  have hX : (AffineTwist.aff a (l * c) (mul_ne_zero hl0 hc)).symm (gaussCoord a (l * c)) =
      RatFunc.X := by
    rw [AlgEquiv.symm_apply_eq, AffineTwist.aff_apply, AffineTwist.affHom_X]
  have ht : gaussCoord a c = algebraMap C (RatFunc C) l * gaussCoord a (l * c) := by
    rw [mul_comm l c]; exact gaussCoord_mul hl0
  rw [← Polynomial.aeval_algHom_apply, ht, map_mul, AlgEquiv.commutes, hX, comp_eq_aeval]
  have h := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom C C[X] (RatFunc C))
    (Polynomial.C l * X) Q
  rw [IsScalarTower.coe_toAlgHom'] at h
  rw [← h, map_mul, RatFunc.algebraMap_C, RatFunc.algebraMap_X]
  rfl

variable (p : ℕ) [hp : Fact p.Prime]

/-- **No `p`-th root at the sheet.** Let `G` be a polynomial whose terms at the radius `‖l‖` are
bounded by `‖λ‖^p`, with equality at an index `m` prime to `p`. Then for no `z ∈ L` with
`v z ≤ 1` (`v` the sheet extension) is `z^p ≡ G(t)/λ^p` modulo the maximal ideal of `v`. -/
theorem sheet_no_root [IsAlgClosed C] (hp1 : ‖(p : C)‖ < 1) {G : C[X]} {lam : C} (hlam : lam ≠ 0)
    (hGle : ∀ i, ‖G.coeff i‖ * ‖l‖ ^ i ≤ ‖lam‖ ^ p) {m : ℕ}
    (hGm : ‖G.coeff m‖ * ‖l‖ ^ m = ‖lam‖ ^ p) (hpm : ¬ p ∣ m) (z : L)
    (hz : (sheetExt hc ν₀ P' h1 hl0 hl1).1 z ≤ 1) :
    ¬ (sheetExt hc ν₀ P' h1 hl0 hl1).1 (z ^ p - algebraMap (RatFunc C) L
      (algebraMap C (RatFunc C) (lam ^ p)⁻¹ * aeval (gaussCoord a c) G)) < 1 := by
  intro hlt
  set S := (sheetExt hc ν₀ P' h1 hl0 hl1).1
  have hS : ∀ ψ : RatFunc C, S (algebraMap (RatFunc C) L ψ) =
      gaussRat (NormedField.valuation (K := C)) a
        (Units.mk0 ‖l * c‖₊ (nnnorm_ne_zero_iff.2 (mul_ne_zero hl0 hc))) ψ := fun ψ ↦ by
    rw [← Valuation.comap_apply, (sheetExt hc ν₀ P' h1 hl0 hl1).2]
  obtain ⟨φ, hφ⟩ := exists_ratFunc_approx hc ν₀ P' h1 hl0 hl1 z one_pos
  replace hφ : S (z - algebraMap (RatFunc C) L φ) < 1 := by exact_mod_cast hφ
  set φL := algebraMap (RatFunc C) L φ
  have hφ1 : S φL ≤ 1 := by
    have := Valuation.map_add S (φL - z) z
    rw [sub_add_cancel, Valuation.map_sub_swap] at this
    exact this.trans (max_le hφ.le hz)
  have hpow : S (z ^ p - φL ^ p) < 1 := by
    rw [← geom_sum₂_mul, map_mul]
    refine mul_lt_one_of_nonneg_of_lt_one_right ?_ zero_le hφ
    refine Valuation.map_sum_le S fun i _ ↦ ?_
    rw [map_mul, map_pow, map_pow]
    exact mul_le_one' (pow_le_one₀ zero_le hz) (pow_le_one₀ zero_le hφ1)
  set ψG := algebraMap C (RatFunc C) (lam ^ p)⁻¹ * aeval (gaussCoord a c) G
  have hdiff : S (algebraMap (RatFunc C) L (φ ^ p - ψG)) < 1 := by
    rw [map_sub, map_pow]
    have : φL ^ p - algebraMap (RatFunc C) L ψG =
        -(z ^ p - φL ^ p) + (z ^ p - algebraMap (RatFunc C) L ψG) := by ring
    rw [this]
    exact (Valuation.map_add S _ _).trans_lt (max_lt (by rw [Valuation.map_neg]; exact hpow) hlt)
  rw [hS, ← AffineTwist.gauss1_aff_symm (mul_ne_zero hl0 hc)] at hdiff
  have hφ1' :
      GaussFibre.gauss1 C ((AffineTwist.aff a (l * c) (mul_ne_zero hl0 hc)).symm φ) ≤ 1 := by
    rw [AffineTwist.gauss1_aff_symm, ← hS]; exact hφ1
  set σ := (AffineTwist.aff a (l * c) (mul_ne_zero hl0 hc)).symm
  set Ĝ : C[X] := Polynomial.C (lam ^ p)⁻¹ * G.comp (Polynomial.C l * X)
  have hσG : σ ψG = algebraMap C[X] (RatFunc C) Ĝ := by
    have h2 := aff_symm_aeval (a := a) hc hl0 G
    rw [show ψG = algebraMap C (RatFunc C) (lam ^ p)⁻¹ * aeval (gaussCoord a c) G from rfl,
      map_mul, AlgEquiv.commutes]
    change _ * (AffineTwist.aff a (l * c) (mul_ne_zero hl0 hc)).symm _ = _
    rw [h2, show Ĝ = Polynomial.C (lam ^ p)⁻¹ * G.comp (Polynomial.C l * X) from rfl, map_mul,
      RatFunc.algebraMap_C]
    rfl
  rw [map_sub, map_pow, hσG] at hdiff
  -- write `σ φ = P / Q`
  set φ'' := σ φ
  obtain ⟨d, hd⟩ := GaussFibre.exists_sup_eq φ''.denom
  have hden0 : φ''.denom ≠ 0 := φ''.denom_ne_zero
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, nnnorm_zero] at hd
    have := (Gauss.sup_eq_zero_iff (v := NormedField.valuation (K := C))).1 hd
    exact hden0 this
  set Q := Polynomial.C d⁻¹ * φ''.denom
  set P := Polynomial.C d⁻¹ * φ''.num
  have hQsup : Gauss.sup (NormedField.valuation (K := C)) 1 Q = 1 := by
    rw [Gauss.sup_mul, Gauss.sup_C, hd, NormedField.valuation_apply, nnnorm_inv,
      inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hd0)]
  have hφPQ : φ'' = algebraMap C[X] (RatFunc C) P / algebraMap C[X] (RatFunc C) Q := by
    rw [map_mul, map_mul, mul_div_mul_left _ _ (by simpa using inv_ne_zero hd0),
      RatFunc.num_div_denom]
  have hQ0 : algebraMap C[X] (RatFunc C) Q ≠ 0 := by
    simpa [Q] using ⟨hd0, hden0⟩
  have hPsup : Gauss.sup (NormedField.valuation (K := C)) 1 P ≤ 1 := by
    have : GaussFibre.gauss1 C (algebraMap C[X] (RatFunc C) P) =
        GaussFibre.gauss1 C φ'' * GaussFibre.gauss1 C (algebraMap C[X] (RatFunc C) Q) := by
      rw [hφPQ, map_div₀, div_mul_cancel₀ _ (by
        rw [GaussFibre.gauss1_algebraMap, hQsup]; exact one_ne_zero)]
    rw [← GaussFibre.gauss1_algebraMap, this, GaussFibre.gauss1_algebraMap, hQsup, mul_one]
    exact hφ1'
  have hR : Gauss.sup (NormedField.valuation (K := C)) 1 (P ^ p - Ĝ * Q ^ p) < 1 := by
    have : algebraMap C[X] (RatFunc C) (P ^ p - Ĝ * Q ^ p) =
        (φ'' ^ p - algebraMap C[X] (RatFunc C) Ĝ) * algebraMap C[X] (RatFunc C) Q ^ p := by
      rw [hφPQ, div_pow, map_sub, map_mul, map_pow, map_pow]
      field_simp
    rw [← GaussFibre.gauss1_algebraMap, this, map_mul, map_pow, GaussFibre.gauss1_algebraMap, hQsup,
      one_pow, mul_one]
    exact hdiff
  -- integrality and the contradiction
  have hPint : IntP P := fun i ↦ by exact_mod_cast norm_coeff_le_of_sup hPsup i
  have hQint : IntP Q := fun i ↦ by exact_mod_cast norm_coeff_le_of_sup hQsup.le i
  have hlamp : ‖lam ^ p‖ ≠ 0 := by rw [norm_pow]; exact pow_ne_zero _ (norm_ne_zero_iff.2 hlam)
  have hĜc : ∀ i, Ĝ.coeff i = (lam ^ p)⁻¹ * (G.coeff i * l ^ i) := fun i ↦ by
    rw [coeff_C_mul, comp_C_mul_X_coeff]
  have hĜint : IntP Ĝ := fun i ↦ by
    rw [hĜc, norm_mul, norm_inv, norm_mul, norm_pow, norm_pow]
    exact inv_mul_le_one_of_le₀ (hGle i) (pow_nonneg (norm_nonneg _) _)
  have hĜm : ‖Ĝ.coeff m‖ = 1 := by
    rw [hĜc, norm_mul, norm_inv, norm_mul, norm_pow, norm_pow, hGm,
      inv_mul_cancel₀ (by rw [← norm_pow]; exact hlamp)]
  obtain ⟨j, hj⟩ := Gauss.exists_term_eq_sup (v := NormedField.valuation (K := C)) (r := 1) Q
  rw [hQsup] at hj
  have hQj : ‖Q.coeff j‖ = 1 := by
    simpa [Gauss.term, ← NNReal.coe_inj] using hj
  obtain ⟨i, hi⟩ := exists_norm_coeff_eq_one p hp1 hĜint hĜm hpm hPint hQint hQj
  have := norm_coeff_lt_of_sup hR i
  rw [← NNReal.coe_lt_coe, coe_nnnorm, hi] at this
  exact lt_irrefl _ this

lemma sheet_algebraMap (ψ : RatFunc C) :
    (sheetExt hc ν₀ P' h1 hl0 hl1).1 (algebraMap (RatFunc C) L ψ) =
      gaussRat (NormedField.valuation (K := C)) a
        (Units.mk0 ‖l * c‖₊ (nnnorm_ne_zero_iff.2 (mul_ne_zero hl0 hc))) ψ := by
  rw [← Valuation.comap_apply, (sheetExt hc ν₀ P' h1 hl0 hl1).2]

/-- The value of a polynomial in `t` at the sheet: `max_i ‖Qᵢ‖ ‖l‖^i`. -/
lemma sheet_aeval_le {Q : C[X]} {r : ℝ≥0} (hQ : ∀ i, ‖Q.coeff i‖₊ * ‖l‖₊ ^ i ≤ r) :
    (sheetExt hc ν₀ P' h1 hl0 hl1).1 (algebraMap (RatFunc C) L (aeval (gaussCoord a c) Q)) ≤ r := by
  rw [sheet_algebraMap, DiscGerm.gaussRat_aeval_eq hc (mul_ne_zero hl0 hc)]
  refine Gauss.sup_le_iff.2 fun i ↦ ?_
  simp only [Gauss.term, comp_C_mul_X_coeff, Units.val_one, one_pow, mul_one,
    NormedField.valuation_apply, nnnorm_mul, nnnorm_pow, mul_div_cancel_right₀ _ hc]
  exact hQ i

lemma le_sheet_aeval (Q : C[X]) (i : ℕ) :
    ‖Q.coeff i‖₊ * ‖l‖₊ ^ i ≤
      (sheetExt hc ν₀ P' h1 hl0 hl1).1 (algebraMap (RatFunc C) L (aeval (gaussCoord a c) Q)) := by
  rw [sheet_algebraMap, DiscGerm.gaussRat_aeval_eq hc (mul_ne_zero hl0 hc)]
  have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1)
    (Q.comp (Polynomial.C (l * c / c) * X)) i
  simpa [Gauss.term, comp_C_mul_X_coeff, mul_div_cancel_right₀ _ hc] using this

end Sheet

/-! ### The Kummer extension at the sheet: residue degree `p` -/

section KummerSheet

open IsLocalRing FundamentalInequality

variable {L : Type*} [Field L] [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  {a c : C} (hc : c ≠ 0) (ν₀ : DiscVal a c) (P' : Ideal (DRint a c L)) [P'.IsMaximal]
  (h1 : discDegree ν₀ P' = 1) {l : C} (hl0 : l ≠ 0) (hl1 : ‖l‖ < 1)
  {F' : Type*} [Field F'] [Algebra L F'] [FiniteDimensional L F']
  (p : ℕ) [hp : Fact p.Prime]

variable (L) in
/-- The candidate generator `w = (θ - h̃(t))/λ` of the residue extension. -/
noncomputable def kumW (a c : C) (θ : F') (h' : C[X]) (lam : C) : F' :=
  (θ - algebraMap L F' (algebraMap (RatFunc C) L (aeval (gaussCoord a c) h'))) /
    algebraMap L F' (algebraMap (RatFunc C) L (algebraMap C (RatFunc C) lam))

/-- The element `G(t)/λ^p` of `L`, `G = f̃ - h̃^p`, whose residue is `w̄^p`. -/
noncomputable def kumX (a c : C) (f' h' : C[X]) (lam : C) : L :=
  algebraMap (RatFunc C) L
    (algebraMap C (RatFunc C) (lam ^ p)⁻¹ * aeval (gaussCoord a c) (f' - h' ^ p))

/-- **The residue of `G(t)/λ^p` is not a `p`-th power** in the residue field of the sheet: the
reduced Kummer polynomial `X^p - (G(t)/λ^p)‾` is irreducible. -/
theorem irreducible_kumX [IsAlgClosed C] (hp1 : ‖(p : C)‖ < 1) {f' h' : C[X]} {lam : C}
    (hlam : lam ≠ 0) (hGle : ∀ i, ‖(f' - h' ^ p).coeff i‖ * ‖l‖ ^ i ≤ ‖lam‖ ^ p) {m : ℕ}
    (hGm : ‖(f' - h' ^ p).coeff m‖ * ‖l‖ ^ m = ‖lam‖ ^ p) (hpm : ¬ p ∣ m)
    (hx1 : (sheetExt hc ν₀ P' h1 hl0 hl1).1 (kumX p a c f' h' lam : L) ≤ 1) :
    Irreducible (X ^ p - Polynomial.C (residue (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring
      ⟨kumX p a c f' h' lam, hx1⟩)) := by
  refine X_pow_sub_C_irreducible_of_prime hp.out fun b hb ↦ ?_
  obtain ⟨zO, rfl⟩ := residue_surjective b
  apply sheet_no_root hc ν₀ P' h1 hl0 hl1 p hp1 hlam hGle hGm hpm (zO : L) zO.2
  have h0 : residue (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring
      (zO ^ p - ⟨kumX p a c f' h' lam, hx1⟩) = 0 := by rw [map_sub, map_pow, hb, sub_self]
  rw [residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff] at h0
  exact h0

omit [FiniteDimensional L F'] in
/-- **The purely inseparable case at the sheet, valuations.** Let `θ ∈ F'` with `θ^p = f ∈ L`,
`v` an extension of the sheet extension to `F'`, and polynomials `f̃, h̃` with integral `h̃` such
that `G = f̃ - h̃^p` has terms `‖Gᵢ‖ ‖l‖^i ≤ ‖λ‖^p`, with equality at some index, `‖γ‖ < ‖λ‖ ≤ 1`,
and `v(f - f̃(t)) < ‖λ‖^p`. Then `v w = 1` for `w = (θ - h̃(t))/λ`, `w^p ≡ G(t)/λ^p`, and
`v(G(t)/λ^p) = 1`. -/
theorem insep_value {γ : C} (hγ : γ ^ (p - 1) = -(p : C))
    (v : Valuation F' ℝ≥0) (hvS : v.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    {θ : F'} {f : L} (hθ : θ ^ p = algebraMap L F' f) {f' h' : C[X]}
    (hh' : ∀ i, ‖h'.coeff i‖₊ ≤ 1) {lam : C} (hγl : ‖γ‖₊ < ‖lam‖₊) (hl1' : ‖lam‖₊ ≤ 1)
    (hGle : ∀ i, ‖(f' - h' ^ p).coeff i‖ * ‖l‖ ^ i ≤ ‖lam‖ ^ p) {m : ℕ}
    (hGm : ‖(f' - h' ^ p).coeff m‖ * ‖l‖ ^ m = ‖lam‖ ^ p)
    (hf : (sheetExt hc ν₀ P' h1 hl0 hl1).1
      (f - algebraMap (RatFunc C) L (aeval (gaussCoord a c) f')) < ‖lam‖₊ ^ p) :
    v (kumW L a c θ h' lam) = 1 ∧
      v (kumW L a c θ h' lam ^ p - algebraMap L F' (kumX p a c f' h' lam)) < 1 ∧
      (sheetExt hc ν₀ P' h1 hl0 hl1).1 (kumX p a c f' h' lam) = 1 := by
  set S := (sheetExt hc ν₀ P' h1 hl0 hl1).1
  letI : Algebra C F' :=
    ((algebraMap L F').comp ((algebraMap (RatFunc C) L).comp (algebraMap C (RatFunc C)))).toAlgebra
  set ι : RatFunc C →+* F' := (algebraMap L F').comp (algebraMap (RatFunc C) L)
  have hvι : ∀ ψ : RatFunc C, v (ι ψ) = S (algebraMap (RatFunc C) L ψ) := fun ψ ↦ by
    rw [← hvS, Valuation.comap_apply]; rfl
  have hv : ∀ b : C, v (algebraMap C F' b) = ‖b‖₊ := fun b ↦ by
    change v (ι (algebraMap C (RatFunc C) b)) = _
    rw [hvι, sheet_algebraMap, gaussRat_algebraMap_C, NormedField.valuation_apply]
  set G := f' - h' ^ p
  set H := ι (aeval (gaussCoord a c) h')
  set Fv := ι (aeval (gaussCoord a c) f')
  have hH : v H ≤ 1 := by
    rw [hvι]
    exact sheet_aeval_le hc ν₀ P' h1 hl0 hl1 fun i ↦
      mul_le_one' (hh' i) (pow_le_one₀ zero_le (by exact_mod_cast hl1.le))
  have hFH : Fv - H ^ p = ι (aeval (gaussCoord a c) G) := by
    simp only [Fv, H, G, map_sub, map_pow]
  have hG : v (Fv - H ^ p) = ‖lam‖₊ ^ p := by
    rw [hFH, hvι]
    refine le_antisymm (sheet_aeval_le hc ν₀ P' h1 hl0 hl1 fun i ↦ ?_) ?_
    · have := hGle i
      rw [← NNReal.coe_le_coe]; push_cast; exact this
    · have := le_sheet_aeval hc ν₀ P' h1 hl0 hl1 G m
      refine le_trans (le_of_eq ?_) this
      rw [← NNReal.coe_inj]; push_cast; exact hGm.symm
  have hθF : v (θ ^ p - Fv) < ‖lam‖₊ ^ p := by
    rw [hθ, show Fv = algebraMap L F' (algebraMap (RatFunc C) L (aeval (gaussCoord a c) f')) from
      rfl, ← map_sub, ← Valuation.comap_apply, hvS]
    exact hf
  obtain ⟨hs, hred⟩ := KummerResidue.valuation_sub_eq v hv p hγ hH hγl hl1' hG hθF
  have hlam0 : lam ≠ 0 := nnnorm_ne_zero_iff.1 (lt_of_le_of_lt zero_le hγl).ne'
  have hw : kumW L a c θ h' lam = (θ - H) / algebraMap C F' lam := rfl
  have hxv : algebraMap L F' (kumX p a c f' h' lam) = (Fv - H ^ p) / algebraMap C F' lam ^ p := by
    rw [hFH, div_eq_inv_mul, ← map_pow, ← map_inv₀]
    change ι _ = ι (algebraMap C (RatFunc C) (lam ^ p)⁻¹) * ι _
    rw [← map_mul]
  have hSx : ∀ z : L, S z = v (algebraMap L F' z) := fun z ↦ by
    rw [← hvS, Valuation.comap_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [hw, map_div₀, hv, hs, div_self (nnnorm_ne_zero_iff.2 hlam0)]
  · rw [hw, hxv]; exact hred
  · rw [hSx, hxv, map_div₀, hG, map_pow, hv, div_self (pow_ne_zero _
      (nnnorm_ne_zero_iff.2 hlam0))]

/-- **The purely inseparable case at the sheet**: the residue extension has degree `≥ p`. -/
theorem le_inertiaDeg_insep [IsAlgClosed C] (hp1 : ‖(p : C)‖ < 1) {γ : C}
    (hγ : γ ^ (p - 1) = -(p : C)) (v : Valuation F' ℝ≥0)
    (hvS : v.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    {θ : F'} {f : L} (hθ : θ ^ p = algebraMap L F' f) {f' h' : C[X]}
    (hh' : ∀ i, ‖h'.coeff i‖₊ ≤ 1) {lam : C} (hγl : ‖γ‖₊ < ‖lam‖₊) (hl1' : ‖lam‖₊ ≤ 1)
    (hGle : ∀ i, ‖(f' - h' ^ p).coeff i‖ * ‖l‖ ^ i ≤ ‖lam‖ ^ p) {m : ℕ}
    (hGm : ‖(f' - h' ^ p).coeff m‖ * ‖l‖ ^ m = ‖lam‖ ^ p) (hpm : ¬ p ∣ m)
    (hf : (sheetExt hc ν₀ P' h1 hl0 hl1).1
      (f - algebraMap (RatFunc C) L (aeval (gaussCoord a c) f')) < ‖lam‖₊ ^ p) :
    haveI := DenseCompletion.hasExtension_of_comap_eq hvS
    p ≤ inertiaDeg (sheetExt hc ν₀ P' h1 hl0 hl1).1 v := by
  haveI := DenseCompletion.hasExtension_of_comap_eq hvS
  obtain ⟨hw1, hred, hx1⟩ := insep_value hc ν₀ P' h1 hl0 hl1 p hγ v hvS hθ hh' hγl hl1' hGle
    hGm hf
  have hlam0 : lam ≠ 0 := nnnorm_ne_zero_iff.1 (lt_of_le_of_lt zero_le hγl).ne'
  have hirr := irreducible_kumX hc ν₀ P' h1 hl0 hl1 p hp1 hlam0 hGle hGm hpm hx1.le
  set wO : v.valuationSubring := ⟨kumW L a c θ h' lam, hw1.le⟩
  refine le_inertiaDeg_of_residue_pow hp.out.pos hirr (y := residue v.valuationSubring wO) ?_
  rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap, ← map_pow, ← sub_eq_zero,
    ← map_sub, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact hred

omit [FiniteDimensional L F'] in
/-- The residues of `1, w, …, w^(p-1)` are linearly independent over the residue field of the
sheet. -/
theorem insep_linearIndependent [IsAlgClosed C] (hp1 : ‖(p : C)‖ < 1) {γ : C}
    (hγ : γ ^ (p - 1) = -(p : C)) (v : Valuation F' ℝ≥0)
    (hvS : v.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    {θ : F'} {f : L} (hθ : θ ^ p = algebraMap L F' f) {f' h' : C[X]}
    (hh' : ∀ i, ‖h'.coeff i‖₊ ≤ 1) {lam : C} (hγl : ‖γ‖₊ < ‖lam‖₊) (hl1' : ‖lam‖₊ ≤ 1)
    (hGle : ∀ i, ‖(f' - h' ^ p).coeff i‖ * ‖l‖ ^ i ≤ ‖lam‖ ^ p) {m : ℕ}
    (hGm : ‖(f' - h' ^ p).coeff m‖ * ‖l‖ ^ m = ‖lam‖ ^ p) (hpm : ¬ p ∣ m)
    (hf : (sheetExt hc ν₀ P' h1 hl0 hl1).1
      (f - algebraMap (RatFunc C) L (aeval (gaussCoord a c) f')) < ‖lam‖₊ ^ p) :
    haveI := DenseCompletion.hasExtension_of_comap_eq hvS
    ∃ hw : v (kumW L a c θ h' lam) ≤ 1,
      LinearIndependent (ResidueField (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring)
        (fun j : Fin p ↦ residue v.valuationSubring
          ((⟨kumW L a c θ h' lam, hw⟩ : v.valuationSubring) ^ (j : ℕ))) := by
  haveI := DenseCompletion.hasExtension_of_comap_eq hvS
  obtain ⟨hw1, hred, hx1⟩ := insep_value hc ν₀ P' h1 hl0 hl1 p hγ v hvS hθ hh' hγl hl1' hGle
    hGm hf
  have hlam0 : lam ≠ 0 := nnnorm_ne_zero_iff.1 (lt_of_le_of_lt zero_le hγl).ne'
  have hirr := irreducible_kumX hc ν₀ P' h1 hl0 hl1 p hp1 hlam0 hGle hGm hpm hx1.le
  refine ⟨hw1.le, ?_⟩
  set y := residue v.valuationSubring ⟨kumW L a c θ h' lam, hw1.le⟩
  set a' := residue (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring ⟨_, hx1.le⟩
  have hy : y ^ p = algebraMap _ (ResidueField v.valuationSubring) a' := by
    rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap, ← map_pow, ← sub_eq_zero,
      ← map_sub, residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact hred
  have hmin : minpoly (ResidueField (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring) y =
      X ^ p - Polynomial.C a' := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ (monic_X_pow_sub_C a' hp.out.ne_zero)).symm
    rw [map_sub, map_pow, aeval_X, aeval_C, hy, sub_self]
  have hdeg : (minpoly (ResidueField (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring) y).natDegree
      = p := by rw [hmin, natDegree_X_pow_sub_C]
  have hli := linearIndependent_pow
    (K := ResidueField (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring) y
  rw [hdeg] at hli
  simp only [map_pow]
  exact hli

/-- **Uniqueness of the extension at the sheet** (purely inseparable case): `F'` is spanned by the
powers `θ^i`, `i < p`, so it is spanned by the `w^j`, and the value of `Σ cⱼ wʲ` is
`max_j v(cⱼ)` for every extension (orthogonality); hence there is exactly one extension. -/
theorem insep_ext_unique [IsAlgClosed C] (hp1 : ‖(p : C)‖ < 1) {γ : C}
    (hγ : γ ^ (p - 1) = -(p : C)) {v₁ v₂ : Valuation F' ℝ≥0}
    (hv₁ : v₁.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    (hv₂ : v₂.comap (algebraMap L F') = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    {θ : F'} {f : L} (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤) {f' h' : C[X]}
    (hh' : ∀ i, ‖h'.coeff i‖₊ ≤ 1) {lam : C} (hγl : ‖γ‖₊ < ‖lam‖₊) (hl1' : ‖lam‖₊ ≤ 1)
    (hGle : ∀ i, ‖(f' - h' ^ p).coeff i‖ * ‖l‖ ^ i ≤ ‖lam‖ ^ p) {m : ℕ}
    (hGm : ‖(f' - h' ^ p).coeff m‖ * ‖l‖ ^ m = ‖lam‖ ^ p) (hpm : ¬ p ∣ m)
    (hf : (sheetExt hc ν₀ P' h1 hl0 hl1).1
      (f - algebraMap (RatFunc C) L (aeval (gaussCoord a c) f')) < ‖lam‖₊ ^ p) :
    v₁ = v₂ := by
  set w := kumW L a c θ h' lam
  -- the dimension is at most `p`
  have hdim : Module.finrank L F' ≤ p := by
    have := finrank_range_le_card (R := L) (fun i : Fin p ↦ θ ^ (i : ℕ))
    rwa [Set.finrank, hspan, finrank_top, Fintype.card_fin] at this
  -- for each extension: orthogonality of the powers of `w`
  have key : ∀ (v : Valuation F' ℝ≥0) (hv : v.comap (algebraMap L F') =
      (sheetExt hc ν₀ P' h1 hl0 hl1).1),
      Submodule.span L (Set.range fun j : Fin p ↦ w ^ (j : ℕ)) = ⊤ ∧
      ∀ c : Fin p → L, v (∑ j, c j • w ^ (j : ℕ)) =
        Finset.univ.sup fun j ↦ (sheetExt hc ν₀ P' h1 hl0 hl1).1 (c j) := by
    intro v hv
    haveI := DenseCompletion.hasExtension_of_comap_eq hv
    obtain ⟨hw, hli⟩ := insep_linearIndependent hc ν₀ P' h1 hl0 hl1 p hp1 hγ v hv hθ hh' hγl hl1'
      hGle hGm hpm hf
    have hliL := FundamentalInequality.linearIndependent_of_residue hli
    simp only [SubmonoidClass.coe_pow] at hliL
    refine ⟨hliL.span_eq_top_of_card_eq_finrank' ?_, fun c ↦ ?_⟩
    · have := hliL.fintype_card_le_finrank
      rw [Fintype.card_fin] at this ⊢
      exact le_antisymm this hdim
    · have h := FundamentalInequality.valuation_sum_eq_sup hli Finset.univ c
      have hsum : (∑ j, c j • w ^ (j : ℕ)) = ∑ j ∈ Finset.univ, algebraMap L F' (c j) *
          (((⟨w, hw⟩ : v.valuationSubring) ^ (j : ℕ) : v.valuationSubring) : F') := by
        simp [Algebra.smul_def, w]
      rw [hsum, h]
      congr 1
      ext j
      rw [← Valuation.comap_apply, hv]
  obtain ⟨hspan₁, hval₁⟩ := key v₁ hv₁
  obtain ⟨-, hval₂⟩ := key v₂ hv₂
  refine Valuation.ext fun y ↦ ?_
  have hy : y ∈ Submodule.span L (Set.range fun j : Fin p ↦ w ^ (j : ℕ)) := hspan₁ ▸ trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hy
  rw [hval₁, hval₂]

end KummerSheet

end KummerSheet

end SemistableReduction
