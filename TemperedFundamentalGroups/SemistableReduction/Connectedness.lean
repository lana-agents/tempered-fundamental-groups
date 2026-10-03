/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GenusCount
import TemperedFundamentalGroups.SemistableReduction.TensorIdempotent

/-!
# Connectedness of the special fibre over the Gauss point

Blueprint §9.5, G6.8 (G8.2–G8.5), and §9.11 (no completeness). Let `C` be algebraically closed
(not necessarily complete, e.g. `K̄`), `F / C(X)` finite with an orthonormal `C(X)`-basis for
`gnorm` (G6.3). The main result `no_split` is the
elementary "GAGA for `ℙ¹`" replacing Zariski's connectedness theorem: if `e ∈ F` is integral over
`C[x]` and `e' ∈ F` is integral over `C[x⁻¹]`, both of norm `≤ 1`, and at every extension `w` of
the Gauss valuation both reduce to the same idempotent `ε_w ∈ {0, 1}`, then `ε` is constant.

Proof: the Newton iterates `eₙ = N^[n](e)`, `N(t) = 3t² - 2t³`, converge (for `gnorm`) to the
idempotent, and so do the `e'ₙ`. For an integral `C(X)`-basis `d` of `F`, the traces
`Tr(eₙ dₖ) ∈ C[X]` and `Tr(e'ₙ dₖ) ∈ X^D C[X⁻¹]` differ by `O(ρ^{2ⁿ})` in the Gauss norm, so the
coefficients of `Tr(eₙ dₖ)` in degrees `> D` tend to `0`. Truncating them gives elements
`zₙ = Σ_{i ≤ D', k} aₙ(i, k) Xⁱ d*ₖ` (trace-dual basis `d*`) of a fixed finite-dimensional
`C`-subspace, close to `eₙ`, whose coefficients are Cauchy and whose idempotency defects
`h (zₙ² - zₙ)` (`h` a common denominator of the structure constants) tend to `0` coordinatewise.
Their limit in `Ĉ ⊗_C F` (`Ĉ` the completion) is an idempotent, hence `0` or `1`
(`TensorIdempotent.exists_tendsto_of_approx_idempotent`: `C` algebraically closed); so the `eₙ`
tend to `0` or `1` in `gnorm`, contradicting the two given extensions.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion CurvePlace
  TensorIdempotent
open scoped TensorProduct

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]

section Laurent

/-- The coefficients in degrees `> D` of `P - X^D Q(X⁻¹)` are those of `P`. -/
lemma nnnorm_coeff_le_gauss1 (P Q : C[X]) (D : ℕ) {i : ℕ} (hi : D < i) :
    ‖P.coeff i‖₊ ≤ gauss1 C (algebraMap C[X] (RatFunc C) P -
      RatFunc.X ^ D * aeval (RatFunc.X : RatFunc C)⁻¹ Q) := by
  set M := Q.natDegree
  have hX : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have key : RatFunc.X ^ M * (algebraMap C[X] (RatFunc C) P -
      RatFunc.X ^ D * aeval (RatFunc.X : RatFunc C)⁻¹ Q) =
      algebraMap C[X] (RatFunc C) (X ^ M * P - X ^ D * Q.reverse) := by
    have h1 : (RatFunc.X : RatFunc C) ^ M * RatFunc.X⁻¹ ^ M = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hX, one_pow]
    rw [aeval_X_inv, _root_.map_sub, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X,
      mul_sub]
    congr 1
    calc (RatFunc.X : RatFunc C) ^ M * (RatFunc.X ^ D *
          (algebraMap C[X] (RatFunc C) Q.reverse * RatFunc.X⁻¹ ^ Q.natDegree)) =
        RatFunc.X ^ D * algebraMap C[X] (RatFunc C) Q.reverse *
          (RatFunc.X ^ M * RatFunc.X⁻¹ ^ M) := by ring
      _ = _ := by rw [h1, mul_one]
  have hg : gauss1 C (algebraMap C[X] (RatFunc C) P -
      RatFunc.X ^ D * aeval (RatFunc.X : RatFunc C)⁻¹ Q) =
      Gauss.sup (NormedField.valuation (K := C)) 1 (X ^ M * P - X ^ D * Q.reverse) := by
    rw [← gauss1_algebraMap, ← key, map_mul, map_pow, gauss1_X, one_pow, one_mul]
  rw [hg]
  have hcoeff : (X ^ M * P - X ^ D * Q.reverse).coeff (M + i) = P.coeff i := by
    rw [coeff_sub, coeff_X_pow_mul', coeff_X_pow_mul']
    rw [if_pos (by omega), if_pos (by omega), Nat.add_sub_cancel_left]
    rw [coeff_eq_zero_of_natDegree_lt (p := Q.reverse), sub_zero]
    exact (reverse_natDegree_le Q).trans_lt (by omega)
  have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1)
    (X ^ M * P - X ^ D * Q.reverse) (M + i)
  simpa [Gauss.term, hcoeff] using this

end Laurent

section Limit

open Filter Topology

omit [IsUltrametricDist C] in
lemma pow_two_pow_le {ρ : ℝ≥0} (hρ : ρ ≤ 1) (n : ℕ) : ρ ^ (2 ^ n) ≤ ρ ^ n :=
  pow_le_pow_of_le_one zero_le hρ (Nat.lt_two_pow_self).le

omit [IsUltrametricDist C] in
lemma tendsto_pow_two_pow {ρ : ℝ≥0} (hρ : ρ < 1) :
    Tendsto (fun n : ℕ ↦ ρ ^ (2 ^ n)) atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hρ) (fun _ ↦ zero_le)
    (pow_two_pow_le hρ.le)

omit [IsUltrametricDist C] in
lemma tendsto_nnreal_zero_iff {u : ℕ → ℝ≥0} :
    Tendsto u atTop (𝓝 0) ↔ ∀ ε : ℝ≥0, 0 < ε → ∀ᶠ n in atTop, u n < ε := by
  rw [tendsto_order]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨fun a ha ↦ absurd ha (not_lt_zero (a := a)), h⟩⟩

end Limit

section Trace

variable [FiniteDimensional (RatFunc C) F]

omit [IsUltrametricDist C] in
/-- The trace of an element integral over `C[x]` is a polynomial. -/
lemma exists_trace_eq {f : F} (hint : IsIntegral (Algebra.adjoin C {xF C F}) f) :
    ∃ P : C[X], Algebra.trace (RatFunc C) F f = algebraMap C[X] (RatFunc C) P := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, nextCoeff_of_natDegree_pos
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral f))]
  obtain ⟨Q, hQ⟩ := exists_minpoly_coeff_eq' hint ((minpoly (RatFunc C) f).natDegree - 1)
  exact ⟨(Module.finrank (RatFunc C)⟮f⟯ F : C[X]) * -Q, by
    rw [← hQ, map_mul, _root_.map_neg, map_natCast]⟩

omit [IsUltrametricDist C] in
/-- The trace of an element integral over `C[x⁻¹]` is a polynomial in `X⁻¹`. -/
lemma exists_trace_eq_inv {f : F} (hint : IsIntegral (Algebra.adjoin C {(xF C F)⁻¹}) f) :
    ∃ Q : C[X], Algebra.trace (RatFunc C) F f = aeval (RatFunc.X : RatFunc C)⁻¹ Q := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, nextCoeff_of_natDegree_pos
    (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral f))]
  obtain ⟨Q, hQ⟩ := exists_minpoly_coeff_eq_inv hint ((minpoly (RatFunc C) f).natDegree - 1)
  exact ⟨(Module.finrank (RatFunc C)⟮f⟯ F : C[X]) * -Q, by
    rw [← hQ, map_mul, _root_.map_neg, map_natCast]⟩

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
/-- The Gauss norm of the trace is bounded by the norm (orthonormal basis). -/
lemma gauss1_trace_le [Fintype (Ext C F)] {ι : Type*} [Fintype ι]
    {b : Module.Basis ι (RatFunc C) F}
    (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
    (f : F) : gauss1 C (Algebra.trace (RatFunc C) F f) ≤ gnorm C f := by
  classical
  rw [Algebra.trace_eq_matrix_trace b f, Matrix.trace]
  exact Valuation.map_sum_le _ fun i _ ↦ gauss1_leftMulMatrix_le hb f i i

omit [IsUltrametricDist C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma trace_xF_pow_mul (D : ℕ) (g : F) :
    Algebra.trace (RatFunc C) F (xF C F ^ D * g) =
      RatFunc.X ^ D * Algebra.trace (RatFunc C) F g := by
  rw [xF, ← map_pow, ← Algebra.smul_def, map_smul, smul_eq_mul]

end Trace

section Newton

/-- The Newton step `t ↦ 3t² - 2t³` for idempotents. -/
noncomputable def newton (t : F) : F := 3 * t ^ 2 - 2 * t ^ 3

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma valuation_natCast_le_one (w : Valuation F ℝ≥0) (n : ℕ) : w (n : F) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma valuation_newton_sub_one_le {w : Valuation F ℝ≥0} {t : F} (ht : w t ≤ 1) :
    w (newton t - 1) ≤ w (t - 1) ^ 2 := by
  have : newton t - 1 = -((t - 1) ^ 2 * (2 * t + 1)) := by simp only [newton]; ring
  rw [this, Valuation.map_neg, map_mul, map_pow]
  refine mul_le_of_le_one_right' ((Valuation.map_add _ _ _).trans (max_le ?_ (by simp)))
  rw [map_mul]
  exact mul_le_one' (by exact_mod_cast valuation_natCast_le_one w 2) ht

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma valuation_newton_le {w : Valuation F ℝ≥0} {t : F} (ht : w t ≤ 1) :
    w (newton t) ≤ w t ^ 2 := by
  have : newton t = t ^ 2 * (3 - 2 * t) := by simp only [newton]; ring
  rw [this, map_mul, map_pow]
  refine mul_le_of_le_one_right' ((Valuation.map_sub _ _ _).trans (max_le ?_ ?_))
  · exact_mod_cast valuation_natCast_le_one w 3
  · rw [map_mul]
    exact mul_le_one' (by exact_mod_cast valuation_natCast_le_one w 2) ht

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma valuation_newton_le_one {w : Valuation F ℝ≥0} {t : F} (ht : w t ≤ 1) :
    w (newton t) ≤ 1 :=
  (valuation_newton_le ht).trans (pow_le_one₀ zero_le ht)

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma valuation_iterate_le_one {w : Valuation F ℝ≥0} {t : F} (ht : w t ≤ 1) (n : ℕ) :
    w (newton^[n] t) ≤ 1 := by
  induction n with
  | zero => exact ht
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact valuation_newton_le_one ih

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma valuation_iterate_sub_one_le {w : Valuation F ℝ≥0} {t : F} (ht : w t ≤ 1) (n : ℕ) :
    w (newton^[n] t - 1) ≤ w (t - 1) ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ, pow_mul]
    exact (valuation_newton_sub_one_le (valuation_iterate_le_one ht n)).trans
      (pow_le_pow_left₀ zero_le ih 2)

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma valuation_iterate_le {w : Valuation F ℝ≥0} {t : F} (ht : w t ≤ 1) (n : ℕ) :
    w (newton^[n] t) ≤ w t ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ, pow_mul]
    exact (valuation_newton_le (valuation_iterate_le_one ht n)).trans
      (pow_le_pow_left₀ zero_le ih 2)

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma isIntegral_iterate {A : Type*} [CommRing A] [Algebra A F] {t : F} (ht : IsIntegral A t)
    (n : ℕ) : IsIntegral A (newton^[n] t) := by
  induction n with
  | zero => exact ht
  | succ n ih =>
    rw [Function.iterate_succ_apply', newton]
    have h3 : IsIntegral A (3 : F) := by
      have := isIntegral_algebraMap (R := A) (A := F) (x := (3 : A))
      rwa [map_ofNat] at this
    have h2 : IsIntegral A (2 : F) := by
      have := isIntegral_algebraMap (R := A) (A := F) (x := (2 : A))
      rwa [map_ofNat] at this
    exact (h3.mul (ih.pow 2)).sub (h2.mul (ih.pow 3))

end Newton

section IntegralBasis

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField_F

omit [IsUltrametricDist C] in
/-- Every `f ∈ F` has a nonzero polynomial multiple `Q(x) f` in some `L(D (x)_∞)`. -/
lemma exists_aeval_mul_mem_rrSpace (f : F) :
    ∃ Q : C[X], Q ≠ 0 ∧ ∃ D : ℕ, aeval (xF C F) Q * f ∈ rrSpace (D • poleDivisor C (xF C F)) := by
  classical
  set x := xF C F
  set S := ((finite_setOf_notMem (k := C) f).toFinset).filter fun P ↦ x ∈ P.V
  have ha (P : CurvePlace C F) : ∃ a : C, x ∈ P.V → P.valuation (x - algebraMap C F a) < 1 := by
    by_cases hx : x ∈ P.V
    · obtain ⟨a, ha⟩ := P.exists_valuation_sub_lt_one hx
      exact ⟨a, fun _ ↦ ha⟩
    · exact ⟨0, fun h ↦ absurd h hx⟩
  choose a ha using ha
  set Q : C[X] := ∏ P ∈ S, (X - Polynomial.C (a P)) ^ P.poleOrder f
  have hQ0 : Q ≠ 0 := Finset.prod_ne_zero_iff.2 fun P _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have hy : aeval x Q = ∏ P ∈ S, (x - algebraMap C F (a P)) ^ P.poleOrder f := by
    simp [Q, map_prod]
  have hint (P' : CurvePlace C F) (hx : x ∈ P'.V) : aeval x Q * f ∈ P'.V := by
    have hfac (P : CurvePlace C F) : x - algebraMap C F (a P) ∈ P'.V :=
      sub_mem hx (P'.algebraMap_mem _)
    by_cases hP' : P' ∈ S
    · rw [← P'.valuation_le_one_iff, map_mul, hy, map_prod, ← Finset.mul_prod_erase _ _ hP']
      have hpole : f ∉ P'.V := by
        simpa [S] using (Finset.mem_filter.1 hP').1
      have hvf := P'.valuation_eq_exp_poleOrder hpole
      have hlt := ha P' hx
      have hle : P'.valuation (x - algebraMap C F (a P')) ≤ exp (-1) :=
        WithZero.le_exp_of_lt_exp_add_one (by simpa using hlt)
      have hrest : ∏ P ∈ S.erase P', P'.valuation ((x - algebraMap C F (a P)) ^ P.poleOrder f)
          ≤ 1 := Finset.prod_le_one' fun P _ ↦ by
        rw [map_pow]
        exact pow_le_one₀ zero_le (P'.valuation_le_one_iff.2 (hfac P))
      calc P'.valuation ((x - algebraMap C F (a P')) ^ P'.poleOrder f) *
            (∏ P ∈ S.erase P', P'.valuation ((x - algebraMap C F (a P)) ^ P.poleOrder f)) *
            P'.valuation f ≤ exp (-1) ^ P'.poleOrder f * 1 * exp (P'.poleOrder f : ℤ) := by
            rw [map_pow, hvf]
            gcongr
        _ = 1 := by rw [mul_one, ← exp_nsmul, ← exp_add]; simp
    · have hf : f ∈ P'.V := by
        by_contra hf
        exact hP' (Finset.mem_filter.2 ⟨by simpa using hf, hx⟩)
      refine mul_mem ?_ hf
      rw [hy]
      exact prod_mem fun P _ ↦ pow_mem (hfac P) _
  refine ⟨Q, hQ0, poleNorm C (aeval x Q * f), fun P ↦ ?_⟩
  rw [Finsupp.smul_apply, poleDivisor_apply, nsmul_eq_mul]
  by_cases hx : x ∈ P.V
  · refine (P.valuation_le_one_iff.2 (hint P hx)).trans ?_
    rw [← exp_zero, exp_le_exp]
    positivity
  · refine (P.valuation_le_exp_poleOrder _).trans (exp_le_exp.2 ?_)
    have h1 := poleOrder_le_poleNorm P (aeval x Q * f)
    have h2 := P.one_le_poleOrder hx
    have : (P.poleOrder (aeval x Q * f) : ℤ) ≤ poleNorm C (aeval x Q * f) := by exact_mod_cast h1
    have h3 : (1 : ℤ) ≤ P.poleOrder x := by exact_mod_cast h2
    nlinarith [Int.natCast_nonneg (poleNorm C (aeval x Q * f))]

omit [IsUltrametricDist C] in
lemma rrSpace_nsmul_mono {D D' : ℕ} (h : D ≤ D') :
    rrSpace (D • poleDivisor C (xF C F)) ≤ rrSpace (D' • poleDivisor C (xF C F)) :=
  rrSpace_mono (nsmul_le_nsmul_left (poleDivisor_nonneg _) h)

/-- A `C(X)`-basis of `F` consisting of elements of norm `≤ 1` in some `L(D (x)_∞)`. -/
lemma exists_integral_basis [Fintype (Ext C F)] {ι : Type*} [Finite ι]
    (b : Module.Basis ι (RatFunc C) F) :
    ∃ (d : Module.Basis ι (RatFunc C) F) (D : ℕ), ∀ k,
      d k ∈ rrSpace (D • poleDivisor C (xF C F)) ∧ gnorm C (d k) ≤ 1 := by
  classical
  haveI := Fintype.ofFinite ι
  choose Q hQ0 D hD using fun k ↦ exists_aeval_mul_mem_rrSpace (C := C) (b k)
  have hγ (k : ι) : ∃ γ : C, γ ≠ 0 ∧ ‖γ‖₊ * gnorm C (aeval (xF C F) (Q k) * b k) ≤ 1 := by
    set g := gnorm C (aeval (xF C F) (Q k) * b k)
    obtain ⟨γ, hγ0, hγ⟩ := NormedField.exists_norm_lt C (r := 1 / ((g : ℝ) + 1)) (by positivity)
    refine ⟨γ, norm_pos_iff.1 hγ0, ?_⟩
    have hg : (0 : ℝ) ≤ g := g.2
    have : ‖γ‖ * g ≤ 1 := by
      calc ‖γ‖ * g ≤ 1 / ((g : ℝ) + 1) * g := by gcongr
        _ ≤ 1 := by rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; linarith
    exact_mod_cast this
  choose γ hγ0 hγ using hγ
  have hu (k : ι) : algebraMap C (RatFunc C) (γ k) * algebraMap C[X] (RatFunc C) (Q k) ≠ 0 :=
    mul_ne_zero (by simpa using hγ0 k)
      (by simpa using (IsFractionRing.injective C[X] (RatFunc C)).ne (hQ0 k))
  set u : ι → (RatFunc C)ˣ := fun k ↦ Units.mk0 _ (hu k)
  have hd (k : ι) : b.unitsSMul u k = γ k • (aeval (xF C F) (Q k) * b k) := by
    rw [Module.Basis.unitsSMul_apply, Units.smul_def, Units.val_mk0, Algebra.smul_def,
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, aeval_xF, mul_assoc]
  refine ⟨b.unitsSMul u, Finset.univ.sup D, fun k ↦ ⟨?_, ?_⟩⟩
  · rw [hd]
    exact rrSpace_nsmul_mono (Finset.le_sup (f := D) (Finset.mem_univ k))
      ((rrSpace _).smul_mem (γ k) (hD k))
  · rw [hd, LatticeReduction.gnorm_smul_C]
    exact hγ k

end IntegralBasis

section Bridge

lemma nnnorm_coeff_le_gauss1_algebraMap (Q : C[X]) (i : ℕ) :
    ‖Q.coeff i‖₊ ≤ gauss1 C (algebraMap C[X] (RatFunc C) Q) := by
  rw [gauss1_algebraMap]
  have h1 := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) Q i
  simpa [Gauss.term] using h1

lemma gauss1_algebraMap_le_of_coeff (Q : C[X]) {r : ℝ≥0} (h : ∀ i, ‖Q.coeff i‖₊ ≤ r) :
    gauss1 C (algebraMap C[X] (RatFunc C) Q) ≤ r := by
  rw [gauss1_algebraMap, Gauss.sup_le_iff]
  intro i
  simpa [Gauss.term] using h i

end Bridge

section Main

open Filter Topology


variable [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F]
  [Fintype (Ext C F)]

attribute [local instance] isCurveFunctionField_F

/-- **G6.8 (no splitting)**: if `e` is integral over `C[x]`, `e'` integral over `C[x⁻¹]`, both of
norm `≤ 1`, and at every extension `w` of the Gauss valuation both reduce to `1` or both reduce
to `0`, then they reduce to `1` everywhere or to `0` everywhere. -/
theorem no_split {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
    (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
    {e e' : F} (he : IsIntegral (Algebra.adjoin C {xF C F}) e)
    (he' : IsIntegral (Algebra.adjoin C {(xF C F)⁻¹}) e') (hne : gnorm C e ≤ 1)
    (hne' : gnorm C e' ≤ 1)
    (hw : ∀ w : Ext C F, (w.1 (e - 1) < 1 ∧ w.1 (e' - 1) < 1) ∨ (w.1 e < 1 ∧ w.1 e' < 1)) :
    (∀ w : Ext C F, w.1 (e - 1) < 1) ∨ ∀ w : Ext C F, w.1 e < 1 := by
  classical
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc₀, hc₁⟩ := hcon
  push Not at hc₀ hc₁
  obtain ⟨w₀, hw₀⟩ := hc₀
  obtain ⟨w₁, hw₁⟩ := hc₁
  -- a uniform defect `ρ < 1`
  set δ : Ext C F → ℝ≥0 := fun w ↦
    min (max (w.1 (e - 1)) (w.1 (e' - 1))) (max (w.1 e) (w.1 e'))
  have hδ (w : Ext C F) : δ w < 1 := by
    rcases hw w with h | h
    · exact min_lt_of_left_lt (max_lt h.1 h.2)
    · exact min_lt_of_right_lt (max_lt h.1 h.2)
  set ρ := Finset.univ.sup δ
  have hρ : ρ < 1 := (Finset.sup_lt_iff one_pos).2 fun w _ ↦ hδ w
  have hcase (w : Ext C F) :
      (w.1 (e - 1) ≤ ρ ∧ w.1 (e' - 1) ≤ ρ) ∨ (w.1 e ≤ ρ ∧ w.1 e' ≤ ρ) := by
    have := Finset.le_sup (f := δ) (Finset.mem_univ w)
    rcases min_le_iff.1 this with h | h
    · exact Or.inl ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
    · exact Or.inr ⟨(le_max_left _ _).trans h, (le_max_right _ _).trans h⟩
  -- the Newton iterates
  set E : ℕ → F := fun n ↦ newton^[n] e
  set E' : ℕ → F := fun n ↦ newton^[n] e'
  have hwe (w : Ext C F) : w.1 e ≤ 1 := (le_gnorm w e).trans hne
  have hwe' (w : Ext C F) : w.1 e' ≤ 1 := (le_gnorm w e').trans hne'
  have hpow (n : ℕ) {a : ℝ≥0} (ha : a ≤ ρ) : a ^ (2 ^ n) ≤ ρ ^ (2 ^ n) :=
    pow_le_pow_left₀ zero_le ha _
  have hA (w : Ext C F) (h : w.1 (e - 1) ≤ ρ ∧ w.1 (e' - 1) ≤ ρ) (n : ℕ) :
      w.1 (E n - 1) ≤ ρ ^ (2 ^ n) ∧ w.1 (E' n - 1) ≤ ρ ^ (2 ^ n) :=
    ⟨(valuation_iterate_sub_one_le (hwe w) n).trans (hpow n h.1),
      (valuation_iterate_sub_one_le (hwe' w) n).trans (hpow n h.2)⟩
  have hB (w : Ext C F) (h : w.1 e ≤ ρ ∧ w.1 e' ≤ ρ) (n : ℕ) :
      w.1 (E n) ≤ ρ ^ (2 ^ n) ∧ w.1 (E' n) ≤ ρ ^ (2 ^ n) :=
    ⟨(valuation_iterate_le (hwe w) n).trans (hpow n h.1),
      (valuation_iterate_le (hwe' w) n).trans (hpow n h.2)⟩
  have hE1 (w : Ext C F) (n : ℕ) : w.1 (E n) ≤ 1 := valuation_iterate_le_one (hwe w) n
  have hρn (n : ℕ) : ρ ^ (2 ^ (n + 1)) ≤ ρ ^ (2 ^ n) :=
    pow_le_pow_of_le_one zero_le hρ.le (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
  have hρ1 (n : ℕ) : ρ ^ (2 ^ n) < 1 := pow_lt_one₀ zero_le hρ (by positivity)
  have hdiff (n : ℕ) : gnorm C (E (n + 1) - E n) ≤ ρ ^ (2 ^ n) := gnorm_le_iff.2 fun w ↦ by
    rcases hcase w with h | h
    · have : E (n + 1) - E n = (E (n + 1) - 1) - (E n - 1) := by ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans
        (max_le ((hA w h (n + 1)).1.trans (hρn n)) (hA w h n).1)
    · exact (Valuation.map_sub _ _ _).trans
        (max_le ((hB w h (n + 1)).1.trans (hρn n)) (hB w h n).1)
  have hdiff' (n : ℕ) : gnorm C (E n - E' n) ≤ ρ ^ (2 ^ n) := gnorm_le_iff.2 fun w ↦ by
    rcases hcase w with h | h
    · have : E n - E' n = (E n - 1) - (E' n - 1) := by ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans (max_le (hA w h n).1 (hA w h n).2)
    · exact (Valuation.map_sub _ _ _).trans (max_le (hB w h n).1 (hB w h n).2)
  have hidem (n : ℕ) : gnorm C (E n ^ 2 - E n) ≤ ρ ^ (2 ^ n) := gnorm_le_iff.2 fun w ↦ by
    have : E n ^ 2 - E n = E n * (E n - 1) := by ring
    rw [this, map_mul]
    rcases hcase w with h | h
    · exact (mul_le_of_le_one_left' (hE1 w n)).trans (hA w h n).1
    · refine (mul_le_of_le_one_right' ?_).trans (hB w h n).1
      exact (Valuation.map_sub _ _ _).trans (max_le (hE1 w n) (by simp))
  -- an integral basis and the traces
  obtain ⟨d, D, hd⟩ := exists_integral_basis (C := C) b
  set x := xF C F
  have hEd (n : ℕ) (k : ι) : IsIntegral (Algebra.adjoin C {x}) (E n * d k) :=
    (isIntegral_iterate he n).mul (isIntegral_of_mem_rrSpace (hd k).1)
  have hE'd (n : ℕ) (k : ι) :
      IsIntegral (Algebra.adjoin C {x⁻¹}) (E' n * (d k * x⁻¹ ^ D)) :=
    (isIntegral_iterate he' n).mul (isIntegral_div_of_mem_rrSpace (hd k).1)
  choose P hP using fun n k ↦ exists_trace_eq (hEd n k)
  choose Q hQ using fun n k ↦ exists_trace_eq_inv (hE'd n k)
  have hx0 : x ≠ 0 := by
    intro h
    have := valuation_xF (F := F) w₀
    rw [show xF C F = x from rfl, h, map_zero] at this
    exact zero_ne_one this
  have htrE' (n : ℕ) (k : ι) : Algebra.trace (RatFunc C) F (E' n * d k) =
      RatFunc.X ^ D * aeval (RatFunc.X : RatFunc C)⁻¹ (Q n k) := by
    rw [← hQ, ← trace_xF_pow_mul]
    congr 1
    have hxD : x ^ D * x⁻¹ ^ D = 1 := by rw [← mul_pow, mul_inv_cancel₀ hx0, one_pow]
    calc E' n * d k = E' n * d k * (x ^ D * x⁻¹ ^ D) := by rw [hxD, mul_one]
      _ = x ^ D * (E' n * (d k * x⁻¹ ^ D)) := by ring
  have hdk (k : ι) : gnorm C (d k) ≤ 1 := (hd k).2
  have hPc (k : ι) (n : ℕ) : Gauss.sup (NormedField.valuation (K := C)) 1
      (P (n + 1) k - P n k) ≤ ρ ^ (2 ^ n) := by
    rw [← gauss1_algebraMap, _root_.map_sub, ← hP, ← hP, ← _root_.map_sub, ← sub_mul]
    refine (gauss1_trace_le hb _).trans ((gnorm_mul_le _ _).trans ?_)
    exact (mul_le_of_le_one_right' (hdk k)).trans (hdiff n)
  have htail (k : ι) (n i : ℕ) (hi : D < i) : ‖(P n k).coeff i‖₊ ≤ ρ ^ (2 ^ n) := by
    refine (nnnorm_coeff_le_gauss1 (P n k) (Q n k) D hi).trans ?_
    rw [← hP, ← htrE', ← _root_.map_sub, ← sub_mul]
    refine (gauss1_trace_le hb _).trans ((gnorm_mul_le _ _).trans ?_)
    exact (mul_le_of_le_one_right' (hdk k)).trans (hdiff' n)
  haveI : Nonempty (Ext C F) := ⟨w₀⟩
  -- the trace-dual basis
  set Bf := Algebra.traceForm (RatFunc C) F
  have hBf : Bf.Nondegenerate := traceForm_nondegenerate (RatFunc C) F
  set dd := Bf.dualBasis hBf d
  have hexp (v : F) : v = ∑ k, Algebra.trace (RatFunc C) F (v * d k) • dd k := by
    conv_lhs => rw [← dd.sum_repr v]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]
  -- finite families `wv N (m, k) = Xᵐ dd k` and the polynomials of their coordinates
  set wv : (N : ℕ) → Fin N × ι → F := fun N t ↦ (RatFunc.X : RatFunc C) ^ (t.1 : ℕ) • dd t.2
  set pol : (N : ℕ) → (Fin N × ι → C) → ι → C[X] := fun N g k ↦
    ∑ i : Fin N, Polynomial.C (g (i, k)) * X ^ (i : ℕ)
  have hW1 (N : ℕ) (g : Fin N × ι → C) :
      ∑ t, g t • wv N t = ∑ k, algebraMap C[X] (RatFunc C) (pol N g k) • dd k := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp only [pol, map_sum, Finset.sum_smul, wv]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [map_mul, map_pow, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply,
      RatFunc.algebraMap_X, mul_smul, algebraMap_smul]
  have hW2 (N : ℕ) (g : Fin N × ι → C) (k : ι) (j : ℕ) :
      (pol N g k).coeff j = if h : j < N then g (⟨j, h⟩, k) else 0 := by
    simp only [pol, finsetSum_coeff, coeff_C_mul_X_pow]
    split_ifs with h
    · rw [Finset.sum_eq_single (⟨j, h⟩ : Fin N)]
      · simp
      · intro i _ hi
        rw [if_neg]
        intro hj
        exact hi (Fin.ext hj.symm)
      · simp
    · refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [if_neg]
      intro hj
      exact h (hj ▸ i.2)
  have hW3 {v : F} {φ : ι → C[X]}
      (hφ : ∀ k, Algebra.trace (RatFunc C) F (v * d k) = algebraMap C[X] (RatFunc C) (φ k))
      {N : ℕ} (hN : ∀ k, (φ k).natDegree < N) :
      v = ∑ t, (φ t.2).coeff t.1 • wv N t := by
    rw [hW1]
    conv_lhs => rw [hexp v]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hφ k]
    congr 2
    ext j
    simp only [hW2]
    split_ifs with h
    · rfl
    · exact coeff_eq_zero_of_natDegree_lt ((hN k).trans_le (not_lt.1 h))
  have hW4 (N : ℕ) (g : Fin N × ι → C) (j : ι) :
      Algebra.trace (RatFunc C) F ((∑ t, g t • wv N t) * d j) =
        algebraMap C[X] (RatFunc C) (pol N g j) := by
    rw [hW1, ← Algebra.traceForm_apply, ← LinearMap.BilinForm.dualBasis_repr_apply hBf,
      dd.repr_sum_self]
  set M := Finset.univ.sup fun k ↦ gnorm C (dd k)
  have hwM (N : ℕ) (t : Fin N × ι) : gnorm C (wv N t) ≤ M := by
    simp only [wv]
    rw [gnorm_smul, map_pow, gauss1_X, one_pow, one_mul]
    exact Finset.le_sup (f := fun k ↦ gnorm C (dd k)) (Finset.mem_univ t.2)
  -- the coordinates of `1`
  choose T hT using fun k ↦ exists_trace_eq (isIntegral_of_mem_rrSpace (hd k).1)
  set D' := max D (Finset.univ.sup fun k ↦ (T k).natDegree)
  have hTD (k : ι) : (T k).natDegree < D' + 1 :=
    Nat.lt_succ_of_le ((Finset.le_sup (f := fun k ↦ (T k).natDegree)
      (Finset.mem_univ k)).trans (le_max_right _ _))
  set J := Fin (D' + 1) × ι
  set u : J → F := wv (D' + 1)
  set c : J → C := fun β ↦ (T β.2).coeff β.1
  have hone : (1 : F) = ∑ β, c β • u β :=
    hW3 (fun k ↦ by rw [one_mul, hT k]) hTD
  -- the truncated iterates `zz n`
  set a : ℕ → J → C := fun n β ↦ (P n β.2).coeff β.1
  set zz : ℕ → F := fun n ↦ ∑ β, a n β • u β
  have hEz (n : ℕ) : gnorm C (E n - zz n) ≤ ρ ^ (2 ^ n) * M := by
    have h1 : E n = ∑ k, algebraMap C[X] (RatFunc C) (P n k) • dd k := by
      conv_lhs => rw [hexp (E n)]
      simp only [hP]
    rw [h1, show zz n = ∑ β, a n β • wv (D' + 1) β from rfl, hW1, ← Finset.sum_sub_distrib]
    refine (gnorm_sum_le _ _).trans (Finset.sup_le fun k _ ↦ ?_)
    rw [← sub_smul, gnorm_smul, ← _root_.map_sub]
    refine mul_le_mul' (gauss1_algebraMap_le_of_coeff _ fun i ↦ ?_)
      (Finset.le_sup (f := fun k ↦ gnorm C (dd k)) (Finset.mem_univ k))
    rw [coeff_sub, hW2]
    split_ifs with h
    · simp [a]
    · rw [sub_zero]
      exact htail k n i (lt_of_le_of_lt (le_max_left _ _) (not_lt.1 h))
  -- `zz n` is an approximate idempotent
  set K := max M 1
  have hρle (n : ℕ) : ρ ^ (2 ^ n) ≤ 1 := pow_le_one₀ zero_le hρ.le
  have hzzle (n : ℕ) : gnorm C (zz n ^ 2 - zz n) ≤ ρ ^ (2 ^ n) * max (M * K) 1 := by
    have hzn : gnorm C (zz n) ≤ K := by
      have : zz n = -(E n - zz n) + E n := by rw [neg_sub, sub_add_cancel]
      rw [this]
      refine (gnorm_add_le _ _).trans (max_le ?_ ?_)
      · rw [gnorm_neg]
        exact (hEz n).trans ((mul_le_of_le_one_left' (hρle n)).trans (le_max_left _ _))
      · exact (gnorm_le_iff.2 fun w ↦ hE1 w n).trans (le_max_right _ _)
    have hsum : gnorm C (zz n + E n - 1) ≤ K := by
      refine (gnorm_sub_le _ _).trans (max_le ((gnorm_add_le _ _).trans (max_le hzn
        ((gnorm_le_iff.2 fun w ↦ hE1 w n).trans (le_max_right _ _)))) ?_)
      rw [gnorm_one]
      exact le_max_right _ _
    have key (p q : F) : p ^ 2 - p = -(q - p) * (p + q - 1) + (q ^ 2 - q) := by ring
    rw [key (zz n) (E n)]
    refine (gnorm_add_le _ _).trans (max_le ?_ ?_)
    · refine (gnorm_mul_le _ _).trans ?_
      rw [gnorm_neg]
      calc gnorm C (E n - zz n) * gnorm C (zz n + E n - 1) ≤ (ρ ^ (2 ^ n) * M) * K :=
            mul_le_mul' (hEz n) hsum
        _ = ρ ^ (2 ^ n) * (M * K) := by ring
        _ ≤ _ := mul_le_mul_right (le_max_left _ _) _
    · exact (hidem n).trans (le_mul_of_one_le_right zero_le (le_max_right _ _))
  -- a common denominator of the structure constants
  set s : Finset (RatFunc C) :=
    (Finset.univ.image fun t : J × J × ι ↦
      Algebra.trace (RatFunc C) F (u t.1 * u t.2.1 * d t.2.2)) ∪
    (Finset.univ.image fun t : J × ι ↦ Algebra.trace (RatFunc C) F (u t.1 * d t.2))
  obtain ⟨⟨h, hh⟩, hint⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors C[X]) s
  have hh0 : h ≠ 0 := nonZeroDivisors.ne_zero hh
  set Hr := algebraMap C[X] (RatFunc C) h
  have hHr : Hr ≠ 0 := by
    simpa [Hr] using (IsFractionRing.injective C[X] (RatFunc C)).ne hh0
  set Hf := algebraMap (RatFunc C) F Hr
  have hHf : Hf ≠ 0 := by
    simpa [Hf] using (algebraMap (RatFunc C) F).injective.ne hHr
  choose π2 hπ2 using fun t : J × J × ι ↦ RingHom.mem_rangeS.1
    (hint _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))))
  choose π1 hπ1 using fun t : J × ι ↦ RingHom.mem_rangeS.1
    (hint _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ t))))
  set N := (Finset.univ.sup fun t ↦ (π2 t).natDegree) +
    (Finset.univ.sup fun t ↦ (π1 t).natDegree) + 1
  have hN2 (t : J × J × ι) : (π2 t).natDegree < N := by
    have := Finset.le_sup (f := fun t ↦ (π2 t).natDegree) (Finset.mem_univ t)
    omega
  have hN1 (t : J × ι) : (π1 t).natDegree < N := by
    have := Finset.le_sup (f := fun t ↦ (π1 t).natDegree) (Finset.mem_univ t)
    omega
  have htrH (v : F) (j : ι) : Algebra.trace (RatFunc C) F (Hf * v * d j) =
      Hr * Algebra.trace (RatFunc C) F (v * d j) := by
    rw [mul_assoc, ← Algebra.smul_def, map_smul, smul_eq_mul]
  set κ2 : J → J → Fin N × ι → C := fun β γ t ↦ (π2 (β, γ, t.2)).coeff t.1
  set κ1 : J → Fin N × ι → C := fun β t ↦ (π1 (β, t.2)).coeff t.1
  have hy2 (β γ : J) : Hf * (u β * u γ) = ∑ t, κ2 β γ t • wv N t := by
    refine hW3 (fun k ↦ ?_) (fun k ↦ hN2 (β, γ, k))
    rw [htrH, hπ2 (β, γ, k), Algebra.smul_def]
  have hy1 (β : J) : Hf * u β = ∑ t, κ1 β t • wv N t := by
    refine hW3 (fun k ↦ ?_) (fun k ↦ hN1 (β, k))
    rw [htrH, hπ1 (β, k), Algebra.smul_def]
  -- the quadratic coordinate functions
  set gC : ℕ → Fin N × ι → C := fun n t ↦ ∑ β, ∑ γ, a n β * a n γ * κ2 β γ t -
    ∑ β, a n β * κ1 β t
  have hexpC (n : ℕ) : Hf * (zz n ^ 2 - zz n) = ∑ t, gC n t • wv N t := by
    have h := one_tmul_mul_sq_sub (C := C) (a n) u Hf
    rw [sum_sub_sum_tmul_eq (C := C) (R := C) (a n) _ _ (wv N) κ2 κ1 hy2 hy1] at h
    have h' := congrArg (Algebra.TensorProduct.lid C F) h
    simp only [map_mul, _root_.map_sub, map_sum, Algebra.TensorProduct.lid_tmul, one_smul,
      Algebra.algebraMap_self, RingHom.id_apply] at h'
    rw [sq]
    exact h'
  set K1 := gauss1 C Hr * max (M * K) 1
  have hgC (n : ℕ) (t : Fin N × ι) : ‖gC n t‖₊ ≤ K1 * ρ ^ (2 ^ n) := by
    have h1 : gC n t = (pol N (gC n) t.2).coeff t.1 := by
      rw [hW2, dif_pos t.1.2]
    rw [h1]
    refine (nnnorm_coeff_le_gauss1_algebraMap _ _).trans ?_
    rw [← hW4, ← hexpC]
    refine (gauss1_trace_le hb _).trans ((gnorm_mul_le _ _).trans ?_)
    refine (mul_le_of_le_one_right' (hdk t.2)).trans ((gnorm_mul_le _ _).trans ?_)
    rw [gnorm_algebraMap]
    calc gauss1 C Hr * gnorm C (zz n ^ 2 - zz n) ≤ gauss1 C Hr * (ρ ^ (2 ^ n) * max (M * K) 1) :=
          mul_le_mul' le_rfl (hzzle n)
      _ = K1 * ρ ^ (2 ^ n) := by ring
  -- the coefficients are Cauchy, the idempotency defects tend to `0`
  have hcauchy (β : J) : CauchySeq fun n ↦ a n β := by
    refine cauchySeq_of_le_geometric (ρ : ℝ) 1 hρ fun n ↦ ?_
    rw [dist_eq_norm, ← norm_neg, neg_sub, one_mul]
    have h1 := (nnnorm_coeff_le_gauss1_algebraMap (P (n + 1) β.2 - P n β.2) β.1).trans
      ((gauss1_algebraMap _).trans_le (hPc β.2 n))
    have h2 := h1.trans (pow_two_pow_le hρ.le n)
    rw [coeff_sub] at h2
    exact_mod_cast h2
  have hsmall (t : Fin N × ι) : Tendsto (fun n ↦ gC n t) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun n ↦ ?_) (a := fun n ↦ ((K1 * ρ ^ (2 ^ n) : ℝ≥0) : ℝ))
      (by simpa using NNReal.tendsto_coe.2 ((tendsto_pow_two_pow hρ).const_mul K1))
    exact_mod_cast hgC n t
  -- the coordinate functionals of the family `u`
  have hli : LinearIndependent C u := by
    refine Fintype.linearIndependent_iff.2 fun g hg β ↦ ?_
    rw [show ∑ β, g β • u β = ∑ β, g β • wv (D' + 1) β from rfl, hW1] at hg
    have hk := Fintype.linearIndependent_iff.1 dd.linearIndependent _ hg β.2
    have hp : pol (D' + 1) g β.2 = 0 :=
      (IsFractionRing.injective C[X] (RatFunc C)) (by rw [hk, map_zero])
    have := hW2 (D' + 1) g β.2 β.1
    rw [hp, coeff_zero, dif_pos β.1.2] at this
    exact this.symm
  obtain ⟨ε, hε, hlimε⟩ := exists_tendsto_of_approx_idempotent u hli c hone Hf hHf (wv N) κ2 κ1
    hy2 hy1 a hcauchy hsmall
  -- hence `zz n → ε` and `E n → ε`
  have hcoef (β : J) : Tendsto (fun n ↦ ‖a n β - ε * c β‖₊) atTop (𝓝 0) := by
    have h := tendsto_iff_norm_sub_tendsto_zero.1 (hlimε β)
    exact NNReal.tendsto_coe.1 (by simpa using h)
  have hzzε (n : ℕ) : gnorm C (zz n - ε • (1 : F)) ≤
      (Finset.univ.sup fun β ↦ ‖a n β - ε * c β‖₊) * M := by
    rw [hone, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine (gnorm_sum_le _ _).trans (Finset.sup_le fun β _ ↦ ?_)
    rw [smul_smul, ← sub_smul, LatticeReduction.gnorm_smul_C]
    exact mul_le_mul' (Finset.le_sup (f := fun β ↦ ‖a n β - ε * c β‖₊) (Finset.mem_univ β))
      (hwM _ β)
  have hsup : Tendsto (fun n ↦ Finset.univ.sup fun β ↦ ‖a n β - ε * c β‖₊) atTop (𝓝 0) := by
    refine tendsto_nnreal_zero_iff.2 fun δ hδ ↦ ?_
    filter_upwards [(Filter.eventually_all_finset Finset.univ).2 fun β _ ↦
      tendsto_nnreal_zero_iff.1 (hcoef β) δ hδ] with n hn
    exact (Finset.sup_lt_iff hδ).2 hn
  have hconv : Tendsto (fun n ↦ max (ρ ^ (2 ^ n) * M)
      ((Finset.univ.sup fun β ↦ ‖a n β - ε * c β‖₊) * M)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_two_pow hρ).mul_const M).max (hsup.mul_const M)
  obtain ⟨n, hn⟩ := (tendsto_nnreal_zero_iff.1 hconv 1 one_pos).exists
  have hEε : gnorm C (E n - ε • (1 : F)) < 1 := by
    have : E n - ε • (1 : F) = (E n - zz n) + (zz n - ε • (1 : F)) :=
      (sub_add_sub_cancel _ _ _).symm
    rw [this]
    exact ((gnorm_add_le _ _).trans (max_le_max (hEz n) (hzzε n))).trans_lt hn
  have hcase₁ : w₁.1 (e - 1) ≤ ρ ∧ w₁.1 (e' - 1) ≤ ρ := by
    rcases hcase w₁ with h | h
    · exact h
    · exact absurd (h.1.trans_lt hρ) (not_lt.2 hw₁)
  have hcase₀ : w₀.1 e ≤ ρ ∧ w₀.1 e' ≤ ρ := by
    rcases hcase w₀ with h | h
    · exact absurd (h.1.trans_lt hρ) (not_lt.2 hw₀)
    · exact h
  clear_value zz a c u wv pol gC
  rcases hε with hε | hε
  · -- `ε = 0` contradicts `w₁`
    rw [hε] at hEε
    have h1n : w₁.1 (E n) = 1 := by
      have : E n = (E n - 1) + 1 := (sub_add_cancel _ _).symm
      rw [this, Valuation.map_add_eq_of_lt_right, map_one]
      rw [map_one]
      exact ((hA w₁ hcase₁ n).1).trans_lt (hρ1 n)
    have := (le_gnorm w₁ _).trans_lt hEε
    rw [zero_smul, sub_zero, h1n] at this
    exact lt_irrefl _ this
  · -- `ε = 1` contradicts `w₀`
    rw [hε] at hEε
    have h0n : w₀.1 (E n - 1) = 1 := by
      rw [← Valuation.map_neg, neg_sub, sub_eq_add_neg, Valuation.map_add_eq_of_lt_left, map_one]
      rw [Valuation.map_neg, map_one]
      exact ((hB w₀ hcase₀ n).1).trans_lt (hρ1 n)
    have := (le_gnorm w₀ _).trans_lt hEε
    rw [one_smul, h0n] at this
    exact lt_irrefl _ this

end Main

end GaussFibre

end SemistableReduction
