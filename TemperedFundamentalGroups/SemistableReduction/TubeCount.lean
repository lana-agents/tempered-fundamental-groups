/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NormFormula

/-!
# Counting extensions near a residue class: constancy of tube degrees

Blueprint §9.9, W7 layer S5. In the setting of `SemistableReduction.LocalGlobal` (`F` a
non-archimedean normed field, `K ⊇ F` complete with `F` dense, `F' / F` finite separable,
factors `g` of the minimal polynomial of a primitive element over `K`, `toLocal g : F' → K[X]/(g)`),
let `y ∈ F'` with `‖toLocal g y‖ ≤ 1` for all `g`. The **tube count**
`Σ_{g : ‖toLocal g y‖ < 1} deg g` (the number of conjugates of `y`, i.e. the sum of the local
degrees of the extensions `w'` of the norm with `w'(y) < 1`) is computed algebraically:

* `normPoly F y = minpoly_F(y) ^ [F' : F(y)]` (the characteristic polynomial), with
  `norm_sub_algebraMap`: `N_{F'/F}(y - t) = (-1)^[F':F] · normPoly F y (t)`;
* `normPoly_map_eq_prod` (`F` infinite): `normPoly F y = ∏_g normPoly K (toLocal g y)` over `K`
  (both sides agree at every `t ∈ F` by the norm formula `algebraMap_norm_eq_prod`);
* `IsResOrder P i`: `P` has coefficients in the unit ball and its reduction has trailing
  degree `i` (Gauss lemma: additive under products, `IsResOrder.mul`);
* `isResOrder_minpoly`, `isResOrder_normPoly`: `normPoly K z` has residue order `deg g` if `‖z‖ < 1`, and `0` if
  `‖z‖ = 1` (the spectral norm is the spectral value of the minimal polynomial);
* **`sum_natDegree_eq_natTrailingDegree`**: if `ι : A → F` is a ring map,
  `𝔭 = {a ∈ A : ‖ι a‖ < 1}`, and `P ∈ A[X]` maps to `normPoly F y`, then
  `Σ_{g : ‖toLocal g y‖ < 1} deg g = natTrailingDegree (P mod 𝔭)`.

The right side does not depend on the norm. Applied to the node ring `A = O_C[x, c/x]` and the
Gauss points `w_{0,s}`, `|c| < s < 1` (all centred at the node, `𝔭` its maximal ideal), and to
`y = e − 1` for an element `e` of the integral closure separating the points over the node, this
is the **constancy of the tube degree** along the open segment (S5): it needs no finiteness of
the integral closure over `O_C` and no completion of the node ring.
-/

open Polynomial NNReal IntermediateField

namespace SemistableReduction

namespace TubeCount

section NormPoly

variable (F : Type*) {L : Type*} [Field F] [Field L] [Algebra F L]

/-- The characteristic polynomial `minpoly_F(y) ^ [L : F(y)]` of `y ∈ L` over `F`. -/
noncomputable def normPoly (y : L) : F[X] := minpoly F y ^ Module.finrank F⟮y⟯ L

variable {F}

lemma monic_normPoly [FiniteDimensional F L] (y : L) : (normPoly F y).Monic :=
  (minpoly.monic (Algebra.IsIntegral.isIntegral y)).pow _

lemma finrank_mul_natDegree [FiniteDimensional F L] (y : L) :
    Module.finrank F⟮y⟯ L * (minpoly F y).natDegree = Module.finrank F L := by
  rw [← IntermediateField.adjoin.finrank (Algebra.IsIntegral.isIntegral y), mul_comm,
    Module.finrank_mul_finrank]

/-- `N_{L/F}(y - t) = (-1)^[L:F] · normPoly F y (t)`. -/
theorem norm_sub_algebraMap [FiniteDimensional F L] (y : L) (t : F) :
    Algebra.norm F (y - algebraMap F L t) =
      (-1) ^ Module.finrank F L * (normPoly F y).eval t := by
  set x := y - algebraMap F L t
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly F x = (minpoly F y).comp (X + C t) := minpoly.sub_algebraMap y t
  have hdeg : (minpoly F x).natDegree = (minpoly F y).natDegree := by
    rw [hmin, natDegree_comp, natDegree_X_add_C, mul_one]
  have hpos : 0 < (minpoly F y).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral y)
  have hfin : Module.finrank F⟮x⟯ L = Module.finrank F⟮y⟯ L := by
    have h1 := finrank_mul_natDegree (F := F) x
    have h2 := finrank_mul_natDegree (F := F) y
    rw [hdeg] at h1
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)
  have hcoeff : (minpoly F x).coeff 0 = (minpoly F y).eval t := by
    rw [hmin, coeff_zero_eq_eval_zero, eval_comp]
    simp
  rw [Algebra.norm_eq_norm_adjoin F x, ← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, ← PowerBasis.natDegree_minpoly,
    IntermediateField.adjoin.powerBasis_gen hx, IntermediateField.minpoly_gen, hcoeff, hdeg,
    hfin, normPoly, eval_pow, mul_pow, ← pow_mul, ← finrank_mul_natDegree (F := F) y,
    mul_comm (Module.finrank F⟮y⟯ L)]

end NormPoly

section ResOrder

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/-- `P` has coefficients in the closed unit ball and its reduction has trailing degree `i`:
`‖Pᵢ‖ = 1` and `‖Pⱼ‖ < 1` for `j < i`. -/
def IsResOrder (P : K[X]) (i : ℕ) : Prop :=
  (∀ j, ‖P.coeff j‖ ≤ 1) ∧ ‖P.coeff i‖ = 1 ∧ ∀ j < i, ‖P.coeff j‖ < 1

lemma norm_sum_lt_one {ι : Type*} (s : Finset ι) (f : ι → K) (h : ∀ x ∈ s, ‖f x‖ < 1) :
    ‖∑ x ∈ s, f x‖ < 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
  exact hle.trans_lt (h i hi)

omit [IsUltrametricDist K] in
lemma isResOrder_one : IsResOrder (1 : K[X]) 0 := by
  refine ⟨fun j ↦ ?_, by simp, fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
  rw [coeff_one]
  split_ifs <;> simp

lemma IsResOrder.mul {P Q : K[X]} {i j : ℕ} (hP : IsResOrder P i) (hQ : IsResOrder Q j) :
    IsResOrder (P * Q) (i + j) := by
  obtain ⟨hP1, hPi, hPlt⟩ := hP
  obtain ⟨hQ1, hQj, hQlt⟩ := hQ
  have hterm : ∀ a b, ‖P.coeff a * Q.coeff b‖ ≤ 1 := fun a b ↦ by
    rw [norm_mul]
    exact mul_le_one₀ (hP1 a) (norm_nonneg _) (hQ1 b)
  have hlt : ∀ a b, (a < i ∨ b < j) → ‖P.coeff a * Q.coeff b‖ < 1 := by
    rintro a b (h | h) <;> rw [norm_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) (hPlt a h) (hQ1 b)
    · exact mul_lt_one_of_nonneg_of_lt_one_right (hP1 a) (norm_nonneg _) (hQlt b h)
  refine ⟨fun n ↦ ?_, ?_, fun n hn ↦ ?_⟩
  · rw [coeff_mul]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun x _ ↦ hterm _ _
  · have hmem : (i, j) ∈ Finset.HasAntidiagonal.antidiagonal (i + j) :=
      Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i + j)).erase (i, j),
        P.coeff x.1 * Q.coeff x.2‖ < 1 := by
      refine norm_sum_lt_one _ _ fun x hx ↦ hlt _ _ ?_
      obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
      by_contra! H
      exact hne (Prod.ext (by omega) (by omega))
    have hmain : ‖P.coeff i * Q.coeff j‖ = 1 := by rw [norm_mul, hPi, hQj, one_mul]
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hmain]; exact hrest.ne'),
      hmain, max_eq_left hrest.le]
  · rw [coeff_mul]
    refine norm_sum_lt_one _ _ fun x hx ↦ hlt _ _ ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_contra! H
    omega

lemma IsResOrder.pow {P : K[X]} {i : ℕ} (hP : IsResOrder P i) (m : ℕ) :
    IsResOrder (P ^ m) (m * i) := by
  induction m with
  | zero => simpa using isResOrder_one
  | succ m ih => simpa [pow_succ, add_mul] using ih.mul hP

lemma IsResOrder.prod {ι : Type*} (s : Finset ι) (P : ι → K[X]) (i : ι → ℕ)
    (h : ∀ x ∈ s, IsResOrder (P x) (i x)) : IsResOrder (∏ x ∈ s, P x) (∑ x ∈ s, i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isResOrder_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul
      (ih fun x hx ↦ h x (Finset.mem_insert_of_mem hx))

end ResOrder

open LocalGlobal

section Local

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (g : K[X]) [Fact (Irreducible g)]

/-- The minimal polynomial of `z` with `‖z‖ ≤ 1` (spectral norm) has residue order `deg` if
`‖z‖ < 1` and `0` if `‖z‖ = 1`. -/
theorem isResOrder_minpoly (z : Local K g) (hz : ‖z‖ ≤ 1) :
    IsResOrder (minpoly K z) (if ‖z‖ < 1 then (minpoly K z).natDegree else 0) := by
  have hint : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hmon := minpoly.monic hint
  set d := (minpoly K z).natDegree
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  have hspec : ‖z‖ = spectralValue (minpoly K z) := rfl
  have hterm : ∀ i < d, ‖(minpoly K z).coeff i‖ ^ (1 / (d - i : ℝ)) ≤ ‖z‖ := fun i hi ↦ by
    rw [hspec, ← spectralValueTerms_of_lt_natDegree _ hi]
    exact le_ciSup (spectralValueTerms_bddAbove _) i
  have hexp : ∀ i < d, (0 : ℝ) < 1 / (d - i : ℝ) := fun i hi ↦ by
    have : (i : ℝ) < d := by exact_mod_cast hi
    positivity
  have hle : ∀ i, ‖(minpoly K z).coeff i‖ ≤ 1 := by
    intro i
    rcases lt_trichotomy i d with hi | rfl | hi
    · by_contra! H
      exact absurd ((Real.one_lt_rpow H (hexp i hi)).trans_le ((hterm i hi).trans hz))
        (lt_irrefl 1)
    · rw [hmon.coeff_natDegree, norm_one]
    · rw [coeff_eq_zero_of_natDegree_lt hi, norm_zero]
      exact zero_le_one
  split_ifs with hlt
  · refine ⟨hle, by rw [hmon.coeff_natDegree, norm_one], fun i hi ↦ ?_⟩
    by_contra! H
    exact absurd ((Real.one_le_rpow H (hexp i hi).le).trans (hterm i hi)) (not_le.2 hlt)
  · have h1 : ‖z‖ = 1 := le_antisymm hz (not_lt.1 hlt)
    refine ⟨hle, ?_, fun j hj ↦ absurd hj (Nat.not_lt_zero j)⟩
    have h0 := spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow (K := K) (L := Local K g) (x := z)
    rw [← norm_local, h1] at h0
    have hc := norm_nonneg ((minpoly K z).coeff 0)
    have := congrArg (· ^ (d : ℝ)) h0
    simp only [Real.one_rpow] at this
    rw [← Real.rpow_mul hc, one_div, inv_mul_cancel₀ (by exact_mod_cast hd0.ne'),
      Real.rpow_one] at this
    exact this.symm

/-- The characteristic polynomial of `z ∈ K[X]/(g)` with `‖z‖ ≤ 1` has residue order `deg g` if
`‖z‖ < 1` and `0` otherwise. -/
theorem isResOrder_normPoly (z : Local K g) (hz : ‖z‖ ≤ 1) :
    IsResOrder (normPoly K z) (if ‖z‖ < 1 then g.natDegree else 0) := by
  have h := (isResOrder_minpoly g z hz).pow (Module.finrank K⟮z⟯ (Local K g))
  have hdeg : Module.finrank K⟮z⟯ (Local K g) * (minpoly K z).natDegree = g.natDegree := by
    rw [finrank_mul_natDegree, finrank_local]
  split_ifs at h ⊢ with hlt
  · rwa [hdeg] at h
  · simpa [normPoly] using h

end Local

section Global

variable {F K F' : Type*} [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
/-- **The characteristic polynomial is the product of the local ones**:
`normPoly F y = ∏_g normPoly K (toLocal g y)` over `K` (for `F` infinite). -/
theorem normPoly_map_eq_prod [Infinite F] (y : F') :
    (normPoly F y).map (algebraMap F K) = ∏ g : Factor F K F', normPoly K (toLocal g y) := by
  classical
  refine eq_of_infinite_eval_eq _ _ ((Set.infinite_range_of_injective
    (algebraMap F K).injective).mono ?_)
  rintro _ ⟨t, rfl⟩
  simp only [Set.mem_setOf_eq, eval_prod]
  have hglob := algebraMap_norm_eq_prod (F := F) (K := K) (y - algebraMap F F' t)
  rw [norm_sub_algebraMap, map_mul, map_pow, map_neg, map_one] at hglob
  have hloc : ∀ g : Factor F K F', Algebra.norm K (toLocal g (y - algebraMap F F' t)) =
      (-1) ^ g.1.natDegree * (normPoly K (toLocal g y)).eval (algebraMap F K t) := by
    intro g
    rw [map_sub, toLocal_algebraMap, norm_sub_algebraMap, finrank_local]
  simp_rw [hloc, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum] at hglob
  have hsum : ∑ g : Factor F K F', g.1.natDegree = Module.finrank F F' := by
    rw [← sum_natDegree_factors (F := F) (K := K) (F' := F')]
    exact Finset.sum_coe_sort (factors F K F') natDegree
  rw [hsum] at hglob
  rw [eval_map_algebraMap, aeval_algebraMap_apply, aeval_def, Algebra.algebraMap_self, eval₂_id]
  have hu : ((-1 : K) ^ Module.finrank F F') ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu hglob

omit [IsUltrametricDist F] in
/-- **The tube count.** Let `ι : A → F` be a ring map (e.g. the inclusion of a subring),
`𝔭 = {a ∈ A : ‖ι a‖ < 1}`, and `P ∈ A[X]` a lift of the characteristic polynomial of `y ∈ F'`,
where `‖toLocal g y‖ ≤ 1` for all `g`. Then the sum of the local degrees of the extensions `w'`
with `w'(y) < 1` is the trailing degree of `P mod 𝔭`. -/
theorem sum_natDegree_eq_natTrailingDegree [Infinite F] {A : Type*} [CommRing A] (ι : A →+* F)
    (𝔭 : Ideal A) (h𝔭 : ∀ a : A, a ∈ 𝔭 ↔ ‖ι a‖ < 1) (P : A[X])
    (hP : P.map ι = normPoly F y) (hy : ∀ g : Factor F K F', ‖toLocal g y‖ ≤ 1) :
    ∑ g ∈ Finset.univ.filter (fun g : Factor F K F' ↦ ‖toLocal g y‖ < 1), g.1.natDegree =
      (P.map (Ideal.Quotient.mk 𝔭)).natTrailingDegree := by
  classical
  set N := ∑ g ∈ Finset.univ.filter (fun g : Factor F K F' ↦ ‖toLocal g y‖ < 1), g.1.natDegree
  have hres : IsResOrder ((normPoly F y).map (algebraMap F K)) N := by
    rw [normPoly_map_eq_prod, show N = _ from Finset.sum_filter _ _]
    exact IsResOrder.prod _ _ _ fun g _ ↦ isResOrder_normPoly g.1 _ (hy g)
  have hcoeff : ∀ j, ‖((normPoly F y).map (algebraMap F K)).coeff j‖ = ‖ι (P.coeff j)‖ := by
    intro j
    rw [coeff_map, ← hP, coeff_map, norm_algebraMap']
  have hzero : ∀ j, (P.map (Ideal.Quotient.mk 𝔭)).coeff j = 0 ↔
      ‖((normPoly F y).map (algebraMap F K)).coeff j‖ < 1 := by
    intro j
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem, h𝔭, hcoeff]
  obtain ⟨-, hN, hlt⟩ := hres
  have hne : (P.map (Ideal.Quotient.mk 𝔭)).coeff N ≠ 0 := by
    rw [Ne, hzero, hN]
    exact lt_irrefl 1
  refine le_antisymm ?_ (natTrailingDegree_le_of_ne_zero hne)
  by_contra! H
  have hp0 : P.map (Ideal.Quotient.mk 𝔭) ≠ 0 := fun h ↦ hne (by rw [h, coeff_zero])
  exact trailingCoeff_nonzero_iff_nonzero.2 hp0 ((hzero _).2 (hlt _ H))

end Global

end TubeCount

end SemistableReduction
