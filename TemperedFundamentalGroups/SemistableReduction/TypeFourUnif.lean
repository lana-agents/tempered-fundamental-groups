/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourAssembly
import Mathlib.Analysis.Normed.Field.Dense
import TemperedFundamentalGroups.SemistableReduction.CompletionAlgClosed
import TemperedFundamentalGroups.SemistableReduction.DiscGerm

/-!
# Local uniformization at type-4 points: local degree one

Blueprint §9.12, leaf T4, interface `TypeFour.UnifFor`. Let `ξ` be a type-4 point of `C(x)` (or
a point of `Ĉ ∖ C`), `ν` a disc valuation with `ν = ξ`, and `F' / C(x)` finite separable. The
extensions of `ξ` to `F'` are the `extValuation g` for the irreducible factors `g` of the minimal
polynomial over the completion `\hat{C(x)}` (`LocalGlobal`).

* `coordDense_of_natDegree_eq_one`: if `g` has degree one (local degree one), `C(x)` is dense in
  `(F', extValuation g)`;
* `natDegree_eq_one_of_isAlgClosed`, `isAlgClosed_completion`: for a point of `Ĉ ∖ C` (radii
  tending to `0`) the completion is algebraically closed (`C` is dense in it,
  `IsAlgClosed.of_denseRange`), so every local degree is one.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open DiscCount LocalGlobal DenseCompletion

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {a c : C}

section LocalDegree

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F'] in
lemma aeval_X_eq (P : C[X]) : aeval (algebraMap (RatFunc C) F' RatFunc.X) P =
    algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) P) := by
  rw [aeval_algebraMap_apply, RatFunc.aeval_X_left_eq_algebraMap]

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F'] in
lemma aeval_X_div (φ : RatFunc C) :
    aeval (algebraMap (RatFunc C) F' RatFunc.X) φ.num /
      aeval (algebraMap (RatFunc C) F' RatFunc.X) φ.denom = algebraMap (RatFunc C) F' φ := by
  rw [aeval_X_eq, aeval_X_eq, ← map_div₀, RatFunc.num_div_denom]

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- **Local degree one gives density**: if the factor `g` of an extension of a disc valuation
has degree one, `C(x)` is dense in `(F', extValuation g)`. -/
theorem coordDense_of_natDegree_eq_one (ν : DiscVal a c)
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F')
    (hg : g.1.natDegree = 1) :
    CoordDense C (extValuation g) (algebraMap (RatFunc C) F' RatFunc.X) := by
  intro y ε hε
  set K := UniformSpace.Completion (DiscField ν)
  have hfin : Module.finrank K (Local K g.1) = 1 := by rw [finrank_local, hg]
  have hbot : (⊥ : Subalgebra K (Local K g.1)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one hfin
  obtain ⟨k, hk⟩ : toLocal g y ∈ (⊥ : Subalgebra K (Local K g.1)) := by
    rw [hbot]; exact Algebra.mem_top
  change algebraMap K (Local K g.1) k = toLocal g y at hk
  obtain ⟨φ', hφ'⟩ : ∃ φ' : DiscField ν, ‖k - algebraMap (DiscField ν) K φ'‖ < ε := by
    have hd : DenseRange (algebraMap (DiscField ν) K) := by
      have : (algebraMap (DiscField ν) K : DiscField ν → K) = ((↑) : DiscField ν → K) :=
        _root_.funext (algebraMap_completion (DiscField ν))
      rw [this]; exact UniformSpace.Completion.denseRange_coe
    obtain ⟨z, ⟨φ', rfl⟩, hz⟩ := Metric.mem_closure_iff.1 (hd k) ε (by exact_mod_cast hε)
    exact ⟨φ', by rw [← dist_eq_norm]; exact hz⟩
  set φ : RatFunc C := WithAbs.ofAbs φ'
  refine ⟨φ.num, φ.denom, ?_, ?_⟩
  · rw [aeval_X_eq, map_ne_zero_iff _ (algebraMap (RatFunc C) F').injective]
    exact RatFunc.algebraMap_ne_zero (RatFunc.denom_ne_zero φ)
  · rw [aeval_X_div, extValuation_apply]
    have h1 : algebraMap (RatFunc C) F' φ = algebraMap (DiscField ν) F' φ' := rfl
    rw [h1, map_sub, toLocal_algebraMap, ← hk, ← map_sub]
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    refine lt_of_eq_of_lt (norm_algebraMap' _ _) ?_
    exact hφ'

end LocalDegree

/-! ### Points of `Ĉ ∖ C` -/

section Small

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- If `ν(x - b)` gets arbitrarily small, the constants are dense in `(C(x), ν)`. -/
lemma denseRange_C_of_small (ν : DiscVal a c)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ b : C,
      ν.val (RatFunc.X - algebraMap C (RatFunc C) b) < ε) :
    DenseRange (algebraMap C (DiscField ν)) := by
  set e : RatFunc C ≃+* DiscField ν := (WithAbs.equiv _).symm
  set T := (algebraMap C (DiscField ν)).fieldRange.topologicalClosure
  have hC : ∀ b : C, e (algebraMap C (RatFunc C) b) ∈ T := fun b ↦
    Subfield.le_topologicalClosure _ ⟨b, rfl⟩
  have hX : e RatFunc.X ∈ T := by
    refine Metric.mem_closure_iff.2 fun ε hε ↦ ?_
    obtain ⟨b, hb⟩ := hsmall ⟨ε, hε.le⟩ hε
    refine ⟨algebraMap C (DiscField ν) b, ⟨b, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    change ‖e (RatFunc.X - algebraMap C (RatFunc C) b)‖ < ε
    rw [WithAbs.norm_eq_apply_ofAbs]
    exact_mod_cast hb
  have hpoly : ∀ P : C[X], e (algebraMap C[X] (RatFunc C) P) ∈ T := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ => rw [map_add, map_add]; exact add_mem hP hQ
    | monomial n b =>
      rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, RatFunc.algebraMap_X,
        ratFunc_algebraMap_C, map_mul, map_pow]
      exact mul_mem (hC b) (pow_mem hX n)
  intro y
  have hy : y ∈ T := by
    have h := RatFunc.num_div_denom (e.symm y)
    rw [← e.apply_symm_apply y, ← h, map_div₀]
    exact div_mem (hpoly _) (hpoly _)
  exact hy

variable [CharZero C]

omit [IsUltrametricDist C] in
/-- If `ν(x - b)` gets arbitrarily small, the completion of `(C(x), ν)` is algebraically closed
(a point of `Ĉ ∖ C`: the completion is `Ĉ`). -/
theorem isAlgClosed_completion_of_small (ν : DiscVal a c)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ b : C,
      ν.val (RatFunc.X - algebraMap C (RatFunc C) b) < ε) :
    IsAlgClosed (UniformSpace.Completion (DiscField ν)) := by
  haveI : CharZero (DiscField ν) :=
    charZero_of_injective_algebraMap (algebraMap C (DiscField ν)).injective
  refine IsAlgClosed.of_denseRange (K := C) ?_
  have h1 := denseRange_C_of_small ν hsmall
  have h2 : DenseRange ((↑) : DiscField ν → UniformSpace.Completion (DiscField ν)) :=
    UniformSpace.Completion.denseRange_coe
  have : (algebraMap C (UniformSpace.Completion (DiscField ν)) :
      C → UniformSpace.Completion (DiscField ν)) =
      ((↑) : DiscField ν → UniformSpace.Completion (DiscField ν)) ∘ algebraMap C (DiscField ν) :=
    rfl
  rw [this]
  exact h2.comp h1 (UniformSpace.Completion.continuous_coe _)

end Small

/-! ### Extensions as factors -/

section Factors

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- Every extension of a disc valuation `ν` to `F'` is `extValuation g` for a factor `g`. -/
theorem exists_eq_extValuation' (ν : DiscVal a c) {ξ' : Valuation F' ℝ≥0}
    (h' : ξ'.comap (algebraMap (RatFunc C) F') = ν.val) :
    ∃ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F',
      extValuation g = ξ' := by
  have hext : ξ'.comap (algebraMap (DiscField ν) F') =
      NormedField.valuation (K := DiscField ν) := by
    refine Valuation.ext fun y ↦ ?_
    have := congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v y.ofAbs) h'
    simp only [Valuation.comap_apply] at this
    rw [Valuation.comap_apply, valuation_withAbs]
    exact this
  exact exists_eq_extValuation (K := UniformSpace.Completion (DiscField ν)) ⟨ξ', hext⟩

omit [IsAlgClosed C] in
/-- A disc valuation equal to a given type-4 point. -/
lemma exists_discVal {ξ : Valuation (RatFunc C) ℝ≥0} (hξ : Splitting.IsTypeFour ξ) :
    ∃ (a c : C) (ν : DiscVal a c), ν.val = ξ := by
  obtain ⟨b₁, hb₁⟩ := hξ.no_min 0
  exact ⟨b₁, 0 - b₁, ⟨ξ, Splitting.isDiscVal hξ hb₁⟩, rfl⟩

variable [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [CharZero C]

/-- **Points of `Ĉ ∖ C`**: if `ξ(x - b)` gets arbitrarily small, `C(x)` is dense in every
extension of `ξ` (all local degrees are one). -/
theorem coordDense_of_small {ξ : Valuation (RatFunc C) ℝ≥0} (hξ : Splitting.IsTypeFour ξ)
    (hsmall : ∀ ε : ℝ≥0, 0 < ε → ∃ b : C, ξ (RatFunc.X - algebraMap C (RatFunc C) b) < ε)
    {ξ' : Valuation F' ℝ≥0} (h' : ξ'.comap (algebraMap (RatFunc C) F') = ξ) :
    CoordDense C ξ' (algebraMap (RatFunc C) F' RatFunc.X) := by
  obtain ⟨a, c, ν, rfl⟩ := exists_discVal hξ
  obtain ⟨g, rfl⟩ := exists_eq_extValuation' ν h'
  haveI := isAlgClosed_completion_of_small ν hsmall
  exact coordDense_of_natDegree_eq_one ν g
    (natDegree_eq_of_degree_eq_some (IsAlgClosed.degree_eq_one_of_irreducible _
      (irreducible_of_mem_factors g.2)))

end Factors

/-! ### Valuations over `C` -/

section Equiv

omit [IsUltrametricDist C] in
/-- The norms of `C` are dense in `(0, ∞)`. -/
lemma exists_norm_between {r s : ℝ} (hr : 0 < r) (hrs : r < s) :
    ∃ c : C, r < ‖c‖ ∧ ‖c‖ < s := by
  have hθ : (r / s + 1) / 2 < 1 := by
    have : r / s < 1 := (div_lt_one (hr.trans hrs)).2 hrs
    linarith
  obtain ⟨l, hl0, hθl, hl1⟩ := DiscGerm.exists_norm_mem (C := C) hθ
  have hrsl : r / s < ‖l‖ := by
    have : r / s < 1 := (div_lt_one (hr.trans hrs)).2 hrs
    linarith
  have hlpos : 0 < ‖l‖ := norm_pos_iff.2 hl0
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr hl1
  set u := ‖l‖⁻¹
  have hu1 : 1 < u := one_lt_inv_iff₀.2 ⟨hlpos, hl1⟩
  have hus : r * u < s := by
    rw [← lt_div_iff₀' hr]
    have := (inv_lt_inv₀ hlpos (div_pos hr (hr.trans hrs))).2 hrsl
    rwa [inv_div] at this
  have hc₁ : 0 < ‖l ^ m‖ := norm_pos_iff.2 (pow_ne_zero _ hl0)
  have hx : 1 ≤ r / ‖l ^ m‖ := by
    rw [le_div_iff₀ hc₁, one_mul, norm_pow]; exact hm.le
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near hx hu1
  refine ⟨l ^ m * l⁻¹ ^ (n + 1), ?_, ?_⟩
  · rw [norm_mul, norm_pow (l⁻¹), norm_inv]
    rwa [div_lt_iff₀' hc₁] at hn2
  · rw [norm_mul, norm_pow (l⁻¹), norm_inv]
    change ‖l ^ m‖ * u ^ (n + 1) < s
    rw [pow_succ, ← mul_assoc]
    calc ‖l ^ m‖ * u ^ n * u ≤ r * u := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rwa [le_div_iff₀' hc₁] at hn1
      _ < s := hus

omit [IsUltrametricDist C] in
/-- Two real valuations extending the norm of `C` with the same valuation ring are equal. -/
theorem valuation_eq_of_le_one_iff {L : Type*} [Field L] [Algebra C L]
    {v₁ v₂ : Valuation L ℝ≥0} (h₁ : ∀ b : C, v₁ (algebraMap C L b) = ‖b‖₊)
    (h₂ : ∀ b : C, v₂ (algebraMap C L b) = ‖b‖₊) (h : ∀ y, v₁ y ≤ 1 ↔ v₂ y ≤ 1) :
    v₁ = v₂ := by
  have key : ∀ {w₁ w₂ : Valuation L ℝ≥0}, (∀ b : C, w₁ (algebraMap C L b) = ‖b‖₊) →
      (∀ b : C, w₂ (algebraMap C L b) = ‖b‖₊) → (∀ y, w₁ y ≤ 1 ↔ w₂ y ≤ 1) →
      ∀ y, ¬ w₁ y < w₂ y := by
    intro w₁ w₂ h₁ h₂ h y hlt
    have hy : y ≠ 0 := by rintro rfl; simp at hlt
    by_cases h0 : w₁ y = 0
    · exact hy ((map_eq_zero w₁).1 h0)
    have h0' : (0 : ℝ) < w₁ y := NNReal.coe_pos.2 (pos_iff_ne_zero.2 h0)
    obtain ⟨c, hc1, hc2⟩ := exists_norm_between (C := C) h0' (by exact_mod_cast hlt)
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc1
    have hw₁ : (0 : ℝ≥0) < w₁ y := pos_iff_ne_zero.2 h0
    have hw₂ : (0 : ℝ≥0) < w₂ y := pos_iff_ne_zero.2 (by
      intro h0; exact hy ((map_eq_zero w₂).1 h0))
    have hcpos : (0 : ℝ≥0) < ‖c‖₊ := nnnorm_pos.2 hc0
    have e1 : w₁ (y / algebraMap C L c) ≤ 1 := by
      rw [map_div₀, h₁, div_le_one₀ hcpos]
      exact_mod_cast hc1.le
    have e2 := (h _).1 e1
    rw [map_div₀, h₂, div_le_one₀ hcpos] at e2
    have : (w₂ y : ℝ) ≤ ‖c‖ := by exact_mod_cast e2
    exact absurd this (not_le.2 hc2)
  refine Valuation.ext fun y ↦ le_antisymm ?_ ?_
  · exact not_lt.1 (key h₂ h₁ (fun y ↦ (h y).symm) y)
  · exact not_lt.1 (key h₁ h₂ h y)

end Equiv

/-! ### Weak approximation -/

section Approx

variable {F K F' : Type*} [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [Fact (DenseRange (algebraMap F K))]

omit [IsUltrametricDist F] in
/-- **Weak approximation** for the extensions of a valuation: `y` at one extension and `0` at
all others (the idempotent iteration `N` applied to an approximate idempotent). -/
theorem exists_approx (g₀ : Factor F K F') (y : F') {ε : ℝ} (hε : 0 < ε) :
    ∃ z : F', ‖toLocal g₀ (z - y)‖ < ε ∧ ∀ g : Factor F K F', g ≠ g₀ → ‖toLocal g z‖ < ε := by
  classical
  obtain ⟨e, he1, heo⟩ := exists_approx_idempotent (F := F) (K := K) (F' := F') g₀
  have hle : ∀ g : Factor F K F', ‖toLocal g e‖ ≤ 1 := by
    intro g
    by_cases h : g = g₀
    · subst h
      exact ((norm_eq_of_norm_sub_lt (by rwa [norm_one])).trans norm_one).le
    · exact (heo g h).le
  set q : Factor F K F' → ℝ := fun g ↦ if g = g₀ then ‖1 - toLocal g e‖ else ‖toLocal g e‖
  have hq0 : ∀ g, 0 ≤ q g := fun g ↦ by simp only [q]; split_ifs <;> positivity
  have hq1 : ∀ g, q g < 1 := fun g ↦ by
    simp only [q]
    split_ifs with h
    · subst h; rwa [norm_sub_rev]
    · exact heo g h
  have hlim : ∀ g : Factor F K F', ∀ᶠ n in Filter.atTop,
      q g ^ (2 ^ n) * ‖toLocal g y‖ < ε := by
    intro g
    have := (DiscGerm.tendsto_pow_two_pow (hq0 g) (hq1 g)).mul_const ‖toLocal g y‖
    rw [zero_mul] at this
    exact this.eventually (gt_mem_nhds hε)
  obtain ⟨n, hn⟩ := (Filter.eventually_all.2 hlim).exists
  set u : F' := (fun v : F' ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] e
  have hmap : ∀ g : Factor F K F', toLocal g u = Idem.N^[n] (toLocal g e) :=
    fun g ↦ Idem.map_N_iterate (toLocal g).toRingHom e n
  refine ⟨u * y, ?_, fun g hg ↦ ?_⟩
  · have h := hn g₀
    simp only [q, if_pos rfl] at h
    rw [show u * y - y = -((1 - u) * y) by ring, map_neg, norm_neg,
      map_mul, map_sub, map_one, hmap, norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (Idem.norm_one_sub_N_iterate_le (hle g₀) n) (norm_nonneg _)) h
  · have h := hn g
    simp only [q, if_neg hg] at h
    rw [map_mul, hmap, norm_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right
      (Idem.norm_N_iterate_le (hle g) n) (norm_nonneg _)) h

end Approx

/-! ### The decomposition field -/

section Decomposition

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [IsGalois (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] [CharZero C]

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
/-- **`C(x)` is dense in the decomposition field.** If `y ∈ F` is fixed by every automorphism
preserving `ξ'`, it is approximated by rational functions at `ξ'`: a weak approximation `z` of
`y` (`exists_approx`) has trace `Σ_σ σ z ≈ |D| y`. -/
theorem exists_ratFunc_approx_of_fixed (ν : DiscVal a c) {ξ' : Valuation F ℝ≥0}
    (h' : ξ'.comap (algebraMap (RatFunc C) F) = ν.val) {y : F}
    (hy : ∀ σ : F ≃ₐ[RatFunc C] F, (∀ z, ξ' (σ z) = ξ' z) → σ y = y) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ φ : RatFunc C, ξ' (y - algebraMap (RatFunc C) F φ) < ε := by
  classical
  obtain ⟨g₀, hg₀⟩ := exists_eq_extValuation' ν h'
  -- the conjugate valuations
  have hconj : ∀ σ : F ≃ₐ[RatFunc C] F, ∃ g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F, ∀ z, extValuation g z = ξ' (σ z) := by
    intro σ
    have hc : (ξ'.comap σ.toRingEquiv.toRingHom).comap (algebraMap (RatFunc C) F) = ν.val := by
      rw [← h']
      refine Valuation.ext fun φ ↦ ?_
      simp only [Valuation.comap_apply]
      change ξ' (σ (algebraMap (RatFunc C) F φ)) = _
      rw [AlgEquiv.commutes]
    obtain ⟨g, hg⟩ := exists_eq_extValuation' ν hc
    exact ⟨g, fun z ↦ by rw [hg]; rfl⟩
  choose gσ hgσ using hconj
  set D := Finset.univ.filter (fun σ : F ≃ₐ[RatFunc C] F ↦ ∀ z, ξ' (σ z) = ξ' z)
  have hD1 : (1 : F ≃ₐ[RatFunc C] F) ∈ D := Finset.mem_filter.2 ⟨Finset.mem_univ _, fun z ↦ rfl⟩
  set nD := D.card
  have hnD : (nD : C) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨1, hD1⟩)
  have hδ : (0 : ℝ) < ‖(nD : C)‖ := norm_pos_iff.2 hnD
  have hnDF : ξ' (nD : F) = ‖(nD : C)‖₊ := by
    rw [← map_natCast (algebraMap (RatFunc C) F), ← Valuation.comap_apply, h',
      ← map_natCast (algebraMap C (RatFunc C))]
    exact ν.isDiscVal.map_C _
  obtain ⟨z, hz, hzo⟩ := exists_approx (K := UniformSpace.Completion (DiscField ν)) g₀ y
    (ε := ε * ‖(nD : C)‖) (mul_pos (by exact_mod_cast hε) hδ)
  have hval : ∀ w : F, ‖toLocal g₀ w‖ = (ξ' w : ℝ) := fun w ↦ by
    rw [← hg₀, extValuation_apply, coe_nnnorm]
  set D' := Finset.univ.filter (fun σ : F ≃ₐ[RatFunc C] F ↦ ¬ ∀ z, ξ' (σ z) = ξ' z)
  set S := ∑ σ ∈ D, σ (z - y) + ∑ σ ∈ D', σ z
  refine ⟨Algebra.trace (RatFunc C) F z / (nD : RatFunc C), ?_⟩
  have hnF : (nD : F) ≠ 0 := by
    rw [← map_natCast (algebraMap C F)]
    exact (map_ne_zero_iff _ (algebraMap C F).injective).2 hnD
  have hsum : ∑ σ : F ≃ₐ[RatFunc C] F, σ z = (nD : F) * y + S := by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun σ : F ≃ₐ[RatFunc C] F ↦ ∀ z, ξ' (σ z) = ξ' z)]
    have : ∑ σ ∈ D, σ z = ∑ σ ∈ D, (y + σ (z - y)) := Finset.sum_congr rfl fun σ hσ ↦ by
      rw [map_sub, hy σ (Finset.mem_filter.1 hσ).2]; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
    simp only [S, D, D', nD]
    ring
  have hφ : y - algebraMap (RatFunc C) F (Algebra.trace (RatFunc C) F z / (nD : RatFunc C)) =
      -(S / (nD : F)) := by
    rw [map_div₀, _root_.trace_eq_sum_automorphisms, map_natCast, hsum]
    field_simp
    ring
  have hεδ : (0 : ℝ≥0) < ε * ‖(nD : C)‖₊ := mul_pos hε (nnnorm_pos.2 hnD)
  have hS : ξ' S < ε * ‖(nD : C)‖₊ := by
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · refine Valuation.map_sum_lt _ hεδ.ne' fun σ hσ ↦ ?_
      have := hy σ (Finset.mem_filter.1 hσ).2
      rw [(Finset.mem_filter.1 hσ).2, ← NNReal.coe_lt_coe, ← hval]
      push_cast
      exact hz
    · refine Valuation.map_sum_lt _ hεδ.ne' fun σ hσ ↦ ?_
      have hne : gσ σ ≠ g₀ := by
        intro h
        refine (Finset.mem_filter.1 hσ).2 fun w ↦ ?_
        rw [← hgσ σ w, h, hg₀]
      rw [← hgσ σ z, extValuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm]
      push_cast
      exact hzo _ hne
  rw [hφ, Valuation.map_neg, map_div₀, hnDF, div_lt_iff₀ (nnnorm_pos.2 hnD)]
  exact hS

end Decomposition

/-! ### Values at type-4 points -/

section Values

omit [IsAlgClosed C] in
/-- Products of close factors are close. -/
lemma valuation_prod_sub_lt {R ι : Type*} [Field R] (v : Valuation R ℝ≥0) (s : Multiset ι)
    (u w : ι → R) (h : ∀ i ∈ s, v (u i - w i) < v (w i)) :
    v ((s.map u).prod - (s.map w).prod) < (s.map fun i ↦ v (w i)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha := h a (Multiset.mem_cons_self a s)
    have ih' := ih fun i hi ↦ h i (Multiset.mem_cons_of_mem hi)
    have hu : ∀ i ∈ s, v (u i) = v (w i) := fun i hi ↦
      Valuation.map_eq_of_sub_lt v (h i (Multiset.mem_cons_of_mem hi))
    have hprod : v (s.map u).prod = (s.map fun i ↦ v (w i)).prod := by
      rw [← Multiset.prod_hom (f := v), Multiset.map_map]
      congr 1
      exact Multiset.map_congr rfl hu
    have hpos : 0 < (s.map fun i ↦ v (w i)).prod := by
      refine Multiset.prod_pos fun x hx ↦ ?_
      obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.1 hx
      exact zero_le.trans_lt (h i (Multiset.mem_cons_of_mem hi))
    have hwa : 0 < v (w a) := zero_le.trans_lt ha
    simp only [Multiset.map_cons, Multiset.prod_cons]
    rw [show u a * (s.map u).prod - w a * (s.map w).prod =
      (u a - w a) * (s.map u).prod + w a * ((s.map u).prod - (s.map w).prod) by ring]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul, hprod]
      exact mul_lt_mul_of_pos_right ha hpos
    · rw [map_mul]
      exact mul_lt_mul_of_pos_left ih' hwa

variable {ξ : Valuation (RatFunc C) ℝ≥0}

/-- A polynomial is close to its value at a point deeper than all its roots. -/
lemma valuation_sub_eval_lt (hξ : Splitting.IsTypeFour ξ) {R : C[X]} (hR : R ≠ 0) {β : C}
    (hβ : ∀ α ∈ R.roots, GaussLimit.radius ξ β < GaussLimit.radius ξ α) :
    ξ (algebraMap C[X] (RatFunc C) R - algebraMap C (RatFunc C) (R.eval β)) <
      ξ (algebraMap C[X] (RatFunc C) R) := by
  have hsplit := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (k := C) (p := R))
  set u : C → RatFunc C := fun α ↦ algebraMap C[X] (RatFunc C) (X - Polynomial.C α)
  set w : C → RatFunc C := fun α ↦ algebraMap C (RatFunc C) (β - α)
  have hRx : algebraMap C[X] (RatFunc C) R =
      algebraMap C (RatFunc C) R.leadingCoeff * (R.roots.map u).prod := by
    conv_lhs => rw [← hsplit]
    rw [map_mul, ratFunc_algebraMap_C, map_multiset_prod, Multiset.map_map]
    rfl
  have hRβ : algebraMap C (RatFunc C) (R.eval β) =
      algebraMap C (RatFunc C) R.leadingCoeff * (R.roots.map w).prod := by
    conv_lhs => rw [← hsplit]
    rw [eval_mul, eval_C, eval_multiset_prod, map_mul, map_multiset_prod, Multiset.map_map,
      Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun α _ ↦ ?_
    simp [w]
  have hlc : ξ (algebraMap C (RatFunc C) R.leadingCoeff) ≠ 0 := by
    rw [hξ.map_C, NormedField.valuation_apply]
    exact nnnorm_ne_zero_iff.2 (leadingCoeff_ne_zero.2 hR)
  have hclose : ∀ α ∈ R.roots, ξ (u α - w α) < ξ (w α) := by
    intro α hα
    have hr := Splitting.radius_eq_nnnorm hξ (hβ α hα)
    have e : u α - w α = algebraMap C[X] (RatFunc C) (X - Polynomial.C β) := by
      simp only [u, w, map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
      ring
    rw [e, hξ.map_C, NormedField.valuation_apply, ← hr]
    exact hβ α hα
  have hprod := valuation_prod_sub_lt ξ R.roots u w hclose
  have hprod' : ξ (R.roots.map u).prod = (R.roots.map fun i ↦ ξ (w i)).prod := by
    rw [← Multiset.prod_hom (f := ξ), Multiset.map_map]
    congr 1
    exact Multiset.map_congr rfl fun α hα ↦ Valuation.map_eq_of_sub_lt ξ (hclose α hα)
  rw [hRx, hRβ, ← mul_sub, map_mul, map_mul, hprod']
  exact mul_lt_mul_of_pos_left hprod (zero_le.lt_of_ne (Ne.symm hlc))

omit [IsAlgClosed C] in
/-- For finitely many points there is a point deeper than all of them. -/
lemma exists_deeper (hξ : Splitting.IsTypeFour ξ) (s : Finset C) :
    ∃ β : C, ∀ α ∈ s, GaussLimit.radius ξ β < GaussLimit.radius ξ α := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨0, fun α hα ↦ absurd hα (Finset.notMem_empty α)⟩
  obtain ⟨α₀, hα₀, hmin⟩ := s.exists_min_image (GaussLimit.radius ξ) hs
  obtain ⟨β, hβ⟩ := hξ.no_min α₀
  exact ⟨β, fun α hα ↦ hβ.trans_le (hmin α hα)⟩

/-- **The residue field and the values of a type-4 point are those of `C`**: every nonzero
rational function is close to a constant. -/
theorem exists_const_sub_lt (hξ : Splitting.IsTypeFour ξ) {φ : RatFunc C} (hφ : φ ≠ 0) :
    ∃ b : C, ξ (φ - algebraMap C (RatFunc C) b) < ξ φ := by
  classical
  have hnum : φ.num ≠ 0 := RatFunc.num_ne_zero hφ
  have hden : φ.denom ≠ 0 := RatFunc.denom_ne_zero φ
  obtain ⟨β, hβ⟩ := exists_deeper hξ (φ.num.roots + φ.denom.roots).toFinset
  have h1 := valuation_sub_eval_lt hξ hnum (β := β) fun α hα ↦ hβ α
    (Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inl hα)))
  have h2 := valuation_sub_eval_lt hξ hden (β := β) fun α hα ↦ hβ α
    (Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inr hα)))
  set P := algebraMap C[X] (RatFunc C) φ.num
  set Q := algebraMap C[X] (RatFunc C) φ.denom
  set p := algebraMap C (RatFunc C) (φ.num.eval β)
  set q := algebraMap C (RatFunc C) (φ.denom.eval β)
  have hP0 : P ≠ 0 := by simpa [P] using hnum
  have hQ0 : Q ≠ 0 := by simpa [Q] using hden
  have hpP : ξ p = ξ P := Valuation.map_eq_of_sub_lt ξ (by rwa [← Valuation.map_neg, neg_sub])
  have hqQ : ξ q = ξ Q := Valuation.map_eq_of_sub_lt ξ (by rwa [← Valuation.map_neg, neg_sub])
  have hξP : 0 < ξ P := zero_le.lt_of_ne (Ne.symm ((map_ne_zero ξ).2 hP0))
  have hξQ : 0 < ξ Q := zero_le.lt_of_ne (Ne.symm ((map_ne_zero ξ).2 hQ0))
  have hq0 : q ≠ 0 := by
    intro h; rw [h, map_zero] at hqQ; exact hξQ.ne hqQ
  refine ⟨φ.num.eval β / φ.denom.eval β, ?_⟩
  have hφ : φ = P / Q := (RatFunc.num_div_denom φ).symm
  have hb : algebraMap C (RatFunc C) (φ.num.eval β / φ.denom.eval β) = p / q := map_div₀ _ _ _
  rw [hb, hφ, div_sub_div _ _ hQ0 hq0, map_div₀, map_div₀, map_mul, hqQ,
    show ξ P / ξ Q = ξ P * ξ Q / (ξ Q * ξ Q) by field_simp,
    div_lt_div_iff_of_pos_right (mul_pos hξQ hξQ)]
  rw [show P * q - Q * p = (P - p) * q + p * (q - Q) by ring]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
  · rw [map_mul, hqQ]
    exact mul_lt_mul_of_pos_right h1 hξQ
  · rw [map_mul, hpP]
    refine mul_lt_mul_of_pos_left ?_ hξP
    rwa [← Valuation.map_neg, neg_sub]

end Values

end TypeFour

end SemistableReduction
