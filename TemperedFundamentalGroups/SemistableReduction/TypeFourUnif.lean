/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourAssembly
import Mathlib.Analysis.Normed.Field.Dense
import TemperedFundamentalGroups.SemistableReduction.CompletionAlgClosed

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

end TypeFour

end SemistableReduction
