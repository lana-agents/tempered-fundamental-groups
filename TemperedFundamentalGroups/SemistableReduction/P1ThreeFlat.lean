/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeGlue
import TemperedFundamentalGroups.SemistableReduction.TateFibre
import TemperedFundamentalGroups.SemistableReduction.PowFlatTate

/-!
# Flat algebraization of the lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` (MR13 A1)

For `O` a domain with `ϖ ≠ 0`, `(ϖ)` maximal and `O` `ϖ`-adically complete, the coherent chart
algebra `N` on `ℙ¹_O` of `P1Three.exists_algebraization` (the lift of the covering given by
`Sp`, `S0`, `ω`) can be chosen **flat over both charts `O[X]`**
(**`P1Three.exists_flat_algebraization`**), with no further hypotheses: the inputs of
`NodeEtaleGlue.Overlap.exists_flat_algebraization` are

* `hpure0`, `hpure1` (`P1Three.system_hpure0`, `system_hpure1`): the levels of the covering are
  flat over `O/ϖⁿ` (`PowFlat.system_pure0/1`; the levels `R/ϖⁿ⁺¹` of the charts free over `O[X]`,
  `powFlat_R1n`, `powFlat_R0n`, and the cusp patch over `V₀`, `powFlat_cuspPiece`);
* `regularB1`, `regularB0`: nonzero polynomials over `O/ϖ` in `Y`, resp. `X`, are nonzerodivisors
  on `R1/ϖ`, `R0/ϖ` (the charts are free over `O[X]`);
* the regularity of the cusp patch (`NodeEtaleGlue.PatchInput.regularOn_piece`).

The proofs follow the Tate case (`TateGlue0.exists_flat_algebraization_cusp`, `PowFlatTate`).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower PowFlat

noncomputable section

/-! ### The levels `0` of the charts -/

section Charts

variable {O : Type u} [CommRing O] (ϖ a : O) [(Ideal.span {ϖ}).IsPrime]

/-- **Nonzero polynomials over `O/ϖ` in `Y` are nonzerodivisors on `R1/ϖ`.** -/
theorem regularB1 (p : O[X]) (hp : p ∉ (Ideal.span {ϖ}).map C) :
    IsSMulRegular (Tn ϖ (R1 O a) 0) (algebraMap (R1 O a) (Tn ϖ (R1 O a) 0) (aeval (y1 O a) p)) := by
  have e : aeval (y1 O a) p = algebraMap O[X] (R1 O a) p := by
    rw [y1, ← AdjoinRoot.algebraMap_eq, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]
  rw [e, Ideal.Quotient.algebraMap_eq]
  have h := BasisIdeal.isSMulRegular_mk (AdjoinRoot.powerBasis' (monic_G1 O a)).basis _ hp
  rw [← TateGlue0.Iv_zero_map] at h
  exact h

/-- **Nonzero polynomials over `O/ϖ` in `X` are nonzerodivisors on `R0/ϖ`.** -/
theorem regularB0 (p : O[X]) (hp : p ∉ (Ideal.span {ϖ}).map C) :
    IsSMulRegular (Tn ϖ (R0 O a) 0) (algebraMap (R0 O a) (Tn ϖ (R0 O a) 0) (aeval (x0 O a) p)) := by
  have e : aeval (x0 O a) p = algebraMap O[X] (R0 O a) p := by
    rw [x0, ← AdjoinRoot.algebraMap_eq, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]
  rw [e, Ideal.Quotient.algebraMap_eq]
  have h := BasisIdeal.isSMulRegular_mk (AdjoinRoot.powerBasis' (monic_G0 O a)).basis _ hp
  rw [← TateGlue0.Iv_zero_map] at h
  exact h

end Charts

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O] (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))
  (ω : OmegaC Sp S0.C0) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-! ### `ϖ`-purity of the levels -/

omit [IsNoetherianRing O] in
/-- The levels `R1/ϖⁿ⁺¹` of the chart `V₁`. -/
theorem powFlat_R1n [IsDomain O] (hϖ0 : ϖ ≠ 0) (n : ℕ) : PowFlat ϖ (n + 1) (Tn ϖ (R1 O a) n) :=
  tn (T := R1 O a) (isSMulRegular_of_free hϖ0) n

omit [IsNoetherianRing O] in
/-- The levels `R0/ϖⁿ⁺¹` of the chart `V₀`. -/
theorem powFlat_R0n [IsDomain O] (hϖ0 : ϖ ≠ 0) (n : ℕ) : PowFlat ϖ (n + 1) (Tn ϖ (R0 O a) n) :=
  tn (T := R0 O a) (isSMulRegular_of_free hϖ0) n

/-- The cusp patch pieces over `V₀` are `PowFlat`. -/
theorem powFlat_cuspPiece [IsDomain O] (hϖ0 : ϖ ≠ 0) (n : ℕ) :
    PowFlat ϖ (n + 1) ((CuspTower.cuspPiece S0 hϖ hker (isSMulRegular_x0 ϖ a) hO).P n) := by
  haveI : ∀ n, IsScalarTower (R0 O a) (EtaleTower.Tn ϖ (R0 O a) (n + 1))
      (EtaleTower.Tn ϖ (R0 O a) n) := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact patchInput_piece (CuspTower.cuspInput S0 hϖ hker (isSMulRegular_x0 ϖ a)) hθ.out hO
    (fun j ↦ isEmptyElim j) hϖ0 (powFlat_R0n hϖ0 n) (tn_kill ϖ _ n)
    (Ideal.span_singleton_pow ϖ (n + 1))

variable [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] (hϖ0 : ϖ ≠ 0)

include hϖ0 in
/-- **`hpure0`**: the chart modules over `U₀` of the adic system of the covering are flat over
`O/ϖⁿ`. -/
theorem system_hpure0 (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system Sp hϖ hker S0 ω hO).M n).x0) := by
  haveI : (Ideal.span {(overlap Sp hϖ hker S0 ω hO).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : ∀ n, IsNoetherianRing ((input Sp hϖ hker).B n) :=
    fun n ↦ (inferInstance : IsNoetherianRing (Tn ϖ (R1 O a) n))
  exact system_pure0 (overlap Sp hϖ hker S0 ω hO) hθ.out hO
    (fun j ↦ isEmptyElim j) hϖ0 (fun n ↦ powFlat_R1n hϖ0 n)
    (fun n ↦ Ideal.span_singleton_pow ϖ (n + 1)) (fun n ↦ powFlat_cuspPiece hϖ hker S0 hO hϖ0 n) n

include hϖ0 in
/-- **`hpure1`**: the chart modules over `U₁` of the adic system are flat over `O/ϖⁿ`. -/
theorem system_hpure1 (n : ℕ) :
    Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O]
      Module.AEval' ((system Sp hϖ hker S0 ω hO).M n).x1) := by
  haveI : (Ideal.span {(overlap Sp hϖ hker S0 ω hO).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : ∀ n, IsNoetherianRing ((input Sp hϖ hker).B n) :=
    fun n ↦ (inferInstance : IsNoetherianRing (Tn ϖ (R1 O a) n))
  exact system_pure1 (overlap Sp hϖ hker S0 ω hO) hθ.out hO
    (fun j ↦ isEmptyElim j) hϖ0 (fun n ↦ powFlat_R1n hϖ0 n)
    (fun n ↦ Ideal.span_singleton_pow ϖ (n + 1)) n

include hϖ0 in
/-- **Flat algebraization of the lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}`** (MR13 A1): a
coherent chart algebra on `ℙ¹_O`, finite and flat over both charts `O[X]`, whose reductions
modulo `ϖⁿ` are the levels of the covering given by `Sp`, `S0`, `ω`. -/
theorem exists_flat_algebraization [IsAdicComplete (Ideal.span {ϖ}) O] :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n), ((system Sp hϖ hker S0 ω hO).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) := by
  haveI : (Ideal.span {(overlap Sp hϖ hker S0 ω hO).ϖ}).IsMaximal :=
    ‹(Ideal.span {ϖ}).IsMaximal›
  haveI : IsAdicComplete (Ideal.span {(overlap Sp hϖ hker S0 ω hO).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact (overlap Sp hϖ hker S0 ω hO).exists_flat_algebraization hθ.out hO
    (system_hpure0 Sp hϖ hker S0 ω hO hϖ0) (system_hpure1 Sp hϖ hker S0 ω hO hϖ0)
    (regularB1 ϖ a) (regularB0 ϖ a)
    ((CuspTower.cuspInput S0 hϖ hker (isSMulRegular_x0 ϖ a)).regularOn_piece hθ.out hO 0)

end

end P1Three

end SemistableReduction
