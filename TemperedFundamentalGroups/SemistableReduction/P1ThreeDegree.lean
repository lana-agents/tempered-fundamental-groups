/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialFibre
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialChart
import TemperedFundamentalGroups.SemistableReduction.GenericRankTower

/-!
# The degree of the lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` (MR13 (f), degree lemma)

**`P1Three.finrank_lift`**: for the M2 lift `(N, B, α)` (with structure map `ψ`) of a tame covering
`C1` of `V₁ ⊗ k = ℙ¹_k ∖ {0, 1, ā}` over a domain `O`, the generic rank of the second chart `B₁`
over `R1` equals the generic rank of `C1` over `R1/J`:
`rank_{R1} B₁ = rank_{R1/J} C1`.

Proof (`GenericRank.finrank_eq_of_reduction`): `B₁` is finite flat over `O[Y]` (`Y` the coordinate
of the chart module), so its rank over `O[Y]` is the rank of its reduction `B₁/ϖ ≃ C1`
(`specialFibreEquiv1`) over `k[Y]`; both `R1/O[Y]` and `(R1/J)/k[Y]` have rank `3`
(`finrank_R1`, `finrank_Ts_R1`), and the tower law over domains divides by `3` on both sides.

With `IsBaseChange.finrank_eq` this is the degree `[K' ⊗ C : K']` of the generic fibre of the lift
over the function field of `ℙ¹_{K̄}`, i.e. the hypothesis `hdeg` of iut's
`Pi1GaloisAlgebra.line_exists_sigmaQuotient_ofAlgebra` when `C1` has rank `|G|`.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O] (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))
  (ω : OmegaC Sp S0.C0) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)}
  (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
    LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
  (hB : ∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n))
  {ψ : ProjectiveLine.ChartModule.Hom (twoChart O a).chartModule N}
  (hψ : (twoChart O a).algStr.IsHom B ψ)
  (hψα : ∀ n, (α (n + 1)).comp ψ = structureMaps Sp hϖ hker S0 ω hO n)

/-- The reduction `B₁ → B₁/ϖ ≃ C1` as an additive map. -/
def reduction1 : B.Ring1 →+ Sp.C1 :=
  (specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB).toRingHom.toAddMonoidHom.comp
    (Ideal.Quotient.mk (Ideal.span {B.const1 ϖ})).toAddMonoidHom

lemma reduction1_apply (b : B.Ring1) :
    reduction1 Sp hϖ hker S0 ω hO hα hB b =
      specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB (Ideal.Quotient.mk _ b) :=
  rfl

lemma reduction1_mul (x y : B.Ring1) :
    reduction1 Sp hϖ hker S0 ω hO hα hB (x * y) =
      reduction1 Sp hϖ hker S0 ω hO hα hB x * reduction1 Sp hϖ hker S0 ω hO hα hB y := by
  simp only [reduction1_apply, map_mul]

include hψα in
/-- The reduction of the structure map: `ψ(r) ↦ r̄`. -/
lemma reduction1_ψ (r : R1 O a) :
    reduction1 Sp hϖ hker S0 ω hO hα hB (ψ.f1 r) =
      algebraMap (Ts θ (R1 O a)) Sp.C1 (Ideal.Quotient.mk _ r) :=
  specialFibreEquiv1_ψ Sp hϖ hker S0 ω hO hα hB hψα r

include hα hB hψ hψα in
/-- **The degree of the lift**: `rank_{R1} B₁ = rank_{R1/J} C1` (generic ranks over the chart
`V₁ = ℙ¹ ∖ {0, 1, a}` and its special fibre). -/
theorem finrank_lift [IsDomain O] [Module.Finite O[X] (Module.AEval' N.x1)]
    [Module.Flat O[X] (Module.AEval' N.x1)] :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    Module.finrank (R1 O a) B.Ring1 = Module.finrank (Ts θ (R1 O a)) Sp.C1 := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI : Algebra O[X] B.Ring1 := B.polyHom1.toAlgebra
  haveI : IsScalarTower O[X] (R1 O a) B.Ring1 :=
    IsScalarTower.of_algebraMap_eq' (algR1_comp hψ).symm
  haveI := B.finite_polyHom1
  haveI := B.flat_polyHom1
  haveI := isDomain_R1 O a
  haveI := isDomain_Ts_R1 a (θ := θ)
  letI := algTs1 a (θ := θ)
  letI : Algebra k[X] Sp.C1 :=
    ((algebraMap (Ts θ (R1 O a)) Sp.C1).comp (algebraMap k[X] (Ts θ (R1 O a)))).toAlgebra
  haveI : IsScalarTower k[X] (Ts θ (R1 O a)) Sp.C1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra O[X] k[X] := (mapRingHom θ).toAlgebra
  haveI := finite_Ts_R1 a (θ := θ)
  have hR : Function.Injective (algebraMap O[X] (R1 O a)) := FaithfulSMul.algebraMap_injective _ _
  have hc : algebraMap O[X] B.Ring1 (C ϖ) = B.const1 ϖ := by
    simp [ProjectiveLine.ChartModule.AlgStr.polyHom1, RingHom.algebraMap_toAlgebra]
  refine GenericRank.finrank_eq_of_reduction (P := O[X]) (Pb := k[X]) hR (injective_algTs1 a)
    (by rw [finrank_R1, finrank_Ts_R1]) (by rw [finrank_R1]; norm_num)
    (Polynomial.map_surjective θ hθ.out) (reduction1 Sp hϖ hker S0 ω hO hα hB)
    ((specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB).surjective.comp Ideal.Quotient.mk_surjective)
    (fun p b ↦ ?_) (fun b hb ↦ ?_)
  · rw [Algebra.smul_def, Algebra.smul_def, reduction1_mul,
      IsScalarTower.algebraMap_apply O[X] (R1 O a) B.Ring1 p]
    congr 1
    refine (reduction1_ψ Sp hϖ hker S0 ω hO hα hB hψα (algebraMap O[X] (R1 O a) p)).trans ?_
    rw [IsScalarTower.algebraMap_apply k[X] (Ts θ (R1 O a)) Sp.C1]
    exact congrArg (algebraMap (Ts θ (R1 O a)) Sp.C1) (algTs1_map a p).symm
  · rw [reduction1_apply, map_eq_zero_iff _ (specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB).injective,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hb
    obtain ⟨c, rfl⟩ := hb
    rw [← hc, mul_comm, ← Algebra.smul_def]
    refine Submodule.smul_mem_smul ?_ Submodule.mem_top
    rw [RingHom.mem_ker]
    change (C ϖ).map θ = 0
    rw [Polynomial.map_C, hϖ, C_0]

end

end P1Three

end SemistableReduction
