/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ChartAlgebraHomAlgebraization

/-!
# Uniqueness of algebraizations of adic systems of chart algebras

Let `A` be Noetherian and `I`-adically complete and `S` an adic system of chart algebras on
`ℙ¹_A`. If `(N, B, α)` and `(P, BP, β)` are two algebraizations of `S` (coherent chart algebras
with compatible algebra maps to the levels inducing `N / Iⁿ N ≅ S.M n`, resp.
`P / Iⁿ P ≅ S.M n`), then `N` and `P` are isomorphic as chart algebras, compatibly with the
reductions (`AdicChartAlgSystem.exists_iso_of_algebraization`). The proof applies
`AdicChartAlgSystem.exists_isHom_of_system` in both directions and
`AdicChartAlgSystem.eq_of_comp_eq` to the two composites.
-/

universe u

open Polynomial

namespace ProjectiveLine

open ChartModule

namespace AdicChartAlgSystem

variable {A : Type u} [CommRing A] {I : Ideal A} [IsNoetherianRing A] [IsAdicComplete I A]
  (S : AdicChartAlgSystem I)

/-- **Uniqueness of algebraizations**: two algebraizations `(N, B, α)` and `(P, BP, β)` of an
adic system of chart algebras are isomorphic as chart algebras, compatibly with the reductions:
there are mutually inverse morphisms of chart algebras `γ : P → N` and `δ : N → P` with
`α n ∘ γ = β n` and `β n ∘ δ = α n`. -/
theorem exists_iso_of_algebraization {N P : ChartModule A}
    [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]
    [Module.Finite A[X] (Module.AEval' P.x0)] [Module.Finite A[X] (Module.AEval' P.x1)]
    {α : ∀ n, Hom N (S.M n)} {β : ∀ n, Hom P (S.M n)} {B : AlgStr N} {BP : AlgStr P}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom (S.alg n) (α n))
    (hβ : ∀ n, Function.Surjective (β n).f0 ∧ Function.Surjective (β n).f1 ∧
      LinearMap.ker (β n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (β n).f1 = I ^ n • ⊤)
    (hβc : ∀ m n (h : m ≤ n), (S.tr h).comp (β n) = β m)
    (hBP : ∀ n, BP.IsHom (S.alg n) (β n)) :
    ∃ (γ : Hom P N) (δ : Hom N P), γ.comp δ = Hom.id N ∧ δ.comp γ = Hom.id P ∧
      (∀ n, (α n).comp γ = β n) ∧ (∀ n, (β n).comp δ = α n) ∧
      BP.IsHom B γ ∧ B.IsHom BP δ := by
  obtain ⟨γ, hγ, hγB⟩ := S.exists_isHom_of_system hα hαc hB BP β hβc hBP
  obtain ⟨δ, hδ, hδB⟩ := S.exists_isHom_of_system hβ hβc hBP B α hαc hB
  refine ⟨γ, δ, ?_, ?_, hγ, hδ, hγB, hδB⟩
  · refine S.eq_of_comp_eq hα _ _ fun n ↦ ?_
    rw [← Hom.comp_assoc, hγ, hδ, Hom.comp_id]
  · refine S.eq_of_comp_eq hβ _ _ fun n ↦ ?_
    rw [← Hom.comp_assoc, hδ, hγ, Hom.comp_id]

/-- **Uniqueness of algebraizations, chartwise**: the comparison morphism `γ : P → N` of two
algebraizations of an adic system of chart algebras is a morphism of chart algebras compatible
with the reductions which is bijective on both charts and on the overlap. -/
theorem exists_bijective_of_algebraization {N P : ChartModule A}
    [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]
    [Module.Finite A[X] (Module.AEval' P.x0)] [Module.Finite A[X] (Module.AEval' P.x1)]
    {α : ∀ n, Hom N (S.M n)} {β : ∀ n, Hom P (S.M n)} {B : AlgStr N} {BP : AlgStr P}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom (S.alg n) (α n))
    (hβ : ∀ n, Function.Surjective (β n).f0 ∧ Function.Surjective (β n).f1 ∧
      LinearMap.ker (β n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (β n).f1 = I ^ n • ⊤)
    (hβc : ∀ m n (h : m ≤ n), (S.tr h).comp (β n) = β m)
    (hBP : ∀ n, BP.IsHom (S.alg n) (β n)) :
    ∃ γ : Hom P N, (∀ n, (α n).comp γ = β n) ∧ BP.IsHom B γ ∧
      Function.Bijective γ.f0 ∧ Function.Bijective γ.f1 ∧ Function.Bijective γ.f01 := by
  obtain ⟨γ, δ, hγδ, hδγ, hγ, -, hγB, -⟩ :=
    S.exists_iso_of_algebraization hα hαc hB hβ hβc hBP
  refine ⟨γ, hγ, hγB, ?_, ?_, ?_⟩
  · exact ⟨Function.LeftInverse.injective (g := δ.f0) (Hom.f0_eq_of_eq hδγ),
      Function.RightInverse.surjective (g := δ.f0) (Hom.f0_eq_of_eq hγδ)⟩
  · exact ⟨Function.LeftInverse.injective (g := δ.f1) (Hom.f1_eq_of_eq hδγ),
      Function.RightInverse.surjective (g := δ.f1) (Hom.f1_eq_of_eq hγδ)⟩
  · exact ⟨Function.LeftInverse.injective (g := δ.f01) (Hom.f01_eq_of_eq hδγ),
      Function.RightInverse.surjective (g := δ.f01) (Hom.f01_eq_of_eq hγδ)⟩

end AdicChartAlgSystem

end ProjectiveLine
