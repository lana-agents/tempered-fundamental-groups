/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSystemMap
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Base
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Morphisms of algebraizations respect the structure maps (generic; MR13, (f) step 4)

* **`ProjectiveLine.ChartModule.eq_zero_of_mem_pow_smul_top1`** (Krull): an element of the second
  chart module, flat and finite over `A[X]` (`A` a Noetherian domain), lying in `(ϖ)ⁿ M₁` for every
  `n` (`ϖ` a nonunit) is zero;
* **`AdicChartAlgSystem.Algebraization.eq_of_f1_eq`**: elements of the second chart of a flat
  algebraization are detected by their reductions `α (n + 1)`;
* **`NodeEtaleGlue.Overlap.exists_structureMap_systemAt`**: the structure map of an algebraization
  of `V.systemAt ϖ`, with its reductions on the second chart (`B0 → Y n` after the base map);
* **`NodeEtaleGlue.Overlap.map_f1_structure`**: the morphism of algebraizations induced by a
  morphism of adic systems with second-chart components `y n` (e.g. `Overlap.systemMap`) commutes
  with the structure maps `ψ`, `ψ'` from a base model on the second chart, if the `y n` commute
  with the structure maps of the levels.

For the lifts of tame covers of `ℙ¹_k ∖ {0, 1, ā}` this makes the Galois action on the second chart
`B₁` act by `R1`-algebra automorphisms (`P1Three.Datum.algMap_f1_structure`).
-/

universe u

open Polynomial

namespace ProjectiveLine.ChartModule

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (N : ChartModule A)
  [Module.Finite A[X] (Module.AEval' N.x1)] [Module.Flat A[X] (Module.AEval' N.x1)]

/-- **Krull's intersection theorem on the second chart**: if `M₁` is finite and flat over `A[X]`
(`A` a Noetherian domain) and `ϖ` is not a unit, then `⋂ₙ (ϖ)ⁿ M₁ = 0`. -/
theorem eq_zero_of_mem_pow_smul_top1 {ϖ : A} (hϖ : ¬IsUnit ϖ) {z : N.M1}
    (hz : ∀ n, z ∈ (Ideal.span {ϖ}) ^ n • (⊤ : Submodule A N.M1)) : z = 0 := by
  let J : Ideal A[X] := Ideal.span {C ϖ}
  have hJ : J ≠ ⊤ := fun h ↦ hϖ (Polynomial.isUnit_C.mp ((Ideal.span_singleton_eq_top).1 h))
  have key := Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree (R := A[X])
    (M := Module.AEval' N.x1) (I := J) hJ
  have hmem : Module.AEval'.of N.x1 z ∈
      (⨅ i : ℕ, J ^ i • ⊤ : Submodule A[X] (Module.AEval' N.x1)) := by
    refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
    have h := hz n
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at h
    obtain ⟨m, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h
    have : Module.AEval'.of N.x1 (ϖ ^ n • m) = (C ϖ) ^ n • Module.AEval'.of N.x1 m := by
      rw [map_smul, ← C_pow, ← Polynomial.algebraMap_eq, algebraMap_smul]
    rw [this, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  rw [key, Submodule.mem_bot] at hmem
  exact (Module.AEval'.of N.x1).injective (hmem.trans (map_zero _).symm)

end ProjectiveLine.ChartModule

namespace ProjectiveLine.AdicChartAlgSystem.Algebraization

variable {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] {ϖ : A}
  {S : AdicChartAlgSystem (Ideal.span {ϖ})}

/-- **Elements of the second chart of a flat algebraization are detected by their reductions.** -/
theorem eq_of_f1_eq (L : Algebraization S) [Module.Flat A[X] (Module.AEval' L.N.x1)]
    (hϖ : ¬IsUnit ϖ) {x x' : L.N.M1} (h : ∀ n, (L.α (n + 1)).f1 x = (L.α (n + 1)).f1 x') :
    x = x' := by
  rw [← sub_eq_zero]
  refine L.N.eq_zero_of_mem_pow_smul_top1 hϖ fun n ↦ ?_
  have hk : x - x' ∈ LinearMap.ker (L.α (n + 1)).f1 := by
    rw [LinearMap.mem_ker, map_sub, h n, sub_self]
  rw [(L.hα (n + 1)).2.2.2] at hk
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) hk

end ProjectiveLine.AdicChartAlgSystem.Algebraization

namespace SemistableReduction

open AdmissibleLift ProjectiveLine

noncomputable section

namespace NodeEtaleGlue.Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}
  {I : Input θ cov₀ πL} {I' : Input θ cov₀' πL'}
  (V : Overlap I) (V' : Overlap I') (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (ϖ : O) (h : V.ϖ = ϖ)

variable [IsNoetherianRing O] [IsAdicComplete (Ideal.span {ϖ}) O]

/-- **The structure map of an algebraization of `V.systemAt ϖ`** (`BaseMap.exists_structureMap`),
with its reductions on the second chart stated pointwise: `ψ.f1` reduces to `B0 → Y n` after the
base map `a1`. -/
theorem exists_structureMap_systemAt {D : TwoChartRings O} (b : BaseMap V D)
    [Module.Finite O[X] (Module.AEval' D.chartModule.x0)]
    [Module.Finite O[X] (Module.AEval' D.chartModule.x1)]
    (L : AdicChartAlgSystem.Algebraization (V.systemAt hθ hO ϖ h)) :
    ∃ ψ : ChartModule.Hom D.chartModule L.N, D.algStr.IsHom L.B ψ ∧
      ∀ n r, ((L.α (n + 1)).f1 (ψ.f1 r) : I.Y hθ n) = algebraMap I.B0 (I.Y hθ n) (b.a1 r) := by
  subst h
  obtain ⟨ψ, hψ, hψα⟩ := b.exists_structureMap hθ hO L.hα L.hc L.hB
  exact ⟨ψ, hψ, fun n r ↦ LinearMap.congr_fun (congrArg ChartModule.Hom.f1 (hψα n)) r⟩

variable [IsDomain O]

/-- **A morphism of algebraizations respects the structure maps on the second chart**: let
`γ : V.systemAt ϖ → V'.systemAt ϖ` be a morphism of adic systems whose second-chart components at
the levels `n + 1` are ring maps `y n : Y n → Y' n` (e.g. `Overlap.systemMap`, `systemMap_f_succ`)
with `y n ∘ (B0 → Y n) ∘ a1 = (B0' → Y' n) ∘ a1'` for base maps `b`, `b'` of `V`, `V'` from the same
base model `D`; if `ψ`, `ψ'` are morphisms from `D` to algebraizations `L`, `L'` (the latter flat on
the second chart) reducing to the structure maps, then `(map γ L L').f1 ∘ ψ.f1 = ψ'.f1`. -/
theorem map_f1_structure (h' : V'.ϖ = ϖ)
    (γ : AdicChartAlgSystem.Hom (V.systemAt hθ hO ϖ h) (V'.systemAt hθ hO ϖ h'))
    (y : ∀ n, I.Y hθ n →+* I'.Y hθ n)
    (hγ : ∀ n (z : I.Y hθ n), ((γ.f (n + 1)).f1 z : I'.Y hθ n) = y n z)
    {D : TwoChartRings O} (b : BaseMap V D) (b' : BaseMap V' D)
    (hb : ∀ n r, y n (algebraMap I.B0 (I.Y hθ n) (b.a1 r)) =
      algebraMap I'.B0 (I'.Y hθ n) (b'.a1 r))
    (L : AdicChartAlgSystem.Algebraization (V.systemAt hθ hO ϖ h))
    (L' : AdicChartAlgSystem.Algebraization (V'.systemAt hθ hO ϖ h'))
    [Module.Flat O[X] (Module.AEval' L'.N.x1)] (hϖ : ¬IsUnit ϖ)
    (ψ : ChartModule.Hom D.chartModule L.N) (ψ' : ChartModule.Hom D.chartModule L'.N)
    (hψα : ∀ n r, ((L.α (n + 1)).f1 (ψ.f1 r) : I.Y hθ n) = algebraMap I.B0 (I.Y hθ n) (b.a1 r))
    (hψα' : ∀ n r, ((L'.α (n + 1)).f1 (ψ'.f1 r) : I'.Y hθ n) =
      algebraMap I'.B0 (I'.Y hθ n) (b'.a1 r)) (r : D.R1) :
    (AdicChartAlgSystem.Algebraization.map γ L L').f1 (ψ.f1 r) = ψ'.f1 r := by
  refine L'.eq_of_f1_eq hϖ fun n ↦ ?_
  have e1 := LinearMap.congr_fun (congrArg ChartModule.Hom.f1
    (AdicChartAlgSystem.Algebraization.comp_map γ L L' (n + 1))) (ψ.f1 r)
  have e4 : ((L'.α (n + 1)).f1 ((AdicChartAlgSystem.Algebraization.map γ L L').f1 (ψ.f1 r)) :
      I'.Y hθ n) = y n ((L.α (n + 1)).f1 (ψ.f1 r)) := e1.trans (hγ n _)
  exact e4.trans ((congrArg (y n) (hψα n r)).trans ((hb n r).trans (hψα' n r).symm))

end NodeEtaleGlue.Overlap

end

end SemistableReduction
