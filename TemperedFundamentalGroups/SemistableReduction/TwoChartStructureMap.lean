/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ChartAlgebraHomAlgebraization
import TemperedFundamentalGroups.SemistableReduction.TwoChartTower

/-!
# The structure map of an algebraized tower of two-chart rings (Blueprint §12.8, M2.5, step (a))

Let `E` be a tower of two-chart rings with successor maps `e n` (`TwoChartTower.systemShift`) and
`(N, B, α)` an algebraization of the shifted system. A compatible family of morphisms of two-chart
rings `β n : D → E n` out of coherent two-chart rings `D` (the base model `𝒳`, mapping to every
level of the covering) algebraizes to a morphism of chart algebras `ψ : D.algStr → B` reducing to
`β n` (`TwoChartTower.exists_structureMap`) — the structure map `𝒴 → 𝒳`.

`TwoChartTower.liftShift β`: the family `β` extended to the shifted tower (the zero map at level 0);
`TwoChartTower.tr_comp_liftShift`: its compatibility with the transition maps of the system.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TwoChartTower

open ProjectiveLine ProjectiveLine.ChartModule

variable {A : Type u} [CommRing A] {E : ℕ → TwoChartRings A}
  {e : ∀ n, TwoChartMap (E (n + 1)) (E n)} {D : TwoChartRings A}

/-- A family of maps `D → E n` extended to the shifted tower (`0, E 0, E 1, …`). -/
noncomputable def liftShift (β : ∀ n, TwoChartMap D (E n)) : ∀ n, TwoChartMap D (shift E n)
  | 0 => toZero D
  | n + 1 => β n

variable (e) {β : ∀ n, TwoChartMap D (E n)}
  (h0 : ∀ n a, (e n).f0 ((β (n + 1)).f0 a) = (β n).f0 a)
  (h1 : ∀ n a, (e n).f1 ((β (n + 1)).f1 a) = (β n).f1 a)
  (h01 : ∀ n a, (e n).f01 ((β (n + 1)).f01 a) = (β n).f01 a)

include h0 h1 h01 in
/-- **The extended family is compatible with the transition maps of the shifted tower.** -/
lemma tr_comp_liftShift {m n : ℕ} (h : m ≤ n) :
    (trLe (shift E) (shiftMap E e) h).toHom.comp (liftShift β n).toHom =
      (liftShift β m).toHom := by
  refine Hom.ext' (LinearMap.ext fun a ↦ ?_) (LinearMap.ext fun a ↦ ?_) (LinearMap.ext fun a ↦ ?_)
  · exact RingHom.congr_fun (TowerSystem.trLe_comp_a (G := fun k ↦ (shift E k).R0)
      (t := fun k ↦ (shiftMap E e k).f0.toRingHom) (fun k ↦ (liftShift β k).f0.toRingHom)
      (fun k ↦ match k with
        | 0 => RingHom.ext fun _ ↦ @Subsingleton.elim PUnit _ _ _
        | k + 1 => RingHom.ext fun a ↦ h0 k a) h) a
  · exact RingHom.congr_fun (TowerSystem.trLe_comp_a (G := fun k ↦ (shift E k).R1)
      (t := fun k ↦ (shiftMap E e k).f1.toRingHom) (fun k ↦ (liftShift β k).f1.toRingHom)
      (fun k ↦ match k with
        | 0 => RingHom.ext fun _ ↦ @Subsingleton.elim PUnit _ _ _
        | k + 1 => RingHom.ext fun a ↦ h1 k a) h) a
  · exact RingHom.congr_fun (TowerSystem.trLe_comp_a (G := fun k ↦ (shift E k).R01)
      (t := fun k ↦ (shiftMap E e k).f01.toRingHom) (fun k ↦ (liftShift β k).f01.toRingHom)
      (fun k ↦ match k with
        | 0 => RingHom.ext fun _ ↦ @Subsingleton.elim PUnit _ _ _
        | k + 1 => RingHom.ext fun a ↦ h01 k a) h) a

variable {I : Ideal A} [IsNoetherianRing A] [IsAdicComplete I A]
  {he0 : ∀ n, Function.Surjective (e n).f0} {he1 : ∀ n, Function.Surjective (e n).f1}
  {hker0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0)}
  {hker1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1)}
  {hkill0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥}
  {hkill1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥}
  {hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0)}
  {hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)}
  {N : ChartModule A} [Module.Finite A[X] (Module.AEval' N.x0)]
  [Module.Finite A[X] (Module.AEval' N.x1)] {B : AlgStr N}
  {α : ∀ n, Hom N ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).M n)}

include h0 h1 h01 in
/-- **The structure map `𝒴 → 𝒳`**: a compatible family of morphisms of two-chart rings
`β n : D → E n` out of coherent two-chart rings algebraizes to a morphism of chart algebras
`ψ : D.algStr → B` with reductions `β n` (`α (n + 1) ∘ ψ = β n`). -/
theorem exists_structureMap [Module.Finite A[X] (Module.AEval' D.chartModule.x0)]
    [Module.Finite A[X] (Module.AEval' D.chartModule.x1)]
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hc : ∀ m n (h : m ≤ n),
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).tr h).comp (α n) = α m)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n)) :
    ∃ ψ : Hom D.chartModule N, D.algStr.IsHom B ψ ∧ ∀ n, (α (n + 1)).comp ψ = (β n).toHom := by
  obtain ⟨ψ, hψ, hψB⟩ := AdicChartAlgSystem.exists_isHom_of_system _ hα hc hB D.algStr
    (fun n ↦ (liftShift β n).toHom) (fun _ _ h ↦ tr_comp_liftShift e h0 h1 h01 h)
    (fun n ↦ (liftShift β n).isHom)
  exact ⟨ψ, hψB, fun n ↦ hψ (n + 1)⟩

end TwoChartTower

end SemistableReduction
