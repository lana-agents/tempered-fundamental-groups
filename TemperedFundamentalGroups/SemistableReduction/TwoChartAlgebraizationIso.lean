/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TwoChartTower
import TemperedFundamentalGroups.SemistableReduction.AlgebraizationUnique

/-!
# Recognising the algebraization of a tower of two-chart rings (Blueprint §12.8, M2.4)

Let `E : ℕ → TwoChartRings A` be a tower of two-chart rings whose level `n` is killed by `Iⁿ⁺¹`,
with its adic system of chart algebras `S = TwoChartTower.systemShift E e …` (level `n + 1` of `S`
is `E n`). Let `P` be two-chart rings with charts finite over `A[X]` and `β n : P → E n`
compatible maps of two-chart rings, surjective on both charts with kernels `Iⁿ⁺¹ P`. Then `P` is
an algebraization of `S`:

* `TwoChartTower.shiftCone`: the maps `β` shifted by the map to the zero two-chart rings;
* `TwoChartTower.shiftCone_comp`, `TwoChartTower.shiftCone_ker0`, `…_ker1`: they satisfy the
  hypotheses of `AdicChartAlgSystem.exists_iso_of_algebraization`;
* **`TwoChartTower.exists_iso_of_algebraization_shift`**: every algebraization `(N, B, α)` of `S`
  is isomorphic to `P` as a chart algebra, compatibly with the reductions;
* **`TwoChartTower.exists_bijective_of_algebraization_shift`**: the comparison morphism
  `P → N` is bijective on both charts and on the overlap.
-/

universe u

open Polynomial

namespace SemistableReduction

open ProjectiveLine ProjectiveLine.ChartModule

namespace TwoChartTower

variable {A : Type u} [CommRing A] (E : ℕ → TwoChartRings A)
  (e : ∀ n, TwoChartMap (E (n + 1)) (E n)) {P : TwoChartRings A}

/-- The maps `β n : P → E n` shifted by the map to the zero two-chart rings: maps
`P → shift E n`. -/
noncomputable def shiftCone (β : ∀ n, TwoChartMap P (E n)) : ∀ n, TwoChartMap P (shift E n)
  | 0 => toZero P
  | n + 1 => β n

variable {E e} (β : ∀ n, TwoChartMap P (E n))
  (hc0 : ∀ n, (e n).f0.comp (β (n + 1)).f0 = (β n).f0)
  (hc1 : ∀ n, (e n).f1.comp (β (n + 1)).f1 = (β n).f1)
  (hc01 : ∀ n, (e n).f01.comp (β (n + 1)).f01 = (β n).f01)

include hc0 hc1 hc01 in
/-- **The shifted maps are compatible with the transition maps.** -/
theorem shiftCone_comp {m n : ℕ} (h : m ≤ n) :
    (trLe (shift E) (shiftMap E e) h).toHom.comp (shiftCone E β n).toHom =
      (shiftCone E β m).toHom := by
  refine ChartModule.Hom.ext' (LinearMap.ext fun a ↦ ?_) (LinearMap.ext fun a ↦ ?_)
    (LinearMap.ext fun a ↦ ?_)
  · refine RingHom.congr_fun (TowerSystem.trLe_comp_a (G := fun k ↦ (shift E k).R0)
      (t := fun k ↦ (shiftMap E e k).f0.toRingHom)
      (fun k ↦ (shiftCone E β k).f0.toRingHom) (fun k ↦ ?_) h) a
    cases k with
    | zero => exact RingHom.ext fun _ ↦ @Subsingleton.elim PUnit _ _ _
    | succ k => exact congrArg AlgHom.toRingHom (hc0 k)
  · refine RingHom.congr_fun (TowerSystem.trLe_comp_a (G := fun k ↦ (shift E k).R1)
      (t := fun k ↦ (shiftMap E e k).f1.toRingHom)
      (fun k ↦ (shiftCone E β k).f1.toRingHom) (fun k ↦ ?_) h) a
    cases k with
    | zero => exact RingHom.ext fun _ ↦ @Subsingleton.elim PUnit _ _ _
    | succ k => exact congrArg AlgHom.toRingHom (hc1 k)
  · refine RingHom.congr_fun (TowerSystem.trLe_comp_a (G := fun k ↦ (shift E k).R01)
      (t := fun k ↦ (shiftMap E e k).f01.toRingHom)
      (fun k ↦ (shiftCone E β k).f01.toRingHom) (fun k ↦ ?_) h) a
    cases k with
    | zero => exact RingHom.ext fun _ ↦ @Subsingleton.elim PUnit _ _ _
    | succ k => exact congrArg AlgHom.toRingHom (hc01 k)

variable {I : Ideal A}

/-- The kernel of the map to the zero ring is `I⁰ • ⊤ = ⊤`. -/
lemma ker_toPUnit_toLinearMap {R : Type u} [CommRing R] [Algebra A R] :
    LinearMap.ker (toPUnit (A := A) R).toLinearMap = I ^ 0 • (⊤ : Submodule A R) := by
  rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  exact eq_top_iff.mpr fun _ _ ↦ LinearMap.mem_ker.mpr (@Subsingleton.elim PUnit _ _ _)

/-- **The kernels of the shifted maps** on `Spec A[X]`. -/
theorem shiftCone_ker0
    (hk0 : ∀ n, RingHom.ker (β n).f0 = (I ^ (n + 1)).map (algebraMap A P.R0)) (n : ℕ) :
    LinearMap.ker (shiftCone E β n).toHom.f0 = I ^ n • (⊤ : Submodule A P.R0) := by
  cases n with
  | zero => exact ker_toPUnit_toLinearMap
  | succ n => exact ker_toLinearMap _ (hk0 n)

/-- **The kernels of the shifted maps** on `Spec A[Y]`. -/
theorem shiftCone_ker1
    (hk1 : ∀ n, RingHom.ker (β n).f1 = (I ^ (n + 1)).map (algebraMap A P.R1)) (n : ℕ) :
    LinearMap.ker (shiftCone E β n).toHom.f1 = I ^ n • (⊤ : Submodule A P.R1) := by
  cases n with
  | zero => exact ker_toPUnit_toLinearMap
  | succ n => exact ker_toLinearMap _ (hk1 n)

theorem shiftCone_surj0 (hs0 : ∀ n, Function.Surjective (β n).f0) (n : ℕ) :
    Function.Surjective (shiftCone E β n).toHom.f0 := by
  cases n with
  | zero => exact fun _ ↦ ⟨0, @Subsingleton.elim PUnit _ _ _⟩
  | succ n => exact hs0 n

theorem shiftCone_surj1 (hs1 : ∀ n, Function.Surjective (β n).f1) (n : ℕ) :
    Function.Surjective (shiftCone E β n).toHom.f1 := by
  cases n with
  | zero => exact fun _ ↦ ⟨0, @Subsingleton.elim PUnit _ _ _⟩
  | succ n => exact hs1 n

theorem shiftCone_isHom (n : ℕ) :
    P.algStr.IsHom (shift E n).algStr (shiftCone E β n).toHom :=
  (shiftCone E β n).isHom

variable [IsNoetherianRing A] [IsAdicComplete I A]
  (he0 : ∀ n, Function.Surjective (e n).f0) (he1 : ∀ n, Function.Surjective (e n).f1)
  (hker0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0))
  (hker1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1))
  (hkill0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥)
  (hkill1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥)
  (hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0))
  (hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1))
  [Module.Finite A[X] (Module.AEval' P.chartModule.x0)]
  [Module.Finite A[X] (Module.AEval' P.chartModule.x1)]
  (hs0 : ∀ n, Function.Surjective (β n).f0) (hs1 : ∀ n, Function.Surjective (β n).f1)
  (hk0 : ∀ n, RingHom.ker (β n).f0 = (I ^ (n + 1)).map (algebraMap A P.R0))
  (hk1 : ∀ n, RingHom.ker (β n).f1 = (I ^ (n + 1)).map (algebraMap A P.R1))

include hc0 hc1 hc01 hs0 hs1 hk0 hk1 in
/-- **Two-chart rings with compatible surjections onto a tower are its algebraization**: every
algebraization `(N, B, α)` of the adic system `TwoChartTower.systemShift E e …` is isomorphic to
`P` as a chart algebra, compatibly with the reductions `α n` and `shiftCone E β n`. -/
theorem exists_iso_of_algebraization_shift {N : ChartModule A}
    [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).M n)}
    {B : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n),
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).tr h).comp (α n) = α m)
    (hB : ∀ n,
      B.IsHom ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n)) :
    ∃ (γ : Hom P.chartModule N) (δ : Hom N P.chartModule), γ.comp δ = Hom.id N ∧
      δ.comp γ = Hom.id P.chartModule ∧
      (∀ n, (α n).comp γ = (shiftCone E β n).toHom) ∧
      (∀ n, (shiftCone E β n).toHom.comp δ = α n) ∧
      P.algStr.IsHom B γ ∧ B.IsHom P.algStr δ :=
  AdicChartAlgSystem.exists_iso_of_algebraization
    (systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1)
    (β := fun n ↦ (shiftCone E β n).toHom) hα hαc hB
    (fun n ↦ ⟨shiftCone_surj0 β hs0 n, shiftCone_surj1 β hs1 n, shiftCone_ker0 β hk0 n,
      shiftCone_ker1 β hk1 n⟩)
    (fun _ _ h ↦ shiftCone_comp β hc0 hc1 hc01 h) (fun n ↦ shiftCone_isHom β n)

include hc0 hc1 hc01 hs0 hs1 hk0 hk1 in
/-- **Two-chart rings with compatible surjections onto a tower are its algebraization,
chartwise**: the comparison morphism `P → N` into an algebraization of
`TwoChartTower.systemShift E e …` is a morphism of chart algebras compatible with the reductions
which is bijective on both charts and on the overlap. -/
theorem exists_bijective_of_algebraization_shift {N : ChartModule A}
    [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]
    {α : ∀ n, Hom N ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).M n)}
    {B : AlgStr N}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hαc : ∀ m n (h : m ≤ n),
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).tr h).comp (α n) = α m)
    (hB : ∀ n,
      B.IsHom ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n)) :
    ∃ γ : Hom P.chartModule N, (∀ n, (α n).comp γ = (shiftCone E β n).toHom) ∧
      P.algStr.IsHom B γ ∧
      Function.Bijective γ.f0 ∧ Function.Bijective γ.f1 ∧ Function.Bijective γ.f01 :=
  AdicChartAlgSystem.exists_bijective_of_algebraization
    (systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1)
    (β := fun n ↦ (shiftCone E β n).toHom) hα hαc hB
    (fun n ↦ ⟨shiftCone_surj0 β hs0 n, shiftCone_surj1 β hs1 n, shiftCone_ker0 β hk0 n,
      shiftCone_ker1 β hk1 n⟩)
    (fun _ _ h ↦ shiftCone_comp β hc0 hc1 hc01 h) (fun n ↦ shiftCone_isHom β n)

end TwoChartTower

end SemistableReduction
