/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ChartAlgebraHomAlgebraization
import TemperedFundamentalGroups.SemistableReduction.TwoChartNormMap

/-!
# Morphisms of adic systems of chart algebras and their algebraization (MR12 I3, core layer 5)

The last layer of the lifting of morphisms of special-fibre data (Blueprint §12.8, M2.5): a
morphism of the M2 systems of two coverings algebraizes to a morphism of the algebraized
coverings.

* `ChartModule.AlgStr.IsHom.id`, `ChartModule.AlgStr.IsHom.comp`;
* **`AdicChartAlgSystem.Hom S S'`**: morphisms of chart algebras `S.M n → S'.M n` commuting with
  the transition maps; `Hom.id`, `Hom.comp`;
* **`AdicChartAlgSystem.exists_isHom_of_hom`**, **`AdicChartAlgSystem.algHom`**: for
  algebraizations `(N, B, α)` of `S` and `(N', B', α')` of `S'` (`exists_algebraization`), a
  morphism `γ : S → S'` is the system of reductions of a unique morphism of chart algebras
  `N → N'` (`comp_algHom`, `isHom_algHom`, uniqueness `eq_algHom`); `algHom_id`, `algHom_comp`;
* **`TwoChartTower.systemHom`**, **`TwoChartTower.systemShiftHom`**: a family of maps of two-chart
  rings commuting with the successor maps of two towers is a morphism of the associated adic
  systems (`TwoChartTower.system`, `TwoChartTower.systemShift`); naturality of the transition
  maps `TwoChartTower.trLe_comp_toHom`.

Shared by the Tate curve (MR12: `Gal(L/K) ≃ Aut` of the special datum) and the model of
`ℙ¹ ∖ {0, 1, a}` (MR13: the Galois action on the lift of a tame covering).
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] {M N P : ChartModule A}

/-- The identity is a morphism of chart algebras. -/
lemma AlgStr.IsHom.id (B : AlgStr M) : B.IsHom B (Hom.id M) :=
  ⟨by rw [Hom.tensor_id, Hom.id_comp, Hom.comp_id], rfl⟩

/-- Composites of morphisms of chart algebras are morphisms of chart algebras. -/
lemma AlgStr.IsHom.comp {B : AlgStr M} {B' : AlgStr N} {B'' : AlgStr P} {φ : Hom M N}
    {ψ : Hom N P} (hψ : B'.IsHom B'' ψ) (hφ : B.IsHom B' φ) : B.IsHom B'' (ψ.comp φ) :=
  ⟨by rw [Hom.comp_assoc, hφ.1, ← Hom.comp_assoc, hψ.1, Hom.comp_assoc, ← Hom.tensor_comp],
    by rw [Hom.mapH0_comp, hφ.2, hψ.2]⟩

end ChartModule

open ChartModule

namespace AdicChartAlgSystem

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **A morphism of adic systems of chart algebras**: morphisms of chart algebras at every level,
commuting with the transition maps. -/
structure Hom (S S' : AdicChartAlgSystem I) where
  /-- the morphism at level `n` -/
  f : ∀ n, ChartModule.Hom (S.M n) (S'.M n)
  comm : ∀ {m n : ℕ} (h : m ≤ n), (S'.tr h).comp (f n) = (f m).comp (S.tr h)
  isHom : ∀ n, (S.alg n).IsHom (S'.alg n) (f n)

/-- The identity morphism of an adic system. -/
def Hom.id (S : AdicChartAlgSystem I) : Hom S S where
  f n := ChartModule.Hom.id _
  comm h := by rw [ChartModule.Hom.comp_id, ChartModule.Hom.id_comp]
  isHom n := AlgStr.IsHom.id _

/-- Composition of morphisms of adic systems. -/
def Hom.comp {S S' S'' : AdicChartAlgSystem I} (γ' : Hom S' S'') (γ : Hom S S') : Hom S S'' where
  f n := (γ'.f n).comp (γ.f n)
  comm h := by
    rw [← ChartModule.Hom.comp_assoc, γ'.comm h, ChartModule.Hom.comp_assoc, γ.comm h,
      ChartModule.Hom.comp_assoc]
  isHom n := (γ'.isHom n).comp (γ.isHom n)

lemma Hom.id_f (S : AdicChartAlgSystem I) (n : ℕ) : (Hom.id S).f n = ChartModule.Hom.id _ := rfl

lemma Hom.comp_f {S S' S'' : AdicChartAlgSystem I} (γ' : Hom S' S'') (γ : Hom S S') (n : ℕ) :
    (γ'.comp γ).f n = (γ'.f n).comp (γ.f n) := rfl

/-! ### Algebraization of morphisms of systems -/

variable [IsNoetherianRing A] [IsAdicComplete I A]
  {S S' : AdicChartAlgSystem I} (γ : Hom S S')
  {N : ChartModule A} [Module.Finite A[X] (Module.AEval' N.x0)]
  [Module.Finite A[X] (Module.AEval' N.x1)] {B : AlgStr N} {α : ∀ n, ChartModule.Hom N (S.M n)}
  (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)
  (hc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m) (hB : ∀ n, B.IsHom (S.alg n) (α n))
  {N' : ChartModule A} [Module.Finite A[X] (Module.AEval' N'.x0)]
  [Module.Finite A[X] (Module.AEval' N'.x1)] {B' : AlgStr N'}
  {α' : ∀ n, ChartModule.Hom N' (S'.M n)}
  (hα' : ∀ n, Function.Surjective (α' n).f0 ∧ Function.Surjective (α' n).f1 ∧
    LinearMap.ker (α' n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α' n).f1 = I ^ n • ⊤)
  (hc' : ∀ m n (h : m ≤ n), (S'.tr h).comp (α' n) = α' m) (hB' : ∀ n, B'.IsHom (S'.alg n) (α' n))

include hc hB hα' hc' hB' in
/-- **Algebraization of morphisms of systems**: a morphism `γ : S → S'` of adic systems of chart
algebras is the system of reductions of a morphism of chart algebras between algebraizations. -/
theorem exists_isHom_of_hom :
    ∃ ψ : ChartModule.Hom N N', (∀ n, (α' n).comp ψ = (γ.f n).comp (α n)) ∧ B.IsHom B' ψ :=
  S'.exists_isHom_of_system hα' hc' hB' B (fun n ↦ (γ.f n).comp (α n))
    (fun m n h ↦ by rw [← ChartModule.Hom.comp_assoc, γ.comm h, ChartModule.Hom.comp_assoc, hc])
    (fun n ↦ (γ.isHom n).comp (hB n))

/-- **The algebraization of a morphism of systems** `γ : S → S'`: the morphism `N → N'` of the
algebraizations with reductions `γ`. -/
noncomputable def algHom : ChartModule.Hom N N' :=
  (exists_isHom_of_hom γ hc hB hα' hc' hB').choose

lemma comp_algHom (n : ℕ) :
    (α' n).comp (algHom γ hc hB hα' hc' hB') = (γ.f n).comp (α n) :=
  (exists_isHom_of_hom γ hc hB hα' hc' hB').choose_spec.1 n

/-- The algebraization of a morphism of systems is a morphism of chart algebras. -/
lemma isHom_algHom : B.IsHom B' (algHom γ hc hB hα' hc' hB') :=
  (exists_isHom_of_hom γ hc hB hα' hc' hB').choose_spec.2

include hα' in
/-- **Uniqueness**: a morphism `N → N'` with reductions `γ` is the algebraization of `γ`. -/
lemma eq_algHom (ψ : ChartModule.Hom N N') (hψ : ∀ n, (α' n).comp ψ = (γ.f n).comp (α n)) :
    ψ = algHom γ hc hB hα' hc' hB' :=
  S'.eq_of_comp_eq hα' _ _ fun n ↦ by rw [hψ, comp_algHom]

include hα in
/-- The algebraization of the identity is the identity. -/
lemma algHom_id :
    algHom (Hom.id S) hc hB hα hc hB = ChartModule.Hom.id N :=
  (eq_algHom (Hom.id S) hc hB hα hc hB _ fun n ↦ by
    rw [Hom.id_f, ChartModule.Hom.id_comp, ChartModule.Hom.comp_id]).symm

include hα' in
/-- The algebraization is compatible with composition. -/
lemma algHom_comp {S'' : AdicChartAlgSystem I} (γ' : Hom S' S'')
    {N'' : ChartModule A} [Module.Finite A[X] (Module.AEval' N''.x0)]
    [Module.Finite A[X] (Module.AEval' N''.x1)] {B'' : AlgStr N''}
    {α'' : ∀ n, ChartModule.Hom N'' (S''.M n)}
    (hα'' : ∀ n, Function.Surjective (α'' n).f0 ∧ Function.Surjective (α'' n).f1 ∧
      LinearMap.ker (α'' n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α'' n).f1 = I ^ n • ⊤)
    (hc'' : ∀ m n (h : m ≤ n), (S''.tr h).comp (α'' n) = α'' m)
    (hB'' : ∀ n, B''.IsHom (S''.alg n) (α'' n)) :
    algHom (γ'.comp γ) hc hB hα'' hc'' hB'' =
      (algHom γ' hc' hB' hα'' hc'' hB'').comp (algHom γ hc hB hα' hc' hB') :=
  (eq_algHom (γ'.comp γ) hc hB hα'' hc'' hB'' _ fun n ↦ by
    rw [← ChartModule.Hom.comp_assoc, comp_algHom, ChartModule.Hom.comp_assoc, comp_algHom,
      Hom.comp_f, ChartModule.Hom.comp_assoc]).symm

end AdicChartAlgSystem

end ProjectiveLine

namespace SemistableReduction

open ProjectiveLine

namespace TwoChartTower

variable {A : Type u} [CommRing A] {D D' : ℕ → TwoChartRings A}
  {s : ∀ n, TwoChartMap (D (n + 1)) (D n)} {s' : ∀ n, TwoChartMap (D' (n + 1)) (D' n)}
  (φ : ∀ n, TwoChartMap (D n) (D' n))
  (hφ : ∀ n, (s' n).comp (φ (n + 1)) = (φ n).comp (s n))

include hφ in
/-- **Naturality of the transition maps** of towers of two-chart rings. -/
lemma trLe_comp_toHom {m n : ℕ} (h : m ≤ n) :
    (trLe D' s' h).toHom.comp (φ n).toHom = (φ m).toHom.comp (trLe D s h).toHom := by
  have h0 : ∀ k x, (s' k).f0 ((φ (k + 1)).f0 x) = (φ k).f0 ((s k).f0 x) := fun k x ↦
    congrArg (fun χ : TwoChartMap (D (k + 1)) (D' k) ↦ χ.f0 x) (hφ k)
  have h1 : ∀ k x, (s' k).f1 ((φ (k + 1)).f1 x) = (φ k).f1 ((s k).f1 x) := fun k x ↦
    congrArg (fun χ : TwoChartMap (D (k + 1)) (D' k) ↦ χ.f1 x) (hφ k)
  have h01 : ∀ k x, (s' k).f01 ((φ (k + 1)).f01 x) = (φ k).f01 ((s k).f01 x) := fun k x ↦
    congrArg (fun χ : TwoChartMap (D (k + 1)) (D' k) ↦ χ.f01 x) (hφ k)
  refine ChartModule.Hom.ext' (LinearMap.ext fun x ↦ ?_) (LinearMap.ext fun x ↦ ?_)
    (LinearMap.ext fun x ↦ ?_)
  · exact TowerSystem.trLe_comm (G := fun k ↦ (D k).R0) (H := fun k ↦ (D' k).R0)
      (fun k ↦ (φ k).f0.toRingHom) h0 h x
  · exact TowerSystem.trLe_comm (G := fun k ↦ (D k).R1) (H := fun k ↦ (D' k).R1)
      (fun k ↦ (φ k).f1.toRingHom) h1 h x
  · exact TowerSystem.trLe_comm (G := fun k ↦ (D k).R01) (H := fun k ↦ (D' k).R01)
      (fun k ↦ (φ k).f01.toRingHom) h01 h x

variable (I : Ideal A)
  {hs0 : ∀ n, Function.Surjective (s n).f0} {hs1 : ∀ n, Function.Surjective (s n).f1}
  {hker0 : ∀ n, RingHom.ker (s n).f0 = (I ^ n).map (algebraMap A (D (n + 1)).R0)}
  {hker1 : ∀ n, RingHom.ker (s n).f1 = (I ^ n).map (algebraMap A (D (n + 1)).R1)}
  {hkill0 : ∀ n, (I ^ n).map (algebraMap A (D n).R0) = ⊥}
  {hkill1 : ∀ n, (I ^ n).map (algebraMap A (D n).R1) = ⊥}
  {hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (D n).chartModule.x0)}
  {hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (D n).chartModule.x1)}
  {hs0' : ∀ n, Function.Surjective (s' n).f0} {hs1' : ∀ n, Function.Surjective (s' n).f1}
  {hker0' : ∀ n, RingHom.ker (s' n).f0 = (I ^ n).map (algebraMap A (D' (n + 1)).R0)}
  {hker1' : ∀ n, RingHom.ker (s' n).f1 = (I ^ n).map (algebraMap A (D' (n + 1)).R1)}
  {hkill0' : ∀ n, (I ^ n).map (algebraMap A (D' n).R0) = ⊥}
  {hkill1' : ∀ n, (I ^ n).map (algebraMap A (D' n).R1) = ⊥}
  {hfin0' : ∀ n, Module.Finite A[X] (Module.AEval' (D' n).chartModule.x0)}
  {hfin1' : ∀ n, Module.Finite A[X] (Module.AEval' (D' n).chartModule.x1)}

/-- **A map of towers of two-chart rings is a morphism of the adic systems.** -/
noncomputable def systemHom :
    AdicChartAlgSystem.Hom (system D s I hs0 hs1 hker0 hker1 hkill0 hkill1 hfin0 hfin1)
      (system D' s' I hs0' hs1' hker0' hker1' hkill0' hkill1' hfin0' hfin1') where
  f n := (φ n).toHom
  comm h := trLe_comp_toHom φ hφ h
  isHom n := (φ n).isHom

lemma systemHom_f (n : ℕ) :
    (systemHom φ hφ I (hs0 := hs0) (hs1 := hs1) (hker0 := hker0) (hker1 := hker1)
      (hkill0 := hkill0) (hkill1 := hkill1) (hfin0 := hfin0) (hfin1 := hfin1) (hs0' := hs0')
      (hs1' := hs1') (hker0' := hker0') (hker1' := hker1') (hkill0' := hkill0')
      (hkill1' := hkill1') (hfin0' := hfin0') (hfin1' := hfin1')).f n = (φ n).toHom :=
  rfl

/-! ### Shifted towers -/

variable {E E' : ℕ → TwoChartRings A} {e : ∀ n, TwoChartMap (E (n + 1)) (E n)}
  {e' : ∀ n, TwoChartMap (E' (n + 1)) (E' n)} (χ : ∀ n, TwoChartMap (E n) (E' n))
  (hχ : ∀ n, (e' n).comp (χ (n + 1)) = (χ n).comp (e n))

/-- The map of shifted towers: the identity of the zero rings in front. -/
noncomputable def shiftHom : ∀ n, TwoChartMap (shift E n) (shift E' n)
  | 0 => TwoChartMap.id (zero A)
  | n + 1 => χ n

include hχ in
lemma shiftHom_comm : ∀ n, (shiftMap E' e' n).comp (shiftHom χ (n + 1)) =
    (shiftHom χ n).comp (shiftMap E e n)
  | 0 => TwoChartMap.ext (AlgHom.ext fun _ ↦ rfl) (AlgHom.ext fun _ ↦ rfl)
      (AlgHom.ext fun _ ↦ rfl)
  | n + 1 => hχ n

variable {he0 : ∀ n, Function.Surjective (e n).f0} {he1 : ∀ n, Function.Surjective (e n).f1}
  {hK0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0)}
  {hK1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1)}
  {hL0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥}
  {hL1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥}
  {hF0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0)}
  {hF1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)}
  {he0' : ∀ n, Function.Surjective (e' n).f0} {he1' : ∀ n, Function.Surjective (e' n).f1}
  {hK0' : ∀ n, RingHom.ker (e' n).f0 = (I ^ (n + 1)).map (algebraMap A (E' (n + 1)).R0)}
  {hK1' : ∀ n, RingHom.ker (e' n).f1 = (I ^ (n + 1)).map (algebraMap A (E' (n + 1)).R1)}
  {hL0' : ∀ n, (I ^ (n + 1)).map (algebraMap A (E' n).R0) = ⊥}
  {hL1' : ∀ n, (I ^ (n + 1)).map (algebraMap A (E' n).R1) = ⊥}
  {hF0' : ∀ n, Module.Finite A[X] (Module.AEval' (E' n).chartModule.x0)}
  {hF1' : ∀ n, Module.Finite A[X] (Module.AEval' (E' n).chartModule.x1)}

/-- **A map of towers of two-chart rings with level `n` killed by `Iⁿ⁺¹` is a morphism of the
shifted adic systems** (level `n + 1` of the morphism is `χ n`). -/
noncomputable def systemShiftHom :
    AdicChartAlgSystem.Hom
      (systemShift I E e he0 he1 hK0 hK1 hL0 hL1 hF0 hF1)
      (systemShift I E' e' he0' he1' hK0' hK1' hL0' hL1' hF0' hF1') where
  f n := (shiftHom χ n).toHom
  comm h := trLe_comp_toHom (shiftHom χ) (shiftHom_comm χ hχ) h
  isHom n := (shiftHom χ n).isHom

lemma systemShiftHom_f_succ (n : ℕ) :
    (systemShiftHom I χ hχ (he0 := he0) (he1 := he1) (hK0 := hK0) (hK1 := hK1)
      (hL0 := hL0) (hL1 := hL1) (hF0 := hF0) (hF1 := hF1) (he0' := he0')
      (he1' := he1') (hK0' := hK0') (hK1' := hK1') (hL0' := hL0')
      (hL1' := hL1') (hF0' := hF0') (hF1' := hF1')).f (n + 1) = (χ n).toHom :=
  rfl

end TwoChartTower

end SemistableReduction
