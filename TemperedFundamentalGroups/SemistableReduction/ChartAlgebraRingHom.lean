/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraStructureMap
import TemperedFundamentalGroups.SemistableReduction.TwoChartTower
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Ring maps of chart algebras and the special fibre of an algebraization (Blueprint §12.8, M2.5)

A morphism of chart algebras `φ : M → N` (`AlgStr.IsHom B B' φ`) is a ring map on the rings of
sections over the two charts: `AlgStr.IsHom.ringHom0`, `ringHom1` (with `ringHom0_const0`,
`ringHom0_X0`, …). The `A`-module structure of a chart ring is multiplication by the constants
(`AlgStr.smul_eq_const0_mul`), so `I • ⊤ = I · B₀` (`AlgStr.mem_smul_top_iff0`), and a
chart-surjective morphism with kernels `I • ⊤` induces `B₀ ⧸ I B₀ ≃ B'₀`
(`AlgStr.IsHom.quotEquiv0`).

For two-chart rings `D`, the rings of sections of `D.algStr` are `D.R0`, `D.R1`
(`TwoChartRings.ring0Equiv`, `ring1Equiv`).

Application (`AdicChartAlgSystem.quotEquiv0`): if `(N, B, α)` algebraizes an adic system of chart
algebras `S` (`AdicChartAlgSystem.exists_algebraization`), then `B₀ ⧸ Iⁿ B₀ ≃ (S.alg n).Ring0`;
for the shifted tower `E` of two-chart rings (`TwoChartTower.systemShift`),
`B₀ ⧸ Iⁿ⁺¹ B₀ ≃ (E n).R0` (`TwoChartTower.quotEquivShift0`, `quotEquivShift1`) — in particular
the special fibre `B₀ ⧸ I B₀` of the algebraized covering is the level-`0` ring `(E 0).R0`.
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

open BTensor

variable {A : Type u} [CommRing A]

namespace AlgStr

variable {M N : ChartModule A} (B : AlgStr M) (B' : AlgStr N)

/-- An element of `M₀` as an element of the ring `B₀`. -/
def toRing0 (m : M.M0) : B.Ring0 := m

/-- An element of `M₁` as an element of the ring `B₁`. -/
def toRing1 (m : M.M1) : B.Ring1 := m

/-- An element of the ring `B₀` as an element of `M₀`. -/
def ofRing0 (m : B.Ring0) : M.M0 := m

/-- An element of the ring `B₁` as an element of `M₁`. -/
def ofRing1 (m : B.Ring1) : M.M1 := m

/-- The `A`-module structure of `B₀` is multiplication by the constants. -/
lemma toRing0_smul (a : A) (m : M.M0) : B.toRing0 (a • m) = B.const0 a * B.toRing0 m := by
  change _ = B.mul.f0 (tm M.x0 M.x0 (a • B.one.1.1) m)
  rw [tm_smul_left, map_smul, B.one_mul0]
  rfl

/-- The `A`-module structure of `B₁` is multiplication by the constants. -/
lemma toRing1_smul (a : A) (m : M.M1) : B.toRing1 (a • m) = B.const1 a * B.toRing1 m := by
  change _ = B.mul.f1 (tm M.x1 M.x1 (a • B.one.1.2) m)
  rw [tm_smul_left, map_smul, B.one_mul1]
  rfl

/-- Multiplication by `r ∈ B₀`, an `A`-linear map of `M₀`. -/
noncomputable def mulLin0 (r : B.Ring0) : M.M0 →ₗ[A] M.M0 :=
  B.mul.f0 ∘ₗ (BTensor.tmBil M.x0 M.x0 r)

/-- Multiplication by `r ∈ B₁`, an `A`-linear map of `M₁`. -/
noncomputable def mulLin1 (r : B.Ring1) : M.M1 →ₗ[A] M.M1 :=
  B.mul.f1 ∘ₗ (BTensor.tmBil M.x1 M.x1 r)

/-- **`I • ⊤ = I B₀`** on the first chart. -/
lemma mem_smul_top_iff0 (I : Ideal A) (m : B.Ring0) :
    B.ofRing0 m ∈ I • (⊤ : Submodule A M.M0) ↔ m ∈ I.map B.const0 := by
  constructor
  · intro hm
    let P : Submodule A M.M0 :=
      { carrier := {x | B.toRing0 x ∈ I.map B.const0}
        add_mem' := fun {x y} hx hy ↦ by
          have hx' : B.toRing0 x ∈ I.map B.const0 := hx
          have hy' : B.toRing0 y ∈ I.map B.const0 := hy
          change B.toRing0 x + B.toRing0 y ∈ I.map B.const0
          exact Ideal.add_mem _ hx' hy'
        zero_mem' := by
          change B.toRing0 0 ∈ I.map B.const0
          exact (show B.toRing0 0 = 0 from rfl) ▸ Ideal.zero_mem _
        smul_mem' := fun a x hx ↦ by
          change B.toRing0 (a • x) ∈ _
          rw [toRing0_smul]
          have hx' : B.toRing0 x ∈ I.map B.const0 := hx
          exact Ideal.mul_mem_left _ (B.const0 a) hx' }
    have hle : I • (⊤ : Submodule A M.M0) ≤ P := Submodule.smul_le.2 fun a ha x _ ↦ by
      change B.toRing0 (a • x) ∈ I.map B.const0
      rw [toRing0_smul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    exact hle hm
  · intro hm
    let Q : Ideal B.Ring0 :=
      { carrier := {x | B.ofRing0 x ∈ I • (⊤ : Submodule A M.M0)}
        add_mem' := fun {x y} hx hy ↦ by
          have hx' : B.ofRing0 x ∈ I • (⊤ : Submodule A M.M0) := hx
          have hy' : B.ofRing0 y ∈ I • (⊤ : Submodule A M.M0) := hy
          change B.ofRing0 x + B.ofRing0 y ∈ I • (⊤ : Submodule A M.M0)
          exact Submodule.add_mem _ hx' hy'
        zero_mem' := by
          change B.ofRing0 0 ∈ I • (⊤ : Submodule A M.M0)
          exact Submodule.zero_mem _
        smul_mem' := fun r x hx ↦ smul_top_le_comap I (B.mulLin0 r) hx }
    have hle : I.map B.const0 ≤ Q := Ideal.map_le_iff_le_comap.2 fun a ha ↦
      Submodule.smul_mem_smul ha Submodule.mem_top
    exact hle hm

/-- **`I • ⊤ = I B₁`** on the second chart. -/
lemma mem_smul_top_iff1 (I : Ideal A) (m : B.Ring1) :
    B.ofRing1 m ∈ I • (⊤ : Submodule A M.M1) ↔ m ∈ I.map B.const1 := by
  constructor
  · intro hm
    let P : Submodule A M.M1 :=
      { carrier := {x | B.toRing1 x ∈ I.map B.const1}
        add_mem' := fun {x y} hx hy ↦ by
          have hx' : B.toRing1 x ∈ I.map B.const1 := hx
          have hy' : B.toRing1 y ∈ I.map B.const1 := hy
          change B.toRing1 x + B.toRing1 y ∈ I.map B.const1
          exact Ideal.add_mem _ hx' hy'
        zero_mem' := by
          change B.toRing1 0 ∈ I.map B.const1
          exact (show B.toRing1 0 = 0 from rfl) ▸ Ideal.zero_mem _
        smul_mem' := fun a x hx ↦ by
          change B.toRing1 (a • x) ∈ _
          rw [toRing1_smul]
          have hx' : B.toRing1 x ∈ I.map B.const1 := hx
          exact Ideal.mul_mem_left _ (B.const1 a) hx' }
    have hle : I • (⊤ : Submodule A M.M1) ≤ P := Submodule.smul_le.2 fun a ha x _ ↦ by
      change B.toRing1 (a • x) ∈ I.map B.const1
      rw [toRing1_smul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)
    exact hle hm
  · intro hm
    let Q : Ideal B.Ring1 :=
      { carrier := {x | B.ofRing1 x ∈ I • (⊤ : Submodule A M.M1)}
        add_mem' := fun {x y} hx hy ↦ by
          have hx' : B.ofRing1 x ∈ I • (⊤ : Submodule A M.M1) := hx
          have hy' : B.ofRing1 y ∈ I • (⊤ : Submodule A M.M1) := hy
          change B.ofRing1 x + B.ofRing1 y ∈ I • (⊤ : Submodule A M.M1)
          exact Submodule.add_mem _ hx' hy'
        zero_mem' := by
          change B.ofRing1 0 ∈ I • (⊤ : Submodule A M.M1)
          exact Submodule.zero_mem _
        smul_mem' := fun r x hx ↦ smul_top_le_comap I (B.mulLin1 r) hx }
    have hle : I.map B.const1 ≤ Q := Ideal.map_le_iff_le_comap.2 fun a ha ↦
      Submodule.smul_mem_smul ha Submodule.mem_top
    exact hle hm

/-- **Constants regular on a flat chart algebra**: if `M₀` is flat over `A[X]` and `a` is a
nonzerodivisor of `A[X]`, then `a` is a nonzerodivisor of `B₀` (e.g. `a = ϖ` for the flat
algebraization of a covering over a DVR). -/
lemma const0_mem_nonZeroDivisors [Module.Flat A[X] (Module.AEval' M.x0)] {a : A}
    (ha : (Polynomial.C a : A[X]) ∈ nonZeroDivisors A[X]) :
    B.const0 a ∈ nonZeroDivisors B.Ring0 := by
  have hreg : IsSMulRegular (Module.AEval' M.x0) (Polynomial.C a) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  refine mem_nonZeroDivisors_iff_right.2 fun m hm ↦ ?_
  rw [mul_comm] at hm
  have h1 : a • B.ofRing0 m = 0 := by
    have : B.toRing0 (a • B.ofRing0 m) = B.const0 a * m := B.toRing0_smul a (B.ofRing0 m)
    rw [hm] at this
    exact this
  have h2 : (Polynomial.C a : A[X]) • Module.AEval'.of M.x0 (B.ofRing0 m) =
      (Polynomial.C a : A[X]) • 0 := by
    rw [smul_zero, ← Polynomial.algebraMap_eq, algebraMap_smul, ← map_smul, h1, map_zero]
  exact (Module.AEval'.of M.x0).injective ((hreg h2).trans (map_zero _).symm)

variable {B B'} {φ : Hom M N}

/-- **A morphism of chart algebras is a ring map on the first chart.** -/
noncomputable def IsHom.ringHom0 (h : B.IsHom B' φ) : B.Ring0 →+* B'.Ring0 where
  toFun := φ.f0
  map_one' := congrArg (fun x : N.H0 ↦ x.1.1) h.2
  map_mul' a b := by
    have := Hom.f0_eq_of_eq h.1 (tm M.x0 M.x0 a b)
    change φ.f0 (B.mul.f0 (tm M.x0 M.x0 a b)) = B'.mul.f0 (tm N.x0 N.x0 (φ.f0 a) (φ.f0 b))
    rw [← Hom.tensor_f0_tm]
    exact this
  map_zero' := map_zero φ.f0
  map_add' := map_add φ.f0

/-- **A morphism of chart algebras is a ring map on the second chart.** -/
noncomputable def IsHom.ringHom1 (h : B.IsHom B' φ) : B.Ring1 →+* B'.Ring1 where
  toFun := φ.f1
  map_one' := congrArg (fun x : N.H0 ↦ x.1.2) h.2
  map_mul' a b := by
    have := Hom.f1_eq_of_eq h.1 (tm M.x1 M.x1 a b)
    change φ.f1 (B.mul.f1 (tm M.x1 M.x1 a b)) = B'.mul.f1 (tm N.x1 N.x1 (φ.f1 a) (φ.f1 b))
    rw [← Hom.tensor_f1_tm]
    exact this
  map_zero' := map_zero φ.f1
  map_add' := map_add φ.f1

lemma IsHom.ringHom0_apply (h : B.IsHom B' φ) (a : B.Ring0) : h.ringHom0 a = φ.f0 a := rfl

lemma IsHom.ringHom1_apply (h : B.IsHom B' φ) (a : B.Ring1) : h.ringHom1 a = φ.f1 a := rfl

lemma IsHom.ringHom0_const0 (h : B.IsHom B' φ) (a : A) : h.ringHom0 (B.const0 a) = B'.const0 a := by
  change φ.f0 (a • B.one.1.1) = a • B'.one.1.1
  rw [map_smul]
  exact congrArg (a • ·) (h.ringHom0.map_one)

lemma IsHom.ringHom1_const1 (h : B.IsHom B' φ) (a : A) : h.ringHom1 (B.const1 a) = B'.const1 a := by
  change φ.f1 (a • B.one.1.2) = a • B'.one.1.2
  rw [map_smul]
  exact congrArg (a • ·) (h.ringHom1.map_one)

lemma IsHom.ringHom0_X0 (h : B.IsHom B' φ) : h.ringHom0 B.X0 = B'.X0 := by
  change φ.f0 (M.x0 B.one.1.1) = N.x0 B'.one.1.1
  rw [φ.comm_x0]
  exact congrArg N.x0 (h.ringHom0.map_one)

lemma IsHom.ringHom1_X1 (h : B.IsHom B' φ) : h.ringHom1 B.X1 = B'.X1 := by
  change φ.f1 (M.x1 B.one.1.2) = N.x1 B'.one.1.2
  rw [φ.comm_x1]
  exact congrArg N.x1 (h.ringHom1.map_one)

lemma IsHom.ringHom0_polyHom0 (h : B.IsHom B' φ) (p : A[X]) :
    h.ringHom0 (B.polyHom0 p) = B'.polyHom0 p := by
  simp only [polyHom0, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, h.ringHom0_X0]
  congr 1
  ext a
  exact h.ringHom0_const0 a

lemma IsHom.ringHom1_polyHom1 (h : B.IsHom B' φ) (p : A[X]) :
    h.ringHom1 (B.polyHom1 p) = B'.polyHom1 p := by
  simp only [polyHom1, Polynomial.coe_eval₂RingHom, Polynomial.hom_eval₂, h.ringHom1_X1]
  congr 1
  ext a
  exact h.ringHom1_const1 a

/-- The kernel of the ring map on the first chart. -/
lemma IsHom.ker_ringHom0 (h : B.IsHom B' φ) {I : Ideal A}
    (hk : LinearMap.ker φ.f0 = I • ⊤) : RingHom.ker h.ringHom0 = I.map B.const0 := by
  ext m
  rw [RingHom.mem_ker, ← B.mem_smul_top_iff0, ← hk, LinearMap.mem_ker]
  rfl

/-- The kernel of the ring map on the second chart. -/
lemma IsHom.ker_ringHom1 (h : B.IsHom B' φ) {I : Ideal A}
    (hk : LinearMap.ker φ.f1 = I • ⊤) : RingHom.ker h.ringHom1 = I.map B.const1 := by
  ext m
  rw [RingHom.mem_ker, ← B.mem_smul_top_iff1, ← hk, LinearMap.mem_ker]
  rfl

/-- **`B₀ ⧸ I B₀ ≃ B'₀`** for a morphism of chart algebras, surjective with kernel `I • ⊤`. -/
noncomputable def IsHom.quotEquiv0 (h : B.IsHom B' φ) {I : Ideal A}
    (hs : Function.Surjective φ.f0) (hk : LinearMap.ker φ.f0 = I • ⊤) :
    B.Ring0 ⧸ I.map B.const0 ≃+* B'.Ring0 :=
  (Ideal.quotEquivOfEq (h.ker_ringHom0 hk).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := h.ringHom0) hs)

/-- **`B₁ ⧸ I B₁ ≃ B'₁`** for a morphism of chart algebras, surjective with kernel `I • ⊤`. -/
noncomputable def IsHom.quotEquiv1 (h : B.IsHom B' φ) {I : Ideal A}
    (hs : Function.Surjective φ.f1) (hk : LinearMap.ker φ.f1 = I • ⊤) :
    B.Ring1 ⧸ I.map B.const1 ≃+* B'.Ring1 :=
  (Ideal.quotEquivOfEq (h.ker_ringHom1 hk).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := h.ringHom1) hs)

lemma IsHom.quotEquiv0_mk (h : B.IsHom B' φ) {I : Ideal A}
    (hs : Function.Surjective φ.f0) (hk : LinearMap.ker φ.f0 = I • ⊤) (a : B.Ring0) :
    h.quotEquiv0 hs hk (Ideal.Quotient.mk _ a) = φ.f0 a := rfl

lemma IsHom.quotEquiv1_mk (h : B.IsHom B' φ) {I : Ideal A}
    (hs : Function.Surjective φ.f1) (hk : LinearMap.ker φ.f1 = I • ⊤) (a : B.Ring1) :
    h.quotEquiv1 hs hk (Ideal.Quotient.mk _ a) = φ.f1 a := rfl

end AlgStr

end ChartModule

namespace TwoChartRings

open ChartModule

variable {A : Type u} [CommRing A] (D : TwoChartRings A)

noncomputable instance : CommRing D.algStr.Ring0 := AlgStr.instCommRingRing0 _

noncomputable instance : CommRing D.algStr.Ring1 := AlgStr.instCommRingRing1 _

/-- **The ring of sections of `D.algStr` over the first chart is `D.R0`.** -/
noncomputable def ring0Equiv : D.algStr.Ring0 ≃+* D.R0 where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := bmul_tm A D.x a b
  map_add' _ _ := rfl

/-- **The ring of sections of `D.algStr` over the second chart is `D.R1`.** -/
noncomputable def ring1Equiv : D.algStr.Ring1 ≃+* D.R1 where
  toFun a := a
  invFun a := a
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' a b := bmul_tm A D.y a b
  map_add' _ _ := rfl

lemma ring0Equiv_const0 (a : A) : D.ring0Equiv (D.algStr.const0 a) = algebraMap A D.R0 a :=
  (Algebra.algebraMap_eq_smul_one a).symm

lemma ring1Equiv_const1 (a : A) : D.ring1Equiv (D.algStr.const1 a) = algebraMap A D.R1 a :=
  (Algebra.algebraMap_eq_smul_one a).symm

lemma ring0Equiv_X0 : D.ring0Equiv D.algStr.X0 = D.x := mul_one D.x

lemma ring1Equiv_X1 : D.ring1Equiv D.algStr.X1 = D.y := mul_one D.y

end TwoChartRings

namespace AdicChartAlgSystem

open ChartModule

variable {A : Type u} [CommRing A] {I : Ideal A} (S : AdicChartAlgSystem I) {N : ChartModule A}
  {B : AlgStr N} {α : ∀ n, Hom N (S.M n)}

/-- **The reductions of an algebraization are its levels**: for `(N, B, α)` as produced by
`exists_algebraization`, `B₀ ⧸ Iⁿ B₀ ≃ (S.alg n).Ring0`. -/
noncomputable def quotEquiv0 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) (n : ℕ) :
    B.Ring0 ⧸ (I ^ n).map B.const0 ≃+* (S.alg n).Ring0 :=
  (hB n).quotEquiv0 (hα n).1 (hα n).2.2.1

/-- **The reductions of an algebraization are its levels** (second chart). -/
noncomputable def quotEquiv1 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) (n : ℕ) :
    B.Ring1 ⧸ (I ^ n).map B.const1 ≃+* (S.alg n).Ring1 :=
  (hB n).quotEquiv1 (hα n).2.1 (hα n).2.2.2

end AdicChartAlgSystem

end ProjectiveLine

namespace SemistableReduction

namespace TwoChartTower

open ProjectiveLine ProjectiveLine.ChartModule

variable {A : Type u} [CommRing A] {I : Ideal A} {E : ℕ → TwoChartRings A}
  {e : ∀ n, TwoChartMap (E (n + 1)) (E n)}
  {he0 : ∀ n, Function.Surjective (e n).f0} {he1 : ∀ n, Function.Surjective (e n).f1}
  {hker0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0)}
  {hker1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1)}
  {hkill0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥}
  {hkill1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥}
  {hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0)}
  {hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)}
  {N : ChartModule A} {B : AlgStr N}
  {α : ∀ n, Hom N ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).M n)}

/-- **The algebraization of a tower of two-chart rings reduces to its levels** (first chart):
`B₀ ⧸ Iⁿ⁺¹ B₀ ≃ (E n).R0`; for `n = 0` the special fibre of the algebraized covering is the
level-`0` ring. -/
noncomputable def quotEquivShift0 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n)) (n : ℕ) :
    B.Ring0 ⧸ (I ^ (n + 1)).map B.const0 ≃+* (E n).R0 :=
  (AdicChartAlgSystem.quotEquiv0 _ hα hB (n + 1)).trans (TwoChartRings.ring0Equiv (E n))

/-- **The algebraization of a tower of two-chart rings reduces to its levels** (second chart). -/
noncomputable def quotEquivShift1 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n)) (n : ℕ) :
    B.Ring1 ⧸ (I ^ (n + 1)).map B.const1 ≃+* (E n).R1 :=
  (AdicChartAlgSystem.quotEquiv1 _ hα hB (n + 1)).trans (TwoChartRings.ring1Equiv (E n))

lemma quotEquivShift0_mk (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n)) (n : ℕ)
    (a : B.Ring0) :
    quotEquivShift0 hα hB n (Ideal.Quotient.mk _ a) = (α (n + 1)).f0 a := rfl

lemma quotEquivShift0_const0 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n)) (n : ℕ)
    (a : A) :
    quotEquivShift0 hα hB n (Ideal.Quotient.mk _ (B.const0 a)) = algebraMap A (E n).R0 a :=
  ((hB (n + 1)).ringHom0_const0 a).trans ((E n).ring0Equiv_const0 a)

end TwoChartTower

end SemistableReduction
