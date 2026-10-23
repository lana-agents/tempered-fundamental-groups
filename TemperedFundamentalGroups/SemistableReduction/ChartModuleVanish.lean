/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleFF
import FormalSchemes.ChartModuleAdic

/-!
# Morphisms of coherent modules on `ℙ¹_A` vanishing modulo all `Iⁿ` (Blueprint §12.8, M2.5 (f))

Over a Noetherian `I`-adically complete ring `A`, a morphism `φ : N → N'` of coherent chart
modules whose image lies in `Iⁿ N'` for every `n` (on both charts) is zero
(**`ProjectiveLine.ChartModule.Hom.eq_zero_of_forall_mem`**): its reductions modulo all `Iⁿ`
vanish, and morphisms are detected by their reductions (`ChartModule.toHomSystem_bijective`,
Stacks 0883 for `ℙ¹_A`). Chart-wise this fails (`O[X]/(ϖX − 1)`); it is the step from
the formal neighbourhood of the special fibre to the generic fibre.

Applications (`c ∈ A`):

* **`ChartModule.smul_eq_zero_of_forall_mem`**: if `c N ⊆ Iⁿ N` for all `n`, then `c N = 0`;
* **`ChartModule.smul_x0_eq_zero_of_forall_mem`**: if `c X N₀ ⊆ Iⁿ N₀` and `c N₁ ⊆ Iⁿ N₁` for all
  `n`, then `c X N₀ = 0` and `c N₁ = 0` (via the morphism `ChartModule.xHom : N → N(1)`,
  multiplication by the section `X` of `𝒪(1)`, which is `1` on the second chart).
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A]

/-- The zero morphism of chart modules. -/
def Hom.zero (N N' : ChartModule A) : Hom N N' where
  f0 := 0
  f1 := 0
  f01 := 0
  comm_x0 _ := by simp
  comm_x1 _ := by simp
  comm_t _ := by simp
  comm_r0 _ := by simp
  comm_r1 _ := by simp

/-- A morphism of chart modules multiplied by a constant. -/
def Hom.smul {N N' : ChartModule A} (c : A) (φ : Hom N N') : Hom N N' where
  f0 := c • φ.f0
  f1 := c • φ.f1
  f01 := c • φ.f01
  comm_x0 m := by simp [φ.comm_x0]
  comm_x1 m := by simp [φ.comm_x1]
  comm_t z := by simp [φ.comm_t]
  comm_r0 m := by simp [φ.comm_r0]
  comm_r1 m := by simp [φ.comm_r1]

/-- **Multiplication by the section `X` of `𝒪(1)`**: `N → N(1)`, `X` on the first chart, `1` on
the second chart and `T` on the overlap. -/
def xHom (N : ChartModule A) : Hom N (N.twist 1) where
  f0 := N.x0
  f1 := LinearMap.id
  f01 := N.t.toLinearMap
  comm_x0 _ := rfl
  comm_x1 _ := rfl
  comm_t _ := rfl
  comm_r0 m := (N.r0_x0 m).symm
  comm_r1 m := by
    change N.t (N.r1 m) = (N.t ^ (1 : ℤ)) (N.r1 m)
    rw [zpow_one]

variable (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A] {N N' : ChartModule A}
  [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]
  [Module.Finite A[X] (Module.AEval' N'.x0)] [Module.Finite A[X] (Module.AEval' N'.x1)]

/-- **A morphism of coherent chart modules vanishing modulo all `Iⁿ` is zero.** -/
theorem Hom.eq_zero_of_forall_mem (φ : Hom N N')
    (h0 : ∀ n m, φ.f0 m ∈ I ^ n • (⊤ : Submodule A N'.M0))
    (h1 : ∀ n m, φ.f1 m ∈ I ^ n • (⊤ : Submodule A N'.M1)) :
    (∀ m, φ.f0 m = 0) ∧ ∀ m, φ.f1 m = 0 := by
  have heq : φ = Hom.zero N N' := by
    refine (toHomSystem_bijective I N N').1 (Subtype.ext (funext fun n ↦ ?_))
    have e0 : ((N'.quotHom (I ^ n)).comp φ).f0 = ((N'.quotHom (I ^ n)).comp (Hom.zero N N')).f0 :=
      LinearMap.ext fun m ↦ by
        change Submodule.Quotient.mk (φ.f0 m) = Submodule.Quotient.mk 0
        rw [Submodule.Quotient.eq, sub_zero]
        exact h0 n m
    have e1 : ((N'.quotHom (I ^ n)).comp φ).f1 = ((N'.quotHom (I ^ n)).comp (Hom.zero N N')).f1 :=
      LinearMap.ext fun m ↦ by
        change Submodule.Quotient.mk (φ.f1 m) = Submodule.Quotient.mk 0
        rw [Submodule.Quotient.eq, sub_zero]
        exact h1 n m
    exact Hom.ext' e0 e1 (Hom.f01_eq_of_f0_eq e0)
  exact ⟨fun m ↦ congrArg (fun ψ : Hom N N' ↦ ψ.f0 m) heq,
    fun m ↦ congrArg (fun ψ : Hom N N' ↦ ψ.f1 m) heq⟩

omit [Module.Finite A[X] (Module.AEval' N'.x0)] [Module.Finite A[X] (Module.AEval' N'.x1)] in
/-- **A constant killing a coherent chart module modulo all `Iⁿ` kills it.** -/
theorem smul_eq_zero_of_forall_mem {c : A}
    (h0 : ∀ n (m : N.M0), c • m ∈ I ^ n • (⊤ : Submodule A N.M0))
    (h1 : ∀ n (m : N.M1), c • m ∈ I ^ n • (⊤ : Submodule A N.M1)) :
    (∀ m : N.M0, c • m = 0) ∧ ∀ m : N.M1, c • m = 0 :=
  Hom.eq_zero_of_forall_mem I ((Hom.id N).smul c) h0 h1

omit [Module.Finite A[X] (Module.AEval' N'.x0)] [Module.Finite A[X] (Module.AEval' N'.x1)] in
/-- **A constant killing `X N₀` and `N₁` modulo all `Iⁿ`** (a coherent module on `ℙ¹_A` whose
first chart is killed by `c X` and whose second chart is killed by `c`, modulo all `Iⁿ`): then
`c X N₀ = 0` and `c N₁ = 0`. -/
theorem smul_x0_eq_zero_of_forall_mem {c : A}
    (h0 : ∀ n (m : N.M0), c • N.x0 m ∈ I ^ n • (⊤ : Submodule A N.M0))
    (h1 : ∀ n (m : N.M1), c • m ∈ I ^ n • (⊤ : Submodule A N.M1)) :
    (∀ m : N.M0, c • N.x0 m = 0) ∧ ∀ m : N.M1, c • m = 0 := by
  haveI : Module.Finite A[X] (Module.AEval' (N.twist 1).x0) :=
    inferInstanceAs (Module.Finite A[X] (Module.AEval' N.x0))
  haveI : Module.Finite A[X] (Module.AEval' (N.twist 1).x1) :=
    inferInstanceAs (Module.Finite A[X] (Module.AEval' N.x1))
  exact Hom.eq_zero_of_forall_mem (N' := N.twist 1) I ((xHom N).smul c) h0 h1

end ChartModule

end ProjectiveLine
