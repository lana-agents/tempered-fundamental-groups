/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleAdic

/-!
# Nakayama's lemma for coherent modules on `ℙ¹_A` (Blueprint §12.8, M2.5)

Let `A` be Noetherian and `I`-adically complete. A coherent module `N` on `ℙ¹_A` (a chart module,
finite over `A[X]` on both charts) with `I N = N` is zero
(`ProjectiveLine.ChartModule.subsingleton_of_smul_top_eq_top`).

This is the global (proper) form of Nakayama: chart-wise it fails (`O[X]/(ϖX − 1)` is killed by
nothing in `(ϖ)` but equals `ϖ` times itself), and it holds on `ℙ¹_A` because every closed point of
the generic fibre specializes into the special fibre. Proof: `I N = N` gives `Iⁿ N = N`, so all
reductions `N / Iⁿ N` vanish, and by the full faithfulness of completion
(`ChartModule.toHomSystem_bijective`, Stacks 0883 for `ℙ¹_A`) the identity of `N` equals the zero
morphism.

Use in M2.5: a coherent sheaf on the covering `𝒴` (e.g. `ϖᵏ Ω_{𝒴/𝒳}` or the cokernel of
`𝒪_𝒴 → 𝒪_𝒴[1/ϖ]`-type comparison sheaves) which is `ϖ`-divisible vanishes — the step from the
formal-local structure along the special fibre to the generic fibre.
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] (I : Ideal A) (N : ChartModule A)

/-- The zero endomorphism of a chart module. -/
def zeroHom : Hom N N where
  f0 := 0
  f1 := 0
  f01 := 0
  comm_x0 _ := by simp
  comm_x1 _ := by simp
  comm_t _ := by simp
  comm_r0 _ := by simp
  comm_r1 _ := by simp

lemma smul_top_eq_top_pow {M : Type u} [AddCommGroup M] [Module A M]
    (h : I • (⊤ : Submodule A M) = ⊤) (n : ℕ) : I ^ n • (⊤ : Submodule A M) = ⊤ := by
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  | succ n ih => rw [pow_succ, Submodule.mul_smul, h, ih]

/-- `I N₀ = N₀` gives `I N₀₁ = N₀₁` (the overlap is a localization of `N₀`). -/
lemma smul_top_eq_top_overlap (h0 : I • (⊤ : Submodule A N.M0) = ⊤) :
    I • (⊤ : Submodule A N.M01) = ⊤ := by
  refine eq_top_iff.2 fun z _ ↦ ?_
  obtain ⟨m, k, hk⟩ := N.exists_r0 z
  have hm : m ∈ I • (⊤ : Submodule A N.M0) := by rw [h0]; exact Submodule.mem_top
  have h1 : N.r0 m ∈ I • (⊤ : Submodule A N.M01) := smul_top_le_comap I N.r0 hm
  have h2 := smul_top_le_comap I ((N.t ^ k).symm : N.M01 →ₗ[A] N.M01) h1
  rw [Submodule.mem_comap, ← hk] at h2
  simpa using h2

variable [IsNoetherianRing A] [IsAdicComplete I A]
  [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]

/-- **Nakayama's lemma on `ℙ¹_A`**: over a Noetherian `I`-adically complete ring, a coherent chart
module with `I N = N` on both charts is zero. -/
theorem subsingleton_of_smul_top_eq_top (h0 : I • (⊤ : Submodule A N.M0) = ⊤)
    (h1 : I • (⊤ : Submodule A N.M1) = ⊤) : Subsingleton N.M0 ∧ Subsingleton N.M1 := by
  have h01 := N.smul_top_eq_top_overlap I h0
  have hq0 : ∀ n, Subsingleton (N.quot (I ^ n)).M0 := fun n ↦
    Submodule.Quotient.subsingleton_iff.2 (smul_top_eq_top_pow I h0 n)
  have hq1 : ∀ n, Subsingleton (N.quot (I ^ n)).M1 := fun n ↦
    Submodule.Quotient.subsingleton_iff.2 (smul_top_eq_top_pow I h1 n)
  have hq01 : ∀ n, Subsingleton (N.quot (I ^ n)).M01 := fun n ↦
    Submodule.Quotient.subsingleton_iff.2 (smul_top_eq_top_pow I h01 n)
  have heq : Hom.id N = N.zeroHom := (toHomSystem_bijective I N N).1 <| Subtype.ext <| funext
    fun n ↦ Hom.ext' (LinearMap.ext fun _ ↦ (hq0 n).elim _ _)
      (LinearMap.ext fun _ ↦ (hq1 n).elim _ _) (LinearMap.ext fun _ ↦ (hq01 n).elim _ _)
  exact ⟨⟨fun a b ↦ (congrArg (fun φ : Hom N N ↦ φ.f0 a) heq).trans
      (congrArg (fun φ : Hom N N ↦ φ.f0 b) heq).symm⟩,
    ⟨fun a b ↦ (congrArg (fun φ : Hom N N ↦ φ.f1 a) heq).trans
      (congrArg (fun φ : Hom N N ↦ φ.f1 b) heq).symm⟩⟩

end ChartModule

end ProjectiveLine
