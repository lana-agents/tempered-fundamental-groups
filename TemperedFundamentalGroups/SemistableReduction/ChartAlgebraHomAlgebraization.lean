/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleAlgebra

/-!
# Algebraization of morphisms of chart algebras (Blueprint §12.8, M2.5)

Let `A` be Noetherian and `I`-adically complete, `S` an adic system of chart algebras on `ℙ¹_A`
and `(N, B, α)` an algebraization of `S` (`AdicChartAlgSystem.exists_algebraization`). Then

* morphisms `P → N` out of a coherent chart module are detected by their reductions `α n ∘ φ`
  (`AdicChartAlgSystem.eq_of_comp_eq`), and global sections of `N` by their reductions
  (`AdicChartAlgSystem.eq_of_mapH0_eq`);
* a compatible system of morphisms of chart algebras `β n : P → S.M n` out of a coherent chart
  algebra `P` is the system of reductions of a unique morphism of chart algebras `ψ : P → N`
  (`AdicChartAlgSystem.exists_isHom_of_system`).

Use in M2.5: the structure map `𝒴 → 𝒳` of the algebraized covering over the model `𝒳` (both
coherent algebras on `ℙ¹_O`): the levels of the covering are algebras over the levels of `𝒳`, and
these structure maps algebraize (Stacks 0883 for `ℙ¹_A`, via `ChartModule.toHomSystem_bijective`).
-/

universe u

open Polynomial

namespace ProjectiveLine

open ChartModule BTensor

namespace AdicChartAlgSystem

variable {A : Type u} [CommRing A] {I : Ideal A}
  (S : AdicChartAlgSystem I) {N : ChartModule A}
  {α : ∀ n, Hom N (S.M n)}
  (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)

/-- `N / Iⁿ N` receives `S.M n`: the inverse of the reduction `α n`. -/
noncomputable def toQuot (n : ℕ) : Hom (S.M n) (N.quot (I ^ n)) :=
  (α n).descend (hα n).1 (hα n).2.1 (N.quotHom (I ^ n))
    (by rw [(hα n).2.2.1]; exact (Submodule.ker_mkQ _).ge)
    (by rw [(hα n).2.2.2]; exact (Submodule.ker_mkQ _).ge)

lemma toQuot_comp (n : ℕ) : (S.toQuot hα n).comp (α n) = N.quotHom (I ^ n) :=
  Hom.descend_comp _ _ _ _ _ _

/-- `S.M n` receives `N / Iⁿ N`. -/
noncomputable def ofQuot (n : ℕ) : Hom (N.quot (I ^ n)) (S.M n) :=
  (N.quotHom (I ^ n)).descend (Submodule.mkQ_surjective _) (Submodule.mkQ_surjective _) (α n)
    (by
      change LinearMap.ker (Submodule.mkQ _) ≤ _
      rw [Submodule.ker_mkQ, (hα n).2.2.1])
    (by
      change LinearMap.ker (Submodule.mkQ _) ≤ _
      rw [Submodule.ker_mkQ, (hα n).2.2.2])

lemma ofQuot_comp (n : ℕ) : (S.ofQuot hα n).comp (N.quotHom (I ^ n)) = α n :=
  Hom.descend_comp _ _ _ _ _ _

lemma ofQuot_toQuot (n : ℕ) : (S.ofQuot hα n).comp (S.toQuot hα n) = Hom.id _ := by
  refine Hom.comp_cancel (α n) (hα n).1 (hα n).2.1 ?_
  rw [Hom.comp_assoc, toQuot_comp, ofQuot_comp, Hom.id_comp]

variable (hc : ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m)

include hc in
lemma quotMap_toQuot {m n : ℕ} (h : m ≤ n) :
    (N.quotMap (Ideal.pow_le_pow_right h)).comp (S.toQuot hα n) =
      (S.toQuot hα m).comp (S.tr h) := by
  refine Hom.comp_cancel (α n) (hα n).1 (hα n).2.1 ?_
  rw [Hom.comp_assoc, toQuot_comp, Hom.comp_assoc, hc, toQuot_comp]
  exact Hom.ext' rfl rfl rfl

variable [IsNoetherianRing A] [IsAdicComplete I A]
  [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Finite A[X] (Module.AEval' N.x1)]

include hα in
/-- **Morphisms into an algebraization are detected by their reductions.** -/
theorem eq_of_comp_eq {P : ChartModule A} [Module.Finite A[X] (Module.AEval' P.x0)]
    [Module.Finite A[X] (Module.AEval' P.x1)] (φ ψ : Hom P N)
    (h : ∀ n, (α n).comp φ = (α n).comp ψ) : φ = ψ := by
  refine (toHomSystem_bijective I P N).1 (Subtype.ext (funext fun n ↦ ?_))
  change (N.quotHom (I ^ n)).comp φ = (N.quotHom (I ^ n)).comp ψ
  rw [← S.toQuot_comp hα, Hom.comp_assoc, Hom.comp_assoc, h]

include hα in
/-- **Global sections of an algebraization are detected by their reductions.** -/
theorem eq_of_mapH0_eq (x y : N.H0) (h : ∀ n, (α n).mapH0 x = (α n).mapH0 y) : x = y := by
  refine (N.H0ToSystem_bijective I).1 (Subtype.ext (funext fun n ↦ ?_))
  change (N.quotHom (I ^ n)).mapH0 x = (N.quotHom (I ^ n)).mapH0 y
  rw [← S.toQuot_comp hα, Hom.mapH0_comp, Hom.mapH0_comp, h]

variable {B : AlgStr N} (hB : ∀ n, B.IsHom (S.alg n) (α n))

include hα hc hB in
/-- **Algebraization of morphisms of chart algebras**: a compatible system of morphisms of chart
algebras `β n : P → S.M n` out of a coherent chart algebra `P` lifts to a morphism of chart
algebras `ψ : P → N` with reductions `β n` (unique by `eq_of_comp_eq`). -/
theorem exists_isHom_of_system {P : ChartModule A} [Module.Finite A[X] (Module.AEval' P.x0)]
    [Module.Finite A[X] (Module.AEval' P.x1)] (BP : AlgStr P) (β : ∀ n, Hom P (S.M n))
    (hβc : ∀ m n (h : m ≤ n), (S.tr h).comp (β n) = β m)
    (hβ : ∀ n, BP.IsHom (S.alg n) (β n)) :
    ∃ ψ : Hom P N, (∀ n, (α n).comp ψ = β n) ∧ BP.IsHom B ψ := by
  let sys : HomSystem P N I := ⟨fun n ↦ (S.toQuot hα n).comp (β n), fun m n h ↦ by
    change ((N.quotMap (Ideal.pow_le_pow_right h)).comp (S.toQuot hα n)).comp (β n) = _
    rw [S.quotMap_toQuot hα hc h, Hom.comp_assoc, hβc]⟩
  obtain ⟨ψ, hψ⟩ := (toHomSystem_bijective I P N).2 sys
  have hψn : ∀ n, (N.quotHom (I ^ n)).comp ψ = (S.toQuot hα n).comp (β n) := fun n ↦
    congrArg (fun s : HomSystem P N I ↦ s.1 n) hψ
  have hαψ : ∀ n, (α n).comp ψ = β n := fun n ↦ by
    rw [← S.ofQuot_comp hα n, Hom.comp_assoc, hψn, ← Hom.comp_assoc, ofQuot_toQuot, Hom.id_comp]
  refine ⟨ψ, hαψ, ?_, ?_⟩
  · refine S.eq_of_comp_eq hα _ _ fun n ↦ ?_
    rw [← Hom.comp_assoc, hαψ, (hβ n).1, ← Hom.comp_assoc, (hB n).1, Hom.comp_assoc,
      ← Hom.tensor_comp, hαψ]
  · refine S.eq_of_mapH0_eq hα _ _ fun n ↦ ?_
    rw [← Hom.mapH0_comp, hαψ, (hβ n).2, (hB n).2]

end AdicChartAlgSystem

end ProjectiveLine
