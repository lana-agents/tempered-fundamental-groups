/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# The reduction of a point is fixed by its stabiliser (generic; MR13 "A2⁻")

For an `O`-algebra `B` and an `O`-algebra map `χ : B → F` to a field whose image is integral over
`O`, and a maximal ideal `P` of `O`: **`FixedSpecialPoint.exists_maximal_fixed`** gives a maximal
ideal `𝔭` of `B` over `P` containing `ker χ` such that every `O`-algebra endomorphism `σ` of `B`
with `χ ∘ σ = χ` satisfies `σ⁻¹(𝔭) = 𝔭` (`𝔭 = χ⁻¹(𝔐)` for a maximal ideal `𝔐` of `χ(B)` over
`P`, chosen once).

Use (MR13-plan, run 16, "B4′ + A2⁻"): `B = B₀` the cusp chart of the lift of a tame cover,
`F` the residue field of a place `W` of the function field over a cusp, `χ` the reduction
`B₀ → W → W/𝔪_W`, `P = (ϖ)`: the image in `G` of the inertia group of `W` (elements acting trivially
on `W/𝔪_W`) lies in the stabiliser of the special point `𝔭` (a point of `C0 = B₀/ϖ` over the cusp).
Only this inclusion is needed for Route B's B4′, not the identification of the inertia group
with the stabiliser.
-/

universe u

namespace SemistableReduction

namespace FixedSpecialPoint

variable {O B F : Type*} [CommRing O] [CommRing B] [Field F] [Algebra O B] [Algebra O F]

/-- **A maximal ideal over `P` fixed by every `σ` with `χ ∘ σ = χ`.** -/
theorem exists_maximal_fixed (χ : B →ₐ[O] F) [Algebra.IsIntegral O χ.range] (P : Ideal O)
    [P.IsMaximal] (hP : RingHom.ker (algebraMap O F) ≤ P) :
    ∃ 𝔭 : Ideal B, 𝔭.IsMaximal ∧ 𝔭.comap (algebraMap O B) = P ∧ RingHom.ker χ ≤ 𝔭 ∧
      ∀ σ : B →ₐ[O] B, χ.comp σ = χ → 𝔭.comap σ = 𝔭 := by
  have hker : RingHom.ker (algebraMap O χ.range) ≤ P := by
    intro x hx
    apply hP
    rw [RingHom.mem_ker] at hx ⊢
    have := congrArg Subtype.val hx
    simpa using this
  obtain ⟨M, hMmax, hM⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := χ.range) P hker
  have hsurj : Function.Surjective χ.rangeRestrict := AlgHom.rangeRestrict_surjective χ
  refine ⟨M.comap χ.rangeRestrict, Ideal.comap_isMaximal_of_surjective _ hsurj, ?_, ?_, ?_⟩
  · ext x
    rw [Ideal.mem_comap, Ideal.mem_comap, ← hM, Ideal.mem_comap, AlgHom.commutes]
  · intro b hb
    rw [RingHom.mem_ker] at hb
    rw [Ideal.mem_comap]
    have : χ.rangeRestrict b = 0 := Subtype.ext hb
    rw [this]
    exact M.zero_mem
  · intro σ hσ
    ext b
    rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap,
      show χ.rangeRestrict (σ b) = χ.rangeRestrict b from
        Subtype.ext (congrArg (fun f : B →ₐ[O] F ↦ f b) hσ)]

end FixedSpecialPoint

end SemistableReduction
