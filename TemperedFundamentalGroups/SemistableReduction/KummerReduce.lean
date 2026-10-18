/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import TemperedFundamentalGroups.SemistableReduction.AdmissibleLift
import TemperedFundamentalGroups.SemistableReduction.FormalGlueingQuot

/-!
# Reduction of a lifted Kummer factor from level `n + 1` to level `n` (Blueprint §12.8, M2.3)

For the compatibility of the level-`n` patchings (`FormalGlueingQuot.equiv`) one needs the
reduction `ρN : N → N'` of the formal models with kernel `IN`. For a lifted Kummer factor
`N = (R̂/(1 − ε̃)) ⊗_{O[u,v]/(uv−π^e)} O[s,t]/(st − π)` over the chart `R` (`AdmissibleLift.N`)
and an ideal `I ⊆ R` (e.g. `ϖⁿ⁺¹R`), the level-`n` factor over `R/I` is the one with the reduced
lift data `χ' = ψ ∘ χ`, `ε' = ψ ε̃` (`ψ : R̂ → (R/I)^∧` the completion map,
`FormalGlueingQuot.ψ`), and

* `KummerReduce.ρ : N → N'` (`σ ⊗ id`, `σ : R̂/(1 − ε̃) → (R/I)^∧/(1 − ε')` induced by `ψ`),
* `surjective_ρ`, **`ker_ρ`** (`= I N`, for `R` Noetherian: `ker σ = I·R̂/(1 − ε̃)` from
  `CompletionQuot.ker_ψ`, and Mathlib `Algebra.TensorProduct.rTensor_ker`),
* `ρ_algebraMap` (`R`-linear over `R → R/I`) and `ρ_smul` (semilinear over `ψ`)

— the hypotheses `hρN`, `hρNs`, `hρNk` of `FormalGlueingQuot.equiv` for one Kummer factor.
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale

namespace KummerReduce

noncomputable section

open AdmissibleLift

variable {O : Type u} [CommRing O] {R : Type u} [CommRing R] [Algebra O R] (f : R) (I : Ideal R)
  {π : O} {e : ℕ} (χ : A π e →ₐ[O] FormalPatchLevel.Hat f) (ε : FormalPatchLevel.Hat f)

/-- The completion map `ψ : R̂ → (R/I)^∧`. -/
abbrev ψI : FormalPatchLevel.Hat f →ₐ[R] FormalPatchLevel.Hat (FormalGlueingQuot.fq f I) :=
  FormalGlueingQuot.ψ f I

/-- The reduced node coordinates `ψ ∘ χ`. -/
def χI : A π e →ₐ[O] FormalPatchLevel.Hat (FormalGlueingQuot.fq f I) :=
  ((ψI f I).restrictScalars O).comp χ

lemma span_le :
    Ideal.span {1 - ε} ≤ (Ideal.span {1 - ψI f I ε}).comap (ψI f I).toRingHom := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_one]
  exact Ideal.subset_span rfl

/-- `σ : R̂/(1 − ε̃) → (R/I)^∧/(1 − ψ ε̃)`. -/
def σI : LPiece f χ ε →+* LPiece (FormalGlueingQuot.fq f I) (χI f I χ) (ψI f I ε) :=
  Ideal.quotientMap _ (ψI f I).toRingHom (span_le f I ε)

lemma σI_mk (x : FormalPatchLevel.Hat f) :
    σI f I χ ε (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (ψI f I x) :=
  Ideal.quotientMap_mk

lemma surjective_σI : Function.Surjective (σI f I χ ε) :=
  Ideal.quotientMap_surjective (CompletionQuot.surjective_ψ _ _ _ _)

/-- `σ` as a map over the node ring. -/
def σIₐ : LPiece f χ ε →ₐ[A π e] LPiece (FormalGlueingQuot.fq f I) (χI f I χ) (ψI f I ε) :=
  { σI f I χ ε with commutes' := fun a ↦ σI_mk f I χ ε (χ a) }

/-- **The reduction `ρ : N → N'`** of a lifted Kummer factor. -/
def ρ : N f χ ε →ₐ[A π e] N (FormalGlueingQuot.fq f I) (χI f I χ) (ψI f I ε) :=
  Algebra.TensorProduct.map (σIₐ f I χ ε) (AlgHom.id (A π e) (B π))

lemma ρ_tmul (s : LPiece f χ ε) (b : B π) : ρ f I χ ε (s ⊗ₜ b) = σI f I χ ε s ⊗ₜ b := rfl

lemma surjective_ρ : Function.Surjective (ρ f I χ ε) :=
  Algebra.TensorProduct.map_surjective _ _ (surjective_σI f I χ ε) Function.surjective_id

/-- `ker σ = I·R̂/(1 − ε̃)`. -/
lemma ker_σI [IsNoetherianRing R] :
    RingHom.ker (σI f I χ ε) = I.map (algebraMap R (LPiece f χ ε)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, σI_mk] at hx
    change (Ideal.Quotient.mk (Ideal.span {1 - ψI f I ε}) (ψI f I y) :
      FormalPatchLevel.Hat (FormalGlueingQuot.fq f I) ⧸ Ideal.span {1 - ψI f I ε}) = 0 at hx
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hx
    obtain ⟨z, hz⟩ := hx
    obtain ⟨w, rfl⟩ := CompletionQuot.surjective_ψ _ _ _ (FormalGlueingQuot.map_span f I) z
    have hker : y - w * (1 - ε) ∈ RingHom.ker (ψI f I) := by
      rw [RingHom.mem_ker, map_sub, map_mul, map_sub, map_one]
      change ψI f I y - ψI f I w * (1 - ψI f I ε) = 0
      rw [← hz, sub_self]
    rw [CompletionQuot.ker_ψ] at hker
    have heq : (Ideal.Quotient.mk (Ideal.span {1 - ε}) y : LPiece f χ ε) =
        Ideal.Quotient.mk (Ideal.span {1 - ε}) (y - w * (1 - ε)) := by
      have h1 : (Ideal.Quotient.mk (Ideal.span {1 - ε}) (1 - ε) : LPiece f χ ε) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [map_sub, map_mul, h1, mul_zero, sub_zero]
    rw [heq]
    have hmap : (I.map (algebraMap R (FormalPatchLevel.Hat f))).map
        (Ideal.Quotient.mk (Ideal.span {1 - ε})) = I.map (algebraMap R (LPiece f χ ε)) := by
      rw [Ideal.map_map]
      rfl
    rw [← hmap]
    exact Ideal.mem_map_of_mem _ hker
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    rw [Ideal.mem_comap, RingHom.mem_ker]
    change σI f I χ ε (Ideal.Quotient.mk _ (algebraMap R _ r)) = 0
    rw [σI_mk, AlgHom.commutes, IsScalarTower.algebraMap_apply R (R ⧸ I),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero, map_zero]
    rfl

/-- **The kernel of `ρ` is `I N`.** -/
theorem ker_ρ [IsNoetherianRing R] :
    RingHom.ker (ρ f I χ ε) = I.map (algebraMap R (N f χ ε)) := by
  have h := Algebra.TensorProduct.rTensor_ker (σIₐ f I χ ε) (R := A π e) (C := B π)
    (surjective_σI f I χ ε)
  change RingHom.ker (Algebra.TensorProduct.map (σIₐ f I χ ε) (AlgHom.id (A π e) (B π))) = _
  rw [h]
  have hk : RingHom.ker (σIₐ f I χ ε) = RingHom.ker (σI f I χ ε) := rfl
  rw [hk, ker_σI]
  change Ideal.map (Algebra.TensorProduct.includeLeft (R := A π e) (S := A π e)
    (A := LPiece f χ ε) (B := B π)).toRingHom (I.map (algebraMap R (LPiece f χ ε))) = _
  rw [Ideal.map_map]
  rfl

lemma ρ_algebraMap (r : R) :
    ρ f I χ ε (algebraMap R (N f χ ε) r) =
      algebraMap (R ⧸ I) (N (FormalGlueingQuot.fq f I) (χI f I χ) (ψI f I ε))
        (Ideal.Quotient.mk I r) := by
  change ρ f I χ ε (Ideal.Quotient.mk _ (algebraMap R (FormalPatchLevel.Hat f) r) ⊗ₜ 1) = _
  rw [ρ_tmul, σI_mk, AlgHom.commutes, IsScalarTower.algebraMap_apply R (R ⧸ I)]
  rfl

lemma ρ_smul (s : FormalPatchLevel.Hat f) (x : N f χ ε) :
    ρ f I χ ε (s • x) = ψI f I s • ρ f I χ ε x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1

end

end KummerReduce

end SemistableReduction
