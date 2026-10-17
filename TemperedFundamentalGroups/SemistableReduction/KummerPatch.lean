/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerNodePunctured
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel
import TemperedFundamentalGroups.SemistableReduction.KummerNode

/-!
# The Kummer algebra over the formal neighbourhood of a node (Blueprint §12.8, M2.3 (c))

Let `R` be a ring (a chart of the model at some level), `f ∈ R` cutting out a node, `R̂` the
`f`-adic completion, and suppose that `R̂` is an algebra over the node ring `A = O[u,v]/(uv − π^e)`
(formal node coordinates; in the Tate case the coordinates of
`TemperedFundamentalGroups.TateNormal.nodeGerm_chart_zero`) such that

* `f ↦ u + v` in `R̂` (`hf`), and
* `R̂` is flat over `A` (e.g. a completion of an algebra étale over `A`).

The Kummer algebra `N = R̂ ⊗_A B` (`B = O[s,t]/(st − π)`, `u ↦ s^e`, `v ↦ t^e`) then satisfies the
hypotheses of the level-`n` patching `FormalPatchLevel`:

* `KummerPatch.finite`: `N` is finite over `R̂` (`Node.kummer_finite`);
* **`KummerPatch.eq_zero_of_mul_eq_zero`**: `f` is a nonzerodivisor on `N`
  (`KummerEtale.eq_zero_of_mul_eq_zero_tensor`);
* **`KummerPatch.flat_localization`**: for `e` invertible in `O`, `N_f` is flat over `R̂`: it is
  `R̂ ⊗_A B_{u+v}` (Mathlib `IsLocalization.Away.tensorProductEquivTMulRight`), and `B_{u+v}` is
  flat over `A` since it is étale over `A_{u+v}` (`KummerEtale.etale_away`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace KummerPatch

noncomputable section

open KummerEtale

variable {O : Type u} [CommRing O] (π : O) {e : ℕ} {R : Type u} [CommRing R] (f : R)
  [Algebra (A π e) (FormalPatchLevel.Hat f)]

/-- **The Kummer algebra** `N = R̂ ⊗_A B` over the formal neighbourhood of the node. -/
abbrev N : Type u := FormalPatchLevel.Hat f ⊗[A π e] B π

/-- `N` as an `R`-algebra, through `R̂`. -/
instance : Algebra R (N π f (e := e)) :=
  Algebra.compHom _ (algebraMap R (FormalPatchLevel.Hat f))

instance : @IsScalarTower R (FormalPatchLevel.Hat f) (N π f (e := e)) _ Algebra.toSMul
    Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `N` is finite over `R̂`. -/
theorem finite (he : 0 < e) : Module.Finite (FormalPatchLevel.Hat f) (N π f (e := e)) :=
  haveI : Module.Finite (A π e) (B π) := Node.kummer_finite π he
  inferInstance

variable {π f}

omit [Algebra (A π e) (FormalPatchLevel.Hat f)] in
lemma tmul_fA [Algebra (A π e) (FormalPatchLevel.Hat f)] :
    (algebraMap (A π e) (FormalPatchLevel.Hat f) (fA π)) ⊗ₜ[A π e] (1 : B π) =
      (1 : FormalPatchLevel.Hat f) ⊗ₜ[A π e] algebraMap (A π e) (B π) (fA π) := by
  rw [Algebra.algebraMap_eq_smul_one (A := FormalPatchLevel.Hat f),
    Algebra.algebraMap_eq_smul_one (A := B π), TensorProduct.smul_tmul]

lemma algebraMap_f (hf : algebraMap R (FormalPatchLevel.Hat f) f =
    algebraMap (A π e) (FormalPatchLevel.Hat f) (fA π)) :
    algebraMap R (N π f (e := e)) f = (1 : FormalPatchLevel.Hat f) ⊗ₜ[A π e]
      algebraMap (A π e) (B π) (fA π) := by
  change algebraMap (FormalPatchLevel.Hat f) (N π f (e := e)) (algebraMap R _ f) = _
  rw [hf, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    tmul_fA]

/-- **`f` is a nonzerodivisor on the Kummer algebra** (`R̂` flat over `A`). -/
theorem eq_zero_of_mul_eq_zero (he : 0 < e) [Module.Flat (A π e) (FormalPatchLevel.Hat f)]
    (hf : algebraMap R (FormalPatchLevel.Hat f) f =
      algebraMap (A π e) (FormalPatchLevel.Hat f) (fA π))
    (x : N π f (e := e)) (hx : algebraMap R (N π f (e := e)) f * x = 0) : x = 0 := by
  refine eq_zero_of_mul_eq_zero_tensor π he (FormalPatchLevel.Hat f) ?_
  rw [algebraMap_f hf] at hx
  rw [Algebra.TensorProduct.algebraMap_apply, tmul_fA]
  exact hx

/-- `B_{u+v}` is flat over `A` (for `e` invertible in `O`). -/
theorem flat_Bf (he : 0 < e) (heu : IsUnit (e : O)) : Module.Flat (A π e) (Bf π e) := by
  have h1 : (afToBf π e).Flat := (RingHom.Etale.iff_flat_and_formallyUnramified.mp
    (etale_away he heu)).1
  have h2 : (algebraMap (A π e) (Af π e)).Flat := RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (Af π e) (Submonoid.powers (fA π)))
  have h3 : algebraMap (A π e) (Bf π e) = (afToBf π e).comp (algebraMap (A π e) (Af π e)) := by
    refine RingHom.ext fun a ↦ ?_
    rw [RingHom.comp_apply, afToBf, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]
  rw [← RingHom.flat_algebraMap_iff, h3]
  exact RingHom.Flat.comp h2 h1

/-- **`N_f` is flat over `R̂`** (for `e` invertible in `O`). -/
theorem flat_localization (he : 0 < e) (heu : IsUnit (e : O))
    (hf : algebraMap R (FormalPatchLevel.Hat f) f =
      algebraMap (A π e) (FormalPatchLevel.Hat f) (fA π)) :
    Module.Flat (FormalPatchLevel.Hat f) (Localization.Away (algebraMap R (N π f (e := e)) f)) := by
  haveI := flat_Bf (π := π) he heu
  let ι := IsLocalization.Away.tensorProductEquivTMulRight (A π e) (FormalPatchLevel.Hat f)
    (algebraMap (A π e) (B π) (fA π)) (Bf π e)
  haveI : Module.Flat (FormalPatchLevel.Hat f) (Localization.Away
      ((1 : FormalPatchLevel.Hat f) ⊗ₜ[A π e] algebraMap (A π e) (B π) (fA π))) :=
    Module.Flat.of_linearEquiv ι.symm.toLinearEquiv
  rw [algebraMap_f hf]
  infer_instance

/-! ### The patched covering with a Kummer formal neighbourhood -/

variable [IsNoetherianRing R] (J : Ideal R) {n : ℕ} (hJ : J ^ n = ⊥)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]

/-- **Level-`n` patching with the Kummer algebra at the node** (M2.3 (b)–(e) at one level, given
the identification `α₀` modulo `J` of `R̂ ⊗_R P` with `N_f`): the patched algebra
`P ×_{N_f} (R̂ ⊗_A B)` is a finite `R`-algebra, equal to `P` on `D(f)` and to the Kummer algebra
`R̂ ⊗_A B` on the formal neighbourhood of the node. -/
theorem patch_spec (he : 0 < e) (heu : IsUnit (e : O))
    [Module.Flat (A π e) (FormalPatchLevel.Hat f)]
    (hf : algebraMap R (FormalPatchLevel.Hat f) f =
      algebraMap (A π e) (FormalPatchLevel.Hat f) (fA π))
    (hfP : IsUnit (algebraMap R P f))
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P))
    (α₀ : P →ₐ[R] FormalPatchLevel.Nf f (N π f (e := e)) ⧸
      FormalPatchLevel.JNf f J (N π f (e := e)))
    (hsurj : Function.Surjective (FormalPatchLevel.betaMod f J α₀))
    (hinj : ∀ x, FormalPatchLevel.betaMod f J α₀ x = 0 → x ∈ (J.map (algebraMap R
      (FormalPatchLevel.Hat f))) • (⊤ : Submodule (FormalPatchLevel.Hat f)
        (FormalPatchLevel.Hat f ⊗[R] P))) :
    Module.Finite R (FormalPatchLevel.patch f J hJ α₀) ∧
      (letI := FormalGlueing.algebraFst (N π f (e := e)) (FormalPatchLevel.lift f J hJ α₀);
        IsLocalization.Away (algebraMap R (FormalPatchLevel.patch f J hJ α₀) f) P) ∧
      IsBaseChange (FormalPatchLevel.Hat f)
        (FormalGlueing.snd (N π f (e := e)) (FormalPatchLevel.lift f J hJ α₀)).toLinearMap := by
  haveI := flat_localization he heu hf
  haveI := finite π f he
  have hN := eq_zero_of_mul_eq_zero he hf
  exact ⟨FormalPatchLevel.finite_patch f J hJ hfP hN α₀ hsurj hinj hP,
    FormalPatchLevel.isLocalization_patch f J hJ α₀ hfP,
    FormalPatchLevel.isBaseChange_patch f J hJ hfP hN α₀ hsurj hinj⟩

end

end KummerPatch

end SemistableReduction
