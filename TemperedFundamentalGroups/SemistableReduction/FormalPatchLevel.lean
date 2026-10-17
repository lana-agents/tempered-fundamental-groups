/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Smooth.Quotient
import TemperedFundamentalGroups.SemistableReduction.FormalGlueing
import TemperedFundamentalGroups.SemistableReduction.EtaleLiftHom
import TemperedFundamentalGroups.SemistableReduction.CompleteFinite

/-!
# Formal patching at a nilpotent level (Blueprint §12.8, M2.3 steps (d), (e))

The level-`n` step of the formal patching: over `R` (e.g. a chart of the model modulo `ϖⁿ⁺¹`)
with a **nilpotent** ideal `J` (e.g. `(ϖ)`), an element `f` cutting out the nodes and `R̂` the
`f`-adic completion, the covering is glued (`FormalGlueing.glued`) from

* `P`: a formally étale `R`-algebra on which `f` is invertible (the lift over `D(f)` of the
  special-fibre covering of the smooth locus,
  `EtaleLiftExists.exists_finite_etale_lift_of_pow_eq_bot`),
* `N`: an `R̂`-algebra without `f`-torsion (the Kummer algebra over the formal neighbourhood of the
  nodes, `KummerEtale.eq_zero_of_mul_eq_zero_tensor`), with `N_f` flat over `R̂`,

along an identification `R̂ ⊗_R P ≅ N_f`. Such an identification only has to be given **modulo
`J`** (where it comes from the definition of an admissible covering of the special fibre,
`Admissible.Covering`): a map `α₀ : P → N_f/J` whose `R̂`-linear extension is bijective modulo `J`
lifts uniquely to `α : P → N_f` (formal étaleness, `EtaleLift.lift`), and then
`R̂ ⊗_R P → N_f` is bijective (**`FormalPatchLevel.isBaseChange_lift`**), by:

* `FormalPatchLevel.bijective_of_mod` (generic): a linear map `β : M → M'` into a flat module, over
  a ring with a nilpotent ideal `J`, which is surjective modulo `J` and whose kernel modulo `J` is
  trivial, is bijective (surjectivity: nilpotent Nakayama; injectivity:
  `ker β ∩ JM = J ker β` for `M'` flat, Mathlib `LinearMap.ker_inf_smul_top_eq_smul_of_flat`).

Consequences for the glued algebra `G = P ×_{N_f} N` (`FormalPatchLevel.patch`): `G` is a finite
`R`-module (`finite_patch`), `G_f = P` (`isLocalization_patch`) and `R̂ ⊗_R G = N`
(`isBaseChange_patch`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalPatchLevel

/-! ### Bijectivity from bijectivity modulo a nilpotent ideal -/

section Generic

variable {T : Type*} [CommRing T] (J : Ideal T) {n : ℕ} (hJ : J ^ n = ⊥)
  {M M' : Type*} [AddCommGroup M] [Module T M] [AddCommGroup M'] [Module T M']

include hJ in
/-- A submodule `L` with `L + J M = M` is everything, for `J` nilpotent. -/
lemma eq_top_of_sup_smul_top {L : Submodule T M'}
    (h : ∀ y : M', ∃ x ∈ L, y - x ∈ J • (⊤ : Submodule T M')) : L = ⊤ := by
  have key : ∀ k, (⊤ : Submodule T M') ≤ L ⊔ J ^ k • ⊤ := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]; exact le_sup_right
    | succ k ih =>
      intro y _
      obtain ⟨x, hx, hyx⟩ := h y
      have h1 : J • (⊤ : Submodule T M') ≤ L ⊔ J ^ (k + 1) • ⊤ := by
        calc J • (⊤ : Submodule T M') ≤ J • (L ⊔ J ^ k • ⊤) := Submodule.smul_mono le_rfl ih
          _ = J • L ⊔ J • J ^ k • ⊤ := Submodule.smul_sup _ _ _
          _ ≤ L ⊔ J ^ (k + 1) • ⊤ := by
            refine sup_le_sup (Submodule.smul_le_right) ?_
            rw [← Submodule.mul_smul, ← pow_succ']
      have : y = x + (y - x) := by abel
      rw [this]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hx) (h1 hyx)
  have := key n
  rwa [hJ, Submodule.bot_smul, sup_bot_eq, top_le_iff] at this

include hJ in
/-- **Bijectivity from bijectivity modulo a nilpotent ideal**, for a map into a flat module. -/
theorem bijective_of_mod [Module.Flat T M'] (β : M →ₗ[T] M')
    (hsurj : ∀ y : M', ∃ x : M, y - β x ∈ J • (⊤ : Submodule T M'))
    (hinj : ∀ x : M, β x ∈ J • (⊤ : Submodule T M') → x ∈ J • (⊤ : Submodule T M)) :
    Function.Bijective β := by
  have hs : Function.Surjective β := by
    rw [← LinearMap.range_eq_top]
    refine eq_top_of_sup_smul_top J hJ fun y ↦ ?_
    obtain ⟨x, hx⟩ := hsurj y
    exact ⟨β x, LinearMap.mem_range_self β x, hx⟩
  refine ⟨?_, hs⟩
  rw [← LinearMap.ker_eq_bot]
  have hK : LinearMap.ker β ≤ J • LinearMap.ker β := by
    intro x hx
    rw [← LinearMap.ker_inf_smul_top_eq_smul_of_flat J β hs]
    refine ⟨hx, hinj x ?_⟩
    rw [LinearMap.mem_ker.mp hx]
    exact Submodule.zero_mem _
  have : ∀ k, LinearMap.ker β ≤ J ^ k • LinearMap.ker β := by
    intro k
    induction k with
    | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    | succ k ih =>
      calc LinearMap.ker β ≤ J • LinearMap.ker β := hK
        _ ≤ J • J ^ k • LinearMap.ker β := Submodule.smul_mono le_rfl ih
        _ = J ^ (k + 1) • LinearMap.ker β := by rw [← Submodule.mul_smul, ← pow_succ']
  have := this n
  rwa [hJ, Submodule.bot_smul, le_bot_iff] at this

end Generic

/-- `x ∈ J B ↔ x ∈ (J T) • B` for `R → T → B`. -/
lemma mem_map_iff_mem_smul_top {R T B : Type*} [CommRing R] [CommRing T] [CommRing B]
    [Algebra R T] [Algebra R B] [Algebra T B] [IsScalarTower R T B] (J : Ideal R) (x : B) :
    x ∈ J.map (algebraMap R B) ↔ x ∈ (J.map (algebraMap R T)) • (⊤ : Submodule T B) := by
  rw [Ideal.smul_top_eq_map, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
    Submodule.restrictScalars_mem]

/-! ### The patching -/

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R) {n : ℕ} (hJ : J ^ n = ⊥)
  (P : Type u) [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  (N : Type u) [CommRing N] [Algebra R N]

/-- The `f`-adic completion. -/
abbrev Hat : Type u := AdicCompletion (Ideal.span {f}) R

/-- `N_f`, the formal neighbourhood of the nodes with the nodes removed. -/
abbrev Nf : Type u := Localization.Away (algebraMap R N f)

/-- The ideal `J N_f`. -/
abbrev JNf : Ideal (Nf f N) := J.map (algebraMap R (Nf f N))

omit [Algebra.FormallyEtale R P] in
include hJ in
lemma isAdicComplete_JNf : IsAdicComplete (JNf f J N) (Nf f N) :=
  CompleteFinite.isAdicComplete_of_pow_eq_bot _ (n := n)
    (by rw [← Ideal.map_pow, hJ, Ideal.map_bot])

variable {P N}

/-- **The lift `α : P → N_f`** of an identification `α₀ : P → N_f/J` modulo `J`. -/
noncomputable def lift (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N) : P →ₐ[R] Nf f N :=
  haveI := isAdicComplete_JNf f J hJ (N := N)
  EtaleLift.lift (JNf f J N) α₀

lemma mkₐ_comp_lift (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N) :
    (Ideal.Quotient.mkₐ R _).comp (lift f J hJ α₀) = α₀ :=
  haveI := isAdicComplete_JNf f J hJ (N := N)
  EtaleLift.mkₐ_comp_lift (JNf f J N) α₀

variable [Algebra (Hat f) N] [IsScalarTower R (Hat f) N]

/-- The `R̂`-linear extension `R̂ ⊗_R P → N_f/J` of `α₀`. -/
noncomputable def betaMod (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N) :
    Hat f ⊗[R] P →ₗ[Hat f] Nf f N ⧸ JNf f J N :=
  α₀.toLinearMap.liftBaseChange (Hat f)

/-- **The identification `R̂ ⊗_R P ≅ N_f` lifting an identification modulo `J`.** -/
theorem isBaseChange_lift [Module.Flat (Hat f) (Nf f N)] (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N)
    (hsurj : Function.Surjective (betaMod f J α₀))
    (hinj : ∀ x, betaMod f J α₀ x = 0 →
      x ∈ (J.map (algebraMap R (Hat f))) • (⊤ : Submodule (Hat f) (Hat f ⊗[R] P))) :
    IsBaseChange (Hat f) (lift f J hJ α₀).toLinearMap := by
  set α := lift f J hJ α₀
  set β : Hat f ⊗[R] P →ₗ[Hat f] Nf f N := α.toLinearMap.liftBaseChange (Hat f)
  have hJS : (J.map (algebraMap R (Hat f))) ^ n = ⊥ := by rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  -- `β` reduces to `betaMod`
  have hred : ∀ x, Ideal.Quotient.mk (JNf f J N) (β x) = betaMod f J α₀ x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s p =>
      simp only [β, betaMod, LinearMap.liftBaseChange_tmul, AlgHom.toLinearMap_apply]
      rw [← mkₐ_comp_lift f J hJ α₀, AlgHom.comp_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
      rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  have hβ : Function.Bijective β := by
    refine bijective_of_mod _ hJS β (fun y ↦ ?_) (fun x hx ↦ ?_)
    · obtain ⟨x, hx⟩ := hsurj (Ideal.Quotient.mk _ y)
      refine ⟨x, ?_⟩
      rw [← mem_map_iff_mem_smul_top, ← Ideal.Quotient.eq]
      exact hx.symm.trans (hred x).symm
    · refine hinj x ?_
      rw [← hred, Ideal.Quotient.eq_zero_iff_mem, mem_map_iff_mem_smul_top (T := Hat f)]
      exact hx
  refine IsBaseChange.of_equiv (LinearEquiv.ofBijective β hβ) fun p ↦ ?_
  simp [β]

/-! ### The glued algebra -/

/-- **The patched algebra** `G = P ×_{N_f} N` at level `n`. -/
noncomputable abbrev patch (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N) : Subalgebra R (P × N) :=
  FormalGlueing.glued N (lift f J hJ α₀)

omit [Algebra (Hat f) N] [IsScalarTower R (Hat f) N] in
/-- **The patched algebra localizes to `P` on `D(f)`.** -/
theorem isLocalization_patch (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N)
    (hfP : IsUnit (algebraMap R P f)) :
    letI := FormalGlueing.algebraFst N (lift f J hJ α₀)
    IsLocalization.Away (algebraMap R (patch f J hJ α₀) f) P :=
  FormalGlueing.isLocalization_fst f N _ hfP

variable [IsNoetherianRing R] (hfP : IsUnit (algebraMap R P f))
  (hN : ∀ x : N, algebraMap R N f * x = 0 → x = 0)
  [Module.Flat (Hat f) (Nf f N)] (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N)
  (hsurj : Function.Surjective (betaMod f J α₀))
  (hinj : ∀ x, betaMod f J α₀ x = 0 →
    x ∈ (J.map (algebraMap R (Hat f))) • (⊤ : Submodule (Hat f) (Hat f ⊗[R] P)))

include hfP hN hsurj hinj in
/-- **The patched algebra completes to `N` along the nodes.** -/
theorem isBaseChange_patch :
    IsBaseChange (Hat f) (FormalGlueing.snd N (lift f J hJ α₀)).toLinearMap :=
  FormalGlueing.isBaseChange_snd_completion f N _ hfP hN (isBaseChange_lift f J hJ α₀ hsurj hinj)

include hfP hN hsurj hinj in
/-- **The patched algebra is finite** (for `P` finite over `R_f` and `N` finite over `R̂`). -/
theorem finite_patch
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P))
    [Module.Finite (Hat f) N] : Module.Finite R (patch f J hJ α₀) :=
  FormalGlueing.finite_glued_completion f N _ hfP hN (isBaseChange_lift f J hJ α₀ hsurj hinj) hP

end FormalPatchLevel

end SemistableReduction
