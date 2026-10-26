/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalPatchReduction

/-!
# Uniqueness of the level-`n` patched algebra (Blueprint §12.8, M2.5)

In the setting of `FormalPatchReduction` (a chart `R`, `f ∈ R` cutting out the nodes, `R̂` the
`f`-adic completion, a nilpotent ideal `J`, `P` a formally étale lift of `C_f` with
`σ : P/JP ≃ C_f`, `N` the formal model along `V(f)` with `κ : R̂ ⊗_R C ≃ N/JN`), let `M` be an
`R`-algebra with maps `φ₁ : M → P`, `φ₂ : M → N` and `ρ : M → C` such that

* `φ₁` is a localization away from `f`,
* `φ₂` is a base change along `R → R̂`,
* `φ₁` and `φ₂` reduce modulo `J` to `ρ` (via `σ` and `κ`).

Then `M` is the patched algebra `G = P ×_{N_f} N` (`FormalPatchLevel.patch`):

* **`FormalPatchLevel.lift_comp_eq`**: `α ∘ φ₁ = φ₂` in `N_f`, where `α` is the lift of the
  patching datum `α₀ = alphaOfEquiv (specialFibreEquiv σ κ)`. Indeed, the localization `β : P → N_f`
  of `φ₂` reduces to `α₀` modulo `J` (`alphaOfEquiv_spec` on the image of `M`), so `β = α` by the
  uniqueness of lifts out of the formally étale `P` (`EtaleLift.ext_of_comp_eq`);
* **`FormalPatchLevel.patchEquivOfCompat`**: `M ≃ₐ[R] patch f J hJ α₀`, with components `φ₁` and
  `φ₂` (`patchEquivOfCompat_fst`, `patchEquivOfCompat_snd`), by the uniqueness of formal glueing
  (`FormalGlueing.bijective_liftGlued`, Stacks, Theorem 15.91.18, Tag 05ES).

This generalizes `FormalPatchLevel.patchEquivOfEqBot` (the case `J = ⊥`, `M = C`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalPatchLevel

noncomputable section

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R) {n : ℕ} (hJ : J ^ n = ⊥)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {C : Type u} [CommRing C] [Algebra R C]
  {N : Type u} [CommRing N] [Algebra R N] [Algebra (Hat f) N] [IsScalarTower R (Hat f) N]
  (σ : (P ⧸ J.map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R C f))
  (κ : (Hat f ⊗[R] C) ≃ₐ[Hat f] (N ⧸ JN J N))
  {M : Type*} [CommRing M] [Algebra R M] (φ₁ : M →ₐ[R] P) (φ₂ : M →ₐ[R] N) (ρ : M →ₐ[R] C)
  (hloc : letI := φ₁.toRingHom.toAlgebra; IsLocalization.Away (algebraMap R M f) P)
  (hσ : ∀ x, σ (Ideal.Quotient.mk _ (φ₁ x)) = algebraMap C _ (ρ x))
  (hκ : ∀ x, κ ((1 : Hat f) ⊗ₜ ρ x) = Ideal.Quotient.mk _ (φ₂ x))

include hloc hσ hκ in
/-- **Compatibility with the glueing datum**: the lift `α : P → N_f` of
`α₀ = alphaOfEquiv (specialFibreEquiv σ κ)` sends `φ₁ x` to `φ₂ x`. -/
theorem lift_comp_eq (x : M) :
    lift f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ)) (φ₁ x) =
      algebraMap N (Nf f N) (φ₂ x) := by
  letI := φ₁.toRingHom.toAlgebra
  set α₀ := alphaOfEquiv f J (specialFibreEquiv f J σ κ)
  set g : M →+* Nf f N := (algebraMap N (Nf f N)).comp φ₂.toRingHom
  have hg : ∀ y : Submonoid.powers (algebraMap R M f), IsUnit (g y) := by
    rintro ⟨_, k, rfl⟩
    change IsUnit (algebraMap N (Nf f N) (φ₂ (algebraMap R M f ^ k)))
    rw [map_pow, AlgHom.commutes, map_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow k
  have hβ1 : ∀ y : M, IsLocalization.lift hg (φ₁ y) = g y :=
    IsLocalization.lift_eq hg
  -- the localization `β : P → N_f` of `φ₂`
  let β : P →ₐ[R] Nf f N :=
    { IsLocalization.lift hg with
      commutes' := fun r ↦ by
        change IsLocalization.lift hg (algebraMap R P r) = _
        rw [← φ₁.commutes, hβ1]
        change algebraMap N (Nf f N) (φ₂ (algebraMap R M r)) = _
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply] }
  have hβ : ∀ y : M, β (φ₁ y) = g y := hβ1
  -- `β` reduces to `α₀` modulo `J`
  have hred : (Ideal.Quotient.mkₐ R (JNf f J N)).comp β = α₀ := by
    refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext
      (Submonoid.powers (algebraMap R M f)) (RingHom.ext fun y ↦ ?_))
    simp only [RingHom.comp_apply, AlgHom.coe_toRingHom, AlgHom.comp_apply,
      Ideal.Quotient.mkₐ_eq_mk, RingHom.algebraMap_toAlgebra]
    rw [show φ₁.toRingHom y = φ₁ y from rfl, hβ]
    exact (alphaOfEquiv_spec f J σ κ (φ₁ y) (ρ y) (φ₂ y) (hσ y) (hκ y)).symm
  haveI := isAdicComplete_JNf f J hJ (N := N)
  have hβα : lift f J hJ α₀ = β :=
    EtaleLift.ext_of_comp_eq (JNf f J N) (by rw [mkₐ_comp_lift, hred])
  rw [hβα, hβ]
  rfl

variable [IsNoetherianRing R] (hfP : IsUnit (algebraMap R P f))
  (hN : ∀ x : N, algebraMap R N f * x = 0 → x = 0)
  [Module.Flat (Hat f) (Nf f N)] (hφ₂ : IsBaseChange (Hat f) φ₂.toLinearMap)

include hfP hN hφ₂ in
/-- **Uniqueness of the level-`n` patch**: an `R`-algebra `M` localizing to `P` away from `f`,
completing to `N` along `V(f)` and compatible with the patching datum modulo `J` maps
bijectively to the patched algebra. -/
theorem bijective_liftGlued_of_compat :
    Function.Bijective (FormalGlueing.liftGlued N
      (lift f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ))) φ₁ φ₂
      (lift_comp_eq f J hJ σ κ φ₁ φ₂ ρ hloc hσ hκ)) := by
  letI := φ₁.toRingHom.toAlgebra
  have hα := isBaseChange_lift f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ))
    (surjective_betaMod_alphaOfEquiv _) (mem_of_betaMod_alphaOfEquiv_eq_zero _)
  refine FormalGlueing.bijective_liftGlued N _ (Hat f) hfP (FormalGlueing.completion_eq_add f) hN
    hα (FormalGlueing.completion_dvd f) _ _ _ (fun p ↦ ?_) (fun x hx ↦ ?_) hφ₂
  · obtain ⟨⟨x, ⟨_, k, rfl⟩⟩, hx⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap R M f)) p
    refine ⟨x, k, ?_⟩
    change p * φ₁ (algebraMap R M f ^ k) = φ₁ x at hx
    rw [← hx, map_pow, AlgHom.commutes, Algebra.smul_def, map_pow, mul_comm]
  · obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (algebraMap R M f)) P x).mp hx
    exact ⟨k, by rw [Algebra.smul_def, map_pow]; exact hk⟩

/-- **The level-`n` patched algebra is unique**: `M ≃ P ×_{N_f} N` for an `R`-algebra `M` with
`φ₁ : M → P` a localization away from `f`, `φ₂ : M → N` a base change along `R → R̂`, both
reducing modulo `J` to `ρ : M → C` (via `σ` and `κ`). -/
def patchEquivOfCompat :
    M ≃ₐ[R] patch f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ)) :=
  AlgEquiv.ofBijective _ (bijective_liftGlued_of_compat f J hJ σ κ φ₁ φ₂ ρ hloc hσ hκ hfP hN hφ₂)

@[simp]
lemma patchEquivOfCompat_fst (x : M) :
    (patchEquivOfCompat f J hJ σ κ φ₁ φ₂ ρ hloc hσ hκ hfP hN hφ₂ x).1.1 = φ₁ x := rfl

@[simp]
lemma patchEquivOfCompat_snd (x : M) :
    (patchEquivOfCompat f J hJ σ κ φ₁ φ₂ ρ hloc hσ hκ hfP hN hφ₂ x).1.2 = φ₂ x := rfl

end

end FormalPatchLevel

end SemistableReduction
