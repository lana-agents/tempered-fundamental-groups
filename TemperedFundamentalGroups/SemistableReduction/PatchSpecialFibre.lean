/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalPatchReduction

/-!
# The patched algebra on the special fibre is the given covering (Blueprint §12.8, M2.5 (b))

In the setting of `FormalPatchReduction` (a chart `R`, `f ∈ R` cutting out the nodes, `R̂` the
`f`-adic completion, `P` a formally étale lift of `C_f` with `σ : P/JP ≃ C_f`, `N` the formal model
along `V(f)` with `κ : R̂ ⊗_R C ≃ N/JN`), the patched algebra `G = P ×_{N_f} N`
(`FormalPatchLevel.patch`) reduces to the special-fibre covering `C`. At the bottom level, where
`J = 0` (e.g. `R = O/ϖ ⊗ …` with `ker θ = (ϖ)`), this is an isomorphism `C ≃ G`:

* **`FormalPatchLevel.patchEquivOfEqBot`**: for `J = ⊥`, `C ≃ₐ[R] patch f J hJ α₀` with
  `α₀ = alphaOfEquiv (specialFibreEquiv σ κ)`; its components are `C → C_f ≃ P` (via `σ`) and
  `C → R̂ ⊗_R C ≃ N` (via `κ`) (`patchEquivOfEqBot_fst`, `patchEquivOfEqBot_snd`).

Proof: the uniqueness of formal glueing (`FormalGlueing.bijective_liftGlued`, Stacks, Theorem
15.91.18, Tag 05ES): `C` localizes to `C_f ≅ P` away from `f`, its base change to `R̂` is
`R̂ ⊗_R C ≅ N`, and the two maps are compatible with the glueing datum `α = α₀` (for `J = 0` the
lift of `α₀` is `α₀` itself; `alphaOfEquiv_spec`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalPatchLevel

noncomputable section

variable {R : Type u} [CommRing R] {J : Ideal R} (hJ0 : J = ⊥)

/-- For `J = ⊥`, `A / J A ≃ A` (as `S`-algebras). -/
def quotEquivOfEqBot (S : Type u) [CommRing S] (A : Type u) [CommRing A] [Algebra R A]
    [Algebra S A] : (A ⧸ J.map (algebraMap R A)) ≃ₐ[S] A :=
  (Ideal.quotientEquivAlgOfEq S (by rw [hJ0, Ideal.map_bot])).trans (AlgEquiv.quotientBot S A)

@[simp]
lemma quotEquivOfEqBot_mk {S : Type u} [CommRing S] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra S A] (a : A) : quotEquivOfEqBot hJ0 S A (Ideal.Quotient.mk _ a) = a := rfl

lemma mk_quotEquivOfEqBot {S : Type u} [CommRing S] {A : Type u} [CommRing A] [Algebra R A]
    [Algebra S A] (y : A ⧸ J.map (algebraMap R A)) :
    Ideal.Quotient.mk _ (quotEquivOfEqBot hJ0 S A y) = y := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

variable (f : R) {n : ℕ} (hJ : J ^ n = ⊥)
  {P : Type u} [CommRing P] [Algebra R P]
  {C : Type u} [CommRing C] [Algebra R C]
  {N : Type u} [CommRing N] [Algebra R N] [Algebra (Hat f) N] [IsScalarTower R (Hat f) N]
  (σ : (P ⧸ J.map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R C f))
  (κ : (Hat f ⊗[R] C) ≃ₐ[Hat f] (N ⧸ JN J N))

/-- `C_f ≃ P/JP = P` (for `J = ⊥`). -/
def equivP : Localization.Away (algebraMap R C f) ≃ₐ[R] P :=
  σ.symm.trans (quotEquivOfEqBot hJ0 R P)

/-- `R̂ ⊗_R C ≃ N/JN = N` (for `J = ⊥`). -/
def equivN : (Hat f ⊗[R] C) ≃ₐ[Hat f] N :=
  κ.trans (quotEquivOfEqBot hJ0 (Hat f) N)

/-- The map `C → C_f ≃ P` (for `J = ⊥`). -/
def toP : C →ₐ[R] P :=
  (equivP hJ0 f σ).toAlgHom.comp
    (IsScalarTower.toAlgHom R C (Localization.Away (algebraMap R C f)))

/-- The map `C → R̂ ⊗_R C ≃ N` (for `J = ⊥`). -/
def toN : C →ₐ[R] N :=
  ((equivN hJ0 f κ).toAlgHom.restrictScalars R).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := Hat f))

lemma toP_apply (c : C) : toP hJ0 f σ c =
    equivP hJ0 f σ (algebraMap C (Localization.Away (algebraMap R C f)) c) := rfl

lemma toN_apply (c : C) : toN hJ0 f κ c = equivN hJ0 f κ ((1 : Hat f) ⊗ₜ c) := rfl

lemma mk_toP (c : C) : σ (Ideal.Quotient.mk _ (toP hJ0 f σ c)) =
    algebraMap C (Localization.Away (algebraMap R C f)) c := by
  rw [toP_apply, equivP, AlgEquiv.trans_apply, mk_quotEquivOfEqBot, AlgEquiv.apply_symm_apply]

lemma mk_toN (c : C) : κ ((1 : Hat f) ⊗ₜ c) = Ideal.Quotient.mk _ (toN hJ0 f κ c) := by
  rw [toN_apply, equivN, AlgEquiv.trans_apply, mk_quotEquivOfEqBot]

variable [Algebra.FormallyEtale R P]

/-- The two maps are compatible with the glueing datum. -/
lemma lift_toP (c : C) :
    lift f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ)) (toP hJ0 f σ c) =
      algebraMap N (Nf f N) (toN hJ0 f κ c) := by
  have hbot : JNf f J N = ⊥ := by rw [JNf, hJ0, Ideal.map_bot]
  have hinj : Function.Injective (Ideal.Quotient.mk (JNf f J N)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    rwa [Ideal.Quotient.eq_zero_iff_mem, hbot, Ideal.mem_bot] at hx
  apply hinj
  have h := congrArg (fun φ ↦ φ (toP hJ0 f σ c))
    (mkₐ_comp_lift f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ)))
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  rw [h]
  exact alphaOfEquiv_spec f J σ κ _ c _ (mk_toP hJ0 f σ c) (mk_toN hJ0 f κ c)

variable [IsNoetherianRing R] (hfP : IsUnit (algebraMap R P f))
  (hN : ∀ x : N, algebraMap R N f * x = 0 → x = 0)
  [Module.Flat (Hat f) (Nf f N)]

include hfP hN in
/-- **The bottom-level patched algebra is the special-fibre covering**: for `J = ⊥` the map
`C → P ×_{N_f} N` given by `C → C_f ≃ P` and `C → R̂ ⊗_R C ≃ N` is bijective. -/
theorem bijective_toPatch :
    Function.Bijective (FormalGlueing.liftGlued N
      (lift f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ)))
      (toP hJ0 f σ) (toN hJ0 f κ) (lift_toP hJ0 f hJ σ κ)) := by
  have hα := isBaseChange_lift f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ))
    (surjective_betaMod_alphaOfEquiv _) (mem_of_betaMod_alphaOfEquiv_eq_zero _)
  refine FormalGlueing.bijective_liftGlued N _ (Hat f) hfP (FormalGlueing.completion_eq_add f) hN
    hα (FormalGlueing.completion_dvd f) _ _ _ (fun p ↦ ?_) (fun x hx ↦ ?_) ?_
  · -- `C → P` is a localization away from `f`, up to `P ≃ C_f`
    obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, hc⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R C f))
      ((equivP hJ0 f σ).symm p)
    refine ⟨c, k, ?_⟩
    rw [toP_apply, ← hc, map_mul, AlgEquiv.apply_symm_apply, map_pow,
      ← IsScalarTower.algebraMap_apply, ← map_pow, AlgEquiv.commutes, Algebra.smul_def, mul_comm]
  · -- the kernel of `C → C_f` is `f`-power torsion
    have h0 : algebraMap C (Localization.Away (algebraMap R C f)) x = 0 := by
      rw [toP_apply] at hx
      exact (map_eq_zero_iff _ (equivP hJ0 f σ).injective).mp hx
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (algebraMap R C f)) _ x).mp h0
    exact ⟨k, by rw [Algebra.smul_def, map_pow]; exact hk⟩
  · -- `C → N` is the base change along `R → R̂`
    exact IsBaseChange.of_equiv (equivN hJ0 f κ).toLinearEquiv fun c ↦ rfl

/-- **`C ≃ P ×_{N_f} N`** for `J = ⊥`: the bottom-level patched algebra is the given covering of
the special fibre. -/
def patchEquivOfEqBot : C ≃ₐ[R] patch f J hJ (alphaOfEquiv f J (specialFibreEquiv f J σ κ)) :=
  AlgEquiv.ofBijective _ (bijective_toPatch hJ0 f hJ σ κ hfP hN)

lemma patchEquivOfEqBot_fst (c : C) :
    (patchEquivOfEqBot hJ0 f hJ σ κ hfP hN c : P × N).1 = toP hJ0 f σ c := rfl

lemma patchEquivOfEqBot_snd (c : C) :
    (patchEquivOfEqBot hJ0 f hJ σ κ hfP hN c : P × N).2 = toN hJ0 f κ c := rfl

end

end FormalPatchLevel

end SemistableReduction
