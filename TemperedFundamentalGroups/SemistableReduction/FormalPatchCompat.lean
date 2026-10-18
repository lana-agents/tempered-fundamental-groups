/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel

/-!
# Compatibility of the level-`n` patching data across levels (Blueprint §12.8, M2.3 (e'))

`FormalGlueingQuot.equiv` identifies `R' ⊗_R G` with `G'` for glueing data `(P, N, α)` over `R`
and `(P', N', α')` over an `R`-algebra `R'` (surjective structure map) related by reductions
`ρP`, `ρN`, provided the identifications are
compatible (`hcompat`: `α p = n` in `N_f` implies `α'(ρP p) = ρN n` in `N'_f`). For the level-`n`
patching (`FormalPatchLevel`) the identifications `α = lift α₀`, `α' = lift α₀'` are the unique
lifts (formal étaleness of `P`) of identifications `α₀`, `α₀'` modulo the nilpotent ideals `J`,
`J' ⊇ J R'` (`R'` e.g. the chart of the next lower level). **`FormalPatchCompat.hcompat`**:
`hcompat` holds as soon as it holds modulo `J'`,

  `α₀'(ρP p) = ρ̄Q(α₀ p)`  in `N'_f/J'`,

with `ρQ : N_f → N'_f` the localization of `ρN` (`FormalPatchCompat.ρQ`), by the uniqueness of
lifts out of the formally étale `P` into the `J'`-adically complete `N'_f`
(`EtaleLift.ext_of_comp_eq`).
-/

universe u

namespace SemistableReduction

namespace FormalPatchCompat

noncomputable section

open FormalPatchLevel TensorProduct

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R)
  {R' : Type u} [CommRing R'] [Algebra R R']
  {N : Type u} [CommRing N] [Algebra R N]
  {N' : Type u} [CommRing N'] [Algebra R' N']

/-- The image `q f` of `f` in `R'`. -/
abbrev fq : R' := algebraMap R R' f

variable {f} {J' : Ideal R'} (hJJ : J.map (algebraMap R R') ≤ J') (ρN : N →+* N')
  (hρN : ∀ r : R, ρN (algebraMap R N r) = algebraMap R' N' (algebraMap R R' r))

include hρN in
lemma powers_le :
    Submonoid.powers (algebraMap R N f) ≤
      (Submonoid.powers (algebraMap R' N' (fq (R' := R') f))).comap ρN.toMonoidHom := by
  rw [Submonoid.powers_le]
  exact ⟨1, by simpa using (hρN f).symm⟩

/-- The localization `ρQ : N_f → N'_f` of `ρN`. -/
def ρQ : Nf f N →+* Nf (fq (R' := R') f) N' :=
  IsLocalization.map (M := Submonoid.powers (algebraMap R N f))
    (T := Submonoid.powers (algebraMap R' N' (fq (R' := R') f))) _ ρN (powers_le ρN hρN)

lemma ρQ_algebraMap (x : N) :
    ρQ ρN hρN (algebraMap N (Nf f N) x) = algebraMap N' (Nf (fq (R' := R') f) N') (ρN x) :=
  IsLocalization.map_eq _ _

lemma ρQ_algebraMap_R (r : R) :
    ρQ ρN hρN (algebraMap R (Nf f N) r) =
      algebraMap R' (Nf (fq (R' := R') f) N') (algebraMap R R' r) := by
  rw [IsScalarTower.algebraMap_apply R N (Nf f N) r, ρQ_algebraMap, hρN,
    ← IsScalarTower.algebraMap_apply]

include hJJ in
lemma JNf_le : JNf f J N ≤ (JNf (fq (R' := R') f) J' N').comap (ρQ ρN hρN) := by
  rw [JNf, Ideal.map_le_iff_le_comap]
  intro j hj
  rw [Ideal.mem_comap, Ideal.mem_comap, ρQ_algebraMap_R]
  exact Ideal.mem_map_of_mem _ (hJJ (Ideal.mem_map_of_mem _ hj))

/-- `ρ̄Q : N_f/J → N'_f/J'`. -/
def ρQbar :
    (Nf f N ⧸ JNf f J N) →+* (Nf (fq (R' := R') f) N' ⧸ JNf (fq (R' := R') f) J' N') :=
  Ideal.quotientMap _ (ρQ ρN hρN) (JNf_le J hJJ ρN hρN)

lemma ρQbar_mk (y : Nf f N) :
    ρQbar J hJJ ρN hρN (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (ρQ ρN hρN y) :=
  Ideal.quotientMap_mk

section Compat

variable {n n' : ℕ} (hJ : J ^ n = ⊥) (hJ' : J' ^ n' = ⊥)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {P' : Type u} [CommRing P'] [Algebra R' P'] [Algebra.FormallyEtale R' P']
  (ρP : P →+* P')
  (hρP : ∀ r : R, ρP (algebraMap R P r) = algebraMap R' P' (algebraMap R R' r))
  (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N)
  (α₀' : P' →ₐ[R'] Nf (fq (R' := R') f) N' ⧸ JNf (fq (R' := R') f) J' N')
  (hmod : ∀ p, α₀' (ρP p) = ρQbar J hJJ ρN hρN (α₀ p))

include hρP hmod in
/-- **The lifts are compatible**: `α'(ρP p) = ρQ(α p)`. -/
theorem lift_compat (p : P) :
    lift (fq (R' := R') f) J' hJ' α₀' (ρP p) = ρQ ρN hρN (lift f J hJ α₀ p) := by
  letI : Algebra R (Nf (fq (R' := R') f) N') :=
    Algebra.compHom _ (algebraMap R R')
  haveI : IsScalarTower R R' (Nf (fq (R' := R') f) N') :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := isAdicComplete_JNf (fq (R' := R') f) J' hJ' (N := N')
  let g₁ : P →ₐ[R] Nf (fq (R' := R') f) N' :=
    { ((lift (fq (R' := R') f) J' hJ' α₀').toRingHom.comp ρP) with
      commutes' := fun r ↦ by
        change lift (fq (R' := R') f) J' hJ' α₀' (ρP (algebraMap R P r)) = _
        rw [hρP, AlgHom.commutes]
        rfl }
  let g₂ : P →ₐ[R] Nf (fq (R' := R') f) N' :=
    { ((ρQ ρN hρN).comp (lift f J hJ α₀).toRingHom) with
      commutes' := fun r ↦ by
        change ρQ ρN hρN (lift f J hJ α₀ (algebraMap R P r)) = _
        rw [AlgHom.commutes, ρQ_algebraMap_R]
        rfl }
  have h : g₁ = g₂ := by
    refine EtaleLift.ext_of_comp_eq (JNf (fq (R' := R') f) J' N') (AlgHom.ext fun p ↦ ?_)
    change Ideal.Quotient.mk _ (lift (fq (R' := R') f) J' hJ' α₀' (ρP p)) =
      Ideal.Quotient.mk _ (ρQ ρN hρN (lift f J hJ α₀ p))
    have h1 := congrArg (fun g ↦ g (ρP p)) (mkₐ_comp_lift (fq (R' := R') f) J' hJ' α₀')
    have h2 := congrArg (fun g ↦ g p) (mkₐ_comp_lift f J hJ α₀)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1 h2
    rw [h1, ← ρQbar_mk J hJJ ρN hρN, h2, hmod]
  exact congrArg (fun g ↦ g p) h

include hρP hmod in
/-- **`hcompat` of `FormalGlueingQuot.equiv` for the level-`n` patching**, from the
compatibility modulo `J'` of the identifications `α₀`, `α₀'`. -/
theorem hcompat (p : P) (x : N) (h : lift f J hJ α₀ p = algebraMap N (Nf f N) x) :
    lift (fq (R' := R') f) J' hJ' α₀' (ρP p) =
      algebraMap N' (Nf (fq (R' := R') f) N') (ρN x) := by
  rw [lift_compat J hJJ ρN hρN hJ hJ' ρP hρP α₀ α₀' hmod, h, ρQ_algebraMap]

end Compat

end

end FormalPatchCompat

end SemistableReduction
