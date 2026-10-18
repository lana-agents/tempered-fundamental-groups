/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.TensorProduct.Quotient
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel

/-!
# Compatibility of the level-`n` patching data across levels (Blueprint §12.8, M2.3 (e'))

`FormalGlueingQuot.equiv` identifies `G/IG` with `G'` for glueing data `(P, N, α)` over `R` and
`(P', N', α')` over `R/I` related by reductions `ρP`, `ρN`, provided the identifications are
compatible (`hcompat`: `α p = n` in `N_f` implies `α'(ρP p) = ρN n` in `N'_f`). For the level-`n`
patching (`FormalPatchLevel`) the identifications `α = lift α₀`, `α' = lift α₀'` are the unique
lifts (formal étaleness of `P`) of identifications `α₀`, `α₀'` modulo the nilpotent ideals `J`,
`J' = J(R/I)`. **`FormalPatchCompat.hcompat`**: `hcompat` holds as soon as it holds modulo `J'`,

  `α₀'(ρP p) = ρ̄Q(α₀ p)`  in `N'_f/J'`,

with `ρQ : N_f → N'_f` the localization of `ρN` (`FormalPatchCompat.ρQ`), by the uniqueness of
lifts out of the formally étale `P` into the `J'`-adically complete `N'_f`
(`EtaleLift.ext_of_comp_eq`).

The étale part of the level-`n + 1` data reduces to admissible level-`n` data: for `P` formally
étale over `R` with `f` invertible and `P` finite over `R_f`, `P/IP` is formally étale over `R/I`
(`formallyEtale_quot`, base change `(R/I) ⊗_R P ≅ P/IP`), `f̄` is invertible on it
(`isUnit_quot`) and it is finite over `(R/I)_f̄` (`finite_quot`); `ρP = P → P/IP` is surjective
with kernel `IP` — the hypotheses `hρPs`, `hρPk` of `FormalGlueingQuot.equiv`.
-/

universe u

namespace SemistableReduction

namespace FormalPatchCompat

noncomputable section

open FormalPatchLevel TensorProduct

variable {R : Type u} [CommRing R] (f : R) (I J : Ideal R)
  {N : Type u} [CommRing N] [Algebra R N]
  {N' : Type u} [CommRing N'] [Algebra (R ⧸ I) N']

/-- The image `f̄` of `f` in `R/I`. -/
abbrev fq : R ⧸ I := Ideal.Quotient.mk I f

/-- The ideal `J' = J (R/I)`. -/
abbrev J' : Ideal (R ⧸ I) := J.map (Ideal.Quotient.mk I)

variable {f I} (ρN : N →+* N')
  (hρN : ∀ r : R, ρN (algebraMap R N r) = algebraMap (R ⧸ I) N' (Ideal.Quotient.mk I r))

include hρN in
lemma powers_le :
    Submonoid.powers (algebraMap R N f) ≤
      (Submonoid.powers (algebraMap (R ⧸ I) N' (fq f I))).comap ρN.toMonoidHom := by
  rw [Submonoid.powers_le]
  exact ⟨1, by simpa using (hρN f).symm⟩

/-- The localization `ρQ : N_f → N'_f` of `ρN`. -/
def ρQ : Nf f N →+* Nf (fq f I) N' :=
  IsLocalization.map (M := Submonoid.powers (algebraMap R N f))
    (T := Submonoid.powers (algebraMap (R ⧸ I) N' (fq f I))) _ ρN (powers_le ρN hρN)

lemma ρQ_algebraMap (x : N) :
    ρQ ρN hρN (algebraMap N (Nf f N) x) = algebraMap N' (Nf (fq f I) N') (ρN x) :=
  IsLocalization.map_eq _ _

lemma ρQ_algebraMap_R (r : R) :
    ρQ ρN hρN (algebraMap R (Nf f N) r) =
      algebraMap (R ⧸ I) (Nf (fq f I) N') (Ideal.Quotient.mk I r) := by
  rw [IsScalarTower.algebraMap_apply R N (Nf f N) r, ρQ_algebraMap, hρN,
    ← IsScalarTower.algebraMap_apply]

lemma JNf_le : JNf f J N ≤ (JNf (fq f I) (J' I J) N').comap (ρQ ρN hρN) := by
  rw [JNf, Ideal.map_le_iff_le_comap]
  intro j hj
  rw [Ideal.mem_comap, Ideal.mem_comap, ρQ_algebraMap_R]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hj)

/-- `ρ̄Q : N_f/J → N'_f/J'`. -/
def ρQbar : (Nf f N ⧸ JNf f J N) →+* (Nf (fq f I) N' ⧸ JNf (fq f I) (J' I J) N') :=
  Ideal.quotientMap _ (ρQ ρN hρN) (JNf_le J ρN hρN)

lemma ρQbar_mk (y : Nf f N) :
    ρQbar J ρN hρN (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (ρQ ρN hρN y) :=
  Ideal.quotientMap_mk

section Compat

variable {n n' : ℕ} (hJ : J ^ n = ⊥) (hJ' : J' I J ^ n' = ⊥)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {P' : Type u} [CommRing P'] [Algebra (R ⧸ I) P'] [Algebra.FormallyEtale (R ⧸ I) P']
  (ρP : P →+* P')
  (hρP : ∀ r : R, ρP (algebraMap R P r) = algebraMap (R ⧸ I) P' (Ideal.Quotient.mk I r))
  (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N)
  (α₀' : P' →ₐ[R ⧸ I] Nf (fq f I) N' ⧸ JNf (fq f I) (J' I J) N')
  (hmod : ∀ p, α₀' (ρP p) = ρQbar J ρN hρN (α₀ p))

include hρP hmod in
/-- **The lifts are compatible**: `α'(ρP p) = ρQ(α p)`. -/
theorem lift_compat (p : P) :
    lift (fq f I) (J' I J) hJ' α₀' (ρP p) = ρQ ρN hρN (lift f J hJ α₀ p) := by
  letI : Algebra R (Nf (fq f I) N') :=
    Algebra.compHom _ (algebraMap R (R ⧸ I))
  haveI : IsScalarTower R (R ⧸ I) (Nf (fq f I) N') := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := isAdicComplete_JNf (fq f I) (J' I J) hJ' (N := N')
  let g₁ : P →ₐ[R] Nf (fq f I) N' :=
    { ((lift (fq f I) (J' I J) hJ' α₀').toRingHom.comp ρP) with
      commutes' := fun r ↦ by
        change lift (fq f I) (J' I J) hJ' α₀' (ρP (algebraMap R P r)) = _
        rw [hρP, AlgHom.commutes]
        rfl }
  let g₂ : P →ₐ[R] Nf (fq f I) N' :=
    { ((ρQ ρN hρN).comp (lift f J hJ α₀).toRingHom) with
      commutes' := fun r ↦ by
        change ρQ ρN hρN (lift f J hJ α₀ (algebraMap R P r)) = _
        rw [AlgHom.commutes, ρQ_algebraMap_R]
        rfl }
  have h : g₁ = g₂ := by
    refine EtaleLift.ext_of_comp_eq (JNf (fq f I) (J' I J) N') (AlgHom.ext fun p ↦ ?_)
    change Ideal.Quotient.mk _ (lift (fq f I) (J' I J) hJ' α₀' (ρP p)) =
      Ideal.Quotient.mk _ (ρQ ρN hρN (lift f J hJ α₀ p))
    have h1 := congrArg (fun g ↦ g (ρP p)) (mkₐ_comp_lift (fq f I) (J' I J) hJ' α₀')
    have h2 := congrArg (fun g ↦ g p) (mkₐ_comp_lift f J hJ α₀)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h1 h2
    rw [h1, ← ρQbar_mk J ρN hρN, h2, hmod]
  exact congrArg (fun g ↦ g p) h

include hρP hmod in
/-- **`hcompat` of `FormalGlueingQuot.equiv` for the level-`n` patching**, from the
compatibility modulo `J'` of the identifications `α₀`, `α₀'`. -/
theorem hcompat (p : P) (x : N) (h : lift f J hJ α₀ p = algebraMap N (Nf f N) x) :
    lift (fq f I) (J' I J) hJ' α₀' (ρP p) = algebraMap N' (Nf (fq f I) N') (ρN x) := by
  rw [lift_compat J ρN hρN hJ hJ' ρP hρP α₀ α₀' hmod, h, ρQ_algebraMap]

end Compat

/-! ### The étale part at level `n` -/

section Etale

variable (I) {P : Type u} [CommRing P] [Algebra R P]

/-- `P/IP ≃ (R/I) ⊗_R P` as rings. -/
def quotTensor : (P ⧸ I.map (algebraMap R P)) ≃+* (R ⧸ I) ⊗[R] P :=
  (Algebra.TensorProduct.quotIdealMapEquivTensorQuot P I).toRingEquiv.trans
    (Algebra.TensorProduct.comm R P (R ⧸ I)).toRingEquiv

lemma quotTensor_mk (p : P) : quotTensor I (Ideal.Quotient.mk _ p) = 1 ⊗ₜ p := by
  simp [quotTensor, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]

/-- `P/IP ≃ₐ[R/I] (R/I) ⊗_R P`. -/
def quotTensorₐ : (P ⧸ I.map (algebraMap R P)) ≃ₐ[R ⧸ I] (R ⧸ I) ⊗[R] P :=
  AlgEquiv.ofRingEquiv (f := quotTensor I) fun x ↦ by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : algebraMap (R ⧸ I) (P ⧸ I.map (algebraMap R P)) (Ideal.Quotient.mk I r) =
        Ideal.Quotient.mk _ (algebraMap R P r) := rfl
    rw [h1, quotTensor_mk, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := P) r, ← TensorProduct.smul_tmul,
      Algebra.smul_def, mul_one]
    rfl

/-- **`P/IP` is formally étale over `R/I`** if `P` is formally étale over `R`. -/
theorem formallyEtale_quot [Algebra.FormallyEtale R P] :
    Algebra.FormallyEtale (R ⧸ I) (P ⧸ I.map (algebraMap R P)) :=
  Algebra.FormallyEtale.of_equiv (quotTensorₐ I).symm

variable {I}

lemma isUnit_quot (hfP : IsUnit (algebraMap R P f)) :
    IsUnit (algebraMap (R ⧸ I) (P ⧸ I.map (algebraMap R P)) (fq f I)) :=
  hfP.map (Ideal.Quotient.mk _)

/-- **`P/IP` is finite over `(R/I)_f̄`** in the form of `FormalPatchLevel.finite_patch`. -/
lemma finite_quot
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P)) :
    ∃ s : Finset (P ⧸ I.map (algebraMap R P)), ∀ p, ∃ k : ℕ,
      fq f I ^ k • p ∈ Submodule.span (R ⧸ I) (s : Set (P ⧸ I.map (algebraMap R P))) := by
  classical
  obtain ⟨s, hs⟩ := hP
  refine ⟨s.image (Ideal.Quotient.mk _), fun p ↦ ?_⟩
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective p
  obtain ⟨k, hk⟩ := hs q
  refine ⟨k, ?_⟩
  let g : P →ₗ[R] P ⧸ I.map (algebraMap R P) := (Ideal.Quotient.mkₐ R _).toLinearMap
  have h1 : fq f I ^ k • (Ideal.Quotient.mk _ q : P ⧸ I.map (algebraMap R P)) = g (f ^ k • q) := by
    rw [LinearMap.map_smul]
    rfl
  rw [h1]
  have h2 : g (f ^ k • q) ∈ Submodule.span R (g '' (s : Set P)) := by
    rw [← Submodule.map_span]
    exact Submodule.mem_map_of_mem hk
  have h3 : Submodule.span R (g '' (s : Set P)) ≤
      (Submodule.span (R ⧸ I) (↑(s.image (Ideal.Quotient.mk (I.map (algebraMap R P)))) :
        Set (P ⧸ I.map (algebraMap R P)))).restrictScalars R := by
    rw [Submodule.span_le, Finset.coe_image]
    exact Submodule.subset_span
  exact h3 h2

end Etale

end

end FormalPatchCompat

end SemistableReduction
