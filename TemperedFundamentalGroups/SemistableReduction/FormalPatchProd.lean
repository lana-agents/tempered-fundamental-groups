/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Group.Pi.Units
import TemperedFundamentalGroups.SemistableReduction.FormalPatchLevel

/-!
# Products of formal models (Blueprint §12.8, M2.3 (d'))

An admissible covering of the special fibre is, formally along the nodes, a **product** of Kummer
factors `∏_j (R̂/(1 − ε_j)) ⊗_A B_{e_j}` with different ramification indices `e_j`
(`Admissible.Covering`). The level-`n` patching (`FormalPatchLevel`) needs of the formal model
`N` over `R̂`: no `f`-torsion, finiteness, and `N_f` flat over `R̂`. These pass to finite products:

* `FormalPatchProd.eq_zero_of_mul_eq_zero`: no `f`-torsion, componentwise;
* **`FormalPatchProd.isLocalization_toPiLoc`**: `(∏_j N_j)_f = ∏_j (N_j)_f` (finite index set);
* `FormalPatchProd.flat_quotient_one_sub`: `S/(1 − ε)` is flat over `A` if `S` is (`ε`
  idempotent; the bases of the Kummer factors);
* **`FormalPatchProd.flat_localization`**: if every `(N_j)_f` is flat over `R̂`, so is
  `(∏_j N_j)_f` (Mathlib `Module.Flat.directSum_iff`).

Finiteness of a finite product of finite modules is a Mathlib instance.
-/

universe u

namespace SemistableReduction

namespace FormalPatchProd

noncomputable section

variable {R : Type u} [CommRing R] (f : R) {ι : Type} [Finite ι] (N : ι → Type u)
  [∀ j, CommRing (N j)] [∀ j, Algebra R (N j)]

omit [Finite ι] in
variable {N} in
/-- **No `f`-torsion on a product.** -/
theorem eq_zero_of_mul_eq_zero (h : ∀ j (x : N j), algebraMap R (N j) f * x = 0 → x = 0)
    (x : ∀ j, N j) (hx : algebraMap R (∀ j, N j) f * x = 0) : x = 0 :=
  funext fun j ↦ h j (x j) (by simpa using congrFun hx j)

/-- The componentwise localization map `∏_j N_j → ∏_j (N_j)_f`. -/
def toPiLoc : (∀ j, N j) →+* ∀ j, Localization.Away (algebraMap R (N j) f) :=
  RingHom.pi fun j ↦ (algebraMap (N j) _).comp (Pi.evalRingHom N j)

omit [Finite ι] in
lemma toPiLoc_apply (x : ∀ j, N j) (j : ι) :
    toPiLoc f N x j = algebraMap (N j) (Localization.Away (algebraMap R (N j) f)) (x j) := rfl

omit [Finite ι] in
lemma toPiLoc_algebraMap_pow (k : ℕ) (j : ι) :
    toPiLoc f N (algebraMap R (∀ j, N j) f ^ k) j =
      algebraMap (N j) (Localization.Away (algebraMap R (N j) f)) (algebraMap R (N j) f) ^ k := by
  rw [toPiLoc_apply, Pi.pow_apply, map_pow]
  rfl

/-- **`(∏_j N_j)_f = ∏_j (N_j)_f`.** -/
theorem isLocalization_toPiLoc :
    letI := (toPiLoc f N).toAlgebra
    IsLocalization.Away (algebraMap R (∀ j, N j) f)
      (∀ j, Localization.Away (algebraMap R (N j) f)) := by
  letI := (toPiLoc f N).toAlgebra
  classical
  cases nonempty_fintype ι
  rw [IsLocalization.Away, _root_.isLocalization_iff]
  refine ⟨?_, fun z ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · rintro ⟨_, k, rfl⟩
    refine Pi.isUnit_iff.mpr fun j ↦ ?_
    change IsUnit (toPiLoc f N (algebraMap R (∀ j, N j) f ^ k) j)
    rw [toPiLoc_algebraMap_pow]
    exact (IsLocalization.Away.algebraMap_isUnit _).pow k
  · choose p hp using fun j ↦ IsLocalization.surj (Submonoid.powers (algebraMap R (N j) f)) (z j)
    choose k hk using fun j ↦ (p j).2.2
    set K := Finset.univ.sup k
    have hle : ∀ j, k j ≤ K := fun j ↦ Finset.le_sup (Finset.mem_univ j)
    refine ⟨⟨fun j ↦ (p j).1 * algebraMap R (N j) f ^ (K - k j),
      ⟨algebraMap R (∀ j, N j) f ^ K, K, rfl⟩⟩, funext fun j ↦ ?_⟩
    change z j * toPiLoc f N (algebraMap R (∀ j, N j) f ^ K) j = toPiLoc f N _ j
    rw [toPiLoc_algebraMap_pow, toPiLoc_apply, map_mul, map_pow, ← hp j, ← hk j]
    simp only [map_pow]
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (hle j)]
  · have hj : ∀ j, algebraMap (N j) (Localization.Away (algebraMap R (N j) f)) (x j) =
        algebraMap (N j) (Localization.Away (algebraMap R (N j) f)) (y j) := fun j ↦ by
      have := congrFun hxy j
      exact this
    choose c hc using fun j ↦ IsLocalization.exists_of_eq (M := Submonoid.powers
      (algebraMap R (N j) f)) (hj j)
    choose k hk using fun j ↦ (c j).2
    set K := Finset.univ.sup k
    have hle : ∀ j, k j ≤ K := fun j ↦ Finset.le_sup (Finset.mem_univ j)
    refine ⟨⟨algebraMap R (∀ j, N j) f ^ K, K, rfl⟩, funext fun j ↦ ?_⟩
    have h := hc j
    rw [← hk j] at h
    change (algebraMap R (N j) f) ^ K * x j = (algebraMap R (N j) f) ^ K * y j
    rw [← Nat.add_sub_cancel' (hle j), pow_add, mul_comm (_ ^ k j), mul_assoc, mul_assoc, h]

/-- **`S/(1 − ε)` is flat over `A` if `S` is**, for an idempotent `ε` (the base of a Kummer factor
of an admissible covering): `x ↦ εx` splits the projection `S → S/(1 − ε)`. -/
theorem flat_quotient_one_sub {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    [Module.Flat A S] {ε : S} (hε : IsIdempotentElem ε) :
    Module.Flat A (S ⧸ Ideal.span {1 - ε}) := by
  let i₀ : (S ⧸ Ideal.span {1 - ε}) →ₗ[S] S :=
    (Ideal.span {1 - ε}).liftQ (LinearMap.mulLeft S ε) fun x hx ↦ by
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [LinearMap.mem_ker, LinearMap.mulLeft_apply, mul_comm y, ← mul_assoc, mul_sub, mul_one,
        hε.eq, sub_self, zero_mul]
  refine Module.Flat.of_retract (i₀.restrictScalars A)
    ((Ideal.span {1 - ε}).mkQ.restrictScalars A) (LinearMap.ext fun x ↦ ?_)
  obtain ⟨s, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ε * s) = Submodule.Quotient.mk s
  rw [Submodule.Quotient.eq]
  exact Ideal.mem_span_singleton'.mpr ⟨-s, by ring⟩

variable [∀ j, Algebra (FormalPatchLevel.Hat f) (N j)]
  [∀ j, IsScalarTower R (FormalPatchLevel.Hat f) (N j)]

omit [∀ j, IsScalarTower R (FormalPatchLevel.Hat f) (N j)] in
/-- **`(∏_j N_j)_f` is flat over `R̂` if every `(N_j)_f` is.** -/
theorem flat_localization
    (hN : ∀ j, Module.Flat (FormalPatchLevel.Hat f) (Localization.Away (algebraMap R (N j) f))) :
    Module.Flat (FormalPatchLevel.Hat f) (Localization.Away (algebraMap R (∀ j, N j) f)) := by
  cases nonempty_fintype ι
  letI := (toPiLoc f N).toAlgebra
  haveI := isLocalization_toPiLoc f N
  let e := IsLocalization.algEquiv (Submonoid.powers (algebraMap R (∀ j, N j) f))
    (Localization.Away (algebraMap R (∀ j, N j) f)) (∀ j, Localization.Away (algebraMap R (N j) f))
  let e' : Localization.Away (algebraMap R (∀ j, N j) f) ≃ₗ[FormalPatchLevel.Hat f]
      ∀ j, Localization.Away (algebraMap R (N j) f) :=
    { e.toAddEquiv with
      map_smul' := fun r x ↦ by
        change e (r • x) = r • e x
        rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (FormalPatchLevel.Hat f)
          (∀ j, N j), map_mul, AlgEquiv.commutes]
        funext j
        rw [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def]
        change toPiLoc f N _ j * _ = _
        rw [toPiLoc_apply, Pi.algebraMap_apply, ← IsScalarTower.algebraMap_apply] }
  haveI : Module.Flat (FormalPatchLevel.Hat f)
      (DirectSum ι fun j ↦ Localization.Away (algebraMap R (N j) f)) :=
    Module.Flat.directSum_iff.mpr hN
  haveI : Module.Flat (FormalPatchLevel.Hat f) (∀ j, Localization.Away (algebraMap R (N j) f)) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype (FormalPatchLevel.Hat f) ι
      (fun j ↦ Localization.Away (algebraMap R (N j) f))).symm
  exact Module.Flat.of_linearEquiv e'

end

end FormalPatchProd

end SemistableReduction
