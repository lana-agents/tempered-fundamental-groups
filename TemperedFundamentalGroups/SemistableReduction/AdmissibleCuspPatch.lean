/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AdmissibleCusp

/-!
# Level-`n` patching of an admissible covering with marked points (Blueprint §12.8, M2.3)

`AdmissibleLift.patch_spec` patches an admissible covering of a chart **without** marked points.
Here the cusp factors (`Admissible.CuspPiece`, tame ramification over the marked points,
[Mzk1] §3.9 (1′A)) are added: with lift data `L : KummerLift cov` of the Kummer factors and
`M : CuspLift cov` of the cusp factors (a lift `t̃ ∈ R̂` of the coordinate `ψ(X)` at the marked
points and idempotent lifts `δ̃_i`), the lifted formal model is the product over `ι ⊕ κ`

  `NF = ∏_j (R̂/(1 − ε̃_j)) ⊗ O[s,t]/(st − π_j) × ∏_i (R̂/(1 − δ̃_i))[X]/(X^{e'_i} − t̃)`,

* **`AdmissibleLift.kappaF`**: `R̂ ⊗_R C ≃ NF/J NF` (the completed special-fibre covering is the
  reduction of `NF`; `pieceEquiv` on the Kummer factors, `cuspEquiv` on the cusp factors);
* **`AdmissibleLift.patch_specF`**: if `f` is a nonzerodivisor on `R̂`, the patched algebra is
  finite over `R`, equal to `P` on `D(f)`, and to `NF` on the formal neighbourhood of `V(f)`.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace AdmissibleLift

noncomputable section

open KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {f : R} [Algebra k (R ⧸ J θ)]
  {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ f)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ f)}

variable (cov : Admissible.Covering φ ψc)

/-- **Lift data of the cusp factors**: a lift `t̃ ∈ R̂` of the coordinate at the marked points and
lifts `δ̃_i` of the idempotents selecting them. -/
structure CuspLift where
  /-- The lifted coordinate at the marked points. -/
  t : FormalPatchLevel.Hat f
  ht : ψ θ f t = ψc X
  /-- The lifted idempotents. -/
  δ : cov.κ → FormalPatchLevel.Hat f
  hδ : ∀ i, ψ θ f (δ i) = cov.cidem i

variable {cov} (L : KummerLift cov) (M : CuspLift cov)

/-- The factors of the lifted formal model, indexed by `ι ⊕ κ`. -/
def NF : cov.ι ⊕ cov.κ → Type u
  | .inl j => N f (L.χ j) (L.ε j)
  | .inr i => CPiece f (M.δ i) M.t (cov.ce i)

instance NF.commRing : ∀ s, CommRing (NF L M s)
  | .inl j => inferInstanceAs (CommRing (N f (L.χ j) (L.ε j)))
  | .inr i => inferInstanceAs (CommRing (CPiece f (M.δ i) M.t (cov.ce i)))

instance NF.algebraHat : ∀ s, Algebra (FormalPatchLevel.Hat f) (NF L M s)
  | .inl j => inferInstanceAs (Algebra (FormalPatchLevel.Hat f) (N f (L.χ j) (L.ε j)))
  | .inr i => inferInstanceAs (Algebra (FormalPatchLevel.Hat f) (CPiece f (M.δ i) M.t (cov.ce i)))

instance NF.algebraR (s : cov.ι ⊕ cov.κ) : Algebra R (NF L M s) :=
  Algebra.compHom _ (algebraMap R (FormalPatchLevel.Hat f))

instance NF.isScalarTower (s : cov.ι ⊕ cov.κ) :
    @IsScalarTower R (FormalPatchLevel.Hat f) (NF L M s) _ Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The lifted formal model `NF = ∏_{ι ⊕ κ} NF_s`. -/
abbrev NFall : Type u := ∀ s, NF L M s

variable (cov) in
/-- The factors of the special-fibre model, indexed by `ι ⊕ κ`. -/
def Red : cov.ι ⊕ cov.κ → Type u
  | .inl j => Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)
  | .inr i => Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i)

instance Red.commRing : ∀ s, CommRing (Red cov s)
  | .inl j => inferInstanceAs (CommRing (Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)))
  | .inr i => inferInstanceAs (CommRing (Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i)))

variable (cov) in
/-- `∏_{ι ⊕ κ} Red_s ≃ ∏_j KummerPiece × ∏_i CuspPiece`. -/
def sumPi : (∀ s, Red cov s) ≃+* ((∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) ×
    (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i))) where
  toFun x := (fun j ↦ x (.inl j), fun i ↦ x (.inr i))
  invFun p s := match s with
    | .inl j => p.1 j
    | .inr i => p.2 i
  left_inv x := funext fun s ↦ by cases s <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable (hθ : Function.Surjective θ)

/-- The factorwise reduction equivalences `NF_s/J ≃ Red_s`. -/
def redF [IsNoetherianRing R] :
    ∀ s, (NF L M s ⧸ (J θ).map (algebraMap R (NF L M s))) ≃+* Red cov s
  | .inl j => (Ideal.quotEquivOfEq (JN_eq f (L.χ j) (L.ε j))).trans
      (pieceEquiv f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) hθ (L.hπ j) (L.hχ j))
  | .inr i => cuspEquiv θ f ψc (M.δ i) M.t (cov.cidem i) (M.hδ i) M.ht (cov.ce i)

/-- **`NF/J ≃ ∏_j KummerPiece × ∏_i CuspPiece`.** -/
def kappa3F [IsNoetherianRing R] :
    (NFall L M ⧸ (J θ).map (algebraMap R (NFall L M))) ≃+*
      ((∀ j, Admissible.KummerPiece φ (cov.idem j) (cov.e_pos j)) ×
        (∀ i, Admissible.CuspPiece ψc (cov.cidem i) (cov.ce i))) :=
  (PiQuot.equiv (J θ) (NF L M)).trans
    ((RingEquiv.piCongrRight (redF L M hθ)).trans (sumPi cov))

lemma kappa3F_algebraMap [IsNoetherianRing R] (x : FormalPatchLevel.Hat f) :
    kappa3F L M hθ (Ideal.Quotient.mk _ (algebraMap (FormalPatchLevel.Hat f) (NFall L M) x)) =
      algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f x) := by
  refine Prod.ext (funext fun j ↦ ?_) (funext fun i ↦ ?_)
  · change pieceEquiv f φ (cov.e_pos j) (L.χ j) (L.ε j) (cov.idem j) (L.hε j) hθ (L.hπ j)
      (L.hχ j) (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ x ⊗ₜ 1)) = _
    rw [pieceEquiv_mk_tmul, σ_mk, map_one]
    rfl
  · exact cuspEquiv_algebraMap θ f ψc (M.δ i) M.t (cov.cidem i) (M.hδ i) M.ht (cov.ce i) x

lemma kummer_algebraMap' [IsNoetherianRing R] (x : FormalPatchLevel.Hat f) :
    cov.kummer (TensorQuotBase.equiv (C := cov.C) (surjective_ψ θ f) (ker_ψ θ f)
      (algebraMap (FormalPatchLevel.Hat f) (FormalPatchLevel.Hat f ⊗[R] cov.C) x)) =
      algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f x) := by
  have h0 : algebraMap (FormalPatchLevel.Hat f) (FormalPatchLevel.Hat f ⊗[R] cov.C) x =
      x ⊗ₜ 1 := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h0, TensorQuotBase.equiv_tmul]
  have h2 : (ψ θ f x ⊗ₜ[R ⧸ J θ] (1 : cov.C)) =
      algebraMap (Admissible.Hat (fbar θ f)) _ (ψ θ f x) := rfl
  rw [h2, AlgEquiv.commutes]

/-- **The comparison `κ : R̂ ⊗_R C ≃ NF/J NF`** for an admissible covering with marked points. -/
def kappaF [IsNoetherianRing R] :
    (FormalPatchLevel.Hat f ⊗[R] cov.C) ≃ₐ[FormalPatchLevel.Hat f]
      (NFall L M ⧸ (J θ).map (algebraMap R (NFall L M))) :=
  AlgEquiv.ofRingEquiv (f := ((TensorQuotBase.equiv (C := cov.C) (surjective_ψ θ f)
      (ker_ψ θ f)).trans cov.kummer.toRingEquiv).trans (kappa3F L M hθ).symm) fun x ↦ by
    apply (kappa3F L M hθ).injective
    rw [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, RingEquiv.trans_apply,
      AlgEquiv.coe_ringEquiv, kummer_algebraMap']
    exact (kappa3F_algebraMap L M hθ x).symm

/-- **Level-`n` patching of an admissible covering with marked points**: the patched algebra is
finite over the chart, equal to the étale lift `P` on `D(f)`, and to the lifted formal model `NF`
(Kummer factors at the nodes, cusp factors at the marked points) along `V(f)`. -/
theorem patch_specF [IsNoetherianRing R] (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ}
    (hJ : J θ (R := R) ^ n = ⊥)
    (hflat : ∀ j, (L.χ j).toRingHom.Flat) (hidem : ∀ j, IsIdempotentElem (L.ε j))
    (hf : ∀ j, L.χ j (fA (L.π j)) = algebraMap R (FormalPatchLevel.Hat f) f)
    (hcidem : ∀ i, IsIdempotentElem (M.δ i))
    (hreg : ∀ y : FormalPatchLevel.Hat f, algebraMap R _ f * y = 0 → y = 0)
    {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
    (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R cov.C f))
    (hfP : IsUnit (algebraMap R P f))
    (hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f ^ k • p ∈ Submodule.span R (s : Set P)) :
    let α₀ := FormalPatchLevel.alphaOfEquiv f (J θ)
      (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappaF L M hθ))
    Module.Finite R (FormalPatchLevel.patch f (J θ) hJ α₀) ∧
      (letI := FormalGlueing.algebraFst (NFall L M) (FormalPatchLevel.lift f (J θ) hJ α₀);
        IsLocalization.Away (algebraMap R (FormalPatchLevel.patch f (J θ) hJ α₀) f) P) ∧
      IsBaseChange (FormalPatchLevel.Hat f)
        (FormalGlueing.snd (NFall L M) (FormalPatchLevel.lift f (J θ) hJ α₀)).toLinearMap := by
  intro α₀
  haveI : Module.Flat (FormalPatchLevel.Hat f) (FormalPatchLevel.Nf f (NFall L M)) :=
    FormalPatchProd.flat_localization f _ fun s ↦ match s with
      | .inl j => flat_loc (L.χ j) (cov.e_pos j) (isUnit_e θ hO j) (hflat j) (hidem j) (hf j)
      | .inr i => flat_loc_CPiece M.t (cov.ce_pos i) (hcidem i)
  haveI : ∀ s, Module.Finite (FormalPatchLevel.Hat f) (NF L M s) := fun s ↦ match s with
    | .inl j => finite_N (L.χ j) (cov.e_pos j)
    | .inr i => finite_CPiece M.t (cov.ce_pos i)
  have hN : ∀ x : NFall L M, algebraMap R (NFall L M) f * x = 0 → x = 0 :=
    FormalPatchProd.eq_zero_of_mul_eq_zero f fun s ↦ match s with
      | .inl j => noTorsion (L.χ j) (cov.e_pos j) (hflat j) (hidem j) (hf j)
      | .inr i => noTorsion_CPiece M.t (cov.ce_pos i) (hcidem i) hreg
  have hsurj := FormalPatchLevel.surjective_betaMod_alphaOfEquiv
    (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappaF L M hθ))
  have hinj := FormalPatchLevel.mem_of_betaMod_alphaOfEquiv_eq_zero
    (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappaF L M hθ))
  exact ⟨FormalPatchLevel.finite_patch f (J θ) hJ hfP hN α₀ hsurj hinj hP,
    FormalPatchLevel.isLocalization_patch f (J θ) hJ α₀ hfP,
    FormalPatchLevel.isBaseChange_patch f (J θ) hJ hfP hN α₀ hsurj hinj⟩

end

end AdmissibleLift

end SemistableReduction
