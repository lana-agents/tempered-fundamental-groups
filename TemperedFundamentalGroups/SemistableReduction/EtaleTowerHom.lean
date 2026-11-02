/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleTower

/-!
# Functoriality of the étale lifts of special-fibre coverings (MR12 I3, generic core, layer 1)

In the setting of `EtaleTower` (a chart `T` over `O`, its levels `Tn n`, its special fibre `Ts`,
coverings `C`, `C'` of `Ts` étale over `D(b̄)`), an algebra map `φ : C → C'` over `Ts` lifts
uniquely to the étale lifts: for lifts `L` of `C` and `L'` of `C'` at level `n`,
**`EtaleTower.homLift φ L L' : L.E → L'.E`** is the unique `Tn n`-algebra map reducing to
`φ[1/b̄]` under the identifications `σ` (**`σ_homLift`**, uniqueness **`eq_homLift`**). It is
functorial (**`homLift_id`**, **`homLift_comp`**) and commutes with the successor maps of the
towers (**`succ_comp_homLift`**).

This is the étale part (away from the nodes and the marked points) of the lifting of morphisms of
special-fibre data to the M2 levels, shared by the Tate curve (MR12) and the `ℙ¹` model (MR13).
-/

universe u

namespace SemistableReduction

open AdmissibleLift (J)

namespace EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k} {ϖ : O}
  (T : Type u) [CommRing T] [Algebra O T] (hϖ : θ ϖ = 0) (b : T)
  {C C' C'' : Type u} [CommRing C] [CommRing C'] [CommRing C''] [Algebra (Ts θ T) C]
  [Algebra (Ts θ T) C'] [Algebra (Ts θ T) C'']

lemma isUnit_CbMap (φ : C →ₐ[Ts θ T] C') :
    IsUnit ((algebraMap C' (Cb θ T C' b)).comp φ.toRingHom
      (algebraMap (Ts θ T) C (Ideal.Quotient.mk _ b))) := by
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The map `C[1/b̄] → C'[1/b̄]` induced by `φ`. -/
def CbMap (φ : C →ₐ[Ts θ T] C') : Cb θ T C b →+* Cb θ T C' b :=
  IsLocalization.Away.lift (algebraMap (Ts θ T) C (Ideal.Quotient.mk _ b)) (isUnit_CbMap T b φ)

lemma CbMap_algebraMap (φ : C →ₐ[Ts θ T] C') (c : C) :
    CbMap T b φ (algebraMap C _ c) = algebraMap C' _ (φ c) :=
  IsLocalization.Away.lift_eq _ _ c

lemma CbMap_id : CbMap T b (AlgHom.id (Ts θ T) C) = RingHom.id _ :=
  IsLocalization.ringHom_ext (Submonoid.powers (algebraMap (Ts θ T) C (Ideal.Quotient.mk _ b)))
    (RingHom.ext fun c ↦ by
      rw [RingHom.comp_apply, CbMap_algebraMap, RingHom.comp_apply]; rfl)

lemma CbMap_comp (φ : C →ₐ[Ts θ T] C') (ψ : C' →ₐ[Ts θ T] C'') :
    CbMap T b (ψ.comp φ) = (CbMap T b ψ).comp (CbMap T b φ) :=
  IsLocalization.ringHom_ext (Submonoid.powers (algebraMap (Ts θ T) C (Ideal.Quotient.mk _ b)))
    (RingHom.ext fun c ↦ by
      rw [RingHom.comp_apply, CbMap_algebraMap, RingHom.comp_apply, RingHom.comp_apply,
        CbMap_algebraMap, CbMap_algebraMap, AlgHom.comp_apply])

/-- `CbMap φ` as an algebra map over the level `Tn n`. -/
def CbMapₐ (n : ℕ) (φ : C →ₐ[Ts θ T] C') :
    letI := algC T hϖ C n; letI := algC T hϖ C' n
    Cb θ T C b →ₐ[Tn ϖ T n] Cb θ T C' b :=
  letI := algC T hϖ C n
  letI := algC T hϖ C' n
  { toRingHom := CbMap T b φ
    commutes' := fun r ↦ by
      rw [IsScalarTower.algebraMap_apply (Tn ϖ T n) C (Cb θ T C b),
        IsScalarTower.algebraMap_apply (Tn ϖ T n) C' (Cb θ T C' b)]
      change CbMap T b φ (algebraMap C _ (algebraMap (Ts θ T) C (q T hϖ n r))) =
        algebraMap C' _ (algebraMap (Ts θ T) C' (q T hϖ n r))
      rw [CbMap_algebraMap, AlgHom.commutes] }

lemma CbMapₐ_apply (n : ℕ) (φ : C →ₐ[Ts θ T] C') (x : Cb θ T C b) :
    CbMapₐ T hϖ b n φ x = CbMap T b φ x :=
  rfl

variable (hker : RingHom.ker θ ≤ Ideal.span {ϖ})

/-- **The lift of `φ : C → C'` to étale lifts `L`, `L'` at level `n`.** -/
def homLift {n : ℕ} (φ : C →ₐ[Ts θ T] C') (L : Lift T hϖ C b n) (L' : Lift T hϖ C' b n) :
    L.E →ₐ[Tn ϖ T n] L'.E :=
  letI := algC T hϖ C n
  letI := algC T hϖ C' n
  EtaleNil.lift (J θ (R := Tn ϖ T n)) (hJ hker n)
    (L'.σ.symm.toAlgHom.comp ((CbMapₐ T hϖ b n φ).comp
      (L.σ.toAlgHom.comp (Ideal.Quotient.mkₐ _ _))))

/-- **`homLift φ` reduces to `φ[1/b̄]`.** -/
lemma σ_homLift {n : ℕ} (φ : C →ₐ[Ts θ T] C') (L : Lift T hϖ C b n) (L' : Lift T hϖ C' b n)
    (x : L.E) :
    L'.σ (Ideal.Quotient.mk _ (homLift T hϖ b hker φ L L' x)) =
      CbMap T b φ (L.σ (Ideal.Quotient.mk _ x)) := by
  letI := algC T hϖ C n
  letI := algC T hϖ C' n
  have h := EtaleNil.mk_lift (J θ (R := Tn ϖ T n)) (hJ hker n)
    (L'.σ.symm.toAlgHom.comp ((CbMapₐ T hϖ b n φ).comp
      (L.σ.toAlgHom.comp (Ideal.Quotient.mkₐ _ _)))) x
  change L'.σ (Ideal.Quotient.mk _ (EtaleNil.lift _ _ _ x)) = _
  rw [h]
  exact L'.σ.apply_symm_apply _

/-- **Uniqueness**: a `Tn n`-algebra map `L.E → L'.E` reducing to `φ[1/b̄]` is `homLift φ`. -/
lemma eq_homLift {n : ℕ} (φ : C →ₐ[Ts θ T] C') (L : Lift T hϖ C b n) (L' : Lift T hϖ C' b n)
    (g : L.E →ₐ[Tn ϖ T n] L'.E)
    (hg : ∀ x, L'.σ (Ideal.Quotient.mk _ (g x)) = CbMap T b φ (L.σ (Ideal.Quotient.mk _ x))) :
    g = homLift T hϖ b hker φ L L' :=
  letI := algC T hϖ C n
  letI := algC T hϖ C' n
  EtaleNil.ext (J θ (R := Tn ϖ T n)) (hJ hker n) fun x ↦ L'.σ.injective (by
    rw [hg, σ_homLift])

/-- **`homLift` of the identity.** -/
lemma homLift_id {n : ℕ} (L : Lift T hϖ C b n) :
    homLift T hϖ b hker (AlgHom.id (Ts θ T) C) L L = AlgHom.id _ _ :=
  (eq_homLift T hϖ b hker _ L L _ fun x ↦ by
    rw [CbMap_id]; rfl).symm

/-- **`homLift` of a composition.** -/
lemma homLift_comp {n : ℕ} (φ : C →ₐ[Ts θ T] C') (ψ : C' →ₐ[Ts θ T] C'')
    (L : Lift T hϖ C b n) (L' : Lift T hϖ C' b n) (L'' : Lift T hϖ C'' b n) :
    homLift T hϖ b hker (ψ.comp φ) L L'' =
      (homLift T hϖ b hker ψ L' L'').comp (homLift T hϖ b hker φ L L') :=
  (eq_homLift T hϖ b hker _ L L'' _ fun x ↦ by
    rw [AlgHom.comp_apply, σ_homLift, σ_homLift, CbMap_comp, RingHom.comp_apply]).symm

/-- **`homLift` commutes with the successor maps of the towers.** -/
lemma succ_comp_homLift {n : ℕ} (φ : C →ₐ[Ts θ T] C') (L₁ : Lift T hϖ C b (n + 1))
    (L : Lift T hϖ C b n) (L₁' : Lift T hϖ C' b (n + 1)) (L' : Lift T hϖ C' b n) (x : L₁.E) :
    succ T hϖ C' b hker L₁' L' (homLift T hϖ b hker φ L₁ L₁' x) =
      homLift T hϖ b hker φ L L' (succ T hϖ C b hker L₁ L x) := by
  letI := algE T hϖ C' b L'
  haveI := isScalarTower_E T hϖ C' b L'
  letI := algE T hϖ C b L
  haveI := isScalarTower_E T hϖ C b L
  letI := algC T hϖ C' n
  letI := algC T hϖ C' (n + 1)
  letI := algC T hϖ C n
  letI := algC T hϖ C (n + 1)
  let g₁ : L₁.E →ₐ[Tn ϖ T (n + 1)] L'.E :=
    (succ T hϖ C' b hker L₁' L').comp (homLift T hϖ b hker φ L₁ L₁')
  let g₂ : L₁.E →ₐ[Tn ϖ T (n + 1)] L'.E :=
    ((homLift T hϖ b hker φ L L').restrictScalars (Tn ϖ T (n + 1))).comp
      (succ T hϖ C b hker L₁ L)
  have h : g₁ = g₂ := EtaleNil.ext (J θ (R := Tn ϖ T (n + 1))) (hJ hker (n + 1)) fun y ↦ by
    have hJE := JE_succ (θ := θ) (ϖ := ϖ) T n L'.E
    have key : L'.σ (Ideal.Quotient.mk _ (g₁ y)) = L'.σ (Ideal.Quotient.mk _ (g₂ y)) := by
      change L'.σ (Ideal.Quotient.mk _ (succ T hϖ C' b hker L₁' L'
          (homLift T hϖ b hker φ L₁ L₁' y))) =
        L'.σ (Ideal.Quotient.mk _ (homLift T hϖ b hker φ L L' (succ T hϖ C b hker L₁ L y)))
      rw [σ_succ, σ_homLift, σ_homLift, σ_succ]
    have := L'.σ.injective key
    rw [Ideal.Quotient.eq] at this ⊢
    rw [show EtaleNil.JB (J θ (R := Tn ϖ T (n + 1))) L'.E = JE θ ϖ T n L'.E from hJE]
    exact this
  change g₁ x = g₂ x
  exact AlgHom.congr_fun h x

end

end EtaleTower

end SemistableReduction
