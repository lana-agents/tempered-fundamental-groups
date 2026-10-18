/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelEtale
import TemperedFundamentalGroups.SemistableReduction.FormalPatchCompat
import TemperedFundamentalGroups.SemistableReduction.FormalPatchReduction

/-!
# The level-`(n+1)` patch reduces to the level-`n` patch (Blueprint §12.8, M2.3 (e'))

In the setting of `LevelBase` (the coverings `cov₀.transport e₁`, `cov₀.transport e₂` of the
special fibres of consecutive levels `R → R'`), with lift data `L, M` (level `n + 1`) and `L', M'`
(level `n`) related by reduction (`ψ_q ∘ χ_j = χ'_j`, ...):

* `LevelStep.ρN`: the reduction of the full lifted model (`KummerReduce.ρF`);
* **`kappa3F_ρN`**, **`kappaF_one_tmul`**: the comparisons `κ : R̂ ⊗_R C ≅ NF/J` of the two levels
  are compatible (`κ(1 ⊗ c) = x mod J ⇒ κ'(1 ⊗ c) = ρN x mod J'`), from `pieceEquiv_ρ_base`,
  `cuspEquiv_ρc_base` and the transports;
* **`hmod`**: the patching data `α₀ = alphaOfEquiv (specialFibreEquiv σ κ)` agree modulo `J'`
  (through `ρP`, `ρN`; `FormalPatchLevel.alphaOfEquiv_spec`, cancelling a power of `f`);
* **`stepEquiv`**: `R' ⊗_R G_{n+1} ≅ G_n` for the patched algebras (`FormalGlueingQuot.equiv`
  with `FormalPatchCompat.hcompat`, `ρP` from `LevelEtale`, `ρN` from `KummerReduce`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

namespace LevelStep

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R)
  [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))} {e₂ : R₀ ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (h₁ : e₁ f₀ = fbar θ f)
  (he : ∀ r : R, e₂ (e₁.symm (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R R' r))

variable {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}

/-! ### The full lifted models and the comparison `κ` -/

section Model

variable [IsNoetherianRing R] [IsNoetherianRing R']
  (hθ : Function.Surjective θ) (cov₀ : Admissible.Covering φ₀ ψ₀)
  {πL : cov₀.ι → O} (L : KummerLift (cov₀.transport (h := h₁)) πL) (M : CuspLift (cov₀.transport (h
      := h₁)))
  (L' : KummerLift (cov₀.transport (h := h₂ f h₁ he)) πL) (M' : CuspLift (cov₀.transport (h := h₂ f
      h₁ he)))
  (hχχ : ∀ j a, KummerReduce.ψI f (L.χ j a) = L'.χ j a)
  (hεε : ∀ j, KummerReduce.ψI f (L.ε j) = L'.ε j)
  (hδδ : ∀ i, KummerReduce.ψI f (M.δ i) = M'.δ i) (htt : KummerReduce.ψI f M.t = M'.t)

/-- The reduction `NF → NF'` of the full lifted model. -/
abbrev ρN : NFall L M →+* NFall L' M' :=
  KummerReduce.ρF L.χ L.ε M.δ M.t cov₀.ce L'.χ L'.ε M'.δ M'.t hχχ hεε hδδ htt

/-- **`κ₃` at consecutive levels**: `κ₃'(ρN x) = (transport)(κ₃ x)`. -/
theorem kappa3F_ρN (x : NFall L M) :
    kappa3F L' M' hθ (Ideal.Quotient.mk _ (ρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt x)) =
      Admissible.piecesEquiv (h := h₂ f h₁ he) cov₀
        ((Admissible.piecesEquiv (h := h₁) cov₀).symm (kappa3F L M hθ (Ideal.Quotient.mk _ x))) :=
            by
  refine Prod.ext (funext fun j ↦ ?_) (funext fun i ↦ ?_)
  · exact pieceEquiv_ρ_base f h₁ he hθ (cov₀.e_pos j) (L.hπ j) (cov₀.idem j) (L.χ j) (L.ε j)
      (L.hε j) (L.hχ j) (L'.χ j) (L'.ε j) (L'.hε j) (L'.hχ j) (hχχ j) (hεε j) (x (.inl j))
  · exact cuspEquiv_ρc_base f h₁ he (cov₀.cidem i) (M.δ i) M.t (M.hδ i) M.ht (cov₀.ce i) (M'.δ i)
      M'.t (M'.hδ i) M'.ht (hδδ i) htt (x (.inr i))

omit [IsNoetherianRing R'] in
lemma kappaF_apply (y : FormalPatchLevel.Hat f ⊗[R] (cov₀.transport (h := h₁)).C) :
    kappaF L M hθ y = (kappa3F L M hθ).symm
      ((cov₀.transport (h := h₁)).kummer (TensorQuotBase.equiv (C := (cov₀.transport (h := h₁)).C)
          (surjective_ψ θ f) (ker_ψ θ f) y)) := rfl

lemma kappa3F_kappaF (y : FormalPatchLevel.Hat f ⊗[R] (cov₀.transport (h := h₁)).C) :
    kappa3F L M hθ (kappaF L M hθ y) =
      (cov₀.transport (h := h₁)).kummer (TensorQuotBase.equiv (C := (cov₀.transport (h := h₁)).C)
          (surjective_ψ θ f) (ker_ψ θ f) y) := by
  change kappa3F L M hθ ((kappa3F L M hθ).symm _) = _
  rw [RingEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 3000000 in
-- unifying the products of Kummer and cusp factors of the transported covering with the
-- transported products unfolds `Covering.transport`; slow at the default limits
set_option synthInstance.maxHeartbeats 200000 in
-- (same reason, for instance search on these products)
/-- **The comparisons `κ` at consecutive levels are compatible**: if `κ(1 ⊗ c) = x mod J`, then
`κ'(1 ⊗ c) = ρN x mod J'`. -/
theorem kappaF_one_tmul (c : (cov₀.transport (h := h₁)).C) (x : NFall L M)
    (hx : kappaF L M hθ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c) = Ideal.Quotient.mk _ x) :
    kappaF L' M' hθ ((1 : FormalPatchLevel.Hat (f' (R' := R') f)) ⊗ₜ[R']
        (@id (cov₀.transport (h := h₂ f h₁ he)).C c)) =
      Ideal.Quotient.mk _ (ρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt x) := by
  have e2 : TensorQuotBase.equiv (C := (cov₀.transport (h := h₂ f h₁ he)).C)
      (surjective_ψ θ (f' (R' := R') f)) (ker_ψ θ (f' (R' := R') f))
      ((1 : FormalPatchLevel.Hat (f' (R' := R') f)) ⊗ₜ[R']
        (@id (cov₀.transport (h := h₂ f h₁ he)).C c)) =
      (1 : Admissible.Hat (fbar θ (f' (R' := R') f))) ⊗ₜ[R' ⧸ J θ (R := R')]
        (@id (cov₀.transport (h := h₂ f h₁ he)).C c) := by
    rw [TensorQuotBase.equiv_tmul, map_one]
  have e3 := Admissible.transport_kummer_one_tmul (h := h₂ f h₁ he) cov₀ c
  have e4 : cov₀.kummer ((1 : Admissible.Hat f₀) ⊗ₜ[R₀] c) =
      (Admissible.piecesEquiv (h := h₁) cov₀).symm (kappa3F L M hθ (Ideal.Quotient.mk _ x)) := by
    rw [RingEquiv.eq_symm_apply, ← Admissible.transport_kummer_one_tmul (h := h₁) cov₀ c, ← hx,
      kappa3F_kappaF, TensorQuotBase.equiv_tmul, map_one]
    rfl
  rw [kappaF_apply, RingEquiv.symm_apply_eq]
  exact (congrArg (cov₀.transport (h := h₂ f h₁ he)).kummer e2).trans (e3.trans
    ((congrArg (Admissible.piecesEquiv (h := h₂ f h₁ he) cov₀) e4).trans
      (kappa3F_ρN f h₁ he hθ cov₀ L M L' M' hχχ hεε hδδ htt x).symm))

section Hmod

variable {P : Type u} [CommRing P] [Algebra R P] {P' : Type u} [CommRing P'] [Algebra R' P']
  (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R (cov₀.transport (h
      := h₁)).C f))
  (σP' : (P' ⧸ (J θ).map (algebraMap R' P')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov₀.transport (h := h₂ f h₁ he)).C (f' (R' := R') f)))
  (ρP : P →+* P') (hρP : ∀ r, ρP (algebraMap R P r) = algebraMap R' P' (algebraMap R R' r))
  (hσ : ∀ (p : P) (c : (cov₀.transport (h := h₁)).C), σP (Ideal.Quotient.mk _ p) = algebraMap
      (cov₀.transport (h := h₁)).C _ c →
    σP' (Ideal.Quotient.mk _ (ρP p)) = algebraMap (cov₀.transport (h := h₂ f h₁ he)).C _ c)

omit [IsNoetherianRing R] [IsNoetherianRing R'] in
lemma hρN (r : R) :
    ρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt (algebraMap R _ r) =
      algebraMap R' (NFall L' M') (algebraMap R R' r) :=
  KummerReduce.ρF_algebraMap ..

omit [IsNoetherianRing R] [IsNoetherianRing R'] in
include hρP in
/-- Cancelling a power of `f`: compatibility on `p f^k` implies compatibility on `p`. -/
lemma hmod_aux {X X' : Type u} [CommRing X] [CommRing X'] [Algebra R X] [Algebra R' X']
    (α₀ : P →ₐ[R] X) (α₀' : P' →ₐ[R'] X') (ρQb : X →+* X')
    (hρQb : ∀ r, ρQb (algebraMap R X r) = algebraMap R' X' (algebraMap R R' r))
    (hu : IsUnit (algebraMap R' X' (algebraMap R R' f))) (p : P) (k : ℕ)
    (key : α₀' (ρP (p * algebraMap R P (f ^ k))) = ρQb (α₀ (p * algebraMap R P (f ^ k)))) :
    α₀' (ρP p) = ρQb (α₀ p) := by
  simp only [map_mul, hρP, AlgHom.commutes, hρQb, map_pow] at key
  exact (hu.pow k).mul_right_cancel key

set_option maxHeartbeats 3000000 in
-- the patching data of the transported covering: see `kappaF_one_tmul`
include hρP hσ in
/-- **`hmod`: the patching data `α₀` of consecutive levels agree modulo `J'`** (through the
reductions `ρP`, `ρN`): the input of `FormalPatchCompat.hcompat`. -/
theorem hmod [IsScalarTower O R R'] (p : P) :
    FormalPatchLevel.alphaOfEquiv (f' (R' := R') f) (J θ)
        (FormalPatchLevel.specialFibreEquiv (f' (R' := R') f) (J θ) σP' (kappaF L' M' hθ))
        (ρP p) =
      FormalPatchCompat.ρQbar (J θ) (J_map (θ := θ) (R := R) (R' := R')).le
        (ρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt) (hρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt)
        (FormalPatchLevel.alphaOfEquiv f (J θ)
          (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappaF L M hθ)) p) := by
  obtain ⟨⟨c₀, ⟨_, k, rfl⟩⟩, hc₀⟩ :=
    IsLocalization.surj (Submonoid.powers (algebraMap R (cov₀.transport (h := h₁)).C f)) (σP
        (Ideal.Quotient.mk _ p))
  have hp₁ : σP (Ideal.Quotient.mk _ (p * algebraMap R P (f ^ k))) = algebraMap (cov₀.transport (h
      := h₁)).C _ c₀ := by
    rw [map_mul, Ideal.Quotient.mk_algebraMap, map_mul, AlgEquiv.commutes,
      IsScalarTower.algebraMap_apply R (cov₀.transport (h := h₁)).C (Localization.Away (algebraMap
          R (cov₀.transport (h := h₁)).C f)), map_pow]
    exact hc₀
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    (kappaF L M hθ ((1 : FormalPatchLevel.Hat f) ⊗ₜ c₀))
  have h1 := FormalPatchLevel.alphaOfEquiv_spec f (J θ) σP (kappaF L M hθ)
    (p * algebraMap R P (f ^ k)) c₀ x hp₁ hx.symm
  have h2 := FormalPatchLevel.alphaOfEquiv_spec (f' (R' := R') f) (J θ) σP' (kappaF L' M' hθ)
    (ρP (p * algebraMap R P (f ^ k))) c₀ (ρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt x)
    (hσ _ c₀ hp₁) (kappaF_one_tmul f h₁ he hθ cov₀ L M L' M' hχχ hεε hδδ htt c₀ x hx.symm)
  refine hmod_aux f ρP hρP _ _ _ (fun r ↦ ?_) ?_ p k ?_
  · rw [← Ideal.Quotient.mk_algebraMap, FormalPatchCompat.ρQbar_mk,
      FormalPatchCompat.ρQ_algebraMap_R]
    rfl
  · have h0 := IsLocalization.Away.algebraMap_isUnit
      (S := FormalPatchLevel.Nf (f' (R' := R') f) (NFall L' M'))
      (algebraMap R' (NFall L' M') (f' (R' := R') f))
    exact h0.map (Ideal.Quotient.mk
      (FormalPatchLevel.JNf (f' (R' := R') f) (J θ) (NFall L' M')))
  · rw [h2, h1, FormalPatchCompat.ρQbar_mk, FormalPatchCompat.ρQ_algebraMap]

end Hmod

end Model

/-! ### The step `R_n ⊗ G_{n+1} ≅ G_n` -/

section Step

variable [IsNoetherianRing R] [IsNoetherianRing R'] [IsScalarTower O R R']
  (hq : Function.Surjective (algebraMap R R'))
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (cov₀ : Admissible.Covering φ₀ ψ₀)
  {πL : cov₀.ι → O} (L : KummerLift (cov₀.transport (h := h₁)) πL) (M : CuspLift (cov₀.transport (h
      := h₁)))
  (L' : KummerLift (cov₀.transport (h := h₂ f h₁ he)) πL) (M' : CuspLift (cov₀.transport (h := h₂ f
      h₁ he)))
  (hχχ : ∀ j a, KummerReduce.ψI f (L.χ j a) = L'.χ j a)
  (hεε : ∀ j, KummerReduce.ψI f (L.ε j) = L'.ε j)
  (hδδ : ∀ i, KummerReduce.ψI f (M.δ i) = M'.δ i) (htt : KummerReduce.ψI f M.t = M'.t)
  {n n' : ℕ} (hJ : J θ (R := R) ^ n = ⊥) (hJ' : J θ (R := R') ^ n' = ⊥)
  (hflat : ∀ j, (L.χ j).toRingHom.Flat) (hidem : ∀ j, IsIdempotentElem (L.ε j))
  (hf : ∀ j, L.χ j (fA (πL j)) = algebraMap R (FormalPatchLevel.Hat f) f)
  (hcidem : ∀ i, IsIdempotentElem (M.δ i))
  (hreg : ∀ y : FormalPatchLevel.Hat f, algebraMap R _ f * y = 0 → y = 0)
  (hflat' : ∀ j, (L'.χ j).toRingHom.Flat) (hidem' : ∀ j, IsIdempotentElem (L'.ε j))
  (hf' : ∀ j, L'.χ j (fA (πL j)) =
    algebraMap R' (FormalPatchLevel.Hat (f' (R' := R') f)) (f' (R' := R') f))
  (hcidem' : ∀ i, IsIdempotentElem (M'.δ i))
  (hreg' : ∀ y : FormalPatchLevel.Hat (f' (R' := R') f),
    algebraMap R' _ (f' (R' := R') f) * y = 0 → y = 0)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {P' : Type u} [CommRing P'] [Algebra R' P'] [Algebra.FormallyEtale R' P'] [Algebra R P']
  [IsScalarTower R R' P']
  (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R] Localization.Away (algebraMap R (cov₀.transport (h
      := h₁)).C f))
  (σP' : (P' ⧸ (J θ).map (algebraMap R' P')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov₀.transport (h := h₂ f h₁ he)).C (f' (R' := R') f)))
  (hfP : IsUnit (algebraMap R P f)) (hfP' : IsUnit (algebraMap R' P' (f' (R' := R') f)))

set_option maxHeartbeats 3000000 in
-- the patching data of the transported covering: see `kappaF_one_tmul`
/-- **The level-`(n+1)` patch reduces to the level-`n` patch**: `R' ⊗_R G_{n+1} ≅ G_n` for the
patched algebras (`FormalPatchLevel.patch`) of an admissible covering at consecutive levels, with
lift data related by reduction. -/
def stepEquiv :
    (R' ⊗[R] FormalPatchLevel.patch f (J θ) hJ (FormalPatchLevel.alphaOfEquiv f (J θ)
      (FormalPatchLevel.specialFibreEquiv f (J θ) σP (kappaF L M hθ)))) ≃ₐ[R']
    FormalPatchLevel.patch (f' (R' := R') f) (J θ) hJ'
      (FormalPatchLevel.alphaOfEquiv (f' (R' := R') f) (J θ)
        (FormalPatchLevel.specialFibreEquiv (f' (R' := R') f) (J θ) σP' (kappaF L' M' hθ))) :=
  haveI := flat_NFall L M hO hflat hidem hf hcidem
  haveI := flat_NFall L' M' hO hflat' hidem' hf' hcidem'
  have hρP : ∀ r, (ρP f h₁ he cov₀ σP σP' hJ').toRingHom (algebraMap R P r) =
      algebraMap R' P' (algebraMap R R' r) := fun r ↦ by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R R' P']
  FormalGlueingQuot.equiv (ρP := (ρP f h₁ he cov₀ σP σP' hJ').toRingHom)
    (ρN := ρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt) hρP
    (KummerReduce.ρF_smul L.χ L.ε M.δ M.t cov₀.ce L'.χ L'.ε M'.δ M'.t hχχ hεε hδδ htt) hq
    (fun p x h ↦ FormalPatchCompat.hcompat (J θ) (J_map (θ := θ) (R := R) (R' := R')).le
      (ρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt) (hρN f h₁ he cov₀ L M L' M' hχχ hεε hδδ htt) hJ
          hJ'
      (ρP f h₁ he cov₀ σP σP' hJ').toRingHom hρP _ _
      (hmod f h₁ he hθ cov₀ L M L' M' hχχ hεε hδδ htt σP σP' (ρP f h₁ he cov₀ σP σP' hJ').toRingHom
          hρP
        (hσ f h₁ he cov₀ σP σP' hJ')) p x h)
    hfP (ker_ρP f h₁ he hq cov₀ σP σP' hJ') (noTorsion_NFall L M hflat hidem hf hcidem hreg)
    (FormalPatchLevel.isBaseChange_lift f (J θ) hJ _
      (FormalPatchLevel.surjective_betaMod_alphaOfEquiv _)
      (FormalPatchLevel.mem_of_betaMod_alphaOfEquiv_eq_zero _))
    hfP' (noTorsion_NFall L' M' hflat' hidem' hf' hcidem' hreg')
    (FormalPatchLevel.isBaseChange_lift (f' (R' := R') f) (J θ) hJ' _
      (FormalPatchLevel.surjective_betaMod_alphaOfEquiv _)
      (FormalPatchLevel.mem_of_betaMod_alphaOfEquiv_eq_zero _))
    (surjective_ρP f h₁ he hq cov₀ σP σP' hJ')
    (KummerReduce.surjective_ρF L.χ L.ε M.δ M.t cov₀.ce L'.χ L'.ε M'.δ M'.t hχχ hεε hδδ htt hq)
    (KummerReduce.ker_ρF L.χ L.ε M.δ M.t cov₀.ce L'.χ L'.ε M'.δ M'.t hχχ hεε hδδ htt hq)

end Step

end

end LevelStep

end SemistableReduction
