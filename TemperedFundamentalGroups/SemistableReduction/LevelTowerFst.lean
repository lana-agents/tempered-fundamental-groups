/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTowerMk

/-!
# The étale component of the transition maps (Blueprint §12.8, M2.3 (f), tower)

The transition map `tr : G (n+1) → G n` of a tower of patched algebras restricts on `D(f)` to
the reduction `ρP : P (n+1) → P n` of the étale parts (`LevelStep.ρP`), which is compatible with
the identifications `σP : P/JP ≃ C_f`:

* `LevelStep.Tmap`: the map `C_f → C_{f₂}` of the localizations of the (common) covering `C`;
* **`LevelStep.trans₂_fst`**: `σP' (fst (trans₂ x)) = Tmap (σP (fst x))` modulo `J`
  (`FormalGlueingQuot.equiv_tmul_fst`, `LevelStep.σP'_ρP`);
* **`LevelTower.Data.tr_fst`**: the same for the transition maps of a bundled tower.

This is the input for the compatibility of the overlap maps with étale pieces along the tower
(`EtaleNil.ext`).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace LevelStep

section Tmap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R) (f₂ : R') (hf : f' (R' := R') f = f₂)
  [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))} {e₂ : R₀ ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (h₁ : e₁ f₀ = fbar θ f) (h₂ : e₂ f₀ = fbar θ f₂)
  (he : ∀ r : R, e₂ (e₁.symm (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R R' r))
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  (cov₀ : Admissible.Covering φ₀ ψ₀)

/-- The identity of the covering, between its structures over consecutive levels. -/
def idC : (cov₀.transport (h := h₁)).C →+* (cov₀.transport (h := h₂)).C := RingHom.id cov₀.C

include hf he in
lemma idC_algebraMap : idC f f₂ h₁ h₂ cov₀ (algebraMap R (cov₀.transport (h := h₁)).C f) =
    algebraMap R' (cov₀.transport (h := h₂)).C f₂ := by
  subst hf
  exact (algebraMap_C f h₁ he cov₀ f).symm

/-- The map `C_f → C_{f₂}` of the localizations of the covering at consecutive levels. -/
def Tmap : Localization.Away (algebraMap R (cov₀.transport (h := h₁)).C f) →+*
    Localization.Away (algebraMap R' (cov₀.transport (h := h₂)).C f₂) :=
  IsLocalization.Away.lift (algebraMap R (cov₀.transport (h := h₁)).C f)
    (g := (algebraMap (cov₀.transport (h := h₂)).C _).comp (idC f f₂ h₁ h₂ cov₀)) (by
      rw [RingHom.comp_apply, idC_algebraMap f f₂ hf h₁ h₂ he cov₀]
      exact IsLocalization.Away.algebraMap_isUnit _)

lemma Tmap_algebraMap (c : (cov₀.transport (h := h₁)).C) :
    Tmap f f₂ hf h₁ h₂ he cov₀ (algebraMap _ _ c) =
      algebraMap (cov₀.transport (h := h₂)).C _ (idC f f₂ h₁ h₂ cov₀ c) :=
  IsLocalization.Away.lift_eq _ _ c

lemma T_eq_Tmap (y : Localization.Away (algebraMap R (cov₀.transport (h := h₁)).C f)) :
    T f h₁ he cov₀ y = Tmap f (f' (R' := R') f) rfl h₁ (LevelStep.h₂ f h₁ he) he cov₀ y := by
  have : (T f h₁ he cov₀).toRingHom =
      Tmap f (f' (R' := R') f) rfl h₁ (LevelStep.h₂ f h₁ he) he cov₀ :=
    IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R (cov₀.transport (h := h₁)).C f))
      (RingHom.ext fun c ↦ by
        simp only [RingHom.comp_apply]
        rw [Tmap_algebraMap]
        exact T_algebraMap f h₁ he cov₀ c)
  exact RingHom.congr_fun this y

variable [IsScalarTower O R R']
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {P' : Type u} [CommRing P'] [Algebra R' P'] [Algebra R P'] [IsScalarTower R R' P']
  {m : ℕ} (hJ' : J θ (R := R') ^ m = ⊥)
  (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R]
    Localization.Away (algebraMap R (cov₀.transport (h := h₁)).C f))
  (σP' : (P' ⧸ (J θ).map (algebraMap R' P')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov₀.transport (h := h₂)).C f₂))

/-- **The reduction of the étale parts** `P → P'` for a free target element `f₂ = q f`
(`LevelStep.ρP`). -/
def ρP₂ : P →ₐ[R] P' := by
  subst hf
  exact ρP f h₁ he cov₀ σP σP' hJ'

omit [IsScalarTower O R R'] in
/-- `ρP₂` is compatible with the identifications `σP` of the special fibres. -/
lemma σP_ρP₂ (p : P) :
    σP' (Ideal.Quotient.mk _ (ρP₂ f f₂ hf h₁ h₂ he cov₀ hJ' σP σP' p)) =
      Tmap f f₂ hf h₁ h₂ he cov₀ (σP (Ideal.Quotient.mk _ p)) := by
  subst hf
  rw [← T_eq_Tmap]
  exact σP'_ρP f h₁ he cov₀ σP σP' hJ' p

end Tmap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R) (f₂ : R') (hf : f' (R' := R') f = f₂)

variable [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))} {e₂ : R₀ ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (h₁ : e₁ f₀ = fbar θ f) (h₂ : e₂ f₀ = fbar θ f₂)
  (he : ∀ r : R, e₂ (e₁.symm (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R R' r))
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  [IsNoetherianRing R] [IsNoetherianRing R'] [IsScalarTower O R R']
  (hq : Function.Surjective (algebraMap R R'))
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (cov₀ : Admissible.Covering φ₀ ψ₀)
  {πL : cov₀.ι → O} (L : KummerLift (cov₀.transport (h := h₁)) πL)
  (M : CuspLift (cov₀.transport (h := h₁)))
  (L' : KummerLift (cov₀.transport (h := h₂)) πL) (M' : CuspLift (cov₀.transport (h := h₂)))
  (hχχ : ∀ j a, ψ₂ f f₂ hf (L.χ j a) = L'.χ j a)
  (hεε : ∀ j, ψ₂ f f₂ hf (L.ε j) = L'.ε j)
  (hδδ : ∀ i, ψ₂ f f₂ hf (M.δ i) = M'.δ i) (htt : ψ₂ f f₂ hf M.t = M'.t)
  {n n' : ℕ} (hJ : J θ (R := R) ^ n = ⊥) (hJ' : J θ (R := R') ^ n' = ⊥)
  {I₁ I₂ : Ideal O} (hflat : ∀ j, KummerFactorQuot.KFlat I₁ (L.χ j).toRingHom)
  (hidem : ∀ j, IsIdempotentElem (L.ε j))
  (hfχ : ∀ j, L.χ j (fA (πL j)) = algebraMap R (FormalPatchLevel.Hat f) f)
  (hcidem : ∀ i, IsIdempotentElem (M.δ i))
  (hreg : ∀ y : FormalPatchLevel.Hat f, algebraMap R _ f * y = 0 → y = 0)
  (hflat' : ∀ j, KummerFactorQuot.KFlat I₂ (L'.χ j).toRingHom)
  (hidem' : ∀ j, IsIdempotentElem (L'.ε j))
  (hfχ' : ∀ j, L'.χ j (fA (πL j)) = algebraMap R' (FormalPatchLevel.Hat f₂) f₂)
  (hcidem' : ∀ i, IsIdempotentElem (M'.δ i))
  (hreg' : ∀ y : FormalPatchLevel.Hat f₂, algebraMap R' _ f₂ * y = 0 → y = 0)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {P' : Type u} [CommRing P'] [Algebra R' P'] [Algebra.FormallyEtale R' P'] [Algebra R P']
  [IsScalarTower R R' P']
  (σP : (P ⧸ (J θ).map (algebraMap R P)) ≃ₐ[R]
    Localization.Away (algebraMap R (cov₀.transport (h := h₁)).C f))
  (σP' : (P' ⧸ (J θ).map (algebraMap R' P')) ≃ₐ[R']
    Localization.Away (algebraMap R' (cov₀.transport (h := h₂)).C f₂))
  (hfP : IsUnit (algebraMap R P f)) (hfP' : IsUnit (algebraMap R' P' f₂))


include hf he hq hO hχχ hεε hδδ htt hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg'
  hfP hfP' in
/-- **The étale component of the transition map** is `ρP₂`. -/
theorem trans₂_fst_eq (x : patchOf hθ cov₀ f h₁ L M hJ σP) :
    (trans₂ f f₂ hf h₁ h₂ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt
      hJ hJ' hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP' x).1.1 =
      ρP₂ f f₂ hf h₁ h₂ he cov₀ hJ' σP σP' x.1.1 := by
  subst hf
  exact FormalGlueingQuot.φ₁_one_tmul (NFall L M) _ (ρP := (ρP f h₁ he cov₀ σP σP' hJ').toRingHom)
    (fun r ↦ by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes,
      IsScalarTower.algebraMap_apply R R' P']) x

include hf he hq hO hχχ hεε hδδ htt hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg'
  hfP hfP' in
/-- **The étale component of the transition map**: modulo `J`, `fst ∘ trans₂` is `Tmap` under the
identifications `σP`. -/
theorem trans₂_fst (x : patchOf hθ cov₀ f h₁ L M hJ σP) :
    σP' (Ideal.Quotient.mk _ (trans₂ f f₂ hf h₁ h₂ he hq hθ hO cov₀ L M L' M' hχχ hεε hδδ htt
      hJ hJ' hflat hidem hfχ hcidem hreg hflat' hidem' hfχ' hcidem' hreg' σP σP' hfP hfP' x).1.1) =
      Tmap f f₂ hf h₁ h₂ he cov₀ (σP (Ideal.Quotient.mk _ x.1.1)) := by
  rw [trans₂_fst_eq, σP_ρP₂]

end LevelStep

namespace LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  (R : ℕ → Type u) [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  (cov₀ : Admissible.Covering φ₀ ψ₀) (πL : cov₀.ι → O)
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} (hfe : ∀ n, e n f₀ = fbar θ (f n))

variable {R cov₀ πL hfe}
variable (hθ : Function.Surjective θ)

variable [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n)))
  (hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n)
  (he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r))
  (D : ∀ n, Level R cov₀ πL hfe n)
  (hχχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.χ j a) = (D n).L.χ j a)
  (hεε : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.ε j) = (D n).L.ε j)
  (hδδ : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).M.δ i) = (D n).M.δ i)
  (htt : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D (n + 1)).M.t = (D n).M.t)

/-- **The étale component of the transition maps**: modulo `J`, `fst ∘ tr` is `Tmap` under the
identifications `σP` of consecutive levels. -/
theorem tr_fst (n : ℕ) (x : (D (n + 1)).G hθ) :
    (D n).σP (Ideal.Quotient.mk _ (tr hθ hO hq hf he D hχχ hεε hδδ htt n x).1.1) =
      LevelStep.Tmap (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) cov₀
        ((D (n + 1)).σP (Ideal.Quotient.mk _ x.1.1)) :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.trans₂_fst (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) (hq n) hθ hO cov₀
    (D (n + 1)).L (D (n + 1)).M (D n).L (D n).M (hχχ n) (hεε n) (hδδ n) (htt n)
    (D (n + 1)).hJ (D n).hJ (D (n + 1)).hflat (D (n + 1)).hidem (D (n + 1)).hfχ
    (D (n + 1)).hcidem (D (n + 1)).hreg (D n).hflat (D n).hidem (D n).hfχ (D n).hcidem
    (D n).hreg (D (n + 1)).σP (D n).σP (D (n + 1)).hfP (D n).hfP x

/-- **The reduction of the étale parts** `P (n+1) → P n` of a tower (`LevelStep.ρP₂`). -/
def ρPn (n : ℕ) : letI := algP D n; (D (n + 1)).P →ₐ[R (n + 1)] (D n).P :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.ρP₂ (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) cov₀ (D n).hJ
    (D (n + 1)).σP (D n).σP

omit [∀ n, IsNoetherianRing (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
lemma σP_ρPn (n : ℕ) (p : (D (n + 1)).P) :
    (D n).σP (Ideal.Quotient.mk _ (ρPn hf he D n p)) =
      LevelStep.Tmap (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) cov₀
        ((D (n + 1)).σP (Ideal.Quotient.mk _ p)) :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.σP_ρP₂ (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) cov₀ (D n).hJ
    (D (n + 1)).σP (D n).σP p

/-- **The étale component of the transition maps is `ρPn`.** -/
theorem tr_fst_eq (n : ℕ) (x : (D (n + 1)).G hθ) :
    (tr hθ hO hq hf he D hχχ hεε hδδ htt n x).1.1 = ρPn hf he D n x.1.1 :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.trans₂_fst_eq (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) (hq n) hθ hO cov₀
    (D (n + 1)).L (D (n + 1)).M (D n).L (D n).M (hχχ n) (hεε n) (hδδ n) (htt n)
    (D (n + 1)).hJ (D n).hJ (D (n + 1)).hflat (D (n + 1)).hidem (D (n + 1)).hfχ
    (D (n + 1)).hcidem (D (n + 1)).hreg (D n).hflat (D n).hidem (D n).hfχ (D n).hcidem
    (D n).hreg (D (n + 1)).σP (D n).σP (D (n + 1)).hfP (D n).hfP x

end LevelTower

namespace LevelTower.Data

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (T : Data (θ := θ) R cov₀ πL) (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The étale component of the transition maps of a bundled tower**: modulo `J`,
`fst ∘ tr` is `Tmap` under the identifications `σP`. -/
theorem tr_fst (n : ℕ) (x : T.G hθ (n + 1)) :
    (T.level n).σP (Ideal.Quotient.mk _ (T.tr hθ hO n x).1.1) =
      LevelStep.Tmap (T.f (n + 1)) (T.f n) (T.hf n) (T.hfe (n + 1)) (T.hfe n) (T.he n) cov₀
        ((T.level (n + 1)).σP (Ideal.Quotient.mk _ x.1.1)) :=
  LevelTower.tr_fst hθ hO T.hq T.hf T.he
    (mkLevel T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg) T.hcχ
    (hεε_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg T.hf T.he)
    (hδδ_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg T.hf T.he) T.hct n x

/-- **The reduction of the étale parts** `P (n+1) → P n` of a bundled tower. -/
def ρP (n : ℕ) : letI := algP (T.level) n; (T.level (n + 1)).P →ₐ[R (n + 1)] (T.level n).P :=
  LevelTower.ρPn T.hf T.he (mkLevel T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg) n

omit [∀ n, IsScalarTower O (R (n + 1)) (R n)] in
lemma σP_ρP (n : ℕ) (p : (T.level (n + 1)).P) :
    (T.level n).σP (Ideal.Quotient.mk _ (T.ρP n p)) =
      LevelStep.Tmap (T.f (n + 1)) (T.f n) (T.hf n) (T.hfe (n + 1)) (T.hfe n) (T.he n) cov₀
        ((T.level (n + 1)).σP (Ideal.Quotient.mk _ p)) :=
  LevelTower.σP_ρPn T.hf T.he (mkLevel T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg) n p

/-- **The étale component of the transition maps is `ρP`.** -/
theorem tr_fst_eq (n : ℕ) (x : T.G hθ (n + 1)) :
    (T.tr hθ hO n x).1.1 = T.ρP n x.1.1 :=
  LevelTower.tr_fst_eq hθ hO T.hq T.hf T.he
    (mkLevel T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg) T.hcχ
    (hεε_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg T.hf T.he)
    (hδδ_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg T.hf T.he) T.hct n x

end LevelTower.Data

end

end SemistableReduction
