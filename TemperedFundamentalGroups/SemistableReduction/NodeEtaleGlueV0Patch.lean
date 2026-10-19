/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Piece
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Finite
import TemperedFundamentalGroups.SemistableReduction.LevelTowerFst

/-!
# A formal patch as the piece of a covering over `D(c₀) ⊆ V₀` (Blueprint §12.8, M2.3 (f))

Coverings of the special fibre that are tamely ramified over marked points (cusps, [Mzk1] §3.9
(1′A); `Admissible.Covering` with cusp factors `X^e = t`) cannot be described by étale lifts
near the marked points. If the marked points of `V₀` lie in a basic open `D(c₀)` but not in
`D(x₀)`, the piece of the covering over `D(c₀)` is instead a **tower of patched algebras**
(`LevelTower.Data`, with Kummer and cusp factors, `AdmissibleLift.patch_specF`) on the charts
`R n = B' n[1/c₀]`, whose formal coordinate `f n` divides a power of `x₀` (so that `D(x₀)`
misses the marked points). This file bundles this datum as **`NodeEtaleGlue.PatchInput`** and
shows that it is a `Piece0`:

* `PatchInput.Mp n = P n[1/x₀]` (`P n` the étale part of the patch over `D(f n)`),
  `PatchInput.e n : G n[1/x₀] ≃ P n[1/x₀]` (since `f n ∣ x₀ᵏ`);
* `PatchInput.ℓ0' n : C0 → Mp n/J` (`C0 → cov₀.C → cov₀.C[1/f] ≃ P/J → Mp/J`), a localization
  away from `c̄₀ x̄₀` (`isLocalization_ℓ0'`);
* successor maps: the transition maps `tr` of the tower and their localizations `sM`, `sMp`
  (`e_sM`: compatible via `LevelTower.Data.tr_fst_eq`), `ℓ0'_succ` (via `σP_ρP`);
* **`PatchInput.piece : Piece0`**.
-/

universe u

namespace SemistableReduction

open AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  {B0' : Type u} [CommRing B0'] (B' : ℕ → Type u) [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] (qB' : ∀ n, B' n →+* Bs') (C0 : Type u) [CommRing C0]
  [Algebra Bs' C0] (x0 c0 : B0') (x0s c0s : Bs') (ϖ : O)
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  (cov₀ : Admissible.Covering φ₀ ψ₀) (πL : cov₀.ι → O)

/-- **A tower of patched algebras over `D(c₀) ⊆ V₀`**: charts `R n = B' n[1/c₀]` carrying a
tower `T` of patched algebras of an admissible covering `cov₀` (with Kummer and cusp factors) of
the special fibre `R₀`, which is the restriction `C0[1/c̄₀]` of the special-fibre covering `C0`
over `V₀` (`ι₀`), such that `D(x₀)` misses `V(f)` (`hdiv`). -/
structure PatchInput where
  R : ℕ → Type u
  [commRingR : ∀ n, CommRing (R n)]
  [algOR : ∀ n, Algebra O (R n)]
  [noethR : ∀ n, IsNoetherianRing (R n)]
  [algkR : ∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  [algSuccR : ∀ n, Algebra (R (n + 1)) (R n)]
  [towerOR : ∀ n, IsScalarTower O (R (n + 1)) (R n)]
  T : Data (θ := θ) R cov₀ πL
  [algBR : ∀ n, Algebra (B' n) (R n)]
  [towerOBR : ∀ n, IsScalarTower O (B' n) (R n)]
  [away : ∀ n, IsLocalization.Away (algebraMap B0' (B' n) c0) (R n)]
  φs : Bs' →+* R₀
  hφs : ∀ n (x : B' n), T.e n (φs (qB' n x)) = Ideal.Quotient.mk _ (algebraMap (B' n) (R n) x)
  ι₀ : C0 →+* cov₀.C
  hι₀ : ∀ x : Bs', ι₀ (algebraMap Bs' C0 x) = algebraMap R₀ cov₀.C (φs x)
  hc0 : ∀ n, qB' n (algebraMap B0' (B' n) c0) = c0s
  hx0 : ∀ n, qB' n (algebraMap B0' (B' n) x0) = x0s
  hι : letI := ι₀.toAlgebra; IsLocalization.Away (algebraMap Bs' C0 c0s) cov₀.C
  kdiv : ℕ → ℕ
  hdiv : ∀ n, T.f n ∣ algebraMap (B' n) (R n) (algebraMap B0' (B' n) x0) ^ kdiv n
  hBR : ∀ n (x : B' (n + 1)), algebraMap (R (n + 1)) (R n) (algebraMap (B' (n + 1)) (R (n + 1)) x) =
    algebraMap (B' n) (R n) (algebraMap (B' (n + 1)) (B' n) x)
  hkR : ∀ n, RingHom.ker (algebraMap (R (n + 1)) (R n)) =
    (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (R (n + 1)))

omit [Field k] in
/-- The ideal `I·X` of an `R`-algebra is mapped to `I·Y` by an `R`-algebra isomorphism. -/
lemma map_JB_algEquiv {R X Y : Type u} [CommRing R] [CommRing X] [CommRing Y] [Algebra R X]
    [Algebra R Y] (I : Ideal R) (e : X ≃ₐ[R] Y) :
    (EtaleNil.JB I X).map (e.toRingEquiv : X →+* Y) = EtaleNil.JB I Y := by
  rw [EtaleNil.JB, EtaleNil.JB, Ideal.map_map]
  congr 1
  ext r
  exact e.commutes r

omit [Field k] in
/-- Choosing a representative of a class in a quotient (as a lemma: `obtain` with
`Ideal.Quotient.mk_surjective` directly on the special fibres of the pieces is slow). -/
lemma quot_rep {A : Type u} [CommRing A] {I : Ideal A} (x : A ⧸ I) {p : Prop}
    (h : ∀ a, Ideal.Quotient.mk I a = x → p) : p := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
  exact h a ha

namespace PatchInput

attribute [instance] commRingR algOR noethR algkR algSuccR towerOR algBR towerOBR away

variable {θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL}
  (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-! ### Level `n` -/

/-- **The patched algebra at level `n`**, with its instances fixed once (instance synthesis on
the patched algebras `LevelTower.Data.G` and their localizations is expensive). -/
def G : Type u := D.T.G hθ n

instance : CommRing (D.G hθ n) := inferInstanceAs (CommRing (D.T.G hθ n))

instance : Algebra (D.R n) (D.G hθ n) := inferInstanceAs (Algebra (D.R n) (D.T.G hθ n))

/-- The étale part of the patch (over `D(f n)`). -/
abbrev P : Type u := (D.T.level n).P

/-- `x₀` on the chart `R n`. -/
abbrev xR : D.R n := algebraMap (B' n) (D.R n) (algebraMap B0' (B' n) x0)

instance algBG' : Algebra (B' n) (D.G hθ n) :=
  ((algebraMap (D.R n) (D.G hθ n)).comp (algebraMap (B' n) (D.R n))).toAlgebra

instance towerBRG : IsScalarTower (B' n) (D.R n) (D.G hθ n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance algOG : Algebra O (D.G hθ n) :=
  ((algebraMap (D.R n) (D.G hθ n)).comp (algebraMap O (D.R n))).toAlgebra

instance towerORG : IsScalarTower O (D.R n) (D.G hθ n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance towerOG : IsScalarTower O (B' n) (D.G hθ n) :=
  IsScalarTower.of_algebraMap_eq fun o ↦ by
    rw [IsScalarTower.algebraMap_apply O (D.R n) (D.G hθ n),
      IsScalarTower.algebraMap_apply O (B' n) (D.R n),
      ← IsScalarTower.algebraMap_apply (B' n) (D.R n) (D.G hθ n)]

/-- `G n` restricted to `D(x₀)`. -/
abbrev Loc : Type u := Loc0 (B' n) (D.G hθ n) x0

/-- The projection `G n → P n` (`G n` on `D(f n)`). -/
def fst : D.G hθ n →ₐ[D.R n] D.P n := fstP D.T hθ n

include hO in
lemma isLocalization_fst : letI := (D.fst hθ n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (D.R n) (D.G hθ n) (D.T.f n)) (D.P n) :=
  isLocalization_fstP D.T hθ hO n

/-- The étale part restricted to `D(x₀)`: `Mp n = P n[1/x₀]`. -/
abbrev Mp : Type u := Localization.Away (algebraMap (D.R n) (D.P n) (D.xR n))

/-- `G n → P n → Mp n`. -/
def φ : D.G hθ n →+* D.Mp n :=
  (algebraMap (D.P n) (D.Mp n)).comp (D.fst hθ n : D.G hθ n →+* D.P n)

include hO in
/-- **`Mp n = G n[1/x₀]`** (`G n → P n` is a localization away from `f n` and `f n ∣ x₀ᵏ`). -/
theorem isLocalization_φ : letI := (D.φ hθ n).toAlgebra
    IsLocalization.Away (algebraMap (D.R n) (D.G hθ n) (D.xR n)) (D.Mp n) := by
  have h1 := D.isLocalization_fst hθ hO n
  have h2 : letI := (algebraMap (D.P n) (D.Mp n)).toAlgebra
      IsLocalization.Away ((D.fst hθ n : D.G hθ n →+* D.P n)
        (algebraMap (D.R n) (D.G hθ n) (D.xR n))) (D.Mp n) := by
    rw [RingHom.coe_coe, AlgHom.commutes]
    exact RingHomAway.of_algebra _
  have h3 := RingHomAway.comp _ _ _ _ h1 h2
  refine RingHomAway.of_dvd _ _ _ (D.kdiv n) ?_ h3
  rw [← map_pow]
  exact map_dvd _ (D.hdiv n)

/-- `Mp n` as a `G n`-algebra (through `φ`). -/
@[reducible] def algGM : Algebra (D.G hθ n) (D.Mp n) := (D.φ hθ n).toAlgebra

lemma φ_algebraMap (r : D.R n) :
    D.φ hθ n (algebraMap (D.R n) (D.G hθ n) r) = algebraMap (D.R n) (D.Mp n) r := by
  change algebraMap (D.P n) (D.Mp n) ((D.fst hθ n) (algebraMap (D.R n) (D.G hθ n) r)) = _
  rw [AlgHom.commutes]
  exact (IsScalarTower.algebraMap_apply (D.R n) (D.P n) (D.Mp n) r).symm

lemma towerRGM : letI := D.algGM hθ n; IsScalarTower (D.R n) (D.G hθ n) (D.Mp n) := by
  letI := D.algGM hθ n
  exact IsScalarTower.of_algebraMap_eq fun r ↦ (D.φ_algebraMap hθ n r).symm

lemma isLocalization_Loc :
    IsLocalization.Away (algebraMap (D.R n) (D.G hθ n) (D.xR n)) (D.Loc hθ n) :=
  Localization.isLocalization

/-- **`G n[1/x₀] ≃ P n[1/x₀]`** over `G n`. -/
def e : letI := D.algGM hθ n; D.Loc hθ n ≃ₐ[D.G hθ n] D.Mp n :=
  letI := D.algGM hθ n
  haveI := D.isLocalization_φ hθ hO n
  haveI := D.isLocalization_Loc hθ n
  IsLocalization.algEquiv (Submonoid.powers (algebraMap (D.R n) (D.G hθ n) (D.xR n)))
    (D.Loc hθ n) (D.Mp n)

lemma e_algebraMap (g : D.G hθ n) :
    D.e hθ hO n (algebraMap (D.G hθ n) (D.Loc hθ n) g) = D.φ hθ n g :=
  letI := D.algGM hθ n
  (D.e hθ hO n).commutes g

lemma e_algebraMapR (r : D.R n) :
    D.e hθ hO n (algebraMap (D.R n) (D.Loc hθ n) r) = algebraMap (D.R n) (D.Mp n) r := by
  rw [IsScalarTower.algebraMap_apply (D.R n) (D.G hθ n) (D.Loc hθ n), e_algebraMap,
    φ_algebraMap]

/-- `e` over `R n`. -/
def eR : D.Loc hθ n ≃ₐ[D.R n] D.Mp n :=
  letI := D.algGM hθ n
  AlgEquiv.ofRingEquiv (f := (D.e hθ hO n).toRingEquiv) fun r ↦ D.e_algebraMapR hθ hO n r

/-! ### Formal étaleness on the overlap -/

instance formallyEtale_Mp : Algebra.FormallyEtale (D.R n) (D.Mp n) := by
  haveI : Algebra.FormallyEtale (D.P n) (D.Mp n) :=
    Algebra.FormallyEtale.of_isLocalization
      (Submonoid.powers (algebraMap (D.R n) (D.P n) (D.xR n)))
  exact Algebra.FormallyEtale.comp (D.R n) (D.P n) (D.Mp n)

lemma towerBRL : IsScalarTower (B' n) (D.R n) (D.Loc hθ n) := by
  refine IsScalarTower.of_algebraMap_eq fun b ↦ ?_
  rw [IsScalarTower.algebraMap_apply (B' n) (D.G hθ n) (D.Loc hθ n),
    IsScalarTower.algebraMap_apply (D.R n) (D.G hθ n) (D.Loc hθ n)]
  rfl

include hO in
/-- **The piece is formally étale over `B' n` on `D(x₀)`.** -/
theorem formallyEtale_Loc : Algebra.FormallyEtale (B' n) (D.Loc hθ n) := by
  haveI := D.towerBRL hθ n
  haveI : Algebra.FormallyEtale (D.R n) (D.Loc hθ n) :=
    Algebra.FormallyEtale.of_equiv (D.eR hθ hO n).symm
  haveI : Algebra.FormallyEtale (B' n) (D.R n) :=
    Algebra.FormallyEtale.of_isLocalization (Submonoid.powers (algebraMap B0' (B' n) c0))
  exact Algebra.FormallyEtale.comp (B' n) (D.R n) (D.Loc hθ n)

/-! ### The special fibre on the overlap -/

/-- The ideal `J` of an `R n`-algebra. -/
abbrev JR (X : Type u) [CommRing X] [Algebra (D.R n) X] : Ideal X :=
  EtaleNil.JB (J θ (R := D.R n)) X

/-- `cov₀.C[1/f]` at level `n`. -/
abbrev Lf : Type u := Localization.Away (algebraMap (D.R n) (Cc D.T n) (D.T.f n))

/-- `C0 → cov₀.C → cov₀.C[1/f] ≃ P/J → Mp/J`. -/
def ℓ0' : C0 →+* D.Mp n ⧸ D.JR n (D.Mp n) :=
  ((EtaleNil.red (J θ (R := D.R n))
      (IsScalarTower.toAlgHom (D.R n) (D.P n) (D.Mp n))).toRingHom.comp
    ((D.T.level n).σP.symm.toRingEquiv.toRingHom.comp (algebraMap (Cc D.T n) (D.Lf n)))).comp
    D.ι₀

lemma ι₀_alg (y : B' n) : D.ι₀ (algebraMap Bs' C0 (qB' n y)) =
    (algebraMap (D.R n) (Cc D.T n) (algebraMap (B' n) (D.R n) y) : cov₀.C) :=
  ι₀_algebraMap D.T B' qB' D.φs D.hφs D.ι₀ D.hι₀ n y

lemma σ_alg (r : D.R n) : (D.T.level n).σP.symm (algebraMap (Cc D.T n) (D.Lf n)
    (algebraMap (D.R n) (Cc D.T n) r)) = Ideal.Quotient.mk _ (algebraMap (D.R n) (D.P n) r) := by
  rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  rfl

lemma ℓ0'_algebraMap (y : B' n) : D.ℓ0' n (algebraMap Bs' C0 (qB' n y)) =
    Ideal.Quotient.mk _ (algebraMap (D.R n) (D.Mp n) (algebraMap (B' n) (D.R n) y)) := by
  change EtaleNil.red (J θ (R := D.R n)) (IsScalarTower.toAlgHom (D.R n) (D.P n) (D.Mp n))
    ((D.T.level n).σP.symm (algebraMap (Cc D.T n) (D.Lf n)
      (D.ι₀ (algebraMap Bs' C0 (qB' n y))))) = _
  rw [ι₀_alg, σ_alg, EtaleNil.red_mk, IsScalarTower.coe_toAlgHom']
  exact congrArg (Ideal.Quotient.mk _)
    (IsScalarTower.algebraMap_apply (D.R n) (D.P n) (D.Mp n) _).symm

/-- **`Mp n/J = C0[1/(c̄₀ x̄₀)]`.** -/
theorem isLocalization_ℓ0' : letI := (D.ℓ0' n).toAlgebra
    IsLocalization.Away (algebraMap Bs' C0 c0s * algebraMap Bs' C0 x0s)
      (D.Mp n ⧸ D.JR n (D.Mp n)) := by
  set σ : Cc D.T n →+* D.P n ⧸ D.JR n (D.P n) :=
    (D.T.level n).σP.symm.toRingEquiv.toRingHom.comp (algebraMap (Cc D.T n) (D.Lf n))
  set red := (EtaleNil.red (J θ (R := D.R n))
    (IsScalarTower.toAlgHom (D.R n) (D.P n) (D.Mp n))).toRingHom
  have hσ : letI := σ.toAlgebra
      IsLocalization.Away (algebraMap (D.R n) (Cc D.T n) (D.T.f n)) (D.P n ⧸ D.JR n (D.P n)) :=
    RingHomAway.equiv (algebraMap (Cc D.T n) (D.Lf n)) (D.T.level n).σP.symm.toRingEquiv _
      (RingHomAway.of_algebra _)
  have hxσ : σ (algebraMap (D.R n) (Cc D.T n) (D.xR n)) =
      Ideal.Quotient.mk _ (algebraMap (D.R n) (D.P n) (D.xR n)) := by
    exact D.σ_alg n (D.xR n)
  have hred : letI := red.toAlgebra
      IsLocalization.Away (σ (algebraMap (D.R n) (Cc D.T n) (D.xR n)))
        (D.Mp n ⧸ D.JR n (D.Mp n)) := by
    rw [hxσ]
    exact EtaleNil.isLocalization_red _ _
  have h1 := RingHomAway.comp σ red _ _ hσ hred
  have h2 := RingHomAway.of_dvd _ _ _ (D.kdiv n)
    (by rw [← map_pow]; exact map_dvd _ (D.hdiv n)) h1
  have hx := D.ι₀_alg n (algebraMap B0' (B' n) x0)
  rw [D.hx0 n] at hx
  rw [← hx] at h2
  exact RingHomAway.comp D.ι₀ (red.comp σ) _ _ D.hι h2

/-! ### The special fibre of `G n[1/x₀]` -/

lemma JB_Loc : EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n) =
    EtaleNil.JB (J θ (R := D.R n)) (D.Loc hθ n) := by
  haveI := D.towerBRL hθ n
  rw [EtaleNil.JB, EtaleNil.JB, J, J, Ideal.map_map, Ideal.map_map]
  congr 1
  ext o
  change algebraMap (B' n) (D.Loc hθ n) (algebraMap O (B' n) o) =
    algebraMap (D.R n) (D.Loc hθ n) (algebraMap O (D.R n) o)
  rw [IsScalarTower.algebraMap_apply (B' n) (D.R n) (D.Loc hθ n),
    ← IsScalarTower.algebraMap_apply O (B' n) (D.R n)]

lemma map_JR_eR : EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n) =
    (EtaleNil.JB (J θ (R := D.R n)) (D.Mp n)).map
      ((D.eR hθ hO n).symm.toRingEquiv : D.Mp n →+* D.Loc hθ n) := by
  rw [JB_Loc]
  exact (map_JB_algEquiv _ (D.eR hθ hO n).symm).symm

/-- `Mp n/J ≃ G n[1/x₀]/J`. -/
def qe : D.Mp n ⧸ D.JR n (D.Mp n) ≃+*
    D.Loc hθ n ⧸ EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n) :=
  Ideal.quotientEquiv _ _ (D.eR hθ hO n).symm.toRingEquiv (D.map_JR_eR hθ hO n)

/-- **The special fibre of the piece on `D(x₀)`**: `C0 → G n[1/x₀]/J`. -/
def ℓ0 : C0 →+* D.Loc hθ n ⧸ EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n) :=
  (D.qe hθ hO n : D.Mp n ⧸ D.JR n (D.Mp n) →+* _).comp (D.ℓ0' n)

lemma ℓ0_algebraMap (y : B' n) : D.ℓ0 hθ hO n (algebraMap Bs' C0 (qB' n y)) =
    Ideal.Quotient.mk _ (algebraMap (B' n) (D.Loc hθ n) y) := by
  haveI := D.towerBRL hθ n
  change D.qe hθ hO n (D.ℓ0' n (algebraMap Bs' C0 (qB' n y))) = _
  rw [ℓ0'_algebraMap, qe, Ideal.quotientEquiv_mk]
  congr 1
  change (D.eR hθ hO n).symm (algebraMap (D.R n) (D.Mp n) _) = _
  rw [AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

/-- **`G n[1/x₀]/J = C0[1/(c̄₀ x̄₀)]`.** -/
theorem isLocalization_ℓ0 : letI := (D.ℓ0 hθ hO n).toAlgebra
    IsLocalization.Away (algebraMap Bs' C0 c0s * algebraMap Bs' C0 x0s)
      (D.Loc hθ n ⧸ EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n)) :=
  RingHomAway.equiv (D.ℓ0' n) (D.qe hθ hO n) _ (D.isLocalization_ℓ0' n)

/-! ### The successor maps -/

/-- **The transition maps of the tower of patched algebras.** -/
def trG : D.G hθ (n + 1) →+* D.G hθ n := D.T.tr hθ hO n

lemma trG_algebraMap (r : D.R (n + 1)) : D.trG hθ hO n (algebraMap (D.R (n + 1)) _ r) =
    algebraMap (D.R n) (D.G hθ n) (algebraMap (D.R (n + 1)) (D.R n) r) :=
  D.T.tr_algebraMap hθ hO n r

lemma trG_algebraMapB (x : B' (n + 1)) : D.trG hθ hO n (algebraMap (B' (n + 1)) _ x) =
    algebraMap (B' n) (D.G hθ n) (algebraMap (B' (n + 1)) (B' n) x) := by
  rw [IsScalarTower.algebraMap_apply (B' (n + 1)) (D.R (n + 1)) (D.G hθ (n + 1)), trG_algebraMap,
    D.hBR n, ← IsScalarTower.algebraMap_apply]

/-- The reductions of the étale parts as ring maps. -/
def ρPr : D.P (n + 1) →+* D.P n :=
  letI := LevelTower.algP D.T.level n
  (D.T.ρP n : D.P (n + 1) →+* D.P n)

lemma ρPr_algebraMap (r : D.R (n + 1)) : D.ρPr n (algebraMap (D.R (n + 1)) (D.P (n + 1)) r) =
    algebraMap (D.R n) (D.P n) (algebraMap (D.R (n + 1)) (D.R n) r) :=
  letI := LevelTower.algP D.T.level n
  (D.T.ρP n).commutes r

lemma isUnit_c0 : IsUnit (algebraMap (B' n) (D.G hθ n) (algebraMap B0' (B' n) c0)) := by
  rw [IsScalarTower.algebraMap_apply (B' n) (D.R n) (D.G hθ n)]
  exact (IsLocalization.Away.algebraMap_isUnit _).map _

include hO in
lemma gen : ∃ s : Finset (D.G hθ n), ∀ p : D.G hθ n, ∃ k : ℕ,
    algebraMap B0' (B' n) c0 ^ k • p ∈ Submodule.span (B' n) (s : Set (D.G hθ n)) := by
  haveI : Module.Finite (D.R n) (D.G hθ n) := (D.T.spec hθ hO n).1
  refine AwaySpan.gen_of_finite (R := D.R n) fun r ↦ ?_
  obtain ⟨⟨b, ⟨_, k, rfl⟩⟩, hb⟩ :=
    IsLocalization.surj (Submonoid.powers (algebraMap B0' (B' n) c0)) r
  refine ⟨k, b, ?_⟩
  rw [← map_pow, mul_comm]
  exact hb

lemma ker_trG : RingHom.ker (D.trG hθ hO n) =
    (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (D.G hθ (n + 1))) :=
  D.T.ker_tr_of hθ hO (D.hkR n)

variable [∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]

lemma trG_x0 : D.trG hθ hO n (algebraMap (B' (n + 1)) _ (algebraMap B0' (B' (n + 1)) x0)) =
    algebraMap (B' n) (D.G hθ n) (algebraMap B0' (B' n) x0) := by
  rw [trG_algebraMapB, ← IsScalarTower.algebraMap_apply B0' (B' (n + 1)) (B' n)]

lemma isUnit_sM : IsUnit (((algebraMap (D.G hθ n) (D.Loc hθ n)).comp (D.trG hθ hO n))
    (algebraMap (B' (n + 1)) (D.G hθ (n + 1)) (algebraMap B0' (B' (n + 1)) x0))) := by
  rw [RingHom.comp_apply, trG_x0]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- **The successor maps on `D(x₀)`**: the localizations of the transition maps. -/
def sM : D.Loc hθ (n + 1) →+* D.Loc hθ n :=
  IsLocalization.Away.lift _ (D.isUnit_sM hθ hO n)

lemma sM_algebraMap (g : D.G hθ (n + 1)) :
    D.sM hθ hO n (algebraMap (D.G hθ (n + 1)) (D.Loc hθ (n + 1)) g) =
      algebraMap (D.G hθ n) (D.Loc hθ n) (D.trG hθ hO n g) :=
  IsLocalization.Away.lift_eq _ (D.isUnit_sM hθ hO n) g

lemma isUnit_sMp : IsUnit (((algebraMap (D.P n) (D.Mp n)).comp (D.ρPr n))
    (algebraMap (D.R (n + 1)) (D.P (n + 1)) (D.xR (n + 1)))) := by
  rw [RingHom.comp_apply, ρPr_algebraMap, D.hBR n,
    ← IsScalarTower.algebraMap_apply B0' (B' (n + 1)) (B' n)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The successor maps of the étale parts on `D(x₀)`. -/
def sMp : D.Mp (n + 1) →+* D.Mp n :=
  IsLocalization.Away.lift _ (D.isUnit_sMp n)

lemma sMp_algebraMap (p : D.P (n + 1)) :
    D.sMp n (algebraMap (D.P (n + 1)) (D.Mp (n + 1)) p) =
      algebraMap (D.P n) (D.Mp n) (D.ρPr n p) :=
  IsLocalization.Away.lift_eq _ (D.isUnit_sMp n) p

lemma sMp_algebraMapR (r : D.R (n + 1)) :
    D.sMp n (algebraMap (D.R (n + 1)) (D.Mp (n + 1)) r) =
      algebraMap (D.R n) (D.Mp n) (algebraMap (D.R (n + 1)) (D.R n) r) := by
  rw [IsScalarTower.algebraMap_apply (D.R (n + 1)) (D.P (n + 1)) (D.Mp (n + 1)), sMp_algebraMap,
    ρPr_algebraMap, ← IsScalarTower.algebraMap_apply]

/-- **The identifications `e` commute with the successor maps** (`LevelTower.Data.tr_fst_eq`). -/
lemma e_sM (m : D.Loc hθ (n + 1)) :
    D.eR hθ hO n (D.sM hθ hO n m) = D.sMp n (D.eR hθ hO (n + 1) m) := by
  have : (D.eR hθ hO n : D.Loc hθ n →+* D.Mp n).comp (D.sM hθ hO n) =
      (D.sMp n).comp (D.eR hθ hO (n + 1) : D.Loc hθ (n + 1) →+* D.Mp (n + 1)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers
      (algebraMap (B' (n + 1)) (D.G hθ (n + 1)) (algebraMap B0' (B' (n + 1)) x0)))
      (RingHom.ext fun g ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [sM_algebraMap]
    change D.e hθ hO n _ = D.sMp n (D.e hθ hO (n + 1) _)
    rw [e_algebraMap, e_algebraMap]
    change algebraMap (D.P n) (D.Mp n) (D.T.tr hθ hO n g).1.1 =
      D.sMp n (algebraMap (D.P (n + 1)) (D.Mp (n + 1)) g.1.1)
    rw [D.T.tr_fst_eq hθ hO n g, sMp_algebraMap]
    rfl
  exact RingHom.congr_fun this m

lemma JR_le : D.JR (n + 1) (D.Mp (n + 1)) ≤ (D.JR n (D.Mp n)).comap (D.sMp n) := by
  change EtaleNil.JB (J θ (R := D.R (n + 1))) (D.Mp (n + 1)) ≤
    (EtaleNil.JB (J θ (R := D.R n)) (D.Mp n)).comap (D.sMp n)
  rw [EtaleNil.JB, Ideal.map_le_iff_le_comap, Ideal.comap_comap, J, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, sMp_algebraMapR,
    ← IsScalarTower.algebraMap_apply O (D.R (n + 1)) (D.R n)]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ho)

/-- The reduction of `sMp`. -/
def sMpbar : D.Mp (n + 1) ⧸ D.JR (n + 1) (D.Mp (n + 1)) →+* D.Mp n ⧸ D.JR n (D.Mp n) :=
  Ideal.quotientMap _ (D.sMp n) (D.JR_le n)

/-- **The special fibres on `D(x₀)` are compatible with the successor maps** (`σP_ρP`). -/
lemma ℓ0'_succ (c : C0) : D.sMpbar n (D.ℓ0' (n + 1) c) = D.ℓ0' n c := by
  refine quot_rep ((D.T.level (n + 1)).σP.symm
    (algebraMap (Cc D.T (n + 1)) (D.Lf (n + 1)) (D.ι₀ c))) fun p hp ↦ ?_
  have h3 : (D.T.level (n + 1)).σP (Ideal.Quotient.mk _ p) =
      algebraMap (Cc D.T (n + 1)) (D.Lf (n + 1)) (D.ι₀ c) :=
    (congrArg (D.T.level (n + 1)).σP hp).trans (AlgEquiv.apply_symm_apply _ _)
  have h2 := ((D.T.σP_ρP n p).trans (congrArg _ h3)).trans
    (LevelStep.Tmap_algebraMap _ _ _ _ _ _ _ _)
  have h1 : (D.T.level n).σP.symm (algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c)) =
      Ideal.Quotient.mk _ (D.ρPr n p) :=
    ((D.T.level n).σP.symm_apply_eq).mpr h2.symm
  have e1 : D.ℓ0' (n + 1) c =
      Ideal.Quotient.mk _ (algebraMap (D.P (n + 1)) (D.Mp (n + 1)) p) :=
    (congrArg (EtaleNil.red (J θ (R := D.R (n + 1)))
      (IsScalarTower.toAlgHom (D.R (n + 1)) (D.P (n + 1)) (D.Mp (n + 1)))) hp.symm).trans
      (EtaleNil.red_mk _ _ _)
  have e2 : D.ℓ0' n c = Ideal.Quotient.mk _ (algebraMap (D.P n) (D.Mp n) (D.ρPr n p)) :=
    (congrArg (EtaleNil.red (J θ (R := D.R n))
      (IsScalarTower.toAlgHom (D.R n) (D.P n) (D.Mp n))) h1).trans (EtaleNil.red_mk _ _ _)
  calc D.sMpbar n (D.ℓ0' (n + 1) c)
      = D.sMpbar n (Ideal.Quotient.mk _ (algebraMap (D.P (n + 1)) (D.Mp (n + 1)) p)) :=
        congrArg _ e1
    _ = Ideal.Quotient.mk _ (D.sMp n (algebraMap (D.P (n + 1)) (D.Mp (n + 1)) p)) :=
        Ideal.quotientMap_mk
    _ = Ideal.Quotient.mk _ (algebraMap (D.P n) (D.Mp n) (D.ρPr n p)) :=
        congrArg _ (D.sMp_algebraMap n p)
    _ = D.ℓ0' n c := e2.symm

/-- **The special fibres of the piece are compatible with the successor maps.** -/
lemma ℓ0_succ (c : C0) (m : D.Loc hθ (n + 1))
    (hm : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' (n + 1))) (D.Loc hθ (n + 1))) m =
      D.ℓ0 hθ hO (n + 1) c) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n)) (D.sM hθ hO n m) =
      D.ℓ0 hθ hO n c := by
  have h1 : Ideal.Quotient.mk (D.JR (n + 1) (D.Mp (n + 1))) (D.eR hθ hO (n + 1) m) =
      D.ℓ0' (n + 1) c :=
    (D.qe hθ hO (n + 1)).injective ((Ideal.quotientEquiv_mk _ _ _ _ _).trans
      ((congrArg (Ideal.Quotient.mk _) ((D.eR hθ hO (n + 1)).symm_apply_apply m)).trans hm))
  calc Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n)) (D.sM hθ hO n m)
      = Ideal.Quotient.mk _ ((D.eR hθ hO n).symm (D.eR hθ hO n (D.sM hθ hO n m))) :=
        congrArg _ ((D.eR hθ hO n).symm_apply_apply _).symm
    _ = D.qe hθ hO n (Ideal.Quotient.mk _ (D.eR hθ hO n (D.sM hθ hO n m))) :=
        (Ideal.quotientEquiv_mk _ _ _ _ _).symm
    _ = D.qe hθ hO n (Ideal.Quotient.mk _ (D.sMp n (D.eR hθ hO (n + 1) m))) :=
        congrArg _ (congrArg _ (D.e_sM hθ hO n m))
    _ = D.qe hθ hO n (D.sMpbar n (Ideal.Quotient.mk _ (D.eR hθ hO (n + 1) m))) :=
        congrArg _ Ideal.quotientMap_mk.symm
    _ = D.qe hθ hO n (D.sMpbar n (D.ℓ0' (n + 1) c)) := congrArg _ (congrArg _ h1)
    _ = D.ℓ0 hθ hO n c := congrArg _ (D.ℓ0'_succ n c)

/-! ### The piece -/

/-- **The tower of patched algebras over `D(c₀)` as the piece of a covering over `V₀`.** -/
def piece : Piece0 θ B' qB' C0 x0 c0 x0s c0s ϖ where
  P := D.G hθ
  hcP := D.isUnit_c0 hθ
  hfinP := D.gen hθ hO
  etaleM := D.formallyEtale_Loc hθ hO
  ℓ0 := D.ℓ0 hθ hO
  hℓ0 := D.ℓ0_algebraMap hθ hO
  hℓ0loc := D.isLocalization_ℓ0 hθ hO
  sP := D.trG hθ hO
  hsP := D.trG_algebraMapB hθ hO
  hsPs := D.T.surjective_tr hθ hO
  hkP := D.ker_trG hθ hO
  sM := fun n ↦ D.sM hθ hO n
  hsM := fun n ↦ D.sM_algebraMap hθ hO n
  hℓ0succ := fun n ↦ D.ℓ0_succ hθ hO n

end PatchInput

end NodeEtaleGlue

end

end SemistableReduction
