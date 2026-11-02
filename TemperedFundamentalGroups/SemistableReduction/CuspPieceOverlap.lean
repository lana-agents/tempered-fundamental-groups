/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspInputHom

/-!
# Maps of cusp pieces on the overlap (MR12 I3, generic core, step 2 for cusp pieces)

For a morphism `φ0 : C0 → C0'` of cusp special data (`CuspTower.CuspSpecial`), the maps of the
cusp pieces `CuspTower.pieceMap` localized away from `x₀` (`CuspTower.mLoc`, the map `mM` of
`NodeEtaleGlue.Overlap.twoChartMap` for `P0 = cuspPiece`) reduce to `φ0` through the special
fibres `ℓ0 : C0 → G n[1/x₀]/J` of the pieces (**`CuspTower.mk_mLoc_ℓ0`**, the hypothesis `hpℓ` of
`NodeEtaleGlue.Overlap.mk_mM_γM`): `G n[1/x₀] = P n[1/x₀]`, and on the étale part `pMap` reduces
to `covMap φ0` (`LevelTower.σP_pMap`).

The work is done for two arbitrary `NodeEtaleGlue.PatchInput`s over the same chart
(`PatchInput.mLocG`, `PatchInput.MpMapG`, **`PatchInput.eR_mLocG`**,
**`PatchInput.mk_mLocG_ℓ0`**), for maps `pG : G n → G' n` over `B' n` and `pP : P n → P' n`
compatible with the projections `fst` and reducing to `φ0` through `σP`.
-/

universe u

namespace SemistableReduction

noncomputable section

namespace NodeEtaleGlue

namespace PatchInput

open AdmissibleLift LevelTower

/-! ### Maps of patch inputs on the overlap -/

section Map

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 C0' : Type u} [CommRing C0]
  [Algebra Bs' C0] [CommRing C0'] [Algebra Bs' C0'] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {R₀' : Type u} [CommRing R₀'] [Algebra k R₀'] {f₀' : R₀'}
  {φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀'} {ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀'}
  {cov₀' : Admissible.Covering φ₀' ψ₀'} {πL' : cov₀'.ι → O}
  (D : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ cov₀ πL)
  (D' : PatchInput θ B' qB' C0' x0 c0 x0s c0s ϖ cov₀' πL')
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

lemma isUnit_mLocG (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y) :
    IsUnit (((algebraMap (D'.G hθ n) (D'.Loc hθ n)).comp pG)
      (algebraMap (B' n) (D.G hθ n) (algebraMap B0' (B' n) x0))) := by
  rw [RingHom.comp_apply, hpB]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- **The map `G n[1/x₀] → G' n[1/x₀]`** induced by a map `pG : G n → G' n` over `B' n`. -/
def mLocG (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y) :
    D.Loc hθ n →+* D'.Loc hθ n :=
  IsLocalization.Away.lift (algebraMap (B' n) (D.G hθ n) (algebraMap B0' (B' n) x0))
    (g := (algebraMap (D'.G hθ n) (D'.Loc hθ n)).comp pG) (D.isUnit_mLocG D' hθ n pG hpB)

lemma mLocG_algebraMap (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (g : D.G hθ n) :
    D.mLocG D' hθ n pG hpB (algebraMap (D.G hθ n) (D.Loc hθ n) g) =
      algebraMap (D'.G hθ n) (D'.Loc hθ n) (pG g) :=
  IsLocalization.Away.lift_eq _ (D.isUnit_mLocG D' hθ n pG hpB) g

/-- A map of the étale parts compatible with `pG` maps `B' n` to `B' n`. -/
lemma pP_algebraMapB (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g)) (y : B' n) :
    pP (algebraMap (D.R n) (D.P n) (algebraMap (B' n) (D.R n) y)) =
      algebraMap (D'.R n) (D'.P n) (algebraMap (B' n) (D'.R n) y) := by
  have h1 : algebraMap (D.R n) (D.P n) (algebraMap (B' n) (D.R n) y) =
      D.fst hθ n (algebraMap (B' n) (D.G hθ n) y) := ((D.fst hθ n).commutes _).symm
  have h2 : algebraMap (D'.R n) (D'.P n) (algebraMap (B' n) (D'.R n) y) =
      D'.fst hθ n (algebraMap (B' n) (D'.G hθ n) y) := ((D'.fst hθ n).commutes _).symm
  rw [h1, h2, ← hfst, hpB]

lemma isUnit_MpMapG (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g)) :
    IsUnit (((algebraMap (D'.P n) (D'.Mp n)).comp pP) (algebraMap (D.R n) (D.P n) (D.xR n))) := by
  rw [RingHom.comp_apply, pP_algebraMapB D D' hθ n pG hpB pP hfst]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- **The map `P n[1/x₀] → P' n[1/x₀]`** of the étale parts induced by `pP`. -/
def MpMapG (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g)) :
    D.Mp n →+* D'.Mp n :=
  IsLocalization.Away.lift (algebraMap (D.R n) (D.P n) (D.xR n))
    (g := (algebraMap (D'.P n) (D'.Mp n)).comp pP) (D.isUnit_MpMapG D' hθ n pG hpB pP hfst)

lemma MpMapG_algebraMap (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g))
    (p : D.P n) :
    D.MpMapG D' hθ n pG hpB pP hfst (algebraMap (D.P n) (D.Mp n) p) =
      algebraMap (D'.P n) (D'.Mp n) (pP p) :=
  IsLocalization.Away.lift_eq _ (D.isUnit_MpMapG D' hθ n pG hpB pP hfst) p

lemma MpMapG_algebraMapO (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g)) (o : O) :
    D.MpMapG D' hθ n pG hpB pP hfst (algebraMap (D.R n) (D.Mp n) (algebraMap O (D.R n) o)) =
      algebraMap (D'.R n) (D'.Mp n) (algebraMap O (D'.R n) o) := by
  rw [IsScalarTower.algebraMap_apply (D.R n) (D.P n) (D.Mp n), MpMapG_algebraMap,
    IsScalarTower.algebraMap_apply O (B' n) (D.R n), pP_algebraMapB D D' hθ n pG hpB pP hfst,
    ← IsScalarTower.algebraMap_apply O (B' n) (D'.R n),
    ← IsScalarTower.algebraMap_apply (D'.R n) (D'.P n) (D'.Mp n)]

/-- `MpMapG` preserves the ideals `J`. -/
lemma JR_le_MpMapG (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g)) :
    D.JR n (D.Mp n) ≤ (D'.JR n (D'.Mp n)).comap (D.MpMapG D' hθ n pG hpB pP hfst) := by
  change EtaleNil.JB (J θ (R := D.R n)) (D.Mp n) ≤
    (EtaleNil.JB (J θ (R := D'.R n)) (D'.Mp n)).comap (D.MpMapG D' hθ n pG hpB pP hfst)
  rw [EtaleNil.JB, Ideal.map_le_iff_le_comap, Ideal.comap_comap, J, Ideal.map_le_iff_le_comap,
    Ideal.comap_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.comp_apply, MpMapG_algebraMapO]
  exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ho)

/-- **The identifications `e : G n[1/x₀] ≃ P n[1/x₀]` intertwine `mLocG` and `MpMapG`.** -/
lemma eR_mLocG (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g))
    (m : D.Loc hθ n) :
    D'.eR hθ hO n (D.mLocG D' hθ n pG hpB m) =
      D.MpMapG D' hθ n pG hpB pP hfst (D.eR hθ hO n m) := by
  have : (D'.eR hθ hO n : D'.Loc hθ n →+* D'.Mp n).comp (D.mLocG D' hθ n pG hpB) =
      (D.MpMapG D' hθ n pG hpB pP hfst).comp (D.eR hθ hO n : D.Loc hθ n →+* D.Mp n) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers
      (algebraMap (B' n) (D.G hθ n) (algebraMap B0' (B' n) x0))) (RingHom.ext fun g ↦ ?_)
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    rw [mLocG_algebraMap]
    change D'.e hθ hO n _ = D.MpMapG D' hθ n pG hpB pP hfst (D.e hθ hO n _)
    rw [e_algebraMap, e_algebraMap]
    change algebraMap (D'.P n) (D'.Mp n) (D'.fst hθ n (pG g)) =
      D.MpMapG D' hθ n pG hpB pP hfst (algebraMap (D.P n) (D.Mp n) (D.fst hθ n g))
    rw [MpMapG_algebraMap, hfst]
  exact RingHom.congr_fun this m

/-- **`MpMapG` reduces to `φ0` through `ℓ0'`** if `pP` reduces to `φ0` through `σP`. -/
lemma mk_MpMapG_ℓ0' (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g))
    (φ0 : C0 →+* C0')
    (hσ : ∀ (c : C0) (p : D.P n), (D.T.level n).σP (Ideal.Quotient.mk _ p) =
        algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c) →
      (D'.T.level n).σP (Ideal.Quotient.mk _ (pP p)) =
        algebraMap (Cc D'.T n) (D'.Lf n) (D'.ι₀ (φ0 c)))
    (c : C0) (w : D.Mp n) (hw : Ideal.Quotient.mk (D.JR n (D.Mp n)) w = D.ℓ0' n c) :
    Ideal.Quotient.mk (D'.JR n (D'.Mp n)) (D.MpMapG D' hθ n pG hpB pP hfst w) =
      D'.ℓ0' n (φ0 c) := by
  refine quot_rep ((D.T.level n).σP.symm
    (algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c))) fun p hp ↦ ?_
  have h3 : (D.T.level n).σP (Ideal.Quotient.mk _ p) =
      algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c) :=
    (congrArg (D.T.level n).σP hp).trans (AlgEquiv.apply_symm_apply _ _)
  have h1 : (D'.T.level n).σP.symm (algebraMap (Cc D'.T n) (D'.Lf n) (D'.ι₀ (φ0 c))) =
      Ideal.Quotient.mk _ (pP p) :=
    ((D'.T.level n).σP.symm_apply_eq).mpr (hσ c p h3).symm
  have e1 : D.ℓ0' n c = Ideal.Quotient.mk _ (algebraMap (D.P n) (D.Mp n) p) :=
    (congrArg (EtaleNil.red (J θ (R := D.R n))
      (IsScalarTower.toAlgHom (D.R n) (D.P n) (D.Mp n))) hp.symm).trans
      (EtaleNil.red_mk _ _ _)
  have e2 : D'.ℓ0' n (φ0 c) = Ideal.Quotient.mk _ (algebraMap (D'.P n) (D'.Mp n) (pP p)) :=
    (congrArg (EtaleNil.red (J θ (R := D'.R n))
      (IsScalarTower.toAlgHom (D'.R n) (D'.P n) (D'.Mp n))) h1).trans (EtaleNil.red_mk _ _ _)
  rw [e1, Ideal.Quotient.eq] at hw
  rw [e2, ← MpMapG_algebraMap D D' hθ n pG hpB pP hfst, Ideal.Quotient.eq, ← map_sub]
  exact D.JR_le_MpMapG D' hθ n pG hpB pP hfst hw

/-- **`mLocG` reduces to `φ0` through the special fibres `ℓ0` of the pieces.** -/
theorem mk_mLocG_ℓ0 (pG : D.G hθ n →+* D'.G hθ n)
    (hpB : ∀ y : B' n, pG (algebraMap (B' n) (D.G hθ n) y) = algebraMap (B' n) (D'.G hθ n) y)
    (pP : D.P n →+* D'.P n) (hfst : ∀ g, D'.fst hθ n (pG g) = pP (D.fst hθ n g))
    (φ0 : C0 →+* C0')
    (hσ : ∀ (c : C0) (p : D.P n), (D.T.level n).σP (Ideal.Quotient.mk _ p) =
        algebraMap (Cc D.T n) (D.Lf n) (D.ι₀ c) →
      (D'.T.level n).σP (Ideal.Quotient.mk _ (pP p)) =
        algebraMap (Cc D'.T n) (D'.Lf n) (D'.ι₀ (φ0 c)))
    (c : C0) (m : D.Loc hθ n)
    (hm : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (D.Loc hθ n)) m = D.ℓ0 hθ hO n c) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (D'.Loc hθ n)) (D.mLocG D' hθ n pG hpB m) =
      D'.ℓ0 hθ hO n (φ0 c) := by
  have h1 : Ideal.Quotient.mk (D.JR n (D.Mp n)) (D.eR hθ hO n m) = D.ℓ0' n c :=
    (D.qe hθ hO n).injective ((Ideal.quotientEquiv_mk _ _ _ _ _).trans
      ((congrArg (Ideal.Quotient.mk _) ((D.eR hθ hO n).symm_apply_apply m)).trans hm))
  calc Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' n)) (D'.Loc hθ n))
        (D.mLocG D' hθ n pG hpB m)
      = Ideal.Quotient.mk _ ((D'.eR hθ hO n).symm (D'.eR hθ hO n (D.mLocG D' hθ n pG hpB m))) :=
        congrArg _ ((D'.eR hθ hO n).symm_apply_apply _).symm
    _ = D'.qe hθ hO n (Ideal.Quotient.mk _ (D'.eR hθ hO n (D.mLocG D' hθ n pG hpB m))) :=
        (Ideal.quotientEquiv_mk _ _ _ _ _).symm
    _ = D'.qe hθ hO n (Ideal.Quotient.mk _
          (D.MpMapG D' hθ n pG hpB pP hfst (D.eR hθ hO n m))) :=
        congrArg _ (congrArg _ (D.eR_mLocG D' hθ hO n pG hpB pP hfst m))
    _ = D'.qe hθ hO n (D'.ℓ0' n (φ0 c)) :=
        congrArg _ (D.mk_MpMapG_ℓ0' D' hθ n pG hpB pP hfst φ0 hσ c _ h1)
    _ = D'.ℓ0 hθ hO n (φ0 c) := rfl

end Map

end PatchInput

end NodeEtaleGlue

namespace CuspTower

open TateLevel AdmissibleLift EtaleTower NodeEtaleGlue

variable {O : Type u} [CommRing O] {T0' : Type u} [CommRing T0'] [Algebra O T0'] {c0 x0 : T0'}
  {k : Type u} [Field k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  (Sc Sc' : CuspSpecial T0' c0 x0 (θ := θ)) {ϖ : O} (hϖ : θ ϖ = 0)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing T0']
  (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0)
  (n : ℕ)

/-- The map of the cusp pieces as a ring map of the `cuspInput` levels. -/
abbrev pm : (cuspInput Sc hϖ hker hx).G hθ.out n →+* (cuspInput Sc' hϖ hker hx).G hθ.out n :=
  (pieceMap Sc Sc' hϖ hker hx hnf φ0 n).toRingHom

lemma pm_algebraMapB (y : Tn ϖ T0' n) :
    pm Sc Sc' hϖ hker hx hnf φ0 n
        (algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).G hθ.out n) y) =
      algebraMap (Tn ϖ T0' n) ((cuspInput Sc' hϖ hker hx).G hθ.out n) y :=
  (pieceMap Sc Sc' hϖ hker hx hnf φ0 n).commutes _

/-- **The map of the cusp pieces on the overlap** `G n[1/x₀] → G' n[1/x₀]` (the map `mM` of
`Overlap.twoChartMap` for `P0 = cuspPiece`). -/
def mLoc : (cuspInput Sc hϖ hker hx).Loc hθ.out n →+* (cuspInput Sc' hϖ hker hx).Loc hθ.out n :=
  (cuspInput Sc hϖ hker hx).mLocG (cuspInput Sc' hϖ hker hx) hθ.out n
    (pm Sc Sc' hϖ hker hx hnf φ0 n) (pm_algebraMapB Sc Sc' hϖ hker hx hnf φ0 n)

lemma mLoc_algebraMap (g : (cuspInput Sc hϖ hker hx).G hθ.out n) :
    mLoc Sc Sc' hϖ hker hx hnf φ0 n (algebraMap _ _ g) =
      algebraMap _ ((cuspInput Sc' hϖ hker hx).Loc hθ.out n) (pm Sc Sc' hϖ hker hx hnf φ0 n g) :=
  PatchInput.mLocG_algebraMap _ _ _ _ _ _ g

/-- The étale part of `pieceMap`, as a ring map of the `cuspInput` levels. -/
abbrev pMapC : (cuspInput Sc hϖ hker hx).P n →+* (cuspInput Sc' hϖ hker hx).P n :=
  (LevelTower.pMap ((cuspTower Sc hϖ hker hx).level n) ((cuspTower Sc' hϖ hker hx).level n)
    (covMap Sc Sc' φ0)).toRingHom

lemma fst_pm (g : (cuspInput Sc hϖ hker hx).G hθ.out n) :
    (cuspInput Sc' hϖ hker hx).fst hθ.out n (pm Sc Sc' hϖ hker hx hnf φ0 n g) =
      pMapC Sc Sc' hϖ hker hx φ0 n ((cuspInput Sc hϖ hker hx).fst hθ.out n g) :=
  rfl

/-- **`pMap (covMap φ0)` reduces to `φ0` through `σP`** (`LevelTower.σP_pMap`). -/
lemma σP_pMapC (c : Sc.C0) (p : ((cuspTower Sc hϖ hker hx).level n).P)
    (hp : ((cuspTower Sc hϖ hker hx).level n).σP (Ideal.Quotient.mk _ p) =
      algebraMap (Cc (cuspTower Sc hϖ hker hx) n)
        (Localization.Away (algebraMap (Tn ϖ (Rc T0' c0) n) (Cc (cuspTower Sc hϖ hker hx) n)
          ((cuspTower Sc hϖ hker hx).f n))) (Sc.ι₀ c)) :
    ((cuspTower Sc' hϖ hker hx).level n).σP (Ideal.Quotient.mk _
        (LevelTower.pMap ((cuspTower Sc hϖ hker hx).level n)
          ((cuspTower Sc' hϖ hker hx).level n) (covMap Sc Sc' φ0) p)) =
      algebraMap (Cc (cuspTower Sc' hϖ hker hx) n)
        (Localization.Away (algebraMap (Tn ϖ (Rc T0' c0) n) (Cc (cuspTower Sc' hϖ hker hx) n)
          ((cuspTower Sc' hϖ hker hx).f n))) (Sc'.ι₀ (φ0 c)) := by
  refine (LevelTower.σP_pMap ((cuspTower Sc hϖ hker hx).level n)
    ((cuspTower Sc' hϖ hker hx).level n) (covMap Sc Sc' φ0) p).trans ?_
  refine (congrArg (FormalPatchLevel.NfMap ((cuspTower Sc hϖ hker hx).f n)
    (LevelTower.transportMapR ((cuspTower Sc hϖ hker hx).hfe n) (covMap Sc Sc' φ0))) hp).trans ?_
  exact (FormalPatchLevel.NfMap_algebraMap _ _ _).trans
    (congrArg (algebraMap _ _) (covMap_ι₀ Sc Sc' φ0 c))

/-- The map of the étale parts on the overlap `P n[1/x₀] → P' n[1/x₀]`. -/
def MpMap : (cuspInput Sc hϖ hker hx).Mp n →+* (cuspInput Sc' hϖ hker hx).Mp n :=
  (cuspInput Sc hϖ hker hx).MpMapG (cuspInput Sc' hϖ hker hx) hθ.out n
    (pm Sc Sc' hϖ hker hx hnf φ0 n) (pm_algebraMapB Sc Sc' hϖ hker hx hnf φ0 n)
    (pMapC Sc Sc' hϖ hker hx φ0 n) (fst_pm Sc Sc' hϖ hker hx hnf φ0 n)

set_option maxRecDepth 4000 in
/-- `G n[1/x₀] ≃ P n[1/x₀]` intertwines `mLoc` and `MpMap`. -/
lemma eR_mLoc (m : (cuspInput Sc hϖ hker hx).Loc hθ.out n) :
    (cuspInput Sc' hϖ hker hx).eR hθ.out hO n (mLoc Sc Sc' hϖ hker hx hnf φ0 n m) =
      MpMap Sc Sc' hϖ hker hx hnf φ0 n ((cuspInput Sc hϖ hker hx).eR hθ.out hO n m) :=
  PatchInput.eR_mLocG (cuspInput Sc hϖ hker hx) (cuspInput Sc' hϖ hker hx) hθ.out hO n
    (pm Sc Sc' hϖ hker hx hnf φ0 n) (pm_algebraMapB Sc Sc' hϖ hker hx hnf φ0 n)
    (pMapC Sc Sc' hϖ hker hx φ0 n) (fst_pm Sc Sc' hϖ hker hx hnf φ0 n) m

/-- **`MpMap` reduces to `φ0` through `ℓ0'`.** -/
lemma mk_MpMap_ℓ0' (c : Sc.C0) (w : (cuspInput Sc hϖ hker hx).Mp n)
    (hw : Ideal.Quotient.mk ((cuspInput Sc hϖ hker hx).JR n ((cuspInput Sc hϖ hker hx).Mp n)) w =
      (cuspInput Sc hϖ hker hx).ℓ0' n c) :
    Ideal.Quotient.mk ((cuspInput Sc' hϖ hker hx).JR n ((cuspInput Sc' hϖ hker hx).Mp n))
      (MpMap Sc Sc' hϖ hker hx hnf φ0 n w) = (cuspInput Sc' hϖ hker hx).ℓ0' n (φ0 c) :=
  PatchInput.mk_MpMapG_ℓ0' (cuspInput Sc hϖ hker hx) (cuspInput Sc' hϖ hker hx) hθ.out n
    (pm Sc Sc' hϖ hker hx hnf φ0 n) (pm_algebraMapB Sc Sc' hϖ hker hx hnf φ0 n)
    (pMapC Sc Sc' hϖ hker hx φ0 n) (fst_pm Sc Sc' hϖ hker hx hnf φ0 n) φ0.toRingHom
    (fun c p hp ↦ σP_pMapC Sc Sc' hϖ hker hx φ0 n c p hp) c w hw

/-- **The maps of the cusp pieces on the overlap reduce to `φ0` through `ℓ0`** (the hypothesis
`hpℓ` of `NodeEtaleGlue.Overlap.mk_mM_γM` for `P0 = cuspPiece`). -/
theorem mk_mLoc_ℓ0 (c : Sc.C0) (m : (cuspInput Sc hϖ hker hx).Loc hθ.out n)
    (hm : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := Tn ϖ T0' n))
      ((cuspInput Sc hϖ hker hx).Loc hθ.out n)) m = (cuspInput Sc hϖ hker hx).ℓ0 hθ.out hO n c) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := Tn ϖ T0' n))
      ((cuspInput Sc' hϖ hker hx).Loc hθ.out n)) (mLoc Sc Sc' hϖ hker hx hnf φ0 n m) =
      (cuspInput Sc' hϖ hker hx).ℓ0 hθ.out hO n (φ0 c) :=
  PatchInput.mk_mLocG_ℓ0 (cuspInput Sc hϖ hker hx) (cuspInput Sc' hϖ hker hx) hθ.out hO n
    (pm Sc Sc' hϖ hker hx hnf φ0 n) (pm_algebraMapB Sc Sc' hϖ hker hx hnf φ0 n)
    (pMapC Sc Sc' hϖ hker hx φ0 n) (fst_pm Sc Sc' hϖ hker hx hnf φ0 n) φ0.toRingHom
    (fun c p hp ↦ σP_pMapC Sc Sc' hϖ hker hx φ0 n c p hp) c m hm

end CuspTower

end

end SemistableReduction
