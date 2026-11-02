/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHom

/-!
# Morphisms of data of tame covers of `ℙ¹_k ∖ {0, 1, ā}` and the functoriality of their lifts

A tame cover of `ℙ¹_k ∖ {0, 1, ā}` is given by a datum (`P1Three.Datum`, an instance of the
generic `DatumG`): the covering `Sp` over `V₁`, the cusp special datum `S0` over `V₀`, and the
overlap identification `ω : C0[1/x̄] ≃ C1[1/ȳ]`. A morphism of data (`Datum.Hom`, an instance of
the generic `HomG`: maps `φ1`, `φ0` compatible with `ω`) lifts through the M2 construction (MR12's
generic core, recipe "P1Three step-3", MR12-tfg-plan c47):

* `CuspTower.pieceP` (generic: the maps of the cusp pieces `CuspTower.pieceMap` with the `Piece0`
  types), `pieceP_algebraMapB/O`, `sP_pieceP`, `pieceP_id`, `pieceP_comp`; over `V₀` they are used
  with the Kummer normal form hypotheses `P1Three.cuspNFc` at the cusps;
* `Datum.hp0`, `hpO`, `hpS`, `hpB`, `hpγ` and **`Datum.hψ`** (the overlap condition over
  `V₀ ∩ V₁`, `NodeEtaleGlue.Overlap.hψ_of_bottom`);
* `Datum.hyO`, `Datum.twoChartMap` (the morphisms of the two-chart rings at every level).

The morphism of the adic systems (`TwoChartTower.systemShiftHom` of `Datum.twoChartMap`), its
functoriality (`Overlap.twoChartMap_eq_id/comp`, `TwoChartTower.systemShiftHom_eq_id/comp`) and the
morphisms of the algebraizations (`AdicChartAlgSystem.Algebraization.map`) are the next step
(MR13-plan run 14: the concrete `systemShiftHom` application does not elaborate in time yet).

The P1Three data have no nodes (`IsEmpty cov.ι` for `Sp` and `S0`), so the node balance condition
of MR12's I3 (`NodeHom.Balanced`/`BalancedK`, lead decision after MR12 c47) is vacuous here: every
`Datum.Hom` lifts. Balance enters only when the vertex datum (e) is compared with the Tate datum.

Structures over the concrete charts `R1 O a`, `R0 O a` time out at declaration (even
`structure _ where x : R1 O a`), so `DatumG` and `HomG` are stated over abstract types and
instantiated by `abbrev` (rule 17).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace CuspTower

open TateLevel AdmissibleLift EtaleTower

variable {O : Type u} [CommRing O] {T0' : Type u} [CommRing T0'] [Algebra O T0'] {c0 x0 : T0'}
  {k : Type u} [Field k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  (Sc Sc' Sc'' : CuspSpecial T0' c0 x0 (θ := θ)) {ϖ : O} (hϖ : θ ϖ = 0)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing T0']
  (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The maps of the cusp pieces as ring maps of the `Piece0` levels** (`pieceMap`; stating the
maps with the `Piece0` types generically avoids an expensive unification at concrete charts). -/
def pieceP (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ) :
    (cuspPiece Sc hϖ hker hx hO).P n →+* (cuspPiece Sc' hϖ hker hx hO).P n :=
  (pieceMap Sc Sc' hϖ hker hx hnf φ0 n).toRingHom

lemma pieceP_algebraMapB (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ)
    (y : Tn ϖ T0' n) :
    pieceP Sc Sc' hϖ hker hx hO hnf φ0 n
        (algebraMap (Tn ϖ T0' n) ((cuspPiece Sc hϖ hker hx hO).P n) y) =
      algebraMap (Tn ϖ T0' n) ((cuspPiece Sc' hϖ hker hx hO).P n) y :=
  pieceMap_algebraMapB Sc Sc' hϖ hker hx hO hnf φ0 n y

lemma pieceP_algebraMapO (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ) (o : O) :
    pieceP Sc Sc' hϖ hker hx hO hnf φ0 n (algebraMap O ((cuspPiece Sc hϖ hker hx hO).P n) o) =
      algebraMap O ((cuspPiece Sc' hϖ hker hx hO).P n) o :=
  pieceMap_algebraMapO Sc Sc' hϖ hker hx hO hnf φ0 n o

lemma sP_pieceP (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ)
    (x : (cuspPiece Sc hϖ hker hx hO).P (n + 1)) :
    (cuspPiece Sc' hϖ hker hx hO).sP n (pieceP Sc Sc' hϖ hker hx hO hnf φ0 (n + 1) x) =
      pieceP Sc Sc' hϖ hker hx hO hnf φ0 n ((cuspPiece Sc hϖ hker hx hO).sP n x) :=
  sP_pieceMap Sc Sc' hϖ hker hx hO hnf φ0 n x

lemma pieceP_id (hnf : CuspNFc Sc) (n : ℕ) (x : (cuspPiece Sc hϖ hker hx hO).P n) :
    pieceP Sc Sc hϖ hker hx hO hnf (AlgHom.id _ _) n x = x :=
  DFunLike.congr_fun (pieceMap_id Sc hϖ hker hx hnf n) x

lemma pieceP_comp (hnf' : CuspNFc Sc') (hnf'' : CuspNFc Sc'')
    (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (φ0' : Sc'.C0 →ₐ[Ts θ T0'] Sc''.C0) (n : ℕ)
    (x : (cuspPiece Sc hϖ hker hx hO).P n) :
    pieceP Sc Sc'' hϖ hker hx hO hnf'' (φ0'.comp φ0) n x =
      pieceP Sc' Sc'' hϖ hker hx hO hnf'' φ0' n (pieceP Sc Sc' hϖ hker hx hO hnf' φ0 n x) :=
  (DFunLike.congr_fun (pieceMap_comp Sc Sc' Sc'' hϖ hker hx hnf' hnf'' φ0 φ0' n) x).symm

/-- **The maps of the cusp pieces on the overlap reduce to `φ0` through `ℓ0`**, with the map of
the overlaps written as `IsLocalization.Away.lift` of `pieceP` (the form of `Overlap.mM`;
`mk_mLoc_ℓ0`). -/
theorem mk_liftP_ℓ0 (hnf : CuspNFc Sc') (φ0 : Sc.C0 →ₐ[Ts θ T0'] Sc'.C0) (n : ℕ)
    (hp0 : pieceP Sc Sc' hϖ hker hx hO hnf φ0 n (algebraMap (Tn ϖ T0' n)
        ((cuspPiece Sc hϖ hker hx hO).P n) (algebraMap T0' (Tn ϖ T0' n) x0)) =
      algebraMap (Tn ϖ T0' n) ((cuspPiece Sc' hϖ hker hx hO).P n)
        (algebraMap T0' (Tn ϖ T0' n) x0))
    (c : Sc.C0)
    (m : OverlapPiece.M (algebraMap T0' (Tn ϖ T0' n) x0) ((cuspPiece Sc hϖ hker hx hO).P n))
    (hm : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := Tn ϖ T0' n))
      (OverlapPiece.M (algebraMap T0' (Tn ϖ T0' n) x0) ((cuspPiece Sc hϖ hker hx hO).P n))) m =
      (cuspPiece Sc hϖ hker hx hO).ℓ0 n c) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := Tn ϖ T0' n))
      (OverlapPiece.M (algebraMap T0' (Tn ϖ T0' n) x0) ((cuspPiece Sc' hϖ hker hx hO).P n)))
      (IsLocalization.Away.lift (algebraMap (Tn ϖ T0' n) ((cuspPiece Sc hϖ hker hx hO).P n)
          (algebraMap T0' (Tn ϖ T0' n) x0))
        (g := (algebraMap ((cuspPiece Sc' hϖ hker hx hO).P n)
          (OverlapPiece.M (algebraMap T0' (Tn ϖ T0' n) x0)
            ((cuspPiece Sc' hϖ hker hx hO).P n))).comp (pieceP Sc Sc' hϖ hker hx hO hnf φ0 n))
        (by rw [RingHom.comp_apply, hp0]; exact IsLocalization.Away.algebraMap_isUnit _) m) =
      (cuspPiece Sc' hϖ hker hx hO).ℓ0 n (φ0 c) :=
  mk_mLoc_ℓ0 Sc Sc' hϖ hker hx hO hnf φ0 n c m hm

end CuspTower

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

/-! ### Morphisms of data -/

end

section Generic

/-- **A datum of a covering on two charts** (generic, over abstract charts `T1`, `T0`; a
`structure` over the concrete `P1Three` charts times out at declaration, rule 17): a special
covering `Sp` over `T1`, a cusp special datum `S0` over `T0` and an overlap datum in `W Sp S0`. -/
structure DatumG {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
    [Fact (Function.Surjective θ)] (T1 T0 : Type u) [CommRing T1] [Algebra O T1] [CommRing T0]
    [Algebra O T0] (x : T0)
    (W : CuspChart.Special θ T1 1 1 → CuspTower.CuspSpecial T0 1 x (θ := θ) → Type u) :
    Type (u + 1) where
  /-- the covering over the first chart -/
  Sp : CuspChart.Special θ T1 1 1
  /-- the cusp special datum over the second chart -/
  S0 : CuspTower.CuspSpecial T0 1 x (θ := θ)
  /-- the overlap datum -/
  ω : W Sp S0

/-- **A pair of algebra maps satisfying a compatibility `P`** (generic morphisms of data). -/
structure HomG {A1 A0 C1 C1' C0 C0' : Type u} [CommRing A1] [CommRing A0] [CommRing C1]
    [CommRing C1'] [CommRing C0] [CommRing C0'] [Algebra A1 C1] [Algebra A1 C1'] [Algebra A0 C0]
    [Algebra A0 C0'] (P : (C1 →ₐ[A1] C1') → (C0 →ₐ[A0] C0') → Prop) : Type u where
  /-- the map over the first chart -/
  φ1 : C1 →ₐ[A1] C1'
  /-- the map over the second chart -/
  φ0 : C0 →ₐ[A0] C0'
  hω : P φ1 φ0

end Generic

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

variable (O θ a) in
/-- **The datum of a tame cover of `ℙ¹_k ∖ {0, 1, ā}`**: the covering `Sp` over `V₁`, the cusp
special datum `S0` over `V₀`, and the overlap identification `ω : C0[1/x̄] ≃ C1[1/ȳ]`. -/
abbrev Datum : Type (u + 1) :=
  DatumG θ (R1 O a) (R0 O a) (x0 O a) (fun Sp S0 ↦ OmegaC Sp S0.C0)

namespace Datum

/-- The overlap identification of a datum. -/
abbrev om (D : Datum O θ a) : OmegaC D.Sp D.S0.C0 := D.ω

/-- The compatibility of maps `φ1 : C1 → C1'`, `φ0 : C0 → C0'` with `ω`, `ω'`. -/
def OmegaCompat (D D' : Datum O θ a) (φ1 : D.Sp.C1 →ₐ[Ts θ (R1 O a)] D'.Sp.C1)
    (φ0 : D.S0.C0 →ₐ[Ts θ (R0 O a)] D'.S0.C0) : Prop :=
  ∀ z, D'.om (EtaleTower.CbMap (R0 O a) (x0 O a) φ0 z) =
    EtaleTower.CbMap (R1 O a) (y1 O a) φ1 (D.om z)

/-- **A morphism of data**: maps `φ1 : C1 → C1'`, `φ0 : C0 → C0'` compatible with `ω`, `ω'`. -/
abbrev Hom (D D' : Datum O θ a) : Type u := HomG (OmegaCompat D D')

/-- The identity morphism of a datum. -/
def Hom.id (D : Datum O θ a) : Hom D D :=
  ⟨AlgHom.id _ _, AlgHom.id _ _, fun z ↦ by
    rw [EtaleTower.CbMap_id, EtaleTower.CbMap_id]; rfl⟩

/-- Composition of morphisms of data. -/
def Hom.comp {D D' D'' : Datum O θ a} (g : Hom D' D'') (f : Hom D D') : Hom D D'' :=
  ⟨g.φ1.comp f.φ1, g.φ0.comp f.φ0, fun z ↦ by
    rw [EtaleTower.CbMap_comp, EtaleTower.CbMap_comp, RingHom.comp_apply, RingHom.comp_apply,
      g.hω, f.hω]⟩

end Datum

namespace Datum

variable (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {D D' D'' : Datum O θ a}

/-- `φ0` on the localizations at `x̄`. -/
abbrev Lx0Map (f : D.Hom D') :
    EtaleTower.Cb θ (R0 O a) D.S0.C0 (x0 O a) →+* EtaleTower.Cb θ (R0 O a) D'.S0.C0 (x0 O a) :=
  EtaleTower.CbMap (R0 O a) (x0 O a) f.φ0

/-- `φ1` on the localizations at `ȳ`. -/
abbrev Lx1Map (f : D.Hom D') :
    EtaleTower.Cb θ (R1 O a) D.Sp.C1 (y1 O a) →+* EtaleTower.Cb θ (R1 O a) D'.Sp.C1 (y1 O a) :=
  EtaleTower.CbMap (R1 O a) (y1 O a) f.φ1

/-- The maps of the cusp pieces of a morphism of data, as ring maps of the overlap pieces. -/
abbrev pM (f : D.Hom D') (n : ℕ) :
    (overlap D.Sp hϖ hker D.S0 D.om hO).P0.P n →+* (overlap D'.Sp hϖ hker D'.S0 D'.om hO).P0.P n :=
  CuspTower.pieceP D.S0 D'.S0 hϖ hker (isSMulRegular_x0 ϖ a) hO (cuspNFc a ha0 ha1 D'.S0) f.φ0 n

lemma hp0 (f : D.Hom D') (n : ℕ) :
    pM hϖ hker ha0 ha1 hO f n (algebraMap ((overlap D.Sp hϖ hker D.S0 D.om hO).B' n)
        ((overlap D.Sp hϖ hker D.S0 D.om hO).P0.P n)
        (algebraMap (overlap D.Sp hϖ hker D.S0 D.om hO).B0'
          ((overlap D.Sp hϖ hker D.S0 D.om hO).B' n) (overlap D.Sp hϖ hker D.S0 D.om hO).x0)) =
      algebraMap ((overlap D'.Sp hϖ hker D'.S0 D'.om hO).B' n)
        ((overlap D'.Sp hϖ hker D'.S0 D'.om hO).P0.P n)
        (algebraMap (overlap D'.Sp hϖ hker D'.S0 D'.om hO).B0'
          ((overlap D'.Sp hϖ hker D'.S0 D'.om hO).B' n)
          (overlap D'.Sp hϖ hker D'.S0 D'.om hO).x0) :=
  CuspTower.pieceP_algebraMapB D.S0 D'.S0 hϖ hker (isSMulRegular_x0 ϖ a) hO
    (cuspNFc a ha0 ha1 D'.S0) f.φ0 n _

lemma hpO (f : D.Hom D') (n : ℕ) (o : O) :
    pM hϖ hker ha0 ha1 hO f n (algebraMap O ((overlap D.Sp hϖ hker D.S0 D.om hO).P0.P n) o) =
      algebraMap O ((overlap D'.Sp hϖ hker D'.S0 D'.om hO).P0.P n) o :=
  CuspTower.pieceP_algebraMapO D.S0 D'.S0 hϖ hker (isSMulRegular_x0 ϖ a) hO
    (cuspNFc a ha0 ha1 D'.S0) f.φ0 n o

lemma hpS (f : D.Hom D') (n : ℕ) (e : (overlap D.Sp hϖ hker D.S0 D.om hO).P0.P (n + 1)) :
    (overlap D'.Sp hϖ hker D'.S0 D'.om hO).P0.sP n (pM hϖ hker ha0 ha1 hO f (n + 1) e) =
      pM hϖ hker ha0 ha1 hO f n ((overlap D.Sp hϖ hker D.S0 D.om hO).P0.sP n e) :=
  CuspTower.sP_pieceP D.S0 D'.S0 hϖ hker (isSMulRegular_x0 ϖ a) hO
    (cuspNFc a ha0 ha1 D'.S0) f.φ0 n e

lemma hpB (f : D.Hom D') (n : ℕ) (b : (input D.Sp hϖ hker).B0) :
    (overlap D.Sp hϖ hker D.S0 D.om hO).mM (overlap D'.Sp hϖ hker D'.S0 D'.om hO) n
        (pM hϖ hker ha0 ha1 hO f n) (hp0 hϖ hker ha0 ha1 hO f n)
        (letI := (overlap D.Sp hϖ hker D.S0 D.om hO).alg0M n;
          algebraMap (input D.Sp hϖ hker).B0 ((overlap D.Sp hϖ hker D.S0 D.om hO).M n) b) =
      (letI := (overlap D'.Sp hϖ hker D'.S0 D'.om hO).alg0M n;
        algebraMap (input D'.Sp hϖ hker).B0 ((overlap D'.Sp hϖ hker D'.S0 D'.om hO).M n)
          (RingHom.id _ b)) :=
  (overlap D.Sp hϖ hker D.S0 D.om hO).mM_algebraMap0 (overlap D'.Sp hϖ hker D'.S0 D'.om hO)
    (pM hϖ hker ha0 ha1 hO f n) (hp0 hϖ hker ha0 ha1 hO f n) (RingHom.id _)
    (fun y ↦ CuspTower.pieceP_algebraMapB D.S0 D'.S0 hϖ hker (isSMulRegular_x0 ϖ a) hO
      (cuspNFc a ha0 ha1 D'.S0) f.φ0 n y)
    (RingHom.id _) (fun _ ↦ rfl) (RingHom.id _) (fun _ ↦ rfl) b

lemma hpγ (f : D.Hom D') (c : D.Sp.C1) (m : (overlap D.Sp hϖ hker D.S0 D.om hO).M 0)
    (hm : Ideal.Quotient.mk (letI := (overlap D.Sp hϖ hker D.S0 D.om hO).algBM 0;
        EtaleNil.JB (J θ (R := (input D.Sp hϖ hker).B 0)) ((overlap D.Sp hϖ hker D.S0 D.om hO).M 0))
        m = (overlap D.Sp hϖ hker D.S0 D.om hO).γM 0 c) :
    Ideal.Quotient.mk (letI := (overlap D'.Sp hϖ hker D'.S0 D'.om hO).algBM 0;
        EtaleNil.JB (J θ (R := (input D'.Sp hϖ hker).B 0))
          ((overlap D'.Sp hϖ hker D'.S0 D'.om hO).M 0))
      ((overlap D.Sp hϖ hker D.S0 D.om hO).mM (overlap D'.Sp hϖ hker D'.S0 D'.om hO) 0
        (pM hϖ hker ha0 ha1 hO f 0) (hp0 hϖ hker ha0 ha1 hO f 0) m) =
      (overlap D'.Sp hϖ hker D'.S0 D'.om hO).γM 0 (f.φ1 c) :=
  (overlap D.Sp hϖ hker D.S0 D.om hO).mk_mM_γM (overlap D'.Sp hϖ hker D'.S0 D'.om hO)
    (pM hϖ hker ha0 ha1 hO f 0) (hp0 hϖ hker ha0 ha1 hO f 0) (hpO hϖ hker ha0 ha1 hO f 0)
    f.φ0.toRingHom
    (fun c m hm ↦ CuspTower.mk_liftP_ℓ0 D.S0 D'.S0 hϖ hker (isSMulRegular_x0 ϖ a) hO
      (cuspNFc a ha0 ha1 D'.S0) f.φ0 0 (hp0 hϖ hker ha0 ha1 hO f 0) c m hm)
    (Lx0Map f) (fun c ↦ EtaleTower.CbMap_algebraMap (R0 O a) (x0 O a) f.φ0 c)
    f.φ1.toRingHom (Lx1Map f) (fun c ↦ EtaleTower.CbMap_algebraMap (R1 O a) (y1 O a) f.φ1 c)
    f.hω c m hm

/-- **The overlap condition over `V₀ ∩ V₁`** (the hypothesis `hψ` of `Overlap.twoChartMap`), from
the bottom level (`NodeEtaleGlue.Overlap.hψ_of_bottom`). -/
theorem hψ (f : D.Hom D') (n : ℕ) (z : (input D.Sp hϖ hker).Y hθ.out n) :
    (overlap D'.Sp hϖ hker D'.S0 D'.om hO).ψ hθ.out hO n (yMap hϖ hker D.Sp D'.Sp f.φ1 n z) =
      (overlap D.Sp hϖ hker D.S0 D.om hO).mM (overlap D'.Sp hϖ hker D'.S0 D'.om hO) n
        (pM hϖ hker ha0 ha1 hO f n) (hp0 hϖ hker ha0 ha1 hO f n)
        ((overlap D.Sp hϖ hker D.S0 D.om hO).ψ hθ.out hO n z) :=
  (overlap D.Sp hϖ hker D.S0 D.om hO).hψ_of_bottom (overlap D'.Sp hϖ hker D'.S0 D'.om hO)
    hθ.out hO (fun n ↦ yMap hϖ hker D.Sp D'.Sp f.φ1 n)
    (fun n ↦ yMap_algebraMap hϖ hker D.Sp D'.Sp f.φ1 n _)
    (fun n z ↦ yMap_succ hϖ hker D.Sp D'.Sp hO f.φ1 n z)
    (fun n ↦ pM hϖ hker ha0 ha1 hO f n) (fun n ↦ hp0 hϖ hker ha0 ha1 hO f n)
    (fun n e ↦ hpS hϖ hker ha0 ha1 hO f n e) (RingHom.id _)
    (fun n b ↦ yMap_algebraMap hϖ hker D.Sp D'.Sp f.φ1 n b)
    (fun n b ↦ hpB hϖ hker ha0 ha1 hO f n b)
    (J_Tn_zero_eq_bot hker _) (J_Tn_zero_eq_bot hker _) f.φ1.toRingHom
    (fun c ↦ yMap_yEquiv hϖ hker D.Sp D'.Sp hO f.φ1 c)
    (fun c m hm ↦ hpγ hϖ hker ha0 ha1 hO f c m hm) n z

lemma hyO (f : D.Hom D') (n : ℕ) (o : O) :
    yMap hϖ hker D.Sp D'.Sp f.φ1 n
        (letI := (overlap D.Sp hϖ hker D.S0 D.om hO).algOY hθ.out n;
          algebraMap O ((input D.Sp hϖ hker).Y hθ.out n) o) =
      (letI := (overlap D'.Sp hϖ hker D'.S0 D'.om hO).algOY hθ.out n;
        algebraMap O ((input D'.Sp hϖ hker).Y hθ.out n) o) :=
  yMap_algebraMap hϖ hker D.Sp D'.Sp f.φ1 n _

/-- The morphisms of the two-chart rings at level `n` of a morphism of data. -/
abbrev twoChartMap (f : D.Hom D') (n : ℕ) :=
  (overlap D.Sp hϖ hker D.S0 D.om hO).twoChartMap (overlap D'.Sp hϖ hker D'.S0 D'.om hO)
    hθ.out hO n (yMap hϖ hker D.Sp D'.Sp f.φ1 n)
    (yMap_algebraMap hϖ hker D.Sp D'.Sp f.φ1 n _) (hyO hϖ hker hO f n)
    (pM hϖ hker ha0 ha1 hO f n) (hp0 hϖ hker ha0 ha1 hO f n) (hpO hϖ hker ha0 ha1 hO f n)
    (hψ hϖ hker ha0 ha1 hO f n)

end Datum
end

end P1Three

end

end SemistableReduction
