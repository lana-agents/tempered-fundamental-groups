/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialMk
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialFibre
import TemperedFundamentalGroups.SemistableReduction.P1ThreeCuspNF
import TemperedFundamentalGroups.SemistableReduction.EtaleTowerHom
import TemperedFundamentalGroups.SemistableReduction.CuspInputHom
import TemperedFundamentalGroups.SemistableReduction.CuspPieceOverlap
import TemperedFundamentalGroups.SemistableReduction.OverlapHom
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueEnd

/-!
# Maps of the lifts of tame covers of `ℙ¹_k ∖ {0, 1, ā}` over `V₁` (MR13 A1 (b))

A map `φ : C1 → C1'` of the special-fibre coverings over `V₁ = ℙ¹ ∖ {0, 1, a}` lifts uniquely
through the M2 construction over `V₁` (MR12's generic core, recipe "P1Three step-3",
MR12-tfg-plan c47); the cusp side, morphisms of data and the functoriality of the lifts are in
`P1ThreeHomDatum`.

* `CuspChart.Special.covMap` (the map of the coverings of `T[1/1]/J`), `cuspNF_one` (the Kummer
  normal form hypotheses hold trivially over `V₁`: the completion along `1` is zero);
* **`gMap`** (the maps of the trivial patches, `LevelTower.cuspLevelMap`), `tr_gMap`, `gMap_id`,
  `gMap_comp`; **`eMap`** (the maps of the étale lifts `E1`, `EtaleTower.homLift`), `eMap_id`,
  `eMap_comp`, `sE_eMap`;
* **`hg`** (the overlap condition over `V₁`, `NodeEtaleGlue.Input.hg_of_special`), **`yMap`** (the
  map of the coverings over `V₁` at every level), `yMap_succ`, `yMap_algebraMap`, `yMap_id`,
  `yMap_comp`, **`yMap_yEquiv`** (at the bottom level `yMap` is `φ` on `C1 ≃ Y 0`).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

namespace CuspChart

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {T : Type u} [CommRing T] [Algebra O T] {y s : T}

/-- **The map of the coverings of `T[1/1]/J`** induced by a map `φ : C1 → C1'` of the
special-fibre coverings (`cov.C = C1[1/1]` through `ι₀`). -/
def Special.covMap [Fact (Function.Surjective θ)] (Sp Sp' : Special θ T y s)
    (φ : Sp.C1 →ₐ[Ts θ T] Sp'.C1) : Sp.cov.C →ₐ[Ts θ (CuspTower.Rc T (1 : T))] Sp'.cov.C :=
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  { IsLocalization.Away.lift (algebraMap (Ts θ T) Sp.C1 (Ideal.Quotient.mk _ 1))
      (g := Sp'.ι₀.comp φ.toRingHom) (by
        rw [map_one, map_one, map_one]; exact isUnit_one) with
    commutes' := fun x ↦ by
      obtain ⟨z, rfl⟩ := (bijective_φsC_one θ T).2 x
      change IsLocalization.Away.lift _ _ _ = _
      rw [← Sp.hι₀, ← Sp'.hι₀]
      change IsLocalization.Away.lift _ _ (algebraMap Sp.C1 Sp.cov.C _) = _
      rw [IsLocalization.Away.lift_eq, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
        AlgHom.coe_toRingHom, AlgHom.commutes] }

lemma Special.covMap_ι₀ [Fact (Function.Surjective θ)] (Sp Sp' : Special θ T y s)
    (φ : Sp.C1 →ₐ[Ts θ T] Sp'.C1) (x : Sp.C1) :
    Sp.covMap Sp' φ (Sp.ι₀ x) = Sp'.ι₀ (φ x) :=
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  IsLocalization.Away.lift_eq (S := Sp.cov.C) _
    (g := Sp'.ι₀.comp φ.toRingHom) (by rw [map_one, map_one, map_one]; exact isUnit_one) x

/-- `covMap` is determined by its values on `ι₀`. -/
lemma Special.covMap_ext [Fact (Function.Surjective θ)] (Sp Sp' : Special θ T y s)
    {f g : Sp.cov.C →ₐ[Ts θ (CuspTower.Rc T (1 : T))] Sp'.cov.C}
    (h : ∀ x, f (Sp.ι₀ x) = g (Sp.ι₀ x)) : f = g := by
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  exact AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers
    (algebraMap (Ts θ T) Sp.C1 (Ideal.Quotient.mk _ 1))) (RingHom.ext h))

lemma Special.covMap_id [Fact (Function.Surjective θ)] (Sp : Special θ T y s) :
    Sp.covMap Sp (AlgHom.id _ _) = AlgHom.id _ _ :=
  Special.covMap_ext Sp Sp fun x ↦ Special.covMap_ι₀ Sp Sp _ x

lemma Special.covMap_comp [Fact (Function.Surjective θ)] (Sp Sp' Sp'' : Special θ T y s)
    (φ : Sp.C1 →ₐ[Ts θ T] Sp'.C1) (φ' : Sp'.C1 →ₐ[Ts θ T] Sp''.C1) :
    Sp.covMap Sp'' (φ'.comp φ) = (Sp'.covMap Sp'' φ').comp (Sp.covMap Sp' φ) :=
  Special.covMap_ext Sp Sp'' fun x ↦ by
    rw [AlgHom.comp_apply, Special.covMap_ι₀, Special.covMap_ι₀, Special.covMap_ι₀,
      AlgHom.comp_apply]

end CuspChart

/-! ### The maps over `V₁`: trivial patches and étale pieces -/

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp Sp' Sp'' : Special1 O θ a)

omit [IsNoetherianRing O] in
/-- **The Kummer normal form hypotheses over `V₁`** hold trivially: the completion along `1` is
the zero ring. -/
lemma cuspNF_one : LevelTower.CuspNF (CuspTower.ψb (θ := θ) _
    (CuspTower.sC (R1 O a) 1 1) (CuspTower.sC (R1 O a) 1 1)) Sp.cov := fun i ↦ by
  haveI := CuspChart.subsingleton_hat_one (θ := θ) (T := R1 O a)
  haveI : Subsingleton (Admissible.Hat (fbar θ (CuspTower.sC (R1 O a) (1 : R1 O a) (1 : R1 O a)))
      ⧸ Ideal.span {1 - Sp.cov.cidem i}) := Ideal.Quotient.mk_surjective.subsingleton
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, ⟨fun _ _ ↦ Subsingleton.elim _ _⟩,
    fun _ _ ↦ Subsingleton.elim _ _⟩

/-- **The maps of the (trivial) patches over `V₁`** at level `n` induced by `φ : C1 → C1'`. -/
def gMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ) :
    (tower1 Sp hϖ hker).G hθ.out n →ₐ[Tn ϖ (Rc1 O a) n] (tower1 Sp' hϖ hker).G hθ.out n :=
  LevelTower.cuspLevelMap hθ.out ((tower1 Sp hϖ hker).level n) ((tower1 Sp' hϖ hker).level n)
    (Sp.covMap Sp' φ) rfl (cuspNF_one Sp')

lemma gMap_id (n : ℕ) : gMap hϖ hker Sp Sp (AlgHom.id _ _) n = AlgHom.id _ _ :=
  LevelTower.cuspLevelMap_id hθ.out _ _ rfl _ (Sp.covMap_id)

lemma gMap_comp (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (φ' : Sp'.C1 →ₐ[Ts θ (R1 O a)] Sp''.C1)
    (n : ℕ) : (gMap hϖ hker Sp' Sp'' φ' n).comp (gMap hϖ hker Sp Sp' φ n) =
      gMap hϖ hker Sp Sp'' (φ'.comp φ) n :=
  LevelTower.cuspLevelMap_comp hθ.out ((tower1 Sp hϖ hker).level n)
    ((tower1 Sp' hϖ hker).level n) ((tower1 Sp'' hϖ hker).level n)
    (Sp.covMap Sp' φ) (Sp'.covMap Sp'' φ') (Sp.covMap Sp'' (φ'.comp φ)) rfl rfl rfl
    (cuspNF_one Sp') (cuspNF_one Sp'') (Sp.covMap_comp Sp' Sp'' φ φ')

/-- **The maps of the patches commute with the transition maps of the towers.** -/
theorem tr_gMap (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ)
    (x : (tower1 Sp hϖ hker).G hθ.out (n + 1)) :
    (tower1 Sp' hϖ hker).tr hθ.out hO n (gMap hϖ hker Sp Sp' φ (n + 1) x) =
      gMap hϖ hker Sp Sp' φ n ((tower1 Sp hϖ hker).tr hθ.out hO n x) :=
  let T := tower1 Sp hϖ hker
  let T' := tower1 Sp' hϖ hker
  LevelTower.tr_cuspLevelMap hθ.out hO T.hq T.hf T.he T.level T.hcχ
    (LevelTower.hεε_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg
      T.hf T.he)
    (LevelTower.hδδ_mk T.hfe T.hπ T.χ T.hχ T.t T.ht T.hJ T.hflat T.hfχ T.hreg
      T.hf T.he) T.hct
    T'.level T'.hcχ
    (LevelTower.hεε_mk T'.hfe T'.hπ T'.χ T'.hχ T'.t T'.ht T'.hJ T'.hflat T'.hfχ T'.hreg
      T'.hf T'.he)
    (LevelTower.hδδ_mk T'.hfe T'.hπ T'.χ T'.hχ T'.t T'.ht T'.hJ T'.hflat T'.hfχ T'.hreg
      T'.hf T'.he) T'.hct
    (Sp.covMap Sp' φ) (fun _ ↦ rfl) (cuspNF_one Sp') n x

/-- **The maps of the étale lifts over `V₁`** at level `n` induced by `φ : C1 → C1'`
(`EtaleTower.homLift`). -/
def eMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ) :
    (E1 Sp hϖ hker n).E →ₐ[Tn ϖ (R1 O a) n] (E1 Sp' hϖ hker n).E :=
  EtaleTower.homLift (R1 O a) hϖ 1 hker φ (E1 Sp hϖ hker n) (E1 Sp' hϖ hker n)

lemma eMap_id (n : ℕ) : eMap hϖ hker Sp Sp (AlgHom.id _ _) n = AlgHom.id _ _ :=
  EtaleTower.homLift_id (R1 O a) hϖ 1 hker _

lemma eMap_comp (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (φ' : Sp'.C1 →ₐ[Ts θ (R1 O a)] Sp''.C1)
    (n : ℕ) : eMap hϖ hker Sp Sp'' (φ'.comp φ) n =
      (eMap hϖ hker Sp' Sp'' φ' n).comp (eMap hϖ hker Sp Sp' φ n) :=
  EtaleTower.homLift_comp (R1 O a) hϖ 1 hker φ φ' _ _ _

lemma sE_eMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ) (x : (E1 Sp hϖ hker (n + 1)).E) :
    sE Sp' hϖ hker n (eMap hϖ hker Sp Sp' φ (n + 1) x) =
      eMap hϖ hker Sp Sp' φ n (sE Sp hϖ hker n x) :=
  EtaleTower.succ_comp_homLift (R1 O a) hϖ 1 hker φ _ _ _ _ x

/-! ### The maps of the coverings over `V₁` -/

/-- The étale part of `gMap` (`LevelTower.pMap`). -/
abbrev pMap1 (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ) :
    ((tower1 Sp hϖ hker).level n).P →+* ((tower1 Sp' hϖ hker).level n).P :=
  (LevelTower.pMap ((tower1 Sp hϖ hker).level n) ((tower1 Sp' hϖ hker).level n)
    (Sp.covMap Sp' φ)).toRingHom

/-- `covMap φ` on the localizations at `f n` (`FormalPatchLevel.NfMap`). -/
abbrev ℓfMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ) :
    FormalPatchLevel.Nf ((tower1 Sp hϖ hker).f n)
        (Sp.cov.transport (h := (tower1 Sp hϖ hker).hfe n)).C →+*
      FormalPatchLevel.Nf ((tower1 Sp hϖ hker).f n)
        (Sp'.cov.transport (h := (tower1 Sp hϖ hker).hfe n)).C :=
  (FormalPatchLevel.NfMap ((tower1 Sp hϖ hker).f n)
    (LevelTower.transportMapR ((tower1 Sp hϖ hker).hfe n) (Sp.covMap Sp' φ))).toRingHom

lemma ℓfMap_algebraMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ)
    (c : (Sp.cov.transport (h := (tower1 Sp hϖ hker).hfe n)).C) :
    ℓfMap hϖ hker Sp Sp' φ n (algebraMap _ (FormalPatchLevel.Nf ((tower1 Sp hϖ hker).f n)
        (Sp.cov.transport (h := (tower1 Sp hϖ hker).hfe n)).C) c) =
      algebraMap _ (FormalPatchLevel.Nf ((tower1 Sp hϖ hker).f n)
        (Sp'.cov.transport (h := (tower1 Sp hϖ hker).hfe n)).C)
        (LevelTower.transportMapR ((tower1 Sp hϖ hker).hfe n) (Sp.covMap Sp' φ) c) :=
  FormalPatchLevel.NfMap_algebraMap _ _ c

/-- `φ` on the localizations at `1`. -/
abbrev ℓbMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) :
    EtaleTower.Cb θ (R1 O a) Sp.C1 1 →+* EtaleTower.Cb θ (R1 O a) Sp'.C1 1 :=
  EtaleTower.CbMap (R1 O a) 1 φ

/-- **The overlap condition over `V₁`** (the hypothesis `hg` of `NodeEtaleGlue.Input.yMap`), from
the special fibres (`NodeEtaleGlue.Input.hg_of_special`). -/
theorem hg (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ)
    (x : (input Sp hϖ hker).T.G hθ.out n) :
    NodeEtaleGlue.ρa0 (input Sp' hϖ hker).T hθ.out (input Sp' hϖ hker).B
      (input Sp' hϖ hker).qB (input Sp' hϖ hker).φs (input Sp' hϖ hker).hφs
      (input Sp' hϖ hker).ι₀ (input Sp' hϖ hker).hι₀ (input Sp' hϖ hker).a
      (input Sp' hϖ hker).b (input Sp' hϖ hker).ha (input Sp' hϖ hker).hι
      (input Sp' hϖ hker).E (input Sp' hϖ hker).σE (input Sp' hϖ hker).hbE
      (input Sp' hϖ hker).hdiv (input Sp' hϖ hker).hJB (input Sp' hϖ hker).B0 n
      (gMap hϖ hker Sp Sp' φ n x) =
    (input Sp hϖ hker).eab (input Sp' hϖ hker) n (eMap hϖ hker Sp Sp' φ n).toRingHom
      ((eMap hϖ hker Sp Sp' φ n).commutes _)
      (NodeEtaleGlue.ρa0 (input Sp hϖ hker).T hθ.out (input Sp hϖ hker).B
        (input Sp hϖ hker).qB (input Sp hϖ hker).φs (input Sp hϖ hker).hφs
        (input Sp hϖ hker).ι₀ (input Sp hϖ hker).hι₀ (input Sp hϖ hker).a
        (input Sp hϖ hker).b (input Sp hϖ hker).ha (input Sp hϖ hker).hι
        (input Sp hϖ hker).E (input Sp hϖ hker).σE (input Sp hϖ hker).hbE
        (input Sp hϖ hker).hdiv (input Sp hϖ hker).hJB (input Sp hϖ hker).B0 n x) :=
  (input Sp hϖ hker).hg_of_special (input Sp' hϖ hker) hθ.out n
    (gMap hϖ hker Sp Sp' φ n).toRingHom (eMap hϖ hker Sp Sp' φ n).toRingHom
    ((eMap hϖ hker Sp Sp' φ n).commutes _) (RingHom.id _)
    (Ideal.map_le_iff_le_comap.2 fun _ hx ↦ hx) rfl
    (fun r ↦ (eMap hϖ hker Sp Sp' φ n).commutes r)
    (pMap1 hϖ hker Sp Sp' φ n) (fun _ ↦ rfl)
    (fun _ ↦ (LevelTower.pMap ((tower1 Sp hϖ hker).level n) ((tower1 Sp' hϖ hker).level n)
      (Sp.covMap Sp' φ)).commutes _)
    (Sp.covMap Sp' φ).toRingHom (ℓfMap hϖ hker Sp Sp' φ n)
    (fun c ↦ ℓfMap_algebraMap hϖ hker Sp Sp' φ n c)
    (fun x ↦ LevelTower.σP_pMap ((tower1 Sp hϖ hker).level n) ((tower1 Sp' hϖ hker).level n)
      (Sp.covMap Sp' φ) x)
    φ.toRingHom (fun c ↦ Sp.covMap_ι₀ Sp' φ c) (ℓbMap Sp Sp' φ)
    (fun c ↦ EtaleTower.CbMap_algebraMap (R1 O a) 1 φ c)
    (fun x ↦ EtaleTower.σ_homLift (R1 O a) hϖ 1 hker φ _ _ x) x

/-- **The map of the coverings over `V₁` at level `n`** induced by `φ : C1 → C1'`. -/
def yMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ) :
    (input Sp hϖ hker).Y hθ.out n →+* (input Sp' hϖ hker).Y hθ.out n :=
  (input Sp hϖ hker).yMap (input Sp' hϖ hker) hθ.out n (gMap hϖ hker Sp Sp' φ n).toRingHom
    (eMap hϖ hker Sp Sp' φ n).toRingHom ((eMap hϖ hker Sp Sp' φ n).commutes _)
    (hg hϖ hker Sp Sp' φ n)

lemma yMap_succ (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1)
    (n : ℕ) (z : (input Sp hϖ hker).Y hθ.out (n + 1)) :
    (input Sp' hϖ hker).Ymap hθ.out hO n (yMap hϖ hker Sp Sp' φ (n + 1) z) =
      yMap hϖ hker Sp Sp' φ n ((input Sp hϖ hker).Ymap hθ.out hO n z) :=
  (input Sp hϖ hker).yMap_succ (input Sp' hϖ hker) hθ.out hO
    (fun n ↦ (gMap hϖ hker Sp Sp' φ n).toRingHom) (fun n ↦ (eMap hϖ hker Sp Sp' φ n).toRingHom)
    (fun n ↦ (eMap hϖ hker Sp Sp' φ n).commutes _) (fun n ↦ hg hϖ hker Sp Sp' φ n)
    (fun n x ↦ tr_gMap hϖ hker Sp Sp' hO φ n x) (fun n x ↦ sE_eMap hϖ hker Sp Sp' φ n x) n z

lemma yMap_algebraMap (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (n : ℕ)
    (b : (input Sp hϖ hker).B0) :
    yMap hϖ hker Sp Sp' φ n (algebraMap (input Sp hϖ hker).B0 ((input Sp hϖ hker).Y hθ.out n) b) =
      algebraMap (input Sp' hϖ hker).B0 ((input Sp' hϖ hker).Y hθ.out n) b :=
  (input Sp hϖ hker).yMap_algebraMap (input Sp' hϖ hker) hθ.out n _ _
    ((eMap hϖ hker Sp Sp' φ n).commutes _) (hg hϖ hker Sp Sp' φ n) (RingHom.id _)
    (fun _ ↦ (gMap hϖ hker Sp Sp' φ n).commutes _) (fun _ ↦ (eMap hϖ hker Sp Sp' φ n).commutes _)
    b

lemma yMap_id (n : ℕ) (z : (input Sp hϖ hker).Y hθ.out n) :
    yMap hϖ hker Sp Sp (AlgHom.id (Ts θ (R1 O a)) Sp.C1) n z = z :=
  (input Sp hϖ hker).yMap_eq_id hθ.out n _ _ _ _
    (fun x ↦ DFunLike.congr_fun (gMap_id hϖ hker Sp n) x)
    (fun x ↦ DFunLike.congr_fun (eMap_id hϖ hker Sp n) x) z

lemma yMap_comp (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1) (φ' : Sp'.C1 →ₐ[Ts θ (R1 O a)] Sp''.C1)
    (n : ℕ) (z : (input Sp hϖ hker).Y hθ.out n) :
    yMap hϖ hker Sp Sp'' (φ'.comp φ) n z =
      yMap hϖ hker Sp' Sp'' φ' n (yMap hϖ hker Sp Sp' φ n z) :=
  (input Sp hϖ hker).yMap_comp (input Sp' hϖ hker) (input Sp'' hϖ hker) hθ.out n
    _ _ _ _ _ _ _ _ _ _ _ _
    (fun x ↦ (DFunLike.congr_fun (gMap_comp hϖ hker Sp Sp' Sp'' φ φ' n) x).symm)
    (fun x ↦ DFunLike.congr_fun (eMap_comp hϖ hker Sp Sp' Sp'' φ φ' n) x) z

/-- **The map of the coverings over `V₁` at the bottom level is `φ` on `yEquiv : C1 ≃ Y 0`**
(`NodeEtaleGlue.Input.yMap_yEquiv`). -/
theorem yMap_yEquiv (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (φ : Sp.C1 →ₐ[Ts θ (R1 O a)] Sp'.C1)
    (c : Sp.C1) :
    yMap hϖ hker Sp Sp' φ 0 ((input Sp hϖ hker).yEquiv hθ.out hO (J_Tn_zero_eq_bot hker _) c) =
      (input Sp' hϖ hker).yEquiv hθ.out hO (J_Tn_zero_eq_bot hker _) (φ c) :=
  (input Sp hϖ hker).yMap_yEquiv (input Sp' hϖ hker) hθ.out 0
    (g := (gMap hϖ hker Sp Sp' φ 0).toRingHom) (e := (eMap hϖ hker Sp Sp' φ 0).toRingHom)
    (he := (eMap hϖ hker Sp Sp' φ 0).commutes _)
    (p := pMap1 hϖ hker Sp Sp' φ 0) (hgp := fun _ ↦ rfl)
    (φc := (Sp.covMap Sp' φ).toRingHom)
    (ℓf := ℓfMap hϖ hker Sp Sp' φ 0)
    (hℓf := fun c ↦ ℓfMap_algebraMap hϖ hker Sp Sp' φ 0 c)
    (hp := fun x ↦ LevelTower.σP_pMap ((tower1 Sp hϖ hker).level 0)
      ((tower1 Sp' hϖ hker).level 0) (Sp.covMap Sp' φ) x)
    (φ1 := φ.toRingHom) (hφc := fun c ↦ Sp.covMap_ι₀ Sp' φ c)
    (ℓb := ℓbMap Sp Sp' φ)
    (hℓb := fun c ↦ EtaleTower.CbMap_algebraMap (R1 O a) 1 φ c)
    (hσE := fun x ↦ EtaleTower.σ_homLift (R1 O a) hϖ 1 hker φ _ _ x)
    (hO := hO) (hJ0 := J_Tn_zero_eq_bot hker _) (hJ0' := J_Tn_zero_eq_bot hker _)
    (hg := hg hϖ hker Sp Sp' φ 0) c

end

end P1Three

end

end SemistableReduction
