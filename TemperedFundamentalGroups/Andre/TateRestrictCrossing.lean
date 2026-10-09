/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictG1

/-!
# `HarmonicTateR` from `CrossingX1S` (Blueprint §10.3.8, `v(q) = 1`)

The target of `Statement.CrossingX1S` is the projective `O'`-model `c₂ = projModelCode O' hf` of
the function field of the Tate curve over `O'` (`π = √ϖ`), identified with the model of `X₀'` by
`isoR`. The model map `Q.isoψ isoR a` is compatible with the generic points
(`Pres.genericR`) and lies over `O → O'`; the germs of `c₂` at the nodes over `p`, `q` are node
germs over `O'` with uniformizer `√ϖ` (`TateNormal.nodeGerm_p`, `nodeGerm_q`). For `b₆` a unit
this gives `Pres.HarmonicTateR` for `ℰ = {E'}` (`Pres.harmonicTateR_of_crossingX1`).
-/

universe u

open CategoryTheory AlgebraicGeometry SemistableReduction.ProjScheme

namespace TemperedFundamentalGroups

noncomputable section

open TempObj TateRestrict RamifiedQuadratic SemistableReduction.W10Apply CurveConfig

attribute [local instance] TateNormal.algK

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)
  [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero K]
  (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  (R : Type u) [CommRing R] [Algebra K R] {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A] {xW : R}

namespace TateRestrict

/-- The projective `O'`-model of the function field of the Tate curve over `O'`. -/
abbrev c₂ : ModelCode (O' ϖ) :=
  projModelCode (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
    (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))

lemma isoR_toSpec : (isoR hϖ b₄ b₆).hom ≫ (c₂ hϖ b₄ b₆).toSpec ≫
    Spec.map (CommRingCat.ofHom (algebraMap O (O' ϖ))) = (modelR hϖ b₄ b₆).toSpec :=
  modelIsoO_toSpec O (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (θG ϖ) θG_ne_zero
    θG_isIntegral θG_gen (sO_ne_zero hϖ)

/-- The special fibres of the model of `X₀'` and of `c₂`. -/
def ΦR₂ : specialFibre (modelR hϖ b₄ b₆).toSpec ≃ₜ specialFibre (c₂ hϖ b₄ b₆).toSpec :=
  specialFibreHomeomorphDvr (algebraMap O (O' ϖ)) algebraMap_O'_injective _ _ (isoR hϖ b₄ b₆)
    (isoR_toSpec hϖ b₄ b₆)

lemma mem_Z_isoR (z : (modelR hϖ b₄ b₆).scheme) : z ∈ specialFibre (modelR hϖ b₄ b₆).toSpec ↔
    (isoR hϖ b₄ b₆).hom z ∈ SemistableReduction.ModelCode.Z (c₂ hϖ b₄ b₆) := by
  refine ⟨fun h ↦ (ΦR₂ hϖ b₄ b₆ ⟨z, h⟩).2, fun h ↦ ?_⟩
  have e : (isoR hϖ b₄ b₆).inv ((isoR hϖ b₄ b₆).hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
  exact e ▸ ((ΦR₂ hϖ b₄ b₆).symm ⟨_, h⟩).2

lemma isoR_eq_modelIso (p : specialFibre (modelR hϖ b₄ b₆).toSpec) :
    (isoR hϖ b₄ b₆).hom p.1 = (TateNormal.modelIso (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)).hom (ΦR hϖ b₄ b₆ p).1 := by
  have e : (isoT hϖ b₄ b₆).hom ≫ (TateNormal.modelIso (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)).hom = (isoR hϖ b₄ b₆).hom := by
    rw [isoT_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h := congrArg (fun φ ↦ φ p.1) e
  simp only [Scheme.Hom.comp_apply] at h
  rw [coe_ΦR]
  exact h.symm

lemma isoR_of_mem_Cp {p : specialFibre (modelR hϖ b₄ b₆).toSpec}
    (hp : p ∈ (decompR hϖ b₄ b₆).Cp) : (isoR hϖ b₄ b₆).hom p.1 = (TateNormal.modelIso (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)).hom
        (TateModel.pZ (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_mem hϖ)).1 := by
  rw [decompR_eq] at hp
  have h := (TateCovering.Decomp.mem_comap_Cp _ _).1 hp
  rw [TateModel.decomp_Cp] at h
  rw [isoR_eq_modelIso, Set.mem_singleton_iff.1 h]

lemma isoR_of_mem_Cq {q : specialFibre (modelR hϖ b₄ b₆).toSpec}
    (hq : q ∈ (decompR hϖ b₄ b₆).Cq) : (isoR hϖ b₄ b₆).hom q.1 = (TateNormal.modelIso (sO ϖ)
      (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ)).hom
        (TateModel.qZ (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_mem hϖ)).1 := by
  rw [decompR_eq] at hq
  have h := (TateCovering.Decomp.mem_comap_Cq _ _).1 hq
  rw [TateModel.decomp_Cq] at h
  rw [isoR_eq_modelIso, Set.mem_singleton_iff.1 h]

/-- Germ conditions at a point of `c₂`. -/
def NodeGermAt (y : (c₂ hϖ b₄ b₆).scheme) : Prop :=
  ∃ (P : Subring (TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆)))
    (u v : TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆))
    (n : ℕ), (P : Set _) = SemistableReduction.ModelCode.germs (c₂ hϖ b₄ b₆)
        (genericPt (O' ϖ) (TateNormal.hcoords (sO ϖ) (algebraMap O (O' ϖ) b₄)
          (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))) y ∧
    _root_.SemistableReduction.NodeGerm (O' ϖ) (sO ϖ) P u v n ∧ (∀ w ∈ P, u * w ≠ 1) ∧
      (∀ w ∈ P, v * w ≠ 1)

lemma nodeGermAt_of_mem_Cp {p : specialFibre (modelR hϖ b₄ b₆).toSpec}
    (hp : p ∈ (decompR hϖ b₄ b₆).Cp) : NodeGermAt hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom p.1) := by
  rw [isoR_of_mem_Cp hϖ b₄ b₆ hp]
  exact TateNormal.nodeGerm_p (b₄ := algebraMap O (O' ϖ) b₄) (b₆ := algebraMap O (O' ϖ) b₆)
    (sO_ne_zero hϖ) (sO_mem hϖ) (irreducible_sqrt hϖ)

lemma nodeGermAt_of_mem_Cq {q : specialFibre (modelR hϖ b₄ b₆).toSpec}
    (hq : q ∈ (decompR hϖ b₄ b₆).Cq) : NodeGermAt hϖ b₄ b₆ ((isoR hϖ b₄ b₆).hom q.1) := by
  rw [isoR_of_mem_Cq hϖ b₄ b₆ hq]
  exact TateNormal.nodeGerm_q (b₄ := algebraMap O (O' ϖ) b₄) (b₆ := algebraMap O (O' ϖ) b₆)
    (sO_ne_zero hϖ) (sO_mem hϖ) (irreducible_sqrt hϖ)

variable {R} in
/-- `isoR` as an identification of the model of `X₀'` with `c₂`. -/
def eR : (X₀' hϖ b₄ b₆ R heqR A).Lv.c.scheme ≅ (c₂ hϖ b₄ b₆).scheme := isoR hϖ b₄ b₆

variable {R} in
lemma eR_hom : (eR hϖ b₄ b₆ heqR A).hom = (isoR hϖ b₄ b₆).hom := rfl

end TateRestrict

namespace Pres

variable [IsDomain R] {Y : TempObj O R A} (Q : Pres xW Y) {R A}

set_option synthInstance.maxHeartbeats 200000 in
-- instance search for the towers over `O' = O_{K(√ϖ)}` and the function fields is slow
set_option maxHeartbeats 800000 in
-- the definitional checks along the instance paths of `O'` are slow
/-- **`CrossingX1S` for the model map of a member to the restricted Tate model**, with target
the projective `O'`-model `c₂`. -/
theorem crossing_R (hC : SemistableReduction.Statement.CrossingX1S.{u})
    (hx : Transcendental K x) (a : Q.U ⟶ X₀' hϖ b₄ b₆ R heqR A)
    (y' : (c₂ hϖ b₄ b₆).scheme) (w₁' w₂' : Set (c₂ hϖ b₄ b₆).scheme)
    (hw₁ : w₁' ∈ SemistableReduction.ModelCode.components (c₂ hϖ b₄ b₆))
    (hw₂ : w₂' ∈ SemistableReduction.ModelCode.components (c₂ hϖ b₄ b₆)) (hne : w₁' ≠ w₂')
    (hy₁ : y' ∈ w₁') (hy₂ : y' ∈ w₂')
    (hG : NodeGermAt hϖ b₄ b₆ y')
    (v : Set Q.D.c'.scheme) (hv : v ∈ SemistableReduction.ModelCode.components Q.D.c')
    (hψv : Q.isoψ (eR hϖ b₄ b₆ heqR A) a '' v = w₁') :
    ∃ w : SemistableReduction.ModelCode.Walk Q.D.c', w.v 0 = v ∧
      w.Crosses (Q.isoψ (eR hϖ b₄ b₆ heqR A) a) y' ∧
      Q.isoψ (eR hϖ b₄ b₆ heqR A) a '' w.v (Fin.last w.k) = w₂' := by
  haveI : IsScalarTower (O' ϖ) (K' ϖ) (TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆)) := inferInstance
  letI algK' : Algebra (K' ϖ) (TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆)) :=
    TateNormal.algK (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)
  letI : Algebra K (TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆)) :=
    ((@algebraMap (K' ϖ) _ _ _ algK').comp (algebraMap K (K' ϖ))).toAlgebra
  haveI : IsScalarTower K (K' ϖ) (TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆)) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : Algebra K Q.D.L₁ := Q.D.algKL
  haveI : IsScalarTower K Q.D.K' Q.D.L₁ := Q.D.isScalarTower_K
  letI : Algebra (TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆)) Q.D.L₁ := (Q.toFR hϖ b₄ b₆ heqR a hx).toAlgebra
  haveI : IsScalarTower K (TateNormal.TateField (sO ϖ) (algebraMap O (O' ϖ) b₄)
      (algebraMap O (O' ϖ) b₆)) Q.D.L₁ := IsScalarTower.of_algebraMap_eq fun k ↦
    (Q.psiK_algebraMap hϖ b₄ b₆ heqR a k).symm.trans (RingHom.congr_fun
      (TateNormal.toField_comp_algK (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)
        (Q.psiK hϖ b₄ b₆ heqR a) (Q.psiK_sO_ne_zero hϖ b₄ b₆ heqR a)
        (Q.equation_psiK hϖ b₄ b₆ heqR a) (Q.transcendental_psiK hϖ b₄ b₆ heqR a hx))
      (algebraMap K (K' ϖ) k)).symm
  have hres : CommRingCat.ofHom ((algebraMap K (K' ϖ)).restrict O (O' ϖ)
      (fun y hy ↦ by rw [← comap_OE O (K' ϖ)] at hy; exact hy)) =
      CommRingCat.ofHom (algebraMap O (O' ϖ)) := by
    ext
    rfl
  have hto : Q.isoψ (eR hϖ b₄ b₆ heqR A) a ≫ (c₂ hϖ b₄ b₆).toSpec ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap K (K' ϖ)).restrict O (O' ϖ)
        (fun y hy ↦ by rw [← comap_OE O (K' ϖ)] at hy; exact hy))) =
      Q.D.c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K Q.D.K').restrict O Q.D.O'
        (fun y hy ↦ by rw [← Q.D.hO'] at hy; exact hy))) := by
    rw [hres, ← Q.D.toSpec_e_inv]
    simp only [isoψ, Category.assoc, eR_hom]
    exact (congrArg (fun φ ↦ Q.D.e.inv ≫ a.ψ ≫ φ) (isoR_toSpec hϖ b₄ b₆)).trans
      (congrArg (Q.D.e.inv ≫ ·) a.ψ_toSpec)
  exact hC K O Q.D.K' (K' ϖ) Q.D.O' (O' ϖ) Q.D.hO' (comap_OE O (K' ϖ)) Q.D.ϖ' (sO ϖ) Q.D.hϖ'
    (irreducible_sqrt hϖ) Q.D.L₁ _ Q.D.xL Q.D.c' (c₂ hϖ b₄ b₆) (Q.isoψ (eR hϖ b₄ b₆ heqR A) a)
    Q.D.j₁ _ Q.D.wmodel (Q.genericR hϖ b₄ b₆ heqR a hx) hto Q.D.split Q.D.noLoops
    (isDominant_genericPt (O := O' ϖ) _).denseRange y' w₁' w₂' hw₁ hw₂ hne hy₁ hy₂ hG v hv hψv

/-- **`HarmonicTateR` from `CrossingX1S`** when `b₆` is a unit: the special fibre of the
restricted Tate model is the 2-gon `C ∪ E'` with nodes `p`, `q`. -/
theorem harmonicTateR_of_crossingX1 (hC : SemistableReduction.Statement.CrossingX1S.{u})
    (hb : IsUnit b₆) (hx : Transcendental K x) (a : Q.U ⟶ X₀' hϖ b₄ b₆ R heqR A) :
    Q.HarmonicTateR hϖ b₄ b₆ R heqR A {(decompR hϖ b₄ b₆).E} a := by
  have hZ : ∀ y, y ∈ specialFibre (X₀' hϖ b₄ b₆ R heqR A).Lv.c.toSpec ↔
      (eR hϖ b₄ b₆ heqR A).hom y ∈ SemistableReduction.ModelCode.Z (c₂ hϖ b₄ b₆) :=
    mem_Z_isoR hϖ b₄ b₆
  obtain ⟨zC, hCcl, hCE⟩ := exists_closure_eq_C hϖ b₄ b₆
  obtain ⟨zE, hEcl, hEC⟩ := exists_closure_eq_E hϖ b₄ b₆ hb
  have hCc : (decompR hϖ b₄ b₆).C ∈
      irreducibleComponents (X₀' hϖ b₄ b₆ R heqR A).Lv.Z := hCcl ▸
    TateObject.closure_mem_irreducibleComponents (decompR hϖ b₄ b₆).isClosed_E
      (hCcl ▸ (decompR hϖ b₄ b₆).union) hCE
  have hEc : (decompR hϖ b₄ b₆).E ∈
      irreducibleComponents (X₀' hϖ b₄ b₆ R heqR A).Lv.Z := hEcl ▸
    TateObject.closure_mem_irreducibleComponents (decompR hϖ b₄ b₆).isClosed_C
      (hEcl ▸ (Set.union_comm _ _).trans (decompR hϖ b₄ b₆).union) hEC
  have hne : (decompR hϖ b₄ b₆).C ≠ (decompR hϖ b₄ b₆).E := fun h ↦
    hCE (h ▸ hCcl ▸ subset_closure rfl)
  obtain ⟨p, hp⟩ := nonempty_Cp hϖ b₄ b₆
  obtain ⟨q, hq⟩ := nonempty_Cq hϖ b₄ b₆
  have hpCE := (decompR hϖ b₄ b₆).Cp_subset_inter hp
  have hqCE : q ∈ (decompR hϖ b₄ b₆).C ∩ (decompR hϖ b₄ b₆).E := by
    rw [(decompR hϖ b₄ b₆).inter]; exact Or.inr hq
  have hGp := nodeGermAt_of_mem_Cp hϖ b₄ b₆ hp
  have hGq := nodeGermAt_of_mem_Cq hϖ b₄ b₆ hq
  refine ⟨fun i hi ↦ ?_, fun i hi ↦ ?_⟩
  · obtain ⟨w, hw0, hcross, hlast⟩ := Q.crossing_R hϖ b₄ b₆ heqR hC hx a
      (isoPt (eR hϖ b₄ b₆ heqR A) p) (isoSet (eR hϖ b₄ b₆ heqR A) (decompR hϖ b₄ b₆).C)
      (isoSet (eR hϖ b₄ b₆ heqR A) (decompR hϖ b₄ b₆).E) (isoSet_mem _ hZ hCc) (isoSet_mem _ hZ hEc)
      ((isoSet_injective _).ne hne) ⟨p, hpCE.1, rfl⟩ ⟨p, hpCE.2, rfl⟩ hGp (Q.D.compSet i.1)
      (Q.D.compSet_mem i.2) (by rw [Q.isoψ_image_compSet]; exact congrArg _ hi)
    obtain ⟨L, hL, hpL, hlastL⟩ := Q.exists_incWalk_of_crossesG _ a w i hw0 hcross
    refine ⟨L, hL, fun r hr ↦ ?_, ?_⟩
    · rw [isoPt_injective _ (hpL r hr)]
      exact hp
    · rw [hlast] at hlastL
      exact (isoSet_injective _ hlastL).symm
  · obtain ⟨w, hw0, hcross, hlast⟩ := Q.crossing_R hϖ b₄ b₆ heqR hC hx a
      (isoPt (eR hϖ b₄ b₆ heqR A) q) (isoSet (eR hϖ b₄ b₆ heqR A) (decompR hϖ b₄ b₆).E)
      (isoSet (eR hϖ b₄ b₆ heqR A) (decompR hϖ b₄ b₆).C) (isoSet_mem _ hZ hEc) (isoSet_mem _ hZ hCc)
      ((isoSet_injective _).ne hne.symm) ⟨q, hqCE.2, rfl⟩ ⟨q, hqCE.1, rfl⟩ hGq (Q.D.compSet i.1)
      (Q.D.compSet_mem i.2) (by rw [Q.isoψ_image_compSet]; exact congrArg _ hi)
    obtain ⟨L, hL, hpL, hlastL⟩ := Q.exists_incWalk_of_crossesG _ a w i hw0 hcross
    refine ⟨L, hL, fun r hr ↦ ?_, ?_⟩
    · rw [isoPt_injective _ (hpL r hr)]
      exact fun h ↦ Set.disjoint_left.1 (decompR hϖ b₄ b₆).disjoint h hq
    · rw [hlast] at hlastL
      exact (isoSet_injective _ hlastL).symm

end Pres

end

end TemperedFundamentalGroups
