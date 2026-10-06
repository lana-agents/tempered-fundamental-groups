/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Local
import TemperedFundamentalGroups.SemistableReduction.W10Sigma

/-!
# Locally dominated morphisms of disjoint unions of projective model codes

Blueprint §9.7a (W10 assembly). The versions of `homSigma` (W10Sigma) built from local domination
(`homOfLocalProj`, W10Local), with possibly different base rings and semilinear field maps:

* `homSigmaLocal`: the summand `l` of the source union (over `O₂`) is mapped to the summand `π l` of
  the target union (over `O₁`) by `homOfLocalProj (φ l)`; compatible with the generic points
  (`genericPtSigma_comp_homSigmaLocal`) and lying over `Spec τ` (`homSigmaLocal_toSpec`).
* `jSigma`: for subrings `D k ⊆ F k` locally dominating the charts, a morphism
  `Spec (∏ D k) ⟶ projSigma`, restricting to the generic point (`SpecMap_comp_jSigma`); it is
  scheme-theoretically dominant (`isSchemeTheoreticallyDominant_jSigma`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace SemistableReduction

open TemperedFundamentalGroups ProjScheme

section HomSigmaLocal

variable {O₁ O₂ : Type u} [CommRing O₁] [CommRing O₂] {ι κ : Type u} [Fintype ι] [Fintype κ]
  {F : ι → Type u} [∀ k, Field (F k)] [∀ k, Algebra O₁ (F k)] {m : ι → ℕ}
  {f : ∀ k, Fin (m k + 1) → F k} (hf : ∀ k i, f k i ≠ 0)
  {F' : κ → Type u} [∀ l, Field (F' l)] [∀ l, Algebra O₂ (F' l)]
  {n : κ → ℕ} {g : ∀ l, Fin (n l + 1) → F' l} (hg : ∀ l j, g l j ≠ 0)
  (π : κ → ι) (φ : ∀ l, F (π l) →+* F' l)
  (hloc : ∀ l j, LocallyDominates (algebraMap O₁ (F (π l))).range (φ l)
    (projChart (algebraMap O₂ (F' l)).range (g l) j).subtype (f (π l)))

/-- **Componentwise locally dominated morphisms of disjoint unions.** -/
noncomputable def homSigmaLocal : (projSigma O₂ hg).scheme ⟶ (projSigma O₁ hf).scheme :=
  (ModelCode.sigmaIso fun l ↦ projModelCode O₂ (hg l)).inv ≫ Sigma.desc fun l ↦
    homOfLocalProj (R₁ := (algebraMap O₁ (F (π l))).range) (R₂ := (algebraMap O₂ (F' l)).range)
      rfl rfl (hf (π l)) (hg l) (φ l) (hloc l) ≫
      ModelCode.sigmaι (fun k ↦ projModelCode O₁ (hf k)) (π l)

theorem sigmaι_homSigmaLocal (l : κ) :
    ModelCode.sigmaι (fun l ↦ projModelCode O₂ (hg l)) l ≫ homSigmaLocal hf hg π φ hloc =
      homOfLocalProj (R₁ := (algebraMap O₁ (F (π l))).range)
        (R₂ := (algebraMap O₂ (F' l)).range) rfl rfl (hf (π l)) (hg l) (φ l) (hloc l) ≫
        ModelCode.sigmaι (fun k ↦ projModelCode O₁ (hf k)) (π l) := by
  rw [ModelCode.sigmaι, homSigmaLocal, Category.assoc, Iso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ l

/-- Compatibility with the generic points. -/
theorem genericPtSigma_comp_homSigmaLocal :
    genericPtSigma O₂ hg ≫ homSigmaLocal hf hg π φ hloc =
      Spec.map (CommRingCat.ofHom (sigmaRingHom π φ)) ≫ genericPtSigma O₁ hf := by
  rw [← cancel_epi (sigmaSpec fun l ↦ CommRingCat.of (F' l))]
  refine Sigma.hom_ext _ _ fun l ↦ ?_
  rw [ι_sigmaSpec_assoc, ι_sigmaSpec_assoc, reassoc_of% SpecMap_eval_genericPtSigma,
    sigmaι_homSigmaLocal, reassoc_of% genericPt_comp_homOfLocalProj, ← Spec.map_comp_assoc,
    ← SpecMap_eval_genericPtSigma, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- The morphism lies over `Spec O₂ ⟶ Spec O₁` when the `φ l` lie over `τ : O₁ → O₂`. -/
theorem homSigmaLocal_toSpec (τ : O₁ →+* O₂)
    (hτ : ∀ l, (φ l).comp (algebraMap O₁ (F (π l))) = (algebraMap O₂ (F' l)).comp τ) :
    homSigmaLocal hf hg π φ hloc ≫ (projSigma O₁ hf).toSpec =
      (projSigma O₂ hg).toSpec ≫ Spec.map (CommRingCat.ofHom τ) := by
  refine ModelCode.sigma_hom_ext _ fun l ↦ ?_
  rw [reassoc_of% sigmaι_homSigmaLocal, ModelCode.sigmaι_toSpec,
    reassoc_of% ModelCode.sigmaι_toSpec,
    homOfLocalProj_toSpec _ _ _ _ _ _ τ (hτ l)]

end HomSigmaLocal

section JSigma

variable {O : Type u} [CommRing O] {ι : Type u} [Fintype ι] {F : ι → Type u}
  [∀ k, Field (F k)] [∀ k, Algebra O (F k)] {m : ι → ℕ} {f : ∀ k, Fin (m k + 1) → F k}
  (hf : ∀ k i, f k i ≠ 0) (D : ∀ k, Subring (F k))
  (hD : ∀ k, LocallyDominates (algebraMap O (F k)).range (RingHom.id (F k)) (D k).subtype (f k))

/-- The inclusion `∏ D k → ∏ F k`. -/
def piSubtype : (Π k, D k) →+* (Π k, F k) :=
  RingHom.pi fun k ↦ (D k).subtype.comp (Pi.evalRingHom (fun k ↦ D k) k)

/-- **The morphism `Spec (∏ D k) ⟶ projSigma`** from local domination of the charts. -/
noncomputable def jSigma : Spec (CommRingCat.of (Π k, D k)) ⟶ (projSigma O hf).scheme :=
  inv (sigmaSpec fun k ↦ CommRingCat.of (D k)) ≫
    Limits.Sigma.map (fun k ↦ homOfLocal (R₁ := (algebraMap O (F k)).range) (RingHom.id (F k))
      Subtype.val_injective rfl (hf k) (hD k)) ≫
    (ModelCode.sigmaIso fun k ↦ projModelCode O (hf k)).hom

theorem SpecMap_eval_jSigma (k : ι) :
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun k ↦ D k) k)) ≫ jSigma hf D hD =
      homOfLocal (R₁ := (algebraMap O (F k)).range) (RingHom.id (F k))
        Subtype.val_injective rfl (hf k) (hD k) ≫
        ModelCode.sigmaι (fun k ↦ projModelCode O (hf k)) k := by
  rw [← ι_sigmaSpec (fun k ↦ CommRingCat.of (D k)) k, jSigma, Category.assoc,
    IsIso.hom_inv_id_assoc, Limits.Sigma.ι_map_assoc]
  rfl

/-- `jSigma` restricts to the generic point. -/
theorem SpecMap_comp_jSigma :
    Spec.map (CommRingCat.ofHom (piSubtype D)) ≫ jSigma hf D hD = genericPtSigma O hf := by
  rw [← cancel_epi (sigmaSpec fun k ↦ CommRingCat.of (F k))]
  refine Sigma.hom_ext _ _ fun k ↦ ?_
  rw [ι_sigmaSpec_assoc, ι_sigmaSpec_assoc, SpecMap_eval_genericPtSigma, ← Spec.map_comp_assoc]
  have : CommRingCat.ofHom (piSubtype D) ≫ CommRingCat.ofHom (Pi.evalRingHom F k) =
      CommRingCat.ofHom (Pi.evalRingHom (fun k ↦ D k) k) ≫ CommRingCat.ofHom (D k).subtype := rfl
  rw [this, Spec.map_comp, Category.assoc, SpecMap_eval_jSigma, ← Category.assoc,
    SpecMap_comp_homOfLocal]
  simp only [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]

instance isSchemeTheoreticallyDominant_jSigma : IsSchemeTheoreticallyDominant (jSigma hf D hD) := by
  have : IsDominant (Spec.map (CommRingCat.ofHom (piSubtype D)) ≫ jSigma hf D hD) := by
    rw [SpecMap_comp_jSigma]; infer_instance
  have : IsDominant (jSigma hf D hD) :=
    IsDominant.of_comp (Spec.map (CommRingCat.ofHom (piSubtype D))) (jSigma hf D hD)
  exact .of_isDominant _

/-- `jSigma` lies over `Spec O`. -/
theorem jSigma_toSpec (τ : O →+* Π k, D k)
    (hτ : (piSubtype D).comp τ = algebraMap O (Π k, F k)) :
    jSigma hf D hD ≫ (projSigma O hf).toSpec = Spec.map (CommRingCat.ofHom τ) := by
  rw [← cancel_epi (sigmaSpec fun k ↦ CommRingCat.of (D k))]
  refine Sigma.hom_ext _ _ fun k ↦ ?_
  rw [ι_sigmaSpec_assoc, ι_sigmaSpec_assoc, reassoc_of% SpecMap_eval_jSigma,
    ModelCode.sigmaι_toSpec, ← Spec.map_comp]
  refine homOfLocal_toSpec _ _ _ _ _ _ ?_
  ext o
  have := congrFun (congrArg DFunLike.coe hτ) o
  have := congrFun this k
  exact this

end JSigma

section SigmaIso

variable {O O' : Type u} [CommRing O] [CommRing O'] {ι : Type u} [Fintype ι]
  (c : ι → TemperedFundamentalGroups.ModelCode O) (c' : ι → TemperedFundamentalGroups.ModelCode O')
  (e : ∀ k, (c k).scheme ≅ (c' k).scheme)

/-- Componentwise isomorphisms of disjoint unions. -/
noncomputable def sigmaIsoOfIso : (ModelCode.sigma c).scheme ≅ (ModelCode.sigma c').scheme where
  hom := (ModelCode.sigmaIso c).inv ≫
    Limits.Sigma.desc fun k ↦ (e k).hom ≫ ModelCode.sigmaι c' k
  inv := (ModelCode.sigmaIso c').inv ≫
    Limits.Sigma.desc fun k ↦ (e k).inv ≫ ModelCode.sigmaι c k
  hom_inv_id := by
    refine ModelCode.sigma_hom_ext _ fun k ↦ ?_
    simp only [ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc, Limits.Sigma.ι_desc_assoc,
      Limits.Sigma.ι_desc, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    refine ModelCode.sigma_hom_ext _ fun k ↦ ?_
    simp only [ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc, Limits.Sigma.ι_desc_assoc,
      Limits.Sigma.ι_desc, Iso.inv_hom_id_assoc, Category.comp_id]

theorem sigmaι_sigmaIsoOfIso (k : ι) :
    ModelCode.sigmaι c k ≫ (sigmaIsoOfIso c c' e).hom = (e k).hom ≫ ModelCode.sigmaι c' k := by
  simp only [sigmaIsoOfIso, ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc,
    Limits.Sigma.ι_desc]

theorem sigmaι_sigmaIsoOfIso_inv (k : ι) :
    ModelCode.sigmaι c' k ≫ (sigmaIsoOfIso c c' e).inv = (e k).inv ≫ ModelCode.sigmaι c k := by
  simp only [sigmaIsoOfIso, ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc,
    Limits.Sigma.ι_desc]

end SigmaIso

end SemistableReduction
