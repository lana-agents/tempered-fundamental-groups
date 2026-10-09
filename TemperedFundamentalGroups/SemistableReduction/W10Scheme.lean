/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjScheme

/-!
# Morphisms of projective model codes from Zariski domination

Blueprint §9.7 (W10 assembly, scheme realization). For a ring `O`, a field `F` over `O` and a
family `f : Fin (m + 1) → F` of nonzero functions, `projModelCode O hf` is the scheme-theoretic
image of the generic point `toProj O hf : Spec F ⟶ ℙᵐ_O` (M9b, `ProjScheme.lean`).

* `ProjScheme.chartCover`: the charts `Spec R[f j / f i] ⟶` (model) form an open cover; the model
  is reduced (`isReduced_projModelCode`) and separated (`modelCode_scheme_isSeparated`).
* **(6)** `genericPt O hf := (toProj O hf).toImage : Spec F ⟶` (model) is scheme-theoretically
  dominant (`isSchemeTheoreticallyDominant_toImage`, `isSchemeTheoreticallyDominant_genericPt`;
  after composing with an isomorphism: `isSchemeTheoreticallyDominant_genericPt_comp`).
* `hom_ext_genericPt`: morphisms out of the model into a separated scheme are determined by their
  restriction to the generic point.
* **(4)** `homOfDominates`: for a ring map `φ : F₁ → F₂` such that every chart of `g` contains the
  `φ`-image of some chart of `f` (`Dominates`, Zariski domination), a morphism
  `projModelCode O₂ hg ⟶ projModelCode O₁ hf` with `genericPt ≫ ψ = Spec φ ≫ genericPt`
  (`genericPt_comp_homOfDominates`, unique: `eq_homOfDominates`), over `Spec O₂ ⟶ Spec O₁`
  (`homOfDominates_toSpec`, `homOfDominates_toSpec_self`); functorial (`homOfDominates_comp`,
  `homOfDominates_id`). Isomorphisms `isoOfDominates` for ring isomorphisms dominating in both
  directions; actions `actOfDominates : H →* Aut` of groups acting on `F` by chart-preserving
  automorphisms, with the generic point equivariant (`genericPt_comp_actOfDominates`) and over
  `Spec O` (`actOfDominates_toSpec`).
* **(3a)** `baseChangeIso`: for `O → O'` with image `R' = R[θ]` in `F` (`θ ≠ 0` integral over `O`),
  the projective `O'`-model of `g` is isomorphic to the projective `O`-model of
  `thetaFamily θ g = (g, θ g)`, compatibly with the generic points and over `Spec O`.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace SemistableReduction

open TemperedFundamentalGroups ProjScheme

/-- The scheme of a model code is separated. -/
instance modelCode_scheme_isSeparated {O : Type u} [CommRing O]
    (c : TemperedFundamentalGroups.ModelCode O) : c.scheme.IsSeparated :=
  ⟨by rw [← terminal.comp_from c.toSpec]; infer_instance⟩

namespace ProjScheme

section Single

variable {O : Type u} [CommRing O] {F : Type u} [Field F] [Algebra O F] {m : ℕ}
  {f : Fin (m + 1) → F}

instance quasiCompact_toProj (hf : ∀ i, f i ≠ 0) : QuasiCompact (toProj O hf) := by
  have : QuasiCompact (toProj O hf ≫ projSpace.toSpec O m) := by
    rw [toProj_toSpec]; infer_instance
  exact QuasiCompact.of_comp _ (projSpace.toSpec O m)

variable (R : Subring F)

/-- The charts `Spec R[f j / f i] ⟶` (projective model) as an open cover. -/
noncomputable def chartCover (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0) :
    (projModelCode O hf).scheme.OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (m + 1)) (fun i ↦ Spec (CommRingCat.of (projChart R f i)))
    (chartι R hR hf) (fun x ↦ by
      obtain ⟨i, hi⟩ := exists_mem_chartOpen hf x
      rw [← opensRange_chartι R hR hf i] at hi
      obtain ⟨y, hy⟩ := hi
      exact ⟨i, y, hy⟩)

lemma chartCover_f (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    (chartCover R hR hf).f i = chartι R hR hf i := rfl

/-- The projective model is reduced (it is covered by spectra of subrings of `F`). -/
instance isReduced_projModelCode (hf : ∀ i, f i ≠ 0) : IsReduced (projModelCode O hf).scheme :=
  have (i : Fin (m + 1)) : IsReduced ((chartCover _ rfl hf).X i) := by
    change IsReduced (Spec (CommRingCat.of (projChart (algebraMap O F).range f i)))
    infer_instance
  IsReduced.of_openCover (𝒰 := chartCover _ rfl hf)

instance isReduced_image_toProj (hf : ∀ i, f i ≠ 0) : IsReduced (toProj O hf).image :=
  isReduced_projModelCode (O := O) hf

instance isDominant_toImage (hf : ∀ i, f i ≠ 0) : IsDominant (toProj O hf).toImage := by
  infer_instance

variable (O) in
/-- The generic point `Spec F ⟶` (projective model), i.e. `(toProj O hf).toImage`, typed with the
model code as target. -/
noncomputable def genericPt (hf : ∀ i, f i ≠ 0) :
    Spec (CommRingCat.of F) ⟶ (projModelCode O hf).scheme :=
  (toProj O hf).toImage

lemma genericPt_eq_chartι (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
    (i : Fin (m + 1)) :
    genericPt O hf = Spec.map (CommRingCat.ofHom (projChart R f i).subtype) ≫ chartι R hR hf i :=
  toImage_eq_SpecMap_comp_chartι R hR hf i

lemma genericPt_toSpec (hf : ∀ i, f i ≠ 0) :
    genericPt O hf ≫ (projModelCode O hf).toSpec = Spec.map (CommRingCat.ofHom (algebraMap O F)) :=
  toImage_toSpec hf

/-- **(6) The generic point of the projective model is scheme-theoretically dominant.** -/
instance isSchemeTheoreticallyDominant_toImage (hf : ∀ i, f i ≠ 0) :
    IsSchemeTheoreticallyDominant (toProj O hf).toImage :=
  have := isDominant_toImage (O := O) hf
  have := isReduced_image_toProj (O := O) hf
  .of_isDominant (toProj O hf).toImage

instance isSchemeTheoreticallyDominant_genericPt (hf : ∀ i, f i ≠ 0) :
    IsSchemeTheoreticallyDominant (genericPt O hf) :=
  isSchemeTheoreticallyDominant_toImage hf

instance isDominant_genericPt (hf : ∀ i, f i ≠ 0) : IsDominant (genericPt O hf) :=
  isDominant_toImage hf

/-- **(6)**, after composing with an isomorphism. -/
theorem isSchemeTheoreticallyDominant_genericPt_comp (hf : ∀ i, f i ≠ 0) {Y : Scheme.{u}}
    (e : (projModelCode O hf).scheme ≅ Y) :
    IsSchemeTheoreticallyDominant (genericPt O hf ≫ e.hom) :=
  inferInstance

/-- Morphisms out of the projective model into a separated scheme are determined on the generic
point. -/
theorem hom_ext_genericPt (hf : ∀ i, f i ≠ 0) {Y : Scheme.{u}} [Y.IsSeparated]
    {a b : (projModelCode O hf).scheme ⟶ Y}
    (h : genericPt O hf ≫ a = genericPt O hf ≫ b) : a = b :=
  ext_of_isDominant (genericPt O hf) h

end Single

section Dominate

variable {O₁ O₂ : Type u} [CommRing O₁] [CommRing O₂] {F₁ F₂ : Type u} [Field F₁] [Field F₂]
  [Algebra O₁ F₁] [Algebra O₂ F₂] {m n : ℕ} {f : Fin (m + 1) → F₁} {g : Fin (n + 1) → F₂}
  (R₁ : Subring F₁) (R₂ : Subring F₂)

/-- **Zariski domination**: every chart `R₂[g l / g j]` contains the `φ`-image of some chart
`R₁[f k / f i]`. -/
def Dominates (φ : F₁ →+* F₂) (f : Fin (m + 1) → F₁) (g : Fin (n + 1) → F₂) : Prop :=
  ∀ j, ∃ i, ∀ x ∈ projChart R₁ f i, φ x ∈ projChart R₂ g j

/-- Domination can be checked on generators: the chart `R₂[g / g j]` contains `φ(R₁)` and the
`φ (f k / f i)`. -/
lemma dominates_of_forall {φ : F₁ →+* F₂} (hR : ∀ x ∈ R₁, φ x ∈ R₂)
    (h : ∀ j, ∃ i, ∀ k, φ (f k / f i) ∈ projChart R₂ g j) : Dominates R₁ R₂ φ f g := by
  intro j
  obtain ⟨i, hi⟩ := h j
  refine ⟨i, fun x hx ↦ ?_⟩
  have : projChart R₁ f i ≤ (projChart R₂ g j).comap φ :=
    projChart_le (fun y hy ↦ base_le_projChart j (hR y hy)) hi
  exact this hx

variable {R₁ R₂}

/-- The ring map between charts induced by a domination. -/
noncomputable def chartMap (φ : F₁ →+* F₂) {i : Fin (m + 1)} {j : Fin (n + 1)}
    (h : ∀ x ∈ projChart R₁ f i, φ x ∈ projChart R₂ g j) :
    projChart R₁ f i →+* projChart R₂ g j :=
  (φ.comp (projChart R₁ f i).subtype).codRestrict _ fun x ↦ h x x.2

variable (hR₁ : (algebraMap O₁ F₁).range = R₁) (hR₂ : (algebraMap O₂ F₂).range = R₂)
  (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0) (φ : F₁ →+* F₂)

/-- The morphism on the chart `Spec R₂[g / g j]`. -/
noncomputable def localHom {i : Fin (m + 1)} {j : Fin (n + 1)}
    (h : ∀ x ∈ projChart R₁ f i, φ x ∈ projChart R₂ g j) :
    Spec (CommRingCat.of (projChart R₂ g j)) ⟶ (projModelCode O₁ hf).scheme :=
  Spec.map (CommRingCat.ofHom (chartMap φ h)) ≫ chartι R₁ hR₁ hf i

lemma SpecMap_subtype_localHom {i : Fin (m + 1)} {j : Fin (n + 1)}
    (h : ∀ x ∈ projChart R₁ f i, φ x ∈ projChart R₂ g j) :
    Spec.map (CommRingCat.ofHom (projChart R₂ g j).subtype) ≫ localHom hR₁ hf φ h =
      Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf := by
  rw [genericPt_eq_chartι R₁ hR₁ hf i, localHom, ← Category.assoc, ← Category.assoc,
    ← Spec.map_comp, ← Spec.map_comp]
  rfl

lemma localHom_compat (hφ : Dominates R₁ R₂ φ f g) (j j' : Fin (n + 1)) :
    pullback.fst (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j') ≫
        localHom hR₁ hf φ (hφ j).choose_spec =
      pullback.snd (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j') ≫
        localHom hR₁ hf φ (hφ j').choose_spec := by
  have : IsReduced (pullback (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j')) :=
    isReduced_of_isOpenImmersion (pullback.fst _ _)
  let ι := pullback.lift (f := chartι R₂ hR₂ hg j) (g := chartι R₂ hR₂ hg j')
    (Spec.map (CommRingCat.ofHom (projChart R₂ g j).subtype))
    (Spec.map (CommRingCat.ofHom (projChart R₂ g j').subtype))
    (by rw [← genericPt_eq_chartι, ← genericPt_eq_chartι])
  have : IsDominant (ι ≫ pullback.fst _ _ ≫ chartι R₂ hR₂ hg j) := by
    rw [pullback.lift_fst_assoc, ← genericPt_eq_chartι]
    infer_instance
  have : IsDominant ι :=
    IsDominant.of_comp_of_isOpenImmersion ι (pullback.fst _ _ ≫ chartι R₂ hR₂ hg j)
  refine ext_of_isDominant ι ?_
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, SpecMap_subtype_localHom,
    SpecMap_subtype_localHom]

/-- **(4) Zariski domination gives a morphism of projective model codes**: the charts are mapped
by `Spec` of the inclusions `φ (R₁[f / f i]) ⊆ R₂[g / g j]`, glued along the open cover. -/
noncomputable def homOfDominates (hφ : Dominates R₁ R₂ φ f g) :
    (projModelCode O₂ hg).scheme ⟶ (projModelCode O₁ hf).scheme :=
  (chartCover R₂ hR₂ hg).glueMorphisms (fun j ↦ localHom hR₁ hf φ (hφ j).choose_spec)
    (localHom_compat hR₁ hR₂ hf hg φ hφ)

lemma chartι_homOfDominates (hφ : Dominates R₁ R₂ φ f g) (j : Fin (n + 1)) :
    chartι R₂ hR₂ hg j ≫ homOfDominates hR₁ hR₂ hf hg φ hφ =
      localHom hR₁ hf φ (hφ j).choose_spec :=
  Scheme.Cover.ι_glueMorphisms (chartCover R₂ hR₂ hg) _ _ j

/-- **(4)** The morphism is compatible with the generic points. -/
theorem genericPt_comp_homOfDominates (hφ : Dominates R₁ R₂ φ f g) :
    genericPt O₂ hg ≫ homOfDominates hR₁ hR₂ hf hg φ hφ =
      Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf := by
  rw [genericPt_eq_chartι R₂ hR₂ hg 0, Category.assoc, chartι_homOfDominates,
    SpecMap_subtype_localHom]

/-- **(4)** Uniqueness: a morphism compatible with the generic points is `homOfDominates`. -/
theorem eq_homOfDominates (hφ : Dominates R₁ R₂ φ f g)
    {ψ : (projModelCode O₂ hg).scheme ⟶ (projModelCode O₁ hf).scheme}
    (hψ : genericPt O₂ hg ≫ ψ = Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf) :
    ψ = homOfDominates hR₁ hR₂ hf hg φ hφ :=
  hom_ext_genericPt hg (hψ.trans (genericPt_comp_homOfDominates hR₁ hR₂ hf hg φ hφ).symm)

/-- **(4)** The morphism lies over `Spec O₂ ⟶ Spec O₁` when `φ` lies over `τ : O₁ → O₂`. -/
theorem homOfDominates_toSpec (hφ : Dominates R₁ R₂ φ f g) (τ : O₁ →+* O₂)
    (hτ : φ.comp (algebraMap O₁ F₁) = (algebraMap O₂ F₂).comp τ) :
    homOfDominates hR₁ hR₂ hf hg φ hφ ≫ (projModelCode O₁ hf).toSpec =
      (projModelCode O₂ hg).toSpec ≫ Spec.map (CommRingCat.ofHom τ) := by
  refine hom_ext_genericPt hg ?_
  rw [reassoc_of% genericPt_comp_homOfDominates, genericPt_toSpec, reassoc_of% genericPt_toSpec,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hτ]

/-- **(4)** over a common base ring. -/
theorem homOfDominates_toSpec_self {O : Type u} [CommRing O] [Algebra O F₁] [Algebra O F₂]
    {R₁ : Subring F₁} {R₂ : Subring F₂}
    (hR₁ : (algebraMap O F₁).range = R₁) (hR₂ : (algebraMap O F₂).range = R₂)
    (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0) (φ : F₁ →+* F₂) (hφ : Dominates R₁ R₂ φ f g)
    (hτ : φ.comp (algebraMap O F₁) = algebraMap O F₂) :
    homOfDominates hR₁ hR₂ hf hg φ hφ ≫ (projModelCode O hf).toSpec =
      (projModelCode O hg).toSpec := by
  rw [homOfDominates_toSpec hR₁ hR₂ hf hg φ hφ (RingHom.id O) (by rw [hτ]; rfl)]
  simp

omit [Algebra O₁ F₁] [Algebra O₂ F₂] in
lemma Dominates.comp {F₃ : Type u} [Field F₃] {R₃ : Subring F₃} {k : ℕ} {h : Fin (k + 1) → F₃}
    {φ₁ : F₁ →+* F₂} {φ₂ : F₂ →+* F₃} (h₁ : Dominates R₁ R₂ φ₁ f g)
    (h₂ : Dominates R₂ R₃ φ₂ g h) : Dominates R₁ R₃ (φ₂.comp φ₁) f h := by
  intro l
  obtain ⟨j, hj⟩ := h₂ l
  obtain ⟨i, hi⟩ := h₁ j
  exact ⟨i, fun x hx ↦ hj _ (hi x hx)⟩

omit [Field F₂] [Algebra O₁ F₁] in
lemma dominates_id : Dominates R₁ R₁ (RingHom.id F₁) f f :=
  fun j ↦ ⟨j, fun _ hx ↦ hx⟩

/-- **Functoriality** of `homOfDominates`. -/
theorem homOfDominates_comp {O₃ F₃ : Type u} [CommRing O₃] [Field F₃] [Algebra O₃ F₃]
    {R₃ : Subring F₃} {k : ℕ} {h : Fin (k + 1) → F₃} (hR₃ : (algebraMap O₃ F₃).range = R₃)
    (hh : ∀ l, h l ≠ 0) {φ₁ : F₁ →+* F₂} {φ₂ : F₂ →+* F₃} (h₁ : Dominates R₁ R₂ φ₁ f g)
    (h₂ : Dominates R₂ R₃ φ₂ g h) :
    homOfDominates hR₂ hR₃ hg hh φ₂ h₂ ≫ homOfDominates hR₁ hR₂ hf hg φ₁ h₁ =
      homOfDominates hR₁ hR₃ hf hh (φ₂.comp φ₁) (h₁.comp h₂) := by
  refine eq_homOfDominates _ _ _ _ _ _ ?_
  rw [reassoc_of% genericPt_comp_homOfDominates, genericPt_comp_homOfDominates, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem homOfDominates_id : homOfDominates hR₁ hR₁ hf hf (RingHom.id F₁) dominates_id = 𝟙 _ :=
  (eq_homOfDominates _ _ _ _ _ _ (by simp)).symm

/-- **Isomorphisms from two-sided Zariski domination**: a ring isomorphism `φ : F₁ ≃ F₂`
dominating in both directions gives an isomorphism of projective model codes compatible with the
generic points. -/
noncomputable def isoOfDominates (φ : F₁ ≃+* F₂) (h₁ : Dominates R₁ R₂ φ.toRingHom f g)
    (h₂ : Dominates R₂ R₁ φ.symm.toRingHom g f) :
    (projModelCode O₂ hg).scheme ≅ (projModelCode O₁ hf).scheme where
  hom := homOfDominates hR₁ hR₂ hf hg φ.toRingHom h₁
  inv := homOfDominates hR₂ hR₁ hg hf φ.symm.toRingHom h₂
  hom_inv_id := by
    rw [homOfDominates_comp, ← homOfDominates_id hR₂ hg]
    congr 1
    ext x
    simp
  inv_hom_id := by
    rw [homOfDominates_comp, ← homOfDominates_id hR₁ hf]
    congr 1
    ext x
    simp

lemma isoOfDominates_hom (φ : F₁ ≃+* F₂) (h₁ : Dominates R₁ R₂ φ.toRingHom f g)
    (h₂ : Dominates R₂ R₁ φ.symm.toRingHom g f) :
    (isoOfDominates hR₁ hR₂ hf hg φ h₁ h₂).hom = homOfDominates hR₁ hR₂ hf hg φ.toRingHom h₁ :=
  rfl

end Dominate

section Action

variable {O : Type u} [CommRing O] {F : Type u} [Field F] [Algebra O F] {m : ℕ}
  {f : Fin (m + 1) → F} {R : Subring F} (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
  {H : Type*} [Group H] (ρ : H →* (F ≃+* F)) (hρ : ∀ h, Dominates R R (ρ h).toRingHom f f)

/-- **Actions on projective model codes**: a group acting on `F` by automorphisms which preserve
the Zariski model (every chart contains the image of a chart) acts on the projective model code;
`h` acts through `ρ h⁻¹` on functions, so that the generic point is equivariant
(`genericPt_comp_actOfDominates`). -/
noncomputable def actOfDominates : H →* Aut (projModelCode O hf).scheme :=
  MonoidHom.mk' (fun h ↦ isoOfDominates hR hR hf hf (ρ h⁻¹) (hρ h⁻¹)
      (by convert hρ h using 2; rw [map_inv]; rfl)) fun h₁ h₂ ↦ by
    ext1
    simp only [Aut.Aut_mul_def, Iso.trans_hom, isoOfDominates_hom]
    rw [homOfDominates_comp]
    congr 1
    ext x
    simp [mul_inv_rev]

theorem genericPt_comp_actOfDominates (h : H) :
    genericPt O hf ≫ (actOfDominates hR hf ρ hρ h).hom =
      Spec.map (CommRingCat.ofHom (ρ h⁻¹).toRingHom) ≫ genericPt O hf :=
  genericPt_comp_homOfDominates _ _ _ _ _ _

/-- The action is over `Spec O` when `ρ` acts by `O`-algebra automorphisms. -/
theorem actOfDominates_toSpec (hρO : ∀ h (o : O), ρ h (algebraMap O F o) = algebraMap O F o)
    (h : H) :
    (actOfDominates hR hf ρ hρ h).hom ≫ (projModelCode O hf).toSpec =
      (projModelCode O hf).toSpec :=
  homOfDominates_toSpec_self _ _ _ _ _ _ (RingHom.ext fun o ↦ hρO _ o)

end Action

section BaseChange

/-- An element integral over `O` whose inverse lies in a subring `A ⊇ im(O)` lies in `A`. -/
lemma mem_of_inv_mem_of_isIntegral {O F : Type*} [CommRing O] [Field F] [Algebra O F]
    {A : Subring F} (hA : ∀ o, algebraMap O F o ∈ A) {θ : F} (hθ : IsIntegral O θ)
    (h : θ⁻¹ ∈ A) : θ ∈ A := by
  rcases eq_or_ne θ 0 with rfl | h0
  · exact zero_mem _
  obtain ⟨p, hp, he⟩ := hθ
  set d := p.natDegree
  have hd : d ≠ 0 := by
    intro hd
    rw [Polynomial.Monic.natDegree_eq_zero hp] at hd
    simp [hd] at he
  rw [hp.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_finsetSum] at he
  simp only [Polynomial.eval₂_X_pow, Polynomial.eval₂_mul, Polynomial.eval₂_C] at he
  have hu : θ * θ⁻¹ = 1 := mul_inv_cancel₀ h0
  have key : θ = -∑ i ∈ Finset.range d, algebraMap O F (p.coeff i) * θ⁻¹ ^ (d - 1 - i) := by
    have hθd : θ = θ ^ d * θ⁻¹ ^ (d - 1) := by
      rw [← pow_sub_mul_pow θ (Nat.one_le_iff_ne_zero.2 hd), pow_one, mul_comm _ θ, mul_assoc,
        ← mul_pow, hu, one_pow, mul_one]
    calc θ = θ ^ d * θ⁻¹ ^ (d - 1) := hθd
      _ = (-∑ i ∈ Finset.range d, algebraMap O F (p.coeff i) * θ ^ i) * θ⁻¹ ^ (d - 1) := by
        rw [eq_neg_of_add_eq_zero_left he]
      _ = _ := by
        rw [neg_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun i hi ↦ ?_
        have hi : i ≤ d - 1 := by have := Finset.mem_range.1 hi; omega
        rw [mul_assoc, ← pow_sub_mul_pow θ⁻¹ hi, mul_comm (θ ^ i), mul_assoc, ← mul_pow,
          inv_mul_cancel₀ h0, one_pow, mul_one]
  rw [key]
  exact neg_mem (Subring.sum_mem _ fun i _ ↦ mul_mem (hA _) (pow_mem h _))

variable {n : ℕ}

/-- The family `g` together with `θ g`: over `O`, its charts contain `O[θ]`. -/
def thetaFamily {F : Type*} [Mul F] (θ : F) (g : Fin (n + 1) → F) : Fin (n + 1 + n + 1) → F :=
  fun k ↦ Fin.append (m := n + 1) (n := n + 1) g (fun k ↦ θ * g k) k

@[simp]
lemma thetaFamily_castAdd {F : Type*} [Mul F] (θ : F) (g : Fin (n + 1) → F) (k : Fin (n + 1)) :
    thetaFamily θ g (Fin.castAdd (n + 1) k) = g k :=
  Fin.append_left (m := n + 1) (n := n + 1) _ _ _

@[simp]
lemma thetaFamily_natAdd {F : Type*} [Mul F] (θ : F) (g : Fin (n + 1) → F) (k : Fin (n + 1)) :
    thetaFamily θ g (Fin.natAdd (n + 1) k) = θ * g k :=
  Fin.append_right (m := n + 1) (n := n + 1) _ _ _

lemma thetaFamily_ne_zero {F : Type*} [Field F] {θ : F} (hθ : θ ≠ 0) {g : Fin (n + 1) → F}
    (hg : ∀ j, g j ≠ 0) (k : Fin (n + 1 + n + 1)) : thetaFamily θ g k ≠ 0 := by
  refine Fin.addCases (motive := fun k : Fin ((n + 1) + (n + 1)) ↦ thetaFamily θ g k ≠ 0)
    (fun k ↦ ?_) (fun k ↦ ?_) k
  · rw [thetaFamily_castAdd]; exact hg k
  · rw [thetaFamily_natAdd]; exact mul_ne_zero hθ (hg k)

variable {O O' : Type u} [CommRing O] [CommRing O'] {F : Type u} [Field F] [Algebra O F]
  [Algebra O' F] {g : Fin (n + 1) → F} {R R' : Subring F} {θ : F}

omit [Algebra O F] [Algebra O' F] in
lemma dominates_thetaFamily (hθR' : θ ∈ R')
    (hRR' : R ≤ R') :
    Dominates R R' (RingHom.id F) (thetaFamily θ g) g := by
  refine dominates_of_forall _ _ (fun x hx ↦ hRR' hx) fun j ↦ ⟨Fin.castAdd (n + 1) j, fun k ↦ ?_⟩
  refine Fin.addCases (motive := fun k : Fin ((n + 1) + (n + 1)) ↦
    (RingHom.id F) (thetaFamily θ g k / thetaFamily θ g (Fin.castAdd (n + 1) j)) ∈
      projChart R' g j) (fun k ↦ ?_) (fun k ↦ ?_) k
  · simpa using div_mem_projChart j k
  · simp only [thetaFamily_castAdd, thetaFamily_natAdd, RingHom.id_apply, mul_div_assoc]
    exact mul_mem (base_le_projChart j hθR') (div_mem_projChart j k)

lemma thetaFamily_dominates (hR : (algebraMap O F).range = R) (hθ0 : θ ≠ 0)
    (hθ : IsIntegral O θ) (hg : ∀ j, g j ≠ 0) (hR' : R' ≤ Subring.closure (insert θ (R : Set F))) :
    Dominates R' R (RingHom.id F) g (thetaFamily θ g) := by
  have hθmem (j : Fin (n + 1 + n + 1)) : θ ∈ projChart R (thetaFamily θ g) j := by
    refine Fin.addCases (motive := fun j : Fin ((n + 1) + (n + 1)) ↦
      θ ∈ projChart R (thetaFamily θ g) j) (fun j ↦ ?_) (fun j ↦ ?_) j
    · have := div_mem_projChart (R := R) (f := thetaFamily θ g) (Fin.castAdd (n + 1) j)
        (Fin.natAdd (n + 1) j)
      rwa [thetaFamily_castAdd, thetaFamily_natAdd, mul_div_assoc, div_self (hg j),
        mul_one] at this
    · refine mem_of_inv_mem_of_isIntegral (O := O) (fun o ↦ base_le_projChart _
        (hR ▸ ⟨o, rfl⟩)) hθ ?_
      have := div_mem_projChart (R := R) (f := thetaFamily θ g) (Fin.natAdd (n + 1) j)
        (Fin.castAdd (n + 1) j)
      rwa [thetaFamily_castAdd, thetaFamily_natAdd, div_mul_cancel_right₀ (hg j)] at this
  have hbase (j : Fin (n + 1 + n + 1)) : ∀ x ∈ R', x ∈ projChart R (thetaFamily θ g) j :=
    fun x hx ↦ (Subring.closure_le.2 (Set.insert_subset (hθmem j) (base_le_projChart j)))
      (hR' hx)
  intro j
  refine Fin.addCases (motive := fun j : Fin ((n + 1) + (n + 1)) ↦ ∃ i, ∀ x ∈ projChart R' g i,
    (RingHom.id F) x ∈ projChart R (thetaFamily θ g) j) (fun j ↦ ⟨j, ?_⟩) (fun j ↦ ⟨j, ?_⟩) j
  · refine fun x hx ↦ (projChart_le (hbase _) fun k ↦ ?_) hx
    simpa using div_mem_projChart (R := R) (f := thetaFamily θ g) (Fin.castAdd (n + 1) j)
      (Fin.castAdd (n + 1) k)
  · refine fun x hx ↦ (projChart_le (hbase _) fun k ↦ ?_) hx
    have := div_mem_projChart (R := R) (f := thetaFamily θ g) (Fin.natAdd (n + 1) j)
      (Fin.natAdd (n + 1) k)
    rwa [thetaFamily_natAdd, thetaFamily_natAdd, mul_div_mul_left _ _ hθ0] at this

variable (hR : (algebraMap O F).range = R) (hR' : (algebraMap O' F).range = R') (hθ0 : θ ≠ 0)
  (hθ : IsIntegral O θ) (hθR' : θ ∈ R') (hR'le : R' ≤ Subring.closure (insert θ (R : Set F)))
  (hRR' : R ≤ R') (hg : ∀ j, g j ≠ 0)

/-- **(3a) Base change.** If `O' ⊇ O` is generated by `θ` (integral over `O`, `θ ≠ 0`; images
`R' = R[θ]` in `F`), the projective `O'`-model of `g` is isomorphic to the projective `O`-model of
`(g, θ g)`, compatibly with the generic points (`genericPt_comp_baseChangeIso`) and over `Spec O`
(`baseChangeIso_toSpec`). -/
noncomputable def baseChangeIso :
    (projModelCode O (thetaFamily_ne_zero hθ0 hg)).scheme ≅ (projModelCode O' hg).scheme :=
  isoOfDominates hR' hR hg (thetaFamily_ne_zero hθ0 hg) (RingEquiv.refl F)
    (thetaFamily_dominates hR hθ0 hθ hg hR'le) (dominates_thetaFamily hθR' hRR')

theorem genericPt_comp_baseChangeIso :
    genericPt O (thetaFamily_ne_zero hθ0 hg) ≫
        (baseChangeIso hR hR' hθ0 hθ hθR' hR'le hRR' hg).hom =
      genericPt O' hg := by
  rw [baseChangeIso, isoOfDominates_hom, genericPt_comp_homOfDominates]
  exact (congrArg (· ≫ genericPt O' hg) (Spec.map_id (CommRingCat.of F))).trans
    (Category.id_comp _)

theorem baseChangeIso_toSpec [Algebra O O'] [IsScalarTower O O' F] :
    (baseChangeIso hR hR' hθ0 hθ hθR' hR'le hRR' hg).hom ≫ (projModelCode O' hg).toSpec ≫
      Spec.map (CommRingCat.ofHom (algebraMap O O')) =
      (projModelCode O (thetaFamily_ne_zero hθ0 hg)).toSpec := by
  refine hom_ext_genericPt _ ?_
  rw [reassoc_of% genericPt_comp_baseChangeIso, reassoc_of% genericPt_toSpec, genericPt_toSpec,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end BaseChange

end ProjScheme

end SemistableReduction
