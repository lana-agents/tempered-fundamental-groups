/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Scheme

/-!
# Morphisms into projective model codes from local domination

Blueprint §9.7a (W10 assembly). `homOfDominates` (W10Scheme) needs every chart of the source to
map into a single chart of the target. Morphisms of models need not do that; only locally (on
basic opens of the charts) do they land in one chart. This file glues such local data.

* `LocallyDominates R₁ φ f ι`: for a domain `D` with an injection `ι : D → F₂` and a ring map
  `φ : F₁ → F₂`, every prime `𝔮` of `D` has some `s ∉ 𝔮` and a chart `R₁[f / f i]` whose
  `φ`-image lies in `D[1/s]` (inside `F₂`).
* `homOfLocal`: then there is a morphism `Spec D ⟶ projModelCode O₁ hf` with
  `Spec ι ≫ ψ = Spec φ ≫ genericPt` (`SpecMap_comp_homOfLocal`), unique with this property
  (`eq_homOfLocal`), lying over `Spec O₁` (`homOfLocal_toSpec`).
* `homOfLocalProj`: the same with the source a projective model code, every chart of which is
  locally dominated (`genericPt_comp_homOfLocalProj`, `homOfLocalProj_toSpec`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace SemistableReduction

open TemperedFundamentalGroups ProjScheme

/-- `Spec` of an injective ring map is dominant. -/
lemma isDominant_SpecMap_of_injective {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B)
    (hφ : Function.Injective φ) : IsDominant (Spec.map (CommRingCat.ofHom φ)) := by
  rw [isDominant_iff]
  change DenseRange (PrimeSpectrum.comap φ)
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot φ).1 hφ]
  exact bot_le

namespace ProjScheme

section Local

variable {O₁ : Type u} [CommRing O₁] {F₁ : Type u} [Field F₁] [Algebra O₁ F₁] {m : ℕ}
  {f : Fin (m + 1) → F₁} (R₁ : Subring F₁) {F₂ : Type u} [Field F₂] (φ : F₁ →+* F₂)
  {D : Type u} [CommRing D] [IsDomain D] (ι : D →+* F₂)

/-- **Local domination**: every prime of `D` has a basic open neighbourhood `D[1/s]` containing
the `φ`-image of some chart `R₁[f / f i]`. -/
def LocallyDominates (f : Fin (m + 1) → F₁) : Prop :=
  ∀ 𝔮 : PrimeSpectrum D, ∃ i, ∃ s : D, s ∉ 𝔮.asIdeal ∧
    ∀ y ∈ projChart R₁ f i, ∃ d : D, ∃ n : ℕ, φ y * ι s ^ n = ι d

variable {ι} (hι : Function.Injective ι)

omit [IsDomain D] in
include hι in
lemma isUnit_of_ne_zero {s : D} (hs : s ≠ 0) : IsUnit (ι s) :=
  isUnit_iff_ne_zero.2 fun h ↦ hs (hι (h.trans (map_zero ι).symm))

/-- The extension `D[1/s] → F₂` of `ι`. -/
noncomputable def awayLift {s : D} (hs : s ≠ 0) : Localization.Away s →+* F₂ :=
  IsLocalization.Away.lift s (isUnit_of_ne_zero hι hs)

omit [IsDomain D] in
lemma awayLift_algebraMap {s : D} (hs : s ≠ 0) (d : D) :
    awayLift hι hs (algebraMap D (Localization.Away s) d) = ι d :=
  IsLocalization.Away.lift_eq _ _ _

omit [IsDomain D] in
lemma awayLift_comp {s : D} (hs : s ≠ 0) :
    (awayLift hι hs).comp (algebraMap D (Localization.Away s)) = ι :=
  RingHom.ext (awayLift_algebraMap hι hs)

lemma awayLift_injective {s : D} (hs : s ≠ 0) : Function.Injective (awayLift hι hs) := by
  rw [awayLift, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro h
    exact (IsLocalization.injective (Localization.Away s)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hs) h) ▸ rfl
  · intro h
    rw [hι h]

/-- `D[1/s]` is isomorphic to its image in `F₂`. -/
noncomputable def awayEquiv {s : D} (hs : s ≠ 0) :
    Localization.Away s ≃+* (awayLift hι hs).range :=
  RingEquiv.ofBijective (awayLift hι hs).rangeRestrict
    ⟨fun _ _ h ↦ awayLift_injective hι hs (congrArg Subtype.val h),
      (awayLift hι hs).rangeRestrict_surjective⟩

omit [IsDomain D] in
lemma mem_range_awayLift {s : D} (hs : s ≠ 0) {z : F₂} {d : D} {n : ℕ}
    (h : z * ι s ^ n = ι d) : z ∈ (awayLift hι hs).range := by
  refine ⟨IsLocalization.mk' (Localization.Away s) d (⟨s ^ n, n, rfl⟩ : Submonoid.powers s), ?_⟩
  rw [awayLift, IsLocalization.Away.lift, IsLocalization.lift_mk']
  have hu := (isUnit_of_ne_zero hι hs).pow n
  rw [Units.mul_inv_eq_iff_eq_mul]
  simp only [IsUnit.coe_liftRight, MonoidHom.restrict_apply, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, map_pow]
  exact h.symm

omit [IsDomain D] in
lemma exists_of_mem_range_awayLift {s : D} (hs : s ≠ 0) {z : F₂} (h : z ∈ (awayLift hι hs).range) :
    ∃ d : D, ∃ n : ℕ, z * ι s ^ n = ι d := by
  obtain ⟨w, rfl⟩ := h
  obtain ⟨⟨d, ⟨_, n, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) w
  refine ⟨d, n, ?_⟩
  have := IsLocalization.mk'_spec (Localization.Away s) d (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
  have h2 := congrArg (awayLift hι hs) this
  rw [map_mul, awayLift_algebraMap, awayLift_algebraMap] at h2
  rw [← map_pow]
  exact h2

omit [IsDomain D] in
include hι in
/-- **Local domination from generators**: it suffices that for every prime `𝔮` of `D` the
`φ`-images of the generators `f k / f i` of some chart are fractions with denominators outside `𝔮`
(and `φ (R₁) ⊆ ι (D)`). -/
theorem locallyDominates_of_forall (hR : ∀ y ∈ R₁, ∃ d, φ y = ι d)
    (h : ∀ 𝔮 : PrimeSpectrum D, ∃ i, ∀ k, ∃ d s : D, s ∉ 𝔮.asIdeal ∧ φ (f k / f i) * ι s = ι d) :
    LocallyDominates R₁ φ ι f := by
  classical
  intro 𝔮
  obtain ⟨i, hi⟩ := h 𝔮
  choose d t ht hdt using hi
  set s := ∏ k, t k with hs_def
  have hs𝔮 : s ∉ 𝔮.asIdeal := by
    intro hs
    obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := 𝔮.asIdeal)).1 hs
    exact ht k hk
  have hs0 : s ≠ 0 := fun h0 ↦ hs𝔮 (h0 ▸ 𝔮.asIdeal.zero_mem)
  refine ⟨i, s, hs𝔮, fun y hy ↦ exists_of_mem_range_awayLift hι hs0 ?_⟩
  have hle : projChart R₁ f i ≤ (awayLift hι hs0).range.comap φ := by
    refine projChart_le (fun y hy ↦ ?_) (fun k ↦ ?_)
    · obtain ⟨d, hd⟩ := hR y hy
      exact ⟨algebraMap D _ d, by rw [awayLift_algebraMap, hd]⟩
    · refine mem_range_awayLift hι hs0 (d := d k * ∏ l ∈ Finset.univ.erase k, t l) (n := 1) ?_
      rw [pow_one, hs_def, ← Finset.mul_prod_erase Finset.univ t (Finset.mem_univ k), map_mul,
        ← mul_assoc, hdt, map_mul]
  exact hle hy

/-- The ring map from the chart `R₁[f / f i]` to `D[1/s]`. -/
noncomputable def awayChartMap {i : Fin (m + 1)} {s : D} (hs : s ≠ 0)
    (h : ∀ y ∈ projChart R₁ f i, ∃ d : D, ∃ n : ℕ, φ y * ι s ^ n = ι d) :
    projChart R₁ f i →+* Localization.Away s :=
  (awayEquiv hι hs).symm.toRingHom.comp ((φ.comp (projChart R₁ f i).subtype).codRestrict _
    fun y ↦ by
      obtain ⟨d, n, hd⟩ := h y y.2
      exact mem_range_awayLift hι hs hd)

lemma awayLift_awayChartMap {i : Fin (m + 1)} {s : D} (hs : s ≠ 0)
    (h : ∀ y ∈ projChart R₁ f i, ∃ d : D, ∃ n : ℕ, φ y * ι s ^ n = ι d) :
    (awayLift hι hs).comp (awayChartMap R₁ φ hι hs h) = φ.comp (projChart R₁ f i).subtype := by
  ext y
  exact congrArg Subtype.val ((awayEquiv hι hs).apply_symm_apply _)

variable {R₁} (hR₁ : (algebraMap O₁ F₁).range = R₁) (hf : ∀ i, f i ≠ 0)
variable (hloc : LocallyDominates R₁ φ ι f)

omit [IsDomain D] in
lemma ne_zero_of_locallyDominates (𝔮 : PrimeSpectrum D) : (hloc 𝔮).choose_spec.choose ≠ 0 :=
  fun h ↦ (hloc 𝔮).choose_spec.choose_spec.1 (h ▸ 𝔮.asIdeal.zero_mem)

/-- The cover of `Spec D` by the basic opens of local domination. -/
noncomputable def localCover : (Spec (CommRingCat.of D)).OpenCover :=
  Scheme.Cover.mkOfCovers (PrimeSpectrum D)
    (fun 𝔮 ↦ Spec (CommRingCat.of (Localization.Away (hloc 𝔮).choose_spec.choose)))
    (fun 𝔮 ↦ Spec.map (CommRingCat.ofHom (algebraMap D _)))
    (fun x ↦ by
      have hx : x ∈ (Spec.map (CommRingCat.ofHom
          (algebraMap D (Localization.Away (hloc x).choose_spec.choose)))).opensRange := by
        rw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of D)]
        exact (hloc x).choose_spec.choose_spec.1
      obtain ⟨y, hy⟩ := hx
      exact ⟨x, y, hy⟩)

/-- The morphism on the basic open of `𝔮`. -/
noncomputable def localMap (𝔮 : PrimeSpectrum D) :
    Spec (CommRingCat.of (Localization.Away (hloc 𝔮).choose_spec.choose)) ⟶
      (projModelCode O₁ hf).scheme :=
  Spec.map (CommRingCat.ofHom (awayChartMap R₁ φ hι (ne_zero_of_locallyDominates φ hloc 𝔮)
    (hloc 𝔮).choose_spec.choose_spec.2)) ≫ chartι R₁ hR₁ hf (hloc 𝔮).choose

lemma SpecMap_awayLift_localMap (𝔮 : PrimeSpectrum D) :
    Spec.map (CommRingCat.ofHom (awayLift hι (ne_zero_of_locallyDominates φ hloc 𝔮))) ≫
        localMap φ hι hR₁ hf hloc 𝔮 =
      Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf := by
  rw [localMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    awayLift_awayChartMap, genericPt_eq_chartι R₁ hR₁ hf (hloc 𝔮).choose, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

omit [IsDomain D] in
lemma SpecMap_awayLift_comp {s : D} (hs : s ≠ 0) :
    Spec.map (CommRingCat.ofHom (awayLift hι hs)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap D (Localization.Away s))) =
      Spec.map (CommRingCat.ofHom ι) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, awayLift_comp]

lemma localMap_compat (𝔮 𝔮' : PrimeSpectrum D) :
    pullback.fst ((localCover φ hloc).f 𝔮) ((localCover φ hloc).f 𝔮') ≫
        localMap φ hι hR₁ hf hloc 𝔮 =
      pullback.snd ((localCover φ hloc).f 𝔮) ((localCover φ hloc).f 𝔮') ≫
        localMap φ hι hR₁ hf hloc 𝔮' := by
  have : IsReduced (pullback ((localCover φ hloc).f 𝔮) ((localCover φ hloc).f 𝔮')) :=
    isReduced_of_isOpenImmersion (pullback.fst _ _)
  let ι' := pullback.lift (f := (localCover φ hloc).f 𝔮) (g := (localCover φ hloc).f 𝔮')
    (Spec.map (CommRingCat.ofHom (awayLift hι (ne_zero_of_locallyDominates φ hloc 𝔮))))
    (Spec.map (CommRingCat.ofHom (awayLift hι (ne_zero_of_locallyDominates φ hloc 𝔮'))))
    (by
      change _ ≫ Spec.map _ = _ ≫ Spec.map _
      rw [SpecMap_awayLift_comp, SpecMap_awayLift_comp])
  have : IsDominant (ι' ≫ pullback.fst _ _ ≫ (localCover φ hloc).f 𝔮) := by
    rw [pullback.lift_fst_assoc]
    change IsDominant (_ ≫ Spec.map _)
    rw [SpecMap_awayLift_comp]
    exact isDominant_SpecMap_of_injective ι hι
  have : IsDominant ι' :=
    IsDominant.of_comp_of_isOpenImmersion ι' (pullback.fst _ _ ≫ (localCover φ hloc).f 𝔮)
  refine ext_of_isDominant ι' ?_
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  exact (SpecMap_awayLift_localMap φ hι hR₁ hf hloc 𝔮).trans
    (SpecMap_awayLift_localMap φ hι hR₁ hf hloc 𝔮').symm

/-- **Gluing local dominations**: a morphism `Spec D ⟶ projModelCode O₁ hf`. -/
noncomputable def homOfLocal : Spec (CommRingCat.of D) ⟶ (projModelCode O₁ hf).scheme :=
  (localCover φ hloc).glueMorphisms (localMap φ hι hR₁ hf hloc) (localMap_compat φ hι hR₁ hf hloc)

/-- The glued morphism restricts to `Spec φ ≫ genericPt` on the generic point `Spec F₂`. -/
theorem SpecMap_comp_homOfLocal :
    Spec.map (CommRingCat.ofHom ι) ≫ homOfLocal φ hι hR₁ hf hloc =
      Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf := by
  obtain ⟨𝔮⟩ : Nonempty (PrimeSpectrum D) := inferInstance
  rw [← SpecMap_awayLift_comp hι (ne_zero_of_locallyDominates φ hloc 𝔮), Category.assoc]
  change _ ≫ (localCover φ hloc).f 𝔮 ≫ _ = _
  rw [homOfLocal, Scheme.Cover.ι_glueMorphisms]
  exact SpecMap_awayLift_localMap φ hι hR₁ hf hloc 𝔮

/-- Uniqueness of the glued morphism. -/
theorem eq_homOfLocal {ψ : Spec (CommRingCat.of D) ⟶ (projModelCode O₁ hf).scheme}
    (hψ : Spec.map (CommRingCat.ofHom ι) ≫ ψ = Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf) :
    ψ = homOfLocal φ hι hR₁ hf hloc := by
  have := isDominant_SpecMap_of_injective ι hι
  exact ext_of_isDominant (Spec.map (CommRingCat.ofHom ι))
    (hψ.trans (SpecMap_comp_homOfLocal φ hι hR₁ hf hloc).symm)

/-- The glued morphism lies over `Spec O₁` when `φ` and `ι` are compatible over `O₁`. -/
theorem homOfLocal_toSpec (τ : O₁ →+* D) (hτ : ι.comp τ = φ.comp (algebraMap O₁ F₁)) :
    homOfLocal φ hι hR₁ hf hloc ≫ (projModelCode O₁ hf).toSpec =
      Spec.map (CommRingCat.ofHom τ) := by
  have := isDominant_SpecMap_of_injective ι hι
  refine ext_of_isDominant (Spec.map (CommRingCat.ofHom ι)) ?_
  rw [reassoc_of% SpecMap_comp_homOfLocal, genericPt_toSpec, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hτ]

end Local

section LocalProj

variable {O₁ O₂ : Type u} [CommRing O₁] [CommRing O₂] {F₁ F₂ : Type u} [Field F₁] [Field F₂]
  [Algebra O₁ F₁] [Algebra O₂ F₂] {m n : ℕ} {f : Fin (m + 1) → F₁} {g : Fin (n + 1) → F₂}
  {R₁ : Subring F₁} {R₂ : Subring F₂} (hR₁ : (algebraMap O₁ F₁).range = R₁)
  (hR₂ : (algebraMap O₂ F₂).range = R₂) (hf : ∀ i, f i ≠ 0) (hg : ∀ j, g j ≠ 0) (φ : F₁ →+* F₂)
  (hloc : ∀ j, LocallyDominates R₁ φ (projChart R₂ g j).subtype f)

/-- The glued morphism on the chart `Spec R₂[g / g j]`. -/
noncomputable def chartLocal (j : Fin (n + 1)) :
    Spec (CommRingCat.of (projChart R₂ g j)) ⟶ (projModelCode O₁ hf).scheme :=
  homOfLocal φ Subtype.val_injective hR₁ hf (hloc j)

lemma chartLocal_compat (j j' : Fin (n + 1)) :
    pullback.fst (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j') ≫ chartLocal hR₁ hf φ hloc j =
      pullback.snd (chartι R₂ hR₂ hg j) (chartι R₂ hR₂ hg j') ≫ chartLocal hR₁ hf φ hloc j' := by
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
  rw [pullback.lift_fst_assoc, pullback.lift_snd_assoc, chartLocal, chartLocal,
    SpecMap_comp_homOfLocal, SpecMap_comp_homOfLocal]

/-- **Local domination gives a morphism of projective model codes.** -/
noncomputable def homOfLocalProj :
    (projModelCode O₂ hg).scheme ⟶ (projModelCode O₁ hf).scheme :=
  (chartCover R₂ hR₂ hg).glueMorphisms (chartLocal hR₁ hf φ hloc)
    (chartLocal_compat hR₁ hR₂ hf hg φ hloc)

lemma chartι_homOfLocalProj (j : Fin (n + 1)) :
    chartι R₂ hR₂ hg j ≫ homOfLocalProj hR₁ hR₂ hf hg φ hloc = chartLocal hR₁ hf φ hloc j :=
  Scheme.Cover.ι_glueMorphisms (chartCover R₂ hR₂ hg) _ _ j

/-- The morphism is compatible with the generic points. -/
theorem genericPt_comp_homOfLocalProj :
    genericPt O₂ hg ≫ homOfLocalProj hR₁ hR₂ hf hg φ hloc =
      Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf := by
  rw [genericPt_eq_chartι R₂ hR₂ hg 0, Category.assoc, chartι_homOfLocalProj, chartLocal,
    SpecMap_comp_homOfLocal]

/-- Uniqueness: a morphism compatible with the generic points is `homOfLocalProj`. -/
theorem eq_homOfLocalProj
    {ψ : (projModelCode O₂ hg).scheme ⟶ (projModelCode O₁ hf).scheme}
    (hψ : genericPt O₂ hg ≫ ψ = Spec.map (CommRingCat.ofHom φ) ≫ genericPt O₁ hf) :
    ψ = homOfLocalProj hR₁ hR₂ hf hg φ hloc :=
  hom_ext_genericPt hg (hψ.trans (genericPt_comp_homOfLocalProj hR₁ hR₂ hf hg φ hloc).symm)

/-- The morphism lies over `Spec O₂ ⟶ Spec O₁` when `φ` lies over `τ : O₁ → O₂`. -/
theorem homOfLocalProj_toSpec (τ : O₁ →+* O₂)
    (hτ : φ.comp (algebraMap O₁ F₁) = (algebraMap O₂ F₂).comp τ) :
    homOfLocalProj hR₁ hR₂ hf hg φ hloc ≫ (projModelCode O₁ hf).toSpec =
      (projModelCode O₂ hg).toSpec ≫ Spec.map (CommRingCat.ofHom τ) := by
  refine hom_ext_genericPt hg ?_
  rw [reassoc_of% genericPt_comp_homOfLocalProj, genericPt_toSpec, reassoc_of% genericPt_toSpec,
    ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hτ]

end LocalProj

end ProjScheme

end SemistableReduction
