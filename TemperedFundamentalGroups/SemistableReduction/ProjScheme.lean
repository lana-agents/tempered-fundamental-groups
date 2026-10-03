/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjModel
import TemperedFundamentalGroups.SemistableReduction.Statement
import TemperedFundamentalGroups.SemistableReduction.ChartSpecialization

/-!
# The projective model as a model code

Blueprint §9.6 (W5), layer M9b. For a ring `O`, a field `F` with `O → F` (image `R`) and a family
`f : Fin (m + 1) → F` of nonzero functions:

* `ProjScheme.toProj O hf : Spec F ⟶ ℙᵐ_O`, the point with homogeneous coordinates `f`
  (`Spec F ⟶ D₊(x_i) = Spec (O[x]_{x_i})₀` via `a / x_i ^ n ↦ a(f) / f_i ^ n`, `awayEval`;
  independent of `i`, `toProj_eq`), over `Spec O` (`toProj_toSpec`);
* `projModelCode O hf : ModelCode O`, its scheme-theoretic image (`Scheme.Hom.ker`), i.e. the
  closure of the image of `Spec F` in `ℙᵐ_O`;
* `chartOpen O hf i`, the affine open `D₊(x_i)` of the model, covering it
  (`exists_mem_chartOpen`); its ring of sections is the chart `R[f j / f i]` of the Zariski model
  `projModel R f` (`range_chartHom'`, `chartHom'_injective`), as `O`-algebras (`chartEquiv`);
  `chartι : Spec R[f j / f i] ⟶` (model), an open immersion over `Spec O` (`chartι_toSpec`)
  through which the generic point `Spec F ⟶` (model) factors
  (`toImage_eq_SpecMap_comp_chartι`).

Consequences:

* `projModelCode_isSemistable`: if all charts `R[f j / f i]` are semistable
  (`LocalModel.IsSemistable`, e.g. by M7c), the model code is semistable
  (`ModelCode.IsSemistable`, the form of W10);
* `sp_projModelCode`: the scheme-theoretic specialization (`Models/Specialization.sp`) of an
  `Ω`-point of the generic fibre is the point of the chart at the center of the valuation ring
  `j⁻¹(V)` (so it is the Zariski specialization `ZariskiModel.center`, cf. M3).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace SemistableReduction

open TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {F : Type u} [Field F] [Algebra O F] {m : ℕ}

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

namespace ProjScheme

variable (f : Fin (m + 1) → F)

/-- Evaluation of homogeneous coordinates at the family `f`. -/
noncomputable def evalHom : MvPolynomial (Fin (m + 1)) O →+* F :=
  MvPolynomial.eval₂Hom (algebraMap O F) f

/-- The map `(O[x]_s)₀ → F`, `a / s ^ n ↦ a(f) / s(f) ^ n`. -/
noncomputable def awayEval (s : MvPolynomial (Fin (m + 1)) O) (hs : IsUnit (evalHom f s)) :
    Away (𝒜 m) s →+* F :=
  (Localization.awayLift (evalHom f) s hs).comp (algebraMap _ (Localization.Away s))

lemma awayEval_mk {s : MvPolynomial (Fin (m + 1)) O} (hs : IsUnit (evalHom f s)) {d : ℕ}
    (hsd : s ∈ (𝒜 m) d) (n : ℕ) (a : MvPolynomial (Fin (m + 1)) O) (ha : a ∈ (𝒜 m) (n • d)) :
    awayEval f s hs (Away.mk (𝒜 m) hsd n a ha) = evalHom f a / evalHom f s ^ n := by
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  rw [Localization.mk_eq_mk', Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  have : evalHom f s ^ n ≠ 0 := pow_ne_zero _ hs.ne_zero
  simp only [map_pow]
  field_simp

lemma awayEval_comp_awayMap {s t x : MvPolynomial (Fin (m + 1)) O} {d : ℕ} (ht : t ∈ (𝒜 m) d)
    (hx : x = s * t) (hs : IsUnit (evalHom f s)) (hxu : IsUnit (evalHom f x)) :
    (awayEval f x hxu).comp (awayMap (𝒜 m) ht hx) = awayEval f s hs := by
  ext z
  simp only [awayEval, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, val_awayMap]
  rw [← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
  simp [Localization.awayLift, IsLocalization.Away.lift]

/-- The value of `a / x_i ^ n` at `f` (for `a` homogeneous of degree `n`) is `a(f / f_i)`. -/
lemma evalHom_div_pow {a : MvPolynomial (Fin (m + 1)) O} {n : ℕ} (ha : a.IsHomogeneous n)
    (i : Fin (m + 1)) :
    evalHom f a / f i ^ n = MvPolynomial.eval₂ (algebraMap O F) (fun k ↦ f k / f i) a := by
  rw [evalHom, coe_eval₂Hom, eval₂_eq', eval₂_eq', Finset.sum_div]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases hd : coeff d a = 0
  · simp [hd]
  have hdeg : d.degree = n := by
    by_contra h
    exact hd (ha.coeff_eq_zero h)
  rw [Finsupp.degree_eq_sum] at hdeg
  simp_rw [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, hdeg, mul_div_assoc]

variable (R : Subring F)

lemma eval₂_mem_projChart (hR : (algebraMap O F).range = R) (i : Fin (m + 1))
    (a : MvPolynomial (Fin (m + 1)) O) :
    MvPolynomial.eval₂ (algebraMap O F) (fun k ↦ f k / f i) a ∈ projChart R f i := by
  induction a using MvPolynomial.induction_on with
  | C o => exact base_le_projChart i (by rw [eval₂_C, ← hR]; exact ⟨o, rfl⟩)
  | add p q hp hq => rw [eval₂_add]; exact add_mem hp hq
  | mul_X p k hp => rw [eval₂_mul, eval₂_X]; exact mul_mem hp (div_mem_projChart i k)

lemma X_mem (i : Fin (m + 1)) : (X i : MvPolynomial (Fin (m + 1)) O) ∈ (𝒜 m) 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O i)

lemma isUnit_evalHom_X {i : Fin (m + 1)} (hi : f i ≠ 0) :
    IsUnit (evalHom f (X i : MvPolynomial (Fin (m + 1)) O)) := by
  simpa [evalHom] using hi

/-- The range of `(O[x]_{x_i})₀ → F` is the chart `R[f j / f i]`. -/
theorem range_awayEval (hR : (algebraMap O F).range = R) {i : Fin (m + 1)} (hi : f i ≠ 0) :
    (awayEval f (X i) (isUnit_evalHom_X (O := O) f hi)).range = projChart R f i := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (𝒜 m) (X_mem i) z
    rw [awayEval_mk]
    have ha' : a.IsHomogeneous n := by simpa using ha
    have : evalHom f (X i : MvPolynomial (Fin (m + 1)) O) = f i := by simp [evalHom]
    rw [this, evalHom_div_pow f ha' i]
    exact eval₂_mem_projChart f R hR i a
  · refine projChart_le ?_ fun j ↦ ?_
    · intro y hy
      rw [← hR] at hy
      obtain ⟨o, rfl⟩ := hy
      refine ⟨Away.mk (𝒜 m) (X_mem i) 0 (C o) (by simp), ?_⟩
      rw [awayEval_mk]
      simp [evalHom]
    · refine ⟨Away.mk (𝒜 m) (X_mem i) 1 (X j) (by simpa using X_mem j), ?_⟩
      rw [awayEval_mk]
      simp [evalHom]

variable {f}

variable (O m) in
/-- The open immersion `Spec (O[x]_{x_i})₀ ⟶ ℙᵐ_O` of the standard open `D₊(x_i)`. -/
noncomputable def stdι (i : Fin (m + 1)) :
    Spec (CommRingCat.of (Away (𝒜 m) (X i))) ⟶ projSpace O m :=
  Proj.awayι (𝒜 m) (X i) (X_mem i) one_pos

instance (i : Fin (m + 1)) : IsOpenImmersion (stdι O m i) :=
  inferInstanceAs (IsOpenImmersion (Proj.awayι (𝒜 m) (X i) (X_mem i) one_pos))

lemma stdι_toSpec (i : Fin (m + 1)) :
    stdι O m i ≫ projSpace.toSpec O m = Spec.map (CommRingCat.ofHom
      ((fromZeroRingHom (𝒜 m) (Submonoid.powers (X i))).comp (algebraMap O ((𝒜 m) 0)))) := by
  change Proj.awayι (𝒜 m) (X i) (X_mem i) one_pos ≫ Proj.toSpecZero _ ≫ _ = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, CommRingCat.ofHom_comp]

variable (O) in
/-- The morphism `Spec F ⟶ ℙᵐ_O` given by the homogeneous coordinates `f`. -/
noncomputable def toProj (hf : ∀ i, f i ≠ 0) : Spec (CommRingCat.of F) ⟶ projSpace O m :=
  Spec.map (CommRingCat.ofHom (awayEval f (X 0) (isUnit_evalHom_X f (hf 0)))) ≫ stdι O m 0

lemma SpecMap_awayEval_awayι (hf : ∀ i, f i ≠ 0) (i j : Fin (m + 1)) :
    Spec.map (CommRingCat.ofHom (awayEval f (X i) (isUnit_evalHom_X f (hf i)))) ≫
      Proj.awayι (𝒜 m) (X i) (X_mem i) one_pos =
    Spec.map (CommRingCat.ofHom (awayEval f (X i * X j)
      (by rw [map_mul]; exact (isUnit_evalHom_X f (hf i)).mul (isUnit_evalHom_X f (hf j))))) ≫
      Proj.awayι (𝒜 m) (X i * X j) (SetLike.mul_mem_graded (X_mem i) (X_mem j))
        (by norm_num) := by
  rw [← Proj.SpecMap_awayMap_awayι (𝒜 m) (X_mem i) one_pos (X_mem j) rfl, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, awayEval_comp_awayMap]

lemma SpecMap_awayEval_awayι_congr {x y : MvPolynomial (Fin (m + 1)) O} (h : x = y)
    (hx : IsUnit (evalHom f x)) (hy : IsUnit (evalHom f y)) {d : ℕ} (hxd : x ∈ (𝒜 m) d)
    (hyd : y ∈ (𝒜 m) d) (hd : 0 < d) :
    Spec.map (CommRingCat.ofHom (awayEval f x hx)) ≫ Proj.awayι (𝒜 m) x hxd hd =
      Spec.map (CommRingCat.ofHom (awayEval f y hy)) ≫ Proj.awayι (𝒜 m) y hyd hd := by
  subst h
  rfl

lemma SpecMap_awayEval_awayι_eq (hf : ∀ i, f i ≠ 0) (i j : Fin (m + 1)) :
    Spec.map (CommRingCat.ofHom (awayEval f (X i) (isUnit_evalHom_X f (hf i)))) ≫
      Proj.awayι (𝒜 m) (X i) (X_mem i) one_pos =
    Spec.map (CommRingCat.ofHom (awayEval f (X j) (isUnit_evalHom_X f (hf j)))) ≫
      Proj.awayι (𝒜 m) (X j) (X_mem j) one_pos := by
  rw [SpecMap_awayEval_awayι hf i j, SpecMap_awayEval_awayι hf j i]
  exact SpecMap_awayEval_awayι_congr (mul_comm _ _) _ _ _ _ _

theorem toProj_eq (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    toProj O hf = Spec.map (CommRingCat.ofHom (awayEval f (X i) (isUnit_evalHom_X f (hf i)))) ≫
      stdι O m i :=
  SpecMap_awayEval_awayι_eq hf 0 i

theorem toProj_toSpec (hf : ∀ i, f i ≠ 0) :
    toProj O hf ≫ projSpace.toSpec O m = Spec.map (CommRingCat.ofHom (algebraMap O F)) := by
  rw [toProj, Category.assoc, stdι_toSpec, ← Spec.map_comp]
  congr 1
  ext o
  simp only [awayEval, fromZeroRingHom, Localization.awayLift, IsLocalization.Away.lift,
    CommRingCat.hom_ofHom]
  change IsLocalization.lift _ (Localization.mk _ 1) = _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.lift_eq]
  simp [evalHom, MvPolynomial.algebraMap_eq]

variable (O m) in
/-- The standard affine open `D₊(x_i)` of `ℙᵐ_O`. -/
noncomputable def stdOpen (i : Fin (m + 1)) : (projSpace O m).affineOpens :=
  ⟨stdι O m i ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion _⟩

lemma appLE_eq_of_eq_comp {X Y Z : Scheme.{u}} {g : X ⟶ Z} {a : X ⟶ Y} {ι : Y ⟶ Z}
    [IsOpenImmersion ι] (e : g = a ≫ ι) (h) :
    g.appLE (ι ''ᵁ ⊤) ⊤ h = (ι.appIso ⊤).hom ≫ a.app ⊤ := by
  subst e
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
  rfl

lemma appLE_toProj (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) (h) :
    (toProj O hf).appLE (stdOpen O m i).1 ⊤ h =
      ((stdι O m i).appIso ⊤).hom ≫
        (Spec.map (CommRingCat.ofHom (awayEval f (X i) (isUnit_evalHom_X f (hf i))))).appTop :=
  appLE_eq_of_eq_comp (toProj_eq (O := O) hf i) h

lemma appLE_congr_hom {X Y : Scheme.{u}} {g g' : X ⟶ Y} (e : g = g') (U V h) :
    g.appLE U V h = g'.appLE U V (e ▸ h) := by
  subst e
  rfl

variable (O) in
/-- **The projective model as a model code**: the scheme-theoretic image (closure) of
`Spec F ⟶ ℙᵐ_O` given by the homogeneous coordinates `f`. -/
noncomputable def projModelCode (hf : ∀ i, f i ≠ 0) : TemperedFundamentalGroups.ModelCode O :=
  ⟨m, (toProj O hf).ker⟩

lemma projModelCode_scheme (hf : ∀ i, f i ≠ 0) :
    (projModelCode O hf).scheme = (toProj O hf).image := rfl

lemma toProj_preimage_stdOpen (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    toProj O hf ⁻¹ᵁ (stdOpen O m i).1 = ⊤ := by
  refine top_le_iff.1 fun x _ ↦ ?_
  change (toProj O hf) x ∈ stdι O m i ''ᵁ ⊤
  rw [toProj_eq (O := O) hf i, Scheme.Hom.comp_apply]
  exact ⟨_, trivial, rfl⟩

variable (O) in
/-- The affine open `D₊(x_i)` of the projective model. -/
noncomputable def chartOpen (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    (projModelCode O hf).scheme.Opens :=
  (toProj O hf).imageι ⁻¹ᵁ (stdOpen O m i).1

lemma isAffineOpen_chartOpen (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    IsAffineOpen (chartOpen O hf i) :=
  haveI : IsClosedImmersion (toProj O hf).ker.subschemeι := inferInstance
  (stdOpen O m i).2.preimage (toProj O hf).ker.subschemeι

lemma top_le_toImage_preimage_chartOpen (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    ⊤ ≤ (toProj O hf).toImage ⁻¹ᵁ chartOpen O hf i := by
  intro x _
  have := toProj_preimage_stdOpen (O := O) hf i ▸
    (show x ∈ (⊤ : (Spec (CommRingCat.of F)).Opens) from trivial)
  change (toProj O hf).imageι ((toProj O hf).toImage x) ∈ (stdOpen O m i).1
  rwa [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]

variable (O) in
/-- The sections of the projective model over `D₊(x_i)`, as functions on `Spec F`. -/
noncomputable def chartHom' (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    Γ((projModelCode O hf).scheme, chartOpen O hf i) ⟶ CommRingCat.of F :=
  (toProj O hf).toImage.appLE (chartOpen O hf i) ⊤ (top_le_toImage_preimage_chartOpen hf i) ≫
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom

set_option backward.isDefEq.respectTransparency false in
lemma chartHom'_comp (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    (toProj O hf).imageι.app (stdOpen O m i).1 ≫ chartHom' O hf i =
      (toProj O hf).appLE (stdOpen O m i).1 ⊤ (toProj_preimage_stdOpen hf i).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of F)).hom := by
  have A : (toProj O hf).imageι.app (stdOpen O m i).1 ≫
      (toProj O hf).toImage.appLE (chartOpen O hf i) ⊤ (top_le_toImage_preimage_chartOpen hf i) =
      (toProj O hf).appLE (stdOpen O m i).1 ⊤ (toProj_preimage_stdOpen hf i).ge := by
    rw [appLE_congr_hom (Scheme.Hom.toImage_imageι (toProj O hf)).symm, Scheme.Hom.comp_appLE]
    rfl
  rw [chartHom', reassoc_of% A]

set_option backward.isDefEq.respectTransparency false in
lemma chartHom'_comp_eq (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    (toProj O hf).imageι.app (stdOpen O m i).1 ≫ chartHom' O hf i =
      ((stdι O m i).appIso ⊤).hom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (Away (𝒜 m) (X i)))).hom ≫
        CommRingCat.ofHom (awayEval f (X i) (isUnit_evalHom_X f (hf i))) := by
  rw [chartHom'_comp, appLE_toProj]
  simp only [Category.assoc, Scheme.ΓSpecIso_naturality]

lemma chartHom'_apply (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1))
    (w : Γ(projSpace O m, (stdOpen O m i).1)) :
    (chartHom' O hf i).hom (((toProj O hf).imageι.app (stdOpen O m i).1).hom w) =
      awayEval f (X i) (isUnit_evalHom_X f (hf i))
        ((((stdι O m i).appIso ⊤).hom ≫
          (Scheme.ΓSpecIso (CommRingCat.of (Away (𝒜 m) (X i)))).hom).hom w) := by
  have := congr_arg (fun φ ↦ φ.hom w) (chartHom'_comp_eq (O := O) hf i)
  exact this

/-- **The sections of the projective model over `D₊(x_i)` are the chart `R[f j / f i]`.** -/
theorem range_chartHom' (R : Subring F) (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
    (i : Fin (m + 1)) : (chartHom' O hf i).hom.range = projChart R f i := by
  rw [← range_awayEval f R hR (hf i)]
  have h₁ : Function.Surjective ((toProj O hf).imageι.app (stdOpen O m i).1).hom :=
    (toProj O hf).ker.subschemeι_app_surjective (stdOpen O m i)
  have h₂ : Function.Surjective (((stdι O m i).appIso ⊤).hom ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Away (𝒜 m) (X i)))).hom).hom :=
    (ConcreteCategory.bijective_of_isIso _).2
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, rfl⟩ := h₁ z
    exact ⟨_, (chartHom'_apply hf i w).symm⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨w, rfl⟩ := h₂ t
    exact ⟨_, chartHom'_apply hf i w⟩

set_option backward.isDefEq.respectTransparency false in
theorem chartHom'_injective (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    Function.Injective (chartHom' O hf i).hom := by
  have e : (⊤ : (Spec (CommRingCat.of F)).Opens) = (toProj O hf).toImage ⁻¹ᵁ chartOpen O hf i :=
    le_antisymm (top_le_toImage_preimage_chartOpen hf i) le_top
  have : (toProj O hf).toImage.appLE (chartOpen O hf i) ⊤ (top_le_toImage_preimage_chartOpen hf i)
      = (toProj O hf).toImage.app (chartOpen O hf i) ≫
        (Spec (CommRingCat.of F)).presheaf.map (eqToHom e).op := rfl
  rw [chartHom', this]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  refine (ConcreteCategory.bijective_of_isIso _).1.comp
    ((ConcreteCategory.bijective_of_isIso _).1.comp ?_)
  exact (toProj O hf).toImage_app_injective (stdOpen O m i)

lemma toImage_toSpec (hf : ∀ i, f i ≠ 0) :
    (toProj O hf).toImage ≫ (projModelCode O hf).toSpec =
      Spec.map (CommRingCat.ofHom (algebraMap O F)) := by
  change (toProj O hf).toImage ≫ (toProj O hf).imageι ≫ projSpace.toSpec O m = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, toProj_toSpec]

set_option backward.isDefEq.respectTransparency false in
lemma chartHom'_algebraMap_comp (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ (projModelCode O hf).toSpec.appTop ≫
      (projModelCode O hf).scheme.presheaf.map (homOfLE le_top : chartOpen O hf i ⟶ ⊤).op ≫
        chartHom' O hf i = CommRingCat.ofHom (algebraMap O F) := by
  have A : (projModelCode O hf).toSpec.appTop ≫
      (projModelCode O hf).scheme.presheaf.map (homOfLE le_top : chartOpen O hf i ⟶ ⊤).op ≫
        (toProj O hf).toImage.appLE (chartOpen O hf i) ⊤ (top_le_toImage_preimage_chartOpen hf i)
      = (Spec.map (CommRingCat.ofHom (algebraMap O F))).appTop := by
    rw [Scheme.Hom.map_appLE]
    change (projModelCode O hf).toSpec.app ⊤ ≫ (toProj O hf).toImage.appLE
      ((projModelCode O hf).toSpec ⁻¹ᵁ ⊤) ⊤ le_top = _
    rw [← Scheme.Hom.comp_appLE, appLE_congr_hom (toImage_toSpec hf)]
    rfl
  rw [chartHom', reassoc_of% A, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- The ring of sections of the projective model over `D₊(x_i)`, with its `O`-algebra structure
from the structure morphism, maps to `F` compatibly with `O → F`. -/
lemma chartHom'_algebraMap (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) (o : O) :
    letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
      (projModelCode O hf) (chartOpen O hf i)
    (chartHom' O hf i).hom (algebraMap O _ o) = algebraMap O F o :=
  congr_arg (fun φ ↦ φ.hom o) (chartHom'_algebraMap_comp hf i)

lemma irrelevant_le_span_X :
    (HomogeneousIdeal.irrelevant (𝒜 m)).toIdeal ≤
      Ideal.span (Set.range (X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) O)) := by
  intro p hp
  change GradedRing.proj (𝒜 m) 0 p = 0 at hp
  rw [GradedRing.proj_apply] at hp
  have h0 : homogeneousComponent 0 p = 0 := by
    rw [← decomposition.decompose'_apply]
    exact hp
  rw [homogeneousComponent_zero, C_eq_zero] at h0
  rw [← Set.image_univ, mem_ideal_span_X_image]
  intro d hd
  by_contra! H
  have : d = 0 := Finsupp.ext fun k ↦ H k trivial
  subst this
  exact (mem_support_iff.1 hd) h0

lemma exists_mem_chartOpen (hf : ∀ i, f i ≠ 0) (x : (projModelCode O hf).scheme) :
    ∃ i, x ∈ chartOpen O hf i := by
  have htop := Proj.iSup_basicOpen_eq_top (𝒜 m) _ (irrelevant_le_span_X (O := O) (m := m))
  have hx : ((toProj O hf).imageι (x : (toProj O hf).image) : Proj (𝒜 m)) ∈
      ⨆ i, Proj.basicOpen (𝒜 m) (X i) := by
    rw [htop]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  refine ⟨i, ?_⟩
  change (toProj O hf).imageι x ∈ stdι O m i ''ᵁ ⊤
  rw [Scheme.Hom.image_top_eq_opensRange]
  change _ ∈ (Proj.awayι (𝒜 m) (X i) (X_mem i) one_pos).opensRange
  rw [Proj.opensRange_awayι]
  exact hi

variable (R : Subring F)

/-- The `O`-algebra structure on a chart `R[f j / f i]`, `R` the image of `O`. -/
noncomputable abbrev projChartAlgebra (hR : (algebraMap O F).range = R) (i : Fin (m + 1)) :
    Algebra O (projChart R f i) :=
  ((algebraMap O F).codRestrict (projChart R f i) fun o ↦
    base_le_projChart i (hR ▸ ⟨o, rfl⟩)).toAlgebra

/-- **The sections of the projective model over `D₊(x_i)` are the chart `R[f j / f i]`**, as
`O`-algebras. -/
noncomputable def chartEquiv (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
    (i : Fin (m + 1)) :
    letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
      (projModelCode O hf) (chartOpen O hf i)
    letI := projChartAlgebra (f := f) R hR i
    Γ((projModelCode O hf).scheme, chartOpen O hf i) ≃ₐ[O] projChart R f i :=
  letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
    (projModelCode O hf) (chartOpen O hf i)
  letI := projChartAlgebra (f := f) R hR i
  { RingEquiv.ofBijective ((chartHom' O hf i).hom.codRestrict (projChart R f i) fun x ↦ by
        rw [← range_chartHom' R hR hf i]; exact ⟨x, rfl⟩)
      ⟨fun a b h ↦ chartHom'_injective hf i (congr_arg Subtype.val h), fun y ↦ by
        obtain ⟨x, hx⟩ := (range_chartHom' R hR hf i).ge y.2
        exact ⟨x, Subtype.ext hx⟩⟩ with
    commutes' := fun o ↦ Subtype.ext (chartHom'_algebraMap hf i o) }

lemma coe_chartEquiv (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1))
    (x : Γ((projModelCode O hf).scheme, chartOpen O hf i)) :
    (chartEquiv R hR hf i x : F) = (chartHom' O hf i).hom x := rfl

end ProjScheme

open ProjScheme

/-- **Semistability of projective models (M9b).** If every chart `R[f j / f i]` of the projective
model of `f` (with its `O`-algebra structure) is semistable, then so is the model code
`projModelCode O hf`, the closure of the image of `Spec F ⟶ ℙᵐ_O`. -/
theorem projModelCode_isSemistable {n : ℕ} {f : Fin (n + 1) → F} (R : Subring F)
    (hR : (algebraMap O F).range = R)
    (hf : ∀ i, f i ≠ 0) (ϖ : O)
    (h : ∀ i, letI := projChartAlgebra (f := f) R hR i; IsSemistable ϖ (projChart R f i)) :
    TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ
      (projModelCode O hf) := by
  intro x
  have hi := (exists_mem_chartOpen (O := O) hf x).choose_spec
  set i := (exists_mem_chartOpen (O := O) hf x).choose
  refine ⟨chartOpen O hf i, isAffineOpen_chartOpen (O := O) hf i, hi, ?_⟩
  letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
    (projModelCode O hf) (chartOpen O hf i)
  letI := projChartAlgebra (f := f) R hR i
  set e := chartEquiv R hR hf i
  set P := ((isAffineOpen_chartOpen hf i).primeIdealOf ⟨x, hi⟩).asIdeal
  have hQ : (P.comap e.symm.toAlgHom.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have := IsSemistableAt.of_etale_of_comap e.toAlgHom
    (RingHom.Etale.of_bijective e.bijective) (h i _ hQ)
  convert this using 1
  ext y
  simp [Ideal.mem_comap]

namespace ProjScheme

variable (R : Subring F) {f : Fin (m + 1) → F}

/-- The open immersion `Spec R[f j / f i] ⟶` (projective model) of the standard chart. -/
noncomputable def chartι (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
    (i : Fin (m + 1)) :
    Spec (CommRingCat.of (projChart R f i)) ⟶ (projModelCode O hf).scheme :=
  letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
    (projModelCode O hf) (chartOpen O hf i)
  letI := projChartAlgebra (f := f) R hR i
  Spec.map (chartEquiv R hR hf i).toRingEquiv.toCommRingCatIso.hom ≫
    (isAffineOpen_chartOpen hf i).fromSpec

instance (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    IsOpenImmersion (chartι R hR hf i) := by
  unfold chartι
  infer_instance

lemma opensRange_chartι (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
    (i : Fin (m + 1)) : (chartι R hR hf i).opensRange = chartOpen O hf i := by
  simp only [chartι]
  rw [Scheme.Hom.opensRange_comp_of_isIso, IsAffineOpen.opensRange_fromSpec]

set_option backward.isDefEq.respectTransparency false in
/-- The chart `Spec R[f j / f i] ⟶` (projective model) lies over `Spec O`. -/
theorem chartι_toSpec (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
    (i : Fin (m + 1)) :
    chartι R hR hf i ≫ (projModelCode O hf).toSpec =
      Spec.map (CommRingCat.ofHom (projChartAlgebra (f := f) R hR i).algebraMap) := by
  simp only [chartι]
  rw [Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec _ (isAffineOpen_top _)
    (isAffineOpen_chartOpen hf i) le_top, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
    (projModelCode O hf) (chartOpen O hf i)
  letI := projChartAlgebra (f := f) R hR i
  refine CommRingCat.hom_ext (RingHom.ext fun o ↦ ?_)
  have : ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ (projModelCode O hf).toSpec.appLE ⊤
      (chartOpen O hf i) le_top).hom o = algebraMap O _ o := by
    change _ = ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ (projModelCode O hf).toSpec.appTop ≫
      (projModelCode O hf).scheme.presheaf.map (homOfLE le_top).op).hom o
    rw [Scheme.Hom.appLE]
  change (chartEquiv R hR hf i) (((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
    (projModelCode O hf).toSpec.appLE ⊤ (chartOpen O hf i) le_top).hom o) = _
  rw [this, AlgEquiv.commutes]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma toImage_eq_SpecMap_chartHom' (hf : ∀ i, f i ≠ 0) (i : Fin (m + 1)) :
    (toProj O hf).toImage =
      Spec.map (chartHom' O hf i) ≫ (isAffineOpen_chartOpen hf i).fromSpec := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec (toProj O hf).toImage
    (isAffineOpen_chartOpen hf i) (isAffineOpen_top _) (top_le_toImage_preimage_chartOpen hf i)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  rw [chartHom', Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.id_comp]

/-- **The generic point factors through every chart**: `Spec F ⟶` (projective model) is
`Spec F ⟶ Spec R[f j / f i]` (the inclusion of the chart into `F`) followed by the chart. -/
theorem toImage_eq_SpecMap_comp_chartι (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)
    (i : Fin (m + 1)) :
    (toProj O hf).toImage =
      Spec.map (CommRingCat.ofHom (projChart R f i).subtype) ≫ chartι R hR hf i := by
  rw [toImage_eq_SpecMap_chartHom' hf i]
  simp only [chartι]
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

end ProjScheme

/-! ### Specialization -/

section Specialization

open ProjScheme

variable {K : Type u} [Field K] {O : ValuationSubring K} [Algebra K F] [Algebra O F]
  [IsScalarTower O K F] {Ω : Type u} [Field Ω] [Algebra K Ω] {V : ValuationSubring Ω}
  {hV : V.comap (algebraMap K Ω) = O}

lemma sp_congr {X : Scheme.{u}} {g : X ⟶ Spec (CommRingCat.of O)} [UniversallyClosed g]
    [IsSeparated g] {x x' : Spec (CommRingCat.of Ω) ⟶ X} (e : x = x') (hx) :
    sp g V hV x hx = sp g V hV x' (e ▸ hx) := by
  subst e
  rfl

omit [Algebra K F] [IsScalarTower O K F] [Algebra K Ω] in
set_option backward.isDefEq.respectTransparency false in
/-- The `Ω`-point `Spec Ω ⟶ Spec F ⟶` (projective model) factors through the chart
`Spec R[f k / f i]` when `R[f k / f i] ⊆ j⁻¹(V)`. -/
lemma SpecMap_toImage_eq {n : ℕ} {f : Fin (n + 1) → F} (R : Subring F)
    (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0) (j : F →+* Ω) (i : Fin (n + 1))
    (hi : projChart R f i ≤ (V.comap j).toSubring) :
    Spec.map (CommRingCat.ofHom j) ≫ (toProj O hf).toImage =
      Spec.map (CommRingCat.ofHom ((algebraMap V Ω).comp (chartToVal j V _ hi))) ≫
        chartι R hR hf i := by
  rw [toImage_eq_SpecMap_comp_chartι R hR hf i, ← Category.assoc, ← Spec.map_comp]
  congr 2

lemma chartToVal_comp_algebraMap {n : ℕ} {f : Fin (n + 1) → F} (R : Subring F)
    (hR : (algebraMap O F).range = R) (j : F →+* Ω)
    (hj : j.comp (algebraMap K F) = algebraMap K Ω) (i : Fin (n + 1))
    (hi : projChart R f i ≤ (V.comap j).toSubring) :
    letI := projChartAlgebra (f := f) R hR i
    (chartToVal j V _ hi).comp (algebraMap O (projChart R f i)) = valToVal O V hV := by
  refine RingHom.ext fun o ↦ Subtype.ext ?_
  rw [coe_valToVal, valToField, RingHom.comp_apply, ← hj, RingHom.comp_apply]
  change j (algebraMap O F o) = j (algebraMap K F (algebraMap O K o))
  rw [← IsScalarTower.algebraMap_apply]

/-- **Specialization on the projective model (M9b, compatibility with M3).** Let `j : F → Ω` be a
`K`-embedding and `V ⊆ Ω` a valuation subring over `O` such that the chart `R[f k / f i]` lies in
`W = j⁻¹(V)`. The `Ω`-point `Spec Ω ⟶ Spec F ⟶` (projective model) factors through the chart
(`SpecMap_toImage_eq`), and its specialization (`Models/Specialization.sp`) is the image under the
chart of the center `𝔪_W ∩ R[f k / f i]` of `W` (`asIdeal_comap_closedPoint`), whose local ring
is the Zariski specialization `localAt R[f k / f i] W` (`localAt_eq_localSubringOfPrime`). -/
theorem sp_projModelCode {n : ℕ} {f : Fin (n + 1) → F} (R : Subring F)
    (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0) (j : F →+* Ω)
    (hj : j.comp (algebraMap K F) = algebraMap K Ω) (i : Fin (n + 1))
    (hi : projChart R f i ≤ (V.comap j).toSubring) :
    letI := projChartAlgebra (f := f) R hR i
    (sp (projModelCode O hf).toSpec V hV
      (Spec.map (CommRingCat.ofHom ((algebraMap V Ω).comp (chartToVal j V _ hi))) ≫
        chartι R hR hf i)
      (chart_point_comp (hV := hV) _ _ (chartι_toSpec R hR hf i) _
        (chartToVal_comp_algebraMap (hV := hV) R hR j hj i hi)) : (projModelCode O hf).scheme) =
      chartι R hR hf i (PrimeSpectrum.comap (chartToVal j V _ hi) (IsLocalRing.closedPoint V)) :=
  sp_eq_of_chart _ _ (chartι_toSpec R hR hf i) _
    (chartToVal_comp_algebraMap (hV := hV) R hR j hj i hi)

end Specialization

end SemistableReduction
