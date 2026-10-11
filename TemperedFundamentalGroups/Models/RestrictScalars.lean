/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.RingTheory.Ideal.GoingUp
import Oka.RingTheory.MvPolynomial.HomogeneousLocalization
import TemperedFundamentalGroups.Models.BaseChange

/-!
# Restriction of scalars of model codes (Blueprint §11, F8)

Let `f : R₀ →+* R₁` be finite, with `R₀`-module generators `b₀, …, bₙ` of `R₁`. The graded
ring map

`R₀[y_{(i, j)}] → R₁[x₀, …, xₘ]`, `y_{(i, j)} ↦ bᵢ xⱼ`

is surjective in positive degrees (`ProjEmb.surj`), so `Proj` of it is a **closed immersion**
`ProjEmb.emb : ℙᵐ_{R₁} ⟶ ℙᴺ_{R₀}` over `Spec R₁ ⟶ Spec R₀` (`N + 1 = (n + 1)(m + 1)`). Hence
every model code over `R₁` (a closed subscheme of `ℙᵐ_{R₁}`) is also a model code over `R₀`:
`ModelCode.restrictScalars`, with an isomorphism of schemes `ModelCode.rsIso` compatible with
the structure morphisms. If `R₀`, `R₁` are local and `f` is local, the special fibres agree
(`ModelCode.rsSpecialHomeo`).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjEmb

variable {R₀ R₁ : Type u} [CommRing R₀] [CommRing R₁] (f : R₀ →+* R₁) (n m : ℕ)
  (b : Fin (n + 1) → R₁)

/-- The indexing of the variables of `ℙᴺ`, `N + 1 = (n + 1)(m + 1)`. -/
def idx : Fin (n * (m + 1) + m + 1) ≃ Fin (n + 1) × Fin (m + 1) :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

/-- The images `bᵢ xⱼ` of the variables. -/
noncomputable def gen (k : Fin (n * (m + 1) + m + 1)) : MvPolynomial (Fin (m + 1)) R₁ :=
  C (b (idx n m k).1) * X (idx n m k).2

lemma gen_isHomogeneous (k : Fin (n * (m + 1) + m + 1)) : (gen n m b k).IsHomogeneous 1 := by
  rw [gen]
  simpa using (isHomogeneous_C (Fin (m + 1)) (b (idx n m k).1)).mul (isHomogeneous_X R₁ _)

/-- The ring map `R₀[y] → R₁[x]`, `y_{(i, j)} ↦ bᵢ xⱼ`. -/
noncomputable def polyMap :
    MvPolynomial (Fin (n * (m + 1) + m + 1)) R₀ →+* MvPolynomial (Fin (m + 1)) R₁ :=
  eval₂Hom (C.comp f) (gen n m b)

lemma polyMap_C (r : R₀) : polyMap f n m b (C r) = C (f r) := by
  simp [polyMap]

lemma polyMap_X (k : Fin (n * (m + 1) + m + 1)) : polyMap f n m b (X k) = gen n m b k := by
  simp [polyMap]

/-- `polyMap` as a graded ring map. -/
noncomputable def gradedMap :
    homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ →+*ᵍ
      homogeneousSubmodule (Fin (m + 1)) R₁ where
  __ := polyMap f n m b
  map_mem {i x} hx := by
    have h := ((mem_homogeneousSubmodule _ _).mp hx).eval₂ (C.comp f) (gen n m b)
      (fun r => isHomogeneous_C _ _) (gen_isHomogeneous n m b)
    rw [one_mul] at h
    exact h

lemma gradedMap_apply (p : MvPolynomial (Fin (n * (m + 1) + m + 1)) R₀) :
    gradedMap f n m b p = polyMap f n m b p := rfl

variable {f n m b}
variable (hb : ∀ c : R₁, ∃ r : Fin (n + 1) → R₀, ∑ i, f (r i) * b i = c)
include hb

/-- `c xⱼ` is the image of a linear form. -/
lemma exists_deg_one (c : R₁) (j : Fin (m + 1)) :
    ∃ a ∈ homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ 1,
      polyMap f n m b a = C c * X j := by
  obtain ⟨r, hr⟩ := hb c
  refine ⟨∑ i, C (r i) * X ((idx n m).symm (i, j)), ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    simpa using (isHomogeneous_C _ (r i)).mul (isHomogeneous_X R₀ ((idx n m).symm (i, j)))
  · rw [map_sum, ← hr, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, polyMap_C, polyMap_X, gen, Equiv.apply_symm_apply, C_mul, mul_assoc]

/-- Monomials (with coefficient `1`) are images of homogeneous polynomials of the same degree. -/
lemma exists_monomial_one (d : ℕ) (μ : Fin (m + 1) →₀ ℕ) (hμ : μ.degree = d) :
    ∃ a ∈ homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ d,
      polyMap f n m b a = monomial μ 1 := by
  induction d generalizing μ with
  | zero =>
    have : μ = 0 := by
      ext j
      have := (Finsupp.degree_eq_zero_iff μ).1 hμ
      simp [this]
    subst this
    exact ⟨1, SetLike.GradedOne.one_mem, by simp⟩
  | succ d ih =>
    obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
      by_contra! h
      have : μ = 0 := Finsupp.ext h
      simp [this] at hμ
    set μ' := μ - Finsupp.single j 1 with hμ'
    have hsum : μ = μ' + Finsupp.single j 1 := by
      ext k
      simp only [hμ', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
      by_cases hk : k = j
      · subst hk
        simp only [Finsupp.single_eq_same]
        omega
      · simp [Finsupp.single_eq_of_ne hk]
    have hdeg : μ'.degree = d := by
      have := congrArg Finsupp.degree hsum
      rw [map_add, Finsupp.degree_single, hμ] at this
      omega
    obtain ⟨a', ha', ha'e⟩ := ih μ' hdeg
    obtain ⟨a₁, ha₁, ha₁e⟩ := exists_deg_one hb 1 j
    refine ⟨a' * a₁, SetLike.GradedMul.mul_mem ha' ha₁, ?_⟩
    rw [map_mul, ha'e, ha₁e, C_1, one_mul, X, monomial_mul, one_mul, ← hsum]

/-- **`polyMap` is surjective in positive degrees.** -/
lemma surj (d : ℕ) (p : MvPolynomial (Fin (m + 1)) R₁)
    (hp : p ∈ homogeneousSubmodule (Fin (m + 1)) R₁ (d + 1)) :
    ∃ a ∈ homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ (d + 1),
      polyMap f n m b a = p := by
  let S : AddSubmonoid (MvPolynomial (Fin (m + 1)) R₁) :=
    (homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ (d + 1)).toAddSubmonoid.map
      (polyMap f n m b).toAddMonoidHom
  suffices p ∈ S by
    obtain ⟨a, ha, rfl⟩ := this
    exact ⟨a, ha, rfl⟩
  rw [p.as_sum]
  refine AddSubmonoid.sum_mem _ fun μ hμ => ?_
  have hdeg : μ.degree = d + 1 := by
    rw [Finsupp.degree_eq_weight_one]
    exact (mem_homogeneousSubmodule _ _).1 hp (mem_support_iff.1 hμ)
  obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
    by_contra! h
    have : μ = 0 := Finsupp.ext h
    simp [this] at hdeg
  set μ' := μ - Finsupp.single j 1 with hμ'
  have hsum : μ = μ' + Finsupp.single j 1 := by
    ext k
    simp only [hμ', Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply]
    by_cases hk : k = j
    · subst hk
      simp only [Finsupp.single_eq_same]
      omega
    · simp [Finsupp.single_eq_of_ne hk]
  have hdeg' : μ'.degree = d := by
    have := congrArg Finsupp.degree hsum
    rw [map_add, Finsupp.degree_single, hdeg] at this
    omega
  obtain ⟨a', ha', ha'e⟩ := exists_monomial_one hb d μ' hdeg'
  obtain ⟨a₁, ha₁, ha₁e⟩ := exists_deg_one hb (coeff μ p) j
  refine ⟨a' * a₁, SetLike.GradedMul.mul_mem ha' ha₁, ?_⟩
  change polyMap f n m b (a' * a₁) = _
  rw [map_mul, ha'e, ha₁e, ← monomial_zero', X, monomial_mul, monomial_mul, one_mul, zero_add,
    ← hsum, mul_one]

lemma irrelevant_le :
    HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin (m + 1)) R₁) ≤
      (HomogeneousIdeal.irrelevant
        (homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀)).map (gradedMap f n m b) := by
  intro p hp
  change p ∈ (HomogeneousIdeal.map _ _).toIdeal
  rw [HomogeneousIdeal.toIdeal_map]
  have h1 : p ∈ Ideal.span (X '' Set.univ) := by
    rw [mem_ideal_span_X_image]
    intro μ hμ
    by_contra! h
    have : μ = 0 := Finsupp.ext fun i ↦ h i (Set.mem_univ i)
    subst this
    exact (mem_support_iff.mp hμ) ((ProjectiveSpace.mem_irrelevant_iff_coeff_zero p).mp hp)
  refine Ideal.span_le.mpr ?_ h1
  rintro _ ⟨j, -, rfl⟩
  obtain ⟨a, ha, hae⟩ := surj hb 0 (X j) (X_mem_homogeneousSubmodule_one j)
  rw [← hae]
  refine Ideal.mem_map_of_mem (gradedMap f n m b) ?_
  change a ∈ HomogeneousIdeal.irrelevant _
  rw [ProjectiveSpace.mem_irrelevant_iff_coeff_zero]
  exact ((mem_homogeneousSubmodule _ _).1 ha).coeff_eq_zero (by simp)

variable (m) in
/-- **The closed immersion** `ℙᵐ_{R₁} ⟶ ℙᴺ_{R₀}`. -/
noncomputable def emb : projSpace R₁ m ⟶ projSpace R₀ (n * (m + 1) + m) :=
  Proj.map (gradedMap f n m b) (irrelevant_le hb)

/-- `polyMap` on the degree-zero localizations at a variable is surjective. -/
lemma awayMap_surjective (k : Fin (n * (m + 1) + m + 1)) :
    Function.Surjective (Away.map (gradedMap f n m b) (X k)) := by
  intro x
  have hk := X_mem_homogeneousSubmodule_one (R := R₀) k
  obtain ⟨d, a, ha, rfl⟩ := Away.mk_surjective _ (GradedRingHom.map_mem (gradedMap f n m b) hk) x
  obtain ⟨a', ha', hae⟩ := surj hb d (a * gradedMap f n m b (X k)) (by
    have := SetLike.GradedMul.mul_mem ha (GradedRingHom.map_mem (gradedMap f n m b) hk)
    simpa using this)
  refine ⟨Away.mk _ hk (d + 1) a' (by simpa using ha'), ?_⟩
  rw [Away.map_mk]
  apply val_injective
  simp only [Away.val_mk]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [gradedMap_apply] at hae ⊢
  simp only [hae, OneMemClass.coe_one, one_mul]
  change polyMap f n m b (X k) ^ d * _ = _
  ring

lemma isClosedImmersion_map :
    IsClosedImmersion (Proj.map (gradedMap f n m b) (irrelevant_le hb)) := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsClosedImmersion)
    (fun k => Proj.basicOpen _ (X k)) ?_ fun k => ?_
  · exact Proj.iSup_basicOpen_eq_top' _ _ (fun k => ⟨1, X_mem_homogeneousSubmodule_one k⟩)
      (adjoin_range_X_gradeZero_eq_top R₀ _)
  · have hk := X_mem_homogeneousSubmodule_one (R := R₀) k
    have hg := GradedRingHom.map_mem (gradedMap f n m b) hk
    have h1 := Proj.awayι_comp_map (gradedMap f n m b) (irrelevant_le hb) one_pos (X k) hk
    let L := Scheme.isoOfEq _ (Proj.map_preimage_basicOpen (gradedMap f n m b)
      (irrelevant_le hb) (X k)) ≪≫ Proj.basicOpenIsoSpec _ _ hg one_pos
    have h2 : L.inv ≫
        (Proj.map (gradedMap f n m b) (irrelevant_le hb) ∣_ Proj.basicOpen _ (X k)) =
        Spec.map (CommRingCat.ofHom (Away.map (gradedMap f n m b) (X k))) ≫
          (Proj.basicOpenIsoSpec _ (X k) hk one_pos).inv := by
      rw [← cancel_mono (Proj.basicOpen _ (X k)).ι, Category.assoc, Category.assoc,
        morphismRestrict_ι, Proj.basicOpenIsoSpec_inv_ι, ← h1, Iso.trans_inv, Category.assoc,
        Scheme.isoOfEq_inv_ι_assoc, Proj.basicOpenIsoSpec_inv_ι_assoc]
    have w : L.hom ≫ Spec.map (CommRingCat.ofHom (Away.map (gradedMap f n m b) (X k))) =
        (Proj.map (gradedMap f n m b) (irrelevant_le hb) ∣_ Proj.basicOpen _ (X k)) ≫
          (Proj.basicOpenIsoSpec _ (X k) hk one_pos).hom := by
      rw [← cancel_epi L.inv, Iso.inv_hom_id_assoc, reassoc_of% h2, Iso.inv_hom_id,
        Category.comp_id]
    have e : Arrow.mk (Proj.map (gradedMap f n m b) (irrelevant_le hb) ∣_
        Proj.basicOpen _ (X k)) ≅
        Arrow.mk (Spec.map (CommRingCat.ofHom (Away.map (gradedMap f n m b) (X k)))) :=
      Arrow.isoMk L (Proj.basicOpenIsoSpec _ (X k) hk one_pos) w
    exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion e).2
      (IsClosedImmersion.spec_of_surjective _ (awayMap_surjective hb k))

/-- **`emb` is a closed immersion.** -/
instance : IsClosedImmersion (emb m hb) := isClosedImmersion_map hb

lemma awayι_map_toSpec {i : ℕ} (hi : 0 < i) {s : MvPolynomial (Fin (n * (m + 1) + m + 1)) R₀}
    (hs : s ∈ homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ i) :
    Proj.awayι _ (gradedMap f n m b s) (GradedRingHom.map_mem _ hs) hi ≫
      Proj.map (gradedMap f n m b) (irrelevant_le hb) ≫
      (Proj.toSpecZero (homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap R₀ (homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ 0)))) =
    Proj.awayι _ (gradedMap f n m b s) (GradedRingHom.map_mem _ hs) hi ≫
      ((Proj.toSpecZero (homogeneousSubmodule (Fin (m + 1)) R₁) ≫ Spec.map (CommRingCat.ofHom
        (algebraMap R₁ (homogeneousSubmodule (Fin (m + 1)) R₁ 0)))) ≫
      Spec.map (CommRingCat.ofHom f)) := by
  rw [Proj.awayι_comp_map_assoc _ _ hi s hs]
  simp only [Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  simp only [RingHom.comp_apply, fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, HomogeneousLocalization.Away.map, HomogeneousLocalization.map_mk, val_mk]
  congr 1
  · exact polyMap_C f n m b r
  · exact Subtype.ext (map_one (gradedMap f n m b))

lemma map_toSpec : Proj.map (gradedMap f n m b) (irrelevant_le hb) ≫
    (Proj.toSpecZero (homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap R₀ (homogeneousSubmodule (Fin (n * (m + 1) + m + 1)) R₀ 0)))) =
    (Proj.toSpecZero (homogeneousSubmodule (Fin (m + 1)) R₁) ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R₁ (homogeneousSubmodule (Fin (m + 1)) R₁ 0)))) ≫
      Spec.map (CommRingCat.ofHom f) :=
  (Proj.mapAffineOpenCover (gradedMap f n m b) (irrelevant_le hb)).openCover.hom_ext _ _
    fun s => awayι_map_toSpec hb s.1.2 s.2.2

/-- `emb` lies over `Spec R₁ ⟶ Spec R₀`. -/
@[reassoc]
lemma emb_toSpec : emb m hb ≫ projSpace.toSpec R₀ (n * (m + 1) + m) =
    projSpace.toSpec R₁ m ≫ Spec.map (CommRingCat.ofHom f) :=
  map_toSpec hb

end ProjEmb

namespace ProjEmb

/-- A finite ring map has `R₀`-module generators `b₀, …, bₙ`. -/
lemma exists_gen {R₀ R₁ : Type u} [CommRing R₀] [CommRing R₁] (f : R₀ →+* R₁) (hf : f.Finite) :
    ∃ (n : ℕ) (b : Fin (n + 1) → R₁), ∀ c : R₁, ∃ r : Fin (n + 1) → R₀,
      ∑ i, f (r i) * b i = c := by
  letI := f.toAlgebra
  have : Module.Finite R₀ R₁ := hf
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R₀) (M := R₁)
  refine ⟨n, Fin.cons 1 s, fun c => ?_⟩
  have hc : c ∈ Submodule.span R₀ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun R₀).1 hc
  refine ⟨Fin.cons 0 r, ?_⟩
  rw [Fin.sum_univ_succ]
  simp [← hr, Algebra.smul_def, RingHom.algebraMap_toAlgebra]

end ProjEmb

namespace ModelCode

variable {R₀ R₁ : Type u} [CommRing R₀] [CommRing R₁] {f : R₀ →+* R₁} (hf : f.Finite)
  (c : ModelCode R₁)

/-- The number of chosen generators (minus one). -/
noncomputable def rsN : ℕ := (ProjEmb.exists_gen f hf).choose

/-- The chosen `R₀`-module generators of `R₁`. -/
noncomputable def rsB : Fin (rsN hf + 1) → R₁ := (ProjEmb.exists_gen f hf).choose_spec.choose

lemma rsB_spec : ∀ c : R₁, ∃ r : Fin (rsN hf + 1) → R₀, ∑ i, f (r i) * rsB hf i = c :=
  (ProjEmb.exists_gen f hf).choose_spec.choose_spec

/-- The closed immersion `c ⟶ ℙᵐ_{R₁} ⟶ ℙᴺ_{R₀}`. -/
noncomputable abbrev rsι : c.scheme ⟶ projSpace R₀ (rsN hf * (c.m + 1) + c.m) :=
  c.I.subschemeι ≫ ProjEmb.emb c.m (rsB_spec hf)

instance : IsClosedImmersion (c.rsι hf) :=
  @IsClosedImmersion.comp _ _ _ c.I.subschemeι _ inferInstance inferInstance

/-- **Restriction of scalars of a model code** along a finite ring map: the same scheme, as a
closed subscheme of `ℙᴺ_{R₀}`. -/
noncomputable def restrictScalars : ModelCode R₀ :=
  ⟨rsN hf * (c.m + 1) + c.m, (c.rsι hf).ker⟩

/-- The model after restriction of scalars is isomorphic to the given one. -/
noncomputable def rsIso : c.scheme ≅ (c.restrictScalars hf).scheme :=
  @asIso _ _ _ _ (c.rsι hf).toImage (IsClosedImmersion.instIsIsoSchemeToImage (c.rsι hf))

lemma rsIso_hom_subschemeι :
    (c.rsIso hf).hom ≫ (c.restrictScalars hf).I.subschemeι = c.rsι hf :=
  Scheme.Hom.toImage_imageι _

/-- `rsIso` lies over `Spec R₁ ⟶ Spec R₀`. -/
@[reassoc]
lemma rsIso_hom_toSpec :
    (c.rsIso hf).hom ≫ (c.restrictScalars hf).toSpec = c.toSpec ≫ Spec.map (CommRingCat.ofHom f) := by
  rw [toSpec, ← Category.assoc, rsIso_hom_subschemeι]
  change (c.I.subschemeι ≫ ProjEmb.emb c.m (rsB_spec hf)) ≫ projSpace.toSpec R₀ _ =
    (c.I.subschemeι ≫ projSpace.toSpec R₁ c.m) ≫ _
  rw [Category.assoc, Category.assoc, ProjEmb.emb_toSpec]

@[reassoc]
lemma rsIso_inv_toSpec :
    (c.rsIso hf).inv ≫ c.toSpec ≫ Spec.map (CommRingCat.ofHom f) =
      (c.restrictScalars hf).toSpec := by
  rw [← rsIso_hom_toSpec, Iso.inv_hom_id_assoc]

section Local

/-- Only the closed point of `Spec R₁` lies over the closed point of `Spec R₀`. -/
lemma eq_closedPoint_of_map {R₀ R₁ : Type u} [CommRing R₀] [CommRing R₁] [IsLocalRing R₀]
    [IsLocalRing R₁] {f : R₀ →+* R₁} (hf : f.Finite) (x : Spec (CommRingCat.of R₁))
    (hx : Spec.map (CommRingCat.ofHom f) x = (IsLocalRing.closedPoint R₀ : PrimeSpectrum R₀)) :
    x = (IsLocalRing.closedPoint R₁ : PrimeSpectrum R₁) := by
  have hx' : PrimeSpectrum.comap f x = IsLocalRing.closedPoint R₀ := hx
  have hmax : (x.asIdeal.comap f).IsMaximal := by
    have := congrArg PrimeSpectrum.asIdeal hx'
    rw [PrimeSpectrum.comap_asIdeal] at this
    rw [this]
    exact IsLocalRing.maximalIdeal.isMaximal R₀
  have : x.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap' f hf.to_isIntegral _ hmax
  exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal this)

variable [IsLocalRing R₀] [IsLocalRing R₁] [IsLocalHom f]

lemma rsIso_hom_mem (z : specialFibre c.toSpec) :
    (c.rsIso hf).hom z.1 ∈ specialFibre (c.restrictScalars hf).toSpec := by
  rw [mem_specialFibre, ← Scheme.Hom.comp_apply, rsIso_hom_toSpec, Scheme.Hom.comp_apply,
    (mem_specialFibre _ _).1 z.2]
  exact Spec_closedPoint (f := CommRingCat.ofHom f)

omit [IsLocalHom f] in
lemma rsIso_inv_mem (z : specialFibre (c.restrictScalars hf).toSpec) :
    (c.rsIso hf).inv z.1 ∈ specialFibre c.toSpec := by
  have h : ((c.rsIso hf).inv ≫ c.toSpec ≫ Spec.map (CommRingCat.ofHom f)) z.1 =
      (IsLocalRing.closedPoint R₀ : PrimeSpectrum R₀) := by
    rw [rsIso_inv_toSpec]
    exact z.2
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at h
  exact eq_closedPoint_of_map hf _ h

/-- **The special fibres agree** after restriction of scalars. -/
noncomputable def rsSpecialHomeo :
    specialFibre c.toSpec ≃ₜ specialFibre (c.restrictScalars hf).toSpec where
  toFun z := ⟨(c.rsIso hf).hom z.1, c.rsIso_hom_mem hf z⟩
  invFun z := ⟨(c.rsIso hf).inv z.1, c.rsIso_inv_mem hf z⟩
  left_inv z := Subtype.ext (by
    change ((c.rsIso hf).hom ≫ (c.rsIso hf).inv) z.1 = z.1
    rw [Iso.hom_inv_id]
    rfl)
  right_inv z := Subtype.ext (by
    change ((c.rsIso hf).inv ≫ (c.rsIso hf).hom) z.1 = z.1
    rw [Iso.inv_hom_id]
    rfl)
  continuous_toFun := (((c.rsIso hf).hom.continuous.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (((c.rsIso hf).inv.continuous.comp continuous_subtype_val).subtype_mk _)

lemma coe_rsSpecialHomeo (z : specialFibre c.toSpec) :
    (c.rsSpecialHomeo hf z : (c.restrictScalars hf).scheme) = (c.rsIso hf).hom z.1 := rfl

lemma coe_rsSpecialHomeo_symm (z : specialFibre (c.restrictScalars hf).toSpec) :
    ((c.rsSpecialHomeo hf).symm z : c.scheme) = (c.rsIso hf).inv z.1 := rfl

end Local

end ModelCode

end TemperedFundamentalGroups
