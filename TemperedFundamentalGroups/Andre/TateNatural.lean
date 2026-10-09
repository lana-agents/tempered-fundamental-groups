/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateModel
import TemperedFundamentalGroups.SemistableReduction.ProjScheme

/-!
# Naturality of maps to `Proj` and of the Tate model map (Blueprint §10.3.8, HarmonicTate)

* `Proj.comp_fromOfGlobalSections`: `g ≫ fromOfGlobalSections f = fromOfGlobalSections (g^* ∘ f)`
  (via `toBasicOpenOfGlobalSections_naturality` and the naturality of `basicOpenIsoSpecAway`).
* `Proj.fromOfGlobalSections_Spec_eq`: on `Spec T`, if `f r` is a unit, the map is
  `Spec ((A_r)₀ → T) ≫ awayι r`.
* `TateModel.SpecMap_toProj`, `TateModel.SpecMap_toModel`: the point `[x : y : π]` and the map
  `j : Spec T → 𝒯` are natural in the `O`-algebra `T`.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Naturality of `basicOpenIsoSpecAway`. -/
lemma basicOpenIsoSpecAway_naturality {R R' : CommRingCat} (h : R ⟶ R') (x : R) :
    (Spec.map h).resLE (PrimeSpectrum.basicOpen x) (PrimeSpectrum.basicOpen (h x))
      (by intro p hp; exact hp) ≫ (basicOpenIsoSpecAway x).hom =
    (basicOpenIsoSpecAway (h x)).hom ≫
      Spec.map (CommRingCat.ofHom (Localization.awayMap h.hom x)) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away x))))]
  simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Scheme.Hom.resLE_comp_ι]
  have : (Localization.awayMap h.hom x).comp (algebraMap R (Localization.Away x)) =
      (algebraMap R' (Localization.Away (h x))).comp h.hom := IsLocalization.map_comp _
  rw [this, CommRingCat.ofHom_comp, Spec.map_comp, ← Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap]
  rfl

namespace Proj
variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

lemma resLE_homOfLE_resLE_toSpecΓ {X Y : Scheme} (g : Y ⟶ X) (x : Γ(X, ⊤)) :
    g.resLE (X.basicOpen x) (Y.basicOpen (g.appTop x)) (Scheme.preimage_basicOpen_top g x).ge ≫
      X.homOfLE (X.toSpecΓ_preimage_basicOpen x).ge ≫
      X.toSpecΓ.resLE (PrimeSpectrum.basicOpen x) (X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen x) le_rfl =
    Y.homOfLE (Y.toSpecΓ_preimage_basicOpen (g.appTop x)).ge ≫
      Y.toSpecΓ.resLE (PrimeSpectrum.basicOpen (g.appTop x))
        (Y.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen (g.appTop x)) le_rfl ≫
      (Spec.map g.appTop).resLE (PrimeSpectrum.basicOpen x)
        (PrimeSpectrum.basicOpen (g.appTop x)) (fun _ hp => hp) := by
  rw [← cancel_mono (Scheme.Opens.ι _)]
  rw [Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc,
    Scheme.Hom.resLE_comp_ι_assoc, Category.assoc, Category.assoc, Scheme.Hom.resLE_comp_ι,
    Scheme.Hom.resLE_comp_ι_assoc, Scheme.homOfLE_ι_assoc, Scheme.toSpecΓ_naturality]

lemma toBasicOpenOfGlobalSections_naturality {X Y : Scheme} (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d) :
    g.resLE (X.basicOpen (f t)) (Y.basicOpen (g.appTop (f t)))
        (Scheme.preimage_basicOpen_top g (f t)).ge ≫
      toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
    toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl h0d hd := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv,
    ← Scheme.Hom.resLE_eq_morphismRestrict]
  slice_lhs 1 3 => rw [resLE_homOfLE_resLE_toSpecΓ]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [basicOpenIsoSpecAway_naturality]
  simp only [Category.assoc]
  congr 3
  rw [← Category.assoc]
  refine congrArg (· ≫ (basicOpenIsoSpec 𝒜 t hd h0d).inv) ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp only [RingHom.comp_apply]
  rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_map]

lemma basicOpen_ι_fromOfGlobalSections {X : Scheme} (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r : A} {n : ℕ} (hn : 0 < n)
    (hr : r ∈ 𝒜 n) :
    (X.basicOpen (f r)).ι ≫ fromOfGlobalSections 𝒜 f hf =
      toBasicOpenOfGlobalSections 𝒜 f rfl hn hr ≫ (basicOpen 𝒜 r).ι :=
  (openCoverOfMapIrrelevantEqTop 𝒜 f hf).ι_glueMorphisms _ _ ⟨_, _, hn, hr⟩

/-- **Naturality of `fromOfGlobalSections`.** -/
lemma comp_fromOfGlobalSections {X Y : Scheme} (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤) :
    g ≫ fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) hf' := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 _ hf').hom_ext _ _ fun ri => ?_
  obtain ⟨n, r, hn, hr⟩ := ri
  refine Eq.trans ?_ (basicOpen_ι_fromOfGlobalSections 𝒜 _ hf' hn hr).symm
  rw [← toBasicOpenOfGlobalSections_naturality 𝒜 g f hn hr, Category.assoc,
    ← basicOpen_ι_fromOfGlobalSections 𝒜 f hf hn hr, Scheme.Hom.resLE_comp_ι_assoc]
  rfl

/-- If `f r` is a unit, `fromOfGlobalSections` is the map through `D₊(r)`. -/
lemma fromOfGlobalSections_eq_of_isUnit {X : Scheme} (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r : A} {n : ℕ} (hn : 0 < n)
    (hr : r ∈ 𝒜 n) (hu : IsUnit (f r)) :
    fromOfGlobalSections 𝒜 f hf =
      X.topIso.inv ≫ (X.isoOfEq (X.basicOpen_of_isUnit hu)).inv ≫
        toBasicOpenOfGlobalSections 𝒜 f rfl hn hr ≫ (basicOpen 𝒜 r).ι := by
  rw [← basicOpen_ι_fromOfGlobalSections 𝒜 f hf hn hr, ← Category.assoc
    (X.isoOfEq _).inv, Scheme.isoOfEq_inv_ι, ← Category.assoc, Scheme.toIso_inv_ι,
    Category.id_comp]

/-- The prefix of `toBasicOpenOfGlobalSections` on an affine scheme when `f r` is a unit. -/
lemma prefix_eq {T : CommRingCat} (x : Γ(Spec T, ⊤)) (hu : IsUnit x)
    (hu' : IsUnit ((Scheme.ΓSpecIso T).hom.hom x)) :
    (Spec T).topIso.inv ≫ ((Spec T).isoOfEq ((Spec T).basicOpen_of_isUnit hu)).inv ≫
        ((Spec T).isoOfEq ((Spec T).toSpecΓ_preimage_basicOpen x)).inv ≫
        (Spec T).toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫ (basicOpenIsoSpecAway x).hom =
      Spec.map (CommRingCat.ofHom (Localization.awayLift (Scheme.ΓSpecIso T).hom.hom x hu')) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap Γ(Spec T, ⊤)
    (Localization.Away x))))]
  simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap, morphismRestrict_ι,
    Scheme.isoOfEq_inv_ι_assoc, Scheme.toIso_inv_ι_assoc]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Localization.awayLift,
    IsLocalization.Away.lift_comp, CommRingCat.ofHom_hom]
  exact (SpecMap_ΓSpecIso_hom T).symm

/-- **`fromOfGlobalSections` on an affine scheme through a chart**: if `f r` is a unit, the map
`Spec T → Proj A` is `Spec ((A_r)₀ → T) ≫ awayι r`. -/
lemma fromOfGlobalSections_Spec_eq {T : CommRingCat} (f : A →+* Γ(Spec T, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {r : A} {n : ℕ} (hn : 0 < n)
    (hr : r ∈ 𝒜 n) (hu : IsUnit (f r)) (hu' : IsUnit ((Scheme.ΓSpecIso T).hom.hom (f r))) :
    fromOfGlobalSections 𝒜 f hf =
      Spec.map (CommRingCat.ofHom ((Localization.awayLift ((Scheme.ΓSpecIso T).hom.hom.comp f) r
        hu').comp (algebraMap (HomogeneousLocalization.Away 𝒜 r) (Localization.Away r)))) ≫
        awayι 𝒜 r hr hn := by
  rw [fromOfGlobalSections_eq_of_isUnit 𝒜 f hf hn hr hu, ← basicOpenIsoSpec_inv_ι]
  simp only [toBasicOpenOfGlobalSections, Category.assoc]
  slice_lhs 1 5 => rw [prefix_eq (f r) hu hu']
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  rw [← RingHom.comp_assoc]
  congr 1
  refine congrArg (fun F => RingHom.comp F (algebraMap (HomogeneousLocalization.Away 𝒜 r)
    (Localization.Away r))) ?_
  apply IsLocalization.ringHom_ext (M := Submonoid.powers r) (S := Localization.Away r)
  ext a
  simp [Localization.awayLift, IsLocalization.Away.lift, IsLocalization.map_eq,
    IsLocalization.lift_eq]

end Proj

end AlgebraicGeometry

namespace TemperedFundamentalGroups.TateModel

open AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] (π b₄ b₆ : O)
  {T T' : Type u} [CommRing T] [CommRing T'] (φ : O →+* T) (x y : T) (g : T →+* T')

/-- **The point `[x : y : π]` is natural in `T`.** -/
lemma SpecMap_toProj (hπ : IsUnit (φ π)) (hπ' : IsUnit ((g.comp φ) π)) :
    Spec.map (CommRingCat.ofHom g) ≫ toProj π φ x y hπ = toProj π (g.comp φ) (g x) (g y) hπ' := by
  have hev : (Spec.map (CommRingCat.ofHom g)).appTop.hom.comp (evalΓ π φ x y) =
      evalΓ π (g.comp φ) (g x) (g y) := by
    have hnat : ∀ z : T, (Spec.map (CommRingCat.ofHom g)).appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom z) =
        (Scheme.ΓSpecIso (CommRingCat.of T')).inv.hom (g z) := fun z =>
      (congrArg (fun F => F.hom z) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))).symm
    ext p
    · simp only [evalΓ, evalPt, RingHom.comp_apply, hnat, eval₂Hom_C]
    · simp only [evalΓ, evalPt, RingHom.comp_apply, hnat, eval₂Hom_X']
      fin_cases p <;> simp
  have aux : ∀ (f₁ f₂ : MvPolynomial (Fin (2 + 1)) O →+* Γ(Spec (CommRingCat.of T'), ⊤))
      (_ : f₁ = f₂) hf₁ hf₂, Proj.fromOfGlobalSections (homogeneousSubmodule (Fin (2 + 1)) O)
        f₁ hf₁ = Proj.fromOfGlobalSections _ f₂ hf₂ := by
    rintro _ _ rfl _ _; rfl
  exact (Proj.comp_fromOfGlobalSections _ _ _ (map_irrelevant_evalΓ π φ x y hπ)
    (by rw [hev]; exact map_irrelevant_evalΓ π _ _ _ hπ')).trans (aux _ _ hev _ _)


/-- **The map `j : Spec T → 𝒯` is natural in `T`.** -/
lemma SpecMap_toModel [IsReduced T] [IsReduced T']
    (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆)) (hπ : IsUnit (φ π))
    (heq' : g y ^ 2 + g x * g y = g x ^ 3 + (g.comp φ) (π ^ 2 * b₄) * g x +
      (g.comp φ) (π ^ 2 * b₆)) (hπ' : IsUnit ((g.comp φ) π)) :
    Spec.map (CommRingCat.ofHom g) ≫ toModel π b₄ b₆ φ heq hπ =
      toModel π b₄ b₆ (g.comp φ) heq' hπ' := by
  rw [← cancel_mono (ι π b₄ b₆), Category.assoc, toModel_ι, toModel_ι, SpecMap_toProj]


/-- **The point `[x : y : π]` is the projective point of `(x/π, y/π, 1)`** (comparison of
`TateModel.toProj` with `ProjScheme.toProj` over a field). -/
lemma toProj_eq_projScheme {F : Type u} [Field F] [Algebra O F] (x y : F)
    (hπ : IsUnit (algebraMap O F π))
    (hf : ∀ i, (![x / algebraMap O F π, y / algebraMap O F π, 1] : Fin (2 + 1) → F) i ≠ 0) :
    toProj π (algebraMap O F) x y hπ = SemistableReduction.ProjScheme.toProj O hf := by
  have hu : IsUnit (evalΓ π (algebraMap O F) x y (X 2)) := by
    simp only [evalΓ, evalPt, RingHom.comp_apply, eval₂Hom_X']
    exact hπ.map _
  have hu' : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
      (evalΓ π (algebraMap O F) x y (X 2))) := hu.map _
  rw [toProj, Proj.fromOfGlobalSections_Spec_eq _ _ _ one_pos
    (SemistableReduction.ProjScheme.X_mem (O := O) (m := 2) 2) hu hu',
    SemistableReduction.ProjScheme.toProj_eq (O := O) hf 2]
  congr 2
  ext a
  obtain ⟨n, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _
    (SemistableReduction.ProjScheme.X_mem (O := O) (m := 2) 2) a
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, SemistableReduction.ProjScheme.awayEval_mk,
    evalΓ]
  rw [Localization.mk_eq_mk', Localization.awayLift, IsLocalization.Away.lift,
    IsLocalization.lift_mk'_spec]
  simp only [RingHom.comp_apply, Iso.inv_hom_id_apply]
  have hn : g.IsHomogeneous n := by
    have := (mem_homogeneousSubmodule _ _).1 hg
    simpa using this
  have hv : (![x, y, algebraMap O F π] : Fin (2 + 1) → F) = fun i =>
      algebraMap O F π *
        (![x / algebraMap O F π, y / algebraMap O F π, 1] : Fin (2 + 1) → F) i := by
    funext i
    fin_cases i <;> simp [mul_div_cancel₀ _ hπ.ne_zero]
  simp only [evalPt, coe_eval₂Hom, SemistableReduction.ProjScheme.evalHom, map_pow, eval₂_X]
  rw [hv, eval₂_mul_of_isHomogeneous hn]
  simp [mul_comm]

end TemperedFundamentalGroups.TateModel
