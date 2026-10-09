/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateModel

/-!
# Naturality of maps to `Proj` and of the Tate model map (Blueprint §10.3.8, HarmonicTate)

* `Proj.comp_fromOfGlobalSections`: `g ≫ fromOfGlobalSections f = fromOfGlobalSections (g^* ∘ f)`
  (via `toBasicOpenOfGlobalSections_naturality` and the naturality of `basicOpenIsoSpecAway`).
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

end TemperedFundamentalGroups.TateModel
