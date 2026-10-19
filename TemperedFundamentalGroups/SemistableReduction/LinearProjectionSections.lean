/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LinearProjectionKer

/-!
# Sections of a linear projection over the charts of `ℙ¹`

For a linear projection `p = [ℓ₀ : ℓ₁] : Z ⟶ ℙ¹_O` of `ι : Z ⟶ ℙᵐ_O` (`LinearProjection.proj`):

* **`LinearProjection.preimage_proj_basicOpen`**: `p⁻¹ D₊(g) = ι⁻¹ D₊(g(ℓ₀, ℓ₁))` for `g`
  homogeneous of positive degree; in particular `p⁻¹ D₊(y_k) = V_k`;
* `LinearProjection.secZ k : (O[x]_{(ℓ_k)})₀ → Γ(Z, V_k)` (`a ↦ ι^*(a)`), with
  `secRes k a = (V_k).topIso.inv (secZ k a)` (`LinearProjection.secRes_eq`);
* **`LinearProjection.appLE_proj_awayToSection`**: pulling back a section `b` of `D₊(y_k)` along
  `p` gives `secZ k (b(ℓ₀, ℓ₁))`;
* `LinearProjection.res_secZ`: restriction of `secZ k a` to `ι⁻¹ D₊(ℓ_k g)` is
  `ι^*(awayMap a)`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace SemistableReduction

namespace LinearProjection

open TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {m : ℕ}

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

/-- `D₊(f) ≅ Spec (A_f)₀` on global sections sends `a` to `a`. -/
lemma basicOpenIsoSpec_hom_appTop {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {𝒜' : ℕ → Submodule R A} [GradedAlgebra 𝒜'] {f : A} {d : ℕ} (hf : f ∈ 𝒜' d) (hd : 0 < d)
    (b : Away 𝒜' f) :
    (Proj.basicOpenIsoSpec 𝒜' f hf hd).hom.appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜' f))).inv b) =
      (Proj.basicOpen 𝒜' f).topIso.inv (Proj.awayToSection 𝒜' f b) := by
  rw [Proj.basicOpenIsoSpec_hom, Scheme.Hom.appTop, Proj.basicOpenToSpec_app_top]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso _).inv, Iso.inv_hom_id, CommRingCat.id_apply]
  rfl

/-- The inverse of `D₊(f) ≅ Spec (A_f)₀` on global sections sends `a` to `a`. -/
lemma basicOpenIsoSpec_inv_appTop {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {𝒜' : ℕ → Submodule R A} [GradedAlgebra 𝒜'] {f : A} {d : ℕ} (hf : f ∈ 𝒜' d) (hd : 0 < d)
    (b : Away 𝒜' f) :
    (Proj.basicOpenIsoSpec 𝒜' f hf hd).inv.appTop
      ((Proj.basicOpen 𝒜' f).topIso.inv (Proj.awayToSection 𝒜' f b)) =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜' f))).inv b := by
  rw [← basicOpenIsoSpec_hom_appTop hf hd, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    Iso.inv_hom_id, Scheme.Hom.id_appTop, CommRingCat.id_apply]

variable (ℓ : Fin (1 + 1) → MvPolynomial (Fin (m + 1)) O)
  (hℓ : ∀ j, ℓ j ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O 1)
  {Z : Scheme.{u}} (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O))

/-- **Pulling back fractions to the chart `V_k`**: `ι^* : (O[x]_{(ℓ_k)})₀ → Γ(Z, V_k)`. -/
noncomputable def secZ (k : Fin (1 + 1)) :
    Away (𝒜 m) (linHom ℓ hℓ (X k)) →+* Γ(Z, V ℓ hℓ ι k) :=
  (ι.app (D ℓ hℓ k)).hom.comp (Proj.awayToSection (𝒜 m) (linHom ℓ hℓ (X k))).hom

lemma secRes_eq (k : Fin (1 + 1)) (a : Away (𝒜 m) (linHom ℓ hℓ (X k))) :
    secRes ℓ hℓ ι k a = (V ℓ hℓ ι k).topIso.inv (secZ ℓ hℓ ι k a) := by
  change (chartSpec ℓ hℓ ι k).appTop ((Scheme.ΓSpecIso _).inv a) = _
  rw [chartSpec, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, basicOpenIsoSpec_hom_appTop,
    Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply (D ℓ hℓ k).topIso.inv, Iso.inv_hom_id, CommRingCat.id_apply,
    Scheme.Hom.appLE_eq_app]
  rfl

/-- `Away.map` of the linear projection sends `g ^ d / s ^ e` to `φ(g) ^ d / φ(s) ^ e`. -/
lemma awayMap_isLocalizationElem {s g : MvPolynomial (Fin (1 + 1)) O} {d e : ℕ}
    (hs : s ∈ (𝒜 1) d) (hg : g ∈ (𝒜 1) e) :
    Away.map (linHom ℓ hℓ) s (Away.isLocalizationElem hs hg) =
      Away.isLocalizationElem ((linHom ℓ hℓ).map_mem hs) ((linHom ℓ hℓ).map_mem hg) := by
  rw [Away.map_mk]
  apply val_injective
  simp only [Away.val_mk, map_pow]
  rfl

variable {ℓ hℓ ι} (hcov : ∀ z : Z, ι z ∈ D ℓ hℓ 0 ∨ ι z ∈ D ℓ hℓ 1)

lemma proj_apply (k : Fin (1 + 1)) (x : V ℓ hℓ ι k) :
    proj ℓ hℓ ι hcov x.1 = Proj.awayι (𝒜 1) (X k) (X_mem' k) one_pos
      (Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k))) (chartSpec ℓ hℓ ι k x)) := by
  have h := congrArg (fun f ↦ f x) (ι_proj ℓ hℓ ι hcov k)
  simp only [chartHom_eq, Scheme.Hom.comp_apply] at h
  exact h

/-- **Preimages of basic opens under the linear projection**: `p⁻¹ D₊(g) = ι⁻¹ D₊(g(ℓ))`. -/
lemma mem_preimage_basicOpen {g : MvPolynomial (Fin (1 + 1)) O} {d : ℕ} (hg : g ∈ (𝒜 1) d)
    (hd : 0 < d) (z : Z) :
    proj ℓ hℓ ι hcov z ∈ Proj.basicOpen (𝒜 1) g ↔
      ι z ∈ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ g) := by
  obtain ⟨j, hj⟩ : ∃ j, z ∈ V ℓ hℓ ι j := by
    rcases hcov z with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  let x : V ℓ hℓ ι j := ⟨z, hj⟩
  have e1 : ∀ P, Proj.awayι (𝒜 1) (X j) (X_mem' j) one_pos P ∈ Proj.basicOpen (𝒜 1) g ↔
      P ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem' j) hg) := fun P ↦
    SetLike.ext_iff.1 (Proj.awayι_preimage_basicOpen (𝒜 1) (X_mem' j) one_pos hg hd) P
  have e2 : ∀ P, Proj.awayι (𝒜 m) (linHom ℓ hℓ (X j)) ((linHom ℓ hℓ).map_mem (X_mem' j)) one_pos P ∈
      Proj.basicOpen (𝒜 m) (linHom ℓ hℓ g) ↔ P ∈ PrimeSpectrum.basicOpen
        (Away.isLocalizationElem ((linHom ℓ hℓ).map_mem (X_mem' j)) ((linHom ℓ hℓ).map_mem hg)) :=
    fun P ↦ SetLike.ext_iff.1 (Proj.awayι_preimage_basicOpen (𝒜 m)
      ((linHom ℓ hℓ).map_mem (X_mem' j)) one_pos ((linHom ℓ hℓ).map_mem hg) hd) P
  change proj ℓ hℓ ι hcov x.1 ∈ _ ↔ ι x.1 ∈ _
  rw [proj_apply, ← awayι_chartSpec, e1, e2]
  change Away.isLocalizationElem (X_mem' j) hg ∉ Ideal.comap _ _ ↔ _ ∉ _
  rw [Ideal.mem_comap]
  change Away.map (linHom ℓ hℓ) (X j) (Away.isLocalizationElem (X_mem' j) hg) ∉ _ ↔ _
  rw [awayMap_isLocalizationElem]

/-- **`p⁻¹ D₊(g) = ι⁻¹ D₊(g(ℓ₀, ℓ₁))`.** -/
lemma preimage_proj_basicOpen {g : MvPolynomial (Fin (1 + 1)) O} {d : ℕ} (hg : g ∈ (𝒜 1) d)
    (hd : 0 < d) :
    proj ℓ hℓ ι hcov ⁻¹ᵁ Proj.basicOpen (𝒜 1) g = ι ⁻¹ᵁ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ g) :=
  TopologicalSpace.Opens.ext (Set.ext fun z ↦ mem_preimage_basicOpen hcov hg hd z)

/-- **The preimages of the charts of `ℙ¹` are the `V_k`.** -/
lemma preimage_proj_U (k : Fin (1 + 1)) :
    proj ℓ hℓ ι hcov ⁻¹ᵁ Proj.basicOpen (𝒜 1) (X k) = V ℓ hℓ ι k :=
  preimage_proj_basicOpen hcov (X_mem' k) one_pos

lemma resLE_proj (k : Fin (1 + 1))
    (e : V ℓ hℓ ι k ≤ proj ℓ hℓ ι hcov ⁻¹ᵁ Proj.basicOpen (𝒜 1) (X k)) :
    (proj ℓ hℓ ι hcov).resLE (Proj.basicOpen (𝒜 1) (X k)) (V ℓ hℓ ι k) e =
      chartSpec ℓ hℓ ι k ≫ Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k))) ≫
        (Proj.basicOpenIsoSpec (𝒜 1) (X k) (X_mem' k) one_pos).inv := by
  rw [← cancel_mono (Proj.basicOpen (𝒜 1) (X k)).ι, Scheme.Hom.resLE_comp_ι, ι_proj, chartHom_eq]
  simp only [Category.assoc, Proj.basicOpenIsoSpec_inv_ι]

/-- **Pulling back sections of `D₊(y_k)` along the projection**: for `b ∈ (O[y]_{(y_k)})₀`,
`p^* b = ι^*(b(ℓ₀, ℓ₁))` on `V_k`. -/
lemma appLE_proj_awayToSection (k : Fin (1 + 1))
    (e : V ℓ hℓ ι k ≤ proj ℓ hℓ ι hcov ⁻¹ᵁ Proj.basicOpen (𝒜 1) (X k))
    (b : Away (𝒜 1) (X k : MvPolynomial (Fin (1 + 1)) O)) :
    (proj ℓ hℓ ι hcov).appLE (Proj.basicOpen (𝒜 1) (X k)) (V ℓ hℓ ι k) e
      (Proj.awayToSection (𝒜 1) (X k) b) = secZ ℓ hℓ ι k (Away.map (linHom ℓ hℓ) (X k) b) := by
  apply (V ℓ hℓ ι k).topIso.commRingCatIsoToRingEquiv.symm.injective
  change (V ℓ hℓ ι k).topIso.inv _ = (V ℓ hℓ ι k).topIso.inv _
  rw [← secRes_eq]
  have key : (V ℓ hℓ ι k).topIso.inv ((proj ℓ hℓ ι hcov).appLE (Proj.basicOpen (𝒜 1) (X k))
      (V ℓ hℓ ι k) e (Proj.awayToSection (𝒜 1) (X k) b)) =
      ((proj ℓ hℓ ι hcov).resLE (Proj.basicOpen (𝒜 1) (X k)) (V ℓ hℓ ι k) e).appTop
        ((Proj.basicOpen (𝒜 1) (X k)).topIso.inv (Proj.awayToSection (𝒜 1) (X k) b)) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply,
      CommRingCat.comp_apply, ← CommRingCat.comp_apply (Proj.basicOpen (𝒜 1) (X k)).topIso.inv,
      Iso.inv_hom_id, CommRingCat.id_apply]
  rw [key, resLE_proj]
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    CommRingCat.comp_apply, basicOpenIsoSpec_inv_appTop,
    ← CommRingCat.comp_apply _ (Spec.map _).appTop, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- **Restriction of `ι^* a` to a smaller basic open** `ι⁻¹ D₊(ℓ_k g)`. -/
lemma res_secZ (k : Fin (1 + 1)) {g x : MvPolynomial (Fin (m + 1)) O} {e : ℕ} (hg : g ∈ (𝒜 m) e)
    (hx : x = linHom ℓ hℓ (X k) * g) (hle : ι ⁻¹ᵁ Proj.basicOpen (𝒜 m) x ≤ V ℓ hℓ ι k)
    (a : Away (𝒜 m) (linHom ℓ hℓ (X k))) :
    Z.presheaf.map (homOfLE hle).op (secZ ℓ hℓ ι k a) =
      ι.app (Proj.basicOpen (𝒜 m) x) (Proj.awayToSection (𝒜 m) x (awayMap (𝒜 m) hg hx a)) := by
  have h1 := ConcreteCategory.congr_hom
    (Proj.awayMap_awayToSection (𝒜 m) (f := linHom ℓ hℓ (X k)) hg hx) a
  have h2 := ConcreteCategory.congr_hom
    (ι.naturality (homOfLE (Proj.basicOpen_mono (𝒜 m) _ _ ⟨g, hx⟩)).op)
    (Proj.awayToSection (𝒜 m) (linHom ℓ hℓ (X k)) a)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at h1 h2
  rw [h1, h2]
  rfl

/-- **`Γ(V_k) ≅ Γ(Z, p⁻¹ D₊(y_k))`.** -/
noncomputable def sectionsEquiv (k : Fin (1 + 1)) :
    Γ(V ℓ hℓ ι k, ⊤) ≃+* Γ(Z, proj ℓ hℓ ι hcov ⁻¹ᵁ Proj.basicOpen (𝒜 1) (X k)) :=
  ((V ℓ hℓ ι k).topIso ≪≫
    Z.presheaf.mapIso (eqToIso (preimage_proj_U hcov k)).op).commRingCatIsoToRingEquiv

lemma sectionsEquiv_secRes (k : Fin (1 + 1)) (a : Away (𝒜 m) (linHom ℓ hℓ (X k))) :
    sectionsEquiv hcov k (secRes ℓ hℓ ι k a) =
      Z.presheaf.map (homOfLE (preimage_proj_U hcov k).le).op (secZ ℓ hℓ ι k a) := by
  rw [secRes_eq]
  change ((V ℓ hℓ ι k).topIso.inv ≫ (V ℓ hℓ ι k).topIso.hom ≫
    Z.presheaf.map (eqToHom (preimage_proj_U hcov k)).op) _ = _
  rw [Iso.inv_hom_id_assoc]
  rfl

/-- **Compatibility with the pull-back of functions on the charts of `ℙ¹`**: under
`Γ(V_k) ≅ Γ(Z, p⁻¹ D₊(y_k))`, `baseRes k b` is `p^* b`. -/
lemma sectionsEquiv_baseRes (k : Fin (1 + 1))
    (b : Away (𝒜 1) (X k : MvPolynomial (Fin (1 + 1)) O)) :
    sectionsEquiv hcov k (baseRes ℓ hℓ ι k b) =
      (proj ℓ hℓ ι hcov).app (Proj.basicOpen (𝒜 1) (X k)) (Proj.awayToSection (𝒜 1) (X k) b) := by
  rw [baseRes, RingHom.comp_apply, sectionsEquiv_secRes,
    ← appLE_proj_awayToSection hcov k (preimage_proj_U hcov k).ge b, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_map, Scheme.Hom.appLE_eq_app]

end LinearProjection

end SemistableReduction
