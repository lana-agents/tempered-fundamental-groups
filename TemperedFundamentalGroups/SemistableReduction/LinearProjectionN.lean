/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Models.Projective

/-!
# Linear projections `ℙᵐ ⇢ ℙⁿ` restricted to schemes missing the centre

The generalisation of `SemistableReduction.LinearProjection` (`ℙᵐ ⇢ ℙ¹`) to `n + 1` linear
forms `ℓ₀, …, ℓₙ` in `O[x₀, …, xₘ]`:

* `LinearProjectionN.linHom ℓ : O[y₀, …, yₙ] →+*ᵍ O[x₀, …, xₘ]`, `y_j ↦ ℓ_j`;
* `chartMap ℓ s : D₊(ℓ(s)) ⟶ ℙⁿ_O` (`Spec` of `HomogeneousLocalization.Away.map`), compatible on
  overlaps (`chartMap_compat`) and over `Spec O` (`chartMap_toSpec`);
* for `ι : Z ⟶ ℙᵐ_O` missing the centre `V(ℓ₀, …, ℓₙ)` (`hcov`), the glued morphism
  **`proj ℓ ι hcov : Z ⟶ ℙⁿ_O`** with `proj_toSpec`;
* **`mem_proj_iff`**: for `g` homogeneous of positive degree, `g` vanishes at `proj z` iff
  `g(ℓ₀, …, ℓₙ)` vanishes at `ι z`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization Limits

namespace SemistableReduction

namespace LinearProjectionN

open TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {m n : ℕ}

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

lemma X_mem' (k : Fin (n + 1)) : (X k : MvPolynomial (Fin (n + 1)) O) ∈ (𝒜 n) 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O k)

/-- **The graded homomorphism `O[y₀, …, yₙ] → O[x₀, …, xₘ]`, `y_j ↦ ℓ_j`** for linear forms
`ℓ_j`. -/
noncomputable def linHom (ℓ : Fin (n + 1) → MvPolynomial (Fin (m + 1)) O)
    (hℓ : ∀ j, ℓ j ∈ (𝒜 m) 1) : (𝒜 n) →+*ᵍ (𝒜 m) where
  toRingHom := (aeval ℓ).toRingHom
  map_mem := by
    intro i x hx
    have hx' : x.IsHomogeneous i := (mem_homogeneousSubmodule _ _).1 hx
    have := hx'.aeval ℓ (fun j ↦ (mem_homogeneousSubmodule _ _).1 (hℓ j))
    rw [one_mul] at this
    exact (mem_homogeneousSubmodule _ _).2 this

variable (ℓ : Fin (n + 1) → MvPolynomial (Fin (m + 1)) O)
  (hℓ : ∀ j, ℓ j ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O 1)

@[simp]
lemma linHom_apply (x : MvPolynomial (Fin (n + 1)) O) : linHom ℓ hℓ x = aeval ℓ x := rfl

/-- The projection on the chart `D₊(ℓ(s))`. -/
noncomputable def chartMap (s : MvPolynomial (Fin (n + 1)) O) {d : ℕ} (hs : s ∈ (𝒜 n) d)
    (hd : 0 < d) :
    (Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)).toScheme ⟶ Proj (𝒜 n) :=
  (Proj.basicOpenIsoSpec (𝒜 m) (linHom ℓ hℓ s) ((linHom ℓ hℓ).map_mem hs) hd).hom ≫
    Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) s)) ≫ Proj.awayι (𝒜 n) s hs hd

lemma awayMap_comp_awayMap {s g x : MvPolynomial (Fin (n + 1)) O} {d e : ℕ} (hs : s ∈ (𝒜 n) d)
    (hg : g ∈ (𝒜 n) e) (hx : x = s * g) :
    (awayMap (𝒜 m) ((linHom ℓ hℓ).map_mem hg)
        (show linHom ℓ hℓ x = linHom ℓ hℓ s * linHom ℓ hℓ g by rw [hx, map_mul])).comp
      (Away.map (linHom ℓ hℓ) s) =
    (Away.map (linHom ℓ hℓ) x).comp (awayMap (𝒜 n) hg hx) := by
  ext z
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective (𝒜 n) hs z
  simp only [RingHom.coe_comp, Function.comp_apply, Away.map_mk, awayMap_mk, Away.val_mk,
    map_mul, map_pow]
  rfl

lemma homOfLE_chartMap {s g x : MvPolynomial (Fin (n + 1)) O} {d e : ℕ} (hs : s ∈ (𝒜 n) d)
    (hd : 0 < d) (hg : g ∈ (𝒜 n) e) (hx : x = s * g) (hxd : x ∈ (𝒜 n) (d + e))
    (hle : Proj.basicOpen (𝒜 m) (linHom ℓ hℓ x) ≤ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)) :
    (Proj (𝒜 m)).homOfLE hle ≫ chartMap ℓ hℓ s hs hd =
      chartMap ℓ hℓ x hxd (hd.trans_le (Nat.le_add_right d e)) := by
  have hx' : linHom ℓ hℓ x = linHom ℓ hℓ s * linHom ℓ hℓ g := by rw [hx, map_mul]
  have key := Proj.basicOpenToSpec_SpecMap_awayMap (𝒜 m)
    ((linHom ℓ hℓ).map_mem hg) hx' (f := linHom ℓ hℓ s)
  simp only [chartMap, Proj.basicOpenIsoSpec_hom]
  change (Proj (𝒜 m)).homOfLE hle ≫ _ = _
  rw [← Category.assoc ((Proj (𝒜 m)).homOfLE hle), ← key, Category.assoc,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    awayMap_comp_awayMap ℓ hℓ hs hg hx, CommRingCat.ofHom_comp, Spec.map_comp_assoc,
    Proj.SpecMap_awayMap_awayι (𝒜 n) hs hd hg hx]

lemma chartMap_compat {s g x : MvPolynomial (Fin (n + 1)) O} {d : ℕ} (hs : s ∈ (𝒜 n) d)
    (hg : g ∈ (𝒜 n) d) (hd : 0 < d) (hx : x = s * g) (hxd : x ∈ (𝒜 n) (d + d))
    (hle₁ : Proj.basicOpen (𝒜 m) (linHom ℓ hℓ x) ≤ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s))
    (hle₂ : Proj.basicOpen (𝒜 m) (linHom ℓ hℓ x) ≤ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ g)) :
    (Proj (𝒜 m)).homOfLE hle₁ ≫ chartMap ℓ hℓ s hs hd =
      (Proj (𝒜 m)).homOfLE hle₂ ≫ chartMap ℓ hℓ g hg hd := by
  rw [homOfLE_chartMap ℓ hℓ hs hd hg hx hxd,
    homOfLE_chartMap ℓ hℓ hg hd hs (hx.trans (mul_comm _ _)) hxd]

lemma chartMap_toSpec (s : MvPolynomial (Fin (n + 1)) O) {d : ℕ} (hs : s ∈ (𝒜 n) d)
    (hd : 0 < d) :
    chartMap ℓ hℓ s hs hd ≫ projSpace.toSpec O n =
      (Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)).ι ≫ projSpace.toSpec O m := by
  have hι : (Proj.basicOpen (𝒜 m) (linHom ℓ hℓ s)).ι =
      (Proj.basicOpenIsoSpec (𝒜 m) (linHom ℓ hℓ s) ((linHom ℓ hℓ).map_mem hs) hd).hom ≫
        Proj.awayι (𝒜 m) (linHom ℓ hℓ s) ((linHom ℓ hℓ).map_mem hs) hd := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  rw [hι]
  change chartMap ℓ hℓ s hs hd ≫ Proj.toSpecZero (𝒜 n) ≫ _ =
    _ ≫ Proj.toSpecZero (𝒜 m) ≫ _
  simp only [chartMap, Category.assoc]
  rw [Proj.awayι_toSpecZero_assoc, Proj.awayι_toSpecZero_assoc]
  congr 1
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext o
  change val (Away.map (linHom ℓ hℓ) s (fromZeroRingHom (𝒜 n) _ (algebraMap O _ o))) =
    val (fromZeroRingHom (𝒜 m) _ (algebraMap O _ o))
  simp only [fromZeroRingHom, Away.map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.map_mk, val_mk]
  simp [MvPolynomial.algebraMap_eq]

/-! ### The projection on a scheme missing the centre -/

variable {Z : Scheme.{u}} (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O))

/-- The basic open `D₊(ℓ_k)` of `ℙᵐ_O`. -/
noncomputable abbrev D (k : Fin (n + 1)) : (Proj (𝒜 m)).Opens :=
  Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X k))

/-- The chart `V_k = ι⁻¹ D₊(ℓ_k)` of `Z`. -/
noncomputable abbrev V (k : Fin (n + 1)) : Z.Opens := ι ⁻¹ᵁ D ℓ hℓ k

/-- The projection on the chart `V_k`. -/
noncomputable def chartHom (k : Fin (n + 1)) : (V ℓ hℓ ι k).toScheme ⟶ Proj (𝒜 n) :=
  ι.resLE (D ℓ hℓ k) (V ℓ hℓ ι k) le_rfl ≫ chartMap ℓ hℓ (X k) (X_mem' k) one_pos

variable {ℓ hℓ ι} in
lemma isOpenCover_V (hcov : ∀ z : Z, ∃ k, ι z ∈ D ℓ hℓ k) :
    TopologicalSpace.IsOpenCover (V ℓ hℓ ι) := by
  refine top_le_iff.1 fun z _ ↦ ?_
  rw [TopologicalSpace.Opens.mem_iSup]
  obtain ⟨k, h⟩ := hcov z
  exact ⟨k, h⟩

/-- The open cover of `Z` by the charts `V_k`. -/
noncomputable def cover (hcov : ∀ z : Z, ∃ k, ι z ∈ D ℓ hℓ k) : Z.OpenCover :=
  Z.openCoverOfIsOpenCover (V ℓ hℓ ι) (isOpenCover_V hcov)

lemma D_mul_le_left (a b : Fin (n + 1)) :
    Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X a * X b)) ≤ D ℓ hℓ a := by
  rw [map_mul, Proj.basicOpen_mul]
  exact inf_le_left

lemma D_mul_le_right (a b : Fin (n + 1)) :
    Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X a * X b)) ≤ D ℓ hℓ b := by
  rw [map_mul, Proj.basicOpen_mul]
  exact inf_le_right

lemma V_inf_le (a b : Fin (n + 1)) :
    V ℓ hℓ ι a ⊓ V ℓ hℓ ι b ≤ ι ⁻¹ᵁ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X a * X b)) := by
  rw [map_mul, Proj.basicOpen_mul]
  exact le_rfl

lemma chartHom_compat (a b : Fin (n + 1)) :
    Z.homOfLE (inf_le_left : V ℓ hℓ ι a ⊓ V ℓ hℓ ι b ≤ _) ≫ chartHom ℓ hℓ ι a =
      Z.homOfLE (inf_le_right : V ℓ hℓ ι a ⊓ V ℓ hℓ ι b ≤ _) ≫ chartHom ℓ hℓ ι b := by
  simp only [chartHom, Scheme.Hom.map_resLE_assoc]
  have h₁ := Scheme.Hom.resLE_map ι (V_inf_le ℓ hℓ ι a b) (D_mul_le_left ℓ hℓ a b)
  have h₂ := Scheme.Hom.resLE_map ι (V_inf_le ℓ hℓ ι a b) (D_mul_le_right ℓ hℓ a b)
  rw [← h₁, ← h₂, Category.assoc, Category.assoc,
    chartMap_compat ℓ hℓ (X_mem' a) (X_mem' b) one_pos rfl
      (SetLike.mul_mem_graded (X_mem' a) (X_mem' b))]

variable (hcov : ∀ z : Z, ∃ k, ι z ∈ D ℓ hℓ k)

/-- **The linear projection `[ℓ₀ : … : ℓₙ] : Z ⟶ ℙⁿ_O`** for `Z` missing the centre. -/
noncomputable def proj : Z ⟶ Proj (𝒜 n) :=
  (cover ℓ hℓ ι hcov).glueMorphisms (chartHom ℓ hℓ ι) fun a b ↦ by
    let e := (isPullback_opens_inf (V ℓ hℓ ι a) (V ℓ hℓ ι b)).isoPullback
    change pullback.fst (V ℓ hℓ ι a).ι (V ℓ hℓ ι b).ι ≫ _ =
      pullback.snd (V ℓ hℓ ι a).ι (V ℓ hℓ ι b).ι ≫ _
    rw [← cancel_epi e.hom, ← Category.assoc, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
    exact chartHom_compat ℓ hℓ ι a b

lemma ι_proj (k : Fin (n + 1)) : (V ℓ hℓ ι k).ι ≫ proj ℓ hℓ ι hcov = chartHom ℓ hℓ ι k :=
  (cover ℓ hℓ ι hcov).ι_glueMorphisms _ _ k

/-- **The projection lies over `Spec O`.** -/
lemma proj_toSpec :
    proj ℓ hℓ ι hcov ≫ projSpace.toSpec O n = ι ≫ projSpace.toSpec O m := by
  refine (cover ℓ hℓ ι hcov).hom_ext _ _ fun k ↦ ?_
  change (V ℓ hℓ ι k).ι ≫ _ = (V ℓ hℓ ι k).ι ≫ _
  rw [← Category.assoc, ι_proj, chartHom, Category.assoc, chartMap_toSpec, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc]

/-- The chart `V_k ⟶ Spec (O[x]_{(ℓ_k)})₀`. -/
noncomputable def chartSpec (k : Fin (n + 1)) :
    (V ℓ hℓ ι k).toScheme ⟶ Spec (CommRingCat.of (Away (𝒜 m) (linHom ℓ hℓ (X k)))) :=
  ι.resLE (D ℓ hℓ k) (V ℓ hℓ ι k) le_rfl ≫
    (Proj.basicOpenIsoSpec (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k))
      one_pos).hom

lemma chartHom_eq (k : Fin (n + 1)) :
    chartHom ℓ hℓ ι k = chartSpec ℓ hℓ ι k ≫
      Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k))) ≫
        Proj.awayι (𝒜 n) (X k) (X_mem' k) one_pos := by
  simp only [chartHom, chartSpec, chartMap, Category.assoc]

lemma awayι_chartSpec (k : Fin (n + 1)) (x : V ℓ hℓ ι k) :
    Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos
      (chartSpec ℓ hℓ ι k x) = ι x.1 := by
  rw [← Scheme.Hom.comp_apply, chartSpec, Category.assoc, ← Proj.basicOpenIsoSpec_inv_ι,
    Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
  rfl

lemma awayMap_isLocalizationElem {s g : MvPolynomial (Fin (n + 1)) O} {d e : ℕ}
    (hs : s ∈ (𝒜 n) d) (hg : g ∈ (𝒜 n) e) :
    Away.map (linHom ℓ hℓ) s (Away.isLocalizationElem hs hg) =
      Away.isLocalizationElem ((linHom ℓ hℓ).map_mem hs) ((linHom ℓ hℓ).map_mem hg) := by
  rw [Away.map_mk]
  apply val_injective
  simp only [Away.val_mk, map_pow]
  rfl

variable {ℓ hℓ ι}

lemma proj_apply (k : Fin (n + 1)) (x : V ℓ hℓ ι k) :
    proj ℓ hℓ ι hcov x.1 = Proj.awayι (𝒜 n) (X k) (X_mem' k) one_pos
      (Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k))) (chartSpec ℓ hℓ ι k x)) := by
  have h := congrArg (fun f ↦ f x) (ι_proj ℓ hℓ ι hcov k)
  simp only [chartHom_eq, Scheme.Hom.comp_apply] at h
  exact h

/-- **Preimages of basic opens under the linear projection**: `p⁻¹ D₊(g) = ι⁻¹ D₊(g(ℓ))`. -/
lemma mem_preimage_basicOpen {g : MvPolynomial (Fin (n + 1)) O} {d : ℕ} (hg : g ∈ (𝒜 n) d)
    (hd : 0 < d) (z : Z) :
    proj ℓ hℓ ι hcov z ∈ Proj.basicOpen (𝒜 n) g ↔
      ι z ∈ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ g) := by
  obtain ⟨j, hj⟩ := hcov z
  let x : V ℓ hℓ ι j := ⟨z, hj⟩
  have e1 : ∀ P, Proj.awayι (𝒜 n) (X j) (X_mem' j) one_pos P ∈ Proj.basicOpen (𝒜 n) g ↔
      P ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem' j) hg) := fun P ↦
    SetLike.ext_iff.1 (Proj.awayι_preimage_basicOpen (𝒜 n) (X_mem' j) one_pos hg hd) P
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

/-- **The point formula**: a homogeneous `g` of positive degree vanishes at `proj z` iff
`g(ℓ₀, …, ℓₙ)` vanishes at `ι z`. -/
lemma mem_proj_iff {g : MvPolynomial (Fin (n + 1)) O} {d : ℕ} (hg : g ∈ (𝒜 n) d)
    (hd : 0 < d) (z : Z) :
    g ∈ (proj ℓ hℓ ι hcov z).asHomogeneousIdeal ↔
      aeval ℓ g ∈ (ι z).asHomogeneousIdeal := by
  have h := mem_preimage_basicOpen hcov hg hd z
  rw [← not_iff_not]
  exact h

/-- The point formula for the variables. -/
lemma X_mem_proj_iff (k : Fin (n + 1)) (z : Z) :
    (X k : MvPolynomial (Fin (n + 1)) O) ∈ (proj ℓ hℓ ι hcov z).asHomogeneousIdeal ↔
      ℓ k ∈ (ι z).asHomogeneousIdeal := by
  rw [mem_proj_iff hcov (X_mem' k) one_pos, aeval_X]

/-! ### Points of `ℙᵐ` with values in rings -/

section Points

variable {T : Type u} [CommRing T] [Algebra O T]

/-- The evaluation `(O[x]_{(s)})₀ → T`, `a / s ^ k ↦ a(c) / s(c) ^ k`, when `s(c)` is a unit. -/
noncomputable def awayEvalT (c : Fin (m + 1) → T) (s : MvPolynomial (Fin (m + 1)) O)
    (hs : IsUnit (aeval c s)) : Away (𝒜 m) s →+* T :=
  (Localization.awayLift (aeval c).toRingHom s hs).comp (algebraMap _ (Localization.Away s))

lemma awayEvalT_mk (c : Fin (m + 1) → T) {s : MvPolynomial (Fin (m + 1)) O}
    (hs : IsUnit (aeval c s)) {d : ℕ} (hsd : s ∈ (𝒜 m) d) (k : ℕ)
    (a : MvPolynomial (Fin (m + 1)) O) (ha : a ∈ (𝒜 m) (k • d)) :
    awayEvalT c s hs (Away.mk (𝒜 m) hsd k a ha) * aeval c s ^ k = aeval c a := by
  simp only [awayEvalT, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  have hv : (aeval c).toRingHom s * ↑hs.unit⁻¹ = 1 := by
    simp [AlgHom.toRingHom_eq_coe]
  rw [Localization.awayLift_mk (aeval c).toRingHom s a _ hv k, mul_assoc, ← mul_pow]
  have : (↑hs.unit⁻¹ : T) * aeval c s = 1 := by simp
  rw [this, one_pow, mul_one]
  rfl

lemma awayEvalT_comp_awayMap (c : Fin (m + 1) → T) {s t x : MvPolynomial (Fin (m + 1)) O}
    {d : ℕ} (ht : t ∈ (𝒜 m) d) (hx : x = s * t) (hs : IsUnit (aeval c s))
    (hxu : IsUnit (aeval c x)) :
    (awayEvalT c x hxu).comp (awayMap (𝒜 m) ht hx) = awayEvalT c s hs := by
  ext z
  simp only [awayEvalT, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply, val_awayMap]
  rw [← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
  simp [Localization.awayLift, IsLocalization.Away.lift]

/-- **The `T`-point `[c₀ : … : cₘ]` of `ℙᵐ_O`** through the chart `D₊(s)` (`s(c)` a unit). -/
noncomputable def ptT (c : Fin (m + 1) → T) (s : MvPolynomial (Fin (m + 1)) O)
    (hs : IsUnit (aeval c s)) {d : ℕ} (hsd : s ∈ (𝒜 m) d) (hd : 0 < d) :
    Spec (CommRingCat.of T) ⟶ Proj (𝒜 m) :=
  Spec.map (CommRingCat.ofHom (awayEvalT c s hs)) ≫ Proj.awayι (𝒜 m) s hsd hd

lemma ptT_congr (c : Fin (m + 1) → T) {s t : MvPolynomial (Fin (m + 1)) O} (h : s = t)
    (hs : IsUnit (aeval c s)) (ht : IsUnit (aeval c t)) {d : ℕ} (hsd : s ∈ (𝒜 m) d)
    (htd : t ∈ (𝒜 m) d) (hd : 0 < d) : ptT c s hs hsd hd = ptT c t ht htd hd := by
  subst h
  rfl

lemma ptT_mul (c : Fin (m + 1) → T) {s t : MvPolynomial (Fin (m + 1)) O}
    (hs : IsUnit (aeval c s)) (ht : IsUnit (aeval c t)) {d e : ℕ} (hsd : s ∈ (𝒜 m) d)
    (hte : t ∈ (𝒜 m) e) (hd : 0 < d) :
    ptT c s hs hsd hd = ptT c (s * t) (by rw [map_mul]; exact hs.mul ht)
      (SetLike.mul_mem_graded hsd hte) (hd.trans_le (Nat.le_add_right d e)) := by
  rw [ptT, ptT, ← Proj.SpecMap_awayMap_awayι (𝒜 m) hsd hd hte rfl, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, awayEvalT_comp_awayMap c hte rfl hs]

/-- **The point does not depend on the chart.** -/
lemma ptT_eq (c : Fin (m + 1) → T) {s t : MvPolynomial (Fin (m + 1)) O}
    (hs : IsUnit (aeval c s)) (ht : IsUnit (aeval c t)) {d : ℕ} (hsd : s ∈ (𝒜 m) d)
    (htd : t ∈ (𝒜 m) d) (hd : 0 < d) : ptT c s hs hsd hd = ptT c t ht htd hd := by
  rw [ptT_mul c hs ht hsd htd hd, ptT_mul c ht hs htd hsd hd]
  exact ptT_congr c (mul_comm _ _) _ _ _ _ _

/-- The point lies over `Spec O`. -/
lemma ptT_toSpec (c : Fin (m + 1) → T) (s : MvPolynomial (Fin (m + 1)) O)
    (hs : IsUnit (aeval c s)) {d : ℕ} (hsd : s ∈ (𝒜 m) d) (hd : 0 < d) :
    ptT c s hs hsd hd ≫ projSpace.toSpec O m = Spec.map (CommRingCat.ofHom (algebraMap O T)) := by
  change _ ≫ Proj.toSpecZero (𝒜 m) ≫ _ = _
  rw [ptT, Category.assoc, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext o
  change awayEvalT c s hs (fromZeroRingHom (𝒜 m) _ (algebraMap O _ o)) = algebraMap O T o
  simp only [awayEvalT, fromZeroRingHom, RingHom.coe_comp, Function.comp_apply,
    HomogeneousLocalization.algebraMap_apply]
  rw [Localization.awayLift, IsLocalization.Away.lift]
  change IsLocalization.lift _ (Localization.mk _ 1) = _
  rw [Localization.mk_one_eq_algebraMap, IsLocalization.lift_eq]
  simp [MvPolynomial.algebraMap_eq]

/-- **Naturality in `T`.** -/
lemma SpecMap_ptT {T' : Type u} [CommRing T'] [Algebra O T'] (r : T →ₐ[O] T')
    (c : Fin (m + 1) → T) (s : MvPolynomial (Fin (m + 1)) O)
    (hs : IsUnit (aeval c s)) (hs' : IsUnit (aeval (fun i => r (c i)) s)) {d : ℕ}
    (hsd : s ∈ (𝒜 m) d) (hd : 0 < d) :
    Spec.map (CommRingCat.ofHom (r : T →+* T')) ≫ ptT c s hs hsd hd =
      ptT (fun i => r (c i)) s hs' hsd hd := by
  rw [ptT, ptT, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext z
  simp only [awayEvalT, RingHom.coe_comp, Function.comp_apply]
  rw [← RingHom.comp_apply]
  congr 1
  refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun a ↦ ?_)
  simp only [Localization.awayLift, IsLocalization.Away.lift, RingHom.coe_comp,
    Function.comp_apply, IsLocalization.lift_eq, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]

/-- **The point formula**: a homogeneous `a` of positive degree vanishes at the image of `x`
iff `a(c)` lies in `x`. -/
lemma mem_ptT_iff (c : Fin (m + 1) → T) {s : MvPolynomial (Fin (m + 1)) O}
    (hs : IsUnit (aeval c s)) {d : ℕ} (hsd : s ∈ (𝒜 m) d) (hd : 0 < d)
    (x : Spec (CommRingCat.of T)) {a : MvPolynomial (Fin (m + 1)) O} {e : ℕ} (ha : a ∈ (𝒜 m) e)
    (he : 0 < e) :
    a ∈ (ptT c s hs hsd hd x).asHomogeneousIdeal ↔ aeval c a ∈ x.asIdeal := by
  have h := SetLike.ext_iff.1 (Proj.awayι_preimage_basicOpen (𝒜 m) hsd hd ha he)
    (Spec.map (CommRingCat.ofHom (awayEvalT c s hs)) x)
  rw [ptT, Scheme.Hom.comp_apply]
  rw [← not_iff_not]
  refine h.trans ?_
  change awayEvalT c s hs (Away.isLocalizationElem hsd ha) ∉ x.asIdeal ↔ _
  have hmk := awayEvalT_mk c hs hsd e (a ^ d) (by
    convert! SetLike.pow_mem_graded d ha using 2; exact mul_comm _ _)
  have hx := x.isPrime
  have hu : IsUnit (aeval c s ^ e) := hs.pow e
  constructor
  · intro h1 h2
    refine h1 ?_
    have : awayEvalT c s hs (Away.isLocalizationElem hsd ha) * aeval c s ^ e ∈ x.asIdeal := by
      rw [Away.isLocalizationElem, hmk, map_pow]
      exact Ideal.pow_mem_of_mem _ h2 _ hd
    exact (hx.mem_or_mem this).resolve_right fun h' =>
      hx.ne_top (Ideal.eq_top_of_isUnit_mem _ h' hu)
  · intro h1 h2
    refine h1 (hx.mem_of_pow_mem d ?_)
    rw [← map_pow, ← hmk]
    exact Ideal.mul_mem_right _ _ h2

end Points

/-! ### The projection of a point -/

variable (ℓ hℓ) in
/-- **The projection of a `T`-point**: if `ι ∘ x` is the point `c` (through the chart
`D₊(ℓ_k)`), then `proj ∘ x` is the point `ℓ(c)` (through `D₊(y_k)`). -/
lemma comp_proj_of_eq_ptT {W : Scheme.{u}} (x : W ⟶ Z) {T : Type u} [CommRing T] [Algebra O T]
    (c : Fin (m + 1) → T) (k : Fin (n + 1))
    (hk : IsUnit (aeval c (linHom ℓ hℓ (X k)))) (y : W ⟶ Spec (CommRingCat.of T))
    (hx : x ≫ ι = y ≫ ptT c (linHom ℓ hℓ (X k)) hk ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos)
    (hk' : IsUnit (aeval (fun j => aeval c (ℓ j)) (X k : MvPolynomial (Fin (n + 1)) O))) :
    x ≫ proj ℓ hℓ ι hcov = y ≫ ptT (fun j => aeval c (ℓ j)) (X k) hk' (X_mem' k) one_pos := by
  have hrange : Set.range x ⊆ Set.range (V ℓ hℓ ι k).ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change ι (x w) ∈ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X k))
    rw [← Scheme.Hom.comp_apply, hx, Scheme.Hom.comp_apply, ptT, Scheme.Hom.comp_apply]
    exact (SetLike.ext_iff.1 (Proj.opensRange_awayι (𝒜 m) _
      ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos) _).1 ⟨_, rfl⟩
  set x' := IsOpenImmersion.lift (V ℓ hℓ ι k).ι x hrange
  have hx' : x' ≫ (V ℓ hℓ ι k).ι = x := IsOpenImmersion.lift_fac _ _ _
  have hchart : x' ≫ chartSpec ℓ hℓ ι k =
      y ≫ Spec.map (CommRingCat.ofHom (awayEvalT c (linHom ℓ hℓ (X k)) hk)) := by
    rw [← cancel_mono (Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k))
      one_pos), Category.assoc, Category.assoc, chartSpec, Category.assoc,
      ← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι,
      ← Category.assoc, hx', hx]
    rfl
  rw [← hx', Category.assoc, ι_proj, chartHom_eq, ← Category.assoc, hchart, Category.assoc,
    ← Category.assoc (Spec.map _), ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext z
  obtain ⟨e, a, ha, rfl⟩ := Away.mk_surjective (𝒜 n) (X_mem' k) z
  have h1 := awayEvalT_mk (fun j => aeval c (ℓ j)) hk' (X_mem' k) e a ha
  have h2 := awayEvalT_mk c hk ((linHom ℓ hℓ).map_mem (X_mem' k)) e (linHom ℓ hℓ a)
    ((linHom ℓ hℓ).map_mem ha)
  simp only [CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply, Away.map_mk]
  have e1 : aeval (fun j => aeval c (ℓ j)) a = aeval c (linHom ℓ hℓ a) := by
    rw [linHom_apply, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have e2 : aeval (fun j => aeval c (ℓ j)) (X k : MvPolynomial (Fin (n + 1)) O) =
      aeval c (linHom ℓ hℓ (X k)) := by
    rw [linHom_apply, aeval_X, aeval_X]
  rw [e1, e2] at h1
  have hu : IsUnit (aeval c (linHom ℓ hℓ (X k)) ^ e) := hk.pow e
  exact hu.mul_left_inj.1 (h2.trans h1.symm)

end LinearProjectionN

end SemistableReduction
