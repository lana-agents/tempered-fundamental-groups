/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LinearProjection
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Linear projections of closed subschemes of `ℙᵐ` to `ℙ¹` (Blueprint §12.8, M2 step 4(c))

Let `ι : Z ⟶ ℙᵐ_O` be a morphism (in the application a closed immersion, e.g. the scheme of a
`ModelCode`) and `ℓ₀, ℓ₁` linear forms such that `Z` misses the centre `V(ℓ₀, ℓ₁)`
(`hcov`). Then the linear projection `[ℓ₀ : ℓ₁]` restricts to a morphism

* `LinearProjection.proj : Z ⟶ ℙ¹_O`, glued from the charts `ι⁻¹ D₊(ℓ_k) ⟶ D₊(ℓ_k) ⟶ ℙ¹_O`
  (`LinearProjection.chartMap`, which agree on overlaps), with `ι_proj` and, over `Spec O`,
  `proj_toSpec`.

**Quasi-finiteness criterion** (`locallyQuasiFinite_proj`): if `ι` is a closed immersion and on
each chart `V_k = ι⁻¹ D₊(ℓ_k)` the restrictions `σ_k (x_i / ℓ_k)` of the coordinate functions are
integral over the image `θ_k` of `O[ℓ_{1-k} / ℓ_k]`, then `proj` is locally quasi-finite (each
`V_k ⟶ Spec O[ℓ_{1-k}/ℓ_k]` is even finite). Integrality may be checked up to nilpotents
(`isNilpotent_secRes`: a section `G / ℓ_k^e` with `G` vanishing at every point of `Z` restricts to
a nilpotent function on `V_k`).
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization Limits

namespace SemistableReduction

namespace LinearProjection

open TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] {m : ℕ}

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

lemma X_mem' (k : Fin (1 + 1)) : (X k : MvPolynomial (Fin (1 + 1)) O) ∈ (𝒜 1) 1 :=
  (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O k)

variable (ℓ : Fin (1 + 1) → MvPolynomial (Fin (m + 1)) O)
  (hℓ : ∀ j, ℓ j ∈ MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O 1)
  {Z : Scheme.{u}} (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O))

/-- The basic open `D₊(ℓ_k)` of `ℙᵐ_O`. -/
noncomputable abbrev D (k : Fin (1 + 1)) : (Proj (𝒜 m)).Opens :=
  Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X k))

/-- The chart `V_k = ι⁻¹ D₊(ℓ_k)` of `Z`. -/
noncomputable abbrev V (k : Fin (1 + 1)) : Z.Opens := ι ⁻¹ᵁ D ℓ hℓ k

/-- The projection on the chart `V_k`. -/
noncomputable def chartHom (k : Fin (1 + 1)) : (V ℓ hℓ ι k).toScheme ⟶ Proj (𝒜 1) :=
  ι.resLE (D ℓ hℓ k) (V ℓ hℓ ι k) le_rfl ≫ chartMap ℓ hℓ (X k) (X_mem' k) one_pos

variable {ℓ hℓ ι} in
lemma isOpenCover_V (hcov : ∀ z : Z, ι z ∈ D ℓ hℓ 0 ∨ ι z ∈ D ℓ hℓ 1) :
    TopologicalSpace.IsOpenCover (V ℓ hℓ ι) := by
  refine top_le_iff.1 fun z _ ↦ ?_
  rw [TopologicalSpace.Opens.mem_iSup]
  rcases hcov z with h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩

/-- The open cover of `Z` by the charts `V_k`. -/
noncomputable def cover (hcov : ∀ z : Z, ι z ∈ D ℓ hℓ 0 ∨ ι z ∈ D ℓ hℓ 1) : Z.OpenCover :=
  Z.openCoverOfIsOpenCover (V ℓ hℓ ι) (isOpenCover_V hcov)

lemma D_mul_le_left (a b : Fin (1 + 1)) :
    Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X a * X b)) ≤ D ℓ hℓ a := by
  rw [map_mul, Proj.basicOpen_mul]
  exact inf_le_left

lemma D_mul_le_right (a b : Fin (1 + 1)) :
    Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X a * X b)) ≤ D ℓ hℓ b := by
  rw [map_mul, Proj.basicOpen_mul]
  exact inf_le_right

lemma V_inf_le (a b : Fin (1 + 1)) :
    V ℓ hℓ ι a ⊓ V ℓ hℓ ι b ≤ ι ⁻¹ᵁ Proj.basicOpen (𝒜 m) (linHom ℓ hℓ (X a * X b)) := by
  rw [map_mul, Proj.basicOpen_mul]
  exact le_rfl

/-- **The charts agree on overlaps.** -/
lemma chartHom_compat (a b : Fin (1 + 1)) :
    Z.homOfLE (inf_le_left : V ℓ hℓ ι a ⊓ V ℓ hℓ ι b ≤ _) ≫ chartHom ℓ hℓ ι a =
      Z.homOfLE (inf_le_right : V ℓ hℓ ι a ⊓ V ℓ hℓ ι b ≤ _) ≫ chartHom ℓ hℓ ι b := by
  simp only [chartHom, Scheme.Hom.map_resLE_assoc]
  have h₁ := Scheme.Hom.resLE_map ι (V_inf_le ℓ hℓ ι a b) (D_mul_le_left ℓ hℓ a b)
  have h₂ := Scheme.Hom.resLE_map ι (V_inf_le ℓ hℓ ι a b) (D_mul_le_right ℓ hℓ a b)
  rw [← h₁, ← h₂, Category.assoc, Category.assoc,
    chartMap_compat ℓ hℓ (X_mem' a) (X_mem' b) one_pos rfl
      (SetLike.mul_mem_graded (X_mem' a) (X_mem' b))]

variable (hcov : ∀ z : Z, ι z ∈ D ℓ hℓ 0 ∨ ι z ∈ D ℓ hℓ 1)

/-- **The linear projection `[ℓ₀ : ℓ₁] : Z ⟶ ℙ¹_O`** for `Z` missing the centre. -/
noncomputable def proj : Z ⟶ Proj (𝒜 1) :=
  (cover ℓ hℓ ι hcov).glueMorphisms (chartHom ℓ hℓ ι) fun a b ↦ by
    let e := (isPullback_opens_inf (V ℓ hℓ ι a) (V ℓ hℓ ι b)).isoPullback
    change pullback.fst (V ℓ hℓ ι a).ι (V ℓ hℓ ι b).ι ≫ _ =
      pullback.snd (V ℓ hℓ ι a).ι (V ℓ hℓ ι b).ι ≫ _
    rw [← cancel_epi e.hom, ← Category.assoc, ← Category.assoc, IsPullback.isoPullback_hom_fst,
      IsPullback.isoPullback_hom_snd]
    exact chartHom_compat ℓ hℓ ι a b

lemma ι_proj (k : Fin (1 + 1)) : (V ℓ hℓ ι k).ι ≫ proj ℓ hℓ ι hcov = chartHom ℓ hℓ ι k :=
  (cover ℓ hℓ ι hcov).ι_glueMorphisms _ _ k

/-- **The projection lies over `Spec O`.** -/
lemma proj_toSpec :
    proj ℓ hℓ ι hcov ≫ projSpace.toSpec O 1 = ι ≫ projSpace.toSpec O m := by
  refine (cover ℓ hℓ ι hcov).hom_ext _ _ fun k ↦ ?_
  change (V ℓ hℓ ι k).ι ≫ _ = (V ℓ hℓ ι k).ι ≫ _
  rw [← Category.assoc, ι_proj, chartHom, Category.assoc, chartMap_toSpec, ← Category.assoc,
    Scheme.Hom.resLE_comp_ι, Category.assoc]

/-! ### The chart rings and quasi-finiteness -/

/-- The chart `V_k ⟶ Spec (O[x]_{(ℓ_k)})₀`. -/
noncomputable def chartSpec (k : Fin (1 + 1)) :
    (V ℓ hℓ ι k).toScheme ⟶ Spec (CommRingCat.of (Away (𝒜 m) (linHom ℓ hℓ (X k)))) :=
  ι.resLE (D ℓ hℓ k) (V ℓ hℓ ι k) le_rfl ≫
    (Proj.basicOpenIsoSpec (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k))
      one_pos).hom

/-- **Restriction of homogeneous fractions to the chart `V_k`**:
`(O[x]_{(ℓ_k)})₀ → Γ(V_k)`. -/
noncomputable def secRes (k : Fin (1 + 1)) :
    Away (𝒜 m) (linHom ℓ hℓ (X k)) →+* Γ(V ℓ hℓ ι k, ⊤) :=
  (chartSpec ℓ hℓ ι k).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (Away (𝒜 m) (linHom ℓ hℓ (X k))))).inv.hom

/-- The map `O[ℓ_{1-k} / ℓ_k] → Γ(V_k)` (more precisely from the chart ring `(O[y]_{(y_k)})₀` of
`ℙ¹_O`). -/
noncomputable def baseRes (k : Fin (1 + 1)) :
    Away (𝒜 1) (X k : MvPolynomial (Fin (1 + 1)) O) →+* Γ(V ℓ hℓ ι k, ⊤) :=
  (secRes ℓ hℓ ι k).comp (Away.map (linHom ℓ hℓ) (X k))

/-- The coordinate function `x_i / ℓ_k` on `D₊(ℓ_k)`. -/
noncomputable abbrev coordFrac (k : Fin (1 + 1)) (i : Fin (m + 1)) :
    Away (𝒜 m) (linHom ℓ hℓ (X k)) :=
  Away.mk (𝒜 m) ((linHom ℓ hℓ).map_mem (X_mem' k)) 1 (X i)
    (by simpa using (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O i))

lemma isAffineOpen_V [IsClosedImmersion ι] (k : Fin (1 + 1)) : IsAffineOpen (V ℓ hℓ ι k) :=
  (Proj.isAffineOpen_basicOpen (𝒜 m) _ ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos).preimage ι

instance [IsClosedImmersion ι] (k : Fin (1 + 1)) : IsClosedImmersion (chartSpec ℓ hℓ ι k) := by
  unfold chartSpec
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

lemma secRes_surjective [IsClosedImmersion ι] (k : Fin (1 + 1)) :
    Function.Surjective (secRes ℓ hℓ ι k) := by
  have h₁ := (chartSpec ℓ hℓ ι k).app_surjective ⊤ (isAffineOpen_top _)
  have h₂ := (Scheme.ΓSpecIso
    (CommRingCat.of (Away (𝒜 m) (linHom ℓ hℓ (X k))))).commRingCatIsoToRingEquiv.symm.surjective
  exact h₁.comp h₂

/-- A section of an affine scheme with empty basic open is nilpotent. -/
lemma isNilpotent_of_basicOpen_eq_bot {X : Scheme.{u}} [IsAffine X] (s : Γ(X, ⊤))
    (h : X.basicOpen s = ⊥) : IsNilpotent s := by
  rw [← PrimeSpectrum.basicOpen_eq_bot_iff]
  refine eq_bot_iff.2 fun p hp ↦ ?_
  obtain ⟨x, rfl⟩ := X.isoSpec.hom.homeomorph.surjective p
  have hx : x ∈ X.toSpecΓ ⁻¹ᵁ PrimeSpectrum.basicOpen s := hp
  rw [Scheme.toSpecΓ_preimage_basicOpen, h] at hx
  exact hx

/-- **Fractions vanishing on `Z` restrict to nilpotent functions on the charts.** For `G`
homogeneous of degree `e` lying in every point of `Z` (i.e. vanishing on `Z`), the function
`G / ℓ_k^e` on `V_k` is nilpotent. -/
lemma isNilpotent_secRes [IsClosedImmersion ι] (k : Fin (1 + 1)) {G : MvPolynomial (Fin (m + 1)) O}
    {e : ℕ} (hG : G ∈ (𝒜 m) e) (he : 0 < e) (hZ : ∀ z : Z, G ∈ (ι z).asHomogeneousIdeal) :
    IsNilpotent (secRes ℓ hℓ ι k (Away.isLocalizationElem
      ((linHom ℓ hℓ).map_mem (X_mem' k)) hG)) := by
  haveI : IsAffine (V ℓ hℓ ι k).toScheme := isAffineOpen_V ℓ hℓ ι k
  refine isNilpotent_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun x hx ↦ ?_)
  have hx' : x ∈ chartSpec ℓ hℓ ι k ⁻¹ᵁ (Spec _).basicOpen ((Scheme.ΓSpecIso _).inv
      (Away.isLocalizationElem ((linHom ℓ hℓ).map_mem (X_mem' k)) hG)) := by
    rw [Scheme.preimage_basicOpen_top]
    simp only [secRes, RingHom.comp_apply] at hx
    exact hx
  rw [basicOpen_eq_of_affine] at hx'
  have hx'' : chartSpec ℓ hℓ ι k x ∈ Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k))
      ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos ⁻¹ᵁ Proj.basicOpen (𝒜 m) G := by
    rw [Proj.awayι_preimage_basicOpen (𝒜 m) _ one_pos hG he]
    exact hx'
  have hι : Proj.awayι (𝒜 m) (linHom ℓ hℓ (X k)) ((linHom ℓ hℓ).map_mem (X_mem' k)) one_pos
      (chartSpec ℓ hℓ ι k x) = ι x.1 := by
    rw [← Scheme.Hom.comp_apply, chartSpec, Category.assoc, ← Proj.basicOpenIsoSpec_inv_ι,
      Iso.hom_inv_id_assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.comp_apply]
    rfl
  change _ ∈ Proj.basicOpen (𝒜 m) G at hx''
  rw [hι, Proj.mem_basicOpen] at hx''
  exact (hx'' (hZ x.1)).elim

/-! ### Finiteness of the charts -/

/-- `Away.map` of the linear projection is compatible with the constants `O`. -/
lemma awayMap_fromZero (s : MvPolynomial (Fin (1 + 1)) O) (o : O) :
    Away.map (linHom ℓ hℓ) s (fromZeroRingHom (𝒜 1) _ (algebraMap O ((𝒜 1) 0) o)) =
      fromZeroRingHom (𝒜 m) _ (algebraMap O ((𝒜 m) 0) o) := by
  ext
  simp only [fromZeroRingHom, Away.map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.map_mk, val_mk]
  simp [MvPolynomial.algebraMap_eq]

lemma adjoin_X_eq_top :
    Algebra.adjoin ((𝒜 m) 0) (Set.range (X : Fin (m + 1) → MvPolynomial (Fin (m + 1)) O)) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a =>
    have : (C a : MvPolynomial (Fin (m + 1)) O) =
        algebraMap ((𝒜 m) 0) (MvPolynomial (Fin (m + 1)) O) ⟨C a, by simp⟩ := rfl
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- The generators `(∏ x_i ^ {a_i}) / ℓ_k ^ a` of `(O[x]_{(ℓ_k)})₀` are monomials in the
coordinate functions `x_i / ℓ_k`. -/
lemma mk_prod_eq (k : Fin (1 + 1)) (a : ℕ) (ai : Fin (m + 1) → ℕ)
    (hai : ∑ i, ai i • 1 = a • 1) (h) :
    Away.mk (𝒜 m) ((linHom ℓ hℓ).map_mem (X_mem' k)) a (∏ i, X i ^ ai i) h =
      ∏ i, coordFrac ℓ hℓ k i ^ ai i := by
  apply (show Function.Injective (algebraMap (Away (𝒜 m) (linHom ℓ hℓ (X k)))
    (Localization.Away (linHom ℓ hℓ (X k)))) from val_injective _)
  simp only [map_pow, map_prod, HomogeneousLocalization.algebraMap_apply, Away.val_mk]
  simp only [Localization.mk_pow, Localization.mk_prod]
  congr 1
  apply Subtype.ext
  simp only [smul_eq_mul, mul_one] at hai
  simp only [SubmonoidClass.coe_pow, Finset.prod_pow_eq_pow_sum, hai, linHom_X, pow_one]
  exact congrArg (· ^ a) (linHom_X ℓ hℓ k)

variable {ℓ hℓ ι} in
/-- **Integrality of the chart rings.** If the coordinate functions `x_i / ℓ_k` restrict to
functions integral over `O[ℓ_{1-k}/ℓ_k]` on `V_k`, then `Γ(V_k)` is finite over it. -/
theorem finite_baseRes [IsClosedImmersion ι] (k : Fin (1 + 1))
    (hint : ∀ i, (baseRes ℓ hℓ ι k).IsIntegralElem (secRes ℓ hℓ ι k (coordFrac ℓ hℓ k i))) :
    (baseRes ℓ hℓ ι k).Finite := by
  set ψ := Away.map (linHom ℓ hℓ) (X k : MvPolynomial (Fin (1 + 1)) O)
  have hbase : ∀ y, (baseRes ℓ hℓ ι k).IsIntegralElem (secRes ℓ hℓ ι k (ψ y)) :=
    fun y ↦ RingHom.isIntegralElem_map (f := baseRes ℓ hℓ ι k) (x := y)
  -- the elements whose restriction is integral form a subalgebra containing the generators
  let S : Subalgebra ((𝒜 m) 0) (Away (𝒜 m) (linHom ℓ hℓ (X k))) :=
    { carrier := {b | (baseRes ℓ hℓ ι k).IsIntegralElem (secRes ℓ hℓ ι k b)}
      mul_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_mul] at ha hb ⊢
        exact RingHom.IsIntegralElem.mul _ ha hb
      add_mem' := fun {a b} ha hb ↦ by
        simp only [Set.mem_setOf_eq, map_add] at ha hb ⊢
        exact RingHom.IsIntegralElem.add _ ha hb
      algebraMap_mem' := fun r ↦ by
        obtain ⟨o, rfl⟩ := (bijective_algebraMap_projSpace O m).2 r
        simp only [Set.mem_setOf_eq, HomogeneousLocalization.algebraMap_eq]
        rw [← awayMap_fromZero ℓ hℓ]
        exact hbase _ }
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← Away.adjoin_mk_prod_pow_eq_top ((linHom ℓ hℓ).map_mem (X_mem' k))
      (Fin (m + 1)) X (adjoin_X_eq_top (O := O) (m := m)) (fun _ ↦ 1)
      (fun i ↦ (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O i)), Algebra.adjoin_le_iff]
    rintro _ ⟨a, ai, hai, -, rfl⟩
    change (baseRes ℓ hℓ ι k).IsIntegralElem (secRes ℓ hℓ ι k _)
    rw [mk_prod_eq ℓ hℓ k a ai hai, map_prod]
    have hpow : ∀ (x : Γ(V ℓ hℓ ι k, ⊤)) (n : ℕ), (baseRes ℓ hℓ ι k).IsIntegralElem x →
        (baseRes ℓ hℓ ι k).IsIntegralElem (x ^ n) := fun x n hx ↦ by
      induction n with
      | zero => simpa using RingHom.isIntegralElem_map (f := baseRes ℓ hℓ ι k) (x := 1)
      | succ n ih => rw [pow_succ]; exact RingHom.IsIntegralElem.mul _ ih hx
    refine Finset.prod_induction _ _ (fun x y hx hy ↦ RingHom.IsIntegralElem.mul _ hx hy) ?_
      fun i _ ↦ by rw [map_pow]; exact hpow _ _ (hint i)
    simpa using RingHom.isIntegralElem_map (f := baseRes ℓ hℓ ι k) (x := 1)
  have hint' : (baseRes ℓ hℓ ι k).IsIntegral := fun c ↦ by
    obtain ⟨b, rfl⟩ := secRes_surjective ℓ hℓ ι k c
    have hb : b ∈ S := hS ▸ Algebra.mem_top
    exact hb
  have hψ : ψ.FiniteType := by
    have h₁ : (algebraMap ((𝒜 m) 0) (Away (𝒜 m) (linHom ℓ hℓ (X k)))).FiniteType := by
      rw [RingHom.finiteType_algebraMap]
      exact Away.finiteType _ 1 ((linHom ℓ hℓ).map_mem (X_mem' k))
    have h₂ : (algebraMap O ((𝒜 m) 0)).FiniteType :=
      RingHom.FiniteType.of_surjective _ (bijective_algebraMap_projSpace O m).2
    have h₃ := h₁.comp h₂
    have heq : (algebraMap ((𝒜 m) 0) (Away (𝒜 m) (linHom ℓ hℓ (X k)))).comp
        (algebraMap O ((𝒜 m) 0)) =
        ψ.comp ((fromZeroRingHom (𝒜 1) _).comp (algebraMap O ((𝒜 1) 0))) := by
      ext o
      simp only [RingHom.comp_apply, HomogeneousLocalization.algebraMap_eq]
      rw [awayMap_fromZero ℓ hℓ]
    rw [heq] at h₃
    exact RingHom.FiniteType.of_comp_finiteType h₃
  exact RingHom.IsIntegral.to_finite hint'
    ((RingHom.FiniteType.of_surjective _ (secRes_surjective ℓ hℓ ι k)).comp hψ)

lemma chartHom_eq (k : Fin (1 + 1)) :
    chartHom ℓ hℓ ι k = chartSpec ℓ hℓ ι k ≫
      Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k))) ≫
        Proj.awayι (𝒜 1) (X k) (X_mem' k) one_pos := by
  simp only [chartHom, chartSpec, chartMap, Category.assoc]

variable {ℓ hℓ ι} in
/-- **The chart maps `V_k ⟶ Spec O[ℓ_{1-k}/ℓ_k]` are finite** under the integrality
hypothesis. -/
theorem isFinite_chartSpec_comp [IsClosedImmersion ι] (k : Fin (1 + 1))
    (hint : ∀ i, (baseRes ℓ hℓ ι k).IsIntegralElem (secRes ℓ hℓ ι k (coordFrac ℓ hℓ k i))) :
    IsFinite (chartSpec ℓ hℓ ι k ≫
      Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k)))) := by
  haveI : IsAffine (V ℓ hℓ ι k).toScheme := isAffineOpen_V ℓ hℓ ι k
  rw [HasAffineProperty.iff_of_isAffine (P := @IsFinite)]
  refine ⟨inferInstance, ?_⟩
  have e : (chartSpec ℓ hℓ ι k ≫
      Spec.map (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k)))).appTop.hom =
      (baseRes ℓ hℓ ι k).comp (Scheme.ΓSpecIso _).hom.hom := by
    rw [Scheme.Hom.comp_appTop]
    have h := Scheme.ΓSpecIso_naturality
      (CommRingCat.ofHom (Away.map (linHom ℓ hℓ) (X k : MvPolynomial (Fin (1 + 1)) O)))
    rw [← Iso.eq_comp_inv] at h
    rw [h]
    ext x
    simp [baseRes, secRes]
    rfl
  rw [e]
  exact (finite_baseRes k hint).comp
    (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso _).commRingCatIsoToRingEquiv.surjective)

variable {ℓ hℓ ι} in
/-- **Quasi-finiteness of the projection**: if on each chart the coordinate functions are
integral over `O[ℓ_{1-k}/ℓ_k]`, the projection `Z ⟶ ℙ¹_O` is locally quasi-finite. -/
theorem locallyQuasiFinite_proj [IsClosedImmersion ι]
    (hint : ∀ k i, (baseRes ℓ hℓ ι k).IsIntegralElem (secRes ℓ hℓ ι k (coordFrac ℓ hℓ k i))) :
    LocallyQuasiFinite (proj ℓ hℓ ι hcov) := by
  rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyQuasiFinite) (cover ℓ hℓ ι hcov)]
  intro k
  change LocallyQuasiFinite ((V ℓ hℓ ι k).ι ≫ proj ℓ hℓ ι hcov)
  rw [ι_proj, chartHom_eq, ← Category.assoc]
  haveI := isFinite_chartSpec_comp k (hint k)
  infer_instance

/-! ### Tools for checking the integrality hypothesis -/

lemma isIntegralElem_secRes_awayMap (k : Fin (1 + 1)) (y : Away (𝒜 1) (X k)) :
    (baseRes ℓ hℓ ι k).IsIntegralElem (secRes ℓ hℓ ι k (Away.map (linHom ℓ hℓ) (X k) y)) :=
  RingHom.isIntegralElem_map (f := baseRes ℓ hℓ ι k) (x := y)

/-- A root of a monic polynomial up to a nilpotent is integral. -/
lemma _root_.RingHom.isIntegralElem_of_monic_of_isNilpotent {R S : Type*} [CommRing R]
    [CommRing S] (f : R →+* S) {x : S} {p : Polynomial R} (hp : p.Monic)
    (h : IsNilpotent (p.eval₂ f x)) : f.IsIntegralElem x := by
  obtain ⟨n, hn⟩ := h
  exact ⟨p ^ n, hp.pow n, by rw [Polynomial.eval₂_pow, hn]⟩

/-- The value of a homogeneous fraction in the localization `O[x][1/s]`. -/
lemma val_away_mk {s : MvPolynomial (Fin (m + 1)) O} {d : ℕ} (hs : s ∈ (𝒜 m) d) (n : ℕ)
    (a : MvPolynomial (Fin (m + 1)) O) (ha : a ∈ (𝒜 m) (n • d)) :
    (Away.mk (𝒜 m) hs n a ha).val =
      algebraMap _ (Localization.Away s) a * IsLocalization.Away.invSelf s ^ n := by
  rw [Away.val_mk, IsLocalization.Away.invSelf, ← IsLocalization.mk'_pow, one_pow,
    ← IsLocalization.mk'_eq_mul_mk'_one, Localization.mk_eq_mk']
  rfl

lemma val_fromZero (s : MvPolynomial (Fin (m + 1)) O) (o : O) :
    (fromZeroRingHom (𝒜 m) (Submonoid.powers s) (algebraMap O ((𝒜 m) 0) o)).val =
      algebraMap _ (Localization.Away s) (C o : MvPolynomial (Fin (m + 1)) O) := by
  simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, val_mk]
  rw [← Localization.mk_one_eq_algebraMap]
  rfl

end LinearProjection

end SemistableReduction
