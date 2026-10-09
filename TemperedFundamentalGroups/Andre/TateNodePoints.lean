/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateNodeGerm
import TemperedFundamentalGroups.Andre.TateModelNormal
import TemperedFundamentalGroups.Andre.TateNatural

/-!
# Node germs of the Tate model at `p` and `q` (HarmonicTate glue)

The Tate model `𝒯` is the projective model of its function field
(`TateNormal.modelIdeal_eq_ker`); `TateNormal.modelIso : 𝒯 ≅ projModelCode O hf` is the resulting
identification, compatible with the embeddings into `ℙ²_O` and the structure maps.

`TateNormal.nodeGerm_p`, `TateNormal.nodeGerm_q`: the germs of `projModelCode` (with its generic
point) at the images of `p` and `q` form a node germ `u v = ϖⁿ` with `u, v` non-units: the points
lie in the chart `x₀ ≠ 0` (`ProjScheme.chartι`), where `s`, `w` (resp. `s + 1`, `w`) and `𝔪`
vanish (`ProjScheme.mem_imageι_chartι_iff`), so `TateNormal.nodeGerm_chart_zero` applies.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open SemistableReduction.ProjScheme
open _root_.SemistableReduction (locAt)

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))] (hπ0 : π ≠ 0)

local notation "L" => TateField π b₄ b₆

attribute [local instance] algK

lemma eqToHom_subschemeι {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    eqToHom (congrArg Scheme.IdealSheafData.subscheme h) ≫ J.subschemeι = I.subschemeι := by
  subst h
  simp

/-- **The Tate model is the projective model of its function field.** -/
def modelIso : (TateModel.model π b₄ b₆).scheme ≅ (projModelCode O (hcoords π b₄ b₆ hπ0)).scheme :=
  eqToIso (congrArg Scheme.IdealSheafData.subscheme (modelIdeal_eq_ker π b₄ b₆ hπ0))

lemma modelIso_hom_imageι :
    (modelIso π b₄ b₆ hπ0).hom ≫ (toProj O (hcoords π b₄ b₆ hπ0)).imageι = TateModel.ι π b₄ b₆ :=
  eqToHom_subschemeι (modelIdeal_eq_ker π b₄ b₆ hπ0)

lemma modelIso_hom_toSpec :
    (modelIso π b₄ b₆ hπ0).hom ≫ (projModelCode O (hcoords π b₄ b₆ hπ0)).toSpec =
      (TateModel.model π b₄ b₆).toSpec := by
  change _ ≫ (toProj O (hcoords π b₄ b₆ hπ0)).imageι ≫ projSpace.toSpec O 2 = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ projSpace.toSpec O 2) (modelIso_hom_imageι π b₄ b₆ hπ0))

lemma modelIso_hom_apply_imageι (z : (TateModel.model π b₄ b₆).scheme) :
    (toProj O (hcoords π b₄ b₆ hπ0)).imageι ((modelIso π b₄ b₆ hπ0).hom z) =
      TateModel.ι π b₄ b₆ z := by
  have := congrArg (fun φ : (TateModel.model π b₄ b₆).scheme ⟶ projSpace O 2 => φ z)
    (modelIso_hom_imageι π b₄ b₆ hπ0)
  simp only [Scheme.Hom.comp_apply] at this
  exact this

/-- A point of the Tate model whose image in `ℙ²` avoids `xᵢ = 0` comes from the chart
`xᵢ ≠ 0`. -/
lemma exists_chartι_eq_of {i : Fin (2 + 1)} {z : (TateModel.model π b₄ b₆).scheme}
    (hz : X i ∉ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal) :
    ∃ Q : Spec (CommRingCat.of (chart π b₄ b₆ i)),
      chartι (baseRing π b₄ b₆) rfl (hcoords π b₄ b₆ hπ0) i Q = (modelIso π b₄ b₆ hπ0).hom z := by
  have hmem : (modelIso π b₄ b₆ hπ0).hom z ∈ chartOpen O (hcoords π b₄ b₆ hπ0) i := by
    change (toProj O (hcoords π b₄ b₆ hπ0)).imageι ((modelIso π b₄ b₆ hπ0).hom z) ∈
      (stdι O 2 i ''ᵁ ⊤)
    rw [Scheme.Hom.image_top_eq_opensRange, modelIso_hom_apply_imageι]
    change TateModel.ι π b₄ b₆ z ∈ (Proj.awayι _ (X i) (X_mem i) one_pos).opensRange
    rw [Proj.opensRange_awayι]
    exact hz
  rw [← opensRange_chartι (baseRing π b₄ b₆) rfl (hcoords π b₄ b₆ hπ0) i] at hmem
  obtain ⟨Q, hQ⟩ := hmem
  exact ⟨Q, hQ⟩

/-- A point of the Tate model whose image in `ℙ²` avoids `x₀ = 0` comes from the chart
`x₀ ≠ 0`. -/
lemma exists_chartι_eq {z : (TateModel.model π b₄ b₆).scheme}
    (hz : X 0 ∉ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal) :
    ∃ Q : Spec (CommRingCat.of (chart π b₄ b₆ 0)),
      chartι (baseRing π b₄ b₆) rfl (hcoords π b₄ b₆ hπ0) 0 Q = (modelIso π b₄ b₆ hπ0).hom z :=
  exists_chartι_eq_of π b₄ b₆ hπ0 hz

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O

/-- **Node germs at the points of `𝒯` over `p` (`δ = 0`) and `q` (`δ = -1`)**, in terms of the
homogeneous prime of the point: `x₀ ∉`, `x₁ - δ x₀ ∈`, `x₂ ∈` and `𝔪 x₀ ⊆`. -/
theorem nodeGerm_of_mem {ϖ : O} (hϖ : Irreducible ϖ) (z : (TateModel.model π b₄ b₆).scheme)
    (δ : O) (hδ : δ = 0 ∨ δ = -1) (hX0 : X 0 ∉ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal)
    (hσ : X 1 - C δ * X 0 ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal)
    (hw : X 2 ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal)
    (h𝔪 : ∀ o ∈ IsLocalRing.maximalIdeal O,
      C o * X 0 ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal) :
    ∃ (P : Subring L) (u v : L) (n : ℕ),
      (P : Set L) = TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
        (projModelCode O (hcoords π b₄ b₆ hπ0)) (genericPt O (hcoords π b₄ b₆ hπ0))
        ((modelIso π b₄ b₆ hπ0).hom z) ∧
      _root_.SemistableReduction.NodeGerm O ϖ P u v n ∧ (∀ w ∈ P, u * w ≠ 1) ∧
        (∀ w ∈ P, v * w ≠ 1) := by
  set hf := hcoords π b₄ b₆ hπ0
  obtain ⟨Q, hQ⟩ := exists_chartι_eq π b₄ b₆ hπ0 hX0
  obtain ⟨n, ε, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hπ0 hϖ
  have hπε : π = ((ε⁻¹ : Oˣ) : O) * ϖ ^ n := by
    rw [← hn, mul_comm, mul_assoc, Units.mul_inv, mul_one]
  have hpt : (toProj O hf).imageι (chartι (baseRing π b₄ b₆) rfl hf 0 Q) =
      TateModel.ι π b₄ b₆ z := by
    rw [hQ]; exact modelIso_hom_apply_imageι π b₄ b₆ hπ0 z
  have hmem : ∀ {g : MvPolynomial (Fin (2 + 1)) O} (hg : g ∈ 𝒜 1) {y : L}
      (hy : y ∈ chart π b₄ b₆ 0), evalHom (coords π b₄ b₆) g / coords π b₄ b₆ 0 ^ 1 = y →
      g ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal → (⟨y, hy⟩ : chart π b₄ b₆ 0) ∈ Q.asIdeal :=
    fun {g} hg {y} hy hval h => by
      rw [← hpt, mem_imageι_chartι_iff (baseRing π b₄ b₆) rfl hf 0 Q hg one_pos] at h
      obtain ⟨h', hQ'⟩ := h
      convert hQ' using 1
      exact Subtype.ext hval.symm
  have ha0 : coords π b₄ b₆ 0 ≠ 0 := aL_ne_zero π b₄ b₆
  have hc0 : coords π b₄ b₆ 0 = aL π b₄ b₆ := rfl
  have hc1 : coords π b₄ b₆ 1 = bL π b₄ b₆ := rfl
  have hc2 : coords π b₄ b₆ 2 = 1 := rfl
  obtain ⟨hG, hu, hv⟩ := nodeGerm_chart_zero π b₄ b₆ hπε δ hδ Q.asIdeal
    (hmem (by simpa using (isHomogeneous_X O 1).sub ((isHomogeneous_C_mul_X δ 0)))
      (sub_mem (sL_mem π b₄ b₆) (algebraMap_mem_chart π b₄ b₆ 0 δ)) (by
        simp only [evalHom, coe_eval₂Hom, eval₂_sub, eval₂_X, eval₂_mul, eval₂_C, pow_one]
        rw [sL, sub_div, mul_div_assoc, div_self ha0, mul_one]) hσ)
    (hmem (by simpa using isHomogeneous_X O 2) (wL_mem π b₄ b₆) (by
        simp only [evalHom, coe_eval₂Hom, eval₂_X, pow_one]) hw)
    (fun o ho => hmem (by simpa using isHomogeneous_C_mul_X o 0)
      (algebraMap_mem_chart π b₄ b₆ 0 o) (by
        simp only [evalHom, coe_eval₂Hom, eval₂_mul, eval₂_C, eval₂_X, pow_one]
        rw [mul_div_assoc, div_self ha0, mul_one]) (h𝔪 o ho))
  refine ⟨locAt (chart π b₄ b₆ 0) Q.asIdeal, _, _, n, ?_, hG, hu, hv⟩
  rw [← hQ, germs_chartι]

/-- **Node germs at the points of `𝒯` over `r = [0 : 0 : 1]`**, when
`c = b₆ − π² b₄² ≠ 0` divides `π`, in terms of the homogeneous prime of the point:
`x₂ ∉`, `x₀, x₁ ∈` and `𝔪 x₂ ⊆`. -/
theorem nodeGerm_of_mem_two {ϖ : O} (hϖ : Irreducible ϖ) (hπm : π ∈ IsLocalRing.maximalIdeal O)
    (hc0 : b₆ - π ^ 2 * b₄ ^ 2 ≠ 0) (hcπ : b₆ - π ^ 2 * b₄ ^ 2 ∣ π)
    (z : (TateModel.model π b₄ b₆).scheme)
    (hX2 : X 2 ∉ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal)
    (hX0 : X 0 ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal)
    (hX1 : X 1 ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal)
    (h𝔪 : ∀ o ∈ IsLocalRing.maximalIdeal O,
      C o * X 2 ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal) :
    ∃ (P : Subring L) (u v : L) (n : ℕ),
      (P : Set L) = TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
        (projModelCode O (hcoords π b₄ b₆ hπ0)) (genericPt O (hcoords π b₄ b₆ hπ0))
        ((modelIso π b₄ b₆ hπ0).hom z) ∧
      _root_.SemistableReduction.NodeGerm O ϖ P u v n ∧ (∀ w ∈ P, u * w ≠ 1) ∧
        (∀ w ∈ P, v * w ≠ 1) := by
  set hf := hcoords π b₄ b₆ hπ0
  obtain ⟨Q, hQ⟩ := exists_chartι_eq_of π b₄ b₆ hπ0 hX2
  obtain ⟨n, ε, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hc0 hϖ
  have hc : b₆ - π ^ 2 * b₄ ^ 2 = ((ε⁻¹ : Oˣ) : O) * ϖ ^ n := by
    rw [← hn, mul_comm (b₆ - π ^ 2 * b₄ ^ 2) (ε : O), Units.inv_mul_cancel_left]
  obtain ⟨t, ht⟩ := hcπ
  have hpt : (toProj O hf).imageι (chartι (baseRing π b₄ b₆) rfl hf 2 Q) =
      TateModel.ι π b₄ b₆ z := by
    rw [hQ]; exact modelIso_hom_apply_imageι π b₄ b₆ hπ0 z
  have hmem : ∀ {g : MvPolynomial (Fin (2 + 1)) O} (hg : g ∈ 𝒜 1) {y : L}
      (hy : y ∈ chart π b₄ b₆ 2), evalHom (coords π b₄ b₆) g / coords π b₄ b₆ 2 ^ 1 = y →
      g ∈ (TateModel.ι π b₄ b₆ z).asHomogeneousIdeal → (⟨y, hy⟩ : chart π b₄ b₆ 2) ∈ Q.asIdeal :=
    fun {g} hg {y} hy hval h => by
      rw [← hpt, mem_imageι_chartι_iff (baseRing π b₄ b₆) rfl hf 2 Q hg one_pos] at h
      obtain ⟨h', hQ'⟩ := h
      convert hQ' using 1
      exact Subtype.ext hval.symm
  have hc2 : coords π b₄ b₆ 2 = 1 := rfl
  obtain ⟨hG, hu, hv⟩ := nodeGerm_chart_two π b₄ b₆ hπ0 hπm hc ht Q.asIdeal
    (hmem (by simpa using isHomogeneous_X O 0) (aL_mem_chart_two π b₄ b₆) (by
        simp only [evalHom, coe_eval₂Hom, eval₂_X, pow_one, hc2, div_one]; rfl) hX0)
    (hmem (by simpa using isHomogeneous_X O 1) (bL_mem_chart_two π b₄ b₆) (by
        simp only [evalHom, coe_eval₂Hom, eval₂_X, pow_one, hc2, div_one]; rfl) hX1)
    (fun o ho => hmem (by simpa using isHomogeneous_C_mul_X o 2)
      (algebraMap_mem_chart π b₄ b₆ 2 o) (by
        simp only [evalHom, coe_eval₂Hom, eval₂_mul, eval₂_C, eval₂_X, pow_one, hc2, div_one]
        change algebraMap O L o * 1 = _
        rw [mul_one]) (h𝔪 o ho))
  refine ⟨locAt (chart π b₄ b₆ 2) Q.asIdeal, _, _, n, ?_, hG, hu, hv⟩
  rw [← hQ, germs_chartι]

variable {π b₄ b₆}

/-- **The germ at `p` is a node germ.** -/
theorem nodeGerm_p (hπm : π ∈ IsLocalRing.maximalIdeal O) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ (P : Subring L) (u v : L) (n : ℕ),
      (P : Set L) = TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
        (projModelCode O (hcoords π b₄ b₆ hπ0)) (genericPt O (hcoords π b₄ b₆ hπ0))
        ((modelIso π b₄ b₆ hπ0).hom (TateModel.pZ π b₄ b₆ hπm).1) ∧
      _root_.SemistableReduction.NodeGerm O ϖ P u v n ∧ (∀ w ∈ P, u * w ≠ 1) ∧
        (∀ w ∈ P, v * w ≠ 1) := by
  have h := TateModel.ιZ_pZ (b₄ := b₄) (b₆ := b₆) hπm
  change TateModel.ι π b₄ b₆ _ = _ at h
  refine nodeGerm_of_mem π b₄ b₆ hπ0 hϖ _ 0 (.inl rfl) ?_ ?_ ?_ fun o ho => ?_ <;>
    rw [h, TateModel.mem_pointP]
  · simp [TateModel.gp]
  · simp [TateModel.gp]
  · simp [TateModel.gp]
  · simp [TateModel.gp, (IsLocalRing.residue_eq_zero_iff o).2 ho]

/-- **The germ at `q` is a node germ.** -/
theorem nodeGerm_q (hπm : π ∈ IsLocalRing.maximalIdeal O) {ϖ : O} (hϖ : Irreducible ϖ) :
    ∃ (P : Subring L) (u v : L) (n : ℕ),
      (P : Set L) = TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
        (projModelCode O (hcoords π b₄ b₆ hπ0)) (genericPt O (hcoords π b₄ b₆ hπ0))
        ((modelIso π b₄ b₆ hπ0).hom (TateModel.qZ π b₄ b₆ hπm).1) ∧
      _root_.SemistableReduction.NodeGerm O ϖ P u v n ∧ (∀ w ∈ P, u * w ≠ 1) ∧
        (∀ w ∈ P, v * w ≠ 1) := by
  have h := TateModel.ιZ_qZ (b₄ := b₄) (b₆ := b₆) hπm
  change TateModel.ι π b₄ b₆ _ = _ at h
  refine nodeGerm_of_mem π b₄ b₆ hπ0 hϖ _ (-1) (.inr rfl) ?_ ?_ ?_ fun o ho => ?_ <;>
    rw [h, TateModel.mem_pointQ]
  · simp [TateModel.gq]
  · simp [TateModel.gq]
  · simp [TateModel.gq]
  · simp [TateModel.gq, (IsLocalRing.residue_eq_zero_iff o).2 ho]

section Generic

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma toModel_congr {T : Type u} [CommRing T] [IsReduced T] {φ φ' : O →+* T} {x x' y y' : T}
    (hφ : φ = φ') (hx : x = x') (hy : y = y')
    (heq : y ^ 2 + x * y = x ^ 3 + φ (π ^ 2 * b₄) * x + φ (π ^ 2 * b₆)) (hπ : IsUnit (φ π))
    (heq' : y' ^ 2 + x' * y' = x' ^ 3 + φ' (π ^ 2 * b₄) * x' + φ' (π ^ 2 * b₆))
    (hπ' : IsUnit (φ' π)) :
    TateModel.toModel π b₄ b₆ φ heq hπ = TateModel.toModel π b₄ b₆ φ' heq' hπ' := by
  subst hφ hx hy
  rfl

omit [IsDiscreteValuationRing O] in
lemma toProj_congr {m : ℕ} {F : Type u} [Field F] [Algebra O F] {f g : Fin (m + 1) → F}
    (h : f = g) (hf : ∀ i, f i ≠ 0) (hg : ∀ i, g i ≠ 0) : toProj O hf = toProj O hg := by
  subst h
  rfl

variable (π b₄ b₆)

include hπ0 in
lemma isUnit_algebraMap_π : IsUnit (algebraMap O L π) :=
  isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (algebraMap_O_injective π b₄ b₆)).2 hπ0)

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- The point `(π a, π b)` of the Tate curve over its function field. -/
lemma equation_L : (algebraMap O L π * bL π b₄ b₆) ^ 2 +
      (algebraMap O L π * aL π b₄ b₆) * (algebraMap O L π * bL π b₄ b₆) =
    (algebraMap O L π * aL π b₄ b₆) ^ 3 + algebraMap O L (π ^ 2 * b₄) *
      (algebraMap O L π * aL π b₄ b₆) + algebraMap O L (π ^ 2 * b₆) := by
  have h := bL_sq π b₄ b₆
  rw [algebraMap_cpoly] at h
  simp only [map_mul, map_pow]
  linear_combination algebraMap O L π ^ 2 * h

/-- **The generic point of the Tate model** is `[π a : π b : π] = [a : b : 1]`. -/
theorem toModel_comp_modelIso :
    TateModel.toModel π b₄ b₆ (algebraMap O L) (equation_L π b₄ b₆)
        (isUnit_algebraMap_π π b₄ b₆ hπ0) ≫ (modelIso π b₄ b₆ hπ0).hom =
      genericPt O (hcoords π b₄ b₆ hπ0) := by
  have hu := isUnit_algebraMap_π π b₄ b₆ hπ0
  have hfun : (![algebraMap O L π * aL π b₄ b₆ / algebraMap O L π,
      algebraMap O L π * bL π b₄ b₆ / algebraMap O L π, 1] : Fin (2 + 1) → L) =
      coords π b₄ b₆ := by
    rw [mul_div_cancel_left₀ _ hu.ne_zero, mul_div_cancel_left₀ _ hu.ne_zero]
  have hf' : ∀ i, (![algebraMap O L π * aL π b₄ b₆ / algebraMap O L π,
      algebraMap O L π * bL π b₄ b₆ / algebraMap O L π, 1] : Fin (2 + 1) → L) i ≠ 0 := by
    rw [hfun]; exact hcoords π b₄ b₆ hπ0
  refine (cancel_mono (toProj O (hcoords π b₄ b₆ hπ0)).imageι).1 ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (modelIso_hom_imageι π b₄ b₆ hπ0)).trans ?_
  refine (TateModel.toModel_ι π b₄ b₆ (algebraMap O L) (equation_L π b₄ b₆) hu).trans ?_
  rw [TateModel.toProj_eq_projScheme π _ _ hu hf',
    toProj_congr hfun hf' (hcoords π b₄ b₆ hπ0)]
  exact (Scheme.Hom.toImage_imageι _).symm

end Generic

end

end TemperedFundamentalGroups.TateNormal
