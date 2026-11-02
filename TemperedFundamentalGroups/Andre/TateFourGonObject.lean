/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Oka.AlgebraicGeometry.Modules.Support
import TemperedFundamentalGroups.Andre.TateFourGon
import TemperedFundamentalGroups.Andre.TateObject
import TemperedFundamentalGroups.SemistableReduction.LinearProjectionN

/-!
# The `4`-gon model of `E_{q²}` over the Tate model of `E_q`

Let `π, b₄, b₆` be the Tate data of `E_q` (the object `X₀` of `Andre/TateObject.lean`) and
`π, b₄', b₆'` those of `E_{q²}`, with the constants `ε, γ, κ` of the `4`-gon model
(`Andre/TateFourGon.lean`, TFGD-plan "Run 4"). This file constructs:

* `FourGon.model`: the reduced closed subscheme of `ℙ⁴_O` on the common zeros of the five
  equations `FourGon.Rels` and of `F(ℓ)`, the Tate cubic of `E_q` composed with the linear forms
  `ℓ = (X₀ + X₂ − ε X₄, X₁ + X₃ + κ X₄, X₄)` (Vélu: `x = x₁ + x₂ − x_T`, `y = y₁ + y₂ + c_y`);
* `FourGon.ψ : model ⟶ TateModel.model π b₄ b₆`: the linear projection `[ℓ₀ : ℓ₁ : ℓ₂]` (the
  model misses its centre, `FourGon.hcov`), lying over `O` (`FourGon.ψ_toSpec`), with the point
  formula `FourGon.mem_ψ_iff`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial
open SemistableReduction.LinearProjectionN

namespace TemperedFundamentalGroups

/-! ### Maps `(z, n) ↦ (f z, 2n + κ z + c)` of `ℤ`-coverings -/

namespace TateCovering.Decomp

variable {Z Z' : Type*} [TopologicalSpace Z] [TopologicalSpace Z']

/-- The map `(z, n) ↦ (f z, 2n + κ z + c)` from the `ℤ`-covering of `D'` to that of `D`. -/
def mapTwo (D' : Decomp Z') (D : Decomp Z) (f : Z' → Z) (κ : Z' → ℤ) (c : ℤ)
    (y : D'.Space) : D.Space :=
  ⟨f y.pt, 2 * y.n + κ y.pt + c⟩

variable {D' : Decomp Z'} {D : Decomp Z}

/-- **Continuity of `mapTwo`**: the sheet labels are locally constant along the sheets. -/
theorem continuous_mapTwo {f : Z' → Z} (hf : Continuous f) (κ : Z' → ℤ) (c : ℤ)
    (h1 : ∀ z, f z ∉ D.Cq → z ∉ D'.Cq)
    (h2 : ∀ v, IsOpen {z | f z ∉ D.Cq ∧ κ z = v})
    (h3 : ∀ v, IsOpen {z | z ∉ D'.Cq ∧ f z ∉ D.Cp ∧ κ z - D.shift (f z) = v})
    (h4 : ∀ v, IsOpen {z | z ∉ D'.Cp ∧ f z ∉ D.Cp ∧
      2 * D'.shift z + κ z - D.shift (f z) = v}) :
    Continuous (mapTwo D' D f κ c) := by
  rw [continuous_iff]
  refine ⟨hf.comp D'.continuous_pt, fun k => ?_, fun k => ?_⟩
  · have : {y : D'.Space | (mapTwo D' D f κ c y).pt ∉ D.Cq ∧ (mapTwo D' D f κ c y).n = k} =
        ⋃ j : ℤ, {y : D'.Space | y.pt ∉ D'.Cq ∧ y.n = j} ∩
          (fun y : D'.Space => y.pt) ⁻¹' {z | f z ∉ D.Cq ∧ κ z = k - 2 * j - c} := by
      ext y
      simp only [mapTwo, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨hq, hk⟩
        exact ⟨y.n, ⟨h1 _ hq, rfl⟩, hq, by omega⟩
      · rintro ⟨j, ⟨-, rfl⟩, hq, hk⟩
        exact ⟨hq, by omega⟩
    rw [this]
    exact isOpen_iUnion fun j => (D'.isOpen_sheet₁ j).inter ((h2 _).preimage D'.continuous_pt)
  · have : {y : D'.Space | (mapTwo D' D f κ c y).pt ∉ D.Cp ∧
        (mapTwo D' D f κ c y).n - D.shift (mapTwo D' D f κ c y).pt = k} =
        ⋃ j : ℤ, (({y : D'.Space | y.pt ∉ D'.Cq ∧ y.n = j} ∩
          (fun y : D'.Space => y.pt) ⁻¹'
            {z | z ∉ D'.Cq ∧ f z ∉ D.Cp ∧ κ z - D.shift (f z) = k - 2 * j - c}) ∪
          ({y : D'.Space | y.pt ∉ D'.Cp ∧ y.n - D'.shift y.pt = j} ∩
          (fun y : D'.Space => y.pt) ⁻¹' {z | z ∉ D'.Cp ∧ f z ∉ D.Cp ∧
            2 * D'.shift z + κ z - D.shift (f z) = k - 2 * j - c})) := by
      ext y
      simp only [mapTwo, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_union, Set.mem_inter_iff,
        Set.mem_preimage]
      constructor
      · rintro ⟨hp, hk⟩
        by_cases hq : y.pt ∈ D'.Cq
        · have hp' : y.pt ∉ D'.Cp := fun h => D'.notMem_Cq_of_mem_Cp h hq
          exact ⟨y.n - D'.shift y.pt, Or.inr ⟨⟨hp', rfl⟩, hp', hp, by omega⟩⟩
        · exact ⟨y.n, Or.inl ⟨⟨hq, rfl⟩, hq, hp, by omega⟩⟩
      · rintro ⟨j, ⟨⟨-, rfl⟩, -, hp, hk⟩ | ⟨⟨-, hj⟩, -, hp, hk⟩⟩
        · exact ⟨hp, by omega⟩
        · exact ⟨hp, by omega⟩
    rw [this]
    exact isOpen_iUnion fun j =>
      ((D'.isOpen_sheet₁ j).inter ((h3 _).preimage D'.continuous_pt)).union
        ((D'.isOpen_sheet₂ j).inter ((h4 _).preimage D'.continuous_pt))

end TateCovering.Decomp

/-- **Level sets of a function which is constant on the pieces of a finite closed cover** of an
open set are open. -/
lemma isOpen_level_of_pieces {Z : Type*} [TopologicalSpace Z] {ι : Type*} [Finite ι]
    {U : Set Z} (hU : IsOpen U) (P : ι → Set Z) (hP : ∀ i, IsClosed (P i))
    (hcov : ∀ z ∈ U, ∃ i, z ∈ P i) (φ : Z → ℤ) (val : ι → ℤ)
    (hφ : ∀ i, ∀ z ∈ U, z ∈ P i → φ z = val i) (v : ℤ) : IsOpen {z | z ∈ U ∧ φ z = v} := by
  have : {z | z ∈ U ∧ φ z = v} = U ∩ (⋃ i ∈ {i | val i ≠ v}, P i)ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_iUnion,
      exists_prop, not_exists, not_and]
    constructor
    · rintro ⟨hz, rfl⟩
      exact ⟨hz, fun i hi hzi => hi (hφ i z hz hzi).symm⟩
    · rintro ⟨hz, h⟩
      obtain ⟨i, hi⟩ := hcov z hz
      refine ⟨hz, ?_⟩
      by_contra hne
      exact h i (fun e => hne ((hφ i z hz hi).trans e)) hi
  rw [this]
  exact hU.inter ((Set.toFinite _).isClosed_biUnion fun i _ => hP i).isOpen_compl

namespace FourGon

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O]

set_option hygiene false in
local notation "R5" => MvPolynomial (Fin (4 + 1)) O

local notation "𝒜₄" => MvPolynomial.homogeneousSubmodule (Fin (4 + 1)) O
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O

variable (π b₄ b₆ b₄' b₆' ε γ κ : O)

/-! ### The model -/

/-- The linear forms `ℓ = (X₀ + X₂ − ε X₄, X₁ + X₃ + κ X₄, X₄)` of the map to the Tate model. -/
def ℓψ : Fin (2 + 1) → R5 := ![X 0 + X 2 - C ε * X 4, X 1 + X 3 + C κ * X 4, X 4]

lemma isHomogeneous_X_add_X_add_C_mul (a b c : Fin (4 + 1)) (e : O) :
    (X a + X b + C e * X c : R5).IsHomogeneous 1 :=
  ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).add
    ((isHomogeneous_C _ _).mul (isHomogeneous_X _ _))

lemma ℓψ_mem (j : Fin (2 + 1)) : ℓψ ε κ j ∈ 𝒜₄ 1 := by
  rw [mem_homogeneousSubmodule]
  fin_cases j
  · change (X 0 + X 2 - C ε * X 4 : R5).IsHomogeneous 1
    exact ((isHomogeneous_X _ _).add (isHomogeneous_X _ _)).sub
      ((isHomogeneous_C _ _).mul (isHomogeneous_X _ _))
  · exact isHomogeneous_X_add_X_add_C_mul 1 3 4 κ
  · exact isHomogeneous_X O (4 : Fin (4 + 1))

/-- The Tate cubic of `E_q` on the linear forms `ℓ`. -/
def Fℓ : R5 := aeval (ℓψ ε κ) (TateModel.F π b₄ b₆)

/-- The equations of the model. -/
def RelsF (P : Ideal R5) : Prop := Rels π b₄' b₆' ε γ P ∧ Fℓ π b₄ b₆ ε κ ∈ P

lemma isClosed_setOf_mem_projSpace (g : R5) :
    IsClosed {y : projSpace O 4 | g ∈ y.asHomogeneousIdeal} := by
  have e : {y : projSpace O 4 | g ∈ y.asHomogeneousIdeal} =
      (↑(Proj.basicOpen 𝒜₄ g) : Set (Proj 𝒜₄))ᶜ := by
    ext y
    exact not_not.symm
  rw [e]
  exact (Proj.basicOpen 𝒜₄ g).isOpen.isClosed_compl

/-- The closed subset of `ℙ⁴_O` cut out by the equations. -/
def relSet : TopologicalSpace.Closeds (projSpace O 4) :=
  ⟨{y | RelsF π b₄ b₆ b₄' b₆' ε γ κ y.asHomogeneousIdeal.toIdeal}, by
    have hc := isClosed_setOf_mem_projSpace (O := O)
    have : {y : projSpace O 4 | RelsF π b₄ b₆ b₄' b₆' ε γ κ y.asHomogeneousIdeal.toIdeal} =
        {y | cub π b₄' b₆' 0 1 ∈ y.asHomogeneousIdeal} ∩
        ({y | cub π b₄' b₆' 2 3 ∈ y.asHomogeneousIdeal} ∩
        ({y | Q₃ ε γ ∈ y.asHomogeneousIdeal} ∩ ({y | Q₄ ε ∈ y.asHomogeneousIdeal} ∩
        ({y | Q₅ π ε γ ∈ y.asHomogeneousIdeal} ∩
          {y | Fℓ π b₄ b₆ ε κ ∈ y.asHomogeneousIdeal})))) := by
      ext y
      simp only [RelsF, Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
        exact ⟨h1, h2, h3, h4, h5, h6⟩
      · rintro ⟨h1, h2, h3, h4, h5, h6⟩
        exact ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    rw [this]
    exact (hc _).inter ((hc _).inter ((hc _).inter ((hc _).inter ((hc _).inter (hc _)))))⟩

/-- The ideal sheaf of the model. -/
abbrev modelIdeal : (projSpace O 4).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (relSet π b₄ b₆ b₄' b₆' ε γ κ)

/-- **The `4`-gon model**: the reduced closed subscheme of `ℙ⁴_O` on `relSet`. -/
def model : ModelCode O where
  m := 4
  I := modelIdeal π b₄ b₆ b₄' b₆' ε γ κ

/-- The closed immersion of the model into `ℙ⁴_O`. -/
abbrev ιm : (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subscheme ⟶ projSpace O 4 :=
  (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subschemeι

lemma range_ιm : Set.range (ιm π b₄ b₆ b₄' b₆' ε γ κ) =
    {y | RelsF π b₄ b₆ b₄' b₆' ε γ κ y.asHomogeneousIdeal.toIdeal} := by
  rw [Scheme.IdealSheafData.range_subschemeι, modelIdeal,
    Scheme.IdealSheafData.coe_support_vanishingIdeal]
  rfl

lemma relsF_ιm (z : (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subscheme) :
    RelsF π b₄ b₆ b₄' b₆' ε γ κ (ιm π b₄ b₆ b₄' b₆' ε γ κ z).asHomogeneousIdeal.toIdeal := by
  have : ιm π b₄ b₆ b₄' b₆' ε γ κ z ∈ Set.range (ιm π b₄ b₆ b₄' b₆' ε γ κ) := ⟨z, rfl⟩
  rwa [range_ιm] at this

lemma toSpec_eq : (model π b₄ b₆ b₄' b₆' ε γ κ).toSpec =
    ιm π b₄ b₆ b₄' b₆' ε γ κ ≫ projSpace.toSpec O 4 := rfl

/-! ### The model misses the centre of the projection -/

variable {π b₄ b₆ b₄' b₆' ε γ κ}

/-- A point of `ℙ⁴` where `Q₃, Q₅` and the three linear forms vanish does not exist (`2` a
unit). -/
lemma exists_ℓψ_notMem (h2 : IsUnit (2 : O)) (y : projSpace O 4)
    (h3 : Q₃ ε γ ∈ y.asHomogeneousIdeal)
    (h5 : Q₅ π ε γ ∈ y.asHomogeneousIdeal) : ∃ k, ℓψ ε κ k ∉ y.asHomogeneousIdeal := by
  by_contra hall
  push Not at hall
  have hP := y.isPrime
  set q := Ideal.Quotient.mk y.asHomogeneousIdeal.toIdeal
  have hq : ∀ g : R5, q g = 0 ↔ g ∈ y.asHomogeneousIdeal := fun g =>
    Ideal.Quotient.eq_zero_iff_mem
  have e0 := (hq _).2 (hall 0)
  have e1 := (hq _).2 (hall 1)
  have e2 := (hq _).2 (hall 2)
  have e3 := (hq _).2 h3
  have e5 := (hq _).2 h5
  simp only [ℓψ, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, map_add, map_sub, map_mul] at e0 e1 e2
  simp only [Q₃, Q₅, map_add, map_sub, map_mul, map_pow] at e3 e5
  have h2q : IsUnit (2 : R5 ⧸ y.asHomogeneousIdeal.toIdeal) := by
    have := h2.map (algebraMap O (R5 ⧸ y.asHomogeneousIdeal.toIdeal))
    rwa [map_ofNat] at this
  have e02 : q (X 2) = -q (X 0) := by linear_combination e0 + q (C ε) * e2
  have e13 : q (X 3) = -q (X 1) := by linear_combination e1 - q (C κ) * e2
  simp only [e2, e02, mul_zero, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at e3
  have hX0 : q (X 0) = 0 := pow_eq_zero_iff two_ne_zero |>.1 (by linear_combination -e3)
  have hX2 : q (X 2) = 0 := by rw [e02, hX0, neg_zero]
  simp only [e2, e13, hX0, hX2, mul_zero, add_zero, map_ofNat, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at e5
  have hX1 : q (X 1) = 0 := by
    have h4 : (2 * 2 : R5 ⧸ y.asHomogeneousIdeal.toIdeal) * q (X 1) ^ 2 = 0 := by
      linear_combination -e5
    exact pow_eq_zero_iff two_ne_zero |>.1 ((h2q.mul h2q).mul_right_eq_zero.1 h4)
  have hX3 : q (X 3) = 0 := by rw [e13, hX1, neg_zero]
  obtain ⟨i, hi⟩ := exists_X_notMem y
  refine hi ((hq _).1 ?_)
  fin_cases i
  exacts [hX0, hX1, hX2, hX3, e2]

variable (π b₄ b₆ b₄' b₆' ε γ κ)

/-- The model misses the centre of the projection. -/
lemma hcov (h2 : IsUnit (2 : O)) (z : (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subscheme) :
    ∃ k, ιm π b₄ b₆ b₄' b₆' ε γ κ z ∈ D (ℓψ ε κ) (ℓψ_mem ε κ) k := by
  obtain ⟨k, hk⟩ := exists_ℓψ_notMem (κ := κ) h2 _ (relsF_ιm π b₄ b₆ b₄' b₆' ε γ κ z).1.q₃
    (relsF_ιm π b₄ b₆ b₄' b₆' ε γ κ z).1.q₅
  refine ⟨k, ?_⟩
  change linHom (ℓψ ε κ) (ℓψ_mem ε κ) (X k) ∉ _
  rwa [linHom_apply, aeval_X]

/-- The linear projection `[ℓ₀ : ℓ₁ : ℓ₂] : model ⟶ ℙ²_O`. -/
def ψ₀ (h2 : IsUnit (2 : O)) : (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subscheme ⟶ projSpace O 2 :=
  proj (ℓψ ε κ) (ℓψ_mem ε κ) (ιm π b₄ b₆ b₄' b₆' ε γ κ) (hcov π b₄ b₆ b₄' b₆' ε γ κ h2)

lemma ψ₀_toSpec (h2 : IsUnit (2 : O)) :
    ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2 ≫ projSpace.toSpec O 2 =
      ιm π b₄ b₆ b₄' b₆' ε γ κ ≫ projSpace.toSpec O 4 :=
  proj_toSpec _ _ _ _

lemma mem_ψ₀_iff (h2 : IsUnit (2 : O)) {g : MvPolynomial (Fin (2 + 1)) O} {d : ℕ}
    (hg : g ∈ 𝒜₂ d) (hd : 0 < d) (z : (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subscheme) :
    g ∈ (ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2 z).asHomogeneousIdeal ↔
      aeval (ℓψ ε κ) g ∈ (ιm π b₄ b₆ b₄' b₆' ε γ κ z).asHomogeneousIdeal :=
  mem_proj_iff _ hg hd z

instance (h2 : IsUnit (2 : O)) : QuasiCompact (ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2) := by
  have : QuasiCompact (ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2 ≫ projSpace.toSpec O 2) := by
    rw [ψ₀_toSpec]
    haveI : QuasiCompact (projSpace.toSpec O 4) := inferInstance
    infer_instance
  exact .of_comp _ (projSpace.toSpec O 2)

lemma modelIdeal_le_ker (h2 : IsUnit (2 : O)) :
    TateModel.modelIdeal π b₄ b₆ ≤ (ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2).ker := by
  refine le_trans ?_ (TateModel.radical_ker_le _)
  rw [← Scheme.IdealSheafData.vanishingIdeal_support]
  refine Scheme.IdealSheafData.vanishingIdeal_antimono ?_
  change (↑((ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2).ker.support) : Set (projSpace O 2)) ⊆ _
  rw [Scheme.Hom.support_ker]
  refine (TateModel.cubicSet π b₄ b₆).isClosed.closure_subset_iff.2 ?_
  rintro _ ⟨z, rfl⟩
  refine not_not.2 ?_
  rw [mem_ψ₀_iff π b₄ b₆ b₄' b₆' ε γ κ h2
    ((mem_homogeneousSubmodule _ _).2 (TateModel.isHomogeneous_F π b₄ b₆)) three_pos]
  exact (relsF_ιm π b₄ b₆ b₄' b₆' ε γ κ z).2

/-- **The model map `ψ : model ⟶ 𝒯`** to the Tate model of `E_q`. -/
def ψ (h2 : IsUnit (2 : O)) :
    (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subscheme ⟶ (TateModel.modelIdeal π b₄ b₆).subscheme :=
  (ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2).toImage ≫
    Scheme.IdealSheafData.inclusion (modelIdeal_le_ker π b₄ b₆ b₄' b₆' ε γ κ h2)

lemma ψ_ι (h2 : IsUnit (2 : O)) :
    ψ π b₄ b₆ b₄' b₆' ε γ κ h2 ≫ TateModel.ι π b₄ b₆ = ψ₀ π b₄ b₆ b₄' b₆' ε γ κ h2 := by
  rw [ψ, Category.assoc, Scheme.IdealSheafData.inclusion_subschemeι, Scheme.Hom.toImage_imageι]

lemma ψ_toSpec (h2 : IsUnit (2 : O)) :
    ψ π b₄ b₆ b₄' b₆' ε γ κ h2 ≫ TateModel.ι π b₄ b₆ ≫ projSpace.toSpec O 2 =
      ιm π b₄ b₆ b₄' b₆' ε γ κ ≫ projSpace.toSpec O 4 := by
  rw [← Category.assoc, ψ_ι, ψ₀_toSpec]

lemma mem_ψ_iff (h2 : IsUnit (2 : O)) {g : MvPolynomial (Fin (2 + 1)) O} {d : ℕ}
    (hg : g ∈ 𝒜₂ d) (hd : 0 < d) (z : (modelIdeal π b₄ b₆ b₄' b₆' ε γ κ).subscheme) :
    g ∈ (TateModel.ι π b₄ b₆ (ψ π b₄ b₆ b₄' b₆' ε γ κ h2 z)).asHomogeneousIdeal ↔
      aeval (ℓψ ε κ) g ∈ (ιm π b₄ b₆ b₄' b₆' ε γ κ z).asHomogeneousIdeal := by
  rw [← Scheme.Hom.comp_apply, ψ_ι]
  exact mem_ψ₀_iff π b₄ b₆ b₄' b₆' ε γ κ h2 hg hd z

/-! ### The pieces of the special fibre and the sheet functions -/

section Pieces

variable {π b₄ b₆ b₄' b₆' ε γ κ} {P : Ideal R5} [hP : P.IsPrime]

/-- The fibre `ψ⁻¹(p)` of the node `p` of the `2`-gon: `X₄ = X₁ + X₃ = 0`. -/
def Np (P : Ideal R5) : Prop := X 4 ∈ P ∧ X 1 + X 3 ∈ P

omit hP in
lemma sub_mem' {a b : R5} (h : a + b ∈ P) (hb : b ∈ P) : a ∈ P := by
  have := P.sub_mem h hb
  rwa [add_sub_cancel_right] at this

omit hP in
lemma sub_mem'' {a b : R5} (h : a + b ∈ P) (ha : a ∈ P) : b ∈ P := by
  have := P.sub_mem h ha
  rwa [add_sub_cancel_left] at this

omit hP in
lemma all_false (hX : ∃ i, (X i : R5) ∉ P) (h0 : (X 0 : R5) ∈ P) (h1 : (X 1 : R5) ∈ P)
    (h2 : (X 2 : R5) ∈ P) (h3 : (X 3 : R5) ∈ P) (h4 : (X 4 : R5) ∈ P) : False := by
  obtain ⟨i, hi⟩ := hX
  fin_cases i
  exacts [hi h0, hi h1, hi h2, hi h3, hi h4]

omit hP in
lemma lc_not_cp (hX : ∃ i, (X i : R5) ∉ P) (h : Lc P) : ¬ MemCp P :=
  fun ⟨h0, h1, h4, _⟩ => all_false hX h0 h1 h.2.1 h.2.2 h4

omit hP in
lemma cq_lc (h : MemCq P) : Lc P := ⟨h.2.2.1, h.1, h.2.1⟩

omit hP in
lemma cp_gp (h : MemCp P) : Gp P := ⟨h.2.1, h.2.2.2⟩

omit hP in
lemma cp_lb (h : MemCp P) : Lb P := ⟨h.2.2.1, h.1, h.2.1⟩

omit hP in
lemma cq_gm (h : MemCq P) : Gm P := ⟨h.2.2.2, h.2.1⟩

omit hP in
lemma cq_not_lb (hX : ∃ i, (X i : R5) ∉ P) (h : MemCq P) : ¬ Lb P :=
  fun ⟨_, h0, h1⟩ => all_false hX h0 h1 h.1 h.2.1 h.2.2.1

omit hP in
lemma cp_not_gm (hX : ∃ i, (X i : R5) ∉ P) (h : MemCp P) : ¬ Gm P :=
  fun ⟨_, h3⟩ => all_false hX h.1 h.2.1 (sub_mem' h.2.2.2 h3) h3 h.2.2.1

lemma gp_x4 (hR : Rels π b₄' b₆' ε γ P) (hε : C ε ∈ P) (h : Gp P) (h4 : (X 4 : R5) ∈ P) :
    MemCp P ∨ Np P := by
  have r3 := q₃_reduce hR.q₃ hε
  have h02 : X 0 * X 2 ∈ P := by
    have := P.add_mem r3 (P.mul_mem_left (C γ) (P.pow_mem_of_mem h4 2 two_pos))
    rwa [sub_add_cancel] at this
  rcases hP.mem_or_mem h02 with h0 | h2
  · exact Or.inl ⟨h0, h.1, h4, h.2⟩
  · exact Or.inr ⟨h4, by
      have h3 := sub_mem'' h.2 h2
      exact P.add_mem h.1 h3⟩

lemma gm_x4 (hR : Rels π b₄' b₆' ε γ P) (hε : C ε ∈ P) (h : Gm P) (h4 : (X 4 : R5) ∈ P) :
    MemCq P ∨ Np P := by
  have r3 := q₃_reduce hR.q₃ hε
  have h02 : X 0 * X 2 ∈ P := by
    have := P.add_mem r3 (P.mul_mem_left (C γ) (P.pow_mem_of_mem h4 2 two_pos))
    rwa [sub_add_cancel] at this
  rcases hP.mem_or_mem h02 with h0 | h2
  · exact Or.inr ⟨h4, P.add_mem (sub_mem'' h.1 h0) h.2⟩
  · exact Or.inl ⟨h2, h.2, h4, h.1⟩

lemma memA_memB (hR : Rels π b₄' b₆' ε γ P) (hε : C ε ∈ P) (hγ : IsUnit γ)
    (hX : ∃ i, (X i : R5) ∉ P) (hA : MemA P) (hB : MemB P) : MemCp P ∨ MemCq P :=
  (memA_and_memB_iff hR hε hγ hX).1 ⟨hA, hB⟩

lemma lb_memA (hR : Rels π b₄' b₆' ε γ P) (hε : C ε ∈ P) (hγ : IsUnit γ)
    (hX : ∃ i, (X i : R5) ∉ P) (h : Lb P) (hA : MemA P) : MemCp P :=
  (memA_memB hR hε hγ hX hA (Or.inl h)).resolve_right fun hq => cq_not_lb hX hq h

lemma gm_memA (hR : Rels π b₄' b₆' ε γ P) (hε : C ε ∈ P) (hγ : IsUnit γ)
    (hX : ∃ i, (X i : R5) ∉ P) (h : Gm P) (hA : MemA P) : MemCq P :=
  (memA_memB hR hε hγ hX hA (Or.inr h)).resolve_left fun hp => cp_not_gm hX hp h

open Classical in
/-- The parity function `κ = 1` on `A ∖ Cp`, `0` elsewhere. -/
def κf (P : Ideal R5) : ℤ := if MemA P ∧ ¬ MemCp P then 1 else 0

open Classical in
/-- The shift of the `4`-gon decomposition: `0` on `A`, `1` off `A`. -/
def shiftA (P : Ideal R5) : ℤ := if MemA P then 0 else 1

open Classical in
/-- The shift of the `2`-gon decomposition pulled back: `0` on `X₄ = 0`, `1` elsewhere. -/
def shiftC (P : Ideal R5) : ℤ := if (X 4 : R5) ∈ P then 0 else 1

/-- **The values of `κ − shift_C` on the pieces** (off `Cq` and `ψ⁻¹(p)`). -/
lemma κ_sub_shiftC (hR : Rels π b₄' b₆' ε γ P) (hε : C ε ∈ P) (hγ : IsUnit γ)
    (hX : ∃ i, (X i : R5) ∉ P) (hq : ¬ MemCq P) (hn : ¬ Np P) :
    (Lc P → κf P - shiftC P = 1) ∧ (Gp P → κf P - shiftC P = 0) ∧
      (Lb P → κf P - shiftC P = 0) ∧ (Gm P → κf P - shiftC P = -1) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · simp [κf, shiftC, lc_not_cp hX h, h.1, Or.inl h, MemA]
  · by_cases hp : MemCp P
    · simp [κf, shiftC, hp, hp.2.2.1]
    · have h4 : (X 4 : R5) ∉ P := fun h4 => (gp_x4 hR hε h h4).elim hp hn
      simp [κf, shiftC, hp, h4, MemA, h]
  · have : ¬ (MemA P ∧ ¬ MemCp P) := fun ⟨hA, hp⟩ => hp (lb_memA hR hε hγ hX h hA)
    simp [κf, shiftC, this, h.1]
  · have hA : ¬ MemA P := fun hA => hq (gm_memA hR hε hγ hX h hA)
    have h4 : (X 4 : R5) ∉ P := fun h4 => (gm_x4 hR hε h h4).elim hq hn
    simp [κf, shiftC, hA, h4]

/-- **The values of `2 shift_A + κ − shift_C` on the pieces** (off `Cp` and `ψ⁻¹(p)`). -/
lemma two_shiftA_add_κ_sub_shiftC (hR : Rels π b₄' b₆' ε γ P) (hε : C ε ∈ P) (hγ : IsUnit γ)
    (hX : ∃ i, (X i : R5) ∉ P) (hp : ¬ MemCp P) (hn : ¬ Np P) :
    (Lc P → 2 * shiftA P + κf P - shiftC P = 1) ∧ (Gp P → 2 * shiftA P + κf P - shiftC P = 0) ∧
      (Lb P → 2 * shiftA P + κf P - shiftC P = 2) ∧
      (Gm P → 2 * shiftA P + κf P - shiftC P = 1) := by
  have lc : Lc P → 2 * shiftA P + κf P - shiftC P = 1 := fun h => by
    simp [κf, shiftC, shiftA, hp, h.1, Or.inl h, MemA]
  refine ⟨lc, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have h4 : (X 4 : R5) ∉ P := fun h4 => (gp_x4 hR hε h h4).elim hp hn
    simp [κf, shiftC, shiftA, hp, h4, MemA, h]
  · have hA : ¬ MemA P := fun hA => hp (lb_memA hR hε hγ hX h hA)
    simp [κf, shiftC, shiftA, hA, h.1]
  · by_cases hA : MemA P
    · exact lc (cq_lc (gm_memA hR hε hγ hX h hA))
    · have h4 : (X 4 : R5) ∉ P := fun h4 =>
        (gm_x4 hR hε h h4).elim (fun hq => hA (Or.inl (cq_lc hq))) hn
      simp [κf, shiftC, shiftA, hA, h4]

/-- `κ` off `Cp ∪ Cq`: `κ = 1` iff not on `B`. -/
lemma κf_of_not (hR : Rels π b₄' b₆' ε γ P) (hπ : C π ∈ P) (hb : C b₆' ∈ P) (hε : C ε ∈ P)
    (h2 : IsUnit (2 : O)) (hγ : IsUnit γ) (hX : ∃ i, (X i : R5) ∉ P) (hp : ¬ MemCp P)
    (hq : ¬ MemCq P) : (κf P = 1 ↔ ¬ MemB P) ∧ (κf P = 0 ↔ ¬ MemA P) := by
  have hAB := memA_or_memB hR hπ hb hε h2 hγ
  have hnot : ¬ (MemA P ∧ MemB P) := fun ⟨hA, hB⟩ =>
    (memA_memB hR hε hγ hX hA hB).elim hp hq
  by_cases hA : MemA P
  · have hB : ¬ MemB P := fun hB => hnot ⟨hA, hB⟩
    simp [κf, hA, hp, hB]
  · have hB : MemB P := hAB.resolve_left hA
    simp [κf, hA, hB]

/-- **`ψ⁻¹(q) = Cp ∪ Cq`.** -/
lemma x4_x0123_iff (hR : Rels π b₄' b₆' ε γ P) (hπ : C π ∈ P) (hb : C b₆' ∈ P) (hε : C ε ∈ P)
    (h2 : IsUnit (2 : O)) (hγ : IsUnit γ) :
    ((X 4 : R5) ∈ P ∧ X 0 + X 1 + (X 2 + X 3) ∈ P) ↔ MemCp P ∨ MemCq P := by
  constructor
  · rintro ⟨h4, hs⟩
    rcases mem_pieces hR hπ hb hε h2 hγ with h | h | h | h
    · exact Or.inr ⟨h.2.1, h.2.2, h4, sub_mem' hs (P.add_mem h.2.1 h.2.2)⟩
    · have h0 : (X 0 : R5) ∈ P := by
        have : (X 0 + X 1 + (X 2 + X 3) : R5) = X 0 + (X 1 + (X 2 + X 3)) := by ring
        rw [this] at hs
        exact sub_mem' hs (P.add_mem h.1 h.2)
      exact Or.inl ⟨h0, h.1, h4, h.2⟩
    · exact Or.inl ⟨h.2.1, h.2.2, h4, sub_mem'' hs (P.add_mem h.2.1 h.2.2)⟩
    · have h2' : (X 2 : R5) ∈ P := by
        have : (X 0 + X 1 + (X 2 + X 3) : R5) = X 2 + (X 3 + (X 0 + X 1)) := by ring
        rw [this] at hs
        exact sub_mem' hs (P.add_mem h.2 h.1)
      exact Or.inr ⟨h2', h.2, h4, h.1⟩
  · rintro (h | h)
    · exact ⟨h.2.2.1, P.add_mem (P.add_mem h.1 h.2.1) h.2.2.2⟩
    · exact ⟨h.2.2.1, P.add_mem h.2.2.2 (P.add_mem h.1 h.2.1)⟩

end Pieces

end

end FourGon

end TemperedFundamentalGroups
