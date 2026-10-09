/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10MainE
import TemperedFundamentalGroups.SemistableReduction.W10Discs
import TemperedFundamentalGroups.SemistableReduction.Splitting

/-!
# From the Gauss tree over `C` to the Gauss tree over `E`

Blueprint §9.7a, steps 3–4.

* `tree_descent`: a convex reduced `Gal`-stable Gauss tree over `C` with centres and radii in an
  isometrically embedded `E` is a convex reduced `Gal(E/K)`-stable tree over `E`.
* `comap_comap_eq_gauss`: a valuation subring over a disc of `V₀ ⊆ V` restricts, along a field map
  `χ` over `ratFuncMap φ`, to the Gauss valuation ring of a disc of the tree over `E` (the input
  `hV'` of `strongA_body_of_tree`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] (φ : E →+* C)
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

include hφ in
lemma valuation_comap_eq_of_isometry : (ν).comap φ = νE := by
  ext x
  rw [Valuation.comap_apply, NormedField.valuation_apply, NormedField.valuation_apply]
  rw [show ‖φ x‖₊ = ‖x‖₊ from NNReal.eq (hφ x)]

variable {ι : Type*} {a c : ι → C} {aE cE : ι → E} (haE : ∀ i, φ (aE i) = a i)
  (hcE : ∀ i, φ (cE i) = c i)

include hφ haE hcE in
lemma isConvex_descent (h : GaussTree.IsConvex ν a c) : GaussTree.IsConvex νE aE cE := by
  rw [← valuation_comap_eq_of_isometry φ hφ, isConvex_comap_iff]
  convert h using 1 <;> ext i <;> simp [haE, hcE]

include hφ haE hcE in
lemma isReduced_descent (h : GaussTree.IsReduced ν a c) : GaussTree.IsReduced νE aE cE := by
  rw [← valuation_comap_eq_of_isometry φ hφ, isReduced_comap_iff]
  convert h using 1 <;> ext i <;> simp [haE, hcE]

omit [IsUltrametricDist C] in
include hφ haE hcE in
/-- **Galois stability descends**: if `τ` on `C` extends `σ` on `E` and is isometric, and the tree
over `C` is `τ`-stable, then the tree over `E` is `σ`-stable. -/
lemma stab_descent (σ : E →+* E) (τ : C →+* C) (hτσ : ∀ e, τ (φ e) = φ (σ e))
    (hτ : ∀ z, ‖τ z‖ = ‖z‖) (h : W7.DiscsLE (fun i ↦ τ (a i)) c a c) (i : ι) :
    ∃ i', νE (σ (cE i)) = νE (cE i') ∧ νE (σ (aE i) - aE i') ≤ νE (cE i') := by
  obtain ⟨i', h₁, h₂⟩ := h i
  refine ⟨i', ?_, ?_⟩
  · rw [NormedField.valuation_apply, NormedField.valuation_apply]
    refine NNReal.eq ?_
    simp only [coe_nnnorm]
    rw [← hφ, ← hφ, ← hτσ, hτ, hcE, hcE, h₁]
  · rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_le_coe]
    simp only [coe_nnnorm]
    rw [← hφ, ← hφ, map_sub, ← hτσ, haE, haE, hcE, ← norm_neg, neg_sub]
    exact h₂

section Gauss

variable [IsAlgClosed C] {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* F'}
  (hχ : ∀ x, χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) F' (ratFuncMap φ x))

include hφ haE hcE hχ in
/-- **Restriction of the centres to `E(X)`**: a valuation subring of `F'` over a disc of
`V₀ ⊆ V` restricts along `χ` to the Gauss valuation ring of a disc of the tree over `E`. -/
theorem comap_comap_eq_gauss (hc : ∀ i, c i ≠ 0) (hcE0 : ∀ i, cE i ≠ 0) {ι₀ : Type*}
    {a₀ c₀ : ι₀ → C} (hc₀ : ∀ k, c₀ k ≠ 0) (hle : W7.DiscsLE a₀ c₀ a c)
    {W : ValuationSubring F'} {k : ι₀}
    (hW : W.comap (algebraMap (RatFunc C) F') = (gaussRat ν (a₀ k)
      (Units.mk0 (ν (c₀ k)) ((Valuation.ne_zero_iff _).2 (hc₀ k)))).valuationSubring) :
    ∃ j, (W.comap χ).comap (algebraMap (RatFunc E) F₀) = (gaussRat νE (aE j)
      (Units.mk0 (νE (cE j)) ((Valuation.ne_zero_iff _).2 (hcE0 j)))).valuationSubring := by
  obtain ⟨j, h₁, h₂⟩ := hle k
  refine ⟨j, ?_⟩
  have hr : (Units.mk0 (ν (c₀ k)) ((Valuation.ne_zero_iff _).2 (hc₀ k))) =
      Units.mk0 (ν (c j)) ((Valuation.ne_zero_iff _).2 (hc j)) := by
    ext
    simp only [Units.val_mk0, NormedField.valuation_apply]
    rw [show ‖c₀ k‖₊ = ‖c j‖₊ from NNReal.eq (by simpa using h₁.symm)]
  have hga : gaussRat ν (a₀ k) (Units.mk0 (ν (c₀ k)) ((Valuation.ne_zero_iff _).2 (hc₀ k))) =
      gaussRat ν (a j) (Units.mk0 (ν (c j)) ((Valuation.ne_zero_iff _).2 (hc j))) := by
    rw [hr]
    refine Splitting.gaussRat_eq_of_le ?_
    simp only [Units.val_mk0, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm]
    rw [← norm_neg, neg_sub]
    exact h₂
  rw [hga] at hW
  have hcomp : χ.comp (algebraMap (RatFunc E) F₀) =
      (algebraMap (RatFunc C) F').comp (ratFuncMap φ) := RingHom.ext hχ
  rw [ValuationSubring.comap_comap, hcomp, ← ValuationSubring.comap_comap, hW, ← haE j,
    comap_valuationSubring_gaussRat, valuation_comap_eq_of_isometry φ hφ]
  congr 2
  ext
  simp only [Units.val_mk0, ← hcE j]
  rw [← valuation_comap_eq_of_isometry φ hφ, Valuation.comap_apply]

end Gauss

end W10Assembly

end SemistableReduction
