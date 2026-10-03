/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentSetting
import TemperedFundamentalGroups.SemistableReduction.ConstantDescent

/-!
# Residue fields of the vertices over `E` (O1, S7.9 (ii))

Blueprint §9.12, O1. In the setting of `DVRDescentSetting` (`χ : F₀ → F'` over
`ratFuncMap φ : E(x) → C(x)`), for an extension `W ∈ Ext C F'` of the outer Gauss point:

* `resE W`: the residues `red (χ f)` of the elements `f ∈ F₀` with `W(χ f) ≤ 1`, a subring of
  `κ(W)` (the residue field of the restricted vertex `W|_{F₀}`, embedded in `κ(W)`);
* `kE φ`: the residue field of `O_E`, with its embedding into the residue field `𝓀` of `O_C`
  (`kEAlgebra`).
-/

open NNReal Polynomial IsLocalRing Valuation

namespace SemistableReduction

namespace DVRDescent

open GaussTube FundamentalInequality GaussStability GaussFibre

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [Field E] (φ : E →+* C)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- The residue field of `O_E`. -/
abbrev kE : Type _ := ResidueField (vE φ).valuationSubring

/-- `O_E → O_C`. -/
noncomputable def integersMap : (vE φ).valuationSubring →+* HenselComplete.integers C :=
  (φ.comp (vE φ).valuationSubring.subtype).codRestrict _ fun a ↦ by
    have : vE φ a ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).mp a.2
    exact (Valuation.mem_valuationSubring_iff _ _).mpr this

instance : IsLocalHom (integersMap φ) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.valuationSubring.integers _)] at ha
  rw [Valuation.Integers.isUnit_iff_valuation_eq_one (Valuation.valuationSubring.integers _)]
  exact ha

/-- The embedding of residue fields `κ_E → 𝓀`. -/
@[reducible] noncomputable def kEAlgebra : Algebra (kE φ) 𝓀 :=
  (ResidueField.map (integersMap φ)).toAlgebra

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] (χ : F₀ →+* F')

/-- The residues over `E` at a vertex `W` of `F'`: the residues of `χ f`, `f ∈ F₀`, `W(χ f) ≤ 1`.
-/
noncomputable def resE (W : Ext C F') : Subring (ResidueField W.1.valuationSubring) where
  carrier := {z | ∃ f : F₀, W.1 (χ f) ≤ 1 ∧ red C (χ f) W = z}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    refine ⟨f * g, ?_, ?_⟩
    · rw [map_mul, map_mul]; exact mul_le_one' hf hg
    · rw [map_mul, red_mul hf hg]
  one_mem' := ⟨1, by simp, by simp [red_one]⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    refine ⟨f + g, ?_, ?_⟩
    · rw [map_add]; exact (Valuation.map_add _ _ _).trans (max_le hf hg)
    · rw [map_add, red_add hf hg]
  zero_mem' := ⟨0, by simp, by simp [red_zero]⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    refine ⟨-f, by rwa [_root_.map_neg, Valuation.map_neg], ?_⟩
    rw [_root_.map_neg]
    have := red_add hf (by rwa [Valuation.map_neg] : W.1 (-χ f) ≤ 1)
    rw [add_neg_cancel, red_zero] at this
    exact (neg_eq_of_add_eq_zero_right this.symm).symm

end DVRDescent

end SemistableReduction
