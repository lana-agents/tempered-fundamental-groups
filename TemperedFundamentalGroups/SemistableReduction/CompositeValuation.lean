/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CentreMap
import TemperedFundamentalGroups.SemistableReduction.MonomialExists
import TemperedFundamentalGroups.SemistableReduction.UniqueExtension

/-!
# Composite valuations (Blueprint §10.3.8, CrossingX1, CX2)

For a valuation subring `W` of a field `F` and a valuation subring `V` of its residue field,
`composite W V = {f ∈ W | f̄ ∈ V}` is a valuation subring of `F` contained in `W`.

* `exists_le_dominates`: inside `W` there is a valuation subring dominating any local ring
  mapping into `W` (the centre of a point on the closure of the centre of `W`);
* `exists_le_lt_one`: **zeros of non-constant functions**: if a unit `g` of `W` has
  `g⁻¹ ∈ 𝔪_R` for some `R ≤ W` containing the image of a DVR `O₁` (with `𝔪_{O₁} ↦ 𝔪_W`), then
  `g ∈ 𝔪_{R'}` for some `R' ≤ W` containing the image of `O₁` (the residue of `g` is
  transcendental over the residue field of `O₁`).
-/

universe u

open IsLocalRing Polynomial

namespace TemperedFundamentalGroups.SemistableReduction.CompositeValuation

variable {F : Type u} [Field F]

/-- The residue of an element of `W`. -/
noncomputable abbrev res (W : ValuationSubring F) : W →+* ResidueField W := residue W

/-- The composite valuation subring. -/
def composite (W : ValuationSubring F) (V : ValuationSubring (ResidueField W)) :
    ValuationSubring F where
  carrier := {f | ∃ h : f ∈ W, res W ⟨f, h⟩ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    have : res W ⟨a * b, mul_mem ha hb⟩ = res W ⟨a, ha⟩ * res W ⟨b, hb⟩ := by
      rw [← map_mul]; rfl
    rw [this]; exact mul_mem ha' hb'
  one_mem' := ⟨W.one_mem, by
    have : res W ⟨1, W.one_mem⟩ = 1 := map_one _
    rw [this]; exact V.one_mem⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨add_mem ha hb, ?_⟩
    have : res W ⟨a + b, add_mem ha hb⟩ = res W ⟨a, ha⟩ + res W ⟨b, hb⟩ := by
      rw [← map_add]; rfl
    rw [this]; exact add_mem ha' hb'
  zero_mem' := ⟨W.zero_mem, by
    have : res W ⟨0, W.zero_mem⟩ = 0 := map_zero _
    rw [this]; exact V.zero_mem⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨neg_mem ha, ?_⟩
    have : res W ⟨-a, neg_mem ha⟩ = -res W ⟨a, ha⟩ := by
      rw [← map_neg]; rfl
    rw [this]; exact neg_mem ha'
  mem_or_inv_mem' := by
    intro f
    rcases W.mem_or_inv_mem f with hf | hf
    · rcases eq_or_ne f 0 with rfl | hf0
      · left; exact ⟨W.zero_mem, by
          have : res W ⟨0, W.zero_mem⟩ = 0 := map_zero _
          rw [this]; exact V.zero_mem⟩
      by_cases hfi : f⁻¹ ∈ W
      · have hu : res W ⟨f, hf⟩ * res W ⟨f⁻¹, hfi⟩ = 1 := by
          rw [← map_mul, ← map_one (res W)]; congr 1; ext; simp [hf0]
        rcases V.mem_or_inv_mem (res W ⟨f, hf⟩) with h | h
        · exact .inl ⟨hf, h⟩
        · refine .inr ⟨hfi, ?_⟩
          rwa [eq_inv_of_mul_eq_one_right hu]
      · -- `f ∈ 𝔪_W`, so its residue is `0`
        have hm : (⟨f, hf⟩ : W) ∈ maximalIdeal W := fun hu ↦ hfi (by
          obtain ⟨w, hw⟩ := hu.exists_right_inv
          have : f⁻¹ = (w : F) := by
            rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ hf0, mul_comm]
            exact congrArg Subtype.val hw
          rw [this]; exact w.2)
        refine .inl ⟨hf, ?_⟩
        rw [show res W _ = 0 from (residue_eq_zero_iff _).2 hm]
        exact V.zero_mem
    · rcases eq_or_ne f 0 with rfl | hf0
      · left; exact ⟨W.zero_mem, by
          have : res W ⟨0, W.zero_mem⟩ = 0 := map_zero _
          rw [this]; exact V.zero_mem⟩
      by_cases hff : f ∈ W
      · have hu : res W ⟨f, hff⟩ * res W ⟨f⁻¹, hf⟩ = 1 := by
          rw [← map_mul, ← map_one (res W)]; congr 1; ext; simp [hf0]
        rcases V.mem_or_inv_mem (res W ⟨f, hff⟩) with h | h
        · exact .inl ⟨hff, h⟩
        · refine .inr ⟨hf, ?_⟩
          rwa [eq_inv_of_mul_eq_one_right hu]
      · have hm : (⟨f⁻¹, hf⟩ : W) ∈ maximalIdeal W := fun hu ↦ hff (by
          obtain ⟨w, hw⟩ := hu.exists_right_inv
          have : f = (w : F) := by
            have h1 : f⁻¹ * (w : F) = 1 := congrArg Subtype.val hw
            exact (inv_mul_eq_one₀ hf0).1 h1
          rw [this]; exact w.2)
        refine .inr ⟨hf, ?_⟩
        rw [show res W _ = 0 from (residue_eq_zero_iff _).2 hm]
        exact V.zero_mem

lemma mem_composite {W : ValuationSubring F} {V : ValuationSubring (ResidueField W)} {f : F} :
    f ∈ composite W V ↔ ∃ h : f ∈ W, res W ⟨f, h⟩ ∈ V := Iff.rfl

lemma composite_le (W : ValuationSubring F) (V : ValuationSubring (ResidueField W)) :
    composite W V ≤ W := fun _ ⟨h, _⟩ ↦ h

/-- For `R ≤ W`, the maximal ideal of `W` lies in that of `R`. -/
lemma valuation_lt_one_of_le {R W : ValuationSubring F} (hRW : R ≤ W) {f : F}
    (hf : W.valuation f < 1) : R.valuation f < 1 := by
  rw [CentreGerms.valuation_lt_one_iff_inv] at hf ⊢
  rcases hf with h | h
  · exact .inl h
  · exact .inr fun h' ↦ h (hRW h')

/-- Elements of `W` whose residue lies in the maximal ideal of `V` lie in the maximal ideal of
the composite. -/
lemma composite_valuation_lt_one {W : ValuationSubring F} {V : ValuationSubring (ResidueField W)}
    {f : F} (hf : f ∈ W) (hV : V.valuation (res W ⟨f, hf⟩) < 1) :
    (composite W V).valuation f < 1 := by
  rw [CentreGerms.valuation_lt_one_iff_inv]
  rcases eq_or_ne f 0 with h0 | h0
  · exact .inl h0
  refine .inr fun ⟨hi, hi'⟩ ↦ ?_
  have hu : res W ⟨f, hf⟩ * res W ⟨f⁻¹, hi⟩ = 1 := by
    rw [← map_mul, ← map_one (res W)]; congr 1; ext; simp [h0]
  rw [CentreGerms.valuation_lt_one_iff_inv] at hV
  rcases hV with h | h
  · rw [h, zero_mul] at hu; exact zero_ne_one hu
  · exact h (by rwa [eq_inv_of_mul_eq_one_right hu] at hi')

/-- **Dominating valuations inside `W`.** -/
theorem exists_le_dominates (W : ValuationSubring F) {A : Type u} [CommRing A] [IsLocalRing A]
    (φ : A →+* F) (hφ : ∀ a, φ a ∈ W) :
    ∃ R : ValuationSubring F, R ≤ W ∧ (∀ a, φ a ∈ R) ∧
      ∀ a ∈ maximalIdeal A, R.valuation (φ a) < 1 := by
  let ρ : A →+* ResidueField W := (res W).comp (φ.codRestrict W.toSubring hφ)
  obtain ⟨V, hV, hloc⟩ := IsLocalRing.exists_factor_valuationRing ρ
  refine ⟨composite W V, composite_le W V, fun a ↦ ⟨hφ a, hV a⟩, fun a ha ↦ ?_⟩
  refine composite_valuation_lt_one (hφ a) ?_
  have hnu : ¬ IsUnit ((ρ.codRestrict V.toSubring hV) a) := fun hu ↦ ha (hloc.map_nonunit a hu)
  exact (ValuationSubring.valuation_lt_one_iff V ⟨ρ a, hV a⟩).1 hnu

end TemperedFundamentalGroups.SemistableReduction.CompositeValuation
