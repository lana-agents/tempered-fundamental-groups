/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteE
import TemperedFundamentalGroups.SemistableReduction.W10RouteNorm

/-!
# The routing of G4: `W10.TreeChartsSemistable` from the pointwise descent statements

Blueprint §9.7a, step 4 (G4 (ii)). **`W10Route.treeChartsSemistable`**: the pointwise descent
statements for smooth points (`SmoothDescentStatement`) and for node points
(`NodeDescentStatement`) imply `W10.TreeChartsSemistable`.

Proof. Let `𝔭` be a prime of a chart `B` of the normalization in `F₀` of the tree model over
`O_E`, the center of a valuation subring `W` of `F₀` (Chevalley).

* **Special fibre** (`W ∩ E = O_E`, `isSemistableAt_special`): the local ring of `B` at `W` is that
  of the normalization of a routed standard chart `S` (`exists_routed_normChart`): a vertex chart
  off the child directions, an edge chart at the node, or the chart at `∞` of the root. `W` lifts
  to `W'` on `F'` with `W' ∩ C = O_C` (`exists_lift`); on the corresponding twist of `F'` the
  center of `W'` lies in a point over `C` that is smooth, resp. an ordinary double point, by
  `W7.IsSemistableTree` (`vertexCase`, `closedCase`, `nodeCase`; the twists are matched by
  `smoothOver_aff_aff`, `smoothOver_aff_zero`); the descent statements give semistability over
  `O_E` of the twisted `E`-chart (`DRint 0 1`, `Rint`), which is the normalization of `S`
  (`chartEquiv`); semistability transfers to `B` (`isSemistableAt_of_localAt_eq`, both charts of
  finite type).
* **Generic fibre** (`W ⊇ E`, `isSemistableAt_generic`): `W` has a refinement `W₂ ⊆ W` with
  `W₂ ∩ E = O_E` (`exists_le_special`); a chart of `M'` contains `W₂`, it is semistable at the
  center of `W₂` (special fibre) and hence at its generization, the center of `W`.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

/-! ### Valuations under ring maps -/

section Val

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] (f : K₁ →+* K₂) (W : ValuationSubring K₂)

lemma comap_val_le_one_iff (y : K₁) :
    (W.comap f).valuation y ≤ 1 ↔ W.valuation (f y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
  rfl

lemma comap_val_eq_one_iff (y : K₁) :
    (W.comap f).valuation y = 1 ↔ W.valuation (f y) = 1 := by
  rw [valuation_eq_one_iff_mem_and_inv_mem, valuation_eq_one_iff_mem_and_inv_mem,
    ValuationSubring.mem_comap, ValuationSubring.mem_comap, map_inv₀, Ne, Ne,
    map_eq_zero_iff _ f.injective]

lemma comap_val_lt_one_iff (y : K₁) :
    (W.comap f).valuation y < 1 ↔ W.valuation (f y) < 1 := by
  rw [lt_iff_le_and_ne, lt_iff_le_and_ne, comap_val_le_one_iff, Ne, Ne, comap_val_eq_one_iff]

end Val

/-! ### Isometric embeddings -/

section Isometry

variable {E C : Type*} [NontriviallyNormedField E] [NontriviallyNormedField C]
  [IsUltrametricDist E] [IsUltrametricDist C] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)

include hφ in
lemma valuation_map (e : E) :
    NormedField.valuation (K := C) (φ e) = NormedField.valuation (K := E) e := by
  rw [NormedField.valuation_apply, NormedField.valuation_apply]
  exact NNReal.eq (by simpa using hφ e)

variable {ι : Type*} {aE cE : ι → E}

include hφ in
lemma discLE_map_iff {i j : ι} :
    DiscLE (NormedField.valuation (K := C)) (fun i ↦ φ (aE i)) (fun i ↦ φ (cE i)) i j ↔
      DiscLE (NormedField.valuation (K := E)) aE cE i j := by
  simp only [DiscLE, ← map_sub, valuation_map hφ]

include hφ in
lemma isConvex_of_map
    (h : IsConvex (NormedField.valuation (K := C)) (fun i ↦ φ (aE i)) (fun i ↦ φ (cE i))) :
    IsConvex (NormedField.valuation (K := E)) aE cE := by
  intro i j
  obtain ⟨k, hik, hjk, hk⟩ := h i j
  refine ⟨k, (discLE_map_iff hφ).1 hik, (discLE_map_iff hφ).1 hjk, ?_⟩
  simpa only [← map_sub, valuation_map hφ] using hk

include hφ in
lemma isReduced_of_map
    (h : IsReduced (NormedField.valuation (K := C)) (fun i ↦ φ (aE i)) (fun i ↦ φ (cE i))) :
    IsReduced (NormedField.valuation (K := E)) aE cE := fun i j hij hji ↦
  h i j ((discLE_map_iff hφ).2 hij) ((discLE_map_iff hφ).2 hji)

end Isometry

/-! ### Valuation subrings over `O_C` -/

lemma isOverOC_of_comap {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
    {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G] [IsScalarTower C (RatFunc C) G]
    (W' : ValuationSubring G)
    (h : W'.comap (algebraMap C G) = (NormedField.valuation (K := C)).valuationSubring) :
    IsOverOC C W' := fun k ↦ by
  rw [← IsScalarTower.algebraMap_apply C (RatFunc C) G, ValuationSubring.valuation_le_one_iff]
  change k ∈ W'.comap (algebraMap C G) ↔ _
  rw [h, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

/-! ### Refining generic-fibre valuations -/

section Refine

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {F₀ : Type*} [Field F₀] [Algebra E F₀]

set_option hygiene false in
local notation "κE" o => algebraMap E F₀ o

variable (W : ValuationSubring F₀) (hWE : ∀ e : E, (κE e) ∈ W)

omit [IsUltrametricDist E] in
include hWE in
lemma refine_mul {x y : F₀} {o₁ o₂ : E} (h₁ : W.valuation (x - κE o₁) < 1)
    (h₂ : W.valuation (y - κE o₂) < 1) : W.valuation (x * y - κE (o₁ * o₂)) < 1 := by
  have hv : ∀ e, W.valuation (κE e) ≤ 1 := fun e ↦ (W.valuation_le_one_iff _).2 (hWE e)
  have e1 : x * y - (κE (o₁ * o₂)) = (x - κE o₁) * (y - κE o₂) + (κE o₁) * (y - κE o₂) +
      (κE o₂) * (x - κE o₁) := by rw [map_mul]; ring
  rw [e1]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_add _ _ _).trans_lt
    (max_lt ?_ ?_)) ?_) <;> rw [Valuation.map_mul]
  · exact mul_lt_one_of_nonneg_of_lt_one_left zero_le h₁ h₂.le
  · exact mul_lt_one_of_nonneg_of_lt_one_right (hv o₁) zero_le h₂
  · exact mul_lt_one_of_nonneg_of_lt_one_right (hv o₂) zero_le h₁

omit [IsUltrametricDist E] in
include hWE in
/-- The constant of an element of `E + 𝔪_W` is unique. -/
lemma refine_unique {x : F₀} {o o' : E} (h : W.valuation (x - κE o) < 1)
    (h' : W.valuation (x - κE o') < 1) : o = o' := by
  by_contra hne
  have hu : W.valuation (κE (o' - o)) = 1 := by
    rw [valuation_eq_one_iff_mem_and_inv_mem, ← map_inv₀]
    exact ⟨by simpa [sub_eq_zero] using Ne.symm hne, hWE _, hWE _⟩
  have : (κE (o' - o)) = (x - κE o) - (x - κE o') := by rw [map_sub]; ring
  rw [this] at hu
  exact (lt_irrefl _ (hu ▸ (Valuation.map_sub _ _ _).trans_lt (max_lt h h')))

/-- The subring `O_E + 𝔪_W` of a valuation subring `W ⊇ E`. -/
def refineRing : Subring F₀ where
  carrier := {x | ∃ o : E, ‖o‖ ≤ 1 ∧ W.valuation (x - κE o) < 1}
  zero_mem' := ⟨0, by simp, by simp⟩
  one_mem' := ⟨1, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨o₁, ho₁, h₁⟩ ⟨o₂, ho₂, h₂⟩
    refine ⟨o₁ + o₂, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ho₁ ho₂), ?_⟩
    have : x + y - (κE (o₁ + o₂)) = (x - κE o₁) + (y - κE o₂) := by rw [map_add]; ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt h₁ h₂)
  neg_mem' := by
    rintro x ⟨o, ho, h⟩
    refine ⟨-o, by simpa using ho, ?_⟩
    have : -x - (κE (-o)) = -(x - κE o) := by rw [map_neg]; ring
    rw [this, Valuation.map_neg]
    exact h
  mul_mem' := by
    rintro x y ⟨o₁, ho₁, h₁⟩ ⟨o₂, ho₂, h₂⟩
    exact ⟨o₁ * o₂, by rw [norm_mul]; exact mul_le_one₀ ho₁ (norm_nonneg _) ho₂,
      refine_mul W hWE h₁ h₂⟩

/-- The maximal ideal `𝔪_E + 𝔪_W` of `O_E + 𝔪_W`. -/
def refineIdeal : Ideal (refineRing W hWE) where
  carrier := {x | ∃ o : E, ‖o‖ < 1 ∧ W.valuation ((x : F₀) - κE o) < 1}
  zero_mem' := ⟨0, by simp, by simp⟩
  add_mem' := by
    rintro x y ⟨o₁, ho₁, h₁⟩ ⟨o₂, ho₂, h₂⟩
    refine ⟨o₁ + o₂, (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ho₁ ho₂), ?_⟩
    have : ((x + y : refineRing W hWE) : F₀) - (κE (o₁ + o₂)) =
        ((x : F₀) - κE o₁) + ((y : F₀) - κE o₂) := by
      rw [map_add, Subring.coe_add]; ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt h₁ h₂)
  smul_mem' := by
    rintro ⟨r, o₁, ho₁, h₁⟩ x ⟨o₂, ho₂, h₂⟩
    have hn : ‖o₁ * o₂‖ < 1 := by
      rw [norm_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right ho₁ (norm_nonneg _) ho₂
    exact ⟨o₁ * o₂, hn, refine_mul W hWE h₁ h₂⟩

instance refineIdeal_isPrime : (refineIdeal W hWE).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one]
    rintro ⟨o, ho, h⟩
    have h1 : W.valuation ((1 : F₀) - κE (1 : E)) < 1 := by simp
    have := refine_unique W hWE h h1
    subst this
    simp at ho
  mem_or_mem' := by
    rintro ⟨x, o₁, ho₁, h₁⟩ ⟨y, o₂, ho₂, h₂⟩ ⟨o, ho, h⟩
    have hxy := refine_mul W hWE h₁ h₂
    have := refine_unique W hWE h hxy
    subst this
    by_contra hne
    push Not at hne
    rw [norm_mul] at ho
    have h₁' : 1 ≤ ‖o₁‖ := not_lt.1 fun hlt ↦ hne.1 ⟨o₁, hlt, h₁⟩
    have h₂' : 1 ≤ ‖o₂‖ := not_lt.1 fun hlt ↦ hne.2 ⟨o₂, hlt, h₂⟩
    exact absurd ho (not_lt.2 (one_le_mul_of_one_le_of_one_le h₁' h₂'))

variable {ϖ : (NormedField.valuation (K := E)).valuationSubring}

include hWE in
/-- **Refining a generic-fibre valuation**: a valuation subring `W ⊇ E` of `F₀` contains a
valuation subring `W₂` with `W₂ ∩ E = O_E` (the composite with `O_E` on the residue field). -/
theorem exists_le_special
    [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
    (hϖ : Irreducible ϖ) :
    ∃ W₂ : ValuationSubring F₀, W₂ ≤ W ∧
      W₂.comap (algebraMap E F₀) = (NormedField.valuation (K := E)).valuationSubring := by
  obtain ⟨W₂, hRW, hcen⟩ := exists_centerIdeal_eq (refineRing W hWE) (refineIdeal W hWE)
  have hmem : ∀ x (h : x ∈ refineRing W hWE), (⟨x, h⟩ : refineRing W hWE) ∈ refineIdeal W hWE →
      W₂.valuation x < 1 := by
    intro x h hx
    rw [← hcen, mem_centerIdeal_iff] at hx
    exact hx
  refine ⟨W₂, fun f hf ↦ ?_, ?_⟩
  · by_contra hfW
    have hf0 : f ≠ 0 := by rintro rfl; exact hfW (zero_mem W)
    have hinv : W.valuation f⁻¹ < 1 := by
      have h1 : f⁻¹ ∈ W := (W.mem_or_inv_mem f).resolve_left hfW
      refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 h1) fun h ↦ hfW ?_
      rw [map_inv₀, inv_eq_one] at h
      exact (W.valuation_le_one_iff _).1 h.le
    have hR : f⁻¹ ∈ refineRing W hWE := ⟨0, by simp, by simpa using hinv⟩
    have h2 := hmem _ hR ⟨0, by simp, by simpa using hinv⟩
    have h3 : W₂.valuation f ≤ 1 := (W₂.valuation_le_one_iff _).2 hf
    have : W₂.valuation (f * f⁻¹) < 1 := by
      rw [map_mul]; exact mul_lt_one_of_nonneg_of_lt_one_right h3 zero_le h2
    rw [mul_inv_cancel₀ hf0, map_one] at this
    exact lt_irrefl _ this
  · have hO : (NormedField.valuation (K := E)).valuationSubring ≤ W₂.comap (algebraMap E F₀) := by
      intro o ho
      have ho' : ‖o‖ ≤ 1 := by
        have : NormedField.valuation (K := E) o ≤ 1 := ho
        rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at this
        simpa using this
      exact hRW ⟨o, ho', by simp⟩
    rcases eq_or_eq_top_of_le hϖ _ hO with h | h
    · exact h
    · exfalso
      have hϖ1 : ‖(ϖ : E)‖ < 1 := by
        have h' := (Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one.not.mp
          hϖ.not_isUnit
        have h'' : NormedField.valuation (K := E) (ϖ : E) ≤ 1 := ϖ.2
        have := lt_of_le_of_ne h'' h'
        rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe] at this
        simpa using this
      have hR : (κE (ϖ : E)) ∈ refineRing W hWE := ⟨ϖ, hϖ1.le, by simp⟩
      have hlt := hmem _ hR ⟨ϖ, hϖ1, by simp⟩
      have hϖ0 : (ϖ : E) ≠ 0 := fun h ↦ hϖ.ne_zero (Subtype.ext h)
      have hinv : (κE (ϖ : E)⁻¹) ∈ W₂ := by
        have : (ϖ : E)⁻¹ ∈ W₂.comap (algebraMap E F₀) := by rw [h]; trivial
        exact this
      have : W₂.valuation ((κE (ϖ : E)) * κE (ϖ : E)⁻¹) < 1 := by
        rw [map_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hlt
          ((W₂.valuation_le_one_iff _).2 hinv)
      rw [← map_mul, mul_inv_cancel₀ hϖ0, map_one, map_one] at this
      exact lt_irrefl _ this

end Refine

end W10Route

end SemistableReduction
