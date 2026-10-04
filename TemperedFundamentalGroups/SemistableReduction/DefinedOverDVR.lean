/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussDescent

/-!
# Function fields defined over a complete discretely valued subfield

Blueprint §9.10, R4 (setting of the descent (a1)). For a non-archimedean field `C` and a finite
extension `F' / C(x)`, `DefinedOverDVR C F'` says that `F'` comes from a function field over a
complete discretely valued subfield `K ⊆ C` over which `C` is algebraic, and that every finite
subset of `C` lies in a finitely generated (hence finite) complete discretely valued extension
`E ⊇ K` inside `C` (the W9 setting: `C` an algebraic closure of a complete discretely valued
field of characteristic `0`):

* there are `K`, and a primitive element `θ` of `F' / C(x)` whose minimal polynomial has
  coefficients in `K(x)` (`ratFuncMap K → C`), so that `F' = K(x)(θ) ⊗_{K(x)} C(x)`;
* for every finite `S ⊆ C` there is `E = K(T)` (`T` finite) containing `S`, complete with
  discrete valuation ring of integers.

The descent of the C-level ordinary double points (`GaussTube.IsNodeODP`) to such `E` and the
exact node data (`GaussTube.NodeData`) are §9.10 L3 (a1) (in progress elsewhere).
-/

open Polynomial

namespace SemistableReduction

universe u

/-- The integers of a subfield `E ⊆ C` (for the restriction of the norm of `C`) form a complete
discrete valuation ring. -/
def IsCompleteDVRSubfield {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
    (E : Subfield C) : Prop :=
  IsDiscreteValuationRing ((NormedField.valuation (K := C)).comap E.subtype).valuationSubring ∧
    IsComplete (E : Set C)

/-- **`F'` is defined over a complete discretely valued subfield of `C`**, and `C` is exhausted
by finitely generated complete discretely valued extensions of it. -/
def DefinedOverDVR (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] (F' : Type*)
    [Field F'] [Algebra (RatFunc C) F'] : Prop :=
  ∃ K : Subfield C, IsCompleteDVRSubfield K ∧ Algebra.IsAlgebraic K C ∧
    (∀ S : Finset C, ∃ T : Finset C, (∀ s ∈ S, s ∈ Subfield.closure ((K : Set C) ∪ T)) ∧
      IsCompleteDVRSubfield (Subfield.closure ((K : Set C) ∪ T))) ∧
    ∃ θ : F', Algebra.adjoin (RatFunc C) {θ} = ⊤ ∧
      ∀ i, (minpoly (RatFunc C) θ).coeff i ∈ (ratFuncMap K.subtype).range

section Transfer

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

omit [IsUltrametricDist C] in
lemma closure_union_eq {K : Subfield C} {T T' : Finset C}
    (hT : ∀ t ∈ T, t ∈ Subfield.closure ((K : Set C) ∪ T')) :
    Subfield.closure ((Subfield.closure ((K : Set C) ∪ T) : Set C) ∪ T') =
      Subfield.closure ((K : Set C) ∪ T') := by
  apply le_antisymm
  · refine Subfield.closure_le.2 (Set.union_subset ?_ (fun t ht ↦
      Subfield.subset_closure (Or.inr ht)))
    refine Subfield.closure_le.2 (Set.union_subset (fun t ht ↦ Subfield.subset_closure
      (Or.inl ht)) fun t ht ↦ hT t ht)
  · refine Subfield.closure_le.2 (Set.union_subset (fun t ht ↦ ?_) fun t ht ↦
      Subfield.subset_closure (Or.inr ht))
    exact Subfield.subset_closure (Or.inl (Subfield.subset_closure (Or.inl ht)))

omit [IsUltrametricDist C] in
/-- A rational function whose numerator and denominator have coefficients in `E` comes from
`E(x)`. -/
lemma mem_range_ratFuncMap {E : Subfield C} {f : RatFunc C}
    (hnum : ∀ c ∈ f.num.coeffs, c ∈ E) (hden : ∀ c ∈ f.denom.coeffs, c ∈ E) :
    f ∈ (ratFuncMap E.subtype).range := by
  have hlift (p : C[X]) (hp : ∀ c ∈ p.coeffs, c ∈ E) : p ∈ Polynomial.lifts E.subtype := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h : p.coeff n = 0
    · exact ⟨0, by rw [h, map_zero]⟩
    · exact ⟨⟨_, hp _ (Polynomial.coeff_mem_coeffs h)⟩, rfl⟩
  obtain ⟨p, hp⟩ := hlift _ hnum
  obtain ⟨q, hq⟩ := hlift _ hden
  refine ⟨algebraMap E[X] (RatFunc E) p / algebraMap E[X] (RatFunc E) q, ?_⟩
  rw [coe_mapRingHom] at hp hq
  rw [map_div₀, ratFuncMap_algebraMap, ratFuncMap_algebraMap, hp, hq, RatFunc.num_div_denom]

omit [IsUltrametricDist C] in
lemma isAlgebraic_of_le {K E : Subfield C} (hle : K ≤ E) {x : C} (hx : IsAlgebraic K x) :
    IsAlgebraic E x := by
  obtain ⟨p, hp0, hp⟩ := hx
  refine ⟨p.map (Subfield.inclusion hle), (Polynomial.map_ne_zero_iff
    (Subfield.inclusion hle).injective).2 hp0, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hp

/-- **O2: `DefinedOverDVR` passes to every finite separable extension of `C(x)`** (in particular
to all intermediate fields of the Galois closure): the condition on `C` is independent of the
field, and a primitive element of the new field has a minimal polynomial with coefficients in
`E(x)` for a finitely generated complete discretely valued `E ⊇ K` containing the finitely many
coefficients involved. -/
theorem DefinedOverDVR.of_finite {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
    (h : DefinedOverDVR C F') (L : Type*) [Field L] [Algebra (RatFunc C) L]
    [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L] :
    DefinedOverDVR C L := by
  classical
  obtain ⟨K, -, halg, hS, -⟩ := h
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (RatFunc C) L
  set μ := minpoly (RatFunc C) α
  set S : Finset C := (Finset.range (μ.natDegree + 1)).biUnion fun i ↦
    (μ.coeff i).num.coeffs ∪ (μ.coeff i).denom.coeffs
  obtain ⟨T, hTS, hT⟩ := hS S
  set E := Subfield.closure ((K : Set C) ∪ T)
  have hKE : K ≤ E := fun x hx ↦ Subfield.subset_closure (Or.inl hx)
  refine ⟨E, hT, ⟨fun x ↦ isAlgebraic_of_le hKE (halg.isAlgebraic x)⟩, fun S' ↦ ?_, α, ?_,
    fun i ↦ ?_⟩
  · obtain ⟨T'', h1, h2⟩ := hS (S' ∪ T)
    refine ⟨T'', ?_, ?_⟩
    · rw [closure_union_eq fun t ht ↦ h1 t (Finset.mem_union_right _ ht)]
      exact fun s hs ↦ h1 s (Finset.mem_union_left _ hs)
    · rw [closure_union_eq fun t ht ↦ h1 t (Finset.mem_union_right _ ht)]
      exact h2
  · have hint : IsAlgebraic (RatFunc C) α := Algebra.IsAlgebraic.isAlgebraic α
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint, hα,
      IntermediateField.top_toSubalgebra]
  · by_cases hi : i ≤ μ.natDegree
    · have hmem : ∀ c, c ∈ (μ.coeff i).num.coeffs ∪ (μ.coeff i).denom.coeffs → c ∈ E :=
        fun c hc ↦ hTS c (Finset.mem_biUnion.2 ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), hc⟩)
      exact mem_range_ratFuncMap (fun c hc ↦ hmem c (Finset.mem_union_left _ hc))
        (fun c hc ↦ hmem c (Finset.mem_union_right _ hc))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
      exact zero_mem _

end Transfer

end SemistableReduction
