/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Exhausting
import TemperedFundamentalGroups.SemistableReduction.NodeMaximum
import TemperedFundamentalGroups.SemistableReduction.TreeBridge
import TemperedFundamentalGroups.SemistableReduction.NodeUpward
import TemperedFundamentalGroups.SemistableReduction.GaussTreeSemistable
import TemperedFundamentalGroups.SemistableReduction.GaussTreeFinite

/-!
# Gluing of exhausting discs: intersections of node charts (O11, preparation)

Blueprint §9.12, O11. For `|c'| ≤ |e| ≤ |u| ≤ 1` the annulus `|c'| ≤ |t| ≤ 1` is the union of the
annuli `|e| ≤ |t| ≤ 1` and `|c'| ≤ |t| ≤ |u|`, and its (normalized) node chart is the intersection
of theirs:

* `nodeRing_eq_inf`: `O_C[x, c'/x] = O_C[x, e/x] ∩ O_C[x/u, c'/x]` (Laurent polynomials with
  Gauss value `≤ 1` at the two ends, `mem_nodeRing_of_mul_pow`);
* `nodeChart_coord_eq_inf`: the same in the coordinate `t = (x - a)/c`;
* `isIntegral_inf_iff`, `normChart_inf`: integrality over the intersection of two integrally
  closed subrings with the same fraction field (minimal polynomials);
* **`mem_rint_iff_and`**: `Rint c' (Aff a c F') = Rint e (Aff a c F') ∩ Rint (c'/u) (Aff a (cu) F')`
  as subsets of `F'`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace ExhaustGluing

open GaussTube ZariskiModel

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- A function in the subring generated over `O_C` by functions of Gauss value `≤ 1` has Gauss
value `≤ 1`. -/
lemma gaussRat_le_one_of_mem_closure (s : ℝ≥0ˣ) {S : Set (RatFunc C)} (hS : ∀ g ∈ S, w s g ≤ 1)
    {f : RatFunc C} (hf : f ∈ Subring.closure
      ((baseRing (RatFunc C) (NormedField.valuation (K := C)).valuationSubring :
        Set (RatFunc C)) ∪ S)) : w s f ≤ 1 := by
  have hle : Subring.closure
      ((baseRing (RatFunc C) (NormedField.valuation (K := C)).valuationSubring :
        Set (RatFunc C)) ∪ S) ≤ (w s).valuationSubring.toSubring := by
    refine Subring.closure_le.2 (Set.union_subset ?_ fun g hg ↦ hS g hg)
    rintro _ ⟨o, ho, rfl⟩
    change w s (algebraMap C (RatFunc C) o) ≤ 1
    rw [gaussRat_C]
    have : ν o ≤ 1 := ho
    rwa [NormedField.valuation_apply] at this
  exact hle hf

/-- Elements of the node chart are Laurent polynomials. -/
lemma exists_mul_pow_eq {c : C} {f : RatFunc C} (hf : f ∈ nodeRing c) :
    ∃ (k : ℕ) (Q : C[X]), f * RatFunc.X ^ k = algebraMap C[X] (RatFunc C) Q := by
  induction hf using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, -, rfl⟩ | rfl | rfl
    · exact ⟨0, Polynomial.C b, by simp [RatFunc.algebraMap_C]⟩
    · exact ⟨0, Polynomial.X, by simp⟩
    · refine ⟨1, Polynomial.C c, ?_⟩
      rw [pow_one, div_mul_cancel₀ _ RatFunc.X_ne_zero, RatFunc.algebraMap_C]
      rfl
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, Q, hQ⟩ := ha
    obtain ⟨l, R, hR⟩ := hb
    refine ⟨k + l, Q * Polynomial.X ^ l + R * Polynomial.X ^ k, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hQ, ← hR, RatFunc.algebraMap_X]
    ring
  | neg a _ ha =>
    obtain ⟨k, Q, hQ⟩ := ha
    exact ⟨k, -Q, by rw [map_neg, ← hQ]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, Q, hQ⟩ := ha
    obtain ⟨l, R, hR⟩ := hb
    exact ⟨k + l, Q * R, by rw [map_mul, ← hQ, ← hR]; ring⟩

/-- **Intersection of node charts** (in the coordinate `x`): for `|c'| ≤ |e| ≤ |u| ≤ 1`, the chart
`O_C[x, c'/x]` of the annulus `|c'| ≤ |x| ≤ 1` is the intersection of the charts
`O_C[x, e/x]` and `O_C[x/u, c'/x]` of the annuli `|e| ≤ |x| ≤ 1` and `|c'| ≤ |x| ≤ |u|`. -/
theorem nodeRing_eq_inf {c' e u : C} (hc'0 : c' ≠ 0) (hu0 : u ≠ 0) (hc'e : ‖c'‖ ≤ ‖e‖)
    (heu : ‖e‖ ≤ ‖u‖) (hu1 : ‖u‖ ≤ 1) :
    nodeRing c' = nodeRing e ⊓
      nodeChart ν (RatFunc.X / algebraMap C (RatFunc C) u) (c' / u) := by
  have he0 : e ≠ 0 := norm_pos_iff.1 ((norm_pos_iff.2 hc'0).trans_le hc'e)
  have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have hu' : algebraMap C (RatFunc C) u ≠ 0 := by simpa using hu0
  have hwX : ∀ s : ℝ≥0ˣ, w s RatFunc.X = s := gaussRat_X
  set su : ℝ≥0ˣ := Units.mk0 ‖c'‖₊ (by simpa using hc'0)
  refine le_antisymm (le_inf ?_ ?_) fun f ⟨hf₁, hf₂⟩ ↦ ?_
  · exact nodeRing_le hc'e he0
  · refine nodeChart_le baseRing_le_nodeChart ?_ ?_
    · have hmem := mul_mem (baseRing_le_nodeChart (v := NormedField.valuation (K := C))
        (y := RatFunc.X / algebraMap C (RatFunc C) u) (c := c' / u)
        (algebraMap_mem_baseRing' (c := u) (by
          rw [NormedField.valuation_apply]; exact_mod_cast hu1))) self_mem_nodeChart
      rwa [mul_div_cancel₀ _ hu'] at hmem
    · have hmem := div_mem_nodeChart (v := NormedField.valuation (K := C))
        (y := RatFunc.X / algebraMap C (RatFunc C) u) (c := c' / u)
      rwa [map_div₀, div_div_div_cancel_right₀ hu'] at hmem
  · obtain ⟨k, Q, hQ⟩ := exists_mul_pow_eq hf₁
    refine mem_nodeRing_of_mul_pow hc'0 hQ ?_ ?_
    · refine gaussRat_le_one_of_mem_closure 1 ?_ hf₁
      rintro g (rfl | hg)
      · rw [hwX]; rfl
      · rw [Set.mem_singleton_iff] at hg
        rw [hg, map_div₀, gaussRat_C, hwX, Units.val_one, div_one]
        exact_mod_cast heu.trans hu1
    · refine gaussRat_le_one_of_mem_closure _ ?_ hf₂
      rintro g (rfl | hg)
      · rw [map_div₀, gaussRat_C, hwX]
        refine div_le_one_of_le₀ ?_ zero_le
        change ‖c'‖₊ ≤ ‖u‖₊
        exact_mod_cast hc'e.trans heu
      · rw [Set.mem_singleton_iff] at hg
        rw [hg, map_div₀ (algebraMap C (RatFunc C)), div_div_div_cancel_right₀ hu', map_div₀,
          gaussRat_C, hwX]
        change ‖c'‖₊ / ‖c'‖₊ ≤ 1
        exact div_self_le_one _


/-- Ring maps over `C` carry node charts to node charts. -/
lemma map_nodeChart (φ : RatFunc C →ₐ[C] RatFunc C) (z : RatFunc C) (γ : C) :
    (nodeChart ν z γ).map φ.toRingHom = nodeChart ν (φ z) γ := by
  rw [nodeChart, nodeChart, RingHom.map_closure, Set.image_union]
  congr 2
  · ext f
    simp only [baseRing, Subring.coe_map, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
      exact ⟨o, ho, (φ.commutes o).symm⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨_, ⟨o, ho, rfl⟩, φ.commutes o⟩
  · rw [Set.image_insert_eq, Set.image_singleton]
    congr 2
    change φ (algebraMap C (RatFunc C) γ / z) = _
    rw [map_div₀, AlgHom.commutes]

/-- **Intersection of node charts** in the coordinate `t = (x - a)/c`: for `|c'| ≤ |e| ≤ |u| ≤ 1`,
`O_C[t, c'/t] = O_C[t, e/t] ∩ O_C[t/u, c'/t]`. -/
theorem nodeChart_coord_eq_inf {a c c' e u : C} (hc0 : c ≠ 0) (hc'0 : c' ≠ 0) (hu0 : u ≠ 0)
    (hc'e : ‖c'‖ ≤ ‖e‖) (heu : ‖e‖ ≤ ‖u‖) (hu1 : ‖u‖ ≤ 1) :
    nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) c' =
      nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) e ⊓
        nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a (c * u)) (c' / u) := by
  set φ := (AffineTwist.aff a c hc0).toAlgHom
  have hφX : φ RatFunc.X = GaussTree.coord (RatFunc.X : RatFunc C) a c := by
    change AffineTwist.affHom a c hc0 RatFunc.X = _
    rw [AffineTwist.affHom_X, gaussCoord_eq_coord hc0]
  have hφu : φ (RatFunc.X / algebraMap C (RatFunc C) u) =
      GaussTree.coord (RatFunc.X : RatFunc C) a (c * u) := by
    rw [map_div₀, AlgHom.commutes, hφX, GaussTree.coord, GaussTree.coord, map_mul, div_div]
  have h := congrArg (fun S : Subring (RatFunc C) ↦ S.map φ.toRingHom)
    (nodeRing_eq_inf hc'0 hu0 hc'e heu hu1)
  rw [Subring.map_inf _ _ φ.toRingHom (AffineTwist.aff a c hc0).injective] at h
  rw [← hφX, ← hφu, ← map_nodeChart, ← map_nodeChart, ← map_nodeChart]
  exact h

lemma isIntegral_of_subring_le {L E : Type*} [Field L] [CommRing E] [Algebra L E]
    {A B : Subring L} (h : A ≤ B) {y : E} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨p, hm, hp⟩ := hy
  refine ⟨p.map (Subring.inclusion h), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp

/-- Integrality over the intersection of two integrally closed subrings with fraction field `L`. -/
theorem isIntegral_inf_iff {L E : Type*} [Field L] [Field E] [Algebra L E]
    {A₁ A₂ : Subring L} [IsIntegrallyClosed A₁] [IsFractionRing A₁ L]
    [IsIntegrallyClosed A₂] [IsFractionRing A₂ L] (y : E) :
    IsIntegral (A₁ ⊓ A₂ : Subring L) y ↔ IsIntegral A₁ y ∧ IsIntegral A₂ y := by
  constructor
  · intro h
    exact ⟨isIntegral_of_subring_le inf_le_left h, isIntegral_of_subring_le inf_le_right h⟩
  · rintro ⟨h₁, h₂⟩
    have e₁ := minpoly.isIntegrallyClosed_eq_field_fractions' L h₁
    have e₂ := minpoly.isIntegrallyClosed_eq_field_fractions' L h₂
    have hc : ↑(minpoly L y).coeffs ⊆ ((A₁ ⊓ A₂ : Subring L) : Set L) := fun c hc' ↦ by
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc'
      refine ⟨?_, ?_⟩
      · rw [e₁, coeff_map]; exact Subtype.prop _
      · rw [e₂, coeff_map]; exact Subtype.prop _
    refine ⟨(minpoly L y).toSubring _ hc, ?_, ?_⟩
    · exact (monic_toSubring _ _ hc).2 (minpoly.monic (h₁.tower_top (A := L)))
    · have := minpoly.aeval L y
      rw [← map_toSubring _ _ hc, aeval_def, eval₂_map] at this
      exact this

section Normalization

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

omit [IsUltrametricDist C] in
/-- The normalization of the intersection of two integrally closed subrings of `C(x)` with
fraction field `C(x)` is the intersection of their normalizations. -/
theorem normChart_inf {A₁ A₂ : Subring (RatFunc C)} [IsIntegrallyClosed A₁]
    [IsFractionRing A₁ (RatFunc C)] [IsIntegrallyClosed A₂] [IsFractionRing A₂ (RatFunc C)] :
    normChart F' (A₁ ⊓ A₂) = normChart F' A₁ ⊓ normChart F' A₂ := by
  ext y
  rw [← integralClosure_toSubring_eq, ← integralClosure_toSubring_eq,
    ← integralClosure_toSubring_eq]
  exact isIntegral_inf_iff y

end Normalization

section Twisted

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

open AffineTwist TreeBridge

lemma mem_rint_aff_iff {a c : C} (hc0 : c ≠ 0) (c' : C) (y : F') :
    AffineTwist.toAff hc0 y ∈ Rint c' (Aff a c hc0 F') ↔
      y ∈ normChart F' (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) c') := by
  rw [← map_rint_aff hc0 c']
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- **Intersection of normalized node charts** (twisted form): for `|c'| ≤ |e| ≤ |u| ≤ 1`, the
normalized chart of the annulus `|c'| ≤ |t| ≤ 1` (`t = (x - a)/c`) is the intersection of those of
the annuli `|e| ≤ |t| ≤ 1` and `|c'| ≤ |t| ≤ |u|` (the latter in the coordinate `t/u`). -/
theorem mem_rint_iff_and {a c c' e u : C} (hc0 : c ≠ 0) (hc'0 : c' ≠ 0) (hu0 : u ≠ 0)
    (hc'e : ‖c'‖ ≤ ‖e‖) (heu : ‖e‖ ≤ ‖u‖) (hu1 : ‖u‖ ≤ 1) (y : F') :
    toAff hc0 y ∈ Rint c' (Aff a c hc0 F') ↔
      toAff hc0 y ∈ Rint e (Aff a c hc0 F') ∧
        toAff (mul_ne_zero hc0 hu0) y ∈ Rint (c' / u) (Aff a (c * u) (mul_ne_zero hc0 hu0) F') := by
  have he0 : e ≠ 0 := norm_pos_iff.1 ((norm_pos_iff.2 hc'0).trans_le hc'e)
  have hcu0 : c * u ≠ 0 := mul_ne_zero hc0 hu0
  rw [mem_rint_aff_iff, mem_rint_aff_iff, mem_rint_aff_iff,
    nodeChart_coord_eq_inf hc0 hc'0 hu0 hc'e heu hu1]
  have hg₁ := isGaussCoord_coord (v := ν) (a := a) hc0
  have hg₂ := isGaussCoord_coord (v := ν) (a := a) hcu0
  haveI : IsIntegrallyClosed (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) e) :=
    isIntegrallyClosed_nodeChart hg₁ he0 (by
      rw [NormedField.valuation_apply]; exact_mod_cast heu.trans hu1)
  haveI : IsIntegrallyClosed
      (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a (c * u)) (c' / u)) :=
    isIntegrallyClosed_nodeChart hg₂ (div_ne_zero hc'0 hu0) (by
      rw [NormedField.valuation_apply, nnnorm_div]
      exact div_le_one_of_le₀ (by exact_mod_cast hc'e.trans heu) zero_le)
  haveI : IsFractionRing (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) e)
      (RatFunc C) :=
    hg₁.isFractionRing_of_le (polyChart_le baseRing_le_nodeChart self_mem_nodeChart)
  haveI : IsFractionRing
      (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a (c * u)) (c' / u)) (RatFunc C) :=
    hg₂.isFractionRing_of_le (polyChart_le baseRing_le_nodeChart self_mem_nodeChart)
  rw [normChart_inf]
  rfl

end Twisted

end ExhaustGluing

end SemistableReduction
