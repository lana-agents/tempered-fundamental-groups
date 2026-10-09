/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AnnulusModel
import TemperedFundamentalGroups.SemistableReduction.AnnulusUnit
import TemperedFundamentalGroups.SemistableReduction.GaussNorm
import TemperedFundamentalGroups.SemistableReduction.TubeCount

/-!
# Constancy of tube degrees along an open segment of Gauss points

Blueprint §9.9, W7 layer S5. Let `C` be a non-archimedean field, `c ∈ C` with `0 < |c| < 1`, and
`nodeRing c = O_C[x, c/x] ⊆ C(x)` the node chart of the annulus `|c| ≤ |x| ≤ 1`. The Gauss points
`w_{0,s}`, `|c| < s < 1`, of the open segment are all centred at the node:

* `exists_const`: every `a ∈ nodeRing c` is `κ + (a - κ)` with `κ ∈ O_C` and `w_{0,s}(a - κ) < 1`
  for all `s` of the open segment (induction over the generators `O_C`, `x`, `c/x`);
* `tubeIdeal c = {a : w_{0,s}(a) < 1 for all s ∈ (|c|, 1)}`, an ideal (the node), and
  `mem_tubeIdeal_iff`: for one (equivalently every) `s` of the open segment, `a ∈ tubeIdeal c`
  iff `w_{0,s}(a) < 1`.

With W4 (`C` algebraically closed of characteristic `0`, `‖p‖ < 1`) and the tube count
(`TubeCount.sum_natDegree_eq_natTrailingDegree`):

* **`sum_ramificationIdx_mul_inertiaDeg_eq`**: for `y ∈ F'` whose characteristic polynomial over
  `C(x)` has coefficients in `nodeRing c` (e.g. `y` integral over the node chart), and `s` in the
  open segment with `w'(y) ≤ 1` for all `w' ∣ w_{0,s}`:
  `Σ_{w' ∣ w_{0,s}, w'(y) < 1} e(w') f(w') = natTrailingDegree (P mod tubeIdeal c)`.

The right side does not depend on `s`: the number of extensions near the residue class of `y`,
weighted by their local degrees, is constant along the open segment. Applied to `y = e - 1` for
an element `e` of the integral closure of the node chart reducing to `1` at one point `P'` over
the node and to `0` at the others, this is the constancy of the tube degree `d_{P'}` (S5).
-/

open Polynomial NNReal

namespace SemistableReduction

namespace GaussTube

universe u

open FundamentalInequality GaussStability LocalGlobal TubeCount

section Node

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- The node chart `O_C[x, c/x] ⊆ C(x)` (`AnnulusModel.nodeChart`). -/
noncomputable def nodeRing (c : C) : Subring (RatFunc C) :=
  nodeChart (NormedField.valuation (K := C)) RatFunc.X c

/-- The open segment `|c| < s < 1` of radii. -/
def segment (c : C) : Set ℝ≥0ˣ := {s | ‖c‖₊ < (s : ℝ≥0) ∧ (s : ℝ≥0) < 1}

lemma gaussRat_X (s : ℝ≥0ˣ) : w s RatFunc.X = s := AnnulusUnit.gaussRat_X s

lemma gaussRat_C (s : ℝ≥0ˣ) (b : C) : w s (algebraMap C (RatFunc C) b) = ‖b‖₊ := by
  rw [gaussRat_algebraMap_C, NormedField.valuation_apply]

/-- Every element of the node chart is a constant plus an element of value `< 1` on the open
segment. -/
theorem exists_const {c : C} {a : RatFunc C} (ha : a ∈ nodeRing c) :
    ∃ κ : C, ‖κ‖ ≤ 1 ∧ ∀ s ∈ segment c, w s (a - algebraMap C (RatFunc C) κ) < 1 := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨b, hb, rfl⟩ | rfl | rfl
    · refine ⟨b, ?_, fun s _ ↦ by simp⟩
      have : NormedField.valuation b ≤ 1 := hb
      rw [NormedField.valuation_apply] at this
      exact_mod_cast this
    · exact ⟨0, by simp, fun s hs ↦ by simp [hs.2]⟩
    · refine ⟨0, by simp, fun s hs ↦ ?_⟩
      rw [map_zero, sub_zero, map_div₀, gaussRat_C, gaussRat_X]
      exact (div_lt_one (by simp)).2 hs.1
  | zero => exact ⟨0, by simp, fun s _ ↦ by simp⟩
  | one => exact ⟨1, by simp, fun s _ ↦ by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨κ, hκ, h⟩ := hx
    obtain ⟨κ', hκ', h'⟩ := hy
    refine ⟨κ + κ', (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hκ hκ'),
      fun s hs ↦ ?_⟩
    rw [map_add, add_sub_add_comm]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (h s hs) (h' s hs))
  | neg x _ hx =>
    obtain ⟨κ, hκ, h⟩ := hx
    refine ⟨-κ, by simpa using hκ, fun s hs ↦ ?_⟩
    rw [map_neg, show -x - -algebraMap C (RatFunc C) κ = -(x - algebraMap C (RatFunc C) κ) by
      ring, Valuation.map_neg]
    exact h s hs
  | mul x y _ _ hx hy =>
    obtain ⟨κ, hκ, h⟩ := hx
    obtain ⟨κ', hκ', h'⟩ := hy
    refine ⟨κ * κ', by rw [norm_mul]; exact mul_le_one₀ hκ (norm_nonneg _) hκ',
      fun s hs ↦ ?_⟩
    set u := x - algebraMap C (RatFunc C) κ
    set u' := y - algebraMap C (RatFunc C) κ'
    have hk : w s (algebraMap C (RatFunc C) κ) ≤ 1 := by
      rw [gaussRat_C]; exact_mod_cast hκ
    have hk' : w s (algebraMap C (RatFunc C) κ') ≤ 1 := by
      rw [gaussRat_C]; exact_mod_cast hκ'
    have : x * y - algebraMap C (RatFunc C) (κ * κ') =
        u * u' + algebraMap C (RatFunc C) κ * u' + algebraMap C (RatFunc C) κ' * u := by
      simp only [u, u', map_mul]
      ring
    rw [this]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_add _ _ _).trans_lt
      (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
    · exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (h s hs) (h' s hs).le
    · exact mul_lt_one_of_nonneg_of_lt_one_right hk zero_le (h' s hs)
    · exact mul_lt_one_of_nonneg_of_lt_one_right hk' zero_le (h s hs)

lemma gaussRat_le_one {c : C} {a : RatFunc C} (ha : a ∈ nodeRing c) {s : ℝ≥0ˣ}
    (hs : s ∈ segment c) : w s a ≤ 1 := by
  obtain ⟨κ, hκ, h⟩ := exists_const ha
  have : a = (a - algebraMap C (RatFunc C) κ) + algebraMap C (RatFunc C) κ := by ring
  rw [this]
  refine (Valuation.map_add _ _ _).trans (max_le (h s hs).le ?_)
  rw [gaussRat_C]
  exact_mod_cast hκ

/-- On the open segment, `w_{0,s}(a) < 1` iff the constant `κ` of `a` has `|κ| < 1`; in
particular it does not depend on `s`. -/
lemma gaussRat_lt_one_iff {c : C} {a : RatFunc C} {κ : C}
    (h : ∀ s ∈ segment c, w s (a - algebraMap C (RatFunc C) κ) < 1) {s : ℝ≥0ˣ}
    (hs : s ∈ segment c) : w s a < 1 ↔ ‖κ‖ < 1 := by
  have ha : a = algebraMap C (RatFunc C) κ + (a - algebraMap C (RatFunc C) κ) := by ring
  constructor
  · intro hlt
    by_contra! H
    have hκ : w s (algebraMap C (RatFunc C) κ) = ‖κ‖₊ := gaussRat_C s κ
    have h1 : (1 : ℝ≥0) ≤ ‖κ‖₊ := by exact_mod_cast H
    rw [ha, Valuation.map_add_eq_of_lt_left _ (by rw [hκ]; exact (h s hs).trans_le h1), hκ]
      at hlt
    exact absurd hlt (not_lt.2 h1)
  · intro hκ
    rw [ha]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ (h s hs))
    rw [gaussRat_C]
    exact_mod_cast hκ

lemma gaussRat_lt_one_iff_of_mem {c : C} {a : RatFunc C} (ha : a ∈ nodeRing c) {s s' : ℝ≥0ˣ}
    (hs : s ∈ segment c) (hs' : s' ∈ segment c) : w s a < 1 ↔ w s' a < 1 := by
  obtain ⟨κ, -, h⟩ := exists_const ha
  rw [gaussRat_lt_one_iff h hs, gaussRat_lt_one_iff h hs']

/-- The ideal of the node: the elements of value `< 1` on the open segment. -/
def tubeIdeal (c : C) : Ideal (nodeRing c) where
  carrier := {a | ∀ s ∈ segment c, w s (a : RatFunc C) < 1}
  add_mem' {a b} ha hb s hs := by
    simp only [Subring.coe_add]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt (ha s hs) (hb s hs))
  zero_mem' s _ := by simp
  smul_mem' b a ha s hs := by
    simp only [smul_eq_mul, Subring.coe_mul, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (gaussRat_le_one b.2 hs) zero_le (ha s hs)

/-- For any `s` of the open segment, `a ∈ tubeIdeal c` iff `w_{0,s}(a) < 1`. -/
lemma mem_tubeIdeal_iff {c : C} (a : nodeRing c) {s : ℝ≥0ˣ} (hs : s ∈ segment c) :
    a ∈ tubeIdeal c ↔ w s (a : RatFunc C) < 1 :=
  ⟨fun h ↦ h s hs, fun h _ hs' ↦ (gaussRat_lt_one_iff_of_mem a.2 hs hs').1 h⟩

end Node

section Count

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {c : C} {s : ℝ≥0ˣ} {cs : C}
  (hcs : NormedField.valuation cs = (s : ℝ≥0))
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

include hp hp1 hcs in
/-- **Tube count along the open segment.** Let `y ∈ F'` have characteristic polynomial over
`C(x)` with coefficients in the node chart `O_C[x, c/x]` (lift `P`), and let `s` be in the open
segment `(|c|, 1)` with `w'(y) ≤ 1` for all `w' ∣ w_{0,s}`. Then
`Σ_{w' ∣ w_{0,s}, w'(y) < 1} e(w') f(w')` is the trailing degree of `P` modulo the node ideal;
in particular it does not depend on `s`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_eq [Fintype (GaussExtension (0 : C) s F')]
    (hs : s ∈ segment c) (y : F') (P : (nodeRing c)[X])
    (hP : P.map (nodeRing c).subtype = normPoly (RatFunc C) y)
    (hy : ∀ w' : GaussExtension (0 : C) s F', w'.1 y ≤ 1) :
    ∑ w' ∈ Finset.univ.filter (fun w' : GaussExtension (0 : C) s F' ↦ w'.1 y < 1),
        ramificationIdx (RatFunc C) w'.1 *
          inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 s) w'.1 =
      (P.map (Ideal.Quotient.mk (tubeIdeal c))).natTrailingDegree := by
  classical
  haveI : Infinite (RatFunc C) :=
    Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
  set e : RatFunc C ≃+* GaussField (0 : C) s := (WithAbs.equiv _).symm
  haveI : Infinite (GaussField (0 : C) s) := Infinite.of_injective e e.injective
  set ι : nodeRing c →+* GaussField (0 : C) s := e.toRingHom.comp (nodeRing c).subtype
  have hPι : P.map ι = normPoly (GaussField (0 : C) s) y := by
    rw [← Polynomial.map_map, hP]
    exact normPoly_map_ringEquiv e (by ext; rfl) y
  have h𝔭 : ∀ a : nodeRing c, a ∈ tubeIdeal c ↔ ‖ι a‖ < 1 := by
    intro a
    rw [mem_tubeIdeal_iff a hs, norm_gaussField]
    exact NNReal.coe_lt_one.symm
  have hy' : ∀ g : Factor (GaussField (0 : C) s) (UniformSpace.Completion (GaussField (0 : C) s))
      F', ‖toLocal g y‖ ≤ 1 := fun g ↦ by
    have := hy (factorEquiv g)
    rw [factorEquiv_apply_val, extValuation_apply] at this
    exact_mod_cast this
  rw [← sum_natDegree_eq_natTrailingDegree ι _ h𝔭 P hPι hy', Finset.sum_filter,
    Finset.sum_filter]
  refine (Fintype.sum_equiv (factorEquiv (a := (0 : C)) (r := s) (F' := F')).symm _ _
    fun w' ↦ ?_)
  obtain ⟨g, rfl⟩ := (factorEquiv (a := (0 : C)) (r := s) (F' := F')).surjective w'
  rw [Equiv.symm_apply_apply, natDegree_eq_ramificationIdx_mul_inertiaDeg hp hp1 hcs g]
  have : ‖toLocal g y‖ < 1 ↔ (factorEquiv g).1 y < 1 := by
    rw [factorEquiv_apply_val, extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
  simp only [this]

end Count

end GaussTube

end SemistableReduction
