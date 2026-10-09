/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Stab
import TemperedFundamentalGroups.SemistableReduction.TubePoints

/-!
# Tube counts at a type-3 radius

Blueprint §9.10a (II.1). With STAB3 (`Type3.finsum_ramificationIdx_mul_inertiaDeg_eq_of_irrat`)
the S5 machinery works at irrational radii:

* `natDegree_eq_of_irrat`, `inertiaDeg_eq_one_of_irrat`: every extension `w'` of `w_{a,ρ}`,
  `ρ ∉ |C^×|`, has local degree `e(w') f(w')` and `f(w') = 1`;
* `sum_ramificationIdx_mul_inertiaDeg_eq_of_stable`: the tube count at any radius at which the
  local degrees are `e f` (types 2 and 3);
* **`tubeDegree_eq_of_irrat`**: the tube degree at an irrational radius of the open segment equals
  the tube degree at any radius of the value group.
-/

open Polynomial NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability LocalGlobal TubeCount

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- At a radius `r`, the local degree of every extension is `e · f`. -/
def LocalStable (a : C) (r : ℝ≥0ˣ) (F' : Type*) [Field F'] [Algebra (RatFunc C) F']
    [FiniteDimensional (RatFunc C) F'] [Algebra.IsSeparable (RatFunc C) F'] : Prop :=
  ∀ g : Factor (GaussField a r) (UniformSpace.Completion (GaussField a r)) F',
    g.1.natDegree = ramificationIdx (RatFunc C) (factorEquiv g).1 *
      inertiaDeg (gaussRat (NormedField.valuation (K := C)) a r) (factorEquiv g).1

include hp hp1 in
/-- Gauss points of the value group are locally stable (W4). -/
lemma localStable_of_eq {a : C} {r : ℝ≥0ˣ} {c : C} (hc : NormedField.valuation c = (r : ℝ≥0)) :
    LocalStable a r F' := fun g ↦ natDegree_eq_ramificationIdx_mul_inertiaDeg hp hp1 hc g

include hp hp1 in
/-- **Type-3 points are locally stable** (STAB3). -/
lemma localStable_of_irrat {a : C} {r : ℝ≥0ˣ} (hr : ∀ z : C, ‖z‖₊ ≠ (r : ℝ≥0)) :
    LocalStable a r F' := by
  classical
  intro g
  have hW := Type3.finsum_ramificationIdx_mul_inertiaDeg_eq_of_irrat (a := a) hr hp hp1
    (F' := F')
  rw [← finsum_comp_equiv (factorEquiv (a := a) (r := r) (F' := F')),
    finsum_eq_sum_of_fintype] at hW
  have hsum := sum_natDegree_factors (F := GaussField a r)
    (K := UniformSpace.Completion (GaussField a r)) (F' := F')
  rw [← Finset.sum_coe_sort (factors _ _ F') natDegree] at hsum
  have hdeg : Module.finrank (GaussField a r) F' = Module.finrank (RatFunc C) F' :=
    Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv _) (RingEquiv.refl F') (by ext; rfl)
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (fun g _ ↦ ramificationIdx_mul_inertiaDeg_factorEquiv_le (F' := F') g)).1
    (by rw [hW, hsum, hdeg]) g (Finset.mem_univ g)
  exact this.symm

include hp hp1 in
/-- **`f = 1` at type-3 points.** -/
lemma inertiaDeg_eq_one_of_irrat {a : C} {r : ℝ≥0ˣ} (hr : ∀ z : C, ‖z‖₊ ≠ (r : ℝ≥0))
    (w' : GaussExtension a r F') :
    inertiaDeg (gaussRat (NormedField.valuation (K := C)) a r) w'.1 = 1 := by
  obtain ⟨g, rfl⟩ := (factorEquiv (a := a) (r := r) (F' := F')).surjective w'
  rw [← inertiaDeg_gaussField]
  change inertiaDeg (NormedField.valuation (K := GaussField a r)) (extValuation g) = 1
  rw [inertiaDeg_extValuation]
  exact (Type3.ramificationIdx_eq_finrank hp hp1 (Type3.isType3_genK (a := a) hr)
    (Local (UniformSpace.Completion (GaussField a r)) g.1)).2

omit [IsAlgClosed C] [CharZero C] in
/-- **Tube count** at a locally stable radius of the open segment (copy of
`sum_ramificationIdx_mul_inertiaDeg_eq` with `LocalStable` for W4). -/
theorem sum_ramificationIdx_mul_inertiaDeg_eq_of_stable {c : C} {s : ℝ≥0ˣ}
    (hstab : LocalStable (0 : C) s F') [Fintype (GaussExtension (0 : C) s F')]
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
  rw [Equiv.symm_apply_apply, hstab g]
  have : ‖toLocal g y‖ < 1 ↔ (factorEquiv g).1 y < 1 := by
    rw [factorEquiv_apply_val, extValuation_apply, ← NNReal.coe_lt_one, coe_nnnorm]
  simp only [this]

omit [IsAlgClosed C] [CharZero C] in
/-- **Constancy of the tube degree** between two locally stable radii of the open segment. -/
theorem tubeDegree_eq_of_stable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0) {s s' : ℝ≥0ˣ}
    (hs : s ∈ segment c) (hs' : s' ∈ segment c) (hstab : LocalStable (0 : C) s F')
    (hstab' : LocalStable (0 : C) s' F') [Fintype (GaussExtension (0 : C) s F')]
    [Fintype (GaussExtension (0 : C) s' F')] (P' : Ideal (Rint c F')) [P'.IsMaximal] :
    tubeDegree hs P' = tubeDegree hs' P' := by
  classical
  set T : Finset (Ideal (Rint c F')) :=
    (Finset.univ.image (center hs) ∪ Finset.univ.image (center hs')).erase P'
  obtain ⟨e, he1, heQ⟩ := exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    refine ⟨?_, hne⟩
    rcases Finset.mem_union.1 hQ with hQ | hQ <;> obtain ⟨w', -, rfl⟩ := Finset.mem_image.1 hQ
    exacts [center_isMaximal hc hc0 hs w', center_isMaximal hc hc0 hs' w']
  set y : Rint c F' := e - 1
  obtain ⟨P, hP⟩ := exists_lift_normPoly hc0 hc.le y.2
  have key : ∀ {t : ℝ≥0ˣ} (ht : t ∈ segment c) (w' : GaussExtension (0 : C) t F'),
      center ht w' ∈ Finset.univ.image (center hs) ∪ Finset.univ.image (center hs') →
      (w'.1 (y : F') < 1 ↔ center ht w' = P') := by
    intro t ht w' hmem
    constructor
    · intro hlt
      by_contra hne
      have he : w'.1 (e : F') < 1 :=
        (mem_center_iff ht w' e).1 (heQ _ (Finset.mem_erase.2 ⟨hne, hmem⟩))
      have : w'.1 ((y : F')) = 1 := by
        rw [show (y : F') = -1 + (e : F') by simp [y]; ring,
          Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, map_one]; exact he),
          Valuation.map_neg, map_one]
      exact lt_irrefl 1 (this ▸ hlt)
    · intro h
      rw [← mem_center_iff ht, h]
      exact he1
  have hcount : ∀ {t : ℝ≥0ˣ} (ht : t ∈ segment c), LocalStable (0 : C) t F' →
      ∀ [Fintype (GaussExtension (0 : C) t F')],
      (∀ w' : GaussExtension (0 : C) t F', center ht w' ∈
        Finset.univ.image (center hs) ∪ Finset.univ.image (center hs')) →
      tubeDegree ht P' = (P.map (Ideal.Quotient.mk (tubeIdeal c))).natTrailingDegree := by
    intro t ht hst _ hall
    rw [← sum_ramificationIdx_mul_inertiaDeg_eq_of_stable hst ht (y : F') P hP
      fun w' ↦ valuation_le_one_of_isIntegral ht w' y.2, tubeDegree]
    exact Finset.sum_congr (Finset.filter_congr fun w' _ ↦ (key ht w' (hall w')).symm) fun _ _ ↦
      rfl
  rw [hcount hs hstab fun w' ↦ Finset.mem_union_left _ (Finset.mem_image_of_mem _
      (Finset.mem_univ w')),
    hcount hs' hstab' fun w' ↦ Finset.mem_union_right _ (Finset.mem_image_of_mem _
      (Finset.mem_univ w'))]

end GaussTube

end SemistableReduction
