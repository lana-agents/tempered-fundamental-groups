/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTreeSemistable

/-!
# The tree of projective lines is normal

Blueprint §9.6 (W5), layer M8a.

* `mem_of_forall_mem_localAt` (conductor argument): an element of `F` lying in the local rings of
  a subring `C` at the centers of all valuation subrings `W ⊇ C` lies in `C`; hence
  `isIntegral_mem_of_forall` (normality is local).
* `IsGaussCoord.isFractionRing_polyChart`, `IsGaussCoord.isIntegral_mem_polyChart`: the chart
  `O[z]` of a Gauss coordinate has fraction field `F` and is integrally closed in `F` (it is
  isomorphic to `O[X]`, integrally closed by Mathlib); the node chart likewise
  (`isIntegral_mem_nodeChart`, via `Node.isIntegrallyClosed`).
* `gaussJoinModel_isNormal`: for a convex reduced family of Gauss valuations of `K(X)` over `O` of
  rank at most one, the join model is normal (its local rings are those of standard charts).
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel GaussTree

section Local

variable {F : Type u} [Field F]

/-- **Conductor argument**: if `x` lies in the local ring of `C` at the center of every valuation
subring `W ⊇ C`, then `x ∈ C`. -/
theorem mem_of_forall_mem_localAt {C : Subring F} {x : F}
    (h : ∀ W : ValuationSubring F, C ≤ W.toSubring → x ∈ localAt C W) : x ∈ C := by
  let I : Ideal C :=
    { carrier := {s | (s : F) * x ∈ C}
      add_mem' := fun {s t} hs ht ↦ by
        change ((s : F) + t) * x ∈ C
        rw [add_mul]
        exact C.add_mem hs ht
      zero_mem' := by
        change ((0 : C) : F) * x ∈ C
        rw [Subring.coe_zero, zero_mul]
        exact C.zero_mem
      smul_mem' := fun c s hs ↦ by
        change ((c : F) * s) * x ∈ C
        rw [mul_assoc]
        exact C.mul_mem c.2 hs }
  by_contra hx
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : C) ∈ I := htop ▸ Submodule.mem_top
    have h1' : ((1 : C) : F) * x ∈ C := h1
    rw [Subring.coe_one, one_mul] at h1'
    exact hx h1'
  obtain ⟨𝔪, h𝔪, hI𝔪⟩ := I.exists_le_maximal hI
  obtain ⟨W, hCW, hcen⟩ := exists_centerIdeal_eq C 𝔪
  obtain ⟨s, hs, hsW, hxs⟩ := h W hCW
  have hsI : (⟨s, hs⟩ : C) ∈ I := by
    change s * x ∈ C
    rw [mul_comm]
    exact hxs
  have hs𝔪 := hI𝔪 hsI
  rw [← hcen, mem_centerIdeal_iff] at hs𝔪
  rw [hsW] at hs𝔪
  exact lt_irrefl _ hs𝔪

/-- **Normality is local**: if all local rings of `C` at centers of valuation subrings are
integrally closed in `F`, so is `C`. -/
theorem isIntegral_mem_of_forall {C : Subring F}
    (hC : ∀ W : ValuationSubring F, C ≤ W.toSubring → ∀ x : F,
      IsIntegral (localAt C W) x → x ∈ localAt C W)
    {x : F} (hx : IsIntegral C x) : x ∈ C := by
  refine mem_of_forall_mem_localAt fun W hW ↦ hC W hW x ?_
  obtain ⟨p, hpm, hp⟩ := hx
  refine ⟨p.map (Subring.inclusion le_localAt), hpm.map _, ?_⟩
  rw [eval₂_map]
  exact hp

end Local

section Standard

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀} {w : Valuation F Γ₀} {z : F}

namespace IsGaussCoord

variable (h : IsGaussCoord v w z)
include h

/-- Every element of `F` is a quotient of two elements of `O[z]`. -/
lemma exists_eq_div_polyChart (x : F) :
    ∃ p q, p ∈ polyChart v z ∧ q ∈ polyChart v z ∧ x = p / q := by
  obtain ⟨P, Q, hQ, rfl⟩ := h.exists_eq_div x
  rcases le_or_gt (Gauss.sup v 1 P) 1 with hP | hP
  · exact ⟨_, _, mem_polyChart_iff.2 ⟨P, hP, rfl⟩, mem_polyChart_iff.2 ⟨Q, hQ.le, rfl⟩, rfl⟩
  · have hP0 : P ≠ 0 := by
      rintro rfl
      simp [Gauss.sup_zero] at hP
    obtain ⟨d, hd, hdP⟩ := exists_sup_eq_one (v := v) hP0
    have hdQ : Gauss.sup v 1 (C d * Q) ≤ 1 := by
      rw [Gauss.sup_mul, Gauss.sup_C, hQ, mul_one]
      have h1 := hdP
      rw [Gauss.sup_mul, Gauss.sup_C] at h1
      have hpos : 0 < Gauss.sup v 1 P := lt_trans zero_lt_one hP
      have : v d = (Gauss.sup v 1 P)⁻¹ := eq_inv_of_mul_eq_one_left h1
      rw [this]
      exact inv_le_one_of_one_le₀ hP.le
    refine ⟨_, _, mem_polyChart_iff.2 ⟨C d * P, hdP.le, rfl⟩,
      mem_polyChart_iff.2 ⟨C d * Q, hdQ, rfl⟩, ?_⟩
    rw [map_mul, map_mul, aeval_C, mul_div_mul_left]
    simpa using hd

lemma isFractionRing_polyChart : IsFractionRing (polyChart v z) F :=
  IsFractionRing.of_field _ _ fun x ↦ by
    obtain ⟨p, q, hp, hq, rfl⟩ := h.exists_eq_div_polyChart x
    exact ⟨⟨p, hp⟩, ⟨q, hq⟩, rfl⟩

lemma isFractionRing_of_le {A : Subring F} (hA : polyChart v z ≤ A) : IsFractionRing A F :=
  IsFractionRing.of_field _ _ fun x ↦ by
    obtain ⟨p, q, hp, hq, rfl⟩ := h.exists_eq_div_polyChart x
    exact ⟨⟨p, hA hp⟩, ⟨q, hA hq⟩, rfl⟩

end IsGaussCoord

/-- A subring `A ⊆ F` with fraction field `F` which is integrally closed (as a ring) is integrally
closed in `F`. -/
lemma isIntegral_mem_of_isIntegrallyClosed {A : Subring F} [IsFractionRing A F]
    [IsIntegrallyClosed A] {x : F} (hx : IsIntegral A x) : x ∈ A := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact y.2

variable [Algebra v.valuationSubring F] [IsScalarTower v.valuationSubring K F]

/-- The chart `O[z]` of a Gauss coordinate is integrally closed in `F`. -/
theorem IsGaussCoord.isIntegral_mem_polyChart (h : IsGaussCoord v w z) {x : F}
    (hx : IsIntegral (polyChart v z) x) : x ∈ polyChart v z := by
  have := h.isFractionRing_polyChart
  let e : v.valuationSubring[X] ≃+* polyChart v z :=
    (AlgEquiv.ofInjective _ (aeval_injective' h)).toRingEquiv.trans
      (RingEquiv.subringCongr (range_aeval z))
  have : IsIntegrallyClosed (polyChart v z) := IsIntegrallyClosed.of_equiv e
  exact isIntegral_mem_of_isIntegrallyClosed hx

/-- The node chart `O[y, c / y]` of a Gauss coordinate is integrally closed in `F`. -/
theorem IsGaussCoord.isIntegral_mem_nodeChart {c : K} (h : IsGaussCoord v w z) (hc0 : c ≠ 0)
    (hcO : v c ≤ 1) {x : F} (hx : IsIntegral (nodeChart v z c) x) : x ∈ nodeChart v z c := by
  have := h.isFractionRing_of_le (A := nodeChart v z c)
    (polyChart_le baseRing_le_nodeChart self_mem_nodeChart)
  have := isIntegrallyClosed_nodeChart h hc0 hcO
  exact isIntegral_mem_of_isIntegrallyClosed hx

end Standard

/-! ### The join model of a convex family is normal -/

section Tree

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

/-- Standard charts are integrally closed in `K(X)`. -/
theorem IsStandardChart.isIntegral_mem {ι : Type*} {a c : ι → K} (hc : ∀ i, c i ≠ 0)
    {B : Subring (RatFunc K)} (hB : IsStandardChart v a c (RatFunc.X : RatFunc K) B)
    {x : RatFunc K} (hx : IsIntegral B x) : x ∈ B := by
  rcases hB with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, m, hjm, -, rfl⟩
  · exact (isGaussCoord_coord (hc i)).isIntegral_mem_polyChart hx
  · exact (isGaussCoord_coord (hc i)).inv.isIntegral_mem_polyChart hx
  · exact (isGaussCoord_coord (a := a j) (hc m)).isIntegral_mem_nodeChart
      (div_ne_zero (hc j) (hc m)) (hjm.div_le_one hc).1 hx

/-- **The tree of `ℙ¹`s is normal.** For a convex reduced nonempty finite family of Gauss
valuations of `K(X)` over a valuation ring of rank at most one, every chart of `gaussJoinModel` is
integrally closed in `K(X)`. -/
theorem gaussJoinModel_isNormal {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → K}
    (hc : ∀ i, c i ≠ 0) (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hrank : ∀ O' : ValuationSubring K, v.valuationSubring ≤ O' →
      O' = v.valuationSubring ∨ O' = ⊤) :
    (gaussJoinModel v a c).IsNormal := by
  intro C hC x hx
  refine isIntegral_mem_of_forall (fun W hCW y hy ↦ ?_) hx
  have hW : baseRing (RatFunc K) v.valuationSubring ≤ W.toSubring :=
    ((gaussJoinModel v a c).le_chart C hC).trans hCW
  obtain ⟨B, hB, -, hcenter⟩ := gaussJoinModel_center_eq hc hconv hred hrank hW
  have hloc : localAt C W = localAt B W := by
    rw [← center_eq gaussJoinModel_isProper gaussJoinModel_isSeparated hW hC hCW, hcenter]
  rw [hloc] at hy ⊢
  exact isIntegral_mem_localAt (fun z hz ↦ IsStandardChart.isIntegral_mem hc hB hz) hy

end Tree

end SemistableReduction
