/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ModelBase
import TemperedFundamentalGroups.SemistableReduction.NodeCore

/-!
# The target side of a crossing (Blueprint §10.3.8, CrossingX1, CX7)

Let `c'` be a model with dominant generic point `j'`, `y'` a point whose germs `P` form a node
core with coordinates `u v = ϖ ^ n` (`NodeCore`).

* `germs_local`: `P` is a noetherian local ring;
* `isCentre_of_lt_one`: a valuation subring containing `P` with `ϖ, u, v` in its maximal ideal
  has centre `y'`;
* `centre_eq_of_branch`: two valuation subrings containing `P`, with `ϖ, v` in the maximal ideal
  and `u` a unit, have the same centre;
* `unit_or_unit`: at a valuation subring containing `P`, with `ϖ` in the maximal ideal and centre
  other than `y'`, exactly one of `u, v` is a unit.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingTarget

open CentreGerms ValuativeCentre

variable {R : Type u} [CommRing R] {L : Type u} [Field L]
  {c : TemperedFundamentalGroups.ModelCode R} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
  {y : c.scheme} (hy : j (closedPoint L) ⤳ y) {P : Subring L}
  (hP : (P : Set L) = ModelCode.germs c j y)

include hy hP in
lemma germs_eq_range' : (P : Set L) = Set.range (stalkTo j hy).hom := by
  rw [hP, germs_eq_range c j hy]

include hy hP in
/-- **The germ ring is local and noetherian.** -/
theorem germs_local [IsNoetherianRing R] :
    IsLocalRing P ∧ IsNoetherianRing P := by
  haveI : IsLocallyNoetherian c.scheme := LocallyOfFiniteType.isLocallyNoetherian c.toSpec
  have hPr : P = (stalkTo j hy).hom.range := SetLike.coe_injective (by
    rw [germs_eq_range' hy hP, RingHom.coe_range])
  subst hPr
  exact ⟨.of_surjective' (stalkTo j hy).hom.rangeRestrict
    (stalkTo j hy).hom.rangeRestrict_surjective, isNoetherianRing_range _⟩

variable {O : Type*} [CommRing O] {ι : O →+* L} {ϖ u v : L} {n : ℕ}

include hy hP in
/-- **Valuations dominating the node are centred there.** -/
theorem isCentre_of_lt_one (h : NodeCore P ι ϖ u v n) [IsLocalRing P] {V : ValuationSubring L}
    (hPV : P ≤ V.toSubring) (hϖ : V.valuation ϖ < 1) (hu : V.valuation u < 1)
    (hv : V.valuation v < 1) : IsCentre j V y := by
  rw [isCentre_iff_dominates c j hy, Dominates, ← hP]
  exact ⟨fun f hf ↦ hPV hf, fun f hf hf1 ↦ h.valuation_lt_one hPV hϖ hu hv hf hf1⟩

include hy hP in
/-- Valuations centred at `y` dominate `P`. -/
theorem le_of_isCentre {V : ValuationSubring L} (hV : IsCentre j V y) :
    P ≤ V.toSubring ∧ ∀ f ∈ P, (∀ w ∈ P, f * w ≠ 1) → V.valuation f < 1 := by
  rw [isCentre_iff_dominates c j hy, Dominates, ← hP] at hV
  exact ⟨fun f hf ↦ hV.1 hf, hV.2⟩

include hy hP in
/-- **The branch on which `u` is a unit has a unique centre.** -/
theorem centre_eq_of_branch (h : NodeCore P ι ϖ u v n) [IsLocalRing P] [IsNoetherianRing P]
    {V₁ V₂ : ValuationSubring L} (h₁ : P ≤ V₁.toSubring) (h₂ : P ≤ V₂.toSubring)
    (hϖ₁ : V₁.valuation ϖ < 1) (hv₁ : V₁.valuation v < 1) (hu₁ : V₁.valuation u = 1)
    (hϖ₂ : V₂.valuation ϖ < 1) (hv₂ : V₂.valuation v < 1) (hu₂ : V₂.valuation u = 1)
    {x₁ x₂ : c.scheme} (hx₁ : IsCentre j V₁ x₁) (hx₂ : IsCentre j V₂ x₂) : x₁ = x₂ := by
  have hmemP : ∀ s, (stalkTo j hy).hom s ∈ P := fun s ↦ by
    rw [← SetLike.mem_coe, germs_eq_range' hy hP]; exact ⟨s, rfl⟩
  refine centre_eq c.toSpec j hy (fun s ↦ h₁ (hmemP s)) (fun s ↦ h₂ (hmemP s))
    (fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ ?_⟩) hx₁ hx₂
  · exact h.valuation_lt_one_of_branch h₁ h₂ hϖ₁ hv₁ hu₁ hϖ₂ hv₂ (hmemP s) hs
  · exact h.valuation_lt_one_of_branch h₂ h₁ hϖ₂ hv₂ hu₂ hϖ₁ hv₁ (hmemP s) hs

include hy hP in
/-- **Exactly one coordinate is a unit** at a valuation subring containing `P` with `ϖ` in its
maximal ideal and not centred at `y`. -/
theorem unit_or_unit (h : NodeCore P ι ϖ u v n) [IsLocalRing P] {V : ValuationSubring L}
    (hPV : P ≤ V.toSubring) (hϖ : V.valuation ϖ < 1) {x : c.scheme} (hx : IsCentre j V x)
    (hxy : x ≠ y) :
    (V.valuation u = 1 ∧ V.valuation v < 1) ∨ (V.valuation v = 1 ∧ V.valuation u < 1) := by
  have hu1 : V.valuation u ≤ 1 := (V.valuation_le_one_iff _).2 (hPV h.u_mem)
  have hv1 : V.valuation v ≤ 1 := (V.valuation_le_one_iff _).2 (hPV h.v_mem)
  have hprod : V.valuation u * V.valuation v < 1 := by
    rw [← map_mul, h.mul_eq, map_pow]
    exact pow_lt_one₀ zero_le hϖ (by have := h.one_le; omega)
  rcases hu1.lt_or_eq with hu | hu <;> rcases hv1.lt_or_eq with hv | hv
  · exact absurd (centre_unique c.toSpec hx (isCentre_of_lt_one hy hP h hPV hϖ hu hv)) hxy
  · exact .inr ⟨hv, hu⟩
  · exact .inl ⟨hu, hv⟩
  · rw [hu, hv, one_mul] at hprod; exact absurd hprod (lt_irrefl _)

end TemperedFundamentalGroups.SemistableReduction.CrossingTarget
