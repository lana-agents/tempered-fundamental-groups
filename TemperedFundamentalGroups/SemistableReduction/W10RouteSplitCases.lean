/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteTwist

/-!
# Points of the vertex and node charts over `C`, for any pointwise property (G4′, part 1)

Blueprint §10.3.8 (split nodes). Copies of `closedCase`, `vertexCase`, `nodeCase`
(`W10RouteTwist`) for an arbitrary property `Q` of primes of the `E`-chart in place of
semistability (`closedCaseQ`, `vertexCaseQ`, `nodeCaseQ`): the proofs only route the center of a
valuation over `O_C` to a point over `C` where the pointwise descent applies.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section CasesQ

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {G : Type u} [Field G] [Algebra (RatFunc C) G]
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F₀ : Type u} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* G}
  (hχ : DVRDescent.IsCompat φ χ)

set_option hygiene false in
local notation "ψ" => algebraMap (RatFunc C) G

set_option hygiene false in
local notation "κ" k => algebraMap (RatFunc C) G (algebraMap C (RatFunc C) k)

include hφ hχ in
/-- **Node points**: if `x, c₀/x ∈ 𝔪_W'` and the descent applies at the node points of
`Rint c₀ G`, the center of `W'` restricts to a prime of `Rint c₀E F₀` contained in a prime
satisfying `Q`. -/
theorem nodeCaseQ {c₀ : C} (hc : ‖c₀‖ < 1) (hc0 : c₀ ≠ 0) {c₀E : E} (hcE : φ c₀E = c₀)
    (Q : Ideal (Rint c₀E F₀) → Prop)
    (W' : ValuationSubring G) (hO : IsOverOC C W') (hX : W'.valuation (ψ RatFunc.X) < 1)
    (hcX : W'.valuation (ψ (algebraMap C (RatFunc C) c₀ / RatFunc.X)) < 1)
    (hnode : ∀ P' : Ideal (Rint c₀ G), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c₀) (Rint c₀ G)) = tubeIdeal c₀ →
      Q (P'.comap (ιN χ hφ hχ hcE))) :
    ∃ 𝔮 : Ideal (Rint c₀E F₀), Q 𝔮 ∧
      ∀ y : Rint c₀E F₀, W'.valuation (χ y) < 1 → y ∈ 𝔮 := by
  have hcomap := comap_centerI_rint hc hc0 hO hX hcX
  haveI := tubeIdeal_isMaximal hc hc0
  haveI : (centerI W' (Rint c₀ G) (rint_le hO hX hcX)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hcomap]; infer_instance)
  exact ⟨_, hnode _ inferInstance hcomap, fun y hy ↦ hy⟩

variable (Q : Ideal (DRint (0 : E) 1 F₀) → Prop)

include hφ hχ in
/-- **Closed points of a vertex chart**: if `x - β ∈ 𝔪_W'` and the descent applies at the points
of `DRint 0 1 (Aff β 1 G)` over `(𝔪_C, x - β)`, the center of `W'` restricts to a prime of
`DRint 0 1 F₀` contained in a prime satisfying `Q`. -/
theorem closedCaseQ (W' : ValuationSubring G) (hO : IsOverOC C W') {β : C} (hβ : ‖β‖ ≤ 1)
    (hXβ : W'.valuation (ψ RatFunc.X - κ β) < 1)
    (hsm : ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G)), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) =
        discIdeal (0 : C) 1 → Q (P'.comap (ιβ χ hφ hχ hβ))) :
    ∃ 𝔮 : Ideal (DRint (0 : E) 1 F₀), Q 𝔮 ∧
      ∀ y : DRint (0 : E) 1 F₀, W'.valuation (χ y) < 1 → y ∈ 𝔮 := by
  let Wβ : ValuationSubring (Aff β 1 one_ne_zero G) := W'
  have hOβ : IsOverOC C Wβ := isOverOC_aff hO β
  have hXβ' : Wβ.valuation (algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X) < 1 := by
    rw [algebraMap_aff_X]; exact hXβ
  have hcomap := comap_centerI_drint hOβ hXβ'
  haveI : (centerI Wβ (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))
      (drint_le hOβ ((Wβ.valuation_le_one_iff _).1 hXβ'.le))).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
      (by rw [hcomap]; exact discIdeal_isMaximal one_ne_zero)
  exact ⟨_, hsm _ inferInstance hcomap, fun y hy ↦ hy⟩

include hφ hχ in
/-- **Points of a vertex chart off the child directions** `D`: closed points (some `x - β ∈ 𝔪_W'`)
and the generic points of the components (all `x - β` units; going up to a closed point in a
free residue direction). -/
theorem vertexCaseQ [IsAlgClosed C] (W' : ValuationSubring G) (hO : IsOverOC C W')
    (hX : ψ RatFunc.X ∈ W') (D : Finset C)
    (hD : ∀ δ ∈ D, ‖δ‖ ≤ 1 ∧ W'.valuation (ψ RatFunc.X - κ δ) = 1)
    (hsm : ∀ (β : C) (hβ : ‖β‖ ≤ 1), (∀ δ ∈ D, ‖β - δ‖ = 1) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G)), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) =
        discIdeal (0 : C) 1 → Q (P'.comap (ιβ χ hφ hχ hβ))) :
    ∃ 𝔮 : Ideal (DRint (0 : E) 1 F₀), Q 𝔮 ∧
      ∀ y : DRint (0 : E) 1 F₀, W'.valuation (χ y) < 1 → y ∈ 𝔮 := by
  by_cases hcl : ∃ β : C, ‖β‖ ≤ 1 ∧ W'.valuation (ψ RatFunc.X - κ β) < 1
  · obtain ⟨β, hβ, hXβ⟩ := hcl
    refine closedCaseQ hφ hχ Q W' hO hβ hXβ (hsm β hβ fun δ hδ ↦ ?_)
    obtain ⟨hδ1, hδu⟩ := hD δ hδ
    have hval : W'.valuation (κ (β - δ)) = 1 := by
      have : (κ (β - δ)) = (ψ RatFunc.X - κ δ) - (ψ RatFunc.X - κ β) := by
        simp only [map_sub]; ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (by rw [hδu]; exact hXβ), hδu]
    have hle : ‖β - δ‖ ≤ 1 := (norm_sub_le_max' _ _).trans (max_le hβ hδ1)
    refine le_antisymm hle (not_lt.1 fun hlt ↦ ?_)
    rw [← hO.lt_one_iff, hval] at hlt
    exact lt_irrefl _ hlt
  · push Not at hcl
    obtain ⟨β, hβ, hfar⟩ := exists_far D fun δ hδ ↦ (hD δ hδ).1
    have hnc : ∀ δ ∈ D, ‖β - δ‖ = 1 := fun δ hδ ↦ le_antisymm
      ((norm_sub_le_max' _ _).trans (max_le hβ (hD δ hδ).1)) (hfar δ hδ)
    let Wβ : ValuationSubring (Aff β 1 one_ne_zero G) := W'
    have hOβ : IsOverOC C Wβ := isOverOC_aff hO β
    have hXβ : algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X ∈ Wβ := by
      rw [algebraMap_aff_X]
      exact sub_mem hX (hO.mem hβ)
    have hgen : ∀ b : C, ‖b‖ ≤ 1 → Wβ.valuation
        (algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X -
          algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) (algebraMap C (RatFunc C) b)) = 1 := by
      intro b hb
      have e : algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) (algebraMap C (RatFunc C) b) =
          toAff one_ne_zero (κ b) := by
        change ψ (aff β 1 one_ne_zero _) = _
        rw [AlgEquiv.commutes]; rfl
      rw [algebraMap_aff_X, e]
      change W'.valuation (ψ RatFunc.X - (κ β) - (κ b)) = 1
      have : ψ RatFunc.X - (κ β) - (κ b) = ψ RatFunc.X - κ (β + b) := by
        simp only [map_add]; ring
      rw [this]
      have hβb : ‖β + b‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hβ hb)
      exact le_antisymm ((W'.valuation_le_one_iff _).2 (sub_mem hX (hO.mem hβb))) (hcl _ hβb)
    have hle := comap_centerI_drint_le hOβ hXβ hgen
    haveI := discIdeal_isMaximal (a := (0 : C)) one_ne_zero
    obtain ⟨Qm, hQI, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (discIdeal (0 : C) 1) _ hle
    haveI := hQp
    haveI : Qm.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
      (by rw [hQc]; exact discIdeal_isMaximal one_ne_zero)
    exact ⟨_, hsm β hβ hnc Qm inferInstance hQc, fun y hy ↦ hQI hy⟩

end CasesQ

end W10Route

end SemistableReduction
