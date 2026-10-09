/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateCrossingField
import TemperedFundamentalGroups.Andre.TateModelCharts
import TemperedFundamentalGroups.SemistableReduction.TrdegOne
import TemperedFundamentalGroups.SemistableReduction.MonomialUnique
import TemperedFundamentalGroups.SemistableReduction.ProjChartGerms

/-!
# The germs of the Tate model at `p` and `q` are node germs (HarmonicTate glue)

In the chart `x₀ ≠ 0` of the Tate model (`s = x₁/x₀`, `w = x₂/x₀`) the equation is
`w (s (s + 1) − b₆ w²) = π (1 + b₄ w²)` (`TateNormal.chart_zero_eq`). At `p = (0, 0)` and
`q = (−1, 0)`, with `π = ε ϖⁿ`, the coordinates `u = w`, `v = (s (s + 1) − b₆ w²) / ((1 + b₄ w²) ε)`
satisfy `u v = ϖⁿ` exactly, and the localization of the chart is a node germ
(`TateNormal.nodeGerm_chart_zero`, Blueprint §10.3.8):

* the function field is algebraic over `K[1/a]` (`isAlgebraic_adjoin_wL`, via transcendence
  degree one);
* every element of the chart is a constant modulo `(s − δ, w)` (`exists_const_mod`), and
  `s − δ = (v ε (1 + b₄ w²) + b₆ w²) / (s + 1 + δ)` with `s + 1 + δ` a unit at the point;
* every element of the function field is a quotient of elements of the chart
  (`exists_div_chart_zero`).
-/

universe u

open Polynomial
open _root_.SemistableReduction (locAt mem_locAt_of_mem inv_mem_locAt mul_ne_one_of_mem
  div_mul_ne_one ne_zero_of_notMem)

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "L" => TateField π b₄ b₆

attribute [local instance] algK

instance : IsScalarTower O K L :=
  IsScalarTower.of_algebraMap_eq fun o => (IsFractionRing.lift_algebraMap _ o).symm

lemma algebraMap_K_coe (o : O) : algebraMap K L (o : K) = algebraMap O L o :=
  (IsScalarTower.algebraMap_apply O K L o).symm

/-- `a = X` is transcendental over `K`. -/
lemma transcendental_aL : Transcendental K (aL π b₄ b₆) := by
  have hO : Transcendental O (aL π b₄ b₆) := by
    rw [transcendental_iff_injective]
    intro p q hpq
    have h : ∀ r : O[X], aeval (aL π b₄ b₆) r = algebraMap O[X] L r := fun r => by
      rw [aL, aeval_algebraMap_apply, aeval_X_left_apply]
    rw [h, h] at hpq
    exact algebraMap_injective π b₄ b₆ hpq
  intro h
  exact hO ((IsFractionRing.isAlgebraic_iff O K L).2 h)

/-- `w = 1/a` is transcendental over `K`. -/
lemma transcendental_wL : Transcendental K (aL π b₄ b₆)⁻¹ := fun h =>
  transcendental_aL π b₄ b₆ (IsAlgebraic.inv_iff.1 h)

/-- The function field is algebraic over `K[a]`. -/
lemma isAlgebraic_adjoin_aL : Algebra.IsAlgebraic (Algebra.adjoin K {aL π b₄ b₆}) L := by
  -- `O[X] → TateRing` is integral
  haveI : Algebra.IsAlgebraic O[X] (TateRing π b₄ b₆) := by
    have hb : IsIntegral O[X] (bA π b₄ b₆) :=
      ⟨fpoly π b₄ b₆, fpoly_monic π b₄ b₆, AdjoinRoot.eval₂_root _⟩
    refine ⟨fun z => ?_⟩
    obtain ⟨p, q, rfl⟩ := exists_repr π b₄ b₆ z
    exact (isIntegral_algebraMap.add (isIntegral_algebraMap.mul hb)).isAlgebraic
  haveI : Module.IsTorsionFree O[X] L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact algebraMap_injective π b₄ b₆
  haveI : Algebra.IsAlgebraic O[X] L :=
    (IsFractionRing.isAlgebraic_iff' O[X] (TateRing π b₄ b₆) L).1 inferInstance
  have hmem : ∀ p : O[X], algebraMap O[X] L p ∈ Algebra.adjoin K {aL π b₄ b₆} := fun p => by
    have : algebraMap O[X] L p = aeval (aL π b₄ b₆) (p.map (algebraMap O K)) := by
      rw [aeval_map_algebraMap, aL, aeval_algebraMap_apply, aeval_X_left_apply]
    rw [this, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨_, rfl⟩
  letI : Algebra O[X] (Algebra.adjoin K {aL π b₄ b₆}) :=
    ((algebraMap O[X] L).codRestrict (Algebra.adjoin K {aL π b₄ b₆}).toSubring hmem).toAlgebra
  haveI : IsScalarTower O[X] (Algebra.adjoin K {aL π b₄ b₆}) L :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Algebra.IsAlgebraic.extendScalars (R := O[X]) fun p q h =>
    algebraMap_injective π b₄ b₆ (congrArg Subtype.val h)

/-- The function field is algebraic over `K[1/a]`. -/
lemma isAlgebraic_adjoin_wL : Algebra.IsAlgebraic (Algebra.adjoin K {(aL π b₄ b₆)⁻¹}) L :=
  SemistableReduction.isAlgebraic_adjoin_of_transcendental (transcendental_aL π b₄ b₆)
    (isAlgebraic_adjoin_aL π b₄ b₆) (transcendental_wL π b₄ b₆)


/-! ### The chart `x₀ ≠ 0` near the nodes `p = (0, 0)` and `q = (-1, 0)` -/

/-- `s = x₁/x₀ = b/a`. -/
abbrev sL : L := coords π b₄ b₆ 1 / coords π b₄ b₆ 0

/-- `w = x₂/x₀ = 1/a`. -/
abbrev wL : L := coords π b₄ b₆ 2 / coords π b₄ b₆ 0

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma algebraMap_cpoly : algebraMap O[X] L (cpoly π b₄ b₆) =
    algebraMap O L π * aL π b₄ b₆ ^ 3 + algebraMap O L π * algebraMap O L b₄ * aL π b₄ b₆ +
      algebraMap O L b₆ := by
  simp only [cpoly, map_add, map_mul, map_pow, aL, algebraMap_O_apply]

/-- **The equation in the chart `x₀ ≠ 0`**: `w (s (s + 1) − b₆ w²) = π (1 + b₄ w²)`. -/
lemma chart_zero_eq : wL π b₄ b₆ * (sL π b₄ b₆ * (sL π b₄ b₆ + 1) -
      algebraMap O L b₆ * wL π b₄ b₆ ^ 2) =
    algebraMap O L π * (1 + algebraMap O L b₄ * wL π b₄ b₆ ^ 2) := by
  have ha : aL π b₄ b₆ ≠ 0 := aL_ne_zero π b₄ b₆
  have h := bL_sq π b₄ b₆
  rw [algebraMap_cpoly] at h
  have hs : sL π b₄ b₆ = bL π b₄ b₆ / aL π b₄ b₆ := rfl
  have hw : wL π b₄ b₆ = 1 / aL π b₄ b₆ := rfl
  rw [hs, hw]
  field_simp
  linear_combination h

lemma sL_mem : sL π b₄ b₆ ∈ chart π b₄ b₆ 0 := mem_chart π b₄ b₆ 0 1
lemma wL_mem : wL π b₄ b₆ ∈ chart π b₄ b₆ 0 := mem_chart π b₄ b₆ 0 2

lemma wL_eq : wL π b₄ b₆ = (aL π b₄ b₆)⁻¹ := by
  simp [wL, coords]

/-- Every element of the chart is a constant modulo `(s - δ, w)`. -/
lemma exists_const_mod (δ : O) {x : L} (hx : x ∈ chart π b₄ b₆ 0) :
    ∃ (o : O) (y₁ y₂ : L), y₁ ∈ chart π b₄ b₆ 0 ∧ y₂ ∈ chart π b₄ b₆ 0 ∧
      x = algebraMap O L o + (sL π b₄ b₆ - algebraMap O L δ) * y₁ + wL π b₄ b₆ * y₂ := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨o, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨o, 0, 0, zero_mem _, zero_mem _, by simp⟩
    · fin_cases j
      · refine ⟨1, 0, 0, zero_mem _, zero_mem _, ?_⟩
        change aL π b₄ b₆ / aL π b₄ b₆ = _
        rw [div_self (aL_ne_zero π b₄ b₆), map_one]
        ring
      · exact ⟨δ, 1, 0, one_mem _, zero_mem _, by
          change sL π b₄ b₆ = _
          ring⟩
      · exact ⟨0, 0, 1, zero_mem _, one_mem _, by
          change wL π b₄ b₆ = _
          rw [map_zero]
          ring⟩
  | zero => exact ⟨0, 0, 0, zero_mem _, zero_mem _, by simp⟩
  | one => exact ⟨1, 0, 0, zero_mem _, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨o, a₁, a₂, ha₁, ha₂, rfl⟩ := hx
    obtain ⟨o', b₁, b₂, hb₁, hb₂, rfl⟩ := hy
    exact ⟨o + o', a₁ + b₁, a₂ + b₂, add_mem ha₁ hb₁, add_mem ha₂ hb₂, by rw [map_add]; ring⟩
  | neg x _ hx =>
    obtain ⟨o, a₁, a₂, ha₁, ha₂, rfl⟩ := hx
    exact ⟨-o, -a₁, -a₂, neg_mem ha₁, neg_mem ha₂, by rw [map_neg]; ring⟩
  | mul x y hx' hy' hx hy =>
    obtain ⟨o, a₁, a₂, ha₁, ha₂, rfl⟩ := hx
    obtain ⟨o', b₁, b₂, hb₁, hb₂, rfl⟩ := hy
    have hσ : sL π b₄ b₆ - algebraMap O L δ ∈ chart π b₄ b₆ 0 :=
      sub_mem (sL_mem π b₄ b₆) (SemistableReduction.base_le_projChart 0 ⟨δ, rfl⟩)
    have hO : ∀ o : O, algebraMap O L o ∈ chart π b₄ b₆ 0 := fun o =>
      SemistableReduction.base_le_projChart 0 ⟨o, rfl⟩
    refine ⟨o * o', algebraMap O L o * b₁ + a₁ * algebraMap O L o' +
        a₁ * (sL π b₄ b₆ - algebraMap O L δ) * b₁ + a₁ * wL π b₄ b₆ * b₂,
      algebraMap O L o * b₂ + a₂ * algebraMap O L o' +
        a₂ * (sL π b₄ b₆ - algebraMap O L δ) * b₁ + a₂ * wL π b₄ b₆ * b₂, ?_, ?_, ?_⟩
    · exact add_mem (add_mem (add_mem (mul_mem (hO o) hb₁) (mul_mem ha₁ (hO o')))
        (mul_mem (mul_mem ha₁ hσ) hb₁)) (mul_mem (mul_mem ha₁ (wL_mem π b₄ b₆)) hb₂)
    · exact add_mem (add_mem (add_mem (mul_mem (hO o) hb₂) (mul_mem ha₂ (hO o')))
        (mul_mem (mul_mem ha₂ hσ) hb₁)) (mul_mem (mul_mem ha₂ (wL_mem π b₄ b₆)) hb₂)
    · rw [map_mul]; ring

lemma algebraMap_mem_chart (i : Fin (2 + 1)) (o : O) : algebraMap O L o ∈ chart π b₄ b₆ i :=
  SemistableReduction.base_le_projChart i ⟨o, rfl⟩

/-- Elements of the chart `x₂ ≠ 0` (i.e. of `O[a, b]`) become elements of the chart `x₀ ≠ 0`
after multiplication by a power of `w = 1/a`. -/
lemma exists_wL_pow_mul_mem {x : L} (hx : x ∈ chart π b₄ b₆ 2) :
    ∃ k : ℕ, wL π b₄ b₆ ^ k * x ∈ chart π b₄ b₆ 0 := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨o, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨0, by simpa using algebraMap_mem_chart π b₄ b₆ 0 o⟩
    · have hc0 : coords π b₄ b₆ 0 = aL π b₄ b₆ := rfl
      have hc1 : coords π b₄ b₆ 1 = bL π b₄ b₆ := rfl
      have hc2 : coords π b₄ b₆ 2 = 1 := rfl
      have hw : wL π b₄ b₆ = 1 / aL π b₄ b₆ := rfl
      have hs : sL π b₄ b₆ = bL π b₄ b₆ / aL π b₄ b₆ := rfl
      have hj : j = 0 ∨ j = 1 ∨ j = 2 := by fin_cases j <;> simp
      rcases hj with rfl | rfl | rfl
      · refine ⟨1, ?_⟩
        change wL π b₄ b₆ ^ 1 * (coords π b₄ b₆ 0 / coords π b₄ b₆ 2) ∈ _
        rw [hc0, hc2, hw, div_one, pow_one, one_div, inv_mul_cancel₀ (aL_ne_zero π b₄ b₆)]
        exact one_mem _
      · refine ⟨1, ?_⟩
        change wL π b₄ b₆ ^ 1 * (coords π b₄ b₆ 1 / coords π b₄ b₆ 2) ∈ _
        rw [hc1, hc2, div_one, pow_one, hw, one_div, inv_mul_eq_div, ← hs]
        exact sL_mem π b₄ b₆
      · refine ⟨0, ?_⟩
        change wL π b₄ b₆ ^ 0 * (coords π b₄ b₆ 2 / coords π b₄ b₆ 2) ∈ _
        rw [hc2, div_one, pow_zero, one_mul]
        exact one_mem _
  | zero => exact ⟨0, by simp⟩
  | one => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    have : wL π b₄ b₆ ^ (k + l) * (x + y) =
        wL π b₄ b₆ ^ l * (wL π b₄ b₆ ^ k * x) + wL π b₄ b₆ ^ k * (wL π b₄ b₆ ^ l * y) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem (wL_mem π b₄ b₆) _) hk)
      (mul_mem (pow_mem (wL_mem π b₄ b₆) _) hl)
  | neg x _ hx =>
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, by rw [mul_neg]; exact neg_mem hk⟩
  | mul x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨l, hl⟩ := hy
    refine ⟨k + l, ?_⟩
    have : wL π b₄ b₆ ^ (k + l) * (x * y) = (wL π b₄ b₆ ^ k * x) * (wL π b₄ b₆ ^ l * y) := by
      ring
    rw [this]
    exact mul_mem hk hl

/-- Every element of the function field is a quotient of elements of the chart `x₀ ≠ 0`. -/
lemma exists_div_chart_zero (f : L) :
    ∃ g h : L, g ∈ chart π b₄ b₆ 0 ∧ h ∈ chart π b₄ b₆ 0 ∧ h ≠ 0 ∧ f = g / h := by
  obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := TateRing π b₄ b₆) f
  have hmem : ∀ γ : TateRing π b₄ b₆, algebraMap _ L γ ∈ chart π b₄ b₆ 2 := fun γ => by
    rw [chart_two_eq]; exact ⟨γ, rfl⟩
  obtain ⟨k, hk⟩ := exists_wL_pow_mul_mem π b₄ b₆ (hmem α)
  obtain ⟨l, hl⟩ := exists_wL_pow_mul_mem π b₄ b₆ (hmem β)
  have hw0 : wL π b₄ b₆ ≠ 0 := by rw [wL_eq]; exact inv_ne_zero (aL_ne_zero π b₄ b₆)
  have hβ0 : algebraMap (TateRing π b₄ b₆) L β ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hβ
  refine ⟨wL π b₄ b₆ ^ l * (wL π b₄ b₆ ^ k * algebraMap _ L α),
    wL π b₄ b₆ ^ k * (wL π b₄ b₆ ^ l * algebraMap _ L β),
    mul_mem (pow_mem (wL_mem π b₄ b₆) _) hk, mul_mem (pow_mem (wL_mem π b₄ b₆) _) hl,
    mul_ne_zero (pow_ne_zero _ hw0) (mul_ne_zero (pow_ne_zero _ hw0) hβ0), ?_⟩
  field_simp

variable {π b₄ b₆} in
/-- The node coordinate `v = (s (s + 1) − b₆ w²) / ((1 + b₄ w²) ε)`. -/
def vL (ε : O) : L :=
  (sL π b₄ b₆ * (sL π b₄ b₆ + 1) - algebraMap O L b₆ * wL π b₄ b₆ ^ 2) /
    ((1 + algebraMap O L b₄ * wL π b₄ b₆ ^ 2) * algebraMap O L ε)

set_option maxHeartbeats 800000 in
-- a single long proof: generation modulo `(ϖ, u, v)` needs many ring identities in `L`
/-- **The germ of the Tate model at `p` (`δ = 0`) or `q` (`δ = -1`) is a node germ** with
exact coordinates `u = w`, `v = (s (s + 1) − b₆ w²) / ((1 + b₄ w²) ε)`, `u v = ϖⁿ` where
`π = ε ϖⁿ`; `u, v` are non-units. Here `Q` is a prime of the chart `x₀ ≠ 0` containing `𝔪`,
`s - δ` and `w`. -/
theorem nodeGerm_chart_zero {ϖ : O} {ε : Oˣ} {n : ℕ} (hπε : π = ε * ϖ ^ n) (δ : O)
    (hδ : δ = 0 ∨ δ = -1) (Q : Ideal (chart π b₄ b₆ 0)) [Q.IsPrime]
    (hσ : (⟨sL π b₄ b₆ - algebraMap O L δ,
      sub_mem (sL_mem π b₄ b₆) (algebraMap_mem_chart π b₄ b₆ 0 δ)⟩ : chart π b₄ b₆ 0) ∈ Q)
    (hw : (⟨wL π b₄ b₆, wL_mem π b₄ b₆⟩ : chart π b₄ b₆ 0) ∈ Q)
    (h𝔪 : ∀ o ∈ IsLocalRing.maximalIdeal O,
      (⟨algebraMap O L o, algebraMap_mem_chart π b₄ b₆ 0 o⟩ : chart π b₄ b₆ 0) ∈ Q) :
    SemistableReduction.NodeGerm O ϖ (locAt (chart π b₄ b₆ 0) Q) (wL π b₄ b₆)
        (vL (ε : O)) n ∧
      (∀ z ∈ locAt (chart π b₄ b₆ 0) Q, wL π b₄ b₆ * z ≠ 1) ∧
      (∀ z ∈ locAt (chart π b₄ b₆ 0) Q, vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) * z ≠ 1) := by
  set s := sL π b₄ b₆
  set w := wL π b₄ b₆
  have hO : ∀ o : O, algebraMap O L o ∈ (chart π b₄ b₆ 0) := algebraMap_mem_chart π b₄ b₆ 0
  have hQ1 : ∀ x : (chart π b₄ b₆ 0), IsUnit x → x ∉ Q := fun x hx h =>
    Ideal.IsPrime.ne_top inferInstance (Ideal.eq_top_of_isUnit_mem _ h hx)
  -- `τ = s + 1 + δ`, `σ τ = s (s + 1)`
  set σ := s - algebraMap O L δ
  set τ := s + 1 + algebraMap O L δ
  have hτA : τ ∈ (chart π b₄ b₆ 0) := add_mem (add_mem (sL_mem π b₄ b₆) (one_mem _)) (hO δ)
  have hστ : σ * τ = s * (s + 1) := by
    rcases hδ with rfl | rfl <;> simp only [map_zero, map_neg, map_one, σ, τ] <;> ring
  have hτQ : (⟨τ, hτA⟩ : (chart π b₄ b₆ 0)) ∉ Q := by
    intro h
    have hd : (⟨τ, hτA⟩ : (chart π b₄ b₆ 0)) - ⟨σ, sub_mem (sL_mem π b₄ b₆) (hO δ)⟩ ∈ Q :=
      sub_mem h hσ
    refine hQ1 _ ?_ hd
    rcases hδ with rfl | rfl
    · convert isUnit_one using 1
      exact Subtype.ext (by simp [σ, τ])
    · have hu : IsUnit (-1 : chart π b₄ b₆ 0) := isUnit_one.neg
      convert hu using 1
      exact Subtype.ext (by simp [σ, τ])
  -- `D = 1 + b₄ w²` and `ε` are units at the point
  have hDA : 1 + algebraMap O L b₄ * w ^ 2 ∈ (chart π b₄ b₆ 0) :=
    add_mem (one_mem _) (mul_mem (hO b₄) (pow_mem (wL_mem π b₄ b₆) 2))
  have hDQ : (⟨_, hDA⟩ : (chart π b₄ b₆ 0)) ∉ Q := by
    intro h
    have hw2 : (⟨algebraMap O L b₄ * w ^ 2,
        mul_mem (hO b₄) (pow_mem (wL_mem π b₄ b₆) 2)⟩ : (chart π b₄ b₆ 0)) ∈ Q := by
      have : (⟨algebraMap O L b₄ * w ^ 2, mul_mem (hO b₄) (pow_mem (wL_mem π b₄ b₆) 2)⟩ :
          (chart π b₄ b₆ 0)) =
          ⟨algebraMap O L b₄, hO b₄⟩ * ⟨w, wL_mem π b₄ b₆⟩ ^ 2 := rfl
      rw [this]
      exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hw 2 two_pos)
    have h1 : (1 : (chart π b₄ b₆ 0)) ∈ Q := by
      have := sub_mem h hw2
      convert this using 1
      exact Subtype.ext (by simp)
    exact hQ1 1 isUnit_one h1
  have hεA : algebraMap O L (ε : O) ∈ (chart π b₄ b₆ 0) := hO _
  have hεQ : (⟨_, hεA⟩ : (chart π b₄ b₆ 0)) ∉ Q := by
    refine hQ1 _ ⟨⟨⟨_, hεA⟩, ⟨_, hO (ε⁻¹ : Oˣ)⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (by
        change algebraMap O L _ * algebraMap O L _ = 1
        rw [← map_mul, Units.mul_inv, map_one])
    · exact Subtype.ext (by
        change algebraMap O L _ * algebraMap O L _ = 1
        rw [← map_mul, Units.inv_mul, map_one])
  have hDεA : (1 + algebraMap O L b₄ * w ^ 2) * algebraMap O L (ε : O) ∈ (chart π b₄ b₆ 0) :=
    mul_mem hDA hεA
  have hDεQ : (⟨_, hDεA⟩ : (chart π b₄ b₆ 0)) ∉ Q := fun h => by
    rcases Ideal.IsPrime.mem_or_mem inferInstance
      (show (⟨_, hDA⟩ : (chart π b₄ b₆ 0)) * ⟨_, hεA⟩ ∈ Q from h)
      with h | h
    exacts [hDQ h, hεQ h]
  have hDε0 := ne_zero_of_notMem (chart π b₄ b₆ 0) Q hDεQ
  have hNA : s * (s + 1) - algebraMap O L b₆ * w ^ 2 ∈ (chart π b₄ b₆ 0) :=
    sub_mem (mul_mem (sL_mem π b₄ b₆) (add_mem (sL_mem π b₄ b₆) (one_mem _)))
      (mul_mem (hO b₆) (pow_mem (wL_mem π b₄ b₆) 2))
  have hNQ : (⟨_, hNA⟩ : (chart π b₄ b₆ 0)) ∈ Q := by
    have h1 : (⟨_, hNA⟩ : (chart π b₄ b₆ 0)) = ⟨σ, sub_mem (sL_mem π b₄ b₆) (hO δ)⟩ * ⟨τ, hτA⟩ -
        ⟨algebraMap O L b₆, hO b₆⟩ * ⟨w, wL_mem π b₄ b₆⟩ ^ 2 :=
      Subtype.ext (by push_cast; rw [hστ])
    rw [h1]
    exact sub_mem (Ideal.mul_mem_right _ _ hσ)
      (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hw 2 two_pos))
  have hv : vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) =
      (s * (s + 1) - algebraMap O L b₆ * w ^ 2) *
        ((1 + algebraMap O L b₄ * w ^ 2) * algebraMap O L (ε : O))⁻¹ := div_eq_mul_inv _ _
  have hvP : vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) ∈ locAt (chart π b₄ b₆ 0) Q := by
    rw [hv]
    exact mul_mem (mem_locAt_of_mem hNA) (inv_mem_locAt hDεQ)
  -- `w v = ϖⁿ`
  have hmul : w * vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) = algebraMap K L (ϖ : K) ^ n := by
    have heq := chart_zero_eq π b₄ b₆
    have hD0 : (1 + algebraMap O L b₄ * w ^ 2) ≠ 0 := ne_zero_of_notMem (chart π b₄ b₆ 0) Q hDQ
    have hε0 : algebraMap O L (ε : O) ≠ 0 := ne_zero_of_notMem (chart π b₄ b₆ 0) Q hεQ
    have hπ' : algebraMap O L π = algebraMap O L (ε : O) * algebraMap O L ϖ ^ n := by
      rw [← map_pow, ← map_mul]; exact congrArg _ hπε
    rw [vL, mul_div_assoc', heq, hπ', algebraMap_K_coe, div_eq_iff (mul_ne_zero hD0 hε0)]
    ring
  refine ⟨⟨fun o => ?_, mem_locAt_of_mem (wL_mem π b₄ b₆), hvP, hmul, ?_, fun f => ?_,
    fun f _ hf => ?_⟩, mul_ne_one_of_mem (wL_mem π b₄ b₆) hw, ?_⟩
  · rw [algebraMap_K_coe]; exact mem_locAt_of_mem (hO o)
  · -- generation modulo `(ϖ, u, v)`
    rintro _ ⟨a, b, hb, rfl⟩
    obtain ⟨oa, a₁, a₂, ha₁, ha₂, ha⟩ := exists_const_mod π b₄ b₆ δ a.2
    obtain ⟨ob, b₁, b₂, hb₁, hb₂, hb'⟩ := exists_const_mod π b₄ b₆ δ b.2
    have hob : IsUnit ob := by
      by_contra hu
      apply hb
      have : b = ⟨algebraMap O L ob, hO ob⟩ + ⟨σ, sub_mem (sL_mem π b₄ b₆) (hO δ)⟩ * ⟨b₁, hb₁⟩ +
          ⟨w, wL_mem π b₄ b₆⟩ * ⟨b₂, hb₂⟩ := Subtype.ext (by push_cast; exact hb')
      rw [this]
      exact add_mem (add_mem (h𝔪 ob ((IsLocalRing.mem_maximalIdeal ob).2 hu))
        (Ideal.mul_mem_right _ _ hσ)) (Ideal.mul_mem_right _ _ hw)
    obtain ⟨ub, hub⟩ := hob.exists_right_inv
    obtain ⟨o, ho⟩ : ∃ o : O, o = oa * ub := ⟨_, rfl⟩
    have hb0 := ne_zero_of_notMem (chart π b₄ b₆ 0) Q hb
    have hτ0 := ne_zero_of_notMem (chart π b₄ b₆ 0) Q hτQ
    -- `a − o b = σ (a₁ − o b₁) + w (a₂ − o b₂)`
    have hab : (a : L) - algebraMap O L o * b =
        σ * (a₁ - algebraMap O L o * b₁) + w * (a₂ - algebraMap O L o * b₂) := by
      rw [ha, hb']
      have : algebraMap O L oa - algebraMap O L o * algebraMap O L ob = 0 := by
        rw [← map_mul, ← map_sub, show oa - o * ob = 0 by
          rw [ho, show oa * ub * ob = oa * (ob * ub) by ring, hub, mul_one, sub_self], map_zero]
      linear_combination this
    -- `σ = (v ε D + b₆ w²) / τ`
    have hσv : σ * τ = vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) *
        ((1 + algebraMap O L b₄ * w ^ 2) * algebraMap O L (ε : O)) +
          algebraMap O L b₆ * w ^ 2 := by
      rw [vL, div_mul_cancel₀ _ hDε0, hστ]
      ring
    have hτinv : τ⁻¹ ∈ locAt (chart π b₄ b₆ 0) Q := inv_mem_locAt hτQ
    have hbinv : (b : L)⁻¹ ∈ locAt (chart π b₄ b₆ 0) Q := inv_mem_locAt hb
    have hO' := fun o => mem_locAt_of_mem (Q := Q) (hO o)
    refine ⟨o, 0, zero_mem _,
      algebraMap O L b₆ * w * (a₁ - algebraMap O L o * b₁) * τ⁻¹ * (b : L)⁻¹ +
        (a₂ - algebraMap O L o * b₂) * (b : L)⁻¹, ?_,
      (1 + algebraMap O L b₄ * w ^ 2) * algebraMap O L (ε : O) *
        (a₁ - algebraMap O L o * b₁) * τ⁻¹ * (b : L)⁻¹, ?_, ?_⟩
    · have := mem_locAt_of_mem (Q := Q) (wL_mem π b₄ b₆)
      have h1 := mem_locAt_of_mem (Q := Q) ha₁
      have h2 := mem_locAt_of_mem (Q := Q) ha₂
      have h3 := mem_locAt_of_mem (Q := Q) hb₁
      have h4 := mem_locAt_of_mem (Q := Q) hb₂
      exact add_mem (mul_mem (mul_mem (mul_mem (mul_mem (hO' b₆) this)
        (sub_mem h1 (mul_mem (hO' o) h3))) hτinv) hbinv)
        (mul_mem (sub_mem h2 (mul_mem (hO' o) h4)) hbinv)
    · have h1 := mem_locAt_of_mem (Q := Q) ha₁
      have h3 := mem_locAt_of_mem (Q := Q) hb₁
      exact mul_mem (mul_mem (mul_mem (mem_locAt_of_mem hDεA)
        (sub_mem h1 (mul_mem (hO' o) h3))) hτinv) hbinv
    · rw [algebraMap_K_coe, mul_zero, add_zero]
      have hz : (a : L) / b = algebraMap O L o + ((a : L) - algebraMap O L o * b) / b := by
        field_simp
        ring
      rw [hz, hab]
      have hσ' : σ = (vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) *
          ((1 + algebraMap O L b₄ * w ^ 2) * algebraMap O L (ε : O)) +
            algebraMap O L b₆ * w ^ 2) / τ := by
        rw [← hσv, mul_div_cancel_right₀ _ hτ0]
      rw [hσ']
      field_simp
      ring
  · -- fraction field
    obtain ⟨g, h, hg, hh, h0, rfl⟩ := exists_div_chart_zero π b₄ b₆ f
    exact ⟨g, mem_locAt_of_mem hg, h, mem_locAt_of_mem hh, h0, rfl⟩
  · -- algebraic over `K(u)`
    have halg := isAlgebraic_adjoin_wL π b₄ b₆
    rw [← wL_eq] at halg
    exact SemistableReduction.exists_relation_of_transcendental halg hf
  · -- `v` is a non-unit
    rw [show vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) =
      ((⟨_, hNA⟩ : (chart π b₄ b₆ 0)) : L) / ((⟨_, hDεA⟩ : (chart π b₄ b₆ 0)) : L) from rfl]
    exact div_mul_ne_one hNQ hDεQ

end

end TemperedFundamentalGroups.TateNormal
