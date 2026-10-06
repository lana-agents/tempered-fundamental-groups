/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8BLimit
import TemperedFundamentalGroups.SemistableReduction.ExhaustGluing
import TemperedFundamentalGroups.SemistableReduction.S8Transport

/-!
# Exhausting discs of a bad residue ball intersect ([AW Lemma 2.7(iii)], O6.1b)

Blueprint §9.12 O6.1b. If `D, D' ⊆ B` are disjoint discs exhausting in the residue ball `B`, let
`s = ‖a - a'‖` be the distance of their centres. The open ball `ball a' s` contains `D'` and
lies off the skeleton of the annulus `B ∖ D`, so by the tube condition (T⇒) for `D` all its Gauss
points are discs of tubes and (D⇐) makes it good (`ballGood_off`). Gluing of good discs (O11g)
along `D'` then makes `B` good.

Inputs (named hypotheses of their owners): (T⇒) `ExhaustGluing.TubeOfExhausting`,
(D⇐) `ExhaustGluing.SmoothOfDiscCond` (M10/O9 agent) and O11g `S8A.GoodGluingFor`.
-/

open Metric

namespace SemistableReduction

namespace S8A

open GaussTube AffineTwist BallTree ExhaustGluing

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- **Goodness off an exhausting disc**: if `closedBall a ‖c₁‖` is exhausting in `ball a ‖c‖`
and `a' ∈ ball a ‖c‖` lies outside it, the open ball of radius `‖a' - a‖` around `a'` is good. -/
theorem discSmooth_off (hT : TubeOfExhausting C F) (hD : SmoothOfDiscCond C F) {a c c₁ a' : C}
    (hc : c ≠ 0) (hc₁ : ‖c₁‖ < 1) (hc₁0 : c₁ ≠ 0) (hE : IsExhausting a hc hc₁ hc₁0 F)
    (h₁ : ‖c * c₁‖ < ‖a' - a‖) (h₂ : ‖a' - a‖ < ‖c‖) (hu : a' - a ≠ 0) :
    DiscSmooth F a' hu := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hTc := hT _ _ _ _ _ _ hE
  refine hD _ _ hu ⟨fun γ hγ hγ1 ↦ ?_, fun β γ hγ hβ hγβ ↦ ?_⟩
  · -- the Gauss point `w_{a', |u γ|}`
    have hβ : ‖c₁‖ < ‖(a' - a) / c‖ := by
      rw [norm_div, lt_div_iff₀ hcpos, mul_comm, ← norm_mul]; exact h₁
    have hβ1 : ‖(a' - a) / c‖ < 1 := by rw [norm_div, div_lt_one hcpos]; exact h₂
    have hγβ : ‖(a' - a) * γ / c‖ < ‖(a' - a) / c‖ := by
      rw [norm_div, norm_div, norm_mul]
      exact div_lt_div_of_pos_right (mul_lt_of_lt_one_right (norm_pos_iff.2 hu) hγ1) hcpos
    refine (isTubeDisc_congr _ _ (by field_simp; ring) (by field_simp)).1
      (hTc.2 ((a' - a) / c) ((a' - a) * γ / c) (div_ne_zero (mul_ne_zero hu hγ) hc) hβ hβ1 hγβ)
  · -- the Gauss point `w_{a' + u β, |u γ|}`
    set β' := (a' + (a' - a) * β - a) / c
    have hnorm : ‖a' + (a' - a) * β - a‖ = ‖a' - a‖ := by
      have hlt : ‖(a' - a) * β‖ < ‖a' - a‖ := by
        rw [norm_mul]; exact mul_lt_of_lt_one_right (norm_pos_iff.2 hu) hβ
      rw [show a' + (a' - a) * β - a = (a' - a) + (a' - a) * β by ring]
      exact IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne' |>.trans
        (max_eq_left hlt.le)
    have hβ' : ‖c₁‖ < ‖β'‖ := by
      rw [norm_div, hnorm, lt_div_iff₀ hcpos, mul_comm, ← norm_mul]; exact h₁
    have hβ'1 : ‖β'‖ < 1 := by rw [norm_div, hnorm, div_lt_one hcpos]; exact h₂
    have hγβ' : ‖(a' - a) * γ / c‖ < ‖β'‖ := by
      rw [norm_div, norm_div, hnorm, norm_mul]
      refine div_lt_div_of_pos_right ?_ hcpos
      exact mul_lt_of_lt_one_right (norm_pos_iff.2 hu) (hγβ.trans hβ)
    refine (isTubeDisc_congr _ _ (by simp only [β']; field_simp; ring) (by field_simp)).1
      (hTc.2 β' ((a' - a) * γ / c) (div_ne_zero (mul_ne_zero hu hγ) hc) hβ' hβ'1 hγβ')

/-- **[AW Lemma 2.7(iii)] (O6.1b)**: two exhausting discs of a bad residue ball intersect. -/
theorem exhInterFor_of (hT : TubeOfExhausting C F) (hD : SmoothOfDiscCond C F)
    (hG : GoodGluingFor C F) : ExhInterFor C F := by
  intro b c hc hbad D hD₁ D' hD₂
  by_contra hne
  obtain ⟨a₁, d₁, hd₁, rfl⟩ := hD₁.1
  obtain ⟨a₂, d₂, hd₂, rfl⟩ := hD₂.1
  have hfar₁ : ‖d₁‖ < ‖a₂ - a₁‖ := by
    by_contra! h
    exact hne ⟨a₂, BallTree.mem_closedBall'.2 h, BallTree.mem_closedBall'.2 (by simp)⟩
  have hfar₂ : ‖d₂‖ < ‖a₂ - a₁‖ := by
    by_contra! h
    exact hne ⟨a₁, BallTree.mem_closedBall'.2 (by simp),
      BallTree.mem_closedBall'.2 (by rwa [norm_sub_rev])⟩
  have ha₁ : a₁ ∈ ball b ‖c‖ := hD₁.2.1 (BallTree.mem_closedBall'.2 (by simp))
  have ha₂ : a₂ ∈ ball b ‖c‖ := hD₂.2.1 (BallTree.mem_closedBall'.2 (by simp))
  have hball : ball b ‖c‖ = ball a₁ ‖c‖ := IsUltrametricDist.ball_eq_of_mem ha₁
  have hcball : closedBall b ‖c‖ = closedBall a₁ ‖c‖ :=
    IsUltrametricDist.closedBall_eq_of_mem (ball_subset_closedBall ha₁)
  have hsc : ‖a₂ - a₁‖ < ‖c‖ := BallTree.mem_ball'.1 (hball ▸ ha₂)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hd₁c : ‖d₁ / c‖ < 1 := by
    rw [norm_div, div_lt_one hcpos]; exact hfar₁.trans hsc
  have hE : IsExhausting a₁ hc hd₁c (div_ne_zero hd₁ hc) F :=
    hD₁.2.2 a₁ c (d₁ / c) hc hd₁c (div_ne_zero hd₁ hc) (by rw [mul_div_cancel₀ _ hc]) hcball
  have hu : a₂ - a₁ ≠ 0 := by
    intro h; rw [h, norm_zero] at hfar₁; exact (norm_nonneg _).not_gt hfar₁
  have hoff := discSmooth_off hT hD hc hd₁c (div_ne_zero hd₁ hc) hE
    (by rw [mul_div_cancel₀ _ hc]; exact hfar₁) hsc hu
  have hgood : BallGood F (ball a₂ ‖a₂ - a₁‖) := (S8A.Transport.ballGood_iff hu).2 hoff
  refine hbad (hG b c a₂ (a₂ - a₁) d₂ hc hu hd₂ hfar₂ ?_ hD₂.2.2 hgood)
  intro z hz
  rw [hball]
  exact BallTree.mem_ball'.2 ((norm_sub_le_max' z a₂ a₁).trans_lt
    (max_lt ((BallTree.mem_closedBall'.1 hz).trans_lt hsc) hsc))

end S8A

end SemistableReduction
