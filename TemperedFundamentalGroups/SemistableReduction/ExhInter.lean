/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8BLimit
import TemperedFundamentalGroups.SemistableReduction.ExhaustGluing
import TemperedFundamentalGroups.SemistableReduction.S8Transport
import TemperedFundamentalGroups.SemistableReduction.NearBoundary

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

/-- **O6.1e (O11g in ball form)** from the single-centre gluing `discSmooth_iff_of_le` (M10/O9
agent, under (T⇒), (D⇒), (D⇐)) and representation independence (`Transport.ballGood_iff`). -/
theorem goodGluingFor_of (hT : TubeOfExhausting C F) (hD : DiscCondOfSmooth C F)
    (hD' : SmoothOfDiscCond C F) : GoodGluingFor C F := by
  intro b c a u e hc hu he heu hsub hE hgood
  have ha : a ∈ ball b ‖c‖ := hsub (BallTree.mem_closedBall'.2 (by simp))
  have hball : ball b ‖c‖ = ball a ‖c‖ := IsUltrametricDist.ball_eq_of_mem ha
  have hcball : closedBall b ‖c‖ = closedBall a ‖c‖ :=
    IsUltrametricDist.closedBall_eq_of_mem (ball_subset_closedBall ha)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have huc : ‖u‖ < ‖c‖ := ((closedBall_subset_ball_iff').1 (hsub.trans hball.le)).1
  have hu1 : ‖u / c‖ < 1 := by rw [norm_div, div_lt_one hcpos]; exact huc
  have heu' : ‖e / c‖ < ‖u / c‖ := by
    rw [norm_div, norm_div]; exact div_lt_div_of_pos_right heu hcpos
  have hbig : IsExhausting a hc (heu'.trans hu1) (div_ne_zero he hc) F :=
    hE a c (e / c) hc (heu'.trans hu1) (div_ne_zero he hc) (by rw [mul_div_cancel₀ _ hc])
      hcball
  have hiff := discSmooth_iff_of_le hT hD hD' hc (div_ne_zero hu hc) hu1 (div_ne_zero he hc)
    heu' hbig
  have hcu : c * (u / c) = u := mul_div_cancel₀ _ hc
  have hsmall : DiscSmooth F a (mul_ne_zero hc (div_ne_zero hu hc)) := by
    have := (Transport.ballGood_iff (mul_ne_zero hc (div_ne_zero hu hc))).1 (by rwa [hcu])
    exact this
  rw [hball]
  exact (Transport.ballGood_iff hc).2 (hiff.2 hsmall)

/-- **O6.1d (O11)** from the M10/O9 agent's `ExhaustGluing.isExhausting_iff_of_le` under (T⇒),
(T⇐). -/
theorem o11For_of (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F) : O11For C F :=
  fun hc0 hu0 hu he0 heu hc'0 hc'e _ _ hbig hsmall ↦
    (isExhausting_iff_of_le hT hT' hc0 hu0 hu he0 heu hc'0 hc'e hbig).2 hsmall

/-- **Representation independence of exhaustion** (under (T⇒), (T⇐)): if `closedBall b ‖c e‖` is
exhausting in `ball b ‖c‖` in the chart `(b, c, e)`, it is so in every chart (`EdgeGood`). -/
theorem edgeGood_of_isExhausting (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F)
    {b c e : C} (hc : c ≠ 0) (he : ‖e‖ < 1) (he0 : e ≠ 0) (hE : IsExhausting b hc he he0 F) :
    EdgeGood F (closedBall b ‖c * e‖) (closedBall b ‖c‖) := by
  intro a₀ c₀ c₀' hc₀ hc₀' hc0₀' hD0 hG0
  have hTc := hT _ _ _ _ _ _ hE
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨hcc, hab⟩ := (closedBall_eq_closedBall_iff' hc hc₀).1 hG0
  obtain ⟨hce, hab'⟩ := (closedBall_eq_closedBall_iff' (mul_ne_zero hc he0)
    (mul_ne_zero hc₀ hc0₀')).1 hD0
  have hee : ‖c₀'‖ = ‖e‖ := by
    rw [norm_mul, norm_mul, ← hcc] at hce
    exact (mul_left_cancel₀ hcpos.ne' hce).symm
  refine hT' _ _ _ _ _ _ ⟨fun γ hγ h1 h2 ↦ ?_, fun β γ hγ h1 h2 h3 ↦ ?_⟩
  · -- the circles: centres within `‖c e‖` of `b`
    have hγ' : ‖e‖ < ‖c₀ * γ / c‖ := by
      rw [norm_div, norm_mul, ← hcc, mul_div_cancel_left₀ _ hcpos.ne', ← hee]; exact h1
    have hγ'1 : ‖c₀ * γ / c‖ < 1 := by
      rw [norm_div, norm_mul, ← hcc, mul_div_cancel_left₀ _ hcpos.ne']; exact h2
    have hcirc := (isTubeCircle_congr _ (mul_ne_zero hc₀ hγ) rfl (by field_simp)).1
      (hTc.1 (c₀ * γ / c) (div_ne_zero (mul_ne_zero hc₀ hγ) hc) hγ' hγ'1)
    intro b' hb'
    refine hcirc b' ?_
    have hce' : ‖c * e‖ < ‖c₀ * γ‖ := by
      rw [norm_mul, norm_mul, ← hcc, ← hee]
      exact mul_lt_mul_of_pos_left h1 hcpos
    calc ‖b - b'‖ ≤ max ‖b - a₀‖ ‖a₀ - b'‖ := norm_sub_le_max' b a₀ b'
      _ < ‖c₀ * γ‖ := max_lt (hab'.trans_lt hce') hb'
  · -- the discs off the skeleton
    have hcb : ‖c * e‖ < ‖c₀ * β‖ := by
      rw [norm_mul, norm_mul, ← hcc, ← hee]
      exact mul_lt_mul_of_pos_left h1 hcpos
    have hnorm : ‖a₀ + c₀ * β - b‖ = ‖c₀ * β‖ := by
      have hlt : ‖a₀ - b‖ < ‖c₀ * β‖ := by rw [norm_sub_rev]; exact hab'.trans_lt hcb
      rw [show a₀ + c₀ * β - b = c₀ * β + (a₀ - b) by ring]
      exact (IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne').trans
        (max_eq_left hlt.le)
    have hβ' : ‖(a₀ + c₀ * β - b) / c‖ = ‖β‖ := by
      rw [norm_div, hnorm, norm_mul, ← hcc, mul_div_cancel_left₀ _ hcpos.ne']
    have hγ' : ‖c₀ * γ / c‖ = ‖γ‖ := by
      rw [norm_div, norm_mul, ← hcc, mul_div_cancel_left₀ _ hcpos.ne']
    refine (isTubeDisc_congr _ (mul_ne_zero hc₀ hγ) (by field_simp; ring) (by field_simp)).1
      (hTc.2 ((a₀ + c₀ * β - b) / c) (c₀ * γ / c) (div_ne_zero (mul_ne_zero hc₀ hγ) hc)
        (by rw [hβ', ← hee]; exact h1) (by rw [hβ']; exact h2) (by rw [hβ', hγ']; exact h3))

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **O6.1a** (`R4ExFor`, every residue ball contains an exhausting disc) from R4(ii)
(`GaussTube.belowGerm`, proved) and the representation independence of exhaustion under (T⇒),
(T⇐). -/
theorem r4ExFor_of (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F) : R4ExFor C F := by
  intro b c hc
  obtain ⟨e, he0, he1, hgerm⟩ := GaussTube.belowGerm hp hp1 (F' := F) b c hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨closedBall b ‖c * e‖, ⟨b, c * e, mul_ne_zero hc he0, rfl⟩, ?_, ?_⟩
  · intro z hz
    refine BallTree.mem_ball'.2 ((BallTree.mem_closedBall'.1 hz).trans_lt ?_)
    rw [norm_mul]
    exact mul_lt_of_lt_one_right hcpos he1
  · exact edgeGood_of_isExhausting hT hT' hc he1 he0 (hgerm e he1 he0 le_rfl)

end S8A

end SemistableReduction
