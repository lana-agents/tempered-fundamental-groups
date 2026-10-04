/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Interfaces

/-!
# S8.B: the minimal exhausting disc as the limit of the exhausting discs

Blueprint §9.10 (S8.B, [AW §4, Prop. 4.2]), §9.12 O6.1. Let `B = ball b ‖c‖` be a bad residue
ball of a finite extension `F / C(x)` and `𝒟` the set of discs `D ⊆ B` which are exhausting in
`B` (`EdgeGood F D (closedBall b ‖c‖)`, `ExhSet`). [AW]'s limit argument:

* the members of `𝒟` intersect pairwise ([AW Lemma 2.7(iii)], `ExhInterFor`), hence they form a
  chain; their intersection is nonempty unless the limit is of type 4 (`L7For`, [AW §4 case (4)]);
* if `a` is a common point, every `D ∈ 𝒟` is `closedBall a r`. Let `ρ` be the infimum of the radii.
  If it is attained, `closedBall a ρ` is the minimum.
  - `ρ = 0` (**type 1**): small balls around the classical point `a` are good
    (`ClassicalGoodFor`, S8.2), and goodness glues along an exhausting disc (`GoodGluingFor`, O11g),
    so `B` would be good;
  - `ρ ∈ |C^×|` (**type 2**): the outward germ of annuli at `w_{a,ρ}` (`TypeTwoGermFor`, the dual of
    R4(ii)) and gluing of exhaustion (`O11For`, O11) make `closedBall a ρ` exhausting;
  - `ρ ∉ |C^×|` (**type 3**): the germ of annuli at the type-3 point `w_{a,ρ}` (`TypeThreeGermFor`,
    S8.4) and O11 give an exhausting disc of radius `< ρ`.

The inputs are **open interfaces** (Blueprint §9.12), recorded as definitions and taken as explicit
hypotheses of `s8bMinFor_of_inputs`. `O11For` is the (⇐) direction of the O11 owner's statement
`ExhaustGluing.isExhausting_iff_of_le` verbatim. `L7For` is the S8.5 owner's form.
-/

open Metric

namespace SemistableReduction

namespace S8A

open GaussTube AffineTwist BallTree

section Field

variable (C : Type*) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- The discs `D ⊆ ball b ‖c‖` which are exhausting in `ball b ‖c‖`. -/
def ExhSet (b c : C) : Set (Set C) :=
  {D | IsDisc D ∧ D ⊆ ball b ‖c‖ ∧ EdgeGood F D (closedBall b ‖c‖)}

/-- **R4(ii)** in its weakest form: every residue ball contains an exhausting disc. -/
def R4ExFor : Prop :=
  ∀ b c : C, c ≠ 0 → (ExhSet C F b c).Nonempty

/-- **[AW Lemma 2.7(iii)]**: two exhausting discs of a bad residue ball intersect. -/
def ExhInterFor : Prop :=
  ∀ b c : C, c ≠ 0 → ¬ BallGood F (ball b ‖c‖) →
    ∀ D ∈ ExhSet C F b c, ∀ D' ∈ ExhSet C F b c, (D ∩ D').Nonempty

/-- **L7** ([AW §4 case (4)], owner S8.5 agent): pairwise intersecting exhausting discs of a bad
residue ball have a common point (the limit is not of type 4). -/
def L7For : Prop :=
  ∀ (b c : C) (_hc : c ≠ 0), ¬ BallGood F (ball b ‖c‖) →
    (∀ D ∈ ExhSet C F b c, ∀ D' ∈ ExhSet C F b c, (D ∩ D').Nonempty) →
      ¬ (⋂₀ ExhSet C F b c = ∅)

/-- **O11** (gluing of exhaustion, owner M10/O9 agent; the (⇐) direction of
`ExhaustGluing.isExhausting_iff_of_le`): for `U = {|x - a| < |c|}`, `U' = {|x - a| < |cu|}` and
discs `D(a, |cc'|) ⊆ D(a, |ce|) ⊆ U'`, if `D(a, |ce|)` is exhausting in `U` and `D(a, |cc'|)` is
exhausting in `U'`, then `D(a, |cc'|)` is exhausting in `U`. -/
def O11For : Prop :=
  ∀ {a c u e c' : C} (hc0 : c ≠ 0) (hu0 : u ≠ 0) (hu : ‖u‖ < 1) (he0 : e ≠ 0) (heu : ‖e‖ < ‖u‖)
    (hc'0 : c' ≠ 0) (hc'e : ‖c'‖ ≤ ‖e‖) (hcu : ‖c' / u‖ < 1) (hcu0 : c' / u ≠ 0),
    IsExhausting a hc0 (heu.trans hu) he0 F →
    IsExhausting a (mul_ne_zero hc0 hu0) hcu hcu0 F →
    IsExhausting a hc0 (hc'e.trans_lt (heu.trans hu)) hc'0 F

/-- **O11g** (gluing of goodness, owner M10/O9 agent): if `closedBall a ‖e‖ ⊆ ball a ‖u‖ ⊆ B` and
`closedBall a ‖e‖` is exhausting in `B`, then goodness of `ball a ‖u‖` implies goodness of `B`. -/
def GoodGluingFor : Prop :=
  ∀ b c a u e : C, c ≠ 0 → u ≠ 0 → e ≠ 0 → ‖e‖ < ‖u‖ → closedBall a ‖u‖ ⊆ ball b ‖c‖ →
    EdgeGood F (closedBall a ‖e‖) (closedBall b ‖c‖) → BallGood F (ball a ‖u‖) →
      BallGood F (ball b ‖c‖)

/-- **S8.2** (type 1): small residue balls around a classical point are good. -/
def ClassicalGoodFor : Prop :=
  ∀ a : C, ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ c : C, c ≠ 0 → ‖c‖ ≤ s₀ → BallGood F (ball a ‖c‖)

/-- **Dual of R4(ii)** (type 2): the outward germ of annuli at a type-2 point `w_{a,|z|}`. -/
def TypeTwoGermFor : Prop :=
  ∀ a z : C, z ≠ 0 → ∃ ρ' > ‖z‖, ∀ c₂ : C, ‖z‖ < ‖c₂‖ → ‖c₂‖ ≤ ρ' →
    EdgeGood F (closedBall a ‖z‖) (closedBall a ‖c₂‖)

/-- **S8.4** (type 3): the germ of annuli at a type-3 point `w_{a,ρ}`, `ρ ∉ |C^×|`. -/
def TypeThreeGermFor : Prop :=
  ∀ (a : C) (ρ : ℝ), 0 < ρ → (∀ z : C, ‖z‖ ≠ ρ) → ∃ c₁ : C, c₁ ≠ 0 ∧ ‖c₁‖ < ρ ∧
    ∃ ρ₂ > ρ, ∀ c₂ : C, ρ < ‖c₂‖ → ‖c₂‖ ≤ ρ₂ →
      EdgeGood F (closedBall a ‖c₁‖) (closedBall a ‖c₂‖)

/-- The open inputs of S8.B for `F` (Blueprint §9.12 O6.1). -/
structure S8BLimitInputs : Prop where
  r4ex : R4ExFor C F
  inter : ExhInterFor C F
  l7 : L7For C F
  o11 : O11For C F
  goodGluing : GoodGluingFor C F
  classical : ClassicalGoodFor C F
  typeTwo : TypeTwoGermFor C F
  typeThree : TypeThreeGermFor C F

end Field

section Proofs

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

omit [IsAlgClosed C] in
lemma closedBall_eq_of_norm_sub_le {a a' : C} {r : ℝ} (h : ‖a - a'‖ ≤ r) :
    closedBall a r = closedBall a' r :=
  IsUltrametricDist.closedBall_eq_of_mem (mem_closedBall'.2 (by rwa [norm_sub_rev]))

omit [IsAlgClosed C] in
/-- A disc containing `a` is centred at `a`. -/
lemma IsDisc.eq_closedBall_of_mem {D : Set C} (hD : IsDisc D) {a : C} (ha : a ∈ D) :
    ∃ d : C, d ≠ 0 ∧ D = closedBall a ‖d‖ := by
  obtain ⟨a', d, hd, rfl⟩ := hD
  exact ⟨d, hd, IsUltrametricDist.closedBall_eq_of_mem ha⟩

omit [IsAlgClosed C] in
lemma norm_le_of_closedBall_subset {a : C} {d d' : C}
    (h : closedBall a ‖d‖ ⊆ closedBall a ‖d'‖) : ‖d‖ ≤ ‖d'‖ :=
  ((closedBall_subset_closedBall_iff').1 h).1

/-- **Gluing of exhaustion in `EdgeGood` form** (from O11): for `‖c₁‖ ≤ ‖d₁‖ < ‖d₂‖ < ‖c‖`, if
`closedBall a ‖d₁‖` is exhausting in `ball a ‖c‖` and `closedBall a ‖c₁‖` is exhausting in
`ball a ‖d₂‖`, then `closedBall a ‖c₁‖` is exhausting in `ball a ‖c‖`. -/
theorem edgeGood_glue (ho11 : O11For C F) {a c d₁ d₂ c₁ : C} (hc : c ≠ 0) (hd₁ : d₁ ≠ 0)
    (hd₂ : d₂ ≠ 0) (h₁₂ : ‖d₁‖ < ‖d₂‖) (h₂c : ‖d₂‖ < ‖c‖) (h₁ : ‖c₁‖ ≤ ‖d₁‖)
    (hE : EdgeGood F (closedBall a ‖d₁‖) (closedBall a ‖c‖))
    (hD : EdgeGood F (closedBall a ‖c₁‖) (closedBall a ‖d₂‖)) :
    EdgeGood F (closedBall a ‖c₁‖) (closedBall a ‖c‖) := by
  intro a₀ c₀ c₀' hc₀ hc₀' hc0₀' hD0 hG0
  have hc0pos : 0 < ‖c₀‖ := norm_pos_iff.2 hc₀
  obtain ⟨hcc, hac⟩ := (closedBall_eq_closedBall_iff' hc hc₀).1 hG0
  have hc₁0 : c₁ ≠ 0 := by
    rintro rfl
    have h := (closedBall_subset_closedBall_iff').1 hD0.ge
    rw [norm_zero, norm_mul] at h
    exact (mul_pos hc0pos (norm_pos_iff.2 hc0₀')).not_ge h.1
  obtain ⟨h1c, ha1⟩ := (closedBall_eq_closedBall_iff' hc₁0 (mul_ne_zero hc₀ hc0₀')).1 hD0
  set u := d₂ / c₀ with hu_def
  set e := d₁ / c₀ with he_def
  have hu0 : u ≠ 0 := div_ne_zero hd₂ hc₀
  have he0 : e ≠ 0 := div_ne_zero hd₁ hc₀
  have hnu : ‖u‖ = ‖d₂‖ / ‖c₀‖ := norm_div _ _
  have hne : ‖e‖ = ‖d₁‖ / ‖c₀‖ := norm_div _ _
  have hu : ‖u‖ < 1 := by rw [hnu, div_lt_one hc0pos, ← hcc]; exact h₂c
  have heu : ‖e‖ < ‖u‖ := by rw [hnu, hne]; exact div_lt_div_of_pos_right h₁₂ hc0pos
  have hc'e : ‖c₀'‖ ≤ ‖e‖ := by
    rw [hne, le_div_iff₀ hc0pos, mul_comm, ← norm_mul, ← h1c]; exact h₁
  have hcu : ‖c₀' / u‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.2 hu0)]; exact hc'e.trans_lt heu
  have hcu0 : c₀' / u ≠ 0 := div_ne_zero hc0₀' hu0
  have hce : c₀ * e = d₁ := by rw [he_def]; field_simp
  have hcuu : c₀ * u = d₂ := by rw [hu_def]; field_simp
  have hbig : IsExhausting a₀ hc₀ (heu.trans hu) he0 F := by
    refine hE a₀ c₀ e hc₀ (heu.trans hu) he0 ?_ hG0
    rw [hce]
    exact closedBall_eq_of_norm_sub_le (ha1.trans h₁)
  have hsmall : IsExhausting a₀ (mul_ne_zero hc₀ hu0) hcu hcu0 F := by
    refine hD a₀ (c₀ * u) (c₀' / u) (mul_ne_zero hc₀ hu0) hcu hcu0 ?_ ?_
    · rw [hD0]
      congr 2
      field_simp
    · rw [hcuu]
      exact closedBall_eq_of_norm_sub_le (ha1.trans (h₁.trans h₁₂.le))
  exact ho11 hc₀ hu0 hu he0 heu hc0₀' hc'e hcu hcu0 hbig hsmall

/-- **S8.B** ([AW Thm 2.6], Blueprint §9.12 O6.1) from the open inputs: a bad residue ball contains
a smallest exhausting disc. -/
theorem s8bMinFor_of_inputs (H : S8BLimitInputs C F) : S8BMinFor C F := by
  intro b c hc hbad
  set 𝒟 := ExhSet C F b c with h𝒟
  have hpair := H.inter b c hc hbad
  obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.2 (H.l7 b c hc hbad hpair)
  rw [Set.mem_sInter] at ha
  obtain ⟨D₀, hD₀⟩ := H.r4ex b c hc
  have hab : a ∈ ball b ‖c‖ := hD₀.2.1 (ha D₀ hD₀)
  have hballeq : ball b ‖c‖ = ball a ‖c‖ := IsUltrametricDist.ball_eq_of_mem hab
  have hcballeq : closedBall b ‖c‖ = closedBall a ‖c‖ :=
    IsUltrametricDist.closedBall_eq_of_mem (ball_subset_closedBall hab)
  -- the radii of the exhausting discs (all centred at `a`)
  set R : Set ℝ := {r | ∃ d : C, d ≠ 0 ∧ ‖d‖ = r ∧ closedBall a ‖d‖ ∈ 𝒟} with hR
  have hmemR : ∀ D ∈ 𝒟, ∃ d : C, d ≠ 0 ∧ D = closedBall a ‖d‖ ∧ ‖d‖ ∈ R := by
    intro D hD
    obtain ⟨d, hd, rfl⟩ := IsDisc.eq_closedBall_of_mem hD.1 (ha D hD)
    exact ⟨d, hd, rfl, d, hd, rfl, hD⟩
  have hRne : R.Nonempty := by
    obtain ⟨d, -, -, hd⟩ := hmemR D₀ hD₀
    exact ⟨_, hd⟩
  have hRbdd : BddBelow R := ⟨0, by rintro _ ⟨d, -, rfl, -⟩; exact norm_nonneg _⟩
  set ρ := sInf R with hρ
  have hρle : ∀ r ∈ R, ρ ≤ r := fun r hr ↦ csInf_le hRbdd hr
  have hρ0 : 0 ≤ ρ := le_csInf hRne (by rintro _ ⟨d, -, rfl, -⟩; exact norm_nonneg _)
  -- radii of exhausting discs are `< ‖c‖`
  have hRc : ∀ d : C, closedBall a ‖d‖ ∈ 𝒟 → ‖d‖ < ‖c‖ := fun d hd ↦
    ((closedBall_subset_ball_iff').1 (hd.2.1.trans hballeq.le)).1
  by_cases hρR : ρ ∈ R
  · -- the infimum is attained: minimum
    obtain ⟨d, hd, hdρ, hdD⟩ := hρR
    refine ⟨closedBall a ‖d‖, hdD.1, hdD.2.1, hdD.2.2, fun D' hD' hD'B hD'E ↦ ?_⟩
    obtain ⟨d', hd', rfl, hd'R⟩ := hmemR D' ⟨hD', hD'B, hD'E⟩
    exact closedBall_subset_closedBall (hdρ ▸ hρle _ hd'R)
  exfalso
  -- two exhausting discs of radii in `(ρ, t)`
  have htwo : ∀ t, ρ < t → ∃ d₁ d₂ : C, d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ ρ < ‖d₁‖ ∧ ‖d₁‖ < ‖d₂‖ ∧ ‖d₂‖ < t ∧
      closedBall a ‖d₁‖ ∈ 𝒟 ∧ closedBall a ‖d₂‖ ∈ 𝒟 := by
    intro t ht
    obtain ⟨_, ⟨d₂, hd₂, rfl, hd₂D⟩, h₂t⟩ := exists_lt_of_csInf_lt hRne ht
    have hρ₂ : ρ < ‖d₂‖ := lt_of_le_of_ne (hρle _ ⟨d₂, hd₂, rfl, hd₂D⟩)
      (fun h ↦ hρR (h ▸ ⟨d₂, hd₂, rfl, hd₂D⟩))
    obtain ⟨_, ⟨d₁, hd₁, rfl, hd₁D⟩, h₁₂⟩ := exists_lt_of_csInf_lt hRne hρ₂
    have hρ₁ : ρ < ‖d₁‖ := lt_of_le_of_ne (hρle _ ⟨d₁, hd₁, rfl, hd₁D⟩)
      (fun h ↦ hρR (h ▸ ⟨d₁, hd₁, rfl, hd₁D⟩))
    exact ⟨d₁, d₂, hd₁, hd₂, hρ₁, h₁₂, h₂t, hd₁D, hd₂D⟩
  -- a germ of annuli below `ρ` contradicts the minimality of `ρ`
  have hgerm : ∀ c₁ : C, c₁ ≠ 0 → ‖c₁‖ ≤ ρ → ∀ ρ₂ > ρ, (∀ c₂ : C, ρ < ‖c₂‖ → ‖c₂‖ ≤ ρ₂ →
      EdgeGood F (closedBall a ‖c₁‖) (closedBall a ‖c₂‖)) → False := by
    intro c₁ hc₁ hc₁ρ ρ₂ hρ₂ hgood
    obtain ⟨d₁, d₂, hd₁, hd₂, hρ₁, h₁₂, h₂t, hd₁D, hd₂D⟩ := htwo ρ₂ hρ₂
    have hE : EdgeGood F (closedBall a ‖d₁‖) (closedBall a ‖c‖) := hcballeq ▸ hd₁D.2.2
    have hglue := edgeGood_glue H.o11 hc hd₁ hd₂ h₁₂ (hRc d₂ hd₂D) (hc₁ρ.trans hρ₁.le) hE
      (hgood d₂ (hρ₁.trans h₁₂) h₂t.le)
    have hmem : closedBall a ‖c₁‖ ∈ 𝒟 :=
      ⟨⟨a, c₁, hc₁, rfl⟩, (closedBall_subset_closedBall (hc₁ρ.trans hρ₁.le)).trans hd₁D.2.1,
        hcballeq ▸ hglue⟩
    exact hρR (le_antisymm hc₁ρ (hρle _ ⟨c₁, hc₁, rfl, hmem⟩) ▸ ⟨c₁, hc₁, rfl, hmem⟩)
  rcases hρ0.eq_or_lt with hρ0 | hρpos
  · -- type 1
    obtain ⟨s₀, hs₀, hgood⟩ := H.classical a
    obtain ⟨d₁, d₂, hd₁, hd₂, -, h₁₂, h₂t, hd₁D, hd₂D⟩ := htwo s₀ (hρ0 ▸ hs₀)
    refine hbad (H.goodGluing b c a d₂ d₁ hc hd₂ hd₁ h₁₂ hd₂D.2.1 hd₁D.2.2 (hgood d₂ hd₂ h₂t.le))
  by_cases hval : ∃ z : C, ‖z‖ = ρ
  · -- type 2
    obtain ⟨z, hz⟩ := hval
    have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz; exact hρpos.ne hz
    obtain ⟨ρ', hρ', hgood⟩ := H.typeTwo a z hz0
    exact hgerm z hz0 hz.le ρ' (hz ▸ hρ') fun c₂ h₁ h₂ ↦ hgood c₂ (hz ▸ h₁) h₂
  · -- type 3
    push Not at hval
    obtain ⟨c₁, hc₁, hc₁ρ, ρ₂, hρ₂, hgood⟩ := H.typeThree a ρ hρpos hval
    exact hgerm c₁ hc₁ hc₁ρ.le ρ₂ hρ₂ hgood

end Proofs

end S8A

end SemistableReduction
