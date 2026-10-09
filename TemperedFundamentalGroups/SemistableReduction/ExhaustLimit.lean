/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhaustInterfaces
import TemperedFundamentalGroups.SemistableReduction.TypeFourLimit
import TemperedFundamentalGroups.SemistableReduction.TypeFourGood
import TemperedFundamentalGroups.SemistableReduction.TypeOneGerm
import TemperedFundamentalGroups.SemistableReduction.TypeTwoGerm
import TemperedFundamentalGroups.SemistableReduction.KummerUnram
import TemperedFundamentalGroups.SemistableReduction.S8DescentA6
import TemperedFundamentalGroups.SemistableReduction.TypeThreeGermTwo
import TemperedFundamentalGroups.SemistableReduction.TypeFourUnif

/-!
# (D⇐) and (T⇐) from the two `δ`-count steps (O12)

Blueprint §9.12, O12. **`ExhaustGluing.smoothOfDiscCond_of`**: an open disc satisfying the
valuative disc condition is good, from the `δ`-count step `ExhaustDescentFor` (R5), the type-3 germ
and goodness near type-4 points. Proof by a limit argument: a bad disc `B₀` contains bad sub-discs
of smaller radius (R4(ii) `GaussTube.belowGerm` and descent). Choose nested bad discs
`B_{n+1} ⊆ B_n` whose radius is less than `1/(n+1)` above the infimum of the radii of the bad
sub-discs of `B_n`, and let `ρ` be the limit of the radii.

* `⋂ B_n = ∅`: some `B_n` is good (`S8A.TypeFourGoodFor`);
* `b ∈ ⋂ B_n`, `ρ = 0`: small discs around `b` are good (`S8A.ClassicalGoodFor`, proved);
* `ρ = |z| > 0`: the type-2 germ (`S8A.typeTwoGermFor`) makes `D(b, ρ)` exhausting in some `B_n`;
  descent and R4(ii) give a bad disc of radius `< ρ` inside all `B_n`;
* `ρ ∉ |C^×|`: the type-3 germ gives an exhausting disc of radius `< ρ` in some `B_n`, and descent a
  bad disc of radius `< ρ` inside all `B_n`.

In the last two cases the infimum property of the sequence forces `ρ ≤` that radius `< ρ`.

**`ExhaustGluing.exhaustingOfTube_of`**: (T⇐) from the gluing step `ExhaustGlueFor` (R5), (D⇐)
and the two-sided type-3 germ `S8A.TypeThreeGermTwoFor` (an infimum argument over the radii below
which all discs are exhausting; the one-sided germ does not suffice for this argument).
`smoothOfDiscCond_and_exhaustingOfTube` combines the two.

* `ExhaustGluing.isTubeDisc_of_discCond`, `discCond_mono`: the disc condition for sub-discs.
-/

open Metric

namespace SemistableReduction

namespace ExhaustGluing

open AffineTwist

universe u v

section Cond

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type v} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- Under the disc condition for `|x - a| < |c|`, every Gauss point `w_{x,|γ|}` with `|x - a| < |c|`
and `|γ| < |c|` is a disc of a tube. -/
theorem isTubeDisc_of_discCond {a c : C} {hc : c ≠ 0} (h : DiscCond F a hc) {x γ : C}
    (hγ : γ ≠ 0) (hx : ‖x - a‖ < ‖c‖) (hγc : ‖γ‖ < ‖c‖) : IsTubeDisc F x hγ := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hγ'0 : γ / c ≠ 0 := div_ne_zero hγ hc
  have hβ1 : ‖(x - a) / c‖ < 1 := by rw [norm_div, div_lt_one hcpos]; exact hx
  have hγ'1 : ‖γ / c‖ < 1 := by rw [norm_div, div_lt_one hcpos]; exact hγc
  have hxβ : a + c * ((x - a) / c) = x := by field_simp; ring
  have hγγ : c * (γ / c) = γ := by field_simp
  rcases lt_or_ge ‖γ / c‖ ‖(x - a) / c‖ with h1 | h1
  · exact (isTubeDisc_congr _ _ hxβ hγγ).1 (h.2 _ _ hγ'0 hβ1 h1)
  · refine isTubeDisc_of_norm_sub_le hγ ?_
      ((isTubeDisc_congr _ _ rfl hγγ).1 (h.1 _ hγ'0 hγ'1))
    rw [show a - x = -(c * ((x - a) / c)) by rw [mul_div_cancel₀ _ hc]; ring, norm_neg, norm_mul,
      ← hγγ, norm_mul]
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

/-- The disc condition from tube discs at all Gauss points of the open disc. -/
theorem discCond_of_isTubeDisc {b d : C} (hd : d ≠ 0)
    (H : ∀ (x γ : C) (hγ : γ ≠ 0), ‖x - b‖ < ‖d‖ → ‖γ‖ < ‖d‖ → IsTubeDisc F x hγ) :
    DiscCond F b hd := by
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hd
  refine ⟨fun γ hγ hγ1 ↦ H _ _ _ (by simpa using hdpos) ?_, fun β γ hγ hβ hγβ ↦ H _ _ _ ?_ ?_⟩
  · rw [norm_mul]; exact mul_lt_of_lt_one_right hdpos hγ1
  · rw [add_sub_cancel_left, norm_mul]; exact mul_lt_of_lt_one_right hdpos hβ
  · rw [norm_mul]; exact mul_lt_of_lt_one_right hdpos (hγβ.trans hβ)

/-- **Restriction of the disc condition** to a sub-disc `|x - b| < |d|` of `|x - a| < |c|`. -/
theorem discCond_mono {a c b d : C} {hc : c ≠ 0} (h : DiscCond F a hc) (hd : d ≠ 0)
    (hb : ‖b - a‖ < ‖c‖) (hdc : ‖d‖ ≤ ‖c‖) : DiscCond F b hd := by
  refine discCond_of_isTubeDisc hd fun x γ hγ hx hγd ↦ isTubeDisc_of_discCond h hγ ?_
    (hγd.trans_le hdc)
  rw [show x - a = (x - b) + (b - a) by ring]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hx.trans_le hdc) hb)

/-- **One step of descent**: if `D(b, |d c'|)` is exhausting in the bad disc `|x - b| < |d|`
satisfying the disc condition, some residue class of `D(b, |d c'|)` is bad. -/
theorem exists_bad_of_exhausting (hED : ExhaustDescentFor C F) {b d c' : C} (hd : d ≠ 0)
    (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0) (hE : IsExhausting b hd hc' hc0' F)
    (hcond : DiscCond F b hd) (hbad : ¬ DiscSmooth F b hd) :
    ∃ b' : C, ‖b' - b‖ ≤ ‖d * c'‖ ∧ ¬ DiscSmooth F b' (mul_ne_zero hd hc0') := by
  obtain ⟨β, hβ, h⟩ := hED b d c' hd hc' hc0' hE (hcond.1 c' hc0' hc') hbad
  refine ⟨_, ?_, h⟩
  rw [add_sub_cancel_left, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hβ

end Cond

section Limit

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type v} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- **A bad disc has a bad sub-disc of smaller radius** (R4(ii) and descent). -/
theorem exists_bad_lt (hED : ExhaustDescentFor C F) {b d : C} (hd : d ≠ 0)
    (hcond : DiscCond F b hd) (hbad : ¬ DiscSmooth F b hd) :
    ∃ (b' d' : C) (hd' : d' ≠ 0), ‖b' - b‖ < ‖d‖ ∧ ‖d'‖ < ‖d‖ ∧ ¬ DiscSmooth F b' hd' := by
  obtain ⟨e, he0, he1, hE⟩ := GaussTube.belowGerm hp hp1 (F' := F) b d hd
  obtain ⟨b', hb', h⟩ := exists_bad_of_exhausting hED hd he1 he0 (hE e he1 he0 le_rfl) hcond hbad
  have hlt : ‖d * e‖ < ‖d‖ := by
    rw [norm_mul]; exact mul_lt_of_lt_one_right (norm_pos_iff.2 hd) he1
  exact ⟨b', d * e, mul_ne_zero hd he0, hb'.trans_lt hlt, hlt, h⟩

include hp hp1 in
/-- **(D⇐)** `SmoothOfDiscCond` (Blueprint §9.12 O12), from the descent of singularities into an
exhausting disc of a tube (`ExhaustDescentFor`, R5), the type-3 germ and goodness near type-4
points. -/
theorem smoothOfDiscCond_of (hED : ExhaustDescentFor C F) (h3 : S8A.TypeThreeGermFor C F)
    (h4 : S8A.TypeFourGoodFor C F) : SmoothOfDiscCond C F := by
  intro a c hc hcond
  by_contra hbad0
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  -- bad discs inside `|x - a| < |c|`, and the inclusion of discs
  let Bad : C × C → Prop := fun q ↦
    ‖q.1 - a‖ < ‖c‖ ∧ ‖q.2‖ ≤ ‖c‖ ∧ ∃ h : q.2 ≠ 0, ¬ DiscSmooth F q.1 h
  let Sub : C × C → C × C → Prop := fun q q' ↦ ‖q.1 - q'.1‖ < ‖q'.2‖ ∧ ‖q.2‖ ≤ ‖q'.2‖
  have ultra : ∀ x y z : C, ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖ := fun x y z ↦ by
    rw [show x - z = (x - y) + (y - z) by ring]; exact IsUltrametricDist.norm_add_le_max _ _
  have bad_of_sub : ∀ q q', Bad q' → Sub q q' → ∀ h : q.2 ≠ 0, ¬ DiscSmooth F q.1 h → Bad q :=
    fun q q' hq' hs h hq ↦ ⟨(ultra _ q'.1 _).trans_lt (max_lt (hs.1.trans_le hq'.2.1) hq'.1),
      hs.2.trans hq'.2.1, h, hq⟩
  have cond : ∀ q, Bad q → ∀ h : q.2 ≠ 0, DiscCond F q.1 h :=
    fun q hq h ↦ discCond_mono hcond h hq.1 hq.2.1
  -- the infimum of the radii of the bad sub-discs
  let rad : C × C → ℝ := fun q ↦ sInf ((fun q' : C × C ↦ ‖q'.2‖) '' {q' | Bad q' ∧ Sub q' q})
  have hbdd : ∀ q, BddBelow ((fun q' : C × C ↦ ‖q'.2‖) '' {q' | Bad q' ∧ Sub q' q}) :=
    fun q ↦ ⟨0, by rintro _ ⟨q', -, rfl⟩; exact norm_nonneg _⟩
  have rad_le : ∀ q q', Bad q' → Sub q' q → rad q ≤ ‖q'.2‖ :=
    fun q q' h hs ↦ csInf_le (hbdd q) ⟨q', ⟨h, hs⟩, rfl⟩
  -- one step of the construction
  have hstep : ∀ q : C × C, Bad q → ∀ n : ℕ, ∃ q', Bad q' ∧ Sub q' q ∧ ‖q'.2‖ < ‖q.2‖ ∧
      ‖q'.2‖ < rad q + 1 / (n + 1) := by
    intro q hq n
    obtain ⟨hq0, hqs⟩ := hq.2.2
    obtain ⟨b', d', hd', hb', hd'q, h⟩ := exists_bad_lt hp hp1 hED hq0 (cond q hq hq0) hqs
    have hs₀ : Sub (b', d') q := ⟨hb', hd'q.le⟩
    have hbad₀ := bad_of_sub (b', d') q hq hs₀ hd' h
    have hlt : rad q < min ‖q.2‖ (rad q + 1 / (n + 1)) :=
      lt_min ((rad_le q _ hbad₀ hs₀).trans_lt hd'q) (lt_add_of_pos_right _ (by positivity))
    obtain ⟨_, ⟨q', ⟨hq', hs⟩, rfl⟩, hlt'⟩ :=
      exists_lt_of_csInf_lt (show ((fun q' : C × C ↦ ‖q'.2‖) '' {q' | Bad q' ∧ Sub q' q}).Nonempty
        from ⟨_, (b', d'), ⟨hbad₀, hs₀⟩, rfl⟩) hlt
    exact ⟨q', hq', hs, hlt'.trans_le (min_le_left _ _), hlt'.trans_le (min_le_right _ _)⟩
  choose! f hf using hstep
  let s : ℕ → C × C := fun n ↦ Nat.rec (a, c) (fun n q ↦ f q n) n
  have hs0 : s 0 = (a, c) := rfl
  have hsucc : ∀ n, s (n + 1) = f (s n) n := fun _ ↦ rfl
  have hbad : ∀ n, Bad (s n) := by
    intro n
    induction n with
    | zero => exact ⟨show ‖a - a‖ < ‖c‖ by simpa using hcpos, le_rfl, hc, hbad0⟩
    | succ n ih => rw [hsucc]; exact (hf _ ih n).1
  have hfs : ∀ n, Sub (s (n + 1)) (s n) ∧ ‖(s (n + 1)).2‖ < ‖(s n).2‖ ∧
      ‖(s (n + 1)).2‖ < rad (s n) + 1 / (n + 1) := fun n ↦ by
    rw [hsucc]; exact (hf _ (hbad n) n).2
  have hd : ∀ n, (s n).2 ≠ 0 := fun n ↦ (hbad n).2.2.1
  have hns : ∀ n, ¬ DiscSmooth F (s n).1 (hd n) := fun n ↦ (hbad n).2.2.2
  -- the radii and their limit
  have hanti : StrictAnti fun n ↦ ‖(s n).2‖ := strictAnti_nat_of_succ_lt fun n ↦ (hfs n).2.1
  have hbddr : BddBelow (Set.range fun n ↦ ‖(s n).2‖) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact norm_nonneg _⟩
  set ρ : ℝ := ⨅ n, ‖(s n).2‖ with hρdef
  have hρle : ∀ n, ρ ≤ ‖(s n).2‖ := fun n ↦ ciInf_le hbddr n
  have hρlt : ∀ n, ρ < ‖(s n).2‖ := fun n ↦
    (hρle (n + 1)).trans_lt (hanti (Nat.lt_succ_self n))
  have hρ0 : 0 ≤ ρ := le_ciInf fun n ↦ norm_nonneg _
  -- the nested balls
  have hsub : ∀ n, ball (s (n + 1)).1 ‖(s (n + 1)).2‖ ⊆ ball (s n).1 ‖(s n).2‖ := by
    intro n x hx
    rw [mem_ball, dist_eq_norm] at hx ⊢
    exact (ultra _ (s (n + 1)).1 _).trans_lt
      (max_lt (hx.trans_le (hfs n).1.2) (hfs n).1.1)
  -- the infimum property: a bad disc inside all `B_n` has radius `≥ ρ`
  have key : ∀ q, Bad q → (∀ n, Sub q (s n)) → ρ ≤ ‖q.2‖ := by
    intro q hq hqs
    refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    calc ρ ≤ ‖(s (n + 1)).2‖ := hρle (n + 1)
      _ < rad (s n) + 1 / (n + 1) := (hfs n).2.2
      _ ≤ ‖q.2‖ + ε := add_le_add (rad_le _ _ hq (hqs n)) hn.le
  -- a disc of radius `< ρ` close to a common point is inside all `B_n`
  have sub_all : ∀ (b : C), (∀ n, ‖b - (s n).1‖ < ‖(s n).2‖) → ∀ q : C × C,
      ‖q.1 - b‖ ≤ ρ → ‖q.2‖ < ρ → ∀ n, Sub q (s n) := fun b hb q h1 h2 n ↦
    ⟨(ultra _ b _).trans_lt (max_lt (h1.trans_lt (hρlt n)) (hb n)), (h2.trans (hρlt n)).le⟩
  -- type 4
  by_cases hempty : (⋂ n, ball (s n).1 ‖(s n).2‖) = ∅
  · obtain ⟨n, hn⟩ := h4 (fun n ↦ (s n).1) (fun n ↦ (s n).2) hd hsub hempty
    exact hns n hn
  obtain ⟨b, hb⟩ := Set.nonempty_iff_ne_empty.2 hempty
  have hb' : ∀ n, ‖b - (s n).1‖ < ‖(s n).2‖ := fun n ↦ by
    have := Set.mem_iInter.1 hb n
    rwa [mem_ball, dist_eq_norm] at this
  have hballeq : ∀ n, ball b ‖(s n).2‖ = ball (s n).1 ‖(s n).2‖ := fun n ↦
    IsUltrametricDist.ball_eq_of_mem (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hb' n)
  have hnsb : ∀ n, ¬ DiscSmooth F b (hd n) := fun n h ↦
    hns n ((S8A.Transport.discGood_iff_of_ball_eq (hd n) (hd n) (hballeq n)).1 h)
  have hba : ‖b - a‖ < ‖c‖ := by simpa [hs0] using hb' 0
  have hbad_of : ∀ q : C × C, ‖q.1 - b‖ ≤ ρ → ‖q.2‖ < ρ → ∀ h : q.2 ≠ 0,
      ¬ DiscSmooth F q.1 h → False := fun q h1 h2 h hq ↦ by
    have hs := sub_all b hb' q h1 h2
    exact (key q (bad_of_sub q (s 0) (hbad 0) (hs 0) h hq) hs).not_gt h2
  rcases hρ0.eq_or_lt with hρ0 | hρpos
  · -- type 1
    obtain ⟨s₀, hs₀, hgood⟩ := ClassicalSmooth.classicalGoodFor_of hp hp1
      (fun a ↦ ClassicalSmooth.kummerUnramFor F a) (fun L _ _ _ _ _ _ _ _ ↦
        ClassicalSmooth.a6For hp hp1) b
    obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt (show ρ < s₀ by rw [← hρ0]; exact hs₀)
    exact hnsb n ((S8A.Transport.ballGood_iff (hd n)).1 (hgood _ (hd n) hn.le))
  by_cases hnorm : ∃ z : C, ‖z‖ = ρ
  · -- type 2
    obtain ⟨z, hz⟩ := hnorm
    have hz0 : z ≠ 0 := norm_pos_iff.1 (hz ▸ hρpos)
    obtain ⟨ρ', hρ', H⟩ := S8A.typeTwoGermFor hp hp1 (F := F) b z hz0
    obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt (show ρ < ρ' by rw [← hz]; exact hρ')
    have hdn : 0 < ‖(s n).2‖ := norm_pos_iff.2 (hd n)
    have hc' : ‖z / (s n).2‖ < 1 := by
      rw [norm_div, div_lt_one hdn, hz]; exact hρlt n
    have hc0' : z / (s n).2 ≠ 0 := div_ne_zero hz0 (hd n)
    have hzz : (s n).2 * (z / (s n).2) = z := mul_div_cancel₀ _ (hd n)
    have hE := H (s n).2 (z / (s n).2) (hd n) hc' hc0' (by rw [hzz]) hn.le
    have hcondb : DiscCond F b (hd n) := discCond_mono hcond (hd n) hba (hbad n).2.1
    obtain ⟨b', hb'b, hb'bad⟩ := exists_bad_of_exhausting hED (hd n) hc' hc0' hE hcondb (hnsb n)
    rw [hzz, hz] at hb'b
    set d' := (s n).2 * (z / (s n).2)
    have hd'0 : d' ≠ 0 := mul_ne_zero (hd n) hc0'
    have hd'n : ‖d'‖ = ρ := by rw [hzz, hz]
    have hcond' : DiscCond F b' hd'0 := discCond_mono hcond hd'0
      ((ultra _ b _).trans_lt (max_lt (hb'b.trans_lt (hρlt 0)) hba)) (hd'n ▸ (hρlt 0).le)
    obtain ⟨b'', d'', hd'', hb'', hd''lt, h''⟩ := exists_bad_lt hp hp1 hED hd'0 hcond' hb'bad
    rw [hd'n] at hb'' hd''lt
    exact hbad_of (b'', d'') ((ultra _ b' _).trans (max_le hb''.le hb'b)) hd''lt hd'' h''
  · -- type 3
    push Not at hnorm
    obtain ⟨c₁, hc₁0, hc₁ρ, ρ₂, hρ₂, H⟩ := h3 b ρ hρpos hnorm
    obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt hρ₂
    have hdn : 0 < ‖(s n).2‖ := norm_pos_iff.2 (hd n)
    have hc' : ‖c₁ / (s n).2‖ < 1 := by
      rw [norm_div, div_lt_one hdn]; exact hc₁ρ.trans (hρlt n)
    have hc0' : c₁ / (s n).2 ≠ 0 := div_ne_zero hc₁0 (hd n)
    have hcc : (s n).2 * (c₁ / (s n).2) = c₁ := mul_div_cancel₀ _ (hd n)
    have hE := H (s n).2 (hρlt n) hn.le b (s n).2 (c₁ / (s n).2) (hd n) hc' hc0'
      (by rw [hcc]) rfl
    have hcondb : DiscCond F b (hd n) := discCond_mono hcond (hd n) hba (hbad n).2.1
    obtain ⟨b', hb'b, hb'bad⟩ := exists_bad_of_exhausting hED (hd n) hc' hc0' hE hcondb (hnsb n)
    rw [hcc] at hb'b
    exact hbad_of (b', _) (hb'b.trans hc₁ρ.le) (by simp only; rw [hcc]; exact hc₁ρ) _ hb'bad

include hp hp1 in
/-- **(T⇐)** `ExhaustingOfTube` (Blueprint §9.12 O12), from the gluing of exhaustion through a
circle of a tube (`ExhaustGlueFor`, R5), (D⇐) and the two-sided type-3 germ. Let `ρ` be the
infimum of the radii `r ≥ |c'|` such that `D(a, |c v|)` is exhausting in `|x - a| < |c|` for all
`r ≤ |v| < 1` (R4(ii) starts this set). At a type-2 radius `ρ` the type-2 germ and gluing make
`ρ` a member, and R4(ii) and gluing go below `ρ` unless `ρ = |c'|`; at a type-3 radius the
two-sided type-3 germ and gluing go below `ρ`. The residue classes off the centre of the circles
are good by (D⇐), from the off-skeleton clause of the tube condition. -/
theorem exhaustingOfTube_of (hGl : ExhaustGlueFor C F) (hD : SmoothOfDiscCond C F)
    (h3 : S8A.TypeThreeGermTwoFor C F) : ExhaustingOfTube C F := by
  intro a c c' hc hc' hc0' hT
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  have hc'pos : 0 < ‖c'‖ := norm_pos_iff.2 hc0'
  have ultra : ∀ x y z : C, ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖ := fun x y z ↦ by
    rw [show x - z = (x - y) + (y - z) by ring]; exact IsUltrametricDist.norm_add_le_max _ _
  -- the residue classes off the centre of a circle of the annulus are good
  have hoff : ∀ (u : C) (hu0 : u ≠ 0), ‖c'‖ < ‖u‖ → ‖u‖ < 1 → ∀ β : C, ‖β‖ = 1 →
      DiscSmooth F (a + c * u * β) (mul_ne_zero hc hu0) := by
    intro u hu0 hcu hu1 β hβ
    refine hD _ _ _ (discCond_of_isTubeDisc _ fun x γ hγ hx hγd ↦ ?_)
    have hcuβ : ‖c * u * β‖ = ‖c * u‖ := by rw [norm_mul _ β, hβ, mul_one]
    have hge : ‖c * u‖ ≤ ‖x - a‖ := by
      have h := ultra (c * u * β) (x - a) 0
      rw [show c * u * β - (x - a) = -(x - (a + c * u * β)) by ring, norm_neg, sub_zero,
        sub_zero, hcuβ] at h
      rcases le_max_iff.1 h with h' | h'
      · exact absurd h' (not_le.2 hx)
      · exact h'
    have hlt : ‖x - a‖ < ‖c‖ := by
      have h := ultra (x - a) (c * u * β) 0
      rw [show x - a - c * u * β = x - (a + c * u * β) by ring, sub_zero, sub_zero, hcuβ] at h
      refine h.trans_lt (max_lt (hx.trans ?_) ?_) <;>
      · rw [norm_mul]; exact mul_lt_of_lt_one_right hcpos hu1
    have hγ'0 : γ / c ≠ 0 := div_ne_zero hγ hc
    have hβ'u : ‖u‖ ≤ ‖(x - a) / c‖ := by
      rw [norm_div, le_div_iff₀ hcpos, mul_comm, ← norm_mul]; exact hge
    have hγ'u : ‖γ / c‖ < ‖u‖ := by
      rw [norm_div, div_lt_iff₀ hcpos, mul_comm, ← norm_mul]; exact hγd
    have hxβ : a + c * ((x - a) / c) = x := by rw [mul_div_cancel₀ _ hc]; ring
    refine (isTubeDisc_congr _ _ hxβ (mul_div_cancel₀ _ hc)).1
      (hT.2 _ _ hγ'0 (hcu.trans_le hβ'u) ?_ (hγ'u.trans_le hβ'u))
    rw [norm_div, div_lt_one hcpos]; exact hlt
  -- exhaustion in `|x - a| < |c|`
  let Ex : C → Prop := fun v ↦ ∀ (hv : ‖v‖ < 1) (hv0 : v ≠ 0), IsExhausting a hc hv hv0 F
  -- gluing through the circle `w_{a,|c u|}`
  have glue : ∀ (u v : C) (hu0 : u ≠ 0) (hu1 : ‖u‖ < 1), ‖c'‖ < ‖u‖ → Ex u → v ≠ 0 →
      ‖v‖ < ‖u‖ → (∀ (h : ‖v / u‖ < 1) (h0 : v / u ≠ 0),
        IsExhausting a (mul_ne_zero hc hu0) h h0 F) → Ex v := by
    intro u v hu0 hu1 hcu hEu hv0 hvu hE hv hv0'
    have hvu1 : ‖v / u‖ < 1 := by rw [norm_div, div_lt_one (norm_pos_iff.2 hu0)]; exact hvu
    have hvu0 : v / u ≠ 0 := div_ne_zero hv0 hu0
    exact S8A.isExhausting_congr hc (mul_div_cancel₀ v hu0) _ _ hv hv0' F
      (hGl a c u (v / u) hc hu1 hu0 hvu1 hvu0 (hEu hu1 hu0) (hE hvu1 hvu0)
        (hT.1 u hu0 hcu hu1) (hoff u hu0 hcu hu1))
  -- the set of radii from which on all discs are exhausting
  let E : Set ℝ := {r | ‖c'‖ ≤ r ∧ r < 1 ∧ ∀ u : C, r ≤ ‖u‖ → ‖u‖ < 1 → Ex u}
  suffices hmem : ‖c'‖ ∈ E from hmem.2.2 c' le_rfl hc' hc' hc0'
  have hbdd : BddBelow E := ⟨‖c'‖, fun r hr ↦ hr.1⟩
  obtain ⟨e, he0, he1, He⟩ := GaussTube.belowGerm hp hp1 (F' := F) a c hc
  have hne : E.Nonempty := ⟨max ‖e‖ ‖c'‖, le_max_right _ _, max_lt he1 hc',
    fun u hu hu1 hv hv0 ↦ He u hv hv0 ((le_max_left _ _).trans hu)⟩
  set ρ := sInf E with hρdef
  have hρc' : ‖c'‖ ≤ ρ := le_csInf hne fun r hr ↦ hr.1
  have hρpos : 0 < ρ := hc'pos.trans_le hρc'
  have hρ1 : ρ < 1 := by
    obtain ⟨r, hr⟩ := hne
    exact (csInf_le hbdd hr).trans_lt hr.2.1
  have above : ∀ u : C, ρ < ‖u‖ → ‖u‖ < 1 → Ex u := by
    intro u hu hu1
    obtain ⟨r, hr, hru⟩ := exists_lt_of_csInf_lt hne hu
    exact hr.2.2 u hru.le hu1
  have notmem : ∀ r ∈ E, r < ρ → False := fun r hr hrρ ↦ (csInf_le hbdd hr).not_gt hrρ
  by_cases hnorm : ∃ z : C, ‖z‖ = ρ
  · -- type 2
    obtain ⟨z, hz⟩ := hnorm
    have hz0 : z ≠ 0 := norm_pos_iff.1 (hz ▸ hρpos)
    have hcz0 : c * z ≠ 0 := mul_ne_zero hc hz0
    obtain ⟨ρ', hρ', H2⟩ := S8A.typeTwoGermFor hp hp1 (F := F) a (c * z) hcz0
    have hρ'c : ρ < min 1 (ρ' / ‖c‖) := lt_min hρ1 (by
      rw [lt_div_iff₀ hcpos, mul_comm, ← hz, ← norm_mul]; exact hρ')
    obtain ⟨u, hρu, hu⟩ := TypeFour.exists_norm_between (C := C) hρpos hρ'c
    have hu1 : ‖u‖ < 1 := hu.trans_le (min_le_left _ _)
    have hu0 : u ≠ 0 := norm_pos_iff.1 (hρpos.trans hρu)
    have at_rho : ∀ v : C, ‖v‖ = ρ → Ex v := by
      intro v hv
      refine glue u v hu0 hu1 (hρc'.trans_lt hρu) (above u hρu hu1)
        (norm_pos_iff.1 (hv ▸ hρpos)) (hv ▸ hρu) fun h h0 ↦ H2 _ _ _ _ _ ?_ ?_
      · rw [mul_assoc, mul_div_cancel₀ _ hu0, norm_mul, norm_mul, hv, hz]
      · rw [norm_mul, ← le_div_iff₀' hcpos]; exact (hu.trans_le (min_le_right _ _)).le
    have hρE : ρ ∈ E := ⟨hρc', hρ1, fun u hu hu1 ↦
      hu.eq_or_lt.elim (fun h ↦ at_rho u h.symm) (fun h ↦ above u h hu1)⟩
    rcases hρc'.eq_or_lt with h | hlt
    · rwa [h]
    · exfalso
      obtain ⟨e', he'0, he'1, He'⟩ := GaussTube.belowGerm hp hp1 (F' := F) a (c * z) hcz0
      have hz1 : ‖z‖ < 1 := hz ▸ hρ1
      refine notmem (max ‖c'‖ (ρ * ‖e'‖)) ⟨le_max_left _ _, (max_lt hlt
        (mul_lt_of_lt_one_right hρpos he'1)).trans hρ1, fun u hu hu1 ↦ ?_⟩
        (max_lt hlt (mul_lt_of_lt_one_right hρpos he'1))
      rcases le_or_gt ρ ‖u‖ with hρu | hρu
      · exact hρE.2.2 u hρu hu1
      have hu0 : u ≠ 0 := norm_pos_iff.1 (hc'pos.trans_le ((le_max_left _ _).trans hu))
      refine glue z u hz0 hz1 (hz ▸ hlt) (at_rho z hz) hu0 (hz ▸ hρu) fun h h0 ↦ He' _ h h0 ?_
      rw [norm_div, le_div_iff₀ (norm_pos_iff.2 hz0), hz, mul_comm]
      exact (le_max_right _ _).trans hu
  · -- type 3
    push Not at hnorm
    have hlt : ‖c'‖ < ρ := hρc'.lt_of_ne (hnorm c')
    have hnorm' : ∀ w : C, ‖w‖ ≠ ‖c‖ * ρ := fun w hw ↦ hnorm (w / c) (by
      rw [norm_div, hw, mul_div_cancel_left₀ _ hcpos.ne'])
    obtain ⟨r₁, hr₁, ρ₂, hρ₂, H3⟩ := h3 a (‖c‖ * ρ) (mul_pos hcpos hρpos) hnorm'
    have hρ₂c : ρ < min 1 (ρ₂ / ‖c‖) := lt_min hρ1 (by rw [lt_div_iff₀' hcpos]; exact hρ₂)
    obtain ⟨u, hρu, hu⟩ := TypeFour.exists_norm_between (C := C) hρpos hρ₂c
    have hu1 : ‖u‖ < 1 := hu.trans_le (min_le_left _ _)
    have hu0 : u ≠ 0 := norm_pos_iff.1 (hρpos.trans hρu)
    have hr₁ρ : r₁ / ‖c‖ < ρ := by rw [div_lt_iff₀' hcpos]; exact hr₁
    refine absurd (notmem (max ‖c'‖ (r₁ / ‖c‖)) ⟨le_max_left _ _, (max_lt hlt hr₁ρ).trans hρ1,
      fun v hv hv1 ↦ ?_⟩ (max_lt hlt hr₁ρ)) not_false
    rcases lt_or_ge ρ ‖v‖ with hρv | hvρ
    · exact above v hρv hv1
    have hvρ' : ‖v‖ < ρ := hvρ.lt_of_ne (hnorm v)
    have hv0 : v ≠ 0 := norm_pos_iff.1 (hc'pos.trans_le ((le_max_left _ _).trans hv))
    refine glue u v hu0 hu1 (hρc'.trans_lt hρu) (above u hρu hu1) hv0 (hvρ'.trans hρu)
      fun h h0 ↦ H3 (c * v) (c * u) (mul_ne_zero hc hv0) ?_ ?_ ?_ ?_ a (c * u) (v / u)
        (mul_ne_zero hc hu0) h h0 ?_ rfl
    · rw [norm_mul, ← div_le_iff₀' hcpos]; exact (le_max_right _ _).trans hv
    · rw [norm_mul]; exact mul_lt_mul_of_pos_left hvρ' hcpos
    · rw [norm_mul]; exact mul_lt_mul_of_pos_left hρu hcpos
    · rw [norm_mul, ← le_div_iff₀' hcpos]; exact (hu.trans_le (min_le_right _ _)).le
    · rw [mul_assoc, mul_div_cancel₀ _ hu0]

include hp hp1 in
/-- **(D⇐) and (T⇐)** from the two `δ`-count steps (R5), the two-sided type-3 germ and goodness
near type-4 points. -/
theorem smoothOfDiscCond_and_exhaustingOfTube (hED : ExhaustDescentFor C F)
    (hGl : ExhaustGlueFor C F) (h3 : S8A.TypeThreeGermTwoFor C F)
    (h4 : S8A.TypeFourGoodFor C F) : SmoothOfDiscCond C F ∧ ExhaustingOfTube C F :=
  have hD := smoothOfDiscCond_of hp hp1 hED (S8A.typeThreeGermFor_of_two h3) h4
  ⟨hD, exhaustingOfTube_of hp hp1 hGl hD h3⟩

end Limit

end ExhaustGluing

end SemistableReduction
