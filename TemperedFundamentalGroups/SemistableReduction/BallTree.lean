/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W7Statement

/-!
# Gauss trees as finite sets of balls

Blueprint §9.12, O6 (S8.A, infrastructure). The global improvement argument of [AW] constructs
the vertex set *canonically* (so that it is stable under the automorphisms of `C` stabilizing the
input). A vertex set is therefore represented by a finite set of closed balls
`D = closedBall a ‖c‖ ⊆ C` (`c ≠ 0`), which does not depend on the choice of centres and radius
parameters, and converted to the indexed form `(ι, a, c)` of `gaussJoinModel` and `W7.Statement`
only at the end.

* `closedBall_subset_closedBall_iff'`, `closedBall_eq_closedBall_iff'`: inclusion and equality of
  discs in terms of `(a, c)` (`DiscLE`);
* `IsDisc D`: `D` is a closed ball of radius in `|C^×|`;
* `BallTree.IsTree T`: a finite nonempty set of discs closed under joins (`IsJoin`: the smallest
  disc containing two discs);
* `BallTree.toFamily`: the indexed form, convex and reduced (`isConvex_toFamily`,
  `isReduced_toFamily`).
-/

open Metric
open scoped NNReal

namespace SemistableReduction

namespace BallTree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

section Balls

omit [IsUltrametricDist C] in
lemma mem_closedBall' {x a : C} {r : ℝ} : x ∈ closedBall a r ↔ ‖x - a‖ ≤ r := by
  rw [mem_closedBall, dist_eq_norm]

omit [IsUltrametricDist C] in
lemma mem_ball' {x a : C} {r : ℝ} : x ∈ ball a r ↔ ‖x - a‖ < r := by
  rw [mem_ball, dist_eq_norm]

lemma norm_sub_le_max' (x y z : C) : ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖ := by
  have := IsUltrametricDist.norm_add_le_max (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this

/-- Inclusion of discs. -/
lemma closedBall_subset_closedBall_iff' {a a' c c' : C} :
    closedBall a ‖c‖ ⊆ closedBall a' ‖c'‖ ↔ ‖c‖ ≤ ‖c'‖ ∧ ‖a - a'‖ ≤ ‖c'‖ := by
  constructor
  · intro h
    have h1 : ‖a - a'‖ ≤ ‖c'‖ := mem_closedBall'.1 (h (mem_closedBall'.2 (by simp)))
    have h2 : ‖(a + c) - a'‖ ≤ ‖c'‖ :=
      mem_closedBall'.1 (h (mem_closedBall'.2 (by simp)))
    refine ⟨?_, h1⟩
    have := norm_sub_le_max' (a + c) a' a
    rw [show a + c - a = c by ring, norm_sub_rev a' a] at this
    exact this.trans (max_le h2 h1)
  · rintro ⟨h1, h2⟩ x hx
    exact mem_closedBall'.2 ((norm_sub_le_max' x a a').trans
      (max_le ((mem_closedBall'.1 hx).trans h1) h2))

/-- Equality of discs. -/
lemma closedBall_eq_closedBall_iff' {a a' c c' : C} (_hc : c ≠ 0) (_hc' : c' ≠ 0) :
    closedBall a ‖c‖ = closedBall a' ‖c'‖ ↔ ‖c‖ = ‖c'‖ ∧ ‖a - a'‖ ≤ ‖c‖ := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := (closedBall_subset_closedBall_iff').1 h.le
    obtain ⟨h3, -⟩ := (closedBall_subset_closedBall_iff').1 h.ge
    have he := le_antisymm h1 h3
    exact ⟨he, he ▸ h2⟩
  · rintro ⟨h1, h2⟩
    refine le_antisymm ((closedBall_subset_closedBall_iff').2 ⟨h1.le, h1 ▸ h2⟩)
      ((closedBall_subset_closedBall_iff').2 ⟨h1.ge, ?_⟩)
    rw [norm_sub_rev]
    exact h1 ▸ h2

/-- A disc inside an open ball has smaller radius. -/
lemma closedBall_subset_ball_iff' {a b c : C} {r : ℝ} :
    closedBall a ‖c‖ ⊆ ball b r ↔ ‖c‖ < r ∧ ‖a - b‖ < r := by
  constructor
  · intro h
    have h1 : ‖a - b‖ < r := mem_ball'.1 (h (mem_closedBall'.2 (by simp)))
    have h2 : ‖(a + c) - b‖ < r := mem_ball'.1 (h (mem_closedBall'.2 (by simp)))
    refine ⟨?_, h1⟩
    have := norm_sub_le_max' (a + c) b a
    rw [show a + c - a = c by ring, norm_sub_rev b a] at this
    exact this.trans_lt (max_lt h2 h1)
  · rintro ⟨h1, h2⟩ x hx
    exact mem_ball'.2 ((norm_sub_le_max' x a b).trans_lt
      (max_lt ((mem_closedBall'.1 hx).trans_lt h1) h2))

/-- Disc inclusion in terms of the Gauss tree order. -/
lemma discLE_iff_subset {ι : Type*} {a c : ι → C} (_hc : ∀ i, c i ≠ 0) {i j : ι} :
    GaussTree.DiscLE ν a c i j ↔ closedBall (a i) ‖c i‖ ⊆ closedBall (a j) ‖c j‖ := by
  rw [TreeBridge.discLE_iff, closedBall_subset_closedBall_iff']

end Balls

/-- `D` is a closed disc with radius in `|C^×|`. -/
def IsDisc (D : Set C) : Prop := ∃ a c : C, c ≠ 0 ∧ D = closedBall a ‖c‖

/-- `G` is the **join** of the discs `D` and `E`: the smallest disc containing both. -/
def IsJoin (D E G : Set C) : Prop :=
  IsDisc G ∧ D ⊆ G ∧ E ⊆ G ∧ ∀ G', IsDisc G' → D ⊆ G' → E ⊆ G' → G ⊆ G'

/-- A **ball tree**: a finite nonempty set of discs containing the joins of its members. -/
structure IsTree (T : Finset (Set C)) : Prop where
  disc : ∀ D ∈ T, IsDisc D
  nonempty : T.Nonempty
  join : ∀ D ∈ T, ∀ E ∈ T, ∃ G ∈ T, IsJoin D E G

/-- The join of two discs exists (radius `max (‖c‖, ‖c'‖, ‖a - a'‖)`). -/
lemma exists_isJoin {D E : Set C} (hD : IsDisc D) (hE : IsDisc E) : ∃ G, IsJoin D E G := by
  obtain ⟨a, c, hc, rfl⟩ := hD
  obtain ⟨a', c', hc', rfl⟩ := hE
  -- an element realizing the maximal radius
  obtain ⟨g, hg0, hg⟩ : ∃ g : C, g ≠ 0 ∧ ‖g‖ = max (max ‖c‖ ‖c'‖) ‖a - a'‖ := by
    rcases le_total (max ‖c‖ ‖c'‖) ‖a - a'‖ with h | h
    · refine ⟨a - a', ?_, by rw [max_eq_right h]⟩
      intro h0
      rw [h0, norm_zero] at h
      exact (norm_pos_iff.2 hc).not_ge ((le_max_left _ _).trans h)
    · rw [max_eq_left h]
      rcases le_total ‖c‖ ‖c'‖ with h' | h'
      · exact ⟨c', hc', by rw [max_eq_right h']⟩
      · exact ⟨c, hc, by rw [max_eq_left h']⟩
  refine ⟨closedBall a ‖g‖, ⟨a, g, hg0, rfl⟩, ?_, ?_, ?_⟩
  · exact (closedBall_subset_closedBall_iff').2
      ⟨hg ▸ (le_max_left _ _).trans (le_max_left _ _), by simp⟩
  · refine (closedBall_subset_closedBall_iff').2
      ⟨hg ▸ (le_max_right _ _).trans (le_max_left _ _), ?_⟩
    rw [norm_sub_rev, hg]
    exact le_max_right _ _
  · rintro G' ⟨b, d, hd, rfl⟩ h1 h2
    obtain ⟨h11, h12⟩ := (closedBall_subset_closedBall_iff').1 h1
    obtain ⟨h21, h22⟩ := (closedBall_subset_closedBall_iff').1 h2
    refine (closedBall_subset_closedBall_iff').2 ⟨?_, h12⟩
    rw [hg]
    refine max_le (max_le h11 h21) ?_
    have := norm_sub_le_max' a b a'
    rw [norm_sub_rev b a'] at this
    exact this.trans (max_le h12 h22)

section Discs

/-- Discs meeting each other are nested. -/
lemma subset_or_subset_of_mem {a a' c c' z : C} (h : z ∈ closedBall a ‖c‖)
    (h' : z ∈ closedBall a' ‖c'‖) :
    closedBall a ‖c‖ ⊆ closedBall a' ‖c'‖ ∨ closedBall a' ‖c'‖ ⊆ closedBall a ‖c‖ := by
  rw [mem_closedBall'] at h h'
  rcases le_total ‖c‖ ‖c'‖ with hle | hle
  · refine .inl (closedBall_subset_closedBall_iff'.2 ⟨hle, ?_⟩)
    have := norm_sub_le_max' a z a'
    rw [norm_sub_rev a z] at this
    exact this.trans (max_le (h.trans hle) h')
  · refine .inr (closedBall_subset_closedBall_iff'.2 ⟨hle, ?_⟩)
    have := norm_sub_le_max' a' z a
    rw [norm_sub_rev a' z] at this
    exact this.trans (max_le (h'.trans hle) h)

/-- Discs are nested or disjoint. -/
lemma IsDisc.subset_or_subset_or_disjoint {D E : Set C} (hD : IsDisc D) (hE : IsDisc E) :
    D ⊆ E ∨ E ⊆ D ∨ Disjoint D E := by
  obtain ⟨a, c, -, rfl⟩ := hD
  obtain ⟨a', c', -, rfl⟩ := hE
  by_cases h : ∃ z, z ∈ closedBall a ‖c‖ ∧ z ∈ closedBall a' ‖c'‖
  · obtain ⟨z, hz, hz'⟩ := h
    rcases subset_or_subset_of_mem hz hz' with h1 | h1
    · exact .inl h1
    · exact .inr (.inl h1)
  · push Not at h
    exact .inr (.inr (Set.disjoint_left.2 h))

omit [IsUltrametricDist C] in
lemma IsDisc.nonempty {D : Set C} (hD : IsDisc D) : D.Nonempty := by
  obtain ⟨a, c, -, rfl⟩ := hD
  exact ⟨a, mem_closedBall'.2 (by simp)⟩

/-- Discs with a common point are nested. -/
lemma IsDisc.subset_or_subset {D E : Set C} (hD : IsDisc D) (hE : IsDisc E) (h : (D ∩ E).Nonempty) :
    D ⊆ E ∨ E ⊆ D := by
  rcases hD.subset_or_subset_or_disjoint hE with h1 | h1 | h1
  · exact .inl h1
  · exact .inr h1
  · exact absurd h (Set.not_nonempty_iff_eq_empty.2 (Set.disjoint_iff_inter_eq_empty.1 h1))

omit [IsUltrametricDist C] in
lemma IsJoin.symm {D E G : Set C} (h : IsJoin D E G) : IsJoin E D G :=
  ⟨h.1, h.2.2.1, h.2.1, fun G' h1 h2 h3 ↦ h.2.2.2 G' h1 h3 h2⟩

omit [IsUltrametricDist C] in
lemma IsJoin.unique {D E G G' : Set C} (h : IsJoin D E G) (h' : IsJoin D E G') : G = G' :=
  le_antisymm (h.2.2.2 G' h'.1 h'.2.1 h'.2.2.1) (h'.2.2.2 G h.1 h.2.1 h.2.2.1)

omit [IsUltrametricDist C] in
lemma isJoin_of_subset {D E : Set C} (hE : IsDisc E) (h : D ⊆ E) : IsJoin D E E :=
  ⟨hE, h, le_rfl, fun _ _ _ h2 ↦ h2⟩

/-- **Joins through a floor**: if `D ⊆ G` and `X` is disjoint from `G`, the join of `G` and `X`
is the join of `D` and `X`. -/
lemma IsJoin.of_floor {D G X J : Set C} (hD : IsDisc D) (hG : IsDisc G) (hX : IsDisc X)
    (hDG : D ⊆ G) (hGX : Disjoint G X) (hJ : IsJoin D X J) : IsJoin G X J := by
  have hGJ : G ⊆ J := by
    have hne : (G ∩ J).Nonempty := by
      obtain ⟨z, hz⟩ := hD.nonempty
      exact ⟨z, hDG hz, hJ.2.1 hz⟩
    rcases hG.subset_or_subset hJ.1 hne with h | h
    · exact h
    · exact absurd (hJ.2.2.1.trans h) fun hXG ↦
        (Set.not_nonempty_iff_eq_empty.2 (Set.disjoint_iff_inter_eq_empty.1 hGX))
          (by obtain ⟨z, hz⟩ := hX.nonempty; exact ⟨z, hXG hz, hz⟩)
  exact ⟨hJ.1, hGJ, hJ.2.2.1, fun G' h1 h2 h3 ↦ hJ.2.2.2 G' h1 (hDG.trans h2) h3⟩

end Discs

section Tree

omit [IsUltrametricDist C] in
/-- A ball tree has a root containing all its discs. -/
lemma IsTree.exists_root {T : Finset (Set C)} (hT : IsTree T) : ∃ R ∈ T, ∀ D ∈ T, D ⊆ R := by
  obtain ⟨R, hR⟩ := T.exists_maximal hT.nonempty
  refine ⟨R, hR.1, fun D hD ↦ ?_⟩
  obtain ⟨G, hG, hJ⟩ := hT.join R hR.1 D hD
  exact hJ.2.2.1.trans (hR.2 hG hJ.2.1)

/-- **Adding floored discs**: adding to a ball tree finitely many discs, each containing a disc of
the tree, gives a ball tree. -/
lemma IsTree.union_of_floor {T S : Finset (Set C)} {_ : DecidableEq (Set C)} (hT : IsTree T)
    (hS : ∀ G ∈ S, IsDisc G) (hfl : ∀ G ∈ S, ∃ D ∈ T, D ⊆ G) : IsTree (T ∪ S) := by
  have hdisc : ∀ D ∈ T ∪ S, IsDisc D := fun D hD ↦ by
    rcases Finset.mem_union.1 hD with h | h
    · exact hT.disc D h
    · exact hS D h
  -- the join of a floored disc with any member
  have key : ∀ G ∈ S, ∀ Y ∈ T ∪ S, ∃ J ∈ T ∪ S, IsJoin G Y J := by
    intro G hG Y hY
    obtain ⟨D, hD, hDG⟩ := hfl G hG
    have hGd := hS G hG
    have hYd := hdisc Y hY
    rcases hGd.subset_or_subset_or_disjoint hYd with h | h | h
    · exact ⟨Y, hY, isJoin_of_subset hYd h⟩
    · exact ⟨G, Finset.mem_union_right _ hG, (isJoin_of_subset hGd h).symm⟩
    · -- the join is that of the floor
      suffices hDY : ∃ J ∈ T ∪ S, IsJoin D Y J by
        obtain ⟨J, hJ, hJ'⟩ := hDY
        exact ⟨J, hJ, hJ'.of_floor (hT.disc D hD) hGd hYd hDG h⟩
      rcases Finset.mem_union.1 hY with hY' | hY'
      · obtain ⟨J, hJ, hJ'⟩ := hT.join D hD Y hY'
        exact ⟨J, Finset.mem_union_left _ hJ, hJ'⟩
      · obtain ⟨D', hD', hD'Y⟩ := hfl Y hY'
        rcases (hT.disc D hD).subset_or_subset_or_disjoint hYd with h' | h' | h'
        · exact ⟨Y, hY, isJoin_of_subset hYd h'⟩
        · exfalso
          obtain ⟨z, hz⟩ := hYd.nonempty
          exact Set.disjoint_left.1 h (hDG (h' hz)) hz
        · obtain ⟨J, hJ, hJ'⟩ := hT.join D' hD' D hD
          exact ⟨J, Finset.mem_union_left _ hJ,
            (hJ'.of_floor (hT.disc D' hD') hYd (hT.disc D hD) hD'Y h'.symm).symm⟩
  refine ⟨hdisc, hT.nonempty.mono Finset.subset_union_left, fun X hX Y hY ↦ ?_⟩
  rcases Finset.mem_union.1 hX with hX' | hX'
  · rcases Finset.mem_union.1 hY with hY' | hY'
    · obtain ⟨J, hJ, hJ'⟩ := hT.join X hX' Y hY'
      exact ⟨J, Finset.mem_union_left _ hJ, hJ'⟩
    · obtain ⟨J, hJ, hJ'⟩ := key Y hY' X hX
      exact ⟨J, hJ, hJ'.symm⟩
  · exact key X hX' Y hY

/-- **Joins with a disc in a leaf ball**: let `B` be an open residue ball of the disc `P` (same
radius, centre in `P`) and `D ⊆ B` a disc. For a disc `X` not contained in `B`, either `D ⊆ X`, or
the join of `D` and `X` contains `P`. -/
lemma join_leaf {a b c : C} (_hc : c ≠ 0) (hb : b ∈ closedBall a ‖c‖) {D X J : Set C}
    (hD : IsDisc D) (hDB : D ⊆ ball b ‖c‖) (_hX : IsDisc X) (hXB : ¬ X ⊆ ball b ‖c‖)
    (hJ : IsJoin D X J) : closedBall a ‖c‖ ⊆ J := by
  obtain ⟨z, hz⟩ := hD.nonempty
  have hzP : z ∈ closedBall a ‖c‖ := by
    have hzb := mem_ball'.1 (hDB hz)
    rw [mem_closedBall'] at hb ⊢
    exact (norm_sub_le_max' z b a).trans (max_le hzb.le hb)
  obtain ⟨e, d, hd, he⟩ := hJ.1
  have hzJ : z ∈ J := hJ.2.1 hz
  rw [he] at hzJ ⊢
  rcases subset_or_subset_of_mem hzP hzJ with h | h
  · exact h
  · obtain ⟨h1, h2⟩ := closedBall_subset_closedBall_iff'.1 h
    rcases lt_or_eq_of_le h1 with hlt | heq
    · -- `J ⊆ B`, hence `X ⊆ B`
      exfalso
      apply hXB
      intro x hx
      have hxJ : x ∈ closedBall e ‖d‖ := he ▸ hJ.2.2.1 hx
      rw [mem_closedBall'] at hxJ hzJ
      rw [mem_ball']
      have hzb := mem_ball'.1 (hDB hz)
      have := norm_sub_le_max' x z b
      refine this.trans_lt (max_lt ?_ hzb)
      have := norm_sub_le_max' x e z
      rw [norm_sub_rev e z] at this
      exact this.trans_lt (max_lt (hxJ.trans_lt hlt) (hzJ.trans_lt hlt))
    · -- equal radius: `J = P`
      refine closedBall_subset_closedBall_iff'.2 ⟨heq.ge, ?_⟩
      rw [norm_sub_rev, heq]
      exact h2

variable (T : Finset (Set C)) in
/-- `B` is a **leaf ball** of `T`: an open residue ball `ball b ‖c‖` (`b ∈ P = closedBall a ‖c‖`)
of a disc `P ∈ T` containing no disc of `T`. -/
def IsLeafBall (B : Set C) : Prop :=
  ∃ a b c : C, c ≠ 0 ∧ closedBall a ‖c‖ ∈ T ∧ b ∈ closedBall a ‖c‖ ∧ B = ball b ‖c‖ ∧
    ∀ E ∈ T, ¬ E ⊆ B

/-- Joins of members inside leaf balls are joins of their parents. -/
lemma isJoin_parent {a b c : C} (hc : c ≠ 0) (hb : b ∈ closedBall a ‖c‖) {G Y J : Set C}
    (hG : IsDisc G) (hGB : G ⊆ ball b ‖c‖) (hY : IsDisc Y) (hYB : ¬ Y ⊆ ball b ‖c‖)
    (hJ : IsJoin G Y J) : IsJoin (closedBall a ‖c‖) Y J := by
  have hPJ := join_leaf hc hb hG hGB hY hYB hJ
  exact ⟨hJ.1, hPJ, hJ.2.2.1, fun G' h1 h2 h3 ↦ hJ.2.2.2 G' h1
    (hGB.trans ((Metric.ball_subset_closedBall).trans
      (by rw [← IsUltrametricDist.closedBall_eq_of_mem hb]) |>.trans h2)) h3⟩

/-- **Improvements keep the tree property**: adding discs inside distinct leaf balls of a ball
tree gives a ball tree. -/
lemma IsTree.union_of_leaf {S : Finset (Set C)} {_ : DecidableEq (Set C)} (hT : IsTree T)
    (hS : ∀ G ∈ S, IsDisc G)
    (hleaf : ∀ G ∈ S, ∃ a b c : C, c ≠ 0 ∧ closedBall a ‖c‖ ∈ T ∧ b ∈ closedBall a ‖c‖ ∧
      G ⊆ ball b ‖c‖ ∧ (∀ E ∈ T, ¬ E ⊆ ball b ‖c‖) ∧ ∀ G' ∈ S, G' ≠ G → ¬ G' ⊆ ball b ‖c‖) :
    IsTree (T ∪ S) := by
  have hdisc : ∀ D ∈ T ∪ S, IsDisc D := fun D hD ↦ by
    rcases Finset.mem_union.1 hD with h | h
    · exact hT.disc D h
    · exact hS D h
  have key : ∀ G ∈ S, ∀ Y ∈ T ∪ S, ∃ J ∈ T ∪ S, IsJoin G Y J := by
    intro G hG Y hY
    obtain ⟨a, b, c, hc, hP, hb, hGB, hTB, hSB⟩ := hleaf G hG
    have hGd := hS G hG
    have hYd := hdisc Y hY
    rcases hGd.subset_or_subset_or_disjoint hYd with h | h | h
    · exact ⟨Y, hY, isJoin_of_subset hYd h⟩
    · exact ⟨G, Finset.mem_union_right _ hG, (isJoin_of_subset hGd h).symm⟩
    · have hYB : ¬ Y ⊆ ball b ‖c‖ := by
        rcases Finset.mem_union.1 hY with hY' | hY'
        · exact hTB Y hY'
        · refine hSB Y hY' ?_
          rintro rfl
          obtain ⟨z, hz⟩ := hGd.nonempty
          exact Set.disjoint_left.1 h hz hz
      obtain ⟨J, hJ⟩ := exists_isJoin hGd hYd
      have hPJ := isJoin_parent hc hb hGd hGB hYd hYB hJ
      refine ⟨J, ?_, hJ⟩
      rcases Finset.mem_union.1 hY with hY' | hY'
      · obtain ⟨J', hJ', hJ''⟩ := hT.join _ hP Y hY'
        rw [hPJ.unique hJ'']
        exact Finset.mem_union_left _ hJ'
      · obtain ⟨a', b', c', hc', hP', hb', hYB', hTB', -⟩ := hleaf Y hY'
        have h2 := isJoin_parent hc' hb' hYd hYB' (hT.disc _ hP) (hTB' _ hP) hPJ.symm
        obtain ⟨J', hJ', hJ''⟩ := hT.join _ hP' _ hP
        rw [h2.unique hJ'']
        exact Finset.mem_union_left _ hJ'
  refine ⟨hdisc, hT.nonempty.mono Finset.subset_union_left, fun X hX Y hY ↦ ?_⟩
  rcases Finset.mem_union.1 hX with hX' | hX'
  · rcases Finset.mem_union.1 hY with hY' | hY'
    · obtain ⟨J, hJ, hJ'⟩ := hT.join X hX' Y hY'
      exact ⟨J, Finset.mem_union_left _ hJ, hJ'⟩
    · obtain ⟨J, hJ, hJ'⟩ := key Y hY' X hX
      exact ⟨J, hJ, hJ'.symm⟩
  · exact key X hX' Y hY

end Tree

section Family

variable {T : Finset (Set C)} (hT : ∀ D ∈ T, IsDisc D)

variable (T) in
/-- The `i`-th disc of `T` (in a fixed enumeration). -/
noncomputable def famDisc (i : Fin T.card) : Set C := (T.equivFin.symm i : Set C)

omit [NontriviallyNormedField C] [IsUltrametricDist C] in
lemma famDisc_mem (i : Fin T.card) : famDisc T i ∈ T := (T.equivFin.symm i).2

omit [NontriviallyNormedField C] [IsUltrametricDist C] in
lemma famDisc_injective : Function.Injective (famDisc T) := fun _ _ h ↦
  T.equivFin.symm.injective (Subtype.ext h)

omit [NontriviallyNormedField C] [IsUltrametricDist C] in
lemma exists_famDisc {D : Set C} (hD : D ∈ T) : ∃ i, famDisc T i = D :=
  ⟨T.equivFin ⟨D, hD⟩, by simp [famDisc]⟩

/-- A disc has a representation centred at `0` if it contains `0`. -/
lemma IsDisc.exists_centre {D : Set C} (hD : IsDisc D) :
    ∃ a c : C, (c ≠ 0 ∧ D = closedBall a ‖c‖) ∧ ((0 : C) ∈ D → a = 0) := by
  obtain ⟨a, c, hc, rfl⟩ := hD
  by_cases h0 : (0 : C) ∈ closedBall a ‖c‖
  · exact ⟨0, c, ⟨hc, IsUltrametricDist.closedBall_eq_of_mem h0⟩, fun _ ↦ rfl⟩
  · exact ⟨a, c, ⟨hc, rfl⟩, fun h ↦ absurd h h0⟩

/-- The centres of the discs of `T` (`0` for discs containing `0`). -/
noncomputable def famA (i : Fin T.card) : C :=
  Classical.choose ((hT _ (famDisc_mem i)).exists_centre)

/-- The radius parameters of the discs of `T`. -/
noncomputable def famC (i : Fin T.card) : C :=
  Classical.choose (Classical.choose_spec ((hT _ (famDisc_mem i)).exists_centre))

lemma famC_ne_zero (i : Fin T.card) : famC hT i ≠ 0 :=
  (Classical.choose_spec (Classical.choose_spec ((hT _ (famDisc_mem i)).exists_centre))).1.1

lemma famDisc_eq (i : Fin T.card) : famDisc T i = closedBall (famA hT i) ‖famC hT i‖ :=
  (Classical.choose_spec (Classical.choose_spec ((hT _ (famDisc_mem i)).exists_centre))).1.2

/-- Discs containing `0` are centred at `0`. -/
lemma famA_eq_zero {i : Fin T.card} (h : (0 : C) ∈ famDisc T i) : famA hT i = 0 :=
  (Classical.choose_spec (Classical.choose_spec ((hT _ (famDisc_mem i)).exists_centre))).2 h

lemma discLE_fam_iff {i j : Fin T.card} :
    GaussTree.DiscLE ν (famA hT) (famC hT) i j ↔ famDisc T i ⊆ famDisc T j := by
  rw [discLE_iff_subset (famC_ne_zero hT), famDisc_eq hT, famDisc_eq hT]

/-- The indexed family of a set of discs is reduced. -/
lemma isReduced_fam : GaussTree.IsReduced ν (famA hT) (famC hT) := fun _ _ h1 h2 ↦
  famDisc_injective (le_antisymm ((discLE_fam_iff hT).1 h1) ((discLE_fam_iff hT).1 h2))

/-- The indexed family of a ball tree is convex. -/
lemma isConvex_fam (hT' : IsTree T) : GaussTree.IsConvex ν (famA hT) (famC hT) := by
  intro i j
  obtain ⟨G, hG, hJ⟩ := hT'.join _ (famDisc_mem i) _ (famDisc_mem j)
  obtain ⟨k, rfl⟩ := exists_famDisc hG
  refine ⟨k, (discLE_fam_iff hT).2 hJ.2.1, (discLE_fam_iff hT).2 hJ.2.2.1, ?_⟩
  -- the explicit join is a disc containing both
  obtain ⟨g, hg0, hg⟩ : ∃ g : C, g ≠ 0 ∧ ‖g‖ = max (max ‖famC hT i‖ ‖famC hT j‖)
      ‖famA hT i - famA hT j‖ := by
    rcases le_total (max ‖famC hT i‖ ‖famC hT j‖) ‖famA hT i - famA hT j‖ with h | h
    · refine ⟨famA hT i - famA hT j, ?_, by rw [max_eq_right h]⟩
      intro h0
      rw [h0, norm_zero] at h
      exact (norm_pos_iff.2 (famC_ne_zero hT i)).not_ge ((le_max_left _ _).trans h)
    · rw [max_eq_left h]
      rcases le_total ‖famC hT i‖ ‖famC hT j‖ with h' | h'
      · exact ⟨famC hT j, famC_ne_zero hT j, by rw [max_eq_right h']⟩
      · exact ⟨famC hT i, famC_ne_zero hT i, by rw [max_eq_left h']⟩
  have hsub : famDisc T k ⊆ closedBall (famA hT i) ‖g‖ := by
    refine hJ.2.2.2 _ ⟨_, g, hg0, rfl⟩ ?_ ?_
    · rw [famDisc_eq hT]
      exact closedBall_subset_closedBall_iff'.2
        ⟨hg ▸ (le_max_left _ _).trans (le_max_left _ _), by simp⟩
    · rw [famDisc_eq hT]
      refine closedBall_subset_closedBall_iff'.2
        ⟨hg ▸ (le_max_right _ _).trans (le_max_left _ _), ?_⟩
      rw [norm_sub_rev, hg]
      exact le_max_right _ _
  rw [famDisc_eq hT] at hsub
  have h1 := (closedBall_subset_closedBall_iff'.1 hsub).1
  rw [hg] at h1
  have : ((ν (famC hT k) : ℝ≥0) : ℝ) ≤ ((max (max (ν (famC hT i)) (ν (famC hT j)))
      (ν (famA hT i - famA hT j)) : ℝ≥0) : ℝ) := by
    simpa [NormedField.valuation_apply] using h1
  exact_mod_cast this

/-- Discs of `T` are discs of the indexed family. -/
lemma discsLE_fam {ι₀ : Type*} {a₀ c₀ : ι₀ → C} (hc₀ : ∀ k, c₀ k ≠ 0)
    (h : ∀ k, closedBall (a₀ k) ‖c₀ k‖ ∈ T) : W7.DiscsLE a₀ c₀ (famA hT) (famC hT) := by
  intro k
  obtain ⟨i, hi⟩ := exists_famDisc (h k)
  rw [famDisc_eq hT] at hi
  obtain ⟨h1, h2⟩ := (closedBall_eq_closedBall_iff' (famC_ne_zero hT i) (hc₀ k)).1 hi
  exact ⟨i, h1, h2⟩

end Family

section OpenBalls

/-- Equality of open balls with radii in `|C^×|`. -/
lemma ball_eq_ball_iff' {b b' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) :
    ball b ‖c‖ = ball b' ‖c'‖ ↔ ‖c‖ = ‖c'‖ ∧ ‖b - b'‖ < ‖c‖ := by
  constructor
  · intro h
    have hb : ‖b - b'‖ < ‖c'‖ := mem_ball'.1 (h ▸ mem_ball'.2 (by simpa using hc))
    have hb' : ‖b' - b‖ < ‖c‖ := mem_ball'.1 (h ▸ mem_ball'.2 (by simpa using hc'))
    have hle : ‖c‖ ≤ ‖c'‖ := by
      by_contra hlt
      push Not at hlt
      -- `b' + c'` lies in the larger ball only
      have h1 : b' + c' ∈ ball b ‖c‖ := by
        rw [mem_ball']
        have := norm_sub_le_max' (b' + c') b' b
        rw [show b' + c' - b' = c' by ring] at this
        exact this.trans_lt (max_lt hlt hb')
      rw [h, mem_ball', show b' + c' - b' = c' by ring] at h1
      exact lt_irrefl _ h1
    have hge : ‖c'‖ ≤ ‖c‖ := by
      by_contra hlt
      push Not at hlt
      have h1 : b + c ∈ ball b' ‖c'‖ := by
        rw [mem_ball']
        have := norm_sub_le_max' (b + c) b b'
        rw [show b + c - b = c by ring] at this
        exact this.trans_lt (max_lt hlt hb)
      rw [← h, mem_ball', show b + c - b = c by ring] at h1
      exact lt_irrefl _ h1
    have he := le_antisymm hle hge
    exact ⟨he, he ▸ hb⟩
  · rintro ⟨h1, h2⟩
    rw [← h1]
    exact IsUltrametricDist.ball_eq_of_mem (mem_ball'.2 (by rw [norm_sub_rev]; exact h2))

/-- Equal open balls have equal closed balls. -/
lemma closedBall_eq_of_ball_eq {b b' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h : ball b ‖c‖ = ball b' ‖c'‖) : closedBall b ‖c‖ = closedBall b' ‖c'‖ := by
  obtain ⟨h1, h2⟩ := (ball_eq_ball_iff' hc hc').1 h
  exact (closedBall_eq_closedBall_iff' hc hc').2 ⟨h1, h2.le⟩

/-- A residue ball lies in its disc. -/
lemma ball_subset_closedBall_of_mem {a b c : C} (hb : b ∈ closedBall a ‖c‖) :
    ball b ‖c‖ ⊆ closedBall a ‖c‖ := by
  rw [IsUltrametricDist.closedBall_eq_of_mem hb]
  exact ball_subset_closedBall

/-- A disc meeting an open ball of larger radius lies in it. -/
lemma closedBall_subset_ball_of_mem {a b c d z : C} (hz : z ∈ closedBall a ‖d‖)
    (hz' : z ∈ ball b ‖c‖) (hdc : ‖d‖ < ‖c‖) : closedBall a ‖d‖ ⊆ ball b ‖c‖ := by
  intro x hx
  rw [mem_closedBall'] at hz hx
  rw [mem_ball'] at hz' ⊢
  have := norm_sub_le_max' x z b
  refine this.trans_lt (max_lt ?_ hz')
  have := norm_sub_le_max' x a z
  rw [norm_sub_rev a z] at this
  exact this.trans_lt (max_lt (hx.trans_lt hdc) (hz.trans_lt hdc))

/-- Open residue balls of radius `‖c‖` are equal or disjoint. -/
lemma ball_eq_or_disjoint' {b b' : C} {r : ℝ} :
    ball b r = ball b' r ∨ Disjoint (ball b r) (ball b' r) :=
  IsUltrametricDist.ball_eq_or_disjoint b b' r

end OpenBalls

end BallTree

end SemistableReduction
