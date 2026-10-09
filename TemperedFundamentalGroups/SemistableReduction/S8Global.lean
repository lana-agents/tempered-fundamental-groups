/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Interfaces

/-!
# S8.A: the global improvement argument

Blueprint §9.10 (S8.A), §9.12 (O6). The argument of [AW §2.5] (proof of Theorem 2.8 from
Proposition 2.8), on finite sets of balls, against the local interfaces of `S8Interfaces`.

Fix `F / C(x)` (Galois in the application). For a ball tree `T` with root `R`:

* `badLeaves F T`: the bad leaf balls of `T` (leaf residue balls over which some point is not
  smooth); finite by `FiniteBadFor`;
* `dmin F B`: the smallest exhausting disc of a bad ball (`S8BMinFor`); canonical, since the
  minimum is unique;
* `step F T = T ∪ {dmin B | B bad leaf ball}`: [AW]'s improvement at *all* critical points at
  once;
* `Inv F T R`: `T` is a ball tree with root `R` all of whose edges are good;
* `inv_step`: `step` preserves `Inv` (new edges are exhausting by construction);
* `exists_lt_of_mem_badLeaves_step`: every bad leaf ball of `step T` is a residue ball of some
  `dmin B`, `B` a bad leaf ball of `T`, and has smaller measure (`R5MeasureFor`);
* `exists_badLeaves_eq_empty`: the iteration terminates.
-/

open Metric

namespace SemistableReduction

namespace S8A

open BallTree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

section Dmin

lemma isMinExh_congr {b b' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) (h : ball b ‖c‖ = ball b' ‖c'‖)
    {D : Set C} : IsMinExh F b hc D ↔ IsMinExh F b' hc' D := by
  unfold IsMinExh
  rw [h, closedBall_eq_of_ball_eq hc hc' h]

lemma IsMinExh.unique {b c : C} {hc : c ≠ 0} {D D' : Set C} (h : IsMinExh F b hc D)
    (h' : IsMinExh F b hc D') : D = D' :=
  le_antisymm (h.2.2.2 D' h'.1 h'.2.1 h'.2.2.1) (h'.2.2.2 D h.1 h.2.1 h.2.2.1)

variable (F) in
open Classical in
/-- The smallest exhausting disc of an open ball (`∅` if there is none). -/
noncomputable def dmin (B : Set C) : Set C :=
  if h : ∃ D : Set C, ∃ (b c : C) (hc : c ≠ 0), B = ball b ‖c‖ ∧ IsMinExh F b hc D then
    Classical.choose h else ∅

lemma dmin_spec {b c : C} (hc : c ≠ 0) {D : Set C} (hD : IsMinExh F b hc D) :
    IsMinExh F b hc (dmin F (ball b ‖c‖)) := by
  have h : ∃ D : Set C, ∃ (b' c' : C) (hc' : c' ≠ 0), ball b ‖c‖ = ball b' ‖c'‖ ∧
      IsMinExh F b' hc' D := ⟨D, b, c, hc, rfl, hD⟩
  rw [dmin, dif_pos h]
  obtain ⟨b', c', hc', hB, hmin⟩ := Classical.choose_spec h
  exact (isMinExh_congr hc hc' hB).2 hmin

lemma dmin_eq {b c : C} (hc : c ≠ 0) {D : Set C} (hD : IsMinExh F b hc D) :
    dmin F (ball b ‖c‖) = D :=
  (dmin_spec hc hD).unique hD

end Dmin

section Leaves

variable (F) in
/-- The bad leaf balls of `T`. -/
def badLeaves (T : Finset (Set C)) : Set (Set C) := {B | IsLeafBall T B ∧ ¬ BallGood F B}

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma isResBall_of_isLeafBall {T : Finset (Set C)} {B : Set C} (h : IsLeafBall T B) :
    ∃ D ∈ T, IsResBall D B := by
  obtain ⟨a, b, c, hc, hP, hb, rfl, -⟩ := h
  exact ⟨_, hP, a, b, c, hc, rfl, hb, rfl⟩

lemma finite_badLeaves (hfin : FiniteBadFor C F) {T : Finset (Set C)} (hT : ∀ D ∈ T, IsDisc D) :
    (badLeaves F T).Finite := by
  refine (Set.Finite.biUnion T.finite_toSet fun D hD ↦ hfin D (hT D hD)).subset ?_
  rintro B ⟨hB, hbad⟩
  obtain ⟨D, hD, hres⟩ := isResBall_of_isLeafBall hB
  exact Set.mem_biUnion hD ⟨hres, hbad⟩

omit [IsAlgClosed C] in
/-- Leaf balls meeting each other are equal. -/
lemma eq_of_isLeafBall {T : Finset (Set C)} {B B' : Set C} (hB : IsLeafBall T B)
    (hB' : IsLeafBall T B') (h : (B ∩ B').Nonempty) : B = B' := by
  obtain ⟨a, b, c, hc, hP, hb, rfl, hleaf⟩ := hB
  obtain ⟨a', b', c', hc', hP', hb', rfl, hleaf'⟩ := hB'
  obtain ⟨z, hz, hz'⟩ := h
  have hzP : z ∈ closedBall a ‖c‖ := ball_subset_closedBall_of_mem hb hz
  have hzP' : z ∈ closedBall a' ‖c'‖ := ball_subset_closedBall_of_mem hb' hz'
  have hle : ‖c‖ ≤ ‖c'‖ := by
    by_contra hlt
    push Not at hlt
    exact hleaf _ hP' (closedBall_subset_ball_of_mem hzP' hz hlt)
  have hge : ‖c'‖ ≤ ‖c‖ := by
    by_contra hlt
    push Not at hlt
    exact hleaf' _ hP (closedBall_subset_ball_of_mem hzP hz' hlt)
  have he := le_antisymm hle hge
  rw [← he] at hz' ⊢
  rw [IsUltrametricDist.ball_eq_of_mem hz, IsUltrametricDist.ball_eq_of_mem hz']

omit [IsAlgClosed C] in
/-- A strict inclusion of discs has strictly smaller radius. -/
lemma norm_lt_of_ssubset {a a' d c : C} (h : closedBall a ‖d‖ ⊂ closedBall a' ‖c‖) : ‖d‖ < ‖c‖ := by
  obtain ⟨h1, h2⟩ := closedBall_subset_closedBall_iff'.1 h.1
  refine lt_of_le_of_ne h1 fun he ↦ h.2 ?_
  exact closedBall_subset_closedBall_iff'.2 ⟨he.ge, by rw [norm_sub_rev, he]; exact h2⟩

end Leaves

section Step

variable (F) in
/-- The invariant of the iteration: `T` is a ball tree with root `R` all of whose edges are
good. -/
structure Inv (T : Finset (Set C)) (R : Set C) : Prop where
  tree : IsTree T
  root_mem : R ∈ T
  root : ∀ D ∈ T, D ⊆ R
  edge : ∀ E ∈ T, ∀ G ∈ T, E ⊂ G → (∀ X ∈ T, ¬ (E ⊂ X ∧ X ⊂ G)) → EdgeGood F E G

variable (hfin : FiniteBadFor C F) (hmin : S8BMinFor C F)

include hmin in
/-- The smallest exhausting disc of a bad leaf ball. -/
lemma isMinExh_dmin {T : Finset (Set C)} {B : Set C} (hB : B ∈ badLeaves F T) :
    ∃ a b c : C, ∃ hc : c ≠ 0, closedBall a ‖c‖ ∈ T ∧ b ∈ closedBall a ‖c‖ ∧
      B = ball b ‖c‖ ∧ (∀ E ∈ T, ¬ E ⊆ B) ∧ IsMinExh F b hc (dmin F B) := by
  obtain ⟨⟨a, b, c, hc, hP, hb, rfl, hleaf⟩, hbad⟩ := hB
  obtain ⟨D, hD⟩ := hmin b c hc hbad
  exact ⟨a, b, c, hc, hP, hb, rfl, hleaf, dmin_spec hc hD⟩

variable (F) in
open Classical in
/-- **One improvement step** ([AW §2.5]): add the smallest exhausting disc of every bad leaf
ball. -/
noncomputable def step (T : Finset (Set C)) : Finset (Set C) :=
  if h : (badLeaves F T).Finite then T ∪ h.toFinset.image (dmin F) else T

open Classical in
lemma step_eq {T : Finset (Set C)} (h : (badLeaves F T).Finite) :
    step F T = T ∪ h.toFinset.image (dmin F) := by
  rw [step, dif_pos h]

lemma mem_step {T : Finset (Set C)} (h : (badLeaves F T).Finite) {X : Set C} :
    X ∈ step F T ↔ X ∈ T ∨ ∃ B ∈ badLeaves F T, dmin F B = X := by
  rw [step_eq h, Finset.mem_union, Finset.mem_image]
  simp only [Set.Finite.mem_toFinset]

include hfin hmin in
/-- **The improvement step preserves the invariant.** -/
theorem inv_step {T : Finset (Set C)} {R : Set C} (hT : Inv F T R) : Inv F (step F T) R := by
  classical
  have hf := finite_badLeaves hfin hT.tree.disc
  have hmem := fun X ↦ mem_step (F := F) (T := T) hf (X := X)
  -- the new discs lie in their leaf balls
  have hnew : ∀ B ∈ badLeaves F T, IsDisc (dmin F B) ∧ dmin F B ⊆ B := fun B hB ↦ by
    obtain ⟨a, b, c, hc, -, -, rfl, -, h⟩ := isMinExh_dmin hmin hB
    exact ⟨h.1, h.2.1⟩
  have htree : IsTree (step F T) := by
    rw [step_eq hf]
    refine hT.tree.union_of_leaf (fun G hG ↦ ?_) fun G hG ↦ ?_
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hG
      exact (hnew B ((Set.Finite.mem_toFinset hf).1 hB)).1
    · obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hG
      have hB' := (Set.Finite.mem_toFinset hf).1 hB
      obtain ⟨a, b, c, hc, hP, hb, hBe, hleaf, h⟩ := isMinExh_dmin hmin hB'
      refine ⟨a, b, c, hc, hP, hb, hBe ▸ h.2.1, hBe ▸ hleaf, fun G' hG' hne hsub ↦ ?_⟩
      obtain ⟨B', hB'', rfl⟩ := Finset.mem_image.1 hG'
      have hB''' := (Set.Finite.mem_toFinset hf).1 hB''
      apply hne
      obtain ⟨hd', hsub'⟩ := hnew B' hB'''
      obtain ⟨z, hz⟩ := hd'.nonempty
      rw [eq_of_isLeafBall hB'''.1 hB'.1 ⟨z, hsub' hz, hBe ▸ hsub hz⟩]
  refine ⟨htree, (hmem R).2 (.inl hT.root_mem), fun D hD ↦ ?_, ?_⟩
  · rcases (hmem D).1 hD with h | ⟨B, hB, rfl⟩
    · exact hT.root D h
    · obtain ⟨a, b, c, hc, hP, hb, rfl, -, h⟩ := isMinExh_dmin hmin hB
      exact h.2.1.trans ((ball_subset_closedBall_of_mem hb).trans (hT.root _ hP))
  · intro E hE G hG hEG hmin'
    rcases (hmem E).1 hE with hE' | ⟨B, hB, rfl⟩
    · rcases (hmem G).1 hG with hG' | ⟨B, hB, rfl⟩
      · exact hT.edge E hE' G hG' hEG fun X hX ↦ hmin' X ((hmem X).2 (.inl hX))
      · exfalso
        obtain ⟨a, b, c, hc, -, -, rfl, hleaf, h⟩ := isMinExh_dmin hmin hB
        exact hleaf E hE' (hEG.1.trans h.2.1)
    · -- `E = dmin B`; the edge goes to the parent of `B`
      obtain ⟨a, b, c, hc, hP, hb, hBe, hleaf, h⟩ := isMinExh_dmin hmin hB
      have hPb : closedBall a ‖c‖ = closedBall b ‖c‖ :=
        IsUltrametricDist.closedBall_eq_of_mem hb
      have hEP : dmin F B ⊂ closedBall a ‖c‖ := by
        refine ⟨h.2.1.trans (hBe ▸ ball_subset_closedBall_of_mem hb), fun hPE ↦ ?_⟩
        exact hleaf _ hP (hPE.trans (hBe ▸ h.2.1))
      have hGd := htree.disc G hG
      have hGP : G = closedBall a ‖c‖ := by
        obtain ⟨z, hz⟩ := h.1.nonempty
        rcases hGd.subset_or_subset (hT.tree.disc _ hP) ⟨z, hEG.1 hz, hEP.1 hz⟩ with hsub | hsub
        · by_contra hne
          have hss : G ⊂ closedBall a ‖c‖ := ⟨hsub, fun h' ↦ hne (le_antisymm hsub h')⟩
          obtain ⟨g, d, hd, rfl⟩ := hGd
          have hlt := norm_lt_of_ssubset hss
          have hGB : closedBall g ‖d‖ ⊆ B :=
            hBe ▸ closedBall_subset_ball_of_mem (hEG.1 hz) (hBe ▸ h.2.1 hz) hlt
          rcases (hmem _).1 hG with hG' | ⟨B', hB', hB'e⟩
          · exact hleaf _ hG' hGB
          · obtain ⟨hd', hsub'⟩ := hnew B' hB'
            have hBB : B' = B := eq_of_isLeafBall hB'.1 hB.1
              ⟨z, hsub' (hB'e ▸ hEG.1 hz), hGB (hEG.1 hz)⟩
            rw [hBB] at hB'e
            exact hEG.2 (hB'e ▸ le_rfl)
        · by_contra hne
          exact hmin' _ ((hmem _).2 (.inl hP)) ⟨hEP, hsub, fun h' ↦ hne (le_antisymm h' hsub)⟩
      rw [hGP, hPb]
      exact h.2.2.1

variable (hR5 : R5MeasureFor C F)

include hfin hmin in
/-- **Bad leaf balls of the improved tree** are residue balls of the new discs. -/
theorem exists_of_mem_badLeaves_step {T : Finset (Set C)} {R : Set C} (hT : Inv F T R)
    {B' : Set C} (hB' : B' ∈ badLeaves F (step F T)) :
    ∃ B ∈ badLeaves F T, IsResBall (dmin F B) B' := by
  have hf := finite_badLeaves hfin hT.tree.disc
  obtain ⟨⟨a, b, c, hc, hX, hb, rfl, hleaf⟩, hbad⟩ := hB'
  rcases (mem_step hf).1 hX with hX' | ⟨B, hB, hBe⟩
  · exfalso
    have hleafT : IsLeafBall T (ball b ‖c‖) :=
      ⟨a, b, c, hc, hX', hb, rfl, fun E hE ↦ hleaf E ((mem_step hf).2 (.inl hE))⟩
    obtain ⟨-, b', c', hc', -, -, hBe, -, h⟩ := isMinExh_dmin hmin ⟨hleafT, hbad⟩
    exact hleaf _ ((mem_step hf).2 (.inr ⟨_, ⟨hleafT, hbad⟩, rfl⟩)) (hBe ▸ h.2.1)
  · exact ⟨B, hB, a, b, c, hc, hBe, hBe ▸ hb, rfl⟩

include hfin hmin hR5 in
/-- **Termination** ([AW §2.5]): the iterated improvement reaches a tree without bad leaf balls. -/
theorem exists_badLeaves_eq_empty {T : Finset (Set C)} {R : Set C} (hT : Inv F T R) :
    ∃ n, badLeaves F ((step F)^[n] T) = ∅ := by
  obtain ⟨μ, hμ⟩ := hR5
  suffices key : ∀ m : ℕ, ∀ T : Finset (Set C), Inv F T R → (∀ B ∈ badLeaves F T, μ B < m) →
      ∃ n, badLeaves F ((step F)^[n] T) = ∅ by
    have hf := finite_badLeaves hfin hT.tree.disc
    refine key (hf.toFinset.sup μ + 1) T hT fun B hB ↦ Nat.lt_succ_of_le ?_
    exact Finset.le_sup (f := μ) ((Set.Finite.mem_toFinset hf).2 hB)
  intro m
  induction m with
  | zero =>
    intro T _ h
    exact ⟨0, Set.eq_empty_of_forall_notMem fun B hB ↦ Nat.not_lt_zero _ (h B hB)⟩
  | succ m ih =>
    intro T hT h
    obtain ⟨n, hn⟩ := ih (step F T) (inv_step hfin hmin hT) fun B' hB' ↦ by
      obtain ⟨B, hB, hres⟩ := exists_of_mem_badLeaves_step hfin hmin hT hB'
      obtain ⟨a, b, c, hc, -, -, hBe, -, hB2⟩ := isMinExh_dmin hmin hB
      have hbad : ¬ BallGood F (ball b ‖c‖) := hBe ▸ hB.2
      have := hμ b c hc _ hbad hB2 B' (hBe ▸ hres) hB'.2
      rw [← hBe] at this
      exact Nat.lt_of_lt_of_le this (Nat.lt_succ_iff.1 (h B hB))
    exact ⟨n + 1, by rw [Function.iterate_succ_apply]; exact hn⟩

lemma subset_step {T : Finset (Set C)} : T ⊆ step F T := by
  classical
  intro X hX
  rw [step]
  split_ifs
  · exact Finset.mem_union_left _ hX
  · exact hX

lemma subset_iterate_step {T : Finset (Set C)} (n : ℕ) : T ⊆ (step F)^[n] T := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans subset_step

include hfin hmin in
lemma inv_iterate_step {T : Finset (Set C)} {R : Set C} (hT : Inv F T R) (n : ℕ) :
    Inv F ((step F)^[n] T) R := by
  induction n with
  | zero => exact hT
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step hfin hmin ih

end Step

end S8A

end SemistableReduction
