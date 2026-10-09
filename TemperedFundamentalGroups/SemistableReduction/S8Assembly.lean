/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Global

/-!
# S8.A: assembly of the semistable Gauss tree

Blueprint §9.12, O6. Continuation of `S8Global`, for a fixed finite extension `F / C(x)`:

* `hull S`: the joins of all pairs of a finite set of discs, a ball tree containing `S`
  (`isTree_hull`);
* `repair F T₀ = T₀ ∪ (breaks of all segments of T₀)` (`EdgeRepairFor`, O10): a ball tree all of
  whose edges are good (`inv_repair`);
* `isSemistableTree_fam`: a ball tree with good edges, no bad leaf balls and a root whose residue
  class at `∞` is good gives a semistable Gauss tree in the sense of `W7.IsSemistableTree`.
-/

open Metric

namespace SemistableReduction

namespace S8A

open BallTree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

section Hull

open Classical in
/-- The join of two discs (`∅` if it does not exist). -/
noncomputable def joinFn (D E : Set C) : Set C :=
  if h : ∃ G, IsJoin D E G then Classical.choose h else ∅

omit [IsAlgClosed C] in
lemma joinFn_spec {D E : Set C} (hD : IsDisc D) (hE : IsDisc E) : IsJoin D E (joinFn D E) := by
  have h := exists_isJoin hD hE
  rw [joinFn, dif_pos h]
  exact Classical.choose_spec h

omit [IsAlgClosed C] in
lemma joinFn_self {D : Set C} (hD : IsDisc D) : joinFn D D = D :=
  (joinFn_spec hD hD).unique (isJoin_of_subset hD le_rfl)

open Classical in
/-- The **hull** of a finite set of discs: all joins of pairs. -/
noncomputable def hull (S : Finset (Set C)) : Finset (Set C) :=
  (S ×ˢ S).image fun p ↦ joinFn p.1 p.2

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma mem_hull {S : Finset (Set C)} {G : Set C} :
    G ∈ hull S ↔ ∃ D ∈ S, ∃ E ∈ S, joinFn D E = G := by
  classical
  simp [hull, Finset.mem_image, Finset.mem_product, and_assoc]

omit [IsAlgClosed C] in
lemma subset_hull {S : Finset (Set C)} (hS : ∀ D ∈ S, IsDisc D) : S ⊆ hull S := fun D hD ↦
  mem_hull.2 ⟨D, hD, D, hD, joinFn_self (hS D hD)⟩

omit [IsAlgClosed C] in
/-- The hull of a nonempty finite set of discs is a ball tree. -/
lemma isTree_hull {S : Finset (Set C)} (hS : ∀ D ∈ S, IsDisc D) (hne : S.Nonempty) :
    IsTree (hull S) := by
  have hdisc : ∀ G ∈ hull S, IsDisc G := fun G hG ↦ by
    obtain ⟨D, hD, E, hE, rfl⟩ := mem_hull.1 hG
    exact (joinFn_spec (hS D hD) (hS E hE)).1
  refine ⟨hdisc, hne.mono (subset_hull hS), fun X hX Y hY ↦ ?_⟩
  rcases (hdisc X hX).subset_or_subset_or_disjoint (hdisc Y hY) with h | h | h
  · exact ⟨Y, hY, isJoin_of_subset (hdisc Y hY) h⟩
  · exact ⟨X, hX, (isJoin_of_subset (hdisc X hX) h).symm⟩
  · obtain ⟨D₁, hD₁, E₁, hE₁, rfl⟩ := mem_hull.1 hX
    obtain ⟨D₂, hD₂, E₂, hE₂, rfl⟩ := mem_hull.1 hY
    have hJ₁ := joinFn_spec (hS D₁ hD₁) (hS E₁ hE₁)
    have hJ₂ := joinFn_spec (hS D₂ hD₂) (hS E₂ hE₂)
    have hJ := joinFn_spec (hS D₁ hD₁) (hS D₂ hD₂)
    refine ⟨joinFn D₁ D₂, mem_hull.2 ⟨D₁, hD₁, D₂, hD₂, rfl⟩, ?_⟩
    have h1 : IsJoin (joinFn D₁ E₁) D₂ (joinFn D₁ D₂) :=
      hJ.of_floor (hS D₁ hD₁) hJ₁.1 (hS D₂ hD₂) hJ₁.2.1
        (Set.disjoint_of_subset_right hJ₂.2.1 h)
    exact (h1.symm.of_floor (hS D₂ hD₂) hJ₂.1 hJ₁.1 hJ₂.2.1 h.symm).symm

omit [IsAlgClosed C] in
/-- The hull of a set of discs inside `R` lies inside `R`. -/
lemma subset_of_mem_hull {S : Finset (Set C)} (hS : ∀ D ∈ S, IsDisc D) {R : Set C}
    (hR : IsDisc R) (hSR : ∀ D ∈ S, D ⊆ R) {G : Set C} (hG : G ∈ hull S) : G ⊆ R := by
  obtain ⟨D, hD, E, hE, rfl⟩ := mem_hull.1 hG
  exact (joinFn_spec (hS D hD) (hS E hE)).2.2.2 R hR (hSR D hD) (hSR E hE)

end Hull

section Repair

variable (F) in
/-- The breaks of all segments of `T`. -/
def breaks (T : Finset (Set C)) : Set (Set C) :=
  {G | ∃ D ∈ T, ∃ D' ∈ T, D ⊆ D' ∧ G ∈ Brk F D D'}

lemma finite_breaks (hedge : EdgeRepairFor C F) {T : Finset (Set C)} (hT : ∀ D ∈ T, IsDisc D) :
    (breaks F T).Finite := by
  classical
  refine (Set.Finite.biUnion T.finite_toSet fun D hD ↦ Set.Finite.biUnion T.finite_toSet
    fun D' hD' ↦ (show (if D ⊆ D' then Brk F D D' else ∅).Finite by
      split_ifs with h
      · exact (hedge D D' (hT D hD) (hT D' hD') h).1
      · exact Set.finite_empty)).subset ?_
  rintro G ⟨D, hD, D', hD', hDD', hG⟩
  exact Set.mem_biUnion hD (Set.mem_biUnion hD' (by rw [if_pos hDD']; exact hG))

variable (F) in
open Classical in
/-- **Edge repair** (O10): add the breaks of all segments. -/
noncomputable def repair (T : Finset (Set C)) : Finset (Set C) :=
  if h : (breaks F T).Finite then T ∪ h.toFinset else T

lemma mem_repair {T : Finset (Set C)} (h : (breaks F T).Finite) {X : Set C} :
    X ∈ repair F T ↔ X ∈ T ∨ X ∈ breaks F T := by
  classical
  rw [repair, dif_pos h, Finset.mem_union, Set.Finite.mem_toFinset]

variable (hedge : EdgeRepairFor C F)

include hedge in
/-- **The repaired tree has good edges.** -/
theorem inv_repair {T : Finset (Set C)} {R : Set C} (hT : IsTree T) (hR : R ∈ T)
    (hRT : ∀ D ∈ T, D ⊆ R) : Inv F (repair F T) R := by
  classical
  have hf := finite_breaks hedge hT.disc
  have hmem := fun X ↦ mem_repair (F := F) (T := T) hf (X := X)
  -- every member has a floor in `T`
  have hfloor : ∀ X ∈ repair F T, ∃ D ∈ T, D ⊆ X := fun X hX ↦ by
    rcases (hmem X).1 hX with h | ⟨D, hD, D', -, -, hG⟩
    · exact ⟨X, h, le_rfl⟩
    · exact ⟨D, hD, hG.2.1.1⟩
  have htree : IsTree (repair F T) := by
    rw [repair, dif_pos hf]
    refine hT.union_of_floor (fun G hG ↦ ?_) fun G hG ↦ ?_
    · rw [Set.Finite.mem_toFinset] at hG
      obtain ⟨D, hD, D', hD', hDD', hG'⟩ := hG
      exact hG'.1
    · rw [Set.Finite.mem_toFinset] at hG
      obtain ⟨D, hD, D', hD', hDD', hG'⟩ := hG
      exact ⟨D, hD, hG'.2.1.1⟩
  have hroot : ∀ X ∈ repair F T, X ⊆ R := fun X hX ↦ by
    rcases (hmem X).1 hX with h | ⟨D, -, D', hD', -, hG⟩
    · exact hRT X h
    · exact hG.2.2.1.1.trans (hRT D' hD')
  refine ⟨htree, (hmem R).2 (.inl hR), hroot, fun E hE G hG hEG hmin ↦ ?_⟩
  obtain ⟨D, hD, hDE⟩ := hfloor E hE
  refine ((hedge D R (hT.disc D hD) (hT.disc R hR) (hRT D hD)).2 E G (htree.disc E hE)
    (htree.disc G hG) hDE hEG (hroot G hG)) fun X hX hX' ↦ ?_
  exact hmin X ((hmem X).2 (.inr ⟨D, hD, R, hR, hRT D hD, hX⟩)) hX'

end Repair

section Semistable

variable {T : Finset (Set C)} (hTd : ∀ D ∈ T, IsDisc D)

omit [IsAlgClosed C] in
lemma famDisc_ssubset_of_isEdge (hTd : ∀ D ∈ T, IsDisc D) {j m : Fin T.card}
    (h : TreeBridge.IsEdge (famA hTd) (famC hTd) j m) : famDisc T j ⊂ famDisc T m :=
  ⟨(discLE_fam_iff hTd).1 h.1, fun h' ↦ h.2.1
    (famDisc_injective (le_antisymm ((discLE_fam_iff hTd).1 h.1) h'))⟩

/-- **Semistable Gauss trees from good ball trees.** A ball tree with good edges, without bad leaf
balls, whose root is `closedBall 0 ‖ρ‖` with good residue class at `∞` (`InftyGoodFor`), gives a
semistable Gauss tree. -/
theorem isSemistableTree_fam {R : Set C} (hT : Inv F T R) (hbad : badLeaves F T = ∅) {ρ : C}
    (hρ : ρ ≠ 0) (hRρ : R = closedBall 0 ‖ρ‖)
    (hinf : ∀ (c : C) (hc : c ≠ 0), ‖ρ‖ ≤ ‖c‖ → InftyChartGood F 0 hc) :
    W7.IsSemistableTree (famA hT.tree.disc) (famC hT.tree.disc) (famC_ne_zero hT.tree.disc) F := by
  set hTd := hT.tree.disc
  have hred := isReduced_fam hTd
  refine ⟨fun j m he h1 h0 P' hmax hP ↦ ?_, fun i β hβ hdir P' hmax hP ↦ ?_,
    fun i hi P' hmax hP ↦ ?_⟩
  · -- nodes: the edges of the tree are good
    have hsub := famDisc_ssubset_of_isEdge hTd he
    have hmin : ∀ X ∈ T, ¬ (famDisc T j ⊂ X ∧ X ⊂ famDisc T m) := by
      rintro X hX ⟨hX1, hX2⟩
      obtain ⟨k, rfl⟩ := exists_famDisc hX
      rcases he.2.2 k ((discLE_fam_iff hTd).2 hX1.1) ((discLE_fam_iff hTd).2 hX2.1) with
        rfl | rfl
      · exact hX1.2 le_rfl
      · exact hX2.2 le_rfl
    have hg := hT.edge _ (famDisc_mem j) _ (famDisc_mem m) hsub hmin
    have hjm : famA hTd j ∈ closedBall (famA hTd m) ‖famC hTd m‖ := by
      rw [← famDisc_eq hTd]
      exact hsub.1 (by rw [famDisc_eq hTd]; exact BallTree.mem_closedBall'.2 (by simp))
    refine hg (famA hTd j) (famC hTd m) (famC hTd j / famC hTd m) (famC_ne_zero hTd m) h1 h0
      ?_ ?_ P' hmax hP
    · rw [famDisc_eq hTd, mul_div_cancel₀ _ (famC_ne_zero hTd m)]
    · rw [famDisc_eq hTd]
      exact IsUltrametricDist.closedBall_eq_of_mem hjm
  · -- smooth points: the residue ball is a good leaf ball
    have hc := famC_ne_zero hTd i
    have hb : (famA hTd i + famC hTd i * β) ∈ closedBall (famA hTd i) ‖famC hTd i‖ := by
      rw [BallTree.mem_closedBall']
      simp only [add_sub_cancel_left, norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) hβ
    have hleaf : IsLeafBall T (ball (famA hTd i + famC hTd i * β) ‖famC hTd i‖) := by
      refine ⟨famA hTd i, (famA hTd i + famC hTd i * β), famC hTd i, hc,
        famDisc_eq hTd i ▸ famDisc_mem i, hb, rfl,
        fun E hE hEB ↦ ?_⟩
      obtain ⟨l, rfl⟩ := exists_famDisc hE
      have hli : famDisc T l ⊆ famDisc T i := by
        rw [famDisc_eq hTd i]
        exact hEB.trans (ball_subset_closedBall_of_mem hb)
      have hne : l ≠ i := by
        rintro rfl
        -- the disc is not contained in its residue ball
        have hx : famA hTd l + famC hTd l * (β + 1) ∈ famDisc T l := by
          rw [famDisc_eq hTd, BallTree.mem_closedBall']
          simp only [add_sub_cancel_left, norm_mul]
          refine mul_le_of_le_one_right (norm_nonneg _) ?_
          exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hβ (by simp))
        have := BallTree.mem_ball'.1 (hEB hx)
        simp only [show famA hTd l + famC hTd l * (β + 1) - (famA hTd l + famC hTd l * β) =
          famC hTd l by ring] at this
        exact lt_irrefl _ this
      obtain ⟨k, hk, hlk⟩ := TreeBridge.exists_edge_of_lt hred ((discLE_fam_iff hTd).2 hli) hne
      have hki := famDisc_ssubset_of_isEdge hTd hk
      obtain ⟨z, hz⟩ := (hTd _ hE).nonempty
      have hzk : z ∈ famDisc T k := (discLE_fam_iff hTd).1 hlk hz
      rw [famDisc_eq hTd k] at hzk hki
      rw [famDisc_eq hTd i] at hki
      have hkB := closedBall_subset_ball_of_mem hzk (hEB hz) (norm_lt_of_ssubset hki)
      have hak : famA hTd k ∈ closedBall (famA hTd k) ‖famC hTd k‖ :=
        BallTree.mem_closedBall'.2 (by simp)
      have h1 := BallTree.mem_ball'.1 (hkB hak)
      have h2 := hdir k hk
      rw [norm_sub_rev] at h2
      exact lt_irrefl _ (h2 ▸ h1)
    have hgood : BallGood F (ball (famA hTd i + famC hTd i * β) ‖famC hTd i‖) := by
      by_contra hb'
      have : ball (famA hTd i + famC hTd i * β) ‖famC hTd i‖ ∈ badLeaves F T := ⟨hleaf, hb'⟩
      rw [hbad] at this
      exact this
    exact hgood (famA hTd i + famC hTd i * β) _ hc rfl P' hmax hP
  · -- the root: its residue class at `∞` is good
    obtain ⟨ρi, rfl⟩ := exists_famDisc hT.root_mem
    have hiρ : i = ρi := by
      by_contra hne
      have hle : GaussTree.DiscLE ν (famA hTd) (famC hTd) i ρi :=
        (discLE_fam_iff hTd).2 (hT.root _ (famDisc_mem i))
      obtain ⟨k, hk, -⟩ := TreeBridge.exists_edge_of_lt' hred hle hne
      exact hi k hk
    subst hiρ
    have h0 : (0 : C) ∈ famDisc T i := by
      rw [hRρ]; exact BallTree.mem_closedBall'.2 (by simp)
    have ha := famA_eq_zero hTd h0
    have hR := hRρ
    rw [famDisc_eq hTd] at hR
    obtain ⟨h1, -⟩ := (closedBall_eq_closedBall_iff' (famC_ne_zero hTd i) hρ).1 hR
    have hinf' := hinf _ (famC_ne_zero hTd i) h1.ge
    revert P'
    rw [ha]
    exact hinf'

end Semistable

end S8A

end SemistableReduction
