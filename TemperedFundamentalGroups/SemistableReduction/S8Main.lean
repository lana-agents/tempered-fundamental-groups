/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Transport

/-!
# S8.A: `W7.Statement` from the local interfaces

Blueprint §9.12, O6. **`W7.statement_of_interfaces`**: the local inputs `S8A.GaloisInputs`
(S8.B, R5, finiteness of bad balls, the residue class at `∞`, EdgeRepair; transport is
proved, `Transport.transportFor`) and the
Galois reduction `S8A.S8CReduction` imply `W7.Statement`. All of them are explicit hypotheses,
recorded as open in Blueprint §9.12 (O6.1–O6.6, O10).

Construction ([AW §2.5], canonical): for the Galois extension `F` of S8.C, the discs of `V₀` and
a large root `R = closedBall 0 ‖ρ‖` (whose residue class at `∞` is good); their hull; its edge
repair (all edges good); then the improvement step until no bad leaf ball is left. Every stage
commutes with isometric automorphisms `τ` of `C` extending to `F` (`S8Equivariance`), so a
`τ`-stable `V₀` gives a `τ`-stable `V`.
-/

universe u v

open Metric

namespace SemistableReduction

open BallTree S8A

/-- **The empty family**: the hull of the given discs and a root. -/
theorem W7.statement_empty {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
    {ι₀ : Type} [Finite ι₀] (a₀ c₀ : ι₀ → C) (hc₀ : ∀ k, c₀ k ≠ 0) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a c : ι → C) (_ : ∀ i, c i ≠ 0),
      GaussTree.IsConvex (NormedField.valuation (K := C)) a c ∧
      GaussTree.IsReduced (NormedField.valuation (K := C)) a c ∧
      W7.DiscsLE a₀ c₀ a c ∧
      ∀ τ : C ≃+* C, (∀ z, ‖τ z‖ = ‖z‖) →
        W7.DiscsLE (fun k ↦ τ (a₀ k)) c₀ a₀ c₀ → W7.DiscsLE (fun i ↦ τ (a i)) c a c := by
  classical
  haveI := Fintype.ofFinite ι₀
  obtain ⟨ρ, hρ⟩ := NormedField.exists_lt_norm C (∑ k, (‖a₀ k‖ + ‖c₀ k‖))
  have hρ0 : ρ ≠ 0 := norm_pos_iff.1 ((Finset.sum_nonneg fun k _ ↦ by positivity).trans_lt hρ)
  set R : Set C := closedBall 0 ‖ρ‖ with hRdef
  have hRd : IsDisc R := ⟨0, ρ, hρ0, rfl⟩
  set S₀ : Finset (Set C) := Finset.univ.image fun k ↦ closedBall (a₀ k) ‖c₀ k‖
  set S : Finset (Set C) := insert R S₀
  have hSd : ∀ D ∈ S, IsDisc D := fun D hD ↦ by
    rcases Finset.mem_insert.1 hD with rfl | hD
    · exact hRd
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hD
      exact ⟨a₀ k, c₀ k, hc₀ k, rfl⟩
  set T := hull S
  have hT : IsTree T := isTree_hull hSd ⟨R, Finset.mem_insert_self _ _⟩
  haveI : Nonempty (Fin T.card) := ⟨⟨0, Finset.card_pos.2 hT.nonempty⟩⟩
  refine ⟨Fin T.card, inferInstance, inferInstance, famA hT.disc, famC hT.disc,
    famC_ne_zero hT.disc, isConvex_fam _ hT, isReduced_fam _,
    discsLE_fam _ hc₀ fun k ↦ subset_hull hSd (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ k))), ?_⟩
  intro τ hτ hV₀
  have hS : S.image (img τ) = S := by
    refine Finset.eq_of_subset_of_card_le (fun G hG ↦ ?_) ?_
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 hG
      rcases Finset.mem_insert.1 hD with rfl | hD
      · rw [hRdef, img_closedBall hτ, map_zero]
        exact Finset.mem_insert_self _ _
      · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hD
        obtain ⟨k', h1, h2⟩ := hV₀ k
        rw [img_closedBall hτ]
        have : closedBall (τ (a₀ k)) ‖c₀ k‖ = closedBall (a₀ k') ‖c₀ k'‖ := by
          refine (closedBall_eq_closedBall_iff' (hc₀ k) (hc₀ k')).2 ⟨h1.symm, ?_⟩
          rw [norm_sub_rev, ← h1]
          exact h2
        rw [this]
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k'))
    · rw [Finset.card_image_of_injective _ (img_injective τ)]
  have hT' : T.image (img τ) = T := by
    rw [← hull_image hτ hSd, hS]
  intro i
  have hmem : img τ (famDisc T i) ∈ T := by
    have := Finset.mem_image_of_mem (img τ) (famDisc_mem (T := T) i)
    rwa [hT'] at this
  obtain ⟨j, hj⟩ := exists_famDisc hmem
  rw [famDisc_eq hT.disc, famDisc_eq hT.disc, img_closedBall hτ] at hj
  obtain ⟨h1, h2⟩ := (closedBall_eq_closedBall_iff' (famC_ne_zero _ j)
    (famC_ne_zero _ i)).1 hj
  exact ⟨j, h1, h2⟩

/-- **W7 from the local interfaces** ([AW §2.5] + S8.C). -/
theorem W7.statement_of_interfaces (hG : GaloisInputs.{u}) (hC : S8CReduction.{u, v}) :
    W7.Statement.{u, v} := by
  intro C _ _ _ _ p hp hp1 κ _ F' _ _ _ _ _ hdef ι₀ _ a₀ c₀ hc₀
  rcases isEmpty_or_nonempty κ with hκ | hκ
  · obtain ⟨ι, h1, h2, a, c, hc, h3, h4, h5, h6⟩ := W7.statement_empty a₀ c₀ hc₀
    exact ⟨ι, h1, h2, a, c, hc, h3, h4, h5, fun k ↦ isEmptyElim k, fun τ hτ _ ↦ h6 τ hτ⟩
  obtain ⟨F, _, _, _, _, _, _, hdefF, hdesc, hlift⟩ := hC C p hp hp1 κ F' hκ hdef
  have hmin := hG.s8b C p hp hp1 F hdefF
  have hR5 := hG.r5 C p hp hp1 F hdefF
  have hfin := hG.finiteBad C p hp hp1 F hdefF
  obtain ⟨R₀, hR₀⟩ := hG.infty C p hp hp1 F hdefF
  have hrep := hG.edgeRepair C p hp hp1 F hdefF
  have htr : TransportFor C F := Transport.transportFor
  classical
  -- the root
  obtain ⟨ρ, hρ⟩ := NormedField.exists_lt_norm C (max R₀ (∑ k, (‖a₀ k‖ + ‖c₀ k‖)))
  have hsum : ∀ k, ‖a₀ k‖ + ‖c₀ k‖ ≤ ‖ρ‖ := fun k ↦
    (Finset.single_le_sum (f := fun k ↦ ‖a₀ k‖ + ‖c₀ k‖) (fun k _ ↦ by positivity)
      (Finset.mem_univ k)).trans ((le_max_right _ _).trans hρ.le)
  have hρ0 : ρ ≠ 0 := by
    have h0 : (0 : ℝ) ≤ max R₀ (∑ k, (‖a₀ k‖ + ‖c₀ k‖)) :=
      (Finset.sum_nonneg fun k _ ↦ by positivity).trans (le_max_right _ _)
    exact norm_pos_iff.1 (h0.trans_lt hρ)
  set R : Set C := closedBall 0 ‖ρ‖ with hRdef
  have hRd : IsDisc R := ⟨0, ρ, hρ0, rfl⟩
  set S₀ : Finset (Set C) := Finset.univ.image fun k ↦ closedBall (a₀ k) ‖c₀ k‖
  set S : Finset (Set C) := insert R S₀
  have hSd : ∀ D ∈ S, IsDisc D := fun D hD ↦ by
    rcases Finset.mem_insert.1 hD with rfl | hD
    · exact hRd
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hD
      exact ⟨a₀ k, c₀ k, hc₀ k, rfl⟩
  have hSR : ∀ D ∈ S, D ⊆ R := fun D hD ↦ by
    rcases Finset.mem_insert.1 hD with rfl | hD
    · exact le_rfl
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hD
      refine closedBall_subset_closedBall_iff'.2 ⟨?_, ?_⟩
      · linarith [hsum k, norm_nonneg (a₀ k)]
      · rw [sub_zero]
        linarith [hsum k, norm_nonneg (c₀ k)]
  -- the hull, the repair and the iteration
  set T₀ := hull S
  have hT₀ : IsTree T₀ := isTree_hull hSd ⟨R, Finset.mem_insert_self _ _⟩
  have hRT₀ : R ∈ T₀ := subset_hull hSd (Finset.mem_insert_self _ _)
  have hroot₀ : ∀ D ∈ T₀, D ⊆ R := fun D hD ↦ subset_of_mem_hull hSd hRd hSR hD
  set T₁ := repair F T₀
  have hI₁ := inv_repair hrep hT₀ hRT₀ hroot₀
  have hex := exists_badLeaves_eq_empty hfin hmin hR5 hI₁
  set T := (step F)^[Nat.find hex] T₁
  have hI : Inv F T R := inv_iterate_step hfin hmin hI₁ _
  have hbad : badLeaves F T = ∅ := Nat.find_spec hex
  have hST : ∀ D ∈ S, D ∈ T := fun D hD ↦ subset_iterate_step _
    ((mem_repair (finite_breaks hrep hT₀.disc)).2 (.inl (subset_hull hSd hD)))
  haveI : Nonempty (Fin T.card) := ⟨⟨0, Finset.card_pos.2 hI.tree.nonempty⟩⟩
  refine ⟨Fin T.card, inferInstance, inferInstance, famA hI.tree.disc, famC hI.tree.disc,
    famC_ne_zero hI.tree.disc, isConvex_fam _ hI.tree, isReduced_fam _,
    discsLE_fam _ hc₀ fun k ↦ hST _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_univ k))), fun k ↦ ?_, ?_⟩
  · -- semistability for `F`, then for the family
    refine hdesc _ _ _ _ (isSemistableTree_fam hI hbad hρ0 rfl fun c hc h1 ↦
      hR₀ c hc ?_) k
    exact (le_max_left _ _).trans (hρ.le.trans h1)
  · -- equivariance
    intro τ hτ hσ hV₀
    obtain ⟨σ'', hσ''⟩ := hlift τ hτ hσ
    obtain ⟨hball, hedge⟩ := htr τ hτ σ'' hσ''
    -- the input discs are `τ`-stable
    have hS : S.image (img τ) = S := by
      refine Finset.eq_of_subset_of_card_le (fun G hG ↦ ?_) ?_
      · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 hG
        rcases Finset.mem_insert.1 hD with rfl | hD
        · rw [hRdef, img_closedBall hτ, map_zero]
          exact Finset.mem_insert_self _ _
        · obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hD
          obtain ⟨k', h1, h2⟩ := hV₀ k
          rw [img_closedBall hτ]
          have : closedBall (τ (a₀ k)) ‖c₀ k‖ = closedBall (a₀ k') ‖c₀ k'‖ := by
            refine (closedBall_eq_closedBall_iff' (hc₀ k) (hc₀ k')).2 ⟨h1.symm, ?_⟩
            rw [norm_sub_rev, ← h1]
            exact h2
          rw [this]
          exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ k'))
      · rw [Finset.card_image_of_injective _ (img_injective τ)]
    have hT₀' : T₀.image (img τ) = T₀ := by
      rw [← hull_image hτ hSd, hS]
    have hT₁' : T₁.image (img τ) = T₁ := by
      rw [← repair_image hτ hedge hrep hT₀.disc, hT₀']
    have hTn : ∀ n, ((step F)^[n] T₁).image (img τ) = (step F)^[n] T₁ := by
      intro n
      induction n with
      | zero => exact hT₁'
      | succ n ih =>
        rw [Function.iterate_succ_apply', ← step_image hτ hball hedge hfin hmin
          (inv_iterate_step hfin hmin hI₁ n).tree.disc, ih]
    intro i
    have hmem : img τ (famDisc T i) ∈ T := by
      have h := hTn (Nat.find hex)
      change T.image (img τ) = T at h
      have := Finset.mem_image_of_mem (img τ) (famDisc_mem (T := T) i)
      rwa [h] at this
    obtain ⟨j, hj⟩ := exists_famDisc hmem
    rw [famDisc_eq hI.tree.disc, famDisc_eq hI.tree.disc, img_closedBall hτ] at hj
    obtain ⟨h1, h2⟩ := (closedBall_eq_closedBall_iff' (famC_ne_zero _ j)
      (famC_ne_zero _ i)).1 hj
    exact ⟨j, h1, h2⟩

end SemistableReduction
