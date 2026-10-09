/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Assembly

/-!
# S8.A: equivariance of the canonical construction

Blueprint §9.12, O6. Let `τ` be an isometric ring automorphism of `C`. It acts on discs and balls
by images (`img τ`), preserving discs, inclusions and joins. If goodness of balls and edges is
`τ`-invariant (`TransportFor`, applied to a `τ`-semilinear automorphism of `F`), every step of the
canonical construction commutes with `τ`: `hull_image`, `repair_image`, `step_image`.
-/

open Metric

namespace SemistableReduction

namespace S8A

open BallTree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section Image

variable (τ : C ≃+* C)

/-- The action of `τ` on subsets of `C`. -/
def img (D : Set C) : Set C := τ '' D

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma img_injective : Function.Injective (img τ) :=
  Set.image_injective.2 τ.injective

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma img_subset_iff {D E : Set C} : img τ D ⊆ img τ E ↔ D ⊆ E :=
  Set.image_subset_image_iff τ.injective

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma img_ssubset_iff {D E : Set C} : img τ D ⊂ img τ E ↔ D ⊂ E := by
  simp only [Set.ssubset_def, img_subset_iff]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma img_symm_img (D : Set C) : img τ.symm (img τ D) = D := by
  simp [img, Set.image_image]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma img_img_symm (D : Set C) : img τ (img τ.symm D) = D := by
  simp [img, Set.image_image]

variable {τ} (hτ : ∀ z, ‖τ z‖ = ‖z‖)
include hτ

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma norm_symm (z : C) : ‖τ.symm z‖ = ‖z‖ := by
  rw [← hτ, RingEquiv.apply_symm_apply]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma img_closedBall (a : C) (r : ℝ) : img τ (closedBall a r) = closedBall (τ a) r := by
  ext x
  simp only [img, Set.mem_image, BallTree.mem_closedBall']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← map_sub, hτ]
  · intro hx
    refine ⟨τ.symm x, ?_, τ.apply_symm_apply x⟩
    have := hτ (τ.symm x - a)
    rw [map_sub, RingEquiv.apply_symm_apply] at this
    rw [← this]
    exact hx

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma img_ball (a : C) (r : ℝ) : img τ (ball a r) = ball (τ a) r := by
  ext x
  simp only [img, Set.mem_image, BallTree.mem_ball']
  constructor
  · rintro ⟨y, hy, rfl⟩
    rwa [← map_sub, hτ]
  · intro hx
    refine ⟨τ.symm x, ?_, τ.apply_symm_apply x⟩
    have := hτ (τ.symm x - a)
    rw [map_sub, RingEquiv.apply_symm_apply] at this
    rw [← this]
    exact hx

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma isDisc_img {D : Set C} (hD : IsDisc D) : IsDisc (img τ D) := by
  obtain ⟨a, c, hc, rfl⟩ := hD
  refine ⟨τ a, τ c, by simpa using hc, ?_⟩
  rw [img_closedBall hτ, hτ]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma isDisc_img_iff {D : Set C} : IsDisc (img τ D) ↔ IsDisc D := by
  refine ⟨fun h ↦ ?_, isDisc_img hτ⟩
  have := isDisc_img (τ := τ.symm) (norm_symm hτ) h
  rwa [img_symm_img] at this

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma isJoin_img {D E G : Set C} (h : IsJoin D E G) : IsJoin (img τ D) (img τ E) (img τ G) := by
  refine ⟨isDisc_img hτ h.1, (img_subset_iff τ).2 h.2.1, (img_subset_iff τ).2 h.2.2.1,
    fun G' hG' h1 h2 ↦ ?_⟩
  rw [← img_img_symm τ G', img_subset_iff]
  refine h.2.2.2 _ (isDisc_img (norm_symm hτ) hG') ?_ ?_
  · rw [← img_symm_img τ D]
    exact (img_subset_iff τ.symm).2 h1
  · rw [← img_symm_img τ E]
    exact (img_subset_iff τ.symm).2 h2

omit [IsAlgClosed C] in
lemma joinFn_img {D E : Set C} (hD : IsDisc D) (hE : IsDisc E) :
    joinFn (img τ D) (img τ E) = img τ (joinFn D E) :=
  (joinFn_spec (isDisc_img hτ hD) (isDisc_img hτ hE)).unique (isJoin_img hτ (joinFn_spec hD hE))

omit [IsAlgClosed C] in
/-- **The hull commutes with `τ`.** -/
lemma hull_image [DecidableEq (Set C)] {S : Finset (Set C)} (hS : ∀ D ∈ S, IsDisc D) :
    hull (S.image (img τ)) = (hull S).image (img τ) := by
  ext G
  simp only [mem_hull, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨D, hD, rfl⟩, _, ⟨E, hE, rfl⟩, rfl⟩
    exact ⟨joinFn D E, ⟨D, hD, E, hE, rfl⟩, (joinFn_img hτ (hS D hD) (hS E hE)).symm⟩
  · rintro ⟨_, ⟨D, hD, E, hE, rfl⟩, rfl⟩
    exact ⟨_, ⟨D, hD, rfl⟩, _, ⟨E, hE, rfl⟩, joinFn_img hτ (hS D hD) (hS E hE)⟩

end Image

section Transport

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  {τ : C ≃+* C} (hτ : ∀ z, ‖τ z‖ = ‖z‖)
  (hball : ∀ B : Set C, BallGood F (img τ B) ↔ BallGood F B)
  (hedge : ∀ E G : Set C, EdgeGood F (img τ E) (img τ G) ↔ EdgeGood F E G)

include hτ hedge in
lemma brk_img {D D' : Set C} : Brk F (img τ D) (img τ D') = img τ '' Brk F D D' := by
  ext G
  constructor
  · rintro ⟨hG, h1, h2, hno⟩
    refine ⟨img τ.symm G, ⟨(isDisc_img_iff hτ).1 (by rwa [img_img_symm]),
      by rwa [← img_ssubset_iff τ, img_img_symm], by rwa [← img_ssubset_iff τ, img_img_symm],
      fun ⟨G₁, G₂, hG₁, hG₂, hD1, h1', h2', hD2, hgood⟩ ↦ hno ⟨img τ G₁, img τ G₂,
        isDisc_img hτ hG₁, isDisc_img hτ hG₂, (img_subset_iff τ).2 hD1,
        by rw [← img_img_symm τ G]; exact (img_ssubset_iff τ).2 h1',
        by rw [← img_img_symm τ G]; exact (img_ssubset_iff τ).2 h2',
        (img_subset_iff τ).2 hD2, (hedge G₁ G₂).2 hgood⟩⟩, img_img_symm τ G⟩
  · rintro ⟨G, ⟨hG, h1, h2, hno⟩, rfl⟩
    refine ⟨isDisc_img hτ hG, (img_ssubset_iff τ).2 h1, (img_ssubset_iff τ).2 h2,
      fun ⟨G₁, G₂, hG₁, hG₂, hD1, h1', h2', hD2, hgood⟩ ↦ hno ⟨img τ.symm G₁, img τ.symm G₂,
        (isDisc_img_iff hτ).1 (by rwa [img_img_symm]),
        (isDisc_img_iff hτ).1 (by rwa [img_img_symm]),
        by rwa [← img_subset_iff τ, img_img_symm],
        by rwa [← img_ssubset_iff τ, img_img_symm],
        by rwa [← img_ssubset_iff τ, img_img_symm],
        by rwa [← img_subset_iff τ, img_img_symm],
        (hedge _ _).1 (by rwa [img_img_symm, img_img_symm])⟩⟩

include hτ hedge in
lemma breaks_img [DecidableEq (Set C)] {T : Finset (Set C)} :
    breaks F (T.image (img τ)) = img τ '' breaks F T := by
  ext G
  simp only [breaks, Finset.mem_image, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨D, hD, rfl⟩, _, ⟨D', hD', rfl⟩, hDD', hG⟩
    rw [brk_img hτ hedge] at hG
    obtain ⟨G', hG', rfl⟩ := hG
    exact ⟨G', ⟨D, hD, D', hD', (img_subset_iff τ).1 hDD', hG'⟩, rfl⟩
  · rintro ⟨G', ⟨D, hD, D', hD', hDD', hG'⟩, rfl⟩
    refine ⟨_, ⟨D, hD, rfl⟩, _, ⟨D', hD', rfl⟩, (img_subset_iff τ).2 hDD', ?_⟩
    rw [brk_img hτ hedge]
    exact ⟨G', hG', rfl⟩

include hτ hedge in
/-- **The edge repair commutes with `τ`.** -/
lemma repair_image [DecidableEq (Set C)] (hrep : EdgeRepairFor C F) {T : Finset (Set C)}
    (hT : ∀ D ∈ T, IsDisc D) : repair F (T.image (img τ)) = (repair F T).image (img τ) := by
  have hT' : ∀ D ∈ T.image (img τ), IsDisc D := fun D hD ↦ by
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.1 hD
    exact isDisc_img hτ (hT D' hD')
  ext G
  rw [mem_repair (finite_breaks hrep hT'), breaks_img hτ hedge,
    Finset.mem_image (s := repair F T)]
  constructor
  · rintro (h | ⟨G', hG', rfl⟩)
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 h
      exact ⟨D, (mem_repair (finite_breaks hrep hT)).2 (.inl hD), rfl⟩
    · exact ⟨G', (mem_repair (finite_breaks hrep hT)).2 (.inr hG'), rfl⟩
  · rintro ⟨G', hG', rfl⟩
    rcases (mem_repair (finite_breaks hrep hT)).1 hG' with h | h
    · exact .inl (Finset.mem_image_of_mem _ h)
    · exact .inr ⟨G', h, rfl⟩

omit [IsUltrametricDist C] [IsAlgClosed C] in
include hτ in
lemma isLeafBall_img [DecidableEq (Set C)] {T : Finset (Set C)} {B : Set C}
    (h : IsLeafBall T B) : IsLeafBall (T.image (img τ)) (img τ B) := by
  obtain ⟨a, b, c, hc, hP, hb, rfl, hleaf⟩ := h
  refine ⟨τ a, τ b, τ c, by simpa using hc, ?_, ?_, ?_, fun E hE hEB ↦ ?_⟩
  · rw [hτ, ← img_closedBall hτ]
    exact Finset.mem_image_of_mem _ hP
  · rw [hτ, ← img_closedBall hτ]
    exact Set.mem_image_of_mem _ hb
  · rw [hτ, img_ball hτ]
  · obtain ⟨E, hE', rfl⟩ := Finset.mem_image.1 hE
    exact hleaf E hE' ((img_subset_iff τ).1 hEB)

include hτ hball in
lemma badLeaves_img [DecidableEq (Set C)] {T : Finset (Set C)} :
    badLeaves F (T.image (img τ)) = img τ '' badLeaves F T := by
  ext B
  constructor
  · rintro ⟨hB, hbad⟩
    refine ⟨img τ.symm B, ⟨?_, fun h ↦ hbad ?_⟩, img_img_symm τ B⟩
    · have := isLeafBall_img (norm_symm hτ) hB
      rwa [Finset.image_image, show img τ.symm ∘ img τ = id from
        funext (img_symm_img τ), Finset.image_id] at this
    · rw [← img_img_symm τ B]
      exact (hball _).2 h
  · rintro ⟨B, ⟨hB, hbad⟩, rfl⟩
    exact ⟨isLeafBall_img hτ hB, fun h ↦ hbad ((hball B).1 h)⟩

include hτ hedge in
lemma isMinExh_img {b c : C} (hc : c ≠ 0) {D : Set C} (h : IsMinExh F b hc D) :
    IsMinExh F (τ b) (c := τ c) (by simpa using hc) (img τ D) := by
  obtain ⟨hD, hDB, hg, hmin⟩ := h
  have hB : img τ (ball b ‖c‖) = ball (τ b) ‖τ c‖ := by rw [hτ, img_ball hτ]
  have hP : img τ (closedBall b ‖c‖) = closedBall (τ b) ‖τ c‖ := by rw [hτ, img_closedBall hτ]
  refine ⟨isDisc_img hτ hD, hB ▸ (img_subset_iff τ).2 hDB, hP ▸ (hedge _ _).2 hg,
    fun D' hD' h1 h2 ↦ ?_⟩
  rw [← img_img_symm τ D', img_subset_iff]
  refine hmin _ ((isDisc_img_iff hτ).1 (by rwa [img_img_symm])) ?_ ?_
  · rw [← img_subset_iff τ, img_img_symm, hB]
    exact h1
  · rw [← hedge, img_img_symm, hP]
    exact h2

include hτ hedge in
lemma dmin_img {b c : C} (hc : c ≠ 0) (hmin : S8BMinFor C F)
    (hbad : ¬ BallGood F (ball b ‖c‖)) :
    dmin F (img τ (ball b ‖c‖)) = img τ (dmin F (ball b ‖c‖)) := by
  obtain ⟨D, hD⟩ := hmin b c hc hbad
  have h1 := dmin_spec hc hD
  have h2 := isMinExh_img hτ hedge hc h1
  rw [show img τ (ball b ‖c‖) = ball (τ b) ‖τ c‖ by rw [hτ, img_ball hτ]]
  exact dmin_eq _ h2

include hτ hball hedge in
/-- **The improvement step commutes with `τ`.** -/
lemma step_image [DecidableEq (Set C)] (hfin : FiniteBadFor C F) (hmin : S8BMinFor C F)
    {T : Finset (Set C)} (hT : ∀ D ∈ T, IsDisc D) :
    step F (T.image (img τ)) = (step F T).image (img τ) := by
  have hT' : ∀ D ∈ T.image (img τ), IsDisc D := fun D hD ↦ by
    obtain ⟨D', hD', rfl⟩ := Finset.mem_image.1 hD
    exact isDisc_img hτ (hT D' hD')
  -- `dmin` commutes with `τ` on bad leaf balls
  have hd : ∀ B ∈ badLeaves F T, dmin F (img τ B) = img τ (dmin F B) := fun B hB ↦ by
    obtain ⟨⟨a, b, c, hc, -, -, rfl, -⟩, hbad⟩ := hB
    exact dmin_img hτ hedge hc hmin hbad
  ext G
  rw [mem_step (finite_badLeaves hfin hT'), badLeaves_img hτ hball,
    Finset.mem_image (s := step F T)]
  constructor
  · rintro (h | ⟨_, ⟨B, hB, rfl⟩, rfl⟩)
    · obtain ⟨D, hD, rfl⟩ := Finset.mem_image.1 h
      exact ⟨D, (mem_step (finite_badLeaves hfin hT)).2 (.inl hD), rfl⟩
    · exact ⟨dmin F B, (mem_step (finite_badLeaves hfin hT)).2 (.inr ⟨B, hB, rfl⟩),
        (hd B hB).symm⟩
  · rintro ⟨G', hG', rfl⟩
    rcases (mem_step (finite_badLeaves hfin hT)).1 hG' with h | ⟨B, hB, rfl⟩
    · exact .inl (Finset.mem_image_of_mem _ h)
    · exact .inr ⟨img τ B, ⟨B, hB, rfl⟩, hd B hB⟩

end Transport

end S8A

end SemistableReduction
