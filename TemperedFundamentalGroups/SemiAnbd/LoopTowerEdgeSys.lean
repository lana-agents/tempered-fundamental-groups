/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.LoopTowerBounded

/-!
# Edge systems of the loop tower are translates of the base edge system

The edge analogue of `LoopTower.exists_smul_baseSys`: for a compact vertex group `Π`, every system
of edge kind of the tree tower of a loop of groups is `h • baseEdgeSys` (König's lemma over the
finite edge cosets `k B_N`), and its stabilizer is a conjugate of the image of the second branch
`b₁(E) ⊆ Π` ([SemiAnbd] Thm 3.7(iii): the edge-like subgroups are the conjugates of the images of
the `π₁(G_e)`).

* `LoopTower.baseEdgeSys`: the system of the edge cosets `B` (from `G` to `t G`);
* **`LoopTower.exists_smul_baseEdgeSys`**: every system of edge kind is a translate of it;
* **`LoopTower.stab_baseEdgeSys_eq`**: its stabilizer is the image of `b₁(E)` (for closed `b₁(E)`
  and levels separating points);
* **`LoopTower.stab_edge_eq_conj`**: every edge-like subgroup is a conjugate of it.
-/

open CategoryTheory HNNExtension
open scoped Pointwise

namespace TemperedFundamentalGroups

namespace LoopTower

noncomputable section

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [Group E] {b₀ b₁ : E →* Pv}

variable (b₀ b₁) in
/-- The base edge system: the edge coset `B` (from `G` to `t G`) at every level. -/
def baseEdgeSys : (tower b₀ b₁).Sys :=
  ⟨fun N ↦ .inr ((1 : levelGroup N) : _ ⧸ edgeSubgroup (levelEquiv N)), fun {N N'} f ↦ by
    change vertexMap f.le (Sum.inr (QuotientGroup.mk 1)) = Sum.inr (QuotientGroup.mk 1)
    rw [vertexMap_inr, map_one]⟩

/-- The representatives of the edge coset of a system at level `N`. -/
def edgeReps (s : (tower b₀ b₁).Sys) (N : Level b₀ b₁) : Type u :=
  {x : levelGroup N // (Sum.inr (x : _ ⧸ edgeSubgroup (levelEquiv N)) : BSVertex _) = s.1 N}

lemma edgeReps_map (s : (tower b₀ b₁).Sys) {N N' : Level b₀ b₁} (f : N ⟶ N')
    (x : edgeReps s N) :
    (Sum.inr ((levelMap f.le x.1 : levelGroup N') : _ ⧸ edgeSubgroup (levelEquiv N')) :
      BSVertex _) = s.1 N' := by
  exact (congrArg (vertexMap f.le) x.2).trans (s.2 f)

lemma finite_edgeReps [IsTopologicalGroup Pv] [CompactSpace Pv] (s : (tower b₀ b₁).Sys)
    (N : Level b₀ b₁) (x₀ : edgeReps s N) : Finite (edgeReps s N) := by
  refine Finite.of_surjective (fun b : (branch₁ N).range ↦
    (⟨x₀.1 * of (b : levelQuot N), ?_⟩ : edgeReps s N)) ?_
  · exact (congrArg Sum.inr ((mk_edge_eq_iff (k := x₀.1)).2 ⟨b, rfl⟩).symm).trans x₀.2
  · rintro ⟨x, hx⟩
    obtain ⟨b, hb⟩ := mk_edge_eq_iff.1 (Sum.inr.inj (hx.trans x₀.2.symm)).symm
    exact ⟨b, Subtype.ext hb.symm⟩

/-- **Every system of edge kind is a translate of the base edge system.** -/
theorem exists_smul_baseEdgeSys [IsTopologicalGroup Pv] [CompactSpace Pv]
    (s : (tower b₀ b₁).Sys) (hs : ∀ N, (tower b₀ b₁).kind N (s.1 N) = false) :
    ∃ h : loopGroup b₀ b₁, h • baseEdgeSys b₀ b₁ = s := by
  have hne : ∀ N, Nonempty (edgeReps s N) := fun N ↦ by
    rcases hsN : s.1 N with c | c
    · have := hs N
      rw [hsN] at this
      exact absurd this (by simp [tower])
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      exact ⟨⟨x, hsN.symm⟩⟩
  let F : Level b₀ b₁ ⥤ Type u :=
    { obj N := edgeReps s N
      map f := TypeCat.ofHom fun x ↦ ⟨levelMap f.le x.1, edgeReps_map s f x⟩
      map_id N := by
        ext x
        exact Subtype.ext (DFunLike.congr_fun (levelMap_id N) x.1)
      map_comp f g := by
        ext x
        exact Subtype.ext (levelMap_apply_apply f.le g.le x.1).symm }
  haveI : ∀ N, Nonempty (F.obj N) := hne
  haveI : ∀ N, Finite (F.obj N) := fun N ↦ finite_edgeReps s N (hne N).some
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system F
  let h : loopGroup b₀ b₁ := ⟨fun N ↦ (u N).1, fun N N' hle ↦
    congrArg Subtype.val (hu (homOfLE hle))⟩
  refine ⟨h, TreeTower.Sys.ext fun N ↦ ?_⟩
  rw [TreeTower.smul_apply]
  change proj N h • (Sum.inr ((1 : levelGroup N) : _ ⧸ edgeSubgroup (levelEquiv N)) :
    BSVertex _) = s.1 N
  rw [Sum.smul_inr, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  exact (u N).2

lemma mem_stab_baseEdgeSys {x : loopGroup b₀ b₁} :
    x ∈ TreeTower.stab (baseEdgeSys b₀ b₁) ↔ ∀ N, proj N x ∈ edgeSubgroup (levelEquiv N) := by
  rw [TreeTower.mem_stab]
  refine forall_congr' fun N ↦ ?_
  change proj N x • (Sum.inr ((1 : levelGroup N) : _ ⧸ edgeSubgroup (levelEquiv N)) :
    BSVertex (levelEquiv N)) = Sum.inr _ ↔ _
  rw [Sum.smul_inr, Sum.inr.injEq, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp

/-- **The edge-like subgroup of the base edge system is the image of the second branch**, for
compact `Π` with closed `b₁(E)`, separated by the levels. -/
theorem stab_baseEdgeSys_eq [CompactSpace Pv] [IsTopologicalGroup Pv]
    (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1)
    (hcl : IsClosed (b₁.range : Set Pv)) :
    TreeTower.stab (baseEdgeSys b₀ b₁) = (b₁.range).map (vertexIncl b₀ b₁) := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · have hx' := mem_stab_baseEdgeSys.1 hx
    have hv : x ∈ TreeTower.stab (baseSys b₀ b₁) := mem_stab_baseSys.2 fun N ↦ by
      obtain ⟨b, hb, hbe⟩ := hx' N
      exact ⟨b, hbe⟩
    rw [stab_baseSys_eq_range] at hv
    obtain ⟨π, rfl⟩ := hv
    refine ⟨π, mem_of_forall_level hsep hcl fun N ↦ ?_, rfl⟩
    obtain ⟨b, ⟨ε, hε⟩, hbe⟩ := hx' N
    rw [proj_vertexIncl, (of_injective _).eq_iff] at hbe
    refine ⟨b₁ ε, ⟨ε, rfl⟩, ?_⟩
    rw [← QuotientGroup.eq]
    rw [← hbe, ← hε]
    rfl
  · rintro _ ⟨_, ⟨ε, rfl⟩, rfl⟩
    exact mem_stab_baseEdgeSys.2 fun N ↦ ⟨branch₁ N ε, ⟨ε, rfl⟩, rfl⟩

/-- **Edge-like subgroups are conjugates of the image of the edge group** ([SemiAnbd] Thm 3.7(iii)):
the stabilizer of every system of edge kind is a conjugate of the image of `b₁(E)`. -/
theorem stab_edge_eq_conj [CompactSpace Pv] [IsTopologicalGroup Pv]
    (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1)
    (hcl : IsClosed (b₁.range : Set Pv)) (s : (tower b₀ b₁).Sys)
    (hs : ∀ N, (tower b₀ b₁).kind N (s.1 N) = false) :
    ∃ h : loopGroup b₀ b₁,
      TreeTower.stab s = ConjAct.toConjAct h • (b₁.range).map (vertexIncl b₀ b₁) := by
  obtain ⟨h, rfl⟩ := exists_smul_baseEdgeSys s hs
  exact ⟨h, by rw [TreeTower.stab_smul, stab_baseEdgeSys_eq hsep hcl]⟩

end

end LoopTower

end TemperedFundamentalGroups
