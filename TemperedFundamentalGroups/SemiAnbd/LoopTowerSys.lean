/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.LoopTowerEdge

/-!
# Verticial systems of the loop tower are translates of the base system

For a compact vertex group `Π`, the level quotients `Q_N` are finite, so a compatible family of
vertex cosets `k_N Q_N` has a compatible family of representatives (König's lemma for the finite
cosets, `nonempty_sections_of_finite_cofiltered_system`). Hence every verticial system of the tree
tower of a loop of groups is `h • baseSys` for some `h` in the loop group, and every verticial
subgroup is a conjugate of the image of `Π` ([SemiAnbd] Thm 3.7(i): the verticial subgroups are
the conjugates of the `π₁(G_v)`, parametrised by `π^temp / Π_v`).

* **`LoopTower.exists_smul_baseSys`**: every system of vertex kind is a translate of `baseSys`;
* **`LoopTower.stab_eq_conj_range`**: its stabilizer is a conjugate of the range of `vertexIncl`.
-/

open CategoryTheory HNNExtension
open scoped Pointwise

namespace TemperedFundamentalGroups

namespace LoopTower

noncomputable section

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [IsTopologicalGroup Pv] [CompactSpace Pv]
  [Group E] {b₀ b₁ : E →* Pv}

instance (N : Level b₀ b₁) : Finite (levelQuot N) :=
  Subgroup.quotient_finite_of_isOpen _ N.2.2.1

/-- The representatives of the vertex coset of a system at level `N`. -/
def sysReps (s : (tower b₀ b₁).Sys) (N : Level b₀ b₁) : Type u :=
  {x : levelGroup N // (Sum.inl (x : _ ⧸ vertexSubgroup (levelEquiv N)) : BSVertex _) = s.1 N}

omit [IsTopologicalGroup Pv] [CompactSpace Pv] in
lemma sysReps_map (s : (tower b₀ b₁).Sys) {N N' : Level b₀ b₁} (f : N ⟶ N')
    (x : sysReps s N) :
    (Sum.inl ((levelMap f.le x.1 : levelGroup N') : _ ⧸ vertexSubgroup (levelEquiv N')) :
      BSVertex _) = s.1 N' := by
  exact (congrArg (vertexMap f.le) x.2).trans (s.2 f)

lemma finite_sysReps (s : (tower b₀ b₁).Sys) (N : Level b₀ b₁) (x₀ : sysReps s N) :
    Finite (sysReps s N) := by
  refine Finite.of_surjective (fun q : levelQuot N ↦ (⟨x₀.1 * of q, ?_⟩ : sysReps s N)) ?_
  · exact (congrArg Sum.inl ((mk_vertex_eq_iff (k := x₀.1)).2 ⟨q, rfl⟩).symm).trans x₀.2
  · rintro ⟨x, hx⟩
    obtain ⟨q, hq⟩ := mk_vertex_eq_iff.1 (Sum.inl.inj (hx.trans x₀.2.symm)).symm
    exact ⟨q, Subtype.ext hq.symm⟩

/-- **Every system of vertex kind is a translate of the base system.** -/
theorem exists_smul_baseSys (s : (tower b₀ b₁).Sys) (hs : TreeTower.IsVert s) :
    ∃ h : loopGroup b₀ b₁, h • baseSys b₀ b₁ = s := by
  have hne : ∀ N, Nonempty (sysReps s N) := fun N ↦ by
    rcases hsN : s.1 N with c | c
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective c
      exact ⟨⟨x, hsN.symm⟩⟩
    · have := hs N
      rw [hsN] at this
      exact absurd this (by simp [tower])
  let F : Level b₀ b₁ ⥤ Type u :=
    { obj N := sysReps s N
      map f := TypeCat.ofHom fun x ↦ ⟨levelMap f.le x.1, sysReps_map s f x⟩
      map_id N := by
        ext x
        exact Subtype.ext (DFunLike.congr_fun (levelMap_id N) x.1)
      map_comp f g := by
        ext x
        exact Subtype.ext (levelMap_apply_apply f.le g.le x.1).symm }
  haveI : ∀ N, Nonempty (F.obj N) := hne
  haveI : ∀ N, Finite (F.obj N) := fun N ↦ finite_sysReps s N (hne N).some
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system F
  let h : loopGroup b₀ b₁ := ⟨fun N ↦ (u N).1, fun N N' hle ↦
    congrArg Subtype.val (hu (homOfLE hle))⟩
  refine ⟨h, TreeTower.Sys.ext fun N ↦ ?_⟩
  rw [TreeTower.smul_apply]
  change proj N h • (Sum.inl ((1 : levelGroup N) : _ ⧸ vertexSubgroup (levelEquiv N)) :
    BSVertex _) = s.1 N
  rw [Sum.smul_inl, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
  exact (u N).2

/-- **Verticial subgroups are conjugates of the vertex group** ([SemiAnbd] Thm 3.7(i)). -/
theorem stab_eq_conj_range (s : (tower b₀ b₁).Sys) (hs : TreeTower.IsVert s) :
    ∃ h : loopGroup b₀ b₁,
      TreeTower.stab s = ConjAct.toConjAct h • (vertexIncl b₀ b₁).range := by
  obtain ⟨h, rfl⟩ := exists_smul_baseSys s hs
  refine ⟨h, ?_⟩
  rw [TreeTower.stab_smul, stab_baseSys_eq_range]

end

end LoopTower

end TemperedFundamentalGroups
