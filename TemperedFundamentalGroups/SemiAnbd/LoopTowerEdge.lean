/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.LoopTowerVertex

/-!
# Colours, branch inversions and edge-like subgroups of the loop tower

The remaining structural hypotheses of the tree-tower consumers `TreeTower.pscAdj_of_estranged`
and `TreeTower.isGraphic_iff_of_estranged` (CG3') for the tree tower of a loop of groups
(`SemiAnbd/LoopTower.lean`); only estrangement (bridge B3) is not treated here.

* `LoopTower.instIsCofiltered`: the levels form a cofiltered category;
* `LoopTower.preservesKind_tower`: the transition maps preserve vertex and edge cosets;
* **`LoopTower.noBranchSwap_tower`**: an element fixing an edge coset fixes both ends;
* **`LoopTower.stab_ne_bot_of_edge`** (`hedge`): for a commutative edge group, every system that is
  eventually of edge kind has a nontrivial stabilizer, as soon as some level sees a nontrivial
  element of the second branch image.
-/

open CategoryTheory HNNExtension QuotientGroup

namespace TemperedFundamentalGroups

namespace LoopTower

noncomputable section

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [Group E] {b₀ b₁ : E →* Pv}

instance instIsCodirectedOrder : IsCodirectedOrder (Level b₀ b₁) :=
  ⟨fun N N' ↦ ⟨Level.inf N N', Level.inf_le_left N N', Level.inf_le_right N N'⟩⟩

variable [IsTopologicalGroup Pv] in
instance instNonempty : Nonempty (Level b₀ b₁) := ⟨Level.top⟩

variable [IsTopologicalGroup Pv] in
instance instIsCofiltered : IsCofiltered (Level b₀ b₁) := inferInstance

theorem preservesKind_tower : (tower b₀ b₁).PreservesKind := by
  intro N N' f v
  change (vertexMap f.le v).isLeft = v.isLeft
  simp only [vertexMap, Sum.isLeft_map]

lemma smul_inr_eq_iff {N : Level b₀ b₁} (g k : levelGroup N) :
    g • (Sum.inr (k : _ ⧸ edgeSubgroup (levelEquiv N)) : BSVertex (levelEquiv N)) =
        Sum.inr (k : _ ⧸ edgeSubgroup (levelEquiv N)) ↔
      ∃ b : (branch₁ N).range, g * k = k * of (b : levelQuot N) := by
  rw [Sum.smul_inr, Sum.inr.injEq, MulAction.Quotient.smul_mk, smul_eq_mul, eq_comm,
    mk_edge_eq_iff]

lemma noBranchSwap_aux {N : Level b₀ b₁} (g k : levelGroup N) (w : BSVertex (levelEquiv N))
    (hw : (bassSerreGraph (levelEquiv N)).Adj (Sum.inr (k : _ ⧸ edgeSubgroup (levelEquiv N))) w)
    (hge : g • (Sum.inr (k : _ ⧸ edgeSubgroup (levelEquiv N)) : BSVertex (levelEquiv N)) =
      Sum.inr (k : _ ⧸ edgeSubgroup (levelEquiv N))) : g • w = w := by
  rw [adj_inr_iff] at hw
  obtain ⟨b, hb⟩ := (smul_inr_eq_iff g k).1 hge
  rcases hw with rfl | rfl
  · rw [Sum.smul_inl, MulAction.Quotient.smul_mk, smul_eq_mul, hb]
    exact congrArg Sum.inl ((mk_vertex_eq_iff (k := k)
      (k' := (k * of (b : levelQuot N) : levelGroup N))).2 ⟨_, rfl⟩).symm
  · rw [Sum.smul_inl, MulAction.Quotient.smul_mk, smul_eq_mul, ← mul_assoc, hb, mul_assoc,
      of_mul_t, ← mul_assoc]
    exact congrArg Sum.inl ((mk_vertex_eq_iff (k := k * t)
      (k' := (k * t * of ((levelEquiv N).symm b : levelQuot N) : levelGroup N))).2 ⟨_, rfl⟩).symm

/-- **No branch inversions** in the loop tower: an element fixing the edge coset `k B` fixes `k G`
and `k t G`. -/
theorem noBranchSwap_tower : (tower b₀ b₁).NoBranchSwap := by
  intro N g e w he hw hge
  rcases e with e | e
  · exact absurd he (by simp [tower])
  induction e using QuotientGroup.induction_on with
  | H k => exact noBranchSwap_aux g k w hw hge

/-- Conjugating an element of the (commutative) second branch image by a representative of an
edge coset does not depend on the representative. -/
lemma conj_eq_of_mk_eq (hE : ∀ x y : E, x * y = y * x) {N : Level b₀ b₁} {k k' : levelGroup N}
    (h : (k : _ ⧸ edgeSubgroup (levelEquiv N)) = k') (ε : E) :
    k * of (branch₁ N ε) * k⁻¹ = k' * of (branch₁ N ε) * k'⁻¹ := by
  obtain ⟨⟨_, η, rfl⟩, rfl⟩ := mk_edge_eq_iff.1 h
  change _ = k * of (branch₁ N η) * of (branch₁ N ε) * (k * of (branch₁ N η))⁻¹
  have hc : (of (branch₁ N η) : levelGroup N) * of (branch₁ N ε) =
      of (branch₁ N ε) * of (branch₁ N η) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hE]
  rw [mul_inv_rev]
  simp only [mul_assoc]
  rw [← mul_assoc (of (branch₁ N η)) (of (branch₁ N ε)), hc, mul_assoc, mul_inv_cancel_left]

/-- A representative of an edge coset. -/
def edgeRep {N : Level b₀ b₁} (e : levelGroup N ⧸ edgeSubgroup (levelEquiv N)) : levelGroup N :=
  e.out

lemma mk_edgeRep {N : Level b₀ b₁} (e : levelGroup N ⧸ edgeSubgroup (levelEquiv N)) :
    ((edgeRep e : levelGroup N) : _ ⧸ edgeSubgroup (levelEquiv N)) = e :=
  e.out_eq'

/-- **Edge-like subgroups of the loop tower are nontrivial** (the `hedge` hypothesis of
`TreeTower.pscAdj_of_estranged`), for a commutative edge group with a nontrivial image of the
second branch at some level. -/
theorem stab_ne_bot_of_edge (hE : ∀ x y : E, x * y = y * x)
    (hnt : ∃ (N₀ : Level b₀ b₁) (ε : E), branch₁ N₀ ε ≠ 1) (e : (tower b₀ b₁).Sys)
    (he : ∀ N, ∃ (N' : Level b₀ b₁) (_ : N' ⟶ N), (tower b₀ b₁).kind N' (e.1 N') = false) :
    TreeTower.stab e ≠ ⊥ := by
  -- every level is of edge kind
  have hkind : ∀ N, ∃ c, e.1 N = Sum.inr c := fun N ↦ by
    obtain ⟨N', f, hN'⟩ := he N
    have h1 := e.2 f
    rcases hc : e.1 N with c | c
    · rw [← h1] at hc
      rcases hc' : e.1 N' with c' | c'
      · rw [hc'] at hN'; exact absurd hN' (by simp [tower])
      · rw [hc'] at hc; exact absurd hc (by simp [tower, vertexMap])
    · exact ⟨c, rfl⟩
  choose c hc using hkind
  obtain ⟨N₀, ε, hε⟩ := hnt
  -- the element `(k_N · b₁(ε) · k_N⁻¹)_N`
  let g : ∀ N, levelGroup N := fun N ↦ edgeRep (c N) * of (branch₁ N ε) * (edgeRep (c N))⁻¹
  have hcompat : ∀ N N' (h : N ≤ N'), levelMap h (g N) = g N' := by
    intro N N' h
    have h1 := e.2 (homOfLE h)
    rw [hc, hc] at h1
    change vertexMap h (Sum.inr _) = _ at h1
    rw [← mk_edgeRep (c N), vertexMap_inr, Sum.inr.injEq, ← mk_edgeRep (c N')] at h1
    simp only [g, map_mul, map_inv, levelMap_of, quotMap_branch₁]
    exact conj_eq_of_mk_eq hE h1 ε
  let x : loopGroup b₀ b₁ := ⟨g, hcompat⟩
  have hx : x ∈ TreeTower.stab e := by
    rw [TreeTower.mem_stab]
    intro N
    have key : g N • (Sum.inr (edgeRep (c N) : _ ⧸ edgeSubgroup (levelEquiv N)) :
        BSVertex (levelEquiv N)) = Sum.inr (edgeRep (c N) : _ ⧸ edgeSubgroup (levelEquiv N)) :=
      (smul_inr_eq_iff _ _).2 ⟨⟨branch₁ N ε, ε, rfl⟩, by simp [g, mul_assoc]⟩
    rw [mk_edgeRep, ← hc] at key
    exact key
  intro hbot
  have : x = 1 := by rw [← Subgroup.mem_bot, ← hbot]; exact hx
  have h1 := congrArg (proj N₀) this
  change g N₀ = 1 at h1
  simp only [g, mul_inv_eq_one, mul_eq_left] at h1
  exact hε ((of_injective _).eq_iff.1 (h1.trans (map_one _).symm))

end

end LoopTower

end TemperedFundamentalGroups
