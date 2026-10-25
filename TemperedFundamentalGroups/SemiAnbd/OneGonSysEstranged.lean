/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.LoopTowerEdgeSys
import TemperedFundamentalGroups.SemiAnbd.OneGonTower

/-!
# Estrangement of systems for `G^Σ` of the stable 1-gon (bridge B3, revised)

For the tree tower `oneGonTower P` of `π^temp(G^Σ)` of the stable 1-gon:

* **`oneGon_dist_le_two_of_bounded`** (the bounded case, unconditional): a nontrivial element
  fixing two compatible systems whose distances are bounded keeps them at distance `≤ 2` at every
  level. Input: `G^Σ` is totally estranged (`oneGonSigma_totallyEstranged`, [SemiAnbd] Def 2.4(iv)).
* `OneGonSysEstrangedUnbounded P` — **a named hypothesis (debt, `MR13-plan.md`)**: the unbounded
  case does not occur, i.e. a nontrivial element of `π^temp(G^Σ)` never fixes two systems whose
  distances are unbounded. (Expected from the profinite comparison `π^temp(G^Σ) ↪ π̂₁(G^Σ)` with
  the finite Galois coverings of `G^Σ`, [SemiAnbd] Prop 2.6/Cor 2.7, Prop 3.6(iii); not available
  yet. The level-wise statement `TreeTower.Estranged` is false here, `oneGonTower_not_estranged`.)
* Under this hypothesis: **`oneGon_sysEstranged`**, **`oneGon_pscAdj`** (`PSCAdj`) and
  **`oneGon_isGraphic_iff`** (CG3': an isomorphism of tempered groups of 1-gons is graphic iff it is
  group-theoretically verticial; [SemiAnbd] Thm 3.7(iii)/Cor 3.9 in tower form).
* `oneGon_stab_edge_eq_conj`: the edge-like subgroups are the conjugates of the image of `ℤ^Σ`
  (inertia of the node), [SemiAnbd] Thm 3.7(iii).
-/

open CategoryTheory Pi1 Pi1.Profinite Pi1.SurfaceGroup
open scoped Pointwise

namespace TemperedFundamentalGroups

open LoopTower

variable {P : ℕ → Prop}

/-- The branch images of the 1-gon are closed. -/
theorem oneGon_isClosed_range (X : Bool) :
    IsClosed ((br (oneGonB₀ P) (oneGonB₁ P) X).range : Set (proSigma P 0 3)) := by
  cases X <;>
  exact (isCompact_range (ProSigmaCompletion.continuous_map _)).isClosed

/-- The branch images of the 1-gon are estranged ([SemiAnbd] Def 2.4(iv), from
`oneGonSigma_totallyEstranged`). -/
theorem oneGon_estranged (X Y : Bool) (q : proSigma P 0 3)
    (h : X ≠ Y ∨ q ∉ (br (oneGonB₀ P) (oneGonB₁ P) X).range) :
    (br (oneGonB₀ P) (oneGonB₁ P) X).range ⊓
      (ConjAct.toConjAct q • (br (oneGonB₀ P) (oneGonB₁ P) Y).range) = ⊥ := by
  have key := fun hr ↦ oneGonSigma_totallyEstranged (P := P) false (!X) () rfl false (!Y) rfl q hr
  cases X <;> cases Y
  · exact key (Or.inr (h.resolve_left fun h ↦ h rfl))
  · exact key (Or.inl fun h ↦ absurd (congrArg Prod.snd h) (by decide))
  · exact key (Or.inl fun h ↦ absurd (congrArg Prod.snd h) (by decide))
  · exact key (Or.inr (h.resolve_left fun h ↦ h rfl))

/-- **The bounded case of estrangement of systems for the 1-gon**: a nontrivial element of
`π^temp(G^Σ)` fixing two systems at bounded distance keeps them at distance `≤ 2` at every level. -/
theorem oneGon_dist_le_two_of_bounded {g : oneGonTempered P} (hg : g ≠ 1)
    {s s' : (oneGonTower P).Sys} (hs : g ∈ TreeTower.stab s) (hs' : g ∈ TreeTower.stab s')
    (hbdd : ∃ C, ∀ N, ((oneGonTower P).graph N).dist (s.1 N) (s'.1 N) ≤ C) (N) :
    ((oneGonTower P).graph N).dist (s.1 N) (s'.1 N) ≤ 2 :=
  dist_le_two_of_bounded oneGon_sep oneGon_isClosed_range oneGon_estranged hg hs hs' hbdd N

/-- **Edge-like subgroups of `π^temp(G^Σ)` of the 1-gon** ([SemiAnbd] Thm 3.7(iii)): the stabilizer
of every system of edge kind is a conjugate of the image of the node inertia `ℤ^Σ ⊆ Π^Σ_{0,3}`. -/
theorem oneGon_stab_edge_eq_conj (s : (oneGonTower P).Sys)
    (hs : ∀ N, (oneGonTower P).kind N (s.1 N) = false) :
    ∃ h : oneGonTempered P, TreeTower.stab s =
      ConjAct.toConjAct h • ((oneGonB₁ P).range).map (vertexIncl (oneGonB₀ P) (oneGonB₁ P)) :=
  stab_edge_eq_conj oneGon_sep (oneGon_isClosed_range true) s hs

variable (P) in
/-- **Debt (named hypothesis, `MR13-plan.md`)**: the unbounded case of estrangement of systems for
the 1-gon does not occur — a nontrivial element of `π^temp(G^Σ)` fixing two compatible systems
keeps them at bounded distance. Together with the (proved) bounded case this is
`(oneGonTower P).SysEstranged`. -/
def OneGonSysEstrangedUnbounded : Prop :=
  ∀ g : oneGonTempered P, g ≠ 1 → ∀ s s' : (oneGonTower P).Sys,
    g ∈ TreeTower.stab s → g ∈ TreeTower.stab s' →
      ∃ C, ∀ N, ((oneGonTower P).graph N).dist (s.1 N) (s'.1 N) ≤ C

/-- **Estrangement of systems for the 1-gon**, given the unbounded case. -/
theorem oneGon_sysEstranged (hU : OneGonSysEstrangedUnbounded P) :
    (oneGonTower P).SysEstranged := fun g hg s s' hs hs' N ↦
  oneGon_dist_le_two_of_bounded hg hs hs' (hU g hg s s' hs hs') N

/-- **`PSCAdj` for the 1-gon**: group-theoretic adjacency of verticial systems is adjacency in the
limit tree, given the unbounded case of estrangement of systems. -/
theorem oneGon_pscAdj {ℓ : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ) (hU : OneGonSysEstrangedUnbounded P) :
    (oneGonTower P).PSCAdj :=
  TreeTower.pscAdj_of_sysEstranged isFunctorial_tower (oneGon_sysEstranged hU) noBranchSwap_tower
    (oneGon_hedge hℓ hP)

/-- **CG3' for the 1-gon** ([SemiAnbd] Thm 3.7(iii)/Cor 3.9, tower form): an isomorphism of the
tempered fundamental groups of the pro-`Σ` 1-gons is graphic iff it is group-theoretically
verticial, given the unbounded case of estrangement of systems on both sides. -/
theorem oneGon_isGraphic_iff {P' : ℕ → Prop} {ℓ ℓ' : ℕ} (hℓ : ℓ.Prime) (hP : P ℓ)
    (hℓ' : ℓ'.Prime) (hP' : P' ℓ') (hU : OneGonSysEstrangedUnbounded P)
    (hU' : OneGonSysEstrangedUnbounded P') (α : oneGonTempered P ≃* oneGonTempered P') :
    TreeTower.IsGraphic (oneGonTower P) (oneGonTower P') α ↔
      TreeTower.IsGroupTheoreticallyVerticial (oneGonTower P) (oneGonTower P') α :=
  TreeTower.isGraphic_iff_of_sysEstranged isFunctorial_tower isFunctorial_tower
    (oneGon_sysEstranged hU) (oneGon_sysEstranged hU') noBranchSwap_tower noBranchSwap_tower
    (oneGon_hedge hℓ hP) (oneGon_hedge hℓ' hP')

end TemperedFundamentalGroups
