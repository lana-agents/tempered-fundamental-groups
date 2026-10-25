/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.CombGC

/-!
# Estrangement of compatible systems (the limit form of [SemiAnbd] Def 2.4(iv))

`TreeTower.Estranged` asks for small fixed sets *level by level*; this fails for the pro-`ℓ`
1-gon (`oneGonTower_not_estranged`). The adjacency hypothesis `PSCAdj` of CG3 only needs the
**limit form**: a nontrivial element fixing two compatible systems keeps them at distance `≤ 2` at
every level (`TreeTower.SysEstranged`). This is the form in which [SemiAnbd] Def 2.4(iv) enters the
statement of Thm 3.7(iii) (`semianbd.txt` l.1909–1918: a nontrivial compact subgroup in two
verticial subgroups determines "a compatible system of pairs of vertices ... joined to one another
by a single [closed] edge").

* `TreeTower.SysEstranged`, `TreeTower.Estranged.sysEstranged` (the level form implies it);
* `TreeTower.limAdj_of_adjG_of_sysEstranged`, **`TreeTower.pscAdj_of_sysEstranged`** (W11 with the
  limit form), **`TreeTower.isGraphic_iff_of_sysEstranged`** (CG3' with the limit form).
-/

universe u v w x

open CategoryTheory

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type x} [Group Γ] {J : Type u} [Category.{v} J] (T : TreeTower.{u, v, w} Γ J)

/-- **Estrangement of systems**: a nontrivial element fixing two compatible systems keeps them at
distance `≤ 2` at every level. -/
def SysEstranged : Prop :=
  ∀ g : Γ, g ≠ 1 → ∀ s s' : T.Sys, g ∈ stab s → g ∈ stab s' →
    ∀ k, (T.graph k).dist (s.1 k) (s'.1 k) ≤ 2

variable {T}

/-- The level form of estrangement implies the limit form. -/
theorem Estranged.sysEstranged (hE : T.Estranged) : T.SysEstranged := by
  intro g hg s s' hs hs' j
  obtain ⟨k, f, hk⟩ := hE g hg j
  rw [← s.2 f, ← s'.2 f]
  exact (T.dist_map_le f _ _).trans (hk _ _ (mem_stab.1 hs k) (mem_stab.1 hs' k))

/-- Under estrangement of systems, group-theoretically adjacent systems are adjacent in the limit
tree. -/
theorem limAdj_of_adjG_of_sysEstranged (hE : T.SysEstranged) {s s' : T.Sys} (h : AdjG s s') :
    LimAdj s s' := by
  refine ⟨h.1, fun j ↦ ?_⟩
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.2
  exact hE g (fun h1 ↦ hg1 (Subtype.ext h1)) s s' hg.1 hg.2 j

/-- **W11 with the limit form of estrangement**: `PSCAdj` for functorial towers without branch
inversions, with nontrivial edge-like subgroups, whose systems are estranged. -/
theorem pscAdj_of_sysEstranged [IsCofilteredOrEmpty J] (hT : T.IsFunctorial)
    (hE : T.SysEstranged) (hB : T.NoBranchSwap)
    (hedge : ∀ e : T.Sys, (∀ j, ∃ (k : J) (_ : k ⟶ j), T.kind k (e.1 k) = false) → stab e ≠ ⊥) :
    T.PSCAdj := fun s s' ↦
  ⟨limAdj_of_adjG_of_sysEstranged hE, adjG_of_limAdj hT hB hedge s.2.1 s'.2.1⟩

variable {Γ' : Type*} [Group Γ'] {J' : Type*} [Category J'] {T' : TreeTower.{_, _, w} Γ' J'}

/-- **CG3' with the limit form of estrangement**: graphicity of isomorphisms of tower groups is
equivalent to group-theoretic verticiality. -/
theorem isGraphic_iff_of_sysEstranged [IsCofilteredOrEmpty J] [IsCofilteredOrEmpty J']
    {α : Γ ≃* Γ'} (hT : T.IsFunctorial) (hT' : T'.IsFunctorial) (hE : T.SysEstranged)
    (hE' : T'.SysEstranged) (hB : T.NoBranchSwap) (hB' : T'.NoBranchSwap)
    (hedge : ∀ e : T.Sys, (∀ j, ∃ (k : J) (_ : k ⟶ j), T.kind k (e.1 k) = false) → stab e ≠ ⊥)
    (hedge' : ∀ e : T'.Sys, (∀ j, ∃ (k : J') (_ : k ⟶ j), T'.kind k (e.1 k) = false) →
      stab e ≠ ⊥) :
    IsGraphic T T' α ↔ IsGroupTheoreticallyVerticial T T' α :=
  isGraphic_iff_isGroupTheoreticallyVerticial (pscAdj_of_sysEstranged hT hE hB hedge)
    (pscAdj_of_sysEstranged hT' hE' hB' hedge')

end TreeTower

end TemperedFundamentalGroups
