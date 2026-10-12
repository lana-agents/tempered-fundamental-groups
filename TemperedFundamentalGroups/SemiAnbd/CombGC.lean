/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemiAnbd.TreeTower

/-!
# Combinatorial Grothendieck conjecture: graphicity in tree towers (Blueprint §12.6, CG1–CG3)

[CombGC] Thm. 1.6 says that an isomorphism of fundamental groups of semi-graphs of anabelioids of
PSC type is *graphic* (induced by an isomorphism of the semi-graphs) if and only if it is
*group-theoretically verticial* (maps verticial subgroups onto verticial subgroups). We state and
prove the tempered analogue in tree towers (Blueprint §12.4), under the PSC-type adjacency
hypothesis `TreeTower.PSCAdj`. The profinite statement needs profinite trees and is not
formalized (Blueprint §12.6, CG4).

* `TreeTower.IsGroupTheoreticallyVerticial α` (**CG1**): `α` maps the verticial subgroups of
  systems with `(HI)` onto those of the other tower.
* `TreeTower.IsGraphic α` (**CG1**): `α` has a vertex correspondence preserving adjacency of the
  limit trees.
* `TreeTower.IsGraphic.isGroupTheoreticallyVerticial` (**CG2**).
* `TreeTower.isGraphic_of_isGroupTheoreticallyVerticial` (**CG3**), and
  `TreeTower.isGraphic_iff_isGroupTheoreticallyVerticial`.
-/

universe u v w x

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type x} [Group Γ] {J : Type u} [CategoryTheory.Category.{v} J]
  {T : TreeTower.{u, v, w} Γ J} {Γ' : Type*} [Group Γ'] {J' : Type*}
  [CategoryTheory.Category J'] {T' : TreeTower.{_, _, w} Γ' J'}

variable (T T') in
/-- **CG1**: `α` is **group-theoretically verticial**: it maps the verticial subgroups of `T`
(of systems with `(HI)`) onto those of `T'`. -/
def IsGroupTheoreticallyVerticial (α : Γ ≃* Γ') : Prop :=
  (∀ s : T.VSys, ∃ s' : T'.VSys, (stab s.1).map α.toMonoidHom = stab s'.1) ∧
    ∀ s' : T'.VSys, ∃ s : T.VSys, (stab s.1).map α.toMonoidHom = stab s'.1

variable (T T') in
/-- **CG1**: `α` is **graphic**: it induces a bijection of verticial systems, compatible with the
verticial subgroups, that preserves adjacency of the limit trees. -/
def IsGraphic (α : Γ ≃* Γ') : Prop :=
  ∃ E : VertexCorrespondence (T := T) (T' := T') α,
    ∀ s s' : T.VSys, LimAdj s.1 s'.1 ↔ LimAdj (E.e s).1 (E.e s').1

/-- **CG2**: graphic isomorphisms are group-theoretically verticial. -/
theorem IsGraphic.isGroupTheoreticallyVerticial {α : Γ ≃* Γ'} (h : IsGraphic T T' α) :
    IsGroupTheoreticallyVerticial T T' α := by
  obtain ⟨E, -⟩ := h
  refine ⟨fun s ↦ ⟨E.e s, E.map_stab s⟩, fun s' ↦ ⟨E.e.symm s', ?_⟩⟩
  rw [E.map_stab, Equiv.apply_symm_apply]

/-- **CG3, the combinatorial Grothendieck conjecture for tree towers**: under the PSC-type
adjacency hypothesis, group-theoretically verticial isomorphisms are graphic. -/
theorem isGraphic_of_isGroupTheoreticallyVerticial {α : Γ ≃* Γ'} (hT : T.PSCAdj)
    (hT' : T'.PSCAdj) (h : IsGroupTheoreticallyVerticial T T' α) : IsGraphic T T' α := by
  obtain ⟨E⟩ := nonempty_vertexCorrespondence α h.1 h.2
  exact ⟨E, E.limAdj_iff hT hT'⟩

/-- **CG2 + CG3**. -/
theorem isGraphic_iff_isGroupTheoreticallyVerticial {α : Γ ≃* Γ'} (hT : T.PSCAdj)
    (hT' : T'.PSCAdj) : IsGraphic T T' α ↔ IsGroupTheoreticallyVerticial T T' α :=
  ⟨IsGraphic.isGroupTheoreticallyVerticial, isGraphic_of_isGroupTheoreticallyVerticial hT hT'⟩

end TreeTower

end TemperedFundamentalGroups
