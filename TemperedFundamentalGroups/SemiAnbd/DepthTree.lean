/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# A depth criterion for trees

A simple graph is a tree if it carries a *depth function* `d : V → ℕ` such that adjacent vertices
have different depths, the root has depth `0`, and every other vertex has exactly
one neighbour of smaller depth (its *parent*). This is the form in which the Bass–Serre tree of an
HNN extension is shown to be a tree (`SemiAnbd/HNNTree.lean`): the depth of a coset is the number
of `t`-letters of a reduced word.

## Main results

* `SimpleGraph.isTree_of_depth`: the criterion.
-/

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The hypotheses of the depth criterion for trees. -/
structure DepthData (d : V → ℕ) (r : V) : Prop where
  /-- Adjacent vertices have different depths. -/
  ne_of_adj : ∀ x y, G.Adj x y → d x ≠ d y
  /-- The root has depth `0`. -/
  root_depth : d r = 0
  /-- Every vertex other than the root has a neighbour of smaller depth. -/
  exists_lt : ∀ x, x ≠ r → ∃ y, G.Adj x y ∧ d y < d x
  /-- Every vertex has at most one neighbour of smaller depth. -/
  unique_lt : ∀ x y z, G.Adj x y → d y < d x → G.Adj x z → d z < d x → y = z

namespace DepthData

variable {G} {d : V → ℕ} {r : V} (h : G.DepthData d r)
include h

/-- Every vertex is reachable from the root. -/
theorem reachable_root (x : V) : G.Reachable x r := by
  induction hn : d x using Nat.strong_induction_on generalizing x with
  | _ n ih =>
    by_cases hx : x = r
    · exact hx ▸ Reachable.refl _
    · obtain ⟨y, hxy, hy⟩ := h.exists_lt x hx
      exact hxy.reachable.trans (ih (d y) (hn ▸ hy) y rfl)

/-- The parent of a vertex (the root is its own parent). -/
noncomputable def parent (x : V) : V := by
  classical
  exact if hx : x = r then r else (h.exists_lt x hx).choose

lemma parent_spec {x : V} (hx : x ≠ r) : G.Adj x (h.parent x) ∧ d (h.parent x) < d x := by
  classical
  simp only [parent, dif_neg hx]
  exact (h.exists_lt x hx).choose_spec

lemma eq_parent {x y : V} (hxy : G.Adj x y) (hy : d y < d x) : y = h.parent x := by
  have hx : x ≠ r := by
    rintro rfl
    have := h.root_depth
    omega
  exact h.unique_lt x y _ hxy hy (h.parent_spec hx).1 (h.parent_spec hx).2

/-- A neighbour of `x` other than its parent is a child of `x`. -/
lemma parent_eq_of_adj {x y : V} (hxy : G.Adj x y) (hne : y ≠ h.parent x) : h.parent y = x := by
  have hd := h.ne_of_adj x y hxy
  rcases lt_or_gt_of_ne hd with hlt | hlt
  · exact (h.eq_parent hxy.symm hlt).symm
  · exact absurd (h.eq_parent hxy hlt) hne

/-- `z` lies below `x`: some iterate of `parent` maps `z` to `x`. -/
def Below (x z : V) : Prop := ∃ n, h.parent^[n] z = x

lemma depth_le_of_below {x z : V} (hz : h.Below x z) : d x ≤ d z := by
  obtain ⟨n, rfl⟩ := hz
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    refine (ih (z := h.parent z)).trans ?_
    by_cases hz : z = r
    · simp [parent, hz]
    · exact (h.parent_spec hz).2.le

/-- The vertices below `x` are closed under the edges other than `{x, parent x}`. -/
lemma below_of_adj {x z w : V} (hz : h.Below x z)
    (hzw : (G.deleteEdges {s(x, h.parent x)}).Adj z w) : h.Below x w := by
  rw [deleteEdges_adj, Set.mem_singleton_iff] at hzw
  obtain ⟨hzw, hne⟩ := hzw
  obtain ⟨n, hn⟩ := hz
  by_cases hw : w = h.parent z
  · subst hw
    rcases n with _ | n
    · simp only [Function.iterate_zero, id_eq] at hn
      exact absurd (by rw [hn]) hne
    · exact ⟨n, by rwa [Function.iterate_succ_apply] at hn⟩
  · refine ⟨n + 1, ?_⟩
    rw [Function.iterate_succ_apply, h.parent_eq_of_adj hzw hw, hn]

/-- Every edge `{x, parent x}` is a bridge. -/
theorem isBridge_parent {x : V} (hx : x ≠ r) : G.IsBridge s(x, h.parent x) := by
  rw [isBridge_iff]
  rintro ⟨p⟩
  have key : ∀ {a b : V} (q : (G.deleteEdges {s(x, h.parent x)}).Walk a b), h.Below x a →
      h.Below x b := by
    intro a b q
    induction q with
    | nil => exact id
    | cons hab _ ih => exact fun ha ↦ ih (h.below_of_adj ha hab)
  have := h.depth_le_of_below (key p ⟨0, rfl⟩)
  have := (h.parent_spec hx).2
  omega

/-- **The depth criterion**: the graph is a tree. -/
theorem isTree : G.IsTree where
  connected := by
    haveI : Nonempty V := ⟨r⟩
    exact Connected.mk fun x y ↦ (h.reachable_root x).trans (h.reachable_root y).symm
  isAcyclic := by
    rw [isAcyclic_iff_forall_isBridge]
    intro e he
    induction e using Sym2.ind with
    | _ a b =>
    rw [mem_edgeSet] at he
    rcases lt_or_gt_of_ne (h.ne_of_adj a b he) with hlt | hlt
    · have hb : b ≠ r := fun hb ↦ by have := h.root_depth; subst hb; omega
      rw [Sym2.eq_swap, h.eq_parent he.symm hlt]
      exact h.isBridge_parent hb
    · have ha : a ≠ r := fun ha ↦ by have := h.root_depth; subst ha; omega
      rw [h.eq_parent he hlt]
      exact h.isBridge_parent ha

end DepthData

/-- **The depth criterion for trees.** -/
theorem isTree_of_depth {d : V → ℕ} {r : V} (h : G.DepthData d r) : G.IsTree := h.isTree

end SimpleGraph
