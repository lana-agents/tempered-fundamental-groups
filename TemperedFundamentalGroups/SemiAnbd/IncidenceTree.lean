/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.ZMod.QuotientGroup
import TemperedFundamentalGroups.SemiAnbd.TreeFixedPoint
import TemperedFundamentalGroups.Topology.DualGraphPi1

/-!
# The tree covering of an incidence graph is a tree (Blueprint §12.5, C1–C3)

Let `K` be a curve configuration (components `ι` of `Z` and their special points) with root
component `r`. The vertices of the tree covering `K.Tree r` are the reduced walks in the
incidence graph starting at `r`, adjacent when one extends the other by one step
(`Tree.Adj`; §11.3, G6.3).

* `CurveConfig.treeGraph K r` and **`CurveConfig.isTree_treeGraph`** (**C1**): it is a tree in
  Mathlib's sense (connected, `Tree.mem_of_adj_closed`; acyclic, the length is a rank function
  with unique parent `TreeGeom.isAcyclic_of_rank`), 2-coloured by the type of the last vertex
  (`Tree.kind`: component or special point, `Tree.kind_ne_of_adj`).
* (**C2**) the combinatorial fundamental group `K.Loop r` acts on `K.Tree r` by translation
  (`instMulActionLoopTree`) by coloured graph automorphisms (`adj_smul_iff`, `kind_smul`), freely
  (`eq_one_of_smul_eq`).
* **`CurveConfig.eq_one_of_isOfFinOrder`** (**C3**): `K.Loop r` has no torsion: a finite subgroup
  fixes a vertex (`TreeGeom.exists_fixed_of_finite`), hence is trivial.
-/

universe u v

namespace TemperedFundamentalGroups

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

namespace Tree

lemma length_pos (t : K.Tree r) : 0 < t.1.length := List.length_pos_iff.2 t.2.ne_nil

lemma length_of_adj {t t' : K.Tree r} (h : t.Adj t') :
    t'.1.length = t.1.length + 1 ∨ t.1.length = t'.1.length + 1 := by
  rcases h with h | h
  · left; rw [← h, List.length_tail]; have := length_pos t'; omega
  · right; rw [← h, List.length_tail]; have := length_pos t; omega

lemma not_adj_self (t : K.Tree r) : ¬ t.Adj t := by
  intro h
  rcases length_of_adj h with h | h <;> omega

/-- The parent of a vertex (its unique neighbour of smaller length) is its tail. -/
lemma eq_of_adj_of_length_lt {t a : K.Tree r} (h : t.Adj a) (hl : a.1.length < t.1.length) :
    a.1 = t.1.tail := by
  rcases h with h | h
  · rw [← h, List.length_tail] at hl; omega
  · exact h.symm

/-- The colour of a vertex of the tree: `true` over components, `false` over special points. -/
def kind (t : K.Tree r) : Bool :=
  match t.1.head? with
  | some (.inl _) => true
  | _ => false

lemma kind_ne_of_adj {t t' : K.Tree r} (h : t.Adj t') : kind t ≠ kind t' := by
  obtain ⟨a, ha⟩ := exists_head t
  obtain ⟨b, hb⟩ := exists_head t'
  have hab := adj_head t.2 t'.2 h ha hb
  unfold kind
  rw [ha, hb]
  rcases a with i | s <;> rcases b with j | s' <;> simp_all [CurveConfig.Adj]

end Tree

variable (K r) in
/-- **C1**: the tree covering of the incidence graph as a simple graph. -/
def treeGraph : SimpleGraph (K.Tree r) where
  Adj t t' := t.Adj t'
  symm := ⟨fun _ _ h ↦ Tree.adj_comm.1 h⟩
  loopless := ⟨fun t h ↦ Tree.not_adj_self t h⟩

@[simp]
lemma treeGraph_adj {t t' : K.Tree r} : (treeGraph K r).Adj t t' ↔ t.Adj t' := Iff.rfl

/-- **C1**: the tree covering of the incidence graph is a tree. -/
theorem isTree_treeGraph : (treeGraph K r).IsTree where
  connected := by
    haveI : Nonempty (K.Tree r) := ⟨root K r⟩
    refine ⟨fun t t' ↦ ?_⟩
    exact Tree.mem_of_adj_closed (A := {w | (treeGraph K r).Reachable t w})
      (fun a b hab (ha : (treeGraph K r).Reachable t a) ↦ ha.trans (SimpleGraph.Adj.reachable hab))
      (SimpleGraph.Reachable.refl t) t'
  isAcyclic := TreeGeom.isAcyclic_of_rank (fun t ↦ t.1.length)
    (fun _ _ h ↦ (Tree.length_of_adj h).symm)
    (fun _ _ _ ha hb hla hlb ↦ Tree.ext ((Tree.eq_of_adj_of_length_lt ha hla).trans
      (Tree.eq_of_adj_of_length_lt hb hlb).symm))

/-! ### C2: the deck action -/

/-- **C2**: closed walks at the root act on the tree by translation. -/
noncomputable instance instMulActionLoopTree : MulAction (K.Loop r) (K.Tree r) where
  smul a t := Tree.translate a t
  one_smul t := congrFun Loop.translate_one t
  mul_smul a b t := congrFun (Loop.translate_mul a b) t

lemma smul_def (a : K.Loop r) (t : K.Tree r) : a • t = Tree.translate a t := rfl

lemma adj_smul_iff (a : K.Loop r) (t t' : K.Tree r) :
    (treeGraph K r).Adj (a • t) (a • t') ↔ (treeGraph K r).Adj t t' := by
  refine ⟨fun h ↦ ?_, fun h ↦ (Tree.isHom_translate a).adj _ _ h⟩
  have := (Tree.isHom_translate a⁻¹).adj _ _ h
  rwa [← smul_def, ← smul_def, inv_smul_smul, inv_smul_smul] at this

lemma kind_smul (a : K.Loop r) (t : K.Tree r) : Tree.kind (a • t) = Tree.kind t := by
  unfold Tree.kind
  rw [smul_def, (Tree.isHom_translate a).head t]

lemma not_adj_smul (a : K.Loop r) (t : K.Tree r) : ¬ (treeGraph K r).Adj t (a • t) :=
  fun h ↦ Tree.kind_ne_of_adj h (kind_smul a t).symm

/-- **C2**: the translation action is free. -/
lemma eq_one_of_smul_eq {a : K.Loop r} {t : K.Tree r} (h : a • t = t) : a = 1 := by
  have h' : Tree.translate a = id := Tree.IsHom.ext (Tree.isHom_translate a) Tree.IsHom.id h
  apply Subtype.ext
  rw [Loop.one_val, ← Tree.translate_root a, h']
  rfl

/-- **C3**: the combinatorial fundamental group of the incidence graph has no torsion. -/
theorem eq_one_of_isOfFinOrder {a : K.Loop r} (hfin : IsOfFinOrder a) : a = 1 := by
  have : Finite (Subgroup.zpowers a) := hfin.finite_zpowers.to_subtype
  obtain ⟨c, hc⟩ := TreeGeom.exists_fixed_of_finite (Γ := Subgroup.zpowers a)
    (G := treeGraph K r) isTree_treeGraph (fun g x y ↦ adj_smul_iff g.1 x y)
    (fun g x ↦ not_adj_smul g.1 x)
  exact eq_one_of_smul_eq (hc ⟨a, Subgroup.mem_zpowers a⟩)

end CurveConfig

end TemperedFundamentalGroups
