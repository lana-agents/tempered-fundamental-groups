/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemiAnbd.IncidenceTree

/-!
# Maps of tree coverings induce maps of trees (Blueprint §12.5, C5)

Let `K` be a curve configuration on `Z` whose generic points are not special (`hη`). Every vertex
`t` of the tree `K.Tree r` has a **canonical point** `canon hη t` in the tree covering
`K.Cover r`: `(η_i, t)` if `t` lies over the component `i`, and `(s, t)` if `t` lies over the
special point `s`. A continuous map `f : K.Cover r → K'.Cover r'` induces the map of vertices
`vmap hη f t`, the tree coordinate of `f (canon hη t)`.

* `CurveConfig.vmap_adj`: `vmap hη f` is **non-expanding** (adjacent vertices go to adjacent or
  equal vertices). The canonical point of a vertex over a component specialises to the canonical
  points of its neighbours (`canon_specializes`), and specialisation in the tree covering moves
  the tree coordinate by at most one step (`Tree.eq_or_adj_of_specializes`: the topology of the
  tree is the Alexandrov topology in which vertices over special points specialise to their
  neighbours).
* `CurveConfig.PreservesCanon`, `CurveConfig.PreservesSheets`, and the composition rules
  `vmap_comp_of_preservesCanon`, `vmap_comp_of_preservesSheets`.
* `CurveConfig.preservesCanon_of_over`, `CurveConfig.preservesSheets_of_over`,
  `CurveConfig.kind_vmap_of_over`: a continuous map over a map `ψ : Z → Z'` that sends generic
  points to generic points and reflects and preserves special points (e.g. a homeomorphism of
  special fibres) preserves canonical points and sheets, and the colours of vertices.
-/

universe u v u' v'

open Set Topology

namespace TemperedFundamentalGroups

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

namespace Tree

/-- Specialisation in the tree: a vertex specialises only to itself and, if it lies over a
special point, to its neighbours. -/
lemma eq_or_adj_of_specializes {a b : K.Tree r} (h : a ⤳ b) : a = b ∨ b.Adj a := by
  rcases b.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · exact .inl ((specializes_iff_forall_open.1 h) {b} (isOpen_singleton hi) rfl)
  · exact (specializes_iff_forall_open.1 h) (star b) (isOpen_star hs) (.inl rfl)

/-- A vertex adjacent to a vertex over a special point specialises to it. -/
lemma specializes_of_adj {t t' : K.Tree r} {s : Z} (hs : t'.1.head? = some (.inr s))
    (h : t'.Adj t) : t ⤳ t' :=
  specializes_iff_forall_open.2 fun _ hU ht' ↦ hU t' t ⟨s, hs⟩ h ht'

lemma kind_eq_true_iff {t : K.Tree r} : kind t = true ↔ ∃ i, t.1.head? = some (.inl i) := by
  unfold kind
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩ <;> simp_all

lemma kind_eq_false_iff {t : K.Tree r} : kind t = false ↔ ∃ s, t.1.head? = some (.inr s) := by
  unfold kind
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩ <;> simp_all

end Tree

/-- Specialisation in the tree covering moves the tree coordinate by at most one step. -/
lemma Cover.eq_or_adj_of_specializes {x y : K.Cover r} (h : x ⤳ y) :
    x.1.2 = y.1.2 ∨ y.1.2.Adj x.1.2 :=
  Tree.eq_or_adj_of_specializes (specializes_prod.1 ((subtype_specializes_iff x y).1 h)).2

/-- Points of a component are specialisations of its generic point. -/
lemma η_specializes {i : ι} {z : Z} (hz : z ∈ K.C i) : K.η i ⤳ z :=
  specializes_iff_forall_open.2 fun U hU hzU ↦ K.η_generic i U hU ⟨z, hzU, hz⟩

section Canon

variable (hη : ∀ i, K.η i ∉ K.S)

/-- The canonical point of the piece of a vertex: the generic point of its component, or its
special point. -/
noncomputable def canonPt (t : K.Tree r) : Z := (t.1.head?).elim (K.η r) (Sum.elim K.η id)

lemma canonPt_of_inl {t : K.Tree r} {i : ι} (h : t.1.head? = some (.inl i)) :
    canonPt t = K.η i := by
  simp [canonPt, h]

lemma canonPt_of_inr {t : K.Tree r} {s : Z} (h : t.1.head? = some (.inr s)) :
    canonPt t = s := by
  simp [canonPt, h]

include hη in
lemma canonPt_mem (t : K.Tree r) : canonPt t ∈ K.piece t.1.head? := by
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · rw [canonPt_of_inl hi, hi]
    exact ⟨K.η_mem i, hη i⟩
  · rw [canonPt_of_inr hs, hs]
    rfl

/-- The **canonical point** of a vertex of the tree in the tree covering. -/
noncomputable def canon (t : K.Tree r) : K.Cover r := ⟨(canonPt t, t), canonPt_mem hη t⟩

@[simp]
lemma canon_snd (t : K.Tree r) : (canon hη t).1.2 = t := rfl

/-- A point over a special point is the canonical point of its vertex. -/
lemma eq_canon_of_inr {x : K.Cover r} {s : Z} (h : x.1.2.1.head? = some (.inr s)) :
    x = canon hη x.1.2 :=
  Cover.ext ((Cover.eq_of_inr h).trans (canonPt_of_inr h).symm) rfl

/-- The canonical point of a vertex over a component specialises to the points of its sheet. -/
lemma canon_specializes_of_inl {x : K.Cover r} {i : ι} (h : x.1.2.1.head? = some (.inl i)) :
    canon hη x.1.2 ⤳ x := by
  refine (subtype_specializes_iff _ _).2 (specializes_prod.2 ⟨?_, specializes_rfl⟩)
  change canonPt x.1.2 ⤳ x.1.1
  rw [canonPt_of_inl h]
  exact η_specializes (Cover.mem_piece_inl h).1

/-- The canonical point of a vertex over a component specialises to the canonical points of its
neighbours. -/
lemma canon_specializes {t t' : K.Tree r} {i : ι} (hi : t.1.head? = some (.inl i))
    (h : t.Adj t') : canon hη t ⤳ canon hη t' := by
  obtain ⟨s, hs, -, hsi⟩ := head_inr_of_adj t.2 t'.2 h hi
  refine (subtype_specializes_iff _ _).2 (specializes_prod.2 ⟨?_, ?_⟩)
  · rw [canonPt_of_inl hi, canonPt_of_inr hs]
    exact η_specializes hsi
  · exact Tree.specializes_of_adj hs (Tree.adj_comm.1 h)

variable {Z' : Type u'} [TopologicalSpace Z'] {ι' : Type v'} {K' : CurveConfig Z' ι'} {r' : ι'}

/-- The **map of vertices** induced by a map of tree coverings: the tree coordinate of the image
of the canonical point. -/
noncomputable def vmap (f : K.Cover r → K'.Cover r') (t : K.Tree r) : K'.Tree r' :=
  (f (canon hη t)).1.2

/-- **The map of vertices is non-expanding.** -/
theorem vmap_adj {f : K.Cover r → K'.Cover r'} (hf : Continuous f) {t t' : K.Tree r}
    (h : t.Adj t') : (vmap hη f t).Adj (vmap hη f t') ∨ vmap hη f t = vmap hη f t' := by
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · rcases Cover.eq_or_adj_of_specializes ((canon_specializes hη hi h).map hf) with h' | h'
    · exact .inr h'
    · exact .inl (Tree.adj_comm.1 h')
  · obtain ⟨i, hi, -⟩ := head_inl_of_adj t.2 t'.2 h hs
    rcases Cover.eq_or_adj_of_specializes
      ((canon_specializes hη hi (Tree.adj_comm.1 h)).map hf) with h' | h'
    · exact .inr h'.symm
    · exact .inl h'

/-- The map of vertices of the identity. -/
lemma vmap_id : vmap hη (id : K.Cover r → K.Cover r) = id := rfl

/-- `f` sends canonical points to canonical points. -/
def PreservesCanon (hη' : ∀ j, K'.η j ∉ K'.S) (f : K.Cover r → K'.Cover r') : Prop :=
  ∀ t, f (canon hη t) = canon hη' (vmap hη f t)

/-- `f` sends sheets (the points with a given tree coordinate) into sheets. -/
def PreservesSheets (f : K.Cover r → K'.Cover r') : Prop :=
  ∀ x, (f x).1.2 = vmap hη f x.1.2

variable {Z'' : Type*} [TopologicalSpace Z''] {ι'' : Type*} {K'' : CurveConfig Z'' ι''}
  {r'' : ι''}

lemma vmap_comp_of_preservesCanon (hη' : ∀ j, K'.η j ∉ K'.S) {f : K.Cover r → K'.Cover r'}
    (g : K'.Cover r' → K''.Cover r'') (hf : PreservesCanon hη hη' f) :
    vmap hη (g ∘ f) = vmap hη' g ∘ vmap hη f := by
  funext t
  change (g (f (canon hη t))).1.2 = (g (canon hη' (vmap hη f t))).1.2
  rw [hf t]

lemma vmap_comp_of_preservesSheets (hη' : ∀ j, K'.η j ∉ K'.S) (f : K.Cover r → K'.Cover r')
    {g : K'.Cover r' → K''.Cover r''} (hg : PreservesSheets hη' g) :
    vmap hη (g ∘ f) = vmap hη' g ∘ vmap hη f := by
  funext t
  exact hg (f (canon hη t))

section Over

variable (hη' : ∀ j, K'.η j ∉ K'.S) {f : K.Cover r → K'.Cover r'} {ψ : Z → Z'}
  (hfψ : ∀ x, (f x).1.1 = ψ x.1.1) (hgen : ∀ i, ∃ j, ψ (K.η i) = K'.η j)
  (hS : ∀ z, ψ z ∈ K'.S ↔ z ∈ K.S)

include hη' hfψ hgen in
/-- The vertex of the image of the canonical point of a vertex over a component lies over a
component. -/
lemma vmap_inl_of_over {t : K.Tree r} {i : ι} (hi : t.1.head? = some (.inl i)) :
    ∃ j, (vmap hη f t).1.head? = some (.inl j) ∧ (f (canon hη t)).1.1 = K'.η j := by
  obtain ⟨j, hj⟩ := hgen i
  have hpt : (f (canon hη t)).1.1 = K'.η j := by
    rw [hfψ]; change ψ (canonPt t) = _; rw [canonPt_of_inl hi, hj]
  rcases (vmap hη f t).2.head_cases with ⟨j', hj'⟩ | ⟨s, hsS, hs⟩
  · refine ⟨j', hj', ?_⟩
    have hmem := Cover.mem_piece_inl (x := f (canon hη t)) hj'
    rw [hpt] at hmem ⊢
    rw [K'.eq_of_notMem_S (K'.η_mem j) hmem.1 (hη' j)]
  · have := Cover.eq_of_inr (x := f (canon hη t)) hs
    rw [hpt] at this
    exact absurd (this ▸ hsS) (hη' j)

include hfψ hS in
/-- The vertex of the image of the canonical point of a vertex over a special point lies over a
special point. -/
lemma vmap_inr_of_over {t : K.Tree r} {s : Z} (hs : t.1.head? = some (.inr s)) :
    ∃ s', (vmap hη f t).1.head? = some (.inr s') ∧ (f (canon hη t)).1.1 = s' := by
  have hsS : s ∈ K.S := by
    rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s₁, hs₁, h₁⟩
    · rw [hs] at hi; cases hi
    · rw [hs] at h₁; cases h₁; exact hs₁
  have hpt : (f (canon hη t)).1.1 = ψ s := by
    rw [hfψ]; change ψ (canonPt t) = _; rw [canonPt_of_inr hs]
  rcases (vmap hη f t).2.head_cases with ⟨j, hj⟩ | ⟨s', -, hs'⟩
  · have hmem := Cover.mem_piece_inl (x := f (canon hη t)) hj
    rw [hpt] at hmem
    exact absurd ((hS s).2 hsS) hmem.2
  · exact ⟨s', hs', Cover.eq_of_inr (x := f (canon hη t)) hs'⟩

include hη' hfψ hgen hS

/-- **Maps over `ψ` preserve canonical points.** -/
theorem preservesCanon_of_over : PreservesCanon hη hη' f := by
  intro t
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · obtain ⟨j, hj, hpt⟩ := vmap_inl_of_over hη hη' hfψ hgen hi
    exact Cover.ext (hpt.trans (canonPt_of_inl hj).symm) rfl
  · obtain ⟨s', hs', hpt⟩ := vmap_inr_of_over hη hfψ hS hs
    exact Cover.ext (hpt.trans (canonPt_of_inr hs').symm) rfl

/-- **Maps over `ψ` preserve the colours of vertices.** -/
theorem kind_vmap_of_over (t : K.Tree r) : Tree.kind (vmap hη f t) = Tree.kind t := by
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · obtain ⟨j, hj, -⟩ := vmap_inl_of_over hη hη' hfψ hgen hi
    rw [Tree.kind_eq_true_iff.2 ⟨j, hj⟩, Tree.kind_eq_true_iff.2 ⟨i, hi⟩]
  · obtain ⟨s', hs', -⟩ := vmap_inr_of_over hη hfψ hS hs
    rw [Tree.kind_eq_false_iff.2 ⟨s', hs'⟩, Tree.kind_eq_false_iff.2 ⟨s, hs⟩]

/-- **Continuous maps over `ψ` preserve sheets.** -/
theorem preservesSheets_of_over (hf : Continuous f) : PreservesSheets hη f := by
  intro x
  rcases x.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · obtain ⟨j, hj, -⟩ := vmap_inl_of_over hη hη' hfψ hgen hi
    rcases Cover.eq_or_adj_of_specializes ((canon_specializes_of_inl hη hi).map hf) with h | h
    · exact h.symm
    · exfalso
      have hfx : (f x).1.1 ∉ K'.S := by
        rw [hfψ]; exact fun h ↦ (Cover.mem_piece_inl hi).2 ((hS _).1 h)
      have hk : Tree.kind (f x).1.2 = true := by
        rcases (f x).1.2.2.head_cases with ⟨j', hj'⟩ | ⟨s', hs'S, hs'⟩
        · exact Tree.kind_eq_true_iff.2 ⟨j', hj'⟩
        · exact absurd (by rw [Cover.eq_of_inr hs']; exact hs'S) hfx
      exact Tree.kind_ne_of_adj h (hk.trans (Tree.kind_eq_true_iff.2 ⟨j, hj⟩).symm)
  · conv_lhs => rw [eq_canon_of_inr hη hs]
    rfl

end Over

end Canon

end CurveConfig

end TemperedFundamentalGroups
