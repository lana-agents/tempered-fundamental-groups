/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.GenericLift

/-!
# The tree covering of a configuration of curves

A *curve configuration* on a topological space `Z` (`CurveConfig`) is a finite family of closed
subsets `C i` ("components"), each with a generic point `η i`, covering `Z`, together with a
finite set `S` of closed points ("special points") containing all points lying on two different
components. The irreducible components of a noetherian quasi-sober `T₀` space of dimension `≤ 1`
form such a configuration (`TemperedFundamentalGroups.Topology.UniversalCovering`).

Let `Γ` be the bipartite incidence graph with vertex set `ι ⊕ Z`: the component `i` is joined
to the special point `s` if `s ∈ C i`. For a root `r : ι`, the vertices of the universal covering
tree of `Γ` are the reduced walks in `Γ` starting at `r` (`CurveConfig.Tree`), coded as lists
with the last vertex first. We glue copies of the pieces `C i \ S` and of the special points along
this tree (`CurveConfig.Cover`): the points are pairs `(z, t)` with `z` in the piece of the last
vertex of `t`, topologised as a subspace of `Z × Tree`, where the tree carries the Alexandrov
topology in which a special vertex specialises to its neighbours.

## Main results

* `CurveConfig.isCoveringMap_proj`: the first projection `Cover → Z` is a covering map.
* `CurveConfig.connectedSpace_cover`: the cover is connected.
* `CurveConfig.exists_lift`: every continuous map from the cover to a space `Y` lifts along every
  covering map `P → Y`, through every point of the fibre. In particular the cover is simply
  connected in the covering sense.
-/

universe u v

open Set Topology Filter

namespace TemperedFundamentalGroups

/-- A finite configuration of curves on a topological space: closed "components" with generic
points covering the space, meeting only in a finite set of closed "special" points. -/
structure CurveConfig (Z : Type u) [TopologicalSpace Z] (ι : Type v) where
  /-- The components. -/
  C : ι → Set Z
  isClosed_C : ∀ i, IsClosed (C i)
  /-- The generic points of the components. -/
  η : ι → Z
  η_mem : ∀ i, η i ∈ C i
  η_generic : ∀ i (U : Set Z), IsOpen U → (U ∩ C i).Nonempty → η i ∈ U
  /-- The special points. -/
  S : Set Z
  finite_S : S.Finite
  isClosed_singleton : ∀ s ∈ S, IsClosed ({s} : Set Z)
  cover : ∀ z, ∃ i, z ∈ C i
  mem_S : ∀ z i j, z ∈ C i → z ∈ C j → i ≠ j → z ∈ S

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} (K : CurveConfig Z ι)

section Basic

lemma isClosed_of_subset_S {A : Set Z} (hA : A ⊆ K.S) : IsClosed A := by
  rw [← biUnion_of_singleton A]
  exact (K.finite_S.subset hA).isClosed_biUnion fun s hs ↦ K.isClosed_singleton s (hA hs)

lemma eq_of_notMem_S {z : Z} {i j : ι} (hi : z ∈ K.C i) (hj : z ∈ K.C j) (hz : z ∉ K.S) :
    i = j := by
  by_contra h
  exact hz (K.mem_S z i j hi hj h)

/-- A component containing a given point. -/
noncomputable def comp (z : Z) : ι := (K.cover z).choose

lemma mem_comp (z : Z) : z ∈ K.C (K.comp z) := (K.cover z).choose_spec

lemma comp_eq {z : Z} {i : ι} (hi : z ∈ K.C i) (hz : z ∉ K.S) : K.comp z = i :=
  K.eq_of_notMem_S (K.mem_comp z) hi hz

variable [Finite ι]

/-- The piece `C i \ S` of a component is open. -/
lemma isOpen_piece (i : ι) : IsOpen (K.C i \ K.S) := by
  have : K.C i \ K.S = (K.S ∪ ⋃ j ∈ {j | j ≠ i}, K.C j)ᶜ := by
    ext z
    simp only [Set.mem_sdiff, mem_compl_iff, mem_union, mem_iUnion, mem_setOf_eq, not_or,
      not_exists]
    constructor
    · rintro ⟨hi, hS⟩
      exact ⟨hS, fun j hj hzj ↦ hj (K.eq_of_notMem_S hzj hi hS)⟩
    · rintro ⟨hS, h⟩
      refine ⟨?_, hS⟩
      by_contra hi
      exact h _ (fun he ↦ hi (he ▸ K.mem_comp z)) (K.mem_comp z)
  rw [this]
  exact (K.isClosed_of_subset_S subset_rfl |>.union
    ((toFinite _).isClosed_biUnion fun j _ ↦ K.isClosed_C j)).isOpen_compl

/-- The standard open neighbourhood of a special point `s`: remove the other special points and
the components not containing `s`. -/
def nbhdS (s : Z) : Set Z := (K.S \ {s})ᶜ ∩ (⋃ i ∈ {i | s ∉ K.C i}, K.C i)ᶜ

lemma isOpen_nbhdS (s : Z) : IsOpen (K.nbhdS s) :=
  (K.isClosed_of_subset_S sdiff_subset).isOpen_compl.inter
    ((toFinite _).isClosed_biUnion fun j _ ↦ K.isClosed_C j).isOpen_compl

omit [Finite ι] in
lemma mem_nbhdS_self (s : Z) : s ∈ K.nbhdS s := by
  simp [nbhdS]

omit [Finite ι] in
lemma notMem_S_of_mem_nbhdS {s y : Z} (hy : y ∈ K.nbhdS s) (hys : y ≠ s) : y ∉ K.S :=
  fun h ↦ hy.1 ⟨h, hys⟩

omit [Finite ι] in
lemma mem_C_of_mem_nbhdS {s y : Z} (hy : y ∈ K.nbhdS s) {i : ι} (hi : y ∈ K.C i) :
    s ∈ K.C i := by
  by_contra h
  exact hy.2 (mem_biUnion (x := i) h hi)

end Basic

section Graph

/-- Adjacency in the incidence graph of the configuration. -/
def Adj : ι ⊕ Z → ι ⊕ Z → Prop
  | .inl i, .inr s => s ∈ K.S ∧ s ∈ K.C i
  | .inr s, .inl i => s ∈ K.S ∧ s ∈ K.C i
  | .inl _, .inl _ => False
  | .inr _, .inr _ => False

lemma adj_comm {v w : ι ⊕ Z} : K.Adj v w ↔ K.Adj w v := by
  cases v <;> cases w <;> simp [Adj]

variable (r : ι)

/-- Reduced walks in the incidence graph starting at the component `r`, coded as lists with the
last vertex first. -/
def Red : List (ι ⊕ Z) → Prop
  | [] => False
  | [v] => v = .inl r
  | v :: u :: l => K.Adj v u ∧ l.head? ≠ some v ∧ Red (u :: l)

variable {K r}

lemma Red.ne_nil {l : List (ι ⊕ Z)} (h : K.Red r l) : l ≠ [] := by
  rintro rfl; exact h

lemma Red.tail {v : ι ⊕ Z} {l : List (ι ⊕ Z)} (h : K.Red r (v :: l)) (hl : l ≠ []) :
    K.Red r l := by
  obtain ⟨u, m, rfl⟩ := List.exists_cons_of_ne_nil hl
  exact h.2.2

lemma Red.adj {v u : ι ⊕ Z} {l : List (ι ⊕ Z)} (h : K.Red r (v :: u :: l)) : K.Adj v u := h.1

lemma Red.head_cases {l : List (ι ⊕ Z)} (h : K.Red r l) :
    (∃ i, l.head? = some (.inl i)) ∨ (∃ s ∈ K.S, l.head? = some (.inr s)) := by
  match l, h with
  | [.inl i], _ => exact .inl ⟨i, rfl⟩
  | [.inr s], h => exact absurd (show (Sum.inr s : ι ⊕ Z) = .inl r from h) Sum.inr_ne_inl
  | .inl i :: _ :: _, _ => exact .inl ⟨i, rfl⟩
  | .inr s :: .inl i :: _, h => exact .inr ⟨s, h.1.1, rfl⟩
  | .inr s :: .inr _ :: _, h => exact h.1.elim

omit [TopologicalSpace Z] in
open scoped Classical in
/-- The neighbour of a walk `l` over a vertex `v` adjacent to its last vertex: drop the last
vertex if the walk came from `v`, and append `v` otherwise. -/
noncomputable def nbr (l : List (ι ⊕ Z)) (v : ι ⊕ Z) : List (ι ⊕ Z) :=
  if l.tail.head? = some v then l.tail else v :: l

lemma red_nbr {l : List (ι ⊕ Z)} (hl : K.Red r l) {h v : ι ⊕ Z} (hh : l.head? = some h)
    (hv : K.Adj h v) : K.Red r (nbr l v) ∧ (nbr l v).head? = some v := by
  obtain ⟨h', m, rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
  obtain rfl : h' = h := by simpa using hh
  unfold nbr
  split_ifs with hm
  · obtain ⟨m', rfl⟩ : ∃ m', m = v :: m' := by
      match m, hm with
      | v' :: m', hm => exact ⟨m', by simpa using hm⟩
    exact ⟨hl.tail (by simp), rfl⟩
  · exact ⟨⟨K.adj_comm.1 hv, hm, hl⟩, rfl⟩

omit [TopologicalSpace Z] in
lemma nbr_adj (l : List (ι ⊕ Z)) (v : ι ⊕ Z) : (nbr l v).tail = l ∨ l.tail = nbr l v := by
  unfold nbr
  split_ifs
  · exact .inr rfl
  · exact .inl rfl

lemma eq_nbr {l l' : List (ι ⊕ Z)} (hl : K.Red r l) (hl' : K.Red r l')
    (hadj : l'.tail = l ∨ l.tail = l') {v : ι ⊕ Z} (hv : l'.head? = some v) : l' = nbr l v := by
  rcases hadj with hadj | hadj
  · obtain ⟨w, m, rfl⟩ := List.exists_cons_of_ne_nil hl'.ne_nil
    obtain rfl : w = v := by simpa using hv
    obtain rfl : m = l := hadj
    obtain ⟨h, k, rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
    unfold nbr
    rw [List.tail_cons, if_neg hl'.2.1]
  · obtain ⟨h, m, rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
    obtain rfl : m = l' := hadj
    unfold nbr
    rw [List.tail_cons, if_pos (by simpa using hv)]

lemma adj_head {l l' : List (ι ⊕ Z)} (hl : K.Red r l) (hl' : K.Red r l')
    (hadj : l'.tail = l ∨ l.tail = l') {a b : ι ⊕ Z} (ha : l.head? = some a)
    (hb : l'.head? = some b) : K.Adj a b := by
  rcases hadj with hadj | hadj
  · obtain ⟨w, m, rfl⟩ := List.exists_cons_of_ne_nil hl'.ne_nil
    obtain rfl : m = l := hadj
    obtain ⟨h, k, rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
    obtain rfl : h = a := by simpa using ha
    obtain rfl : w = b := by simpa using hb
    exact K.adj_comm.1 hl'.adj
  · obtain ⟨h, m, rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
    obtain rfl : m = l' := hadj
    obtain ⟨w, k, rfl⟩ := List.exists_cons_of_ne_nil hl'.ne_nil
    obtain rfl : h = a := by simpa using ha
    obtain rfl : w = b := by simpa using hb
    exact hl.adj

lemma head_inl_of_adj {l l' : List (ι ⊕ Z)} (hl : K.Red r l) (hl' : K.Red r l')
    (hadj : l'.tail = l ∨ l.tail = l') {s : Z} (hs : l.head? = some (.inr s)) :
    ∃ i, l'.head? = some (.inl i) ∧ s ∈ K.S ∧ s ∈ K.C i := by
  rcases hl'.head_cases with ⟨i, hi⟩ | ⟨s', -, hs'⟩
  · exact ⟨i, hi, adj_head hl hl' hadj hs hi⟩
  · exact (adj_head hl hl' hadj hs hs').elim

lemma head_inr_of_adj {l l' : List (ι ⊕ Z)} (hl : K.Red r l) (hl' : K.Red r l')
    (hadj : l'.tail = l ∨ l.tail = l') {i : ι} (hi : l.head? = some (.inl i)) :
    ∃ s, l'.head? = some (.inr s) ∧ s ∈ K.S ∧ s ∈ K.C i := by
  rcases hl'.head_cases with ⟨j, hj⟩ | ⟨s, -, hs⟩
  · exact (adj_head hl hl' hadj hi hj).elim
  · exact ⟨s, hs, adj_head hl hl' hadj hi hs⟩

end Graph

variable (r : ι)

/-- The universal covering tree of the incidence graph: reduced walks starting at `r`. -/
@[ext]
structure Tree where
  /-- The walk. -/
  val : List (ι ⊕ Z)
  property : K.Red r val

variable {K r}

/-- Adjacency in the tree. -/
def Tree.Adj (t t' : K.Tree r) : Prop := t'.1.tail = t.1 ∨ t.1.tail = t'.1

lemma Tree.adj_comm {t t' : K.Tree r} : t.Adj t' ↔ t'.Adj t := Or.comm

/-- The Alexandrov topology on the tree in which a vertex over a special point specialises to its
neighbours: a set is open if it contains the neighbours of each of its special vertices. -/
instance : TopologicalSpace (K.Tree r) where
  IsOpen U := ∀ t t' : K.Tree r, (∃ s, t.1.head? = some (.inr s)) → t.Adj t' → t ∈ U → t' ∈ U
  isOpen_univ := by simp
  isOpen_inter U V hU hV t t' hs ha ht := ⟨hU t t' hs ha ht.1, hV t t' hs ha ht.2⟩
  isOpen_sUnion F hF t t' hs ha := by
    rintro ⟨U, hU, ht⟩
    exact ⟨U, hU, hF U hU t t' hs ha ht⟩

namespace Tree

lemma isOpen_iff {U : Set (K.Tree r)} :
    IsOpen U ↔ ∀ t t' : K.Tree r, (∃ s, t.1.head? = some (.inr s)) → t.Adj t' → t ∈ U →
      t' ∈ U := Iff.rfl

lemma isOpen_singleton {t : K.Tree r} {i : ι} (ht : t.1.head? = some (.inl i)) :
    IsOpen ({t} : Set (K.Tree r)) := by
  rintro t₁ t' ⟨s, hs⟩ - rfl
  rw [ht] at hs
  cases hs

/-- The star of a vertex: the vertex and its neighbours. -/
def star (w : K.Tree r) : Set (K.Tree r) := {t | t = w ∨ w.Adj t}

lemma isOpen_star {w : K.Tree r} {s : Z} (hw : w.1.head? = some (.inr s)) : IsOpen (star w) := by
  rintro t₁ t' ⟨s', hs'⟩ ha (rfl | ht₁)
  · exact .inr ha
  · obtain ⟨i, hi, -⟩ := head_inl_of_adj w.2 t₁.2 ht₁ hw
    rw [hi] at hs'
    cases hs'

/-- The neighbour of a vertex over an adjacent vertex of the incidence graph. -/
noncomputable def nbr (t : K.Tree r) {h v : ι ⊕ Z} (hh : t.1.head? = some h) (hv : K.Adj h v) :
    K.Tree r :=
  ⟨CurveConfig.nbr t.1 v, (red_nbr t.2 hh hv).1⟩

lemma nbr_head (t : K.Tree r) {h v : ι ⊕ Z} (hh : t.1.head? = some h) (hv : K.Adj h v) :
    (t.nbr hh hv).1.head? = some v :=
  (red_nbr t.2 hh hv).2

lemma adj_nbr (t : K.Tree r) {h v : ι ⊕ Z} (hh : t.1.head? = some h) (hv : K.Adj h v) :
    t.Adj (t.nbr hh hv) :=
  nbr_adj t.1 v

lemma eq_nbr {t t' : K.Tree r} (hadj : t.Adj t') {h v : ι ⊕ Z} (hh : t.1.head? = some h)
    (hv : K.Adj h v) (hv' : t'.1.head? = some v) : t' = t.nbr hh hv :=
  Tree.ext (CurveConfig.eq_nbr t.2 t'.2 hadj hv')

end Tree

section Cover

/-- The piece of `Z` attached to a vertex of the incidence graph. -/
def piece : Option (ι ⊕ Z) → Set Z
  | some (.inl i) => K.C i \ K.S
  | some (.inr s) => {s}
  | none => ∅

variable (K r)

/-- The tree covering: pairs `(z, t)` with `z` in the piece of the last vertex of `t`. -/
abbrev Cover : Type _ := {x : Z × K.Tree r // x.1 ∈ K.piece x.2.1.head?}

/-- The projection of the tree covering to `Z`. -/
def proj (x : K.Cover r) : Z := x.1.1

variable {K r}

lemma continuous_proj : Continuous (K.proj r) :=
  continuous_fst.comp continuous_subtype_val

lemma Cover.ext {x y : K.Cover r} (h1 : x.1.1 = y.1.1) (h2 : x.1.2 = y.1.2) : x = y :=
  Subtype.ext (Prod.ext h1 h2)

lemma Cover.mem_piece_inl {x : K.Cover r} {i : ι} (h : x.1.2.1.head? = some (.inl i)) :
    x.1.1 ∈ K.C i \ K.S := by
  have := x.2; rwa [h] at this

lemma Cover.eq_of_inr {x : K.Cover r} {s : Z} (h : x.1.2.1.head? = some (.inr s)) :
    x.1.1 = s := by
  have := x.2; rwa [h] at this

open scoped Classical in
/-- The vertex of the tree for the point `z` of the component of a vertex `t` over `i`: `t` itself
if `z` is not special, and the neighbour of `t` over `z` otherwise. -/
noncomputable def inclT (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) (z : K.C i) :
    K.Tree r :=
  if hz : z.1 ∈ K.S then t.nbr h (v := .inr z.1) ⟨hz, z.2⟩ else t

lemma inclT_mem (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) (z : K.C i) :
    z.1 ∈ K.piece (inclT t i h z).1.head? := by
  unfold inclT
  split_ifs with hz
  · rw [Tree.nbr_head]; rfl
  · rw [h]; exact ⟨z.2, hz⟩

/-- The copy of the component of a vertex `t` over `i` inside the tree covering. -/
noncomputable def incl (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) (z : K.C i) :
    K.Cover r :=
  ⟨(z.1, inclT t i h z), inclT_mem t i h z⟩

lemma incl_of_notMem {t : K.Tree r} {i : ι} {h : t.1.head? = some (.inl i)} {z : K.C i}
    (hz : z.1 ∉ K.S) : (incl t i h z).1 = (z.1, t) := by
  simp [incl, inclT, hz]

lemma incl_of_mem {t : K.Tree r} {i : ι} {h : t.1.head? = some (.inl i)} {z : K.C i}
    (hz : z.1 ∈ K.S) : (incl t i h z).1 = (z.1, t.nbr h (v := .inr z.1) ⟨hz, z.2⟩) := by
  simp [incl, inclT, hz]

lemma proj_incl (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) (z : K.C i) :
    K.proj r (incl t i h z) = z.1 := rfl

lemma continuous_inclT (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) :
    Continuous (inclT t i h) := by
  rw [continuous_def]
  intro V hV
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  by_cases hzS : z.1 ∈ K.S
  · refine ⟨Subtype.val ⁻¹' (K.S \ {z.1})ᶜ, fun z' hz' ↦ ?_,
      (K.isClosed_of_subset_S sdiff_subset).isOpen_compl.preimage continuous_subtype_val,
      by simp⟩
    by_cases hz'S : z'.1 ∈ K.S
    · obtain rfl : z' = z := Subtype.ext (by by_contra hne; exact hz' ⟨hz'S, hne⟩)
      exact hz
    · change inclT t i h z' ∈ V
      have hz' : inclT t i h z ∈ V := hz
      rw [inclT, dif_pos hzS] at hz'
      rw [inclT, dif_neg hz'S]
      exact hV _ t ⟨z.1, Tree.nbr_head _ _ _⟩ (Tree.adj_comm.1 (Tree.adj_nbr _ _ _)) hz'
  · refine ⟨Subtype.val ⁻¹' K.Sᶜ, fun z' hz' ↦ ?_,
      (K.isClosed_of_subset_S subset_rfl).isOpen_compl.preimage continuous_subtype_val, hzS⟩
    change inclT t i h z' ∈ V
    have hzV : inclT t i h z ∈ V := hz
    rw [inclT, dif_neg hzS] at hzV
    rwa [inclT, dif_neg (show z'.1 ∉ K.S from hz')]

lemma continuous_incl (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) :
    Continuous (incl t i h) :=
  (continuous_subtype_val.prodMk (continuous_inclT t i h)).subtype_mk _

end Cover

section Covering

variable [Finite ι]

open scoped Classical in
/-- The local sections of the tree covering over the piece of a component. -/
noncomputable def secC {i : ι} {z : Z} (hz : z ∈ K.C i \ K.S)
    (t : {t : K.Tree r // t.1.head? = some (.inl i)}) (y : Z) : K.Cover r :=
  if hy : y ∈ K.C i \ K.S then ⟨(y, t.1), show y ∈ K.piece t.1.1.head? by rw [t.2]; exact hy⟩
  else ⟨(z, t.1), show z ∈ K.piece t.1.1.head? by rw [t.2]; exact hz⟩

omit [Finite ι] in
lemma secC_of_mem {i : ι} {z : Z} (hz : z ∈ K.C i \ K.S)
    (t : {t : K.Tree r // t.1.head? = some (.inl i)}) {y : Z} (hy : y ∈ K.C i \ K.S) :
    (secC hz t y).1 = (y, t.1) := by
  simp [secC, hy]

open scoped Classical in
/-- The local sections of the tree covering over the neighbourhood of a special point. -/
noncomputable def secS {s : Z} (hs : s ∈ K.S)
    (w : {w : K.Tree r // w.1.head? = some (.inr s)}) (y : Z) : K.Cover r :=
  if hy : y ∈ K.nbhdS s ∧ y ≠ s then
    ⟨(y, w.1.nbr w.2 (v := .inl (K.comp y)) ⟨hs, K.mem_C_of_mem_nbhdS hy.1 (K.mem_comp y)⟩),
      by dsimp only; rw [Tree.nbr_head]; exact ⟨K.mem_comp y, K.notMem_S_of_mem_nbhdS hy.1 hy.2⟩⟩
  else ⟨(s, w.1), show s ∈ K.piece w.1.1.head? by rw [w.2]; rfl⟩

omit [Finite ι] in
lemma secS_self {s : Z} (hs : s ∈ K.S) (w : {w : K.Tree r // w.1.head? = some (.inr s)}) :
    (secS hs w s).1 = (s, w.1) := by
  simp [secS]

omit [Finite ι] in
lemma secS_of_ne {s : Z} (hs : s ∈ K.S) (w : {w : K.Tree r // w.1.head? = some (.inr s)})
    {y : Z} (hy : y ∈ K.nbhdS s) (hys : y ≠ s) {i : ι} (hi : y ∈ K.C i) :
    (secS hs w y).1 = (y, w.1.nbr w.2 (v := .inl i) ⟨hs, K.mem_C_of_mem_nbhdS hy hi⟩) := by
  obtain rfl : K.comp y = i := K.comp_eq hi (K.notMem_S_of_mem_nbhdS hy hys)
  simp [secS, hy, hys]

omit [Finite ι] in
lemma secS_fst {s : Z} (hs : s ∈ K.S) (w : {w : K.Tree r // w.1.head? = some (.inr s)})
    {y : Z} (hy : y ∈ K.nbhdS s) : (secS hs w y).1.1 = y := by
  by_cases hys : y = s
  · subst hys; rw [secS_self]
  · rw [secS_of_ne hs w hy hys (K.mem_comp y)]

lemma continuousOn_secS {s : Z} (hs : s ∈ K.S)
    (w : {w : K.Tree r // w.1.head? = some (.inr s)}) : ContinuousOn (secS hs w) (K.nbhdS s) := by
  rw [IsEmbedding.subtypeVal.isInducing.continuousOn_iff]
  have hτ : ContinuousOn (fun y ↦ (secS hs w y).1.2) (K.nbhdS s) := by
    rw [continuousOn_open_iff (K.isOpen_nbhdS s)]
    intro V hV
    rw [isOpen_iff_forall_mem_open]
    rintro y ⟨hyU, hyV⟩
    by_cases hys : y = s
    · subst hys
      have hwV : w.1 ∈ V := by
        have : (secS hs w y).1.2 ∈ V := hyV
        rwa [secS_self] at this
      refine ⟨K.nbhdS y, fun y' hy' ↦ ⟨hy', ?_⟩, K.isOpen_nbhdS y, hyU⟩
      change (secS hs w y').1.2 ∈ V
      by_cases hy's : y' = y
      · subst hy's; rw [secS_self]; exact hwV
      · rw [secS_of_ne hs w hy' hy's (K.mem_comp y')]
        exact hV _ _ ⟨y, w.2⟩
          (Tree.adj_nbr w.1 w.2 (v := .inl (K.comp y'))
            ⟨hs, K.mem_C_of_mem_nbhdS hy' (K.mem_comp y')⟩) hwV
    · have hyS := K.notMem_S_of_mem_nbhdS hyU hys
      refine ⟨K.nbhdS s ∩ (K.C (K.comp y) \ K.S), fun y' hy' ↦ ⟨hy'.1, ?_⟩,
        (K.isOpen_nbhdS s).inter (K.isOpen_piece _), hyU, K.mem_comp y, hyS⟩
      have hy's : y' ≠ s := fun h ↦ hy'.2.2 (h ▸ hs)
      change (secS hs w y').1.2 ∈ V
      have : (secS hs w y).1.2 ∈ V := hyV
      rw [secS_of_ne hs w hyU hys (K.mem_comp y)] at this
      rw [secS_of_ne hs w hy'.1 hy's hy'.2.1]
      exact this
  refine (continuousOn_id.prodMk hτ).congr fun y hy ↦ ?_
  simp only [Function.comp_apply, id_eq]
  exact Prod.ext (secS_fst hs w hy) rfl

/-- The projection of the tree covering is a covering map. -/
theorem isCoveringMap_proj : IsCoveringMap (K.proj r) := by
  intro z
  by_cases hz : z ∈ K.S
  · refine isEvenlyCovered_of_sections continuous_proj (K.isOpen_nbhdS z) (K.mem_nbhdS_self z)
      (secS hz) (continuousOn_secS hz) (fun w y hy ↦ secS_fst hz w hy) (fun w ↦ ?_)
      (fun e he ↦ ?_)
    · have : secS hz w '' K.nbhdS z =
          Subtype.val ⁻¹' (K.nbhdS z ×ˢ Tree.star w.1) := by
        ext e
        constructor
        · rintro ⟨y, hy, rfl⟩
          by_cases hyz : y = z
          · subst hyz
            simp only [mem_preimage, mem_prod]
            rw [secS_self]
            exact ⟨hy, .inl rfl⟩
          · simp only [mem_preimage, mem_prod]
            rw [secS_of_ne hz w hy hyz (K.mem_comp y)]
            exact ⟨hy, .inr (Tree.adj_nbr w.1 w.2 (v := .inl (K.comp y))
              ⟨hz, K.mem_C_of_mem_nbhdS hy (K.mem_comp y)⟩)⟩
        · rintro ⟨he1, he2 | he2⟩
          · have := Cover.eq_of_inr (x := e) (he2 ▸ w.2)
            refine ⟨z, K.mem_nbhdS_self z, Cover.ext ?_ ?_⟩ <;> rw [secS_self]
            · exact this.symm
            · exact he2.symm
          · obtain ⟨i, hi, -, hzi⟩ := head_inl_of_adj w.1.2 e.1.2.2 he2 w.2
            have hm := Cover.mem_piece_inl hi
            have hne : e.1.1 ≠ z := fun h ↦ hm.2 (h ▸ hz)
            refine ⟨e.1.1, he1, Cover.ext ?_ ?_⟩ <;> rw [secS_of_ne hz w he1 hne hm.1]
            exact (Tree.eq_nbr he2 w.2 (v := .inl i) ⟨hz, hzi⟩ hi).symm
      rw [this]
      exact ((K.isOpen_nbhdS z).prod (Tree.isOpen_star w.2)).preimage continuous_subtype_val
    · change e.1.1 ∈ K.nbhdS z at he
      rcases e.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, hs, hs'⟩
      · have hm := Cover.mem_piece_inl hi
        have hne : e.1.1 ≠ z := fun h ↦ hm.2 (h ▸ hz)
        have hzi := K.mem_C_of_mem_nbhdS he hm.1
        let w₀ : {w : K.Tree r // w.1.head? = some (.inr z)} :=
          ⟨e.1.2.nbr hi (v := .inr z) ⟨hz, hzi⟩, Tree.nbr_head _ _ _⟩
        refine ⟨w₀, Cover.ext ?_ ?_, fun w' hw' ↦ ?_⟩ <;>
          try rw [proj, secS_of_ne hz _ he hne hm.1]
        · exact (Tree.eq_nbr (Tree.adj_comm.1 (Tree.adj_nbr e.1.2 hi (v := .inr z) ⟨hz, hzi⟩))
            w₀.2 (v := .inl i) ⟨hz, hzi⟩ hi).symm
        · have h2 := congrArg (fun x : K.Cover r ↦ x.1.2) hw'
          simp only [proj] at h2
          rw [secS_of_ne hz _ he hne hm.1] at h2
          have hadj : e.1.2.Adj w'.1 := by
            rw [← h2]; exact Tree.adj_comm.1 (Tree.adj_nbr w'.1 w'.2 (v := .inl i) ⟨hz, hzi⟩)
          exact Subtype.ext (Tree.eq_nbr hadj hi (v := .inr z) ⟨hz, hzi⟩ w'.2)
      · have he' := Cover.eq_of_inr hs'
        obtain rfl : s = z := by
          by_contra h
          exact he.1 ⟨by rw [he']; exact hs, by rw [he']; exact h⟩
        refine ⟨⟨e.1.2, hs'⟩, ?_, fun w' hw' ↦ ?_⟩
        · change secS hz _ e.1.1 = e
          rw [he']
          exact Cover.ext (by rw [secS_self, he']) (by rw [secS_self])
        · have h2 := congrArg (fun x : K.Cover r ↦ x.1.2) hw'
          simp only [proj, he', secS_self] at h2
          exact Subtype.ext h2
  · have hzc : z ∈ K.C (K.comp z) \ K.S := ⟨K.mem_comp z, hz⟩
    refine isEvenlyCovered_of_sections continuous_proj (K.isOpen_piece _) hzc (secC hzc)
      (fun t ↦ ?_) (fun t y hy ↦ ?_) (fun t ↦ ?_) (fun e he ↦ ?_)
    · rw [continuousOn_iff_continuous_restrict]
      have : (K.C (K.comp z) \ K.S).restrict (secC hzc t) = fun y ↦ (⟨(y.1, t.1),
          show y.1 ∈ K.piece t.1.1.head? by rw [t.2]; exact y.2⟩ : K.Cover r) := by
        funext y
        exact Subtype.ext (secC_of_mem hzc t y.2)
      rw [this]
      exact (continuous_subtype_val.prodMk continuous_const).subtype_mk _
    · change (secC hzc t y).1.1 = y
      rw [secC_of_mem hzc t hy]
    · have : secC hzc t '' (K.C (K.comp z) \ K.S) = (fun e : K.Cover r ↦ e.1.2) ⁻¹' {t.1} := by
        ext e
        constructor
        · rintro ⟨y, hy, rfl⟩
          simp only [mem_preimage, mem_singleton_iff]
          rw [secC_of_mem hzc t hy]
        · intro he
          have he' : e.1.2 = t.1 := he
          have hm := Cover.mem_piece_inl (x := e) (he' ▸ t.2)
          refine ⟨e.1.1, hm, Cover.ext ?_ ?_⟩ <;> rw [secC_of_mem hzc t hm]
          exact he'.symm
      rw [this]
      exact (Tree.isOpen_singleton t.2).preimage (continuous_snd.comp continuous_subtype_val)
    · change e.1.1 ∈ K.C (K.comp z) \ K.S at he
      rcases e.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, hs, hs'⟩
      · have hm := Cover.mem_piece_inl hi
        obtain rfl : i = K.comp z := K.eq_of_notMem_S hm.1 he.1 hm.2
        refine ⟨⟨e.1.2, hi⟩, Cover.ext ?_ ?_, fun t' ht' ↦ ?_⟩ <;>
          try rw [proj, secC_of_mem hzc _ he]
        have h2 := congrArg (fun x : K.Cover r ↦ x.1.2) ht'
        simp only [proj] at h2
        rw [secC_of_mem hzc _ he] at h2
        exact Subtype.ext h2
      · exact absurd (Cover.eq_of_inr hs' ▸ hs) he.2

end Covering

section Incl

lemma Red.ne_nil_of_inr {s : Z} {m : List (ι ⊕ Z)} (hl : K.Red r (.inr s :: m)) : m ≠ [] := by
  rintro rfl
  exact Sum.inr_ne_inl hl

lemma Red.inr_cons {s : Z} {m : List (ι ⊕ Z)} (hl : K.Red r (.inr s :: m)) :
    ∃ i, m.head? = some (.inl i) ∧ s ∈ K.S ∧ s ∈ K.C i :=
  head_inl_of_adj hl (hl.tail hl.ne_nil_of_inr) (.inr rfl) rfl

/-- A point over a component vertex lies on the copy of that component. -/
lemma eq_incl_of_inl (x : K.Cover r) {i : ι} (h : x.1.2.1.head? = some (.inl i)) :
    x = incl x.1.2 i h ⟨x.1.1, (Cover.mem_piece_inl h).1⟩ :=
  Cover.ext (by rw [incl_of_notMem (Cover.mem_piece_inl h).2])
    (by rw [incl_of_notMem (Cover.mem_piece_inl h).2])

/-- A point over a special vertex lies on the copy of each adjacent component. -/
lemma eq_incl_of_inr (x : K.Cover r) {s : Z} (hs : x.1.2.1.head? = some (.inr s)) {t : K.Tree r}
    {i : ι} (h : t.1.head? = some (.inl i)) (hadj : t.Adj x.1.2) (hsi : s ∈ K.C i) :
    x = incl t i h ⟨s, hsi⟩ := by
  have hx := Cover.eq_of_inr hs
  obtain ⟨-, -, hS, -⟩ := head_inl_of_adj x.1.2.2 t.2 (Tree.adj_comm.1 hadj) hs
  refine Cover.ext ?_ ?_ <;> rw [incl_of_mem (z := ⟨s, hsi⟩) hS]
  · exact hx
  · exact Tree.eq_nbr hadj h (v := .inr s) ⟨hS, hsi⟩ hs

lemma exists_eq_incl (x : K.Cover r) :
    ∃ (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) (z : K.C i), x = incl t i h z := by
  rcases x.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · exact ⟨_, _, _, _, eq_incl_of_inl x hi⟩
  · obtain ⟨u, m, hum⟩ := List.exists_cons_of_ne_nil x.1.2.2.ne_nil
    have hu : u = .inr s := by rw [hum] at hs; simpa using hs
    subst hu
    have hl : K.Red r (.inr s :: m) := hum ▸ x.1.2.2
    obtain ⟨i, hi, -, hsi⟩ := hl.inr_cons
    let t : K.Tree r := ⟨m, hl.tail hl.ne_nil_of_inr⟩
    exact ⟨t, i, hi, _, eq_incl_of_inr x hs hi (.inl (by rw [hum]; rfl)) hsi⟩

variable (K) in
lemma generic_subtype (i : ι) :
    ∀ U : Set (K.C i), IsOpen U → U.Nonempty → (⟨K.η i, K.η_mem i⟩ : K.C i) ∈ U := by
  intro U hU ⟨x, hx⟩
  obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
  exact K.η_generic i V hV ⟨x.1, hx, x.2⟩

instance (i : ι) : PreconnectedSpace (K.C i) :=
  preconnectedSpace_of_generic (K.generic_subtype i)

variable (K r) in
/-- The root of the tree. -/
def root : K.Tree r := ⟨[.inl r], rfl⟩

variable (K r) in
/-- The base point of the tree covering over a point `z₀` of the root component. -/
noncomputable def base {z₀ : Z} (hz₀ : z₀ ∈ K.C r) : K.Cover r :=
  incl (root K r) r rfl ⟨z₀, hz₀⟩

lemma proj_base {z₀ : Z} (hz₀ : z₀ ∈ K.C r) : K.proj r (base K r hz₀) = z₀ := rfl

/-- The tree covering is connected. -/
theorem connectedSpace_cover {z₀ : Z} (hz₀ : z₀ ∈ K.C r) : ConnectedSpace (K.Cover r) := by
  let b := base K r hz₀
  have hrange : ∀ (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) (z' : K.C i),
      incl t i h z' ∈ connectedComponent b → ∀ z, incl t i h z ∈ connectedComponent b := by
    intro t i h z' hz' z
    rw [connectedComponent_eq hz']
    exact (isPreconnected_range (continuous_incl t i h)).subset_connectedComponent
      ⟨z', rfl⟩ ⟨z, rfl⟩
  have key : ∀ (l : List (ι ⊕ Z)) (hl : K.Red r l),
      (∀ i (h : l.head? = some (.inl i)) z, incl ⟨l, hl⟩ i h z ∈ connectedComponent b) ∧
      (∀ x : K.Cover r, x.1.2.1 = l → x ∈ connectedComponent b) := by
    intro l
    induction l with
    | nil => exact fun hl ↦ hl.elim
    | cons v m ih =>
      intro hl
      have hcomp : (∀ i (h : (v :: m).head? = some (.inl i)) z,
          incl ⟨v :: m, hl⟩ i h z ∈ connectedComponent b) →
          (∀ x : K.Cover r, x.1.2.1 = v :: m → x ∈ connectedComponent b) := by
        intro H x hx
        rcases x.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
        · rw [eq_incl_of_inl x hi]
          have : x.1.2 = ⟨v :: m, hl⟩ := Tree.ext hx
          have hi' := hi
          rw [hx] at hi'
          convert H i hi' ⟨x.1.1, (Cover.mem_piece_inl hi).1⟩
        · rw [hx] at hs
          obtain rfl : v = .inr s := by simpa using hs
          obtain ⟨i, hi, -, hsi⟩ := hl.inr_cons
          have hadj : (⟨m, hl.tail hl.ne_nil_of_inr⟩ : K.Tree r).Adj x.1.2 := .inl (by rw [hx]; rfl)
          rw [eq_incl_of_inr x (by rw [hx]; rfl) hi hadj hsi]
          exact (ih (hl.tail hl.ne_nil_of_inr)).1 i hi _
      refine ⟨?_, fun x hx ↦ hcomp ?_ x hx⟩ <;>
      · intro i h
        obtain rfl : v = .inl i := by simpa using h
        rcases m with _ | ⟨w, m⟩
        · obtain rfl : i = r := Sum.inl_injective hl
          exact hrange _ _ _ ⟨z₀, hz₀⟩ (mem_connectedComponent)
        · obtain ⟨s, hs, hS, hsi⟩ := head_inr_of_adj hl (hl.tail (by simp)) (.inr rfl) h
          obtain rfl : w = .inr s := by simpa using hs
          refine hrange _ _ _ ⟨s, hsi⟩ ((ih (hl.tail (by simp))).2 _ ?_)
          rw [incl_of_mem (z := ⟨s, hsi⟩) hS]
          change nbr (.inl i :: .inr s :: m) (.inr s) = .inr s :: m
          unfold nbr; simp
  exact connectedSpace_iff_connectedComponent.2
    ⟨b, eq_univ_of_forall fun x ↦ (key x.1.2.1 x.1.2.2).2 x rfl⟩

end Incl

section Lift

variable {Y P : Type*} [TopologicalSpace Y] [TopologicalSpace P]

open scoped Classical in
/-- A lift of `g` on the copy of the component of the vertex `t`, through `y` at `x`. -/
noncomputable def liftAt (q : P → Y) (g : K.Cover r → Y) (t : K.Tree r) (i : ι)
    (h : t.1.head? = some (.inl i)) (x : Z) (y : P) : Z → P :=
  if H : ∃ f : K.C i → P, Continuous f ∧ (∀ z, q (f z) = g (incl t i h z)) ∧
      ∃ hx : x ∈ K.C i, f ⟨x, hx⟩ = y then
    fun z ↦ if hz : z ∈ K.C i then H.choose ⟨z, hz⟩ else y
  else fun _ ↦ y

lemma liftAt_spec {q : P → Y} (hq : IsCoveringMap q) {g : K.Cover r → Y} (hg : Continuous g)
    (t : K.Tree r) (i : ι) (h : t.1.head? = some (.inl i)) {x : Z} (hx : x ∈ K.C i) {y : P}
    (hy : q y = g (incl t i h ⟨x, hx⟩)) :
    Continuous (fun z : K.C i ↦ liftAt q g t i h x y z) ∧
      (∀ z : K.C i, q (liftAt q g t i h x y z) = g (incl t i h z)) ∧
      liftAt q g t i h x y x = y := by
  have H : ∃ f : K.C i → P, Continuous f ∧ (∀ z, q (f z) = g (incl t i h z)) ∧
      ∃ hx : x ∈ K.C i, f ⟨x, hx⟩ = y := by
    obtain ⟨f, hf, hqf, hfx⟩ := exists_lift_of_generic hq (K.generic_subtype i)
      (hg.comp (continuous_incl t i h)) ⟨x, hx⟩ y hy
    exact ⟨f, hf, fun z ↦ congrFun hqf z, hx, hfx⟩
  have e : (fun z : K.C i ↦ liftAt q g t i h x y z) = H.choose := by
    funext z
    simp only [liftAt, dif_pos H, dif_pos z.2]
  refine ⟨?_, fun z ↦ ?_, ?_⟩
  · rw [e]; exact H.choose_spec.1
  · rw [show liftAt q g t i h x y z = H.choose z from congrFun e z]
    exact H.choose_spec.2.1 z
  · rw [show liftAt q g t i h x y x = H.choose ⟨x, hx⟩ from congrFun e ⟨x, hx⟩]
    exact H.choose_spec.2.2.2

lemma lift_unique {q : P → Y} (hq : IsCoveringMap q) {i : ι} {f₁ f₂ : K.C i → P}
    (h₁ : Continuous f₁) (h₂ : Continuous f₂) (he : ∀ z, q (f₁ z) = q (f₂ z)) (z : K.C i)
    (hz : f₁ z = f₂ z) : f₁ = f₂ :=
  hq.eq_of_comp_eq h₁ h₂ (funext he) z hz

variable (q : P → Y) (g : K.Cover r → Y) (z₀ : Z) (y₀ : P)

open scoped Classical in
/-- The lift of `g` on the copy of the component of a vertex, defined by recursion along the
walk from the root. -/
noncomputable def liftF : List (ι ⊕ Z) → Z → P
  | [] => fun _ ↦ y₀
  | .inr s :: l => fun _ ↦ liftF l s
  | [.inl i] => if h : K.Red r [.inl i] then liftAt q g ⟨[.inl i], h⟩ i rfl z₀ y₀ else fun _ ↦ y₀
  | .inl i :: .inr s :: l =>
    if h : K.Red r (.inl i :: .inr s :: l) then
      liftAt q g ⟨_, h⟩ i rfl s (liftF (.inr s :: l) s)
    else fun _ ↦ y₀
  | .inl _ :: .inl _ :: _ => fun _ ↦ y₀

variable {q g z₀ y₀}

theorem liftF_spec (hq : IsCoveringMap q) (hg : Continuous g) (hz₀ : z₀ ∈ K.C r)
    (hy₀ : q y₀ = g (base K r hz₀)) : ∀ (l : List (ι ⊕ Z)) (hl : K.Red r l),
    (∀ i (h : l.head? = some (.inl i)), Continuous (fun z : K.C i ↦ liftF q g z₀ y₀ l z) ∧
      ∀ z : K.C i, q (liftF q g z₀ y₀ l z) = g (incl ⟨l, hl⟩ i h z)) ∧
    (∀ x : K.Cover r, x.1.2.1 = l → q (liftF q g z₀ y₀ l x.1.1) = g x)
  | [], hl => hl.elim
  | [.inl i], hl => by
    obtain rfl : i = r := Sum.inl_injective hl
    have H := liftAt_spec hq hg ⟨[.inl i], hl⟩ i rfl hz₀ hy₀
    have e : liftF q g z₀ y₀ [.inl i] = liftAt q g ⟨[.inl i], hl⟩ i rfl z₀ y₀ := by
      simp only [liftF, dif_pos hl]
    have h1 : ∀ i' (h : [Sum.inl i].head? = some (.inl i')),
        Continuous (fun z : K.C i' ↦ liftF q g z₀ y₀ [.inl i] z) ∧
        ∀ z : K.C i', q (liftF q g z₀ y₀ [.inl i] z) = g (incl ⟨[.inl i], hl⟩ i' h z) := by
      intro i' h
      obtain rfl : i = i' := by simpa using h
      rw [e]; exact ⟨H.1, H.2.1⟩
    refine ⟨h1, fun x hx ↦ ?_⟩
    rcases x.1.2.2.head_cases with ⟨j, hj⟩ | ⟨s, -, hs⟩
    · have hm := Cover.mem_piece_inl hj
      have hj' := hj
      rw [hx] at hj'
      have : x = incl ⟨_, hl⟩ j hj' ⟨x.1.1, hm.1⟩ := Cover.ext
        (by rw [incl_of_notMem hm.2]) (by rw [incl_of_notMem hm.2]; exact Tree.ext hx)
      calc _ = _ := (h1 j hj').2 ⟨x.1.1, hm.1⟩
        _ = g x := by rw [← this]
    · rw [hx] at hs; simp at hs
  | .inl i :: .inr s :: l, hl => by
    have ih := liftF_spec hq hg hz₀ hy₀ (.inr s :: l) (hl.tail (by simp))
    have hsi : s ∈ K.C i := hl.1.2
    have hS : s ∈ K.S := hl.1.1
    let t : K.Tree r := ⟨_, hl⟩
    have hanchor : q (liftF q g z₀ y₀ (.inr s :: l) s) = g (incl t i rfl ⟨s, hsi⟩) := by
      refine ih.2 _ ?_
      rw [incl_of_mem (z := ⟨s, hsi⟩) hS]
      change nbr (.inl i :: .inr s :: l) (.inr s) = .inr s :: l
      unfold nbr; simp
    have H := liftAt_spec hq hg t i rfl hsi hanchor
    have e : liftF q g z₀ y₀ (.inl i :: .inr s :: l) =
        liftAt q g t i rfl s (liftF q g z₀ y₀ (.inr s :: l) s) := by
      simp only [liftF, dif_pos hl]; rfl
    have h1 : ∀ i' (h : (Sum.inl i :: Sum.inr s :: l).head? = some (.inl i')),
        Continuous (fun z : K.C i' ↦ liftF q g z₀ y₀ (.inl i :: .inr s :: l) z) ∧
        ∀ z : K.C i', q (liftF q g z₀ y₀ (.inl i :: .inr s :: l) z) =
          g (incl ⟨_, hl⟩ i' h z) := by
      intro i' h
      obtain rfl : i = i' := by simpa using h
      rw [e]; exact ⟨H.1, H.2.1⟩
    refine ⟨h1, fun x hx ↦ ?_⟩
    rcases x.1.2.2.head_cases with ⟨j, hj⟩ | ⟨s', -, hs'⟩
    · have hm := Cover.mem_piece_inl hj
      have hj' := hj
      rw [hx] at hj'
      have : x = incl ⟨_, hl⟩ j hj' ⟨x.1.1, hm.1⟩ := Cover.ext
        (by rw [incl_of_notMem hm.2]) (by rw [incl_of_notMem hm.2]; exact Tree.ext hx)
      calc _ = _ := (h1 j hj').2 ⟨x.1.1, hm.1⟩
        _ = g x := by rw [← this]
    · rw [hx] at hs'; simp at hs'
  | .inl _ :: .inl _ :: _, hl => hl.1.elim
  | .inr s :: l, hl => by
    have ih := liftF_spec hq hg hz₀ hy₀ l (hl.tail hl.ne_nil_of_inr)
    refine ⟨fun i h ↦ by simp at h, fun x hx ↦ ?_⟩
    obtain ⟨i, hi, -, hsi⟩ := hl.inr_cons
    have hs : x.1.2.1.head? = some (.inr s) := by rw [hx]; rfl
    have hadj : (⟨l, hl.tail hl.ne_nil_of_inr⟩ : K.Tree r).Adj x.1.2 := .inl (by rw [hx]; rfl)
    have hx1 := Cover.eq_of_inr hs
    conv_rhs => rw [eq_incl_of_inr x hs hi hadj hsi]
    rw [hx1]
    exact (ih.1 i hi).2 ⟨s, hsi⟩

lemma incl_snd_cons {i : ι} {s : Z} {m : List (ι ⊕ Z)} (hl : K.Red r (.inl i :: .inr s :: m))
    (h : (Sum.inl i :: Sum.inr s :: m).head? = some (.inl i)) (hsi : s ∈ K.C i) :
    (incl ⟨_, hl⟩ i h ⟨s, hsi⟩).1.2.1 = .inr s :: m := by
  rw [incl_of_mem (z := ⟨s, hsi⟩) hl.1.1]
  change nbr (.inl i :: .inr s :: m) (.inr s) = .inr s :: m
  unfold nbr; simp

omit [TopologicalSpace Y] in
lemma liftF_cons_cons {i : ι} {s : Z} {m : List (ι ⊕ Z)} (hl : K.Red r (.inl i :: .inr s :: m)) :
    liftF q g z₀ y₀ (.inl i :: .inr s :: m) =
      liftAt q g ⟨_, hl⟩ i rfl s (liftF q g z₀ y₀ (.inr s :: m) s) := by
  simp only [liftF, dif_pos hl]

omit [TopologicalSpace Y] in
lemma liftF_root : liftF q g z₀ y₀ [.inl r] = liftAt q g (root K r) r rfl z₀ y₀ := by
  simp only [liftF]; exact dif_pos (root K r).2

lemma liftF_compat (hq : IsCoveringMap q) (hg : Continuous g) (hz₀ : z₀ ∈ K.C r)
    (hy₀ : q y₀ = g (base K r hz₀)) {l : List (ι ⊕ Z)} (hl : K.Red r l) {i : ι}
    (h : l.head? = some (.inl i)) {s : Z} (hsi : s ∈ K.C i) :
    liftF q g z₀ y₀ l s = liftF q g z₀ y₀ (nbr l (.inr s)) s := by
  unfold nbr
  split_ifs with hc
  · obtain ⟨v, m, rfl⟩ := List.exists_cons_of_ne_nil hl.ne_nil
    obtain rfl : v = .inl i := by simpa using h
    obtain ⟨w, m', rfl⟩ := List.exists_cons_of_ne_nil (show m ≠ [] by rintro rfl; simp at hc)
    obtain rfl : w = .inr s := by simpa using hc
    have hanchor : q (liftF q g z₀ y₀ (.inr s :: m') s) = g (incl ⟨_, hl⟩ i rfl ⟨s, hsi⟩) :=
      (liftF_spec hq hg hz₀ hy₀ _ (hl.tail (by simp))).2 _ (incl_snd_cons hl rfl hsi)
    rw [liftF_cons_cons hl]
    exact (liftAt_spec hq hg _ i rfl hsi hanchor).2.2
  · rfl

/-- Lifting from the tree covering, with the base point. -/
theorem exists_lift_base [Finite ι] (hq : IsCoveringMap q) (hg : Continuous g) (hz₀ : z₀ ∈ K.C r)
    (hy₀ : q y₀ = g (base K r hz₀)) :
    ∃ f : K.Cover r → P, Continuous f ∧ q ∘ f = g ∧ f (base K r hz₀) = y₀ := by
  have hspec := liftF_spec hq hg hz₀ hy₀
  have hroot : liftF q g z₀ y₀ [.inl r] z₀ = y₀ := by
    rw [liftF_root]
    exact (liftAt_spec hq hg (root K r) r rfl hz₀ hy₀).2.2
  refine ⟨fun e ↦ liftF q g z₀ y₀ e.1.2.1 e.1.1, ?_, funext fun e ↦ (hspec _ e.1.2.2).2 e rfl, ?_⟩
  · refine continuous_iff_continuousAt.2 fun x ↦ ?_
    rcases x.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, hS, hs⟩
    · let N : Set (K.Cover r) := {e | e.1.2 = x.1.2}
      have hN : N ∈ 𝓝 x := ((Tree.isOpen_singleton hi).preimage
        (continuous_snd.comp continuous_subtype_val)).mem_nhds rfl
      have hF : ContinuousOn (liftF q g z₀ y₀ x.1.2.1) (K.C i) :=
        continuousOn_iff_continuous_restrict.2 ((hspec _ x.1.2.2).1 i hi).1
      have hmaps : MapsTo (K.proj r) N (K.C i) := fun e he ↦
        (Cover.mem_piece_inl (x := e) (by rw [show e.1.2 = x.1.2 from he]; exact hi)).1
      have h1 := (hF.continuousWithinAt (hmaps (show x ∈ N from rfl))).comp
        continuous_proj.continuousWithinAt hmaps
      refine (continuousWithinAt_iff_continuousAt hN).1 (h1.congr (fun e he ↦ ?_) rfl)
      rw [show e.1.2 = x.1.2 from he]; rfl
    · let N : Set (K.Cover r) := Subtype.val ⁻¹' (univ ×ˢ Tree.star x.1.2)
      have hNo : IsOpen N :=
        (isOpen_univ.prod (Tree.isOpen_star hs)).preimage continuous_subtype_val
      let A : {c : ι // s ∈ K.C c} → Set (K.Cover r) := fun c ↦ N ∩ K.proj r ⁻¹' K.C c.1
      have hx1 : x.1.1 = s := Cover.eq_of_inr hs
      refine continuousAt_of_finite_cover A
        (mem_of_superset (hNo.mem_nhds ⟨trivial, .inl rfl⟩) fun e he ↦ ?_) fun c ↦ ?_
      · rcases he.2 with h | h
        · have : e.1.1 = s := Cover.eq_of_inr (by rw [h]; exact hs)
          exact mem_iUnion.2 ⟨⟨K.comp s, K.mem_comp s⟩, he,
            show e.1.1 ∈ _ by rw [this]; exact K.mem_comp s⟩
        · obtain ⟨c, hc, -, hsc⟩ := head_inl_of_adj x.1.2.2 e.1.2.2 h hs
          exact mem_iUnion.2 ⟨⟨c, hsc⟩, he, (Cover.mem_piece_inl hc).1⟩
      · let tc : K.Tree r := x.1.2.nbr hs (v := .inl c.1) ⟨hS, c.2⟩
        have htc : tc.1.head? = some (.inl c.1) := Tree.nbr_head _ _ _
        have hF : ContinuousOn (liftF q g z₀ y₀ tc.1) (K.C c.1) :=
          continuousOn_iff_continuous_restrict.2 ((hspec _ tc.2).1 c.1 htc).1
        have hmaps : MapsTo (K.proj r) (A c) (K.C c.1) := fun e he ↦ he.2
        have hxA : x ∈ A c := ⟨⟨trivial, .inl rfl⟩, show x.1.1 ∈ _ by rw [hx1]; exact c.2⟩
        have h1 := (hF.continuousWithinAt (hmaps hxA)).comp
          continuous_proj.continuousWithinAt hmaps
        have heq : ∀ e ∈ A c,
            liftF q g z₀ y₀ e.1.2.1 e.1.1 = liftF q g z₀ y₀ tc.1 (K.proj r e) := by
          rintro e ⟨⟨-, he⟩, hec⟩
          rcases he with h | h
          · have he1 : e.1.1 = s := Cover.eq_of_inr (by rw [h]; exact hs)
            change _ = liftF q g z₀ y₀ tc.1 e.1.1
            rw [h, he1, liftF_compat hq hg hz₀ hy₀ tc.2 htc c.2]
            rw [← CurveConfig.eq_nbr tc.2 x.1.2.2 (Tree.adj_comm.1 (Tree.adj_nbr _ _ _)) hs]
          · obtain ⟨c', hc', -, -⟩ := head_inl_of_adj x.1.2.2 e.1.2.2 h hs
            have hm := Cover.mem_piece_inl hc'
            obtain rfl : c' = c.1 := K.eq_of_notMem_S hm.1 hec hm.2
            have : e.1.2 = tc := Tree.eq_nbr h hs (v := .inl c.1) ⟨hS, c.2⟩ hc'
            rw [this]; rfl
        exact h1.congr (fun e he ↦ heq e he) (heq x hxA)
  · change liftF q g z₀ y₀ (base K r hz₀).1.2.1 (base K r hz₀).1.1 = y₀
    by_cases hz₀S : z₀ ∈ K.S
    · unfold base
      rw [incl_of_mem hz₀S]
      change liftF q g z₀ y₀ (nbr [.inl r] (.inr z₀)) z₀ = y₀
      exact (liftF_compat hq hg hz₀ hy₀ (root K r).2 (i := r) rfl hz₀).symm.trans hroot
    · unfold base
      rw [incl_of_notMem hz₀S]
      exact hroot

/-- Lifting from the tree covering: every continuous map from the tree covering lifts along a
covering map, through every point of the fibre. -/
theorem exists_lift_incl [Finite ι] (hq : IsCoveringMap q) (hg : Continuous g) (hz₀ : z₀ ∈ K.C r) :
    ∀ (l : List (ι ⊕ Z)) (hl : K.Red r l) (i : ι) (h : l.head? = some (.inl i)) (z : K.C i)
    (y : P), q y = g (incl ⟨l, hl⟩ i h z) →
    ∃ f : K.Cover r → P, Continuous f ∧ q ∘ f = g ∧ f (incl ⟨l, hl⟩ i h z) = y
  | [], hl, _, _, _, _, _ => hl.elim
  | [.inl i'], hl, i, h, z, y, hy => by
    obtain rfl : i' = r := Sum.inl_injective hl
    obtain rfl : i' = i := by simpa using h
    obtain ⟨L, hL, hqL, hLz⟩ := exists_lift_of_generic hq (K.generic_subtype i')
      (hg.comp (continuous_incl _ i' h)) z y hy
    obtain ⟨f, hf, hqf, hfb⟩ := exists_lift_base (y₀ := L ⟨z₀, hz₀⟩) hq hg hz₀
      (congrFun hqL ⟨z₀, hz₀⟩)
    have : f ∘ incl ⟨[.inl i'], hl⟩ i' h = L := lift_unique hq (hf.comp (continuous_incl _ _ _))
      hL (fun z' ↦ by
        change (q ∘ f) _ = (q ∘ L) z'
        rw [hqf, hqL]; rfl) ⟨z₀, hz₀⟩ hfb
    exact ⟨f, hf, hqf, by rw [← hLz, ← this]; rfl⟩
  | .inl i' :: .inr s :: m, hl, i, h, z, y, hy => by
    obtain rfl : i' = i := by simpa using h
    obtain ⟨L, hL, hqL, hLz⟩ := exists_lift_of_generic hq (K.generic_subtype i')
      (hg.comp (continuous_incl _ i' h)) z y hy
    have hlm : K.Red r (.inr s :: m) := hl.tail (by simp)
    obtain ⟨i₂, hi₂, -, hsi₂⟩ := hlm.inr_cons
    let tm : K.Tree r := ⟨m, hlm.tail hlm.ne_nil_of_inr⟩
    have hsnd := incl_snd_cons hl h hl.1.2
    have hx : incl ⟨_, hl⟩ i' h ⟨s, hl.1.2⟩ = incl tm i₂ hi₂ ⟨s, hsi₂⟩ := by
      refine eq_incl_of_inr _ (by rw [hsnd]; rfl) hi₂ (.inl (by rw [hsnd]; rfl)) hsi₂
    obtain ⟨f, hf, hqf, hfs⟩ := exists_lift_incl hq hg hz₀ m tm.2 i₂ hi₂ ⟨s, hsi₂⟩
      (L ⟨s, hl.1.2⟩) (by rw [← hx]; exact congrFun hqL _)
    have : f ∘ incl ⟨_, hl⟩ i' h = L := lift_unique hq (hf.comp (continuous_incl _ _ _))
      hL (fun z' ↦ by
        change (q ∘ f) _ = (q ∘ L) z'
        rw [hqf, hqL]; rfl) ⟨s, hl.1.2⟩ (by
          change f (incl ⟨_, hl⟩ i' h ⟨s, hl.1.2⟩) = _
          rw [hx]; exact hfs)
    exact ⟨f, hf, hqf, by rw [← hLz, ← this]; rfl⟩
  | .inl _ :: .inl _ :: _, hl, _, _, _, _, _ => hl.1.elim
  | .inr _ :: _, _, _, h, _, _, _ => by simp at h

/-- Lifting from the tree covering: every continuous map from the tree covering lifts along a
covering map, through every point of the fibre. -/
theorem exists_lift [Finite ι] (hq : IsCoveringMap q) (hg : Continuous g) (hz₀ : z₀ ∈ K.C r)
    (b : K.Cover r) (y : P) (hy : q y = g b) :
    ∃ f : K.Cover r → P, Continuous f ∧ q ∘ f = g ∧ f b = y := by
  obtain ⟨t, i, h, z, rfl⟩ := exists_eq_incl b
  exact exists_lift_incl hq hg hz₀ t.1 t.2 i h z y hy

end Lift

end CurveConfig

end TemperedFundamentalGroups
