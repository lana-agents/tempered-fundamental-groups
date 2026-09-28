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

end CurveConfig

end TemperedFundamentalGroups
