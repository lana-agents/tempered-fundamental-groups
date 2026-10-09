/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Data.ENNReal.Inv
import TemperedFundamentalGroups.Topology.TreeLength

/-!
# Lengths of points of the tree covering (Blueprint §10.3.6, item 3)

Let `K` be a curve configuration on `Z` with tree covering `K.Cover r` (vertices of the tree
`K.Tree r`: reduced walks from `r` in the incidence graph, ending at a component — a *component
vertex* — or at a special point — a *special vertex*). Given weights `w : Z → ℝ≥0∞` on the special
points, the **length** between two vertices `a`, `b` (`CurveConfig.tlen`) is the infimum of the
weights of the walks of the tree between component vertices `a'`, `b'` *near* `a`, `b`
(`CurveConfig.Near`: `a' = a` for a component vertex `a`, `a'` a neighbour for a special vertex
`a`); the weight of a walk is the sum of the weights of the special vertices it passes.
Special endpoints are thus not counted: this makes the length non-increasing along maps of
coverings (below) and zero on the diagonal.

* `CurveConfig.tlen_self`: `tlen a a = 0`;
* `CurveConfig.finite_tlen_le`: if the weights of the special points are bounded below by
  `μ > 0` (finitely many special points, positive weights), only finitely many vertices have
  length `≤ L` from a fixed vertex, for every `L ≠ ⊤`;
* `CurveConfig.tlen_map_le`: **monotonicity**. Let `h : K.Cover r → K'.Cover r'` be continuous
  over `ψ : Z → Z'`. Suppose every component is either *contracted* (`ψ '' C i` a point) or
  mapped onto a component `C' i'` with `ψ (η i) ∉ S'`, and that the weights are **harmonic**:
  every walk of the incidence graph of `K` crossing a special point `y'` of `K'` (its special
  points over `y'`, its inner components contracted to `y'`, its end components mapped onto
  different components `C' a ≠ C' b`), using each special point at most once and without
  backtracking, has weight at least `w' y'` (`IsHarmonicWeight`). Then lengths do not increase:
  `tlen w' (h p) (h q) ≤ tlen w p q` (on the vertices of the points `p`, `q`).

The harmonicity hypothesis is the combinatorial content of (X2) of
`SemistableReduction.Statement.HarmonicX`; the reduction from arbitrary walks of the tree to
walks with distinct special points and no backtracking is `IncWalk.exists_short`.
-/

universe u v u' v'

open Set Topology
open scoped ENNReal

namespace TemperedFundamentalGroups

namespace CurveConfig

section Vertices

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- A component vertex of the tree. -/
def IsComp (t : K.Tree r) : Prop := ∃ i, t.1.head? = some (.inl i)

/-- A special vertex of the tree. -/
def IsSpecial (t : K.Tree r) : Prop := ∃ s, t.1.head? = some (.inr s)

lemma isComp_or_isSpecial (t : K.Tree r) : IsComp t ∨ IsSpecial t := by
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · exact .inl ⟨i, hi⟩
  · exact .inr ⟨s, hs⟩

lemma not_isComp_of_isSpecial {t : K.Tree r} (h : IsSpecial t) : ¬ IsComp t := by
  rintro ⟨i, hi⟩
  obtain ⟨s, hs⟩ := h
  rw [hi] at hs
  cases hs

lemma mem_S_of_head {t : K.Tree r} {s : Z} (h : t.1.head? = some (.inr s)) : s ∈ K.S := by
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s', hs', h'⟩
  · rw [hi] at h; cases h
  · rw [h] at h'
    obtain rfl : s = s' := by simpa using h'
    exact hs'

lemma isSpecial_of_adj {t t' : K.Tree r} (ht : IsComp t) (hadj : t.Adj t') : IsSpecial t' := by
  obtain ⟨i, hi⟩ := ht
  obtain ⟨s, hs, -⟩ := head_inr_of_adj t.2 t'.2 hadj hi
  exact ⟨s, hs⟩

lemma isComp_of_adj {t t' : K.Tree r} (ht : IsSpecial t) (hadj : t.Adj t') : IsComp t' := by
  obtain ⟨s, hs⟩ := ht
  obtain ⟨i, hi, -⟩ := head_inl_of_adj t.2 t'.2 hadj hs
  exact ⟨i, hi⟩

/-- A special vertex has a neighbour. -/
lemma exists_adj_of_isSpecial {t : K.Tree r} (ht : IsSpecial t) : ∃ t', t.Adj t' := by
  obtain ⟨s, hs⟩ := ht
  obtain ⟨i, hi⟩ := K.cover s
  exact ⟨t.nbr hs (v := .inl i) ⟨mem_S_of_head hs, hi⟩, Tree.adj_nbr _ _ _⟩

/-- `a'` is a component vertex **near** `a`: `a` itself if `a` is a component vertex, a
neighbour of `a` if `a` is a special vertex. -/
def Near (a a' : K.Tree r) : Prop := (a' = a ∧ IsComp a) ∨ (IsSpecial a ∧ a.Adj a')

lemma Near.isComp {a a' : K.Tree r} (h : Near a a') : IsComp a' := by
  rcases h with ⟨rfl, h⟩ | ⟨h, hadj⟩
  · exact h
  · exact isComp_of_adj h hadj

lemma exists_near (a : K.Tree r) : ∃ a', Near a a' := by
  rcases isComp_or_isSpecial a with h | h
  · exact ⟨a, .inl ⟨rfl, h⟩⟩
  · obtain ⟨a', ha'⟩ := exists_adj_of_isSpecial h
    exact ⟨a', .inr ⟨h, ha'⟩⟩

/-- `X ≼ T`: `X = T`, or `X` is a special vertex adjacent to `T` (the vertices of the points in
the closure of a point over `T`). -/
def Below (X T : K.Tree r) : Prop := X = T ∨ (IsSpecial X ∧ X.Adj T)

lemma Below.near {X T : K.Tree r} (h : Below X T) (hT : IsComp T) : Near X T := by
  rcases h with rfl | ⟨hX, hadj⟩
  · exact .inl ⟨rfl, hT⟩
  · exact .inr ⟨hX, hadj⟩

lemma Below.eq_of_isSpecial {X T : K.Tree r} (h : Below X T) (hT : IsSpecial T) : X = T := by
  rcases h with rfl | ⟨hX, hadj⟩
  · rfl
  · exact absurd (isComp_of_adj hX hadj) (not_isComp_of_isSpecial hT)

/-- Neighbours of a vertex form a finite set. -/
lemma finite_adj [Finite ι] (t : K.Tree r) : {t' : K.Tree r | t.Adj t'}.Finite := by
  have h₁ : {t' : K.Tree r | t.1.tail = t'.1}.Subsingleton := fun a ha b hb =>
    Tree.ext ((show t.1.tail = a.1 from ha).symm.trans hb)
  have h₂ : {t' : K.Tree r | t'.1.tail = t.1}.Finite := by
    refine Set.Finite.of_finite_image (f := fun t' : K.Tree r => t'.1.head?) ?_ ?_
    · refine ((finite_vertices (K := K)).image some |>.union (finite_singleton none)).subset ?_
      rintro _ ⟨t', -, rfl⟩
      rcases h : t'.1.head? with _ | a
      · exact .inr h
      · exact .inl ⟨a, Red.mem_vertices t'.2 a (List.mem_of_mem_head? h), h.symm⟩
    · intro a ha b hb hab
      apply Tree.ext
      obtain ⟨x, m, hx⟩ := List.exists_cons_of_ne_nil a.2.ne_nil
      obtain ⟨y, n, hy⟩ := List.exists_cons_of_ne_nil b.2.ne_nil
      have hab' : a.1.head? = b.1.head? := hab
      have ha' : a.1.tail = t.1 := ha
      have hb' : b.1.tail = t.1 := hb
      rw [hx] at hab' ha' ⊢
      rw [hy] at hab' hb' ⊢
      simp only [List.head?_cons, Option.some.injEq, List.tail_cons] at hab' ha' hb'
      rw [hab', ha', hb']
  exact (h₂.union h₁.finite).subset fun t' ht' => by
    rcases ht' with h | h
    · exact .inl h
    · exact .inr h

end Vertices

section Walks

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- A walk of the tree from a vertex, coded by its pairs `(σ, t)` of a special vertex and the
next component vertex. -/
def PWalk : K.Tree r → List (K.Tree r × K.Tree r) → Prop
  | _, [] => True
  | t, (σ, t') :: L => t.Adj σ ∧ σ.Adj t' ∧ PWalk t' L

/-- The end of a walk. -/
def pend : K.Tree r → List (K.Tree r × K.Tree r) → K.Tree r
  | t, [] => t
  | _, (_, t') :: L => pend t' L

@[simp] lemma pWalk_nil (t : K.Tree r) : PWalk t [] := trivial

@[simp] lemma pWalk_cons (t σ t' : K.Tree r) (L : List (K.Tree r × K.Tree r)) :
    PWalk t ((σ, t') :: L) ↔ t.Adj σ ∧ σ.Adj t' ∧ PWalk t' L := Iff.rfl

@[simp] lemma pend_nil (t : K.Tree r) : pend t [] = t := rfl

@[simp] lemma pend_cons (t σ t' : K.Tree r) (L : List (K.Tree r × K.Tree r)) :
    pend t ((σ, t') :: L) = pend t' L := rfl

lemma pWalk_append {t : K.Tree r} {L₁ L₂ : List (K.Tree r × K.Tree r)} :
    PWalk t (L₁ ++ L₂) ↔ PWalk t L₁ ∧ PWalk (pend t L₁) L₂ := by
  induction L₁ generalizing t with
  | nil => simp
  | cons p L₁ ih =>
    obtain ⟨σ, t'⟩ := p
    simp only [List.cons_append, pWalk_cons, pend_cons, ih, and_assoc]

lemma pend_append (t : K.Tree r) (L₁ L₂ : List (K.Tree r × K.Tree r)) :
    pend t (L₁ ++ L₂) = pend (pend t L₁) L₂ := by
  induction L₁ generalizing t with
  | nil => rfl
  | cons p L₁ ih => obtain ⟨σ, t'⟩ := p; exact ih t'

lemma PWalk.isComp_pend {t : K.Tree r} (ht : IsComp t) :
    ∀ {L : List (K.Tree r × K.Tree r)}, PWalk t L → IsComp (pend t L)
  | [], _ => ht
  | (_, _) :: _, ⟨h₁, h₂, h₃⟩ =>
    PWalk.isComp_pend (isComp_of_adj (isSpecial_of_adj ht h₁) h₂) h₃

lemma PWalk.isComp_snd {t : K.Tree r} (ht : IsComp t) :
    ∀ {L : List (K.Tree r × K.Tree r)}, PWalk t L → ∀ p ∈ L, IsComp p.2
  | [], _ => by simp
  | (_, _) :: _, ⟨h₁, h₂, h₃⟩ => by
    have ht' := isComp_of_adj (isSpecial_of_adj ht h₁) h₂
    rintro p (_ | ⟨_, hp⟩)
    · exact ht'
    · exact PWalk.isComp_snd ht' h₃ p hp

lemma PWalk.isSpecial_fst {t : K.Tree r} (ht : IsComp t) :
    ∀ {L : List (K.Tree r × K.Tree r)}, PWalk t L → ∀ p ∈ L, IsSpecial p.1
  | [], _ => by simp
  | (_, _) :: _, ⟨h₁, h₂, h₃⟩ => by
    have hσ := isSpecial_of_adj ht h₁
    rintro p (_ | ⟨_, hp⟩)
    · exact hσ
    · exact PWalk.isSpecial_fst (isComp_of_adj hσ h₂) h₃ p hp

/-- The weight of a vertex: `w s` for a special vertex over `s`, `0` for a component vertex. -/
noncomputable def tw (w : Z → ℝ≥0∞) (t : K.Tree r) : ℝ≥0∞ :=
  ((t.1.head?).map (Sum.elim (fun _ => 0) w)).getD 0

lemma tw_of_inr (w : Z → ℝ≥0∞) {t : K.Tree r} {s : Z} (h : t.1.head? = some (.inr s)) :
    tw w t = w s := by
  simp [tw, h]

lemma tw_of_inl (w : Z → ℝ≥0∞) {t : K.Tree r} {i : ι} (h : t.1.head? = some (.inl i)) :
    tw w t = 0 := by
  simp [tw, h]

/-- The weight of a walk: the sum of the weights of its special vertices. -/
noncomputable def cost (w : Z → ℝ≥0∞) (L : List (K.Tree r × K.Tree r)) : ℝ≥0∞ :=
  (L.map fun p => tw w p.1).sum

@[simp] lemma cost_nil (w : Z → ℝ≥0∞) : cost w ([] : List (K.Tree r × K.Tree r)) = 0 := rfl

@[simp] lemma cost_cons (w : Z → ℝ≥0∞) (p : K.Tree r × K.Tree r) (L : List (K.Tree r × K.Tree r)) :
    cost w (p :: L) = tw w p.1 + cost w L := by
  simp [cost]

lemma cost_append (w : Z → ℝ≥0∞) (L₁ L₂ : List (K.Tree r × K.Tree r)) :
    cost w (L₁ ++ L₂) = cost w L₁ + cost w L₂ := by
  simp [cost]

/-- The lengths of the walks between component vertices near `a` and `b`. -/
def lenSet (w : Z → ℝ≥0∞) (a b : K.Tree r) : Set ℝ≥0∞ :=
  {x | ∃ a' b' L, Near a a' ∧ Near b b' ∧ PWalk a' L ∧ pend a' L = b' ∧ cost w L = x}

/-- **The length between two vertices of the tree** (special endpoints not counted). -/
noncomputable def tlen (w : Z → ℝ≥0∞) (a b : K.Tree r) : ℝ≥0∞ := sInf (lenSet w a b)

lemma tlen_le (w : Z → ℝ≥0∞) {a b a' b' : K.Tree r} {L : List (K.Tree r × K.Tree r)}
    (ha : Near a a') (hb : Near b b') (hL : PWalk a' L) (hLb : pend a' L = b') :
    tlen w a b ≤ cost w L :=
  sInf_le ⟨a', b', L, ha, hb, hL, hLb, rfl⟩

@[simp] theorem tlen_self (w : Z → ℝ≥0∞) (a : K.Tree r) : tlen w a a = 0 := by
  obtain ⟨a', ha'⟩ := exists_near a
  exact le_antisymm ((tlen_le w ha' ha' (L := []) trivial rfl).trans_eq rfl) (zero_le)

/-- Weights are bounded below along walks: every pair contributes a special vertex. -/
lemma length_mul_le_cost {w : Z → ℝ≥0∞} {μ : ℝ≥0∞} (hμ : ∀ s ∈ K.S, μ ≤ w s) {t : K.Tree r}
    (ht : IsComp t) {L : List (K.Tree r × K.Tree r)} (hL : PWalk t L) :
    (L.length : ℝ≥0∞) * μ ≤ cost w L := by
  have key : ∀ p ∈ L, μ ≤ tw w p.1 := fun p hp => by
    obtain ⟨s, hs⟩ := hL.isSpecial_fst ht p hp
    rw [tw_of_inr w hs]
    exact hμ s (mem_S_of_head hs)
  clear hL ht
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, cost_cons, add_mul, one_mul]
    rw [add_comm]
    exact add_le_add (key p (by simp)) (ih fun q hq => key q (by simp [hq]))

/-- The vertices reachable by walks with at most `N` pairs. -/
def ball (t : K.Tree r) (N : ℕ) : Set (K.Tree r) :=
  {b | ∃ L, PWalk t L ∧ pend t L = b ∧ L.length ≤ N}

lemma finite_ball [Finite ι] (t : K.Tree r) (N : ℕ) : (ball t N).Finite := by
  induction N with
  | zero =>
    refine (finite_singleton t).subset ?_
    rintro b ⟨L, -, rfl, hL⟩
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hL)]
    rfl
  | succ N ih =>
    refine (ih.union (ih.biUnion fun x _ =>
      (finite_adj x).biUnion fun σ _ => finite_adj σ)).subset ?_
    rintro b ⟨L, hL, rfl, hlen⟩
    rcases L.eq_nil_or_concat with rfl | ⟨L', p, rfl⟩
    · exact .inl ⟨[], trivial, rfl, Nat.zero_le _⟩
    · obtain ⟨σ, t'⟩ := p
      rw [List.concat_eq_append] at hL hlen ⊢
      rw [pWalk_append] at hL
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      refine .inr (mem_biUnion (x := pend t L') ⟨L', hL.1, rfl, by omega⟩ ?_)
      exact mem_biUnion (x := σ) hL.2.1 (by rw [pend_append]; exact hL.2.2.1)

/-- **Finiteness**: if the weights of the special points are bounded below by `μ > 0`, only
finitely many vertices have length at most `L ≠ ⊤` from `a`. -/
theorem finite_tlen_le [Finite ι] {w : Z → ℝ≥0∞} {μ : ℝ≥0∞} (hμ0 : μ ≠ 0)
    (hμ : ∀ s ∈ K.S, μ ≤ w s) (a : K.Tree r) {L : ℝ≥0∞} (hL : L ≠ ⊤) :
    {b : K.Tree r | tlen w a b ≤ L}.Finite := by
  obtain ⟨N, hN⟩ := ENNReal.exists_nat_mul_gt hμ0 (ENNReal.add_ne_top.2 ⟨hL, ENNReal.one_ne_top⟩)
  have hnear : ∀ x : K.Tree r, {y : K.Tree r | Near x y}.Finite := fun x =>
    ((finite_singleton x).union (finite_adj x)).subset fun y hy => by
      rcases hy with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact .inl rfl
      · exact .inr h
  have hnear' : ∀ y : K.Tree r, {x : K.Tree r | Near x y}.Finite := fun y =>
    ((finite_singleton y).union (finite_adj y)).subset fun x hx => by
      rcases hx with ⟨rfl, -⟩ | ⟨-, h⟩
      · exact .inl rfl
      · exact .inr (Tree.adj_comm.1 h)
  refine ((hnear a).biUnion fun a' _ => (finite_ball a' N).biUnion fun b' _ =>
    hnear' b').subset ?_
  intro b hb
  have hlt : tlen w a b < L + 1 :=
    lt_of_le_of_lt hb (ENNReal.lt_add_right hL one_ne_zero)
  obtain ⟨_, ⟨a', b', Lw, ha, hb', hLw, hend, rfl⟩, hlt'⟩ := sInf_lt_iff.1 hlt
  refine mem_biUnion (x := a') ha (mem_biUnion (x := b') ⟨Lw, hLw, hend, ?_⟩ hb')
  by_contra hlen
  push Not at hlen
  have h₁ : (N : ℝ≥0∞) * μ ≤ Lw.length * μ := by
    gcongr
  exact absurd (hN.trans_le (h₁.trans ((length_mul_le_cost hμ ha.isComp hLw).trans hlt'.le)))
    (lt_irrefl _)

/-- Every component vertex has walks to and from the root. -/
lemma exists_pWalk_root : ∀ (n : ℕ) (t : K.Tree r), t.1.length ≤ n → IsComp t →
    (∃ L, PWalk t L ∧ pend t L = root K r ∧ ∀ p ∈ L, IsSpecial p.1) ∧
    (∃ L, PWalk (root K r) L ∧ pend (root K r) L = t ∧ ∀ p ∈ L, IsSpecial p.1)
  | 0, t, hn, _ => absurd (List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)) t.2.ne_nil
  | n + 1, t, hn, ⟨i, hi⟩ => by
    obtain ⟨v, m, hvm⟩ := List.exists_cons_of_ne_nil t.2.ne_nil
    obtain rfl : v = .inl i := by rw [hvm] at hi; simpa using hi
    rcases m with _ | ⟨u, m⟩
    · have ht : t = root K r := by
        apply Tree.ext
        have hr : K.Red r [.inl i] := hvm ▸ t.2
        rw [hvm, show (Sum.inl i : ι ⊕ Z) = .inl r from hr]
        rfl
      subst ht
      exact ⟨⟨[], trivial, rfl, by simp⟩, ⟨[], trivial, rfl, by simp⟩⟩
    · have hl : K.Red r (.inl i :: u :: m) := hvm ▸ t.2
      obtain ⟨s, hs, hS, hsi⟩ := head_inr_of_adj hl (hl.tail (by simp)) (.inr rfl) rfl
      obtain rfl : u = .inr s := by simpa using hs
      have hl' : K.Red r (.inr s :: m) := hl.tail (by simp)
      let σ : K.Tree r := ⟨.inr s :: m, hl'⟩
      let t' : K.Tree r := ⟨m, hl'.tail hl'.ne_nil_of_inr⟩
      obtain ⟨j, hj, -⟩ := hl'.inr_cons
      have hlen : t'.1.length ≤ n := by
        have := congrArg List.length hvm
        simp only [List.length_cons] at this
        change m.length ≤ n
        omega
      obtain ⟨⟨L₁, h₁, e₁, s₁⟩, ⟨L₂, h₂, e₂, s₂⟩⟩ := exists_pWalk_root n t' hlen ⟨j, hj⟩
      have hσ : IsSpecial σ := ⟨s, rfl⟩
      have htσ : t.Adj σ := .inr (by rw [hvm]; rfl)
      have hσt' : σ.Adj t' := .inr rfl
      refine ⟨⟨(σ, t') :: L₁, ⟨htσ, hσt', h₁⟩, e₁, ?_⟩, ⟨L₂ ++ [(σ, t)], ?_, ?_, ?_⟩⟩
      · rintro p (_ | ⟨_, hp⟩)
        · exact hσ
        · exact s₁ p hp
      · rw [pWalk_append, e₂]
        exact ⟨h₂, Tree.adj_comm.1 hσt', Tree.adj_comm.1 htσ, trivial⟩
      · rw [pend_append, e₂]
        rfl
      · intro p hp
        rcases List.mem_append.1 hp with hp | hp
        · exact s₂ p hp
        · rw [List.mem_singleton.1 hp]
          exact hσ

/-- **Lengths are finite** for finite weights (the tree is connected). -/
theorem tlen_ne_top {w : Z → ℝ≥0∞} (hw : ∀ s, w s ≠ ⊤) (a b : K.Tree r) : tlen w a b ≠ ⊤ := by
  obtain ⟨a', ha⟩ := exists_near a
  obtain ⟨b', hb⟩ := exists_near b
  obtain ⟨⟨L₁, h₁, e₁, -⟩, -⟩ := exists_pWalk_root _ a' le_rfl ha.isComp
  obtain ⟨-, ⟨L₂, h₂, e₂, -⟩⟩ := exists_pWalk_root _ b' le_rfl hb.isComp
  refine ne_top_of_le_ne_top ?_ (tlen_le w ha hb (L := L₁ ++ L₂)
    (pWalk_append.2 ⟨h₁, e₁ ▸ h₂⟩) (by rw [pend_append, e₁, e₂]))
  have htw : ∀ t : K.Tree r, tw w t ≠ ⊤ := fun t => by
    rcases isComp_or_isSpecial t with ⟨i, hi⟩ | ⟨s, hs⟩
    · rw [tw_of_inl w hi]; exact ENNReal.zero_ne_top
    · rw [tw_of_inr w hs]; exact hw s
  generalize L₁ ++ L₂ = L
  induction L with
  | nil => exact ENNReal.zero_ne_top
  | cons p L ih => rw [cost_cons]; exact ENNReal.add_ne_top.2 ⟨htw _, ih⟩

end Walks

section Points

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- The closure of a vertex of the tree: the vertex and, for a component vertex, its special
neighbours. -/
lemma below_of_mem_closure {t t₀ : K.Tree r} (h : t ∈ closure {t₀}) : Below t t₀ := by
  rcases isComp_or_isSpecial t with ⟨i, hi⟩ | ⟨s, hs⟩
  · obtain ⟨_, h₁, h₂⟩ := mem_closure_iff.1 h {t} (Tree.isOpen_singleton hi) rfl
    exact .inl ((mem_singleton_iff.1 h₁).symm.trans (mem_singleton_iff.1 h₂))
  · obtain ⟨_, h₁, h₂⟩ := mem_closure_iff.1 h _ (Tree.isOpen_star hs) (.inl rfl)
    rw [mem_singleton_iff.1 h₂] at h₁
    rcases h₁ with h₁ | h₁
    · exact .inl h₁.symm
    · exact .inr ⟨⟨s, hs⟩, h₁⟩

lemma continuous_vtx : Continuous fun x : K.Cover r => x.1.2 :=
  continuous_snd.comp continuous_subtype_val

lemma below_of_mem_closure_cover {x y : K.Cover r} (h : x ∈ closure {y}) : Below x.1.2 y.1.2 :=
  below_of_mem_closure (map_mem_closure (f := fun x : K.Cover r => x.1.2) continuous_vtx h
    (fun a ha => by rw [mem_singleton_iff.1 ha]; rfl))

/-- Two points over the same point of `Z`, one in the closure of the other, are equal. -/
lemma eq_of_mem_closure {x y : K.Cover r} (h : x ∈ closure {y}) (hxy : x.1.1 = y.1.1) :
    x = y := by
  rcases below_of_mem_closure_cover h with h | ⟨⟨s, hs⟩, hadj⟩
  · exact Cover.ext hxy h
  · obtain ⟨i, hi, -⟩ := head_inl_of_adj x.1.2.2 y.1.2.2 hadj hs
    have h₁ := (Cover.mem_piece_inl hi).2
    rw [← hxy, Cover.eq_of_inr hs] at h₁
    exact (h₁ (mem_S_of_head hs)).elim

/-- The label of a vertex: its component (for a component vertex). -/
def lab (t : K.Tree r) : ι :=
  match t.1.head? with
  | some (.inl i) => i
  | _ => r

lemma lab_of {t : K.Tree r} {i : ι} (h : t.1.head? = some (.inl i)) : lab t = i := by
  simp [lab, h]

/-- The **generic point of a vertex**: the generic point of the copy of the component of a
component vertex, the special point of a special vertex. -/
noncomputable def gen (t : K.Tree r) : K.Cover r :=
  match h : t.1.head? with
  | some (.inl i) => incl t i h ⟨K.η i, K.η_mem i⟩
  | some (.inr s) => ⟨(s, t), by rw [h]; rfl⟩
  | none => absurd (List.head?_eq_none_iff.1 h) t.2.ne_nil

lemma gen_of_inl {t : K.Tree r} {i : ι} (h : t.1.head? = some (.inl i)) :
    gen t = incl t i h ⟨K.η i, K.η_mem i⟩ := by
  unfold gen
  split
  · rename_i i' h'
    obtain rfl : i' = i := by rw [h] at h'; simpa using h'.symm
    rfl
  · rename_i s h'
    rw [h] at h'; cases h'
  · rename_i h'
    rw [h] at h'; cases h'

lemma gen_of_inr {t : K.Tree r} {s : Z} (h : t.1.head? = some (.inr s)) :
    (gen t).1 = (s, t) := by
  unfold gen
  split
  · rename_i i' h'
    rw [h] at h'; cases h'
  · rename_i s' h'
    obtain rfl : s' = s := by rw [h] at h'; simpa using h'.symm
    rfl
  · rename_i h'
    rw [h] at h'; cases h'

lemma gen_fst_of_inl {t : K.Tree r} {i : ι} (h : t.1.head? = some (.inl i)) :
    (gen t).1.1 = K.η i := by
  rw [gen_of_inl h]; rfl

/-- The special point of a special vertex. -/
noncomputable def spt (t : K.Tree r) : Z := (gen t).1.1

lemma spt_of {t : K.Tree r} {s : Z} (h : t.1.head? = some (.inr s)) : spt t = s := by
  rw [spt, gen_of_inr h]

lemma mem_C_of_near {x : K.Cover r} {t : K.Tree r} {i : ι} (ht : t.1.head? = some (.inl i))
    (h : Near x.1.2 t) : x.1.1 ∈ K.C i := by
  rcases h with ⟨rfl, -⟩ | ⟨⟨s, hs⟩, hadj⟩
  · exact (Cover.mem_piece_inl ht).1
  · obtain ⟨i', hi', -, hsi⟩ := head_inl_of_adj x.1.2.2 t.2 hadj hs
    rw [ht] at hi'
    obtain rfl : i' = i := by simpa using hi'.symm
    rw [Cover.eq_of_inr hs]
    exact hsi

/-- A point near a component vertex lies in the closure of its generic point. -/
lemma mem_closure_gen {x : K.Cover r} {t : K.Tree r} (h : Near x.1.2 t) :
    x ∈ closure {gen t} := by
  obtain ⟨i, hi⟩ := h.isComp
  have hx : x = incl t i hi ⟨x.1.1, mem_C_of_near hi h⟩ := by
    rcases h with ⟨rfl, -⟩ | ⟨⟨s, hs⟩, hadj⟩
    · exact eq_incl_of_inl x hi
    · have hxs : x.1.1 = s := Cover.eq_of_inr hs
      have := eq_incl_of_inr x hs hi (Tree.adj_comm.1 hadj)
        (by rw [← hxs]; exact mem_C_of_near hi (.inr ⟨⟨s, hs⟩, hadj⟩))
      refine this.trans ?_
      congr 1
      exact Subtype.ext hxs.symm
  rw [hx, gen_of_inl hi]
  refine map_mem_closure (continuous_incl t i hi) ?_
    (fun a ha => by rw [mem_singleton_iff.1 ha]; rfl)
  rw [mem_closure_iff]
  intro U hU hxU
  exact ⟨_, K.generic_subtype i U hU ⟨_, hxU⟩, rfl⟩

lemma gen_near_of_adj {σ t : K.Tree r} (hσ : IsSpecial σ) (hadj : σ.Adj t) :
    Near (gen σ).1.2 t := by
  obtain ⟨s, hs⟩ := hσ
  rw [gen_of_inr hs]
  exact .inr ⟨⟨s, hs⟩, hadj⟩

lemma near_self_gen {t : K.Tree r} (ht : IsComp t) : Near t t := .inl ⟨rfl, ht⟩

end Points

section IncWalk

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} (K : CurveConfig Z ι)

/-- A walk of the incidence graph from the component `i`, coded by its pairs `(s, j)` of a
special point and the next component. -/
def IncWalk : ι → List (Z × ι) → Prop
  | _, [] => True
  | i, (s, j) :: L => s ∈ K.S ∧ s ∈ K.C i ∧ s ∈ K.C j ∧ IncWalk j L

/-- The last component of a walk of the incidence graph. -/
def lastLab : ι → List (Z × ι) → ι
  | i, [] => i
  | _, (_, j) :: L => lastLab j L

/-- No backtracking: consecutive components are different. -/
def NoBack : ι → List (Z × ι) → Prop
  | _, [] => True
  | i, (_, j) :: L => i ≠ j ∧ NoBack j L

variable {K}

omit [TopologicalSpace Z] in
@[simp] lemma lastLab_nil (i : ι) : lastLab i ([] : List (Z × ι)) = i := rfl

omit [TopologicalSpace Z] in
@[simp] lemma lastLab_cons (i j : ι) (s : Z) (L : List (Z × ι)) :
    lastLab i ((s, j) :: L) = lastLab j L := rfl

omit [TopologicalSpace Z] in
lemma lastLab_append (i : ι) (A B : List (Z × ι)) :
    lastLab i (A ++ B) = lastLab (lastLab i A) B := by
  induction A generalizing i with
  | nil => rfl
  | cons p A ih => obtain ⟨s, j⟩ := p; exact ih j

lemma incWalk_append {i : ι} {A B : List (Z × ι)} :
    IncWalk K i (A ++ B) ↔ IncWalk K i A ∧ IncWalk K (lastLab i A) B := by
  induction A generalizing i with
  | nil => simp [IncWalk]
  | cons p A ih =>
    obtain ⟨s, j⟩ := p
    simp only [List.cons_append, IncWalk, ih, lastLab_cons, and_assoc]

lemma exists_dup_of_not_nodup {α β : Type*} (f : α → β) :
    ∀ {L : List α}, ¬ (L.map f).Nodup →
      ∃ A p B q C, L = A ++ p :: (B ++ q :: C) ∧ f p = f q
  | [], h => (h List.nodup_nil).elim
  | x :: L, h => by
    rw [List.map_cons, List.nodup_cons, not_and_or] at h
    rcases h with h | h
    · rw [not_not, List.mem_map] at h
      obtain ⟨q, hq, hfq⟩ := h
      obtain ⟨B, C, rfl⟩ := List.append_of_mem hq
      exact ⟨[], x, B, q, C, rfl, hfq.symm⟩
    · obtain ⟨A, p, B, q, C, rfl, hpq⟩ := exists_dup_of_not_nodup f h
      exact ⟨x :: A, p, B, q, C, rfl, hpq⟩

omit [TopologicalSpace Z] in
lemma exists_back_of_not_noBack : ∀ {i : ι} {L : List (Z × ι)}, ¬ NoBack i L →
    ∃ A s j B, L = A ++ (s, j) :: B ∧ j = lastLab i A
  | _, [], h => (h trivial).elim
  | i, (s, j) :: L, h => by
    simp only [NoBack, not_and_or, not_not] at h
    rcases h with h | h
    · exact ⟨[], s, j, L, rfl, h.symm⟩
    · obtain ⟨A, s', j', B, rfl, hj⟩ := exists_back_of_not_noBack h
      exact ⟨(s, j) :: A, s', j', B, rfl, hj⟩

/-- **Shortening walks of the incidence graph**: every walk has a sub-walk with the same ends,
using each special point at most once and without backtracking, whose special points form a
sublist and whose inner components are inner components of the walk. -/
theorem IncWalk.exists_short (Q : ι → Prop) : ∀ (n : ℕ) {i₀ : ι} {L : List (Z × ι)},
    L.length ≤ n → IncWalk K i₀ L → (∀ p ∈ L.dropLast, Q p.2) →
    ∃ L', IncWalk K i₀ L' ∧ lastLab i₀ L' = lastLab i₀ L ∧ (L'.map Prod.fst).Nodup ∧
      NoBack i₀ L' ∧ (L'.map Prod.fst).Sublist (L.map Prod.fst) ∧ ∀ p ∈ L'.dropLast, Q p.2
  | 0, i₀, L, hn, hL, hQ => by
    obtain rfl := List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)
    exact ⟨[], trivial, rfl, List.nodup_nil, trivial, List.Sublist.slnil, by simp⟩
  | n + 1, i₀, L, hn, hL, hQ => by
    by_cases hgood : (L.map Prod.fst).Nodup ∧ NoBack i₀ L
    · exact ⟨L, hL, rfl, hgood.1, hgood.2, List.Sublist.refl _, hQ⟩
    -- a strictly shorter walk with the same properties
    suffices h : ∃ L₁ : List (Z × ι), L₁.length < L.length ∧ IncWalk K i₀ L₁ ∧
        lastLab i₀ L₁ = lastLab i₀ L ∧ (L₁.map Prod.fst).Sublist (L.map Prod.fst) ∧
        ∀ p ∈ L₁.dropLast, Q p.2 by
      obtain ⟨L₁, hlen, hL₁, hlast, hsub, hQ₁⟩ := h
      obtain ⟨L', h₁, h₂, h₃, h₄, h₅, h₆⟩ :=
        IncWalk.exists_short Q n (L := L₁) (by omega) hL₁ hQ₁
      exact ⟨L', h₁, h₂.trans hlast, h₃, h₄, h₅.trans hsub, h₆⟩
    rw [not_and_or] at hgood
    rcases hgood with hdup | hback
    · obtain ⟨A, p, B, q, C, rfl, hpq⟩ := exists_dup_of_not_nodup Prod.fst hdup
      refine ⟨A ++ (p.1, q.2) :: C, by simp, ?_, ?_, ?_, ?_⟩
      · rw [incWalk_append] at hL ⊢
        obtain ⟨hA, hL⟩ := hL
        obtain ⟨s, j⟩ := p
        obtain ⟨hs, hsA, -, hL⟩ := hL
        rw [incWalk_append] at hL
        obtain ⟨-, hL⟩ := hL
        obtain ⟨s', j'⟩ := q
        obtain ⟨-, -, hs'j', hC⟩ := hL
        simp only at hpq
        subst hpq
        exact ⟨hA, hs, hsA, hs'j', hC⟩
      · obtain ⟨s, j⟩ := p
        obtain ⟨s', j'⟩ := q
        simp [lastLab_append]
      · simp only [List.map_append, List.map_cons]
        refine List.Sublist.append_left (List.Sublist.cons_cons _ ?_) _
        exact List.sublist_append_of_sublist_right (List.sublist_cons_self _ _)
      · intro x hx
        rcases C.eq_nil_or_concat with rfl | ⟨C', c, rfl⟩
        · rw [List.dropLast_concat] at hx
          refine hQ x ?_
          rw [show A ++ p :: (B ++ [q]) = (A ++ p :: B) ++ [q] by simp, List.dropLast_concat]
          simp [hx]
        · simp only [List.concat_eq_append] at hx hQ ⊢
          rw [show A ++ (p.1, q.2) :: (C' ++ [c]) = (A ++ (p.1, q.2) :: C') ++ [c] by simp,
            List.dropLast_concat] at hx
          have hL' : ∀ y ∈ A ++ p :: (B ++ q :: C'), Q y.2 := fun y hy => hQ y (by
            rw [show A ++ p :: (B ++ q :: (C' ++ [c])) = (A ++ p :: (B ++ q :: C')) ++ [c] by
              simp, List.dropLast_concat]
            exact hy)
          simp only [List.mem_append, List.mem_cons] at hx
          rcases hx with hx | rfl | hx
          · exact hL' x (by simp [hx])
          · exact hL' q (by simp)
          · exact hL' x (by simp [hx])
    · obtain ⟨A, s, j, B, rfl, hj⟩ := exists_back_of_not_noBack hback
      refine ⟨A ++ B, by simp, ?_, ?_, ?_, ?_⟩
      · rw [incWalk_append] at hL ⊢
        obtain ⟨hA, -, -, -, hB⟩ := hL
        exact ⟨hA, hj ▸ hB⟩
      · rw [lastLab_append, lastLab_append, lastLab_cons, ← hj]
      · simp only [List.map_append, List.map_cons]
        exact List.Sublist.append_left (List.sublist_cons_self _ _) _
      · intro x hx
        rcases B.eq_nil_or_concat with rfl | ⟨B', b, rfl⟩
        · rw [List.append_nil] at hx
          exact hQ x (by
            rw [show A ++ [(s, j)] = A ++ [(s, j)] from rfl, List.dropLast_concat]
            exact List.dropLast_subset _ hx)
        · simp only [List.concat_eq_append] at hx hQ ⊢
          rw [← List.append_assoc, List.dropLast_concat] at hx
          refine hQ x ?_
          rw [show A ++ (s, j) :: (B' ++ [b]) = (A ++ (s, j) :: B') ++ [b] by simp,
            List.dropLast_concat]
          simp only [List.mem_append, List.mem_cons] at hx ⊢
          tauto

omit [TopologicalSpace Z] in
/-- The `j`-th component of a walk of the incidence graph (`0 ≤ j ≤ length`). -/
def cget (i₀ : ι) (L : List (Z × ι)) (j : Fin (L.length + 1)) : ι :=
  (i₀ :: L.map Prod.snd)[j.1]'(by simpa using j.2)

omit [TopologicalSpace Z] in
@[simp] lemma cget_zero (i₀ : ι) (L : List (Z × ι)) : cget i₀ L 0 = i₀ := rfl

omit [TopologicalSpace Z] in
lemma cget_succ (i₀ : ι) (L : List (Z × ι)) (j : Fin L.length) :
    cget i₀ L j.succ = L[j.1].2 := by
  simp [cget]

omit [TopologicalSpace Z] in
lemma cget_last : ∀ (i₀ : ι) (L : List (Z × ι)), cget i₀ L (Fin.last _) = lastLab i₀ L
  | _, [] => rfl
  | _, (s, j) :: L => by
    rw [lastLab_cons, ← cget_last j L]
    simp [cget]

lemma IncWalk.getElem : ∀ {i₀ : ι} {L : List (Z × ι)}, IncWalk K i₀ L → ∀ j : Fin L.length,
    L[j.1].1 ∈ K.S ∧ L[j.1].1 ∈ K.C (cget i₀ L j.castSucc) ∧ L[j.1].1 ∈ K.C L[j.1].2
  | _, [], _, j => j.elim0
  | i₀, (s, i) :: L, ⟨h₁, h₂, h₃, h₄⟩, j => by
    rcases j with ⟨_ | j, hj⟩
    · exact ⟨h₁, h₂, h₃⟩
    · have := IncWalk.getElem h₄ ⟨j, by simpa using hj⟩
      simpa [cget] using this

omit [TopologicalSpace Z] in
lemma NoBack.getElem : ∀ {i₀ : ι} {L : List (Z × ι)}, NoBack i₀ L → ∀ j : Fin L.length,
    cget i₀ L j.castSucc ≠ L[j.1].2
  | _, [], _, j => j.elim0
  | i₀, (s, i) :: L, ⟨h₁, h₂⟩, j => by
    rcases j with ⟨_ | j, hj⟩
    · exact h₁
    · have := NoBack.getElem h₂ ⟨j, by simpa using hj⟩
      simpa [cget] using this

omit [TopologicalSpace Z] in
lemma cget_mem_dropLast (i₀ : ι) (L : List (Z × ι)) (j : Fin (L.length + 1)) (h₀ : j ≠ 0)
    (hl : j ≠ Fin.last _) : ∃ p ∈ L.dropLast, p.2 = cget i₀ L j := by
  obtain ⟨j, hj⟩ := j
  rcases j with _ | j
  · exact (h₀ rfl).elim
  · have hjl : j + 1 < L.length := by
      have : j + 1 ≠ L.length := fun h => hl (Fin.ext h)
      omega
    refine ⟨L[j], ?_, by simp [cget]⟩
    rw [List.mem_iff_getElem]
    exact ⟨j, by simp; omega, by simp [List.getElem_dropLast]⟩

end IncWalk

section Map

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}
  {Z' : Type u'} [TopologicalSpace Z'] {ι' : Type v'} {K' : CurveConfig Z' ι'} {r' : ι'}
  (ψ : Z → Z')

/-- The component `C i` is **contracted** by `ψ`. -/
def Contr (i : ι) : Prop := ∃ y, ψ '' K.C i = {y}

variable (K K') in
/-- **Harmonic weights** along `ψ : Z → Z'`: every walk of the incidence graph of `K` crossing a
special point `y'` of `K'` — its special points over `y'`, its inner components contracted to
`y'`, its end components not contracted and mapped onto different components `C' a ≠ C' b`
through `y'` — which uses each special point at most once and does not backtrack, has weight
at least `w' y'`. -/
def IsHarmonicWeight (w : Z → ℝ≥0∞) (w' : Z' → ℝ≥0∞) : Prop :=
  ∀ (i₀ : ι) (L : List (Z × ι)) (y' : Z') (a b : ι'), L ≠ [] → IncWalk K i₀ L →
    (L.map Prod.fst).Nodup → NoBack i₀ L → (∀ p ∈ L, ψ p.1 = y') →
    (∀ p ∈ L.dropLast, ψ '' K.C p.2 = {y'}) →
    ¬ Contr (K := K) ψ i₀ → ¬ Contr (K := K) ψ (lastLab i₀ L) →
    ψ '' K.C i₀ = K'.C a → ψ '' K.C (lastLab i₀ L) = K'.C b → a ≠ b →
    y' ∈ K'.S → y' ∈ K'.C a → y' ∈ K'.C b →
    w' y' ≤ (L.map fun p => w p.1).sum

variable {ψ} {h : K.Cover r → K'.Cover r'} (hh : Continuous h) (hψ : ∀ x, (h x).1.1 = ψ x.1.1)
include hh

/-- (F1) Points near a component vertex map below the image of its generic point. -/
lemma below_map_gen {x : K.Cover r} {t : K.Tree r} (hx : Near x.1.2 t) :
    Below (h x).1.2 (h (gen t)).1.2 :=
  below_of_mem_closure_cover (map_mem_closure hh (mem_closure_gen hx)
    (fun a ha => by rw [mem_singleton_iff.1 ha]; rfl))

include hψ

/-- (F2) A contracted component: all points near it map to the image of its generic point. -/
lemma map_eq_map_gen {x : K.Cover r} {t : K.Tree r} {i : ι} (ht : t.1.head? = some (.inl i))
    (hc : Contr (K := K) ψ i) (hx : Near x.1.2 t) : h x = h (gen t) := by
  obtain ⟨y, hy⟩ := hc
  refine eq_of_mem_closure (map_mem_closure hh (mem_closure_gen hx)
    (fun a ha => by rw [mem_singleton_iff.1 ha]; rfl)) ?_
  rw [hψ, hψ]
  have h₁ : ψ x.1.1 ∈ ψ '' K.C i := ⟨_, mem_C_of_near ht hx, rfl⟩
  have h₂ : ψ (gen t).1.1 ∈ ψ '' K.C i :=
    ⟨_, by rw [gen_fst_of_inl ht]; exact K.η_mem i, rfl⟩
  rw [hy] at h₁ h₂
  exact h₁.trans h₂.symm

omit hh in
/-- (F3) The generic point of a non-contracted component maps to a component vertex over the
image component. -/
lemma map_gen_of_not_contr
    (hNC : ∀ i, ¬ Contr (K := K) ψ i → ∃ i', ψ '' K.C i = K'.C i' ∧ ψ (K.η i) ∉ K'.S)
    {t : K.Tree r} {i : ι} (ht : t.1.head? = some (.inl i)) (hc : ¬ Contr (K := K) ψ i) :
    ∃ i', (h (gen t)).1.2.1.head? = some (.inl i') ∧ ψ '' K.C i = K'.C i' := by
  obtain ⟨i', hi', hS⟩ := hNC i hc
  have hpt : (h (gen t)).1.1 = ψ (K.η i) := by rw [hψ, gen_fst_of_inl ht]
  rcases (h (gen t)).1.2.2.head_cases with ⟨j, hj⟩ | ⟨s, hs, hs'⟩
  · refine ⟨i', ?_, hi'⟩
    have hmem := Cover.mem_piece_inl hj
    rw [hpt] at hmem
    have : ψ (K.η i) ∈ K'.C i' := hi' ▸ ⟨_, K.η_mem i, rfl⟩
    rw [hj, K'.eq_of_notMem_S hmem.1 this hmem.2]
  · have := Cover.eq_of_inr hs'
    rw [hpt] at this
    exact (hS (this ▸ hs)).elim

omit hh hψ in
lemma exists_split (P : K.Tree r × K.Tree r → Prop) : ∀ L : List (K.Tree r × K.Tree r),
    (∀ p ∈ L, P p) ∨ ∃ L₁ x L₂, L = L₁ ++ x :: L₂ ∧ (∀ p ∈ L₁, P p) ∧ ¬ P x
  | [] => .inl (by simp)
  | x :: L => by
    by_cases hx : P x
    · rcases exists_split P L with h | ⟨L₁, y, L₂, rfl, h₁, h₂⟩
      · exact .inl fun p hp => (List.mem_cons.1 hp).elim (fun e => e ▸ hx) (h p)
      · exact .inr ⟨x :: L₁, y, L₂, rfl,
          fun p hp => (List.mem_cons.1 hp).elim (fun e => e ▸ hx) (h₁ p), h₂⟩
    · exact .inr ⟨[], x, L, rfl, by simp, hx⟩

/-- (Seg) Along a walk whose inner components are contracted, all special vertices and inner
components have the same image. -/
lemma map_gen_seg : ∀ {t₀ σ₁ t₁ : K.Tree r} {L : List (K.Tree r × K.Tree r)}, IsComp t₀ →
    PWalk t₀ ((σ₁, t₁) :: L) → (∀ p ∈ ((σ₁, t₁) :: L).dropLast, Contr (K := K) ψ (lab p.2)) →
    (∀ p ∈ (σ₁, t₁) :: L, h (gen p.1) = h (gen σ₁)) ∧
      ∀ p ∈ ((σ₁, t₁) :: L).dropLast, h (gen p.2) = h (gen σ₁)
  | t₀, σ₁, t₁, [], _, _, _ => by simp
  | t₀, σ₁, t₁, (σ₂, t₂) :: L, ht₀, ⟨h₁, h₂, h₃⟩, hc => by
    have hσ₁ := isSpecial_of_adj ht₀ h₁
    obtain ⟨i₁, hi₁⟩ := isComp_of_adj hσ₁ h₂
    have hct₁ : Contr (K := K) ψ i₁ := by
      have := hc (σ₁, t₁) (by simp [List.dropLast_cons_of_ne_nil])
      rwa [lab_of hi₁] at this
    have e₁ : h (gen σ₁) = h (gen t₁) :=
      map_eq_map_gen hh hψ hi₁ hct₁ (gen_near_of_adj hσ₁ h₂)
    have e₂ : h (gen σ₂) = h (gen t₁) :=
      map_eq_map_gen hh hψ hi₁ hct₁
        (gen_near_of_adj (isSpecial_of_adj ⟨i₁, hi₁⟩ h₃.1) (Tree.adj_comm.1 h₃.1))
    obtain ⟨ih₁, ih₂⟩ := map_gen_seg (L := L) ⟨i₁, hi₁⟩ h₃ fun p hp =>
      hc p (by rw [List.dropLast_cons_of_ne_nil (by simp)]; exact List.mem_cons_of_mem _ hp)
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rcases List.mem_cons.1 hp with rfl | hp
      · rfl
      · rw [ih₁ p hp, e₂, e₁]
    · rw [List.dropLast_cons_of_ne_nil (by simp)] at hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact e₁.symm
      · rw [ih₂ p hp, e₂, e₁]

omit hh hψ in
lemma lab_mem_C_of_adj {t σ : K.Tree r} (ht : IsComp t) (hadj : t.Adj σ) :
    spt σ ∈ K.S ∧ spt σ ∈ K.C (lab t) := by
  obtain ⟨i, hi⟩ := ht
  obtain ⟨s, hs, hS, hsi⟩ := head_inr_of_adj t.2 σ.2 hadj hi
  rw [spt_of hs, lab_of hi]
  exact ⟨hS, hsi⟩

/-- The walk of the incidence graph underlying a walk of the tree. -/
noncomputable def labW (L : List (K.Tree r × K.Tree r)) : List (Z × ι) :=
  L.map fun p => (spt p.1, lab p.2)

omit hh hψ in
lemma incWalk_labW : ∀ {t : K.Tree r} {L : List (K.Tree r × K.Tree r)}, IsComp t →
    PWalk t L → IncWalk K (lab t) (labW L)
  | _, [], _, _ => trivial
  | t, (σ, t') :: L, ht, ⟨h₁, h₂, h₃⟩ => by
    have ht' := isComp_of_adj (isSpecial_of_adj ht h₁) h₂
    exact ⟨(lab_mem_C_of_adj ht h₁).1, (lab_mem_C_of_adj ht h₁).2,
      (lab_mem_C_of_adj ht' (Tree.adj_comm.1 h₂)).2, incWalk_labW ht' h₃⟩

omit hh hψ in
lemma lastLab_labW : ∀ (t : K.Tree r) (L : List (K.Tree r × K.Tree r)),
    lastLab (lab t) (labW L) = lab (pend t L)
  | _, [] => rfl
  | _, (_, t') :: L => lastLab_labW t' L

omit hh hψ in
lemma sum_labW (w : Z → ℝ≥0∞) {t : K.Tree r} {L : List (K.Tree r × K.Tree r)} (ht : IsComp t)
    (hL : PWalk t L) : ((labW L).map fun p => w p.1).sum = cost w L := by
  rw [labW, List.map_map, cost]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  obtain ⟨s, hs⟩ := hL.isSpecial_fst ht p hp
  simp [spt_of hs, tw_of_inr w hs]

/-- The image vertex of a vertex: the vertex of the image of its generic point. -/
noncomputable def img (h : K.Cover r → K'.Cover r') (t : K.Tree r) : K'.Tree r' := (h (gen t)).1.2

variable (hNC : ∀ i, ¬ Contr (K := K) ψ i → ∃ i', ψ '' K.C i = K'.C i' ∧ ψ (K.η i) ∉ K'.S)
  (hC' : Function.Injective K'.C) {w : Z → ℝ≥0∞} {w' : Z' → ℝ≥0∞}
  (hw : IsHarmonicWeight K K' ψ w w')
include hNC hC' hw

/-- (Crossing) The images of the ends of a crossing segment are at distance at most its
weight. -/
lemma cross_le {t₀ : K.Tree r} {S : List (K.Tree r × K.Tree r)} {σ t : K.Tree r}
    (ht₀ : IsComp t₀) (hc₀ : ¬ Contr (K := K) ψ (lab t₀)) (hS : PWalk t₀ (S ++ [(σ, t)]))
    (hSc : ∀ p ∈ S, Contr (K := K) ψ (lab p.2)) (hct : ¬ Contr (K := K) ψ (lab t))
    (hne : img h t₀ ≠ img h t) :
    IsSpecial (h (gen σ)).1.2 ∧ (h (gen σ)).1.2.Adj (img h t₀) ∧
      (h (gen σ)).1.2.Adj (img h t) ∧ w' (h (gen σ)).1.1 ≤ cost w (S ++ [(σ, t)]) := by
  obtain ⟨i₀, hi₀⟩ := ht₀
  have ht : IsComp t := by
    have := PWalk.isComp_pend ⟨i₀, hi₀⟩ hS
    rwa [pend_append] at this
  obtain ⟨i, hi⟩ := ht
  rw [lab_of hi₀] at hc₀
  rw [lab_of hi] at hct
  obtain ⟨a, ha, hia⟩ := map_gen_of_not_contr hψ hNC hi₀ hc₀
  obtain ⟨b, hb, hib⟩ := map_gen_of_not_contr hψ hNC hi hct
  -- the first special vertex
  obtain ⟨σ₁, t₁, L, hSL⟩ : ∃ σ₁ t₁ L, S ++ [(σ, t)] = (σ₁, t₁) :: L := by
    rcases S with _ | ⟨⟨σ₁, t₁⟩, L⟩
    · exact ⟨σ, t, [], rfl⟩
    · exact ⟨σ₁, t₁, L ++ [(σ, t)], rfl⟩
  rw [hSL] at hS
  have hdl : ((σ₁, t₁) :: L).dropLast = S := by rw [← hSL, List.dropLast_concat]
  obtain ⟨hseg₁, hseg₂⟩ := map_gen_seg hh hψ ⟨i₀, hi₀⟩ hS (by rw [hdl]; exact hSc)
  have hσσ₁ : h (gen σ) = h (gen σ₁) := hseg₁ (σ, t) (by rw [← hSL]; simp)
  set P := h (gen σ)
  have hσ₁ := isSpecial_of_adj ⟨i₀, hi₀⟩ hS.1
  have hσ : IsSpecial σ := by
    have := hS
    rw [← hSL, pWalk_append] at this
    exact isSpecial_of_adj (PWalk.isComp_pend ⟨i₀, hi₀⟩ this.1) this.2.1
  have hσt : σ.Adj t := by
    have := hS
    rw [← hSL, pWalk_append] at this
    exact this.2.2.1
  have hb₀ : Below P.1.2 (img h t₀) := by
    rw [show P = h (gen σ₁) from hσσ₁]
    exact below_map_gen hh (gen_near_of_adj hσ₁ (Tree.adj_comm.1 hS.1))
  have hb₁ : Below P.1.2 (img h t) := below_map_gen hh (gen_near_of_adj hσ hσt)
  have hc₀' : IsComp (img h t₀) := ⟨a, ha⟩
  have hc₁' : IsComp (img h t) := ⟨b, hb⟩
  -- the image of the special vertices is a special vertex adjacent to both ends
  have hsp : IsSpecial P.1.2 := by
    rcases hb₀ with h₀ | h₀
    · rcases hb₁ with h₁ | h₁
      · exact (hne (h₀.symm.trans h₁)).elim
      · exact h₁.1
    · exact h₀.1
  have hadj₀ : P.1.2.Adj (img h t₀) := by
    rcases hb₀ with h₀ | h₀
    · exact absurd (h₀ ▸ hc₀') (not_isComp_of_isSpecial hsp)
    · exact h₀.2
  have hadj₁ : P.1.2.Adj (img h t) := by
    rcases hb₁ with h₁ | h₁
    · exact absurd (h₁ ▸ hc₁') (not_isComp_of_isSpecial hsp)
    · exact h₁.2
  refine ⟨hsp, hadj₀, hadj₁, ?_⟩
  obtain ⟨y', hy'⟩ := hsp
  have hPy : P.1.1 = y' := Cover.eq_of_inr hy'
  obtain ⟨a', ha', hy'S, hy'a⟩ := head_inl_of_adj P.1.2.2 (img h t₀).2 hadj₀ hy'
  obtain ⟨b', hb', -, hy'b⟩ := head_inl_of_adj P.1.2.2 (img h t).2 hadj₁ hy'
  rw [img, ha] at ha'
  rw [img, hb] at hb'
  obtain rfl : a' = a := by simpa using ha'.symm
  obtain rfl : b' = b := by simpa using hb'.symm
  have hab : a' ≠ b' := by
    rintro rfl
    exact hne ((Tree.eq_nbr hadj₀ hy' (v := .inl a') ⟨hy'S, hy'a⟩ ha).trans
      (Tree.eq_nbr hadj₁ hy' (v := .inl a') ⟨hy'S, hy'a⟩ hb).symm)
  -- the walk of the incidence graph
  have hW := incWalk_labW ⟨i₀, hi₀⟩ hS
  rw [lab_of hi₀] at hW
  have hlast : lastLab i₀ (labW ((σ₁, t₁) :: L)) = i := by
    rw [← lab_of hi₀, lastLab_labW, ← hSL, pend_append, pend_cons, pend_nil, lab_of hi]
  obtain ⟨L', hW', hlast', hnd, hnb, hsub, hQ⟩ := IncWalk.exists_short
    (fun j => ψ '' K.C j = {y'}) _ le_rfl hW (by
      intro p hp
      rw [labW, List.map_dropLast.symm, hdl] at hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
      have hqS : q ∈ (σ₁, t₁) :: L := by rw [← hSL]; simp [hq]
      obtain ⟨j, hj⟩ := hS.isComp_snd ⟨i₀, hi₀⟩ q hqS
      obtain ⟨y, hy⟩ := hSc q hq
      have hPq : h (gen q.2) = P := (hseg₂ q (by rw [hdl]; exact hq)).trans hσσ₁.symm
      have hη : ψ (K.η j) = y' := by
        rw [← hPy, ← hPq, hψ, gen_fst_of_inl hj]
      have hηy : ψ (K.η j) ∈ ψ '' K.C (lab q.2) := ⟨_, by rw [lab_of hj]; exact K.η_mem j, rfl⟩
      rw [hy, hη] at hηy
      change ψ '' K.C (lab q.2) = {y'}
      rw [hy, mem_singleton_iff.1 hηy])
  have hsum : ((labW ((σ₁, t₁) :: L)).map fun p => w p.1).sum = cost w (S ++ [(σ, t)]) := by
    rw [hSL]; exact sum_labW w ⟨i₀, hi₀⟩ hS
  rw [← hsum, hPy]
  have hL'ne : L' ≠ [] := by
    rintro rfl
    rw [lastLab_nil, hlast] at hlast'
    subst hlast'
    exact hab (hC' (hia.symm.trans hib))
  have hmem : ∀ p ∈ L', ψ p.1 = y' := by
    intro p hp
    have h₁ : p.1 ∈ (labW ((σ₁, t₁) :: L)).map Prod.fst :=
      hsub.subset (List.mem_map_of_mem hp)
    rw [labW, List.map_map] at h₁
    obtain ⟨q, hq, hq'⟩ := List.mem_map.1 h₁
    rw [← hq']
    change ψ (gen q.1).1.1 = y'
    rw [← hψ, hseg₁ q hq, ← hσσ₁, hPy]
  refine (hw i₀ L' y' a' b' hL'ne hW' hnd hnb hmem hQ hc₀ (by rw [hlast', hlast]; exact hct)
    hia (by rw [hlast', hlast]; exact hib) hab hy'S hy'a hy'b).trans ?_
  rw [show (L'.map fun p => w p.1) = (L'.map Prod.fst).map w by simp [List.map_map],
    show ((labW ((σ₁, t₁) :: L)).map fun p => w p.1) =
      ((labW ((σ₁, t₁) :: L)).map Prod.fst).map w by simp [List.map_map]]
  exact (hsub.map w).sum_le_sum fun _ _ => zero_le

omit hNC hC' hw in
/-- Along a walk all of whose components are contracted, the end component has the image of
the first special vertex. -/
lemma map_gen_pend_of_contr : ∀ {t₀ σ₁ t₁ : K.Tree r} {L : List (K.Tree r × K.Tree r)},
    IsComp t₀ → PWalk t₀ ((σ₁, t₁) :: L) → (∀ p ∈ (σ₁, t₁) :: L, Contr (K := K) ψ (lab p.2)) →
    h (gen (pend t₀ ((σ₁, t₁) :: L))) = h (gen σ₁)
  | t₀, σ₁, t₁, L, ht₀, ⟨h₁, h₂, h₃⟩, hc => by
    have hσ₁ := isSpecial_of_adj ht₀ h₁
    obtain ⟨i₁, hi₁⟩ := isComp_of_adj hσ₁ h₂
    have hct₁ : Contr (K := K) ψ i₁ := by
      have := hc (σ₁, t₁) (by simp)
      rwa [lab_of hi₁] at this
    have e₁ : h (gen σ₁) = h (gen t₁) :=
      map_eq_map_gen hh hψ hi₁ hct₁ (gen_near_of_adj hσ₁ h₂)
    rcases L with _ | ⟨⟨σ₂, t₂⟩, L⟩
    · exact e₁.symm
    · have e₂ : h (gen σ₂) = h (gen t₁) :=
        map_eq_map_gen hh hψ hi₁ hct₁
          (gen_near_of_adj (isSpecial_of_adj ⟨i₁, hi₁⟩ h₃.1) (Tree.adj_comm.1 h₃.1))
      rw [pend_cons, map_gen_pend_of_contr ⟨i₁, hi₁⟩ h₃
        (fun p hp => hc p (List.mem_cons_of_mem _ hp)), e₂, e₁]

omit hh hψ hNC hC' hw in
lemma tlen_eq_zero_of_below {X Y V : K'.Tree r'} (hX : Below X V) (hY : Below Y V) :
    tlen w' X Y = 0 := by
  rcases isComp_or_isSpecial V with hV | hV
  · exact le_antisymm ((tlen_le w' (hX.near hV) (hY.near hV) (L := []) trivial rfl).trans_eq rfl)
      zero_le
  · rw [hX.eq_of_isSpecial hV, hY.eq_of_isSpecial hV, tlen_self]

/-- (Claim D) A walk from a non-contracted component vertex maps to a walk from its image of no
larger weight, ending near anything below the image of the end. -/
theorem exists_walk_img_aux : ∀ (n : ℕ) {t₀ : K.Tree r} {L : List (K.Tree r × K.Tree r)},
    L.length ≤ n → IsComp t₀ → ¬ Contr (K := K) ψ (lab t₀) → PWalk t₀ L → ∀ (Y : K'.Tree r'),
    Below Y (img h (pend t₀ L)) →
    ∃ Y' L', Near Y Y' ∧ PWalk (img h t₀) L' ∧ pend (img h t₀) L' = Y' ∧
      cost w' L' ≤ cost w L
  | 0, t₀, L, hn, ht₀, hc₀, _, Y, hY => by
    obtain rfl := List.length_eq_zero_iff.1 (Nat.le_zero.1 hn)
    obtain ⟨i₀, hi₀⟩ := ht₀
    rw [lab_of hi₀] at hc₀
    obtain ⟨a, ha, -⟩ := map_gen_of_not_contr hψ hNC hi₀ hc₀
    exact ⟨img h t₀, [], hY.near ⟨a, ha⟩, trivial, rfl, zero_le⟩
  | n + 1, t₀, L, hn, ht₀, hc₀, hL, Y, hY => by
    obtain ⟨i₀, hi₀⟩ := ht₀
    have hc₀' := hc₀
    rw [lab_of hi₀] at hc₀'
    obtain ⟨a, ha, -⟩ := map_gen_of_not_contr hψ hNC hi₀ hc₀'
    have hcomp₀ : IsComp (img h t₀) := ⟨a, ha⟩
    rcases exists_split (fun p => Contr (K := K) ψ (lab p.2)) L with
      hall | ⟨L₁, ⟨σ, t⟩, L₃, rfl, h₁, hct⟩
    · rcases L with _ | ⟨⟨σ₁, t₁⟩, L⟩
      · exact ⟨img h t₀, [], hY.near hcomp₀, trivial, rfl, zero_le⟩
      · have e := map_gen_pend_of_contr hh hψ ⟨i₀, hi₀⟩ hL hall
        have hσ₁ := isSpecial_of_adj ⟨i₀, hi₀⟩ hL.1
        have hb : Below (h (gen σ₁)).1.2 (img h t₀) :=
          below_map_gen hh (gen_near_of_adj hσ₁ (Tree.adj_comm.1 hL.1))
        rw [img, e] at hY
        refine ⟨img h t₀, [], ?_, trivial, rfl, zero_le⟩
        rcases hb with hb | ⟨hsp, hadj⟩
        · exact (hb ▸ hY).near hcomp₀
        · rw [hY.eq_of_isSpecial hsp]
          exact .inr ⟨hsp, hadj⟩
    · rw [show L₁ ++ (σ, t) :: L₃ = (L₁ ++ [(σ, t)]) ++ L₃ by simp] at hL hY ⊢
      rw [pWalk_append] at hL
      have hpend : pend t₀ (L₁ ++ [(σ, t)]) = t := by simp [pend_append]
      rw [hpend] at hL
      rw [pend_append, hpend] at hY
      have ht : IsComp t := by
        have := PWalk.isComp_pend ⟨i₀, hi₀⟩ hL.1
        rwa [hpend] at this
      obtain ⟨Y', L₃', hY', hL₃', hend, hcost⟩ := exists_walk_img_aux n (L := L₃)
        (by simp only [List.length_append, List.length_cons] at hn; omega)
        ht hct hL.2 Y hY
      by_cases he : img h t₀ = img h t
      · refine ⟨Y', L₃', hY', he ▸ hL₃', he ▸ hend, hcost.trans ?_⟩
        rw [cost_append]
        exact le_add_self
      · obtain ⟨hsp, hadj₀, hadj₁, hcross⟩ :=
          cross_le hh hψ hNC hC' hw ⟨i₀, hi₀⟩ hc₀ hL.1 h₁ hct he
        refine ⟨Y', ((h (gen σ)).1.2, img h t) :: L₃', hY',
          ⟨Tree.adj_comm.1 hadj₀, hadj₁, hL₃'⟩, hend, ?_⟩
        obtain ⟨y', hy'⟩ := hsp
        rw [cost_cons, cost_append, tw_of_inr w' hy', ← Cover.eq_of_inr hy']
        exact add_le_add hcross hcost

theorem exists_walk_img {t₀ : K.Tree r} {L : List (K.Tree r × K.Tree r)} (ht₀ : IsComp t₀)
    (hc₀ : ¬ Contr (K := K) ψ (lab t₀)) (hL : PWalk t₀ L) (Y : K'.Tree r')
    (hY : Below Y (img h (pend t₀ L))) :
    ∃ Y' L', Near Y Y' ∧ PWalk (img h t₀) L' ∧ pend (img h t₀) L' = Y' ∧
      cost w' L' ≤ cost w L :=
  exists_walk_img_aux hh hψ hNC hC' hw _ le_rfl ht₀ hc₀ hL Y hY

/-- (Claim C) The length between points below the images of the ends of a walk is at most the
weight of the walk. -/
theorem tlen_le_cost {t₀ : K.Tree r} {L : List (K.Tree r × K.Tree r)} (ht₀ : IsComp t₀)
    (hL : PWalk t₀ L) {X Y : K'.Tree r'} (hX : Below X (img h t₀))
    (hY : Below Y (img h (pend t₀ L))) : tlen w' X Y ≤ cost w L := by
  by_cases hc₀ : Contr (K := K) ψ (lab t₀)
  · obtain ⟨i₀, hi₀⟩ := ht₀
    rw [lab_of hi₀] at hc₀
    rcases exists_split (fun p => Contr (K := K) ψ (lab p.2)) L with
      hall | ⟨L₁, ⟨σ, t⟩, L₃, rfl, h₁, hct⟩
    · rcases L with _ | ⟨⟨σ₁, t₁⟩, L⟩
      · exact (tlen_eq_zero_of_below hX hY).trans_le zero_le
      · have e := map_gen_pend_of_contr hh hψ ⟨i₀, hi₀⟩ hL hall
        have hσ₁ := isSpecial_of_adj ⟨i₀, hi₀⟩ hL.1
        have e₀ : h (gen σ₁) = h (gen t₀) :=
          map_eq_map_gen hh hψ hi₀ hc₀ (gen_near_of_adj hσ₁ (Tree.adj_comm.1 hL.1))
        rw [img, e, e₀] at hY
        exact (tlen_eq_zero_of_below hX hY).trans_le zero_le
    · rw [show L₁ ++ (σ, t) :: L₃ = (L₁ ++ [(σ, t)]) ++ L₃ by simp] at hL hY ⊢
      rw [pWalk_append] at hL
      have hpend : pend t₀ (L₁ ++ [(σ, t)]) = t := by simp [pend_append]
      rw [hpend] at hL
      rw [pend_append, hpend] at hY
      have ht : IsComp t := by
        have := PWalk.isComp_pend ⟨i₀, hi₀⟩ hL.1
        rwa [hpend] at this
      -- the image of the start is the image of the first crossing
      obtain ⟨σ₁, t₁, M, hSM⟩ : ∃ σ₁ t₁ M, L₁ ++ [(σ, t)] = (σ₁, t₁) :: M := by
        rcases L₁ with _ | ⟨⟨σ₁, t₁⟩, M⟩
        · exact ⟨σ, t, [], rfl⟩
        · exact ⟨σ₁, t₁, M ++ [(σ, t)], rfl⟩
      have hS := hL.1
      rw [hSM] at hS
      have hdl : ((σ₁, t₁) :: M).dropLast = L₁ := by rw [← hSM, List.dropLast_concat]
      obtain ⟨hseg₁, -⟩ := map_gen_seg hh hψ ⟨i₀, hi₀⟩ hS (by rw [hdl]; exact h₁)
      have hσσ₁ : h (gen σ) = h (gen σ₁) := hseg₁ (σ, t) (by rw [← hSM]; simp)
      have hσ₁ := isSpecial_of_adj ⟨i₀, hi₀⟩ hS.1
      have e₀ : h (gen σ₁) = h (gen t₀) :=
        map_eq_map_gen hh hψ hi₀ hc₀ (gen_near_of_adj hσ₁ (Tree.adj_comm.1 hS.1))
      have hσ : IsSpecial σ ∧ σ.Adj t := by
        have := hL.1
        rw [pWalk_append] at this
        exact ⟨isSpecial_of_adj (PWalk.isComp_pend ⟨i₀, hi₀⟩ this.1) this.2.1, this.2.2.1⟩
      have hb : Below (img h t₀) (img h t) := by
        rw [img, ← e₀, ← hσσ₁]
        exact below_map_gen hh (gen_near_of_adj hσ.1 hσ.2)
      obtain ⟨Y', L₃', hY', hL₃', hend, hcost⟩ :=
        exists_walk_img hh hψ hNC hC' hw ht hct hL.2 Y hY
      have hXn : Near X (img h t) := by
        obtain ⟨b, hb', -⟩ := map_gen_of_not_contr hψ hNC (i := lab t)
          (by obtain ⟨j, hj⟩ := ht; rw [lab_of hj]; exact hj) hct
        rcases hb with hb | ⟨hsp, hadj⟩
        · exact (hb ▸ hX).near ⟨b, hb'⟩
        · rw [hX.eq_of_isSpecial hsp]
          exact .inr ⟨hsp, hadj⟩
      refine (tlen_le w' hXn hY' hL₃' hend).trans (hcost.trans ?_)
      rw [cost_append]
      exact le_add_self
  · obtain ⟨Y', L', hY', hL', hend, hcost⟩ := exists_walk_img hh hψ hNC hC' hw ht₀ hc₀ hL Y hY
    obtain ⟨i₀, hi₀⟩ := ht₀
    rw [lab_of hi₀] at hc₀
    obtain ⟨a, ha, -⟩ := map_gen_of_not_contr hψ hNC hi₀ hc₀
    exact (tlen_le w' (hX.near ⟨a, ha⟩) hY' hL' hend).trans hcost

/-- **Monotonicity of lengths along maps of tree coverings**: for `h : K.Cover r → K'.Cover r'`
continuous over `ψ`, with every component contracted or mapped onto a component (its generic
point to a non-special point), and harmonic weights, lengths do not increase. -/
theorem tlen_map_le (p q : K.Cover r) : tlen w' (h p).1.2 (h q).1.2 ≤ tlen w p.1.2 q.1.2 := by
  refine le_sInf ?_
  rintro _ ⟨a', b', L, ha, hb, hL, hend, rfl⟩
  exact tlen_le_cost hh hψ hNC hC' hw ha.isComp hL (below_map_gen hh ha)
    (hend ▸ below_map_gen hh hb)

end Map

end CurveConfig

end TemperedFundamentalGroups
