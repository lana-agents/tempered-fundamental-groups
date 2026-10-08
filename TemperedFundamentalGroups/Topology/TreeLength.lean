/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.CurveCovering

/-!
# Weighted lengths in the tree covering of a curve configuration (Blueprint §10.3.6, item 3)

The vertices of the tree covering `CurveConfig.Cover` of a curve configuration `K` (root `r`)
are the reduced walks in the incidence graph starting at `r` (`CurveConfig.Tree`): lists of
components `.inl i` and special points `.inr s` (the edges of the dual graph, i.e. the nodes),
last vertex first. Given **weights** `w : Z → ℕ` on the special points (for a semistable model:
the thickness of a node times its local degree over a base model), the **length** of a walk is the
sum of the weights of the special points it crosses (`CurveConfig.wlen`).

* `CurveConfig.Red.mem_vertices`: the entries of a reduced walk are components or special points;
* `CurveConfig.Red.length_le`: if all weights on `S` are positive, a reduced walk of length `L`
  has at most `2 L + 1` entries;
* `CurveConfig.finite_tree_wlen_le`, `CurveConfig.finite_cover_wlen_le`: for positive weights,
  there are only finitely many vertices of the tree, and finitely many points of the covering over
  a given point of `Z`, of length at most `L` (the finiteness clause of B5).
-/

universe u v

open Set

namespace TemperedFundamentalGroups

namespace CurveConfig

section Weight

variable {Z : Type u} {ι : Type v}

/-- The weight of a vertex of the incidence graph: `0` for components, `w s` for special
points. -/
def vweight (w : Z → ℕ) : ι ⊕ Z → ℕ := Sum.elim (fun _ => 0) w

/-- The **weighted length** of a walk: the sum of the weights of the special points on it. -/
def wlen (w : Z → ℕ) (l : List (ι ⊕ Z)) : ℕ := (l.map (vweight w)).sum

@[simp] lemma wlen_nil (w : Z → ℕ) : wlen (ι := ι) w [] = 0 := rfl

@[simp] lemma wlen_cons (w : Z → ℕ) (a : ι ⊕ Z) (l : List (ι ⊕ Z)) :
    wlen w (a :: l) = vweight w a + wlen w l := by
  simp [wlen]

@[simp] lemma vweight_inl (w : Z → ℕ) (i : ι) : vweight w (.inl i : ι ⊕ Z) = 0 := rfl

@[simp] lemma vweight_inr (w : Z → ℕ) (s : Z) : vweight w (.inr s : ι ⊕ Z) = w s := rfl

end Weight

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

variable (K) in
/-- The vertices of the incidence graph: components and special points. -/
def vertices : Set (ι ⊕ Z) := range Sum.inl ∪ Sum.inr '' K.S

lemma finite_vertices [Finite ι] : (vertices K).Finite :=
  (finite_range _).union (K.finite_S.image _)

/-- The entries of a reduced walk are components or special points. -/
theorem Red.mem_vertices : ∀ {l : List (ι ⊕ Z)}, K.Red r l → ∀ a ∈ l, a ∈ vertices K
  | [], h => h.elim
  | [v], h => by
    intro a ha
    rw [List.mem_singleton] at ha
    rw [ha]
    exact .inl ⟨r, (show v = .inl r from h).symm⟩
  | v :: u :: m, h => by
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · rcases a with i | s
      · exact .inl ⟨i, rfl⟩
      · rcases u with i | s'
        · exact .inr ⟨s, h.1.1, rfl⟩
        · exact h.1.elim
    · exact Red.mem_vertices h.2.2 a ha

/-- **Reduced walks are short**: if all special points have positive weight, a reduced walk of
weighted length `L` has at most `2 L + 1` entries (and at most `2 L` if it ends at a special
point). -/
theorem Red.length_le {w : Z → ℕ} (hw : ∀ s ∈ K.S, 1 ≤ w s) :
    ∀ {l : List (ι ⊕ Z)}, K.Red r l →
      l.length ≤ 2 * wlen w l + 1 ∧ ∀ s m, l = .inr s :: m → l.length ≤ 2 * wlen w l
  | [], h => h.elim
  | [v], h => by
    have hv : v = .inl r := h
    subst hv
    refine ⟨by simp, fun s m hsm => ?_⟩
    simp at hsm
  | v :: u :: m, h => by
    obtain ⟨ih₁, ih₂⟩ := Red.length_le hw h.2.2
    rcases v with i | s
    · rcases u with i' | s'
      · exact h.1.elim
      · have := ih₂ s' m rfl
        refine ⟨?_, fun s₀ m₀ h₀ => by simp at h₀⟩
        simp only [List.length_cons, wlen_cons, vweight_inl, vweight_inr] at this ⊢
        omega
    · have hs : 1 ≤ w s := hw s (by rcases u with i' | s' <;> [exact h.1.1; exact h.1.elim])
      have hlen : (Sum.inr s :: u :: m : List (ι ⊕ Z)).length ≤
          2 * wlen w (Sum.inr s :: u :: m) := by
        simp only [List.length_cons, wlen_cons, vweight_inr] at ih₁ ⊢
        omega
      exact ⟨hlen.trans (Nat.le_succ _), fun _ _ _ => hlen⟩

/-- Lists of bounded length with entries in a finite set form a finite set. -/
lemma finite_lists_of_finite {α : Type*} {V : Set α} (hV : V.Finite) (n : ℕ) :
    {l : List α | l.length ≤ n ∧ ∀ a ∈ l, a ∈ V}.Finite := by
  haveI := hV.to_subtype
  refine ((List.finite_length_le (α := V) n).image (List.map Subtype.val)).subset ?_
  rintro l ⟨hlen, hmem⟩
  refine ⟨l.attach.map fun a => ⟨a.1, hmem a.1 a.2⟩, by simpa using hlen, ?_⟩
  simp

/-- **Finiteness of bounded-length vertices**: if all special points have positive weight, only
finitely many vertices of the tree have weighted length at most `L`. -/
theorem finite_tree_wlen_le [Finite ι] {w : Z → ℕ} (hw : ∀ s ∈ K.S, 1 ≤ w s) (L : ℕ) :
    {t : K.Tree r | wlen w t.1 ≤ L}.Finite := by
  refine ((finite_lists_of_finite (finite_vertices (K := K)) (2 * L + 1)).preimage
    (fun t _ t' _ h => Tree.ext h)).subset ?_
  intro t ht
  exact ⟨(Red.length_le hw t.2).1.trans (by simp only [mem_setOf_eq] at ht; omega),
    Red.mem_vertices t.2⟩

/-- **Finiteness of bounded-length points of the covering** over a point `z`: if all special
points have positive weight, only finitely many points of the tree covering over `z` lie over
vertices of weighted length at most `L`. -/
theorem finite_cover_wlen_le [Finite ι] {w : Z → ℕ} (hw : ∀ s ∈ K.S, 1 ≤ w s) (z : Z)
    (L : ℕ) : {x : K.Cover r | K.proj r x = z ∧ wlen w x.1.2.1 ≤ L}.Finite := by
  refine Set.Finite.of_finite_image (f := fun x : K.Cover r => x.1.2)
    ((finite_tree_wlen_le hw L).subset ?_) fun x hx y hy h => Cover.ext (hx.1.trans hy.1.symm) h
  rintro _ ⟨x, hx, rfl⟩
  exact hx.2

end CurveConfig

end TemperedFundamentalGroups
