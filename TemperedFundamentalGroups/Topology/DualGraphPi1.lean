/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.CurveCovering

/-!
# The combinatorial fundamental group of the incidence graph (Blueprint §11.3, G6.3)

Let `K` be a curve configuration on `Z` with incidence graph `Γ` (vertices `ι ⊕ Z`) and root
component `r`. The vertices of the universal covering tree `K.Tree r` are the reduced walks in
`Γ` starting at `r`. The **combinatorial fundamental group** `K.Loop r` of `Γ` at `r` is the set
of reduced closed walks at `r`, with the product given by concatenation followed by reduction:
`mulList a l` walks from the end of `a` along `l`, cancelling backtracks (`mulList_cons`: each
step is `CurveConfig.nbr`, which either drops the last vertex or appends a new one).

## Main results

* `Tree.IsHom`: maps of the tree preserving adjacency and the labels (last vertices); two such
  maps agreeing at one vertex agree (`Tree.IsHom.ext`), and they are surjective
  (`Tree.IsHom.surjective`), by connectivity of the tree (`Tree.mem_of_adj_closed`).
* `Tree.translate a`: the left translation by a closed walk `a`, a tree map sending the root to
  `a`; `translate_mul : translate (a * b) = translate a ∘ translate b`.
* `instGroupLoop`: the group structure on reduced closed walks at `r`.
* `coverHom : K.Loop r →* (K.Cover r ≃ₜ K.Cover r)`: closed walks act on the tree covering by
  homeomorphisms over `Z`, `(z, t) ↦ (z, a · t)` (`proj_coverHom`).
-/

universe u v

open Set Topology

namespace TemperedFundamentalGroups

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

variable (K r) in
/-- **The combinatorial fundamental group** of the incidence graph at the root `r`: reduced
closed walks at `r` (vertices of the tree whose last vertex is `r`). -/
def Loop : Type _ := {t : K.Tree r // t.1.head? = some (.inl r)}

namespace Tree

lemma exists_head (t : K.Tree r) : ∃ v, t.1.head? = some v := by
  obtain ⟨v, m, hm⟩ := List.exists_cons_of_ne_nil t.2.ne_nil
  exact ⟨v, by rw [hm]; rfl⟩

/-- **The tree is connected**: a set of vertices closed under adjacency containing one vertex
contains all vertices. -/
theorem mem_of_adj_closed {A : Set (K.Tree r)} (hA : ∀ t t', t.Adj t' → t ∈ A → t' ∈ A)
    {t : K.Tree r} (ht : t ∈ A) (t' : K.Tree r) : t' ∈ A := by
  have hroot : root K r ∈ A := by
    obtain ⟨l, hl⟩ := t
    induction l with
    | nil => exact hl.elim
    | cons v l ih =>
      match l, hl, ih with
      | [], hl, _ =>
        obtain rfl : v = .inl r := hl
        exact ht
      | u :: m, hl, ih =>
        exact ih (hl.tail (by simp)) (hA _ ⟨u :: m, hl.tail (by simp)⟩ (.inr rfl) ht)
  obtain ⟨l, hl⟩ := t'
  induction l with
  | nil => exact hl.elim
  | cons v l ih =>
    match l, hl, ih with
    | [], hl, _ =>
      obtain rfl : v = .inl r := hl
      exact hroot
    | u :: m, hl, ih => exact hA ⟨u :: m, hl.tail (by simp)⟩ _ (.inl rfl) (ih (hl.tail (by simp)))

/-- Maps of the tree preserving the last vertex and adjacency. -/
structure IsHom (f : K.Tree r → K.Tree r) : Prop where
  head : ∀ t, (f t).1.head? = t.1.head?
  adj : ∀ t t', t.Adj t' → (f t).Adj (f t')

namespace IsHom

variable {f g : K.Tree r → K.Tree r}

lemma id : IsHom (id : K.Tree r → K.Tree r) := ⟨fun _ ↦ rfl, fun _ _ h ↦ h⟩

lemma comp (hf : IsHom f) (hg : IsHom g) : IsHom (f ∘ g) :=
  ⟨fun t ↦ (hf.head _).trans (hg.head t), fun _ _ h ↦ hf.adj _ _ (hg.adj _ _ h)⟩

/-- Tree maps commute with taking neighbours. -/
lemma map_nbr (hf : IsHom f) (t : K.Tree r) {h v : ι ⊕ Z} (hh : t.1.head? = some h)
    (hv : K.Adj h v) : f (t.nbr hh hv) = (f t).nbr ((hf.head t).trans hh) hv :=
  eq_nbr (hf.adj _ _ (adj_nbr t hh hv)) _ hv ((hf.head _).trans (nbr_head t hh hv))

/-- **Rigidity**: two tree maps agreeing at one vertex are equal. -/
theorem ext (hf : IsHom f) (hg : IsHom g) {t : K.Tree r} (h : f t = g t) : f = g := by
  funext t'
  refine mem_of_adj_closed (A := {x | f x = g x}) (fun x y hxy (hx : f x = g x) ↦ ?_) h t'
  obtain ⟨a, ha⟩ := exists_head x
  obtain ⟨v, hv⟩ := exists_head y
  have hav : K.Adj a v := adj_head x.2 y.2 hxy ha hv
  change f y = g y
  rw [eq_nbr hxy ha hav hv, hf.map_nbr, hg.map_nbr]
  congr 1

/-- Tree maps are surjective. -/
theorem surjective (hf : IsHom f) : Function.Surjective f := by
  intro t'
  refine mem_of_adj_closed (A := range f) (fun x y hxy ↦ ?_) (mem_range_self (root K r)) t'
  rintro ⟨w, rfl⟩
  obtain ⟨a, ha⟩ := exists_head w
  obtain ⟨v, hv⟩ := exists_head y
  have hav : K.Adj a v := adj_head (f w).2 y.2 hxy ((hf.head w).trans ha) hv
  exact ⟨w.nbr ha hav, by rw [hf.map_nbr, eq_nbr hxy _ hav hv]⟩

/-- Tree maps are continuous for the Alexandrov topology. -/
theorem continuous (hf : IsHom f) : Continuous f := by
  rw [continuous_def]
  intro U hU t t' ⟨s, hs⟩ hadj ht
  exact hU (f t) (f t') ⟨s, (hf.head t).trans hs⟩ (hf.adj _ _ hadj) ht

end IsHom

end Tree

section Translate

omit [TopologicalSpace Z] in
/-- Concatenation followed by reduction: walk from the last vertex of `a` along the walk `l`
(coded with the last vertex first, starting at the root), cancelling backtracks. -/
noncomputable def mulList (a : List (ι ⊕ Z)) : List (ι ⊕ Z) → List (ι ⊕ Z)
  | [] => a
  | [_] => a
  | v :: u :: l => nbr (mulList a (u :: l)) v

omit [TopologicalSpace Z] in
lemma mulList_cons (a : List (ι ⊕ Z)) (v u : ι ⊕ Z) (l : List (ι ⊕ Z)) :
    mulList a (v :: u :: l) = nbr (mulList a (u :: l)) v := rfl

theorem red_mulList {a : List (ι ⊕ Z)} (ha : K.Red r a) (har : a.head? = some (.inl r)) :
    ∀ {l : List (ι ⊕ Z)}, K.Red r l → K.Red r (mulList a l) ∧ (mulList a l).head? = l.head?
  | [], hl => hl.elim
  | [_], hl => by
      obtain rfl : _ = Sum.inl r := hl
      exact ⟨ha, har⟩
  | v :: u :: l, hl => by
      obtain ⟨h1, h2⟩ := red_mulList ha har (l := u :: l) hl.2.2
      exact red_nbr h1 h2 (K.adj_comm.1 hl.1)

namespace Tree

/-- **Left translation** of the tree by a reduced closed walk `a` at the root. -/
noncomputable def translate (a : K.Loop r) (t : K.Tree r) : K.Tree r :=
  ⟨mulList a.1.1 t.1, (red_mulList a.1.2 a.2 t.2).1⟩

lemma translate_val (a : K.Loop r) (t : K.Tree r) : (translate a t).1 = mulList a.1.1 t.1 := rfl

lemma translate_root (a : K.Loop r) : translate a (root K r) = a.1 := rfl

lemma translate_head (a : K.Loop r) (t : K.Tree r) :
    (translate a t).1.head? = t.1.head? :=
  (red_mulList a.1.2 a.2 t.2).2

lemma translate_adj_of_tail (a : K.Loop r) {t t' : K.Tree r} (h : t'.1.tail = t.1) :
    (translate a t).Adj (translate a t') := by
  obtain ⟨v, m, hm⟩ := List.exists_cons_of_ne_nil t'.2.ne_nil
  rw [hm, List.tail_cons] at h
  obtain ⟨u, l, hl⟩ := List.exists_cons_of_ne_nil t.2.ne_nil
  subst h
  have := nbr_adj (mulList a.1.1 (u :: l)) v
  unfold Tree.Adj
  rw [translate_val, translate_val, hm, hl, mulList_cons]
  exact this

lemma isHom_translate (a : K.Loop r) : IsHom (translate a) where
  head := translate_head a
  adj t t' := by
    rintro (h | h)
    · exact translate_adj_of_tail a h
    · exact Tree.adj_comm.1 (translate_adj_of_tail a h)

end Tree

namespace Loop

open Tree

instance : One (K.Loop r) := ⟨⟨root K r, rfl⟩⟩

noncomputable instance : Mul (K.Loop r) :=
  ⟨fun a b ↦ ⟨translate a b.1, (translate_head a b.1).trans b.2⟩⟩

lemma exists_translate_eq_root (a : K.Loop r) : ∃ b : K.Tree r, translate a b = root K r :=
  (isHom_translate a).surjective _

noncomputable instance : Inv (K.Loop r) :=
  ⟨fun a ↦ ⟨(exists_translate_eq_root a).choose, by
    rw [← translate_head a, (exists_translate_eq_root a).choose_spec]; rfl⟩⟩

lemma one_val : (1 : K.Loop r).1 = root K r := rfl

/-- The product of closed walks is concatenation followed by reduction. -/
lemma mul_val (a b : K.Loop r) : (a * b).1 = translate a b.1 := rfl

lemma mul_val_val (a b : K.Loop r) : (a * b).1.1 = mulList a.1.1 b.1.1 := rfl

lemma translate_inv (a : K.Loop r) : translate a a⁻¹.1 = root K r :=
  (exists_translate_eq_root a).choose_spec

lemma translate_mul (a b : K.Loop r) : translate (a * b) = translate a ∘ translate b :=
  IsHom.ext (isHom_translate _) ((isHom_translate a).comp (isHom_translate b))
    (t := root K r) rfl

lemma translate_one : translate (1 : K.Loop r) = id :=
  IsHom.ext (isHom_translate _) IsHom.id (t := root K r) rfl

/-- **The combinatorial fundamental group of the incidence graph**: reduced closed walks at the
root under concatenation and reduction. -/
noncomputable instance instGroupLoop : Group (K.Loop r) :=
  Group.ofRightAxioms
    (fun a b c ↦ Subtype.ext (by
      rw [mul_val, mul_val, mul_val, translate_mul]; rfl))
    (fun _ ↦ rfl)
    (fun a ↦ Subtype.ext (translate_inv a))

lemma translate_inv_translate (a : K.Loop r) (t : K.Tree r) :
    translate a⁻¹ (translate a t) = t := by
  rw [← Function.comp_apply (f := translate a⁻¹), ← translate_mul, inv_mul_cancel,
    translate_one, id]

lemma translate_translate_inv (a : K.Loop r) (t : K.Tree r) :
    translate a (translate a⁻¹ t) = t := by
  rw [← Function.comp_apply (f := translate a), ← translate_mul, mul_inv_cancel,
    translate_one, id]

end Loop

end Translate

section CoverAction

open Tree

/-- The map of the tree covering induced by a tree map. -/
def coverMap {f : K.Tree r → K.Tree r} (hf : IsHom f) (x : K.Cover r) : K.Cover r :=
  ⟨(x.1.1, f x.1.2), by rw [hf.head]; exact x.2⟩

lemma continuous_coverMap {f : K.Tree r → K.Tree r} (hf : IsHom f) : Continuous (coverMap hf) :=
  (continuous_fst.comp continuous_subtype_val |>.prodMk
    (hf.continuous.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _

/-- A closed walk at the root acts on the tree covering by a homeomorphism over `Z`. -/
noncomputable def coverTranslate (a : K.Loop r) : K.Cover r ≃ₜ K.Cover r where
  toFun := coverMap (isHom_translate a)
  invFun := coverMap (isHom_translate a⁻¹)
  left_inv x := Cover.ext rfl (Loop.translate_inv_translate a x.1.2)
  right_inv x := Cover.ext rfl (Loop.translate_translate_inv a x.1.2)
  continuous_toFun := continuous_coverMap _
  continuous_invFun := continuous_coverMap _

/-- **The action of the combinatorial fundamental group on the tree covering**. -/
noncomputable def coverHom : K.Loop r →* (K.Cover r ≃ₜ K.Cover r) where
  toFun := coverTranslate
  map_one' := Homeomorph.ext fun x ↦ Cover.ext rfl (congrFun Loop.translate_one x.1.2)
  map_mul' a b := Homeomorph.ext fun x ↦ Cover.ext rfl (congrFun (Loop.translate_mul a b) x.1.2)

lemma coverHom_apply (a : K.Loop r) (x : K.Cover r) :
    (coverHom a x).1 = (x.1.1, translate a x.1.2) := rfl

lemma proj_coverHom (a : K.Loop r) (x : K.Cover r) : K.proj r (coverHom a x) = K.proj r x := rfl

end CoverAction

end CurveConfig

end TemperedFundamentalGroups
