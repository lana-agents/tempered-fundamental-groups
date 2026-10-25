/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.HNNExtension

/-!
# The `t`-length of elements of an HNN extension

For an HNN extension `H = G *_{t A t⁻¹ = B}` (Mathlib's `HNNExtension G A B φ`, with
`t * a = φ a * t`) the number of `t`-letters of a reduced word does not depend on the word
(Britton's lemma, `HNNExtension.NormalWord.ReducedWord.map_fst_eq_and_of_prod_eq`). We call it the
`t`-length `HNNExtension.tLength h`, and compute it after multiplying by `of x * t ^ ε` on the
right (`tLength_mul_of_mul_t_pow`): the length goes up by one unless the last letter cancels.
This is the input for the Bass–Serre tree of `H` (`SemiAnbd/HNNTree.lean`).

## Main results

* `HNNExtension.tLength_prod`: the `t`-length of the product of a reduced word is its length.
* `HNNExtension.tLength_mul_of`: right multiplication by `G` does not change the `t`-length.
* `HNNExtension.tLength_mul_t_pow`: right multiplication by `t ^ ε` changes it by exactly one.
* `HNNExtension.tLength_eq_zero_iff`: `t`-length zero means lying in `G`.
* `HNNExtension.tLength_mul_of_mul_t_pow`: the precise rule for `h * of x * t ^ ε` in terms of the
  last letter of a reduced word of `h`.
-/

open HNNExtension.NormalWord

namespace HNNExtension

variable {G : Type*} [Group G] {A B : Subgroup G} {φ : A ≃* B}

lemma t_pow_mul_of_mul_t_pow_neg (u : ℤˣ) (a : toSubgroup A B u) :
    (t ^ (u : ℤ) * of (a : G) * t ^ (-(u : ℤ)) : HNNExtension G A B φ) =
      of (toSubgroupEquiv φ u a : G) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simp only [Units.val_one, zpow_one, zpow_neg, toSubgroupEquiv_one]
    exact (equiv_eq_conj a).symm
  · simp only [Units.val_neg, Units.val_one, Int.reduceNeg, zpow_neg, zpow_one,
      toSubgroupEquiv_neg_one]
    exact (equiv_symm_eq_conj (b := a)).symm

variable (φ) in
lemma exists_reducedWord (h : HNNExtension G A B φ) :
    ∃ w : ReducedWord G A B, w.prod φ = h := by
  obtain ⟨d⟩ := TransversalPair.nonempty G A B
  exact ⟨(equiv φ d h).toReducedWord, (equiv φ d).symm_apply_apply h⟩

/-- The **`t`-length** of an element of the HNN extension: the number of `t`-letters of any
reduced word representing it. -/
noncomputable def tLength (h : HNNExtension G A B φ) : ℕ :=
  (exists_reducedWord φ h).choose.toList.length

/-- The `t`-length of the product of a reduced word is its length (Britton). -/
theorem tLength_prod (w : ReducedWord G A B) : tLength (w.prod φ) = w.toList.length := by
  have h := (exists_reducedWord φ (w.prod φ)).choose_spec
  have := congrArg List.length
    (ReducedWord.map_fst_eq_and_of_prod_eq φ h).1
  simpa [tLength] using this

/-- The reduced word with the same letters and a new head. -/
def _root_.HNNExtension.NormalWord.ReducedWord.withHead (w : ReducedWord G A B) (g : G) :
    ReducedWord G A B := ⟨g, w.toList, w.chain⟩

lemma prod_withHead (w : ReducedWord G A B) (g : G) :
    (w.withHead g).prod φ = of (g * w.head⁻¹) * w.prod φ := by
  simp [ReducedWord.withHead, ReducedWord.prod, ← mul_assoc]

/-- A reduced word with toList `l ++ [(u, g)]`, with the last letter replaced. -/
def _root_.HNNExtension.NormalWord.ReducedWord.setLast (head : G) (l : List (ℤˣ × G)) (u : ℤˣ)
    (g : G) (hc : (l ++ [(u, g)]).IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1))
    (g' : G) : ReducedWord G A B where
  head := head
  toList := l ++ [(u, g')]
  chain := by
    rw [List.isChain_append] at hc ⊢
    refine ⟨hc.1, List.isChain_singleton _, fun x hx y hy ↦ ?_⟩
    rw [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact hc.2.2 x hx (u, g) (by simp)

lemma _root_.List.eq_nil_or_append_singleton {α : Type*} (l : List α) :
    l = [] ∨ ∃ l' a, l = l' ++ [a] := by
  rcases l.eq_nil_or_concat with h | ⟨l', a, h⟩
  exacts [.inl h, .inr ⟨l', a, by simp [h]⟩]

/-- Right multiplication by `G` does not change the `t`-length. -/
theorem tLength_mul_of (h : HNNExtension G A B φ) (x : G) : tLength (h * of x) = tLength h := by
  obtain ⟨w, rfl⟩ := exists_reducedWord φ h
  obtain ⟨head, l, hc⟩ := w
  rcases l.eq_nil_or_append_singleton with rfl | ⟨l, ⟨u, g⟩, rfl⟩
  · have h1 := tLength_prod (φ := φ) ⟨head * x, [], List.isChain_nil⟩
    have h2 := tLength_prod (φ := φ) ⟨head, [], List.isChain_nil⟩
    simp only [ReducedWord.prod, List.map_nil, List.prod_nil, mul_one, map_mul] at h1 h2 ⊢
    rw [h1, h2]
  · have e : (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of x =
        (ReducedWord.setLast head l u g hc (g * x)).prod φ := by
      simp [ReducedWord.prod, ReducedWord.setLast, mul_assoc]
    rw [e, tLength_prod, tLength_prod]
    simp [ReducedWord.setLast]

/-- `t`-length zero means lying in (the image of) `G`. -/
theorem tLength_eq_zero_iff (h : HNNExtension G A B φ) :
    tLength h = 0 ↔ h ∈ (of : G →* _).range := by
  obtain ⟨w, rfl⟩ := exists_reducedWord φ h
  rw [tLength_prod, List.length_eq_zero_iff]
  constructor
  · intro hw
    exact ⟨w.head, by simp [ReducedWord.prod, hw]⟩
  · exact ReducedWord.toList_eq_nil_of_mem_of_range φ w

open scoped Classical in
/-- **The `t`-length after multiplying by `of x * t ^ ε`**, when `h` is the product of a reduced
word with last letter `(u, g)`: it drops by one if `t ^ u * of (g * x) * t ^ ε` cancels, i.e.
`g * x ∈ toSubgroup A B u` and `ε = -u`, and grows by one otherwise. -/
theorem tLength_mul_of_mul_t_pow (head : G) (l : List (ℤˣ × G)) (u : ℤˣ) (g : G)
    (hc : (l ++ [(u, g)]).IsChain (fun a b => a.2 ∈ toSubgroup A B a.1 → a.1 = b.1))
    (x : G) (ε : ℤˣ) :
    tLength ((⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of x * t ^ (ε : ℤ)) =
      if g * x ∈ toSubgroup A B u ∧ ε = -u then l.length else l.length + 2 := by
  split_ifs with hcan
  · obtain ⟨hmem, rfl⟩ := hcan
    have key :
        (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of x * t ^ ((-u : ℤˣ) : ℤ) =
        (⟨head, l, (List.isChain_append.1 hc).1⟩ : ReducedWord G A B).prod φ *
          of (toSubgroupEquiv φ u ⟨g * x, hmem⟩ : G) := by
      rw [← t_pow_mul_of_mul_t_pow_neg]
      simp [ReducedWord.prod, List.map_append, List.prod_append, mul_assoc]
    rw [key, tLength_mul_of, tLength_prod]
  · let w : ReducedWord G A B :=
      { head := head
        toList := l ++ [(u, g * x), (ε, 1)]
        chain := by
          have hc' := hc
          rw [List.isChain_append] at hc'
          rw [show l ++ [(u, g * x), (ε, 1)] = l ++ [(u, g * x)] ++ [(ε, 1)] by simp,
            List.isChain_append]
          refine ⟨(ReducedWord.setLast head l u g hc (g * x)).chain, List.isChain_singleton _, ?_⟩
          intro a ha b hb
          simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
            Option.mem_def, Option.some.injEq] at ha
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
          subst ha hb
          intro hm
          rcases Int.units_eq_one_or u with rfl | rfl <;>
            rcases Int.units_eq_one_or ε with rfl | rfl <;> simp_all }
    have e : (⟨head, l ++ [(u, g)], hc⟩ : ReducedWord G A B).prod φ * of x * t ^ (ε : ℤ) =
        w.prod φ := by
      simp [w, ReducedWord.prod, List.map_append, List.prod_append, mul_assoc]
    rw [e, tLength_prod]
    simp [w]

/-- For `h ∈ G`, `h * of x * t ^ ε` has `t`-length one. -/
theorem tLength_of_mul_t_pow (g : G) (ε : ℤˣ) :
    tLength (of g * t ^ (ε : ℤ) : HNNExtension G A B φ) = 1 := by
  have := tLength_prod (φ := φ) ⟨g, [(ε, 1)], List.isChain_singleton _⟩
  simpa [ReducedWord.prod] using this

/-- Right multiplication by `t ^ ε` changes the `t`-length by exactly one. -/
theorem tLength_mul_t_pow (h : HNNExtension G A B φ) (ε : ℤˣ) :
    tLength (h * t ^ (ε : ℤ)) = tLength h + 1 ∨ tLength (h * t ^ (ε : ℤ)) + 1 = tLength h := by
  obtain ⟨⟨head, l, hc⟩, rfl⟩ := exists_reducedWord φ h
  rcases l.eq_nil_or_append_singleton with rfl | ⟨l, ⟨u, g⟩, rfl⟩
  · left
    rw [tLength_prod]
    simpa [ReducedWord.prod] using tLength_of_mul_t_pow (φ := φ) head ε
  · have := tLength_mul_of_mul_t_pow (φ := φ) head l u g hc 1 ε
    rw [map_one, mul_one] at this
    rw [this, tLength_prod]
    split_ifs <;> simp

end HNNExtension
