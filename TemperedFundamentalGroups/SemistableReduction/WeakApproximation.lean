/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weak approximation for finitely many incomparable valuations

Blueprint §9.5, R1 (used for the places of a function field of one variable, and for type-2
valuations in W6). Let `v i` (`i : ι`) be valuations of a field `K` with values in a common
`Γ`. We say `v i` and `v j` are *incomparable* (`WeakApproximation.Incomparable`) if neither
valuation ring contains the other.

* `exists_lt_one_and_one_lt`: if `v i` is incomparable with every `v j`, `j ∈ S`, `j ≠ i`, there is
  `u` with `v i u < 1` and `v j u > 1` for these `j` (Stichtenoth, *Algebraic Function Fields and
  Codes*, proof of Thm. 1.3.1: induction on `S`, replacing `y` by `y + z ^ r` with `r` avoiding
  finitely many exponents);
* `valuation_inv_one_add_pow`: for such `u`, `z = (1 + u ^ s)⁻¹` satisfies `v i (z - 1) = v i u ^ s`
  and `v j z = (v j u ^ s)⁻¹`, i.e. `z` is close to `1` at `v i` and close to `0` at the `v j`.
-/

namespace SemistableReduction

namespace WeakApproximation

variable {K : Type*} [Field K] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {ι : Type*}
  (v : ι → Valuation K Γ)

/-- `v i` and `v j` are incomparable: neither valuation ring contains the other. -/
def Incomparable (i j : ι) : Prop :=
  (∃ a, v i a ≤ 1 ∧ 1 < v j a) ∧ ∃ b, v j b ≤ 1 ∧ 1 < v i b

/-- In a linearly ordered group with zero, `a ^ r = b` has at most one solution `r` if `1 < b`. -/
lemma subsingleton_setOf_pow_eq {a b : Γ} (hb : 1 < b) : {r : ℕ | a ^ r = b}.Subsingleton := by
  intro r hr s hs
  simp only [Set.mem_setOf_eq] at hr hs
  have ha0 : a ≠ 0 := by
    rintro rfl
    rcases r with _ | r
    · rw [pow_zero] at hr
      exact hb.ne hr
    · rw [zero_pow (Nat.succ_ne_zero r)] at hr
      exact (zero_lt_one.trans hb).ne hr
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_pow] at hr
    exact hb.ne hr
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · rcases lt_or_gt_of_ne ha1 with ha | ha
    · have := pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha h
      rw [hr, hs] at this
      exact lt_irrefl _ this
    · have := pow_lt_pow_right₀ ha h
      rw [hr, hs] at this
      exact lt_irrefl _ this
  · rcases lt_or_gt_of_ne ha1 with ha | ha
    · have := pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ha0) ha h
      rw [hr, hs] at this
      exact lt_irrefl _ this
    · have := pow_lt_pow_right₀ ha h
      rw [hr, hs] at this
      exact lt_irrefl _ this

/-- **Weak approximation, step 1.** If `v i` is incomparable with each `v j`, `j ∈ S \ {i}`, there
is `u` with `v i u < 1` and `1 < v j u` for all `j ∈ S \ {i}`. -/
theorem exists_lt_one_and_one_lt (i : ι) (S : Finset ι)
    (hS : ∀ j ∈ S, j ≠ i → Incomparable v i j) :
    ∃ u : K, v i u < 1 ∧ ∀ j ∈ S, j ≠ i → 1 < v j u := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, by simp, by simp⟩
  | insert j₀ S hj₀ ih =>
    obtain ⟨y, hyi, hyS⟩ := ih fun j hj hji ↦ hS j (Finset.mem_insert_of_mem hj) hji
    by_cases hj₀i : j₀ = i
    · subst hj₀i
      refine ⟨y, hyi, fun j hj hji ↦ ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact absurd rfl hji
      · exact hyS j hj hji
    by_cases hy : 1 < v j₀ y
    · refine ⟨y, hyi, fun j hj hji ↦ ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact hy
      · exact hyS j hj hji
    replace hy := not_lt.1 hy
    obtain ⟨⟨a, hai, haj⟩, ⟨b, hbj, hbi⟩⟩ := hS j₀ (Finset.mem_insert_self _ _) hj₀i
    have hb0 : b ≠ 0 := by
      rintro rfl
      simp at hbi
    set z := a / b
    have hzi : v i z < 1 := by
      rw [map_div₀, div_lt_one₀ (zero_lt_one.trans hbi)]
      exact hai.trans_lt hbi
    have hzj : 1 < v j₀ z := by
      rw [map_div₀, one_lt_div₀ ((Valuation.pos_iff _).2 hb0)]
      exact hbj.trans_lt haj
    -- choose an exponent `r ≥ 1` with `v j z ^ r ≠ v j y` for all `j ∈ S \ {i}`
    have hfin : (⋃ j ∈ S.filter (· ≠ i), {r : ℕ | v j z ^ r = v j y}).Finite := by
      refine Set.Finite.biUnion (Finset.finite_toSet _) fun j hj ↦ ?_
      obtain ⟨hjS, hji⟩ := Finset.mem_filter.1 hj
      exact (subsingleton_setOf_pow_eq (hyS j hjS hji)).finite
    obtain ⟨r, hr⟩ := (hfin.union (Set.finite_singleton 0)).exists_notMem
    simp only [Set.mem_union, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_filter,
      Set.mem_singleton_iff, not_or, not_exists] at hr
    obtain ⟨hr, hr0⟩ := hr
    have hrpos : 0 < r := Nat.pos_of_ne_zero hr0
    refine ⟨y + z ^ r, ?_, fun j hj hji ↦ ?_⟩
    · refine (Valuation.map_add _ _ _).trans_lt (max_lt hyi ?_)
      rw [map_pow]
      exact pow_lt_one₀ zero_le hzi hr0
    · rcases Finset.mem_insert.1 hj with rfl | hj
      · have hlt : v j y < v j (z ^ r) := by
          rw [map_pow]
          exact hy.trans_lt (one_lt_pow₀ hzj hr0)
        rw [Valuation.map_add_eq_of_lt_right _ hlt, map_pow]
        exact one_lt_pow₀ hzj hr0
      · have hne : v j y ≠ v j (z ^ r) := by
          rw [map_pow]
          exact fun h ↦ hr j ⟨hj, hji⟩ h.symm
        rw [Valuation.map_add_of_distinct_val _ hne]
        exact (hyS j hj hji).trans_le (le_max_left _ _)

/-- **Weak approximation, step 2.** If `v i u < 1` and `s ≠ 0`, then `z = (1 + u ^ s)⁻¹` satisfies
`v i (z - 1) = v i u ^ s` and `v j z = (v j u ^ s)⁻¹` whenever `1 < v j u`. -/
theorem valuation_inv_one_add_pow {i : ι} {u : K} (hu : v i u < 1) {s : ℕ} (hs : s ≠ 0) :
    v i ((1 + u ^ s)⁻¹ - 1) = v i u ^ s ∧
      ∀ j, 1 < v j u → v j (1 + u ^ s)⁻¹ = (v j u ^ s)⁻¹ := by
  have hi : v i (1 + u ^ s) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left, map_one]
    rw [map_one, map_pow]
    exact pow_lt_one₀ zero_le hu hs
  have h0 : 1 + u ^ s ≠ 0 := by
    intro h
    rw [h, map_zero] at hi
    exact zero_ne_one hi
  refine ⟨?_, fun j hj ↦ ?_⟩
  · have : (1 + u ^ s)⁻¹ - 1 = -(u ^ s) * (1 + u ^ s)⁻¹ := by
      field_simp
      ring
    rw [this, map_mul, Valuation.map_neg, map_inv₀, hi, inv_one, mul_one, map_pow]
  · rw [map_inv₀, Valuation.map_add_eq_of_lt_right, map_pow]
    rw [map_one, map_pow]
    exact one_lt_pow₀ hj hs

end WeakApproximation

end SemistableReduction
