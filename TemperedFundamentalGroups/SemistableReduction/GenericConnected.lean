/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Connected special fibre ⇒ connected generic fibre (MR13 A1)

Let `A` be a Noetherian domain, `π ∈ A` a nonzero nonunit and `B` a finite torsion-free
`A`-algebra (e.g. the chart algebra `B₁` of the lift of a tame cover, finite flat over `O[Y]`, with
`π = ϖ`). If the special fibre `B/πB` is **reduced and has no nontrivial idempotents** (a connected
étale cover of a reduced curve), then the generic fibre `B[1/π]` has no nontrivial idempotents
(**`GenericConnected.isIdempotentElem_away`**):

* an idempotent `e = b/πᵐ` of `B[1/π]` with `m` minimal has `m = 0`: from `b² = πᵐ b` in `B`
  (`π` is regular on `B`) and `m ≥ 1`, `b̄² = 0` in `B/π`, so `b ∈ πB` (reducedness) and `m` was
  not minimal;
* so `e ∈ B`; its reduction is `0` or `1`, and in the first case `e = eⁿ ∈ πⁿB` for all `n`, hence
  `e = 0` by Krull's intersection theorem for the torsion-free finite `A`-module `B`
  (`Ideal.iInf_pow_smul_eq_bot_of_isTorsionFree`); in the second case the same for `1 − e`.
-/

namespace SemistableReduction

namespace GenericConnected

variable {A B : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B] {π : A} (hπ : π ≠ 0) (hπu : ¬IsUnit π)

omit [IsNoetherianRing A] [Module.Finite A B] in
include hπ in
/-- `π` is a nonzerodivisor on `B`. -/
lemma algebraMap_mul_cancel {x y : B} (h : algebraMap A B π * x = algebraMap A B π * y) :
    x = y := by
  rw [← Algebra.smul_def, ← Algebra.smul_def] at h
  exact smul_right_injective B hπ h

include hπu in
/-- **Krull**: an element of `⋂ πⁿ B` is zero. -/
lemma eq_zero_of_forall_mem {b : B}
    (h : ∀ n : ℕ, ∃ c : B, b = algebraMap A B π ^ n * c) : b = 0 := by
  have hI : Ideal.span {π} ≠ ⊤ := fun h ↦ hπu (Ideal.span_singleton_eq_top.mp h)
  have h0 := (Ideal.span {π}).iInf_pow_smul_eq_bot_of_isTorsionFree (M := B) hI
  have hb : b ∈ (⨅ i : ℕ, Ideal.span {π} ^ i • ⊤ : Submodule A B) := by
    refine Submodule.mem_iInf _ |>.mpr fun n ↦ ?_
    obtain ⟨c, rfl⟩ := h n
    rw [← map_pow, ← Algebra.smul_def]
    exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self π) n)
      Submodule.mem_top
  rw [h0] at hb
  exact hb

include hπu in
/-- An idempotent of `B` with reduction `0` modulo `π` is `0`. -/
lemma eq_zero_of_isIdempotentElem {e : B} (he : IsIdempotentElem e)
    (h0 : Ideal.Quotient.mk (Ideal.span {algebraMap A B π}) e = 0) : e = 0 := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp h0)
  refine eq_zero_of_forall_mem hπu fun n ↦ ⟨e * c ^ n, ?_⟩
  calc e = e ^ (n + 1) := (he.pow_succ_eq n).symm
    _ = algebraMap A B π ^ n * (e * c ^ n) := by
      rw [pow_succ', ← hc]
      ring

variable (S : Type*) [CommRing S] [Algebra B S] [IsLocalization.Away (algebraMap A B π) S]

omit [IsNoetherianRing A] [Module.Finite A B] in
include hπ in
/-- `π` is a nonzerodivisor of `B`. -/
lemma mem_nonZeroDivisors : algebraMap A B π ∈ nonZeroDivisors B :=
  mem_nonZeroDivisors_iff_right.mpr fun x hx ↦
    algebraMap_mul_cancel hπ (by rw [mul_comm, hx, mul_zero])

omit [IsNoetherianRing A] [Module.Finite A B] in
include hπ in
/-- `B → B[1/π]` is injective. -/
lemma injective_algebraMap_away : Function.Injective (algebraMap B S) :=
  IsLocalization.injective (M := Submonoid.powers (algebraMap A B π)) S
    (Submonoid.powers_le.mpr (mem_nonZeroDivisors hπ))

variable (hred : IsReduced (B ⧸ Ideal.span {algebraMap A B π}))

omit [IsNoetherianRing A] [Module.Finite A B] in
include hπ hred in
/-- An idempotent of `B[1/π]` lies in `B`. -/
lemma exists_eq_of_isIdempotentElem {e : S} (he : IsIdempotentElem e) :
    ∃ b : B, algebraMap B S b = e := by
  classical
  have hex : ∃ m : ℕ, ∃ b : B, e * algebraMap B S (algebraMap A B π ^ m) = algebraMap B S b := by
    obtain ⟨⟨b, _, m, rfl⟩, h⟩ := IsLocalization.surj (Submonoid.powers (algebraMap A B π)) e
    exact ⟨m, b, h⟩
  obtain ⟨b, hb⟩ := Nat.find_spec hex
  set m := Nat.find hex with hm
  suffices hm0 : m = 0 by
    refine ⟨b, ?_⟩
    rw [← hb, hm0, pow_zero, map_one, mul_one]
  by_contra hne
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
  set p := algebraMap A B π
  have hpu : IsUnit (algebraMap B S p) := IsLocalization.Away.algebraMap_isUnit p
  -- `b² = pᵐ b` in `B`
  have hb2 : b * b = p ^ m * b := by
    apply injective_algebraMap_away hπ S
    rw [map_mul, map_mul, ← hb]
    calc e * algebraMap B S (p ^ m) * (e * algebraMap B S (p ^ m)) =
        (e * e) * algebraMap B S (p ^ m) * algebraMap B S (p ^ m) := by ring
      _ = _ := by rw [he.eq]; ring
  -- so `b ∈ pB`
  have hbn : IsNilpotent (Ideal.Quotient.mk (Ideal.span {p}) b) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← map_mul, hb2, hk, pow_succ, mul_assoc, map_mul, map_mul,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p), zero_mul, mul_zero]
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
    (Ideal.Quotient.eq_zero_iff_mem.mp (hbn.eq_zero))
  -- and `e pᵏ = c`, contradicting the minimality of `m`
  have hk' : e * algebraMap B S (p ^ k) = algebraMap B S c := by
    apply hpu.mul_left_cancel
    calc algebraMap B S p * (e * algebraMap B S (p ^ k)) = e * algebraMap B S (p ^ m) := by
          rw [hk, pow_succ, map_mul]; ring
      _ = algebraMap B S (p * c) := by rw [hb, ← hc, mul_comm]
      _ = _ := map_mul _ _ _
  have := Nat.find_min' hex ⟨c, hk'⟩
  omega

include hπ hπu hred in
/-- **Connected special fibre ⇒ connected generic fibre**: if `B/πB` is reduced and has only the
trivial idempotents, so has `B[1/π]`. -/
theorem isIdempotentElem_away
    (hconn : ∀ e : B ⧸ Ideal.span {algebraMap A B π}, IsIdempotentElem e → e = 0 ∨ e = 1)
    {e : S} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  obtain ⟨b, rfl⟩ := exists_eq_of_isIdempotentElem hπ S hred he
  have hb : IsIdempotentElem b :=
    injective_algebraMap_away hπ S (by rw [map_mul, he.eq])
  rcases hconn _ (hb.map (Ideal.Quotient.mk _)) with h | h
  · left
    rw [eq_zero_of_isIdempotentElem hπu hb h, map_zero]
  · right
    have h1 : Ideal.Quotient.mk (Ideal.span {algebraMap A B π}) (1 - b) = 0 := by
      rw [map_sub, h, map_one, sub_self]
    have := eq_zero_of_isIdempotentElem hπu hb.one_sub h1
    rw [sub_eq_zero] at this
    rw [← this, map_one]

end GenericConnected

end SemistableReduction
