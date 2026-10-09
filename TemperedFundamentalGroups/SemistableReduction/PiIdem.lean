/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Primitive idempotents of products of domains

* `PiIdem.exists_eq_single`: a nonzero primitive idempotent of `Π k, D k` (all `D k` domains) is a
  coordinate idempotent `Pi.single k 1`;
* `PiIdem.quotSingleEquiv`: `(Π k, D k) ⧸ (1 − e_k) ≃ D k`.
-/

namespace SemistableReduction.PiIdem

variable {ι : Type*} [DecidableEq ι] {D : ι → Type*} [∀ k, CommRing (D k)]

/-- A nonzero primitive idempotent of a product of domains is a coordinate idempotent. -/
lemma exists_eq_single [∀ k, IsDomain (D k)] {e : Π k, D k} (he : IsIdempotentElem e)
    (h0 : e ≠ 0) (hprim : ∀ f : Π k, D k, IsIdempotentElem f → f * e = 0 ∨ f * e = e) :
    ∃ k, e = Pi.single k 1 := by
  have hk : ∀ k, e k = 0 ∨ e k = 1 := fun k => by
    have h := congrFun he.eq k
    simp only [Pi.mul_apply] at h
    rcases mul_eq_zero.1 (show e k * (e k - 1) = 0 by rw [mul_sub, h, mul_one, sub_self]) with
      h' | h'
    · exact Or.inl h'
    · exact Or.inr (sub_eq_zero.1 h')
  obtain ⟨k, hk1⟩ : ∃ k, e k = 1 := by
    by_contra h
    push Not at h
    exact h0 (funext fun k => (hk k).resolve_right (h k))
  refine ⟨k, ?_⟩
  have hsingle : IsIdempotentElem (Pi.single k 1 : Π k, D k) := by
    rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
  rcases hprim _ hsingle with h | h
  · have := congrFun h k
    simp [hk1] at this
  · rw [← h]
    ext l
    by_cases hl : l = k
    · subst hl; simp [hk1]
    · simp [hl]

lemma ker_eval_eq_span (k : ι) :
    RingHom.ker (Pi.evalRingHom D k) = Ideal.span {1 - Pi.single k 1} := by
  ext z
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hz
    refine ⟨z, ?_⟩
    ext l
    by_cases hl : l = k
    · subst hl; simpa using hz
    · simp [hl]
  · rintro ⟨w, rfl⟩
    simp

/-- `(Π D) / (1 - e_k) ≅ D k`. -/
noncomputable def quotSingleEquiv (k : ι) :
    ((Π k, D k) ⧸ Ideal.span {1 - (Pi.single k 1 : Π k, D k)}) ≃+* D k :=
  (Ideal.quotEquivOfEq (ker_eval_eq_span k).symm).trans
    (RingHom.quotientKerEquivOfSurjective (f := Pi.evalRingHom D k)
      fun x => ⟨Pi.single k x, by simp⟩)

lemma quotSingleEquiv_mk (k : ι) (z : Π k, D k) :
    quotSingleEquiv k (Ideal.Quotient.mk _ z) = z k := rfl

end SemistableReduction.PiIdem
