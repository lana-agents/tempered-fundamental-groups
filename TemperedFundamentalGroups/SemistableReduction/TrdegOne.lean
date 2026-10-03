/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Function fields of curves are algebraic over every transcendental element (W8′, XL1)

Blueprint §9.7 (XL1, `NodeGerm.alg`). If `L ⊇ K` is algebraic over `K[x]` with `x` transcendental
(transcendence degree one), then `L` is algebraic over `K[u]` for every transcendental `u ∈ L`
(`isAlgebraic_adjoin_of_transcendental`, via Mathlib's transcendence bases), and every nonzero
`f ∈ L` satisfies a relation `c₀(u) = Σ_k c_k(u) f ^ (k + 1)` with `c₀ ≠ 0`
(`exists_relation_of_transcendental`).
-/

open Polynomial

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Transcendence degree one**: `L` is algebraic over `K[u]` for every transcendental `u`. -/
theorem isAlgebraic_adjoin_of_transcendental {x u : L} (hx : Transcendental K x)
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K {x}) L) (hu : Transcendental K u) :
    Algebra.IsAlgebraic (Algebra.adjoin K {u}) L := by
  have hix : AlgebraicIndependent K (fun _ : PUnit ↦ x) :=
    algebraicIndependent_unique_type_iff.mpr hx
  have hiu : AlgebraicIndependent K (fun _ : PUnit ↦ u) :=
    algebraicIndependent_unique_type_iff.mpr hu
  have hbx : IsTranscendenceBasis K (fun _ : PUnit ↦ x) := by
    rw [hix.isTranscendenceBasis_iff_isAlgebraic, Set.range_const]
    exact halg
  have htr : Algebra.trdeg K L = 1 := by
    rw [← hbx.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one]
  have hbu : IsTranscendenceBasis K (fun _ : PUnit ↦ u) :=
    hiu.isTranscendenceBasis_of_trdeg_le (by rw [htr]; exact Cardinal.one_lt_aleph0)
      (by rw [htr, Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one])
  have := hbu.isAlgebraic
  rwa [Set.range_const] at this

/-- **The algebraic relation** of a nonzero `f` over `K[u]` with nonzero constant term. -/
theorem exists_relation_of_transcendental {u : L}
    (halg : Algebra.IsAlgebraic (Algebra.adjoin K {u}) L) {f : L} (hf : f ≠ 0) :
    ∃ (c₀ : K[X]) (S : Finset ℕ) (c : ℕ → K[X]),
      c₀ ≠ 0 ∧ aeval u c₀ = ∑ k ∈ S, aeval u (c k) * f ^ (k + 1) := by
  classical
  obtain ⟨P, hP0, hPf⟩ := (halg.isAlgebraic f)
  obtain ⟨Q, hPQ, hQX⟩ := P.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hP0 0
  simp only [map_zero, sub_zero] at hPQ hQX
  have hQf : aeval f Q = 0 := by
    rw [hPQ, map_mul, map_pow, aeval_X] at hPf
    exact (mul_eq_zero.mp hPf).resolve_left (pow_ne_zero _ hf)
  have hQ0 : Q.coeff 0 ≠ 0 := fun h ↦ hQX (X_dvd_iff.mpr h)
  -- coefficients of `Q` are polynomials in `u`
  have hcoef : ∀ i, ∃ q : K[X], aeval u q = (Q.coeff i : L) := fun i ↦ by
    have h1 : ((Q.coeff i : Algebra.adjoin K {u}) : L) ∈ (aeval u : K[X] →ₐ[K] L).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (Q.coeff i).2
    obtain ⟨q, hq⟩ := h1
    exact ⟨q, hq⟩
  choose q hq using hcoef
  refine ⟨q 0, Finset.range Q.natDegree, fun k ↦ -q (k + 1), ?_, ?_⟩
  · intro h
    apply hQ0
    apply Subtype.ext
    rw [← hq 0, h, map_zero]
    rfl
  · rw [aeval_eq_sum_range, Finset.sum_range_succ'] at hQf
    simp only [pow_zero, Algebra.smul_def] at hQf
    have e : ∀ i, algebraMap (Algebra.adjoin K {u}) L (Q.coeff i) = aeval u (q i) :=
      fun i ↦ (hq i).symm
    simp only [e, mul_one] at hQf
    rw [eq_neg_of_add_eq_zero_right hQf]
    simp [Finset.sum_neg_distrib]

end SemistableReduction
