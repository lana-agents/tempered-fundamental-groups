/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ConductorLocal

/-!
# Smooth points of reduced curves: one branch

Blueprint §9.9, S7(c) (the one-branch version of S7.8, abstract form; input of §9.10 A6/R1). Let
`ρ : R → K` be a ring homomorphism to a function field of one variable over an algebraically
closed field `k` (the reduction of a chart to the component through a point), `Ã ⊇ ρ(R)` a subring
(the normalization of the component), `Q` a place of `K` and `P` a prime of `R` which is the point
of `Q` (`r ∉ P ⇒ ρ r` is a unit at `Q`); suppose the constants lift to `R`.

* `exists_conductor₁`: if `Ã` is spanned over `ρ(R)` by finitely many elements, each a fraction of
  elements of `ρ(R)`, some `σ ∈ R` with `ρ σ ≠ 0` lies in the conductor: `σ Ã ⊆ ρ(R)`;
* `exists_eq_of_jets₁` (**closedness**, `δ_y = 0 ⇒ Ō_y = O_Q`): if every `a ∈ O_Q` is reached by
  the local ring `R_P` modulo every power of the maximal ideal, it is reached exactly;
* `exists_jet`: modulo every power of the maximal ideal, `a ∈ O_Q` is a polynomial with constant
  coefficients in a uniformizer;
* **`exists_eq_of_uniformizer`**: if some `t ∈ R` reduces to a uniformizer at `Q`, then the local
  ring of the special fibre at `P` is `O_Q`: every `a ∈ O_Q` is `ρ y / ρ s` with `s ∉ P`;
* `exists_uniformizer_of_forall`: conversely, if `ρ(R)_P = O_Q`, some element of `R` reduces to
  a uniformizer;
* **`exists_sub_mem_ker₁`** (the smooth point): if `ρ(R)_P = O_Q` and `ρ t` is a uniformizer,
  every `z` vanishing at the point satisfies `ρ (s z - a t) = 0` for some `a` and `s ∉ P`
  (the form consumed by R1, `BranchRecognition.maximalIdeal_eq_span_of_branch`).
-/

open WithZero Polynomial

namespace SemistableReduction

namespace SmoothPoint

variable {R : Type*} [CommRing R] {K : Type*} [Field K] (ρ : R →+* K)

/-- **An element in the conductor** of one component. -/
theorem exists_conductor₁ (Ã : Subring K) (G : Finset K)
    (hspan : ∀ α ∈ Ã, ∃ r : K → R, α = ∑ g ∈ G, ρ (r g) * g)
    (hfrac : ∀ g ∈ G, ∃ p q : R, ρ q ≠ 0 ∧ ρ p = g * ρ q) :
    ∃ σ : R, ρ σ ≠ 0 ∧ ∀ α ∈ Ã, ∃ r : R, ρ r = ρ σ * α := by
  classical
  have h (g : K) : ∃ p q : R, g ∈ G → ρ q ≠ 0 ∧ ρ p = g * ρ q := by
    by_cases hg : g ∈ G
    · obtain ⟨p, q, hq, hpq⟩ := hfrac g hg
      exact ⟨p, q, fun _ ↦ ⟨hq, hpq⟩⟩
    · exact ⟨0, 0, fun h ↦ absurd h hg⟩
  choose p q hpq using h
  refine ⟨∏ g ∈ G, q g, ?_, fun α hα ↦ ?_⟩
  · rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun g hg ↦ (hpq g hg).1
  obtain ⟨c, hc⟩ := hspan α hα
  refine ⟨∑ g ∈ G, c g * p g * ∏ g' ∈ G.erase g, q g', ?_⟩
  simp only [map_sum, map_mul, map_prod]
  rw [hc, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg ↦ ?_
  rw [(hpq g hg).2, ← Finset.mul_prod_erase G (fun g ↦ ρ (q g)) hg]
  ring

variable {k : Type*} [Field k] [Algebra k K] [IsAlgClosed k] [IsCurveFunctionField k K]
  (Q : CurvePlace k K)

/-- **Closedness of the local ring in its normalization**, one branch: if `σ` is in the
conductor and every element of `O_Q` is made `Ã`-integral by some `τ ∉ P`, an element of `O_Q`
reached by `R_P` modulo every power of the maximal ideal is reached exactly. -/
theorem exists_eq_of_jets₁ (Ã : Subring K) (P : Ideal R) [P.IsPrime]
    (hP : ∀ r, r ∉ P → ρ r ≠ 0) {σ : R} (hσ0 : ρ σ ≠ 0) (hσQ : ρ σ ∈ Q.V)
    (hσ : ∀ α ∈ Ã, ∃ r : R, ρ r = ρ σ * α)
    (hτ : ∀ g ∈ Q.V, ∃ τ : R, τ ∉ P ∧ ρ τ * g ∈ Ã) {a : K}
    (hjet : ∀ M : ℕ, ∃ y s : R, s ∉ P ∧ Q.valuation (ρ y / ρ s - a) ≤ exp (-(M : ℤ))) :
    ∃ y s : R, s ∉ P ∧ ρ y = a * ρ s := by
  obtain ⟨n, hn⟩ := ConductorLocal.valuation_le_exp_of_ne_zero Q hσ0 hσQ
  obtain ⟨y₀, s₀, hs₀, he⟩ := hjet n
  set e := ρ y₀ / ρ s₀ - a
  have hg : e / ρ σ ∈ Q.V := by
    refine Q.valuation_le_one_iff.1 ?_
    rw [map_div₀, hn, div_le_one₀ exp_pos]
    exact he
  obtain ⟨τ, hτP, hτÃ⟩ := hτ _ hg
  obtain ⟨r, hr⟩ := hσ _ hτÃ
  have hs := hP s₀ hs₀
  have ht := hP τ hτP
  refine ⟨y₀ * τ - r * s₀, s₀ * τ, Ideal.IsPrime.mul_notMem ‹_› hs₀ hτP, ?_⟩
  have h : ρ σ * (ρ τ * (e / ρ σ)) = ρ τ * e := by field_simp
  rw [map_sub, map_mul, map_mul, hr, map_mul, h]
  simp only [e]
  field_simp
  ring

/-- **Jets in a uniformizer.** If `π` is a uniformizer at `Q`, every `a ∈ O_Q` is congruent to a
polynomial in `π` with constant coefficients modulo every power of the maximal ideal. -/
theorem exists_jet {π : K} (hπ : Q.valuation π = exp (-1)) {a : K} (ha : a ∈ Q.V) (M : ℕ) :
    ∃ p : k[X], Q.valuation (a - aeval π p) ≤ exp (-(M : ℤ)) := by
  have hπ0 : π ≠ 0 := fun h ↦ by rw [h, map_zero] at hπ; exact exp_ne_zero hπ.symm
  induction M with
  | zero =>
    refine ⟨0, ?_⟩
    rw [map_zero, sub_zero, Nat.cast_zero, neg_zero, exp_zero]
    exact Q.valuation_le_one_iff.2 ha
  | succ M ih =>
    obtain ⟨p, hp⟩ := ih
    set e := a - aeval π p
    have hπM : Q.valuation (π ^ M) = exp (-(M : ℤ)) := by
      rw [map_pow, hπ, ← exp_nsmul]
      congr 1
      simp
    have hq : e / π ^ M ∈ Q.V := by
      refine Q.valuation_le_one_iff.1 ?_
      rw [map_div₀, hπM, div_le_one₀ exp_pos]
      exact hp
    refine ⟨p + C (Q.res (e / π ^ M)) * X ^ M, ?_⟩
    have heq : a - aeval π (p + C (Q.res (e / π ^ M)) * X ^ M) =
        π ^ M * (e / π ^ M - algebraMap k K (Q.res (e / π ^ M))) := by
      rw [mul_sub, mul_div_cancel₀ _ (pow_ne_zero _ hπ0)]
      simp only [e, map_add, map_mul, aeval_C, map_pow, aeval_X]
      ring
    rw [heq, map_mul, hπM]
    have h1 := Q.valuation_sub_res_lt_one hq
    have h2 : Q.valuation (e / π ^ M - algebraMap k K (Q.res (e / π ^ M))) ≤ exp (-1) :=
      WithZero.le_exp_of_lt_exp_add_one (by simpa using h1)
    calc exp (-(M : ℤ)) * Q.valuation (e / π ^ M - algebraMap k K (Q.res (e / π ^ M)))
        ≤ exp (-(M : ℤ)) * exp (-1) := mul_le_mul_right h2 _
      _ = exp (-((M + 1 : ℕ) : ℤ)) := by rw [← exp_add]; congr 1; push_cast; ring

/-- **A uniformizer in the local ring gives the smooth point**: if the constants lift to `R`,
`σ` is in the conductor, poles off `Q` can be cleared by `τ ∉ P`, and some `t ∈ R` reduces to a
uniformizer at `Q`, then every `a ∈ O_Q` is `ρ y / ρ s` with `s ∉ P` (`ρ(R)_P = O_Q`). -/
theorem exists_eq_of_uniformizer (Ã : Subring K) (P : Ideal R) [P.IsPrime]
    (hP : ∀ r, r ∉ P → ρ r ≠ 0) (hk : ∀ c : k, ∃ r : R, ρ r = algebraMap k K c)
    {σ : R} (hσ0 : ρ σ ≠ 0) (hσQ : ρ σ ∈ Q.V) (hσ : ∀ α ∈ Ã, ∃ r : R, ρ r = ρ σ * α)
    (hτ : ∀ g ∈ Q.V, ∃ τ : R, τ ∉ P ∧ ρ τ * g ∈ Ã) {t : R}
    (ht : Q.valuation (ρ t) = exp (-1)) {a : K} (ha : a ∈ Q.V) :
    ∃ y s : R, s ∉ P ∧ ρ y = a * ρ s := by
  choose lift hlift using hk
  refine exists_eq_of_jets₁ ρ Q Ã P hP hσ0 hσQ hσ hτ fun M ↦ ?_
  obtain ⟨p, hp⟩ := exists_jet Q ht ha M
  refine ⟨p.sum fun i c ↦ lift c * t ^ i, 1, Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem
    _ · isUnit_one), ?_⟩
  have hy : ρ (p.sum fun i c ↦ lift c * t ^ i) = aeval (ρ t) p := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, hlift]
  rw [hy, map_one, div_one, ← Valuation.map_neg, neg_sub]
  exact hp

/-- Conversely, if `ρ(R)_P = O_Q`, some element of `R` reduces to a uniformizer at `Q`. -/
theorem exists_uniformizer_of_forall (P : Ideal R) (hPQ : ∀ r, r ∉ P → Q.valuation (ρ r) = 1)
    (hfp : ∀ a ∈ Q.V, ∃ y s : R, s ∉ P ∧ ρ y = a * ρ s) :
    ∃ t : R, Q.valuation (ρ t) = exp (-1) := by
  obtain ⟨π, hπ⟩ := Q.exists_valuation_eq_exp_neg_one
  have hπV : π ∈ Q.V := Q.valuation_le_one_iff.1 (by rw [hπ, ← exp_zero, exp_le_exp]; norm_num)
  obtain ⟨y, s, hs, hy⟩ := hfp π hπV
  exact ⟨y, by rw [hy, map_mul, hπ, hPQ s hs, mul_one]⟩

/-- **The smooth point.** If `ρ(R)_P = O_Q` and `ρ t` is a uniformizer at `Q`, every `z ∈ R`
vanishing at `Q` satisfies `ρ (s z - a t) = 0` for some `a ∈ R` and `s ∉ P`. -/
theorem exists_sub_mem_ker₁ (P : Ideal R) [P.IsPrime]
    (hfp : ∀ a ∈ Q.V, ∃ y s : R, s ∉ P ∧ ρ y = a * ρ s) {t : R}
    (ht : Q.valuation (ρ t) = exp (-1)) {z : R} (hz : Q.valuation (ρ z) < 1) :
    ∃ a s : R, s ∉ P ∧ ρ (s * z - a * t) = 0 := by
  have ht0 : ρ t ≠ 0 := fun h ↦ by rw [h, map_zero] at ht; exact exp_ne_zero ht.symm
  have hα : ρ z / ρ t ∈ Q.V := by
    refine Q.valuation_le_one_iff.1 ?_
    rw [map_div₀, ht, div_le_one₀ exp_pos]
    exact WithZero.le_exp_of_lt_exp_add_one (by simpa using hz)
  obtain ⟨y, s, hs, hy⟩ := hfp _ hα
  refine ⟨y, s, hs, ?_⟩
  rw [map_sub, map_mul, map_mul, hy]
  field_simp
  ring

end SmoothPoint

end SemistableReduction
