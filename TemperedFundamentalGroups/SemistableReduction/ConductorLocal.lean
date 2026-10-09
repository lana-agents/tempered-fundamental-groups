/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SpecialFibre

/-!
# Conductors and ordinary double points of reduced curves

Blueprint §9.9, S7.7–S7.8 (abstract form). Let `ρⱼ : R → Kⱼ` (`j = 1, 2`) be ring homomorphisms
to two function fields of one variable over an algebraically closed field `k` (the reductions of a
ring `R` to the two components through a point), `Ãⱼ ⊇ ρⱼ(R)` subrings (the normalizations of the
components).

* `exists_conductor`: if each `Ãⱼ` is spanned over `ρⱼ(R)` by finitely many elements, every
  element of `Ãⱼ` is a fraction of elements of `ρⱼ(R)`, and some `x₀, y₀ ∈ R` separate the two
  components, then some `σ ∈ R` with `ρ₁ σ ≠ 0 ≠ ρ₂ σ` lies in the conductor:
  `σ · (Ã₁ × Ã₂) ⊆ ρ(R)`;
* `exists_eq_of_jets` (**closedness**): for a prime `P` of `R` which is the point of the places
  `Q₁`, `Q₂` on the two components, and assuming that every `(g₁, g₂) ∈ O_{Q₁} × O_{Q₂}` is made
  `Ã`-integral by some `τ ∉ P`: if the local ring `R_P` reaches every element of the fibre product
  `{(a, b) | a(Q₁) = b(Q₂)}` modulo every power of the maximal ideals, it reaches it exactly;
* `exists_sub_mem_ker` (**ordinary double point**): then every `z ∈ P` satisfies
  `s z ≡ a u' + b v'` on both components for `s ∉ P`, whenever `ρ₂ u' = 0`, `ord_{Q₁} ρ₁ u' = 1`,
  `ρ₁ v' = 0`, `ord_{Q₂} ρ₂ v' = 1`.
-/

open WithZero

namespace SemistableReduction

namespace ConductorLocal

variable {R : Type*} [CommRing R] {K₁ K₂ : Type*} [Field K₁] [Field K₂]
  (ρ₁ : R →+* K₁) (ρ₂ : R →+* K₂)

section Conductor

/-- **Elements in the conductor.** -/
theorem exists_conductor (Ã₁ : Subring K₁) (Ã₂ : Subring K₂)
    (G₁ : Finset K₁) (G₂ : Finset K₂) (hG₁ : ∀ g ∈ G₁, g ∈ Ã₁) (hG₂ : ∀ g ∈ G₂, g ∈ Ã₂)
    (hspan₁ : ∀ α ∈ Ã₁, ∃ r : K₁ → R, α = ∑ g ∈ G₁, ρ₁ (r g) * g)
    (hspan₂ : ∀ α ∈ Ã₂, ∃ r : K₂ → R, α = ∑ g ∈ G₂, ρ₂ (r g) * g)
    (hfrac₁ : ∀ α ∈ Ã₁, ∃ p q : R, ρ₁ q ≠ 0 ∧ ρ₁ p = α * ρ₁ q)
    (hfrac₂ : ∀ α ∈ Ã₂, ∃ p q : R, ρ₂ q ≠ 0 ∧ ρ₂ p = α * ρ₂ q)
    {x₀ y₀ : R} (hx₁ : ρ₁ x₀ ≠ 0) (hx₂ : ρ₂ x₀ = 0) (hy₁ : ρ₁ y₀ = 0) (hy₂ : ρ₂ y₀ ≠ 0) :
    ∃ σ : R, ρ₁ σ ≠ 0 ∧ ρ₂ σ ≠ 0 ∧ ∀ α₁ ∈ Ã₁, ∀ α₂ ∈ Ã₂,
      ∃ r : R, ρ₁ r = ρ₁ σ * α₁ ∧ ρ₂ r = ρ₂ σ * α₂ := by
  classical
  -- for each generator, a denominator which is nonzero on both components
  have h₁ (g : K₁) : ∃ s r : R, (g ∈ G₁ → ρ₁ s ≠ 0 ∧ ρ₂ s ≠ 0 ∧ ρ₁ r = ρ₁ s * g ∧ ρ₂ r = 0) := by
    by_cases hg : g ∈ G₁
    · obtain ⟨p, q, hq, hpq⟩ := hfrac₁ g (hG₁ g hg)
      refine ⟨q * x₀ + y₀, p * x₀, fun _ ↦ ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [map_add, map_mul, hy₁, add_zero]; exact mul_ne_zero hq hx₁
      · rw [map_add, map_mul, hx₂, mul_zero, zero_add]; exact hy₂
      · rw [map_mul, map_add, map_mul, hy₁, add_zero, hpq]; ring
      · rw [map_mul, hx₂, mul_zero]
    · exact ⟨0, 0, fun h ↦ absurd h hg⟩
  have h₂ (g : K₂) : ∃ s r : R, (g ∈ G₂ → ρ₁ s ≠ 0 ∧ ρ₂ s ≠ 0 ∧ ρ₁ r = 0 ∧ ρ₂ r = ρ₂ s * g) := by
    by_cases hg : g ∈ G₂
    · obtain ⟨p, q, hq, hpq⟩ := hfrac₂ g (hG₂ g hg)
      refine ⟨x₀ + q * y₀, p * y₀, fun _ ↦ ⟨?_, ?_, ?_, ?_⟩⟩
      · rw [map_add, map_mul, hy₁, mul_zero, add_zero]; exact hx₁
      · rw [map_add, map_mul, hx₂, zero_add]; exact mul_ne_zero hq hy₂
      · rw [map_mul, hy₁, mul_zero]
      · rw [map_mul, map_add, map_mul, hx₂, zero_add, hpq]; ring
    · exact ⟨0, 0, fun h ↦ absurd h hg⟩
  choose s₁ r₁ hsr₁ using h₁
  choose s₂ r₂ hsr₂ using h₂
  set σ₁ := ∏ g ∈ G₁, s₁ g
  set σ₂ := ∏ g ∈ G₂, s₂ g
  refine ⟨σ₁ * σ₂, ?_, ?_, fun α₁ hα₁ α₂ hα₂ ↦ ?_⟩
  · rw [map_mul, map_prod, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun g hg ↦ (hsr₁ g hg).1)
      (Finset.prod_ne_zero_iff.2 fun g hg ↦ (hsr₂ g hg).1)
  · rw [map_mul, map_prod, map_prod]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun g hg ↦ (hsr₁ g hg).2.1)
      (Finset.prod_ne_zero_iff.2 fun g hg ↦ (hsr₂ g hg).2.1)
  obtain ⟨c₁, hc₁⟩ := hspan₁ α₁ hα₁
  obtain ⟨c₂, hc₂⟩ := hspan₂ α₂ hα₂
  refine ⟨σ₂ * ∑ g ∈ G₁, c₁ g * r₁ g * ∏ g' ∈ G₁.erase g, s₁ g' +
    σ₁ * ∑ g ∈ G₂, c₂ g * r₂ g * ∏ g' ∈ G₂.erase g, s₂ g', ?_, ?_⟩
  · simp only [map_add, map_mul, map_sum, map_prod]
    rw [Finset.sum_eq_zero (s := G₂) fun g hg ↦ by rw [(hsr₂ g hg).2.2.1]; ring, mul_zero,
      add_zero, hc₁, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg ↦ ?_
    rw [(hsr₁ g hg).2.2.1, show ρ₁ σ₁ = ∏ g ∈ G₁, ρ₁ (s₁ g) from map_prod _ _ _,
      ← Finset.mul_prod_erase G₁ (fun g ↦ ρ₁ (s₁ g)) hg]
    ring
  · simp only [map_add, map_mul, map_sum, map_prod]
    rw [Finset.sum_eq_zero (s := G₁) fun g hg ↦ by rw [(hsr₁ g hg).2.2.2]; ring, mul_zero,
      zero_add, hc₂, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg ↦ ?_
    rw [(hsr₂ g hg).2.2.2, show ρ₂ σ₂ = ∏ g ∈ G₂, ρ₂ (s₂ g) from map_prod _ _ _,
      ← Finset.mul_prod_erase G₂ (fun g ↦ ρ₂ (s₂ g)) hg]
    ring

end Conductor

section Local

variable {k : Type*} [Field k] [Algebra k K₁] [Algebra k K₂] [IsAlgClosed k]
  [IsCurveFunctionField k K₁] [IsCurveFunctionField k K₂]

/-- An element of `O_Q` which is not a unit has positive order. -/
lemma valuation_le_exp_of_ne_zero (Q : CurvePlace k K₁) {a : K₁} (ha : a ≠ 0) (haQ : a ∈ Q.V) :
    ∃ n : ℕ, Q.valuation a = exp (-(n : ℤ)) := by
  have h0 : Q.valuation a ≠ 0 := (Valuation.ne_zero_iff _).2 ha
  have h1 := Q.valuation_le_one_iff.2 haQ
  refine ⟨(-log (Q.valuation a)).toNat, ?_⟩
  rw [← exp_log h0, ← exp_zero, exp_le_exp] at h1
  rw [Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]

variable (Q₁ : CurvePlace k K₁) (Q₂ : CurvePlace k K₂)

/-- **Closedness of the local ring in its normalization.** Let `σ` be in the conductor (nonzero on
both components), and let every pair of regular elements be made `Ã`-integral by some `τ ∉ P`.
If elements of the fibre product `{(a, b) | a(Q₁) = b(Q₂)}` are reached by `R_P` modulo every
power of the maximal ideals, they are reached exactly. -/
theorem exists_eq_of_jets (Ã₁ : Subring K₁) (Ã₂ : Subring K₂) (P : Ideal R) [P.IsPrime]
    (hP₁ : ∀ r, r ∉ P → ρ₁ r ≠ 0) (hP₂ : ∀ r, r ∉ P → ρ₂ r ≠ 0)
    {σ : R} (hσ₁ : ρ₁ σ ≠ 0) (hσ₂ : ρ₂ σ ≠ 0) (hσQ₁ : ρ₁ σ ∈ Q₁.V) (hσQ₂ : ρ₂ σ ∈ Q₂.V)
    (hσ : ∀ α₁ ∈ Ã₁, ∀ α₂ ∈ Ã₂, ∃ r : R, ρ₁ r = ρ₁ σ * α₁ ∧ ρ₂ r = ρ₂ σ * α₂)
    (hτ : ∀ g₁ ∈ Q₁.V, ∀ g₂ ∈ Q₂.V, ∃ τ : R, τ ∉ P ∧ ρ₁ τ * g₁ ∈ Ã₁ ∧ ρ₂ τ * g₂ ∈ Ã₂)
    {a : K₁} {b : K₂}
    (hjet : ∀ M : ℕ, ∃ y s : R, s ∉ P ∧ Q₁.valuation (ρ₁ y / ρ₁ s - a) ≤ exp (-(M : ℤ)) ∧
      Q₂.valuation (ρ₂ y / ρ₂ s - b) ≤ exp (-(M : ℤ))) :
    ∃ y s : R, s ∉ P ∧ ρ₁ y = a * ρ₁ s ∧ ρ₂ y = b * ρ₂ s := by
  obtain ⟨n₁, hn₁⟩ := valuation_le_exp_of_ne_zero Q₁ hσ₁ hσQ₁
  obtain ⟨n₂, hn₂⟩ := valuation_le_exp_of_ne_zero (K₁ := K₂) Q₂ hσ₂ hσQ₂
  obtain ⟨y₀, s₀, hs₀, he₁, he₂⟩ := hjet (n₁ + n₂)
  set e₁ := ρ₁ y₀ / ρ₁ s₀ - a
  set e₂ := ρ₂ y₀ / ρ₂ s₀ - b
  have hg₁ : e₁ / ρ₁ σ ∈ Q₁.V := by
    refine Q₁.valuation_le_one_iff.1 ?_
    rw [map_div₀, hn₁, div_le_one₀ exp_pos]
    exact he₁.trans (by rw [exp_le_exp]; omega)
  have hg₂ : e₂ / ρ₂ σ ∈ Q₂.V := by
    refine Q₂.valuation_le_one_iff.1 ?_
    rw [map_div₀, hn₂, div_le_one₀ exp_pos]
    exact he₂.trans (by rw [exp_le_exp]; omega)
  obtain ⟨τ, hτP, hτ₁, hτ₂⟩ := hτ _ hg₁ _ hg₂
  obtain ⟨r, hr₁, hr₂⟩ := hσ _ hτ₁ _ hτ₂
  have hs₁ := hP₁ s₀ hs₀
  have hs₂ := hP₂ s₀ hs₀
  have ht₁ := hP₁ τ hτP
  have ht₂ := hP₂ τ hτP
  refine ⟨y₀ * τ - r * s₀, s₀ * τ, Ideal.IsPrime.mul_notMem ‹_› hs₀ hτP, ?_, ?_⟩
  · have h : ρ₁ σ * (ρ₁ τ * (e₁ / ρ₁ σ)) = ρ₁ τ * e₁ := by field_simp
    rw [map_sub, map_mul, map_mul, hr₁, map_mul, h]
    simp only [e₁]
    field_simp
    ring
  · have h : ρ₂ σ * (ρ₂ τ * (e₂ / ρ₂ σ)) = ρ₂ τ * e₂ := by field_simp
    rw [map_sub, map_mul, map_mul, hr₂, map_mul, h]
    simp only [e₂]
    field_simp
    ring

/-- **The ordinary double point.** If the local ring reaches the whole fibre product, then for
`u', v'` with `ρ₂ u' = 0`, `ρ₁ u'` a uniformizer at `Q₁`, `ρ₁ v' = 0`, `ρ₂ v'` a uniformizer at
`Q₂`, every `z` vanishing at the point satisfies `s z - a u' - b v' ∈ ker ρ₁ ∩ ker ρ₂` for some
`s ∉ P`. -/
theorem exists_sub_mem_ker (P : Ideal R) [P.IsPrime]
    (hfp : ∀ a ∈ Q₁.V, ∀ b ∈ Q₂.V, Q₁.res a = Q₂.res b →
      ∃ y s : R, s ∉ P ∧ ρ₁ y = a * ρ₁ s ∧ ρ₂ y = b * ρ₂ s)
    {u' v' : R} (hu₁ : Q₁.valuation (ρ₁ u') = exp (-1)) (hu₂ : ρ₂ u' = 0)
    (hv₁ : ρ₁ v' = 0) (hv₂ : Q₂.valuation (ρ₂ v') = exp (-1))
    {z : R} (hz₁ : Q₁.valuation (ρ₁ z) < 1) (hz₂ : Q₂.valuation (ρ₂ z) < 1) :
    ∃ a b s : R, s ∉ P ∧ ρ₁ (s * z - a * u' - b * v') = 0 ∧ ρ₂ (s * z - a * u' - b * v') = 0 := by
  have hu0 : ρ₁ u' ≠ 0 := fun h ↦ by rw [h, map_zero] at hu₁; exact exp_ne_zero hu₁.symm
  have hv0 : ρ₂ v' ≠ 0 := fun h ↦ by rw [h, map_zero] at hv₂; exact exp_ne_zero hv₂.symm
  -- the quotients
  have hα : ρ₁ z / ρ₁ u' ∈ Q₁.V := by
    refine Q₁.valuation_le_one_iff.1 ?_
    rw [map_div₀, hu₁, div_le_one₀ exp_pos]
    exact WithZero.le_exp_of_lt_exp_add_one (by simpa using hz₁)
  have hβ : ρ₂ z / ρ₂ v' ∈ Q₂.V := by
    refine Q₂.valuation_le_one_iff.1 ?_
    rw [map_div₀, hv₂, div_le_one₀ exp_pos]
    exact WithZero.le_exp_of_lt_exp_add_one (by simpa using hz₂)
  obtain ⟨y₁, s₁, hs₁, h₁₁, h₁₂⟩ := hfp _ hα (algebraMap k K₂ (Q₁.res (ρ₁ z / ρ₁ u')))
    (Q₂.algebraMap_mem _) (by rw [Q₂.res_algebraMap])
  obtain ⟨y₂, s₂, hs₂, h₂₁, h₂₂⟩ := hfp (algebraMap k K₁ (Q₂.res (ρ₂ z / ρ₂ v')))
    (Q₁.algebraMap_mem _) _ hβ (by rw [Q₁.res_algebraMap])
  refine ⟨y₁ * s₂, y₂ * s₁, s₁ * s₂, Ideal.IsPrime.mul_notMem ‹_› hs₁ hs₂, ?_, ?_⟩
  · simp only [map_sub, map_mul, hv₁, h₁₁]
    field_simp
    ring
  · simp only [map_sub, map_mul, hu₂, h₂₂]
    field_simp
    ring

end Local

end ConductorLocal

end SemistableReduction
