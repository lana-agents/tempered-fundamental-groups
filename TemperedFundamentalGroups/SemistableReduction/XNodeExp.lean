/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XRadiusMatch

/-!
# Exponents of a node coordinate of `y'` along a node over it (Blueprint §9.7, X1/X2)

`node_exponents`: let `z` be an unfolded node (coordinates `u v = ϖ₁ ^ n`, branches `W₁` where `u`
is a unit and `W₂`) whose germs contain the germs of an unfolded node `y'` (coordinate `u'`,
`u' v' = ϖ₂ ^ n'`). Then `W₁(u') = W₁(ϖ₁) ^ q₁`, `W₂(u') = W₂(ϖ₁) ^ q₂` with `q₁ ≤ q₂`, and if
`q₁ < q₂` the x-length data satisfy `e n = e' (q₂ - q₁)` (`node_slope`): the x-length of `z` is
`e' / e₁` times the increase of the exponent of `u'`.
-/

open Polynomial

namespace SemistableReduction

variable {K K₁ K₂ L₁ L₂ : Type*} [Field K] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra K K₁] [Algebra K K₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
  [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
  [IsScalarTower K L₂ L₁]
  {O₁ : ValuationSubring K₁} {ϖ₁ : O₁} {O₂ : ValuationSubring K₂} {ϖ₂ : O₂}

/-- **The two uniformizers in `L₁`**: `ϖ₂ ^ e₂ = ζ ϖ₁ ^ e₁` with `ζ` a unit of `P`. -/
lemma exists_zeta {ϖ : K} {η₁ : O₁ˣ} {η₂ : O₂ˣ} {e₁ e₂ : ℕ}
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂) {P : Subring L₁}
    (hP₁ : ∀ o : O₁, algebraMap K₁ L₁ (o : K₁) ∈ P)
    (hP₂ : ∀ o : O₂, algebraMap L₂ L₁ (algebraMap K₂ L₂ (o : K₂)) ∈ P) :
    ∃ ζ ∈ P, ζ⁻¹ ∈ P ∧ ζ ≠ 0 ∧ algebraMap L₂ L₁ (algebraMap K₂ L₂ (ϖ₂ : K₂)) ^ e₂ =
      ζ * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ e₁ := by
  set ι₂ : K₂ →+* L₁ := (algebraMap L₂ L₁).comp (algebraMap K₂ L₂)
  have hη₂0 : ι₂ ((η₂ : O₂) : K₂) ≠ 0 := by
    have : ((η₂ : O₂) : K₂) ≠ 0 := fun h ↦ η₂.ne_zero (Subtype.ext h)
    simp [ι₂, this]
  have hη₁0 : algebraMap K₁ L₁ ((η₁ : O₁) : K₁) ≠ 0 := by
    have : ((η₁ : O₁) : K₁) ≠ 0 := fun h ↦ η₁.ne_zero (Subtype.ext h)
    simp [this]
  have hη₂inv : (ι₂ ((η₂ : O₂) : K₂))⁻¹ = ι₂ ((η₂⁻¹ : O₂ˣ) : K₂) := by
    rw [← map_inv₀]; congr 1
    exact (eq_inv_of_mul_eq_one_right (congrArg Subtype.val η₂.mul_inv)).symm
  have hη₁inv : (algebraMap K₁ L₁ ((η₁ : O₁) : K₁))⁻¹ = algebraMap K₁ L₁ ((η₁⁻¹ : O₁ˣ) : K₁) := by
    rw [← map_inv₀]; congr 1
    exact (eq_inv_of_mul_eq_one_right (congrArg Subtype.val η₁.mul_inv)).symm
  refine ⟨algebraMap K₁ L₁ ((η₁ : O₁) : K₁) * (ι₂ ((η₂ : O₂) : K₂))⁻¹,
    mul_mem (hP₁ _) (by rw [hη₂inv]; exact hP₂ _), ?_, mul_ne_zero hη₁0 (inv_ne_zero hη₂0), ?_⟩
  · rw [mul_inv, inv_inv, hη₁inv]
    exact mul_mem (hP₁ _) (hP₂ _)
  · have hbase : ι₂ (algebraMap K K₂ ϖ) = algebraMap K₁ L₁ (algebraMap K K₁ ϖ) := by
      change algebraMap L₂ L₁ (algebraMap K₂ L₂ (algebraMap K K₂ ϖ)) = _
      rw [← IsScalarTower.algebraMap_apply K K₂ L₂, ← IsScalarTower.algebraMap_apply K L₂ L₁,
        IsScalarTower.algebraMap_apply K K₁ L₁]
    rw [hϖK₂, hϖK₁, map_mul, map_mul, map_pow, map_pow] at hbase
    change ι₂ (ϖ₂ : K₂) ^ e₂ = _
    field_simp
    rw [← hbase]
    ring

variable [Algebra.IsAlgebraic K K₁] [Algebra.IsAlgebraic K K₂] [IsDiscreteValuationRing O₁]
  [IsDiscreteValuationRing O₂]

/-- **Exponents of `u'` along a node over `y'`** (X1/X2). -/
theorem node_exponents (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂) {ϖ : K} {η₁ : O₁ˣ}
    {η₂ : O₂ˣ} {e₁ e₂ : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂)
    {P : Subring L₁} {u v x₁ ε : L₁} {n : ℕ} {a β : K₁} {e α : ℕ}
    {W₁ W₂ : ValuationSubring L₁} (H : UnfoldedNodeGerm O₁ ϖ₁ P u v n x₁ a β e α ε W₁ W₂)
    (HB : NodeBranches O₁ ϖ₁ P (algebraMap O₁ L₁) u v n W₁ W₂)
    (hGs : NodeGerm O₁ ϖ₁ P v u n)
    (hint : ∀ s : ℚ, 0 < s → s < n → ∃ U : ValuationSubring L₁,
      IsMonomialPt O₁ (P : Set L₁) (algebraMap K₁ L₁ (ϖ₁ : K₁)) u s U)
    (hdiv : ∀ t ∈ P, ∀ M : ℕ, (∃ r ∈ P, t * r = algebraMap K₁ L₁ (ϖ₁ : K₁) ^ M) →
      ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ α * u ^ e ∨
        t = ε * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ α * v ^ e)
    {Q : Subring L₂} {u' v' x₂ ε' : L₂} {n' : ℕ} {a' β' : K₂} {e' α' : ℕ}
    {W₁' W₂' : ValuationSubring L₂}
    (H' : UnfoldedNodeGerm O₂ ϖ₂ Q u' v' n' x₂ a' β' e' α' ε' W₁' W₂')
    (hx : algebraMap L₂ L₁ x₂ = x₁) (hQP : ∀ q ∈ Q, algebraMap L₂ L₁ q ∈ P) :
    ∃ q₁ q₂ : ℕ, q₁ ≤ q₂ ∧
      W₁.valuation (algebraMap L₂ L₁ u') = W₁.valuation (algebraMap K₁ L₁ (ϖ₁ : K₁)) ^ q₁ ∧
      W₂.valuation (algebraMap L₂ L₁ u') = W₂.valuation (algebraMap K₁ L₁ (ϖ₁ : K₁)) ^ q₂ ∧
      (q₁ < q₂ → ((e * n : ℕ) : ℚ) = e' * ((q₂ : ℚ) - q₁)) := by
  set ι := algebraMap L₂ L₁
  set ϖL := algebraMap K₁ L₁ (ϖ₁ : K₁)
  obtain ⟨ζ, hζ, hζ', hζ0, hζϖ⟩ := exists_zeta hϖK₁ hϖK₂ H.germ.algebraMap_mem
    (fun o ↦ hQP _ (H'.germ.algebraMap_mem o))
  -- `u'` divides a power of `ϖ₁`
  have hu'P : ι u' ∈ P := hQP _ H'.germ.u_mem
  have hdivides : ∃ r ∈ P, ι u' * r = ϖL ^ (e₁ * n') := by
    refine ⟨ι v' * ι (algebraMap K₂ L₂ (ϖ₂ : K₂)) ^ (n' * (e₂ - 1)) * ζ⁻¹ ^ n',
      mul_mem (mul_mem (hQP _ H'.germ.v_mem) (pow_mem (hQP _ (H'.germ.algebraMap_mem _)) _))
        (pow_mem hζ' _), ?_⟩
    have h1 : ι u' * ι v' = ι (algebraMap K₂ L₂ (ϖ₂ : K₂)) ^ n' := by
      rw [← map_mul, H'.germ.mul_eq, map_pow]
    calc ι u' * (ι v' * ι (algebraMap K₂ L₂ (ϖ₂ : K₂)) ^ (n' * (e₂ - 1)) * ζ⁻¹ ^ n')
        = (ι u' * ι v') * ι (algebraMap K₂ L₂ (ϖ₂ : K₂)) ^ (n' * (e₂ - 1)) * ζ⁻¹ ^ n' := by ring
      _ = (ι (algebraMap K₂ L₂ (ϖ₂ : K₂)) ^ e₂) ^ n' * ζ⁻¹ ^ n' := by
          rw [h1, ← pow_add, ← pow_mul, mul_comm e₂ n']
          congr 2
          rw [Nat.mul_sub, mul_one, Nat.add_sub_cancel' (Nat.le_mul_of_pos_right n' he₂)]
      _ = ϖL ^ (e₁ * n') := by
          rw [hζϖ, mul_pow, ← pow_mul, mul_assoc, mul_left_comm, ← mul_pow,
            mul_inv_cancel₀ hζ0, one_pow, mul_one]
  obtain ⟨ε'', hε, hεi, r, p, hform⟩ := hdiv _ hu'P _ hdivides
  have hu'0 : ι u' ≠ 0 := by
    have : u' ≠ 0 := fun h ↦ by
      have := H'.germ.mul_eq; rw [h, zero_mul] at this
      have h2 : (ϖ₂ : K₂) ≠ 0 := fun h ↦ hϖ₂.ne_zero (Subtype.ext h)
      exact pow_ne_zero _ (by simpa using h2) this.symm
    simpa using this
  have hε0 : ε'' ≠ 0 := by rintro rfl; rcases hform with h | h <;> simp [h] at hu'0
  have hP₁ := HB.mono₁.1
  have hP₂ := HB.mono₂.1
  have hW₁ε : W₁.valuation ε'' = 1 :=
    (valuation_eq_one_iff_mem_and_inv_mem W₁).2 ⟨hε0, hP₁ hε, hP₁ hεi⟩
  have hW₂ε : W₂.valuation ε'' = 1 :=
    (valuation_eq_one_iff_mem_and_inv_mem W₂).2 ⟨hε0, hP₂ hε, hP₂ hεi⟩
  have hW₁u : W₁.valuation u = 1 := NodeBranches.isLogValue_zero_iff.1 HB.mono₁.2.2.1
  have hW₂v : W₂.valuation v = 1 := NodeBranches.isLogValue_zero_iff.1 HB.swap.mono₁.2.2.1
  have hW₂u : W₂.valuation u = W₂.valuation ϖL ^ n :=
    (NodeBranches.isLogValue_nat_iff n).1 HB.mono₂.2.2.1
  have hW₁v : W₁.valuation v = W₁.valuation ϖL ^ n :=
    (NodeBranches.isLogValue_nat_iff n).1 HB.swap.mono₂.2.2.1
  have hslope := fun hp ↦ node_slope hϖ₁ hϖ₂ he₁ he₂ hϖK₁ hϖK₂ H HB hGs hint H' hx hQP hε hεi hε0
    (p := p) (r := r) hp
  rcases hform with h | h
  · refine ⟨r, r + p * n, by omega, ?_, ?_, fun hlt ↦ ?_⟩
    · rw [h, map_mul, map_mul, map_pow, map_pow, hW₁ε, hW₁u, one_pow, one_mul, mul_one]
    · rw [h, map_mul, map_mul, map_pow, map_pow, hW₂ε, hW₂u, one_mul, ← pow_mul, ← pow_add,
        mul_comm n p]
    · have hp : 1 ≤ p := by
        rcases Nat.eq_zero_or_pos p with h0 | h0
        · subst h0; simp at hlt
        · exact h0
      have := (hslope hp).1 (by rw [h]; ring)
      push_cast
      rw [this]
      ring
  · rcases Nat.eq_zero_or_pos p with h0 | hp
    · subst h0
      refine ⟨r, r, le_rfl, ?_, ?_, fun hlt ↦ absurd hlt (lt_irrefl _)⟩
      · rw [h, pow_zero, mul_one, map_mul, map_pow, hW₁ε, one_mul]
      · rw [h, pow_zero, mul_one, map_mul, map_pow, hW₂ε, one_mul]
    · exact ((hslope hp).2 (by rw [h]; ring)).elim

end SemistableReduction
