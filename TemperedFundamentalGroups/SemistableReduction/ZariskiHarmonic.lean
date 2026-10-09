/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization

/-!
# Positions on an annulus and the length inequality (W8′, H5, valuative core)

Blueprint §9.7. Let `s ∈ F` be the coordinate of a base edge (`s · (c/s) = ϖ ^ N`). At a node
point `P` of a model of `F` with node coordinates `u, v ∈ P`, `u v = ϖ ^ n`, at which
`s = ε ϖ ^ α u ^ d` with `ε` a unit of `P`, a vertex `W ⊇ P` (a valuation subring with
`W(ϖ) < 1` on which `u` or `v` is a unit) has `W(s) = W(ϖ) ^ p` with `p = α` (if `W(u) = 1`) or
`p = α + d n` (if `W(v) = 1`): the **position** of `W` on the base annulus
(`valuation_eq_pow_of_node`). Hence along a walk `W₀, P₁, W₁, …, P_k, W_k` whose consecutive
vertices are the two branches at `P_i`, the positions change by `d_i n_i`, and
`|p_k - p_0| ≤ ∑ d_i n_i` (`abs_sub_le_sum_of_steps`): crossing an edge of the base costs at
least its thickness (the length inequality (H2) of `ModelCode.IsHarmonicGeneral`), with equality
for monotone walks.
-/

namespace SemistableReduction

/-- **Telescoping**: if consecutive terms of `p` differ by `len i`, then `|p k - p 0| ≤ ∑ len i`. -/
theorem abs_sub_le_sum_of_steps {k : ℕ} (p : Fin (k + 1) → ℤ) (len : Fin k → ℕ)
    (h : ∀ i : Fin k, |p i.succ - p i.castSucc| = len i) :
    |p (Fin.last k) - p 0| ≤ ∑ i, (len i : ℤ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h' := ih (fun i ↦ p i.castSucc) (fun i ↦ len i.castSucc) (fun i ↦ h i.castSucc)
    rw [Fin.sum_univ_castSucc]
    calc |p (Fin.last (k + 1)) - p 0|
        = |(p (Fin.last k).succ - p (Fin.last k).castSucc) +
            (p (Fin.last k).castSucc - p 0)| := by
          congr 1
          simp only [Fin.succ_last]
          abel
      _ ≤ |p (Fin.last k).succ - p (Fin.last k).castSucc| +
            |p (Fin.last k).castSucc - p 0| := abs_add_le _ _
      _ ≤ (len (Fin.last k) : ℤ) + ∑ i : Fin k, (len i.castSucc : ℤ) := by
          rw [h (Fin.last k)]
          simp only [Fin.castSucc_zero] at h'
          gcongr
      _ = ∑ i : Fin k, (len i.castSucc : ℤ) + (len (Fin.last k) : ℤ) := add_comm _ _

variable {F : Type*} [Field F]

/-- Exponents of a value `< 1` are determined. -/
theorem pow_injective_of_lt_one {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {γ : Γ}
    (h0 : γ ≠ 0) (h1 : γ < 1) {a b : ℕ} (h : γ ^ a = γ ^ b) : a = b :=
  (pow_right_strictAnti₀ (zero_lt_iff.mpr h0) h1).injective h

/-- **Position of a branch at a node.** Let `u, v ∈ W` with `u v = ϖ ^ n` and
`s = ε ϖ ^ α u ^ d` with `W(ε) = 1`. If `W(u) = 1` then `W(s) = W(ϖ) ^ α`; if `W(v) = 1` then
`W(s) = W(ϖ) ^ (α + d n)`. -/
theorem valuation_eq_pow_of_node (W : ValuationSubring F) {u v s ε ϖ : F} {n α d : ℕ}
    (huv : u * v = ϖ ^ n) (hs : s = ε * ϖ ^ α * u ^ d) (hε : W.valuation ε = 1) :
    (W.valuation u = 1 → W.valuation s = W.valuation ϖ ^ α) ∧
    (W.valuation v = 1 → W.valuation s = W.valuation ϖ ^ (α + d * n)) := by
  refine ⟨fun hu ↦ ?_, fun hv ↦ ?_⟩
  · rw [hs, map_mul, map_mul, hε, map_pow, map_pow, hu, one_pow, one_mul, mul_one]
  · have hu : W.valuation u = W.valuation ϖ ^ n := by
      have := congrArg W.valuation huv
      rwa [map_mul, hv, mul_one, map_pow] at this
    rw [hs, map_mul, map_mul, hε, map_pow, map_pow, hu, one_mul, ← pow_mul, ← pow_add, mul_comm n d]

/-- **Node data at a point of a model** (the output of the W7 node lemma S9): the point `P`
contains node coordinates `u, v` with `u v = ϖ ^ n`, and its two branches are the vertices `W₁`
(on which `u` is a unit) and `W₂` (on which `v` is a unit). -/
structure IsBranchNode (ϖ : F) (P : Subring F) (u v : F) (n : ℕ)
    (W₁ W₂ : ValuationSubring F) : Prop where
  mul_eq : u * v = ϖ ^ n
  le₁ : P ≤ W₁.toSubring
  le₂ : P ≤ W₂.toSubring
  val₁ : W₁.valuation u = 1
  val₂ : W₂.valuation v = 1

/-- A unit of `P` has value `1` on every valuation subring containing `P`. -/
lemma valuation_eq_one_of_isUnit {P : Subring F} {W : ValuationSubring F} (hW : P ≤ W.toSubring)
    {ε : F} (hε : ε ∈ P) (hε' : ε⁻¹ ∈ P) (h0 : ε ≠ 0) : W.valuation ε = 1 :=
  (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨h0, hW hε, hW hε'⟩

/-- **Positions of the two branches of a node.** If `s = ε ϖ ^ α u ^ d` with `ε` a unit of `P`,
then `W₁(s) = W₁(ϖ) ^ α` and `W₂(s) = W₂(ϖ) ^ (α + d n)`. -/
theorem IsBranchNode.positions {ϖ : F} {P : Subring F} {u v : F} {n : ℕ}
    {W₁ W₂ : ValuationSubring F} (h : IsBranchNode ϖ P u v n W₁ W₂) {s ε : F} {α d : ℕ}
    (hs : s = ε * ϖ ^ α * u ^ d) (hε : ε ∈ P) (hε' : ε⁻¹ ∈ P) (h0 : ε ≠ 0) :
    W₁.valuation s = W₁.valuation ϖ ^ α ∧ W₂.valuation s = W₂.valuation ϖ ^ (α + d * n) :=
  ⟨(valuation_eq_pow_of_node W₁ h.mul_eq hs (valuation_eq_one_of_isUnit h.le₁ hε hε' h0)).1
      h.val₁,
    (valuation_eq_pow_of_node W₂ h.mul_eq hs (valuation_eq_one_of_isUnit h.le₂ hε hε' h0)).2
      h.val₂⟩

/-- **The length inequality along a walk** (H2, valuative form). Let `W₀, …, W_k` be valuation
subrings and `P₁, …, P_k` node points such that `P_i` joins `W_{i-1}` and `W_i` (in either
order) as its two branches, and `s = εᵢ ϖ ^ αᵢ uᵢ ^ dᵢ` at `P_i` (`εᵢ` a unit of `P_i`).
If the positions `pᵢ` of the `Wᵢ` (`Wᵢ(s) = Wᵢ(ϖ) ^ pᵢ`, `Wᵢ(ϖ) < 1`) are defined, then
`|p_k - p_0| ≤ ∑ dᵢ nᵢ`. -/
theorem abs_sub_le_sum_of_branchNodes {ϖ s : F} {k : ℕ} (W : Fin (k + 1) → ValuationSubring F)
    (hϖ : ∀ i, (W i).valuation ϖ < 1) (hϖ0 : ϖ ≠ 0) (p : Fin (k + 1) → ℕ)
    (hp : ∀ i, (W i).valuation s = (W i).valuation ϖ ^ p i)
    (P : Fin k → Subring F) (u v ε : Fin k → F) (n α d : Fin k → ℕ)
    (hnode : ∀ i, IsBranchNode ϖ (P i) (u i) (v i) (n i) (W i.castSucc) (W i.succ) ∨
      IsBranchNode ϖ (P i) (u i) (v i) (n i) (W i.succ) (W i.castSucc))
    (hs : ∀ i, s = ε i * ϖ ^ α i * u i ^ d i) (hε : ∀ i, ε i ∈ P i) (hε' : ∀ i, (ε i)⁻¹ ∈ P i)
    (hε0 : ∀ i, ε i ≠ 0) :
    |(p (Fin.last k) : ℤ) - p 0| ≤ ∑ i, ((d i * n i : ℕ) : ℤ) := by
  refine abs_sub_le_sum_of_steps (fun i ↦ (p i : ℤ)) (fun i ↦ d i * n i) fun i ↦ ?_
  have hW0 : ∀ j, (W j).valuation ϖ ≠ 0 := fun j ↦ by simpa using hϖ0
  rcases hnode i with h | h
  · obtain ⟨h₁, h₂⟩ := h.positions (hs i) (hε i) (hε' i) (hε0 i)
    have e₁ := pow_injective_of_lt_one (hW0 _) (hϖ _) ((hp i.castSucc).symm.trans h₁)
    have e₂ := pow_injective_of_lt_one (hW0 _) (hϖ _) ((hp i.succ).symm.trans h₂)
    simp only [e₁, e₂]
    push_cast
    rw [show ((α i : ℤ) + d i * n i - α i) = d i * n i by ring]
    exact abs_of_nonneg (by positivity)
  · obtain ⟨h₁, h₂⟩ := h.positions (hs i) (hε i) (hε' i) (hε0 i)
    have e₁ := pow_injective_of_lt_one (hW0 _) (hϖ _) ((hp i.succ).symm.trans h₁)
    have e₂ := pow_injective_of_lt_one (hW0 _) (hϖ _) ((hp i.castSucc).symm.trans h₂)
    simp only [e₁, e₂]
    push_cast
    rw [show ((α i : ℤ) - (α i + d i * n i)) = -(d i * n i) by ring, abs_neg]
    exact abs_of_nonneg (by positivity)

end SemistableReduction
