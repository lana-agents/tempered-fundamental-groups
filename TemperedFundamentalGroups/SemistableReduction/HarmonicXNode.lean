/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.HarmonicX0
import TemperedFundamentalGroups.SemistableReduction.XNodeExp
import TemperedFundamentalGroups.SemistableReduction.XHarmonicGlue
import TemperedFundamentalGroups.SemistableReduction.CentreMap

/-!
# Nodes of `c` over a node `y'` of `c'` (Blueprint §9.7, X1/X2)

`node_rel`: let `ψ : c ⟶ c'` be a map of unfolded W-models and `y'` an unfolded node of `c'`
with coordinate `u'`. For every node `z` of `c` over `y'`, with x-length `l`, there are the two
components `A ≠ B` through `z` with exponents `W_A(u') = W_A(ϖ₁) ^ q_A`, `W_B(u') = W_B(ϖ₁) ^ q_B`,
`q_A ≤ q_B`, and `l e₁ = e' (q_B - q_A)` as soon as `q_A < q_B` (`node_exponents`); `l > 0`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode _root_.SemistableReduction

variable {K K₁ K₂ L₁ L₂ : Type u} [Field K] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra K K₁] [Algebra K K₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
  [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
  [IsScalarTower K L₂ L₁] [Algebra.IsAlgebraic K K₁] [Algebra.IsAlgebraic K K₂]
  {O₁ : ValuationSubring K₁} {O₂ : ValuationSubring K₂} [IsDiscreteValuationRing O₁]
  [IsDiscreteValuationRing O₂] [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁]

/-- **A node of `c` over the node `y'`** (X1/X2). -/
theorem node_rel {ϖ₁ : O₁} {ϖ₂ : O₂} (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂) {ϖ : K}
    {η₁ : O₁ˣ} {η₂ : O₂ˣ} {e₁ e₂ : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂) {x : L₂}
    {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}
    {ψ : c.scheme ⟶ c'.scheme} {j : Spec (CommRingCat.of L₁) ⟶ c.scheme}
    {j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme} (hU₁ : IsUnfolded O₁ (algebraMap L₂ L₁ x) c j)
    (hsplit₁ : HasSplitNodes ϖ₁ c) (hloops₁ : NoLoops c)
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j')
    {Q : Subring L₂} {u' v' ε' : L₂} {n' : ℕ} {a' β' : K₂} {e' α' : ℕ}
    {W₁' W₂' : ValuationSubring L₂}
    (H' : UnfoldedNodeGerm O₂ ϖ₂ Q u' v' n' x a' β' e' α' ε' W₁' W₂') {y' : c'.scheme}
    (hQg : (Q : Set L₂) = germs c' j' y') {z : c.scheme} (hz : IsNodePt c z) (hψz : ψ z = y')
    {l : ℚ}
    (hl : IsXLength (algebraMap K₁ L₁ (algebraMap K K₁ ϖ)) O₁ ϖ₁ c j (algebraMap L₂ L₁ x) z l) :
    ∃ (A B : Set c.scheme) (hA : A ∈ components c) (hB : B ∈ components c),
      z ∈ A ∧ z ∈ B ∧ A ≠ B ∧ ∃ qA qB : ℕ,
        (Wc hU₁.isWModel hA).valuation (algebraMap L₂ L₁ u') =
          (Wc hU₁.isWModel hA).valuation (algebraMap O₁ L₁ ϖ₁) ^ qA ∧
        (Wc hU₁.isWModel hB).valuation (algebraMap L₂ L₁ u') =
          (Wc hU₁.isWModel hB).valuation (algebraMap O₁ L₁ ϖ₁) ^ qB ∧
        qA ≤ qB ∧ (qA < qB → l * e₁ = e' * ((qB : ℚ) - qA)) ∧ 0 < l := by
  obtain ⟨P, u, v, n, a, β, e, α, ε, v₁, v₂, hv₁, hv₂, H, HB, hPg, hz₁, hz₂, hGs, hint, hdiv,
    hsec⟩ := exists_unfoldedNodeGerm hU₁ hϖ₁ hsplit₁ hloops₁ hz
  have hle := (isXLength_iff_of_unfolded hU₁.isWModel hϖ₁ he₁ hϖK₁ H HB hPg hdiv hsec l).1 hl
  have hϖL : algebraMap K₁ L₁ (ϖ₁ : K₁) = algebraMap O₁ L₁ ϖ₁ := algebraMap_O_K ϖ₁
  have hQP : ∀ q ∈ Q, algebraMap L₂ L₁ q ∈ P := fun q hq ↦ by
    rw [← SetLike.mem_coe, hPg]
    exact germs_map ψ j j' hj z (by rw [hψz, ← hQg]; exact hq)
  have hdiv' : ∀ t ∈ P, ∀ M : ℕ, (∃ r ∈ P, t * r = algebraMap K₁ L₁ (ϖ₁ : K₁) ^ M) →
      ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ α * u ^ e ∨
        t = ε * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ α * v ^ e := by
    rw [hϖL]; exact hdiv
  obtain ⟨q₁, q₂, hq, h₁, h₂, hlt⟩ := node_exponents hϖ₁ hϖ₂ he₁ he₂ hϖK₁ hϖK₂ H HB hGs hint
    hdiv' H' rfl hQP
  rw [hϖL] at h₁ h₂
  have hne : v₁ ≠ v₂ := by
    rintro rfl
    have hu1 := NodeBranches.isLogValue_zero_iff.1 HB.mono₁.2.2.1
    have hun := (NodeBranches.isLogValue_nat_iff n).1 HB.mono₂.2.2.1
    rw [hu1] at hun
    have hϖW := HB.mono₁.2.1
    have : (Wc hU₁.isWModel hv₁).valuation (algebraMap K₁ L₁ (ϖ₁ : K₁)) ^ n < 1 :=
      pow_lt_one₀ zero_le hϖW (by have := H.one_le_n; omega)
    rw [← hun] at this
    exact lt_irrefl _ this
  have he₁0 : (e₁ : ℚ) ≠ 0 := by exact_mod_cast he₁.ne'
  refine ⟨v₁, v₂, hv₁, hv₂, hz₁, hz₂, hne, q₁, q₂, h₁, h₂, hq, fun hqq ↦ ?_, ?_⟩
  · rw [hle, ← hlt hqq]
    push_cast
    field_simp
  · rw [hle]
    have : (1 : ℚ) ≤ e := by exact_mod_cast H.one_le_e
    have : (1 : ℚ) ≤ n := by exact_mod_cast H.one_le_n
    positivity

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
