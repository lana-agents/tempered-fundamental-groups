/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.HarmonicXEnd
import TemperedFundamentalGroups.SemistableReduction.CrossingWalk

/-!
# Exponents along a crossing walk (Blueprint §9.7, X1/X2)

`walk_exponents`: along a walk of `c` crossing the node `y'` of `c'` (coordinate `u'`,
`u' v' = ϖ₂ ^ n'`) from a component over `w₁'` to one over `w₂'`, the exponents `E i` of `u'`
at the components satisfy `e' |E (i+1) - E i| ≤ l i e₁` for the x-lengths `l i` of the nodes,
with equality when `E (i+1) ≠ E i` (`node_rel`), and `|E k - E 0| e₂ = e₁ n'` (`end_exponent`).
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
  [IsDiscreteValuationRing O₂] [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂]
  [IsScalarTower O₂ K₂ L₂]

/-- The two branches of a node are different. -/
lemma _root_.SemistableReduction.NodeBranches.ne {K L : Type*} [Field K] [Field L]
    [Algebra K L] {O : ValuationSubring K}
    {ϖK : O} {P : Subring L} {ι : O →+* L} {u v : L} {n : ℕ} {W₁ W₂ : ValuationSubring L}
    (H : NodeBranches O ϖK P ι u v n W₁ W₂) : W₁ ≠ W₂ := by
  rintro rfl
  have hu1 := NodeBranches.isLogValue_zero_iff.1 H.mono₁.2.2.1
  have hun := (NodeBranches.isLogValue_nat_iff n).1 H.mono₂.2.2.1
  rw [hu1] at hun
  have : W₁.valuation (algebraMap K L ϖK) ^ n < 1 :=
    pow_lt_one₀ zero_le H.mono₁.2.1 (by have := H.core.one_le; omega)
  rw [← hun] at this
  exact lt_irrefl _ this

/-- **Exponents along a crossing walk.** -/
theorem walk_exponents {ϖ₁ : O₁} {ϖ₂ : O₂} (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂)
    {ϖ : K} {η₁ : O₁ˣ} {η₂ : O₂ˣ} {e₁ e₂ : ℕ} (he₁ : 0 < e₁) (he₂ : 0 < e₂)
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂) {x : L₂}
    {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}
    {ψ : c.scheme ⟶ c'.scheme} {j : Spec (CommRingCat.of L₁) ⟶ c.scheme}
    {j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme} (hU₁ : IsUnfolded O₁ (algebraMap L₂ L₁ x) c j)
    (hU₂ : IsUnfolded O₂ x c' j') (hsplit₁ : HasSplitNodes ϖ₁ c) (hloops₁ : NoLoops c)
    (hsplit₂ : HasSplitNodes ϖ₂ c') (hloops₂ : NoLoops c')
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j')
    {Q : Subring L₂} {u' v' ε' : L₂} {n' : ℕ} {a' β' : K₂} {e' α' : ℕ}
    {v₁' v₂' : Set c'.scheme} (hv₁' : v₁' ∈ components c') (hv₂' : v₂' ∈ components c')
    (H' : UnfoldedNodeGerm O₂ ϖ₂ Q u' v' n' x a' β' e' α' ε' (Wc hU₂.isWModel hv₁')
      (Wc hU₂.isWModel hv₂'))
    (HB' : NodeBranches O₂ ϖ₂ Q (algebraMap O₂ L₂) u' v' n' (Wc hU₂.isWModel hv₁')
      (Wc hU₂.isWModel hv₂'))
    {y' : c'.scheme} (hy' : IsNodePt c' y') (hQg : (Q : Set L₂) = germs c' j' y')
    (hy₁' : y' ∈ v₁') (hy₂' : y' ∈ v₂') {w₁' w₂' : Set c'.scheme} (hw₁ : w₁' ∈ components c')
    (hw₂ : w₂' ∈ components c') (hne : w₁' ≠ w₂') (hyw₁ : y' ∈ w₁') (hyw₂ : y' ∈ w₂')
    (w : Walk c) (hcross : w.Crosses ψ y') (hψ0 : ψ '' w.v 0 = w₁')
    (hψk : ψ '' w.v (Fin.last w.k) = w₂') (l : Fin w.k → ℚ)
    (hl : ∀ i, IsXLength (algebraMap K₁ L₁ (algebraMap K K₁ ϖ)) O₁ ϖ₁ c j (algebraMap L₂ L₁ x)
      (w.x i) (l i)) :
    ∃ E : Fin (w.k + 1) → ℕ,
      (∀ i, (Wc hU₁.isWModel (w.mem_components i)).valuation (algebraMap L₂ L₁ u') =
        (Wc hU₁.isWModel (w.mem_components i)).valuation (algebraMap O₁ L₁ ϖ₁) ^ E i) ∧
      (∀ i : Fin w.k, e' * |(E i.succ : ℚ) - E i.castSucc| ≤ l i * e₁ ∧
        (E i.castSucc ≠ E i.succ → l i * e₁ = e' * |(E i.succ : ℚ) - E i.castSucc|)) ∧
      |(E (Fin.last w.k) : ℚ) - E 0| * e₂ = e₁ * n' := by
  set hW := hU₁.isWModel
  have hWϖ : ∀ {v} (hv : v ∈ components c), (Wc hW hv).valuation (algebraMap O₁ L₁ ϖ₁) < 1 :=
    fun hv ↦ valuation_ϖ_lt_one hW hϖ₁ (hv.2.1 (gp_mem hv)) (Wc_spec hW hv)
  have hW0 : ∀ {v} (hv : v ∈ components c), (Wc hW hv).valuation (algebraMap O₁ L₁ ϖ₁) ≠ 0 :=
    fun hv ↦ by
      rw [← algebraMap_O_K]; simpa using fun h ↦ hϖ₁.ne_zero (Subtype.ext h)
  -- the edges
  have hedge : ∀ i : Fin w.k, ∃ a b : ℕ,
      (Wc hW (w.mem_components i.castSucc)).valuation (algebraMap L₂ L₁ u') =
        (Wc hW (w.mem_components i.castSucc)).valuation (algebraMap O₁ L₁ ϖ₁) ^ a ∧
      (Wc hW (w.mem_components i.succ)).valuation (algebraMap L₂ L₁ u') =
        (Wc hW (w.mem_components i.succ)).valuation (algebraMap O₁ L₁ ϖ₁) ^ b ∧
      e' * |(b : ℚ) - a| ≤ l i * e₁ ∧ (a ≠ b → l i * e₁ = e' * |(b : ℚ) - a|) := by
    intro i
    obtain ⟨hz, hz₁, hz₂, hd⟩ := w.joins i
    obtain ⟨A, B, hA, hB, hzA, hzB, hAB, qA, qB, hqA, hqB, hq, hlt, hpos⟩ :=
      node_rel hϖ₁ hϖ₂ he₁ he₂ hϖK₁ hϖK₂ hU₁ hsplit₁ hloops₁ hj H' hQg hz (hcross.2.2.2.2.2 i)
        (hl i)
    have hc₁ := w.mem_components i.castSucc
    have hc₂ := w.mem_components i.succ
    have hdist : w.v i.castSucc ≠ w.v i.succ := by
      rcases hd with h | h
      · exact h
      · exact absurd ((h A hA hzA).trans (h B hB hzB).symm) hAB
    have t₁ := two_components hW hϖ₁ hsplit₁ hloops₁ hz hc₁ hA hB hz₁ hzA hzB
    have t₂ := two_components hW hϖ₁ hsplit₁ hloops₁ hz hc₂ hA hB hz₂ hzA hzB
    have key : ∀ a b : ℕ, a ≤ b → (a < b → l i * e₁ = e' * ((b : ℚ) - a)) →
        e' * |(b : ℚ) - a| ≤ l i * e₁ ∧ (a ≠ b → l i * e₁ = e' * |(b : ℚ) - a|) := by
      intro a b hab h
      have habq : (a : ℚ) ≤ b := by exact_mod_cast hab
      rw [abs_of_nonneg (by linarith)]
      rcases hab.lt_or_eq with h' | h'
      · exact ⟨(h h').ge, fun _ ↦ h h'⟩
      · subst h'
        refine ⟨by rw [sub_self, mul_zero]; positivity, fun h ↦ absurd rfl h⟩
    have key' : ∀ a b : ℕ, a ≤ b → (a < b → l i * e₁ = e' * ((b : ℚ) - a)) →
        e' * |(a : ℚ) - b| ≤ l i * e₁ ∧ (b ≠ a → l i * e₁ = e' * |(a : ℚ) - b|) := by
      intro a b hab h
      rw [abs_sub_comm]
      exact ⟨(key a b hab h).1, fun hne ↦ (key a b hab h).2 (Ne.symm hne)⟩
    rcases t₁ with h₁ | h₁ | h₁ <;> rcases t₂ with h₂ | h₂ | h₂
    · exact absurd (h₁.trans h₂.symm) hdist
    · refine ⟨qA, qB, ?_, ?_, key qA qB hq hlt⟩
      · rw [Wc_congr hW hc₁ hA h₁]; exact hqA
      · rw [Wc_congr hW hc₂ hB h₂]; exact hqB
    · exact absurd h₂ hAB
    · refine ⟨qB, qA, ?_, ?_, key' qA qB hq hlt⟩
      · rw [Wc_congr hW hc₁ hB h₁]; exact hqB
      · rw [Wc_congr hW hc₂ hA h₂]; exact hqA
    · exact absurd (h₁.trans h₂.symm) hdist
    · exact absurd h₂ hAB
    · exact absurd h₁ hAB
    · exact absurd h₁ hAB
    · exact absurd h₁ hAB
  -- the exponents at the components
  have hk := hcross.1
  have hEx : ∀ i : Fin (w.k + 1), ∃ q : ℕ,
      (Wc hW (w.mem_components i)).valuation (algebraMap L₂ L₁ u') =
        (Wc hW (w.mem_components i)).valuation (algebraMap O₁ L₁ ϖ₁) ^ q := by
    intro i
    by_cases hi : (i : ℕ) < w.k
    · obtain ⟨a, -, ha, -⟩ := hedge ⟨i, hi⟩
      have e : (⟨i, hi⟩ : Fin w.k).castSucc = i := Fin.ext rfl
      rw [e] at ha
      exact ⟨a, ha⟩
    · obtain ⟨-, b, -, hb, -⟩ := hedge ⟨w.k - 1, by omega⟩
      have e : (⟨w.k - 1, by omega⟩ : Fin w.k).succ = i := Fin.ext (by simp; omega)
      rw [e] at hb
      exact ⟨b, hb⟩
  choose E hE using hEx
  have huniq : ∀ (i : Fin (w.k + 1)) (q : ℕ),
      (Wc hW (w.mem_components i)).valuation (algebraMap L₂ L₁ u') =
        (Wc hW (w.mem_components i)).valuation (algebraMap O₁ L₁ ϖ₁) ^ q → q = E i :=
    fun i q h ↦ pow_inj (hW0 _) (hWϖ _) (h.symm.trans (hE i))
  refine ⟨E, hE, fun i ↦ ?_, ?_⟩
  · obtain ⟨a, b, ha, hb, h⟩ := hedge i
    rw [huniq _ _ ha, huniq _ _ hb] at h
    exact h
  · -- the ends
    have hW' := hU₂.isWModel
    have hv₁₂ : v₁' ≠ v₂' := fun h ↦ HB'.ne (Wc_congr hW' hv₁' hv₂' h)
    have hends : ∀ (i : Fin (w.k + 1)) (w' : Set c'.scheme) (hw' : w' ∈ components c'),
        y' ∈ w' → ψ '' w.v i = w' → (w' = v₁' ∧ E i = 0) ∨ (w' = v₂' ∧ E i * e₂ = e₁ * n') := by
      intro i w' hw' hyw hψi
      have he := end_exponent hϖ₁ hϖ₂ hϖK₁ hϖK₂ hW hW' hj HB' (w.mem_components i) hw' hψi (hE i)
      rcases two_components hW' hϖ₂ hsplit₂ hloops₂ hy' hw' hv₁' hv₂' hyw hy₁' hy₂' with
        h | h | h
      · exact .inl ⟨h, he.1 (Wc_congr hW' hw' hv₁' h)⟩
      · exact .inr ⟨h, he.2 (Wc_congr hW' hw' hv₂' h)⟩
      · exact absurd h hv₁₂
    have he₂0 : (e₂ : ℚ) ≠ 0 := by exact_mod_cast he₂.ne'
    rcases hends 0 w₁' hw₁ hyw₁ hψ0 with ⟨h₁, h₁'⟩ | ⟨h₁, h₁'⟩ <;>
      rcases hends (Fin.last w.k) w₂' hw₂ hyw₂ hψk with ⟨h₂, h₂'⟩ | ⟨h₂, h₂'⟩
    · exact absurd (h₁.trans h₂.symm) hne
    · have : (E (Fin.last w.k) : ℚ) * e₂ = e₁ * n' := by exact_mod_cast h₂'
      rw [h₁', Nat.cast_zero, sub_zero, abs_of_nonneg (by positivity), this]
    · have : (E 0 : ℚ) * e₂ = e₁ * n' := by exact_mod_cast h₁'
      rw [h₂', Nat.cast_zero, zero_sub, abs_neg, abs_of_nonneg (by positivity), this]
    · exact absurd (h₁.trans h₂.symm) hne

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
