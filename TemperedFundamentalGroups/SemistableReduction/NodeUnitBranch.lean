/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The branch on which a node coordinate is a unit is unique (Blueprint §10.3.8, CrossingX1, CX3)

Let `P ⊆ L` be a noetherian local subring with `P = O + ϖ P + u P + v P` (the germs of a node with
coordinates `u, v`; `O` a local ring with `𝔪_O = ϖ O`), and `u ∈ 𝔪_P`. Two valuation subrings
`W₁, W₂ ⊇ P` in which `ϖ` and `v` lie in the maximal ideal and `u` is a unit have the same
contraction to `P` (`valuation_lt_one_of_branch`).

Proof: if `W₁(f) < 1`, then `f ∈ u ^ M P + (ϖ, v)` for every `M` (expansion in `u`, the constant
terms being forced into `𝔪_O` because `u` is a unit in `W₁`). Hence the image of `f` in
`P ⧸ (𝔪_{W₂} ∩ P)` lies in every power of the maximal ideal, so it is `0` (Krull).
-/

open IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.NodeUnitBranch

variable {L : Type*} [Field L] {O : Type*} [CommRing O]

/-- The prime `𝔪_W ∩ P`. -/
def contr (P : Subring L) (W : ValuationSubring L) (h : P ≤ W.toSubring) : Ideal P :=
  (maximalIdeal W).comap (Subring.inclusion h)

lemma mem_contr {P : Subring L} {W : ValuationSubring L} {h : P ≤ W.toSubring} {p : P} :
    p ∈ contr P W h ↔ W.valuation (p : L) < 1 :=
  ValuationSubring.valuation_lt_one_iff W (Subring.inclusion h p)

instance (P : Subring L) (W : ValuationSubring L) (h : P ≤ W.toSubring) :
    (contr P W h).IsPrime :=
  Ideal.comap_isPrime _ _

/-- **Uniqueness of the unit branch.** -/
theorem valuation_lt_one_of_branch (P : Subring L) [IsNoetherianRing P] [IsLocalRing P]
    (ι : O →+* L) (ϖ u v : L) (hι : ∀ o, ι o ∈ P) (hϖ : ∀ o : O, ¬ IsUnit o → ∃ o', ι o = ϖ * ι o')
    (gen : ∀ z ∈ P, ∃ o : O, ∃ a ∈ P, ∃ b ∈ P, ∃ c ∈ P, z = ι o + ϖ * a + u * b + v * c)
    (huP : u ∈ P) (hu : ∀ w ∈ P, u * w ≠ 1) (hϖP : ϖ ∈ P) (hvP : v ∈ P)
    {W₁ W₂ : ValuationSubring L} (h₁ : P ≤ W₁.toSubring) (h₂ : P ≤ W₂.toSubring)
    (hϖ₁ : W₁.valuation ϖ < 1) (hv₁ : W₁.valuation v < 1) (hu₁ : W₁.valuation u = 1)
    (hϖ₂ : W₂.valuation ϖ < 1) (hv₂ : W₂.valuation v < 1) {f : L} (hf : f ∈ P)
    (hf₁ : W₁.valuation f < 1) : W₂.valuation f < 1 := by
  classical
  -- small elements: in both maximal ideals
  let Small : L → Prop := fun r ↦ r ∈ P ∧ W₁.valuation r < 1 ∧ W₂.valuation r < 1
  have hle₁ : ∀ p ∈ P, W₁.valuation p ≤ 1 := fun p hp ↦ (W₁.valuation_le_one_iff _).2 (h₁ hp)
  have hle₂ : ∀ p ∈ P, W₂.valuation p ≤ 1 := fun p hp ↦ (W₂.valuation_le_one_iff _).2 (h₂ hp)
  have small_add : ∀ r s, Small r → Small s → Small (r + s) := fun r s hr hs ↦
    ⟨add_mem hr.1 hs.1, lt_of_le_of_lt (W₁.valuation.map_add _ _) (max_lt hr.2.1 hs.2.1),
      lt_of_le_of_lt (W₂.valuation.map_add _ _) (max_lt hr.2.2 hs.2.2)⟩
  have small_mul : ∀ p r, p ∈ P → Small r → Small (p * r) := fun p r hp hr ↦
    ⟨mul_mem hp hr.1, by
      rw [map_mul]; exact (mul_le_of_le_one_left' (hle₁ p hp)).trans_lt hr.2.1, by
      rw [map_mul]; exact (mul_le_of_le_one_left' (hle₂ p hp)).trans_lt hr.2.2⟩
  have small_ϖ : ∀ a ∈ P, Small (ϖ * a) := fun a ha ↦ by
    rw [mul_comm]
    exact small_mul a ϖ ha ⟨hϖP, hϖ₁, hϖ₂⟩
  have small_v : ∀ c ∈ P, Small (v * c) := fun c hc ↦ by
    rw [mul_comm]
    exact small_mul c v hc ⟨hvP, hv₁, hv₂⟩
  have hunitP : ∀ p ∈ P, W₁.valuation p < 1 → ∀ w ∈ P, p * w ≠ 1 := fun p hp hp1 w hw h ↦ by
    have : W₁.valuation (p * w) < 1 := by
      rw [map_mul]; exact (mul_le_of_le_one_right' (hle₁ w hw)).trans_lt hp1
    rw [h, map_one] at this
    exact lt_irrefl _ this
  -- the expansion
  have key : ∀ M : ℕ, ∃ b ∈ P, ∃ r, Small r ∧ f = u ^ M * b + r := by
    intro M
    induction M with
    | zero => exact ⟨f, hf, 0, ⟨zero_mem _, by simp, by simp⟩, by simp⟩
    | succ M ih =>
      obtain ⟨b, hb, r, hr, hfb⟩ := ih
      obtain ⟨o, a, ha, b', hb', c, hc, rfl⟩ := gen b hb
      -- `o` is not a unit
      have ho : ¬ IsUnit o := by
        intro hou
        set z := ι o + u * b' with hz
        have hzP : z ∈ P := add_mem (hι o) (mul_mem huP hb')
        have hz1 : W₁.valuation z < 1 := by
          have e : u ^ M * z = f - r - u ^ M * (ϖ * a + v * c) := by rw [hfb]; ring
          have hs : W₁.valuation (f - r - u ^ M * (ϖ * a + v * c)) < 1 := by
            refine lt_of_le_of_lt (W₁.valuation.map_sub _ _)
              (max_lt (lt_of_le_of_lt (W₁.valuation.map_sub _ _) (max_lt hf₁ hr.2.1)) ?_)
            exact (small_mul _ _ (pow_mem huP M) (small_add _ _ (small_ϖ a ha)
              (small_v c hc))).2.1
          rw [← e, map_mul, map_pow, hu₁, one_pow, one_mul] at hs
          exact hs
        -- `z = unit + nonunit` is a unit of `P`
        have hmax : (⟨u * b', mul_mem huP hb'⟩ : P) ∈ maximalIdeal P := by
          have hum : (⟨u, huP⟩ : P) ∈ maximalIdeal P := fun hun ↦ by
            obtain ⟨w, hw⟩ := hun.exists_right_inv
            exact hu w w.2 (congrArg Subtype.val hw)
          have := Ideal.mul_mem_right (⟨b', hb'⟩ : P) _ hum
          exact this
        have hoP : IsUnit (⟨ι o, hι o⟩ : P) := by
          obtain ⟨w, hw⟩ := hou.exists_right_inv
          exact isUnit_iff_exists_inv.2 ⟨⟨ι w, hι w⟩, by ext; simp [← map_mul, hw]⟩
        have hzu : IsUnit (⟨z, hzP⟩ : P) := by
          by_contra hn
          have h1 : (⟨z, hzP⟩ : P) ∈ maximalIdeal P := hn
          have h2 := sub_mem h1 hmax
          have e : (⟨z, hzP⟩ : P) - ⟨u * b', mul_mem huP hb'⟩ = ⟨ι o, hι o⟩ := by
            ext; simp [hz]
          rw [e] at h2
          exact h2 hoP
        obtain ⟨w, hw⟩ := hzu.exists_right_inv
        exact hunitP z hzP hz1 w w.2 (congrArg Subtype.val hw)
      obtain ⟨o', ho'⟩ := hϖ o ho
      refine ⟨b', hb', u ^ M * (ϖ * (ι o' + a)) + u ^ M * (v * c) + r,
        small_add _ _ (small_add _ _ (small_mul _ _ (pow_mem huP M)
          (small_ϖ _ (add_mem (hι o') ha))) (small_mul _ _ (pow_mem huP M) (small_v c hc))) hr,
        ?_⟩
      rw [hfb, ho']
      ring
  -- Krull intersection in `P ⧸ (𝔪_{W₂} ∩ P)`
  set 𝔮 := contr P W₂ h₂
  haveI : Nontrivial (P ⧸ 𝔮) := Ideal.Quotient.nontrivial_iff.2 (Ideal.IsPrime.ne_top inferInstance)
  haveI : IsLocalRing (P ⧸ 𝔮) := .of_surjective' (Ideal.Quotient.mk 𝔮) Ideal.Quotient.mk_surjective
  have hbot := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (P ⧸ 𝔮))
    (maximalIdeal.isMaximal _).ne_top
  have hum : Ideal.Quotient.mk 𝔮 ⟨u, huP⟩ ∈ maximalIdeal (P ⧸ 𝔮) := by
    intro hun
    obtain ⟨w, hw⟩ := hun.exists_right_inv
    obtain ⟨w', rfl⟩ := Ideal.Quotient.mk_surjective w
    rw [← map_mul, ← map_one (Ideal.Quotient.mk 𝔮), Ideal.Quotient.eq] at hw
    have hm : (⟨u, huP⟩ : P) * w' - 1 ∈ maximalIdeal P :=
      le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) hw
    have hu' : IsUnit ((⟨u, huP⟩ : P) * w') := by
      by_contra hn
      have := sub_mem (show (⟨u, huP⟩ : P) * w' ∈ maximalIdeal P from hn) hm
      rw [sub_sub_cancel] at this
      exact (maximalIdeal.isMaximal P).ne_top ((Ideal.eq_top_iff_one _).2 this)
    obtain ⟨t, ht⟩ := (isUnit_of_mul_isUnit_left hu').exists_right_inv
    exact hu t t.2 (congrArg Subtype.val ht)
  have hmem : Ideal.Quotient.mk 𝔮 ⟨f, hf⟩ ∈ ⨅ i, maximalIdeal (P ⧸ 𝔮) ^ i := by
    refine Ideal.mem_iInf.2 fun M ↦ ?_
    obtain ⟨b, hb, r, hr, hfb⟩ := key M
    have e : Ideal.Quotient.mk 𝔮 ⟨f, hf⟩ =
        Ideal.Quotient.mk 𝔮 ⟨u, huP⟩ ^ M * Ideal.Quotient.mk 𝔮 ⟨b, hb⟩ := by
      rw [← map_pow, ← map_mul, Ideal.Quotient.eq, mem_contr]
      have : ((⟨f, hf⟩ - ⟨u, huP⟩ ^ M * ⟨b, hb⟩ : P) : L) = r := by
        simp [hfb]
      rw [this]; exact hr.2.2
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hum M)
  rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, mem_contr] at hmem
  exact hmem

end TemperedFundamentalGroups.SemistableReduction.NodeUnitBranch
