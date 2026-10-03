/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartBasis

/-!
# The Laurent split on the unit circle

Blueprint §9.9, S7⁺.4. A rational function `φ = P / (Q_out Q_in)` over an algebraically closed
non-archimedean field `C`, where `Q_out` has all roots in `|α| > 1` and `Q_in` all roots in
`|α| < 1`, is `φ₊ + φ₋` with `φ₊ = P₊ / Q_out` regular on the closed unit disc and `φ₋ = r / Q_in`,
`deg r < deg Q_in`, regular on `|x| ≥ 1` and vanishing at `∞`; both have Gauss norm `≤ |φ|`
(`exists_laurent_split`). The norm bound is a degree separation after reduction:
`Q̄_in = x̄ᵉ` and `Q̄_out` is a constant.
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "vC" => NormedField.valuation (K := C)

section RedPolyRing

lemma redPoly_map (P' : (HenselComplete.integers C)[X]) :
    redPoly (P'.map (algebraMap (HenselComplete.integers C) C)) = P'.map (residue _) := by
  obtain ⟨P'', hP'', hred⟩ := exists_lift_redPoly (Gauss.sup_one_map_le (v := vC) P')
  rw [← hred, map_injective _ (FaithfulSMul.algebraMap_injective _ C) hP'']

lemma redPoly_mul {P Q : C[X]} (hP : Gauss.sup vC 1 P ≤ 1) (hQ : Gauss.sup vC 1 Q ≤ 1) :
    redPoly (P * Q) = redPoly P * redPoly Q := by
  obtain ⟨P', rfl, -⟩ := exists_lift_redPoly hP
  obtain ⟨Q', rfl, -⟩ := exists_lift_redPoly hQ
  rw [← Polynomial.map_mul, redPoly_map, redPoly_map, redPoly_map, Polynomial.map_mul]

lemma redPoly_add {P Q : C[X]} (hP : Gauss.sup vC 1 P ≤ 1) (hQ : Gauss.sup vC 1 Q ≤ 1) :
    redPoly (P + Q) = redPoly P + redPoly Q := by
  obtain ⟨P', rfl, -⟩ := exists_lift_redPoly hP
  obtain ⟨Q', rfl, -⟩ := exists_lift_redPoly hQ
  rw [← Polynomial.map_add, redPoly_map, redPoly_map, redPoly_map, Polynomial.map_add]

lemma natDegree_redPoly_le (P : C[X]) : (redPoly P).natDegree ≤ P.natDegree := by
  by_cases hP : Gauss.sup vC 1 P ≤ 1
  · obtain ⟨P', hP', hred⟩ := exists_lift_redPoly hP
    rw [← hred, ← hP', natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ C)]
    exact natDegree_map_le
  · rw [redPoly, dif_neg fun h ↦ hP (Gauss.sup_le_iff.2 fun i ↦ by
      simpa [Gauss.term] using h i)]
    simp

omit [IsUltrametricDist C] in
lemma algebraMap_polyC (c : C) :
    algebraMap C[X] (RatFunc C) (Polynomial.C c) = algebraMap C (RatFunc C) c := by
  rw [IsScalarTower.algebraMap_apply C C[X] (RatFunc C), Polynomial.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]

lemma sup_C_mul (c : C) (P : C[X]) :
    Gauss.sup vC 1 (Polynomial.C c * P) = ‖c‖₊ * Gauss.sup vC 1 P := by
  rw [Gauss.sup_mul, ← gauss1_algebraMap, algebraMap_polyC, gauss1_algebraMap_C]

/-- Products of `X - α` over roots in the open unit disc: Gauss norm `1`, reduction `X^e`. -/
lemma prod_disc (s : Multiset C) (hs : ∀ α ∈ s, ‖α‖ < 1) :
    Gauss.sup vC 1 (s.map fun α ↦ X - Polynomial.C α).prod = 1 ∧
      redPoly (s.map fun α ↦ X - Polynomial.C α).prod = X ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.card_zero, pow_zero]
    have h1 : Gauss.sup vC 1 (1 : C[X]) = 1 := by
      rw [← gauss1_algebraMap, map_one, map_one]
    refine ⟨h1, ?_⟩
    rw [← Polynomial.map_one (algebraMap (HenselComplete.integers C) C), redPoly_map,
      Polynomial.map_one]
  | cons α s ih =>
    obtain ⟨h1, h2⟩ := ih fun β hβ ↦ hs β (Multiset.mem_cons_of_mem hβ)
    have hα := hs α (Multiset.mem_cons_self α s)
    have hX := sup_X_sub_C (C := C) hα.le
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons]
    refine ⟨by rw [Gauss.sup_mul, hX, h1, one_mul], ?_⟩
    rw [redPoly_mul hX.le h1.le, h2, pow_succ, mul_comm]
    congr 1
    have hα' : α ∈ HenselComplete.integers C := by
      rw [HenselComplete.mem_integers_iff]; exact hα.le
    have : X - Polynomial.C α = (X - Polynomial.C (⟨α, hα'⟩ : HenselComplete.integers C)).map
        (algebraMap (HenselComplete.integers C) C) := by simp
    rw [this, redPoly_map]
    simp only [Polynomial.map_sub, map_X, map_C, sub_eq_self, C_eq_zero, residue_eq_zero_iff,
      HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
    exact hα

/-- Products of `1 - α⁻¹ X` over roots outside the closed unit disc: Gauss norm `1`,
reduction `1`. -/
lemma prod_out (s : Multiset C) (hs : ∀ α ∈ s, 1 < ‖α‖) :
    Gauss.sup vC 1 (s.map fun α ↦ 1 - Polynomial.C α⁻¹ * X).prod = 1 ∧
      redPoly (s.map fun α ↦ 1 - Polynomial.C α⁻¹ * X).prod = 1 := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero, Multiset.prod_zero]
    have h1 : Gauss.sup vC 1 (1 : C[X]) = 1 := by
      rw [← gauss1_algebraMap, map_one, map_one]
    refine ⟨h1, ?_⟩
    rw [← Polynomial.map_one (algebraMap (HenselComplete.integers C) C), redPoly_map,
      Polynomial.map_one]
  | cons α s ih =>
    obtain ⟨h1, h2⟩ := ih fun β hβ ↦ hs β (Multiset.mem_cons_of_mem hβ)
    have hα := hs α (Multiset.mem_cons_self α s)
    have hαi : ‖α⁻¹‖ < 1 := by
      rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hα
    have hαi' : α⁻¹ ∈ HenselComplete.integers C := by
      rw [HenselComplete.mem_integers_iff]; exact hαi.le
    have hfac : 1 - Polynomial.C α⁻¹ * X = (1 - Polynomial.C (⟨α⁻¹, hαi'⟩ :
        HenselComplete.integers C) * X).map (algebraMap (HenselComplete.integers C) C) := by
      simp
    have hX : Gauss.sup vC 1 (1 - Polynomial.C α⁻¹ * X) = 1 := by
      rw [hfac]
      refine Gauss.sup_one_map_eq (v := vC) _ ?_
      intro h
      have := congrArg (fun P ↦ P.coeff 0) h
      simp at this
    have hr : redPoly (1 - Polynomial.C α⁻¹ * X) = 1 := by
      rw [hfac, redPoly_map]
      simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul, map_X, map_C,
        sub_eq_self, mul_eq_zero, C_eq_zero, residue_eq_zero_iff,
        HenselComplete.mem_maximalIdeal_iff_norm_lt_one, X_ne_zero, or_false]
      exact hαi
    simp only [Multiset.map_cons, Multiset.prod_cons]
    exact ⟨by rw [Gauss.sup_mul, hX, h1, one_mul], by
      rw [redPoly_mul hX.le h1.le, hr, h2, one_mul]⟩

end RedPolyRing

section Split

omit [IsUltrametricDist C] in
lemma prod_X_sub_C_eq (s : Multiset C) (hs : ∀ α ∈ s, α ≠ 0) :
    (s.map fun α ↦ X - Polynomial.C α).prod =
      Polynomial.C (s.map fun α ↦ -α).prod * (s.map fun α ↦ 1 - Polynomial.C α⁻¹ * X).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons α s ih =>
    have hα := hs α (Multiset.mem_cons_self α s)
    simp only [Multiset.map_cons, Multiset.prod_cons, Polynomial.C_mul]
    rw [ih fun β hβ ↦ hs β (Multiset.mem_cons_of_mem hβ)]
    have : X - Polynomial.C α = Polynomial.C (-α) * (1 - Polynomial.C α⁻¹ * X) := by
      rw [mul_sub, mul_one, ← mul_assoc, ← Polynomial.C_mul,
        show -α * α⁻¹ = -1 by rw [neg_mul, mul_inv_cancel₀ hα], Polynomial.C_neg,
        Polynomial.C_neg, Polynomial.C_1]
      ring
    rw [this]
    ring

/-- **Degree separation**: if `deg B < e`, `Q_in` reduces to `X^e` and `Q_out` to `1` (both of
Gauss norm `1`), then `A` and `B` have Gauss norm at most that of `A Q_in + B Q_out`. -/
lemma sup_le_of_sep {A B Qi Qo : C[X]} {e : ℕ} (hB : B.natDegree < e ∨ B = 0)
    (hQi : Gauss.sup vC 1 Qi = 1) (hQi' : redPoly Qi = X ^ e)
    (hQo : Gauss.sup vC 1 Qo = 1) (hQo' : redPoly Qo = 1) :
    Gauss.sup vC 1 A ≤ Gauss.sup vC 1 (A * Qi + B * Qo) ∧
      Gauss.sup vC 1 B ≤ Gauss.sup vC 1 (A * Qi + B * Qo) := by
  set S := A * Qi + B * Qo
  by_contra hcon
  rw [not_and_or, not_le, not_le] at hcon
  set M := max (Gauss.sup vC 1 A) (Gauss.sup vC 1 B)
  have hSM : Gauss.sup vC 1 S < M := by
    rcases hcon with h | h
    · exact h.trans_le (le_max_left _ _)
    · exact h.trans_le (le_max_right _ _)
  have hM0 : 0 < M := lt_of_le_of_lt zero_le hSM
  obtain ⟨γ, hγ⟩ : ∃ γ : C, ‖γ‖₊ = M := by
    rcases le_total (Gauss.sup vC 1 A) (Gauss.sup vC 1 B) with h | h
    · obtain ⟨γ, hγ⟩ := exists_sup_eq B
      exact ⟨γ, by rw [← hγ]; exact (max_eq_right h).symm⟩
    · obtain ⟨γ, hγ⟩ := exists_sup_eq A
      exact ⟨γ, by rw [← hγ]; exact (max_eq_left h).symm⟩
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hγ
    exact hM0.ne hγ
  have hγn : ‖γ⁻¹‖₊ * M = 1 := by
    rw [nnnorm_inv, hγ, inv_mul_cancel₀ hM0.ne']
  set A' := Polynomial.C γ⁻¹ * A
  set B' := Polynomial.C γ⁻¹ * B
  have hA' : Gauss.sup vC 1 A' ≤ 1 := by
    rw [sup_C_mul, ← hγn]
    exact mul_le_mul_right (le_max_left _ _) _
  have hB' : Gauss.sup vC 1 B' ≤ 1 := by
    rw [sup_C_mul, ← hγn]
    exact mul_le_mul_right (le_max_right _ _) _
  have hS' : Gauss.sup vC 1 (A' * Qi + B' * Qo) < 1 := by
    have : A' * Qi + B' * Qo = Polynomial.C γ⁻¹ * S := by simp only [A', B', S]; ring
    rw [this, sup_C_mul, ← hγn]
    exact mul_lt_mul_of_pos_left hSM (by simpa using hγ0)
  have hred := redPoly_eq_zero_of_sup_lt_one hS'
  rw [redPoly_add (by rw [Gauss.sup_mul, hQi, mul_one]; exact hA')
    (by rw [Gauss.sup_mul, hQo, mul_one]; exact hB'), redPoly_mul hA' hQi.le,
    redPoly_mul hB' hQo.le, hQi', hQo', mul_one] at hred
  have hdegB : (redPoly B').natDegree < e ∨ redPoly B' = 0 := by
    rcases hB with hB | hB
    · left
      refine (natDegree_redPoly_le B').trans_lt ?_
      exact (natDegree_C_mul_le _ _).trans_lt hB
    · right
      simp only [B', hB, mul_zero]
      exact redPoly_eq_zero_of_sup_lt_one (by simp [Gauss.sup])
  have hA0 : redPoly A' = 0 := by
    by_contra hA0
    have h1 : redPoly B' = -(redPoly A' * X ^ e) := eq_neg_of_add_eq_zero_right hred
    have h2 : (redPoly B').natDegree = (redPoly A').natDegree + e := by
      rw [h1, natDegree_neg, natDegree_mul hA0 (pow_ne_zero _ X_ne_zero), natDegree_X_pow]
    rcases hdegB with h | h
    · omega
    · rw [h, eq_comm, neg_eq_zero, mul_eq_zero] at h1
      exact h1.elim hA0 (pow_ne_zero _ X_ne_zero)
  have hB0 : redPoly B' = 0 := by
    rw [hA0, zero_mul, zero_add] at hred
    exact hred
  have h1 := sup_lt_one_of_redPoly_eq_zero hA' hA0
  have h2 := sup_lt_one_of_redPoly_eq_zero hB' hB0
  rw [sup_C_mul] at h1 h2
  have h3 : ‖γ⁻¹‖₊ * M < 1 := by
    rcases le_total (Gauss.sup vC 1 A) (Gauss.sup vC 1 B) with h | h
    · rw [show M = Gauss.sup vC 1 B from max_eq_right h]; exact h2
    · rw [show M = Gauss.sup vC 1 A from max_eq_left h]; exact h1
  rw [hγn] at h3
  exact lt_irrefl _ h3

variable [IsAlgClosed C]

/-- **The Laurent split** (S7⁺.4). -/
theorem exists_laurent_split (P : C[X]) {Qo Qi : C[X]} (hQo : Qo ≠ 0) (hQi : Qi ≠ 0)
    (ho : ∀ α ∈ Qo.roots, 1 < ‖α‖) (hi : ∀ α ∈ Qi.roots, ‖α‖ < 1) :
    ∃ Pp r : C[X], (r.natDegree < Qi.natDegree ∨ r = 0) ∧
      algebraMap C[X] (RatFunc C) P / algebraMap C[X] (RatFunc C) (Qo * Qi) =
        algebraMap C[X] (RatFunc C) Pp / algebraMap C[X] (RatFunc C) Qo +
          algebraMap C[X] (RatFunc C) r / algebraMap C[X] (RatFunc C) Qi ∧
      gauss1 C (algebraMap C[X] (RatFunc C) Pp / algebraMap C[X] (RatFunc C) Qo) ≤
        gauss1 C (algebraMap C[X] (RatFunc C) P / algebraMap C[X] (RatFunc C) (Qo * Qi)) ∧
      gauss1 C (algebraMap C[X] (RatFunc C) r / algebraMap C[X] (RatFunc C) Qi) ≤
        gauss1 C (algebraMap C[X] (RatFunc C) P / algebraMap C[X] (RatFunc C) (Qo * Qi)) := by
  set ι := algebraMap C[X] (RatFunc C)
  have hι (Q : C[X]) (hQ : Q ≠ 0) : ι Q ≠ 0 := by simpa [ι] using hQ
  -- monic normalizations
  set lo := Qo.leadingCoeff
  set li := Qi.leadingCoeff
  have hlo : lo ≠ 0 := leadingCoeff_ne_zero.2 hQo
  have hli : li ≠ 0 := leadingCoeff_ne_zero.2 hQi
  set Mo := Qo * Polynomial.C lo⁻¹
  set Mi := Qi * Polynomial.C li⁻¹
  have hMo : Mo.Monic := monic_mul_leadingCoeff_inv hQo
  have hMi : Mi.Monic := monic_mul_leadingCoeff_inv hQi
  have hMoR : Mo.roots = Qo.roots := by
    change (Qo * Polynomial.C lo⁻¹).roots = _
    rw [mul_comm]; exact roots_C_mul _ (inv_ne_zero hlo)
  have hMiR : Mi.roots = Qi.roots := by
    change (Qi * Polynomial.C li⁻¹).roots = _
    rw [mul_comm]; exact roots_C_mul _ (inv_ne_zero hli)
  have hcop : IsCoprime Mo Mi := by
    refine (Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed C C Mo Mi).2 fun a ↦ ?_
    by_contra h
    push Not at h
    have h1 : a ∈ Mo.roots := (mem_roots hMo.ne_zero).2 (by simpa using h.1)
    have h2 : a ∈ Mi.roots := (mem_roots hMi.ne_zero).2 (by simpa using h.2)
    rw [hMoR] at h1
    rw [hMiR] at h2
    exact lt_asymm (ho a h1) (hi a h2)
  obtain ⟨q, r₁, r₂, hr₁, hr₂, hsplit⟩ :=
    Polynomial.div_eq_quo_add_rem_div_add_rem_div (K := RatFunc C) P hMo hMi hcop
  -- the products of roots
  have hMiprod : (Mi.roots.map fun α ↦ X - Polynomial.C α).prod = Mi :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hMi IsAlgClosed.card_roots_eq_natDegree
  have hMoprod : (Mo.roots.map fun α ↦ X - Polynomial.C α).prod = Mo :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hMo IsAlgClosed.card_roots_eq_natDegree
  obtain ⟨hMi1, hMi2⟩ := prod_disc Mi.roots fun α hα ↦ hi α (hMiR ▸ hα)
  rw [hMiprod] at hMi1 hMi2
  obtain ⟨hNo1, hNo2⟩ := prod_out Mo.roots fun α hα ↦ ho α (hMoR ▸ hα)
  set No := (Mo.roots.map fun α ↦ 1 - Polynomial.C α⁻¹ * X).prod
  -- `Mo = κ No`
  set κ := (Mo.roots.map fun α ↦ -α).prod
  have h0 : ∀ α ∈ Mo.roots, α ≠ 0 := fun α hα h ↦ by
    have := ho α (hMoR ▸ hα)
    rw [h, norm_zero] at this
    exact absurd this (by norm_num)
  have hMoNo : Mo = Polynomial.C κ * No := by
    conv_lhs => rw [← hMoprod]
    exact prod_X_sub_C_eq _ h0
  have hκ : κ ≠ 0 := Multiset.prod_ne_zero fun h ↦ by
    obtain ⟨α, hα, hα0⟩ := Multiset.mem_map.1 h
    exact h0 α hα (neg_eq_zero.1 hα0)
  have hQo' : Qo = Polynomial.C (lo * κ) * No := by
    rw [Polynomial.C_mul, mul_assoc, ← hMoNo, mul_comm, mul_assoc, ← Polynomial.C_mul,
      inv_mul_cancel₀ hlo, Polynomial.C_1, mul_one]
  have hQi' : Qi = Polynomial.C li * Mi := by
    rw [mul_comm, mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hli, Polynomial.C_1, mul_one]
  set Pp := Polynomial.C li⁻¹ * (q * Mo + r₁)
  set r := Polynomial.C lo⁻¹ * r₂
  set A := Polynomial.C (lo * κ)⁻¹ * Pp
  set B := Polynomial.C li⁻¹ * r
  have hNo0 : No ≠ 0 := fun h ↦ by rw [h] at hNo1; simp [Gauss.sup] at hNo1
  have hlk : lo * κ ≠ 0 := mul_ne_zero hlo hκ
  have hlo' : algebraMap C (RatFunc C) lo ≠ 0 := by simpa using hlo
  have hli' : algebraMap C (RatFunc C) li ≠ 0 := by simpa using hli
  have hκ' : algebraMap C (RatFunc C) κ ≠ 0 := by simpa using hκ
  have hNo' : ι No ≠ 0 := hι _ hNo0
  have hMi' : ι Mi ≠ 0 := hι _ hMi.ne_zero
  have hφp : ι Pp / ι Qo = ι A / ι No := by
    rw [hQo']
    simp only [A, ι, map_mul, algebraMap_polyC, map_inv₀]
    field_simp
  have hφm : ι r / ι Qi = ι B / ι Mi := by
    rw [hQi']
    simp only [B, ι, map_mul, algebraMap_polyC, map_inv₀]
    field_simp
  have hMo0 := hι _ hMo.ne_zero
  have hMi0 := hι _ hMi.ne_zero
  have hid : ι P / ι (Qo * Qi) = ι Pp / ι Qo + ι r / ι Qi := by
    have eQo : ι Qo = ι Mo * algebraMap C (RatFunc C) lo := by
      have : Qo = Mo * Polynomial.C lo := by
        change Qo = Qo * Polynomial.C lo⁻¹ * Polynomial.C lo
        rw [mul_assoc, ← Polynomial.C_mul, inv_mul_cancel₀ hlo, Polynomial.C_1, mul_one]
      rw [this, map_mul, algebraMap_polyC]
    have eQi : ι Qi = ι Mi * algebraMap C (RatFunc C) li := by
      rw [hQi', map_mul, algebraMap_polyC, mul_comm]
    have ePp : ι Pp = (algebraMap C (RatFunc C) li)⁻¹ * (ι q * ι Mo + ι r₁) := by
      change ι (Polynomial.C li⁻¹ * (q * Mo + r₁)) = _
      rw [map_mul, algebraMap_polyC, map_inv₀, map_add, map_mul]
    have er : ι r = (algebraMap C (RatFunc C) lo)⁻¹ * ι r₂ := by
      change ι (Polynomial.C lo⁻¹ * r₂) = _
      rw [map_mul, algebraMap_polyC, map_inv₀]
    have e1 : ι P = ι q * ι Mo * ι Mi + ι r₁ * ι Mi + ι r₂ * ι Mo := by
      have hs : ι P / (ι Mo * ι Mi) = ι q + ι r₁ / ι Mo + ι r₂ / ι Mi := hsplit
      field_simp at hs
      linear_combination hs
    rw [map_mul, eQo, eQi, ePp, er, e1]
    field_simp
  refine ⟨Pp, r, ?_, hid, ?_⟩
  · by_cases hr0 : r₂ = 0
    · right; simp [r, hr0]
    · left
      refine (natDegree_C_mul_le _ _).trans_lt ?_
      rw [hQi', natDegree_C_mul hli]
      exact natDegree_lt_natDegree hr0 hr₂
  have hsum : ι P / ι (Qo * Qi) = ι (A * Mi + B * No) / (ι No * ι Mi) := by
    rw [hid, hφp, hφm, div_add_div _ _ hNo' hMi']
    congr 1
    rw [map_add, map_mul ι A Mi, map_mul ι B No]
    ring
  have hgsum : gauss1 C (ι P / ι (Qo * Qi)) = Gauss.sup vC 1 (A * Mi + B * No) := by
    rw [hsum, map_div₀, map_mul, gauss1_algebraMap, gauss1_algebraMap, gauss1_algebraMap, hNo1,
      hMi1, mul_one, div_one]
  have hB : B.natDegree < Mi.natDegree ∨ B = 0 := by
    by_cases hr0 : r₂ = 0
    · right; simp [B, r, hr0]
    · left
      refine (natDegree_C_mul_le _ _).trans_lt ((natDegree_C_mul_le _ _).trans_lt ?_)
      exact natDegree_lt_natDegree hr0 hr₂
  have hsep := sup_le_of_sep (A := A) hB hMi1 (by rw [hMi2, IsAlgClosed.card_roots_eq_natDegree]) hNo1 hNo2
  rw [hφp, hφm, hgsum, map_div₀, map_div₀, gauss1_algebraMap, gauss1_algebraMap,
    gauss1_algebraMap, gauss1_algebraMap, hNo1, hMi1, div_one, div_one]
  exact hsep

end Split

end GaussFibre

end SemistableReduction
