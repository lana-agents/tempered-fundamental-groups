/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CompositeValuation

/-!
# Zeros of non-constant functions on a component (Blueprint §10.3.8, CrossingX1, CX2)

Let `W` be a valuation subring of `F` (the generic point of a component), `φ₀ : O₁ → W` a local
ring mapping its maximal ideal into `𝔪_W` (the base), and `g` a unit of `W` (a function on the
component). If `g` has a pole somewhere on the component (`g⁻¹ ∈ 𝔪_R` for a valuation subring
`R ≤ W` containing the base), then `g` also has a zero (`exists_le_lt_one`): its residue is not a
unit in `κ(O₁)[ḡ]`, and a valuation of `κ(W)` centred on `(ḡ)` gives the composite `R'`.
-/

universe u

open IsLocalRing Polynomial

namespace TemperedFundamentalGroups.SemistableReduction.CompositeValuation

variable {F : Type u} [Field F]

lemma not_lt_one_and_sub {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation F Γ)
    {a : F} (h₁ : v a < 1) (h₂ : v (a - 1) < 1) : False := by
  have : v (1 : F) < 1 := by
    have e : (1 : F) = a - (a - 1) := by ring
    rw [e]
    exact lt_of_le_of_lt (v.map_sub _ _) (max_lt h₁ h₂)
  rw [v.map_one] at this
  exact lt_irrefl _ this

lemma pow_mul_inv_pow_lt {g : F} (hg0 : g ≠ 0) {i N : ℕ} (hi : i < N) :
    g ^ (i + 1) * g⁻¹ ^ (N + 1) = g⁻¹ ^ (N - i) := by
  have : N + 1 = (N - i) + (i + 1) := by omega
  rw [this, pow_add g⁻¹ (N - i) (i + 1), ← mul_assoc, mul_comm (g ^ (i + 1)), mul_assoc,
    ← mul_pow, mul_inv_cancel₀ hg0, one_pow, mul_one]

lemma pow_mul_inv_pow_ge {g : F} (hg0 : g ≠ 0) {i N : ℕ} (hi : N ≤ i) :
    g ^ (i + 1) * g⁻¹ ^ (N + 1) = g ^ (i - N) := by
  have : i + 1 = (i - N) + (N + 1) := by omega
  rw [this, pow_add g (i - N) (N + 1), mul_assoc, ← mul_pow, mul_inv_cancel₀ hg0, one_pow,
    mul_one]

/-- **The residue of `g` is not a unit of `κ(O₁)[ḡ]`.** -/
lemma not_unit_residue (W : ValuationSubring F) {O₁ : Type u} [CommRing O₁] [IsLocalRing O₁]
    (φ₀ : O₁ →+* F) (hφm : ∀ o ∈ maximalIdeal O₁, W.valuation (φ₀ o) < 1) {g : F}
    (hgW : g ∈ W) (hgi : g⁻¹ ∈ W) {R : ValuationSubring F} (hRW : R ≤ W) (hR : ∀ o, φ₀ o ∈ R)
    (hgR : R.valuation g⁻¹ < 1) (q : O₁[X]) : ¬ W.valuation (g * q.eval₂ φ₀ g - 1) < 1 := by
  classical
  intro h
  have hg0 : g ≠ 0 := by rintro rfl; simp at h
  have hφW : ∀ o, φ₀ o ∈ W := fun o ↦ hRW (hR o)
  set y := g⁻¹ with hy
  set qb := q.map (residue O₁) with hqb
  set d := q.natDegree
  have heval : q.eval₂ φ₀ g = ∑ i ∈ Finset.range (d + 1), φ₀ (q.coeff i) * g ^ i :=
    eval₂_eq_sum_range _ _
  by_cases hq0 : qb = 0
  · -- all coefficients in `𝔪`
    have hc : ∀ i, q.coeff i ∈ maximalIdeal O₁ := fun i ↦ by
      have := congrArg (fun p ↦ p.coeff i) hq0
      simp only [hqb, coeff_map, coeff_zero] at this
      exact (residue_eq_zero_iff _).1 this
    have hlt : W.valuation (g * q.eval₂ φ₀ g) < 1 := by
      rw [heval, Finset.mul_sum]
      refine Valuation.map_sum_lt _ one_ne_zero fun i _ ↦ ?_
      rw [map_mul, map_mul, map_pow]
      calc W.valuation g * (W.valuation (φ₀ (q.coeff i)) * W.valuation g ^ i)
          ≤ 1 * (W.valuation (φ₀ (q.coeff i)) * 1) := by
            gcongr
            · exact (W.valuation_le_one_iff _).2 hgW
            · exact pow_le_one₀ zero_le ((W.valuation_le_one_iff _).2 hgW)
        _ < 1 := by rw [one_mul, mul_one]; exact hφm _ (hc i)
    exact not_lt_one_and_sub W.valuation hlt h
  -- the leading coefficient of `q̄`
  set N := qb.natDegree
  have hN : q.coeff N ∉ maximalIdeal O₁ := fun hm ↦ by
    have : qb.leadingCoeff = 0 := by
      rw [leadingCoeff, hqb, coeff_map]; exact (residue_eq_zero_iff _).2 hm
    exact hq0 (leadingCoeff_eq_zero.1 this)
  have hgt : ∀ i, N < i → q.coeff i ∈ maximalIdeal O₁ := fun i hi ↦ by
    have := coeff_eq_zero_of_natDegree_lt hi
    rw [hqb, coeff_map] at this
    exact (residue_eq_zero_iff _).1 this
  have hNd : N ≤ d := natDegree_map_le
  -- multiply by `y ^ (N + 1)`
  set E := y ^ (N + 1) * (g * q.eval₂ φ₀ g - 1) with hE
  have hyW : W.valuation y ≤ 1 := (W.valuation_le_one_iff _).2 hgi
  have hER : R.valuation E < 1 := by
    refine valuation_lt_one_of_le hRW ?_
    rw [hE, map_mul, map_pow]
    calc W.valuation y ^ (N + 1) * W.valuation (g * q.eval₂ φ₀ g - 1)
        ≤ 1 * W.valuation (g * q.eval₂ φ₀ g - 1) := by
          gcongr; exact pow_le_one₀ zero_le hyW
      _ < 1 := by rw [one_mul]; exact h
  have hsplit : E = φ₀ (q.coeff N) +
      (∑ i ∈ (Finset.range (d + 1)).erase N, φ₀ (q.coeff i) * (g ^ (i + 1) * y ^ (N + 1)) -
        y ^ (N + 1)) := by
    have hmem : N ∈ Finset.range (d + 1) := Finset.mem_range.2 (by omega)
    rw [hE, heval, mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.add_sum_erase _ _ hmem,
      mul_one]
    have e1 : y ^ (N + 1) * (g * (φ₀ (q.coeff N) * g ^ N)) = φ₀ (q.coeff N) := by
      rw [hy, inv_pow]
      field_simp
      ring
    rw [e1]
    have e2 : ∀ i ∈ (Finset.range (d + 1)).erase N, y ^ (N + 1) * (g * (φ₀ (q.coeff i) * g ^ i)) =
        φ₀ (q.coeff i) * (g ^ (i + 1) * y ^ (N + 1)) := fun i _ ↦ by ring
    rw [Finset.sum_congr rfl e2]
    ring
  have hrest : R.valuation (∑ i ∈ (Finset.range (d + 1)).erase N,
      φ₀ (q.coeff i) * (g ^ (i + 1) * y ^ (N + 1)) - y ^ (N + 1)) < 1 := by
    refine lt_of_le_of_lt (R.valuation.map_sub _ _) (max_lt ?_ ?_)
    · refine Valuation.map_sum_lt _ one_ne_zero fun i hi ↦ ?_
      have hiN := Finset.ne_of_mem_erase hi
      rcases lt_or_gt_of_ne hiN with hlt | hgt'
      · rw [hy, pow_mul_inv_pow_lt hg0 hlt, map_mul, map_pow]
        calc R.valuation (φ₀ (q.coeff i)) * R.valuation g⁻¹ ^ (N - i)
            ≤ 1 * R.valuation g⁻¹ ^ (N - i) := by
              gcongr; exact (R.valuation_le_one_iff _).2 (hR _)
          _ < 1 := by
            rw [one_mul]
            exact pow_lt_one₀ zero_le hgR (by omega)
      · refine valuation_lt_one_of_le hRW ?_
        rw [hy, pow_mul_inv_pow_ge hg0 hgt'.le, map_mul, map_pow]
        calc W.valuation (φ₀ (q.coeff i)) * W.valuation g ^ (i - N)
            ≤ W.valuation (φ₀ (q.coeff i)) * 1 := by
              gcongr; exact pow_le_one₀ zero_le ((W.valuation_le_one_iff _).2 hgW)
          _ < 1 := by rw [mul_one]; exact hφm _ (hgt i hgt')
    · rw [map_pow]; exact pow_lt_one₀ zero_le hgR (by omega)
  have hlead : R.valuation (φ₀ (q.coeff N)) < 1 := by
    have e : φ₀ (q.coeff N) = E - (∑ i ∈ (Finset.range (d + 1)).erase N,
        φ₀ (q.coeff i) * (g ^ (i + 1) * y ^ (N + 1)) - y ^ (N + 1)) := by
      rw [hsplit]; ring
    rw [e]
    exact lt_of_le_of_lt (R.valuation.map_sub _ _) (max_lt hER hrest)
  -- but the leading coefficient is a unit
  have hu : IsUnit (q.coeff N) := by
    by_contra hn; exact hN hn
  obtain ⟨w, hw⟩ := hu.exists_right_inv
  have h1 : R.valuation (φ₀ (q.coeff N)) * R.valuation (φ₀ w) = 1 := by
    rw [← map_mul, ← map_mul, hw, map_one, map_one]
  have h2 : R.valuation (φ₀ w) ≤ 1 := (R.valuation_le_one_iff _).2 (hR w)
  have : R.valuation (φ₀ (q.coeff N)) * R.valuation (φ₀ w) < 1 :=
    (mul_le_of_le_one_right' h2).trans_lt hlead
  rw [h1] at this
  exact lt_irrefl _ this

/-- **Zeros of non-constant functions.** -/
theorem exists_le_lt_one (W : ValuationSubring F) {O₁ : Type u} [CommRing O₁] [IsLocalRing O₁]
    (φ₀ : O₁ →+* F) (hφm : ∀ o ∈ maximalIdeal O₁, W.valuation (φ₀ o) < 1) {g : F}
    (hgW : g ∈ W) (hgi : g⁻¹ ∈ W) {R : ValuationSubring F} (hRW : R ≤ W) (hR : ∀ o, φ₀ o ∈ R)
    (hgR : R.valuation g⁻¹ < 1) :
    ∃ R' : ValuationSubring F, R' ≤ W ∧ (∀ o, φ₀ o ∈ R') ∧ R'.valuation g < 1 := by
  have hφW : ∀ o, φ₀ o ∈ W := fun o ↦ hRW (hR o)
  let ρ₀ : O₁ →+* ResidueField W := (res W).comp (φ₀.codRestrict W.toSubring hφW)
  set gb := res W ⟨g, hgW⟩
  let S : Subring (ResidueField W) := (eval₂RingHom ρ₀ gb).range
  have hgS : gb ∈ S := ⟨X, eval₂_X _ _⟩
  -- `ḡ` is not a unit of `S`
  have hspan : Ideal.span {(⟨gb, hgS⟩ : S)} ≠ ⊤ := by
    intro htop
    obtain ⟨⟨_, q, rfl⟩, hq⟩ := Ideal.mem_span_singleton'.1 ((Ideal.eq_top_iff_one _).1 htop)
    apply not_unit_residue W φ₀ hφm hgW hgi hRW hR hgR q
    have hev : q.eval₂ φ₀ g ∈ W := by
      rw [eval₂_eq_sum_range]
      exact sum_mem fun i _ ↦ mul_mem (hφW _) (pow_mem hgW _)
    have hmemW : g * q.eval₂ φ₀ g - 1 ∈ W := sub_mem (mul_mem hgW hev) (one_mem _)
    have hres : res W ⟨g * q.eval₂ φ₀ g - 1, hmemW⟩ = 0 := by
      have e : (⟨g * q.eval₂ φ₀ g - 1, hmemW⟩ : W) =
          ⟨g, hgW⟩ * (eval₂RingHom (φ₀.codRestrict W.toSubring hφW) ⟨g, hgW⟩ q) - 1 := by
        ext
        simp only [coe_eval₂RingHom]
        rw [eval₂_eq_sum_range, eval₂_eq_sum_range]
        simp
      rw [e, map_sub, map_mul, map_one, sub_eq_zero]
      have e2 : res W (eval₂RingHom (φ₀.codRestrict W.toSubring hφW) ⟨g, hgW⟩ q) =
          eval₂RingHom ρ₀ gb q := by
        rw [coe_eval₂RingHom, coe_eval₂RingHom, hom_eval₂]
      rw [e2]
      have := congrArg Subtype.val hq
      simpa [mul_comm] using this
    have hm : (⟨g * q.eval₂ φ₀ g - 1, hmemW⟩ : W) ∈ maximalIdeal W :=
      (residue_eq_zero_iff _).1 hres
    exact (ValuationSubring.valuation_lt_one_iff W _).1 hm
  obtain ⟨𝔐, h𝔐, hle⟩ := Ideal.exists_le_maximal _ hspan
  obtain ⟨V, hSV, hV, -⟩ :=
    _root_.SemistableReduction.exists_valuationSubring_of_isPrime S 𝔐
  refine ⟨composite W V, composite_le W V, fun o ↦ ⟨hφW o, hSV ⟨C o, eval₂_C _ _⟩⟩, ?_⟩
  exact composite_valuation_lt_one hgW (hV ⟨gb, hgS⟩ (hle (Ideal.mem_span_singleton_self _)))

end TemperedFundamentalGroups.SemistableReduction.CompositeValuation
