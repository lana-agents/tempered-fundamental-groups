/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Gauss

/-!
# Type-2 valuations of `K(X)` are Gauss valuations

Blueprint §9.3, W2. Let `K` be an algebraically closed field with a valuation `v`, and `w` a
valuation of `K(X)` (with values in the same group) extending `v`, whose value group is that of
`v` and whose residue field is transcendental over the residue field of `v`. Then `w` is a Gauss
valuation `gaussRat v a r` (`eq_gaussRat`).

Proof. First (`exists_residue_gaussLin_transcendental`) some `(X - a) / c` has transcendental
residue: otherwise the elements `ψ` with `ψ / λ` a unit of algebraic residue for some `λ ∈ K`
form a submonoid, closed under inverses, containing the constants and all `X - b` (as
`w(X - b) = v(c_b)`), hence every nonzero rational function (factor into linear factors); then
every residue is algebraic. Then (`eq_gaussRat_of_transcendental`) `w(X - b)` is computed from
`X - b = (X - a) + (a - b)`: if `v(a - b) = v(c)`, the residue of `(X - b) / c = (X - a) / c + e`
is `x̄ + ē ≠ 0` as `x̄` is transcendental. So `w(X - b) = max(v(a - b), v(c))`, which is the Gauss
value, and two valuations agreeing on constants and linear polynomials agree on `K(X)`.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section Ext

@[simp]
lemma ratFunc_algebraMap_C (c : K) :
    algebraMap K[X] (RatFunc K) (C c) = algebraMap K (RatFunc K) c := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), algebraMap_eq]

/-- Two valuations of `K(X)` agreeing on polynomials are equal. -/
lemma valuation_ratFunc_ext {w₁ w₂ : Valuation (RatFunc K) Γ₀}
    (h : ∀ p : K[X], w₁ (algebraMap K[X] _ p) = w₂ (algebraMap K[X] _ p)) : w₁ = w₂ := by
  ext φ
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) φ
  rw [map_div₀, map_div₀, h, h]

/-- Over an algebraically closed field, two valuations of `K(X)` agreeing on constants and on
the linear polynomials `X - b` are equal. -/
lemma valuation_ratFunc_ext_of_linear [IsAlgClosed K] {w₁ w₂ : Valuation (RatFunc K) Γ₀}
    (hC : ∀ c, w₁ (algebraMap K _ c) = w₂ (algebraMap K _ c))
    (hX : ∀ b, w₁ (algebraMap K[X] _ (X - C b)) = w₂ (algebraMap K[X] _ (X - C b))) :
    w₁ = w₂ := by
  refine valuation_ratFunc_ext fun p ↦ ?_
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := p))]
  simp only [map_mul, map_multiset_prod, Multiset.map_map, ratFunc_algebraMap_C, hC]
  congr 2
  exact Multiset.map_congr rfl fun b _ ↦ hX b

end Ext

namespace Gauss

variable {v : Valuation K Γ₀} {r : Γ₀ˣ}

lemma sup_X_add_C (e : K) : sup v r (X + C e) = max (v e) r := by
  apply le_antisymm
  · refine sup_le_iff.2 fun i ↦ ?_
    rcases eq_or_ne i 0 with rfl | hi0
    · simp [term]
    rcases eq_or_ne i 1 with rfl | hi1
    · simp [term]
    · simp [term, coeff_X, coeff_C, hi0, Ne.symm hi1]
  · refine max_le ?_ ?_
    · have := term_le_sup (v := v) (r := r) (X + C e) 0
      rwa [term, coeff_add, coeff_X_zero, coeff_C_zero, zero_add, pow_zero, mul_one] at this
    · have := term_le_sup (v := v) (r := r) (X + C e) 1
      rwa [term, coeff_add, coeff_X_one, coeff_C_succ, add_zero, map_one, one_mul,
        pow_one] at this

end Gauss

lemma gauss_X_sub_C (v : Valuation K Γ₀) (a : K) (r : Γ₀ˣ) (b : K) :
    gauss v a r (X - C b) = max (v (a - b)) r := by
  rw [gauss_apply, map_sub, taylor_X, taylor_C, add_sub_assoc, ← C_sub, Gauss.sup_X_add_C]

variable {v : Valuation K Γ₀} {w : Valuation (RatFunc K) Γ₀} [v.HasExtension w]

open ValuationResidue

/-- The residue of an element `algebraMap K L λ` lies in the image of the residue field of `v`. -/
lemma residue_algebraMap_mk {L Γ₁ : Type*} [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ₁] {w : Valuation L Γ₁} [v.HasExtension w] (c : K)
    (hc : v c ≤ 1) (h : algebraMap K L c ∈ w.valuationSubring) :
    residue w.valuationSubring ⟨algebraMap K L c, h⟩ =
      algebraMap (ResidueField v.valuationSubring) (ResidueField w.valuationSubring)
        (residue v.valuationSubring ⟨c, hc⟩) :=
  rfl

/-- **W2**, second half: if `(X - a) / c` has transcendental residue for `w`, then `w` is the
Gauss valuation of radius `v(c)` around `a`. -/
theorem eq_gaussRat_of_transcendental [IsAlgClosed K]
    (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) {a c : K} (hc0 : c ≠ 0)
    (hy : algebraMap K[X] (RatFunc K) (gaussLin a c) ∈ w.valuationSubring)
    (htr : Transcendental (ResidueField v.valuationSubring)
      (residue w.valuationSubring ⟨_, hy⟩)) :
    w = gaussRat v a (Units.mk0 (v c) (by simpa using hc0)) := by
  set r : Γ₀ˣ := Units.mk0 (v c) (by simpa using hc0)
  set y := algebraMap K[X] (RatFunc K) (gaussLin a c)
  have hy1 : w y = 1 := (residue_ne_zero_iff _).1 fun h0 ↦ htr (by rw [h0]; exact isAlgebraic_zero)
  have hXa : algebraMap K[X] (RatFunc K) (X - C a) = algebraMap K (RatFunc K) c * y := by
    rw [← ratFunc_algebraMap_C, ← map_mul, gaussLin, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hc0, C_1, one_mul]
  have hwXa : w (algebraMap K[X] (RatFunc K) (X - C a)) = v c := by
    rw [hXa, map_mul, hw, hy1, mul_one]
  refine valuation_ratFunc_ext_of_linear (fun e ↦ by rw [hw, gaussRat_algebraMap_C])
    fun b ↦ ?_
  rw [gaussRat_algebraMap, gauss_X_sub_C, Units.val_mk0]
  have hsplit : algebraMap K[X] (RatFunc K) (X - C b) =
      algebraMap K[X] (RatFunc K) (X - C a) + algebraMap K (RatFunc K) (a - b) := by
    rw [← ratFunc_algebraMap_C, ← map_add, C_sub]
    ring_nf
  rcases lt_trichotomy (v (a - b)) (v c) with h | h | h
  · rw [hsplit, Valuation.map_add_eq_of_lt_left _ (by rwa [hw, hwXa]), hwXa, max_eq_right h.le]
  · -- the residue of `(X - b) / c = y + e` is `x̄ + ē ≠ 0`
    set e := (a - b) / c
    have he : v e = 1 := by
      rw [map_div₀, h, div_self (by simpa using hc0)]
    have hye : algebraMap K[X] (RatFunc K) (X - C b) =
        algebraMap K (RatFunc K) c * (y + algebraMap K (RatFunc K) e) := by
      rw [hsplit, hXa, mul_add, ← map_mul, mul_div_cancel₀ _ hc0]
    have heO : algebraMap K (RatFunc K) e ∈ w.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, hw, he]
    have hsum : w (y + algebraMap K (RatFunc K) e) = 1 := by
      have hmem : y + algebraMap K (RatFunc K) e ∈ w.valuationSubring := add_mem hy heO
      refine (residue_ne_zero_iff ⟨_, hmem⟩).1 fun h0 ↦ htr ?_
      have : (⟨_, hmem⟩ : w.valuationSubring) = ⟨y, hy⟩ + ⟨_, heO⟩ := rfl
      rw [this, map_add, add_eq_zero_iff_eq_neg, residue_algebraMap_mk e he.le] at h0
      rw [h0]
      exact (isAlgebraic_algebraMap _).neg
    rw [hye, map_mul, hw, hsum, mul_one, h, max_self]
  · rw [hsplit, Valuation.map_add_eq_of_lt_right _ (by rwa [hw, hwXa]), hw, max_eq_left h.le]

/-- **W2**, first half: if the residue field of `w` is transcendental over that of `v` and the
value group of `w` is that of `v`, then some `(X - a) / c` has transcendental residue. -/
theorem exists_residue_gaussLin_transcendental [IsAlgClosed K]
    (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) (hΓ : ∀ f : RatFunc K, ∃ c : K, w f = v c)
    (htr : Algebra.Transcendental (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring)) :
    ∃ a c : K, c ≠ 0 ∧ ∃ hy : algebraMap K[X] (RatFunc K) (gaussLin a c) ∈ w.valuationSubring,
      Transcendental (ResidueField v.valuationSubring) (residue w.valuationSubring ⟨_, hy⟩) := by
  by_contra! H
  set κv := ResidueField v.valuationSubring
  -- the rational functions which are a constant times a unit with algebraic residue
  let S : Submonoid (RatFunc K) :=
    { carrier := {ψ | ∃ l : K, l ≠ 0 ∧ ∃ h : ψ * algebraMap K _ l⁻¹ ∈ w.valuationSubring,
        w (ψ * algebraMap K _ l⁻¹) = 1 ∧ IsAlgebraic κv (residue w.valuationSubring ⟨_, h⟩)}
      one_mem' := ⟨1, one_ne_zero, by simp, by simp, by
        have : (⟨1 * algebraMap K (RatFunc K) 1⁻¹, by simp⟩ :
          w.valuationSubring) = 1 := Subtype.ext (by simp)
        rw [this, map_one]
        exact isAlgebraic_one⟩
      mul_mem' := by
        rintro ψ₁ ψ₂ ⟨l₁, hl₁, h₁, hw₁, ha₁⟩ ⟨l₂, hl₂, h₂, hw₂, ha₂⟩
        have heq : ψ₁ * ψ₂ * algebraMap K (RatFunc K) (l₁ * l₂)⁻¹ =
            ψ₁ * algebraMap K _ l₁⁻¹ * (ψ₂ * algebraMap K _ l₂⁻¹) := by
          rw [mul_inv, map_mul]
          ring
        have hmem : ψ₁ * ψ₂ * algebraMap K (RatFunc K) (l₁ * l₂)⁻¹ ∈ w.valuationSubring := by
          rw [heq]
          exact mul_mem h₁ h₂
        refine ⟨l₁ * l₂, mul_ne_zero hl₁ hl₂, hmem, by rw [heq, map_mul, hw₁, hw₂, one_mul], ?_⟩
        have : (⟨_, hmem⟩ : w.valuationSubring) = ⟨_, h₁⟩ * ⟨_, h₂⟩ := Subtype.ext heq
        rw [this, map_mul]
        exact ha₁.mul ha₂ }
  -- `S` is closed under inverses
  have hinv : ∀ ψ ∈ S, ψ⁻¹ ∈ S := by
    rintro ψ ⟨l, hl, h, hw', ha⟩
    have heq : ψ⁻¹ * algebraMap K (RatFunc K) l⁻¹⁻¹ = (ψ * algebraMap K _ l⁻¹)⁻¹ := by
      rw [mul_inv, map_inv₀, map_inv₀]
    have hmem : ψ⁻¹ * algebraMap K (RatFunc K) l⁻¹⁻¹ ∈ w.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, heq, map_inv₀, hw', inv_one]
    refine ⟨l⁻¹, inv_ne_zero hl, hmem, by rw [heq, map_inv₀, hw', inv_one], ?_⟩
    have : residue w.valuationSubring ⟨_, hmem⟩ = (residue w.valuationSubring ⟨_, h⟩)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      have hne : ψ * algebraMap K (RatFunc K) l⁻¹ ≠ 0 := by
        intro h0
        rw [h0, map_zero] at hw'
        exact zero_ne_one hw'
      have h1 : (ψ⁻¹ * algebraMap K (RatFunc K) l⁻¹⁻¹) * (ψ * algebraMap K _ l⁻¹) = 1 := by
        rw [heq, inv_mul_cancel₀ hne]
      rw [← map_mul, ← map_one (residue _)]
      exact congrArg _ (Subtype.ext h1)
    rw [this]
    exact ha.inv
  -- `S` contains the nonzero constants
  have hconst : ∀ l : K, l ≠ 0 → algebraMap K (RatFunc K) l ∈ S := by
    intro l hl
    have heq : algebraMap K (RatFunc K) l * algebraMap K _ l⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hl, map_one]
    have hmem : algebraMap K (RatFunc K) l * algebraMap K _ l⁻¹ ∈ w.valuationSubring := by
      rw [heq]
      exact one_mem _
    refine ⟨l, hl, hmem, by rw [heq, map_one], ?_⟩
    have : (⟨_, hmem⟩ : w.valuationSubring) = 1 := Subtype.ext heq
    rw [this, map_one]
    exact isAlgebraic_one
  -- `S` contains the linear polynomials
  have hlin : ∀ b : K, algebraMap K[X] (RatFunc K) (X - C b) ∈ S := by
    intro b
    obtain ⟨c, hc⟩ := hΓ (algebraMap K[X] (RatFunc K) (X - C b))
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero, Valuation.zero_iff] at hc
      exact X_sub_C_ne_zero b (IsFractionRing.injective K[X] (RatFunc K) (by simpa using hc))
    have heq : algebraMap K[X] (RatFunc K) (X - C b) * algebraMap K _ c⁻¹ =
        algebraMap K[X] (RatFunc K) (gaussLin b c) := by
      rw [gaussLin, map_mul, ratFunc_algebraMap_C, mul_comm]
    have hw1 : w (algebraMap K[X] (RatFunc K) (gaussLin b c)) = 1 := by
      rw [← heq, map_mul, hc, hw, map_inv₀, mul_inv_cancel₀ (by simpa using hc0)]
    have hmem : algebraMap K[X] (RatFunc K) (gaussLin b c) ∈ w.valuationSubring := hw1.le
    refine ⟨c, hc0, heq ▸ hmem, by rw [heq, hw1], ?_⟩
    have := H b c hc0 hmem
    rw [Transcendental, not_not] at this
    convert this using 3
  -- hence every nonzero rational function
  have hall : ∀ ψ : RatFunc K, ψ ≠ 0 → ψ ∈ S := by
    have hpoly : ∀ p : K[X], p ≠ 0 → algebraMap K[X] (RatFunc K) p ∈ S := by
      intro p hp
      rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
        (IsAlgClosed.card_roots_eq_natDegree (p := p)), map_mul, map_multiset_prod,
        ratFunc_algebraMap_C, Multiset.map_map]
      refine S.mul_mem (hconst _ (leadingCoeff_ne_zero.2 hp)) (S.multiset_prod_mem _ ?_)
      intro q hq
      obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hq
      exact hlin b
    intro ψ hψ
    obtain ⟨f, g, hg, rfl⟩ := IsFractionRing.div_surjective (A := K[X]) ψ
    have hf : f ≠ 0 := by
      rintro rfl
      simp at hψ
    rw [div_eq_mul_inv]
    exact S.mul_mem (hpoly f hf) (hinv _ (hpoly g (nonZeroDivisors.ne_zero hg)))
  -- contradiction with the transcendence of the residue field
  obtain ⟨z, hz⟩ := Algebra.transcendental_def.1 htr
  obtain ⟨φ, rfl⟩ := residue_surjective z
  have hφ0 : (φ : RatFunc K) ≠ 0 := by
    intro h0
    have : φ = 0 := Subtype.ext h0
    rw [this, map_zero] at hz
    exact hz isAlgebraic_zero
  obtain ⟨l, hl, h, hw', ha⟩ := hall φ hφ0
  have hvl : v l ≤ 1 := by
    have h1 := hw'
    simp only [map_mul, map_inv₀, hw] at h1
    rw [mul_inv_eq_one₀ (by simpa using hl)] at h1
    rw [← h1]
    exact φ.2
  have hlO : algebraMap K (RatFunc K) l ∈ w.valuationSubring := by
    rw [Valuation.mem_valuationSubring_iff, hw]
    exact hvl
  have : φ = ⟨_, h⟩ * ⟨_, hlO⟩ := Subtype.ext (by
    change (φ : RatFunc K) = _ * _ * _
    rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hl, map_one, mul_one])
  rw [this, map_mul, residue_algebraMap_mk l hvl] at hz
  exact hz (ha.mul (isAlgebraic_algebraMap _))

/-- **W2**: over an algebraically closed field `K`, a valuation `w` of `K(X)` extending `v`, with
the value group of `v` and residue field transcendental over that of `v` (e.g. of transcendence
degree `1`), is a Gauss valuation `gaussRat v a r`. -/
theorem eq_gaussRat [IsAlgClosed K] (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c)
    (hΓ : ∀ f : RatFunc K, ∃ c : K, w f = v c)
    (htr : Algebra.Transcendental (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring)) :
    ∃ (a : K) (r : Γ₀ˣ), w = gaussRat v a r := by
  obtain ⟨a, c, hc0, hy, htr'⟩ := exists_residue_gaussLin_transcendental hw hΓ htr
  exact ⟨a, _, eq_gaussRat_of_transcendental hw hc0 hy htr'⟩

end SemistableReduction
