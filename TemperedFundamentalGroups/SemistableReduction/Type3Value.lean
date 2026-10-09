/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Approx
import TemperedFundamentalGroups.SemistableReduction.Type3Galois

/-!
# The value group at an extension of a type-3 point

Blueprint §9.10a (II.2). Let `ξ` be an extension of the type-3 Gauss valuation `w_{0,ρ}` to `F'`.

* `ramificationIdx_le_of_gen`: if the value group of `w` is generated over the values of `K` by
  `w(z)` and `w(z)ʲ` is a value of `K`, then `e ≤ |j|`;
* **`exists_coord_value`**: there are `d ≥ e(ξ)`, `z ∈ F'` and `c ∈ C^×` with `ξ(z)ᵈ ρ = |c|`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace Type3

open FundamentalInequality GaussStability TypeThree GaussTube

section ValueGroup

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ]

/-- **A cyclic bound on the ramification index.** -/
lemma ramificationIdx_le_of_gen [FiniteDimensional K L] (w : Valuation L Γ) {z : L} (hz : z ≠ 0)
    (hgen : ∀ v : L, v ≠ 0 → ∃ (b : K) (t : ℤ), w v = w (algebraMap K L b) * w z ^ t)
    {j : ℤ} (hj : j ≠ 0) (hzj : ∃ b : K, w z ^ j = w (algebraMap K L b)) :
    ramificationIdx K w ≤ j.natAbs := by
  set H := valueGroup (w.comap (algebraMap K L))
  set G := valueGroup w
  have hwz : w z ≠ 0 := (Valuation.ne_zero_iff w).2 hz
  set g₀ : G := ⟨Units.mk0 (w z) hwz, valuation_mem_valueGroup w hz⟩
  set Hs := H.subgroupOf G
  set q : G ⧸ Hs := QuotientGroup.mk g₀
  have hval : ∀ t : ℤ, (((g₀ ^ t : G) : Γˣ) : Γ) = w z ^ t := fun t ↦ by
    rw [Subgroup.coe_zpow, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  have hall : ∀ x : G ⧸ Hs, x ∈ Subgroup.zpowers q := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨v, hv⟩ := g.2
    have hv0 : v ≠ 0 := by
      rintro rfl
      rw [map_zero] at hv
      exact (g.1.ne_zero) hv.symm
    obtain ⟨b, t, hbt⟩ := hgen v hv0
    refine Subgroup.mem_zpowers_iff.2 ⟨t, ?_⟩
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    refine ⟨b, ?_⟩
    rw [Valuation.comap_apply, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
      Units.val_inv_eq_inv_val, hval, ← hv, hbt]
    have : w z ^ t ≠ 0 := zpow_ne_zero t hwz
    field_simp
  have hcard : ramificationIdx K w = orderOf q := by
    rw [← Nat.card_zpowers q, (eq_top_iff.2 fun x _ ↦ hall x : Subgroup.zpowers q = ⊤),
      Subgroup.card_top]
    rfl
  have hqj : q ^ j = 1 := by
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    obtain ⟨b, hb⟩ := hzj
    refine ⟨b, ?_⟩
    rw [Valuation.comap_apply, hval, hb]
  have hqn : q ^ j.natAbs = 1 := by
    rcases Int.natAbs_eq j with h | h
    · rw [h, zpow_natCast] at hqj; exact hqj
    · rw [h, zpow_neg, inv_eq_one, zpow_natCast] at hqj; exact hqj
  rw [hcard]
  exact orderOf_le_of_pow_eq_one (Int.natAbs_pos.2 hj) hqn

end ValueGroup

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- **A coordinate value at an extension of a type-3 point**: there are `d ≥ e(ξ)`, `z` and
`c ≠ 0` with `ξ(z)ᵈ ρ = |c|`. -/
theorem exists_coord_value {ρ : ℝ≥0} (hρ : IsIrrat C ρ) {ρu : ℝ≥0ˣ} (hρu : (ρu : ℝ≥0) = ρ)
    (ξ : GaussExtension (0 : C) ρu F') :
    ∃ (d : ℕ) (z : F') (c : C), 1 ≤ d ∧ ramificationIdx (RatFunc C) ξ.1 ≤ d ∧ c ≠ 0 ∧
      ξ.1 z ^ d * ρ = ‖c‖₊ := by
  set e := ramificationIdx (RatFunc C) ξ.1
  have he0 : 0 < e := Nat.pos_of_ne_zero (ramificationIdx_ne_zero ξ.1)
  have hρ0 : ρ ≠ 0 := hρ.pos.ne'
  have hw : ∀ b : RatFunc C, ξ.1 (algebraMap (RatFunc C) F' b) = w ρu b := fun b ↦ by
    rw [← Valuation.comap_apply, ξ.2]
  have hbase : ∀ b : RatFunc C, b ≠ 0 → ∃ (c : C) (m : ℤ), c ≠ 0 ∧ w ρu b = ‖c‖₊ * ρ ^ m := by
    intro b hb
    obtain ⟨c, hc, m, g, hbg, s₁, s₂, h₁, h₂, hg⟩ := exists_monomial hρ hb
    refine ⟨c, m, hc, ?_⟩
    rw [gaussRat_eq_of_monomial hbg (hg ρu (hρu ▸ h₁) (hρu ▸ h₂)), hρu]
  have hpow : ∀ v : F', v ≠ 0 → ∃ (c : C) (k : ℤ), c ≠ 0 ∧ ξ.1 v ^ e = ‖c‖₊ * ρ ^ k := by
    intro v hv
    obtain ⟨b, hb⟩ := exists_pow_ramificationIdx_eq (K := RatFunc C) ξ.1 hv
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero, map_zero] at hb
      exact pow_ne_zero e ((Valuation.ne_zero_iff ξ.1).2 hv) hb
    obtain ⟨c, k, hc, hck⟩ := hbase b hb0
    exact ⟨c, k, hc, by rw [hb, hw, hck]⟩
  let S : AddSubgroup ℤ :=
    { carrier := {k | ∃ (v : F') (c : C), v ≠ 0 ∧ c ≠ 0 ∧ ξ.1 v ^ e = ‖c‖₊ * ρ ^ k}
      zero_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨v, c, hv, hc, h⟩ ⟨v', c', hv', hc', h'⟩
        exact ⟨v * v', c * c', mul_ne_zero hv hv', mul_ne_zero hc hc', by
          rw [map_mul, mul_pow, h, h', nnnorm_mul, zpow_add₀ hρ0]; ring⟩
      neg_mem' := by
        rintro a ⟨v, c, hv, hc, h⟩
        exact ⟨v⁻¹, c⁻¹, inv_ne_zero hv, inv_ne_zero hc, by
          rw [map_inv₀, inv_pow, h, nnnorm_inv, zpow_neg, mul_inv]⟩ }
  obtain ⟨⟨dd, hdS⟩, hgenS⟩ := IsAddCyclic.exists_generator (α := S)
  obtain ⟨z, c₀, hz, hc₀, hzd⟩ := hdS
  have hξz : ξ.1 z ≠ 0 := (Valuation.ne_zero_iff ξ.1).2 hz
  -- every value is `|c| ξ(z)ᵗ`
  have hgen : ∀ v : F', v ≠ 0 → ∃ (c : C) (t : ℤ), ξ.1 v = ‖c‖₊ * ξ.1 z ^ t := by
    intro v hv
    obtain ⟨c, k, hc, hck⟩ := hpow v hv
    obtain ⟨t, ht⟩ := AddSubgroup.mem_zmultiples_iff.1 (hgenS ⟨k, v, c, hv, hc, hck⟩)
    have htk : t * dd = k := by
      have := congrArg Subtype.val ht
      simpa using this
    have hzt0 : ξ.1 z ^ t ≠ 0 := zpow_ne_zero t hξz
    have key : (ξ.1 v / ξ.1 z ^ t) ^ e = ‖c / c₀ ^ t‖₊ := by
      have hzt : (ξ.1 z ^ t) ^ e = ‖c₀‖₊ ^ t * ρ ^ k := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzd, mul_zpow,
          ← zpow_mul, mul_comm dd t, htk]
      have hc₀t : ‖c₀‖₊ ^ t ≠ 0 := zpow_ne_zero t (nnnorm_ne_zero_iff.2 hc₀)
      rw [div_pow, hck, hzt, nnnorm_div, nnnorm_zpow]
      have : ρ ^ k ≠ 0 := zpow_ne_zero k hρ0
      field_simp
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (c / c₀ ^ t) he0
    refine ⟨b, t, ?_⟩
    have : ξ.1 v / ξ.1 z ^ t = ‖b‖₊ := by
      refine (pow_left_inj₀ zero_le zero_le he0.ne').1 ?_
      rw [key, ← nnnorm_pow, hb]
    rw [← this, div_mul_cancel₀ _ hzt0]
  -- the coordinate `x`
  have hx0 : algebraMap (RatFunc C) F' RatFunc.X ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc C) F').injective).2 RatFunc.X_ne_zero
  obtain ⟨c₁, j, hc₁j⟩ := hgen _ hx0
  rw [hw, gaussRat_X, hρu] at hc₁j
  have hc₁ : c₁ ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero, zero_mul] at hc₁j
    exact hρ0 hc₁j
  have hj : j ≠ 0 := by
    rintro rfl
    rw [zpow_zero, mul_one] at hc₁j
    exact hρ c₁ hc₁j.symm
  have hle : e ≤ j.natAbs := by
    refine ramificationIdx_le_of_gen ξ.1 hz (fun v hv ↦ ?_) hj
      ⟨RatFunc.X / algebraMap C (RatFunc C) c₁, ?_⟩
    · obtain ⟨c, t, hct⟩ := hgen v hv
      exact ⟨algebraMap C (RatFunc C) c, t, by rw [hw, gaussRat_C, hct]⟩
    · rw [hw, map_div₀, gaussRat_X, gaussRat_C, hρu, hc₁j]
      field_simp [nnnorm_ne_zero_iff.2 hc₁]
  rcases Int.natAbs_eq j with h | h
  · refine ⟨j.natAbs, z⁻¹, c₁, Int.natAbs_pos.2 hj, hle, hc₁, ?_⟩
    rw [map_inv₀, inv_pow, ← zpow_natCast, ← h, hc₁j, ← mul_assoc, mul_comm _ ‖c₁‖₊,
      mul_assoc, inv_mul_cancel₀ (zpow_ne_zero j hξz), mul_one]
  · refine ⟨j.natAbs, z, c₁, Int.natAbs_pos.2 hj, hle, hc₁, ?_⟩
    have h0 : (j.natAbs : ℤ) + j = 0 := by omega
    rw [hc₁j, ← zpow_natCast, mul_left_comm, ← zpow_add₀ hξz, h0, zpow_zero, mul_one]

end Type3

end SemistableReduction
