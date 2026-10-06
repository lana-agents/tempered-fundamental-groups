/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XLengthUnfolded
import TemperedFundamentalGroups.SemistableReduction.XResidue

/-!
# Nodes over nodes: restriction of monomial points (Blueprint §9.7, X1, XL8)

Let `ψ : c ⟶ c'` be a map of models (function fields `L₂ ⊆ L₁`, constants `K₂`, `K₁`), `z` a node
of `c` over a node `y'` of `c'`: the germs `Q` of `c'` at `y'` map into the germs `P` of `c` at `z`
(`ModelCode.germs_map`), and in `P` the coordinate `u'` of `y'` is `u' = ε u ^ p ϖ₁ ^ r` (`ε` a unit
of `P`, the divisor lemma). Then the interior monomial points of the node `z` restrict to
interior monomial points of `y'`, at the parameter `(r + p s) f₂ / f₁` where
`ϖ₂ ^ f₂ = ζ ϖ₁ ^ f₁` (`NodeGerm.isMonomialPt_comap`): the segment of `z` maps monotonically into
the segment of `y'`.
-/

open Polynomial

namespace SemistableReduction

variable {K₁ K₂ L₁ L₂ : Type*} [Field K₁] [Field K₂] [Field L₁] [Field L₂] [Algebra K₁ L₁]
  [Algebra K₂ L₂] [Algebra L₂ L₁] [Algebra K₂ L₁] [IsScalarTower K₂ L₂ L₁]
  {O₁ : ValuationSubring K₁} [IsDiscreteValuationRing O₁] {ϖ₁ : O₁}
  {O₂ : ValuationSubring K₂} [IsDiscreteValuationRing O₂] {ϖ₂ : O₂}

/-- **Monomial points of a node over a node restrict to monomial points** (XL8, interior points).
-/
theorem NodeGerm.isMonomialPt_comap {P : Subring L₁} {u v : L₁} {n : ℕ}
    (h : NodeGerm O₁ ϖ₁ P u v n) (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂) {Q : Set L₂}
    (hQP : ∀ q ∈ Q, algebraMap L₂ L₁ q ∈ P) (hO₂Q : ∀ o : O₂, algebraMap K₂ L₂ (o : K₂) ∈ Q)
    (halg : ∀ k : K₂, IsAlgebraic K₁ (algebraMap K₂ L₁ k))
    {u' ε : L₁} {u₂ : L₂} (hu₂ : algebraMap L₂ L₁ u₂ = u') {p r : ℕ} (hp : 1 ≤ p)
    (hε : ε ∈ P) (hε' : ε⁻¹ ∈ P) (hε0 : ε ≠ 0)
    (hu' : u' = ε * u ^ p * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ r)
    {ζ : L₁} {f₁ f₂ : ℕ} (hf₁ : 0 < f₁) (hf₂ : 0 < f₂) (hζ : ζ ∈ P) (hζ' : ζ⁻¹ ∈ P)
    (hζ0 : ζ ≠ 0)
    (hϖ : algebraMap K₂ L₁ (ϖ₂ : K₂) ^ f₂ = ζ * algebraMap K₁ L₁ (ϖ₁ : K₁) ^ f₁)
    {s : ℚ} (hs0 : 0 < s) (hsn : s < n) {U : ValuationSubring L₁}
    (hU : IsMonomialPt O₁ (P : Set L₁) (algebraMap K₁ L₁ (ϖ₁ : K₁)) u s U) :
    IsMonomialPt O₂ Q (algebraMap K₂ L₂ (ϖ₂ : K₂)) u₂ ((r + p * s) * f₂ / f₁)
      (U.comap (algebraMap L₂ L₁)) := by
  classical
  set φ := algebraMap L₂ L₁
  set p₁ := algebraMap K₁ L₁ (ϖ₁ : K₁) with hp₁
  set p₂ := algebraMap K₂ L₁ (ϖ₂ : K₂) with hp₂
  have hφϖ : φ (algebraMap K₂ L₂ (ϖ₂ : K₂)) = p₂ := (IsScalarTower.algebraMap_apply _ _ _ _).symm
  have hUO := h.comap_eq hϖ₁ hU
  obtain ⟨hwp0, hwp1⟩ := valuation_uniformizer hUO hϖ₁
  have hϖ₂0 : (ϖ₂ : K₂) ≠ 0 := by exact_mod_cast hϖ₂.ne_zero
  have hp₂0 : p₂ ≠ 0 := by simpa [p₂] using hϖ₂0
  have hεv : U.valuation ε = 1 :=
    (valuation_eq_one_iff_mem_and_inv_mem U).mpr ⟨hε0, hU.1 hε, hU.1 hε'⟩
  have hζv : U.valuation ζ = 1 :=
    (valuation_eq_one_iff_mem_and_inv_mem U).mpr ⟨hζ0, hU.1 hζ, hU.1 hζ'⟩
  have hp₂v : U.valuation p₂ ^ f₂ = U.valuation p₁ ^ f₁ := by
    rw [← map_pow, hϖ, map_mul, hζv, one_mul, map_pow]
  have hp₂1 : U.valuation p₂ < 1 := by
    by_contra hge
    push Not at hge
    have : 1 ≤ U.valuation p₁ ^ f₁ := hp₂v ▸ one_le_pow₀ hge
    exact absurd this (not_le.mpr (pow_lt_one₀ zero_le hwp1 hf₁.ne'))
  have hO₂U : U.comap (algebraMap K₂ L₁) = O₂ := by
    refine comap_eq_of_lt_one hϖ₂ (fun o ↦ ?_) hp₂1
    rw [IsScalarTower.algebraMap_apply K₂ L₂ L₁]
    exact hU.1 (hQP _ (hO₂Q o))
  refine ⟨fun q hq ↦ hU.1 (hQP q hq), ?_, ?_, ?_⟩
  · -- `ϖ₂` is not a unit
    set x := algebraMap K₂ L₂ (ϖ₂ : K₂)
    have hx0 : x ≠ 0 := by simpa [x] using hϖ₂0
    have hxU : x ∈ U.comap φ := by
      rw [ValuationSubring.mem_comap, hφϖ]
      exact (U.valuation_le_one_iff _).mp hp₂1.le
    refine lt_of_le_of_ne ((U.comap φ).valuation_le_one_iff x |>.mpr hxU) fun h1 ↦ ?_
    obtain ⟨-, -, hinv⟩ := (valuation_eq_one_iff_mem_and_inv_mem _).mp h1
    rw [ValuationSubring.mem_comap, map_inv₀, hφϖ, ← U.valuation_le_one_iff, map_inv₀] at hinv
    exact absurd (one_le_of_inv_le_one (by simpa using hp₂0) hinv) (not_le.mpr hp₂1)
  · -- the parameter
    have hx0 : algebraMap K₂ L₂ (ϖ₂ : K₂) ≠ 0 := by simpa using hϖ₂0
    refine IsLogValue.comap hx0 ?_
    rw [hφϖ, hu₂]
    have hlog := hU.2.2.1
    unfold IsLogValue at hlog
    have hD : 0 < s.den * f₁ := Nat.mul_pos s.den_pos hf₁
    have h1 : U.valuation u' ^ s.den = U.valuation p₁ ^ ((r * s.den + p * s.num : ℤ)) := by
      rw [hu', map_mul, map_mul, hεv, one_mul, map_pow, map_pow, mul_pow, ← pow_mul,
        mul_comm p, pow_mul, hlog, ← pow_mul, ← zpow_natCast (U.valuation p₁) (r * s.den),
        ← zpow_natCast (U.valuation p₁ ^ s.num) p, ← zpow_mul, ← zpow_add₀ hwp0]
      congr 1
      push_cast
      ring
    have key : U.valuation u' ^ (s.den * f₁) =
        U.valuation p₂ ^ (((f₂ : ℤ) * (r * s.den + p * s.num))) := by
      rw [pow_mul, h1, ← zpow_natCast, ← zpow_mul, mul_comm _ (f₁ : ℤ), zpow_mul, zpow_natCast,
        ← hp₂v, ← zpow_natCast, ← zpow_mul]
    have := IsLogValue.of_pow_eq hD key
    convert this using 1
    have hd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
    have hf : (f₁ : ℚ) ≠ 0 := by exact_mod_cast hf₁.ne'
    conv_lhs => rw [← Rat.num_div_den s]
    push_cast
    field_simp
  · -- residue transcendence
    set s' : ℚ := (r + p * s) * f₂ / f₁ with hs'
    have hs'0 : 0 < s' := by
      have : (0 : ℚ) < (r + p * s) := by
        have : (1 : ℚ) ≤ p := by exact_mod_cast hp
        positivity
      positivity
    set D := s.den
    set Nn := s.num.toNat
    have hNn : (Nn : ℤ) = s.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hs0).le
    set D' := s'.den
    set N'n := s'.num.toNat
    have hN'n : (N'n : ℤ) = s'.num := Int.toNat_of_nonneg (Rat.num_pos.mpr hs'0).le
    -- the exponent identity `f₁ N' D = D' f₂ (r D + p N)`
    have hexp : f₁ * N'n * D = D' * f₂ * (r * D + p * Nn) := by
      have h1 : (s'.num : ℚ) = s' * D' := s'.mul_den_eq_num.symm
      have h2 : (s.num : ℚ) = s * D := s.mul_den_eq_num.symm
      have hd : (D : ℚ) ≠ 0 := by exact_mod_cast s.den_nz
      have hf : (f₁ : ℚ) ≠ 0 := by exact_mod_cast hf₁.ne'
      have : ((f₁ * N'n * D : ℕ) : ℚ) = ((D' * f₂ * (r * D + p * Nn) : ℕ) : ℚ) := by
        push_cast
        rw [show (N'n : ℚ) = ((N'n : ℤ) : ℚ) by norm_cast, hN'n, h1,
          show (Nn : ℚ) = ((Nn : ℤ) : ℚ) by norm_cast, hNn, h2, hs']
        field_simp
      exact_mod_cast this
    -- the twisting unit
    set w : L₁ := ε ^ (D' * f₂ * D) * ζ⁻¹ ^ (N'n * D)
    have hwP : w ∈ P := P.mul_mem (P.pow_mem hε _) (P.pow_mem hζ' _)
    have hw1 : U.valuation w = 1 := by
      simp only [w, map_mul, map_pow, map_inv₀, hεv, hζv, one_pow, inv_one, mul_one]
    obtain ⟨g1, g2, g3⟩ := generator_bounds h.mul_eq hUO hϖ₁ hs0 hsn hU.2.2.1
    have hlt1 : ∀ y, U.valuation y ^ s.den ≤ U.valuation p₁ → U.valuation y < 1 := by
      intro y hy
      by_contra hge
      push Not at hge
      exact absurd ((one_le_pow₀ hge).trans hy) (not_le.mpr hwp1)
    obtain ⟨o, a₁, ha₁, b₁, hb₁, c₁, hc₁, hwd⟩ := h.gen w hwP
    have hle1 : ∀ z ∈ P, U.valuation z ≤ 1 := fun z hz ↦ (U.valuation_le_one_iff z).mpr (hU.1 hz)
    have hwo : U.valuation (w - algebraMap K₁ L₁ (o : K₁)) < 1 := by
      have : w - algebraMap K₁ L₁ (o : K₁) = p₁ * a₁ + u * b₁ + v * c₁ := by rw [hwd]; ring
      rw [this]
      refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt
        (Valuation.map_add _ _ _) (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
      · exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hle1 _ ha₁)) hwp1
      · exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hle1 _ hb₁)) (hlt1 u g2)
      · exact lt_of_le_of_lt (mul_le_of_le_one_right zero_le (hle1 _ hc₁)) (hlt1 v g3)
    have ho1 : U.valuation (algebraMap K₁ L₁ (o : K₁)) = 1 := by
      have : algebraMap K₁ L₁ (o : K₁) = w - (w - algebraMap K₁ L₁ (o : K₁)) := by ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (by rw [hw1]; exact hwo), hw1]
    have hou : IsUnit o := by
      obtain ⟨ho0, -, hinv⟩ := (valuation_eq_one_iff_mem_and_inv_mem U).mp ho1
      rw [← map_inv₀, ← ValuationSubring.mem_comap, hUO] at hinv
      have ho0' : (o : K₁) ≠ 0 := fun h ↦ ho0 (by rw [h, map_zero])
      exact IsUnit.of_mul_eq_one (⟨_, hinv⟩ : O₁) (Subtype.ext (by simp [ho0']))
    set k := p * D' * f₂
    have hk : 1 ≤ k := Nat.mul_pos (Nat.mul_pos hp s'.den_pos) hf₂
    have htrk := hU.2.2.2.mul_pow hUO hk hou hwo
    -- the identity `(u' ^ D' / p₂ ^ N') ^ (f₂ D) = w g ^ k`
    set z : L₂ := u₂ ^ s'.den / algebraMap K₂ L₂ (ϖ₂ : K₂) ^ s'.num
    have hφz : φ z = u' ^ D' / p₂ ^ N'n := by
      simp only [z, map_div₀, map_pow, map_zpow₀, hu₂, hφϖ]
      rw [← hN'n, zpow_natCast]
    have hp₁0 : p₁ ≠ 0 := by simpa [p₁] using (show (ϖ₁ : K₁) ≠ 0 by exact_mod_cast hϖ₁.ne_zero)
    have hu0 : u ≠ 0 := by
      intro hu0
      have := hU.2.2.1
      unfold IsLogValue at this
      rw [hu0, map_zero, zero_pow s.den_nz] at this
      exact zpow_ne_zero _ hwp0 this.symm
    have hid : (φ z) ^ (f₂ * D) = w * (u ^ s.den / p₁ ^ s.num) ^ k := by
      rw [hφz, ← hNn, zpow_natCast, div_pow, ← pow_mul, ← pow_mul, show N'n * (f₂ * D) =
        f₂ * (N'n * D) by ring, pow_mul p₂ f₂ (N'n * D), hϖ, mul_pow, ← pow_mul,
        show f₁ * (N'n * D) = f₁ * N'n * D by ring, hexp, hu']
      simp only [w, k, inv_pow]
      field_simp
      rw [show s.den = D from rfl, div_pow]
      field_simp
      ring
    have hφzU : φ z ∈ U := by
      have hv : U.valuation (φ z) ^ (f₂ * D) = 1 := by
        rw [← map_pow, hid, map_mul, hw1, one_mul, map_pow]
        have hg1 : U.valuation (u ^ s.den / p₁ ^ s.num) = 1 := by
          have := hU.2.2.2.2 X (by simp)
          simpa using this
        rw [hg1, one_pow]
      have hpos : f₂ * D ≠ 0 := (Nat.mul_pos hf₂ s.den_pos).ne'
      refine (U.valuation_le_one_iff _).mp ?_
      by_contra hgt
      push Not at hgt
      exact absurd hv (ne_of_gt (one_lt_pow₀ hgt hpos))
    have h₁ : IsResidueTranscendental O₁ U (φ z) := by
      refine IsResidueTranscendental.of_pow hUO hφzU (M := f₂ * D) ?_
      rw [hid]; exact htrk
    have h₂ := h₁.of_algebraic hUO hO₂U halg
    exact IsResidueTranscendental.comap (F := L₂) (E := L₁) h₂

end SemistableReduction
