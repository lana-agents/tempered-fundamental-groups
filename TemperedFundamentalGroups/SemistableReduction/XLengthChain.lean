/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XLengthCoord

/-!
# Transport of chains under change of node coordinates (Blueprint §9.7, XL5)

* `isXLength_scale_iff`: `u ↦ ε u ^ e`, `n ↦ n e` (chains rescaled by `e`);
* `isXLength_swap_iff`: `u ↔ v` (chains reversed).
-/

open Polynomial IsLocalRing

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] {ϖK : O} {P : Subring L} {u v : L} {n : ℕ} {ι : O →+* L}
  {W₁ W₂ : ValuationSubring L} {ϖ₀ x : L}

namespace NodeBranches

/-- Chains along `ε u ^ e` and along `u` have the same lengths. -/
theorem isXLength_scale_iff (H : NodeBranches O ϖK P ι u v n W₁ W₂) {ε : L} (hε : ε ∈ P)
    (hεi : ε⁻¹ ∈ P) (hε0 : ε ≠ 0) {e : ℕ} (he : 1 ≤ e)
    (hW₁' : IsMonomialPt O P (algebraMap K L ϖK) (ε * u ^ e) 0 W₁)
    (hW₂' : IsMonomialPt O P (algebraMap K L ϖK) (ε * u ^ e) (n * e : ℕ) W₂) {l : ℚ} :
    IsXLength O P ϖ₀ (algebraMap K L ϖK) (ε * u ^ e) x (n * e) l ↔
      IsXLength O P ϖ₀ (algebraMap K L ϖK) u x n l := by
  have he0 : (0 : ℚ) < e := by exact_mod_cast he
  have hrange : Set.range (XChain.length (O' := O) (P := (P : Set L)) (ϖ := ϖ₀)
      (ϖ' := algebraMap K L ϖK) (u := ε * u ^ e) (x := x) (n := n * e)) =
      Set.range (XChain.length (O' := O) (P := (P : Set L)) (ϖ := ϖ₀)
      (ϖ' := algebraMap K L ϖK) (u := u) (x := x) (n := n)) := by
    ext l
    constructor
    · rintro ⟨γ, rfl⟩
      have hb : ∀ i, 0 ≤ γ.s i ∧ γ.s i ≤ ((n * e : ℕ) : ℚ) := fun i ↦
        ⟨γ.s_zero ▸ γ.strictMono.monotone (Fin.zero_le i),
          γ.s_last ▸ γ.strictMono.monotone (Fin.le_last i)⟩
      refine ⟨{ m := γ.m, s := fun i ↦ γ.s i / e, U := γ.U, U' := γ.U', a := γ.a, ρ := γ.ρ
                s_zero := by simp [γ.s_zero]
                s_last := by rw [γ.s_last]; push_cast; field_simp
                strictMono := fun i j hij ↦ div_lt_div_of_pos_right (γ.strictMono hij) he0
                isMonomialPt := fun i ↦ (H.mono_scale hε hεi hε0 he hW₁' hW₂' (hb i).1
                  (hb i).2).1 (γ.isMonomialPt i)
                comap_eq := γ.comap_eq
                isXGauss := γ.isXGauss }, rfl⟩
    · rintro ⟨γ, rfl⟩
      have hb : ∀ i, 0 ≤ γ.s i ∧ γ.s i ≤ n := fun i ↦
        ⟨γ.s_zero ▸ γ.strictMono.monotone (Fin.zero_le i),
          γ.s_last ▸ γ.strictMono.monotone (Fin.le_last i)⟩
      have hb' : ∀ i, 0 ≤ e * γ.s i ∧ e * γ.s i ≤ ((n * e : ℕ) : ℚ) := fun i ↦
        ⟨by have := (hb i).1; positivity, by
          push_cast; rw [mul_comm (n : ℚ)]; exact mul_le_mul_of_nonneg_left (hb i).2 he0.le⟩
      refine ⟨{ m := γ.m, s := fun i ↦ e * γ.s i, U := γ.U, U' := γ.U', a := γ.a, ρ := γ.ρ
                s_zero := by simp [γ.s_zero]
                s_last := by rw [γ.s_last]; push_cast; ring
                strictMono := fun i j hij ↦ mul_lt_mul_of_pos_left (γ.strictMono hij) he0
                isMonomialPt := fun i ↦ (H.mono_scale hε hεi hε0 he hW₁' hW₂' (hb' i).1
                  (hb' i).2).2 (by rw [mul_div_cancel_left₀ _ he0.ne']; exact γ.isMonomialPt i)
                comap_eq := γ.comap_eq
                isXGauss := γ.isXGauss }, rfl⟩
  unfold IsXLength
  rw [hrange]

/-- Reversing chains. -/
theorem exists_rev (H : NodeBranches O ϖK P ι u v n W₁ W₂)
    (γ : XChain O (P : Set L) ϖ₀ (algebraMap K L ϖK) v x n) :
    ∃ γ' : XChain O (P : Set L) ϖ₀ (algebraMap K L ϖK) u x n, γ'.length = γ.length := by
  refine ⟨{ m := γ.m, s := fun i ↦ n - γ.s (Fin.rev i), U := fun i ↦ γ.U (Fin.rev i)
            U' := fun i ↦ γ.U' (Fin.rev i), a := fun i ↦ γ.a (Fin.rev i)
            ρ := fun i ↦ γ.ρ (Fin.rev i)
            s_zero := by simp [γ.s_last]
            s_last := by simp [γ.s_zero]
            strictMono := fun i j hij ↦ by
              have := γ.strictMono (Fin.rev_lt_rev.2 hij)
              simp only; linarith
            isMonomialPt := fun i ↦ by
              have := (isMonomialPt_swap_iff H.base H.core H.irred).1 (γ.isMonomialPt (Fin.rev i))
              exact this
            comap_eq := fun i ↦ γ.comap_eq _
            isXGauss := fun i ↦ γ.isXGauss _ }, ?_⟩
  simp only [XChain.length]
  exact Fintype.sum_equiv Fin.revPerm _ _ fun i ↦ by
    simp only [Fin.revPerm_apply, Fin.rev_succ, Fin.rev_castSucc]
    exact abs_sub_comm _ _

/-- **The x-length is invariant under `u ↔ v`.** -/
theorem isXLength_swap_iff (H : NodeBranches O ϖK P ι u v n W₁ W₂) {l : ℚ} :
    IsXLength O P ϖ₀ (algebraMap K L ϖK) v x n l ↔
      IsXLength O P ϖ₀ (algebraMap K L ϖK) u x n l := by
  have hrange : Set.range (XChain.length (O' := O) (P := (P : Set L)) (ϖ := ϖ₀)
      (ϖ' := algebraMap K L ϖK) (u := v) (x := x) (n := n)) =
      Set.range (XChain.length (O' := O) (P := (P : Set L)) (ϖ := ϖ₀)
      (ϖ' := algebraMap K L ϖK) (u := u) (x := x) (n := n)) := by
    ext l
    constructor
    · rintro ⟨γ, rfl⟩
      obtain ⟨γ', h⟩ := H.exists_rev γ
      exact ⟨γ', h⟩
    · rintro ⟨γ, rfl⟩
      obtain ⟨γ', h⟩ := H.swap.exists_rev γ
      exact ⟨γ', h⟩
  unfold IsXLength
  rw [hrange]

/-- The case `u' = ε ϖ ^ α u ^ e` of `isXLength_of_coord`. -/
theorem isXLength_of_coord_u (H : NodeBranches O ϖK P ι u v n W₁ W₂) {u' v' : L} {n' : ℕ}
    (hv'P : v' ∈ P) (huv' : u' * v' = algebraMap K L ϖK ^ n') (hu'nu : ∀ w ∈ P, u' * w ≠ 1)
    {ε : L} (hε : ε ∈ P) (hεi : ε⁻¹ ∈ P) {α e : ℕ}
    (hu' : u' = ε * algebraMap K L ϖK ^ α * u ^ e) {l : ℚ}
    (hl : IsXLength O P ϖ₀ (algebraMap K L ϖK) u' x n' l) :
    IsXLength O P ϖ₀ (algebraMap K L ϖK) u x n l := by
  set ϖL := algebraMap K L ϖK
  obtain ⟨γ, -⟩ := hl.1
  have hϖ0 := H.ϖ_ne_zero
  have hε0 : ε ≠ 0 := fun h ↦ by
    rw [hu', h, zero_mul, zero_mul, zero_mul] at huv'; exact pow_ne_zero _ hϖ0 huv'.symm
  have hval1 : ∀ U : ValuationSubring L, (P : Set L) ⊆ U → U.valuation ε = 1 := fun U hPU ↦
    (valuation_eq_one_iff_mem_and_inv_mem U).mpr ⟨hε0, hPU hε, hPU hεi⟩
  have hle : ∀ U : ValuationSubring L, (P : Set L) ⊆ U → ∀ p ∈ P, U.valuation p ≤ 1 :=
    fun U hPU p hp ↦ (U.valuation_le_one_iff _).2 (hPU hp)
  -- the first point
  have h0 := γ.isMonomialPt 0
  rw [γ.s_zero] at h0
  generalize γ.U 0 = V0 at h0
  have hU0 := (isLogValue_zero_iff.1 h0.2.2.1).symm.trans (congrArg V0.valuation hu')
  rw [map_mul, map_mul, hval1 _ h0.1, one_mul, map_pow, map_pow] at hU0
  replace hU0 := hU0.symm
  have hα : α = 0 := by
    by_contra hα
    have h1 : V0.valuation ϖL ^ α * V0.valuation u ^ e < 1 :=
      (mul_le_of_le_one_right' (pow_le_one₀ zero_le (hle _ h0.1 _ H.core.u_mem))).trans_lt
        (pow_lt_one₀ zero_le h0.2.1 hα)
    rw [hU0] at h1; exact lt_irrefl _ h1
  subst hα
  simp only [pow_zero, mul_one, one_mul] at hu' hU0
  have he : 1 ≤ e := by
    by_contra he
    have : e = 0 := by omega
    subst this
    apply hu'nu ε⁻¹ hεi
    rw [hu', pow_zero, mul_one, mul_inv_cancel₀ hε0]
  have hu01 : V0.valuation u = 1 :=
    eq_one_of_pow_eq_one' (hle _ h0.1 _ H.core.u_mem) (by omega) hU0
  have hW₁' : IsMonomialPt O P ϖL (ε * u ^ e) 0 W₁ := by
    rw [← H.uniq₁ _ h0.1 h0.2.1 hu01, ← hu']; exact h0
  -- the last point
  have hm := γ.isMonomialPt (Fin.last γ.m)
  rw [γ.s_last] at hm
  generalize γ.U (Fin.last γ.m) = U at hm
  have hUm := ((isLogValue_nat_iff n').1 hm.2.2.1).symm.trans (congrArg U.valuation hu')
  rw [map_mul, hval1 _ hm.1, one_mul, map_pow] at hUm
  replace hUm := hUm.symm
  have hw0 : U.valuation ϖL ≠ 0 := (Valuation.ne_zero_iff _).2 hϖ0
  have hw1 := hm.2.1
  have hprod : U.valuation u * U.valuation v = U.valuation ϖL ^ n := by
    rw [← map_mul, H.core.mul_eq, map_pow]
  have hle1 : n' ≤ n * e := by
    have h1 : U.valuation ϖL ^ (n * e) ≤ U.valuation ϖL ^ n' := by
      rw [← hUm, pow_mul, ← hprod, mul_pow]
      exact mul_le_of_le_one_right' (pow_le_one₀ zero_le (hle _ hm.1 _ H.core.v_mem))
    exact (pow_le_pow_iff_right_of_lt_one₀ (zero_lt_iff.2 hw0) hw1).1 h1
  have hle2 : n * e ≤ n' := by
    by_contra hlt
    push Not at hlt
    have hid : v ^ e = ε * v' * ϖL ^ (n * e - n') := by
      have hu0 := H.u_ne_zero
      apply mul_left_cancel₀ (pow_ne_zero e hu0)
      calc u ^ e * v ^ e = ϖL ^ (n * e) := by rw [← mul_pow, H.core.mul_eq, ← pow_mul]
        _ = (ε * u ^ e * v') * ϖL ^ (n * e - n') := by
          rw [← hu', huv', ← pow_add, Nat.add_sub_cancel' hlt.le]
        _ = _ := by ring
    have hW₂u : W₂.valuation u ^ 1 = W₂.valuation ϖL ^ (n : ℤ) :=
      (isLogValue_iff one_pos).1 (by simpa using H.mono₂.2.2.1)
    have hW₂v := H.valuation_v_eq hW₂u H.u_ne_zero
    have := congrArg W₂.valuation hid
    rw [map_pow, hW₂v, one_pow, map_mul, map_mul, hval1 _ H.mono₂.1, one_mul, map_pow] at this
    have h1 : W₂.valuation v' * W₂.valuation ϖL ^ (n * e - n') < 1 :=
      (mul_le_of_le_one_left' (hle _ H.mono₂.1 _ hv'P)).trans_lt
        (pow_lt_one₀ zero_le H.mono₂.2.1 (by omega))
    rw [← this] at h1; exact lt_irrefl _ h1
  have hn' : n' = n * e := le_antisymm hle1 hle2
  subst hn'
  have hUu : U.valuation u = U.valuation ϖL ^ n := by
    rw [pow_mul] at hUm; exact pow_inj' (by omega) hUm
  have hUv := H.valuation_v_eq (U := U) (by rw [pow_one, zpow_natCast]; exact hUu) H.u_ne_zero
  have hW₂' : IsMonomialPt O P ϖL (ε * u ^ e) (n * e : ℕ) W₂ := by
    rw [← H.uniq₂ _ hm.1 hm.2.1 hUv, ← hu']; exact hm
  rw [hu'] at hl
  exact (H.isXLength_scale_iff hε hεi hε0 he hW₁' hW₂').1 hl

/-- **The x-length does not depend on the node coordinates** (XL5). -/
theorem isXLength_of_coord (H : NodeBranches O ϖK P ι u v n W₁ W₂) {u' v' : L} {n' : ℕ}
    (hv'P : v' ∈ P) (huv' : u' * v' = algebraMap K L ϖK ^ n') (hu'nu : ∀ w ∈ P, u' * w ≠ 1)
    (hdiv : ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, u' = ε * algebraMap K L ϖK ^ α * u ^ e ∨
      u' = ε * algebraMap K L ϖK ^ α * v ^ e) {l : ℚ}
    (hl : IsXLength O P ϖ₀ (algebraMap K L ϖK) u' x n' l) :
    IsXLength O P ϖ₀ (algebraMap K L ϖK) u x n l := by
  obtain ⟨ε, hε, hεi, α, e, h | h⟩ := hdiv
  · exact H.isXLength_of_coord_u hv'P huv' hu'nu hε hεi h hl
  · exact H.isXLength_swap_iff.1 (H.swap.isXLength_of_coord_u hv'P huv' hu'nu hε hεi h hl)

end NodeBranches

end SemistableReduction
