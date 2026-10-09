/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3NP

/-!
# Continuation of values from a type-3 point

Blueprint §9.10a (II.2). Let `ρ ∉ |C^×|` and `y ∈ F'`, `y ≠ 0`. Near `ρ` the coefficients of the
characteristic polynomial of `y` are monomials in the radius, and the comparisons between their
weighted versions have the same outcome as at `ρ` (no crossing radius equals `ρ`). Hence
(`exists_cont`): for every radius `t` near `ρ` and every extension `w''` of `w_{0,t}`, there are an
extension `ξ` of `w_{0,ρ}` and `N ≥ 1`, `c ∈ C^×`, `m ∈ ℤ` with

  `w''(y)^N = |c| tᵐ`  and  `ξ(y)^N = |c| ρᵐ`,

i.e. `w''(y)` is the monomial continuation of one of the values `ξ(y)` (Newton polygons:
`not_uniqueDom_of_ext` at `t`, `exists_ext_eq_of_not_uniqueDom` at `ρ`).
-/

open Polynomial Filter Topology
open scoped NNReal

namespace SemistableReduction

namespace Type3

open Gauss GaussStability TubeCount TypeThree

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section Persist

variable {ρ : ℝ≥0}

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- **No crossing at `ρ`.** A comparison of two monomials in the radius which holds near `ρ`
holds at `ρ`. -/
lemma near_le_imp (hρ : IsIrrat C ρ) (α β : C) (a b : ℤ) :
    Near ρ fun s ↦ ‖α‖₊ * (s : ℝ≥0) ^ a ≤ ‖β‖₊ * (s : ℝ≥0) ^ b →
      ‖α‖₊ * ρ ^ a ≤ ‖β‖₊ * ρ ^ b := by
  have hρ0 := hρ.pos
  rcases eq_or_ne a b with rfl | hab
  · refine (near_true hρ0).mono fun s _ h ↦ ?_
    have hs : (0 : ℝ≥0) < (s : ℝ≥0) ^ a := zpow_pos (pos_iff_ne_zero.2 s.ne_zero) a
    have := le_of_mul_le_mul_right h hs
    exact mul_le_mul_of_nonneg_right this zero_le
  rcases lt_or_ge (‖β‖₊ * ρ ^ b) (‖α‖₊ * ρ ^ a) with hgt | hle
  · -- the comparison fails at `ρ`, hence near `ρ`
    have hev : ∀ᶠ t in 𝓝 ρ, ‖β‖₊ * t ^ b < ‖α‖₊ * t ^ a :=
      (continuousAt_mul_zpow _ b hρ0.ne').eventually_lt (continuousAt_mul_zpow _ a hρ0.ne') hgt
    exact (near_of_eventually hρ0 hev).mono fun s hs h ↦ absurd h (not_le.2 hs)
  · exact (near_true hρ0).mono fun _ _ _ ↦ hle

end Persist

section Mono

/-- The monomial `|α| sᵃ` in the radius. -/
noncomputable def monoR (α : C) (a : ℤ) (s : ℝ≥0) : ℝ≥0 := ‖α‖₊ * s ^ a

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma monoR_mul (α β : C) (a b : ℤ) {s : ℝ≥0} (hs : s ≠ 0) :
    monoR α a s * monoR β b s = monoR (α * β) (a + b) s := by
  simp only [monoR, nnnorm_mul, zpow_add₀ hs]
  ring

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma monoR_pow (α : C) (a : ℤ) (s : ℝ≥0) (N : ℕ) :
    monoR α a s ^ N = monoR (α ^ N) (a * N) s := by
  simp only [monoR, nnnorm_pow, mul_pow, zpow_mul, zpow_natCast]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma monoR_div (α β : C) (a b : ℤ) {s : ℝ≥0} (hs : s ≠ 0) :
    monoR α a s / monoR β b s = monoR (α / β) (a - b) s := by
  simp only [monoR, nnnorm_div, zpow_sub₀ hs]
  rw [mul_div_mul_comm]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma monoR_pos {α : C} (hα : α ≠ 0) (a : ℤ) {s : ℝ≥0} (hs : s ≠ 0) : 0 < monoR α a s :=
  mul_pos (nnnorm_pos.2 hα) (zpow_pos (pos_iff_ne_zero.2 hs) a)

end Mono

section Cont

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- Monomial data for the coefficients of a polynomial near `ρ`. -/
lemma exists_monoData {ρ : ℝ≥0} (hρ : IsIrrat C ρ) (φ : RatFunc C) :
    ∃ (α : C) (a : ℤ), α ≠ 0 ∧ (φ ≠ 0 → Near ρ fun s ↦ w s φ = monoR α a s) := by
  by_cases hφ : φ = 0
  · exact ⟨1, 0, one_ne_zero, fun h ↦ absurd hφ h⟩
  obtain ⟨c, hc, m, g, heq, hg⟩ := exists_monomial hρ hφ
  exact ⟨c, m, hc, fun _ ↦ hg.mono fun s hs ↦ gaussRat_eq_of_monomial heq hs⟩

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- The comparison of weighted coefficients, as a comparison of two monomials. -/
lemma cmp_iff {α β γ : C} {a b c : ℤ} {s v : ℝ≥0} (hs : s ≠ 0) {k l j : ℕ} (hkl : k < l)
    (hvkl : v ^ (l - k) = monoR β b s / monoR γ c s) :
    monoR α a s * v ^ j ≤ monoR β b s * v ^ k ↔
      monoR (α ^ (l - k) * (β / γ) ^ j) (a * ↑(l - k) + (b - c) * ↑j) s ≤
        monoR (β ^ (l - k) * (β / γ) ^ k) (b * ↑(l - k) + (b - c) * ↑k) s := by
  have hN : 0 < l - k := Nat.sub_pos_of_lt hkl
  rw [← pow_le_pow_iff_left₀ zero_le zero_le hN.ne', mul_pow, mul_pow, ← pow_mul, ← pow_mul,
    mul_comm j, mul_comm k, pow_mul, pow_mul, hvkl, monoR_div _ _ _ _ hs, monoR_pow, monoR_pow,
    monoR_pow, monoR_pow, monoR_mul _ _ _ _ hs, monoR_mul _ _ _ _ hs]

/-- **Continuation of values from a type-3 point** (Newton polygons). -/
theorem exists_cont {ρ : ℝ≥0ˣ} (hρ : IsIrrat C (ρ : ℝ≥0)) (y : F') :
    Near (ρ : ℝ≥0) fun t ↦ ∀ w'' : GaussExtension (0 : C) t F', w''.1 y ≠ 0 →
      ∃ ξ : GaussExtension (0 : C) ρ F', ∃ N : ℕ, 0 < N ∧ ∃ (c : C) (m : ℤ), c ≠ 0 ∧
        w''.1 y ^ N = ‖c‖₊ * (t : ℝ≥0) ^ m ∧ ξ.1 y ^ N = ‖c‖₊ * (ρ : ℝ≥0) ^ m := by
  classical
  have hρ0 := hρ.pos
  set P := normPoly (RatFunc C) y
  set S := Finset.range (P.natDegree + 1)
  choose α a hα hαa using fun j ↦ exists_monoData hρ (P.coeff j)
  -- the coefficients are monomials near `ρ`
  have hN1 : Near (ρ : ℝ≥0) fun s ↦ ∀ j ∈ S, P.coeff j ≠ 0 →
      w s (P.coeff j) = monoR (α j) (a j) s :=
    near_finset hρ0 S fun j _ ↦ by
      by_cases hj : P.coeff j = 0
      · exact (near_true hρ0).mono fun _ _ h ↦ absurd hj h
      · exact (hαa j hj).mono fun _ hs _ ↦ hs
  -- the comparisons do not cross `ρ`
  have hN2 : Near (ρ : ℝ≥0) fun s ↦ ∀ k ∈ S, ∀ l ∈ S, ∀ j ∈ S,
      monoR (α j ^ (l - k) * (α k / α l) ^ j) (a j * ↑(l - k) + (a k - a l) * ↑j) s ≤
        monoR (α k ^ (l - k) * (α k / α l) ^ k) (a k * ↑(l - k) + (a k - a l) * ↑k) s →
      monoR (α j ^ (l - k) * (α k / α l) ^ j) (a j * ↑(l - k) + (a k - a l) * ↑j) ρ ≤
        monoR (α k ^ (l - k) * (α k / α l) ^ k) (a k * ↑(l - k) + (a k - a l) * ↑k) ρ :=
    near_finset hρ0 S fun k _ ↦ near_finset hρ0 S fun l _ ↦ near_finset hρ0 S fun j _ ↦
      near_le_imp hρ _ _ _ _
  obtain ⟨s₁, s₂, h₁, h₂, hN⟩ := hN1.and hN2
  refine ⟨s₁, s₂, h₁, h₂, fun t ht₁ ht₂ w'' hy ↦ ?_⟩
  obtain ⟨hmono, hcmp⟩ := hN t ht₁ ht₂
  have hmonoρ := (hN ρ h₁ h₂).1
  set v : ℝ≥0ˣ := Units.mk0 (w''.1 y) hy
  have hnot := not_uniqueDom_of_ext y w'' hy
  have hP0 : P ≠ 0 := (monic_normPoly (F := RatFunc C) y).ne_zero
  have hsup : 0 < sup (w t) v P := pos_iff_ne_zero.2 fun h ↦ hP0 (sup_eq_zero_iff.1 h)
  obtain ⟨k₀, hk₀⟩ := exists_term_eq_sup (v := w t) (r := v) P
  obtain ⟨l₀, hl₀ne, hl₀⟩ : ∃ l₀, l₀ ≠ k₀ ∧ term (w t) v P l₀ = sup (w t) v P := by
    have h := hnot k₀
    simp only [UniqueDom, not_forall, not_lt] at h
    obtain ⟨l₀, hl, hle⟩ := h
    exact ⟨l₀, hl, le_antisymm (term_le_sup P l₀) (hk₀ ▸ hle)⟩
  -- order the two indices
  obtain ⟨k, l, hkl, hk, hl⟩ : ∃ k l, k < l ∧ term (w t) v P k = sup (w t) v P ∧
      term (w t) v P l = sup (w t) v P := by
    rcases lt_or_gt_of_ne hl₀ne with h | h
    · exact ⟨l₀, k₀, h, hl₀, hk₀⟩
    · exact ⟨k₀, l₀, h, hk₀, hl₀⟩
  have hcoeff_ne : ∀ i, term (w t) v P i = sup (w t) v P → P.coeff i ≠ 0 := by
    intro i hi h0
    rw [term, h0, map_zero, zero_mul] at hi
    exact hsup.ne' hi.symm
  have hmemS : ∀ i, P.coeff i ≠ 0 → i ∈ S := fun i hi ↦
    Finset.mem_range.2 (Nat.lt_succ_of_le (le_natDegree_of_ne_zero hi))
  have hck := hcoeff_ne k hk
  have hcl := hcoeff_ne l hl
  have ht0 : (t : ℝ≥0) ≠ 0 := t.ne_zero
  have hρ0' : (ρ : ℝ≥0) ≠ 0 := ρ.ne_zero
  have hv0 : (v : ℝ≥0) ≠ 0 := v.ne_zero
  have hT : ∀ (s : ℝ≥0ˣ) i, (∀ j ∈ S, P.coeff j ≠ 0 → w s (P.coeff j) = monoR (α j) (a j) s) →
      P.coeff i ≠ 0 → ∀ u : ℝ≥0ˣ, term (w s) u P i = monoR (α i) (a i) s * (u : ℝ≥0) ^ i :=
    fun s i hs hi u ↦ by rw [term, hs i (hmemS i hi) hi]
  -- at `t`: `v^(l-k) = T_k / T_l`
  have hvkl : (v : ℝ≥0) ^ (l - k) = monoR (α k) (a k) t / monoR (α l) (a l) t := by
    have h := hk.trans hl.symm
    rw [hT t k hmono hck, hT t l hmono hcl] at h
    rw [eq_div_iff (monoR_pos (hα l) _ ht0).ne']
    apply mul_right_cancel₀ (pow_ne_zero k hv0)
    calc (v : ℝ≥0) ^ (l - k) * monoR (α l) (a l) t * (v : ℝ≥0) ^ k
        = monoR (α l) (a l) t * (v : ℝ≥0) ^ l := by
          rw [mul_comm ((v : ℝ≥0) ^ (l - k)), mul_assoc, ← pow_add, Nat.sub_add_cancel hkl.le]
      _ = monoR (α k) (a k) t * (v : ℝ≥0) ^ k := h.symm
  -- at `ρ`: the candidate value
  set N := l - k with hNdef
  have hN0 : 0 < N := Nat.sub_pos_of_lt hkl
  set q : ℝ≥0 := monoR (α k) (a k) ρ / monoR (α l) (a l) ρ
  set v₀ : ℝ≥0 := q ^ ((N : ℝ)⁻¹)
  have hv₀N : v₀ ^ N = q := NNReal.rpow_inv_natCast_pow q hN0.ne'
  have hq0 : q ≠ 0 :=
    div_ne_zero (monoR_pos (hα k) _ hρ0').ne' (monoR_pos (hα l) _ hρ0').ne'
  have hv₀0 : v₀ ≠ 0 := fun h ↦ hq0 (by rw [← hv₀N, h, zero_pow hN0.ne'])
  set v₀' : ℝ≥0ˣ := Units.mk0 v₀ hv₀0
  have hnotρ : ∀ b, ¬ UniqueDom (w ρ) v₀' P b := by
    have hkρ := hT ρ k hmonoρ hck v₀'
    have hlρ := hT ρ l hmonoρ hcl v₀'
    have heq : term (w ρ) v₀' P k = term (w ρ) v₀' P l := by
      rw [hkρ, hlρ]
      change monoR (α k) (a k) ρ * v₀ ^ k = monoR (α l) (a l) ρ * v₀ ^ l
      have hl' : v₀ ^ l = v₀ ^ N * v₀ ^ k := by
        rw [← pow_add, hNdef, Nat.sub_add_cancel hkl.le]
      rw [hl', hv₀N, ← mul_assoc, mul_comm (monoR (α l) (a l) ρ) q,
        div_mul_cancel₀ _ (monoR_pos (hα l) _ hρ0').ne']
    have hle : ∀ j, term (w ρ) v₀' P j ≤ term (w ρ) v₀' P k := by
      intro j
      by_cases hj : P.coeff j = 0
      · rw [term, hj, map_zero, zero_mul]; exact zero_le
      rw [hT ρ j hmonoρ hj v₀', hkρ]
      refine (cmp_iff (a := a j) (b := a k) (c := a l) hρ0' hkl
        hv₀N).2 ?_
      refine hcmp k (hmemS k hck) l (hmemS l hcl) j (hmemS j hj) ?_
      have hj' : term (w t) v P j ≤ term (w t) v P k := hk ▸ term_le_sup P j
      rw [hT t j hmono hj, hT t k hmono hck] at hj'
      exact (cmp_iff (a := a j) (b := a k) (c := a l) ht0 hkl
        hvkl).1 hj'
    intro b hb
    rcases eq_or_ne b k with rfl | hbk
    · exact (hb l (Nat.ne_of_gt hkl)).ne heq.symm
    · exact (hb k (Ne.symm hbk)).not_ge (hle b)
  obtain ⟨ξ, hξ⟩ := exists_ext_eq_of_not_uniqueDom y v₀' hnotρ
  refine ⟨ξ, N, hN0, α k / α l, a k - a l, div_ne_zero (hα k) (hα l), ?_, ?_⟩
  · change (v : ℝ≥0) ^ N = _
    rw [hvkl, monoR_div _ _ _ _ ht0]
    rfl
  · rw [hξ]
    change v₀ ^ N = _
    rw [hv₀N]
    change monoR (α k) (a k) ρ / monoR (α l) (a l) ρ = _
    rw [monoR_div _ _ _ _ hρ0']
    rfl

end Cont

end Type3

end SemistableReduction
