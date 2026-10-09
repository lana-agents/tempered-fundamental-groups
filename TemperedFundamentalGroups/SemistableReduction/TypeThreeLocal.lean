/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NearBoundary
import TemperedFundamentalGroups.SemistableReduction.DiscLimit

/-!
# Local analysis at a type-3 point

Blueprint §9.12, O6.1h / O13. Let `ρ ∉ |C^×|` (a *type-3 radius*) and `w_ρ = w_{0,ρ}` the Gauss
valuation of `C(x)`.

* `TypeThree.Near ρ P`: `P s` holds for all radii `s` of an open interval around `ρ`;
* `near_gaussRat_le_one`: a rational function with `w_ρ(φ) ≤ 1` has `w_s(φ) ≤ 1` for all `s`
  near `ρ` (`φ` is monomial around `ρ` and `|c| ρᵐ = 1` forces `m = 0`);
* **`near_valuation_le_one`**: an element of `F'` integral at every extension of `w_ρ` is
  integral at every extension of `w_s`, `s` near `ρ` (norm formula over the completion and
  Lagrange interpolation of the characteristic polynomial, as in `exists_valuation_le_one_near`).
-/

open Polynomial Filter Topology
open scoped NNReal

namespace SemistableReduction

namespace TypeThree

open FundamentalInequality GaussStability LocalGlobal GaussTube AnnulusUnit TubeCount

universe u v

section Near

/-- `P s` holds for all radii `s` in an open interval around `ρ`. -/
def Near (ρ : ℝ≥0) (P : ℝ≥0ˣ → Prop) : Prop :=
  ∃ s₁ s₂ : ℝ≥0, s₁ < ρ ∧ ρ < s₂ ∧ ∀ s : ℝ≥0ˣ, s₁ < (s : ℝ≥0) → (s : ℝ≥0) < s₂ → P s

variable {ρ : ℝ≥0} {P Q : ℝ≥0ˣ → Prop}

lemma Near.mono (h : Near ρ P) (hPQ : ∀ s, P s → Q s) : Near ρ Q := by
  obtain ⟨s₁, s₂, h₁, h₂, h⟩ := h
  exact ⟨s₁, s₂, h₁, h₂, fun s hs₁ hs₂ ↦ hPQ s (h s hs₁ hs₂)⟩

lemma Near.and (hP : Near ρ P) (hQ : Near ρ Q) : Near ρ fun s ↦ P s ∧ Q s := by
  obtain ⟨s₁, s₂, h₁, h₂, hP⟩ := hP
  obtain ⟨t₁, t₂, i₁, i₂, hQ⟩ := hQ
  exact ⟨max s₁ t₁, min s₂ t₂, max_lt h₁ i₁, lt_min h₂ i₂, fun s hs₁ hs₂ ↦
    ⟨hP s ((le_max_left _ _).trans_lt hs₁) (hs₂.trans_le (min_le_left _ _)),
      hQ s ((le_max_right _ _).trans_lt hs₁) (hs₂.trans_le (min_le_right _ _))⟩⟩

lemma near_true (hρ : 0 < ρ) : Near ρ fun _ ↦ True :=
  ⟨0, ρ + 1, hρ, lt_add_one ρ, fun _ _ _ ↦ trivial⟩

lemma near_finset (hρ : 0 < ρ) {ι : Type*} (S : Finset ι) {P : ι → ℝ≥0ˣ → Prop}
    (h : ∀ i ∈ S, Near ρ (P i)) : Near ρ fun s ↦ ∀ i ∈ S, P i s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact (near_true hρ).mono fun _ _ i hi ↦ absurd hi (Finset.notMem_empty i)
  | insert a S _ ih =>
    refine ((h a (Finset.mem_insert_self a S)).and
      (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))).mono fun s hs i hi ↦ ?_
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hs.1
    · exact hs.2 i hi

lemma near_forall (hρ : 0 < ρ) {ι : Type*} [Finite ι] {P : ι → ℝ≥0ˣ → Prop}
    (h : ∀ i, Near ρ (P i)) : Near ρ fun s ↦ ∀ i, P i s := by
  classical
  letI := Fintype.ofFinite ι
  exact (near_finset hρ Finset.univ fun i _ ↦ h i).mono fun s hs i ↦ hs i (Finset.mem_univ i)

/-- An eventual property in the neighbourhood filter of `ρ > 0` holds near `ρ`. -/
lemma near_of_eventually (hρ : 0 < ρ) {P : ℝ≥0 → Prop} (h : ∀ᶠ t in 𝓝 ρ, P t) :
    Near ρ fun s ↦ P s := by
  obtain ⟨l, u, ⟨hl, hu⟩, hsub⟩ :=
    (mem_nhds_iff_exists_Ioo_subset' ⟨0, hρ⟩ ⟨ρ + 1, lt_add_one ρ⟩).1 h
  exact ⟨l, u, hl, hu, fun s hs₁ hs₂ ↦ hsub ⟨hs₁, hs₂⟩⟩

end Near

section Irrat

variable (C : Type u) [NontriviallyNormedField C]

/-- `ρ` is not the absolute value of an element of `C` (a type-3 radius). -/
def IsIrrat (ρ : ℝ≥0) : Prop := ∀ z : C, ‖z‖₊ ≠ ρ

variable {C} [IsAlgClosed C] {ρ : ℝ≥0}

omit [IsAlgClosed C] in
lemma IsIrrat.pos (hρ : IsIrrat C ρ) : 0 < ρ :=
  pos_iff_ne_zero.2 fun h ↦ hρ 0 (by rw [nnnorm_zero, h])

/-- No nonzero power `ρᵐ` of a type-3 radius is an absolute value of `C` (the value group of
`C` is divisible). -/
lemma IsIrrat.eq_zero_of_zpow_eq (hρ : IsIrrat C ρ) {m : ℤ} {κ : C} (h : ρ ^ m = ‖κ‖₊) :
    m = 0 := by
  by_contra hm
  obtain ⟨n, hn, κ', hκ'⟩ : ∃ n : ℕ, 0 < n ∧ ∃ κ' : C, ρ ^ n = ‖κ'‖₊ := by
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
    · refine ⟨n, Nat.pos_of_ne_zero fun h0 ↦ hm (by simp [h0]), κ, ?_⟩
      rw [← h, zpow_natCast]
    · refine ⟨n, Nat.pos_of_ne_zero fun h0 ↦ hm (by simp [h0]), κ⁻¹, ?_⟩
      rw [nnnorm_inv, ← h, zpow_neg, zpow_natCast, inv_inv]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq κ' hn
  refine hρ z ((pow_left_inj₀ (by positivity) (by positivity) hn.ne').1 ?_)
  rw [← nnnorm_pow, hz, hκ']

end Irrat

section Germ

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {ρ : ℝ≥0}

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- **Monomial form around a type-3 radius**: a nonzero rational function is `c xᵐ (1 + g)` with
`w_s(g) < 1` for all `s` near `ρ`. -/
theorem exists_monomial (hρ : IsIrrat C ρ) {φ : RatFunc C} (hφ : φ ≠ 0) :
    ∃ c : C, c ≠ 0 ∧ ∃ m : ℤ, ∃ g : RatFunc C,
      φ = algebraMap C (RatFunc C) c * RatFunc.X ^ m * (1 + g) ∧ Near ρ fun s ↦ w s g < 1 := by
  obtain ⟨ρ₁, ρ₂, -, h₁, h₂, -, c, hc, m, g, heq, hg⟩ :=
    DiscLimit.exists_isMonomialOn_around (v := NormedField.valuation (K := C)) hφ
      (ρ₀ := 0) (ρ₀' := ρ + 1) hρ.pos (lt_add_one ρ) fun α _ ↦ by
        rw [NormedField.valuation_apply]
        exact hρ α
  exact ⟨c, hc, m, g, heq, ρ₁, ρ₂, h₁, h₂, fun s hs₁ hs₂ ↦ hg s ⟨hs₁, hs₂⟩⟩

omit [IsAlgClosed C] in
/-- The value of a monomial form near `ρ`. -/
lemma gaussRat_eq_of_monomial {φ : RatFunc C} {c : C} {m : ℤ} {g : RatFunc C}
    (hφ : φ = algebraMap C (RatFunc C) c * RatFunc.X ^ m * (1 + g)) {s : ℝ≥0ˣ}
    (hg : w s g < 1) : w s φ = ‖c‖₊ * (s : ℝ≥0) ^ m := by
  rw [gaussRat_eq_of_isMonomialOn hφ hg, NormedField.valuation_apply]

lemma continuousAt_mul_zpow (c : ℝ≥0) (m : ℤ) {t : ℝ≥0} (ht : t ≠ 0) :
    ContinuousAt (fun s : ℝ≥0 ↦ c * s ^ m) t :=
  continuousAt_const.mul (continuousAt_zpow₀ t m (Or.inl ht))

/-- **Integrality near a type-3 point**: `w_ρ(φ) ≤ 1` implies `w_s(φ) ≤ 1` for all `s` near `ρ`. -/
theorem near_gaussRat_le_one (hρ : IsIrrat C ρ) {ρu : ℝ≥0ˣ} (hρu : (ρu : ℝ≥0) = ρ)
    {φ : RatFunc C} (h : w ρu φ ≤ 1) : Near ρ fun s ↦ w s φ ≤ 1 := by
  by_cases hφ : φ = 0
  · exact (near_true hρ.pos).mono fun s _ ↦ by simp [hφ]
  obtain ⟨c, hc, m, g, heq, hg⟩ := exists_monomial hρ hφ
  obtain ⟨s₁, s₂, h₁, h₂, hg'⟩ := hg
  have hρg : w ρu g < 1 := hg' ρu (hρu ▸ h₁) (hρu ▸ h₂)
  rw [gaussRat_eq_of_monomial heq hρg, hρu] at h
  rcases h.lt_or_eq with hlt | heq1
  · have hev : ∀ᶠ t in 𝓝 ρ, ‖c‖₊ * t ^ m < 1 :=
      (continuousAt_mul_zpow _ m hρ.pos.ne').eventually (gt_mem_nhds hlt)
    refine ((near_of_eventually hρ.pos hev).and ⟨s₁, s₂, h₁, h₂, hg'⟩).mono fun s hs ↦ ?_
    rw [gaussRat_eq_of_monomial heq hs.2]
    exact hs.1.le
  · have hm : m = 0 := by
      refine hρ.eq_zero_of_zpow_eq (κ := c⁻¹) ?_
      rw [nnnorm_inv]
      exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact heq1)
    refine ⟨s₁, s₂, h₁, h₂, fun s hs₁ hs₂ ↦ ?_⟩
    change w s φ ≤ 1
    rw [gaussRat_eq_of_monomial heq (hg' s hs₁ hs₂), hm, zpow_zero, mul_one]
    rw [hm, zpow_zero, mul_one] at heq1
    exact heq1.le

/-- **Strict integrality near a type-3 point**: `w_ρ(φ) < 1` implies `w_s(φ) < 1` near `ρ`. -/
theorem near_gaussRat_lt_one (hρ : IsIrrat C ρ) {ρu : ℝ≥0ˣ} (hρu : (ρu : ℝ≥0) = ρ)
    {φ : RatFunc C} (h : w ρu φ < 1) : Near ρ fun s ↦ w s φ < 1 := by
  by_cases hφ : φ = 0
  · exact (near_true hρ.pos).mono fun s _ ↦ by simp [hφ]
  obtain ⟨c, hc, m, g, heq, hg⟩ := exists_monomial hρ hφ
  obtain ⟨s₁, s₂, h₁, h₂, hg'⟩ := hg
  have hρg : w ρu g < 1 := hg' ρu (hρu ▸ h₁) (hρu ▸ h₂)
  rw [gaussRat_eq_of_monomial heq hρg, hρu] at h
  have hev : ∀ᶠ t in 𝓝 ρ, ‖c‖₊ * t ^ m < 1 :=
    (continuousAt_mul_zpow _ m hρ.pos.ne').eventually (gt_mem_nhds h)
  refine ((near_of_eventually hρ.pos hev).and ⟨s₁, s₂, h₁, h₂, hg'⟩).mono fun s hs ↦ ?_
  rw [gaussRat_eq_of_monomial heq hs.2]
  exact hs.1

/-- The residue field of `w_ρ` is `k`: a function of value `1` at `w_ρ` is congruent to a
constant. -/
theorem exists_sub_const_lt_one (hρ : IsIrrat C ρ) {ρu : ℝ≥0ˣ} (hρu : (ρu : ℝ≥0) = ρ)
    {φ : RatFunc C} (h : w ρu φ = 1) :
    ∃ c : C, ‖c‖₊ = 1 ∧ w ρu (φ - algebraMap C (RatFunc C) c) < 1 := by
  have hφ : φ ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact zero_ne_one h
  obtain ⟨c, hc, m, g, heq, s₁, s₂, h₁, h₂, hg'⟩ := exists_monomial hρ hφ
  have hρg : w ρu g < 1 := hg' ρu (hρu ▸ h₁) (hρu ▸ h₂)
  have h' := h
  rw [gaussRat_eq_of_monomial heq hρg, hρu] at h'
  have hm : m = 0 := by
    refine hρ.eq_zero_of_zpow_eq (κ := c⁻¹) ?_
    rw [nnnorm_inv]
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h')
  rw [hm, zpow_zero, mul_one] at h'
  refine ⟨c, h', ?_⟩
  rw [heq, hm, zpow_zero, mul_one, mul_add, mul_one, add_sub_cancel_left, map_mul,
    gaussRat_algebraMap_C, NormedField.valuation_apply, h', one_mul]
  exact hρg

variable (C) in
/-- The functions integral near `ρ`, as an additive submonoid. -/
def nearSubmonoid (ρ : ℝ≥0) (hρ : 0 < ρ) : AddSubmonoid (RatFunc C) where
  carrier := {φ | Near ρ fun s ↦ w s φ ≤ 1}
  zero_mem' := (near_true hρ).mono fun s _ ↦ by simp
  add_mem' ha hb := (Set.mem_setOf_eq ▸ ha).and hb |>.mono fun _ hs ↦
    (Valuation.map_add _ _ _).trans (max_le hs.1 hs.2)

end Germ

section Element

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {ρ : ℝ≥0} {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

omit [IsAlgClosed C] in
/-- The norm of an element integral at all extensions of a Gauss valuation is integral. -/
lemma gaussRat_norm_le_one {r : ℝ≥0ˣ} {y : F'}
    (hy : ∀ w' : GaussExtension (0 : C) r F', w'.1 y ≤ 1) :
    w r (Algebra.norm (RatFunc C) y) ≤ 1 := by
  rw [nnnorm_norm_eq_prod_factor]
  refine Finset.prod_le_one' fun g _ ↦ pow_le_one' ?_ _
  rw [← factorEquiv_apply_val]
  exact hy _

/-- **Integrality of elements near a type-3 point**: if `w'(y) ≤ 1` for every extension `w'` of
`w_ρ`, then `w''(y) ≤ 1` for every extension `w''` of `w_s`, `s` near `ρ`. -/
theorem near_valuation_le_one (hρ : IsIrrat C ρ) {ρu : ℝ≥0ˣ} (hρu : (ρu : ℝ≥0) = ρ) {y : F'}
    (hy : ∀ w' : GaussExtension (0 : C) ρu F', w'.1 y ≤ 1) :
    Near ρ fun s ↦ ∀ w'' : GaussExtension (0 : C) s F', w''.1 y ≤ 1 := by
  set P := TubeCount.normPoly (RatFunc C) y
  have hcoeff : ∀ i, P.coeff i ∈ nearSubmonoid C ρ hρ.pos := by
    refine coeff_mem_of_eval_mem (C := C) (nearSubmonoid C ρ hρ.pos) (fun l hl a ha ↦ ?_) P
      fun t ht ↦ ?_
    · refine (Set.mem_setOf_eq ▸ ha : Near ρ _).mono fun s hs ↦ ?_
      rw [map_mul, gaussRat_algebraMap_C, NormedField.valuation_apply]
      exact mul_le_one' (by exact_mod_cast hl) hs
    set z := y - algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) t)
    have hN := norm_sub_algebraMap (F := RatFunc C) y (algebraMap C (RatFunc C) t)
    have heq : P.eval (algebraMap C (RatFunc C) t) = algebraMap C (RatFunc C)
        ((-1) ^ Module.finrank (RatFunc C) F') * Algebra.norm (RatFunc C) z := by
      rw [hN, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow,
        one_mul]
    rw [heq]
    refine near_gaussRat_le_one hρ hρu ?_
    rw [map_mul, gaussRat_algebraMap_C, NormedField.valuation_apply, nnnorm_pow, nnnorm_neg,
      nnnorm_one, one_pow, one_mul]
    refine gaussRat_norm_le_one fun w' ↦ ?_
    have htv : w'.1 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) t)) ≤ 1 := by
      rw [← Valuation.comap_apply, w'.2, gaussRat_algebraMap_C, NormedField.valuation_apply]
      exact_mod_cast ht
    exact (Valuation.map_sub _ _ _).trans (max_le (hy w') htv)
  refine (near_finset hρ.pos (Finset.range (P.natDegree + 1))
    (P := fun i s ↦ w s (P.coeff i) ≤ 1) fun i _ ↦ hcoeff i).mono fun s hs w'' ↦ ?_
  refine valuation_le_one_of_aeval_eq_zero w''.1 (monic_normPoly (F := RatFunc C) y) ?_
    fun i ↦ ?_
  · rw [TubeCount.normPoly, map_pow, minpoly.aeval, zero_pow Module.finrank_pos.ne']
  · rw [← Valuation.comap_apply, w''.2]
    by_cases hi : i ≤ P.natDegree
    · exact hs i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero]
      exact zero_le

end Element

end TypeThree

end SemistableReduction
