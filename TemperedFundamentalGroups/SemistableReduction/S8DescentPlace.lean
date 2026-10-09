/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8DescentCount

/-!
# Descent (A6), part 2: places in a finite extension of function fields

Blueprint §9.10 A6. Let `k` be algebraically closed and `κ₂ / κ₁` a finite extension of function
fields of one variable over `k`.

* `resPlace Q`: the restriction of a place of `κ₂` to `κ₁`;
* `ramIdx Q`: the ramification index, `v_Q(z) = v_{Q|κ₁}(z) ^ e` (`valuation_algebraMap`);
* **`sum_ramIdx_eq`**: `Σ_{Q | Q₁} e(Q | Q₁) = [κ₂ : κ₁]` (Riemann–Roch: a function of `κ₁` with
  a single pole at `Q₁`, and `deg (z)_∞ = [κ : k(z)]` in both fields).
-/

open IntermediateField Valuation WithZero

namespace SemistableReduction

namespace S8A

namespace Descent

open CurvePlace

variable {k κ₁ κ₂ : Type*} [Field k] [Field κ₁] [Field κ₂] [Algebra k κ₁] [Algebra k κ₂]
  [Algebra κ₁ κ₂] [IsScalarTower k κ₁ κ₂] [IsAlgClosed k]

section Res

variable [Algebra.IsAlgebraic κ₁ κ₂]

/-- The restriction of a place of `κ₂` to `κ₁`. -/
def resPlace (Q : CurvePlace k κ₂) : CurvePlace k κ₁ where
  V := Q.V.comap (algebraMap κ₁ κ₂)
  algebraMap_mem c := by
    change algebraMap κ₁ κ₂ (algebraMap k κ₁ c) ∈ Q.V
    rw [← IsScalarTower.algebraMap_apply]
    exact Q.algebraMap_mem c
  ne_top h := Q.ne_top (by
    refine eq_top_iff.2 fun z _ ↦ ?_
    have hint : IsIntegral κ₁ z := Algebra.IsIntegral.isIntegral z
    have hle : (algebraMap κ₁ κ₂).range ≤ Q.V.toSubring := by
      rintro _ ⟨y, rfl⟩
      have : y ∈ Q.V.comap (algebraMap κ₁ κ₂) := h ▸ (trivial : y ∈ (⊤ : ValuationSubring κ₁))
      exact this
    let φ : κ₁ →+* Q.V := (algebraMap κ₁ κ₂).codRestrict Q.V.toSubring fun y ↦ hle ⟨y, rfl⟩
    have : IsIntegral Q.V z :=
      IsIntegral.map_of_comp_eq φ (RingHom.id κ₂) (RingHom.ext fun _ ↦ rfl) hint
    have h2 := (Valuation.valuationSubring.integers Q.V.valuation).mem_of_integral
      (x := z) (by rw [ValuationSubring.valuationSubring_valuation]; exact this)
    exact (ValuationSubring.valuation_le_one_iff Q.V z).1 h2)

omit [IsAlgClosed k] in
lemma mem_resPlace {Q : CurvePlace k κ₂} {y : κ₁} :
    y ∈ (resPlace Q).V ↔ algebraMap κ₁ κ₂ y ∈ Q.V := Iff.rfl

variable [IsCurveFunctionField k κ₁] [IsCurveFunctionField k κ₂]

/-- A uniformizer of the restricted place. -/
noncomputable def unif (Q : CurvePlace k κ₂) : κ₁ :=
  Classical.choose (resPlace (κ₁ := κ₁) Q).exists_valuation_eq_exp_neg_one

omit [IsCurveFunctionField k κ₂] in
lemma valuation_unif (Q : CurvePlace k κ₂) :
    (resPlace (κ₁ := κ₁) Q).valuation (unif Q) = exp (-1) :=
  Classical.choose_spec (resPlace (κ₁ := κ₁) Q).exists_valuation_eq_exp_neg_one

/-- The ramification index `e(Q | Q ∩ κ₁)`. -/
noncomputable def ramIdx (Q : CurvePlace k κ₂) : ℕ :=
  (-log (Q.valuation (algebraMap κ₁ κ₂ (unif (κ₁ := κ₁) Q)))).toNat

/-- Units of the restricted place are units of `Q`. -/
lemma valuation_algebraMap_eq_one {Q : CurvePlace k κ₂} {u : κ₁}
    (hu : (resPlace (κ₁ := κ₁) Q).valuation u = 1) : Q.valuation (algebraMap κ₁ κ₂ u) = 1 := by
  have hu0 : u ≠ 0 := by
    rintro rfl
    simp at hu
  have h1 : u ∈ (resPlace (κ₁ := κ₁) Q).V := (resPlace Q).valuation_le_one_iff.1 hu.le
  have h2 : u⁻¹ ∈ (resPlace (κ₁ := κ₁) Q).V :=
    (resPlace Q).valuation_le_one_iff.1 (by rw [map_inv₀, hu, inv_one])
  have h1' := Q.valuation_le_one_iff.2 (mem_resPlace.1 h1)
  have h2' := Q.valuation_le_one_iff.2 (mem_resPlace.1 h2)
  rw [map_inv₀, map_inv₀] at h2'
  have hne : Q.valuation (algebraMap κ₁ κ₂ u) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (by simpa using hu0)
  exact le_antisymm h1' ((inv_le_one₀ (zero_lt_iff.2 hne)).1 h2')

lemma valuation_unif_lt_one (Q : CurvePlace k κ₂) :
    Q.valuation (algebraMap κ₁ κ₂ (unif (κ₁ := κ₁) Q)) < 1 ∧
      Q.valuation (algebraMap κ₁ κ₂ (unif (κ₁ := κ₁) Q)) ≠ 0 := by
  set π := unif (κ₁ := κ₁) Q
  have hπ := valuation_unif (κ₁ := κ₁) Q
  have hπ0 : π ≠ 0 := by
    intro h
    have h' : (resPlace (κ₁ := κ₁) Q).valuation π = exp (-1) := hπ
    rw [h, map_zero] at h'
    exact WithZero.exp_ne_zero h'.symm
  refine ⟨?_, (Valuation.ne_zero_iff _).2 (by simpa using hπ0)⟩
  have hinv : π⁻¹ ∉ (resPlace (κ₁ := κ₁) Q).V := by
    rw [← (resPlace Q).valuation_le_one_iff, map_inv₀, hπ, ← exp_neg, neg_neg, ← exp_zero,
      exp_le_exp]
    omega
  rw [mem_resPlace, map_inv₀, ← Q.valuation_le_one_iff, map_inv₀] at hinv
  push Not at hinv
  have h0 : Q.valuation (algebraMap κ₁ κ₂ π) ≠ 0 := (Valuation.ne_zero_iff _).2 (by simpa using hπ0)
  exact (one_lt_inv_iff₀.1 hinv).2

lemma one_le_ramIdx (Q : CurvePlace k κ₂) : 1 ≤ ramIdx (κ₁ := κ₁) Q := by
  obtain ⟨h1, h0⟩ := valuation_unif_lt_one (κ₁ := κ₁) Q
  have : log (Q.valuation (algebraMap κ₁ κ₂ (unif (κ₁ := κ₁) Q))) < 0 := by
    rw [← exp_lt_exp, exp_log h0, exp_zero]; exact h1
  rw [ramIdx]
  omega

lemma valuation_algebraMap_unif (Q : CurvePlace k κ₂) :
    Q.valuation (algebraMap κ₁ κ₂ (unif (κ₁ := κ₁) Q)) = exp (-(ramIdx (κ₁ := κ₁) Q : ℤ)) := by
  obtain ⟨h1, h0⟩ := valuation_unif_lt_one (κ₁ := κ₁) Q
  have : log (Q.valuation (algebraMap κ₁ κ₂ (unif (κ₁ := κ₁) Q))) < 0 := by
    rw [← exp_lt_exp, exp_log h0, exp_zero]; exact h1
  rw [ramIdx, Int.toNat_of_nonneg (by omega), neg_neg, exp_log h0]

/-- **`v_Q(z) = v_{Q ∩ κ₁}(z) ^ e(Q | Q ∩ κ₁)`.** -/
theorem valuation_algebraMap (Q : CurvePlace k κ₂) (z : κ₁) :
    Q.valuation (algebraMap κ₁ κ₂ z) =
      (resPlace (κ₁ := κ₁) Q).valuation z ^ ramIdx (κ₁ := κ₁) Q := by
  set Q₁ := resPlace (κ₁ := κ₁) Q
  set π := unif (κ₁ := κ₁) Q
  set e := ramIdx (κ₁ := κ₁) Q
  rcases eq_or_ne z 0 with rfl | hz
  · rw [map_zero, map_zero, map_zero, zero_pow (by have := one_le_ramIdx (κ₁ := κ₁) Q; omega)]
  have hπ : Q₁.valuation π = exp (-1) := valuation_unif Q
  have hπ0 : π ≠ 0 := by
    intro h
    have h' := hπ
    rw [h, map_zero] at h'
    exact WithZero.exp_ne_zero h'.symm
  have hz0 : Q₁.valuation z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  set n := log (Q₁.valuation z)
  set u := z * π ^ n
  have hz' : Q₁.valuation z = exp n := (exp_log hz0).symm
  have hu : Q₁.valuation u = 1 := by
    rw [map_mul, map_zpow₀, hπ, hz', ← exp_zsmul, ← exp_add, exp_eq_one]
    simp
  have hzu : z = u * π ^ (-n) := by
    simp only [u, mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, mul_one]
  rw [hzu, map_mul, map_mul, map_zpow₀, valuation_algebraMap_eq_one hu, one_mul, map_zpow₀,
    valuation_algebraMap_unif, map_mul, hu, one_mul, map_zpow₀, hπ, ← exp_zsmul, ← exp_zsmul,
    ← exp_nsmul]
  congr 1
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

/-- **Pole orders**: `ord_Q(1/z) = e · ord_{Q ∩ κ₁}(1/z)`. -/
lemma poleOrder_algebraMap (Q : CurvePlace k κ₂) (z : κ₁) :
    Q.poleOrder (algebraMap κ₁ κ₂ z) =
      ramIdx (κ₁ := κ₁) Q * (resPlace (κ₁ := κ₁) Q).poleOrder z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [poleOrder]
  have hz0 : (resPlace (κ₁ := κ₁) Q).valuation z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
  rw [poleOrder, poleOrder, valuation_algebraMap, log_pow, nsmul_eq_mul]
  set a := log ((resPlace (κ₁ := κ₁) Q).valuation z)
  rcases le_total a 0 with ha | ha
  · rw [Int.toNat_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) ha),
      Int.toNat_eq_zero.2 ha, mul_zero]
  · rw [Int.toNat_mul (by positivity) ha, Int.toNat_natCast]

omit [IsCurveFunctionField k κ₂] [Algebra.IsAlgebraic κ₁ κ₂] in
/-- **A function with a single pole**: for every place `Q₁` some `z` has pole divisor `n Q₁`,
`n ≥ 1` (Riemann–Roch: `ℓ(n Q₁) = ℓ((n - 1) Q₁) + 1` for `n ≫ 0`). -/
lemma exists_single_pole (Q₁ : CurvePlace k κ₁) :
    ∃ (z : κ₁) (n : ℕ), 1 ≤ n ∧ poleDivisor k z = Finsupp.single Q₁ (n : ℤ) := by
  classical
  obtain ⟨c, hc⟩ := ell_eq_of_le_degree (k := k) (κ := κ₁)
  set n : ℕ := c.toNat + 2
  have hdeg (m : ℕ) : (Finsupp.single Q₁ (m : ℤ) : CurveDivisor k κ₁).degree = m := by
    rw [Finsupp.degree_apply]
    by_cases hm : (m : ℤ) = 0
    · rw [hm, Finsupp.single_zero, Finsupp.support_zero, Finset.sum_empty]
    · rw [Finsupp.support_single _ hm, Finset.sum_singleton, Finsupp.single_eq_same]
  have h1 := hc (Finsupp.single Q₁ (n : ℤ)) (by rw [hdeg]; omega)
  have h2 := hc (Finsupp.single Q₁ ((n - 1 : ℕ) : ℤ)) (by rw [hdeg]; omega)
  rw [hdeg] at h1 h2
  have hlt : ell (Finsupp.single Q₁ ((n - 1 : ℕ) : ℤ) : CurveDivisor k κ₁) <
      ell (Finsupp.single Q₁ (n : ℤ) : CurveDivisor k κ₁) := by
    have : (n - 1 : ℕ) + 1 = n := by omega
    omega
  -- some `z` lies in the larger space only
  obtain ⟨z, hz, hz'⟩ : ∃ z, z ∈ rrSpace (Finsupp.single Q₁ (n : ℤ) : CurveDivisor k κ₁) ∧
      z ∉ rrSpace (Finsupp.single Q₁ ((n - 1 : ℕ) : ℤ) : CurveDivisor k κ₁) := by
    by_contra h
    push Not at h
    exact absurd (Submodule.finrank_mono h) (not_le.2 hlt)
  refine ⟨z, n, by omega, ?_⟩
  ext P
  rw [poleDivisor_apply]
  have hzP := hz P
  by_cases hP : P = Q₁
  · subst hP
    rw [Finsupp.single_eq_same]
    have hnot : ¬ P.valuation z ≤ exp ((n - 1 : ℕ) : ℤ) := by
      intro hle
      apply hz'
      intro P'
      by_cases hP' : P' = P
      · subst hP'; rw [Finsupp.single_eq_same]; exact hle
      · rw [Finsupp.single_eq_of_ne hP']
        have := hz P'
        rwa [Finsupp.single_eq_of_ne hP'] at this
    rw [Finsupp.single_eq_same] at hzP
    have hle := P.poleOrder_le_iff (f := z) (N := n) |>.2 hzP
    have hge : ¬ P.poleOrder z ≤ n - 1 := fun h ↦ hnot (P.poleOrder_le_iff.1 h)
    omega
  · rw [Finsupp.single_eq_of_ne hP]
    rw [Finsupp.single_eq_of_ne hP, exp_zero] at hzP
    rw [P.poleOrder_eq_zero_iff.2 (P.valuation_le_one_iff.1 hzP)]
    rfl

variable [FiniteDimensional κ₁ κ₂]

omit [IsCurveFunctionField k κ₂] [Algebra.IsAlgebraic κ₁ κ₂] [IsAlgClosed k]
  [IsCurveFunctionField k κ₁] in
/-- `[κ₂ : k(z)] = [κ₂ : κ₁] [κ₁ : k(z)]`. -/
lemma finrank_adjoin_algebraMap (z : κ₁) :
    Module.finrank k⟮algebraMap κ₁ κ₂ z⟯ κ₂ =
      Module.finrank k⟮z⟯ κ₁ * Module.finrank κ₁ κ₂ := by
  set φ := IsScalarTower.toAlgHom k κ₁ κ₂
  have hmap : (k⟮z⟯).map φ = k⟮algebraMap κ₁ κ₂ z⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  set A := k⟮z⟯
  have h1 : Module.finrank k⟮algebraMap κ₁ κ₂ z⟯ κ₂ = Module.finrank A κ₂ := by
    rw [← hmap]
    refine Algebra.finrank_eq_of_equiv_equiv (A.equivMap φ).symm.toRingEquiv
      (RingEquiv.refl κ₂) ?_
    ext a
    change algebraMap κ₁ κ₂ ((A.equivMap φ).symm a : κ₁) = (a : κ₂)
    have := congrArg Subtype.val ((A.equivMap φ).apply_symm_apply a)
    rw [← this]
    rfl
  rw [h1, Module.finrank_mul_finrank]

/-- **The fundamental identity for places**: `Σ_{Q | Q₁} e(Q | Q₁) = [κ₂ : κ₁]`. -/
theorem sum_ramIdx_eq (Q₁ : CurvePlace k κ₁) :
    ∃ S : Finset (CurvePlace k κ₂), (∀ Q, Q ∈ S ↔ resPlace (κ₁ := κ₁) Q = Q₁) ∧
      ∑ Q ∈ S, ramIdx (κ₁ := κ₁) Q = Module.finrank κ₁ κ₂ := by
  classical
  obtain ⟨z, n, hn, hz⟩ := exists_single_pole Q₁
  have hpole : ∀ Q : CurvePlace k κ₂, poleDivisor k (algebraMap κ₁ κ₂ z) Q =
      if resPlace (κ₁ := κ₁) Q = Q₁ then (ramIdx (κ₁ := κ₁) Q * n : ℕ) else 0 := by
    intro Q
    rw [poleDivisor_apply, poleOrder_algebraMap]
    have := congrArg (fun D : CurveDivisor k κ₁ ↦ D (resPlace (κ₁ := κ₁) Q)) hz
    simp only [poleDivisor_apply] at this
    split_ifs with h
    · rw [h, Finsupp.single_eq_same] at this
      rw [h, Nat.cast_inj.1 this]
    · rw [Finsupp.single_eq_of_ne h, Nat.cast_eq_zero] at this
      rw [this, mul_zero, Nat.cast_zero]
  set S := (poleDivisor k (algebraMap κ₁ κ₂ z)).support
  have hS : ∀ Q, Q ∈ S ↔ resPlace (κ₁ := κ₁) Q = Q₁ := by
    intro Q
    rw [Finsupp.mem_support_iff, hpole]
    split_ifs with h
    · have := one_le_ramIdx (κ₁ := κ₁) Q
      simp only [h, iff_true, ne_eq, Nat.cast_eq_zero]
      exact Nat.mul_ne_zero (by omega) (by omega)
    · simp [h]
  refine ⟨S, hS, ?_⟩
  -- degrees
  have hz1 : z ∉ (algebraMap k κ₁).range := by
    rintro ⟨c, rfl⟩
    rw [poleDivisor_algebraMap] at hz
    have := congrArg (fun D : CurveDivisor k κ₁ ↦ D Q₁) hz
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at this
    omega
  have hz2 : algebraMap κ₁ κ₂ z ∉ (algebraMap k κ₂).range := by
    rintro ⟨c, hc⟩
    apply hz1
    refine ⟨c, (algebraMap κ₁ κ₂).injective ?_⟩
    rw [← hc, ← IsScalarTower.algebraMap_apply]
  have hd1 := degree_poleDivisor (k := k) hz1
  have hd2 := degree_poleDivisor (k := k) hz2
  rw [hz, Finsupp.degree_apply, Finsupp.support_single _ (by omega), Finset.sum_singleton,
    Finsupp.single_eq_same] at hd1
  rw [finrank_adjoin_algebraMap, ← Nat.cast_inj (R := ℤ).2 rfl] at hd2
  rw [Finsupp.degree_apply] at hd2
  have hsum : ∑ Q ∈ S, poleDivisor k (algebraMap κ₁ κ₂ z) Q =
      ((∑ Q ∈ S, ramIdx (κ₁ := κ₁) Q) * n : ℕ) := by
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun Q hQ ↦ ?_
    rw [hpole, if_pos ((hS Q).1 hQ)]
    push_cast
    ring
  rw [hsum] at hd2
  have h3 : (((∑ Q ∈ S, ramIdx (κ₁ := κ₁) Q) * n : ℕ) : ℤ) =
      ((Module.finrank k⟮z⟯ κ₁ * Module.finrank κ₁ κ₂ : ℕ) : ℤ) := hd2
  push_cast at h3
  rw [← hd1] at h3
  have hn' : (n : ℤ) ≠ 0 := by omega
  have : ((∑ Q ∈ S, ramIdx (κ₁ := κ₁) Q : ℕ) : ℤ) = (Module.finrank κ₁ κ₂ : ℤ) := by
    push_cast
    exact mul_right_cancel₀ hn' (by rw [h3]; ring)
  exact_mod_cast this

end Res

end Descent

end S8A

end SemistableReduction
