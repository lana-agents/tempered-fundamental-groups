/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Basic

/-!
# New value-transcendental generators in extensions of prime degree

Blueprint §9.10a (I.1), (I.2). Let `M` be the closure of `C(y)` with `‖y‖ ∉ |C^×|`
(`IsType3 C y`) and `E / M` an extension of prime degree `q` containing `η` with
`η^q = a y^m (1 + ε)`, `q ∤ m`, `‖ε‖ < 1`.

* `mem_of_approx` (I.1): a closed subgroup `V` of a normed group such that every `x` is
  approximated by an element of `V` up to `δ ‖x‖` (`δ < 1` fixed) is everything;
* `norm_zpow_sub_one_le`: integral powers of a `1`-unit `u` stay as close to `1` as `u`;
* `le_norm_sum_of_pow_eq`: the basis `1, η, …, η^(q-1)` of `E / M` is orthogonal;
* **`isType3_of_pow_eq`** (I.2): `E` is the closure of `C(z)`, `z = η^α y^β` (`α m + β q = 1`);
* **`ramificationIdx_eq_of_pow_eq`**: `e(E | M) = q`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace Type3

open InertiallyGenerated

section Approx

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **(I.1) Approximation lemma.** A closed subgroup `V` such that every `x` lies within
`δ ‖x‖` of `V` (`δ < 1`) contains every element. -/
theorem mem_of_approx (V : AddSubgroup E) (hV : IsClosed (V : Set E)) {δ : ℝ} (hδ : δ < 1)
    (h : ∀ x, ∃ v ∈ V, ‖x - v‖ ≤ δ * ‖x‖) (x : E) : x ∈ V := by
  have h0 : 0 ≤ max δ 0 := le_max_right _ _
  have h1 : max δ 0 < 1 := max_lt hδ zero_lt_one
  have key : ∀ n : ℕ, ∃ v ∈ V, ‖x - v‖ ≤ max δ 0 ^ n * ‖x‖ := by
    intro n
    induction n with
    | zero => exact ⟨0, V.zero_mem, by simp⟩
    | succ n ih =>
      obtain ⟨v, hv, hle⟩ := ih
      obtain ⟨v', hv', hle'⟩ := h (x - v)
      refine ⟨v + v', V.add_mem hv hv', ?_⟩
      rw [show x - (v + v') = x - v - v' by abel, pow_succ]
      calc ‖x - v - v'‖ ≤ δ * ‖x - v‖ := hle'
        _ ≤ max δ 0 * ‖x - v‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
        _ ≤ max δ 0 * (max δ 0 ^ n * ‖x‖) := mul_le_mul_of_nonneg_left hle h0
        _ = _ := by ring
  rw [← SetLike.mem_coe, ← hV.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  have hx1 : 0 < ‖x‖ + 1 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hε hx1) h1
  obtain ⟨v, hv, hle⟩ := key n
  refine ⟨v, hv, ?_⟩
  rw [dist_eq_norm]
  calc ‖x - v‖ ≤ max δ 0 ^ n * ‖x‖ := hle
    _ ≤ max δ 0 ^ n * (‖x‖ + 1) := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg h0 n)
    _ < ε / (‖x‖ + 1) * (‖x‖ + 1) := mul_lt_mul_of_pos_right hn hx1
    _ = ε := div_mul_cancel₀ ε hx1.ne'

end Approx

section Units

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

lemma norm_eq_one_of_norm_sub_one_lt {u : E} (hu : ‖u - 1‖ < 1) : ‖u‖ = 1 := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := u - 1) (y := 1)
    (by rw [norm_one]; exact hu.ne)
  rwa [sub_add_cancel, norm_one, max_eq_right hu.le] at this

/-- Integral powers of a `1`-unit stay as close to `1`. -/
lemma norm_zpow_sub_one_le {u : E} {δ : ℝ} (hu : ‖u - 1‖ ≤ δ) (hδ : δ < 1) (k : ℤ) :
    ‖u ^ k - 1‖ ≤ δ := by
  have hu1 : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt (hu.trans_lt hδ)
  have hnat : ∀ n : ℕ, ‖u ^ n - 1‖ ≤ δ := by
    intro n
    induction n with
    | zero => simpa using (norm_nonneg _).trans hu
    | succ n ih =>
      rw [show u ^ (n + 1) - 1 = u ^ n * (u - 1) + (u ^ n - 1) by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ih)
      rw [norm_mul, norm_pow, hu1, one_pow, one_mul]
      exact hu
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [zpow_natCast]; exact hnat n
  · have hun : u ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.1 (by rw [hu1]; exact one_ne_zero))
    rw [zpow_neg, zpow_natCast, show (u ^ n)⁻¹ - 1 = -(u ^ n - 1) / u ^ n by field_simp; ring,
      norm_div, norm_neg, norm_pow, hu1, one_pow, div_one]
    exact hnat n

end Units

section Ram

open FundamentalInequality

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ]

/-- An element whose value has order exactly `q` modulo the values of `K` forces `q ∣ e`. -/
lemma prime_dvd_ramificationIdx (w : Valuation L Γ) {q : ℕ} (hq : q.Prime) {x : L} (hx0 : x ≠ 0)
    (hxq : ∃ b : K, w x ^ q = w (algebraMap K L b))
    (hx : ∀ b : K, w x ≠ w (algebraMap K L b)) : q ∣ ramificationIdx K w := by
  haveI := Fact.mk hq
  set H := valueGroup (w.comap (algebraMap K L))
  set G := valueGroup w
  set g : G := ⟨Units.mk0 (w x) ((Valuation.ne_zero_iff w).2 hx0), valuation_mem_valueGroup w hx0⟩
  set Hs := H.subgroupOf G
  have hord : orderOf (QuotientGroup.mk g : G ⧸ Hs) = q := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      obtain ⟨b, hb⟩ := hxq
      refine ⟨b, ?_⟩
      rw [Valuation.comap_apply, ← hb]
      simp [g]
    · intro h
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h
      obtain ⟨b, hb⟩ := h
      exact hx b (by rw [← Valuation.comap_apply, hb]; simp [g])
  change q ∣ Hs.index
  rw [← hord]
  exact orderOf_dvd_natCard _

end Ram

section Gen

variable {C M E : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [NormedField M] [IsUltrametricDist M] [NormedAlgebra C M]
  [NormedField E] [IsUltrametricDist E] [NormedAlgebra C E] [NormedAlgebra M E]
  [IsScalarTower C M E]

omit [IsUltrametricDist
  C] [IsUltrametricDist E] [NormedAlgebra C E] [NormedAlgebra M E] [IsScalarTower C M E] in
/-- Two terms `c_i ηⁱ`, `c_j ηʲ` (`i ≠ j < q`, `c_i, c_j ≠ 0`) have distinct norms. -/
lemma norm_mul_pow_ne {y : M} (hy : IsType3 C y) {q : ℕ} (hq : q.Prime) {η : E} {a : C}
    (ha : a ≠ 0) {m : ℤ} (hqm : ¬ (q : ℤ) ∣ m) (hη : ‖η‖ ^ q = ‖a‖ * ‖y‖ ^ m) {c d : M}
    (hc : c ≠ 0) (hd : d ≠ 0) {i j : ℕ} (hij : i < j) (hj : j < q) :
    ‖c‖ * ‖η‖ ^ i ≠ ‖d‖ * ‖η‖ ^ j := by
  intro h
  have hη0 : 0 < ‖η‖ := by
    rcases (norm_nonneg η).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      rw [← h0, zero_pow hq.ne_zero] at hη
      exact (mul_pos (norm_pos_iff.2 ha) (zpow_pos hy.valTrans.norm_pos m)).ne' hη.symm
  have hd0 : 0 < ‖d‖ := norm_pos_iff.2 hd
  -- `‖η‖^(j - i) = ‖c / d‖`
  have h1 : ‖η‖ ^ (j - i) = ‖c / d‖ := by
    rw [norm_div, eq_div_iff hd0.ne']
    have : ‖η‖ ^ j = ‖η‖ ^ (j - i) * ‖η‖ ^ i := by rw [← pow_add, Nat.sub_add_cancel hij.le]
    rw [this] at h
    nlinarith [pow_pos hη0 i, h]
  obtain ⟨b, n, hb, hbn⟩ := exists_norm_eq hy (div_ne_zero hc hd)
  -- raise to the `q`-th power
  have h2 : ‖a ^ (j - i)‖ * ‖y‖ ^ (m * ((j - i : ℕ) : ℤ)) =
      ‖b ^ q‖ * ‖y‖ ^ (n * (q : ℤ)) := by
    rw [norm_pow, norm_pow, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, ← mul_pow, ← mul_pow,
      ← hη, ← hbn, ← h1, ← pow_mul, ← pow_mul, mul_comm]
  have h3 := hy.valTrans.eq_of_norm_mul_zpow_eq (pow_ne_zero _ ha) h2
  have hqdvd : (q : ℤ) ∣ m * ((j - i : ℕ) : ℤ) := ⟨n, by rw [h3, mul_comm]⟩
  rcases (Nat.prime_iff_prime_int.mp hq).dvd_or_dvd hqdvd with h4 | h4
  · exact hqm h4
  · have h5 : q ∣ j - i := Int.natCast_dvd_natCast.1 h4
    have h6 : 0 < j - i := Nat.sub_pos_of_lt hij
    have := Nat.le_of_dvd h6 h5
    omega

omit [IsUltrametricDist C] [NormedAlgebra C E] [IsScalarTower C M E] in
/-- **Orthogonality** of `1, η, …, η^(q-1)`: every term is bounded by the norm of the sum. -/
theorem le_norm_sum_of_pow_eq {y : M} (hy : IsType3 C y) {q : ℕ} (hq : q.Prime) {η : E} {a : C}
    (ha : a ≠ 0) {m : ℤ} (hqm : ¬ (q : ℤ) ∣ m) (hη : ‖η‖ ^ q = ‖a‖ * ‖y‖ ^ m) (c : ℕ → M)
    {j : ℕ} (hj : j < q) :
    ‖c j‖ * ‖η‖ ^ j ≤ ‖∑ i ∈ Finset.range q, algebraMap M E (c i) * η ^ i‖ := by
  classical
  set t : ℕ → ℝ := fun i ↦ ‖c i‖ * ‖η‖ ^ i
  obtain ⟨i, hi, hmax⟩ := (Finset.range q).exists_max_image t ⟨0, Finset.mem_range.2 hq.pos⟩
  rcases (show 0 ≤ t i by positivity).lt_or_eq with hpos | hzero
  · have hci : c i ≠ 0 := by
      intro h0
      simp [t, h0] at hpos
    have hdom : ∀ k ∈ Finset.range q, k ≠ i →
        ‖algebraMap M E (c k) * η ^ k‖ < ‖algebraMap M E (c i) * η ^ i‖ := by
      intro k hk hki
      simp only [norm_mul, norm_algebraMap', norm_pow]
      refine lt_of_le_of_ne (hmax k hk) ?_
      by_cases hck : c k = 0
      · simp only [hck, norm_zero, zero_mul]
        exact hpos.ne
      rcases lt_or_gt_of_ne hki with hlt | hlt
      · exact norm_mul_pow_ne hy hq ha hqm hη hck hci hlt (Finset.mem_range.1 hi)
      · exact (norm_mul_pow_ne hy hq ha hqm hη hci hck hlt (Finset.mem_range.1 hk)).symm
    rw [norm_sum_eq_of_dom hi hdom]
    simp only [norm_mul, norm_algebraMap', norm_pow]
    exact hmax j (Finset.mem_range.2 hj)
  · have := hmax j (Finset.mem_range.2 hj)
    rw [← hzero] at this
    exact this.trans (norm_nonneg _)

open IntermediateField in
omit [IsUltrametricDist M] [IsUltrametricDist E] in
/-- Every element is `Σ_{i < q} cᵢ ηⁱ` if `η ∉ M` and `[E : M] = q` is prime. -/
lemma exists_coeff_of_finrank_prime {q : ℕ} (hq : q.Prime) (hdeg : Module.finrank M E = q)
    {η : E} (hη : η ∉ Set.range (algebraMap M E)) (x : E) :
    ∃ c : ℕ → M, x = ∑ i ∈ Finset.range q, algebraMap M E (c i) * η ^ i := by
  haveI : FiniteDimensional M E := Module.finite_of_finrank_pos (hdeg ▸ hq.pos)
  have hint : IsIntegral M η := Algebra.IsIntegral.isIntegral η
  have hmul := Module.finrank_mul_finrank M M⟮η⟯ E
  have hdvd : Module.finrank M M⟮η⟯ ∣ q := ⟨_, by rw [hmul, hdeg]⟩
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hq'
  · exfalso
    apply hη
    have hbot : M⟮η⟯ = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
    have hmem : η ∈ (⊥ : IntermediateField M E) := hbot ▸ mem_adjoin_simple_self M η
    exact IntermediateField.mem_bot.1 hmem
  have htop : M⟮η⟯ = ⊤ :=
    IntermediateField.eq_of_le_of_finrank_eq le_top (by rw [hq', finrank_top', hdeg])
  have hdegη : (minpoly M η).natDegree = q := by rw [← adjoin.finrank hint, hq']
  have hx : x ∈ Algebra.adjoin M {η} := by
    rw [← adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, htop]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨P, rfl⟩ := hx
  have hmon := minpoly.monic hint
  have hne1 : minpoly M η ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hdegη
    exact hq.ne_zero hdegη.symm
  have hlt : (P %ₘ minpoly M η).natDegree < q := hdegη ▸ natDegree_modByMonic_lt P hmon hne1
  refine ⟨fun i ↦ (P %ₘ minpoly M η).coeff i, ?_⟩
  change aeval η P = _
  rw [← aeval_modByMonic_eq_self_of_root (minpoly.aeval M η), aeval_eq_sum_range' hlt]
  simp only [Algebra.smul_def]

/-- A `1`-unit times a `1`-unit. -/
lemma norm_mul_sub_one_le {u v : E} {δ : ℝ} (hu : ‖u - 1‖ ≤ δ) (hv : ‖v - 1‖ ≤ δ)
    (hδ : δ < 1) : ‖u * v - 1‖ ≤ δ := by
  have hu1 : ‖u‖ = 1 := norm_eq_one_of_norm_sub_one_lt (hu.trans_lt hδ)
  rw [show u * v - 1 = u * (v - 1) + (u - 1) by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hu)
  rw [norm_mul, hu1, one_mul]
  exact hv

variable {y : M} {q : ℕ} {η : E} {a : C} {m : ℤ} {ε : E}

omit [IsUltrametricDist
  C] [IsAlgClosed C] [IsUltrametricDist M] [NormedAlgebra C M] [IsScalarTower C M E] in
/-- The norm of `η`. -/
lemma norm_pow_eq_of_pow_eq (hε : ‖ε‖ < 1)
    (hη : η ^ q = algebraMap C E a * algebraMap M E y ^ m * (1 + ε)) :
    ‖η‖ ^ q = ‖a‖ * ‖y‖ ^ m := by
  have h1 : ‖1 + ε‖ = 1 := norm_eq_one_of_norm_sub_one_lt (by rwa [add_sub_cancel_left])
  rw [← norm_pow, hη, norm_mul, norm_mul, h1, mul_one, norm_algebraMap', norm_zpow,
    norm_algebraMap']

omit [IsUltrametricDist
  C] [IsUltrametricDist E] [NormedAlgebra C E] [NormedAlgebra M E] [IsScalarTower C M E] in
/-- `η` is not in `M`. -/
lemma norm_ne_of_pow_eq (hy : IsType3 C y) (hq : q.Prime) (ha : a ≠ 0)
    (hqm : ¬ (q : ℤ) ∣ m) (hn : ‖η‖ ^ q = ‖a‖ * ‖y‖ ^ m) (b : M) : ‖η‖ ≠ ‖b‖ := by
  intro hb'
  rw [hb'] at hn
  have hb : b ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_pow hq.ne_zero] at hn
    exact (mul_pos (norm_pos_iff.2 ha) (zpow_pos hy.valTrans.norm_pos m)).ne' hn.symm
  obtain ⟨d, n, hd, hdn⟩ := exists_norm_eq hy hb
  have h2 : ‖d ^ q‖ * ‖y‖ ^ (n * (q : ℤ)) = ‖a‖ * ‖y‖ ^ m := by
    rw [← hn, hdn, norm_pow, zpow_mul, zpow_natCast, mul_pow]
  have h3 := hy.valTrans.eq_of_norm_mul_zpow_eq (pow_ne_zero _ hd) h2
  exact hqm ⟨n, by rw [← h3, mul_comm]⟩

omit [IsUltrametricDist C] [IsUltrametricDist E] [NormedAlgebra C E] [IsScalarTower C M E] in
/-- `η` is not in `M`. -/
lemma notMem_range_of_pow_eq (hy : IsType3 C y) (hq : q.Prime) (ha : a ≠ 0)
    (hqm : ¬ (q : ℤ) ∣ m) (hn : ‖η‖ ^ q = ‖a‖ * ‖y‖ ^ m) :
    η ∉ Set.range (algebraMap M E) := by
  rintro ⟨b, rfl⟩
  exact norm_ne_of_pow_eq (E := E) hy hq ha hqm hn b (norm_algebraMap' E b)

omit [IsUltrametricDist C] in
/-- **(I.2) The generator lemma.** If `[E : M] = q` is prime and `η^q = a y^m (1 + ε)` with
`q ∤ m`, `‖ε‖ < 1`, then `E` is the closure of `C(z)` for some value-transcendental `z`. -/
theorem isType3_of_pow_eq (hy : IsType3 C y) (hq : q.Prime) (hdeg : Module.finrank M E = q)
    (ha : a ≠ 0) (hqm : ¬ (q : ℤ) ∣ m) (hε : ‖ε‖ < 1)
    (hη : η ^ q = algebraMap C E a * algebraMap M E y ^ m * (1 + ε)) :
    ∃ z : E, IsType3 C z := by
  classical
  have hn := norm_pow_eq_of_pow_eq hε hη
  have hηM := notMem_range_of_pow_eq hy hq ha hqm hn
  set y' := algebraMap M E y with hy'
  set a' := algebraMap C E a with ha'
  set w : E := 1 + ε with hw
  have hy'0 : y' ≠ 0 := (_root_.map_ne_zero _).2 hy.valTrans.ne_zero
  have ha'0 : a' ≠ 0 := (_root_.map_ne_zero _).2 ha
  have hw1 : ‖w - 1‖ = ‖ε‖ := by rw [hw, add_sub_cancel_left]
  have hw0 : w ≠ 0 := by
    intro h
    have := norm_eq_one_of_norm_sub_one_lt (hw1 ▸ hε : ‖w - 1‖ < 1)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hη0 : η ≠ 0 := by
    rintro rfl
    exact hηM ⟨0, map_zero _⟩
  -- Bezout
  obtain ⟨β, α, hαβ⟩ := ((Nat.prime_iff_prime_int.mp hq).coprime_iff_not_dvd).2 hqm
  -- hαβ : β * q + α * m = 1
  set z : E := η ^ α * y' ^ β with hz
  have hηq : η ^ (q : ℤ) = a' * y' ^ m * w := by rw [zpow_natCast]; exact hη
  -- `z^q = a'^α w^α y'`
  have hzq : z ^ (q : ℤ) = a' ^ α * w ^ α * y' := by
    rw [hz, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm α, zpow_mul, hηq, mul_zpow, mul_zpow,
      ← zpow_mul]
    have : y' ^ (m * α) * y' ^ (β * (q : ℤ)) = y' := by
      rw [← zpow_add₀ hy'0, show m * α + β * q = 1 by linarith, zpow_one]
    calc _ = a' ^ α * w ^ α * (y' ^ (m * α) * y' ^ (β * (q : ℤ))) := by ring
      _ = _ := by rw [this]
  -- `z^m = a'^(-β) w^(-β) η`
  have hzm : z ^ m = (a' ^ β)⁻¹ * (w ^ β)⁻¹ * η := by
    have hym : y' ^ m = η ^ (q : ℤ) * a'⁻¹ * w⁻¹ := by
      rw [hηq]; field_simp
    rw [hz, mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm β m, zpow_mul y', hym, mul_zpow,
      mul_zpow, ← zpow_mul, inv_zpow', inv_zpow', zpow_neg, zpow_neg]
    have : η ^ (α * m) * η ^ ((q : ℤ) * β) = η := by
      rw [← zpow_add₀ hη0, show α * m + q * β = 1 by linarith, zpow_one]
    calc _ = (a' ^ β)⁻¹ * (w ^ β)⁻¹ * (η ^ (α * m) * η ^ ((q : ℤ) * β)) := by ring
      _ = _ := by rw [this]
  have hz0 : z ≠ 0 := by
    rw [hz]; exact mul_ne_zero (zpow_ne_zero _ hη0) (zpow_ne_zero _ hy'0)
  clear_value z
  have hwk : ∀ k : ℤ, ‖w ^ k - 1‖ ≤ ‖ε‖ := fun k ↦ norm_zpow_sub_one_le hw1.le hε k
  have hwn : ∀ k : ℤ, ‖w ^ k‖ = 1 := fun k ↦
    norm_eq_one_of_norm_sub_one_lt ((hwk k).trans_lt hε)
  have hy'eq : y' = algebraMap C E (a ^ α)⁻¹ * z ^ (q : ℤ) * w ^ (-α) := by
    rw [hzq, map_inv₀, map_zpow₀, zpow_neg, ← ha']
    field_simp
  have hηeq : η = algebraMap C E (a ^ β) * z ^ m * w ^ β := by
    rw [hzm, map_zpow₀, ← ha']
    field_simp
  have hmono : ∀ n i : ℤ, y' ^ n * η ^ i = algebraMap C E ((a ^ α)⁻¹ ^ n * (a ^ β) ^ i) *
      z ^ ((q : ℤ) * n + m * i) * w ^ (β * i - α * n) := by
    intro n i
    conv_lhs => rw [hy'eq, hηeq]
    rw [mul_zpow, mul_zpow, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul,
      zpow_add₀ hz0, sub_eq_add_neg, zpow_add₀ hw0, map_mul, map_zpow₀, map_zpow₀,
      show -α * n = -(α * n) by ring]
    simp only [map_zpow₀, map_inv₀]
    ring
  set δ : ℝ := max ‖ε‖ (1 / 2) with hδ
  have hδ1 : δ < 1 := max_lt hε (by norm_num)
  have hδ0 : 0 ≤ δ := le_max_of_le_right (by norm_num)
  have hmem : ∀ (b : C) (k : ℤ), algebraMap C E b * z ^ k ∈ genClosure C z := by
    intro b k
    refine Subfield.le_topologicalClosure _ ?_
    change algebraMap C E b * z ^ k ∈ IntermediateField.adjoin C {z}
    exact mul_mem (IntermediateField.algebraMap_mem _ b)
      (zpow_mem (IntermediateField.mem_adjoin_simple_self C z) k)
  have happrox : ∀ x : E, ∃ v ∈ (genClosure C z).toAddSubgroup, ‖x - v‖ ≤ δ * ‖x‖ := by
    intro x
    obtain ⟨c, rfl⟩ := exists_coeff_of_finrank_prime hq hdeg hηM x
    set X := ∑ i ∈ Finset.range q, algebraMap M E (c i) * η ^ i
    have hf : ∀ i, ∃ f : ℤ →₀ C, ‖c i - lev y f‖ ≤ 1 / 2 * ‖c i‖ := by
      intro i
      by_cases hci : c i = 0
      · exact ⟨0, by simp [hci]⟩
      obtain ⟨f, hf⟩ := exists_lev_near hy (c i) (show 0 < 1 / 2 * ‖c i‖ by
        have := norm_pos_iff.2 hci; positivity)
      exact ⟨f, hf.le⟩
    choose f hf using hf
    have hlev : ∀ i, ‖lev y (f i)‖ ≤ ‖c i‖ := by
      intro i
      have := IsUltrametricDist.norm_add_le_max (c i) (-(c i - lev y (f i)))
      rw [norm_neg, show c i + -(c i - lev y (f i)) = lev y (f i) by ring] at this
      refine this.trans (max_le le_rfl ((hf i).trans ?_))
      nlinarith [norm_nonneg (c i)]
    set L : E := ∑ i ∈ Finset.range q, ∑ n ∈ (f i).support,
      algebraMap C E (f i n * ((a ^ α)⁻¹ ^ n * (a ^ β) ^ (i : ℤ))) * z ^ ((q : ℤ) * n + m * i)
    refine ⟨L, ?_, ?_⟩
    · exact Subfield.sum_mem _ fun i _ ↦ Subfield.sum_mem _ fun n _ ↦ hmem _ _
    have hsplit : X - L = ∑ i ∈ Finset.range q, (algebraMap M E (c i - lev y (f i)) * η ^ i +
        ∑ n ∈ (f i).support, algebraMap C E (f i n) * (y' ^ n * η ^ (i : ℤ)) *
          (1 - w ^ (α * n - β * i))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have e1 : algebraMap M E (lev y (f i)) * η ^ i = ∑ n ∈ (f i).support,
          algebraMap C E (f i n) * (y' ^ n * η ^ (i : ℤ)) := by
        rw [lev_eq_sum, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        rw [mono, map_mul, ← IsScalarTower.algebraMap_apply C M E, map_zpow₀, zpow_natCast]
        ring
      have e2 : ∑ n ∈ (f i).support, algebraMap C E (f i n * ((a ^ α)⁻¹ ^ n * (a ^ β) ^ (i : ℤ))) *
          z ^ ((q : ℤ) * n + m * i) = ∑ n ∈ (f i).support,
            algebraMap C E (f i n) * (y' ^ n * η ^ (i : ℤ)) * w ^ (α * n - β * i) := by
        refine Finset.sum_congr rfl fun n _ ↦ ?_
        have hk : w ^ (β * (i : ℤ) - α * n) * w ^ (α * n - β * i) = 1 := by
          rw [← zpow_add₀ hw0, show β * (i : ℤ) - α * n + (α * n - β * i) = 0 by ring, zpow_zero]
        rw [hmono, map_mul]
        linear_combination (-algebraMap C E (f i n) *
          algebraMap C E ((a ^ α)⁻¹ ^ n * (a ^ β) ^ (i : ℤ)) * z ^ ((q : ℤ) * n + m * i)) * hk
      rw [e2, map_sub, sub_mul, e1]
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
      ring
    rw [hsplit]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
      (mul_nonneg hδ0 (norm_nonneg _)) fun i hi ↦ ?_
    have hiq := Finset.mem_range.1 hi
    have hX := le_norm_sum_of_pow_eq (E := E) hy hq ha hqm hn c hiq
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, norm_algebraMap', norm_pow]
      calc ‖c i - lev y (f i)‖ * ‖η‖ ^ i ≤ 1 / 2 * ‖c i‖ * ‖η‖ ^ i :=
            mul_le_mul_of_nonneg_right (hf i) (by positivity)
        _ ≤ δ * (‖c i‖ * ‖η‖ ^ i) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ ≤ δ * ‖X‖ := mul_le_mul_of_nonneg_left hX hδ0
    · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
        (mul_nonneg hδ0 (norm_nonneg _)) fun n _ ↦ ?_
      rw [norm_mul, norm_mul, norm_mul, norm_algebraMap', norm_zpow, norm_zpow, zpow_natCast,
        hy', norm_algebraMap', norm_sub_rev]
      calc ‖f i n‖ * (‖y‖ ^ n * ‖η‖ ^ i) * ‖w ^ (α * n - β * i) - 1‖
          ≤ ‖f i n‖ * (‖y‖ ^ n * ‖η‖ ^ i) * δ :=
            mul_le_mul_of_nonneg_left ((hwk _).trans (le_max_left _ _)) (by positivity)
        _ = δ * (tm y (f i) n * ‖η‖ ^ i) := by rw [tm]; ring
        _ ≤ δ * (‖c i‖ * ‖η‖ ^ i) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            ((tm_le hy.valTrans _ n).trans (hlev i)) (by positivity)) hδ0
        _ ≤ δ * ‖X‖ := mul_le_mul_of_nonneg_left hX hδ0
  refine ⟨z, ⟨fun d hd ↦ ?_, ?_⟩⟩
  · -- `z` is value-transcendental
    have h1 : ‖z‖ ^ q = ‖a‖ ^ α * ‖y‖ := by
      rw [← zpow_natCast, ← norm_zpow, hzq, norm_mul, norm_mul, hwn, mul_one, norm_zpow,
        hy', norm_algebraMap', norm_algebraMap']
    apply hy.valTrans (d ^ q * (a ^ α)⁻¹)
    rw [norm_mul, norm_pow, ← hd, h1, norm_inv, norm_zpow]
    field_simp
  · rw [eq_top_iff]
    intro x _
    exact mem_of_approx (genClosure C z).toAddSubgroup
      (Subfield.isClosed_topologicalClosure _) hδ1 happrox x


omit [IsUltrametricDist C] [IsScalarTower C M E] in
/-- **`e(E | M) = q`** and `f(E | M) = 1` in the situation of the generator lemma. -/
theorem ramificationIdx_eq_of_pow_eq (hy : IsType3 C y) (hq : q.Prime)
    (hdeg : Module.finrank M E = q) (ha : a ≠ 0) (hqm : ¬ (q : ℤ) ∣ m) (hε : ‖ε‖ < 1)
    (hη : η ^ q = algebraMap C E a * algebraMap M E y ^ m * (1 + ε)) :
    FundamentalInequality.ramificationIdx M (NormedField.valuation (K := E)) = q ∧
      FundamentalInequality.inertiaDeg (NormedField.valuation (K := M))
        (NormedField.valuation (K := E)) = 1 := by
  haveI : FiniteDimensional M E := Module.finite_of_finrank_pos (hdeg ▸ hq.pos)
  have hn := norm_pow_eq_of_pow_eq hε hη
  have hηM := notMem_range_of_pow_eq hy hq ha hqm hn
  have hη0 : η ≠ 0 := by
    rintro rfl
    exact hηM ⟨0, map_zero _⟩
  have hdvd : q ∣ FundamentalInequality.ramificationIdx M (NormedField.valuation (K := E)) := by
    refine prime_dvd_ramificationIdx _ hq hη0 ⟨algebraMap C M a * y ^ m, ?_⟩ fun b hb ↦ ?_
    · ext
      simp only [NormedField.valuation_apply, NNReal.coe_pow, coe_nnnorm, norm_algebraMap',
        norm_mul, norm_zpow, hn]
    · apply norm_ne_of_pow_eq (E := E) hy hq ha hqm hn b
      have := congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) hb
      simpa [NormedField.valuation_apply] using this
  have hle := FundamentalInequality.ramificationIdx_mul_inertiaDeg_le (K := M) (L := E)
    (v := NormedField.valuation (K := M)) (w := NormedField.valuation (K := E))
  have he0 := Nat.pos_of_ne_zero (FundamentalInequality.ramificationIdx_ne_zero (K := M)
    (NormedField.valuation (K := E)))
  have hf0 : 0 < FundamentalInequality.inertiaDeg (NormedField.valuation (K := M))
    (NormedField.valuation (K := E)) := NormedTower.inertiaDeg_pos
  have hqe := Nat.le_of_dvd he0 hdvd
  rw [hdeg] at hle
  constructor
  · nlinarith
  · nlinarith

end Gen

end Type3

end SemistableReduction
