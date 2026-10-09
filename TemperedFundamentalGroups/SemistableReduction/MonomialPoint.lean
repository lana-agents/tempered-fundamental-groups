/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XLength
import TemperedFundamentalGroups.SemistableReduction.ZariskiNormalization

/-!
# Monomial points restrict to Gauss points (Blueprint §9.7, XL2)

Let `O ⊆ K` be a discrete valuation subring with uniformizer `ϖ`, `L / K` a field extension and
`U` a valuation subring of `L` over `O`. If `U(u) = U(ϖ) ^ s` (`s = m / d` in lowest terms) and
the monomial `g = u ^ d / ϖ ^ m` has transcendental residue (`U` is a monomial point at `s`,
`IsMonomialPt`), then `U` restricts on `K[u]` to the Gauss valuation of radius `|ϖ| ^ s`:

  `U(Σ qᵢ uⁱ) = max_i U(qᵢ) U(u) ^ i` (`valuation_aeval_eq_sup_of_monomial`).

Proof: the terms of maximal value have exponents in one class modulo `d` (values of constants
are integral powers of `U(ϖ)`, `gcd(m, d) = 1`); their sum is `q_{i₀} u ^ {i₀} R(g)` with
`R ∈ O[X]` having unit coefficients, so `U(R(g)) = 1` by residue transcendence; the other terms
are strictly smaller.
-/

open Polynomial

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  {O : ValuationSubring K} [IsDiscreteValuationRing O] {ϖ : O} {U : ValuationSubring L}

/-- Values of nonzero constants are integral powers of the value of the uniformizer. -/
lemma exists_valuation_eq_zpow_of_comap (hU : U.comap (algebraMap K L) = O)
    (hϖ : Irreducible ϖ) {q : K} (hq : q ≠ 0) :
    ∃ k : ℤ, U.valuation (algebraMap K L q) = U.valuation (algebraMap K L (ϖ : K)) ^ k := by
  have hunit : ∀ e : Oˣ, U.valuation (algebraMap K L ((e : O) : K)) = 1 := fun e ↦ by
    rw [valuation_eq_one_iff_mem_and_inv_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [Ne, map_eq_zero_iff _ (algebraMap K L).injective]
      exact_mod_cast e.ne_zero
    · rw [← ValuationSubring.mem_comap, hU]; exact (e : O).2
    · rw [← map_inv₀, ← ValuationSubring.mem_comap, hU]
      have : ((e : O) : K)⁻¹ = ((e⁻¹ : Oˣ) : O) := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ (by exact_mod_cast e.ne_zero)]
        exact_mod_cast e.inv_mul
      rw [this]; exact ((e⁻¹ : Oˣ) : O).2
  have hO : ∀ o : O, o ≠ 0 → ∃ k : ℕ,
      U.valuation (algebraMap K L (o : K)) = U.valuation (algebraMap K L (ϖ : K)) ^ k := by
    intro o ho
    obtain ⟨k, e, he⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ
    refine ⟨k, ?_⟩
    have h' : (o : K) = ((e : O) : K) * (ϖ : K) ^ k := by
      rw [he, MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [h', map_mul, map_mul, hunit, one_mul, map_pow, map_pow]
  rcases O.mem_or_inv_mem q with h | h
  · obtain ⟨k, hk⟩ := hO ⟨q, h⟩ (fun h0 ↦ hq (congrArg Subtype.val h0))
    exact ⟨k, by simpa using hk⟩
  · obtain ⟨k, hk⟩ := hO ⟨q⁻¹, h⟩ (fun h0 ↦ hq (inv_eq_zero.mp (congrArg Subtype.val h0)))
    refine ⟨-(k : ℤ), ?_⟩
    simp only [map_inv₀] at hk
    rw [zpow_neg, zpow_natCast, ← hk, inv_inv]

omit [IsDiscreteValuationRing O] in
/-- The uniformizer has value `0 < U(ϖ) < 1`. -/
lemma valuation_uniformizer (hU : U.comap (algebraMap K L) = O) (hϖ : Irreducible ϖ) :
    U.valuation (algebraMap K L (ϖ : K)) ≠ 0 ∧ U.valuation (algebraMap K L (ϖ : K)) < 1 := by
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  refine ⟨by simpa using hϖ0, lt_of_le_of_ne ?_ fun h ↦ ?_⟩
  · rw [ValuationSubring.valuation_le_one_iff, ← ValuationSubring.mem_comap, hU]; exact ϖ.2
  · rw [valuation_eq_one_iff_mem_and_inv_mem] at h
    obtain ⟨-, -, h⟩ := h
    rw [← map_inv₀, ← ValuationSubring.mem_comap, hU] at h
    apply hϖ.not_isUnit
    exact IsUnit.of_mul_eq_one (⟨_, h⟩ : O) (Subtype.ext (by simp [hϖ0]))

/-- **Monomial points restrict to Gauss points** (XL2): if `U(u) = U(ϖ) ^ s` and
`u ^ den s / ϖ ^ num s` has transcendental residue over `O`, then
`U(Σ qᵢ uⁱ) = max_i U(qᵢ) U(u) ^ i`. -/
theorem valuation_aeval_eq_sup_of_monomial (hU : U.comap (algebraMap K L) = O)
    (hϖ : Irreducible ϖ)
    {u : L} {s : ℚ} (hs : IsLogValue U (algebraMap K L (ϖ : K)) u s)
    (htr : IsResidueTranscendental O U (u ^ s.den / algebraMap K L (ϖ : K) ^ s.num))
    (Q : K[X]) :
    U.valuation (aeval u Q) = Q.support.sup
      (fun i ↦ U.valuation (algebraMap K L (Q.coeff i)) * U.valuation u ^ i) := by
  classical
  set w := U.valuation
  set p := algebraMap K L (ϖ : K)
  obtain ⟨hwp0, hwp1⟩ := valuation_uniformizer hU hϖ
  have hp0 : p ≠ 0 := by
    intro h; apply hwp0; change w p = 0; rw [h, map_zero]
  have hden : 0 < s.den := s.den_pos
  have hwu0 : w u ≠ 0 := by
    intro h
    have := hs
    unfold IsLogValue at this
    rw [h, zero_pow hden.ne'] at this
    exact zpow_ne_zero _ hwp0 this.symm
  have hu0 : u ≠ 0 := by simpa [w] using hwu0
  by_cases hQ : Q = 0
  · subst hQ; simp; rfl
  set term : ℕ → _ := fun i ↦ w (algebraMap K L (Q.coeff i)) * w u ^ i with hterm
  have hne : Q.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hQ)
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image Q.support term hne
  set M := term i₁ with hM
  have hsup : Q.support.sup term = M :=
    le_antisymm (Finset.sup_le hmax) (Finset.le_sup (f := term) hi₁)
  change w (aeval u Q) = Q.support.sup term
  rw [hsup]
  have hcoeff0 : ∀ i ∈ Q.support, Q.coeff i ≠ 0 := fun i hi ↦ by simpa using hi
  have hterm0 : ∀ i ∈ Q.support, term i ≠ 0 := fun i hi ↦ by
    simp only [hterm]
    exact mul_ne_zero (by simpa using hcoeff0 i hi) (pow_ne_zero _ hwu0)
  have hM0 : M ≠ 0 := hterm0 i₁ hi₁
  -- exponents
  have hk : ∀ i ∈ Q.support, ∃ k : ℤ, w (algebraMap K L (Q.coeff i)) = w p ^ k :=
    fun i hi ↦ exists_valuation_eq_zpow_of_comap hU hϖ (hcoeff0 i hi)
  have hupow : ∀ i : ℕ, (w u ^ i) ^ s.den = w p ^ (s.num * i) := fun i ↦ by
    rw [← pow_mul, mul_comm, pow_mul, hs, ← zpow_natCast, ← zpow_mul, mul_comm]
  set I := Q.support.filter (fun i ↦ term i = M) with hI
  have hi₁I : i₁ ∈ I := Finset.mem_filter.mpr ⟨hi₁, rfl⟩
  have hIne : I.Nonempty := ⟨i₁, hi₁I⟩
  set i₀ := I.min' hIne
  have hi₀I : i₀ ∈ I := I.min'_mem hIne
  have hi₀le : ∀ i ∈ I, i₀ ≤ i := fun i hi ↦ I.min'_le i hi
  -- divisibility of exponent differences
  have hdvd : ∀ i ∈ I, ∀ j ∈ I, (s.den : ℤ) ∣ (i - j : ℤ) := by
    intro i hi j hj
    obtain ⟨hi', hti⟩ := Finset.mem_filter.mp hi
    obtain ⟨hj', htj⟩ := Finset.mem_filter.mp hj
    obtain ⟨ki, hki⟩ := hk i hi'
    obtain ⟨kj, hkj⟩ := hk j hj'
    have e : ∀ l k, w (algebraMap K L (Q.coeff l)) = w p ^ k →
        term l ^ s.den = w p ^ (k * s.den + s.num * l) := fun l k hl ↦ by
      simp only [hterm]
      rw [mul_pow, hupow, hl, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hwp0]
    have heq : w p ^ (ki * s.den + s.num * i) = w p ^ (kj * s.den + s.num * j) := by
      rw [← e i ki hki, ← e j kj hkj, hti, htj]
    have := zpow_injective_of_lt_one hwp0 hwp1 heq
    have h2 : (s.den : ℤ) ∣ s.num * (j - i) := ⟨ki - kj, by linear_combination -this⟩
    have hcop : IsCoprime (s.den : ℤ) s.num := by
      rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_comm]
      exact s.reduced
    have := hcop.dvd_of_dvd_mul_left h2
    rw [show (i : ℤ) - j = -((j : ℤ) - i) by ring]
    exact (dvd_neg).mpr this
  -- the quotient exponents
  have ht : ∀ i ∈ I, ∃ t : ℕ, i = i₀ + s.den * t := by
    intro i hi
    obtain ⟨c, hc⟩ := hdvd i hi i₀ hi₀I
    have hle := hi₀le i hi
    have hc0 : 0 ≤ c := by
      by_contra hneg
      push Not at hneg
      have : (s.den : ℤ) * c < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hden) hneg
      omega
    refine ⟨c.toNat, ?_⟩
    zify
    rw [Int.toNat_of_nonneg hc0]
    linarith
  choose! t ht using ht
  have hq₀ : Q.coeff i₀ ≠ 0 := hcoeff0 i₀ (Finset.mem_filter.mp hi₀I).1
  have hp0' : algebraMap K L (Q.coeff i₀) ≠ 0 := by simpa using hq₀
  set g := u ^ s.den / p ^ s.num with hg
  have hwg : w g = 1 := by
    rw [hg, map_div₀, map_pow, map_zpow₀, hs, div_self (zpow_ne_zero _ hwp0)]
  set c : ℕ → K := fun i ↦ Q.coeff i * (ϖ : K) ^ (s.num * (t i : ℤ)) / Q.coeff i₀ with hc
  have hid : ∀ i ∈ I, algebraMap K L (Q.coeff i) * u ^ i =
      algebraMap K L (Q.coeff i₀) * u ^ i₀ * (algebraMap K L (c i) * g ^ t i) := by
    intro i hi
    have hi' := ht i hi
    have hpz : p ^ (s.num * (t i : ℤ)) ≠ 0 := zpow_ne_zero _ hp0
    simp only [hc, hg, map_div₀, map_mul, map_zpow₀]
    rw [div_pow, ← zpow_natCast (p ^ s.num), ← zpow_mul]
    rw [show u ^ i = u ^ i₀ * (u ^ s.den) ^ t i by rw [← pow_mul, ← pow_add, ← hi']]
    field_simp
    rfl
  have hval : ∀ i ∈ I, w (algebraMap K L (c i)) = 1 := by
    intro i hi
    have h1 := congrArg w (hid i hi)
    rw [map_mul, map_mul, map_mul, map_mul, map_pow, map_pow, map_pow, hwg, one_pow, mul_one]
      at h1
    have h2 : term i = term i₀ := by
      rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hi₀I).2]
    have h3 : term i₀ * w (algebraMap K L (c i)) = term i₀ * 1 := by
      calc term i₀ * w (algebraMap K L (c i)) = term i := by simpa only [hterm] using h1.symm
        _ = term i₀ * 1 := by rw [h2, mul_one]
    exact mul_left_cancel₀ (hterm0 i₀ (Finset.mem_filter.mp hi₀I).1) h3
  have hcO : ∀ i ∈ I, c i ∈ O ∧ (c i)⁻¹ ∈ O := by
    intro i hi
    obtain ⟨-, h1, h2⟩ := (valuation_eq_one_iff_mem_and_inv_mem U).mp (hval i hi)
    rw [← map_inv₀] at h2
    rw [← ValuationSubring.mem_comap, hU] at h1 h2
    exact ⟨h1, h2⟩
  set c' : ℕ → O := fun i ↦ if h : c i ∈ O then ⟨c i, h⟩ else 0 with hc'
  have hc'v : ∀ i ∈ I, ((c' i : O) : K) = c i := fun i hi ↦ by
    simp [hc', dif_pos (hcO i hi).1]
  set R : O[X] := ∑ i ∈ I, monomial (t i) (c' i) with hR
  have htinj : ∀ i ∈ I, ∀ j ∈ I, t i = t j → i = j := fun i hi j hj h ↦ by
    rw [ht i hi, ht j hj, h]
  have hRcoeff : R.coeff (t i₀) = c' i₀ := by
    rw [hR, finsetSum_coeff, Finset.sum_eq_single i₀]
    · simp
    · intro j hj hji
      rw [coeff_monomial, if_neg]
      exact fun h ↦ hji (htinj j hj i₀ hi₀I h)
    · exact fun h ↦ (h hi₀I).elim
  have hunit : IsUnit (c' i₀) := by
    refine IsUnit.of_mul_eq_one (⟨(c i₀)⁻¹, (hcO i₀ hi₀I).2⟩ : O) (Subtype.ext ?_)
    have hc0 : c i₀ ≠ 0 := by
      intro h; have := hval i₀ hi₀I; rw [h, map_zero, map_zero] at this; exact zero_ne_one this
    simp [hc'v i₀ hi₀I, hc0]
  have hRres : R.map (IsLocalRing.residue O) ≠ 0 := by
    intro h
    have := congrArg (fun P ↦ P.coeff (t i₀)) h
    simp only [coeff_map, hRcoeff, coeff_zero] at this
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunit this
  have hRval := htr.2 R hRres
  have hReval : aeval g (R.map (algebraMap O K)) = ∑ i ∈ I, algebraMap K L (c i) * g ^ t i := by
    rw [hR, Polynomial.map_sum, map_sum]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [Polynomial.map_monomial, aeval_monomial, ← hc'v i hi]
    rfl
  -- the sum over the maximal terms
  have hsumI : ∑ i ∈ I, algebraMap K L (Q.coeff i) * u ^ i =
      algebraMap K L (Q.coeff i₀) * u ^ i₀ * aeval g (R.map (algebraMap O K)) := by
    rw [hReval, Finset.mul_sum]
    exact Finset.sum_congr rfl hid
  have hvalI : w (∑ i ∈ I, algebraMap K L (Q.coeff i) * u ^ i) = M := by
    rw [hsumI, map_mul, hRval, mul_one, map_mul, map_pow]
    exact (Finset.mem_filter.mp hi₀I).2
  have hrest : w (∑ i ∈ Q.support.filter (fun i ↦ ¬ term i = M),
      algebraMap K L (Q.coeff i) * u ^ i) < M := by
    refine Valuation.map_sum_lt _ hM0 fun i hi ↦ ?_
    obtain ⟨hi', hne'⟩ := Finset.mem_filter.mp hi
    rw [map_mul, map_pow]
    exact lt_of_le_of_ne (hmax i hi') hne'
  have hexp : aeval u Q = ∑ i ∈ Q.support, algebraMap K L (Q.coeff i) * u ^ i := by
    conv_lhs => rw [Q.as_sum_support_C_mul_X_pow]
    simp only [map_sum, map_mul, aeval_C, map_pow, aeval_X]
  rw [hexp, ← Finset.sum_filter_add_sum_filter_not Q.support (fun i ↦ term i = M),
    Valuation.map_add_eq_of_lt_left _ (by rw [hvalI]; exact hrest), hvalI]

open Classical in
variable (O ϖ) in
/-- The `ϖ`-adic order of an element of `K` (`0` for `q = 0`). -/
noncomputable def ordO (q : K) : ℤ :=
  if h : ∃ k : ℤ, O.valuation q = O.valuation (ϖ : K) ^ k then h.choose else 0

/-- The value of a nonzero constant is the power of the uniformizer given by its order. -/
lemma valuation_eq_zpow_ordO (hU : U.comap (algebraMap K L) = O) (hϖ : Irreducible ϖ)
    {q : K} (hq : q ≠ 0) :
    U.valuation (algebraMap K L q) = U.valuation (algebraMap K L (ϖ : K)) ^ ordO O ϖ q := by
  have hex : ∃ k : ℤ, O.valuation q = O.valuation (ϖ : K) ^ k := by
    have hO : O.comap (algebraMap K K) = O := by ext; simp
    simpa using exists_valuation_eq_zpow_of_comap (L := K) (U := O) hO hϖ hq
  have hk : O.valuation q = O.valuation (ϖ : K) ^ ordO O ϖ q := by
    rw [ordO, dif_pos hex]; exact hex.choose_spec
  have hϖ0 : (ϖ : K) ≠ 0 := by exact_mod_cast hϖ.ne_zero
  set k := ordO O ϖ q
  set e := q * (ϖ : K) ^ (-k)
  have he : O.valuation e = 1 := by
    rw [map_mul, map_zpow₀, hk, ← zpow_add₀ (by simpa using hϖ0), add_neg_cancel, zpow_zero]
  obtain ⟨-, he1, he2⟩ := (valuation_eq_one_iff_mem_and_inv_mem O).mp he
  have hUe : U.valuation (algebraMap K L e) = 1 := by
    rw [valuation_eq_one_iff_mem_and_inv_mem]
    refine ⟨by simp [e, hq, hϖ0, zpow_ne_zero], ?_, ?_⟩
    · rw [← ValuationSubring.mem_comap, hU]; exact he1
    · rw [← map_inv₀, ← ValuationSubring.mem_comap, hU]; exact he2
  have hq' : q = e * (ϖ : K) ^ k := by
    simp only [e, mul_assoc, ← zpow_add₀ hϖ0, neg_add_cancel, zpow_zero, mul_one]
  rw [hq', map_mul, map_mul, hUe, one_mul, map_zpow₀, map_zpow₀]

variable (O ϖ) in
/-- The **Gauss exponent** of `Q` at the parameter `s = m / d`: `min_i (d · ord(qᵢ) + m i)`;
a monomial point `U` at `s` has `U(Q(u)) ^ d = U(ϖ) ^ gaussExp s Q` (`valuation_aeval_pow`). -/
noncomputable def gaussExp (s : ℚ) (Q : K[X]) : ℤ :=
  if h : Q.support.Nonempty then
    (Q.support.image (fun i ↦ (s.den : ℤ) * ordO O ϖ (Q.coeff i) + s.num * i)).min'
      (h.image _)
  else 0

/-- **Gauss values in exponent form**: for a monomial point `U` at `s` and `Q ≠ 0`,
`U(Q(u)) ^ den s = U(ϖ) ^ gaussExp s Q`; the exponent does not depend on `U`. -/
theorem valuation_aeval_pow_den (hU : U.comap (algebraMap K L) = O) (hϖ : Irreducible ϖ)
    {u : L} {s : ℚ} (hs : IsLogValue U (algebraMap K L (ϖ : K)) u s)
    (htr : IsResidueTranscendental O U (u ^ s.den / algebraMap K L (ϖ : K) ^ s.num))
    {Q : K[X]} (hQ : Q ≠ 0) :
    U.valuation (aeval u Q) ^ s.den =
      U.valuation (algebraMap K L (ϖ : K)) ^ gaussExp O ϖ s Q := by
  classical
  set w := U.valuation
  obtain ⟨hwp0, hwp1⟩ := valuation_uniformizer hU hϖ
  have hne : Q.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (by simpa using hQ)
  set e : ℕ → ℤ := fun i ↦ (s.den : ℤ) * ordO O ϖ (Q.coeff i) + s.num * i with he
  set term : ℕ → _ := fun i ↦ w (algebraMap K L (Q.coeff i)) * w u ^ i with hterm
  have hupow : ∀ i : ℕ, (w u ^ i) ^ s.den = w (algebraMap K L (ϖ : K)) ^ (s.num * i) :=
    fun i ↦ by
      rw [← pow_mul, mul_comm, pow_mul, hs, ← zpow_natCast, ← zpow_mul, mul_comm]
  have hpow : ∀ i ∈ Q.support, term i ^ s.den = w (algebraMap K L (ϖ : K)) ^ e i := by
    intro i hi
    simp only [hterm, he]
    rw [mul_pow, hupow, valuation_eq_zpow_ordO hU hϖ (by simpa using hi), ← zpow_natCast,
      ← zpow_mul, ← zpow_add₀ hwp0, mul_comm (ordO O ϖ (Q.coeff i))]
  obtain ⟨im, him, hmin⟩ := Finset.exists_min_image Q.support e hne
  have hge : ∀ i ∈ Q.support, term i ≤ term im := by
    intro i hi
    have h0 : (0 : U.ValueGroup) < w (algebraMap K L (ϖ : K)) := zero_lt_iff.mpr hwp0
    rw [← pow_le_pow_iff_left₀ zero_le zero_le s.den_nz, hpow i hi, hpow im him,
      zpow_le_zpow_iff_right_of_lt_one₀ h0 hwp1]
    exact hmin i hi
  have hsup : Q.support.sup term = term im :=
    le_antisymm (Finset.sup_le hge) (Finset.le_sup (f := term) him)
  rw [valuation_aeval_eq_sup_of_monomial hU hϖ hs htr Q]
  change Q.support.sup term ^ s.den = _
  rw [hsup, hpow im him]
  congr 1
  rw [gaussExp, dif_pos hne]
  refine le_antisymm ?_ ?_
  · exact Finset.le_min' _ _ _ (fun y hy ↦ by
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hy; exact hmin i hi)
  · exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ him)

end SemistableReduction
