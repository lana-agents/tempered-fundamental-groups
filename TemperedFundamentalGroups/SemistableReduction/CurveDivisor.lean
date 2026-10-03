/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChangeOfGenerator
import TemperedFundamentalGroups.SemistableReduction.CurvePlace
import TemperedFundamentalGroups.SemistableReduction.WeakApproximation

/-!
# Divisors of a function field of one variable

Blueprint §9.5, R1–R3. Let `k` be algebraically closed and `κ / k` a function field of one
variable (`IsCurveFunctionField k κ`), with places `CurvePlace k κ`
(`SemistableReduction.CurvePlace`).

* `IsCurveFunctionField.isAlgebraic_adjoin`, `IsCurveFunctionField.finiteDimensional_adjoin`:
  `κ` is finite over `k(f)` for every `f` transcendental over `k`; every `f ∉ k` is
  transcendental (`transcendental_of_notMem_range`);
* `CurvePlace.exists_valuation_sub_lt_one`: the residue field of every place is `k`;
* `CurvePlace.exists_valuation_eq_and_le` (weak approximation, from
  `SemistableReduction.WeakApproximation`): for distinct places `P, Q₁, …, Q_r` there are
  elements with prescribed order at `P` and arbitrarily high order at the `Qᵢ`;
* `CurvePlace.sum_poleOrder_le`: for `f ∉ k`, `∑_{P pole of f} ord_P(1/f) ≤ [κ : k(f)]` (elements
  `w_{P,j}` with `ord_P w_{P,j} = j < e_P` and high order at the other poles are linearly
  independent over `k(f)`: Stichtenoth, Thm. 1.4.11); in particular `f` has finitely many poles
  (`CurvePlace.finite_setOf_notMem`);
* `CurveDivisor k κ = CurvePlace k κ →₀ ℤ`, the pole divisor `poleDivisor k f`, the principal
  divisor `divisor k f = (f)₀ - (f)_∞` with `v_P(f) = exp (-(divisor k f P))`.
-/

open IntermediateField Polynomial Valuation WithZero
open scoped WithZero

namespace SemistableReduction

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]

section Transcendental

/-- `κ` is algebraic over `k(f)` for every `f` transcendental over `k`. -/
lemma IsCurveFunctionField.isAlgebraic_adjoin [IsCurveFunctionField k κ] {f : κ}
    (hf : Transcendental k f) : Algebra.IsAlgebraic k⟮f⟯ κ := by
  obtain ⟨x, -, hfin⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ)
  have hxf : IsAlgebraic k⟮f⟯ x := ChangeOfGenerator.isAlgebraic_adjoin_of_isAlgebraic
    (Algebra.IsAlgebraic.isAlgebraic (R := k⟮x⟯) f) hf
  exact ⟨fun y ↦ ChangeOfGenerator.isAlgebraic_adjoin_trans
    (Algebra.IsAlgebraic.isAlgebraic (R := k⟮x⟯) y) hxf⟩

/-- `κ` is finite over `k(f)` for every `f` transcendental over `k`. -/
lemma IsCurveFunctionField.finiteDimensional_adjoin [IsCurveFunctionField k κ] {f : κ}
    (hf : Transcendental k f) : FiniteDimensional k⟮f⟯ κ := by
  obtain ⟨x, -, hfin⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ)
  haveI : Algebra.EssFiniteType k k⟮x⟯ := by
    rw [IntermediateField.essFiniteType_iff]
    exact ⟨{x}, by simp⟩
  haveI : Algebra.EssFiniteType k κ := Algebra.EssFiniteType.comp k k⟮x⟯ κ
  haveI : Algebra.EssFiniteType k⟮f⟯ κ := Algebra.EssFiniteType.of_comp k k⟮f⟯ κ
  haveI := isAlgebraic_adjoin hf
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

/-- Over an algebraically closed field, a non-constant element is transcendental. -/
lemma transcendental_of_notMem_range [IsAlgClosed k] {f : κ} (hf : f ∉ (algebraMap k κ).range) :
    Transcendental k f := fun halg ↦ hf <| minpoly.mem_range_of_degree_eq_one k f
  (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible halg.isIntegral))

end Transcendental

section WithZero

lemma WithZero.exp_add_one_le_of_lt {a : ℤᵐ⁰} {n : ℤ} (h : exp n < a) : exp (n + 1) ≤ a := by
  have ha : a ≠ 0 := ne_zero_of_lt h
  rw [← exp_log ha, exp_lt_exp] at h
  rw [← exp_log ha, exp_le_exp]
  omega

lemma WithZero.le_exp_of_lt_exp_add_one {a : ℤᵐ⁰} {n : ℤ} (h : a < exp (n + 1)) : a ≤ exp n := by
  rcases eq_or_ne a 0 with rfl | ha
  · exact zero_le
  rw [← exp_log ha, exp_lt_exp] at h
  rw [← exp_log ha, exp_le_exp]
  omega

end WithZero

namespace CurvePlace

variable [IsAlgClosed k] [IsCurveFunctionField k κ]

section Residue

/-- **The residue field of a place is `k`**: every `f ∈ O_P` is congruent to a constant. Otherwise
all `f - c` are units, so all nonzero polynomials in `f` are units, `k(f) ⊆ O_P`, and then
`κ ⊆ O_P` since `κ / k(f)` is algebraic. -/
theorem exists_valuation_sub_lt_one (P : CurvePlace k κ) {f : κ} (hf : f ∈ P.V) :
    ∃ c : k, P.valuation (f - algebraMap k κ c) < 1 := by
  by_contra! H
  have hk := P.valuation_algebraMap_le_one
  set w := P.valuation
  have hunit (c : k) : w (f - algebraMap k κ c) = 1 :=
    le_antisymm (P.valuation_le_one_iff.2 (sub_mem hf (P.algebraMap_mem c))) (H c)
  have htr : Transcendental k f := by
    intro halg
    obtain ⟨c, rfl⟩ : f ∈ (algebraMap k κ).range := minpoly.mem_range_of_degree_eq_one k f
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible halg.isIntegral))
    have := hunit c
    simp at this
  haveI := IsCurveFunctionField.isAlgebraic_adjoin htr
  have hpoly (s : k[X]) (hs0 : s ≠ 0) : w (aeval f s) = 1 := by
    rw [aeval_eq_prod, map_mul, valuation_algebraMap_eq_one hk (leadingCoeff_ne_zero.2 hs0),
      one_mul, map_multiset_prod]
    refine Multiset.prod_eq_one fun a ha ↦ ?_
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨α, -, rfl⟩ := Multiset.mem_map.1 hb
    exact hunit α
  have hK (y : k⟮f⟯) : w y ≤ 1 := by
    obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff k (y : κ)).1 y.2
    rw [hrs, map_div₀]
    rcases eq_or_ne s 0 with rfl | hs0
    · simp
    rw [hpoly s hs0, div_one]
    exact valuation_aeval_le_one hk (P.valuation_le_one_iff.2 hf) r
  refine P.ne_top (top_unique fun g _ ↦ P.valuation_le_one_iff.1 ?_)
  exact valuation_le_of_aeval_eq_zero (K := k⟮f⟯)
    (minpoly.monic (Algebra.IsIntegral.isIntegral g)) (minpoly.aeval _ g) le_rfl
    fun i ↦ hK ((minpoly k⟮f⟯ g).coeff i)

end Residue

section Approximation

/-- Distinct places have incomparable valuation rings. -/
lemma exists_mem_notMem_of_ne {P Q : CurvePlace k κ} (h : P ≠ Q) : ∃ a ∈ P.V, a ∉ Q.V := by
  by_contra! H
  exact h (CurvePlace.ext (ValuationSubring.eq_of_le_of_ne_top P.V (fun a ha ↦ H a ha) Q.ne_top))

lemma incomparable {P Q : CurvePlace k κ} (h : P ≠ Q) :
    WeakApproximation.Incomparable (fun P : CurvePlace k κ ↦ P.valuation) P Q := by
  obtain ⟨a, haP, haQ⟩ := exists_mem_notMem_of_ne h
  obtain ⟨b, hbQ, hbP⟩ := exists_mem_notMem_of_ne (Ne.symm h)
  exact ⟨⟨a, P.valuation_le_one_iff.2 haP, not_le.1 (mt Q.valuation_le_one_iff.1 haQ)⟩,
    ⟨b, Q.valuation_le_one_iff.2 hbQ, not_le.1 (mt P.valuation_le_one_iff.1 hbP)⟩⟩

/-- **Weak approximation**: an element close to `1` at `P` and close to `0` at finitely many other
places. -/
theorem exists_valuation_sub_one_lt_one (P : CurvePlace k κ) (S : Finset (CurvePlace k κ))
    (ε : CurvePlace k κ → ℤᵐ⁰) (hε : ∀ Q, ε Q ≠ 0) :
    ∃ z : κ, P.valuation (z - 1) < 1 ∧ ∀ Q ∈ S, Q ≠ P → Q.valuation z ≤ ε Q := by
  obtain ⟨u, hu, huS⟩ := WeakApproximation.exists_lt_one_and_one_lt
    (fun P : CurvePlace k κ ↦ P.valuation) P S fun Q _ hQ ↦ incomparable (Ne.symm hQ)
  set s : ℕ := 1 + ∑ Q ∈ S, (-log (ε Q)).toNat
  have hs : s ≠ 0 := by omega
  obtain ⟨h1, h2⟩ := WeakApproximation.valuation_inv_one_add_pow
    (fun P : CurvePlace k κ ↦ P.valuation) hu hs
  refine ⟨(1 + u ^ s)⁻¹, ?_, fun Q hQ hQP ↦ ?_⟩
  · rw [h1]
    exact pow_lt_one₀ zero_le hu hs
  · rw [h2 Q (huS Q hQ hQP)]
    have hu1 : exp 1 ≤ Q.valuation u := by
      simpa using WithZero.exp_add_one_le_of_lt (n := 0) (by simpa using huS Q hQ hQP)
    have hQs : (-log (ε Q)).toNat ≤ ∑ Q ∈ S, (-log (ε Q)).toNat :=
      Finset.single_le_sum (f := fun Q ↦ (-log (ε Q)).toNat) (fun _ _ ↦ Nat.zero_le _) hQ
    calc (Q.valuation u ^ s)⁻¹ ≤ (exp 1 ^ s)⁻¹ := by
          refine inv_anti₀ (pow_pos exp_pos s) (pow_le_pow_left₀ zero_le hu1 s)
      _ = exp (-(s : ℤ)) := by simp
      _ ≤ ε Q := by
          rw [← exp_log (hε Q), exp_le_exp]
          have := Int.self_le_toNat (-log (ε Q))
          omega

/-- An element of prescribed order `-j` at `P` (value `exp j`) and small value at finitely many
other places. -/
theorem exists_valuation_eq_and_le (P : CurvePlace k κ) (S : Finset (CurvePlace k κ)) (j : ℤ)
    (ε : CurvePlace k κ → ℤᵐ⁰) (hε : ∀ Q, ε Q ≠ 0) :
    ∃ w : κ, P.valuation w = exp j ∧ ∀ Q ∈ S, Q ≠ P → Q.valuation w ≤ ε Q := by
  obtain ⟨π, hπ⟩ := P.exists_valuation_eq_exp_neg_one
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact exp_ne_zero hπ.symm
  have hne (Q : CurvePlace k κ) : Q.valuation (π ^ (-j)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (zpow_ne_zero _ hπ0)
  obtain ⟨z, hz1, hzS⟩ := exists_valuation_sub_one_lt_one P S
    (fun Q ↦ ε Q / Q.valuation (π ^ (-j))) fun Q ↦ div_ne_zero (hε Q) (hne Q)
  have hz : P.valuation z = 1 := by
    have : z = (z - 1) + 1 := by ring
    rw [this, Valuation.map_add_eq_of_lt_right, map_one]
    rwa [map_one]
  refine ⟨z * π ^ (-j), ?_, fun Q hQ hQP ↦ ?_⟩
  · rw [map_mul, hz, one_mul, map_zpow₀, hπ, ← exp_zsmul]
    simp
  · rw [map_mul]
    calc Q.valuation z * Q.valuation (π ^ (-j)) ≤
          ε Q / Q.valuation (π ^ (-j)) * Q.valuation (π ^ (-j)) := by
          gcongr
          exact hzS Q hQ hQP
      _ = ε Q := div_mul_cancel₀ _ (hne Q)

end Approximation

section PoleOrder

/-- At a pole, `v_P(f) = exp (ord_P(1/f))`. -/
lemma valuation_eq_exp_poleOrder (P : CurvePlace k κ) {f : κ} (hf : f ∉ P.V) :
    P.valuation f = exp (P.poleOrder f : ℤ) := by
  have h1 : 1 < P.valuation f := not_le.1 (mt P.valuation_le_one_iff.1 hf)
  have h0 : P.valuation f ≠ 0 := ne_zero_of_lt h1
  have hlog : 0 < log (P.valuation f) := by
    rw [← exp_lt_exp, exp_log h0, exp_zero]
    exact h1
  rw [poleOrder, Int.toNat_of_nonneg hlog.le, exp_log h0]

lemma one_le_poleOrder (P : CurvePlace k κ) {f : κ} (hf : f ∉ P.V) : 1 ≤ P.poleOrder f := by
  rw [Nat.one_le_iff_ne_zero]
  exact fun h ↦ hf (P.poleOrder_eq_zero_iff.1 h)

lemma valuation_le_exp_poleOrder (P : CurvePlace k κ) (f : κ) :
    P.valuation f ≤ exp (P.poleOrder f : ℤ) :=
  P.poleOrder_le_iff.1 le_rfl

/-- The order at the places where `y` has a zero is uniform on `k(y)`. -/
lemma exists_zpow_of_mem_adjoin {y φ : κ} (hy : y ≠ 0) (hφ : φ ∈ k⟮y⟯) (hφ0 : φ ≠ 0) :
    ∃ o : ℤ, ∀ P : CurvePlace k κ, P.valuation y < 1 → P.valuation φ = P.valuation y ^ o := by
  obtain ⟨r, s, rfl⟩ := (mem_adjoin_simple_iff k φ).1 hφ
  obtain ⟨hr, hs⟩ := div_ne_zero_iff.1 hφ0
  have hr' : r ≠ 0 := by rintro rfl; simp at hr
  have hs' : s ≠ 0 := by rintro rfl; simp at hs
  refine ⟨(r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0, fun P hP ↦ ?_⟩
  rw [map_div₀, valuation_aeval_eq P.valuation_algebraMap_le_one hP hr',
    valuation_aeval_eq P.valuation_algebraMap_le_one hP hs',
    zpow_sub₀ ((Valuation.ne_zero_iff _).2 hy), zpow_natCast, zpow_natCast]

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma mem_adjoin_inv {f g : κ} (hg : g ∈ k⟮f⟯) : g ∈ k⟮f⁻¹⟯ := by
  refine adjoin_simple_le_iff.2 ?_ hg
  simpa using inv_mem (mem_adjoin_simple_self k f⁻¹)

/-- **Pole orders are bounded by the degree** (Stichtenoth, Thm. 1.4.11, `≤`): for `f ∉ k` and any
finite set `S` of places, `∑_{P ∈ S} poleOrder_P f ≤ [κ : k(f)]`. For each pole `P ∈ S` (of order
`e_P`) and `j < e_P` choose `w_{P,j}` of order `j` at `P` and of order `≥ e_Q` at the other poles
`Q ∈ S`; these are linearly independent over `k(f)`: in a nontrivial relation, normalize the
coefficients by a power of `1/f` (all coefficients `φ` have the same order `o(φ)` at all zeros of
`1/f`), and look at the place `P` and the smallest `j` for which the coefficient of `w_{P,j}` has
minimal `o`. -/
theorem sum_poleOrder_le {f : κ} (hf : f ∉ (algebraMap k κ).range)
    (S : Finset (CurvePlace k κ)) :
    ∑ P ∈ S, P.poleOrder f ≤ Module.finrank k⟮f⟯ κ := by
  classical
  have htr := transcendental_of_notMem_range hf
  haveI := IsCurveFunctionField.finiteDimensional_adjoin htr
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hf ⟨0, map_zero _⟩
  set T := S.filter fun P ↦ f ∉ P.V
  have hsum : ∑ P ∈ S, P.poleOrder f = ∑ P ∈ T, P.poleOrder f := by
    rw [Finset.sum_filter_of_ne]
    intro P _ h
    exact fun hP ↦ h (P.poleOrder_eq_zero_iff.2 hP)
  rw [hsum]
  set e : CurvePlace k κ → ℕ := fun P ↦ P.poleOrder f
  have hyv (P : CurvePlace k κ) (hP : P ∈ T) : P.valuation f⁻¹ = exp (-(e P : ℤ)) := by
    rw [map_inv₀, P.valuation_eq_exp_poleOrder (Finset.mem_filter.1 hP).2, exp_neg]
  have hy1 (P : CurvePlace k κ) (hP : P ∈ T) : P.valuation f⁻¹ < 1 := by
    rw [hyv P hP, ← exp_zero, exp_lt_exp]
    have := P.one_le_poleOrder (Finset.mem_filter.1 hP).2
    change -((P.poleOrder f : ℕ) : ℤ) < 0
    omega
  have hex (P : CurvePlace k κ) (j : ℕ) : ∃ w : κ, P.valuation w = exp (-(j : ℤ)) ∧
      ∀ Q ∈ T, Q ≠ P → Q.valuation w ≤ exp (-(e Q : ℤ)) :=
    exists_valuation_eq_and_le P T _ _ fun _ ↦ exp_ne_zero
  choose w hw1 hw2 using hex
  set I := T.sigma fun P ↦ Finset.range (e P)
  have hli : LinearIndependent k⟮f⟯ (fun i : I ↦ w i.1.1 i.1.2) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    by_contra! hne
    -- the common order of the coefficients at the zeros of `1/f`
    have hord (i : I) : g i ≠ 0 → ∃ o : ℤ, ∀ P : CurvePlace k κ, P.valuation f⁻¹ < 1 →
        P.valuation (g i : κ) = P.valuation f⁻¹ ^ o := fun hgi ↦
      exists_zpow_of_mem_adjoin (inv_ne_zero hf0) (mem_adjoin_inv (g i).2)
        (by exact_mod_cast hgi)
    choose! o ho using hord
    obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image (Finset.univ.filter fun i ↦ g i ≠ 0) o
      (by obtain ⟨i, hi⟩ := hne; exact ⟨i, by simpa using hi⟩)
    replace hi₀ : g i₀ ≠ 0 := (Finset.mem_filter.1 hi₀).2
    set P₀ := i₀.1.1
    have hP₀ : P₀ ∈ T := (Finset.mem_sigma.1 i₀.2).1
    obtain ⟨i₁, hi₁, hmin₁⟩ := Finset.exists_min_image
      (Finset.univ.filter fun i : I ↦ i.1.1 = P₀ ∧ g i ≠ 0 ∧ o i = o i₀) (fun i ↦ i.1.2)
      ⟨i₀, Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl, hi₀, rfl⟩⟩
    obtain ⟨hi₁P, hi₁g, hi₁o⟩ := (Finset.mem_filter.1 hi₁).2
    set μ := o i₀
    set E : ℤ := (e P₀ : ℤ)
    have hj₁ : (i₁.1.2 : ℤ) < E := by
      have h := (Finset.mem_sigma.1 i₁.2).2
      rw [Finset.mem_range, hi₁P] at h
      exact Int.ofNat_lt.2 h
    -- values at `P₀`
    have hvg (i : I) (hgi : g i ≠ 0) : P₀.valuation (g i : κ) = exp (-(E * o i)) := by
      rw [ho i hgi P₀ (hy1 P₀ hP₀), hyv P₀ hP₀, ← exp_zsmul]
      congr 1
      simp only [smul_eq_mul, E]
      ring
    set t : I → κ := fun i ↦ g i • w i.1.1 i.1.2
    have ht1 : P₀.valuation (t i₁) = exp (-(E * μ) - i₁.1.2) := by
      simp only [t, Algebra.smul_def, IntermediateField.algebraMap_apply, map_mul]
      have hw1' : P₀.valuation (w i₁.1.1 i₁.1.2) = exp (-(i₁.1.2 : ℤ)) := by
        rw [← hi₁P]
        exact hw1 _ _
      rw [hvg i₁ hi₁g, hw1', hi₁o, ← exp_add, sub_eq_add_neg]
    have hlt (i : I) (hi : i ≠ i₁) : P₀.valuation (t i) < P₀.valuation (t i₁) := by
      rw [ht1]
      by_cases hgi : g i = 0
      · simp only [t, hgi, zero_smul, map_zero]
        exact exp_pos
      have hoi : μ ≤ o i := hmin i (by simpa using hgi)
      have hEo : E * μ ≤ E * o i := mul_le_mul_of_nonneg_left hoi (by positivity)
      simp only [t, Algebra.smul_def, IntermediateField.algebraMap_apply, map_mul]
      rw [hvg i hgi]
      by_cases hiP : i.1.1 = P₀
      · rw [← hiP, hw1, ← exp_add, exp_lt_exp]
        rcases hoi.lt_or_eq with hoi' | hoi'
        · have : E * (μ + 1) ≤ E * o i := mul_le_mul_of_nonneg_left hoi' (by positivity)
          have : (0 : ℤ) ≤ i.1.2 := Int.natCast_nonneg _
          linarith
        · have hle : i₁.1.2 ≤ i.1.2 := hmin₁ i (by simpa [hiP, hgi] using hoi'.symm)
          have hne : i₁.1.2 ≠ i.1.2 := by
            intro h
            refine hi (Subtype.ext (Sigma.ext (hiP.trans hi₁P.symm) ?_))
            exact heq_of_eq h.symm
          have : (i₁.1.2 : ℤ) < i.1.2 := by exact_mod_cast lt_of_le_of_ne hle hne
          rw [← hoi']
          linarith
      · calc exp (-(E * o i)) * P₀.valuation (w i.1.1 i.1.2) ≤ exp (-(E * o i)) * exp (-E) := by
              gcongr
              exact hw2 i.1.1 i.1.2 P₀ hP₀ (Ne.symm hiP)
          _ < exp (-(E * μ) - i₁.1.2) := by
              rw [← exp_add, exp_lt_exp]
              linarith
    have hsum' : ∑ i, t i = 0 := hg
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i₁)] at hsum'
    have hrest : P₀.valuation (∑ i ∈ Finset.univ.erase i₁, t i) < P₀.valuation (t i₁) := by
      refine Valuation.map_sum_lt _ ?_ fun i hi ↦ hlt i (Finset.ne_of_mem_erase hi)
      rw [ht1]
      exact exp_ne_zero
    have := Valuation.map_add_eq_of_lt_left _ hrest
    rw [hsum', map_zero, ht1] at this
    exact exp_ne_zero this.symm
  have hcard := hli.fintype_card_le_finrank
  rw [Fintype.card_coe, Finset.card_sigma] at hcard
  simpa using hcard

/-- A function has finitely many poles. -/
theorem finite_setOf_notMem (f : κ) : {P : CurvePlace k κ | f ∉ P.V}.Finite := by
  by_cases hf : f ∈ (algebraMap k κ).range
  · obtain ⟨c, rfl⟩ := hf
    simp [algebraMap_mem]
  by_contra hinf
  obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hinf (Module.finrank k⟮f⟯ κ + 1)
  have h1 := sum_poleOrder_le hf t
  have h2 : t.card • 1 ≤ ∑ P ∈ t, P.poleOrder f :=
    Finset.card_nsmul_le_sum _ _ _ fun P hP ↦ P.one_le_poleOrder (ht hP)
  simp only [smul_eq_mul, mul_one] at h2
  omega

end PoleOrder

end CurvePlace

open CurvePlace

variable (k κ) in
/-- Divisors of the function field `κ / k`: finitely supported `ℤ`-valued functions on the places.
Since `k` is algebraically closed, every place has degree `1` and `deg D = Finsupp.degree D`. -/
abbrev CurveDivisor := CurvePlace k κ →₀ ℤ

variable [IsAlgClosed k] [IsCurveFunctionField k κ]

variable (k) in
/-- The pole divisor `(f)_∞ = ∑_P poleOrder_P(f) · P`. -/
noncomputable def poleDivisor (f : κ) : CurveDivisor k κ :=
  Finsupp.ofSupportFinite (fun P ↦ (P.poleOrder f : ℤ)) <|
    (finite_setOf_notMem f).subset fun P hP ↦ by
      simp only [Function.mem_support, ne_eq, Nat.cast_eq_zero] at hP
      exact fun h ↦ hP (P.poleOrder_eq_zero_iff.2 h)

@[simp]
lemma poleDivisor_apply (f : κ) (P : CurvePlace k κ) : poleDivisor k f P = P.poleOrder f := rfl

lemma poleDivisor_nonneg (f : κ) : 0 ≤ poleDivisor k f := fun P ↦ by simp

lemma poleDivisor_algebraMap (c : k) : poleDivisor k (algebraMap k κ c) = 0 := by
  ext P
  simp [P.poleOrder_algebraMap]

variable (k) in
/-- The principal divisor `(f) = (f)₀ - (f)_∞`, with `(f)₀ = (1/f)_∞`. -/
noncomputable def divisor (f : κ) : CurveDivisor k κ := poleDivisor k f⁻¹ - poleDivisor k f

lemma divisor_apply (f : κ) (P : CurvePlace k κ) :
    divisor k f P = -log (P.valuation f) := by
  simp only [divisor, Finsupp.coe_sub, Pi.sub_apply, poleDivisor_apply, CurvePlace.poleOrder,
    map_inv₀, log_inv]
  have := Int.toNat_sub_toNat_neg (-log (P.valuation f))
  rwa [neg_neg] at this

lemma valuation_eq_exp_neg_divisor {f : κ} (hf : f ≠ 0) (P : CurvePlace k κ) :
    P.valuation f = exp (-divisor k f P) := by
  rw [divisor_apply, neg_neg, exp_log ((Valuation.ne_zero_iff _).2 hf)]

lemma divisor_mul {f g : κ} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisor k (f * g) = divisor k f + divisor k g := by
  ext P
  rw [Finsupp.add_apply, divisor_apply, divisor_apply, divisor_apply,
    map_mul, log_mul ((Valuation.ne_zero_iff _).2 hf) ((Valuation.ne_zero_iff _).2 hg)]
  ring

lemma divisor_inv (f : κ) : divisor k f⁻¹ = -divisor k f := by
  simp [divisor, inv_inv]

end SemistableReduction
