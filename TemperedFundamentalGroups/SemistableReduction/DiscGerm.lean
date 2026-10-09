/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Splitting
import TemperedFundamentalGroups.SemistableReduction.SplitDisc
import TemperedFundamentalGroups.SemistableReduction.CompletionAlgClosed

/-!
# Analytic germs at degree-one disc points

Blueprint §9.10, L4 (the bridge). Let `F'/C(x)` be finite separable and `P'` a point of the
integral closure of the disc chart `O_C[t]`, `t = (x - a)/c`, of disc degree one (B5). Then every
`y ∈ R'` has a *germ*: a power series `Σ aᵢ tⁱ` with `|aᵢ| ≤ 1` whose Gauss norm at radius `ρ`
is the value of `y` at the extension of the Gauss point `w_{a,|c|ρ}` centred at `P'`.

Construction (no completions of local rings, no Hensel): with `e ∈ R'` separating `P'` from the
other points over the residue point (`e ≡ 1` on `P'`, `e ∈` the other centres) and the idempotent
iteration `N(u) = 3u² - 2u³`, the traces `pₙ = Tr(Nⁿ(e) y) ∈ O_C[t]` converge, at every disc
valuation, to the value of `y` at `P'` (the local factor at `P'` has degree one, and `Nⁿ(e)` tends
to `1` there and to `0` at the other factors); their coefficients converge in `C`.

* `LocalGlobal.trace_map_eq_sum`: the trace is the sum of the local traces;
  `norm_trace_le`: local traces are bounded by the spectral norm;
  `algebraMap_trace_of_natDegree_eq_one`: in a degree-one factor every element is its trace;
* `Idem.N`, `norm_N_iterate_le`, `norm_one_sub_N_iterate_le`: the iteration converges
  quadratically to `0` resp. `1`;
* `DiscGerm.gaussRat_aeval_eq`, `le_gaussRat_aeval`, `gaussRat_aeval_le_of_terms`: the value of a
  polynomial in `t` at `w_{a,|c'|}` is `max_i |qᵢ| (|c'|/|c|)^i`; `isDiscVal_gaussRat`,
  `gaussDiscVal`; `exists_norm_mem`: norms of `C` are dense below `1`;
* `norm_trace_sub_le`: the approximation step at a degree-one factor;
* **`exists_germ`**, **`exists_germ_gaussNorm`** (`C` need not be complete or algebraically
  closed, §9.11): the polynomials `Qₙ = Tr(Nⁿ(e) y)` converge to `y` at the extension centred at
  `P'` of every disc valuation; their coefficients converge in the completion `Ĉ` to the germ
  `G ∈ Ĉ[[X]]`, uniformly on every disc `|t| ≤ |l| < 1`; at every Gauss point `w_{a,|l c|}` the
  value of `y` there is the Gauss norm `sup_i |aᵢ| |l|^i` of `G`.
-/

open Polynomial NNReal IntermediateField

namespace SemistableReduction

namespace LocalGlobal

open TubeCount

lemma nextCoeff_pow_of_monic {R : Type*} [CommRing R] {q : R[X]} (hq : q.Monic) (k : ℕ) :
    (q ^ k).nextCoeff = k • q.nextCoeff := by
  have := Monic.nextCoeff_prod (Finset.range k) (fun _ ↦ q) fun _ _ ↦ hq
  rwa [Finset.prod_const, Finset.card_range, Finset.sum_const, Finset.card_range] at this

/-- The trace is minus the next coefficient of the characteristic polynomial. -/
lemma trace_eq_neg_nextCoeff_normPoly {F L : Type*} [Field F] [Field L] [Algebra F L]
    [FiniteDimensional F L] (y : L) : Algebra.trace F L y = -(normPoly F y).nextCoeff := by
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, normPoly,
    nextCoeff_pow_of_monic (minpoly.monic (Algebra.IsIntegral.isIntegral y)), nsmul_eq_mul,
    mul_neg]

variable {F K F' : Type*} [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
/-- **The trace is the sum of the local traces** (`F` infinite). -/
theorem trace_map_eq_sum [Infinite F] (y : F') :
    algebraMap F K (Algebra.trace F F' y) =
      ∑ g : Factor F K F', Algebra.trace K (Local K g.1) (toLocal g y) := by
  rw [trace_eq_neg_nextCoeff_normPoly, map_neg, ← nextCoeff_map (algebraMap F K).injective,
    normPoly_map_eq_prod, Monic.nextCoeff_prod _ _ fun g _ ↦ monic_normPoly _,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun g _ ↦ (trace_eq_neg_nextCoeff_normPoly _).symm

/-- **The trace is bounded by the spectral norm.** -/
theorem norm_trace_le (g : K[X]) [Fact (Irreducible g)] (z : Local K g) :
    ‖Algebra.trace K (Local K g) z‖ ≤ ‖z‖ := by
  have hint : IsIntegral K z := Algebra.IsIntegral.isIntegral z
  have hmon := minpoly.monic hint
  set d := (minpoly K z).natDegree
  have hd0 : 0 < d := minpoly.natDegree_pos hint
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, norm_mul, norm_neg]
  have hnat : ‖(Module.finrank K⟮z⟯ (Local K g) : K)‖ ≤ 1 :=
    IsUltrametricDist.norm_natCast_le_one K _
  refine (mul_le_of_le_one_left (norm_nonneg _) hnat).trans ?_
  rw [nextCoeff_of_natDegree_pos hd0]
  have hspec : ‖z‖ = spectralValue (minpoly K z) := rfl
  have hlt : d - 1 < d := Nat.sub_lt hd0 one_pos
  have hterm : ‖(minpoly K z).coeff (d - 1)‖ ^ (1 / (d - (d - 1 : ℕ) : ℝ)) ≤ ‖z‖ := by
    rw [hspec, ← spectralValueTerms_of_lt_natDegree _ hlt]
    exact le_ciSup (spectralValueTerms_bddAbove _) (d - 1)
  have h1 : (d : ℝ) - ((d - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.2 hd0.ne'), Nat.cast_one]
    ring
  rwa [h1, div_one, Real.rpow_one] at hterm

/-- **Degree-one factors.** If `deg g = 1`, every element of `K[X]/(g)` is a scalar, namely its
trace. -/
theorem algebraMap_trace_of_natDegree_eq_one {g : K[X]} [Fact (Irreducible g)]
    (hg : g.natDegree = 1) (z : Local K g) :
    algebraMap K (Local K g) (Algebra.trace K (Local K g) z) = z := by
  have h1 : Module.finrank K (Local K g) = 1 := by rw [finrank_local, hg]
  have hbot : (⊥ : Subalgebra K (Local K g)) = ⊤ := Subalgebra.bot_eq_top_of_finrank_eq_one h1
  obtain ⟨k, rfl⟩ : z ∈ (⊥ : Subalgebra K (Local K g)) := hbot ▸ Algebra.mem_top
  change algebraMap K _ (Algebra.trace K _ (algebraMap K _ k)) = algebraMap K _ k
  rw [Algebra.trace_algebraMap, h1, one_smul]

/-- The norm of a scalar in a degree-one factor. -/
theorem norm_algebraMap_local {g : K[X]} [Fact (Irreducible g)] (k : K) :
    ‖algebraMap K (Local K g) k‖ = ‖k‖ :=
  norm_algebraMap' _ k

end LocalGlobal

/-! ### The idempotent iteration -/

namespace Idem

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

lemma norm_sub_le_max' (x y : E) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

/-- The idempotent iteration `N(u) = 3u² - 2u³`, which fixes `0` and `1` quadratically. -/
def N (u : E) : E := 3 * u ^ 2 - 2 * u ^ 3

lemma norm_N_le {u : E} (hu : ‖u‖ ≤ 1) : ‖N u‖ ≤ ‖u‖ ^ 2 := by
  have h3 : ‖(3 : E)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one E 3
  have h2 : ‖(2 : E)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one E 2
  refine (norm_sub_le_max' _ _).trans (max_le ?_ ?_)
  · rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_left (by positivity) h3
  · rw [norm_mul, norm_pow]
    refine (mul_le_of_le_one_left (by positivity) h2).trans ?_
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) hu

omit [IsUltrametricDist E] in
lemma one_sub_N (u : E) : 1 - N u = (1 - u) ^ 2 * (1 + 2 * u) := by
  unfold N
  ring

lemma norm_one_sub_N_le {u : E} (hu : ‖u‖ ≤ 1) : ‖1 - N u‖ ≤ ‖1 - u‖ ^ 2 := by
  rw [one_sub_N, norm_mul, norm_pow]
  refine mul_le_of_le_one_right (by positivity) ?_
  have h2 : ‖(2 : E)‖ ≤ 1 := by exact_mod_cast IsUltrametricDist.norm_natCast_le_one E 2
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (by rw [norm_one]) ?_)
  rw [norm_mul]
  exact mul_le_one₀ h2 (norm_nonneg _) hu

lemma norm_N_iterate_le {u : E} (hu : ‖u‖ ≤ 1) (n : ℕ) : ‖N^[n] u‖ ≤ ‖u‖ ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 : ‖N^[n] u‖ ≤ 1 := ih.trans (pow_le_one₀ (norm_nonneg _) hu)
    refine (norm_N_le h1).trans ?_
    rw [pow_succ 2 n, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) ih 2

lemma norm_one_sub_N_iterate_le {u : E} (hu : ‖u‖ ≤ 1) (n : ℕ) :
    ‖1 - N^[n] u‖ ≤ ‖1 - u‖ ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h1 : ‖N^[n] u‖ ≤ 1 := by
      have hb : ‖1 - N^[n] u‖ ≤ 1 := ih.trans (pow_le_one₀ (norm_nonneg _) (by
        refine (norm_sub_le_max' _ _).trans (max_le (by rw [norm_one]) hu)))
      calc ‖N^[n] u‖ = ‖1 - (1 - N^[n] u)‖ := by rw [sub_sub_cancel]
        _ ≤ max ‖(1 : E)‖ ‖1 - N^[n] u‖ := norm_sub_le_max' _ _
        _ ≤ 1 := max_le (by rw [norm_one]) hb
    refine (norm_one_sub_N_le h1).trans ?_
    rw [pow_succ 2 n, pow_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) ih 2

/-- `N` is a polynomial with integer coefficients, so it commutes with ring homomorphisms. -/
lemma map_N_iterate {E₁ E₂ : Type*} [CommRing E₁] [CommRing E₂] (f : E₁ →+* E₂) (u : E₁) (n : ℕ) :
    f ((fun v : E₁ ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] u) =
      (fun v : E₂ ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] (f u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
    simp [map_ofNat]

end Idem

/-! ### Values of polynomials in the disc coordinate -/

namespace DiscGerm

open DiscCount Gauss

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] {a c : C}

omit [IsUltrametricDist C] in
/-- `(x - a)/c = (c'/c) · (x - a)/c'`. -/
lemma gaussCoord_eq (hc : c ≠ 0) {c' : C} (hc' : c' ≠ 0) :
    gaussCoord a c = algebraMap C (RatFunc C) (c' / c) * gaussCoord a c' := by
  have h1 := X_eq_gaussCoord (a := a) hc
  have h2 := X_eq_gaussCoord (a := a) hc'
  have hc0 : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
  have key : algebraMap C (RatFunc C) c * gaussCoord a c =
      algebraMap C (RatFunc C) c' * gaussCoord a c' := by
    have := h1.symm.trans h2
    exact add_right_cancel this
  rw [map_div₀, div_mul_eq_mul_div, ← key, mul_div_cancel_left₀ _ hc0]

omit [IsUltrametricDist C] in
/-- A polynomial in `t = (x - a)/c` is a polynomial in `t' = (x - a)/c'`. -/
lemma aeval_gaussCoord_eq (hc : c ≠ 0) {c' : C} (hc' : c' ≠ 0) (Q : C[X]) :
    aeval (gaussCoord a c) Q =
      aeval (gaussCoord a c') (Q.comp (Polynomial.C (c' / c) * X)) := by
  rw [aeval_comp, map_mul, aeval_C, aeval_X, gaussCoord_eq hc hc']

/-- **Gauss value of a polynomial in the disc coordinate.** At `w_{a,|c'|}` the value of `Q(t)`
is `max_i |qᵢ| (|c'|/|c|)^i`; in particular each term is a lower bound. -/
lemma gaussRat_aeval_eq (hc : c ≠ 0) {c' : C} (hc' : c' ≠ 0) (Q : C[X]) :
    gaussRat (NormedField.valuation (K := C)) a (Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc'))
        (aeval (gaussCoord a c) Q) =
      Gauss.sup (NormedField.valuation (K := C)) 1 (Q.comp (Polynomial.C (c' / c) * X)) := by
  rw [aeval_gaussCoord_eq hc hc']
  exact gaussRat_aeval_gaussLin rfl _

lemma le_gaussRat_aeval (hc : c ≠ 0) {c' : C} (hc' : c' ≠ 0) (Q : C[X]) (i : ℕ) :
    ‖Q.coeff i‖₊ * (‖c'‖₊ / ‖c‖₊) ^ i ≤
      gaussRat (NormedField.valuation (K := C)) a (Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc'))
        (aeval (gaussCoord a c) Q) := by
  rw [gaussRat_aeval_eq hc hc']
  have := term_le_sup (v := NormedField.valuation (K := C)) (r := 1)
    (Q.comp (Polynomial.C (c' / c) * X)) i
  simp only [term, Units.val_one, one_pow, mul_one, SplitDisc.coeff_comp_C_mul_X,
    NormedField.valuation_apply] at this
  rwa [nnnorm_mul, nnnorm_pow, nnnorm_div] at this

/-- The Gauss points `w_{a,|c'|}` with `|c'| < |c|` are disc valuations of `|x - a| < |c|`. -/
lemma isDiscVal_gaussRat (hc : c ≠ 0) {c' : C} (hc' : c' ≠ 0) (hlt : ‖c'‖ < ‖c‖) :
    IsDiscVal a c
      (gaussRat (NormedField.valuation (K := C)) a
        (Units.mk0 ‖c'‖₊ (nnnorm_ne_zero_iff.2 hc'))) := by
  refine ⟨fun b ↦ by rw [gaussRat_algebraMap_C]; rfl, ?_⟩
  have h := gaussRat_aeval_eq (a := a) hc hc' X
  rw [aeval_X] at h
  rw [h, X_comp, Gauss.sup_mul, Gauss.sup_C, Gauss.sup_X, Units.val_one, mul_one,
    NormedField.valuation_apply, nnnorm_div, div_lt_one (nnnorm_pos.2 hc)]
  exact_mod_cast hlt

omit [IsUltrametricDist C] in
/-- Values of polynomials in `t` at disc valuations are bounded by `max_i |qᵢ| ν(t)^i`. -/
lemma valuation_aeval_le {ν : Valuation (RatFunc C) ℝ≥0} (hν : IsDiscVal a c ν) {Q : C[X]}
    {M : ℝ≥0} (hM : ∀ i, ‖Q.coeff i‖₊ * ν (gaussCoord a c) ^ i ≤ M) :
    ν (aeval (gaussCoord a c) Q) ≤ M := by
  rw [aeval_eq_sum_range]
  refine Valuation.map_sum_le _ fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, map_pow, hν.map_C]
  exact hM i

omit [IsUltrametricDist C] in
/-- In an algebraically closed nontrivially normed field the norms are dense below `1`. -/
lemma exists_norm_mem [IsAlgClosed C] {θ : ℝ} (hθ : θ < 1) :
    ∃ l : C, l ≠ 0 ∧ θ ≤ ‖l‖ ∧ ‖l‖ < 1 := by
  obtain ⟨μ, hμ0, hμ1⟩ := NormedField.exists_norm_lt_one C
  -- `‖μ‖^(1/m) → 1`
  have hlim : Filter.Tendsto (fun m : ℕ ↦ ‖μ‖ ^ ((m + 1 : ℝ)⁻¹)) Filter.atTop (nhds 1) := by
    have h := (Real.continuousAt_const_rpow (a := ‖μ‖) hμ0.ne').tendsto.comp
      (tendsto_inv_atTop_zero.comp (Filter.tendsto_atTop_add_const_right _ 1
        tendsto_natCast_atTop_atTop))
    simp only [Function.comp_def, Real.rpow_zero] at h
    refine h.congr fun m ↦ ?_
    rfl
  obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds hθ)).exists
  obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq μ (Nat.succ_pos m)
  have hnorm : ‖l‖ = ‖μ‖ ^ ((m + 1 : ℝ)⁻¹) := by
    have h := congrArg norm hl
    rw [norm_pow] at h
    rw [← h, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), Nat.cast_succ,
      mul_inv_cancel₀ (by positivity), Real.rpow_one]
  have hl0 : l ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero m)] at hl
    exact (norm_pos_iff.1 hμ0) hl.symm
  refine ⟨l, hl0, hnorm ▸ hm.le, ?_⟩
  rw [hnorm]
  exact Real.rpow_lt_one hμ0.le hμ1 (by positivity)

omit [IsUltrametricDist C] in
/-- `valuation_aeval_le` with real bounds. -/
lemma valuation_aeval_le' {ν : Valuation (RatFunc C) ℝ≥0} (hν : IsDiscVal a c ν) {Q : C[X]}
    {M : ℝ} (hM : ∀ i, ‖Q.coeff i‖ * (ν (gaussCoord a c) : ℝ) ^ i ≤ M) :
    (ν (aeval (gaussCoord a c) Q) : ℝ) ≤ M := by
  have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) (pow_nonneg (ν _).2 0)).trans (hM 0)
  have h := valuation_aeval_le hν (M := M.toNNReal) fun i ↦ by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hM0]
    push_cast
    exact hM i
  rw [← Real.coe_toNNReal _ hM0]
  exact_mod_cast h

lemma tendsto_pow_two_pow {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Filter.Tendsto (fun n : ℕ ↦ q ^ (2 ^ n)) Filter.atTop (nhds 0) :=
  (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))

lemma pow_two_pow_anti {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) {n m : ℕ} (h : n ≤ m) :
    q ^ (2 ^ m) ≤ q ^ (2 ^ n) :=
  pow_le_pow_of_le_one hq0 hq1 (Nat.pow_le_pow_right (by norm_num) h)

/-! ### The germ -/

section Germ

open LocalGlobal TubeCount DenseCompletion Filter Topology

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

omit [IsUltrametricDist C] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F'] in
lemma norm_algebraMap_completion (ν : DiscVal a c) (f : RatFunc C) :
    ‖algebraMap (DiscField ν) (UniformSpace.Completion (DiscField ν)) (WithAbs.toAbs _ f)‖ =
      ν.val f := by
  change ‖((WithAbs.toAbs _ f : DiscField ν) : UniformSpace.Completion (DiscField ν))‖ = _
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]
  rfl

omit [IsUltrametricDist C] in
lemma toLocal_algebraMap_ratFunc (ν : DiscVal a c)
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F') (f : RatFunc C) :
    toLocal g (algebraMap (RatFunc C) F' f) =
      algebraMap (UniformSpace.Completion (DiscField ν)) (Local _ g.1)
        (algebraMap (DiscField ν) (UniformSpace.Completion (DiscField ν)) (WithAbs.toAbs _ f)) :=
  toLocal_algebraMap g (WithAbs.toAbs _ f)

omit [IsUltrametricDist C] in
lemma norm_toLocal_algebraMap (ν : DiscVal a c)
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F') (f : RatFunc C) :
    ‖toLocal g (algebraMap (RatFunc C) F' f)‖ = ν.val f := by
  rw [toLocal_algebraMap_ratFunc, norm_algebraMap', norm_algebraMap_completion]

omit [IsUltrametricDist C] in
/-- **The trace over `C(x)`, seen in the completion at a disc valuation, is the sum of the local
traces.** -/
lemma trace_completion (ν : DiscVal a c) (y : F') :
    algebraMap (DiscField ν) (UniformSpace.Completion (DiscField ν))
        (WithAbs.toAbs _ (Algebra.trace (RatFunc C) F' y)) =
      ∑ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F',
        Algebra.trace _ (Local _ g.1) (toLocal g y) := by
  haveI : Infinite (RatFunc C) :=
    Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
  haveI : Infinite (DiscField ν) :=
    Infinite.of_injective _ (algebraMap C (DiscField ν)).injective
  set e : RatFunc C ≃+* DiscField ν := (WithAbs.equiv _).symm
  have htr : WithAbs.toAbs _ (Algebra.trace (RatFunc C) F' y) =
      Algebra.trace (DiscField ν) F' y := by
    rw [trace_eq_neg_nextCoeff_normPoly, trace_eq_neg_nextCoeff_normPoly]
    change e (-(normPoly (RatFunc C) y).nextCoeff) = _
    rw [map_neg]
    congr 1
    have h := nextCoeff_map (f := e.toRingHom) e.injective (normPoly (RatFunc C) y)
    rw [normPoly_map_ringEquiv e (by ext; rfl) y] at h
    exact h.symm
  rw [htr]
  exact trace_map_eq_sum y

omit [IsUltrametricDist C] in
/-- **The approximation step.** Let `g₀` be a degree-one factor at a disc valuation `ν`, `e` close
to `1` at `g₀` and to `0` at the other factors (within `q ≤ 1`), and `y` of value `≤ 1` at all
factors. Then `Tr(Nⁿ(e) y)`, seen at `g₀`, is within `q^(2ⁿ)` of `y`. -/
theorem norm_trace_sub_le (ν : DiscVal a c)
    (g₀ : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F')
    (hg₀ : g₀.1.natDegree = 1) {e y : F'} {q : ℝ} (hq1 : q ≤ 1)
    (he₀ : ‖toLocal g₀ e - 1‖ ≤ q) (he : ∀ g, g ≠ g₀ → ‖toLocal g e‖ ≤ q)
    (hy : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F',
      ‖toLocal g y‖ ≤ 1) (n : ℕ) :
    ‖toLocal g₀ (algebraMap (RatFunc C) F'
        (Algebra.trace (RatFunc C) F' ((fun v : F' ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] e * y))) -
      toLocal g₀ y‖ ≤ q ^ (2 ^ n) := by
  classical
  set K := UniformSpace.Completion (DiscField ν)
  set ε := (fun v : F' ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] e
  have hloc (g : Factor (DiscField ν) K F') : toLocal g ε = Idem.N^[n] (toLocal g e) :=
    Idem.map_N_iterate (toLocal g).toRingHom e n
  have heg1 (g : Factor (DiscField ν) K F') : ‖toLocal g e‖ ≤ 1 := by
    by_cases hg : g = g₀
    · subst hg
      calc ‖toLocal g e‖ = ‖(toLocal g e - 1) + 1‖ := by rw [sub_add_cancel]
        _ ≤ max ‖toLocal g e - 1‖ ‖(1 : Local K g.1)‖ := IsUltrametricDist.norm_add_le_max _ _
        _ ≤ 1 := max_le (he₀.trans hq1) (by rw [norm_one])
    · exact (he g hg).trans hq1
  -- the value at `g₀` of `y` is its local trace
  have hy₀ : toLocal g₀ y = algebraMap K _ (Algebra.trace K _ (toLocal g₀ y)) :=
    (algebraMap_trace_of_natDegree_eq_one hg₀ _).symm
  rw [toLocal_algebraMap_ratFunc, trace_completion, hy₀, ← map_sub, norm_algebraMap',
    ← Finset.add_sum_erase _ _ (Finset.mem_univ g₀), add_sub_right_comm, ← map_sub]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · -- the factor `g₀`: `(ε - 1) y`
    refine (norm_trace_le _ _).trans ?_
    rw [map_mul, ← sub_one_mul, norm_mul, hloc]
    refine (mul_le_of_le_one_right (norm_nonneg _) (hy g₀)).trans ?_
    rw [← norm_neg, neg_sub]
    refine (Idem.norm_one_sub_N_iterate_le (heg1 g₀) n).trans ?_
    rw [← norm_neg, neg_sub]
    exact pow_le_pow_left₀ (norm_nonneg _) he₀ _
  · -- the other factors: `ε y`
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg ((norm_nonneg _).trans
      he₀) _) fun g hg ↦ ?_
    refine (norm_trace_le _ _).trans ?_
    rw [map_mul, norm_mul, hloc]
    refine (mul_le_of_le_one_right (norm_nonneg _) (hy g)).trans ?_
    refine (Idem.norm_N_iterate_le (heg1 g) n).trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (he g (Finset.ne_of_mem_erase hg)) _

end Germ

section Main

open LocalGlobal TubeCount DenseCompletion Filter Topology

local notation "Ĉ" => UniformSpace.Completion C

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

/-- Every factor centred at a point of disc degree one has degree one, and is the only factor
centred there. -/
lemma natDegree_eq_one_of_center {hc : c ≠ 0} {ν₀ : DiscVal a c} {P' : Ideal (DRint a c F')}
    [P'.IsMaximal] (h1 : discDegree ν₀ P' = 1) (ν : DiscVal a c)
    {g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F'}
    (hg : center (isDiscVal_comap_extValuation g) = P') : g.1.natDegree = 1 := by
  classical
  have h1' : discDegree ν P' = 1 := (discDegree_eq hc ν₀ ν P').symm.trans h1
  have hle : g.1.natDegree ≤ discDegree ν P' :=
    Finset.single_le_sum (f := fun g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F' ↦ g.1.natDegree) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ g, hg⟩)
  have hpos : 0 < g.1.natDegree := (irreducible_of_mem_factors g.2).natDegree_pos
  omega

lemma eq_of_center {hc : c ≠ 0} {ν₀ : DiscVal a c} {P' : Ideal (DRint a c F')}
    [P'.IsMaximal] (h1 : discDegree ν₀ P' = 1) (ν : DiscVal a c)
    {g g' : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F'}
    (hg : center (isDiscVal_comap_extValuation g) = P')
    (hg' : center (isDiscVal_comap_extValuation g') = P') : g = g' := by
  obtain ⟨g₀, -, huniq⟩ := existsUnique_of_discDegree_eq_one hc ν₀ ν P' h1
  rw [huniq g ⟨hg, natDegree_eq_one_of_center (hc := hc) h1 ν hg⟩,
    huniq g' ⟨hg', natDegree_eq_one_of_center (hc := hc) h1 ν hg'⟩]

/-- **The analytic germ at a degree-one disc point.** Let `P'` be a point of the integral closure
`R'` of `O_C[t]`, `t = (x - a)/c`, of disc degree one (at one, hence every, disc valuation), and
`y ∈ R'`. There are polynomials `Qₙ ∈ O_C[t]` converging to `y` in the completion of `F'` at the
extension centred at `P'` of every disc valuation `ν` (any type), and a power series
`G = Σ aᵢ Xⁱ` over the completion `Ĉ` of `C` (`C` need not be complete), `|aᵢ| ≤ 1`, to which the
`Qₙ` converge uniformly on every disc `|t| ≤ |l| < 1`: `|aᵢ - qₙᵢ| |l|^i ≤ q^(2ⁿ)`, `q < 1`. -/
theorem exists_germ (hc : c ≠ 0) (ν₀ : DiscVal a c) (P' : Ideal (DRint a c F')) [P'.IsMaximal]
    (h1 : discDegree ν₀ P' = 1) (y : DRint a c F') :
    ∃ (G : PowerSeries Ĉ) (Q : ℕ → C[X]), (∀ i, ‖PowerSeries.coeff i G‖₊ ≤ 1) ∧
      (∀ n i, ‖(Q n).coeff i‖₊ ≤ 1) ∧
      (∀ l : C, l ≠ 0 → ‖l‖ < 1 → ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
        ∀ n i, ‖PowerSeries.coeff i G - ((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i ≤ q ^ (2 ^ n)) ∧
      ∀ (ν : DiscVal a c) (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F'),
        center (isDiscVal_comap_extValuation g) = P' →
        Tendsto (fun n ↦ toLocal g (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n))))
          atTop (𝓝 (toLocal g (y : F'))) := by
  classical
  -- Step 1: a separating element
  set T : Finset (Ideal (DRint a c F')) :=
    (Finset.univ.image (fun g : Factor (DiscField ν₀)
      (UniformSpace.Completion (DiscField ν₀)) F' ↦
        center (isDiscVal_comap_extValuation g))).erase P'
  obtain ⟨e, he1, heQ⟩ := GaussTube.exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.1 hQ
    exact ⟨center_isMaximal hc _, hne⟩
  have hcent : ∀ (ν : DiscVal a c)
      (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F'),
      center (isDiscVal_comap_extValuation g) ≠ P' →
        center (isDiscVal_comap_extValuation g) ∈ T := by
    intro ν g hne
    haveI := center_isMaximal hc (isDiscVal_comap_extValuation g)
    have hpos := discDegree_pos hc ν₀ (center (isDiscVal_comap_extValuation g))
      (comap_center _)
    rw [discDegree, Finset.sum_pos_iff] at hpos
    obtain ⟨g₀, hg₀, -⟩ := hpos
    refine Finset.mem_erase.2 ⟨hne, Finset.mem_image.2 ⟨g₀, Finset.mem_univ _, ?_⟩⟩
    exact (Finset.mem_filter.1 hg₀).2
  -- the closeness numbers
  set qq : DiscVal a c → ℝ≥0 := fun ν ↦ Finset.univ.sup fun g : Factor (DiscField ν)
    (UniformSpace.Completion (DiscField ν)) F' ↦
      if center (isDiscVal_comap_extValuation g) = P' then ‖toLocal g (e : F') - 1‖₊
        else ‖toLocal g (e : F')‖₊
  have hqq1 : ∀ ν, qq ν < 1 := by
    intro ν
    refine (Finset.sup_lt_iff zero_lt_one).2 fun g _ ↦ ?_
    split_ifs with hg
    · have : (e - 1 : DRint a c F') ∈ center (isDiscVal_comap_extValuation g) := hg ▸ he1
      rw [mem_center_iff, extValuation_apply] at this
      simpa using this
    · have : e ∈ center (isDiscVal_comap_extValuation g) := heQ _ (hcent ν g hg)
      rw [mem_center_iff, extValuation_apply] at this
      exact this
  have hqq_cl : ∀ ν g, center (isDiscVal_comap_extValuation (ν := ν) g) = P' →
      ‖toLocal g (e : F') - 1‖ ≤ qq ν := by
    intro ν g hg
    have := Finset.le_sup (f := fun g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F' ↦
      if center (isDiscVal_comap_extValuation g) = P' then ‖toLocal g (e : F') - 1‖₊
        else ‖toLocal g (e : F')‖₊) (Finset.mem_univ g)
    rw [if_pos hg] at this
    exact_mod_cast this
  have hqq_far : ∀ ν g, center (isDiscVal_comap_extValuation (ν := ν) g) ≠ P' →
      ‖toLocal g (e : F')‖ ≤ qq ν := by
    intro ν g hg
    have := Finset.le_sup (f := fun g : Factor (DiscField ν)
      (UniformSpace.Completion (DiscField ν)) F' ↦
      if center (isDiscVal_comap_extValuation g) = P' then ‖toLocal g (e : F') - 1‖₊
        else ‖toLocal g (e : F')‖₊) (Finset.mem_univ g)
    rw [if_neg hg] at this
    exact_mod_cast this
  -- Step 2: the traces `pₙ = Tr(Nⁿ(e) y)` are polynomials in `t` with integral coefficients
  set Nf : F' → F' := fun v ↦ 3 * v ^ 2 - 2 * v ^ 3
  have hεint : ∀ n, IsIntegral (discRing a c) (Nf^[n] (e : F') * y) := by
    intro n
    have h := Idem.map_N_iterate (DRint a c F').val.toRingHom e n
    have hmem : Nf^[n] (e : F') * y ∈ DRint a c F' := by
      rw [show Nf^[n] (e : F') = ((fun v : DRint a c F' ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] e : F')
        from h.symm]
      exact ((fun v : DRint a c F' ↦ 3 * v ^ 2 - 2 * v ^ 3)^[n] e * y).2
    exact hmem
  have hpmem : ∀ n, Algebra.trace (RatFunc C) F' (Nf^[n] (e : F') * y) ∈ discRing a c := by
    intro n
    haveI := isFractionRing_discRing (a := a) hc
    haveI := isIntegrallyClosed_discRing (a := a) hc
    exact isIntegral_mem_of_isIntegrallyClosed (Algebra.isIntegral_trace (hεint n))
  choose Q hQ hQp using fun n ↦ mem_polyChart_iff.1 (hpmem n)
  have hQ1 : ∀ n i, ‖(Q n).coeff i‖₊ ≤ 1 := fun n ↦ nnnorm_coeff_le_one (hQ n)
  -- Step 3: the estimate at every disc valuation
  have hest : ∀ (ν : DiscVal a c)
      (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F'),
      center (isDiscVal_comap_extValuation g) = P' → ∀ n,
      ‖toLocal g (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n))) -
        toLocal g (y : F')‖ ≤ (qq ν : ℝ) ^ (2 ^ n) := by
    intro ν g hg n
    rw [hQp n]
    refine norm_trace_sub_le ν g (natDegree_eq_one_of_center (hc := hc) h1 ν hg)
      (by exact_mod_cast (hqq1 ν).le) (hqq_cl ν g hg) (fun g' hg' ↦ hqq_far ν g' fun h ↦
        hg' (eq_of_center (hc := hc) h1 ν h hg)) (fun g' ↦ ?_) n
    have := valuation_le_one_of_isIntegral (isDiscVal_comap_extValuation g') y.2
    rw [extValuation_apply] at this
    exact_mod_cast this
  -- Step 4: coefficient estimates at the Gauss points `w_{a, |l c|}`
  have hgauss : ∀ l : C, l ≠ 0 → ‖l‖ < 1 → ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ n m i,
      ‖(Q n).coeff i - (Q m).coeff i‖ * ‖l‖ ^ i ≤ max (q ^ (2 ^ n)) (q ^ (2 ^ m)) := by
    intro l hl0 hl1
    have hlc : l * c ≠ 0 := mul_ne_zero hl0 hc
    have hlt : ‖l * c‖ < ‖c‖ := by
      rw [norm_mul]
      exact mul_lt_of_lt_one_left (norm_pos_iff.2 hc) hl1
    set νl : DiscVal a c := ⟨_, isDiscVal_gaussRat (a := a) hc hlc hlt⟩
    have h1l : discDegree νl P' = 1 := (discDegree_eq hc ν₀ νl P').symm.trans h1
    have hpos : 0 < discDegree νl P' := by rw [h1l]; exact one_pos
    rw [discDegree, Finset.sum_pos_iff] at hpos
    obtain ⟨gl, hgl, -⟩ := hpos
    have hgl' := (Finset.mem_filter.1 hgl).2
    refine ⟨qq νl, (qq νl).2, by exact_mod_cast hqq1 νl, fun n m i ↦ ?_⟩
    have hle := le_gaussRat_aeval (a := a) hc hlc (Q n - Q m) i
    have hrat : (‖l * c‖₊ / ‖c‖₊ : ℝ≥0) = ‖l‖₊ := by
      rw [nnnorm_mul, mul_div_cancel_right₀ _ (nnnorm_ne_zero_iff.2 hc)]
    rw [hrat] at hle
    have hval : (gaussRat (NormedField.valuation (K := C)) a
        (Units.mk0 ‖l * c‖₊ (nnnorm_ne_zero_iff.2 hlc)) (aeval (gaussCoord a c) (Q n - Q m)) : ℝ)
        = ‖toLocal gl (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n))) -
          toLocal gl (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q m)))‖ := by
      rw [← map_sub, ← map_sub, ← map_sub, norm_toLocal_algebraMap]
    calc ‖(Q n).coeff i - (Q m).coeff i‖ * ‖l‖ ^ i
        = ((‖(Q n - Q m).coeff i‖₊ * ‖l‖₊ ^ i : ℝ≥0) : ℝ) := by
          rw [coeff_sub]
          push_cast
          rfl
      _ ≤ _ := by exact_mod_cast hle
      _ = _ := hval
      _ ≤ max ‖toLocal gl (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n))) -
            toLocal gl (y : F')‖
          ‖toLocal gl (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q m))) -
            toLocal gl (y : F')‖ := by
          rw [← sub_sub_sub_cancel_right _ _ (toLocal gl (y : F'))]
          exact Idem.norm_sub_le_max' _ _
      _ ≤ _ := max_le_max (hest νl gl hgl' n) (hest νl gl hgl' m)
  -- Step 5: the coefficients converge in `Ĉ`
  obtain ⟨l₀, hl₀0, hl₀1⟩ : ∃ l : C, 0 < ‖l‖ ∧ ‖l‖ < 1 := NormedField.exists_norm_lt_one C
  obtain ⟨q₀, hq₀0, hq₀1, hc₀⟩ := hgauss l₀ (norm_pos_iff.1 hl₀0) hl₀1
  have hcauchy : ∀ i, CauchySeq fun n ↦ ((Q n).coeff i : Ĉ) := by
    intro i
    refine (UniformSpace.Completion.uniformContinuous_coe C).comp_cauchySeq ?_
    refine cauchySeq_of_le_tendsto_0 (fun N ↦ q₀ ^ (2 ^ N) / ‖l₀‖ ^ i) (fun n m N hn hm ↦ ?_)
      (by simpa using (tendsto_pow_two_pow hq₀0 hq₀1).div_const (‖l₀‖ ^ i))
    rw [dist_eq_norm, le_div_iff₀ (pow_pos hl₀0 i)]
    exact (hc₀ n m i).trans (max_le (pow_two_pow_anti hq₀0 hq₀1.le hn)
      (pow_two_pow_anti hq₀0 hq₀1.le hm))
  choose A hA using fun i ↦ cauchySeq_tendsto_of_complete (hcauchy i)
  refine ⟨PowerSeries.mk A, Q, fun i ↦ ?_, hQ1, fun l hl0 hl1 ↦ ?_, fun ν g hg ↦ ?_⟩
  · rw [PowerSeries.coeff_mk]
    have : ‖A i‖ ≤ 1 := le_of_tendsto' ((hA i).norm) fun n ↦ by
      rw [UniformSpace.Completion.norm_coe]
      exact_mod_cast hQ1 n i
    exact_mod_cast this
  · -- uniform convergence on `|t| ≤ |l|`
    obtain ⟨q, hq0, hq1, hcl⟩ := hgauss l hl0 hl1
    refine ⟨q, hq0, hq1, fun n i ↦ ?_⟩
    rw [PowerSeries.coeff_mk]
    have hlim : Tendsto (fun m ↦ ‖(Q m).coeff i - (Q n).coeff i‖ * ‖l‖ ^ i) atTop
        (𝓝 (‖A i - ((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i)) := by
      have := (((hA i).sub_const ((Q n).coeff i : Ĉ)).norm).mul_const (‖l‖ ^ i)
      refine this.congr fun m ↦ ?_
      rw [← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]
    refine le_of_tendsto hlim (eventually_atTop.2 ⟨n, fun m hm ↦ ?_⟩)
    exact (hcl m n i).trans (max_le (pow_two_pow_anti hq0 hq1.le hm) le_rfl)
  · -- convergence at `ν`
    have hqν0 : (0 : ℝ) ≤ qq ν := (qq ν).2
    have hqν1 : (qq ν : ℝ) < 1 := by exact_mod_cast hqq1 ν
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun _ ↦ norm_nonneg _) (hest ν g hg) (tendsto_pow_two_pow hqν0 hqν1)

/-- The Gauss point `w_{a,|l c|}`, `0 < |l| < 1`, as a disc valuation. -/
noncomputable def gaussDiscVal (hc : c ≠ 0) {l : C} (hl0 : l ≠ 0) (hl1 : ‖l‖ < 1) : DiscVal a c :=
  ⟨_, isDiscVal_gaussRat (a := a) hc (mul_ne_zero hl0 hc)
    (by rw [norm_mul]; exact mul_lt_of_lt_one_left (norm_pos_iff.2 hc) hl1)⟩

/-- At the Gauss point `w_{a,|l c|}` the value of a polynomial `Q(t)` is bounded by any common
bound of the terms `|qᵢ| |l|^i`. -/
lemma gaussRat_aeval_le_of_terms (hc : c ≠ 0) {l : C} (hl : l ≠ 0) (Q : C[X]) {M : ℝ}
    (hM : ∀ i, ‖Q.coeff i‖ * ‖l‖ ^ i ≤ M) :
    (gaussRat (NormedField.valuation (K := C)) a
      (Units.mk0 ‖l * c‖₊ (nnnorm_ne_zero_iff.2 (mul_ne_zero hl hc)))
        (aeval (gaussCoord a c) Q) : ℝ) ≤ M := by
  have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) 0)).trans (hM 0)
  rw [gaussRat_aeval_eq hc (mul_ne_zero hl hc), ← Real.coe_toNNReal _ hM0, NNReal.coe_le_coe]
  refine sup_le_iff.2 fun i ↦ ?_
  simp only [term, Units.val_one, one_pow, mul_one, SplitDisc.coeff_comp_C_mul_X,
    NormedField.valuation_apply]
  rw [nnnorm_mul, nnnorm_pow, mul_div_cancel_right₀ _ hc, ← NNReal.coe_le_coe,
    Real.coe_toNNReal _ hM0]
  push_cast
  exact hM i

/-- **The germ in valuation terms.** In the situation of `exists_germ`, at every Gauss point
`w_{a,|l c|}` (`0 < |l| < 1`) the value of `y` at the extension centred at `P'` is the Gauss norm
`sup_i |aᵢ| |l|^i` of the germ `G` (a power series over the completion `Ĉ`). -/
theorem exists_germ_gaussNorm (hc : c ≠ 0) (ν₀ : DiscVal a c) (P' : Ideal (DRint a c F'))
    [P'.IsMaximal] (h1 : discDegree ν₀ P' = 1) (y : DRint a c F') :
    ∃ (G : PowerSeries Ĉ) (Q : ℕ → C[X]), (∀ i, ‖PowerSeries.coeff i G‖₊ ≤ 1) ∧
      (∀ n i, ‖(Q n).coeff i‖₊ ≤ 1) ∧
      (∀ l : C, l ≠ 0 → ‖l‖ < 1 → ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧
        ∀ n i, ‖PowerSeries.coeff i G - ((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i ≤ q ^ (2 ^ n)) ∧
      (∀ (ν : DiscVal a c) (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F'),
        center (isDiscVal_comap_extValuation g) = P' →
        Tendsto (fun n ↦ toLocal g (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n))))
          atTop (𝓝 (toLocal g (y : F')))) ∧
      ∀ (l : C) (hl0 : l ≠ 0) (hl1 : ‖l‖ < 1)
        (g : Factor (DiscField (gaussDiscVal hc hl0 hl1))
          (UniformSpace.Completion (DiscField (gaussDiscVal hc hl0 hl1))) F'),
        center (isDiscVal_comap_extValuation g) = P' →
        (extValuation g (y : F') : ℝ) = PowerSeries.gaussNorm (fun x : Ĉ ↦ ‖x‖) ‖l‖ G := by
  obtain ⟨G, Q, hG1, hQ1, hunif, hconv⟩ := exists_germ hc ν₀ P' h1 y
  refine ⟨G, Q, hG1, hQ1, hunif, hconv, fun l hl0 hl1 g hg ↦ ?_⟩
  obtain ⟨q, hq0, hq1, hql⟩ := hunif l hl0 hl1
  have hlim := (hconv (gaussDiscVal hc hl0 hl1) g hg).norm
  rw [extValuation_apply, coe_nnnorm, PowerSeries.gaussNorm_eq]
  have hl0' : 0 ≤ ‖l‖ ^ 0 := pow_nonneg (norm_nonneg _) 0
  have hterm1 : ∀ i, ‖PowerSeries.coeff i G‖ * ‖l‖ ^ i ≤ 1 := fun i ↦
    mul_le_one₀ (by exact_mod_cast hG1 i) (pow_nonneg (norm_nonneg _) _)
      (pow_le_one₀ (norm_nonneg _) hl1.le)
  have hbdd : BddAbove (Set.range fun i ↦ ‖PowerSeries.coeff i G‖ * ‖l‖ ^ i) :=
    ⟨1, by rintro _ ⟨i, rfl⟩; exact hterm1 i⟩
  set gN := ⨆ i, ‖PowerSeries.coeff i G‖ * ‖l‖ ^ i
  have hgN0 : 0 ≤ gN := (mul_nonneg (norm_nonneg _) hl0').trans (le_ciSup hbdd 0)
  -- the values of the approximants
  have hval : ∀ n, ‖toLocal g (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n)))‖ =
      (gaussRat (NormedField.valuation (K := C)) a
        (Units.mk0 ‖l * c‖₊ (nnnorm_ne_zero_iff.2 (mul_ne_zero hl0 hc)))
          (aeval (gaussCoord a c) (Q n)) : ℝ) := fun n ↦
    norm_toLocal_algebraMap (gaussDiscVal hc hl0 hl1) g _
  have hcoe (n i : ℕ) : ‖(Q n).coeff i‖ = ‖((Q n).coeff i : Ĉ)‖ :=
    (UniformSpace.Completion.norm_coe _).symm
  have hq2 (n : ℕ) : 0 ≤ q ^ (2 ^ n) := pow_nonneg hq0 _
  refine le_antisymm ?_ (ciSup_le fun i ↦ ?_)
  · -- `≤`
    have hle (n : ℕ) : ‖toLocal g (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n)))‖ ≤
        max gN (q ^ (2 ^ n)) := by
      rw [hval]
      refine gaussRat_aeval_le_of_terms hc hl0 _ fun i ↦ ?_
      have h := Idem.norm_sub_le_max' (PowerSeries.coeff i G)
        (PowerSeries.coeff i G - ((Q n).coeff i : Ĉ))
      rw [sub_sub_cancel] at h
      rw [hcoe]
      calc ‖((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i ≤
            max ‖PowerSeries.coeff i G‖ ‖PowerSeries.coeff i G - ((Q n).coeff i : Ĉ)‖ *
              ‖l‖ ^ i := mul_le_mul_of_nonneg_right h (pow_nonneg (norm_nonneg _) _)
        _ = max (‖PowerSeries.coeff i G‖ * ‖l‖ ^ i)
              (‖PowerSeries.coeff i G - ((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i) :=
            max_mul_of_nonneg _ _ (pow_nonneg (norm_nonneg _) _)
        _ ≤ _ := max_le_max (le_ciSup hbdd i) (hql n i)
    have h := le_of_tendsto_of_tendsto' hlim
      (tendsto_const_nhds.max (tendsto_pow_two_pow hq0 hq1)) hle
    rwa [max_eq_left hgN0] at h
  · -- `≥`
    have hge (n : ℕ) : ‖PowerSeries.coeff i G‖ * ‖l‖ ^ i ≤
        max ‖toLocal g (algebraMap (RatFunc C) F' (aeval (gaussCoord a c) (Q n)))‖
          (q ^ (2 ^ n)) := by
      have h := Idem.norm_sub_le_max' (PowerSeries.coeff i G - ((Q n).coeff i : Ĉ))
        (-((Q n).coeff i : Ĉ))
      rw [sub_neg_eq_add, sub_add_cancel, norm_neg] at h
      have hle := le_gaussRat_aeval (a := a) hc (mul_ne_zero hl0 hc) (Q n) i
      have hrat : (‖l * c‖₊ / ‖c‖₊ : ℝ≥0) = ‖l‖₊ := by
        rw [nnnorm_mul, mul_div_cancel_right₀ _ (nnnorm_ne_zero_iff.2 hc)]
      rw [hrat] at hle
      have hle' := NNReal.coe_le_coe.2 hle
      push_cast at hle'
      rw [hval]
      calc ‖PowerSeries.coeff i G‖ * ‖l‖ ^ i ≤
            max ‖PowerSeries.coeff i G - ((Q n).coeff i : Ĉ)‖ ‖((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i :=
            mul_le_mul_of_nonneg_right h (pow_nonneg (norm_nonneg _) _)
        _ = max (‖PowerSeries.coeff i G - ((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i)
              (‖((Q n).coeff i : Ĉ)‖ * ‖l‖ ^ i) :=
            max_mul_of_nonneg _ _ (pow_nonneg (norm_nonneg _) _)
        _ ≤ _ := by
            rw [max_comm]
            exact max_le_max (by rw [← hcoe]; exact hle') (hql n i)
    have h := le_of_tendsto_of_tendsto' tendsto_const_nhds
      (hlim.max (tendsto_pow_two_pow hq0 hq1)) hge
    rwa [max_eq_left (norm_nonneg _)] at h

end Main

end DiscGerm

end SemistableReduction
