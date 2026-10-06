/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CriticalRadius
import TemperedFundamentalGroups.SemistableReduction.HenselComplete
import TemperedFundamentalGroups.SemistableReduction.DiscreteCoefficients

/-!
# Good centres

Blueprint §9.10, L4 (K5): Arzdorf's good centre (Prop. 2.31) for polynomials over an
algebraically closed non-archimedean field `C` (no completeness, no Weierstrass preparation, no
integral extensions of power series rings). The germ of the Kummer generator enters only through
a polynomial approximant (DiscGerm's `Q n`), which defines the same local Kummer extensions at
all disc valuations of radius `≤ ‖l‖`.

## Dominant coefficients of polynomials

* `dom_mul`, `dom_pow`, `dom_add_small`: Gauss's lemma in valuative form (maximal coefficient
  norm and the first index attaining it);
* `exists_root_of_dom`: a polynomial whose maximal coefficient is attained first at an index
  `k ≥ 1` has a root of norm `< 1`;
* `exists_norm_eval_eq` (maximum modulus): every polynomial attains its maximal coefficient
  norm at a point of the closed unit disc (the residue field is infinite).

## Iterated norms over towers of `p`-th roots

* `symm`, `norm1`, `norm1_map`: `∏_{i<p} P(ζ^i Y)` is a polynomial in `Y^p`; its value at
  `Y^p = e` is the product over the `p` choices of a root;
* `normAll`, `Valid`: the iterated norm over a tower `X_i^p = e_i(X_0, …, X_{i-1})`;
  `exists_valid_of_normAll_eq_zero`: at a zero of the norm some choice of roots is a zero;
  `norm_normAll_sub_le`: if every choice is within `η ≤ M` of `c`, `‖c‖ ≤ M`, the norm is within
  `η M^(p^n - 1)` of `c^(p^n)`.

## The generic `p`-Taylor algorithm

* `genF`, `genH`, `genA`, `genE`: the truncated `p`-Taylor algorithm for `f(T + s)` with
  symbolic roots (one root per step, round-robin schedule `rr J` over the indices `1, …, J`);
* `step_root`, `conc_inv`, `conc_step`: estimates for every choice of roots;
  `prec_inv`: after `R` rounds the `p`-coefficients are bounded by `bd R`, which tends to `A`.

## The good centre

* **`exists_good_centre`**: for `f` with data `(M, m)`, `m ≥ 2`, `p ∤ m`, `A < M ≤ 1`, there is a
  centre `‖τ‖ < 1` and an approximation `h` such that `f(τ + s) - h^p` is precise with the same
  data and **vanishing linear coefficient**; consequently the critical segment does not start at
  `P₁` (Arzdorf's condition `l ≠ 1`). The iterated norm of the linear coefficient is a polynomial
  in the centre which is close to `f'(T)^(p^N)` on the closed unit disc, so it has a root of norm
  `< 1`.
-/

open Polynomial NNReal

namespace SemistableReduction

namespace GoodCentre

open CriticalRadius

variable {C : Type*} [NormedField C] [IsUltrametricDist C]

/-! ### Dominant coefficients of polynomials -/

section Dominance

/-- The maximal coefficient norm `M` of `P` is attained first at `k`. -/
abbrev DomP (P : C[X]) (M : ℝ) (k : ℕ) : Prop := Dom (fun i ↦ ‖P.coeff i‖) M k

/-- **Gauss's lemma, valuative form**: dominant data multiply. -/
theorem dom_mul {P Q : C[X]} {M M' : ℝ} {k k' : ℕ} (hP : DomP P M k) (hQ : DomP Q M' k')
    (hM : 0 < M) (hM' : 0 < M') : DomP (P * Q) (M * M') (k + k') := by
  classical
  have hMM : 0 ≤ M * M' := (mul_pos hM hM').le
  have hle : ∀ x : ℕ × ℕ, ‖P.coeff x.1 * Q.coeff x.2‖ ≤ M * M' := fun x ↦ by
    rw [norm_mul]
    exact mul_le_mul (hP.le _) (hQ.le _) (norm_nonneg _) hM.le
  -- terms with `x.1 < k` or `x.2 < k'` are strictly smaller
  have hlt : ∀ x : ℕ × ℕ, (x.1 < k ∨ x.2 < k') → ‖P.coeff x.1 * Q.coeff x.2‖ < M * M' := by
    rintro x (h | h) <;> rw [norm_mul]
    · exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hP.lt _ h) (hQ.le _) (norm_nonneg _) hM'
    · calc ‖P.coeff x.1‖ * ‖Q.coeff x.2‖ ≤ M * ‖Q.coeff x.2‖ :=
            mul_le_mul_of_nonneg_right (hP.le _) (norm_nonneg _)
        _ < M * M' := mul_lt_mul_of_pos_left (hQ.lt _ h) hM
  refine ⟨fun i ↦ norm_nonneg _, ?_, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · have hmem : (k, k') ∈ Finset.HasAntidiagonal.antidiagonal (k + k') := by simp
    rw [coeff_mul, ← Finset.add_sum_erase _ _ hmem]
    have h0 : ‖P.coeff k * Q.coeff k'‖ = M * M' := by
      rw [norm_mul, hP.eq, hQ.eq]
    have hrest : ‖∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (k + k')).erase (k, k'),
        P.coeff x.1 * Q.coeff x.2‖ < M * M' := by
      rcases ((Finset.HasAntidiagonal.antidiagonal (k + k')).erase (k, k')).eq_empty_or_nonempty
        with he | hne
      · rw [he, Finset.sum_empty, norm_zero]; exact mul_pos hM hM'
      · obtain ⟨x, hx, hxle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
          (fun x : ℕ × ℕ ↦ P.coeff x.1 * Q.coeff x.2)
        refine hxle.trans_lt (hlt x ?_)
        obtain ⟨hxne, hxa⟩ := Finset.mem_erase.1 hx
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hxa
        by_contra h
        push Not at h
        exact hxne (Prod.ext (by omega) (by omega))
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [h0]; exact hrest.ne'),
      h0, max_eq_left hrest.le]
  · rw [coeff_mul]
    exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hMM fun x _ ↦ hle x
  · rw [coeff_mul]
    rcases (Finset.HasAntidiagonal.antidiagonal i).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]; exact mul_pos hM hM'
    obtain ⟨x, hx, hxle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
      (fun x : ℕ × ℕ ↦ P.coeff x.1 * Q.coeff x.2)
    refine hxle.trans_lt (hlt x ?_)
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_contra h
    push Not at h
    omega

lemma dom_unique {a : ℕ → ℝ} {M M' : ℝ} {k k' : ℕ} (h : Dom a M k) (h' : Dom a M' k') :
    M = M' ∧ k = k' := by
  have hMM : M = M' := le_antisymm (h.eq ▸ h'.le k) (h'.eq ▸ h.le k')
  subst hMM
  refine ⟨rfl, le_antisymm ?_ ?_⟩
  · by_contra hk
    exact absurd h'.eq (h.lt k' (not_le.1 hk)).ne
  · by_contra hk
    exact absurd h.eq (h'.lt k (not_le.1 hk)).ne

omit [IsUltrametricDist C] in
lemma domP_one : DomP (1 : C[X]) 1 0 :=
  ⟨fun i ↦ norm_nonneg _, by simp, fun i ↦ by rw [coeff_one]; split_ifs <;> simp,
    fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩

omit [IsUltrametricDist C] in
lemma domP_C {c : C} : DomP (Polynomial.C c) ‖c‖ 0 :=
  ⟨fun i ↦ norm_nonneg _, by simp, fun i ↦ by
    rw [coeff_C]; split_ifs <;> simp, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩

omit [IsUltrametricDist C] in
lemma domP_X_sub_C {α : C} (hα : 1 ≤ ‖α‖) : DomP (X - Polynomial.C α) ‖α‖ 0 := by
  refine ⟨fun i ↦ norm_nonneg _, by simp, fun i ↦ ?_, fun i hi ↦ absurd hi (Nat.not_lt_zero i)⟩
  rw [coeff_sub, coeff_X, coeff_C]
  rcases i with _ | _ | i <;> simp [hα]

/-- A polynomial whose maximal coefficient is attained first at an index `k ≥ 1` has a root of
norm `< 1`. -/
theorem exists_root_of_dom [IsAlgClosed C] {P : C[X]} {M : ℝ} {k : ℕ} (hP : DomP P M k)
    (hM : 0 < M) (hk : 0 < k) : ∃ α : C, ‖α‖ < 1 ∧ P.IsRoot α := by
  classical
  by_contra! H
  have hP0 : P ≠ 0 := by
    rintro rfl
    have := hP.eq
    rw [coeff_zero, norm_zero] at this
    exact hM.ne this
  have hfac := (IsAlgClosed.splits P).eq_prod_roots
  have hprod : ∀ s : Multiset C, (∀ α ∈ s, 1 ≤ ‖α‖) →
      DomP (s.map fun a ↦ X - Polynomial.C a).prod (s.map (‖·‖)).prod 0 := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simpa using domP_one
    | cons α s ih =>
      intro hs
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
      have hα := hs α (Multiset.mem_cons_self α s)
      have hs' := ih fun β hβ ↦ hs β (Multiset.mem_cons_of_mem hβ)
      have hpos : 0 < (s.map (‖·‖)).prod := by
        refine Multiset.prod_pos fun x hx ↦ ?_
        obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hx
        exact lt_of_lt_of_le one_pos (hs β (Multiset.mem_cons_of_mem hβ))
      simpa using dom_mul (domP_X_sub_C hα) hs' (lt_of_lt_of_le one_pos hα) hpos
  have hroots : ∀ α ∈ P.roots, 1 ≤ ‖α‖ := fun α hα ↦
    not_lt.1 fun h ↦ H α h ((mem_roots hP0).1 hα)
  have hlc : 0 < ‖P.leadingCoeff‖ := norm_pos_iff.2 (leadingCoeff_ne_zero.2 hP0)
  have hpos : 0 < (P.roots.map (‖·‖)).prod := by
    refine Multiset.prod_pos fun x hx ↦ ?_
    obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.1 hx
    exact lt_of_lt_of_le one_pos (hroots β hβ)
  have hD := dom_mul (domP_C (c := P.leadingCoeff)) (hprod _ hroots) hlc hpos
  rw [← hfac] at hD
  have := (dom_unique hP hD).2
  omega

/-- The residue of the value of a polynomial with integral coefficients. -/
lemma rd_eval {Q : C[X]} (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) {u : C} (hu : ‖u‖ ≤ 1) :
    KummerNormalForm.rd (Q.eval u) =
      (∑ i ∈ Finset.range (Q.natDegree + 1),
        monomial i (KummerNormalForm.rd (Q.coeff i))).eval (KummerNormalForm.rd u) := by
  open KummerNormalForm in
  rw [eval_eq_sum_range, rd_sum _ _ fun i _ ↦ ?_, eval_finsetSum]
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [eval_monomial, rd_mul (hQ i) (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hu),
      rd_pow hu]
  · rw [norm_mul, norm_pow]
    exact mul_le_one₀ (hQ i) (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hu)

/-- **Maximum modulus.** Every polynomial attains its maximal coefficient norm at a point of the
closed unit disc. -/
theorem exists_norm_eval_eq [IsAlgClosed C] (P : C[X]) :
    ∃ τ : C, ‖τ‖ ≤ 1 ∧ ∀ i, ‖P.coeff i‖ ≤ ‖P.eval τ‖ := by
  classical
  open KummerNormalForm in
  rcases eq_or_ne P 0 with rfl | hP0
  · exact ⟨0, by simp, fun i ↦ by simp⟩
  -- a coefficient of maximal norm
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.range (P.natDegree + 1))
    (fun i ↦ ‖P.coeff i‖) ⟨P.natDegree, Finset.mem_range.2 (Nat.lt_succ_self _)⟩
  have hmax : ∀ i, ‖P.coeff i‖ ≤ ‖P.coeff i₀‖ := fun i ↦ by
    rcases lt_or_ge i (P.natDegree + 1) with hi | hi
    · exact hi₀ i (Finset.mem_range.2 hi)
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]; exact norm_nonneg _
  set c := P.coeff i₀
  have hc0 : c ≠ 0 := by
    intro h
    apply hP0
    ext i
    have := hmax i
    rw [show c = 0 from h, norm_zero] at this
    simpa using norm_le_zero_iff.1 this
  set Q := Polynomial.C c⁻¹ * P
  have hQc : ∀ i, Q.coeff i = c⁻¹ * P.coeff i := fun i ↦ coeff_C_mul _
  have hQ : ∀ i, ‖Q.coeff i‖ ≤ 1 := fun i ↦ by
    rw [hQc, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hmax i) (norm_nonneg _)
  set Qb := ∑ i ∈ Finset.range (Q.natDegree + 1), monomial i (rd (Q.coeff i))
  have hQb : Qb ≠ 0 := by
    intro h
    have hi₀Q : i₀ ≤ Q.natDegree := by
      refine le_natDegree_of_ne_zero ?_
      rw [hQc, inv_mul_cancel₀ hc0]; exact one_ne_zero
    have := congrArg (coeff · i₀) h
    simp only [Qb, finsetSum_coeff, coeff_monomial, coeff_zero] at this
    rw [Finset.sum_eq_single i₀ (fun j _ hj ↦ if_neg hj) (fun h ↦ absurd
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi₀Q)) h), if_pos rfl, hQc,
      inv_mul_cancel₀ hc0, rd_one] at this
    exact one_ne_zero this
  haveI := DiscreteCoefficients.isAlgClosed_residueField (F := C)
  obtain ⟨ū, hū⟩ : ∃ ū, Qb.eval ū ≠ 0 := by
    by_contra! H
    exact hQb (eq_zero_of_infinite_isRoot Qb (by
      simpa [IsRoot, H] using Set.infinite_univ))
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective ū
  refine ⟨(u : C), HenselComplete.norm_le_one u, fun i ↦ ?_⟩
  have hrd : rd (Q.eval (u : C)) ≠ 0 := by
    rw [rd_eval hQ (HenselComplete.norm_le_one u), rd_coe]
    exact hū
  have hQu : ‖Q.eval (u : C)‖ = 1 := DiscreteCoefficients.norm_eq_one_of_rd_ne_zero
    (by
      rw [eval_eq_sum_range]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun j _ ↦ ?_
      rw [norm_mul, norm_pow]
      exact mul_le_one₀ (hQ j) (pow_nonneg (norm_nonneg _) _)
        (pow_le_one₀ (norm_nonneg _) (HenselComplete.norm_le_one u))) hrd
  have hPQ : P.eval (u : C) = c * Q.eval (u : C) := by
    simp only [Q, eval_mul, eval_C, ← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  rw [hPQ, norm_mul, hQu, mul_one]
  exact hmax i

end Dominance

/-! ### Symmetrization over the `p`-th roots of unity -/

section Symm

variable {S : Type*} [CommRing S] (p : ℕ)

/-- `∏_{i < p} P(ζ^i X)`. -/
noncomputable def symm (ζ : S) (P : S[X]) : S[X] :=
  ∏ i ∈ Finset.range p, P.comp (Polynomial.C (ζ ^ i) * X)

omit [CommRing S] in
lemma pow_mod_eq {S : Type*} [Monoid S] {ζ : S} (hζ : ζ ^ p = 1) (n : ℕ) :
    ζ ^ (n % p) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n p, pow_add, pow_mul, hζ, one_pow, mul_one]

lemma comp_C_mul_X_comp (P : S[X]) (a b : S) :
    (P.comp (Polynomial.C a * X)).comp (Polynomial.C b * X) =
      P.comp (Polynomial.C (b * a) * X) := by
  rw [comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← Polynomial.C_mul, mul_comm a b]

lemma symm_comp {ζ : S} (hp : 0 < p) (hζ : ζ ^ p = 1) (P : S[X]) :
    (symm p ζ P).comp (Polynomial.C ζ * X) = symm p ζ P := by
  classical
  have h := map_prod (compRingHom (Polynomial.C ζ * X)) (fun i ↦ P.comp (Polynomial.C (ζ ^ i) * X))
    (Finset.range p)
  simp only [coe_compRingHom] at h
  rw [symm, h]
  simp only [comp_C_mul_X_comp, ← pow_succ']
  refine Finset.prod_nbij' (fun i ↦ (i + 1) % p) (fun i ↦ (i + p - 1) % p) ?_ ?_ ?_ ?_ ?_
  · intro i _; exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  · intro i _; exact Finset.mem_range.2 (Nat.mod_lt _ hp)
  · intro i hi
    have hi := Finset.mem_range.1 hi
    rcases Nat.lt_or_ge (i + 1) p with h | h
    · rw [Nat.mod_eq_of_lt h, show i + 1 + p - 1 = i + p by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt hi]
    · rw [show i + 1 = p by omega, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega)]
      omega
  · intro i hi
    have hi := Finset.mem_range.1 hi
    rcases Nat.eq_zero_or_pos i with rfl | h
    · have h1 : (0 + p - 1) % p = p - 1 := by
        rw [zero_add]; exact Nat.mod_eq_of_lt (Nat.sub_lt hp one_pos)
      rw [h1, Nat.sub_add_cancel hp, Nat.mod_self]
    · have h1 : (i + p - 1) % p = i - 1 := by
        rw [show i + p - 1 = i - 1 + p by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [h1, Nat.sub_add_cancel h, Nat.mod_eq_of_lt hi]
  · intro i _
    rw [pow_mod_eq p hζ]

lemma coeff_symm_eq_zero [IsDomain S] {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) (P : S[X])
    {k : ℕ} (hk : ¬ p ∣ k) : (symm p ζ P).coeff k = 0 := by
  have h := congrArg (coeff · k) (symm_comp p hp hζ.pow_eq_one P)
  simp only [comp_C_mul_X_coeff] at h
  have hne : ζ ^ k ≠ 1 := fun h' ↦ hk ((hζ.pow_eq_one_iff_dvd k).1 h')
  have : (symm p ζ P).coeff k * (ζ ^ k - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  exact (mul_eq_zero.1 this).resolve_right (sub_ne_zero.2 hne)

/-- The norm of `P(Y)` along `Y^p = e`: `∏ P(ζ^i Y)` is a polynomial in `Y^p`. -/
noncomputable def norm1 (ζ e : S) (P : S[X]) : S := (contract p (symm p ζ P)).eval e

lemma expand_contract_symm [IsDomain S] {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p)
    (P : S[X]) : expand S p (contract p (symm p ζ P)) = symm p ζ P := by
  ext n
  rw [coeff_expand hp]
  split_ifs with h
  · rw [coeff_contract hp.ne', Nat.div_mul_cancel h]
  · exact (coeff_symm_eq_zero p hζ hp P h).symm

/-- **Evaluation of the norm**: `ψ (norm1 e P) = ∏_i P^ψ(ψ(ζ)^i y)` for every `y` with
`y^p = ψ e`. -/
theorem norm1_map [IsDomain S] {ζ : S} (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) {T : Type*}
    [CommRing T] (ψ : S →+* T) {e : S} {y : T} (hy : y ^ p = ψ e) (P : S[X]) :
    ψ (norm1 p ζ e P) = ∏ i ∈ Finset.range p, (P.map ψ).eval (ψ ζ ^ i * y) := by
  rw [norm1, ← eval₂_hom, ← eval_map, ← hy, ← expand_eval, ← map_expand,
    expand_contract_symm p hζ hp, symm, Polynomial.map_prod, eval_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [map_comp, Polynomial.map_mul, map_C, map_X, eval_comp, eval_mul, eval_C, eval_X, map_pow]

end Symm

/-! ### Iterated norms over a tower of `p`-th roots -/

section NormAll

variable {R : Type*} [CommRing R] [IsDomain R] (p : ℕ) (ζ : R)
  (e : (i : ℕ) → MvPolynomial (Fin i) R)

/-- The iterated norm: the root `i` satisfies `X_i^p = e i (X_0, …, X_{i-1})`; in
`MvPolynomial (Fin (n+1)) R` the newest root is the variable `0`. -/
noncomputable def normAll : (n : ℕ) → MvPolynomial (Fin n) R → R
  | 0, Q => MvPolynomial.isEmptyAlgEquiv R (Fin 0) Q
  | n + 1, Q => normAll n (norm1 p (MvPolynomial.C ζ) (e n) (MvPolynomial.finSuccEquiv R n Q))

variable {K : Type*} [Field K] (φ : R →+* K)

/-- Valid root vectors: `x 0` is a `p`-th root of `e n` evaluated at the older roots. -/
def Valid : (n : ℕ) → (Fin n → K) → Prop
  | 0, _ => True
  | n + 1, x => Valid n (Fin.tail x) ∧ x 0 ^ p = MvPolynomial.eval₂ φ (Fin.tail x) (e n)

omit [IsDomain R] in
lemma eval_finSuccEquiv (n : ℕ) (x : Fin n → K) (y : K) (Q : MvPolynomial (Fin (n + 1)) R) :
    ((MvPolynomial.finSuccEquiv R n Q).map (MvPolynomial.eval₂Hom φ x)).eval y =
      MvPolynomial.eval₂ φ (Fin.cons y x) Q := by
  set f : MvPolynomial (Fin (n + 1)) R →+* K := (Polynomial.evalRingHom y).comp
    ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom φ x)).comp
      (MvPolynomial.finSuccEquiv R n).toRingEquiv.toRingHom)
  have : f = MvPolynomial.eval₂Hom φ (Fin.cons y x) := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
    · simp only [f, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        AlgEquiv.toRingEquiv_toRingHom, RingHom.coe_coe, MvPolynomial.eval₂Hom_C]
      rw [show (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) =
        algebraMap R (MvPolynomial (Fin (n + 1)) R) r from rfl, AlgEquiv.commutes]
      simp [Polynomial.coe_mapRingHom]
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · simp [f, MvPolynomial.finSuccEquiv_X_zero]
      · simp [f, MvPolynomial.finSuccEquiv_X_succ]
  exact congrArg (· Q) this

omit [IsDomain R] in
lemma eval_isEmptyAlgEquiv (x : Fin 0 → K) (Q : MvPolynomial (Fin 0) R) :
    φ (MvPolynomial.isEmptyAlgEquiv R (Fin 0) Q) = MvPolynomial.eval₂ φ x Q := by
  have : φ.comp (MvPolynomial.isEmptyAlgEquiv R (Fin 0)).toRingEquiv.toRingHom =
      MvPolynomial.eval₂Hom φ x := by
    refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ Fin.elim0 i)
    change φ (MvPolynomial.isEmptyAlgEquiv R (Fin 0) (MvPolynomial.C r)) =
      MvPolynomial.eval₂Hom φ x (MvPolynomial.C r)
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C,
      show (MvPolynomial.C r : MvPolynomial (Fin 0) R) = algebraMap R _ r from rfl,
      AlgEquiv.commutes]
    rfl
  exact congrArg (· Q) this

/-- **Zeros of the iterated norm.** -/
theorem exists_valid_of_normAll_eq_zero [IsAlgClosed K] (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) :
    ∀ (n : ℕ) (Q : MvPolynomial (Fin n) R), φ (normAll p ζ e n Q) = 0 →
      ∃ x : Fin n → K, Valid p e φ n x ∧ MvPolynomial.eval₂ φ x Q = 0 := by
  intro n
  induction n with
  | zero =>
    intro Q hQ
    exact ⟨Fin.elim0, trivial, by rw [← eval_isEmptyAlgEquiv]; exact hQ⟩
  | succ n ih =>
    intro Q hQ
    obtain ⟨x, hx, hx0⟩ := ih _ hQ
    set ψ := MvPolynomial.eval₂Hom φ x
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (ψ (e n)) hp
    have hζ' : IsPrimitiveRoot (MvPolynomial.C ζ : MvPolynomial (Fin n) R) p :=
      hζ.map_of_injective (MvPolynomial.C_injective _ _)
    have h := norm1_map p hζ' hp ψ hy (MvPolynomial.finSuccEquiv R n Q)
    rw [show ψ (norm1 p (MvPolynomial.C ζ) (e n) (MvPolynomial.finSuccEquiv R n Q)) = 0 from hx0,
      eq_comm, Finset.prod_eq_zero_iff] at h
    obtain ⟨i, -, hi⟩ := h
    rw [eval_finSuccEquiv] at hi
    refine ⟨Fin.cons (ψ (MvPolynomial.C ζ) ^ i * y) x, ⟨?_, ?_⟩, hi⟩
    · simpa [Fin.tail] using hx
    · simp only [Fin.cons_zero, Fin.tail_cons, mul_pow, ← pow_mul, hy]
      rw [mul_comm i p, pow_mul]
      simp only [ψ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
      rw [← map_pow, hζ.pow_eq_one, map_one, one_pow, one_mul]

/-- `‖∏_{i ≤ k} vᵢ - c^(k+1)‖ ≤ η M^k` if `‖vᵢ - c‖ ≤ η ≤ M` and `‖c‖ ≤ M`. -/
lemma norm_prod_sub_pow_le {L : Type*} [NormedField L] [IsUltrametricDist L] {v : ℕ → L}
    {c : L} {η M : ℝ} (hv : ∀ i, ‖v i - c‖ ≤ η) (hc : ‖c‖ ≤ M) (hη : η ≤ M) (hη0 : 0 ≤ η)
    (k : ℕ) : ‖∏ i ∈ Finset.range (k + 1), v i - c ^ (k + 1)‖ ≤ η * M ^ k := by
  have hM0 : 0 ≤ M := hη0.trans hη
  have hvM : ∀ i, ‖v i‖ ≤ M := fun i ↦ by
    have := IsUltrametricDist.norm_add_le_max (v i - c) c
    rw [sub_add_cancel] at this
    exact this.trans (max_le ((hv i).trans hη) hc)
  induction k with
  | zero => simpa using hv 0
  | succ k ih =>
    have hdecomp : ∏ i ∈ Finset.range (k + 1 + 1), v i - c ^ (k + 1 + 1) =
        (∏ i ∈ Finset.range (k + 1), v i - c ^ (k + 1)) * v (k + 1) +
          c ^ (k + 1) * (v (k + 1) - c) := by
      rw [Finset.prod_range_succ, pow_succ]; ring
    rw [hdecomp]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, pow_succ M k, ← mul_assoc]
      exact mul_le_mul ih (hvM _) (norm_nonneg _) (mul_nonneg hη0 (pow_nonneg hM0 _))
    · rw [norm_mul, norm_pow, mul_comm]
      calc ‖v (k + 1) - c‖ * ‖c‖ ^ (k + 1) ≤ η * M ^ (k + 1) :=
            mul_le_mul (hv _) (pow_le_pow_left₀ (norm_nonneg _) hc _)
              (pow_nonneg (norm_nonneg _) _) hη0

/-- **The iterated norm is close to `c^(p^n)`** if every valid evaluation is close to `c`. -/
theorem norm_normAll_sub_le {L : Type*} [NormedField L] [IsUltrametricDist L] [IsAlgClosed L]
    (φ : R →+* L) (hζ : IsPrimitiveRoot ζ p) (hp : 0 < p) :
    ∀ (n : ℕ) (Q : MvPolynomial (Fin n) R) (c : L) (η M : ℝ), 0 ≤ η → η ≤ M → ‖c‖ ≤ M →
      (∀ x : Fin n → L, Valid p e φ n x → ‖MvPolynomial.eval₂ φ x Q - c‖ ≤ η) →
      ‖φ (normAll p ζ e n Q) - c ^ (p ^ n)‖ ≤ η * M ^ (p ^ n - 1) := by
  intro n
  induction n with
  | zero =>
    intro Q c η M _ _ _ h
    simp only [pow_zero, pow_one, Nat.sub_self, mul_one]
    rw [show normAll p ζ e 0 Q = MvPolynomial.isEmptyAlgEquiv R (Fin 0) Q from rfl,
      eval_isEmptyAlgEquiv φ Fin.elim0]
    exact h _ trivial
  | succ n ih =>
    intro Q c η M hη0 hηM hcM h
    have hM0 : 0 ≤ M := hη0.trans hηM
    set Q' := norm1 p (MvPolynomial.C ζ) (e n) (MvPolynomial.finSuccEquiv R n Q)
    have hζ' : IsPrimitiveRoot (MvPolynomial.C ζ : MvPolynomial (Fin n) R) p :=
      hζ.map_of_injective (MvPolynomial.C_injective _ _)
    have hQ' : ∀ x : Fin n → L, Valid p e φ n x →
        ‖MvPolynomial.eval₂ φ x Q' - c ^ p‖ ≤ η * M ^ (p - 1) := by
      intro x hx
      set ψ := MvPolynomial.eval₂Hom φ x
      obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (ψ (e n)) hp
      have h1 := norm1_map p hζ' hp ψ hy (MvPolynomial.finSuccEquiv R n Q)
      change ψ Q' = _ at h1
      rw [show MvPolynomial.eval₂ φ x Q' = ψ Q' from rfl, h1]
      simp only [ψ, eval_finSuccEquiv]
      have hval : ∀ i, ‖MvPolynomial.eval₂ φ (Fin.cons (ψ (MvPolynomial.C ζ) ^ i * y) x) Q - c‖
          ≤ η := fun i ↦ h _ ⟨by simpa [Fin.tail] using hx, by
            simp only [Fin.cons_zero, Fin.tail_cons, mul_pow, ← pow_mul, hy]
            rw [mul_comm i p, pow_mul]
            simp only [ψ, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]
            rw [← map_pow, hζ.pow_eq_one, map_one, one_pow, one_mul]⟩
      have := norm_prod_sub_pow_le hval hcM hηM hη0 (p - 1)
      rwa [Nat.sub_add_cancel hp] at this
    have hpow : ‖c ^ p‖ ≤ M ^ p := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hcM _
    have hηM' : η * M ^ (p - 1) ≤ M ^ p := by
      calc η * M ^ (p - 1) ≤ M * M ^ (p - 1) := mul_le_mul_of_nonneg_right hηM (pow_nonneg hM0 _)
        _ = M ^ p := by rw [← pow_succ', Nat.sub_add_cancel hp]
    have := ih Q' (c ^ p) (η * M ^ (p - 1)) (M ^ p) (mul_nonneg hη0 (pow_nonneg hM0 _)) hηM'
      hpow hQ'
    rw [← pow_mul, ← pow_succ', mul_assoc, ← pow_mul, ← pow_add] at this
    have hq : 1 ≤ p ^ n := Nat.one_le_pow _ _ hp
    have hexp : p - 1 + p * (p ^ n - 1) = p ^ (n + 1) - 1 := by
      rw [pow_succ', Nat.mul_sub_one]
      have : p ≤ p * p ^ n := Nat.le_mul_of_pos_right p hq
      omega
    rw [hexp] at this
    exact this

end NormAll

/-! ### One step of the truncated `p`-Taylor algorithm with a given root -/

section Step

open PTaylor

variable (p : ℕ) [hp : Fact p.Prime]

/-- **One step with a given root.** If `δ^p` is the coefficient of `a = F - h^p` at `p j`
(`j ≥ 1`), then `h' = h + δ tʲ` kills that coefficient up to `‖p‖ ‖δ‖`, keeps the constant
coefficient `0`, and changes every other coefficient by at most `‖p‖ ‖δ‖`. -/
theorem step_root {F h : PowerSeries C} (hh : Bnd h 1) (ha0 : PowerSeries.coeff 0 (F - h ^ p) = 0)
    {j : ℕ} (hj : 1 ≤ j) {δ : C} (hδ : δ ^ p = PowerSeries.coeff (p * j) (F - h ^ p))
    (hδ1 : ‖δ‖₊ ≤ 1) :
    Bnd (h + PowerSeries.monomial j δ) 1 ∧
      PowerSeries.coeff 0 (F - (h + PowerSeries.monomial j δ) ^ p) = 0 ∧
      ∀ i, ‖PowerSeries.coeff i (F - (h + PowerSeries.monomial j δ) ^ p) -
        (if i = p * j then 0 else PowerSeries.coeff i (F - h ^ p))‖₊ ≤ ‖(p : C)‖₊ * ‖δ‖₊ := by
  set y : PowerSeries C := PowerSeries.monomial j δ
  set R := (h + y) ^ p - h ^ p - y ^ p
  have hy : Bnd y 1 := Bnd.monomial hδ1 j
  have hyδ : Bnd y ‖δ‖₊ := Bnd.monomial le_rfl j
  have hR : Bnd R (‖(p : C)‖₊ * ‖δ‖₊) := bnd_add_pow_sub_pow p fun k hk hkp ↦ by
    have := (hh.pow k).mul (hyδ.pow (p - k))
    refine this.mono ?_
    rw [one_pow, one_mul]
    exact pow_le_of_le_one zero_le hδ1 (by omega)
  have hyp : y ^ p = PowerSeries.monomial (p * j) (δ ^ p) := by
    rw [PowerSeries.monomial_pow]
  have hdecomp : F - (h + y) ^ p = (F - h ^ p) - y ^ p - R := by simp only [R]; ring
  have hR0 : PowerSeries.coeff 0 R = 0 := by
    simp only [R, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, map_pow, map_add]
    rw [show PowerSeries.constantCoeff y = 0 by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_monomial,
        if_neg (by omega)], add_zero, zero_pow hp.out.ne_zero]
    ring
  refine ⟨hh.add hy, ?_, fun i ↦ ?_⟩
  · rw [hdecomp, map_sub, map_sub, ha0, hR0, hyp, PowerSeries.coeff_monomial,
      if_neg (by have := hp.out.pos; positivity)]
    simp
  · rw [hdecomp, map_sub, map_sub, hyp, PowerSeries.coeff_monomial]
    split_ifs with hi
    · subst hi
      rw [← hδ, sub_self, zero_sub, sub_zero, nnnorm_neg]
      exact hR _
    · rw [sub_zero, sub_sub_cancel_left, nnnorm_neg]
      exact hR _

end Step

/-! ### The generic `p`-Taylor algorithm with symbolic roots -/

section Generic

variable (p : ℕ) (f : C[X]) (sched : ℕ → ℕ)

/-- `f(T + s)` as a polynomial in `s` over `C[T]`. -/
noncomputable def genF : Polynomial C[X] :=
  (f.map (Polynomial.C : C →+* C[X])).comp (X + Polynomial.C Polynomial.X)

/-- The generic approximant after `i` roots; the newest root is the variable `0`. -/
noncomputable def genH : (i : ℕ) → Polynomial (MvPolynomial (Fin i) C[X])
  | 0 => 0
  | i + 1 => (genH i).map (MvPolynomial.rename Fin.succ).toRingHom +
      Polynomial.C (MvPolynomial.X 0) * X ^ sched i

/-- The generic error `f(T + s) - H^p` after `i` roots. -/
noncomputable def genA (i : ℕ) : Polynomial (MvPolynomial (Fin i) C[X]) :=
  (genF f).map (algebraMap C[X] _) - genH sched i ^ p

/-- The relation of the root `i`: its `p`-th power is the coefficient of `s^(p · sched i)`. -/
noncomputable def genE (i : ℕ) : MvPolynomial (Fin i) C[X] := (genA p f sched i).coeff (p * sched i)

/-- Evaluation at the centre `τ` and the roots `x`. -/
noncomputable abbrev ev (τ : C) {i : ℕ} (x : Fin i → C) : MvPolynomial (Fin i) C[X] →+* C :=
  MvPolynomial.eval₂Hom (Polynomial.evalRingHom τ) x

omit [IsUltrametricDist C] in
lemma map_genF (τ : C) {i : ℕ} (x : Fin i → C) :
    ((genF f).map (algebraMap C[X] (MvPolynomial (Fin i) C[X]))).map (ev τ x) = taylor τ f := by
  rw [Polynomial.map_map, show (ev τ x).comp (algebraMap C[X] (MvPolynomial (Fin i) C[X])) =
    Polynomial.evalRingHom τ from MvPolynomial.eval₂Hom_comp_C _ _, genF, map_comp,
    Polynomial.map_map, taylor_apply]
  rw [show (Polynomial.evalRingHom τ).comp (Polynomial.C : C →+* C[X]) = RingHom.id C from
    RingHom.ext fun c ↦ by simp, Polynomial.map_id]
  simp

omit [IsUltrametricDist C] in
lemma map_genH_succ (τ : C) {i : ℕ} (x : Fin i → C) (y : C) :
    (genH sched (i + 1)).map (ev τ (Fin.cons y x)) =
      (genH sched i).map (ev τ x) + Polynomial.C y * X ^ sched i := by
  rw [genH, Polynomial.map_add, Polynomial.map_map]
  have : (ev τ (Fin.cons y x : Fin (i + 1) → C)).comp
      (MvPolynomial.rename Fin.succ).toRingHom = ev τ x := by
    refine MvPolynomial.ringHom_ext (fun r ↦ by simp) (fun q ↦ ?_)
    change ev τ (Fin.cons y x) (MvPolynomial.rename Fin.succ (MvPolynomial.X q)) = _
    simp
  rw [this]
  simp

omit [IsUltrametricDist C] in
lemma ev_genA (τ : C) {i : ℕ} (x : Fin i → C) :
    (genA p f sched i).map (ev τ x) = taylor τ f - ((genH sched i).map (ev τ x)) ^ p := by
  rw [genA, Polynomial.map_sub, map_genF, Polynomial.map_pow]

omit [IsUltrametricDist C] in
lemma ev_genE (τ : C) {i : ℕ} (x : Fin i → C) :
    ev τ x (genE p f sched i) =
      (taylor τ f - ((genH sched i).map (ev τ x)) ^ p).coeff (p * sched i) := by
  rw [genE, ← ev_genA, coeff_map]

end Generic

/-! ### The concrete algorithm: estimates for every choice of roots -/

section Concrete

open PTaylor

variable (p : ℕ) [hp : Fact p.Prime] (f : C[X]) (sched : ℕ → ℕ)

/-- Coefficients of a Taylor shift at a point of the closed unit disc. -/
lemma norm_taylor_coeff_le {τ : C} (hτ : ‖τ‖ ≤ 1) {M : ℝ} (hM : 0 ≤ M)
    (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M) {k : ℕ} (hk : 1 ≤ k) :
    ‖(taylor τ f).coeff k‖ ≤ M := by
  rw [taylor_coeff, eval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM fun n _ ↦ ?_
  rw [hasseDeriv_coeff, norm_mul, norm_mul, norm_pow]
  calc ‖((n + k).choose k : C)‖ * ‖f.coeff (n + k)‖ * ‖τ‖ ^ n ≤ 1 * M * 1 := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one C _
        · exact hfM _ (by omega)
        · exact pow_le_one₀ (norm_nonneg _) hτ
    _ = M := by ring

lemma norm_eval_le_one {τ : C} (hτ : ‖τ‖ ≤ 1) {M : ℝ} (hM1 : M ≤ 1) (hf0 : ‖f.coeff 0‖ ≤ 1)
    (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M) : ‖f.eval τ‖ ≤ 1 := by
  rw [eval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun n _ ↦ ?_
  rw [norm_mul, norm_pow]
  refine mul_le_one₀ ?_ (pow_nonneg (norm_nonneg _) _) (pow_le_one₀ (norm_nonneg _) hτ)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact hf0
  · exact (hfM n hn).trans hM1

/-- The concrete approximant after `n` roots. -/
noncomputable abbrev cH (τ : C) {n : ℕ} (x : Fin n → C) : C[X] := (genH sched n).map (ev τ x)

omit [IsUltrametricDist C] hp in
lemma valid_succ_iff {τ : C} {n : ℕ} (x : Fin (n + 1) → C) :
    Valid p (genE p f sched) (Polynomial.evalRingHom τ) (n + 1) x ↔
      Valid p (genE p f sched) (Polynomial.evalRingHom τ) n (Fin.tail x) ∧
        x 0 ^ p = (taylor τ f - (cH sched τ (Fin.tail x)) ^ p).coeff (p * sched n) := by
  rw [Valid, ← ev_genE]
  rfl

omit [IsUltrametricDist C] hp in
lemma cH_succ {τ : C} {n : ℕ} (x : Fin (n + 1) → C) :
    cH sched τ x = cH sched τ (Fin.tail x) + Polynomial.C (x 0) * X ^ sched n := by
  conv_lhs => rw [← Fin.cons_self_tail x]
  exact map_genH_succ sched τ (Fin.tail x) (x 0)

/-- **The invariant of the concrete algorithm** (any valid choice of roots): the approximant
has integral coefficients, the error `a = f(τ + s) - h^p` has constant coefficient `0` and all
coefficients of norm `≤ M`, and its linear coefficient is within `‖p‖ M^(1/p)` of `f'(τ)`. -/
theorem conc_inv (hsched0 : sched 0 = 0) (hsched : ∀ i, 1 ≤ i → 1 ≤ sched i) {τ : C}
    (hτ : ‖τ‖ ≤ 1) {M : ℝ≥0} (hM1 : M ≤ 1) (hf0 : ‖f.coeff 0‖ ≤ 1)
    (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M) (hη : ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) ≤ M) :
    ∀ n, 1 ≤ n → ∀ x : Fin n → C, Valid p (genE p f sched) (Polynomial.evalRingHom τ) n x →
      (∀ i, ‖(cH sched τ x).coeff i‖₊ ≤ 1) ∧
      (taylor τ f - cH sched τ x ^ p).coeff 0 = 0 ∧
      (∀ i, ‖(taylor τ f - cH sched τ x ^ p).coeff i‖₊ ≤ M) ∧
      ‖(taylor τ f - cH sched τ x ^ p).coeff 1 - f.derivative.eval τ‖₊ ≤
        ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) := by
  intro n hn
  induction n with
  | zero => omega
  | succ n ih =>
    intro x hx
    rw [valid_succ_iff] at hx
    obtain ⟨hxt, hx0⟩ := hx
    rw [cH_succ]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · -- the first root: `h = x 0` constant
      have hH0 : cH sched τ (Fin.tail x) = 0 := by simp [cH, genH]
      rw [hsched0, mul_zero, hH0, zero_pow hp.out.ne_zero, sub_zero, taylor_coeff_zero] at hx0
      rw [hH0, zero_add, hsched0, pow_zero, mul_one, ← Polynomial.C_pow, hx0]
      have hx1 : ‖x 0‖₊ ≤ 1 := by
        have h1 : ‖x 0‖₊ ^ p ≤ 1 := by
          rw [← nnnorm_pow, hx0, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
          exact norm_eval_le_one f hτ (NNReal.coe_le_coe.2 hM1) hf0 fun i hi ↦ hfM i hi
        exact (pow_le_one_iff_of_nonneg zero_le hp.out.ne_zero).1 h1
      refine ⟨fun i ↦ ?_, by simp [taylor_coeff_zero], fun i ↦ ?_, ?_⟩
      · rw [coeff_C]; split_ifs <;> simp [hx1]
      · rw [coeff_sub, coeff_C]
        split_ifs with hi
        · subst hi; simp [taylor_coeff_zero]
        · rw [sub_zero, ← NNReal.coe_le_coe, coe_nnnorm]
          exact norm_taylor_coeff_le f hτ M.2 (fun i hi ↦ hfM i hi) (by omega)
      · rw [coeff_sub, coeff_C, if_neg one_ne_zero, sub_zero, taylor_coeff_one, sub_self,
          nnnorm_zero]
        exact zero_le
    · obtain ⟨hb, h0, hM, hlin⟩ := ih hn0 (Fin.tail x) hxt
      set h := cH sched τ (Fin.tail x)
      set j := sched n
      have hj : 1 ≤ j := hsched n hn0
      -- pass to power series
      set Fs : PowerSeries C := (taylor τ f : PowerSeries C)
      set hs : PowerSeries C := (h : PowerSeries C)
      have hcoe : ∀ q : C[X], ((taylor τ f - q ^ p : C[X]) : PowerSeries C) =
          Fs - (q : PowerSeries C) ^ p := by
        intro q
        rw [Polynomial.coe_sub, Polynomial.coe_pow]
      have hδ : x 0 ^ p = PowerSeries.coeff (p * j) (Fs - hs ^ p) := by
        rw [← hcoe, Polynomial.coeff_coe]; exact hx0
      have hδM : ‖x 0‖₊ ^ p ≤ M := by rw [← nnnorm_pow, hx0]; exact hM _
      have hδ1 : ‖x 0‖₊ ≤ 1 := (pow_le_one_iff_of_nonneg zero_le hp.out.ne_zero).1
        (hδM.trans hM1)
      have hδη : ‖(p : C)‖₊ * ‖x 0‖₊ ≤ ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        calc ‖x 0‖₊ = (‖x 0‖₊ ^ p) ^ ((p : ℝ)⁻¹) :=
              (NNReal.pow_rpow_inv_natCast _ hp.out.ne_zero).symm
          _ ≤ M ^ ((p : ℝ)⁻¹) := NNReal.rpow_le_rpow hδM (inv_nonneg.2 (Nat.cast_nonneg p))
      obtain ⟨hb', h0', hcl⟩ := step_root p (F := Fs) (h := hs)
        (fun i ↦ by rw [Polynomial.coeff_coe]; exact hb i)
        (by rw [← hcoe, Polynomial.coeff_coe]; exact h0) hj hδ hδ1
      have hmono : ((h + Polynomial.C (x 0) * X ^ j : C[X]) : PowerSeries C) =
          hs + PowerSeries.monomial j (x 0) := by
        rw [Polynomial.coe_add, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_monomial]
      have hcoeff : ∀ i, (taylor τ f - (h + Polynomial.C (x 0) * X ^ j) ^ p).coeff i =
          PowerSeries.coeff i (Fs - (hs + PowerSeries.monomial j (x 0)) ^ p) := fun i ↦ by
        rw [← hmono, ← hcoe, Polynomial.coeff_coe]
      have hcoeff' : ∀ i, (taylor τ f - h ^ p).coeff i = PowerSeries.coeff i (Fs - hs ^ p) :=
        fun i ↦ by rw [← hcoe, Polynomial.coeff_coe]
      have hsub : ∀ a b c : C, ‖a - c‖₊ ≤ max ‖a - b‖₊ ‖b - c‖₊ := fun a b c ↦ by
        rw [show a - c = (a - b) + (b - c) by ring]
        exact IsUltrametricDist.nnnorm_add_le_max _ _
      refine ⟨fun i ↦ ?_, ?_, fun i ↦ ?_, ?_⟩
      · have := hb' i
        rwa [← hmono, Polynomial.coeff_coe] at this
      · rw [hcoeff]; exact h0'
      · rw [hcoeff]
        have h1 := hcl i
        have h2 : ‖(if i = p * j then 0 else PowerSeries.coeff i (Fs - hs ^ p))‖₊ ≤ M := by
          split_ifs
          · simp
          · rw [← hcoeff']; exact hM i
        calc _ ≤ max ‖PowerSeries.coeff i (Fs - (hs + PowerSeries.monomial j (x 0)) ^ p) -
              (if i = p * j then 0 else PowerSeries.coeff i (Fs - hs ^ p))‖₊
              ‖(if i = p * j then 0 else PowerSeries.coeff i (Fs - hs ^ p))‖₊ := by
              have := IsUltrametricDist.nnnorm_add_le_max
                (PowerSeries.coeff i (Fs - (hs + PowerSeries.monomial j (x 0)) ^ p) -
                  (if i = p * j then 0 else PowerSeries.coeff i (Fs - hs ^ p)))
                (if i = p * j then 0 else PowerSeries.coeff i (Fs - hs ^ p))
              rwa [sub_add_cancel] at this
          _ ≤ M := max_le (h1.trans (hδη.trans hη)) h2
      · rw [hcoeff]
        have h1 := hcl 1
        have hp1 : (1 : ℕ) ≠ p * j := by
          have := hp.out.two_le
          nlinarith
        rw [if_neg hp1, ← hcoeff'] at h1
        exact (hsub _ _ _).trans (max_le (h1.trans hδη) hlin)

/-- **One step of the concrete algorithm** (any valid choice of roots): the new error differs
from the old one, with the coefficient at `p · sched n` killed, by at most `‖p‖ ‖x 0‖`. -/
theorem conc_step (hsched0 : sched 0 = 0) (hsched : ∀ i, 1 ≤ i → 1 ≤ sched i) {τ : C}
    (hτ : ‖τ‖ ≤ 1) {M : ℝ≥0} (hM1 : M ≤ 1) (hf0 : ‖f.coeff 0‖ ≤ 1)
    (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M) (hη : ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) ≤ M) {n : ℕ}
    (hn : 1 ≤ n) (x : Fin (n + 1) → C)
    (hx : Valid p (genE p f sched) (Polynomial.evalRingHom τ) (n + 1) x) :
    (∀ i, ‖(taylor τ f - cH sched τ x ^ p).coeff i -
      (if i = p * sched n then 0 else (taylor τ f - cH sched τ (Fin.tail x) ^ p).coeff i)‖₊ ≤
        ‖(p : C)‖₊ * ‖x 0‖₊) ∧
      ‖x 0‖₊ ^ p = ‖(taylor τ f - cH sched τ (Fin.tail x) ^ p).coeff (p * sched n)‖₊ := by
  rw [valid_succ_iff] at hx
  obtain ⟨hxt, hx0⟩ := hx
  obtain ⟨hb, h0, hM, -⟩ := conc_inv p f sched hsched0 hsched hτ hM1 hf0 hfM hη n hn _ hxt
  rw [cH_succ]
  set h := cH sched τ (Fin.tail x)
  set j := sched n
  have hj : 1 ≤ j := hsched n hn
  set Fs : PowerSeries C := (taylor τ f : PowerSeries C)
  set hs : PowerSeries C := (h : PowerSeries C)
  have hcoe : ∀ q : C[X], ((taylor τ f - q ^ p : C[X]) : PowerSeries C) =
      Fs - (q : PowerSeries C) ^ p := fun q ↦ by rw [Polynomial.coe_sub, Polynomial.coe_pow]
  have hδ : x 0 ^ p = PowerSeries.coeff (p * j) (Fs - hs ^ p) := by
    rw [← hcoe, Polynomial.coeff_coe]; exact hx0
  have hδM : ‖x 0‖₊ ^ p ≤ M := by rw [← nnnorm_pow, hx0]; exact hM _
  have hδ1 : ‖x 0‖₊ ≤ 1 := (pow_le_one_iff_of_nonneg zero_le hp.out.ne_zero).1 (hδM.trans hM1)
  obtain ⟨-, -, hcl⟩ := step_root p (F := Fs) (h := hs)
    (fun i ↦ by rw [Polynomial.coeff_coe]; exact hb i)
    (by rw [← hcoe, Polynomial.coeff_coe]; exact h0) hj hδ hδ1
  have hmono : ((h + Polynomial.C (x 0) * X ^ j : C[X]) : PowerSeries C) =
      hs + PowerSeries.monomial j (x 0) := by
    rw [Polynomial.coe_add, Polynomial.C_mul_X_pow_eq_monomial, Polynomial.coe_monomial]
  refine ⟨fun i ↦ ?_, by rw [← nnnorm_pow, hx0]⟩
  have := hcl i
  rwa [← hmono, ← hcoe, ← hcoe, Polynomial.coeff_coe, Polynomial.coeff_coe] at this

/-- The round-robin schedule: index `0` first, then `1, …, J` repeatedly. -/
def rr (J : ℕ) (i : ℕ) : ℕ := if i = 0 then 0 else (i - 1) % J + 1

omit [IsUltrametricDist C] in
lemma rr_spec {J : ℕ} {q r : ℕ} (hr : r < J) : rr J (1 + q * J + r) = r + 1 := by
  rw [rr, if_neg (by omega), show 1 + q * J + r - 1 = r + J * q by ring_nf; omega,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hr]

/-- The bound after `q` rounds: `bd 0 = M`, `bd (q + 1) = ‖p‖ bd q ^ (1/p)`. -/
noncomputable def bd (C : Type*) [NormedField C] (p : ℕ) (M : ℝ≥0) : ℕ → ℝ≥0
  | 0 => M
  | k + 1 => ‖(p : C)‖₊ * bd C p M k ^ ((p : ℝ)⁻¹)

/-- The precision bound in the state `1 + q J + r`. -/
noncomputable def precBd (C : Type*) [NormedField C] (p : ℕ) (M : ℝ≥0) (q r j' : ℕ) : ℝ≥0 :=
  if j' ≤ r then bd C p M (q + 1) else bd C p M q

/-- The precision statement in the state `1 + q J + r`. -/
def PrecState (J : ℕ) (τ : C) (M : ℝ≥0) (q r : ℕ) {n : ℕ} (x : Fin n → C) : Prop :=
  ∀ j', 1 ≤ j' → j' ≤ J →
    ‖(taylor τ f - cH (rr J) τ x ^ p).coeff (p * j')‖₊ ≤ precBd C p M q r j'

/-- One step of the precision invariant. -/
theorem prec_step {J : ℕ} {τ : C} (hτ : ‖τ‖ ≤ 1) {M : ℝ≥0} (hM1 : M ≤ 1)
    (hf0 : ‖f.coeff 0‖ ≤ 1) (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M)
    (hη : ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) ≤ M) (hdec : ∀ k, bd C p M (k + 1) ≤ bd C p M k)
    {q r : ℕ} (hr : r < J) (x : Fin (1 + q * J + r + 1) → C)
    (hx : Valid p (genE p f (rr J)) (Polynomial.evalRingHom τ) (1 + q * J + r + 1) x)
    (ih : PrecState p f J τ M q r (Fin.tail x)) : PrecState p f J τ M q (r + 1) x := by
  have hsched0 : rr J 0 = 0 := by simp [rr]
  have hsched : ∀ i, 1 ≤ i → 1 ≤ rr J i := fun i hi ↦ by rw [rr, if_neg (by omega)]; omega
  obtain ⟨hcl, hδ⟩ := conc_step p f (rr J) hsched0 hsched hτ hM1 hf0 hfM hη (by omega) x hx
  rw [rr_spec hr] at hcl hδ
  have hδq : ‖x 0‖₊ ^ p ≤ bd C p M q := by
    rw [hδ]
    have := ih (r + 1) (by omega) (by omega)
    rwa [precBd, if_neg (by omega)] at this
  have hcross : ‖(p : C)‖₊ * ‖x 0‖₊ ≤ bd C p M (q + 1) := by
    refine mul_le_mul_of_nonneg_left ?_ zero_le
    calc ‖x 0‖₊ = (‖x 0‖₊ ^ p) ^ ((p : ℝ)⁻¹) :=
          (NNReal.pow_rpow_inv_natCast _ hp.out.ne_zero).symm
      _ ≤ bd C p M q ^ ((p : ℝ)⁻¹) := NNReal.rpow_le_rpow hδq (inv_nonneg.2 (Nat.cast_nonneg p))
  intro j' hj'1 hj'J
  have h1 := hcl (p * j')
  by_cases hj : j' = r + 1
  · subst hj
    rw [if_pos rfl, sub_zero] at h1
    rw [precBd, if_pos le_rfl]
    exact h1.trans hcross
  · have hne : p * j' ≠ p * (r + 1) := fun h ↦ hj (Nat.eq_of_mul_eq_mul_left hp.out.pos h)
    rw [if_neg hne] at h1
    have hold := ih j' hj'1 hj'J
    have h2 : ‖(taylor τ f - cH (rr J) τ x ^ p).coeff (p * j')‖₊ ≤
        max (‖(taylor τ f - cH (rr J) τ (Fin.tail x) ^ p).coeff (p * j')‖₊)
          (bd C p M (q + 1)) := by
      have := IsUltrametricDist.nnnorm_add_le_max
        ((taylor τ f - cH (rr J) τ x ^ p).coeff (p * j') -
          (taylor τ f - cH (rr J) τ (Fin.tail x) ^ p).coeff (p * j'))
        ((taylor τ f - cH (rr J) τ (Fin.tail x) ^ p).coeff (p * j'))
      rw [sub_add_cancel] at this
      exact this.trans (by rw [max_comm]; exact max_le_max le_rfl (h1.trans hcross))
    refine h2.trans (max_le ?_ ?_)
    · rw [precBd] at hold ⊢
      split_ifs at hold ⊢ with ha hb hb
      · exact hold
      · omega
      · omega
      · exact hold
    · rw [precBd]
      split_ifs
      · exact le_rfl
      · exact hdec q

/-- **The precision invariant** of the round-robin algorithm. -/
theorem prec_inv {J : ℕ} {τ : C} (hτ : ‖τ‖ ≤ 1) {M : ℝ≥0} (hM1 : M ≤ 1)
    (hf0 : ‖f.coeff 0‖ ≤ 1) (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M)
    (hη : ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) ≤ M) (hdec : ∀ k, bd C p M (k + 1) ≤ bd C p M k) :
    ∀ q r, r ≤ J → ∀ n, n = 1 + q * J + r → ∀ x : Fin n → C,
      Valid p (genE p f (rr J)) (Polynomial.evalRingHom τ) n x →
      PrecState p f J τ M q r x := by
  have hsched0 : rr J 0 = 0 := by simp [rr]
  have hsched : ∀ i, 1 ≤ i → 1 ≤ rr J i := fun i hi ↦ by rw [rr, if_neg (by omega)]; omega
  -- the inner induction on `r`
  have inner : ∀ q, (∀ n, n = 1 + q * J + 0 → ∀ x : Fin n → C,
      Valid p (genE p f (rr J)) (Polynomial.evalRingHom τ) n x →
      PrecState p f J τ M q 0 x) → ∀ r, r ≤ J → ∀ n, n = 1 + q * J + r → ∀ x : Fin n → C,
      Valid p (genE p f (rr J)) (Polynomial.evalRingHom τ) n x →
      PrecState p f J τ M q r x := by
    intro q h0 r
    induction r with
    | zero => intro _; exact h0
    | succ r ih =>
      intro hr n hn x hx
      subst hn
      refine prec_step p f hτ hM1 hf0 hfM hη hdec (by omega) x hx
        (ih (by omega) _ rfl _ ((valid_succ_iff p f (rr J) x).1 hx).1)
  intro q
  induction q with
  | zero =>
    refine inner 0 fun n hn x hx j' _ _ ↦ ?_
    subst hn
    rw [precBd, if_neg (by omega)]
    exact (conc_inv p f (rr J) hsched0 hsched hτ hM1 hf0 hfM hη _ (by omega) x hx).2.2.1 _
  | succ q ihq =>
    refine inner (q + 1) fun n hn x hx j' hj'1 hj'J ↦ ?_
    have := ihq J le_rfl n (by rw [hn]; ring) x hx j' hj'1 hj'J
    rw [precBd, if_pos hj'J] at this
    rw [precBd, if_neg (by omega)]
    exact this

section Bounds

variable {γ : C} (hγ : γ ^ (p - 1) = -(p : C))

omit [IsUltrametricDist C] hp in
include hγ in
lemma nnnorm_p_eq : ‖(p : C)‖₊ = ‖γ‖₊ ^ (p - 1) := by
  rw [← nnnorm_pow, hγ, nnnorm_neg]

omit [IsUltrametricDist C] in
include hγ in
/-- `A ≤ bd k` if `A = ‖γ‖^p ≤ M`. -/
lemma le_bd {M : ℝ≥0} (hAM : ‖γ‖₊ ^ p ≤ M) (k : ℕ) : ‖γ‖₊ ^ p ≤ bd C p M k := by
  induction k with
  | zero => exact hAM
  | succ k ih =>
    rw [bd]
    have h1 : ‖γ‖₊ ≤ bd C p M k ^ ((p : ℝ)⁻¹) := by
      rw [NNReal.le_rpow_inv_iff (by exact_mod_cast hp.out.pos), NNReal.rpow_natCast]; exact ih
    calc ‖γ‖₊ ^ p = ‖(p : C)‖₊ * ‖γ‖₊ := by
          rw [nnnorm_p_eq p hγ, ← pow_succ, Nat.sub_add_cancel hp.out.one_le]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 zero_le

omit [IsUltrametricDist C] in
include hγ in
/-- `‖p‖ B^(1/p) ≤ B` for `B ≥ A`. -/
lemma mul_rpow_inv_le {B : ℝ≥0} (hB : ‖γ‖₊ ^ p ≤ B) :
    ‖(p : C)‖₊ * B ^ ((p : ℝ)⁻¹) ≤ B := by
  set b := B ^ ((p : ℝ)⁻¹)
  have hbB : b ^ p = B := NNReal.rpow_inv_natCast_pow B hp.out.ne_zero
  have hγb : ‖γ‖₊ ≤ b := by
    rw [← hbB] at hB
    exact (pow_le_pow_iff_left₀ zero_le zero_le hp.out.ne_zero).1 hB
  calc ‖(p : C)‖₊ * b = ‖γ‖₊ ^ (p - 1) * b := by rw [nnnorm_p_eq p hγ]
    _ ≤ b ^ (p - 1) * b := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ zero_le hγb _) zero_le
    _ = B := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le, hbB]

omit [IsUltrametricDist C] in
include hγ in
lemma bd_succ_le {M : ℝ≥0} (hAM : ‖γ‖₊ ^ p ≤ M) (k : ℕ) : bd C p M (k + 1) ≤ bd C p M k :=
  mul_rpow_inv_le p hγ (le_bd p hγ hAM k)

omit [IsUltrametricDist C] hp in
lemma bd_succ_le_pBound {M : ℝ≥0} (hM1 : M ≤ 1) (k : ℕ) :
    bd C p M (k + 1) ≤ pBound C p k := by
  induction k with
  | zero =>
    rw [bd, bd, pBound]
    exact mul_le_of_le_one_right' (NNReal.rpow_le_one hM1 (inv_nonneg.2 (Nat.cast_nonneg p)))
  | succ k ih =>
    rw [bd, pBound]
    exact mul_le_mul_of_nonneg_left
      (NNReal.rpow_le_rpow ih (inv_nonneg.2 (Nat.cast_nonneg p))) zero_le

end Bounds

/-- Integers prime to `p` are units: `‖m‖ = 1` if `p ∤ m` and `‖p‖ < 1`. -/
lemma norm_natCast_eq_one (hp1 : ‖(p : C)‖ < 1) {m : ℕ} (hpm : ¬ p ∣ m) : ‖(m : C)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one C m) (not_lt.1 fun hm ↦ ?_)
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp.out).2 hpm
  have hb := Nat.gcd_eq_gcd_ab p m
  rw [hcop.gcd_eq_one] at hb
  have h1 : (1 : C) = (p : C) * (p.gcdA m : C) + (m : C) * (p.gcdB m : C) := by
    have := congrArg (fun z : ℤ ↦ (z : C)) hb
    push_cast at this
    exact this
  have h2 := IsUltrametricDist.norm_add_le_max ((p : C) * (p.gcdA m : C)) ((m : C) * (p.gcdB m : C))
  rw [← h1, norm_one, norm_mul, norm_mul] at h2
  have ha := IsUltrametricDist.norm_intCast_le_one C (p.gcdA m)
  have hb' := IsUltrametricDist.norm_intCast_le_one C (p.gcdB m)
  have : max (‖(p : C)‖ * ‖((p.gcdA m : ℤ) : C)‖) (‖(m : C)‖ * ‖((p.gcdB m : ℤ) : C)‖) < 1 :=
    max_lt ((mul_le_of_le_one_right (norm_nonneg _) ha).trans_lt hp1)
      ((mul_le_of_le_one_right (norm_nonneg _) hb').trans_lt hm)
  exact absurd h2 (not_le.2 this)

omit hp in
/-- At a centre `‖τ‖ < 1` the Taylor coefficients differ from those of `f` by less than `M`. -/
lemma norm_taylor_coeff_sub_lt {τ : C} (hτ : ‖τ‖ < 1) {M : ℝ} (hM : 0 < M)
    (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M) {k : ℕ} (hk : 1 ≤ k) :
    ‖(taylor τ f).coeff k - f.coeff k‖ < M := by
  rw [taylor_coeff, eval_eq_sum_range, Finset.sum_range_succ', hasseDeriv_coeff, zero_add,
    Nat.choose_self, Nat.cast_one, one_mul, pow_zero, mul_one, add_sub_cancel_right]
  rcases (Finset.range (hasseDeriv k f).natDegree).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, norm_zero]; exact hM
  obtain ⟨n, -, hn⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
    (fun n ↦ (hasseDeriv k f).coeff (n + 1) * τ ^ (n + 1))
  refine hn.trans_lt ?_
  rw [hasseDeriv_coeff, norm_mul, norm_mul, norm_pow]
  calc ‖((n + 1 + k).choose k : C)‖ * ‖f.coeff (n + 1 + k)‖ * ‖τ‖ ^ (n + 1)
      ≤ 1 * M * ‖τ‖ ^ (n + 1) := by
        gcongr
        · exact IsUltrametricDist.norm_natCast_le_one C _
        · exact hfM _ (by omega)
    _ < 1 * M * 1 := by
        gcongr
        exact pow_lt_one₀ (norm_nonneg _) hτ (by omega)
    _ = M := by ring

end Concrete

/-! ### K5: the good centre -/

section Main

open PTaylor

variable (p : ℕ) [hp : Fact p.Prime]

omit hp in
/-- The data of the error at a centre `‖τ‖ < 1` for the trivial approximation. -/
lemma dom_taylor {f : C[X]} {M : ℝ} {m : ℕ} (hM : 0 < M) (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M)
    (hfm : ‖f.coeff m‖ = M) (hflt : ∀ i, 1 ≤ i → i < m → ‖f.coeff i‖ < M) (hm : 1 ≤ m)
    {τ : C} (hτ : ‖τ‖ < 1) {β : C} (hβ : β ^ p = f.eval τ) :
    Dom (fun i ↦ ‖(taylor τ f - Polynomial.C β ^ p).coeff i‖) M m := by
  have hcoeff : ∀ i, 1 ≤ i → (taylor τ f - Polynomial.C β ^ p).coeff i = (taylor τ f).coeff i :=
    fun i hi ↦ by rw [coeff_sub, ← Polynomial.C_pow, coeff_C, if_neg (by omega), sub_zero]
  have hc0 : (taylor τ f - Polynomial.C β ^ p).coeff 0 = 0 := by
    rw [coeff_sub, ← Polynomial.C_pow, coeff_C_zero, hβ, taylor_coeff_zero, sub_self]
  have hsub := fun k (hk : 1 ≤ k) ↦ norm_taylor_coeff_sub_lt f hτ hM hfM hk
  have hle : ∀ k, 1 ≤ k → ‖(taylor τ f).coeff k‖ ≤ M := fun k hk ↦
    norm_taylor_coeff_le f hτ.le hM.le hfM hk
  refine ⟨fun i ↦ norm_nonneg _, ?_, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rw [hcoeff m hm]
    refine le_antisymm (hle m hm) ?_
    by_contra hlt
    push Not at hlt
    have h2 : ‖f.coeff m‖ ≤ max ‖(taylor τ f).coeff m - f.coeff m‖ ‖(taylor τ f).coeff m‖ := by
      have := IsUltrametricDist.norm_add_le_max (-((taylor τ f).coeff m - f.coeff m))
        ((taylor τ f).coeff m)
      rwa [neg_sub, sub_add_cancel, norm_sub_rev] at this
    rw [hfm] at h2
    exact absurd h2 (not_le.2 (max_lt (hsub m hm) hlt))
  · rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [hc0, norm_zero]; exact hM.le
    · rw [hcoeff i hi]; exact hle i hi
  · rcases Nat.eq_zero_or_pos i with rfl | hi0
    · rw [hc0, norm_zero]; exact hM
    · rw [hcoeff i hi0]
      have h2 : ‖(taylor τ f).coeff i‖ ≤
          max ‖(taylor τ f).coeff i - f.coeff i‖ ‖f.coeff i‖ := by
        have := IsUltrametricDist.norm_add_le_max ((taylor τ f).coeff i - f.coeff i) (f.coeff i)
        rwa [sub_add_cancel] at this
      exact h2.trans_lt (max_lt (hsub i hi0) (hflt i hi0 hi))

lemma dom_pow {Q : C[X]} {M : ℝ} {k : ℕ} (hQ : DomP Q M k) (hM : 0 < M) (n : ℕ) :
    DomP (Q ^ n) (M ^ n) (n * k) := by
  induction n with
  | zero => simpa using domP_one
  | succ n ih =>
    rw [pow_succ, pow_succ, Nat.succ_mul]
    exact dom_mul ih hQ (pow_pos hM n) hM

lemma dom_add_small {P E : C[X]} {M : ℝ} {k : ℕ} (hP : DomP P M k) (hE : ∀ i, ‖E.coeff i‖ < M) :
    DomP (P + E) M k := by
  refine ⟨fun i ↦ norm_nonneg _, ?_, fun i ↦ ?_, fun i hi ↦ ?_⟩
  · rw [coeff_add, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hP.eq]; exact (hE k).ne'), hP.eq, max_eq_left (hE k).le]
  · rw [coeff_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP.le i) (hE i).le)
  · rw [coeff_add]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hP.lt i hi) (hE i))

omit [IsUltrametricDist C] in
include hp in
/-- `‖p‖ B^(1/p) < B` for `B > A`. -/
lemma mul_rpow_inv_lt {γ : C} (hγ : γ ^ (p - 1) = -(p : C)) {B : ℝ≥0} (hB : ‖γ‖₊ ^ p < B) :
    ‖(p : C)‖₊ * B ^ ((p : ℝ)⁻¹) < B := by
  set b := B ^ ((p : ℝ)⁻¹)
  have hbB : b ^ p = B := NNReal.rpow_inv_natCast_pow B hp.out.ne_zero
  have hγb : ‖γ‖₊ < b := by
    rw [← hbB] at hB
    exact (pow_lt_pow_iff_left₀ zero_le zero_le hp.out.ne_zero).1 hB
  have hb0 : 0 < b := lt_of_le_of_lt zero_le hγb
  calc ‖(p : C)‖₊ * b = ‖γ‖₊ ^ (p - 1) * b := by rw [nnnorm_p_eq p hγ]
    _ < b ^ (p - 1) * b := mul_lt_mul_of_pos_right
        (pow_lt_pow_left₀ hγb zero_le (Nat.sub_ne_zero_of_lt hp.out.one_lt)) hb0
    _ = B := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le, hbB]

/-- **K5: good centre** (Arzdorf, Prop. 2.31, for polynomials over an algebraically closed
non-archimedean field). Let `f` have integral coefficients, coefficients of norm `≤ M` in
positive degrees, with the maximum `M` first attained at `m ≥ 2`, `p ∤ m`, and `A < M ≤ 1`
(`A = ‖γ‖^p`). Then there are a centre `τ`, `‖τ‖ < 1`, and an approximation `h` with integral
coefficients such that `g = f(τ + s) - h^p` has vanishing constant **and linear** coefficient,
the same data `(M, m)`, and is precise at the `p`-indices below `m`. Proof: the generic
`p`-Taylor algorithm with symbolic roots (`genH`, `genE`), the iterated norm `a(T)` of the linear
coefficient (`normAll`), which is close to `f'(T)^(p^N)` on the closed unit disc
(`norm_normAll_sub_le`, `conc_inv`), hence has a root of norm `< 1` (`exists_root_of_dom`);
at a root some choice of roots kills the linear coefficient (`exists_valid_of_normAll_eq_zero`).
-/
theorem exists_good_centre [IsAlgClosed C] (hp0 : (p : C) ≠ 0) {γ : C}
    (hγ : γ ^ (p - 1) = -(p : C)) {f : C[X]} {M : ℝ≥0} {m : ℕ}
    (hf0 : ‖f.coeff 0‖ ≤ 1) (hfM : ∀ i, 1 ≤ i → ‖f.coeff i‖ ≤ M) (hfm : ‖f.coeff m‖ = M)
    (hflt : ∀ i, 1 ≤ i → i < m → ‖f.coeff i‖ < M) (hpm : ¬ p ∣ m) (hm2 : 2 ≤ m)
    (hAM : ‖γ‖₊ ^ p < M) (hM1 : M ≤ 1) :
    ∃ τ : C, ‖τ‖ < 1 ∧ ∃ h : C[X], (∀ i, ‖h.coeff i‖₊ ≤ 1) ∧
      (taylor τ f - h ^ p).coeff 0 = 0 ∧ (taylor τ f - h ^ p).coeff 1 = 0 ∧
      Dom (fun i ↦ ‖(taylor τ f - h ^ p).coeff i‖) M m ∧
      ∀ i, 0 < i → i < m → p ∣ i →
        ‖(taylor τ f - h ^ p).coeff i‖ ^ m < (‖γ‖ ^ p) ^ (m - i) * (M : ℝ) ^ i := by
  classical
  haveI : NeZero (p : C) := ⟨hp0⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C p
  set ζ : C[X] := Polynomial.C ζ₀
  have hζ : IsPrimitiveRoot ζ p := hζ₀.map_of_injective Polynomial.C_injective
  have hpp := hp.out.pos
  have hAMle : ‖γ‖₊ ^ p ≤ M := hAM.le
  have hM0 : 0 < M := lt_of_le_of_lt zero_le hAM
  have hη : ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) ≤ M := mul_rpow_inv_le p hγ hAMle
  have hηlt : ‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) < M := mul_rpow_inv_lt p hγ hAM
  have hdec := bd_succ_le p hγ hAMle
  have hγ1 : ‖γ‖ < 1 := by
    have h1 : ‖γ‖₊ ^ p < 1 := hAM.trans_le hM1
    have := (pow_lt_one_iff_of_nonneg (norm_nonneg γ) hp.out.ne_zero).1 (by exact_mod_cast h1)
    exact this
  have hp1 : ‖(p : C)‖ < 1 := by
    rw [← coe_nnnorm, nnnorm_p_eq p hγ]
    push_cast
    exact pow_lt_one₀ (norm_nonneg _) hγ1 (Nat.sub_ne_zero_of_lt hp.out.one_lt)
  have hm0 : 0 < m := by omega
  set A : ℝ := ‖γ‖ ^ p
  have hA0 : 0 < A := by
    have : (0 : ℝ) < ‖γ‖ := norm_pos_iff.2 (CriticalRadius.gamma_ne_zero p hγ hp0)
    positivity
  have hAMR : A < M := by
    have : ((‖γ‖₊ ^ p : ℝ≥0) : ℝ) < M := by exact_mod_cast hAM
    simpa [A] using this
  -- the number of rounds
  set J := (m - 1) / p
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  set ε : ℝ := (A ^ (m - 1) * M) ^ ((m : ℝ)⁻¹)
  have hAε : A < ε := by
    refine (Real.lt_rpow_inv_iff_of_pos hA0.le
      (mul_nonneg (pow_nonneg hA0.le (m - 1)) M.2) hmR).2 ?_
    rw [Real.rpow_natCast]
    calc A ^ m = A ^ (m - 1) * A := by rw [← pow_succ, Nat.sub_add_cancel hm0]
      _ < A ^ (m - 1) * M := mul_lt_mul_of_pos_left hAMR (pow_pos hA0 _)
  obtain ⟨k₀, hk₀⟩ := CriticalRadius.exists_pBound_lt p hγ hp0 (hAε : ‖γ‖ ^ p < ε)
  set R := k₀ + 1
  have hbdR : (bd C p M R : ℝ) ^ m < A ^ (m - 1) * M := by
    have h1 : (bd C p M R : ℝ) < ε :=
      lt_of_le_of_lt (by exact_mod_cast bd_succ_le_pBound p hM1 k₀) hk₀
    have := (Real.lt_rpow_inv_iff_of_pos (bd C p M R).2
      (mul_nonneg (pow_nonneg hA0.le (m - 1)) M.2) hmR).1 h1
    rwa [Real.rpow_natCast] at this
  -- the generic data
  set N := 1 + R * J
  set Q := (genA p f (rr J) N).coeff 1
  set aT := normAll p ζ (genE p f (rr J)) N Q
  set D := p ^ N
  set P := f.derivative ^ D
  have hsched0 : rr J 0 = 0 := by simp [rr]
  have hsched : ∀ i, 1 ≤ i → 1 ≤ rr J i := fun i hi ↦ by rw [rr, if_neg (by omega)]; omega
  set η : ℝ := ((‖(p : C)‖₊ * M ^ ((p : ℝ)⁻¹) : ℝ≥0) : ℝ)
  have hηM : η ≤ M := by exact_mod_cast hη
  have hηMlt : η < M := by exact_mod_cast hηlt
  have hη0 : 0 ≤ η := NNReal.coe_nonneg _
  have hQev : ∀ (τ : C) (x : Fin N → C),
      MvPolynomial.eval₂ (Polynomial.evalRingHom τ) x Q =
        (taylor τ f - cH (rr J) τ x ^ p).coeff 1 := fun τ x ↦ by
    rw [← ev_genA, coeff_map]
    rfl
  have hest : ∀ τ : C, ‖τ‖ ≤ 1 → ‖(aT - P).eval τ‖ ≤ η * M ^ (D - 1) := by
    intro τ hτ
    have hcM : ‖f.derivative.eval τ‖ ≤ M := by
      rw [← taylor_coeff_one]
      exact norm_taylor_coeff_le f hτ M.2 hfM le_rfl
    have := norm_normAll_sub_le p ζ (genE p f (rr J)) (Polynomial.evalRingHom τ) hζ hpp N Q
      (f.derivative.eval τ) η M hη0 hηM hcM (fun x hx ↦ by
        rw [hQev]
        have := (conc_inv p f (rr J) hsched0 hsched hτ hM1 hf0 hfM hη N (by omega) x hx).2.2.2
        exact_mod_cast this)
    rwa [eval_sub, eval_pow, show aT.eval τ = Polynomial.evalRingHom τ aT from rfl]
  obtain ⟨τ₀, hτ₀, hmax⟩ := exists_norm_eval_eq (aT - P)
  have hEM : η * (M : ℝ) ^ (D - 1) < (M : ℝ) ^ D := by
    have hD : 1 ≤ D := Nat.one_le_pow _ _ hpp
    calc η * (M : ℝ) ^ (D - 1) < M * (M : ℝ) ^ (D - 1) :=
          mul_lt_mul_of_pos_right hηMlt (pow_pos (by exact_mod_cast hM0) _)
      _ = (M : ℝ) ^ D := by rw [← pow_succ', Nat.sub_add_cancel hD]
  have hE : ∀ i, ‖(aT - P).coeff i‖ < (M : ℝ) ^ D := fun i ↦
    ((hmax i).trans (hest τ₀ hτ₀)).trans_lt hEM
  -- dominant data of `f'` and of `a`
  have hm1 : ‖(m : C)‖ = 1 := norm_natCast_eq_one p hp1 hpm
  have hDf : DomP f.derivative M (m - 1) := by
    refine ⟨fun i ↦ norm_nonneg _, ?_, fun i ↦ ?_, fun i hi ↦ ?_⟩
    · rw [coeff_derivative, Nat.sub_add_cancel hm0, norm_mul, hfm]
      rw [show ((m - 1 : ℕ) : C) + 1 = (m : C) by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]; push_cast; ring, hm1, mul_one]
    · rw [coeff_derivative, norm_mul]
      refine mul_le_of_le_one_right (norm_nonneg _) ?_ |>.trans (hfM _ (by omega))
      exact_mod_cast IsUltrametricDist.norm_natCast_le_one C (i + 1)
    · rw [coeff_derivative, norm_mul]
      refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt (hflt _ (by omega) (by omega))
      exact_mod_cast IsUltrametricDist.norm_natCast_le_one C (i + 1)
  have hDP : DomP P ((M : ℝ) ^ D) (D * (m - 1)) := dom_pow hDf (by exact_mod_cast hM0) D
  have hDa : DomP aT ((M : ℝ) ^ D) (D * (m - 1)) := by
    have := dom_add_small hDP hE
    rwa [add_sub_cancel] at this
  have hk : 0 < D * (m - 1) := Nat.mul_pos (Nat.one_le_pow _ _ hpp) (by omega)
  obtain ⟨τ, hτ1, hroot⟩ := exists_root_of_dom hDa (pow_pos (by exact_mod_cast hM0) D) hk
  obtain ⟨x, hx, hx0⟩ := exists_valid_of_normAll_eq_zero p ζ (genE p f (rr J))
    (Polynomial.evalRingHom τ) hζ hpp N Q (by simpa using hroot)
  set h := cH (rr J) τ x
  have hlin : (taylor τ f - h ^ p).coeff 1 = 0 := by rw [← hQev]; exact hx0
  obtain ⟨hb, h0, hall, -⟩ :=
    conc_inv p f (rr J) hsched0 hsched hτ1.le hM1 hf0 hfM hη N (by omega) x hx
  have hprec := prec_inv p f hτ1.le hM1 hf0 hfM hη hdec R 0 (Nat.zero_le _) N (by omega) x hx
  have hbdM : (bd C p M R : ℝ) < M := by
    refine lt_of_pow_lt_pow_left₀ m M.2 (hbdR.trans_le ?_)
    calc A ^ (m - 1) * M ≤ (M : ℝ) ^ (m - 1) * M :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0.le hAMR.le _) M.2
      _ = (M : ℝ) ^ m := by rw [← pow_succ, Nat.sub_add_cancel hm0]
  have hpbd : ∀ i, 0 < i → i < m → p ∣ i → ‖(taylor τ f - h ^ p).coeff i‖ ≤ bd C p M R := by
    rintro i hi0 him ⟨j', rfl⟩
    have hj'1 : 1 ≤ j' := by
      rcases Nat.eq_zero_or_pos j' with rfl | h
      · simp at hi0
      · exact h
    have hj'J : j' ≤ J := (Nat.le_div_iff_mul_le hpp).2 (by rw [mul_comm]; omega)
    have := hprec j' hj'1 hj'J
    rw [precBd, if_neg (by omega)] at this
    exact_mod_cast this
  -- the trivial approximation at `τ`
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq (f.eval τ) hpp
  have hβ1 : ‖β‖₊ ≤ 1 := by
    have h1 : ‖β‖₊ ^ p ≤ 1 := by
      rw [← nnnorm_pow, hβ, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
      exact norm_eval_le_one f hτ1.le (by exact_mod_cast hM1) hf0 hfM
    exact (pow_le_one_iff_of_nonneg zero_le hp.out.ne_zero).1 h1
  have hD0 := dom_taylor (p := p) (by exact_mod_cast hM0) hfM hfm hflt (by omega) hτ1 hβ
  -- comparison through power series (K2 at the radius `1`)
  have hterm : ∀ (q : C[X]) (i : ℕ), CriticalRadius.term
      ((taylor τ f : PowerSeries C) - (q : PowerSeries C) ^ p) 1 i =
        ‖(taylor τ f - q ^ p).coeff i‖ := fun q i ↦ by
    rw [CriticalRadius.term, norm_one, one_pow, mul_one, ← Polynomial.coe_pow,
      ← Polynomial.coe_sub, Polynomial.coeff_coe]
  have hBnd0 : PTaylor.Bnd ((Polynomial.C β : C[X]) : PowerSeries C) 1 := fun i ↦ by
    rw [Polynomial.coeff_coe, coeff_C]; split_ifs <;> simp [hβ1]
  have hBnd : PTaylor.Bnd (h : PowerSeries C) 1 := fun i ↦ by
    rw [Polynomial.coeff_coe]; exact hb i
  have hpM : ∀ M' : ℝ, A < M' → ‖(p : C)‖ ^ p < M' ^ (p - 1) := fun M' hM' ↦ by
    have h1 : ‖(p : C)‖ ^ p = A ^ (p - 1) := by
      rw [← coe_nnnorm, nnnorm_p_eq p hγ]
      push_cast
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [h1]
    exact pow_lt_pow_left₀ hM' hA0.le (Nat.sub_ne_zero_of_lt hp.out.one_lt)
  have hnb := CriticalRadius.not_better_at p (f := (taylor τ f : PowerSeries C))
    hBnd0 hBnd (l := 1) (by simp) (hpM M hAMR) hpm
    (fun i ↦ by rw [hterm]; exact hD0.le i) (by rw [hterm]; exact hD0.eq)
  have hallR : ∀ i, ‖(taylor τ f - h ^ p).coeff i‖ ≤ M := fun i ↦ by exact_mod_cast hall i
  have hgm : ‖(taylor τ f - h ^ p).coeff m‖ = M := by
    refine le_antisymm (hallR m) (not_lt.1 fun hlt ↦ hnb ⟨fun i ↦ ?_, ?_⟩)
    · rw [hterm]; exact hallR i
    · rw [hterm]; exact hlt
  refine ⟨τ, hτ1, h, hb, h0, hlin, ⟨fun i ↦ norm_nonneg _, hgm, hallR, fun i hi ↦ ?_⟩,
    fun i hi0 him hpi ↦ ?_⟩
  · refine lt_of_le_of_ne (hallR i) fun heq ↦ ?_
    by_cases hpi : p ∣ i
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [h0, norm_zero] at heq
        exact (ne_of_lt (by exact_mod_cast hM0)) heq
      · exact absurd ((hpbd i hi0 hi hpi).trans_lt hbdM) (by rw [heq]; exact lt_irrefl _)
    · have hnb2 := CriticalRadius.not_better_at p (f := (taylor τ f : PowerSeries C))
        hBnd hBnd0 (l := 1) (by simp) (hpM M hAMR) hpi
        (fun j ↦ by rw [hterm]; exact hallR j) (by rw [hterm]; exact heq)
      exact hnb2 ⟨fun j ↦ by rw [hterm]; exact hD0.le j, by rw [hterm]; exact hD0.lt i hi⟩
  · calc ‖(taylor τ f - h ^ p).coeff i‖ ^ m ≤ (bd C p M R : ℝ) ^ m :=
          pow_le_pow_left₀ (norm_nonneg _) (hpbd i hi0 him hpi) _
      _ < A ^ (m - 1) * M := hbdR
      _ ≤ A ^ (m - i) * (M : ℝ) ^ i := by
        have h1 : A ^ (m - 1) = A ^ (m - i) * A ^ (i - 1) := by
          rw [← pow_add]; congr 1; omega
        have h2 : (M : ℝ) ^ i = (M : ℝ) ^ (i - 1) * M := by
          rw [← pow_succ]; congr 1; omega
        rw [h1, h2, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hA0.le _)
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA0.le hAMR.le _) M.2

end Main


end GoodCentre

end SemistableReduction
