/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.Node

/-!
# Coefficients on the node and torsion freeness along `u^e + v^e` (Blueprint §12.8, M2.3)

For any commutative ring `O` and `a : O`, the node `Node O a = O[u, v]/(uv − a)` is free over `O`
on the monomials `u^i` (`i ≥ 0`) and `v^j` (`j ≥ 1`); we index them by `ℤ` (`u^k ↦ k`,
`v^j ↦ −j`). Here:

* `Node.coeff a : Node O a →ₗ[O] (ℤ →₀ O)`, the coordinates in this basis (`coeff_monomial`,
  `coeff_injective`), with the multiplication rules `coeff_u_mul`, `coeff_v_mul`
  (`u · u^k = u^{k+1}` for `k ≥ 0`, `u · v^j = a v^{j−1}`, and symmetrically);
* `Node.eq_zero_of_pow_add_pow_mul_eq_zero`: **`u^e + v^e` is a nonzerodivisor on the node**,
  for every `0 < e`, over an arbitrary base `O` (no domain hypothesis: this is used at the
  levels `O/ϖ^{n+1}` of the formal glueing). Proof: the top (or bottom) coefficient survives.

Applied to the Kummer covering `A = Node O (π^e) → B = Node O π` (`u ↦ s^e`, `v ↦ t^e`), the image
of `u + v` in `B` is a nonzerodivisor on `B`, hence on `S ⊗_A B` for every flat `A`-algebra `S`
(`KummerEtale.injective_mul_tensor`): the Kummer algebra over a formal neighbourhood of the node
has no torsion along the node, as the formal glueing (`FormalGlueing.glued`) requires.
-/

universe w

namespace SemistableReduction

namespace Node

noncomputable section

variable {O : Type w} [CommRing O] (a : O)

/-- The value of the coefficient map on the monomial `X^m` of `O[u, v]`: `u^i v^j` with
`i = m 0`, `j = m 1` is `a^{min i j}` times the basis vector of index `i − j`. -/
def coeffMono (m : Fin 2 →₀ ℕ) : ℤ →₀ O :=
  a ^ min (m 0) (m 1) • Finsupp.single ((m 0 : ℤ) - m 1) 1

/-- The coefficient map on `O[u, v]`. -/
def coeffPoly : MvPolynomial (Fin 2) O →ₗ[O] (ℤ →₀ O) :=
  (MvPolynomial.basisMonomials (Fin 2) O).constr O (coeffMono a)

lemma coeffPoly_monomial (m : Fin 2 →₀ ℕ) (c : O) :
    coeffPoly a (MvPolynomial.monomial m c) = c • coeffMono a m := by
  have : MvPolynomial.monomial m c = c • MvPolynomial.basisMonomials (Fin 2) O m := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, coeffPoly, Module.Basis.constr_basis]

lemma coeffPoly_mul_rel (q : MvPolynomial (Fin 2) O) :
    coeffPoly a ((MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C a) * q) = 0 := by
  induction q using MvPolynomial.induction_on' with
  | monomial m c =>
    have h1 : MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.monomial m c =
        MvPolynomial.monomial (m + Finsupp.single 0 1 + Finsupp.single 1 1) c := by
      rw [MvPolynomial.X, MvPolynomial.X, MvPolynomial.monomial_mul, MvPolynomial.monomial_mul]
      congr 1
      · abel_nf
      · ring
    have h2 : MvPolynomial.C a * MvPolynomial.monomial m c = MvPolynomial.monomial m (a * c) := by
      rw [MvPolynomial.C_mul_monomial]
    have hm0 : (m + Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 0 = m 0 + 1 := by simp
    have hm1 : (m + Finsupp.single 0 1 + Finsupp.single 1 1 : Fin 2 →₀ ℕ) 1 = m 1 + 1 := by simp
    rw [sub_mul, h1, h2, map_sub, coeffPoly_monomial, coeffPoly_monomial, coeffMono, coeffMono,
      hm0, hm1]
    have hmin : min (m 0 + 1) (m 1 + 1) = min (m 0) (m 1) + 1 := by omega
    rw [hmin, show ((m 0 + 1 : ℕ) : ℤ) - ((m 1 + 1 : ℕ) : ℤ) = (m 0 : ℤ) - m 1 by push_cast; ring,
      pow_succ, smul_smul, smul_smul, sub_eq_zero]
    congr 1
    ring
  | add p q hp hq => rw [mul_add, map_add, hp, hq, add_zero]

lemma coeffPoly_eq_of_mk_eq {p q : MvPolynomial (Fin 2) O}
    (h : (Ideal.Quotient.mk (Ideal.span {MvPolynomial.X 0 * MvPolynomial.X 1 -
      MvPolynomial.C a}) p : Node O a) = Ideal.Quotient.mk _ q) :
    coeffPoly a p = coeffPoly a q := by
  rw [Ideal.Quotient.eq] at h
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp h
  rw [← sub_eq_zero, ← map_sub, ← hr, mul_comm]
  exact coeffPoly_mul_rel a r

/-- The coefficients of an element of the node, via any representative. -/
def coeffFun (x : Node O a) : ℤ →₀ O :=
  coeffPoly a (Classical.choose (Ideal.Quotient.mk_surjective x))

lemma coeffFun_mk (p : MvPolynomial (Fin 2) O) :
    coeffFun a (Ideal.Quotient.mk _ p) = coeffPoly a p :=
  coeffPoly_eq_of_mk_eq a (Classical.choose_spec (Ideal.Quotient.mk_surjective _))

/-- **The coefficient map** `Node O a →ₗ[O] (ℤ →₀ O)`. -/
def coeff : Node O a →ₗ[O] (ℤ →₀ O) where
  toFun := coeffFun a
  map_add' x y := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_add, coeffFun_mk, coeffFun_mk, coeffFun_mk, map_add]
  map_smul' r x := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have : r • (Ideal.Quotient.mk _ p : Node O a) = Ideal.Quotient.mk _ (r • p) :=
      (map_smul (Ideal.Quotient.mkₐ O _) r p).symm
    rw [this, coeffFun_mk, coeffFun_mk, map_smul, RingHom.id_apply]

lemma coeff_mk (p : MvPolynomial (Fin 2) O) :
    coeff a (Ideal.Quotient.mk _ p) = coeffPoly a p := coeffFun_mk a p

lemma coeff_u_pow (i : ℕ) : coeff a (u a ^ i) = Finsupp.single (i : ℤ) 1 := by
  rw [u, ← map_pow, coeff_mk, MvPolynomial.X_pow_eq_monomial, coeffPoly_monomial, one_smul,
    coeffMono]
  simp

lemma coeff_v_pow (j : ℕ) : coeff a (v a ^ j) = Finsupp.single (-(j : ℤ)) 1 := by
  rw [v, ← map_pow, coeff_mk, MvPolynomial.X_pow_eq_monomial, coeffPoly_monomial, one_smul,
    coeffMono]
  simp

lemma coeff_monomial_inl (i : ℕ) : coeff a (monomial a (.inl i)) = Finsupp.single (i : ℤ) 1 :=
  coeff_u_pow a i

lemma coeff_monomial_inr (j : ℕ) :
    coeff a (monomial a (.inr j)) = Finsupp.single (-((j : ℤ) + 1)) 1 := by
  rw [monomial, Sum.elim_inr, coeff_v_pow]
  push_cast
  rfl

/-- The index of a monomial. -/
def idx : ℕ ⊕ ℕ → ℤ := Sum.elim (fun i ↦ (i : ℤ)) (fun j ↦ -((j : ℤ) + 1))

lemma idx_injective : Function.Injective idx := by
  rintro (i | i) (j | j) h <;> simp only [idx, Sum.elim_inl, Sum.elim_inr] at h
  · rw [Nat.cast_inj.mp h]
  · omega
  · omega
  · have : i = j := by omega
    rw [this]

lemma coeff_monomial (s : ℕ ⊕ ℕ) : coeff a (monomial a s) = Finsupp.single (idx s) 1 := by
  rcases s with i | j
  · exact coeff_monomial_inl a i
  · exact coeff_monomial_inr a j

/-- **The coefficient map is injective** (the monomials form a basis of the node over `O`). -/
theorem coeff_injective : Function.Injective (coeff a) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  have hspan : x ∈ Submodule.span O (Set.range (monomial a)) := by
    rw [span_eq_top]; trivial
  obtain ⟨c, rfl⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hspan
  rw [LinearMap.mem_ker, Finsupp.sum, map_sum] at hx
  simp only [map_smul, coeff_monomial] at hx
  have hc : c = 0 := by
    ext s
    have := congrArg (fun g : ℤ →₀ O ↦ g (idx s)) hx
    simp only [Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finsupp.coe_zero,
      Pi.zero_apply] at this
    rw [Finset.sum_eq_single s] at this
    · simpa using this
    · intro t _ hts
      rw [if_neg]
      exact fun h ↦ hts (idx_injective h)
    · intro hs
      simp [Finsupp.notMem_support_iff.mp hs]
  simp [hc]

/-- Multiplication by `u` on coefficients. -/
theorem coeff_u_mul (x : Node O a) (k : ℤ) :
    coeff a (u a * x) k = (if 0 ≤ k - 1 then 1 else a) * coeff a x (k - 1) := by
  have hspan : x ∈ Submodule.span O (Set.range (monomial a)) := by
    rw [span_eq_top]; trivial
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rcases s with i | j
    · have : u a * monomial a (.inl i) = monomial a (.inl (i + 1)) := by
        simp [monomial, pow_succ, mul_comm]
      rw [this, coeff_monomial, coeff_monomial]
      simp only [idx, Sum.elim_inl, Finsupp.single_apply]
      push_cast
      split_ifs <;> first | (exfalso; omega) | ring
    · rcases j with _ | j
      · have : u a * monomial a (.inr 0) = a • monomial a (.inl 0) := by
          simp [monomial, Algebra.smul_def, ← u_mul_v]
        rw [this, map_smul, coeff_monomial, coeff_monomial]
        simp only [idx, Sum.elim_inl, Sum.elim_inr, Finsupp.smul_apply, Finsupp.single_apply,
          smul_eq_mul]
        push_cast
        split_ifs <;> first | (exfalso; omega) | ring
      · have : u a * monomial a (.inr (j + 1)) = a • monomial a (.inr j) := by
          simp only [monomial, Sum.elim_inr, Algebra.smul_def, ← u_mul_v]
          ring
        rw [this, map_smul, coeff_monomial, coeff_monomial]
        simp only [idx, Sum.elim_inr, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        push_cast
        split_ifs <;> first | (exfalso; omega) | ring
  | zero => simp
  | add y z _ _ hy hz => simp [mul_add, hy, hz, mul_add]
  | smul r y _ hy =>
    rw [mul_smul_comm, map_smul, Finsupp.smul_apply, hy, map_smul, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring

/-- Multiplication by `v` on coefficients. -/
theorem coeff_v_mul (x : Node O a) (k : ℤ) :
    coeff a (v a * x) k = (if k + 1 ≤ 0 then 1 else a) * coeff a x (k + 1) := by
  have hspan : x ∈ Submodule.span O (Set.range (monomial a)) := by
    rw [span_eq_top]; trivial
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    rcases s with i | j
    · rcases i with _ | i
      · have : v a * monomial a (.inl 0) = monomial a (.inr 0) := by simp [monomial]
        rw [this, coeff_monomial, coeff_monomial]
        simp only [idx, Sum.elim_inl, Sum.elim_inr, Finsupp.single_apply]
        push_cast
        split_ifs <;> first | (exfalso; omega) | ring
      · have : v a * monomial a (.inl (i + 1)) = a • monomial a (.inl i) := by
          simp only [monomial, Sum.elim_inl, Algebra.smul_def, ← u_mul_v]
          ring
        rw [this, map_smul, coeff_monomial, coeff_monomial]
        simp only [idx, Sum.elim_inl, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        push_cast
        split_ifs <;> first | (exfalso; omega) | ring
    · have : v a * monomial a (.inr j) = monomial a (.inr (j + 1)) := by
        simp [monomial, pow_succ, mul_comm]
      rw [this, coeff_monomial, coeff_monomial]
      simp only [idx, Sum.elim_inr, Finsupp.single_apply]
      push_cast
      split_ifs <;> first | (exfalso; omega) | ring
  | zero => simp
  | add y z _ _ hy hz => simp [mul_add, hy, hz, mul_add]
  | smul r y _ hy =>
    rw [mul_smul_comm, map_smul, Finsupp.smul_apply, hy, map_smul, Finsupp.smul_apply,
      smul_eq_mul, smul_eq_mul]
    ring

lemma coeff_u_pow_mul_top {x : Node O a} {K : ℤ} (hK : 0 ≤ K) (j : ℕ) :
    coeff a (u a ^ j * x) (K + j) = coeff a x K := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, coeff_u_mul,
      show K + ((j + 1 : ℕ) : ℤ) - 1 = K + j by push_cast; ring,
      ih, if_pos (by omega), one_mul]

lemma coeff_v_pow_mul_bot {x : Node O a} {K : ℤ} (hK : K ≤ 0) (j : ℕ) :
    coeff a (v a ^ j * x) (K - j) = coeff a x K := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc, coeff_v_mul,
      show K - ((j + 1 : ℕ) : ℤ) + 1 = K - j by push_cast; ring,
      ih, if_pos (by omega), one_mul]

lemma coeff_v_pow_mul_eq_zero {x : Node O a} {K : ℤ} (hK : ∀ k, K < k → coeff a x k = 0)
    (j : ℕ) (k : ℤ) (hk : K - j < k) : coeff a (v a ^ j * x) k = 0 := by
  induction j generalizing k with
  | zero => simpa using hK k (by simpa using hk)
  | succ j ih =>
    rw [pow_succ', mul_assoc, coeff_v_mul, ih (k + 1) (by push_cast at hk; omega), mul_zero]

lemma coeff_u_pow_mul_eq_zero {x : Node O a} {K : ℤ} (hK : ∀ k, k < K → coeff a x k = 0)
    (j : ℕ) (k : ℤ) (hk : k < K + j) : coeff a (u a ^ j * x) k = 0 := by
  induction j generalizing k with
  | zero => simpa using hK k (by simpa using hk)
  | succ j ih =>
    rw [pow_succ', mul_assoc, coeff_u_mul, ih (k - 1) (by push_cast at hk; omega), mul_zero]

/-- **`u^e + v^e` is a nonzerodivisor on the node** `O[u, v]/(uv − a)`, for any `O`, `a`,
`0 < e`. -/
theorem eq_zero_of_pow_add_pow_mul_eq_zero {e : ℕ} (he : 0 < e) {x : Node O a}
    (hx : (u a ^ e + v a ^ e) * x = 0) : x = 0 := by
  by_contra hne
  have hsupp : (coeff a x).support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty]
    exact fun h ↦ hne (coeff_injective a (by rw [h, map_zero]))
  have hc := fun k ↦ congrArg (fun g : ℤ →₀ O ↦ g k) (congrArg (coeff a) hx)
  simp only [add_mul, map_add, map_zero, Finsupp.coe_add, Pi.add_apply,
    Finsupp.coe_zero, Pi.zero_apply] at hc
  set K := (coeff a x).support.max' hsupp
  have hKmem : coeff a x K ≠ 0 := Finsupp.mem_support_iff.mp (Finset.max'_mem _ _)
  by_cases hK : 0 ≤ K
  · have hab : ∀ k, K < k → coeff a x k = 0 := fun k hk ↦ by
      by_contra h
      exact absurd (Finset.le_max' _ k (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hk)
    have h := hc (K + e)
    rw [coeff_u_pow_mul_top a hK, coeff_v_pow_mul_eq_zero a hab e _ (by omega), add_zero] at h
    exact hKmem h
  · set k₀ := (coeff a x).support.min' hsupp
    have hk₀mem : coeff a x k₀ ≠ 0 := Finsupp.mem_support_iff.mp (Finset.min'_mem _ _)
    have hk₀ : k₀ ≤ 0 := by
      have := Finset.min'_le_max' _ hsupp
      omega
    have hbe : ∀ k, k < k₀ → coeff a x k = 0 := fun k hk ↦ by
      by_contra h
      exact absurd (Finset.min'_le _ k (Finsupp.mem_support_iff.mpr h)) (not_le.mpr hk)
    have h := hc (k₀ - e)
    rw [coeff_v_pow_mul_bot a hk₀, coeff_u_pow_mul_eq_zero a hbe e _ (by omega), zero_add] at h
    exact hk₀mem h

end

end Node

end SemistableReduction
