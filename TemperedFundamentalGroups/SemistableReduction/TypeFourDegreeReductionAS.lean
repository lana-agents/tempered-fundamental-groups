/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourDegreeReduction

/-!
# Degree reduction at a type-4 point: the Artin–Schreier case

Blueprint §9.12, leaf T4. This file proves `DegRed.DegreeReductionASFor`, the case
`μ = inf_H η(Q - H^p) = A` of `TypeFour.DegreeReductionFor`, and hence
**`DegRed.degreeReductionFor`**. It follows Temkin (*Stable modification of relative curves*,
Prop. 6.3.3 and Lemma 6.3.6 for `a = 1`). The geometric point `z̄` of Temkin's proof is replaced
by deep centres `α ∈ C`. At such a centre the Gauss valuation of the disc `D(α, η(z - α))` agrees
with `η` on any given finite set of polynomials.

* `AdmS η p Q γ b`: the Artin–Schreier coset, normalized multiplicatively by
  `Q ≡ H^p (1 + γ^p b)`, where `γ^(p-1) = -p`. Its moves are `admS_add` (small elements) and
  `admS_sub_AS` (`t^p - t`). `not_admS_C` says a constant is never in the coset.
  `exists_AS_move_lt` is criticality: `μ = A` is approached, using `exists_inv_approx`, the
  density of polynomials. `exists_admS_init` gives a first coset element.
* **`nnnorm_ell_mul_le`** (the first half of `dirtylem`): at a Gauss point, if
  `β - (t^p - t)` has value `< λ`, then the Artin–Schreier linear coefficient
  `ℓ = β̄₁ + Σ_k β̄_{p^k}^{1/p^k}` satisfies `|ℓ| ρ ≤ λ`.
* **`exists_ell_eq`** (the second half): if `|β_m| r^m ≥ 1`, then `|ℓ| = L > 1/r` at all deep
  centres. The proof uses type4lem on `y = (α - z₀)^(1/p^N)` (Temkin's claim (*)) and
  `nnnorm_sum_sub_root_le` (a root of a sum equals the sum of the roots up to `|p|`).
* `dirty_AS`, `step_AS`, `exists_admS_natDegree_le_one`: the degree reduction.
* `final_AS`: the endgame disc, built from a coset element of degree one.
* **`degreeReductionASFor`**, **`degreeReductionFor`**.
-/

set_option linter.unusedSectionVars false

open Polynomial Filter Topology
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

namespace DegRed

open GaussLimit

section PowSum

variable {R : Type*} [CommRing R] (w : Valuation R ℝ≥0) {p : ℕ}

lemma val_natCast_le_one (n : ℕ) : w (n : R) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    push_cast
    exact (Valuation.map_add _ _ _).trans (max_le ih (by simp))

lemma val_choose_le (hp : p.Prime) {k : ℕ} (hk0 : k ≠ 0) (hkp : k < p) :
    w (p.choose k : R) ≤ w (p : R) := by
  obtain ⟨m, hm⟩ := hp.dvd_choose_self hk0 hkp
  rw [hm, Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right zero_le (val_natCast_le_one w m)

/-- The homogeneous binomial estimate `w((x + y)^p - x^p - y^p) ≤ w(p) max(w x, w y)^p`. -/
lemma val_add_pow_sub_le' (hp : p.Prime) (x y : R) :
    w ((x + y) ^ p - x ^ p - y ^ p) ≤ w (p : R) * max (w x) (w y) ^ p := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero,
    Nat.choose_zero_right, one_mul, Nat.sub_zero]
  rw [show ∀ a b c : R, a + c + b - b - c = a by intros; ring]
  refine Valuation.map_sum_le _ fun k hk ↦ ?_
  have hk : k < n + 1 := Finset.mem_range.1 hk
  rw [map_mul, map_mul, map_pow, map_pow]
  calc w x ^ (k + 1) * w y ^ (n + 2 - (k + 1)) * w ((n + 2).choose (k + 1) : R)
      ≤ max (w x) (w y) ^ (k + 1) * max (w x) (w y) ^ (n + 2 - (k + 1)) * w ((n + 2 : ℕ) : R) := by
        gcongr
        · exact le_max_left _ _
        · exact le_max_right _ _
        · exact val_choose_le w hp (by omega) (by omega)
    _ = w ((n + 2 : ℕ) : R) * max (w x) (w y) ^ (n + 2) := by
        rw [← pow_add, Nat.add_sub_cancel' (by omega)]; ring

lemma val_sum_pow_sub_le (hp : p.Prime) {ι : Type*} (s : Finset ι) (f : ι → R) {M : ℝ≥0}
    (hM : ∀ i ∈ s, w (f i) ≤ M) :
    w ((∑ i ∈ s, f i) ^ p - ∑ i ∈ s, f i ^ p) ≤ w (p : R) * M ^ p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [zero_pow hp.ne_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hS : w (∑ i ∈ s, f i) ≤ M :=
      Valuation.map_sum_le _ fun i hi ↦ hM i (Finset.mem_insert_of_mem hi)
    rw [show (f a + ∑ i ∈ s, f i) ^ p - (f a ^ p + ∑ i ∈ s, f i ^ p) =
        ((f a + ∑ i ∈ s, f i) ^ p - f a ^ p - (∑ i ∈ s, f i) ^ p) +
          ((∑ i ∈ s, f i) ^ p - ∑ i ∈ s, f i ^ p) by ring]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ (ih fun i hi ↦ hM i
      (Finset.mem_insert_of_mem hi)))
    refine (val_add_pow_sub_le' w hp _ _).trans ?_
    gcongr
    exact max_le (hM a (Finset.mem_insert_self a s)) hS

lemma val_neg_pow_add_le (hp : p.Prime) (x : R) :
    w ((-x) ^ p + x ^ p) ≤ w (p : R) * w x ^ p := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [neg_sq, ← two_mul, map_mul, map_pow]; norm_num
  · rw [hodd.neg_pow, neg_add_cancel, map_zero]; exact zero_le

lemma val_sum_pow_pow_sub_le (hp : p.Prime) (hwp : w (p : R) ≤ 1) {ι : Type*} (s : Finset ι)
    (f : ι → R) {M : ℝ≥0} (hM : ∀ i ∈ s, w (f i) ≤ M) (k : ℕ) :
    w ((∑ i ∈ s, f i) ^ p ^ (k + 1) - ∑ i ∈ s, f i ^ p ^ (k + 1)) ≤
      w (p : R) * M ^ p ^ (k + 1) := by
  induction k with
  | zero => simpa using val_sum_pow_sub_le w hp s f hM
  | succ k ih =>
    set A₁ := ∑ i ∈ s, f i ^ p ^ (k + 1)
    set e := (∑ i ∈ s, f i) ^ p ^ (k + 1) - A₁
    have hA : w A₁ ≤ M ^ p ^ (k + 1) := Valuation.map_sum_le _ fun i hi ↦ by
      rw [map_pow]; exact pow_le_pow_left₀ zero_le (hM i hi) _
    have he : w e ≤ M ^ p ^ (k + 1) := ih.trans (mul_le_of_le_one_left zero_le hwp)
    have hsplit : (∑ i ∈ s, f i) ^ p ^ (k + 1 + 1) - ∑ i ∈ s, f i ^ p ^ (k + 1 + 1) =
        ((A₁ + e) ^ p - A₁ ^ p - e ^ p) + e ^ p + (A₁ ^ p - ∑ i ∈ s, (f i ^ p ^ (k + 1)) ^ p) := by
      simp only [e, ← pow_mul, ← pow_succ]
      ring
    rw [hsplit]
    have h1 : w ((A₁ + e) ^ p - A₁ ^ p - e ^ p) ≤ w (p : R) * M ^ p ^ (k + 1 + 1) := by
      refine (val_add_pow_sub_le' w hp _ _).trans ?_
      rw [pow_succ p (k + 1), pow_mul]
      gcongr
      exact max_le hA he
    have h2 : w (e ^ p) ≤ w (p : R) * M ^ p ^ (k + 1 + 1) := by
      rw [map_pow, pow_succ p (k + 1), pow_mul]
      calc w e ^ p ≤ (w (p : R) * M ^ p ^ (k + 1)) ^ p := pow_le_pow_left₀ zero_le ih _
        _ = w (p : R) ^ p * (M ^ p ^ (k + 1)) ^ p := mul_pow _ _ _
        _ ≤ w (p : R) * (M ^ p ^ (k + 1)) ^ p := by
          gcongr
          exact pow_le_of_le_one zero_le hwp hp.ne_zero
    have h3 : w (A₁ ^ p - ∑ i ∈ s, (f i ^ p ^ (k + 1)) ^ p) ≤ w (p : R) * M ^ p ^ (k + 1 + 1) := by
      rw [pow_succ p (k + 1), pow_mul]
      exact val_sum_pow_sub_le w hp s _ fun i hi ↦ by
        rw [map_pow]; exact pow_le_pow_left₀ zero_le (hM i hi) _
    exact (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
      (max_le h1 h2)) h3)

lemma val_neg_pow_pow_add_le (hp : p.Prime) (x : R) (k : ℕ) :
    w ((-x) ^ p ^ (k + 1) + x ^ p ^ (k + 1)) ≤ w (p : R) * w x ^ p ^ (k + 1) := by
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [Even.neg_pow ((Nat.even_pow' (Nat.succ_ne_zero k)).2 even_two), ← two_mul, map_mul,
      map_pow]
    norm_num
  · rw [(hodd.pow).neg_pow, neg_add_cancel, map_zero]; exact zero_le

lemma val_one_add_pow_sub_le (hp : p.Prime) (x : R) {M : ℝ≥0}
    (hM : ∀ k, 2 ≤ k → k ≤ p - 1 → w x ^ k ≤ M) :
    w ((1 + x) ^ p - 1 - x ^ p - (p : R) * x) ≤ w (p : R) * M := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [add_comm (1 : R) x, add_pow, Finset.sum_range_succ, Finset.sum_range_succ',
    Finset.sum_range_succ']
  simp only [one_pow, mul_one, Nat.choose_self, Nat.cast_one, Nat.choose_zero_right,
    pow_zero, zero_add, Nat.choose_one_right, pow_one]
  rw [show ∀ a b : R, a + x * b + 1 + x ^ (n + 2) - 1 - x ^ (n + 2) - b * x = a by
    intros; ring]
  refine Valuation.map_sum_le _ fun k hk ↦ ?_
  have hk : k < n := Finset.mem_range.1 hk
  rw [map_mul, map_pow, mul_comm]
  gcongr
  · exact val_choose_le w hp (by omega) (by omega)
  · exact hM _ (by omega) (by omega)

end PowSum

section Roots

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] {p : ℕ}

/-- **Roots of sums are sums of roots** up to `|p|` (Temkin's Lemma 6.3.7(ii)): if
`ω^q = Σ yᵢ^q`, `q = p^(k+1)`, then `|Σ yᵢ - ω|^q ≤ |p| max |yᵢ|^q`. -/
theorem nnnorm_sum_sub_root_le (hp : p.Prime) (hp1 : ‖(p : C)‖₊ ≤ 1) {k : ℕ} {ι : Type*}
    (s : Finset ι) (y : ι → C) {ω : C} (hω : ω ^ p ^ (k + 1) = ∑ i ∈ s, y i ^ p ^ (k + 1))
    {M : ℝ≥0} (hM : ∀ i ∈ s, ‖y i‖₊ ≤ M) :
    ‖∑ i ∈ s, y i - ω‖₊ ^ p ^ (k + 1) ≤ ‖(p : C)‖₊ * M ^ p ^ (k + 1) := by
  classical
  set q := p ^ (k + 1) with hq
  have hq0 : 0 < q := pow_pos hp.pos _
  set nv := NormedField.valuation (K := C)
  have hnv : ∀ x : C, nv x = ‖x‖₊ := fun _ ↦ rfl
  set σ := ∑ i ∈ s, y i
  have he : ‖σ ^ q - ω ^ q‖₊ ≤ ‖(p : C)‖₊ * M ^ q := by
    rw [hω, ← hnv]
    have := val_sum_pow_pow_sub_le nv hp hp1 s y (fun i hi ↦ hM i hi) k
    simpa [hnv] using this
  have hωM : ‖ω‖₊ ≤ M := by
    have h1 : ‖ω‖₊ ^ q ≤ M ^ q := by
      rw [← nnnorm_pow, hω, ← hnv]
      exact Valuation.map_sum_le _ fun i hi ↦ by
        rw [map_pow, hnv]; exact pow_le_pow_left₀ zero_le (hM i hi) _
    exact (pow_le_pow_iff_left₀ zero_le zero_le hq0.ne').1 h1
  -- the roots of `X^q - ω^q`
  set F : C[X] := X ^ q - Polynomial.C (ω ^ q)
  have hFm : F.Monic := monic_X_pow_sub_C _ hq0.ne'
  have hFd : F.natDegree = q := natDegree_X_pow_sub_C
  have hcard : Multiset.card F.roots = q := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hFd]
  have hFprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hFm
    (by rw [hcard, hFd])
  have hne : F.roots.toFinset.Nonempty := by
    rw [Multiset.toFinset_nonempty, ← Multiset.card_pos, hcard]; exact hq0
  obtain ⟨ρ, hρ, hmin⟩ := Finset.exists_min_image _ (fun ρ ↦ ‖σ - ρ‖₊) hne
  have hρr : ρ ∈ F.roots := Multiset.mem_toFinset.1 hρ
  have hρq : ρ ^ q = ω ^ q := by
    have := (mem_roots hFm.ne_zero).1 hρr
    simpa [F, sub_eq_zero] using this
  have h1 : ‖σ - ρ‖₊ ^ q ≤ ‖σ ^ q - ω ^ q‖₊ := by
    have hev : σ ^ q - ω ^ q = (F.roots.map fun ρ' ↦ σ - ρ').prod := by
      conv_lhs => rw [show σ ^ q - ω ^ q = F.eval σ by simp [F]]
      rw [← hFprod, eval_multiset_prod, Multiset.map_map]
      simp
    rw [hev, ← hcard, ← Multiset.prod_replicate, ← Multiset.map_const']
    rw [show ‖(F.roots.map fun ρ' ↦ σ - ρ').prod‖₊ =
        (F.roots.map fun ρ' ↦ ‖σ - ρ'‖₊).prod by
      have := map_multiset_prod (nnnormHom : C →*₀ ℝ≥0) (F.roots.map fun ρ' ↦ σ - ρ')
      rw [Multiset.map_map] at this
      exact this]
    exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ zero_le) fun ρ' hρ' ↦
      hmin ρ' (Multiset.mem_toFinset.2 hρ')
  have hρω : ‖ρ‖₊ = ‖ω‖₊ := by
    have := congrArg nnnorm hρq
    rw [nnnorm_pow, nnnorm_pow] at this
    exact (pow_left_inj₀ zero_le zero_le hq0.ne').1 this
  have h2 : ‖ρ - ω‖₊ ^ q ≤ ‖(p : C)‖₊ * M ^ q := by
    have hsum := val_sum_pow_pow_sub_le nv hp hp1 Finset.univ ![ρ, -ω] (M := M)
      (fun i _ ↦ by fin_cases i <;> simp [hnv, hρω, hωM]) k
    have hneg := val_neg_pow_pow_add_le nv hp ω k
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
    rw [← sub_eq_add_neg, ← hq] at hsum
    rw [← hq] at hneg
    have : (ρ - ω) ^ q = ((ρ - ω) ^ q - (ρ ^ q + (-ω) ^ q)) + ((-ω) ^ q + ω ^ q) := by
      rw [hρq]; ring
    rw [← nnnorm_pow, this, ← hnv]
    refine (Valuation.map_add _ _ _).trans (max_le hsum (hneg.trans ?_))
    rw [hnv]; gcongr; exact hωM
  have h3 : ‖σ - ω‖₊ ≤ max ‖σ - ρ‖₊ ‖ρ - ω‖₊ := by
    rw [show σ - ω = (σ - ρ) + (ρ - ω) by ring]
    exact IsUltrametricDist.nnnorm_add_le_max _ _
  rcases le_total ‖σ - ρ‖₊ ‖ρ - ω‖₊ with h | h
  · rw [max_eq_right h] at h3
    exact (pow_le_pow_left₀ zero_le h3 _).trans h2
  · rw [max_eq_left h] at h3
    exact (pow_le_pow_left₀ zero_le h3 _).trans (h1.trans he)

end Roots

section ASCoset

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {η : Valuation (RatFunc C) ℝ≥0} {p : ℕ}

variable (η p) in
/-- The Artin–Schreier coset, normalized multiplicatively: `Q ≡ H^p (1 + γ^p b)` modulo elements
of value `< A`. -/
def AdmS (Q : C[X]) (γ : C) (b : C[X]) : Prop :=
  ∃ H : C[X], pv η (Q - H ^ p * (1 + Polynomial.C (γ ^ p) * b)) < kb C p

section Gamma

variable {γ : C} (hp : p.Prime) (hγ : γ ^ (p - 1) = -(p : C))

include hp hγ in
lemma nnnorm_gamma_pow_pred : ‖γ‖₊ ^ (p - 1) = ‖(p : C)‖₊ := by
  rw [← nnnorm_pow, hγ, nnnorm_neg]

include hp hγ in
lemma nnnorm_gamma_pow : ‖γ‖₊ ^ p = kb C p := by
  refine (pow_left_inj₀ zero_le zero_le (Nat.sub_ne_zero_of_lt hp.one_lt)).1 ?_
  rw [kb_pow_pred hp, ← pow_mul, mul_comm, pow_mul, nnnorm_gamma_pow_pred hp hγ]

include hp hγ in
lemma natCast_mul_gamma : (p : C) * γ = -γ ^ p := by
  rw [← neg_neg (p : C), ← hγ, neg_mul, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le]

include hp hγ in
lemma nnnorm_gamma_lt_one (hp1 : ‖(p : C)‖ < 1) : ‖γ‖₊ < 1 := by
  have h := nnnorm_gamma_pow_pred hp hγ
  have hp1' : ‖(p : C)‖₊ < 1 := by rwa [← NNReal.coe_lt_coe, coe_nnnorm]
  by_contra hge
  push Not at hge
  exact absurd (h ▸ one_le_pow₀ hge) (not_le.2 hp1')

include hp hγ in
lemma nnnorm_p_le_gamma (hp1 : ‖(p : C)‖ < 1) : ‖(p : C)‖₊ ≤ ‖γ‖₊ := by
  rw [← nnnorm_gamma_pow_pred hp hγ]
  exact pow_le_of_le_one zero_le (nnnorm_gamma_lt_one hp hγ hp1).le
    (Nat.sub_ne_zero_of_lt hp.one_lt)

include hp hγ in
lemma kb_le_gamma (hp1 : ‖(p : C)‖ < 1) : kb C p ≤ ‖γ‖₊ := by
  rw [← nnnorm_gamma_pow hp hγ]
  exact pow_le_of_le_one zero_le (nnnorm_gamma_lt_one hp hγ hp1).le hp.ne_zero

include hp hγ in
lemma kb_eq_p_mul_gamma : kb C p = ‖(p : C)‖₊ * ‖γ‖₊ := by
  rw [← nnnorm_gamma_pow hp hγ, ← nnnorm_gamma_pow_pred hp hγ, ← pow_succ,
    Nat.sub_add_cancel hp.one_lt.le]

end Gamma

variable (hη : Splitting.IsTypeFour η) (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {Q : C[X]}
  (hQ : pv η Q = 1) {γ : C} (hγ : γ ^ (p - 1) = -(p : C)) {E : ℝ≥0} (hE : 1 ≤ E)
  (hγE : ‖γ‖₊ * E ^ p < 1)

include hη in
lemma pv_one_add {y : C[X]} (hy : pv η y < 1) : pv η (1 + y) = 1 := by
  rw [Valuation.map_add_eq_of_lt_left _ (by rwa [map_one]), map_one]

include hp hγ hE hγE hp1 in
lemma kb_mul_E_lt_one : kb C p * E < 1 := by
  calc kb C p * E ≤ ‖γ‖₊ * E ^ p := by
        gcongr
        · exact kb_le_gamma hp hγ hp1
        · exact le_self_pow₀ hE hp.ne_zero
    _ < 1 := hγE

include hp hγ hE hγE hp1 in
lemma kb_mul_E_sq_lt_one : kb C p * E ^ 2 < 1 := by
  calc kb C p * E ^ 2 ≤ ‖γ‖₊ * E ^ p := by
        gcongr
        · exact kb_le_gamma hp hγ hp1
        · exact hp.two_le
    _ < 1 := hγE

include hη hp hγ in
lemma pv_C_gamma_pow_mul (b : C[X]) : pv η (Polynomial.C (γ ^ p) * b) = kb C p * pv η b := by
  rw [map_mul, pv_C hη, nnnorm_pow, nnnorm_gamma_pow hp hγ]

include hη hp hp1 hQ hγ hE hγE in
lemma pv_eq_one_of_admS {H b : C[X]}
    (hH : pv η (Q - H ^ p * (1 + Polynomial.C (γ ^ p) * b)) < kb C p) (hb : pv η b ≤ E) :
    pv η H = 1 := by
  have hAE := kb_mul_E_lt_one hp hp1 hγ hE hγE
  have hg : pv η (Polynomial.C (γ ^ p) * b) < 1 := by
    rw [pv_C_gamma_pow_mul hη hp hγ]
    exact lt_of_le_of_lt (by gcongr) hAE
  have h1 : pv η (H ^ p * (1 + Polynomial.C (γ ^ p) * b)) = pv η Q :=
    Valuation.map_eq_of_sub_lt _ (by
      rw [Valuation.map_sub_swap, hQ]
      exact hH.trans (kb_lt_one hp hp1))
  rw [map_mul, pv_one_add hη hg, mul_one, map_pow, hQ] at h1
  exact (pow_eq_one_iff_of_nonneg zero_le hp.ne_zero).1 h1

include hp hp1 hQ in
lemma kb_lt_pv_of_ns (hNS : ∀ H : RatFunc C, H ≠ 0 →
      kummerBound C p * (η H : ℝ) ^ p < η (algebraMap C[X] (RatFunc C) Q - H ^ p))
    {H : C[X]} (hH : pv η H = 1) : kb C p < pv η (Q - H ^ p) := by
  have hH0 : algebraMap C[X] (RatFunc C) H ≠ 0 := by
    intro h
    rw [IsFractionRing.to_map_eq_zero_iff] at h
    rw [h, map_zero] at hH
    exact zero_ne_one hH
  have := hNS _ hH0
  rw [← map_pow, ← map_sub, ← coe_kb] at this
  change (kb C p : ℝ) * (pv η H : ℝ) ^ p < pv η (Q - H ^ p) at this
  rw [hH, NNReal.coe_one, one_pow, mul_one] at this
  exact_mod_cast this

variable (hNS : ∀ H : RatFunc C, H ≠ 0 →
      kummerBound C p * (η H : ℝ) ^ p < η (algebraMap C[X] (RatFunc C) Q - H ^ p))

include hη hp hp1 hQ hγ hE hγE hNS in
/-- Coset elements have value `> 1` (the coset is not split). -/
lemma one_lt_of_admS {b : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E) : 1 < pv η b := by
  obtain ⟨H, hH⟩ := hb
  have hH1 := pv_eq_one_of_admS hη hp hp1 hQ hγ hE hγE hH hbE
  have hlt := kb_lt_pv_of_ns hp hp1 hQ hNS hH1
  by_contra hle
  push Not at hle
  have h2 : pv η (H ^ p * Polynomial.C (γ ^ p) * b) ≤ kb C p := by
    rw [mul_assoc, map_mul, map_pow, hH1, one_pow, one_mul, pv_C_gamma_pow_mul hη hp hγ]
    exact mul_le_of_le_one_right zero_le hle
  have : Q - H ^ p = (Q - H ^ p * (1 + Polynomial.C (γ ^ p) * b)) +
      H ^ p * Polynomial.C (γ ^ p) * b := by ring
  rw [this] at hlt
  exact absurd (lt_of_lt_of_le hlt ((Valuation.map_add _ _ _).trans (max_le hH.le h2)))
    (lt_irrefl _)

include hη hp hp1 hQ hγ hE hγE in
lemma admS_add {b d : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E) (hd : pv η d < 1) :
    AdmS η p Q γ (b + d) := by
  obtain ⟨H, hH⟩ := hb
  have hH1 := pv_eq_one_of_admS hη hp hp1 hQ hγ hE hγE hH hbE
  refine ⟨H, ?_⟩
  rw [show Q - H ^ p * (1 + Polynomial.C (γ ^ p) * (b + d)) =
      (Q - H ^ p * (1 + Polynomial.C (γ ^ p) * b)) - H ^ p * (Polynomial.C (γ ^ p) * d) by ring]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hH ?_)
  rw [map_mul, map_pow, hH1, one_pow, one_mul, pv_C_gamma_pow_mul hη hp hγ]
  exact mul_lt_of_lt_one_right (kb_pos hp) hd

include hη hp hp1 hQ hγ hE hγE in
lemma admS_sub {b d : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E) (hd : pv η d < 1) :
    AdmS η p Q γ (b - d) := by
  rw [sub_eq_add_neg]
  exact admS_add hη hp hp1 hQ hγ hE hγE hb hbE (by rwa [Valuation.map_neg])

include hp hE in
lemma le_E_of_pow_le {τ : ℝ≥0} (hτ : τ ^ p ≤ E) : τ ≤ E := by
  rcases le_total τ 1 with h | h
  · exact h.trans hE
  · exact (le_self_pow₀ h hp.ne_zero).trans hτ

include hp hγ in
lemma AS_error_eq (t : C[X]) :
    (1 + Polynomial.C γ * t) ^ p - 1 - Polynomial.C (γ ^ p) * (t ^ p - t) =
      (1 + Polynomial.C γ * t) ^ p - 1 - (Polynomial.C γ * t) ^ p -
        (p : C[X]) * (Polynomial.C γ * t) := by
  rw [show (p : C[X]) = Polynomial.C (p : C) by simp, ← mul_assoc, ← map_mul,
    natCast_mul_gamma hp hγ, mul_pow, ← map_pow, map_neg]
  ring

include hη hp hp1 hγ hE hγE in
/-- The Artin–Schreier error `S = (1 + γt)^p - 1 - γ^p (t^p - t)` is small. -/
lemma pv_AS_error_le {t : C[X]} (ht : pv η t ≤ E) :
    pv η ((1 + Polynomial.C γ * t) ^ p - 1 - Polynomial.C (γ ^ p) * (t ^ p - t)) ≤
      kb C p * (‖γ‖₊ * E ^ 2) := by
  have hγ1 := nnnorm_gamma_lt_one hp hγ hp1
  have hγE1 : ‖γ‖₊ * E ≤ 1 := by
    refine le_trans ?_ hγE.le
    gcongr
    exact le_self_pow₀ hE hp.ne_zero
  have hx : pv η (Polynomial.C γ * t) ≤ ‖γ‖₊ * E := by
    rw [map_mul, pv_C hη]; gcongr
  have heq : (1 + Polynomial.C γ * t) ^ p - 1 - Polynomial.C (γ ^ p) * (t ^ p - t) =
      (1 + Polynomial.C γ * t) ^ p - 1 - (Polynomial.C γ * t) ^ p -
        (p : C[X]) * (Polynomial.C γ * t) := by
    rw [show (p : C[X]) = Polynomial.C (p : C) by simp, ← mul_assoc, ← map_mul,
      natCast_mul_gamma hp hγ, mul_pow, ← map_pow, map_neg]
    ring
  rw [heq]
  refine (val_one_add_pow_sub_le (pv η) hp _ (M := (‖γ‖₊ * E) ^ 2) fun k hk _ ↦ ?_).trans ?_
  · exact (pow_le_pow_of_le_one zero_le (hx.trans hγE1) hk).trans
      (pow_le_pow_left₀ zero_le hx 2)
  · rw [show (p : C[X]) = Polynomial.C (p : C) by simp, pv_C hη, kb_eq_p_mul_gamma hp hγ]
    rw [mul_pow, sq ‖γ‖₊]
    calc ‖(p : C)‖₊ * (‖γ‖₊ * ‖γ‖₊ * E ^ 2) = ‖(p : C)‖₊ * ‖γ‖₊ * (‖γ‖₊ * E ^ 2) := by ring
      _ ≤ ‖(p : C)‖₊ * ‖γ‖₊ * (‖γ‖₊ * E ^ 2) := le_rfl

include hη hp hp1 hQ hγ hE hγE in
/-- **The Artin–Schreier move**: subtracting `t^p - t` stays in the coset. -/
lemma admS_sub_AS {b t : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E)
    (ht : pv η t ^ p ≤ E) : AdmS η p Q γ (b - (t ^ p - t)) := by
  obtain ⟨H, hH⟩ := hb
  have hH1 := pv_eq_one_of_admS hη hp hp1 hQ hγ hE hγE hH hbE
  have htE := le_E_of_pow_le hp hE ht
  have hAE := kb_mul_E_lt_one hp hp1 hγ hE hγE
  have hAE2 := kb_mul_E_sq_lt_one hp hp1 hγ hE hγE
  have hγE2 : ‖γ‖₊ * E ^ 2 < 1 :=
    lt_of_le_of_lt (by gcongr; exact hp.two_le) hγE
  set u := Polynomial.C (γ ^ p) * (t ^ p - t)
  set v := Polynomial.C (γ ^ p) * b
  set S := (1 + Polynomial.C γ * t) ^ p - 1 - u
  have hu : pv η u ≤ kb C p * E := by
    rw [pv_C_gamma_pow_mul hη hp hγ]
    gcongr
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ htE)
    rw [map_pow]; exact ht
  have hv : pv η v ≤ kb C p * E := by
    rw [pv_C_gamma_pow_mul hη hp hγ]; gcongr
  have hS := pv_AS_error_le hη hp hp1 hγ hE hγE htE
  refine ⟨H * (1 + Polynomial.C γ * t), ?_⟩
  have hid : Q - (H * (1 + Polynomial.C γ * t)) ^ p *
      (1 + Polynomial.C (γ ^ p) * (b - (t ^ p - t))) =
      (Q - H ^ p * (1 + v)) - H ^ p * (u * (v - u) + S * (1 + v - u)) := by
    simp only [S, u, v, mul_pow]; ring
  rw [hid]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hH ?_)
  rw [map_mul, map_pow, hH1, one_pow, one_mul]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
  · rw [map_mul]
    calc pv η u * pv η (v - u) ≤ (kb C p * E) * (kb C p * E) :=
          mul_le_mul' hu ((Valuation.map_sub _ _ _).trans (max_le hv hu))
      _ = kb C p * (kb C p * E ^ 2) := by ring
      _ < kb C p := mul_lt_of_lt_one_right (kb_pos hp) hAE2
  · rw [map_mul]
    have h1 : pv η (1 + v - u) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
        (max_le (by simp) (hv.trans hAE.le))) (hu.trans hAE.le))
    calc pv η S * pv η (1 + v - u) ≤ kb C p * (‖γ‖₊ * E ^ 2) * 1 := mul_le_mul' hS h1
      _ < kb C p := by rw [mul_one]; exact mul_lt_of_lt_one_right (kb_pos hp) hγE2

include hη hp hp1 hQ hγ hE hγE hNS in
/-- A constant is never in the coset. -/
lemma not_admS_C {κ : C} (hb : AdmS η p Q γ (Polynomial.C κ)) (hκ : ‖κ‖₊ ≤ E) : False := by
  have hdeg : (X ^ p - X - Polynomial.C κ).natDegree = p := by
    have h1 := hp.one_lt
    have h0 := hp.ne_zero
    compute_degree!
    all_goals (try simp [h1.ne, h0]); try omega
  obtain ⟨t₀, ht₀⟩ := IsAlgClosed.exists_root (X ^ p - X - Polynomial.C κ) (by
    intro h
    have := natDegree_eq_of_degree_eq_some h
    rw [hdeg] at this
    exact hp.ne_zero this)
  have ht₀' : t₀ ^ p - t₀ = κ := by
    have := ht₀; simp [IsRoot] at this; linear_combination this
  have hτ : ‖t₀‖₊ ^ p ≤ E := by
    rcases le_total ‖t₀‖₊ 1 with h | h
    · exact (pow_le_one₀ zero_le h).trans hE
    · rcases eq_or_lt_of_le h with h' | h'
      · rw [← h', one_pow]; exact hE
      · have : ‖t₀ ^ p - t₀‖₊ = ‖t₀‖₊ ^ p := by
          rw [sub_eq_add_neg, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm (by
            rw [nnnorm_neg, nnnorm_pow]; exact (lt_self_pow₀ h' hp.one_lt).ne'), nnnorm_neg,
            nnnorm_pow, max_eq_left (le_self_pow₀ h hp.ne_zero)]
        rw [← this, ht₀']; exact hκ
  have h := admS_sub_AS hη hp hp1 hQ hγ hE hγE hb (by rwa [pv_C hη])
    (t := Polynomial.C t₀) (by rwa [pv_C hη])
  rw [← map_pow, ← map_sub, ht₀', sub_self] at h
  have := one_lt_of_admS hη hp hp1 hQ hγ hE hγE hNS h (by simp)
  simp at this

include hη in
/-- Polynomials are dense: a polynomial of value one has polynomial approximate inverses. -/
lemma exists_inv_approx {U : C[X]} (hU : pv η U = 1) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ W : C[X], pv η (U * W - 1) < ε := by
  have hU0 : U ≠ 0 := by rintro rfl; simp at hU
  obtain ⟨d, hd, hdeep⟩ := exists_deep hη hU0
  obtain ⟨a, ha⟩ := exists_radius_lt hd
  have hIs := hdeep a ha (pv η) (pv_C hη) ha
  have hUa : ‖U.eval a‖₊ = 1 := by rw [eval_nnnorm_eq hη hIs, hU]
  have hUa0 : U.eval a ≠ 0 := nnnorm_ne_zero_iff.1 (by rw [hUa]; exact one_ne_zero)
  set u₀ := U.eval a with hu₀
  set n := Polynomial.C u₀⁻¹ * (U - Polynomial.C u₀)
  have hn : pv η n < 1 := by
    rw [map_mul, pv_C hη, nnnorm_inv, hUa, inv_one, one_mul]
    unfold IsU at hIs; rwa [hUa] at hIs
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hε hn
  clear_value u₀
  refine ⟨Polynomial.C u₀⁻¹ * ∑ k ∈ Finset.range K, (-n) ^ k, ?_⟩
  have hUn : U = Polynomial.C u₀ * (1 - (-n)) := by
    simp only [n, sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, ← map_mul,
      mul_inv_cancel₀ hUa0, map_one, one_mul]; ring
  have : U * (Polynomial.C u₀⁻¹ * ∑ k ∈ Finset.range K, (-n) ^ k) - 1 = -(-n) ^ K := by
    rw [hUn, show ∀ x y z : C[X], x * y * (z * ∑ k ∈ Finset.range K, (-n) ^ k) =
      (x * z) * ((∑ k ∈ Finset.range K, (-n) ^ k) * y) by intros; ring, ← map_mul,
      mul_inv_cancel₀ hUa0, map_one, one_mul, geom_sum_mul_neg]
    ring
  rw [this, Valuation.map_neg, map_pow, Valuation.map_neg]
  exact hK

variable (hAS : ∀ ε : ℝ, kummerBound C p < ε →
      ∃ H : C[X], (η (algebraMap C[X] (RatFunc C) (Q - H ^ p)) : ℝ) < ε)

include hAS in
lemma exists_pv_lt_of_AS {t : ℝ≥0} (ht : kb C p < t) : ∃ H : C[X], pv η (Q - H ^ p) < t := by
  obtain ⟨H, hH⟩ := hAS t (by rw [← coe_kb]; exact_mod_cast ht)
  exact ⟨H, by exact_mod_cast hH⟩

include hη hp hp1 hQ hγ hE hγE hAS in
/-- The coset contains an element of value at most `E`. -/
lemma exists_admS_init (hE1 : 1 < E) : ∃ b : C[X], AdmS η p Q γ b ∧ pv η b ≤ E := by
  have hA0 := kb_pos (C := C) hp
  have hAE := kb_mul_E_lt_one hp hp1 hγ hE hγE
  obtain ⟨H₀, hH₀⟩ := exists_pv_lt_of_AS hAS (t := kb C p * E)
    (lt_mul_of_one_lt_right hA0 hE1)
  have hH₀1 : pv η H₀ = 1 := pv_eq_one_of_lt hη hQ hp.ne_zero (hH₀.trans hAE)
  have hU : pv η (H₀ ^ p) = 1 := by rw [map_pow, hH₀1, one_pow]
  obtain ⟨W, hW⟩ := exists_inv_approx hη hU (ε := E⁻¹) (inv_pos.2 (zero_lt_one.trans hE1))
  have hW1 : pv η W = 1 := by
    have h : pv η (H₀ ^ p * W) = 1 := by
      rw [← map_one (pv η)]
      exact Valuation.map_eq_of_sub_lt _ (by
        rw [map_one]; exact hW.trans (inv_lt_one_of_one_lt₀ hE1))
    rwa [map_mul, hU, one_mul] at h
  have hγ0 : γ ≠ 0 := by
    intro h; rw [h, zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt)] at hγ
    exact hp.ne_zero (by exact_mod_cast neg_eq_zero.1 hγ.symm)
  refine ⟨Polynomial.C (γ ^ p)⁻¹ * (Q - H₀ ^ p) * W, ⟨H₀, ?_⟩, ?_⟩
  · have : Q - H₀ ^ p * (1 + Polynomial.C (γ ^ p) * (Polynomial.C (γ ^ p)⁻¹ * (Q - H₀ ^ p) * W)) =
        -((Q - H₀ ^ p) * (H₀ ^ p * W - 1)) := by
      rw [← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hγ0), map_one,
        one_mul]
      ring
    rw [this, Valuation.map_neg, map_mul]
    calc pv η (Q - H₀ ^ p) * pv η (H₀ ^ p * W - 1) < kb C p * E * E⁻¹ :=
          mul_lt_mul'' hH₀ hW zero_le zero_le
      _ = kb C p := by rw [mul_assoc, mul_inv_cancel₀ (zero_lt_one.trans hE1).ne', mul_one]
  · rw [map_mul, map_mul, hW1, mul_one, pv_C hη, nnnorm_inv, nnnorm_pow,
      nnnorm_gamma_pow hp hγ]
    rw [inv_mul_le_iff₀ hA0]
    exact hH₀.le

include hη hp hp1 hQ hγ hE hγE hAS in
/-- **Criticality** (`μ = A` is not attained but approached): every coset element is, up to an
Artin–Schreier move `t^p - t` with `|t|^p ≤ E`, of value `< λ'` for any `1 < λ' ≤ E`. -/
lemma exists_AS_move_lt {b : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E) {lam : ℝ≥0}
    (hlam : 1 < lam) (hlamE : lam ≤ E) :
    ∃ t : C[X], pv η t ^ p ≤ E ∧ pv η (b - (t ^ p - t)) < lam := by
  obtain ⟨H, hH⟩ := hb
  have hH1 := pv_eq_one_of_admS hη hp hp1 hQ hγ hE hγE hH hbE
  have hA0 := kb_pos (C := C) hp
  have hAE := kb_mul_E_lt_one hp hp1 hγ hE hγE
  have hγ1 := nnnorm_gamma_lt_one hp hγ hp1
  have hγ0 : γ ≠ 0 := by
    intro h; rw [h, zero_pow (Nat.sub_ne_zero_of_lt hp.one_lt)] at hγ
    exact hp.ne_zero (by exact_mod_cast neg_eq_zero.1 hγ.symm)
  have hγpos : 0 < ‖γ‖₊ := nnnorm_pos.2 hγ0
  obtain ⟨H₁, hH₁⟩ := exists_pv_lt_of_AS hAS (t := kb C p * lam)
    (lt_mul_of_one_lt_right hA0 hlam)
  have hAlam : kb C p * lam < 1 := lt_of_le_of_lt (by gcongr) hAE
  have hH₁1 : pv η H₁ = 1 := pv_eq_one_of_lt hη hQ hp.ne_zero (hH₁.trans hAlam)
  obtain ⟨W, hW⟩ := exists_inv_approx hη hH1 hA0
  have hW1 : pv η W = 1 := by
    have h : pv η (H * W) = 1 := by
      rw [← map_one (pv η)]
      exact Valuation.map_eq_of_sub_lt _ (by rw [map_one]; exact hW.trans (kb_lt_one hp hp1))
    rwa [map_mul, hH1, one_mul] at h
  set V := H₁ * W
  set t := Polynomial.C γ⁻¹ * (V - 1)
  have htV : 1 + Polynomial.C γ * t = V := by
    simp only [t, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hγ0, map_one, one_mul]; ring
  have hV1 : pv η V = 1 := by rw [map_mul, hH₁1, hW1, one_mul]
  -- `H V` approximates `H₁`
  have hdiff : pv η (H₁ ^ p - (H * V) ^ p) < kb C p := by
    rw [← (Commute.all _ _).geom_sum₂_mul, map_mul]
    have hsum : pv η (∑ i ∈ Finset.range p, H₁ ^ i * (H * V) ^ (p - 1 - i)) ≤ 1 :=
      Valuation.map_sum_le _ fun i _ ↦ by
        rw [map_mul, map_pow, map_pow, map_mul, hH₁1, hH1, hV1]; simp
    have hHV : pv η (H₁ - H * V) < kb C p := by
      rw [show H₁ - H * V = -(H₁ * (H * W - 1)) by simp only [V]; ring, Valuation.map_neg,
        map_mul, hH₁1, one_mul]
      exact hW
    calc pv η (∑ i ∈ Finset.range p, H₁ ^ i * (H * V) ^ (p - 1 - i)) * pv η (H₁ - H * V)
        ≤ 1 * pv η (H₁ - H * V) := by gcongr
      _ < kb C p := by rw [one_mul]; exact hHV
  -- the key estimate `η(V^p - 1 - γ^p b) < A λ`
  have hkey : pv η (V ^ p - 1 - Polynomial.C (γ ^ p) * b) < kb C p * lam := by
    have hid : H ^ p * (V ^ p - 1 - Polynomial.C (γ ^ p) * b) =
        (Q - H ^ p * (1 + Polynomial.C (γ ^ p) * b)) - (Q - H₁ ^ p) - (H₁ ^ p - (H * V) ^ p) := by
      ring
    have h := congrArg (pv η) hid
    rw [map_mul, map_pow, hH1, one_pow, one_mul] at h
    rw [h]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt (lt_of_le_of_lt
      (Valuation.map_sub _ _ _) (max_lt (hH.trans (lt_mul_of_one_lt_right hA0 hlam)) hH₁))
      (hdiff.trans (lt_mul_of_one_lt_right hA0 hlam)))
  set S := (1 + Polynomial.C γ * t) ^ p - 1 - Polynomial.C (γ ^ p) * (t ^ p - t)
  have hSeq : V ^ p - 1 - Polynomial.C (γ ^ p) * b =
      Polynomial.C (γ ^ p) * (t ^ p - t - b) + S := by
    simp only [S, htV]; ring
  -- the size of `t`
  have ht : pv η t ^ p ≤ E := by
    by_contra hgt
    push Not at hgt
    set τ := pv η t
    have hτ1 : 1 < τ := by
      by_contra h; push Not at h
      exact absurd ((pow_le_one₀ zero_le h).trans hE) (not_le.2 hgt)
    have hτp : τ < τ ^ p := lt_self_pow₀ hτ1 hp.one_lt
    have htp : pv η (t ^ p - t) = τ ^ p := by
      rw [Valuation.map_sub_eq_of_lt_left _ (by rw [map_pow]; exact hτp), map_pow]
    have hbt : pv η (t ^ p - t - b) = τ ^ p := by
      rw [Valuation.map_sub_eq_of_lt_left _ (by rw [htp]; exact hbE.trans_lt hgt), htp]
    have hpos : 0 < ‖(p : C)‖₊ := nnnorm_pos.2 (by exact_mod_cast hp.ne_zero)
    have hS : pv η S < kb C p * τ ^ p := by
      rw [show S = _ from AS_error_eq hp hγ t]
      refine lt_of_le_of_lt (val_one_add_pow_sub_le (pv η) hp _
        (M := ‖γ‖₊ ^ 2 * τ ^ (p - 1)) fun k hk hkp ↦ ?_) ?_
      · rw [map_mul, pv_C hη, mul_pow]
        exact mul_le_mul' (pow_le_pow_of_le_one zero_le hγ1.le hk)
          (pow_le_pow_right₀ hτ1.le hkp)
      · rw [show (p : C[X]) = Polynomial.C (p : C) by simp, pv_C hη, kb_eq_p_mul_gamma hp hγ,
          mul_assoc]
        refine mul_lt_mul_of_pos_left ?_ hpos
        rw [sq, mul_assoc]
        refine mul_lt_mul_of_pos_left ?_ hγpos
        calc ‖γ‖₊ * τ ^ (p - 1) < 1 * τ ^ (p - 1) :=
              mul_lt_mul_of_pos_right hγ1 (pow_pos (zero_lt_one.trans hτ1) _)
          _ = τ ^ (p - 1) := one_mul _
          _ ≤ τ ^ p := pow_le_pow_right₀ hτ1.le (Nat.sub_le p 1)
    have hval : pv η (V ^ p - 1 - Polynomial.C (γ ^ p) * b) = kb C p * τ ^ p := by
      rw [hSeq, Valuation.map_add_eq_of_lt_left _ (by
        rw [pv_C_gamma_pow_mul hη hp hγ, hbt]; exact hS), pv_C_gamma_pow_mul hη hp hγ, hbt]
    have : kb C p * lam < kb C p * τ ^ p :=
      mul_lt_mul_of_pos_left (hlamE.trans_lt hgt) hA0
    exact absurd (hval ▸ hkey) (not_lt.2 this.le)
  refine ⟨t, ht, ?_⟩
  have htE := le_E_of_pow_le hp hE ht
  have hS := pv_AS_error_le hη hp hp1 hγ hE hγE htE
  have hγE2 : ‖γ‖₊ * E ^ 2 < 1 :=
    lt_of_le_of_lt (by gcongr; exact hp.two_le) hγE
  have hSA : pv η S < kb C p * lam :=
    lt_of_le_of_lt hS (lt_of_lt_of_le (mul_lt_of_lt_one_right hA0 hγE2)
      (le_mul_of_one_le_right zero_le hlam.le))
  have h2 : pv η (Polynomial.C (γ ^ p) * (t ^ p - t - b)) < kb C p * lam := by
    rw [show Polynomial.C (γ ^ p) * (t ^ p - t - b) =
      (V ^ p - 1 - Polynomial.C (γ ^ p) * b) - S by rw [hSeq]; ring]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hkey hSA)
  rw [pv_C_gamma_pow_mul hη hp hγ] at h2
  rw [show b - (t ^ p - t) = -(t ^ p - t - b) by ring, Valuation.map_neg]
  exact lt_of_mul_lt_mul_left h2 zero_le

end ASCoset

section Claim

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] {p : ℕ}

omit [IsUltrametricDist C] in
lemma taylor_C_mul_pow (α x : C) (n : ℕ) :
    taylor α (Polynomial.C x * (X - Polynomial.C α) ^ n) = Polynomial.C x * X ^ n := by
  rw [taylor_mul, taylor_C, taylor_pow, map_sub, taylor_X, taylor_C, add_sub_cancel_right]

omit [IsUltrametricDist C] in
lemma eq_sum_taylor (f : C[X]) (α : C) :
    f = ∑ i ∈ Finset.range (f.natDegree + 1),
      Polynomial.C ((taylor α f).coeff i) * (X - Polynomial.C α) ^ i := by
  conv_lhs => rw [← sum_taylor_eq f α]
  rw [sum_over_range' _ (fun _ ↦ by simp) _ (by rw [natDegree_taylor]; exact lt_add_one _)]

lemma pow_pow_le_of_le {E x : ℝ≥0} (hE : 1 ≤ E) {v i : ℕ} (hi : i ≤ v)
    (hx : x ^ p ^ v ≤ E) (hp : 0 < p) : x ^ p ^ i ≤ E := by
  rcases le_total x 1 with h | h
  · exact (pow_le_one₀ zero_le h).trans hE
  · exact (pow_le_pow_right₀ h (Nat.pow_le_pow_right hp hi)).trans hx

variable [IsAlgClosed C]

/-- The Gauss valuation at `(α, ρ)` with `g(C c) = |c|`. -/
lemma gw_algebraMap (α : C) (ρ : ℝ≥0ˣ) (c : C) : gw α ρ (algebraMap C C[X] c) = ‖c‖₊ := by
  rw [algebraMap_eq]; exact gw_C α ρ c

lemma gw_C_mul_pow (α : C) (ρ : ℝ≥0ˣ) (x : C) (n : ℕ) :
    gw α ρ (Polynomial.C x * (X - Polynomial.C α) ^ n) = ‖x‖₊ * (ρ : ℝ≥0) ^ n := by
  rw [map_mul, map_pow, gw_C, gw_X_sub_C]

lemma nnnorm_coeff_mul_le_gw (α : C) (ρ : ℝ≥0ˣ) (F : C[X]) (n : ℕ) :
    ‖(taylor α F).coeff n‖₊ * (ρ : ℝ≥0) ^ n ≤ gw α ρ F :=
  nnnorm_taylor_coeff_le α ρ F n

/-- **Temkin's invariant is bounded** (`dirtylem`, case `a = 1`, first half): if `β - (t^p - t)`
has Gauss value `< λ` at `(α, ρ)`, `λ > 1`, then the Artin–Schreier linear coefficient
`ℓ = β̄₁ + Σ_{e = p^k} β̄_e^{1/e}` satisfies `|ℓ| ρ ≤ λ`. -/
theorem nnnorm_ell_mul_le (hp : p.Prime) {α : C} {ρ : ℝ≥0ˣ} {β t : C[X]} {E lam : ℝ≥0}
    (hE : 1 ≤ E) (hpE : ‖(p : C)‖₊ * E ^ p < 1) (hβ : gw α ρ β ≤ E) (ht : gw α ρ t ≤ E)
    (hlam : 1 < lam) (hβt : gw α ρ (β - (t ^ p - t)) < lam) (ω : ℕ → C)
    (hω : ∀ e ∈ (Finset.Icc 1 β.natDegree).filter (p ∣ ·),
      ω e ^ p ^ (e.factorization p) = (taylor α β).coeff e) :
    ‖(taylor α β).coeff 1 + ∑ e ∈ (Finset.Icc 1 β.natDegree).filter (p ∣ ·),
        (if e / p ^ (e.factorization p) = 1 then ω e else 0)‖₊ * (ρ : ℝ≥0) ≤ lam := by
  classical
  set g := gw α ρ
  set S := (Finset.Icc 1 β.natDegree).filter (p ∣ ·)
  set v : ℕ → ℕ := fun e ↦ e.factorization p
  set j : ℕ → ℕ := fun e ↦ e / p ^ (e.factorization p)
  set w := X - Polynomial.C α
  have hjv : ∀ e, j e * p ^ v e = e := fun e ↦ by
    simp only [j, v]; rw [mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self e p
  have hjp : ∀ e ∈ S, ¬ p ∣ j e := fun e he ↦
    Nat.not_dvd_ordCompl hp (by have := (Finset.mem_Icc.1 (Finset.mem_filter.1 he).1).1; omega)
  set θ : ℕ → C[X] := fun e ↦ Polynomial.C (ω e) * w ^ j e
  have hθv : ∀ e ∈ S, θ e ^ p ^ v e = Polynomial.C ((taylor α β).coeff e) * w ^ e := by
    intro e he
    simp only [θ]
    rw [mul_pow, ← map_pow, hω e he, ← pow_mul, hjv]
  have hgθ : ∀ e ∈ S, ∀ i ≤ v e, g (θ e) ^ p ^ i ≤ E := by
    intro e he i hi
    refine pow_pow_le_of_le hE hi ?_ hp.pos
    rw [← map_pow, hθv e he, gw_C_mul_pow]
    exact (nnnorm_coeff_mul_le_gw α ρ β e).trans hβ
  set A : ℕ → C[X] := fun e ↦ ∑ i ∈ Finset.range (v e), θ e ^ p ^ i
  set c := ∑ e ∈ S, A e
  have hgA : ∀ e ∈ S, g (A e) ≤ E := fun e he ↦
    Valuation.map_sum_le _ fun i hi ↦ by
      rw [map_pow]; exact hgθ e he i (Finset.mem_range.1 hi).le
  have hgc : g c ≤ E := Valuation.map_sum_le _ hgA
  -- the error of `c^p`
  set err := c ^ p - ∑ e ∈ S, ∑ i ∈ Finset.range (v e), θ e ^ p ^ (i + 1)
  have hgp : g (p : C[X]) = ‖(p : C)‖₊ := by
    rw [show (p : C[X]) = Polynomial.C (p : C) by simp, gw_C]
  have hgerr : g err ≤ ‖(p : C)‖₊ * E ^ p := by
    have h1 := val_sum_pow_sub_le g hp S A hgA
    have h2 : ∀ e ∈ S, g (A e ^ p - ∑ i ∈ Finset.range (v e), θ e ^ p ^ (i + 1)) ≤
        ‖(p : C)‖₊ * E ^ p := fun e he ↦ by
      have := val_sum_pow_sub_le g hp (Finset.range (v e)) (fun i ↦ θ e ^ p ^ i) (M := E)
        fun i hi ↦ by rw [map_pow]; exact hgθ e he i (Finset.mem_range.1 hi).le
      rw [hgp] at this
      simp only [← pow_mul, ← pow_succ] at this
      exact this
    rw [hgp] at h1
    rw [show err = (c ^ p - ∑ e ∈ S, A e ^ p) +
        ∑ e ∈ S, (A e ^ p - ∑ i ∈ Finset.range (v e), θ e ^ p ^ (i + 1)) by
      simp only [err, c, Finset.sum_sub_distrib]; ring]
    exact (Valuation.map_add _ _ _).trans (max_le h1 (Valuation.map_sum_le _ h2))
  -- telescoping
  have htele : c ^ p - c = err + ∑ e ∈ S,
      (Polynomial.C ((taylor α β).coeff e) * w ^ e - θ e) := by
    have h : ∀ e ∈ S, ∑ i ∈ Finset.range (v e), θ e ^ p ^ (i + 1) - A e =
        Polynomial.C ((taylor α β).coeff e) * w ^ e - θ e := by
      intro e he
      simp only [A]
      rw [← Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ θ e ^ p ^ i), pow_zero,
        pow_one, hθv e he]
    rw [← Finset.sum_congr rfl h, Finset.sum_sub_distrib]
    simp only [err, c]
    ring
  set B := β - (c ^ p - c) with hBdef
  set ell := (taylor α β).coeff 1 + ∑ e ∈ S, (if j e = 1 then ω e else 0) with hell
  have hBc : ∀ i, (taylor α B).coeff i = (taylor α β).coeff i - (taylor α err).coeff i -
      ∑ e ∈ S, (if i = e then (taylor α β).coeff e else 0) +
      ∑ e ∈ S, (if i = j e then ω e else 0) := by
    intro i
    rw [hBdef, htele]
    simp only [map_sub, map_add, map_sum, coeff_sub, coeff_add, finsetSum_coeff, θ, w,
      taylor_C_mul_pow, coeff_C_mul_X_pow, Finset.sum_sub_distrib]
    ring
  have hBp : ∀ i, 1 ≤ i → p ∣ i → (taylor α B).coeff i = -(taylor α err).coeff i := by
    intro i hi hpi
    rw [hBc]
    have h1 : ∑ e ∈ S, (if i = j e then ω e else 0) = 0 :=
      Finset.sum_eq_zero fun e he ↦ by
        rw [if_neg]; rintro rfl; exact hjp e he hpi
    have h2 : (taylor α β).coeff i - ∑ e ∈ S, (if i = e then (taylor α β).coeff e else 0) = 0 := by
      rw [Finset.sum_ite_eq]
      split_ifs with hiS
      · ring
      · have : β.natDegree < i := by
          by_contra hle; push Not at hle
          exact hiS (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hi, hle⟩, hpi⟩)
        rw [coeff_eq_zero_of_natDegree_lt (by rwa [natDegree_taylor])]; ring
    rw [h1]
    linear_combination h2
  have hB1 : (taylor α B).coeff 1 = ell - (taylor α err).coeff 1 := by
    rw [hBc, hell]
    have h1 : ∑ e ∈ S, (if 1 = e then (taylor α β).coeff e else 0) = 0 :=
      Finset.sum_eq_zero fun e he ↦ by
        rw [if_neg]; rintro rfl; exact hp.one_lt.ne' (Nat.dvd_one.1 (Finset.mem_filter.1 he).2)
    rw [h1]
    simp only [eq_comm (a := 1)]
    ring
  have hpE1 : ‖(p : C)‖₊ * E ^ p < lam := hpE.trans hlam
  -- the move `c' = c - t`
  set c' := c - t with hc'def
  have hgc' : g c' ≤ E := (Valuation.map_sub _ _ _).trans (max_le hgc ht)
  set F := B + c' ^ p - c' with hFdef
  have hF : g F < lam := by
    have hX1 := val_add_pow_sub_le' g hp c (-t)
    have hX2 := val_neg_pow_add_le g hp t
    rw [hgp] at hX1 hX2
    have hid : F = (β - (t ^ p - t)) + ((c + -t) ^ p - c ^ p - (-t) ^ p) + ((-t) ^ p + t ^ p) := by
      simp only [hFdef, hBdef, hc'def]; ring
    rw [hid]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt
      (Valuation.map_add _ _ _) (max_lt hβt (lt_of_le_of_lt hX1 ?_))) (lt_of_le_of_lt hX2 ?_))
    · refine lt_of_le_of_lt ?_ hpE1
      gcongr
      exact max_le hgc (by rw [Valuation.map_neg]; exact ht)
    · refine lt_of_le_of_lt ?_ hpE1
      gcongr
  set K := c'.natDegree + 1
  set cc : ℕ → C := fun i ↦ (taylor α c').coeff i with hccdef
  have hc'eq : c' = ∑ i ∈ Finset.range K, Polynomial.C (cc i) * w ^ i := eq_sum_taylor c' α
  set c'' := ∑ i ∈ Finset.range K, (Polynomial.C (cc i) * w ^ i) ^ p with hc''def
  have hgc'' : g (c' ^ p - c'') ≤ ‖(p : C)‖₊ * E ^ p := by
    have := val_sum_pow_sub_le g hp (Finset.range K) (fun i ↦ Polynomial.C (cc i) * w ^ i)
      (M := E) fun i _ ↦ by
        rw [gw_C_mul_pow]; exact (nnnorm_coeff_mul_le_gw α ρ c' i).trans hgc'
    rw [hgp, ← hc'eq] at this
    exact this
  set F' := B + c'' - c' with hF'def
  have hF' : g F' < lam := by
    rw [show F' = F - (c' ^ p - c'') by simp only [hF'def, hFdef]; ring]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hF (hgc''.trans_lt hpE1))
  have hc''c : ∀ n, (taylor α c'').coeff n =
      ∑ i ∈ Finset.range K, (if n = i * p then cc i ^ p else 0) := by
    intro n
    simp only [hc''def, map_sum, finsetSum_coeff, mul_pow, ← map_pow, ← pow_mul, w,
      taylor_C_mul_pow, coeff_C_mul_X_pow]
  have hF'c : ∀ n, (taylor α F').coeff n =
      (taylor α B).coeff n + (taylor α c'').coeff n - cc n := by
    intro n; simp only [hF'def, map_sub, map_add, coeff_sub, coeff_add, hccdef]
  have hF'n : ∀ n, ‖(taylor α F').coeff n‖₊ * (ρ : ℝ≥0) ^ n < lam := fun n ↦
    (nnnorm_coeff_mul_le_gw α ρ F' n).trans_lt hF'
  have herrn : ∀ n, ‖(taylor α err).coeff n‖₊ * (ρ : ℝ≥0) ^ n < 1 := fun n ↦
    ((nnnorm_coeff_mul_le_gw α ρ err n).trans hgerr).trans_lt hpE
  -- the contradiction
  by_contra hcon
  push Not at hcon
  set L0 := ‖ell‖₊ * (ρ : ℝ≥0) with hL0
  have hL1 : 1 < L0 := hlam.trans hcon
  have hcc1 : L0 ≤ ‖cc 1‖₊ * (ρ : ℝ≥0) := by
    have h0 : (taylor α c'').coeff 1 = 0 := by
      rw [hc''c]
      refine Finset.sum_eq_zero fun i _ ↦ if_neg fun h ↦ ?_
      rcases i with _ | i
      · simp at h
      · have : p ≤ (i + 1) * p := Nat.le_mul_of_pos_left p (Nat.succ_pos i)
        have := hp.two_le
        omega
    have hid : ell = cc 1 + (taylor α err).coeff 1 + (taylor α F').coeff 1 := by
      rw [hF'c, h0, hB1]; ring
    have hle : ‖ell‖₊ ≤ max (max ‖cc 1‖₊ ‖(taylor α err).coeff 1‖₊) ‖(taylor α F').coeff 1‖₊ := by
      rw [hid]
      exact (IsUltrametricDist.nnnorm_add_le_max _ _).trans
        (max_le_max (IsUltrametricDist.nnnorm_add_le_max _ _) le_rfl)
    have := mul_le_mul_of_nonneg_right hle (zero_le (a := (ρ : ℝ≥0)))
    rw [max_mul_of_nonneg _ _ zero_le, max_mul_of_nonneg _ _ zero_le] at this
    have he1 := herrn 1
    have hf1 := hF'n 1
    rw [pow_one] at he1 hf1
    by_contra hlt
    push Not at hlt
    exact absurd this (not_le.2 (max_lt (max_lt hlt (he1.trans hL1)) (hf1.trans hcon)))
  set T := (Finset.range K).filter (fun i ↦ L0 ≤ ‖cc i‖₊ * (ρ : ℝ≥0) ^ i) with hTdef
  have hcc10 : cc 1 ≠ 0 := by
    intro h; rw [h, nnnorm_zero, zero_mul] at hcc1
    exact absurd (hL1.trans_le hcc1) (by simp)
  have h1K : 1 ∈ Finset.range K := by
    rw [Finset.mem_range]
    have := le_natDegree_of_ne_zero hcc10
    rw [natDegree_taylor] at this
    omega
  have h1T : 1 ∈ T := Finset.mem_filter.2 ⟨h1K, by rwa [pow_one]⟩
  set I := T.max' ⟨1, h1T⟩
  have hIT : I ∈ T := T.max'_mem _
  have hI1 : 1 ≤ I := T.le_max' 1 h1T
  have hIK : I ∈ Finset.range K := (Finset.mem_filter.1 hIT).1
  have hIL : L0 ≤ ‖cc I‖₊ * (ρ : ℝ≥0) ^ I := (Finset.mem_filter.1 hIT).2
  have hc''I : (taylor α c'').coeff (I * p) = cc I ^ p := by
    rw [hc''c, Finset.sum_eq_single I]
    · rw [if_pos rfl]
    · intro i _ hi
      rw [if_neg]
      intro h
      exact hi (Nat.eq_of_mul_eq_mul_right hp.pos h).symm
    · intro h; exact absurd hIK h
  have hccpI : ‖cc (I * p)‖₊ * (ρ : ℝ≥0) ^ (I * p) < L0 := by
    by_cases hmem : I * p ∈ Finset.range K
    · by_contra hge
      push Not at hge
      have hT : I * p ∈ T := Finset.mem_filter.2 ⟨hmem, hge⟩
      have := T.le_max' _ hT
      have : I < I * p := lt_mul_of_one_lt_right (by omega) hp.one_lt
      omega
    · have : cc (I * p) = 0 := by
        simp only [hccdef]
        refine coeff_eq_zero_of_natDegree_lt ?_
        rw [natDegree_taylor]
        rw [Finset.mem_range] at hmem
        omega
      rw [this, nnnorm_zero, zero_mul]
      exact zero_lt_one.trans hL1
  have hid : cc I ^ p = (taylor α F').coeff (I * p) + (-(taylor α err).coeff (I * p)) * (-1) +
      cc (I * p) := by
    have h1 : 1 ≤ I * p := Nat.mul_pos hI1 hp.pos
    rw [hF'c, hc''I, hBp (I * p) h1 (dvd_mul_left p I)]; ring
  have hle : ‖cc I ^ p‖₊ ≤ max (max ‖(taylor α F').coeff (I * p)‖₊
      ‖(taylor α err).coeff (I * p)‖₊) ‖cc (I * p)‖₊ := by
    rw [hid]
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le_max ?_ le_rfl)
    refine (IsUltrametricDist.nnnorm_add_le_max _ _).trans (max_le_max le_rfl ?_)
    simp
  have := mul_le_mul_of_nonneg_right hle (zero_le (a := (ρ : ℝ≥0) ^ (I * p)))
  rw [max_mul_of_nonneg _ _ zero_le, max_mul_of_nonneg _ _ zero_le] at this
  have hbig : L0 ^ p ≤ ‖cc I ^ p‖₊ * (ρ : ℝ≥0) ^ (I * p) := by
    rw [nnnorm_pow, pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ zero_le hIL p
  have hLp : L0 < L0 ^ p := lt_self_pow₀ hL1 hp.one_lt
  exact absurd (hbig.trans this) (not_le.2 (max_lt (max_lt ((hF'n _).trans (hcon.trans hLp))
    ((herrn _).trans (hL1.trans hLp))) (hccpI.trans hLp)))

end Claim

section StepC

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] {p : ℕ}

omit [IsUltrametricDist C] in
/-- Re-expansion of Taylor coefficients at a new centre. -/
lemma taylor_coeff_eq_sum (β : C[X]) (z₀ α : C) (i : ℕ) :
    (taylor α β).coeff i = ∑ j ∈ Finset.range (β.natDegree + 1),
      (j.choose i : C) * (taylor z₀ β).coeff j * (α - z₀) ^ (j - i) := by
  rw [show taylor α β = taylor (α - z₀) (taylor z₀ β) by rw [taylor_taylor, sub_add_cancel],
    taylor_coeff, hasseDeriv_apply, eval_sum,
    sum_over_range' _ (fun _ ↦ by simp) _ (by rw [natDegree_taylor]; exact lt_add_one _)]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [eval_monomial]

/-- `|(x - y)^(p^N) - (x^(p^N) - y^(p^N))| ≤ |p| max(|x|, |y|)^(p^N)`. -/
lemma nnnorm_sub_pow_sub_le (hp : p.Prime) (hp1 : ‖(p : C)‖₊ ≤ 1) (x y : C) (N : ℕ) :
    ‖(x - y) ^ p ^ N - (x ^ p ^ N - y ^ p ^ N)‖₊ ≤
      ‖(p : C)‖₊ * max ‖x‖₊ ‖y‖₊ ^ p ^ N := by
  rcases N with _ | k
  · simp
  set nv := NormedField.valuation (K := C)
  have hnv : ∀ z : C, nv z = ‖z‖₊ := fun _ ↦ rfl
  have hsum := val_sum_pow_pow_sub_le nv hp hp1 Finset.univ ![x, -y]
    (M := max ‖x‖₊ ‖y‖₊) (fun i _ ↦ by
      fin_cases i <;> simp [hnv]) k
  have hneg := val_neg_pow_pow_add_le nv hp y k
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hsum
  rw [show (x - y) ^ p ^ (k + 1) - (x ^ p ^ (k + 1) - y ^ p ^ (k + 1)) =
      ((x + -y) ^ p ^ (k + 1) - (x ^ p ^ (k + 1) + (-y) ^ p ^ (k + 1))) +
        ((-y) ^ p ^ (k + 1) + y ^ p ^ (k + 1)) by ring, ← hnv]
  refine (Valuation.map_add _ _ _).trans (max_le hsum (hneg.trans ?_))
  rw [hnv]; gcongr; exact le_max_right _ _

lemma max_pow_le {a b c : ℝ≥0} {q : ℕ} (ha : a ^ q ≤ c) (hb : b ^ q ≤ c) : max a b ^ q ≤ c := by
  rcases le_total a b with h | h
  · rwa [max_eq_right h]
  · rwa [max_eq_left h]

lemma natDeg_aux1 {p N m j : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m) (hj : j < m) :
    (j - 1) * p ^ N ≤ (m - 1) * p ^ N - 1 := by
  have hpN : 0 < p ^ N := pow_pos (by omega) N
  have : (j - 1) * p ^ N < (m - 1) * p ^ N := Nat.mul_lt_mul_of_pos_right (by omega) hpN
  omega

lemma natDeg_aux2 {p N m j k : ℕ} (hp : 2 ≤ p) (hm : 2 ≤ m) (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (hj1 : p ^ k ≤ j) (hjm : j ≤ m) :
    (j - p ^ k) * p ^ (N - k) ≤ (m - 1) * p ^ N - 1 := by
  have hpk : 1 ≤ p ^ k := Nat.one_le_pow _ _ (by omega)
  have h1 : (j - p ^ k) * p ^ (N - k) ≤ (m - 1) * p ^ (N - k) :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : p ^ (N - k) < p ^ N := Nat.pow_lt_pow_right (by omega) (by omega)
  have h3 : (m - 1) * p ^ (N - k) < (m - 1) * p ^ N := Nat.mul_lt_mul_of_pos_left h2 (by omega)
  omega

variable [IsAlgClosed C]

/-- **The lower bound on Temkin's invariant** (`dirtylem`, case `a = 1`, second half, Temkin's
claim (*) and Lemma 6.3.5 for `z^(1/p^N)`): if `|β_m| r^m ≥ 1`, `m ≥ 2`, `p ∤ m`, then at all deep
centres `α`, `|β̄₁ + Σ_{k=1}^N β̄_{p^k}^{1/p^k}| = L` for a constant `L > 1/r`. -/
theorem exists_ell_eq [CharZero C] {η : Valuation (RatFunc C) ℝ≥0}
    (hη : Splitting.IsTypeFour η) (hrad : 0 < rad η) (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    {β : C[X]} {E : ℝ≥0} (hpE : ‖(p : C)‖₊ * E < 1) (hβE : pv η β ≤ E)
    (hm : 2 ≤ β.natDegree) (hpm : ¬ p ∣ β.natDegree)
    (hbig : 1 ≤ ‖β.leadingCoeff‖₊ * rad η ^ β.natDegree) :
    ∃ L d : ℝ≥0, 1 < L * rad η ∧ rad η < d ∧ ∀ α : C, radius η α < d → ∀ ω : ℕ → C,
      (∀ k ∈ Finset.Icc 1 (Nat.log p β.natDegree), ω k ^ p ^ k = (taylor α β).coeff (p ^ k)) →
      ‖(taylor α β).coeff 1 + ∑ k ∈ Finset.Icc 1 (Nat.log p β.natDegree), ω k‖₊ = L := by
  classical
  set m := β.natDegree with hmdef
  set N := Nat.log p m with hNdef
  have hp2 := hp.two_le
  have hpN : p ^ N ≤ m := Nat.pow_log_le_self p (by omega)
  have hβ0 : β ≠ 0 := by rintro rfl; simp [m] at hm
  have hp1' : ‖(p : C)‖₊ < 1 := by rwa [← NNReal.coe_lt_coe, coe_nnnorm]
  have hppos : 0 < ‖(p : C)‖₊ := nnnorm_pos.2 (by exact_mod_cast hp.ne_zero)
  -- the origin `z₀`
  obtain ⟨dβ, hdβ, hdeepβ⟩ := exists_deep hη hβ0
  have hrp : rad η < rad η / ‖(p : C)‖₊ := by
    rw [lt_div_iff₀ hppos]; exact mul_lt_of_lt_one_right hrad hp1'
  obtain ⟨z₀, hz₀⟩ := exists_radius_lt (lt_min hdβ hrp)
  set Z₀ := radius η z₀ with hZ₀def
  have hZ₀r : rad η < Z₀ := rad_lt hη z₀
  have hZ₀0 : 0 < Z₀ := hrad.trans hZ₀r
  have hpZ : ‖(p : C)‖₊ * Z₀ < rad η := by
    have := hz₀.trans_le (min_le_right _ _)
    rwa [lt_div_iff₀ hppos, mul_comm] at this
  set b : ℕ → C := fun j ↦ (taylor z₀ β).coeff j with hbdef
  have hb : ∀ j, ‖b j‖₊ * Z₀ ^ j ≤ E := by
    intro j
    set ρ₀ : ℝ≥0ˣ := Units.mk0 Z₀ hZ₀0.ne'
    have hz₀d := hz₀.trans_le (min_le_left _ _)
    have hU := hdeepβ z₀ hz₀d (gw z₀ ρ₀) (gw_C z₀ ρ₀) (by rw [gw_X_sub_C]; exact hz₀d)
    have hgw : gw z₀ ρ₀ β = pv η β := by
      rw [val_eq_of_isU (gw_C z₀ ρ₀) hU, eval_nnnorm_eq hη (hdeepβ z₀ hz₀d _ (pv_C hη) hz₀d)]
    exact (nnnorm_taylor_coeff_le z₀ ρ₀ β j).trans (hgw.trans_le hβE)
  have hbm : b m = β.leadingCoeff := coeff_taylor_natDegree z₀ β
  -- the roots `c k j`
  choose cr hcr using fun k j ↦ IsAlgClosed.exists_pow_nat_eq ((j.choose (p ^ k) : C) * b j)
    (pow_pos hp.pos k)
  set D := (m - 1) * p ^ N with hDdef
  have hD1 : 1 ≤ D := Nat.mul_pos (by omega) (pow_pos hp.pos N)
  set Plow : C[X] := (∑ j ∈ Finset.range m, Polynomial.C ((j : C) * b j) * X ^ ((j - 1) * p ^ N)) +
    ∑ k ∈ Finset.Icc 1 N, ∑ j ∈ Finset.Icc (p ^ k) m,
      Polynomial.C (cr k j) * X ^ ((j - p ^ k) * p ^ (N - k)) with hPlowdef
  set a := (m : C) * b m with hadef
  have ha : a ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : m ≠ 0))
    (by rw [hbm]; exact leadingCoeff_ne_zero.2 hβ0)
  have hna : ‖a‖₊ = ‖β.leadingCoeff‖₊ := by
    rw [hadef, nnnorm_mul, nnnorm_natCast_eq_one hp hp1 hpm, one_mul, hbm]
  have hPlow : Plow.natDegree ≤ D - 1 := by
    refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
    · refine natDegree_sum_le_of_forall_le _ _ fun j hj ↦ (natDegree_C_mul_X_pow_le _ _).trans ?_
      exact natDeg_aux1 hp2 hm (Finset.mem_range.1 hj)
    · refine natDegree_sum_le_of_forall_le _ _ fun k hk ↦
        natDegree_sum_le_of_forall_le _ _ fun j hj ↦ (natDegree_C_mul_X_pow_le _ _).trans ?_
      obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
      obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
      exact natDeg_aux2 hp2 hm hk1 hkN hj1 hjm
  set P := Polynomial.C a * X ^ D + Plow with hPdef
  have hPdeg : P.natDegree = D := by
    rw [hPdef, natDegree_add_eq_left_of_natDegree_lt (by rw [natDegree_C_mul_X_pow _ _ ha]; omega),
      natDegree_C_mul_X_pow _ _ ha]
  have hPlc : P.leadingCoeff = a := by
    rw [leadingCoeff, hPdeg, hPdef, coeff_add, coeff_C_mul_X_pow, if_pos rfl,
      coeff_eq_zero_of_natDegree_lt (by omega), add_zero]
  have hP0 : P ≠ 0 := by intro h; rw [h, natDegree_zero] at hPdeg; omega
  -- the roots of `P` and the points `z₀ + yᵢ^(p^N)`
  set R := P.roots with hRdef
  have hRcard : Multiset.card R = D := by rw [IsAlgClosed.card_roots_eq_natDegree, hPdeg]
  have hPfac : P = Polynomial.C a * (R.map fun y ↦ X - Polynomial.C y).prod := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := P))]
    rw [hPlc]
  set π : C → C := fun y ↦ z₀ + y ^ p ^ N with hπdef
  set Sd : Finset ℝ≥0 := insert Z₀ (R.toFinset.image fun y ↦ radius η (π y))
  set d₁ := Sd.min' (Finset.insert_nonempty _ _)
  have hd₁ : rad η < d₁ := by
    rw [Finset.lt_min'_iff]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact hZ₀r
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hx
      exact rad_lt hη _
  have hd₁Z : d₁ ≤ Z₀ := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
  have hd₁π : ∀ y ∈ R, d₁ ≤ radius η (π y) := fun y hy ↦
    Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
      (Multiset.mem_toFinset.2 hy)))
  set Λ := ‖a‖₊ ^ p ^ N * (R.map fun y ↦ radius η (π y)).prod with hΛdef
  have hkey : ∀ α, radius η α < d₁ → ∀ y : C, y ^ p ^ N = α - z₀ →
      ‖P.eval y‖₊ ^ p ^ N = Λ := by
    intro α hα y hy
    have hαZ : radius η α < Z₀ := hα.trans_le hd₁Z
    have hyZ : ‖y‖₊ ^ p ^ N = Z₀ := by rw [← nnnorm_pow, hy, nnnorm_sub_eq_radius hη hαZ]
    have hfac : ∀ yi ∈ R, ‖y - yi‖₊ ^ p ^ N = radius η (π yi) := by
      intro yi hyi
      set Dπ := radius η (π yi)
      have hαπ : radius η α < Dπ := hα.trans_le (hd₁π yi hyi)
      have hDπ : rad η < Dπ := rad_lt hη _
      have hdist : ‖y ^ p ^ N - yi ^ p ^ N‖₊ = Dπ := by
        rw [show y ^ p ^ N - yi ^ p ^ N = α - π yi by simp only [hπdef]; rw [hy]; ring,
          nnnorm_sub_eq_radius hη hαπ]
      have he := nnnorm_sub_pow_sub_le hp hp1'.le y yi N
      have hlt : ‖(y - yi) ^ p ^ N - (y ^ p ^ N - yi ^ p ^ N)‖₊ < Dπ := by
        refine he.trans_lt ?_
        rcases le_or_gt (‖yi‖₊ ^ p ^ N) Z₀ with h | h
        · calc ‖(p : C)‖₊ * max ‖y‖₊ ‖yi‖₊ ^ p ^ N ≤ ‖(p : C)‖₊ * Z₀ := by
                exact mul_le_mul_of_nonneg_left (max_pow_le hyZ.le h) zero_le
            _ < rad η := hpZ
            _ < Dπ := hDπ
        · have hD : Dπ = ‖yi‖₊ ^ p ^ N := by
            rw [← hdist, sub_eq_add_neg, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm
              (by rw [nnnorm_neg, nnnorm_pow, nnnorm_pow, hyZ]; exact h.ne), nnnorm_neg,
              nnnorm_pow, nnnorm_pow, hyZ, max_eq_right h.le]
          have hpos : 0 < ‖yi‖₊ ^ p ^ N := hZ₀0.trans h
          calc ‖(p : C)‖₊ * max ‖y‖₊ ‖yi‖₊ ^ p ^ N ≤ ‖(p : C)‖₊ * ‖yi‖₊ ^ p ^ N := by
                exact mul_le_mul_of_nonneg_left (max_pow_le (hyZ.le.trans h.le) le_rfl) zero_le
            _ < ‖yi‖₊ ^ p ^ N := mul_lt_of_lt_one_left hpos hp1'
            _ = Dπ := hD.symm
      rw [← nnnorm_pow, show (y - yi) ^ p ^ N = (y ^ p ^ N - yi ^ p ^ N) +
        ((y - yi) ^ p ^ N - (y ^ p ^ N - yi ^ p ^ N)) by ring,
        IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm (by rw [hdist]; exact hlt.ne'),
        hdist, max_eq_left hlt.le]
    rw [hPfac, eval_mul, eval_C, eval_multiset_prod, Multiset.map_map, nnnorm_mul, mul_pow]
    congr 1
    have := map_multiset_prod (nnnormHom : C →*₀ ℝ≥0)
      (R.map ((fun Q : C[X] ↦ Q.eval y) ∘ fun yi ↦ X - Polynomial.C yi))
    rw [Multiset.map_map] at this
    change ‖_‖₊ ^ _ = _
    rw [show ‖(R.map ((fun Q : C[X] ↦ Q.eval y) ∘ fun yi ↦ X - Polynomial.C yi)).prod‖₊ =
      (R.map (fun yi ↦ ‖y - yi‖₊)).prod by
        rw [show (fun yi ↦ ‖y - yi‖₊) = (nnnormHom : C →*₀ ℝ≥0) ∘
          ((fun Q : C[X] ↦ Q.eval y) ∘ fun yi ↦ X - Polynomial.C yi) by
            funext yi; simp]
        exact this]
    rw [← Multiset.prod_map_pow]
    exact congrArg Multiset.prod (Multiset.map_congr rfl hfac)
  -- the constant `L`
  have hq0 : p ^ N ≠ 0 := (pow_pos hp.pos N).ne'
  have hΛ : (‖β.leadingCoeff‖₊ * rad η ^ (m - 1)) ^ p ^ N < Λ := by
    rw [mul_pow, ← hna, ← pow_mul, hΛdef]
    refine mul_lt_mul_of_pos_left ?_ (pow_pos (nnnorm_pos.2 ha) _)
    rw [← hDdef, ← hRcard, ← Multiset.prod_replicate, ← Multiset.map_const']
    refine Multiset.prod_map_lt_prod_map ?_ _ _ (fun _ _ ↦ hrad) fun y _ ↦ rad_lt hη _
    intro h; rw [← Multiset.card_eq_zero, hRcard] at h; omega
  set L := Λ ^ ((p ^ N : ℕ) : ℝ)⁻¹ with hLdef
  have hL : L ^ p ^ N = Λ := NNReal.rpow_inv_natCast_pow Λ hq0
  have hLβ : ‖β.leadingCoeff‖₊ * rad η ^ (m - 1) < L :=
    lt_of_pow_lt_pow_left₀ (p ^ N) zero_le (hL ▸ hΛ)
  have hrinv : (rad η)⁻¹ ≤ ‖β.leadingCoeff‖₊ * rad η ^ (m - 1) := by
    rw [inv_le_iff_one_le_mul₀ hrad]
    have hrm : rad η ^ m = rad η ^ (m - 1) * rad η := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega)]
    have h2 : ‖β.leadingCoeff‖₊ * rad η ^ m = rad η * (‖β.leadingCoeff‖₊ * rad η ^ (m - 1)) := by
      rw [hrm]; ring
    first
    | exact hbig.trans_eq h2
    | exact hbig.trans_eq (h2.trans (mul_comm _ _))
  refine ⟨L, d₁, ?_, hd₁, fun α hα ω hω ↦ ?_⟩
  · calc 1 ≤ ‖β.leadingCoeff‖₊ * rad η ^ m := hbig
      _ = ‖β.leadingCoeff‖₊ * rad η ^ (m - 1) * rad η := by
          rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
      _ < L * rad η := mul_lt_mul_of_pos_right hLβ hrad
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (α - z₀) (pow_pos hp.pos N)
  have hαZ : radius η α < Z₀ := hα.trans_le hd₁Z
  have hyZ : ‖y‖₊ ^ p ^ N = Z₀ := by rw [← nnnorm_pow, hy, nnnorm_sub_eq_radius hη hαZ]
  have hPy : ‖P.eval y‖₊ = L :=
    (pow_left_inj₀ zero_le zero_le hq0).1 ((hkey α hα y hy).trans hL.symm)
  set s : ℕ → C := fun k ↦ ∑ j ∈ Finset.Icc (p ^ k) m, cr k j * y ^ ((j - p ^ k) * p ^ (N - k))
    with hsdef
  have hPeval : P.eval y = (taylor α β).coeff 1 + ∑ k ∈ Finset.Icc 1 N, s k := by
    rw [taylor_coeff_eq_sum β z₀ α 1, ← hmdef, Finset.sum_range_succ, hPdef, hPlowdef]
    simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, eval_finsetSum, Nat.choose_one_right,
      hsdef]
    have hyp : ∀ j, y ^ ((j - 1) * p ^ N) = (α - z₀) ^ (j - 1) := fun j ↦ by
      rw [mul_comm, pow_mul, hy]
    rw [hDdef, hyp, hadef]
    simp only [hyp, hbdef]
    ring
  -- the error of each root
  have herr : ∀ k ∈ Finset.Icc 1 N, ‖s k - ω k‖₊ < Z₀⁻¹ := by
    intro k hk
    obtain ⟨hk1, hkN⟩ := Finset.mem_Icc.1 hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hpk : p ^ (k' + 1) ≤ m := (Nat.pow_le_pow_right hp.pos hkN).trans hpN
    set f : ℕ → C := fun j ↦ cr (k' + 1) j * y ^ ((j - p ^ (k' + 1)) * p ^ (N - (k' + 1)))
    have hfpow : ∀ j, f j ^ p ^ (k' + 1) =
        (j.choose (p ^ (k' + 1)) : C) * b j * (α - z₀) ^ (j - p ^ (k' + 1)) := by
      intro j
      simp only [f]
      have hexp : (j - p ^ (k' + 1)) * p ^ (N - (k' + 1)) * p ^ (k' + 1) =
          p ^ N * (j - p ^ (k' + 1)) := by
        rw [mul_assoc, ← pow_add, Nat.sub_add_cancel hkN, mul_comm]
      rw [mul_pow, hcr, ← pow_mul, hexp, pow_mul, hy]
    have hroot : ω (k' + 1) ^ p ^ (k' + 1) = ∑ j ∈ Finset.Icc (p ^ (k' + 1)) m,
        f j ^ p ^ (k' + 1) := by
      rw [hω _ hk, taylor_coeff_eq_sum β z₀ α, ← hmdef]
      simp only [hfpow]
      symm
      refine Finset.sum_subset (fun j hj ↦ Finset.mem_range.2 (by
        have := (Finset.mem_Icc.1 hj).2; omega)) fun j hj hj' ↦ ?_
      have : j < p ^ (k' + 1) := by
        by_contra h; push Not at h
        exact hj' (Finset.mem_Icc.2 ⟨h, by have := Finset.mem_range.1 hj; omega⟩)
      rw [Nat.choose_eq_zero_of_lt this, Nat.cast_zero, zero_mul, zero_mul]
    have hne : (Finset.Icc (p ^ (k' + 1)) m).Nonempty := Finset.nonempty_Icc.2 hpk
    set M := (Finset.Icc (p ^ (k' + 1)) m).sup fun j ↦ ‖f j‖₊
    have hM : ∀ j ∈ Finset.Icc (p ^ (k' + 1)) m, ‖f j‖₊ ≤ M := fun j hj ↦
      Finset.le_sup (f := fun j ↦ ‖f j‖₊) hj
    have hMb : M ^ p ^ (k' + 1) ≤ E * Z₀⁻¹ ^ p ^ (k' + 1) := by
      obtain ⟨j₀, hj₀, hj₀M⟩ := Finset.exists_mem_eq_sup _ hne (fun j ↦ ‖f j‖₊)
      have hM' : M = ‖f j₀‖₊ := hj₀M
      rw [hM', ← nnnorm_pow, hfpow, nnnorm_mul, nnnorm_mul, nnnorm_pow,
        nnnorm_sub_eq_radius hη hαZ]
      obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj₀
      calc ‖(j₀.choose (p ^ (k' + 1)) : C)‖₊ * ‖b j₀‖₊ * Z₀ ^ (j₀ - p ^ (k' + 1))
          ≤ 1 * ‖b j₀‖₊ * Z₀ ^ (j₀ - p ^ (k' + 1)) := by
            gcongr; exact IsUltrametricDist.nnnorm_natCast_le_one C _
        _ = ‖b j₀‖₊ * Z₀ ^ j₀ * Z₀⁻¹ ^ p ^ (k' + 1) := by
            rw [one_mul, pow_sub₀ _ hZ₀0.ne' hj1, inv_pow, mul_assoc]
        _ ≤ E * Z₀⁻¹ ^ p ^ (k' + 1) := by gcongr; exact hb j₀
    have h := nnnorm_sum_sub_root_le hp hp1'.le (Finset.Icc (p ^ (k' + 1)) m) f hroot hM
    refine lt_of_pow_lt_pow_left₀ (p ^ (k' + 1)) zero_le (h.trans_lt ?_)
    calc ‖(p : C)‖₊ * M ^ p ^ (k' + 1) ≤ ‖(p : C)‖₊ * (E * Z₀⁻¹ ^ p ^ (k' + 1)) := by gcongr
      _ = (‖(p : C)‖₊ * E) * Z₀⁻¹ ^ p ^ (k' + 1) := by ring
      _ < 1 * Z₀⁻¹ ^ p ^ (k' + 1) :=
          mul_lt_mul_of_pos_right hpE (pow_pos (inv_pos.2 hZ₀0) _)
      _ = Z₀⁻¹ ^ p ^ (k' + 1) := one_mul _
  have hdiff : ‖(taylor α β).coeff 1 + ∑ k ∈ Finset.Icc 1 N, ω k - P.eval y‖₊ < Z₀⁻¹ := by
    rw [hPeval, show (taylor α β).coeff 1 + ∑ k ∈ Finset.Icc 1 N, ω k -
        ((taylor α β).coeff 1 + ∑ k ∈ Finset.Icc 1 N, s k) =
        ∑ k ∈ Finset.Icc 1 N, -(s k - ω k) by simp only [neg_sub, Finset.sum_sub_distrib]; ring]
    exact Valuation.map_sum_lt (NormedField.valuation (K := C)) (inv_pos.2 hZ₀0).ne'
      fun k hk ↦ by
        change ‖-(s k - ω k)‖₊ < Z₀⁻¹
        rw [nnnorm_neg]; exact herr k hk
  have hZL : Z₀⁻¹ < L :=
    ((inv_lt_inv₀ hZ₀0 hrad).2 hZ₀r).trans_le (hrinv.trans hLβ.le)
  rw [show (taylor α β).coeff 1 + ∑ k ∈ Finset.Icc 1 N, ω k = P.eval y +
      ((taylor α β).coeff 1 + ∑ k ∈ Finset.Icc 1 N, ω k - P.eval y) by ring,
    IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm (by
      rw [hPy]; exact (hdiff.trans hZL).ne'), hPy, max_eq_left (hdiff.trans hZL).le]

end StepC

section ASMain

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {η : Valuation (RatFunc C) ℝ≥0} {p : ℕ}

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] in
/-- The prime-power indices in the Artin–Schreier reduction. -/
lemma sum_filter_eq_sum_pow (hp : p.Prime) (m : ℕ) (ω : ℕ → C) :
    ∑ e ∈ (Finset.Icc 1 m).filter (p ∣ ·),
        (if e / p ^ (e.factorization p) = 1 then ω e else 0) =
      ∑ k ∈ Finset.Icc 1 (Nat.log p m), ω (p ^ k) := by
  classical
  rw [← Finset.sum_filter]
  have himg : ((Finset.Icc 1 m).filter (p ∣ ·)).filter (fun e ↦ e / p ^ (e.factorization p) = 1)
      = (Finset.Icc 1 (Nat.log p m)).image (p ^ ·) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨⟨he1, hem⟩, hpe⟩, hj⟩
      have hee : e = p ^ e.factorization p := by
        have h := Nat.ordProj_mul_ordCompl_eq_self e p
        rw [hj, mul_one] at h; exact h.symm
      refine ⟨e.factorization p, ⟨hp.factorization_pos_of_dvd (by omega) hpe, ?_⟩, hee.symm⟩
      exact Nat.le_log_of_pow_le hp.one_lt (hee ▸ hem)
    · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
      have hpk : p ^ k ≤ m := (Nat.pow_le_pow_right hp.pos hkN).trans
        (Nat.pow_log_le_self p (by
          intro h; rw [h, Nat.log_zero_right] at hkN; omega))
      refine ⟨⟨⟨Nat.one_le_pow _ _ hp.pos, hpk⟩, dvd_pow_self p (by omega)⟩, ?_⟩
      rw [Nat.factorization_pow_self hp, Nat.div_self (pow_pos hp.pos k)]
  rw [himg, Finset.sum_image fun x _ y _ h ↦ Nat.pow_right_injective hp.two_le h]

variable (hη : Splitting.IsTypeFour η) (hrad : 0 < rad η) (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {Q : C[X]} (hQ : pv η Q = 1) {γ : C} (hγ : γ ^ (p - 1) = -(p : C)) {E : ℝ≥0} (hE1 : 1 < E)
  (hγE : ‖γ‖₊ * E ^ p < 1)
  (hNS : ∀ H : RatFunc C, H ≠ 0 →
      kummerBound C p * (η H : ℝ) ^ p < η (algebraMap C[X] (RatFunc C) Q - H ^ p))
  (hAS : ∀ ε : ℝ, kummerBound C p < ε →
      ∃ H : C[X], (η (algebraMap C[X] (RatFunc C) (Q - H ^ p)) : ℝ) < ε)

include hη hrad hp hp1 hQ hγ hE1 hγE hAS in
/-- **Temkin's `dirtylem` for `a = 1`**: the top coefficient of a coset element of degree
`m ≥ 2`, `p ∤ m`, satisfies `|b_m| r^m < 1`. -/
theorem dirty_AS {b : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E) (hm : 2 ≤ b.natDegree)
    (hpm : ¬ p ∣ b.natDegree) : ‖b.leadingCoeff‖₊ * rad η ^ b.natDegree < 1 := by
  classical
  by_contra hbig
  push Not at hbig
  have hE := hE1.le
  have hγp := nnnorm_p_le_gamma hp hγ hp1
  have hpE : ‖(p : C)‖₊ * E ^ p < 1 := lt_of_le_of_lt (by gcongr) hγE
  have hpE1 : ‖(p : C)‖₊ * E < 1 :=
    lt_of_le_of_lt (by gcongr; exact le_self_pow₀ hE hp.ne_zero) hpE
  obtain ⟨L, d, hL1, hd, hell⟩ := exists_ell_eq hη hrad hp hp1 hpE1 hbE hm hpm hbig
  set lam := min ((1 + L * rad η) / 2) E
  have hlam1 : 1 < lam := lt_min (by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    have := hL1; rw [← NNReal.coe_lt_coe] at this ⊢; push_cast at this ⊢; linarith) hE1
  have hlamE : lam ≤ E := min_le_right _ _
  have hlamL : lam < L * rad η := lt_of_le_of_lt (min_le_left _ _) (by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ≥0) < 2)]
    have := hL1; rw [← NNReal.coe_lt_coe] at this ⊢; push_cast at this ⊢; linarith)
  obtain ⟨t, ht, hbt⟩ := exists_AS_move_lt hη hp hp1 hQ hγ hE hγE hAS hb hbE hlam1 hlamE
  have htE := le_E_of_pow_le hp hE ht
  obtain ⟨db, hdb, hb'⟩ := exists_deep_le hη b
  obtain ⟨dt, hdt, ht'⟩ := exists_deep_le hη t
  obtain ⟨dbt, hdbt, hbt'⟩ := exists_deep_le hη (b - (t ^ p - t))
  obtain ⟨α, hα⟩ := exists_radius_lt (lt_min (lt_min hd hdb) (lt_min hdt hdbt))
  have hαd : radius η α < d := hα.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hαb : radius η α < db := hα.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hαt : radius η α < dt := hα.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hαbt : radius η α < dbt := hα.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  set ρ : ℝ≥0ˣ := Units.mk0 (radius η α) (radius_ne_zero η α)
  have hgb : gw α ρ b ≤ E := (hb' α hαb ρ hαb).trans hbE
  have hgt : gw α ρ t ≤ E := (ht' α hαt ρ hαt).trans htE
  have hgbt : gw α ρ (b - (t ^ p - t)) < lam := (hbt' α hαbt ρ hαbt).trans_lt hbt
  choose ω hω using fun e ↦ IsAlgClosed.exists_pow_nat_eq ((taylor α b).coeff e)
    (pow_pos hp.pos (e.factorization p))
  have hclaim := nnnorm_ell_mul_le hp hE hpE hgb hgt hlam1 hgbt ω (fun e _ ↦ hω e)
  rw [sum_filter_eq_sum_pow hp] at hclaim
  have hL := hell α hαd (fun k ↦ ω (p ^ k)) fun k _ ↦ by
    have := hω (p ^ k); rwa [Nat.factorization_pow_self hp] at this
  rw [hL] at hclaim
  have hL0 : 0 < L := by
    by_contra h; push Not at h; rw [le_zero_iff.1 h, zero_mul] at hL1; exact absurd hL1 (by simp)
  have : L * rad η < L * radius η α := mul_lt_mul_of_pos_left (rad_lt hη α) hL0
  exact absurd (hclaim.trans_lt (hlamL.trans this)) (lt_irrefl _)

include hη hrad hp hp1 hQ hγ hE1 hγE hAS in
/-- **One step of the degree reduction** in the Artin–Schreier case. -/
lemma step_AS {b : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E) (hm : 2 ≤ b.natDegree) :
    ∃ b₁ : C[X], AdmS η p Q γ b₁ ∧ pv η b₁ ≤ E ∧ b₁.natDegree < b.natDegree := by
  have hE := hE1.le
  have hb0 : b ≠ 0 := by rintro rfl; simp at hm
  by_cases hpm : p ∣ b.natDegree
  · obtain ⟨k, hk⟩ := hpm
    obtain ⟨d, hd, hdeep⟩ := exists_deep hη hb0
    obtain ⟨a, ha⟩ := exists_radius_lt hd
    have hUp := hdeep a ha (pv η) (pv_C hη) ha
    set ρ : ℝ≥0ˣ := Units.mk0 (radius η a) (radius_ne_zero η a)
    have hUg := hdeep a ha (gw a ρ) (gw_C a ρ) (by rw [gw_X_sub_C]; exact ha)
    have hterm := nnnorm_taylor_coeff_le a ρ (b - Polynomial.C (b.eval a)) b.natDegree
    rw [map_sub, taylor_C, coeff_sub, coeff_C, if_neg (by omega), sub_zero,
      coeff_taylor_natDegree] at hterm
    have hlt : ‖b.leadingCoeff‖₊ * radius η a ^ b.natDegree < pv η b := by
      rw [← eval_nnnorm_eq hη hUp]; exact hterm.trans_lt hUg
    obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq b.leadingCoeff hp.pos
    set t := Polynomial.C c₀ * (X - Polynomial.C a) ^ k
    have htp : t ^ p = Polynomial.C b.leadingCoeff * (X - Polynomial.C a) ^ b.natDegree := by
      rw [mul_pow, ← map_pow, hc₀, ← pow_mul, hk, mul_comm k p]
    have htv : pv η t ^ p ≤ E := by
      rw [← map_pow, htp, map_mul, map_pow, pv_C hη]; exact (hlt.trans_le hbE).le
    have htE := le_E_of_pow_le hp hE htv
    have hkm : k < b.natDegree := by
      have hk0 : 0 < k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · rw [h, mul_zero] at hk; omega
        · exact h
      rw [hk]
      exact lt_mul_of_one_lt_left hk0 hp.one_lt
    refine ⟨b - (t ^ p - t), admS_sub_AS hη hp hp1 hQ hγ hE hγE hb hbE htv, ?_, ?_⟩
    · rw [show b - (t ^ p - t) = (b - t ^ p) + t by ring]
      refine (Valuation.map_add _ _ _).trans (max_le ((Valuation.map_sub _ _ _).trans
        (max_le hbE (by rw [map_pow]; exact htv))) htE)
    · rw [show b - (t ^ p - t) = (b - t ^ p) + t by ring, htp]
      refine (natDegree_add_le _ _).trans_lt (max_lt (natDegree_sub_lc_lt (by omega) a) ?_)
      exact (natDegree_C_mul_le _ _).trans_lt (by
        rw [natDegree_pow, natDegree_X_sub_C, mul_one]; exact hkm)
  · have hdirty := dirty_AS hη hrad hp hp1 hQ hγ hE1 hγE hAS hb hbE hm hpm
    have hev : ∀ᶠ t in 𝓝[>] (rad η), ‖b.leadingCoeff‖₊ * t ^ b.natDegree < 1 :=
      (ContinuousAt.eventually_lt (f := fun t : ℝ≥0 ↦ ‖b.leadingCoeff‖₊ * t ^ b.natDegree)
        (g := fun _ ↦ 1) (by fun_prop) continuousAt_const hdirty).filter_mono
        nhdsWithin_le_nhds
    obtain ⟨t, ht, ht'⟩ := (hev.and self_mem_nhdsWithin).exists
    obtain ⟨z, hz⟩ := exists_radius_lt (Set.mem_Ioi.1 ht')
    have hd : pv η (Polynomial.C b.leadingCoeff * (X - Polynomial.C z) ^ b.natDegree) < 1 := by
      rw [map_mul, map_pow, pv_C hη, ← radius_eq_pv]
      exact lt_of_le_of_lt (by gcongr) ht
    refine ⟨_, admS_sub hη hp hp1 hQ hγ hE hγE hb hbE hd, ?_, natDegree_sub_lc_lt (by omega) z⟩
    exact (Valuation.map_sub _ _ _).trans (max_le hbE (hd.le.trans hE))

include hη hrad hp hp1 hQ hγ hE1 hγE hAS in
lemma exists_admS_natDegree_le_one :
    ∀ n : ℕ, ∀ b : C[X], b.natDegree = n → AdmS η p Q γ b → pv η b ≤ E →
      ∃ b₁ : C[X], AdmS η p Q γ b₁ ∧ pv η b₁ ≤ E ∧ b₁.natDegree ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hn hb hbE
    by_cases h1 : b.natDegree ≤ 1
    · exact ⟨b, hb, hbE, h1⟩
    obtain ⟨b₁, hb₁, hb₁E, hlt⟩ := step_AS hη hrad hp hp1 hQ hγ hE1 hγE hAS hb hbE (by omega)
    exact ih _ (hn ▸ hlt) _ rfl hb₁ hb₁E

omit [CharZero C] in
lemma isU_pow' {w : Valuation C[X] ℝ≥0} (hw : ∀ c : C, w (Polynomial.C c) = ‖c‖₊) {a : C}
    {F : C[X]} (hF : IsU w a F) (n : ℕ) : IsU w a (F ^ n) := by
  induction n with
  | zero => simpa using isU_C hw (a := a) one_ne_zero
  | succ n ih => rw [pow_succ]; exact isU_mul hw ih hF

include hη hp hp1 hQ hγ hE1 hγE hNS in
/-- **The endgame data** in the Artin–Schreier case, from a coset element of degree `≤ 1`. -/
theorem final_AS {b : C[X]} (hb : AdmS η p Q γ b) (hbE : pv η b ≤ E) (hdeg : b.natDegree ≤ 1)
    (a₀ : C) (ρ₀ : ℝ≥0) (hρ₀ : η (RatFunc.X - algebraMap C (RatFunc C) a₀) < ρ₀) :
    ∃ (H : C[X]) (a c : C), c ≠ 0 ∧
      η (RatFunc.X - algebraMap C (RatFunc C) a) < ‖c‖₊ ∧ ‖c‖₊ ≤ ρ₀ ∧ ‖a - a₀‖₊ ≤ ρ₀ ∧
      ‖H.eval a‖ = 1 ∧
      (∀ i, 1 ≤ i → ‖(H.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ < 1) ∧
      Q.eval a = H.eval a ^ p ∧
      ∃ M : ℝ, kummerBound C p < M ∧
        ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff 1‖ = M ∧
        ∀ i, ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ ≤ M := by
  have hE := hE1.le
  have hA0 := kb_pos (C := C) hp
  -- degree one
  have hdeg1 : b.natDegree = 1 := by
    rcases Nat.lt_or_ge b.natDegree 1 with h0 | h1
    · exfalso
      have hb' : b = Polynomial.C (b.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
      rw [hb'] at hb
      exact not_admS_C hη hp hp1 hQ hγ hE hγE hNS hb (by rw [← pv_C hη, ← hb']; exact hbE)
    · omega
  set β₁ := b.coeff 1
  set β₀ := b.coeff 0
  have hbeq : b = Polynomial.C β₁ * X + Polynomial.C β₀ := eq_X_add_C_of_natDegree_le_one hdeg
  have hb0 : b ≠ 0 := by rintro rfl; simp at hdeg1
  have hβ₁ : β₁ ≠ 0 := by
    have := leadingCoeff_ne_zero.2 hb0
    rwa [leadingCoeff, hdeg1] at this
  have hβ0 : 0 < ‖β₁‖₊ := nnnorm_pos.2 hβ₁
  -- `1 ≤ |β₁| r`
  have hβr : 1 ≤ ‖β₁‖₊ * rad η := by
    by_contra hlt
    push Not at hlt
    have hr' : rad η < 1 / ‖β₁‖₊ := by rwa [lt_div_iff₀ hβ0, mul_comm]
    obtain ⟨z, hz⟩ := exists_radius_lt hr'
    have hd : pv η (Polynomial.C β₁ * (X - Polynomial.C z)) < 1 := by
      rw [map_mul, pv_C hη, ← radius_eq_pv]
      calc ‖β₁‖₊ * radius η z < ‖β₁‖₊ * (1 / ‖β₁‖₊) := mul_lt_mul_of_pos_left hz hβ0
        _ = 1 := mul_div_cancel₀ _ hβ0.ne'
    have hconst : b - Polynomial.C β₁ * (X - Polynomial.C z) = Polynomial.C (β₀ + β₁ * z) := by
      rw [hbeq, map_add, map_mul]; ring
    have h2 := admS_sub hη hp hp1 hQ hγ hE hγE hb hbE hd
    rw [hconst] at h2
    refine not_admS_C hη hp hp1 hQ hγ hE hγE hNS h2 ?_
    rw [← pv_C hη, ← hconst]
    exact (Valuation.map_sub _ _ _).trans (max_le hbE (hd.le.trans hE))
  obtain ⟨H, hH⟩ := hb
  have hH1 := pv_eq_one_of_admS hη hp hp1 hQ hγ hE hγE hH hbE
  set g₀ := γ ^ p with hg₀
  have hng₀ : ‖g₀‖₊ = kb C p := by rw [hg₀, nnnorm_pow, nnnorm_gamma_pow hp hγ]
  set e := Q - H ^ p * (1 + Polynomial.C g₀ * b) with he
  have hH0 : H ≠ 0 := by rintro rfl; simp at hH1
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨dH, hdH, hH'⟩ := exists_deep hη hH0
  obtain ⟨dQ, hdQ, hQ'⟩ := exists_deep hη hQ0
  obtain ⟨de, hde, he'⟩ := exists_deep_le hη e
  have hρ₀r : rad η < ρ₀ := (rad_lt hη a₀).trans (by rwa [radius_eq_val] at hρ₀)
  obtain ⟨c, hc1, hc2⟩ := exists_nnnorm_between hη (lt_min (lt_min hdH hdQ) (lt_min hde hρ₀r))
  have hc0 : c ≠ 0 := nnnorm_pos.1 (lt_of_le_of_lt zero_le hc1)
  have hcH : ‖c‖₊ < dH := hc2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcQ : ‖c‖₊ < dQ := hc2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hce : ‖c‖₊ < de := hc2.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hcρ₀ : ‖c‖₊ < ρ₀ := hc2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨a, ha⟩ := exists_radius_lt hc1
  set ρ : ℝ≥0ˣ := Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0) with hρ
  have hUHp := hH' a (ha.trans hcH) (pv η) (pv_C hη) (ha.trans hcH)
  have hUHg := hH' a (ha.trans hcH) (gw a ρ) (gw_C a ρ) (by rw [gw_X_sub_C]; exact hcH)
  have hHa : ‖H.eval a‖₊ = 1 := by rw [eval_nnnorm_eq hη hUHp, hH1]
  have hHa0 : H.eval a ≠ 0 := nnnorm_ne_zero_iff.1 (by rw [hHa]; exact one_ne_zero)
  have hQa : ‖Q.eval a‖₊ = 1 := by
    rw [eval_nnnorm_eq hη (hQ' a (ha.trans hcQ) (pv η) (pv_C hη) (ha.trans hcQ)), hQ]
  have hge : gw a ρ e < kb C p := (he' a (ha.trans hce) ρ hce).trans_lt hH
  have hUHpg := isU_pow' (gw_C a ρ) hUHg p
  have hgHp : gw a ρ (H ^ p - Polynomial.C (H.eval a ^ p)) < 1 := by
    have := hUHpg; unfold IsU at this; rwa [eval_pow, nnnorm_pow, hHa, one_pow] at this
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (Q.eval a / H.eval a ^ p) hp.pos
  have hun : ‖u‖₊ = 1 := by
    have := congrArg nnnorm hu
    rw [nnnorm_pow, nnnorm_div, nnnorm_pow, hQa, hHa, one_pow, div_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hp.ne_zero).1 this
  set Hout := Polynomial.C u * H with hHout
  have hHouta : Hout.eval a = u * H.eval a := by simp [Hout]
  have hQHa : Q.eval a = Hout.eval a ^ p := by
    rw [hHouta, mul_pow, hu, div_mul_cancel₀ _ (pow_ne_zero _ hHa0)]
  set κ := e.eval a / H.eval a ^ p
  set R := e - Polynomial.C κ * H ^ p with hR
  have hea : e.eval a = Q.eval a - H.eval a ^ p * (1 + g₀ * b.eval a) := by
    simp [he]
  have hu' : u ^ p = 1 + g₀ * b.eval a + κ := by
    rw [hu, show κ = e.eval a / H.eval a ^ p from rfl, hea]; field_simp; ring
  have hG : Q - Hout ^ p = Polynomial.C (g₀ * β₁) * (H ^ p * X) -
      Polynomial.C (g₀ * β₁ * a) * H ^ p + R := by
    have hba : b.eval a = β₁ * a + β₀ := by conv_lhs => rw [hbeq]; simp
    rw [hHout, mul_pow, ← map_pow, hu', hR, he, hba, hbeq]
    simp only [map_add, map_mul, map_one]
    ring
  have hG' : Q - Hout ^ p = Polynomial.C (g₀ * β₁) * (H ^ p * (X - Polynomial.C a)) + R := by
    rw [hG, map_mul (Polynomial.C) (g₀ * β₁) a]; ring
  -- Gauss bounds
  have hgHp1 : gw a ρ (H ^ p) = 1 := by
    rw [val_eq_of_isU (gw_C a ρ) hUHpg, eval_pow, nnnorm_pow, hHa, one_pow]
  have hgR : gw a ρ R < kb C p := by
    rw [hR]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hge ?_)
    rw [map_mul, gw_C, hgHp1, mul_one, show κ = e.eval a / H.eval a ^ p from rfl, nnnorm_div,
      nnnorm_pow, hHa, one_pow, div_one]
    exact (nnnorm_eval_le_gw a ρ e).trans_lt hge
  set Mn : ℝ≥0 := kb C p * (‖β₁‖₊ * ‖c‖₊) with hMndef
  have hMn : kb C p < Mn := by
    refine lt_mul_of_one_lt_right hA0 (hβr.trans_lt ?_)
    exact mul_lt_mul_of_pos_left hc1 hβ0
  have hRi : ∀ i, ‖(R.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖₊ < kb C p :=
    fun i ↦ (nnnorm_comp_coeff_le R a hc0 i).trans_lt hgR
  set T := taylor a H
  have hcoeff : ∀ i, ((Q - Hout ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff i =
      c ^ i * (g₀ * β₁ * ((T ^ p) * X).coeff i) +
        (R.comp (Polynomial.C c * X + Polynomial.C a)).coeff i := by
    intro i
    rw [hG', add_comp, coeff_add, comp_affine_coeff]
    congr 2
    rw [taylor_mul, taylor_C, taylor_mul, taylor_pow, map_sub, taylor_X, taylor_C,
      add_sub_cancel_right, coeff_C_mul]
  have hTp0 : (T ^ p).coeff 0 = H.eval a ^ p := by
    rw [← taylor_pow, taylor_coeff_zero, eval_pow]
  have hTpn : ∀ n, 1 ≤ n → ‖(T ^ p).coeff n‖₊ * ‖c‖₊ ^ n < 1 := by
    intro n hn
    have h := nnnorm_taylor_coeff_le a ρ (H ^ p - Polynomial.C (H.eval a ^ p)) n
    rw [map_sub, taylor_C, coeff_sub, coeff_C, if_neg (by omega), sub_zero, taylor_pow] at h
    exact h.trans_lt hgHp
  -- conclusion
  refine ⟨Hout, a, c, hc0, by rw [radius_eq_val]; exact ha, hcρ₀.le, ?_, ?_, ?_, hQHa, ?_⟩
  · have hsplit : Polynomial.C (a - a₀) = (X - Polynomial.C a₀) - (X - Polynomial.C a) := by
      rw [map_sub]; ring
    rw [← pv_C hη, hsplit]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [← radius_eq_pv, ← radius_eq_val]; exact hρ₀.le
    · rw [← radius_eq_pv]; exact (ha.trans hcρ₀).le
  · rw [hHouta, norm_mul, ← coe_nnnorm, ← coe_nnnorm, hun, hHa]; norm_num
  · intro i hi
    rw [comp_affine_coeff, hHout, taylor_mul, taylor_C, coeff_C_mul, norm_mul, norm_mul,
      ← coe_nnnorm u, hun, NNReal.coe_one, one_mul, norm_pow]
    have h := hTpn i hi
    have h1 : ‖(T).coeff i‖₊ * ‖c‖₊ ^ i < 1 := by
      have h' := nnnorm_taylor_coeff_le a ρ (H - Polynomial.C (H.eval a)) i
      rw [map_sub, taylor_C, coeff_sub, coeff_C, if_neg (by omega), sub_zero] at h'
      have := hUHg; unfold IsU at this; rw [hHa] at this
      exact h'.trans_lt this
    rw [← NNReal.coe_lt_coe, NNReal.coe_mul, NNReal.coe_pow, coe_nnnorm, coe_nnnorm,
      NNReal.coe_one] at h1
    linarith [mul_comm ‖c‖ ‖T.coeff i‖]
  · refine ⟨(Mn : ℝ), by rw [← coe_kb]; exact_mod_cast hMn, ?_, fun i ↦ ?_⟩
    · rw [hcoeff 1, coeff_mul_X, hTp0, pow_one]
      have hmain : ‖c * (g₀ * β₁ * H.eval a ^ p)‖₊ = Mn := by
        rw [nnnorm_mul, nnnorm_mul, nnnorm_mul, hng₀, nnnorm_pow (H.eval a) p, hHa, one_pow,
          mul_one, hMndef]
        ring
      have hlt := (hRi 1).trans hMn
      rw [← coe_nnnorm, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm (by
        rw [hmain]; exact hlt.ne'), hmain, max_eq_left hlt.le]
    · rw [hcoeff i, ← coe_nnnorm]
      refine NNReal.coe_le_coe.2 ((IsUltrametricDist.nnnorm_add_le_max _ _).trans
        (max_le ?_ ((hRi i).trans hMn).le))
      rcases i with _ | n
      · simp
      · rw [coeff_mul_X, nnnorm_mul, nnnorm_mul, nnnorm_mul, hng₀, nnnorm_pow c, hMndef]
        rcases n with _ | n
        · rw [hTp0, nnnorm_pow, hHa]; simp; ring_nf; exact le_rfl
        · have h := hTpn (n + 1) (by omega)
          calc ‖c‖₊ ^ (n + 1 + 1) * (kb C p * ‖β₁‖₊ * ‖(T ^ p).coeff (n + 1)‖₊)
              = kb C p * (‖β₁‖₊ * ‖c‖₊) * (‖(T ^ p).coeff (n + 1)‖₊ * ‖c‖₊ ^ (n + 1)) := by ring
            _ ≤ kb C p * (‖β₁‖₊ * ‖c‖₊) * 1 := by gcongr
            _ = kb C p * (‖β₁‖₊ * ‖c‖₊) := mul_one _

end ASMain

section ASTheorem

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C]

/-- **Degree reduction in the Artin–Schreier case** `μ = A` (Temkin, Prop. 6.3.3 with
Lemma 6.3.6 for `a = 1`). -/
theorem degreeReductionASFor {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) :
    DegreeReductionASFor C p := by
  intro η hη hr Q hQ hNS hAS a₀ ρ₀ hρ₀
  have hQ' : pv η Q = 1 := hQ
  have hrad : 0 < rad η := by
    obtain ⟨r, hr0, hrb⟩ := hr
    exact hr0.trans_le (le_ciInf fun b ↦ by rw [← radius_eq_val]; exact hrb b)
  obtain ⟨γ, hγ⟩ := IsAlgClosed.exists_pow_nat_eq (-(p : C)) (Nat.sub_pos_of_lt hp.one_lt)
  have hγ1 := nnnorm_gamma_lt_one hp hγ hp1
  have hev : ∀ᶠ E in 𝓝[>] (1 : ℝ≥0), ‖γ‖₊ * E ^ p < 1 :=
    (ContinuousAt.eventually_lt (f := fun E : ℝ≥0 ↦ ‖γ‖₊ * E ^ p) (g := fun _ ↦ 1)
      (by fun_prop) continuousAt_const (by simpa using hγ1)).filter_mono nhdsWithin_le_nhds
  obtain ⟨E, hγE, hE1⟩ := (hev.and self_mem_nhdsWithin).exists
  have hE1' : 1 < E := hE1
  obtain ⟨b, hb, hbE⟩ := exists_admS_init hη hp hp1 hQ' hγ hE1'.le hγE hAS hE1'
  obtain ⟨b₁, hb₁, hb₁E, hdeg⟩ := exists_admS_natDegree_le_one hη hrad hp hp1 hQ' hγ hE1' hγE
    hAS _ b rfl hb hbE
  exact final_AS hη hp hp1 hQ' hγ hE1' hγE hNS hb₁ hb₁E hdeg a₀ ρ₀ hρ₀

/-- **`DegreeReductionFor` holds** (Temkin, Prop. 6.3.3): both the purely inseparable and the
Artin–Schreier case are proved. -/
theorem degreeReductionFor {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) :
    DegreeReductionFor C p :=
  degreeReductionFor_of_AS hp hp1 (degreeReductionASFor hp hp1)

end ASTheorem

end DegRed

end TypeFour

end SemistableReduction
