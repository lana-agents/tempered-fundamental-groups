/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NoImmediate

/-!
# Value-transcendental generators: Laurent polynomials

Blueprint §9.12 O13 (STAB3, T0). Let `C ⊆ K` be non-archimedean fields and `y ∈ K` with
`‖y‖ ∉ |C|` (`IsValTrans`, a *value-transcendental* element; e.g. `x - a` at a Gauss point of
type 3). For `C` algebraically closed (so `|C^×|` is divisible):

* `eq_of_norm_mul_zpow_eq`: `‖c‖ ‖y‖ⁿ = ‖d‖ ‖y‖ᵐ` with `c ≠ 0` forces `n = m`;
* Laurent polynomials `lev y f = Σ f n • yⁿ` (`f : ℤ →₀ C`) are **orthogonal**: the terms have
  pairwise distinct norms, so `‖lev y f‖` is attained at a unique dominant index (`exists_dom`),
  and every term is bounded by the norm (`tm_le`);
* `IsType3 C y`: `K` is the closure of `C(y)`. Then Laurent polynomials are dense
  (`exists_lev_near`, via geometric series for `(y - a)⁻¹`, `|a| ≠ ‖y‖`), every nonzero element
  has a dominant monomial (`exists_dom_mono`), and the values of `K` are `|C^×| · ‖y‖^ℤ`.
-/

open Polynomial
open scoped Topology

namespace SemistableReduction

namespace Type3

variable {C K : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  [NontriviallyNormedField K] [IsUltrametricDist K] [NormedAlgebra C K]

variable (C) in
/-- `y` is **value-transcendental** over `C`: its norm is not a norm of `C`. -/
def IsValTrans (y : K) : Prop := ∀ c : C, ‖y‖ ≠ ‖c‖

omit [IsUltrametricDist C] [IsUltrametricDist K] [NormedAlgebra C K] in
lemma IsValTrans.ne_zero {y : K} (hy : IsValTrans C y) : y ≠ 0 := by
  rintro rfl
  exact hy 0 (by simp)

omit [IsUltrametricDist C] [IsUltrametricDist K] [NormedAlgebra C K] in
lemma IsValTrans.norm_pos {y : K} (hy : IsValTrans C y) : 0 < ‖y‖ :=
  norm_pos_iff.2 hy.ne_zero

omit [IsUltrametricDist C] [IsUltrametricDist K] [NormedAlgebra C K] in
/-- If `‖y‖ᵏ` (`k ≠ 0`) is a norm of `C`, so is `‖y‖` (divisibility of `|C^×|`). -/
lemma IsValTrans.zpow_ne [IsAlgClosed C] {y : K} (hy : IsValTrans C y) {k : ℤ} (hk : k ≠ 0)
    (d : C) : ‖y‖ ^ k ≠ ‖d‖ := by
  intro h
  have hy0 := hy.norm_pos
  -- reduce to `k > 0`
  obtain ⟨n, hn, d', hd'⟩ : ∃ n : ℕ, 0 < n ∧ ∃ d' : C, ‖y‖ ^ n = ‖d'‖ := by
    rcases lt_or_gt_of_ne hk with hk | hk
    · refine ⟨(-k).toNat, by omega, d⁻¹, ?_⟩
      rw [norm_inv, ← h, ← zpow_natCast, Int.toNat_of_nonneg (by omega), zpow_neg]
    · refine ⟨k.toNat, by omega, d, ?_⟩
      rw [← h, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq d' hn
  apply hy e
  rw [← he, norm_pow] at hd'
  exact (pow_left_inj₀ hy0.le (norm_nonneg _) hn.ne').1 hd'

omit [IsUltrametricDist C] [IsUltrametricDist K] [NormedAlgebra C K] in
lemma IsValTrans.eq_of_norm_mul_zpow_eq [IsAlgClosed C] {y : K} (hy : IsValTrans C y) {c d : C}
    (hc : c ≠ 0) {n m : ℤ} (h : ‖c‖ * ‖y‖ ^ n = ‖d‖ * ‖y‖ ^ m) : n = m := by
  by_contra hnm
  have hy0 := hy.norm_pos
  apply hy.zpow_ne (sub_ne_zero.2 hnm) (d / c)
  rw [norm_div, eq_div_iff (norm_ne_zero_iff.2 hc), zpow_sub₀ hy0.ne', mul_comm, ← mul_div_assoc,
    h, mul_div_assoc, div_self (zpow_ne_zero _ hy0.ne'), mul_one]

omit [IsUltrametricDist C] [IsUltrametricDist K] [NormedAlgebra C K] in
lemma IsValTrans.ne_norm_mul_zpow [IsAlgClosed C] {y : K} (hy : IsValTrans C y) {c : C}
    (hc : c ≠ 0) {n : ℤ} (hn : n ≠ 0) (d : C) : ‖c‖ * ‖y‖ ^ n ≠ ‖d‖ := fun h ↦
  hn (hy.eq_of_norm_mul_zpow_eq hc (d := d) (m := 0) (by rw [zpow_zero, mul_one, h]))

/-! ### Monomials and Laurent polynomials -/

/-- The monomial `c yⁿ`. -/
noncomputable def mono (y : K) (c : C) (n : ℤ) : K := algebraMap C K c * y ^ n

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma norm_mono (y : K) (c : C) (n : ℤ) : ‖mono y c n‖ = ‖c‖ * ‖y‖ ^ n := by
  rw [mono, norm_mul, norm_algebraMap', norm_zpow]

omit [IsUltrametricDist C] [IsUltrametricDist K] in
@[simp]
lemma mono_zero (y : K) (n : ℤ) : mono y (0 : C) n = 0 := by simp [mono]

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma mono_add (y : K) (c d : C) (n : ℤ) : mono y (c + d) n = mono y c n + mono y d n := by
  simp [mono, add_mul]

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma mono_mul_mono {y : K} (hy : y ≠ 0) (c d : C) (n m : ℤ) :
    mono y c n * mono y d m = mono y (c * d) (n + m) := by
  simp only [mono, map_mul, zpow_add₀ hy]
  ring

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma mono_pow {y : K} (c : C) (n : ℤ) (k : ℕ) :
    mono y c n ^ k = mono y (c ^ (k : ℕ)) ((k : ℤ) * n) := by
  rw [mono, mono, mul_pow, map_pow, ← zpow_natCast (y ^ n), ← zpow_mul, mul_comm n]

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma smul_mono (y : K) (a c : C) (n : ℤ) : algebraMap C K a * mono y c n = mono y (a * c) n := by
  simp [mono, mul_assoc]

/-- The term norms `‖fₙ‖ ‖y‖ⁿ` of a Laurent polynomial. -/
noncomputable def tm (y : K) (f : ℤ →₀ C) (n : ℤ) : ℝ := ‖f n‖ * ‖y‖ ^ n

/-- The Laurent polynomial `Σ fₙ yⁿ`. -/
noncomputable def lev (y : K) (f : ℤ →₀ C) : K := f.sum fun n c ↦ mono y c n

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma lev_add (y : K) (f g : ℤ →₀ C) : lev y (f + g) = lev y f + lev y g :=
  Finsupp.sum_add_index' (fun _ ↦ mono_zero y _) fun n c d ↦ mono_add y c d n

omit [IsUltrametricDist C] [IsUltrametricDist K] in
@[simp]
lemma lev_zero (y : K) : lev y (0 : ℤ →₀ C) = 0 := by simp [lev]

omit [IsUltrametricDist C] [IsUltrametricDist K] in
@[simp]
lemma lev_single (y : K) (n : ℤ) (c : C) : lev y (Finsupp.single n c) = mono y c n :=
  Finsupp.sum_single_index (mono_zero y n)

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma lev_neg (y : K) (f : ℤ →₀ C) : lev y (-f) = -lev y f := by
  rw [eq_neg_iff_add_eq_zero, ← lev_add, neg_add_cancel, lev_zero]

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma lev_sub (y : K) (f g : ℤ →₀ C) : lev y (f - g) = lev y f - lev y g := by
  rw [sub_eq_add_neg, lev_add, lev_neg, ← sub_eq_add_neg]

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma lev_smul (y : K) (a : C) (f : ℤ →₀ C) : lev y (a • f) = algebraMap C K a * lev y f := by
  rw [lev, lev, Finsupp.sum_smul_index' (h := fun n c ↦ mono y c n) (fun n ↦ mono_zero y n),
    Finsupp.mul_sum]
  exact Finset.sum_congr rfl fun n _ ↦ (smul_mono y a (f n) n).symm

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma lev_eq_sum (y : K) (f : ℤ →₀ C) : lev y f = ∑ n ∈ f.support, mono y (f n) n := rfl

variable (C) in
/-- Laurent polynomials: the range of `lev y`, a subalgebra. -/
noncomputable def laurent {y : K} (hy : y ≠ 0) : Subalgebra C K where
  carrier := Set.range (lev y)
  mul_mem' := by
    classical
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    refine ⟨f.sum fun n c ↦ g.sum fun m d ↦ (Finsupp.single (n + m) (c * d) : ℤ →₀ C), ?_⟩
    rw [lev_eq_sum y f, lev_eq_sum y g, Finset.sum_mul_sum]
    rw [Finsupp.sum]
    induction f.support using Finset.induction_on with
    | empty => simp
    | insert n s hn ih =>
      rw [Finset.sum_insert hn, Finset.sum_insert hn, lev_add, ih]
      congr 1
      rw [Finsupp.sum]
      induction g.support using Finset.induction_on with
      | empty => simp
      | insert m t hm ih' =>
        rw [Finset.sum_insert hm, Finset.sum_insert hm, lev_add, ih', lev_single,
          mono_mul_mono hy]
  add_mem' := by
    rintro _ _ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact ⟨f + g, lev_add y f g⟩
  algebraMap_mem' c := ⟨Finsupp.single 0 c, by simp [mono]⟩

omit [IsUltrametricDist C] [IsUltrametricDist K] in
lemma mono_mem_laurent {y : K} (hy : y ≠ 0) (c : C) (n : ℤ) : mono y c n ∈ laurent C hy :=
  ⟨Finsupp.single n c, lev_single y n c⟩

/-! ### Orthogonality -/

/-- A finite sum in which one term strictly dominates has the norm of that term. -/
lemma norm_sum_eq_of_dom {ι : Type*} {s : Finset ι} {g : ι → K} {i : ι}
    (hi : i ∈ s) (hdom : ∀ j ∈ s, j ≠ i → ‖g j‖ < ‖g i‖) : ‖∑ j ∈ s, g j‖ = ‖g i‖ := by
  classical
  rw [← Finset.add_sum_erase s g hi]
  rcases (s.erase i).eq_empty_or_nonempty with he | hne
  · rw [he, Finset.sum_empty, add_zero]
  have hlt : ‖∑ j ∈ s.erase i, g j‖ < ‖g i‖ := by
    obtain ⟨j, hj, hjle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne g
    exact hjle.trans_lt (hdom j (Finset.mem_of_mem_erase hj) (Finset.ne_of_mem_erase hj))
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le]

variable [IsAlgClosed C] {y : K}

omit [IsUltrametricDist C] [IsUltrametricDist K] [NormedAlgebra C K] in
lemma tm_ne_tm (hy : IsValTrans C y) (f : ℤ →₀ C) {n m : ℤ} (hn : f n ≠ 0) (hnm : n ≠ m) :
    tm y f n ≠ tm y f m :=
  fun h ↦ hnm (hy.eq_of_norm_mul_zpow_eq hn h)

omit [IsUltrametricDist C] in
/-- **Orthogonality**: a nonzero Laurent polynomial has a unique dominant index, at which the
norm is attained. -/
theorem exists_dom (hy : IsValTrans C y) {f : ℤ →₀ C} (hf : f ≠ 0) :
    ∃ n, f n ≠ 0 ∧ ‖lev y f‖ = tm y f n ∧ ∀ m, m ≠ n → tm y f m < tm y f n := by
  classical
  obtain ⟨n, hn, hmax⟩ := f.support.exists_max_image (tm y f) (Finsupp.support_nonempty_iff.2 hf)
  have hn0 : f n ≠ 0 := Finsupp.mem_support_iff.1 hn
  have hdom : ∀ m, m ≠ n → tm y f m < tm y f n := by
    intro m hm
    by_cases hm' : f m = 0
    · simp only [tm, hm', norm_zero, zero_mul]
      exact mul_pos (norm_pos_iff.2 hn0) (zpow_pos hy.norm_pos _)
    · exact lt_of_le_of_ne (hmax m (Finsupp.mem_support_iff.2 hm'))
        (tm_ne_tm hy f hm' hm)
  refine ⟨n, hn0, ?_, hdom⟩
  rw [lev_eq_sum, norm_sum_eq_of_dom hn fun m _ hm ↦ by
    rw [norm_mono, norm_mono]; exact hdom m hm, norm_mono]
  rfl

omit [IsUltrametricDist C] in
lemma tm_le (hy : IsValTrans C y) (f : ℤ →₀ C) (m : ℤ) : tm y f m ≤ ‖lev y f‖ := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [tm]
  obtain ⟨n, -, hn, hdom⟩ := exists_dom hy hf
  rw [hn]
  rcases eq_or_ne m n with rfl | hmn
  · exact le_rfl
  · exact (hdom m hmn).le

omit [IsUltrametricDist C] [IsUltrametricDist K] [NormedAlgebra C K] [IsAlgClosed C] in
lemma tm_nonneg (f : ℤ →₀ C) (n : ℤ) : 0 ≤ tm y f n := by
  unfold tm; positivity

/-- If `‖lev f - lev g‖ < ‖lev g‖` and `g` is dominant at `n`, then so is `f`, with the same
norm. -/
lemma dom_of_near (hy : IsValTrans C y) {f g : ℤ →₀ C} {n : ℤ} (hn : ‖lev y g‖ = tm y g n)
    (hfg : ‖lev y f - lev y g‖ < ‖lev y g‖) : ‖lev y f‖ = tm y f n := by
  have hfg' : ‖lev y (f - g)‖ < ‖lev y g‖ := by rwa [lev_sub]
  have h1 : ‖lev y f‖ = ‖lev y g‖ := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hfg.ne
    rwa [sub_add_cancel, max_eq_right hfg.le] at this
  have h2 : tm y (f - g) n < tm y g n := (tm_le hy _ n).trans_lt (hn ▸ hfg')
  have h3 : tm y f n = tm y g n := by
    have e : f n = (f - g) n + g n := by simp
    unfold tm at h2 ⊢
    rw [e]
    have hyn : 0 < ‖y‖ ^ n := zpow_pos hy.norm_pos n
    have h2' : ‖(f - g) n‖ < ‖g n‖ := lt_of_mul_lt_mul_right h2 hyn.le
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h2'.ne, max_eq_right h2'.le]
  rw [h1, hn, h3]

/-! ### Density -/

open InertiallyGenerated

omit [IsUltrametricDist K] in
/-- An inverse `x⁻¹` lies in the closure of `S` if `x sₙ = 1 - qⁿ` with `sₙ ∈ S`, `‖q‖ < 1`. -/
lemma inv_mem_closure {S : Set K} {x q : K} (hx : x ≠ 0) (hq : ‖q‖ < 1)
    (hs : ∀ N : ℕ, ∃ s ∈ S, x * s = 1 - q ^ N) : x⁻¹ ∈ closure S := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hx0 : 0 < ‖x⁻¹‖ := norm_pos_iff.2 (inv_ne_zero hx)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (div_pos hε hx0) hq
  obtain ⟨s, hsS, hs⟩ := hs N
  refine ⟨s, hsS, ?_⟩
  have e : s = x⁻¹ * (1 - q ^ N) := by rw [← hs, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  rw [dist_eq_norm, e, show x⁻¹ - x⁻¹ * (1 - q ^ N) = x⁻¹ * q ^ N by ring, norm_mul, norm_pow]
  calc ‖x⁻¹‖ * ‖q‖ ^ N < ‖x⁻¹‖ * (ε / ‖x⁻¹‖) := mul_lt_mul_of_pos_left hN hx0
    _ = ε := mul_div_cancel₀ ε hx0.ne'

variable (C) in
/-- `y` is a value-transcendental generator of `K`: `K` is the closure of `C(y)`. -/
structure IsType3 (y : K) : Prop where
  valTrans : IsValTrans C y
  genClosure_eq_top : genClosure C y = ⊤

omit [IsAlgClosed C] [IsUltrametricDist C] [IsUltrametricDist K] in
lemma inv_sub_mem (hy : IsValTrans C y) (a : C) :
    (y - algebraMap C K a)⁻¹ ∈ closure (laurent C hy.ne_zero : Set K) := by
  have hy0 := hy.ne_zero
  have hne : ‖y‖ ≠ ‖algebraMap C K a‖ := by rw [norm_algebraMap']; exact hy a
  have hx : y - algebraMap C K a ≠ 0 := fun h ↦ hne (by rw [sub_eq_zero.1 h])
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · -- `‖y‖ < ‖a‖`: `(y - a)⁻¹ = -Σ yᵏ / a^(k+1)`
    have ha0 : algebraMap C K a ≠ 0 := norm_pos_iff.1 (hy.norm_pos.trans hlt)
    refine inv_mem_closure hx (q := y / algebraMap C K a)
      (by rw [norm_div, div_lt_one (hy.norm_pos.trans hlt)]; exact hlt) fun N ↦ ?_
    refine ⟨-∑ k ∈ Finset.range N, y ^ k / algebraMap C K a ^ (k + 1),
      neg_mem (Subalgebra.sum_mem _ fun k _ ↦ ?_), ?_⟩
    · have : y ^ k / algebraMap C K a ^ (k + 1) = mono y ((a ^ (k + 1))⁻¹) k := by
        rw [mono, map_inv₀, map_pow, zpow_natCast, div_eq_inv_mul]
      rw [this]
      exact mono_mem_laurent hy0 _ _
    · induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, neg_add, mul_add, ih, div_pow, div_pow]
        field_simp [ha0]
        ring
  · -- `‖a‖ < ‖y‖`: `(y - a)⁻¹ = Σ aᵏ / y^(k+1)`
    refine inv_mem_closure hx (q := algebraMap C K a / y)
      (by rw [norm_div, div_lt_one hy.norm_pos]; exact hlt) fun N ↦ ?_
    refine ⟨∑ k ∈ Finset.range N, algebraMap C K a ^ k / y ^ (k + 1),
      Subalgebra.sum_mem _ fun k _ ↦ ?_, ?_⟩
    · have : algebraMap C K a ^ k / y ^ (k + 1) = mono y (a ^ k) (-((k : ℤ) + 1)) := by
        rw [mono, map_pow, zpow_neg, div_eq_mul_inv]
        norm_cast
      rw [this]
      exact mono_mem_laurent hy0 _ _
    · induction N with
      | zero => simp
      | succ N ih =>
        rw [Finset.sum_range_succ, mul_add, ih, div_pow, div_pow]
        field_simp [hy0]
        ring

omit [IsUltrametricDist C] [IsUltrametricDist K] in
/-- The closure of the Laurent polynomials contains `C(y)`. -/
lemma adjoin_le_closure (hy : IsValTrans C y) :
    (IntermediateField.adjoin C {y} : Set K) ⊆ closure (laurent C hy.ne_zero : Set K) := by
  set T := (laurent C hy.ne_zero).topologicalClosure
  have hT : (T : Set K) = closure (laurent C hy.ne_zero : Set K) := rfl
  have hyT : y ∈ laurent C hy.ne_zero := by
    simpa [mono] using mono_mem_laurent (C := C) hy.ne_zero 1 1
  have hpol (r : C[X]) : aeval y r ∈ T := by
    refine (laurent C hy.ne_zero).le_topologicalClosure ?_
    exact (Algebra.adjoin_le (Set.singleton_subset_iff.2 hyT))
      (Polynomial.aeval_mem_adjoin_singleton C y)
  intro x hx
  rw [SetLike.mem_coe, IntermediateField.mem_adjoin_simple_iff] at hx
  obtain ⟨r, s, rfl⟩ := hx
  rw [← hT, div_eq_mul_inv]
  refine T.mul_mem (hpol r) ?_
  have e := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits s))
  rw [← e, map_mul, aeval_C, map_multiset_prod, Multiset.map_map, mul_inv,
    ← Multiset.prod_map_inv]
  refine T.mul_mem (T.algebraMap_mem _ |> fun h ↦ by rw [← map_inv₀]; exact h) ?_
  refine Subalgebra.multiset_prod_mem _ fun z hz ↦ ?_
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hz
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C]
  exact inv_sub_mem hy a

omit [IsUltrametricDist C] [IsUltrametricDist K] in
/-- **Density of Laurent polynomials** in a value-transcendentally generated field. -/
theorem exists_lev_near (hK : IsType3 C y) (x : K) {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℤ →₀ C, ‖x - lev y f‖ < ε := by
  have hx : x ∈ closure (laurent C hK.valTrans.ne_zero : Set K) := by
    have : x ∈ genClosure C y := by rw [hK.genClosure_eq_top]; trivial
    exact closure_minimal (adjoin_le_closure hK.valTrans) isClosed_closure this
  obtain ⟨_, ⟨f, rfl⟩, hf⟩ := Metric.mem_closure_iff.1 hx ε hε
  exact ⟨f, by rwa [dist_eq_norm] at hf⟩

omit [IsUltrametricDist C] in
/-- **Dominant monomials**: every nonzero `x` is `c yⁿ` up to an element of smaller norm. -/
theorem exists_dom_mono (hK : IsType3 C y) {x : K} (hx : x ≠ 0) :
    ∃ (c : C) (n : ℤ), c ≠ 0 ∧ ‖x‖ = ‖c‖ * ‖y‖ ^ n ∧ ‖x - mono y c n‖ < ‖x‖ := by
  classical
  have hy := hK.valTrans
  obtain ⟨f, hf⟩ := exists_lev_near hK x (norm_pos_iff.2 hx)
  have hfx : ‖lev y f‖ = ‖x‖ := by
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x) (y := -(x - lev y f))
      (by rw [norm_neg]; exact hf.ne')
    rwa [norm_neg, max_eq_left hf.le, show x + -(x - lev y f) = lev y f by ring] at this
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [lev_zero, norm_zero] at hfx
    exact hx (norm_eq_zero.1 hfx.symm)
  obtain ⟨n, hn0, hn, hdom⟩ := exists_dom hy hf0
  refine ⟨f n, n, hn0, by rw [← hfx, hn]; rfl, ?_⟩
  have hrest : ‖lev y f - mono y (f n) n‖ < ‖x‖ := by
    rw [← lev_single, ← lev_sub, ← hfx, hn]
    set g := f - Finsupp.single n (f n)
    rcases eq_or_ne g 0 with hg | hg
    · rw [hg, lev_zero, norm_zero]
      exact mul_pos (norm_pos_iff.2 hn0) (zpow_pos hy.norm_pos _)
    obtain ⟨m, hm0, hm, -⟩ := exists_dom hy hg
    have hmn : m ≠ n := by
      rintro rfl
      exact hm0 (by simp [g])
    rw [hm]
    have : tm y g m = tm y f m := by simp [tm, g, hmn]
    rw [this]
    exact hdom m hmn
  have := IsUltrametricDist.norm_add_le_max (x - lev y f) (lev y f - mono y (f n) n)
  rw [show x - lev y f + (lev y f - mono y (f n) n) = x - mono y (f n) n by ring] at this
  exact this.trans_lt (max_lt hf hrest)

omit [IsUltrametricDist C] in
/-- The values of `K`: `‖x‖ = ‖c‖ ‖y‖ⁿ`. -/
theorem exists_norm_eq (hK : IsType3 C y) {x : K} (hx : x ≠ 0) :
    ∃ (c : C) (n : ℤ), c ≠ 0 ∧ ‖x‖ = ‖c‖ * ‖y‖ ^ n := by
  obtain ⟨c, n, hc, h, -⟩ := exists_dom_mono hK hx
  exact ⟨c, n, hc, h⟩

omit [IsUltrametricDist C] in
/-- An element of norm `1` is a constant up to an element of norm `< 1` (residue field `k`). -/
theorem exists_const_near (hK : IsType3 C y) {x : K} (hx : ‖x‖ = 1) :
    ∃ c : C, ‖c‖ = 1 ∧ ‖x - algebraMap C K c‖ < 1 := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  obtain ⟨c, n, hc, h, hlt⟩ := exists_dom_mono hK hx0
  have hn : n = 0 := hK.valTrans.eq_of_norm_mul_zpow_eq hc (d := 1) (m := 0) (by
    rw [← h, hx, norm_one, zpow_zero, one_mul])
  subst hn
  rw [zpow_zero, mul_one] at h
  refine ⟨c, by rw [← h, hx], ?_⟩
  rwa [mono, zpow_zero, mul_one, hx] at hlt

end Type3

end SemistableReduction
