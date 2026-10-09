/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Tube
import TemperedFundamentalGroups.SemistableReduction.TypeThreeLocal

/-!
# Newton polygons at a type-3 radius: continuation of values

Blueprint §9.10a (II.2). For `y ∈ F'` with characteristic polynomial `P = Σ cⱼ Tʲ` over `C(x)`:

* `UniqueDom`, `uniqueDom_mul`: if the weighted coefficients `v(pᵢ) rⁱ` of two polynomials have a
  unique maximum, so do those of the product (at the sum of the indices);
* `uniqueDom_minpoly`: for `z` in a finite extension of a complete field `K`, the weighted
  coefficients of `minpoly K z` at a radius `r ≠ ‖z‖` have a unique maximum;
* **`exists_ext_eq_of_twice`** (Newton polygon at `ρ`): if the maximum of `w_ρ(cⱼ) vʲ` is attained
  twice, then `v = ξ(y)` for an extension `ξ` of `w_ρ`;
* `twice_of_ext` (any radius): `v = w''(y)` for an extension `w''` of `w_t` attains the maximum of
  `w_t(cⱼ) vʲ` twice.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace Type3

open Gauss

section Dom

variable {K : Type*} [Field K] (v : Valuation K ℝ≥0) (r : ℝ≥0ˣ)

/-- The weighted coefficients of `p` have a unique maximum, at `a`. -/
def UniqueDom (p : K[X]) (a : ℕ) : Prop := ∀ j, j ≠ a → term v r p j < term v r p a

variable {v r}

lemma UniqueDom.pos {p : K[X]} {a : ℕ} (h : UniqueDom v r p a) : 0 < term v r p a :=
  lt_of_le_of_lt zero_le (h (a + 1) (by omega))

lemma UniqueDom.sup_eq {p : K[X]} {a : ℕ} (h : UniqueDom v r p a) :
    sup v r p = term v r p a := by
  refine le_antisymm (sup_le_iff.2 fun j ↦ ?_) (term_le_sup p a)
  rcases eq_or_ne j a with rfl | hj
  · exact le_rfl
  · exact (h j hj).le

/-- **Unique maxima multiply.** -/
theorem uniqueDom_mul {p q : K[X]} {a b : ℕ} (hp : UniqueDom v r p a) (hq : UniqueDom v r q b) :
    UniqueDom v r (p * q) (a + b) := by
  classical
  have hM : ∀ i j : ℕ, (i, j) ≠ (a, b) →
      term v r p i * term v r q j < term v r p a * term v r q b := by
    intro i j hij
    rcases eq_or_ne i a with rfl | hi
    · have hj : j ≠ b := fun h ↦ hij (by rw [h])
      exact mul_lt_mul_of_pos_left (hq j hj) hp.pos
    · rcases eq_or_ne j b with rfl | hj
      · exact mul_lt_mul_of_pos_right (hp i hi) hq.pos
      · exact mul_lt_mul'' (hp i hi) (hq j hj) zero_le zero_le
  have hterm : ∀ k : ℕ, term v r (p * q) k = v (∑ x ∈ Finset.HasAntidiagonal.antidiagonal k,
      p.coeff x.1 * q.coeff x.2) * (r : ℝ≥0) ^ k := fun k ↦ by rw [term, coeff_mul]
  have hsum_le : ∀ k : ℕ, ∀ x ∈ Finset.HasAntidiagonal.antidiagonal k,
      v (p.coeff x.1 * q.coeff x.2) * (r : ℝ≥0) ^ k = term v r p x.1 * term v r q x.2 := by
    intro k x hx
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    rw [term, term, map_mul, ← hx, pow_add]
    ring
  -- the value at `a + b`
  have hab : term v r (p * q) (a + b) = term v r p a * term v r q b := by
    rw [hterm]
    have hmem : (a, b) ∈ Finset.HasAntidiagonal.antidiagonal (a + b) :=
      Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
    rw [← Finset.add_sum_erase _ _ hmem]
    have hrpos : (0 : ℝ≥0) < (r : ℝ≥0) ^ (a + b) := pow_pos (pos_iff_ne_zero.2 r.ne_zero) _
    have hlt : v (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (a + b)).erase (a, b),
        p.coeff x.1 * q.coeff x.2) < v (p.coeff a * q.coeff b) := by
      have h0 : 0 < v (p.coeff a * q.coeff b) := by
        have := hsum_le (a + b) (a, b) hmem
        have hpos := mul_pos hp.pos hq.pos
        rw [← this] at hpos
        exact pos_of_mul_pos_left hpos zero_le
      refine (Valuation.map_sum_lt v h0.ne' fun x hx ↦ ?_)
      obtain ⟨hne, hx⟩ := Finset.mem_erase.1 hx
      have h1 := hsum_le (a + b) x hx
      have h2 := hsum_le (a + b) (a, b) hmem
      have h3 := hM x.1 x.2 hne
      rw [← h1, ← h2] at h3
      exact lt_of_mul_lt_mul_right h3 zero_le
    change v (p.coeff a * q.coeff b + _) * _ = _
    rw [Valuation.map_add_eq_of_lt_left _ hlt]
    exact hsum_le (a + b) (a, b) hmem
  intro k hk
  rw [hab]
  rw [hterm]
  calc v (∑ x ∈ Finset.HasAntidiagonal.antidiagonal k, p.coeff x.1 * q.coeff x.2) * (r : ℝ≥0) ^ k
      ≤ (Finset.HasAntidiagonal.antidiagonal k).sup (fun x ↦ v (p.coeff x.1 * q.coeff x.2)) *
          (r : ℝ≥0) ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ zero_le
        exact Valuation.map_sum_le v fun x hx ↦
          Finset.le_sup (f := fun x ↦ v (p.coeff x.1 * q.coeff x.2)) hx
    _ < term v r p a * term v r q b := by
        rcases (Finset.HasAntidiagonal.antidiagonal k).eq_empty_or_nonempty with he | hne
        · rw [he, Finset.sup_empty, bot_eq_zero', zero_mul]
          exact mul_pos hp.pos hq.pos
        obtain ⟨x, hx, hxmax⟩ := Finset.exists_max_image _
          (fun x ↦ v (p.coeff x.1 * q.coeff x.2)) hne
        have hsup : (Finset.HasAntidiagonal.antidiagonal k).sup
            (fun x ↦ v (p.coeff x.1 * q.coeff x.2)) =
            v (p.coeff x.1 * q.coeff x.2) :=
          le_antisymm (Finset.sup_le hxmax)
            (Finset.le_sup (f := fun x ↦ v (p.coeff x.1 * q.coeff x.2)) hx)
        rw [hsup, hsum_le k x hx]
        refine hM x.1 x.2 fun h ↦ hk ?_
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
        have h' := Prod.mk.inj h
        rw [← hx, h'.1, h'.2]

/-- Powers of a polynomial with a unique maximum. -/
theorem uniqueDom_pow {p : K[X]} {a : ℕ} (hp : UniqueDom v r p a) (n : ℕ) :
    UniqueDom v r (p ^ n) (n * a) := by
  induction n with
  | zero =>
    intro j hj
    simp only [pow_zero, zero_mul] at hj ⊢
    simp [term, coeff_one, hj]
  | succ n ih =>
    rw [pow_succ, show (n + 1) * a = n * a + a by ring]
    exact uniqueDom_mul ih hp

/-- Finite products of polynomials with unique maxima. -/
theorem uniqueDom_prod {ι : Type*} (s : Finset ι) (p : ι → K[X]) (a : ι → ℕ)
    (h : ∀ i ∈ s, UniqueDom v r (p i) (a i)) :
    UniqueDom v r (∏ i ∈ s, p i) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro j hj
    simp only [Finset.prod_empty, Finset.sum_empty] at hj ⊢
    simp [term, coeff_one, hj]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact uniqueDom_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

end Dom

section Minpoly

variable {K L : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [NormedField L] [NormedAlgebra K L] [FiniteDimensional K L]

/-- The coefficients of the minimal polynomial of `z` are bounded by the powers of `‖z‖`. -/
lemma norm_coeff_minpoly_le (z : L) {j : ℕ} (hj : j < (minpoly K z).natDegree) :
    ‖(minpoly K z).coeff j‖ ≤ ‖z‖ ^ ((minpoly K z).natDegree - j) := by
  have hs : ‖z‖ = spectralValue (minpoly K z) := NormedAlgebra.norm_eq_spectralNorm K z
  have h1 : spectralValueTerms (minpoly K z) j ≤ ‖z‖ :=
    hs ▸ le_ciSup (spectralValueTerms_bddAbove _) j
  rw [spectralValueTerms_of_lt_natDegree _ hj] at h1
  have hpos : (0 : ℝ) < ((minpoly K z).natDegree - j : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have h2 := Real.rpow_le_rpow (by positivity) h1 hpos.le
  have hne : ((minpoly K z).natDegree - j : ℝ) ≠ 0 := by
    rw [← Nat.cast_sub hj.le]; exact hpos.ne'
  rw [← Real.rpow_mul (norm_nonneg _), show (1 / ((minpoly K z).natDegree - j : ℝ)) *
      (((minpoly K z).natDegree - j : ℕ) : ℝ) = 1 by
    rw [Nat.cast_sub hj.le]; field_simp, Real.rpow_one, Real.rpow_natCast] at h2
  exact h2

/-- The constant coefficient of the minimal polynomial has norm `‖z‖ ^ deg`. -/
lemma norm_coeff_zero_minpoly (z : L) :
    ‖(minpoly K z).coeff 0‖ = ‖z‖ ^ (minpoly K z).natDegree := by
  have hdeg : 0 < (minpoly K z).natDegree :=
    minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral z)
  have hs : ‖z‖ = ‖(minpoly K z).coeff 0‖ ^ (1 / (minpoly K z).natDegree : ℝ) := by
    rw [NormedAlgebra.norm_eq_spectralNorm K z]
    exact spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow K L z
  rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel
    (by exact_mod_cast hdeg.ne'), Real.rpow_one]

/-- **Pure factors**: at a radius `r ≠ ‖z‖` the weighted coefficients of `minpoly K z` have a
unique maximum. -/
theorem exists_uniqueDom_minpoly (z : L) {r : ℝ≥0ˣ} (hr : ((r : ℝ≥0) : ℝ) ≠ ‖z‖) :
    ∃ a, UniqueDom (NormedField.valuation (K := K)) r (minpoly K z) a := by
  set P := minpoly K z
  set n := P.natDegree
  have hmon : P.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral z)
  have hn : 0 < n := minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral z)
  have hterm : ∀ j, ((term (NormedField.valuation (K := K)) r P j : ℝ≥0) : ℝ) = ‖P.coeff j‖ *
      ((r : ℝ≥0) : ℝ) ^ j := fun j ↦ by simp [term, NormedField.valuation_apply]
  have hr0 : (0 : ℝ) < ((r : ℝ≥0) : ℝ) := by
    have := r.ne_zero
    positivity
  rcases lt_or_gt_of_ne hr with hlt | hgt
  · -- `r < ‖z‖`: the constant term dominates
    refine ⟨0, fun j hj ↦ ?_⟩
    rw [← NNReal.coe_lt_coe, hterm, hterm, norm_coeff_zero_minpoly, pow_zero, mul_one]
    rcases lt_or_ge n j with hjn | hjn
    · rw [coeff_eq_zero_of_natDegree_lt hjn, norm_zero, zero_mul]
      exact pow_pos (hr0.trans hlt) n
    rcases hjn.lt_or_eq with hjn | rfl
    · calc ‖P.coeff j‖ * ((r : ℝ≥0) : ℝ) ^ j ≤ ‖z‖ ^ (n - j) * ((r : ℝ≥0) : ℝ) ^ j :=
            mul_le_mul_of_nonneg_right (norm_coeff_minpoly_le z hjn) (by positivity)
        _ < ‖z‖ ^ (n - j) * ‖z‖ ^ j :=
            mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hlt hr0.le (by omega))
              (pow_pos (hr0.trans hlt) _)
        _ = ‖z‖ ^ n := by rw [← pow_add, Nat.sub_add_cancel hjn.le]
    · rw [hmon.coeff_natDegree, norm_one, one_mul]
      exact pow_lt_pow_left₀ hlt hr0.le (by omega)
  · -- `‖z‖ < r`: the leading term dominates
    refine ⟨n, fun j hj ↦ ?_⟩
    rw [← NNReal.coe_lt_coe, hterm, hterm, hmon.coeff_natDegree, norm_one, one_mul]
    rcases lt_or_gt_of_ne hj with hjn | hjn
    · calc ‖P.coeff j‖ * ((r : ℝ≥0) : ℝ) ^ j ≤ ‖z‖ ^ (n - j) * ((r : ℝ≥0) : ℝ) ^ j :=
            mul_le_mul_of_nonneg_right (norm_coeff_minpoly_le z hjn) (by positivity)
        _ < ((r : ℝ≥0) : ℝ) ^ (n - j) * ((r : ℝ≥0) : ℝ) ^ j :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hgt (norm_nonneg _) (by omega))
              (pow_pos hr0 _)
        _ = ((r : ℝ≥0) : ℝ) ^ n := by rw [← pow_add, Nat.sub_add_cancel hjn.le]
    · rw [coeff_eq_zero_of_natDegree_lt hjn, norm_zero, zero_mul]
      exact pow_pos hr0 n

end Minpoly

section AtRho

open GaussStability LocalGlobal TubeCount

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- **Newton polygon at a Gauss point.** If the weighted coefficients of the characteristic
polynomial of `y` at the radius `v` (for the Gauss valuation `w_{0,ρ}`) do not have a unique
maximum, then `v = ξ(y)` for some extension `ξ` of `w_{0,ρ}`. -/
theorem exists_ext_eq_of_not_uniqueDom {ρ : ℝ≥0ˣ} (y : F') (v : ℝ≥0ˣ)
    (h : ∀ a, ¬ UniqueDom (w ρ) v (normPoly (RatFunc C) y) a) :
    ∃ ξ : GaussExtension (0 : C) ρ F', ξ.1 y = v := by
  classical
  by_contra! hno
  haveI : Infinite (RatFunc C) :=
    Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
  set K := UniformSpace.Completion (GaussField (0 : C) ρ)
  set e : RatFunc C ≃+* GaussField (0 : C) ρ := (WithAbs.equiv _).symm
  haveI : Infinite (GaussField (0 : C) ρ) := Infinite.of_injective e e.injective
  set ι : RatFunc C →+* K := (algebraMap (GaussField (0 : C) ρ) K).comp e.toRingHom
  have hι : ∀ c : RatFunc C, NormedField.valuation (K := K) (ι c) = w ρ c := fun c ↦ by
    ext
    simp only [NormedField.valuation_apply, coe_nnnorm, ι, RingHom.comp_apply]
    erw [DenseCompletion.algebraMap_completion, UniformSpace.Completion.norm_coe]
    rfl
  have hmap : (normPoly (RatFunc C) y).map ι =
      ∏ g : Factor (GaussField (0 : C) ρ) K F', normPoly K (toLocal g y) := by
    rw [← normPoly_map_eq_prod (F := GaussField (0 : C) ρ) (K := K), ← Polynomial.map_map,
      normPoly_map_ringEquiv e (by ext; rfl) y]
    rfl
  -- every factor has a unique maximum
  have hfac : ∀ g : Factor (GaussField (0 : C) ρ) K F', ∃ a,
      UniqueDom (NormedField.valuation (K := K)) v (normPoly K (toLocal g y)) a := by
    intro g
    have hne : ((v : ℝ≥0) : ℝ) ≠ ‖toLocal g y‖ := by
      intro hv
      apply hno (factorEquiv g)
      rw [factorEquiv_apply_val, extValuation_apply]
      exact NNReal.eq (by rw [coe_nnnorm, ← hv])
    obtain ⟨a, ha⟩ := exists_uniqueDom_minpoly (K := K) (toLocal g y) hne
    exact ⟨_, uniqueDom_pow ha _⟩
  choose a ha using hfac
  have hprod := uniqueDom_prod Finset.univ _ a fun g _ ↦ ha g
  rw [← hmap] at hprod
  refine h (∑ g, a g) fun j hj ↦ ?_
  have := hprod j hj
  simp only [term, coeff_map, hι] at this
  exact this

omit [Algebra.IsSeparable (RatFunc C) F'] in
/-- **The value at an extension attains the maximum twice** (any radius): `P(y) = 0`. -/
theorem not_uniqueDom_of_ext {t : ℝ≥0ˣ} (y : F') (ξ : GaussExtension (0 : C) t F')
    (hy : ξ.1 y ≠ 0) (a : ℕ) :
    ¬ UniqueDom (w t) (Units.mk0 (ξ.1 y) hy) (normPoly (RatFunc C) y) a := by
  classical
  intro hU
  have hP0 : aeval y (normPoly (RatFunc C) y) = 0 := by
    rw [TubeCount.normPoly, map_pow, minpoly.aeval, zero_pow Module.finrank_pos.ne']
  set P := normPoly (RatFunc C) y
  have hterm : ∀ j, ξ.1 (algebraMap (RatFunc C) F' (P.coeff j) * y ^ j) =
      term (w t) (Units.mk0 (ξ.1 y) hy) P j := fun j ↦ by
    rw [map_mul, map_pow, ← Valuation.comap_apply, ξ.2]
    rfl
  set n := P.natDegree
  have ha : a ≤ n := by
    by_contra! han
    have := hU.pos
    rw [term, coeff_eq_zero_of_natDegree_lt han, map_zero, zero_mul] at this
    exact lt_irrefl 0 this
  rw [aeval_eq_sum_range] at hP0
  have hmem : a ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  rw [← Finset.add_sum_erase _ _ hmem] at hP0
  have hlt : ξ.1 (∑ j ∈ (Finset.range (n + 1)).erase a, P.coeff j • y ^ j) <
      ξ.1 (P.coeff a • y ^ a) := by
    have h0 : ξ.1 (P.coeff a • y ^ a) ≠ 0 := by
      rw [Algebra.smul_def, hterm]; exact hU.pos.ne'
    refine Valuation.map_sum_lt _ h0 fun j hj ↦ ?_
    rw [Algebra.smul_def, Algebra.smul_def, hterm, hterm]
    exact hU j (Finset.ne_of_mem_erase hj)
  have := congrArg ξ.1 hP0
  rw [Valuation.map_add_eq_of_lt_left _ hlt, map_zero, Algebra.smul_def, hterm] at this
  exact hU.pos.ne' this

end AtRho

end Type3

end SemistableReduction
