/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussClassification

/-!
# Units of an annulus of the base: Laurent normal form along a segment of Gauss points

Blueprint §9.9, W7 layer S1. Let `K` be a field with a valuation `v` and `S` a set of radii
(units of the value monoid), thought of as the Gauss points `w_{0,s}`, `s ∈ S`, of a segment
`(r₁, r₂)` of the skeleton of `𝔸¹`. A rational function `φ` is **monomial on `S`**
(`IsMonomialOn v S φ`) if `φ = c · Xᵐ · (1 + g)` with `c ≠ 0`, `m ∈ ℤ` and `w_{0,s}(g) < 1` for
all `s ∈ S`; then `w_{0,s}(φ) = v(c) · sᵐ` (`gaussRat_eq_of_isMonomialOn`), i.e. `|φ|` is a
monomial along the segment, and the residue of `φ / (c Xᵐ)` at every `w_{0,s}` is `1`.

* the functions monomial on `S` form a subgroup of `K(X)ˣ` (`IsMonomialOn.mul`, `.inv`, `.pow`,
  `.zpow`), containing the constants, `X`, and `X - α` whenever `|α|` is not in the "range" of
  `S` (`isMonomialOn_X_sub_C`: `v(α) < s` for all `s ∈ S`, or `s < v(α)` for all `s ∈ S`);
* **`isMonomialOn_of_roots`** (`K` algebraically closed): a nonzero rational function none of
  whose zeros or poles has absolute value in the range of `S` is monomial on `S`. For an open
  annulus `r₁ < |x| < r₂` of the base containing no branch point, this is the normal form
  `φ = c xᵐ (1 + g)`, `|g| < 1` on the annulus, of units of the annulus (the tame/wild
  dichotomy of W7 starts from it: the Kummer equation `T^d = φ` is in normal form when `p ∤ m`).
-/

open Polynomial

namespace SemistableReduction

namespace AnnulusUnit

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (S : Set Γ₀ˣ)

/-- `φ` is monomial along the Gauss points `w_{0,s}`, `s ∈ S`: `φ = c · Xᵐ · (1 + g)` with
`c ≠ 0` and `w_{0,s}(g) < 1` for all `s ∈ S`. -/
def IsMonomialOn (φ : RatFunc K) : Prop :=
  ∃ c : K, c ≠ 0 ∧ ∃ m : ℤ, ∃ g : RatFunc K,
    φ = algebraMap K (RatFunc K) c * RatFunc.X ^ m * (1 + g) ∧ ∀ s ∈ S, gaussRat v 0 s g < 1

variable {v S}

@[simp]
lemma gaussRat_X (s : Γ₀ˣ) : gaussRat v 0 s RatFunc.X = s := by
  rw [← RatFunc.algebraMap_X, gaussRat_algebraMap, gauss_apply, taylor_zero,
    Gauss.sup_X]

lemma gaussRat_one_add {s : Γ₀ˣ} {g : RatFunc K} (hg : gaussRat v 0 s g < 1) :
    gaussRat v 0 s (1 + g) = 1 :=
  Valuation.map_one_add_of_lt _ hg

/-- The value of a function monomial on `S` at `w_{0,s}`, `s ∈ S`, is `v(c) · sᵐ`. -/
theorem gaussRat_eq_of_isMonomialOn {φ : RatFunc K} {c : K} {m : ℤ} {g : RatFunc K}
    (hφ : φ = algebraMap K (RatFunc K) c * RatFunc.X ^ m * (1 + g)) {s : Γ₀ˣ}
    (hg : gaussRat v 0 s g < 1) :
    gaussRat v 0 s φ = v c * (s : Γ₀) ^ m := by
  rw [hφ, map_mul, map_mul, map_zpow₀, gaussRat_X, gaussRat_algebraMap_C, gaussRat_one_add hg,
    mul_one]

lemma isMonomialOn_C {c : K} (hc : c ≠ 0) : IsMonomialOn v S (algebraMap K (RatFunc K) c) :=
  ⟨c, hc, 0, 0, by simp, fun s _ ↦ by simp⟩

lemma isMonomialOn_one : IsMonomialOn v S 1 := by
  simpa using isMonomialOn_C (v := v) (S := S) (one_ne_zero (α := K))

lemma isMonomialOn_X : IsMonomialOn v S RatFunc.X :=
  ⟨1, one_ne_zero, 1, 0, by simp, fun s _ ↦ by simp⟩

lemma IsMonomialOn.mul {φ ψ : RatFunc K} (hφ : IsMonomialOn v S φ) (hψ : IsMonomialOn v S ψ) :
    IsMonomialOn v S (φ * ψ) := by
  obtain ⟨c, hc, m, g, rfl, hg⟩ := hφ
  obtain ⟨c', hc', m', g', rfl, hg'⟩ := hψ
  refine ⟨c * c', mul_ne_zero hc hc', m + m', g + g' + g * g', ?_, fun s hs ↦ ?_⟩
  · rw [map_mul, zpow_add₀ (RatFunc.X_ne_zero)]
    ring
  · refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (lt_of_le_of_lt
      (Valuation.map_add _ _ _) (max_lt (hg s hs) (hg' s hs))) ?_)
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hg s hs) (hg' s hs).le

lemma IsMonomialOn.inv {φ : RatFunc K} (hφ : IsMonomialOn v S φ) (hφ0 : φ ≠ 0) :
    IsMonomialOn v S φ⁻¹ := by
  obtain ⟨c, hc, m, g, rfl, hg⟩ := hφ
  have h1g : 1 + g ≠ 0 := by
    rintro h
    exact hφ0 (by rw [h, mul_zero])
  refine ⟨c⁻¹, inv_ne_zero hc, -m, -g / (1 + g), ?_, fun s hs ↦ ?_⟩
  · rw [map_inv₀, zpow_neg, mul_inv, mul_inv]
    congr 1
    field_simp
    ring
  · rw [map_div₀, Valuation.map_neg, gaussRat_one_add (hg s hs), div_one]
    exact hg s hs

lemma IsMonomialOn.pow {φ : RatFunc K} (hφ : IsMonomialOn v S φ) (n : ℕ) :
    IsMonomialOn v S (φ ^ n) := by
  induction n with
  | zero => simpa using isMonomialOn_one
  | succ n ih => simpa [pow_succ] using ih.mul hφ

lemma isMonomialOn_prod {ι : Type*} (s : Multiset ι) (f : ι → RatFunc K)
    (hf : ∀ i ∈ s, IsMonomialOn v S (f i)) : IsMonomialOn v S (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using isMonomialOn_one
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons]
    exact (hf a (Multiset.mem_cons_self a s)).mul
      (ih fun i hi ↦ hf i (Multiset.mem_cons_of_mem hi))

/-- `X - α` is monomial on `S` if `|α|` lies on one side of all radii in `S`. -/
lemma isMonomialOn_X_sub_C {α : K}
    (hα : (∀ s ∈ S, v α < (s : Γ₀)) ∨ ∀ s ∈ S, (s : Γ₀) < v α) :
    IsMonomialOn v S (RatFunc.X - algebraMap K (RatFunc K) α) := by
  rcases hα with hα | hα
  · refine ⟨1, one_ne_zero, 1, -(algebraMap K (RatFunc K) α / RatFunc.X), ?_, fun s hs ↦ ?_⟩
    · have : (RatFunc.X : RatFunc K) ≠ 0 := RatFunc.X_ne_zero
      rw [map_one, one_mul, zpow_one, mul_add, mul_one, mul_neg, mul_div_cancel₀ _ this,
        sub_eq_add_neg]
    · rw [Valuation.map_neg, map_div₀, gaussRat_X, gaussRat_algebraMap_C]
      exact (div_lt_one₀ (by simp)).2 (hα s hs)
  · rcases eq_or_ne α 0 with rfl | hα0
    · simpa using isMonomialOn_X (v := v) (S := S)
    refine ⟨-α, neg_ne_zero.2 hα0, 0, -(RatFunc.X / algebraMap K (RatFunc K) α), ?_,
      fun s hs ↦ ?_⟩
    · have : algebraMap K (RatFunc K) α ≠ 0 := by simpa using hα0
      rw [map_neg, zpow_zero, mul_one]
      field_simp
      ring
    · rw [Valuation.map_neg, map_div₀, gaussRat_X, gaussRat_algebraMap_C]
      exact (div_lt_one₀ (lt_of_le_of_lt zero_le (hα s hs))).2 (hα s hs)

section AlgClosed

variable [IsAlgClosed K]

/-- A nonzero polynomial whose roots avoid the radii `S` is monomial on `S`. -/
theorem isMonomialOn_polynomial {Q : K[X]} (hQ : Q ≠ 0)
    (hroots : ∀ α ∈ Q.roots, (∀ s ∈ S, v α < (s : Γ₀)) ∨ ∀ s ∈ S, (s : Γ₀) < v α) :
    IsMonomialOn v S (algebraMap K[X] (RatFunc K) Q) := by
  have hQ' := C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := Q))
  rw [← hQ', map_mul, map_multiset_prod, Multiset.map_map]
  refine IsMonomialOn.mul ?_ (isMonomialOn_prod _ _ fun α hα ↦ ?_)
  · convert isMonomialOn_C (v := v) (S := S) (leadingCoeff_ne_zero.2 hQ) using 1
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]
  · convert isMonomialOn_X_sub_C (v := v) (S := S) (hroots α hα) using 1
    simp only [Function.comp_apply, map_sub, RatFunc.algebraMap_X]
    rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), Polynomial.algebraMap_eq]

/-- **Units of an annulus of the base.** A nonzero rational function none of whose zeros and
poles has absolute value in the range of the radii `S` is monomial on `S`:
`φ = c Xᵐ (1 + g)` with `w_{0,s}(g) < 1` for all `s ∈ S`. -/
theorem isMonomialOn_of_roots {φ : RatFunc K} (hφ : φ ≠ 0)
    (hroots : ∀ α, (α ∈ φ.num.roots ∨ α ∈ φ.denom.roots) →
      (∀ s ∈ S, v α < (s : Γ₀)) ∨ ∀ s ∈ S, (s : Γ₀) < v α) :
    IsMonomialOn v S φ := by
  have hnum : φ.num ≠ 0 := RatFunc.num_ne_zero hφ
  have hden : algebraMap K[X] (RatFunc K) φ.denom ≠ 0 := by
    simpa using φ.denom_ne_zero
  rw [← RatFunc.num_div_denom φ, div_eq_mul_inv]
  exact (isMonomialOn_polynomial hnum fun α h ↦ hroots α (Or.inl h)).mul
    ((isMonomialOn_polynomial φ.denom_ne_zero fun α h ↦ hroots α (Or.inr h)).inv hden)

end AlgClosed

end AnnulusUnit

end SemistableReduction
