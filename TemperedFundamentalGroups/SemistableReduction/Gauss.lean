/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Gauss valuations

Blueprint §9.3, W1. Let `K` be a field with a valuation `v : Valuation K Γ₀` (multiplicative
convention), `a ∈ K` and `r ∈ Γ₀ˣ`. The **Gauss valuation** of radius `r` around `a` is
`w (Σ cᵢ (X - a) ^ i) = max_i v(cᵢ) * r ^ i`.

* `Gauss.sup v r p = max_i v(pᵢ) * r ^ i`, and `Gauss.sup_mul` (the Gauss lemma: the leading
  term argument at the smallest index attaining the maximum);
* `gauss₀ v r : Valuation K[X] Γ₀`, the Gauss valuation around `0`;
* `gauss v a r : Valuation K[X] Γ₀`, around `a` (via the Taylor shift `p ↦ p(X + a)`);
* `gaussRat v a r : Valuation (RatFunc K) Γ₀`, its extension to the rational function field; it
  extends `v` (`gaussRat_algebraMap_C`, `Valuation.HasExtension`).
-/

open Polynomial

namespace SemistableReduction

namespace Gauss

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (r : Γ₀ˣ)

/-- The weighted coefficient `v(pᵢ) * r ^ i`. -/
def term (p : K[X]) (i : ℕ) : Γ₀ := v (p.coeff i) * (r : Γ₀) ^ i

/-- The maximum `max_i v(pᵢ) * r ^ i` of the weighted coefficients. -/
def sup (p : K[X]) : Γ₀ := p.support.sup (term v r p)

variable {v r}

lemma term_le_sup (p : K[X]) (i : ℕ) : term v r p i ≤ sup v r p := by
  by_cases h : i ∈ p.support
  · exact Finset.le_sup (f := term v r p) h
  · rw [term, notMem_support_iff.1 h, map_zero, zero_mul]
    exact zero_le

lemma sup_le_iff {p : K[X]} {g : Γ₀} : sup v r p ≤ g ↔ ∀ i, term v r p i ≤ g :=
  ⟨fun h i ↦ (term_le_sup p i).trans h, fun h ↦ Finset.sup_le fun i _ ↦ h i⟩

lemma exists_term_eq_sup (p : K[X]) : ∃ i, term v r p i = sup v r p := by
  rcases p.support.eq_empty_or_nonempty with h | h
  · refine ⟨0, ?_⟩
    rw [support_eq_empty] at h
    simp [h, term, sup, bot_eq_zero]
  · obtain ⟨i, -, he⟩ := Finset.exists_mem_eq_sup _ h (term v r p)
    exact ⟨i, he.symm⟩

lemma sup_eq_of_term_eq {p q : K[X]} {s : Γ₀ˣ} (h : ∀ i, term v r p i = term v s q i) :
    sup v r p = sup v s q :=
  le_antisymm (sup_le_iff.2 fun i ↦ (h i).trans_le (term_le_sup q i))
    (sup_le_iff.2 fun i ↦ (h i).symm.trans_le (term_le_sup p i))

@[simp]
lemma sup_zero : sup v r 0 = 0 := by simp [sup, bot_eq_zero]

lemma term_eq_zero_iff {p : K[X]} {i : ℕ} : term v r p i = 0 ↔ p.coeff i = 0 := by
  simp [term, r.ne_zero]

@[simp]
lemma sup_eq_zero_iff {p : K[X]} : sup v r p = 0 ↔ p = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ sup_zero⟩
  by_contra hp
  have := term_le_sup (v := v) (r := r) p p.natDegree
  rw [h, le_zero_iff, term_eq_zero_iff, coeff_natDegree, leadingCoeff_eq_zero] at this
  exact hp this

@[simp]
lemma sup_C (c : K) : sup v r (C c) = v c := by
  apply le_antisymm
  · refine sup_le_iff.2 fun i ↦ ?_
    rcases eq_or_ne i 0 with rfl | hi
    · simp [term]
    · simp [term, coeff_C, hi]
  · simpa [term] using term_le_sup (v := v) (r := r) (C c) 0

lemma sup_add_le (p q : K[X]) : sup v r (p + q) ≤ max (sup v r p) (sup v r q) := by
  refine sup_le_iff.2 fun i ↦ ?_
  rcases v.map_add' (p.coeff i) (q.coeff i) with h | h
  · exact (mul_le_mul_left h _ |>.trans (term_le_sup p i)).trans (le_max_left _ _)
      |> (by simpa [term] using ·)
  · exact (mul_le_mul_left h _ |>.trans (term_le_sup q i)).trans (le_max_right _ _)
      |> (by simpa [term] using ·)

lemma sup_mul_le (p q : K[X]) : sup v r (p * q) ≤ sup v r p * sup v r q := by
  refine sup_le_iff.2 fun n ↦ ?_
  have hr : (0 : Γ₀) < (r : Γ₀) ^ n := pow_pos (zero_lt_iff.2 r.ne_zero) n
  rw [term, ← le_mul_inv_iff₀ hr, coeff_mul]
  refine v.map_sum_le fun x hx ↦ ?_
  rw [le_mul_inv_iff₀ hr, ← Finset.HasAntidiagonal.mem_antidiagonal.1 hx, pow_add, map_mul,
    mul_mul_mul_comm]
  exact mul_le_mul' (term_le_sup p x.1) (term_le_sup q x.2)

/-- Strict inequality for products in a linearly ordered group with zero. -/
private lemma mul_lt_mul_aux {a b c d : Γ₀} (h : a < b) (h' : c ≤ d) (hd : d ≠ 0) :
    a * c < b * d :=
  (mul_le_mul_right h' a).trans_lt ((mul_lt_mul_iff_left₀ (zero_lt_iff.2 hd)).2 h)

/-- **Gauss's lemma**: the Gauss norm is multiplicative. -/
lemma sup_mul (p q : K[X]) : sup v r (p * q) = sup v r p * sup v r q := by
  refine le_antisymm (sup_mul_le p q) ?_
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  have hp' : sup v r p ≠ 0 := by simpa using hp
  have hq' : sup v r q ≠ 0 := by simpa using hq
  classical
  let i₀ := Nat.find (exists_term_eq_sup (v := v) (r := r) p)
  let j₀ := Nat.find (exists_term_eq_sup (v := v) (r := r) q)
  have hi₀ : term v r p i₀ = sup v r p := Nat.find_spec (exists_term_eq_sup p)
  have hj₀ : term v r q j₀ = sup v r q := Nat.find_spec (exists_term_eq_sup q)
  have hlt_p : ∀ i < i₀, term v r p i < sup v r p := fun i hi ↦
    lt_of_le_of_ne (term_le_sup p i) (Nat.find_min (exists_term_eq_sup p) hi)
  have hlt_q : ∀ j < j₀, term v r q j < sup v r q := fun j hj ↦
    lt_of_le_of_ne (term_le_sup q j) (Nat.find_min (exists_term_eq_sup q) hj)
  refine le_trans ?_ (term_le_sup (p * q) (i₀ + j₀))
  have hr : (0 : Γ₀) < (r : Γ₀) ^ (i₀ + j₀) := pow_pos (zero_lt_iff.2 r.ne_zero) _
  have hmem : (i₀, j₀) ∈ Finset.HasAntidiagonal.antidiagonal (i₀ + j₀) :=
    Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
  -- the main term
  have hmain : v (p.coeff i₀ * q.coeff j₀) * (r : Γ₀) ^ (i₀ + j₀) = sup v r p * sup v r q := by
    rw [← hi₀, ← hj₀, term, term, map_mul, pow_add, mul_mul_mul_comm]
  have hne : v (p.coeff i₀ * q.coeff j₀) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmain
    exact mul_ne_zero hp' hq' hmain.symm
  have hrest : v (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal (i₀ + j₀)).erase (i₀, j₀),
      p.coeff x.1 * q.coeff x.2) < v (p.coeff i₀ * q.coeff j₀) := by
    refine v.map_sum_lt hne fun x hx ↦ ?_
    obtain ⟨hx0, hx⟩ := Finset.mem_erase.1 hx
    rw [← mul_lt_mul_iff_left₀ hr, hmain, ← Finset.HasAntidiagonal.mem_antidiagonal.1 hx,
      pow_add, map_mul,
      mul_mul_mul_comm]
    change term v r p x.1 * term v r q x.2 < _
    rcases lt_trichotomy x.1 i₀ with h1 | h1 | h1
    · exact mul_lt_mul_aux (hlt_p _ h1) (term_le_sup q _) hq'
    · have h2 : x.2 = j₀ := by
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        omega
      exact absurd (Prod.ext h1 h2) hx0
    · have h2 : x.2 < j₀ := by
        have := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
        omega
      rw [mul_comm (term v r p x.1), mul_comm (sup v r p)]
      exact mul_lt_mul_aux (hlt_q _ h2) (term_le_sup p _) hp'
  rw [term, coeff_mul, ← Finset.add_sum_erase _ _ hmem, v.map_add_eq_of_lt_left hrest, hmain]

end Gauss

open Gauss

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (a : K) (r : Γ₀ˣ)

/-- The Gauss valuation `Σ cᵢ X ^ i ↦ max_i v(cᵢ) * r ^ i` on `K[X]`. -/
noncomputable def gauss₀ : Valuation K[X] Γ₀ where
  toFun := Gauss.sup v r
  map_zero' := sup_zero
  map_one' := by simpa using sup_C (v := v) (r := r) 1
  map_mul' := sup_mul
  map_add_le_max' := sup_add_le

lemma gauss₀_apply (p : K[X]) : gauss₀ v r p = Gauss.sup v r p := rfl

/-- The Gauss valuation `Σ cᵢ (X - a) ^ i ↦ max_i v(cᵢ) * r ^ i` on `K[X]` of radius `r` around
`a`: the Gauss valuation around `0` of the Taylor shift `p(X + a)`. -/
noncomputable def gauss : Valuation K[X] Γ₀ :=
  (gauss₀ v r).comap (taylorEquiv a).toRingEquiv.toRingHom

lemma gauss_apply (p : K[X]) : gauss v a r p = Gauss.sup v r (taylor a p) := rfl

@[simp]
lemma gauss_C (c : K) : gauss v a r (C c) = v c := by
  simp [gauss_apply]

lemma gauss_eq_zero_iff {p : K[X]} : gauss v a r p = 0 ↔ p = 0 := by
  rw [gauss_apply, sup_eq_zero_iff]
  exact (taylorEquiv a).map_eq_zero_iff

/-- The Gauss valuation of `Q((X - a) / c)` is `max_i v(Qᵢ)` when `v(c) = r`. -/
lemma gauss_comp (c : K) (hc : v c = r) (Q : K[X]) :
    gauss v a r (Q.comp (C c⁻¹ * (X - C a))) = Gauss.sup v 1 Q := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact r.ne_zero (by simp [← hc])
  rw [gauss_apply]
  have : taylor a (Q.comp (C c⁻¹ * (X - C a))) = Q.comp (C c⁻¹ * X) := by
    rw [taylor_apply, comp_assoc]
    simp
  rw [this]
  refine sup_eq_of_term_eq fun i ↦ ?_
  simp only [term, comp_C_mul_X_coeff, map_mul, map_pow, map_inv₀, hc, Units.val_one, one_pow,
    mul_one]
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (by simp), one_pow, mul_one]

/-- The Gauss valuation of radius `r` around `a`, extended to the rational function field. -/
noncomputable def gaussRat : Valuation (RatFunc K) Γ₀ :=
  (gauss v a r).extendToLocalization (S := nonZeroDivisors K[X])
    (fun p hp ↦ by
      simpa [Valuation.mem_supp_iff, gauss_eq_zero_iff] using nonZeroDivisors.ne_zero hp)
    (RatFunc K)

@[simp]
lemma gaussRat_algebraMap (p : K[X]) :
    gaussRat v a r (algebraMap K[X] (RatFunc K) p) = gauss v a r p :=
  Valuation.extendToLocalization_apply_map_apply _ _ _ _

@[simp]
lemma gaussRat_algebraMap_C (c : K) : gaussRat v a r (algebraMap K (RatFunc K) c) = v c := by
  rw [IsScalarTower.algebraMap_apply K K[X] (RatFunc K), gaussRat_algebraMap, algebraMap_eq,
    gauss_C]

instance gaussRat_hasExtension : v.HasExtension (gaussRat v a r) :=
  ⟨fun x y ↦ by rw [Valuation.comap_apply, Valuation.comap_apply, gaussRat_algebraMap_C,
    gaussRat_algebraMap_C]⟩


/-! ### Residue fields of valuation extensions -/

section Residue

open IsLocalRing

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {v : Valuation K Γ₀} {w : Valuation L Γ₁} [v.HasExtension w]

namespace ValuationResidue

/-- An element of the valuation ring has nonzero residue iff it has valuation `1`. -/
lemma residue_ne_zero_iff (x : w.valuationSubring) :
    residue w.valuationSubring x ≠ 0 ↔ w x = 1 := by
  rw [residue_ne_zero_iff_isUnit,
    (Valuation.valuationSubring.integers w).isUnit_iff_valuation_eq_one]
  rfl

/-- The residue of a polynomial expression is the reduced polynomial evaluated at the residue. -/
lemma residue_aeval (P : v.valuationSubring[X]) (y : w.valuationSubring) :
    residue w.valuationSubring (aeval y P) =
      aeval (residue w.valuationSubring y) (P.map (residue v.valuationSubring)) := by
  rw [aeval_def, aeval_def, eval₂_map, hom_eval₂]
  rfl

lemma coe_aeval (P : v.valuationSubring[X]) (y : w.valuationSubring) :
    ((aeval y P : w.valuationSubring) : L) =
      aeval (y : L) (P.map (algebraMap v.valuationSubring K)) := by
  rw [aeval_map_algebraMap]
  exact (aeval_algebraMap_apply L y P).symm

/-- A polynomial with integral coefficients lifts to the valuation ring. -/
lemma exists_map_eq (Q : K[X]) (hQ : ∀ i, v (Q.coeff i) ≤ 1) :
    ∃ P : v.valuationSubring[X], P.map (algebraMap v.valuationSubring K) = Q := by
  rw [← mem_lifts, lifts_iff_coeff_lifts]
  exact fun n ↦ ⟨⟨Q.coeff n, hQ n⟩, rfl⟩

end ValuationResidue

end Residue

namespace Gauss

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {r : Γ₀ˣ}

@[simp]
lemma sup_X : sup v r X = r := by
  apply le_antisymm
  · refine sup_le_iff.2 fun i ↦ ?_
    rcases eq_or_ne i 1 with rfl | hi
    · simp [term]
    · simp [term, coeff_X, Ne.symm hi]
  · simpa [term] using term_le_sup (v := v) (r := r) X 1

lemma sup_one_map_le (P : v.valuationSubring[X]) :
    sup v 1 (P.map (algebraMap v.valuationSubring K)) ≤ 1 :=
  sup_le_iff.2 fun i ↦ by
    rw [term, coeff_map, Units.val_one, one_pow, mul_one]
    exact (P.coeff i).2

lemma sup_one_map_eq (P : v.valuationSubring[X])
    (hP : P.map (IsLocalRing.residue v.valuationSubring) ≠ 0) :
    sup v 1 (P.map (algebraMap v.valuationSubring K)) = 1 := by
  refine le_antisymm (sup_one_map_le P) ?_
  obtain ⟨i, hi⟩ : ∃ i, (P.map (IsLocalRing.residue v.valuationSubring)).coeff i ≠ 0 := by
    by_contra! h
    exact hP (Polynomial.ext fun i ↦ by simpa using h i)
  rw [coeff_map] at hi
  have := (ValuationResidue.residue_ne_zero_iff (P.coeff i)).1 hi
  simpa [term, this] using term_le_sup (v := v) (r := 1) (P.map (algebraMap _ K)) i

end Gauss

section GaussResidue

open IsLocalRing ValuationResidue Gauss

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation K Γ₀) (a : K) (r : Γ₀ˣ) {c : K}

/-- The linear polynomial `(X - a) / c`. -/
noncomputable def gaussLin (a c : K) : K[X] := C c⁻¹ * (X - C a)

variable {v a r}

lemma gaussRat_aeval_gaussLin (hc : v c = r) (Q : K[X]) :
    gaussRat v a r (aeval (algebraMap K[X] (RatFunc K) (gaussLin a c)) Q) = Gauss.sup v 1 Q := by
  rw [aeval_algebraMap_apply, ← comp_eq_aeval, gaussRat_algebraMap, gaussLin, gauss_comp v a r c hc]

variable (v a r) in
/-- The element `(X - a) / c` of the valuation ring of the Gauss valuation, where `v(c) = r`. -/
noncomputable def gaussGen (hc : v c = r) : (gaussRat v a r).valuationSubring :=
  ⟨algebraMap K[X] (RatFunc K) (gaussLin a c), by
    rw [Valuation.mem_valuationSubring_iff, ← aeval_X (R := K)
      (algebraMap K[X] (RatFunc K) (gaussLin a c)), gaussRat_aeval_gaussLin hc, sup_X,
      Units.val_one]⟩

lemma coe_gaussGen (hc : v c = r) :
    (gaussGen v a r hc : RatFunc K) = algebraMap K[X] (RatFunc K) (gaussLin a c) := rfl

/-- **W1** (residue field, transcendence): the residue `x̄` of `(X - a) / c` (`v(c) = r`) is
transcendental over the residue field of `v`. -/
theorem transcendental_residue_gaussGen (hc : v c = r) :
    Transcendental (ResidueField v.valuationSubring)
      (residue (gaussRat v a r).valuationSubring (gaussGen v a r hc)) := by
  rintro ⟨Pbar, hPbar, hroot⟩
  obtain ⟨P, rfl⟩ := map_surjective _ (residue_surjective (R := v.valuationSubring)) Pbar
  rw [← residue_aeval] at hroot
  refine (residue_ne_zero_iff _).2 ?_ hroot
  rw [coe_aeval, coe_gaussGen, gaussRat_aeval_gaussLin hc, sup_one_map_eq P hPbar]

/-- **W1** (residue field, generation): the residue field of the Gauss valuation is generated
over the residue field of `v` by the residue of `(X - a) / c` (`v(c) = r`). Together with
`transcendental_residue_gaussGen`, it is the rational function field `κ(v)(x̄)`. -/
theorem adjoin_residue_gaussGen_eq_top (hc : v c = r) :
    IntermediateField.adjoin (ResidueField v.valuationSubring)
      {residue (gaussRat v a r).valuationSubring (gaussGen v a r hc)} = ⊤ := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact r.ne_zero (by simp [← hc])
  rw [eq_top_iff]
  rintro z -
  obtain ⟨φ, rfl⟩ := residue_surjective z
  obtain ⟨f, g, hg, hfg⟩ := IsFractionRing.div_surjective (A := K[X]) (φ : RatFunc K)
  have hg0 : g ≠ 0 := nonZeroDivisors.ne_zero hg
  set ℓ := gaussLin a c
  set ℓ' := algebraMap K[X] (RatFunc K) ℓ
  have hA : ∀ Q : K[X], algebraMap K[X] (RatFunc K) (Q.comp ℓ) = aeval ℓ' Q := fun Q ↦ by
    rw [comp_eq_aeval, aeval_algebraMap_apply]
  have hσ : (C c * X + C a).comp ℓ = X := by
    simp only [ℓ, gaussLin, add_comp, mul_comp, C_comp, X_comp]
    rw [← mul_assoc, ← C_mul, mul_inv_cancel₀ hc0, C_1, one_mul, sub_add_cancel]
  set F := f.comp (C c * X + C a)
  set G := g.comp (C c * X + C a)
  have hf : algebraMap K[X] (RatFunc K) f = aeval ℓ' F := by
    rw [← hA, comp_assoc, hσ, comp_X]
  have hg' : algebraMap K[X] (RatFunc K) g = aeval ℓ' G := by
    rw [← hA, comp_assoc, hσ, comp_X]
  have hG0 : G ≠ 0 := by
    rintro hG
    rw [hG, map_zero] at hg'
    exact hg0 (IsFractionRing.injective K[X] (RatFunc K) (by simpa using hg'))
  obtain ⟨j, hj⟩ := exists_term_eq_sup (v := v) (r := 1) G
  set d := G.coeff j
  have hvd : v d = Gauss.sup v 1 G := by simpa [term] using hj
  have hd0 : d ≠ 0 := by
    intro h
    rw [h, map_zero, eq_comm, sup_eq_zero_iff] at hvd
    exact hG0 hvd
  set G₁ := C d⁻¹ * G
  set F₁ := C d⁻¹ * F
  have hG₁ : Gauss.sup v 1 G₁ = 1 := by
    rw [Gauss.sup_mul, sup_C, ← hvd, map_inv₀, inv_mul_cancel₀ (by simpa using hd0)]
  have hφ : (φ : RatFunc K) * aeval ℓ' G₁ = aeval ℓ' F₁ := by
    simp only [G₁, F₁, map_mul, aeval_C, ← hf, ← hg', ← hfg]
    have : algebraMap K[X] (RatFunc K) g ≠ 0 := by
      simpa using (IsFractionRing.injective K[X] (RatFunc K)).ne hg0
    field_simp
  have hF₁ : Gauss.sup v 1 F₁ ≤ 1 := by
    rw [← gaussRat_aeval_gaussLin (a := a) hc, ← hφ, map_mul, gaussRat_aeval_gaussLin hc, hG₁,
      mul_one]
    exact φ.2
  obtain ⟨PF, hPF⟩ := exists_map_eq (v := v) F₁ fun i ↦ by
    simpa [term] using (term_le_sup (v := v) (r := 1) F₁ i).trans hF₁
  obtain ⟨PG, hPG⟩ := exists_map_eq (v := v) G₁ fun i ↦ by
    simpa [term] using (term_le_sup (v := v) (r := 1) G₁ i).trans hG₁.le
  set y := gaussGen v a r hc
  have ht : ((aeval y PG : (gaussRat v a r).valuationSubring) : RatFunc K) = aeval ℓ' G₁ := by
    rw [coe_aeval, hPG]
    rfl
  have hu : ((aeval y PF : (gaussRat v a r).valuationSubring) : RatFunc K) = aeval ℓ' F₁ := by
    rw [coe_aeval, hPF]
    rfl
  have htne : residue _ (aeval y PG) ≠ 0 := by
    rw [residue_ne_zero_iff, ht, gaussRat_aeval_gaussLin hc, hG₁]
  have hmul : φ * aeval y PG = aeval y PF := Subtype.ext (by
    rw [Subring.coe_mul, ht, hu, ← hφ])
  have hres : residue _ φ = residue _ (aeval y PF) / residue _ (aeval y PG) := by
    rw [eq_div_iff htne, ← map_mul, hmul]
  rw [hres, residue_aeval, residue_aeval]
  refine div_mem ?_ ?_ <;>
    exact IntermediateField.algebra_adjoin_le_adjoin _ _ (aeval_mem_adjoin_singleton _ _)

end GaussResidue

end SemistableReduction
