/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.InnerVertex

/-!
# The maximum principle for the node chart

Blueprint §9.9, S7.5. Let `nodeRing c = O_C[x, c/x]` (`0 < |c| < 1`) and `F' / C(x)` finite.

* `mem_nodeRing_of_mul_pow`: a Laurent polynomial `a = Q / xᵏ` with `w_{0,1}(a) ≤ 1` and
  `w_{0,|c|}(a) ≤ 1` lies in `O_C[x, c/x]`;
* `minpoly_coeff_mul_pow`: if `xᴺ y` is integral over `C[x]`, the coefficients of the minimal
  polynomial of `y` over `C(x)` are Laurent polynomials;
* **`isIntegral_of_le`** (maximum principle): if `xᴺ y` is integral over `C[x]` and `y` has value
  `≤ 1` at all extensions of `w_{0,1}` and of `w_{0,|c|}`, then `y` is integral over the node
  chart (`y ∈ R'`).
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

section Laurent

lemma X_mem_nodeRing (c : C) : (RatFunc.X : RatFunc C) ∈ nodeRing c :=
  self_mem_nodeChart (v := NormedField.valuation (K := C))

lemma div_X_mem_nodeRing (c : C) : algebraMap C (RatFunc C) c / RatFunc.X ∈ nodeRing c :=
  div_mem_nodeChart (v := NormedField.valuation (K := C))

lemma gaussRat_polynomial_term_le (s : ℝ≥0ˣ) (Q : C[X]) (i : ℕ) :
    ‖Q.coeff i‖₊ * (s : ℝ≥0) ^ i ≤ w s (algebraMap C[X] (RatFunc C) Q) := by
  rw [gaussRat_algebraMap, gauss_apply, taylor_zero]
  have := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := s) Q i
  simpa [Gauss.term] using this

/-- **Laurent polynomials in the node chart**: `a = Q / xᵏ` with `w_{0,1}(a) ≤ 1` and
`w_{0,|c|}(a) ≤ 1` lies in `O_C[x, c/x]`. -/
theorem mem_nodeRing_of_mul_pow {c : C} (hc0 : c ≠ 0) {a : RatFunc C} {k : ℕ} {Q : C[X]}
    (hQ : a * RatFunc.X ^ k = algebraMap C[X] (RatFunc C) Q) (h1 : w 1 a ≤ 1)
    (hc : w (Units.mk0 ‖c‖₊ (by simpa using hc0)) a ≤ 1) : a ∈ nodeRing c := by
  set sc : ℝ≥0ˣ := Units.mk0 ‖c‖₊ (by simpa using hc0)
  have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have hXk : (RatFunc.X : RatFunc C) ^ k ≠ 0 := pow_ne_zero _ hX0
  have ha : a = algebraMap C[X] (RatFunc C) Q / RatFunc.X ^ k := by
    rw [← hQ, mul_div_cancel_right₀ _ hXk]
  -- coefficient bounds
  have hb (s : ℝ≥0ˣ) (hs : w s a ≤ 1) (i : ℕ) : ‖Q.coeff i‖₊ * (s : ℝ≥0) ^ i ≤ (s : ℝ≥0) ^ k := by
    have h := gaussRat_polynomial_term_le s Q i
    rw [← hQ, map_mul, map_pow, AnnulusUnit.gaussRat_X] at h
    exact h.trans (mul_le_of_le_one_left zero_le hs)
  have hb1 (i : ℕ) : ‖Q.coeff i‖ ≤ 1 := by
    have := hb 1 h1 i
    simp only [Units.val_one, one_pow, mul_one] at this
    exact_mod_cast this
  have hbc (i : ℕ) : ‖Q.coeff i‖₊ * ‖c‖₊ ^ i ≤ ‖c‖₊ ^ k := hb sc hc i
  have hc0' : (0 : ℝ≥0) < ‖c‖₊ := nnnorm_pos.2 hc0
  -- termwise
  rw [ha, Q.as_sum_range_C_mul_X_pow, map_sum, Finset.sum_div]
  refine Subring.sum_mem _ fun i _ ↦ ?_
  rw [map_mul, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  by_cases hik : k ≤ i
  · have : RatFunc.C (Q.coeff i) * RatFunc.X ^ i / RatFunc.X ^ k =
        RatFunc.C (Q.coeff i) * RatFunc.X ^ (i - k) := by
      rw [mul_div_assoc, pow_sub₀ _ hX0 hik, div_eq_mul_inv]
    rw [this]
    exact Subring.mul_mem _ (algebraMap_mem_nodeRing (hb1 i))
      (Subring.pow_mem _ (X_mem_nodeRing c) _)
  · rw [not_le] at hik
    set n := k - i
    have hcn : (c : C) ^ n ≠ 0 := pow_ne_zero _ hc0
    have : RatFunc.C (Q.coeff i) * RatFunc.X ^ i / RatFunc.X ^ k =
        algebraMap C (RatFunc C) (Q.coeff i / c ^ n) *
          (algebraMap C (RatFunc C) c / RatFunc.X) ^ n := by
      have hk : k = i + n := by omega
      have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
      rw [hk, pow_add, div_pow, map_div₀, map_pow, ← RatFunc.algebraMap_C]
      field_simp
      exact (IsScalarTower.algebraMap_apply C C[X] (RatFunc C) _).symm
    rw [this]
    refine Subring.mul_mem _ (algebraMap_mem_nodeRing ?_)
      (Subring.pow_mem _ (div_X_mem_nodeRing c) _)
    rw [norm_div, norm_pow, div_le_one (pow_pos (norm_pos_iff.2 hc0) _)]
    have h := hbc i
    have hk : k = i + n := by omega
    rw [hk, pow_add] at h
    have h' : ‖Q.coeff i‖₊ * ‖c‖₊ ^ i ≤ ‖c‖₊ ^ n * ‖c‖₊ ^ i := by rw [mul_comm (‖c‖₊ ^ n)]; exact h
    have := le_of_mul_le_mul_right h' (pow_pos hc0' i)
    exact_mod_cast this

end Laurent

section Maximum

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

omit [IsUltrametricDist C] in
/-- If `xᴺ y` is integral over `C[x]`, the coefficients of the minimal polynomial of `y` over
`C(x)` are Laurent polynomials: `μ_n · x^{N (d - n)} ∈ C[x]`. -/
lemma minpoly_coeff_mul_pow {y : F'} {N : ℕ}
    (hint : IsIntegral (Algebra.adjoin C {xF C F'}) (xF C F' ^ N * y)) (n : ℕ) :
    ∃ Q : C[X], (minpoly (RatFunc C) y).coeff n *
      RatFunc.X ^ (N * ((minpoly (RatFunc C) y).natDegree - n)) =
        algebraMap C[X] (RatFunc C) Q := by
  set μ := minpoly (RatFunc C) y
  set s : RatFunc C := RatFunc.X ^ N
  have hs0 : s ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  set z := xF C F' ^ N * y
  have hz : z = algebraMap (RatFunc C) F' s * y := by simp [z, s, xF]
  have hyi : IsIntegral (RatFunc C) y := Algebra.IsIntegral.isIntegral y
  have hzi : IsIntegral (RatFunc C) z := Algebra.IsIntegral.isIntegral z
  set ν := μ.scaleRoots s
  have hνm : ν.Monic := (monic_scaleRoots_iff s).2 (minpoly.monic hyi)
  have hνz : aeval z ν = 0 := by
    rw [hz]
    exact scaleRoots_aeval_eq_zero (minpoly.aeval _ y)
  have hdvd : minpoly (RatFunc C) z ∣ ν := minpoly.dvd _ _ hνz
  have hdeg : ν.natDegree ≤ (minpoly (RatFunc C) z).natDegree := by
    rw [natDegree_scaleRoots]
    have hy' : y = algebraMap (RatFunc C) F' s⁻¹ * z := by
      rw [hz, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hs0, map_one, one_mul]
    have h0 : aeval y ((minpoly (RatFunc C) z).scaleRoots s⁻¹) = 0 := by
      rw [hy']
      exact scaleRoots_aeval_eq_zero (minpoly.aeval _ z)
    have hm : ((minpoly (RatFunc C) z).scaleRoots s⁻¹).Monic :=
      (monic_scaleRoots_iff _).2 (minpoly.monic hzi)
    have := natDegree_le_of_dvd (minpoly.dvd _ _ h0) hm.ne_zero
    rwa [natDegree_scaleRoots] at this
  have heq : ν = minpoly (RatFunc C) z :=
    eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hνm hdvd hdeg
  obtain ⟨Q, hQ⟩ := exists_minpoly_coeff_eq' (C := C) (F := F') hint n
  refine ⟨Q, ?_⟩
  rw [hQ, ← heq, coeff_scaleRoots, pow_mul]

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma comap_toInv_eq {c : C} (hc0 : c ≠ 0) [IsAlgClosed C] (v : Ext C (Inv c hc0 F')) :
    (v.1.comap (toInv hc0).toRingHom).comap (algebraMap (RatFunc C) F') =
      gaussRat (NormedField.valuation (K := C)) 0 (invRad hc0 1) := by
  ext φ
  rw [comap_apply, comap_apply]
  have h : (toInv hc0).toRingHom (algebraMap (RatFunc C) F' φ) =
      algebraMap (RatFunc C) (Inv c hc0 F') (inv hc0 φ) := by
    rw [algebraMap_inv_apply, inv_inv_apply]
    rfl
  rw [h, ← comap_apply, v.2, gaussRat_inv]

omit [IsUltrametricDist C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma minpoly_toInv {c : C} (hc0 : c ≠ 0) (y : F') :
    minpoly (RatFunc C) (toInv hc0 y : Inv c hc0 F') =
      (minpoly (RatFunc C) y).map (inv hc0).toRingEquiv.toRingHom := by
  have hyi : IsIntegral (RatFunc C) y := Algebra.IsIntegral.isIntegral y
  have hyi' : IsIntegral (RatFunc C) (toInv hc0 y : Inv c hc0 F') :=
    Algebra.IsIntegral.isIntegral _
  -- the two algebra maps differ by `inv`
  have hcomp (φ : RatFunc C) : algebraMap (RatFunc C) (Inv c hc0 F') (inv hc0 φ) =
      toInv hc0 (algebraMap (RatFunc C) F' φ) := by
    rw [algebraMap_inv_apply, inv_inv_apply]
  have hcomp' (φ : RatFunc C) : (toInv hc0).symm (algebraMap (RatFunc C) (Inv c hc0 F') φ) =
      algebraMap (RatFunc C) F' (inv hc0 φ) := by
    rw [algebraMap_inv_apply, RingEquiv.symm_apply_apply]
  set μ := minpoly (RatFunc C) y
  set Q := μ.map (inv hc0).toRingEquiv.toRingHom
  have hQm : Q.Monic := (minpoly.monic hyi).map _
  have hQ0 : aeval (toInv hc0 y : Inv c hc0 F') Q = 0 := by
    rw [aeval_def, eval₂_map]
    have : (algebraMap (RatFunc C) (Inv c hc0 F')).comp (inv hc0).toRingEquiv.toRingHom =
        (toInv hc0).toRingHom.comp (algebraMap (RatFunc C) F') :=
      RingHom.ext fun φ ↦ hcomp φ
    rw [this]
    refine ((hom_eval₂ μ (algebraMap (RatFunc C) F') (toInv hc0).toRingHom y).symm).trans ?_
    rw [← aeval_def, minpoly.aeval, map_zero]
  set μI := minpoly (RatFunc C) (toInv hc0 y : Inv c hc0 F')
  have hdvd : μI ∣ Q := minpoly.dvd _ _ hQ0
  have hdeg : Q.natDegree ≤ μI.natDegree := by
    rw [natDegree_map]
    have h0 : aeval y (μI.map (inv hc0).toRingEquiv.toRingHom) = 0 := by
      rw [aeval_def, eval₂_map]
      have : (algebraMap (RatFunc C) F').comp (inv hc0).toRingEquiv.toRingHom =
          (toInv hc0).symm.toRingHom.comp (algebraMap (RatFunc C) (Inv c hc0 F')) :=
        RingHom.ext fun φ ↦ (hcomp' φ).symm
      rw [this]
      refine ((hom_eval₂ μI (algebraMap (RatFunc C) (Inv c hc0 F')) (toInv hc0).symm.toRingHom
        (toInv hc0 y)).symm).trans ?_
      rw [← aeval_def, minpoly.aeval, map_zero]
    have hm : (μI.map (inv hc0).toRingEquiv.toRingHom).Monic := (minpoly.monic hyi').map _
    have := natDegree_le_of_dvd (minpoly.dvd _ _ h0) hm.ne_zero
    rwa [natDegree_map] at this
  exact (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hyi') hQm hdvd hdeg).symm

variable [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **The maximum principle for the node chart**: if `xᴺ y` is integral over `C[x]` and `y` has
value `≤ 1` at all extensions of `w_{0,1}` and of `w_{0,|c|}`, then `y` is integral over
`O_C[x, c/x]`. -/
theorem isIntegral_of_le {c : C} (hc0 : c ≠ 0) {y : F'} {N : ℕ}
    (hint : IsIntegral (Algebra.adjoin C {xF C F'}) (xF C F' ^ N * y))
    (hout : ∀ v : Ext C F', v.1 y ≤ 1)
    (hin : ∀ v : GaussExtension (0 : C) (invRad hc0 1) F', v.1 y ≤ 1) :
    IsIntegral (nodeRing c) y := by
  classical
  set μ := minpoly (RatFunc C) y
  have hyi : IsIntegral (RatFunc C) y := Algebra.IsIntegral.isIntegral y
  -- outer bound
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_orthonormal_basis ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F') hp hp1)
  have h1 (n : ℕ) : gauss1 C (μ.coeff n) ≤ 1 :=
    gauss1_minpoly_coeff_le hb (gnorm_le_iff.2 hout) n
  -- inner bound, through the inversion
  haveI : Finite (Ext C (Inv c hc0 F')) := finite_ext (F := Inv c hc0 F') hp hp1
  letI : Fintype (Ext C (Inv c hc0 F')) := Fintype.ofFinite _
  obtain ⟨b', hb'⟩ := exists_orthonormal_basis ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := Inv c hc0 F') hp hp1)
  have hgI : gnorm C (toInv hc0 y : Inv c hc0 F') ≤ 1 :=
    gnorm_le_iff.2 fun v ↦ hin ⟨v.1.comap (toInv hc0).toRingHom, comap_toInv_eq hc0 v⟩
  have h2 (n : ℕ) : gaussRat (NormedField.valuation (K := C)) 0 (invRad hc0 1) (μ.coeff n) ≤ 1 := by
    have := gauss1_minpoly_coeff_le hb' hgI n
    rw [minpoly_toInv, coeff_map] at this
    change gaussRat _ 0 1 (inv hc0 (μ.coeff n)) ≤ 1 at this
    rwa [gaussRat_inv] at this
  have hrad : invRad hc0 1 = Units.mk0 ‖c‖₊ (by simpa using hc0) := by
    ext; simp [coe_invRad]
  -- the coefficients lie in the node chart
  have hmem (n : ℕ) : μ.coeff n ∈ nodeRing c := by
    obtain ⟨Q, hQ⟩ := minpoly_coeff_mul_pow hint n
    exact mem_nodeRing_of_mul_pow hc0 hQ (h1 n) (hrad ▸ h2 n)
  have hO : (μ.coeffs : Set (RatFunc C)) ⊆ nodeRing c := fun a ha ↦ by
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 ha
    exact hmem n
  refine ⟨μ.toSubring _ hO, (monic_toSubring _ _ _).2 (minpoly.monic hyi), ?_⟩
  have : (μ.toSubring _ hO).map (nodeRing c).subtype = μ := map_toSubring _ _ _
  have h : eval₂ (algebraMap (nodeRing c) F') y (μ.toSubring _ hO) = aeval y μ := by
    conv_rhs => rw [← this]
    rw [aeval_def, eval₂_map]
    rfl
  rw [h, minpoly.aeval]

end Maximum

end GaussTube

end SemistableReduction
