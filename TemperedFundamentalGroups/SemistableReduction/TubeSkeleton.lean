/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhaustGluing
import TemperedFundamentalGroups.SemistableReduction.NearBoundary
import TemperedFundamentalGroups.SemistableReduction.DiscLimit

/-!
# The skeleton clause of (T⇒)

Blueprint §9.12, O11 (T⇒), skeleton part. For an exhausting annulus `|c'| < |t| < 1`
(`t = (x - a)/c`) with exact node data at its node points (`NodeDataOfODP`, a named hypothesis
discharged by O1), every Gauss point `w_{a,|cγ|}` of its skeleton (`|c'| < |γ| < 1`) is a circle of
a tube (`ExhaustGluing.IsTubeCircle`).

* `TubeSkeleton.tube_of_eq_smul_pow`: if `x = λ uᵈ` (`λ ∈ kˣ`) and `[κ : k(x)] ≤ d`, then
  `κ = k(u)`: genus `0`, one zero and one pole of `x`;
* `GaussTube.exists_sub_const_lt_one`: elements of the normalized node chart are constants modulo
  the maximal ideal of every extension of a Gauss point of the open segment;
* `AffineTwist.extTrans` (with `inertiaDeg_extTrans`, `ramificationIdx_extTrans`): an extension of
  the outer Gauss point of the twist by `(a', cγ)` is an extension of `w_{0,|γ|}` on the twist by
  `(a, c)` (`|a' - a| ≤ |cγ|`);
* **`ExhaustGluing.tube_of_ext`**, **`isTubeCircle_of_exhausting`**: at the centre `P'` of such an
  extension the exact node data `σ x = e uᵈ` give `x/γ ≡ λ (u/π)ᵈ` (`πᵈ = γ`), and the tube degree
  `d` of `P'` (S6) bounds `[κ(w) : k(x̄)]`;
* `ExhaustGluing.tubeOfExhausting`: (T⇒) modulo `NodeDataOfODP` and the off-skeleton clause
  `OffSkeletonOfExhausting` (the local lemma (L)).
-/

open Polynomial WithZero IntermediateField
open scoped NNReal

namespace SemistableReduction

namespace TubeSkeleton

open PlaceNorm CurvePlace

section Core

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

/-- `x = λ uᵈ` (`λ ∈ kˣ`, `d ≥ 1`) has the zeros of `u`, with orders multiplied by `d`. -/
lemma zeros_eq_of_eq_smul_pow {x u : κ} (hu0 : u ≠ 0) {lam : k} (hlam : lam ≠ 0) {d : ℕ}
    (hd : 1 ≤ d) (hx : x = algebraMap k κ lam * u ^ d) :
    zeros k x = zeros k u ∧ ∀ Q ∈ zeros k u, ord x Q = d * ord u Q := by
  have hval (Q : CurvePlace k κ) : Q.valuation x = Q.valuation u ^ d := by
    rw [hx, map_mul, map_pow,
      valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one hlam, one_mul]
  have hx0 : x ≠ 0 := by
    rw [hx]
    exact mul_ne_zero ((_root_.map_ne_zero _).2 hlam) (pow_ne_zero _ hu0)
  have hmem (Q : CurvePlace k κ) (y : κ) (hy : y ≠ 0) : Q ∈ zeros k y ↔ Q.valuation y < 1 := by
    have h0 : Q.valuation y ≠ 0 := (Valuation.ne_zero_iff _).2 hy
    rw [mem_zeros, ← Q.valuation_le_one_iff, map_inv₀, not_le]
    exact one_lt_inv₀ (pos_iff_ne_zero.2 h0)
  have hz : zeros k x = zeros k u := by
    ext Q
    rw [hmem Q x hx0, hmem Q u hu0, hval, pow_lt_one_iff_of_nonneg zero_le (by omega)]
  refine ⟨hz, fun Q hQ ↦ ?_⟩
  have h1 := valuation_x (hz ▸ hQ : Q ∈ zeros k x)
  have h2 := valuation_x hQ
  rw [hval, h2, ← exp_nsmul] at h1
  have := exp_injective h1
  simp only [nsmul_eq_mul, mul_neg, neg_inj] at this
  exact_mod_cast this.symm

/-- **Tube residue curves.** If `x = λ uᵈ` (`λ ∈ kˣ`, `d ≥ 1`) is transcendental and
`[κ : k(x)] ≤ d`, then `κ = k(u)`: the genus is `0`, and `x` has exactly one zero and one pole. -/
theorem tube_of_eq_smul_pow {x u : κ} {lam : k} (hlam : lam ≠ 0) {d : ℕ} (hd : 1 ≤ d)
    (hx : x = algebraMap k κ lam * u ^ d) (hxr : x ∉ (algebraMap k κ).range)
    (hf : Module.finrank k⟮x⟯ κ ≤ d) :
    genus k κ = 0 ∧ (zeros k x⁻¹).card = 1 ∧ (zeros k x).card = 1 := by
  have hur : u ∉ (algebraMap k κ).range := by
    rintro ⟨b, rfl⟩
    exact hxr ⟨lam * b ^ d, by rw [hx, map_mul, map_pow]⟩
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hur ⟨0, map_zero _⟩
  have huir : u⁻¹ ∉ (algebraMap k κ).range := by
    rintro ⟨b, hb⟩
    exact hur ⟨b⁻¹, by rw [map_inv₀, hb, inv_inv]⟩
  obtain ⟨hz, hord⟩ := zeros_eq_of_eq_smul_pow hu0 hlam hd hx
  have hxi : x⁻¹ = algebraMap k κ lam⁻¹ * u⁻¹ ^ d := by
    rw [hx, mul_inv, inv_pow, map_inv₀]
  obtain ⟨hzi, -⟩ := zeros_eq_of_eq_smul_pow (inv_ne_zero hu0) (inv_ne_zero hlam) hd hxi
  -- `[κ : k(x)] = d [κ : k(u)]`
  have hsum := sum_ord hxr
  rw [Finset.sum_congr hz fun Q hQ ↦ hord Q hQ, ← Finset.mul_sum, sum_ord hur] at hsum
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hur)
  have hpos : 0 < Module.finrank k⟮u⟯ κ := Module.finrank_pos
  have h1 : Module.finrank k⟮u⟯ κ = 1 := by
    have : d * Module.finrank k⟮u⟯ κ ≤ d * 1 := by rw [hsum, mul_one]; exact hf
    have := Nat.le_of_mul_le_mul_left this (by omega)
    omega
  have hcard (y : κ) (hy : y ∉ (algebraMap k κ).range) (h : Module.finrank k⟮y⟯ κ = 1) :
      (zeros k y).card = 1 := by
    have hs := sum_ord hy
    rw [h] at hs
    have hle := Finset.card_nsmul_le_sum (zeros k y) (fun Q ↦ ord y Q) 1 fun Q hQ ↦ one_le_ord hQ
    rw [smul_eq_mul, mul_one, hs] at hle
    have hne : (zeros k y).Nonempty := by
      by_contra h'
      rw [Finset.not_nonempty_iff_eq_empty] at h'
      rw [h', Finset.sum_empty] at hs
      exact zero_ne_one hs
    have := hne.card_pos
    omega
  refine ⟨genus_eq_zero_of_adjoin_eq_top (finrank_eq_one_iff_eq_top.1 h1), ?_, ?_⟩
  · rw [hzi]
    exact hcard _ huir (by rw [adjoin_inv_eq]; exact h1)
  · rw [hz]
    exact hcard _ hur h1

end Core

end TubeSkeleton

namespace GaussTube

open GaussFibre GaussStability

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F']

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- **Elements of the normalized node chart are constants at interior Gauss points**: for an
extension `w'` of a Gauss point `w_{0,s}` of the open segment and `y ∈ R' = Rint c F'`, some
`κ ∈ O_C` has `w'(y - κ) < 1` (reduce an integral equation of `y` coefficientwise
(`exists_const`) and factor it over `C`). -/
theorem exists_sub_const_lt_one {c : C} {s : ℝ≥0ˣ} (hs : s ∈ segment c)
    (w' : GaussExtension (0 : C) s F') (y : Rint c F') :
    ∃ κ : C, ‖κ‖ ≤ 1 ∧ w'.1 ((y : F') - algebraMap C F' κ) < 1 := by
  classical
  obtain ⟨p, hm, hp⟩ := y.2
  set n := p.natDegree
  choose κ hκ1 hκ using fun i ↦ exists_const (p.coeff i).2
  set q : C[X] := ∑ i : Fin n, Polynomial.C (κ i) * X ^ (i : ℕ)
  set P : C[X] := X ^ n + q
  have hPm : P.Monic := monic_X_pow_add (degree_sum_fin_lt _)
  have hy1 : w'.1 (y : F') ≤ 1 := valuation_le_one_of_isIntegral hs w' y.2
  have hcoeff (i : ℕ) : w'.1 (algebraMap (RatFunc C) F' (p.coeff i : RatFunc C) -
      algebraMap C F' (κ i)) < 1 := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', ← map_sub, ← Valuation.comap_apply,
      w'.2]
    exact hκ i s hs
  -- `P(y)` is small
  have hPy : w'.1 (aeval (y : F') P) < 1 := by
    have hal (a : nodeRing c) : algebraMap (nodeRing c) F' a =
        algebraMap (RatFunc C) F' (a : RatFunc C) := rfl
    have h1 : ∑ i : Fin n, algebraMap (RatFunc C) F' (p.coeff i : RatFunc C) * (y : F') ^ (i : ℕ) +
        (y : F') ^ n = 0 := by
      have := hp
      rw [eval₂_eq_sum_range, Finset.sum_range_succ, hm.coeff_natDegree, map_one, one_mul,
        ← Fin.sum_univ_eq_sum_range (fun i ↦ algebraMap (nodeRing c) F' (p.coeff i) *
          (y : F') ^ i)] at this
      simpa only [hal] using this
    have h2 : aeval (y : F') P = ∑ i : Fin n, algebraMap C F' (κ i) * (y : F') ^ (i : ℕ) +
        (y : F') ^ n := by
      simp only [P, q, map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C]
      ring
    have h3 : aeval (y : F') P = -∑ i : Fin n, (algebraMap (RatFunc C) F'
        (p.coeff i : RatFunc C) - algebraMap C F' (κ i)) * (y : F') ^ (i : ℕ) := by
      rw [h2, ← sub_eq_zero, ← h1]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    rw [h3, Valuation.map_neg]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ ↦ ?_
    rw [map_mul, map_pow]
    exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hcoeff i) (pow_le_one₀ zero_le hy1)
  -- the roots of `P` are integral
  have hcoeffP (j : ℕ) : NormedField.valuation (K := C) (P.coeff j) ≤ 1 := by
    rw [NormedField.valuation_apply]
    have hq : ‖q.coeff j‖ ≤ 1 := by
      rw [finsetSum_coeff]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ ↦ ?_
      rw [coeff_C_mul_X_pow]
      split_ifs
      · exact hκ1 i
      · simp
    have hX : ‖(X ^ n : C[X]).coeff j‖ ≤ 1 := by
      rw [coeff_X_pow]
      split_ifs <;> simp
    have := (IsUltrametricDist.norm_add_le_max ((X ^ n : C[X]).coeff j) (q.coeff j)).trans
      (max_le hX hq)
    rw [← coeff_add] at this
    exact_mod_cast this
  have hfac : P = (P.roots.map fun r ↦ X - Polynomial.C r).prod := by
    conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := P)
      IsAlgClosed.card_roots_eq_natDegree]
    rw [hPm.leadingCoeff, Polynomial.C_1, one_mul]
  have hroot (r : C) (hr : r ∈ P.roots) : ‖r‖ ≤ 1 := by
    have := valuation_le_one_of_aeval_eq_zero (NormedField.valuation (K := C)) hPm
      (by rw [aeval_def, Algebra.algebraMap_self, eval₂_id]; exact (mem_roots hPm.ne_zero).1 hr)
      (fun i ↦ by simpa using hcoeffP i)
    rw [NormedField.valuation_apply] at this
    exact_mod_cast this
  by_contra! H
  have hall : ∀ r ∈ P.roots, w'.1 ((y : F') - algebraMap C F' r) = 1 := fun r hr ↦
    le_antisymm ((Valuation.map_sub _ _ _).trans (max_le hy1 (by
      rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', ← Valuation.comap_apply, w'.2,
        gaussRat_algebraMap_C, NormedField.valuation_apply]
      exact_mod_cast hroot r hr))) (H r (hroot r hr))
  have hprod : aeval (y : F') P = (P.roots.map fun r ↦ (y : F') - algebraMap C F' r).prod := by
    conv_lhs => rw [hfac]
    rw [map_multiset_prod, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun r _ ↦ ?_
    simp
  have h1 : w'.1 (aeval (y : F') P) = 1 := by
    rw [hprod, map_multiset_prod]
    refine Multiset.prod_eq_one fun x hx ↦ ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.1 hz
    exact hall r hr
  rw [h1] at hPy
  exact lt_irrefl 1 hPy

end GaussTube

namespace AffineTwist

open GaussFibre GaussStability

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

omit [IsAlgClosed C] in
lemma aff_X_sub_C {a c : C} (hc0 : c ≠ 0) (b : C) :
    aff a c hc0 (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) =
      algebraMap C (RatFunc C) c⁻¹ *
        algebraMap C[X] (RatFunc C) (X - Polynomial.C (a + c * b)) := by
  have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
  rw [aff_apply, affHom_algebraMap, map_sub, aeval_X, aeval_C, gaussCoord_eq, map_sub,
    ratFunc_algebraMap_C, RatFunc.algebraMap_X, map_inv₀, map_add, map_mul]
  field_simp
  ring

omit [IsAlgClosed C] [IsUltrametricDist C] in
lemma nnnorm_aux {a c b : C} (hc0 : c ≠ 0) (r : ℝ≥0ˣ) :
    ‖c⁻¹‖₊ * max ‖a - (a + c * b)‖₊
      ((Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0) * r : ℝ≥0ˣ) : ℝ≥0) = max ‖(0 : C) - b‖₊ r := by
  rw [show a - (a + c * b) = -(c * b) by ring, nnnorm_neg, nnnorm_mul, zero_sub, nnnorm_neg,
    Units.val_mul, Units.val_mk0, nnnorm_inv, ← mul_max, ← mul_assoc,
    inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hc0), one_mul]

/-- `w_{a,|c| r} ∘ σ = w_{0,r}` for the affine map `σ : x ↦ (x - a)/c`. -/
lemma gaussRat_aff_mul {a c : C} (hc0 : c ≠ 0) (r : ℝ≥0ˣ) (φ : RatFunc C) :
    gaussRat (NormedField.valuation (K := C)) a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0) * r)
      (aff a c hc0 φ) = gaussRat (NormedField.valuation (K := C)) 0 r φ := by
  have h : (gaussRat (NormedField.valuation (K := C)) a
      (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0) * r)).comap (aff a c hc0).toRingEquiv.toRingHom =
      gaussRat (NormedField.valuation (K := C)) 0 r := by
    refine valuation_ratFunc_ext_of_linear (fun b ↦ ?_) fun b ↦ ?_
    · rw [Valuation.comap_apply]
      change gaussRat _ a _ (aff a c hc0 (algebraMap C (RatFunc C) b)) = _
      rw [AlgEquiv.commutes, gaussRat_algebraMap_C, gaussRat_algebraMap_C]
    · rw [Valuation.comap_apply]
      change gaussRat _ a _ (aff a c hc0 (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
      rw [aff_X_sub_C, map_mul, gaussRat_algebraMap_C, gaussRat_algebraMap, gauss_X_sub_C,
        gaussRat_algebraMap, gauss_X_sub_C, NormedField.valuation_apply,
        NormedField.valuation_apply, NormedField.valuation_apply]
      exact nnnorm_aux hc0 r
  exact congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v φ) h

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F']

/-- The identity between two affine twists of `F'`. -/
noncomputable def affId {a c a' c' : C} (hc0 : c ≠ 0) (hc0' : c' ≠ 0) :
    Aff a c hc0 F' ≃+* Aff a' c' hc0' F' := (toAff hc0).symm.trans (toAff hc0')

/-- The change of coordinates `τ = σ_{a,c}⁻¹ ∘ σ_{a',c'}` between two affine twists:
`algebraMap' φ = algebraMap (τ φ)`. -/
noncomputable def affTrans (a c a' c' : C) (hc0 : c ≠ 0) (hc0' : c' ≠ 0) :
    RatFunc C ≃ₐ[C] RatFunc C := (aff a' c' hc0').trans (aff a c hc0).symm

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [IsAlgClosed C] in
lemma algebraMap_affTrans {a c a' c' : C} (hc0 : c ≠ 0) (hc0' : c' ≠ 0) (φ : RatFunc C) :
    affId (F' := F') hc0 hc0' (algebraMap (RatFunc C) (Aff a c hc0 F')
      (affTrans a c a' c' hc0 hc0' φ)) =
      algebraMap (RatFunc C) (Aff a' c' hc0' F') φ := by
  change toAff (a := a') hc0' ((toAff (a := a) hc0).symm (toAff (a := a) hc0
    (algebraMap (RatFunc C) F' (aff a c hc0 ((aff a c hc0).symm (aff a' c' hc0' φ)))))) =
      toAff (a := a') hc0' (algebraMap (RatFunc C) F' (aff a' c' hc0' φ))
  rw [RingEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]

/-- The Gauss point `w_{a',|cγ|} = w_{a,|cγ|}` (`|a' - a| ≤ |cγ|`) on the twist by `(a', cγ)` is
`w_{0,|γ|}` on the twist by `(a, c)`. -/
lemma gauss1_affTrans_symm {a c a' γ : C} (hc0 : c ≠ 0) (hγ : γ ≠ 0)
    (hle : ‖a' - a‖ ≤ ‖c * γ‖) (φ : RatFunc C) :
    gauss1 C ((affTrans a c a' (c * γ) hc0 (mul_ne_zero hc0 hγ)).symm φ) =
      gaussRat (NormedField.valuation (K := C)) 0 (Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ)) φ := by
  change gauss1 C ((aff a' (c * γ) (mul_ne_zero hc0 hγ)).symm (aff a c hc0 φ)) = _
  rw [gauss1_aff_symm, DiscLimit.gaussRat_eq_of_le (b := a) (by
      rw [NormedField.valuation_apply, ← nnnorm_neg, neg_sub]; exact_mod_cast hle),
    show Units.mk0 ‖c * γ‖₊ (nnnorm_ne_zero_iff.2 (mul_ne_zero hc0 hγ)) =
      Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0) * Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ) by
      ext; simp, gaussRat_aff_mul]

open Valuation in
/-- An extension of the outer Gauss point of the twist `(a', cγ)` (`|a' - a| ≤ |cγ|`) is an
extension of `w_{0,|γ|}` on the twist `(a, c)`. -/
noncomputable def extTrans {a c a' γ : C} (hc0 : c ≠ 0) (hγ : γ ≠ 0) (hle : ‖a' - a‖ ≤ ‖c * γ‖)
    (v : Ext C (Aff a' (c * γ) (mul_ne_zero hc0 hγ) F')) :
    GaussExtension (0 : C) (Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ)) (Aff a c hc0 F') :=
  ⟨v.1.comap (affId (F' := F') (a := a) (a' := a') hc0 (mul_ne_zero hc0 hγ)).toRingHom,
    Valuation.ext fun φ ↦ by
    rw [comap_apply, comap_apply]
    have h := algebraMap_affTrans (F' := F') (a := a) (a' := a') hc0 (mul_ne_zero hc0 hγ)
      ((affTrans a c a' (c * γ) hc0 (mul_ne_zero hc0 hγ)).symm φ)
    rw [AlgEquiv.apply_symm_apply] at h
    change v.1 (affId (F' := F') (a := a) (a' := a') hc0 (mul_ne_zero hc0 hγ)
      (algebraMap (RatFunc C) (Aff a c hc0 F') φ)) = _
    rw [h, ← comap_apply, v.2, gauss1_affTrans_symm hc0 hγ hle]⟩

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma extTrans_apply {a c a' γ : C} (hc0 : c ≠ 0) (hγ : γ ≠ 0) (hle : ‖a' - a‖ ≤ ‖c * γ‖)
    (v : Ext C (Aff a' (c * γ) (mul_ne_zero hc0 hγ) F')) (y : Aff a c hc0 F') :
    (extTrans hc0 hγ hle v).1 y =
      v.1 (affId (F' := F') (a := a) (a' := a') hc0 (mul_ne_zero hc0 hγ) y) := by
  change (v.1.comap (affId (F' := F') (a := a) (a' := a') hc0 (mul_ne_zero hc0 hγ)).toRingHom) y = _
  rw [Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- The inertia degree is invariant under `extTrans`. -/
lemma inertiaDeg_extTrans {a c a' γ : C} (hc0 : c ≠ 0) (hγ : γ ≠ 0) (hle : ‖a' - a‖ ≤ ‖c * γ‖)
    (v : Ext C (Aff a' (c * γ) (mul_ne_zero hc0 hγ) F')) :
    FundamentalInequality.inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0
        (Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ))) (extTrans hc0 hγ hle v).1 =
      FundamentalInequality.inertiaDeg (gauss1 C) v.1 := by
  set τ := affTrans a c a' (c * γ) hc0 (mul_ne_zero hc0 hγ)
  set sγ : ℝ≥0ˣ := Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ)
  have hτ (φ : RatFunc C) :
      gauss1 C (τ.symm φ) = gaussRat (NormedField.valuation (K := C)) 0 sγ φ :=
    gauss1_affTrans_symm hc0 hγ hle φ
  let e₁ : (gaussRat (NormedField.valuation (K := C)) 0 sγ).valuationSubring ≃+*
      (gauss1 C).valuationSubring :=
    { toFun := fun x ↦ ⟨τ.symm x, by
        rw [Valuation.mem_valuationSubring_iff, hτ]; exact x.2⟩
      invFun := fun y ↦ ⟨τ y, by
        rw [Valuation.mem_valuationSubring_iff, ← hτ, AlgEquiv.symm_apply_apply]; exact y.2⟩
      left_inv := fun x ↦ Subtype.ext (τ.apply_symm_apply x)
      right_inv := fun y ↦ Subtype.ext (τ.symm_apply_apply y)
      map_mul' := fun x y ↦ Subtype.ext (map_mul _ _ _)
      map_add' := fun x y ↦ Subtype.ext (map_add _ _ _) }
  set ι := affId (F' := F') (a := a) (a' := a') hc0 (mul_ne_zero hc0 hγ)
  let e₂ : (extTrans hc0 hγ hle v).1.valuationSubring ≃+* v.1.valuationSubring :=
    { toFun := fun x ↦ ⟨ι x.1, by
        rw [Valuation.mem_valuationSubring_iff, ← extTrans_apply]; exact x.2⟩
      invFun := fun y ↦ ⟨ι.symm y.1, by
        rw [Valuation.mem_valuationSubring_iff, extTrans_apply, RingEquiv.apply_symm_apply]
        exact y.2⟩
      left_inv := fun x ↦ Subtype.ext (ι.symm_apply_apply x.1)
      right_inv := fun y ↦ Subtype.ext (ι.apply_symm_apply y.1)
      map_mul' := fun x y ↦ Subtype.ext (map_mul ι x.1 y.1)
      map_add' := fun x y ↦ Subtype.ext (map_add ι x.1 y.1) }
  refine Algebra.finrank_eq_of_equiv_equiv (IsLocalRing.ResidueField.mapEquiv e₁)
    (IsLocalRing.ResidueField.mapEquiv e₂) ?_
  ext r
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective r
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap,
    Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap,
    IsLocalRing.ResidueField.map_residue]
  congr 1
  apply Subtype.ext
  have h := algebraMap_affTrans (F' := F') (a := a) (a' := a') hc0 (mul_ne_zero hc0 hγ) (τ.symm x)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- `e = 1` for the extensions of `w_{0,|γ|}` obtained by `extTrans`. -/
lemma ramificationIdx_extTrans [FiniteDimensional (RatFunc C) F'] {a c a' γ : C} (hc0 : c ≠ 0)
    (hγ : γ ≠ 0) (hle : ‖a' - a‖ ≤ ‖c * γ‖)
    (v : Ext C (Aff a' (c * γ) (mul_ne_zero hc0 hγ) F')) :
    FundamentalInequality.ramificationIdx (RatFunc C) (extTrans hc0 hγ hle v).1 = 1 := by
  set τ := affTrans a c a' (c * γ) hc0 (mul_ne_zero hc0 hγ)
  have hτ (φ : RatFunc C) : gauss1 C (τ.symm φ) = gaussRat (NormedField.valuation (K := C)) 0
      (Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ)) φ := gauss1_affTrans_symm hc0 hγ hle φ
  refine FundamentalInequality.ramificationIdx_eq_one_of_divisible' _
    (v := gaussRat (NormedField.valuation (K := C)) 0 (Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ)))
    fun φ n hn ↦ ?_
  obtain ⟨d, hd⟩ := gauss1_divisible (τ.symm φ) n hn
  refine ⟨τ d, ?_⟩
  rw [← hτ, ← hτ, AlgEquiv.symm_apply_apply, hd]

end AffineTwist

namespace ExhaustGluing

open GaussTube GaussFibre GaussStability AffineTwist PlaceNorm TubeSkeleton

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F' : Type*) [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable (C) in
/-- **Exact node data at ordinary double points** (named hypothesis, Blueprint §9.12; discharged
by O1 under `DefinedOverDVR`): every node point of a normalized node chart of an affine twist of
`F'` which is an ordinary double point over `C` carries exact node data. -/
def NodeDataOfODP : Prop :=
  ∀ (a c c' : C) (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0)
    (P' : Ideal (Rint c' (Aff a c hc F'))), P'.IsMaximal →
    P'.comap (algebraMap (nodeRing c') (Rint c' (Aff a c hc F'))) = tubeIdeal c' →
    IsNodeODP hc' hc0' P' →
      ∃ b₁ : OuterBranch C (Aff a c hc F'), outerBranches hc' P' = {b₁} ∧
        Nonempty (NodeData hc' P' b₁)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) F']

variable {F'}

include hp hp1 in
omit [Algebra.IsSeparable (RatFunc C) F'] in
/-- **The skeleton clause of (T⇒) at one extension.** Let the annulus `|c'| < |t| < 1`
(`t = (x - a)/c`) be exhausting, with exact node data at its node points, `|c'| < |γ| < 1` and
`|a' - a| < |cγ|`. Every extension `w` of the Gauss point `w_{a',|cγ|} = w_{a,|cγ|}` (as an
extension of the outer Gauss point of the twist by `(a', cγ)`) has a rational residue curve with one
point over `t̄' = 0` and one over `t̄' = ∞`. Proof: at the centre `P'` of `w` on the node chart, the
exact node data give `x/γ ≡ λ (u/π)ᵈ` (`πᵈ = γ`; the units `σ, e` reduce to constants,
`exists_sub_const_lt_one`), and the tube degree `d` of `P'` (S6) bounds `[κ(w) : k(x̄)]`
(`tube_of_eq_smul_pow`). -/
theorem tube_of_ext (hND : NodeDataOfODP C F') {a c c' : C} (hc : c ≠ 0) (hc' : ‖c'‖ < 1)
    (hc0' : c' ≠ 0) (hex : IsExhausting a hc hc' hc0' F') {γ a' : C} (hγ : γ ≠ 0)
    (h1 : ‖c'‖ < ‖γ‖) (h2 : ‖γ‖ < 1) (hle : ‖a' - a‖ < ‖c * γ‖)
    (w : Ext C (Aff a' (c * γ) (mul_ne_zero hc hγ) F')) :
    genus 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring) = 0 ∧
      (zeros 𝓀 (red C (xF C (Aff a' (c * γ) (mul_ne_zero hc hγ) F')) w)⁻¹).card = 1 ∧
      (zeros 𝓀 (red C (xF C (Aff a' (c * γ) (mul_ne_zero hc hγ) F')) w)).card = 1 := by
  classical
  haveI : Algebra.IsSeparable (RatFunc C) (Aff a c hc F') :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Finite (Ext C (Aff a c hc F')) := finite_ext (F := Aff a c hc F') hp hp1
  letI : Fintype (Ext C (Aff a c hc F')) := Fintype.ofFinite _
  have hcγ : c * γ ≠ 0 := mul_ne_zero hc hγ
  let W := extTrans hc hγ hle.le w
  let sγ : ℝ≥0ˣ := Units.mk0 ‖γ‖₊ (nnnorm_ne_zero_iff.2 hγ)
  haveI : Finite (GaussExtension (0 : C) sγ (Aff a c hc F')) :=
    finite_gaussExtension (F' := Aff a c hc F') 0 sγ
  letI : Fintype (GaussExtension (0 : C) sγ (Aff a c hc F')) := Fintype.ofFinite _
  have hs : sγ ∈ segment c' :=
    ⟨show ‖c'‖₊ < ‖γ‖₊ by exact_mod_cast h1, show ‖γ‖₊ < 1 by exact_mod_cast h2⟩
  -- the centre of `W` and its exact node data
  let P' := center hs W
  haveI hPmax : P'.IsMaximal := center_isMaximal hc' hc0' hs W
  have hPc := comap_center hs W
  obtain ⟨b₁, h₁, ⟨N⟩⟩ := hND a c c' hc hc' hc0' P' hPmax hPc (hex P' hPmax hPc)
  have hP₁ : placeIdeal hc' b₁.1 b₁.2.2 = P' := by
    have : b₁ ∈ outerBranches hc' P' := by rw [h₁]; exact Set.mem_singleton b₁
    exact this
  -- valuations on the twist `(a, c)`
  have hWC (b : C) : W.1 (algebraMap C (Aff a c hc F') b) = ‖b‖₊ := by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) (Aff a c hc F'), ← Valuation.comap_apply,
      W.2, gaussRat_algebraMap_C, NormedField.valuation_apply]
  have hW1 (y : Rint c' (Aff a c hc F')) (hy : y ∉ P') : W.1 (y : Aff a c hc F') = 1 :=
    le_antisymm (valuation_le_one_of_isIntegral hs W y.2) (not_lt.1 fun h ↦ hy h)
  have hconst (y : Rint c' (Aff a c hc F')) (hy : y ∉ P') :
      ∃ κ : C, ‖κ‖₊ = 1 ∧ W.1 ((y : Aff a c hc F') - algebraMap C (Aff a c hc F') κ) < 1 := by
    obtain ⟨κ, -, hκ⟩ := exists_sub_const_lt_one hs W y
    refine ⟨κ, ?_, hκ⟩
    have h := Valuation.map_eq_of_sub_lt W.1 (x := (y : Aff a c hc F'))
      (y := algebraMap C (Aff a c hc F') κ) (by rw [Valuation.map_sub_swap, hW1 y hy]; exact hκ)
    rw [hW1 y hy, hWC] at h
    exact h
  obtain ⟨κσ, hκσ, hσκ⟩ := hconst N.σ N.σ_notMem
  obtain ⟨κe, hκe, heκ⟩ := hconst N.e N.e_notMem
  -- `W(u) = |π|`, `πᵈ = γ`
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq γ (N.one_le_d : 0 < N.d)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by have := N.one_le_d; omega)] at hπ
    exact hγ hπ.symm
  have hWx : W.1 (xF C (Aff a c hc F')) = ‖γ‖₊ := by
    change W.1 (algebraMap (RatFunc C) (Aff a c hc F') RatFunc.X) = _
    rw [← Valuation.comap_apply, W.2, AnnulusUnit.gaussRat_X]
    rfl
  have hWu : W.1 N.u = ‖π‖₊ := by
    have h := congrArg W.1 N.x_eq
    rw [map_mul, map_mul, map_pow, hW1 _ N.σ_notMem, hW1 _ N.e_notMem, one_mul, one_mul,
      hWx] at h
    have h' : W.1 N.u ^ N.d = ‖π‖₊ ^ N.d := h.symm.trans (by rw [← nnnorm_pow, hπ])
    exact (pow_left_inj₀ zero_le zero_le (by have := N.one_le_d; omega)).1 h'
  -- passing to the twist `(a', cγ)`
  let ι := affId (F' := F') (a := a) (a' := a') hc hcγ
  have hwι (y : Aff a c hc F') : w.1 (ι y) = W.1 y := (extTrans_apply hc hγ hle.le w y).symm
  let K := Aff a' (c * γ) hcγ F'
  have hιC (b : C) : ι (algebraMap C (Aff a c hc F') b) = algebraMap C K b := rfl
  have hιx : ι (xF C (Aff a c hc F')) =
      algebraMap C K γ * xF C K + algebraMap C K ((a' - a) / c) := by
    rw [xF_aff, xF_aff]
    have hg : gaussCoord a c = algebraMap C (RatFunc C) γ * gaussCoord a' (c * γ) +
        algebraMap C (RatFunc C) ((a' - a) / c) := by
      rw [gaussCoord_eq, gaussCoord_eq]
      have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
      have hγ' : algebraMap C (RatFunc C) γ ≠ 0 := by simpa using hγ
      simp only [map_inv₀, map_mul, map_div₀, map_sub]
      field_simp
      ring
    change toAff hcγ (algebraMap (RatFunc C) F' (gaussCoord a c)) = _
    rw [hg, map_add, map_mul, map_add, map_mul, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
    rfl
  let U : K := ι (N.u * (algebraMap C (Aff a c hc F') π)⁻¹)
  have hU : w.1 U = 1 := by
    rw [hwι, map_mul, map_inv₀, hWu, hWC, mul_inv_cancel₀ (nnnorm_ne_zero_iff.2 hπ0)]
  let lam : C := κe / κσ
  have hlam1 : ‖lam‖₊ = 1 := by rw [nnnorm_div, hκe, hκσ, div_one]
  have hσ0 : ((N.σ : Aff a c hc F')) ≠ 0 := fun h ↦ by
    have := hW1 _ N.σ_notMem
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hκσ0 : κσ ≠ 0 := fun h ↦ by rw [h, nnnorm_zero] at hκσ; exact zero_ne_one hκσ
  -- `w(x' - λ Uᵈ) < 1`
  have hγK : algebraMap C K γ ≠ 0 := by simpa using hγ
  have hxK : xF C K = ι ((xF C (Aff a c hc F') - algebraMap C (Aff a c hc F') ((a' - a) / c)) /
      algebraMap C (Aff a c hc F') γ) := by
    rw [map_div₀, map_sub, hιC, hιC, hιx, add_sub_cancel_right, mul_div_cancel_left₀ _ hγK]
  have hπγ : algebraMap C (Aff a c hc F') π ^ N.d = algebraMap C (Aff a c hc F') γ := by
    rw [← map_pow, hπ]
  have hπ0' : algebraMap C (Aff a c hc F') π ≠ 0 := by simpa using hπ0
  have hκσ' : algebraMap C (Aff a c hc F') κσ ≠ 0 := by simpa using hκσ0
  have hinner : (xF C (Aff a c hc F') - algebraMap C (Aff a c hc F') ((a' - a) / c)) /
      algebraMap C (Aff a c hc F') γ - algebraMap C (Aff a c hc F') lam *
        (N.u * (algebraMap C (Aff a c hc F') π)⁻¹) ^ N.d =
      ((N.e - algebraMap C (Aff a c hc F') κe) * algebraMap C (Aff a c hc F') κσ -
        algebraMap C (Aff a c hc F') κe * (N.σ - algebraMap C (Aff a c hc F') κσ)) /
        ((N.σ : Aff a c hc F') * algebraMap C (Aff a c hc F') κσ) *
        (N.u * (algebraMap C (Aff a c hc F') π)⁻¹) ^ N.d -
      algebraMap C (Aff a c hc F') ((a' - a) / c / γ) := by
    have hx : xF C (Aff a c hc F') = N.e * N.u ^ N.d / N.σ := by
      rw [eq_div_iff hσ0, mul_comm]
      exact N.x_eq
    have hcG : algebraMap C (Aff a c hc F') c ≠ 0 := by simpa using hc
    have hγG : algebraMap C (Aff a c hc F') γ ≠ 0 := by simpa using hγ
    have hπd : algebraMap C (Aff a c hc F') π ^ N.d ≠ 0 := pow_ne_zero _ hπ0'
    rw [hx]
    simp only [lam, map_div₀, map_sub, mul_pow, inv_pow]
    rw [← hπγ]
    field_simp
    ring
  have hWinner : W.1 ((xF C (Aff a c hc F') - algebraMap C (Aff a c hc F') ((a' - a) / c)) /
      algebraMap C (Aff a c hc F') γ - algebraMap C (Aff a c hc F') lam *
        (N.u * (algebraMap C (Aff a c hc F') π)⁻¹) ^ N.d) < 1 := by
    rw [hinner]
    refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
    · rw [map_mul, map_pow, map_mul, map_inv₀, hWu, hWC, mul_inv_cancel₀
        (nnnorm_ne_zero_iff.2 hπ0), one_pow, mul_one, map_div₀, map_mul, hW1 _ N.σ_notMem, hWC,
        hκσ, one_mul, div_one]
      refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt ?_ ?_)
      · rw [map_mul, hWC, hκσ, mul_one]
        exact heκ
      · rw [map_mul, hWC, hκe, one_mul]
        exact hσκ
    · rw [hWC, nnnorm_div, nnnorm_div]
      have : ‖a' - a‖₊ < ‖c‖₊ * ‖γ‖₊ := by rw [← nnnorm_mul]; exact_mod_cast hle
      rw [div_div, div_lt_one (mul_pos (nnnorm_pos.2 hc) (nnnorm_pos.2 hγ))]
      exact this
  have hxdiff : w.1 (xF C K - algebraMap C K lam * U ^ N.d) < 1 := by
    have h : xF C K - algebraMap C K lam * U ^ N.d =
        ι ((xF C (Aff a c hc F') - algebraMap C (Aff a c hc F') ((a' - a) / c)) /
          algebraMap C (Aff a c hc F') γ - algebraMap C (Aff a c hc F') lam *
            (N.u * (algebraMap C (Aff a c hc F') π)⁻¹) ^ N.d) := by
      rw [map_sub, ← hxK, map_mul, hιC, map_pow]
    rw [h, hwι]
    exact hWinner
  -- the residue identity `x̄' = λ̄ Ūᵈ`
  have hlamC : ‖lam‖₊ ≤ 1 := hlam1.le
  set lamR : 𝓀 := IsLocalRing.residue (HenselComplete.integers C)
    ⟨lam, by simpa using (HenselComplete.mem_integers_iff lam).2 (by exact_mod_cast hlamC)⟩
  have hlamR : lamR ≠ 0 := by
    rw [Ne, GaussTube.residue_eq_zero_iff_norm, not_lt]
    change 1 ≤ ‖lam‖
    rw [← coe_nnnorm, hlam1, NNReal.coe_one]
  have hUd : w.1 (algebraMap C K lam * U ^ N.d) ≤ 1 := by
    rw [map_mul, map_pow, hU, one_pow, mul_one, valuation_algebraMap_C']
    exact hlamC
  have hred : red C (xF C K) w = algebraMap 𝓀 _ lamR * red C U w ^ N.d := by
    have h0 := (red_eq_zero_iff ((Valuation.map_sub _ _ _).trans
      (max_le (valuation_xF w).le hUd))).2 hxdiff
    rw [red_sub (valuation_xF w).le hUd, sub_eq_zero] at h0
    rw [h0, red_mul (by rw [valuation_algebraMap_C']; exact hlamC)
      (by rw [map_pow, hU, one_pow]), red_algebraMap_C lam hlamC, red_pow hU.le]
  -- the degree bound `[κ(w) : k(x̄')] ≤ d`
  have hf : FundamentalInequality.inertiaDeg (gauss1 C) w.1 ≤ N.d := by
    rw [← inertiaDeg_extTrans hc hγ hle.le w]
    have hsum := tubeDegree_eq_vertexDegree (F' := Aff a c hc F') hp hp1 hc' hc0' hs (cs := γ)
      (by rw [NormedField.valuation_apply]; rfl) P'
    rw [vertexDegree_eq_ord_of_eq_singleton hc' h₁, NodeData.ord_x hc' hP₁ N] at hsum
    have hmem : W ∈ Finset.univ.filter
        (fun w' : GaussExtension (0 : C) sγ (Aff a c hc F') ↦ center hs w' = P') :=
      Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
    have hle' := Finset.single_le_sum (f := fun w' : GaussExtension (0 : C) sγ (Aff a c hc F') ↦
      FundamentalInequality.ramificationIdx (RatFunc C) w'.1 *
        FundamentalInequality.inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 sγ) w'.1)
      (fun _ _ ↦ Nat.zero_le _) hmem
    rw [← tubeDegree, hsum, ramificationIdx_extTrans hc hγ hle.le w, one_mul] at hle'
    exact hle'
  have hxr :
      red C (xF C K) w ∉ (algebraMap 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring)).range :=
    fun ⟨b, hb⟩ ↦ transcendental_red_x (F := K) w (hb ▸ isAlgebraic_algebraMap b)
  exact tube_of_eq_smul_pow hlamR N.one_le_d hred hxr (by rw [finrank_adjoin_red_x]; exact hf)

include hp hp1 in
omit [Algebra.IsSeparable (RatFunc C) F'] in
/-- **(T⇒), skeleton clause**: every Gauss point `w_{a,|cγ|}` (`|c'| < |γ| < 1`) of the skeleton of
an exhausting annulus `|c'| < |t| < 1` is a circle of a tube (modulo `NodeDataOfODP`). -/
theorem isTubeCircle_of_exhausting (hND : NodeDataOfODP C F') {a c c' : C} (hc : c ≠ 0)
    (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0) (hex : IsExhausting a hc hc' hc0' F') {γ : C} (hγ : γ ≠ 0)
    (h1 : ‖c'‖ < ‖γ‖) (h2 : ‖γ‖ < 1) : IsTubeCircle F' a (mul_ne_zero hc hγ) := by
  intro b' hb'
  have hle : ‖b' - a‖ < ‖c * γ‖ := by rwa [norm_sub_rev]
  refine ⟨fun w ↦ ?_, fun w ↦ ?_⟩
  · obtain ⟨hg, hpoles, -⟩ := tube_of_ext hp hp1 hND hc hc' hc0' hex hγ h1 h2 hle w
    exact ⟨hg, hpoles⟩
  · exact (tube_of_ext hp hp1 hND hc hc' hc0' hex hγ h1 h2 hle w).2.2

variable (C F') in
/-- **(T⇒), off-skeleton clause** (named hypothesis, Blueprint §9.12): the Gauss points of an
exhausting annulus off its skeleton are discs of a tube. To be discharged by the local lemma (L)
(the residue class of a smooth point is an open disc). -/
def OffSkeletonOfExhausting : Prop :=
  ∀ (a c c' : C) (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0),
    IsExhausting a hc hc' hc0' F' →
      ∀ (β γ : C) (hγ : γ ≠ 0), ‖c'‖ < ‖β‖ → ‖β‖ < 1 → ‖γ‖ < ‖β‖ →
        IsTubeDisc F' (a + c * β) (mul_ne_zero hc hγ)

include hp hp1 in
omit [Algebra.IsSeparable (RatFunc C) F'] in
/-- **(T⇒)** `TubeOfExhausting`, modulo exact node data at ordinary double points
(`NodeDataOfODP`, O1) and the off-skeleton clause (`OffSkeletonOfExhausting`, lemma (L)). -/
theorem tubeOfExhausting (hND : NodeDataOfODP C F') (hOff : OffSkeletonOfExhausting C F') :
    TubeOfExhausting C F' := fun a c c' hc hc' hc0' hex ↦
  ⟨fun _ hγ h1 h2 ↦ isTubeCircle_of_exhausting hp hp1 hND hc hc' hc0' hex hγ h1 h2,
    hOff a c c' hc hc' hc0' hex⟩

end ExhaustGluing

end SemistableReduction
