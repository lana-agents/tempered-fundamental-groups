/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeMaximum
import TemperedFundamentalGroups.SemistableReduction.CurveGenerators

/-!
# The reduction of the node chart at the outer vertex

Blueprint §9.9, S7.7 (one component). Let `R' = Rint c F'` be the integral closure of the node chart
`O_C[x, c/x]` in `F'` and `v` an extension of the outer Gauss point `w_{0,1}`, with residue curve
`κ(v)` and reduction `ρ = redHom : R' → κ(v)`.

* `redHom_isIntegral`: `ρ(R')` is integral over `k[x̄]`;
* `exists_redHom_eq_aeval`: every `P(x̄)`, `P ∈ k[X]`, is a reduction;
* `exists_span`: the integral closure `Ã` of `k[x̄]` in `κ(v)` is spanned over `ρ(R')` by finitely
  many elements (`CurveGenerators.exists_generators`);
* `exists_frac`: every element of `κ(v)` is a quotient `ρ p / ρ q` (the residues of the orthonormal
  basis of G6.3, made integral over `C[x]`, span `κ(v)` over `κ(w_{0,1})`).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable {c : C}

/-- The reduction `R' → κ(v)` at an extension `v` of the outer Gauss point. -/
noncomputable def redHom (hc : ‖c‖ < 1) (v : Ext C F') :
    Rint c F' →+* ResidueField v.1.valuationSubring where
  toFun y := red C (y : F') v
  map_one' := by simp [red_one]
  map_mul' y z := by
    simp only [Subalgebra.coe_mul]
    exact red_mul (valuation_le_one_R hc v y) (valuation_le_one_R hc v z)
  map_zero' := by simp [red_zero]
  map_add' y z := by
    simp only [Subalgebra.coe_add]
    exact red_add (valuation_le_one_R hc v y) (valuation_le_one_R hc v z)

lemma redHom_apply (hc : ‖c‖ < 1) (v : Ext C F') (y : Rint c F') :
    redHom hc v y = red C (y : F') v := rfl

/-- `x` as an element of `R'`. -/
noncomputable def xR (c : C) : Rint c F' :=
  algebraMap (nodeRing c) (Rint c F') ⟨RatFunc.X, X_mem_nodeRing c⟩

/-- `c/x` as an element of `R'`. -/
noncomputable def yR (c : C) : Rint c F' :=
  algebraMap (nodeRing c) (Rint c F') ⟨_, div_X_mem_nodeRing c⟩

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma coe_xR : ((xR c : Rint c F') : F') = xF C F' := rfl

/-- The constants of `O_C` as elements of `R'`. -/
noncomputable def constR (c : C) (b : HenselComplete.integers C) : Rint c F' :=
  algebraMap (nodeRing c) (Rint c F') ⟨algebraMap C (RatFunc C) b,
    algebraMap_mem_nodeRing ((HenselComplete.mem_integers_iff _).1 b.2)⟩

lemma redHom_xR (hc : ‖c‖ < 1) (v : Ext C F') : redHom hc v (xR c) = red C (xF C F') v := rfl

lemma redHom_yR (hc : ‖c‖ < 1) (v : Ext C F') : redHom hc v (yR c) = 0 := by
  rw [redHom_apply, red_eq_zero_iff (valuation_le_one_R hc v _)]
  change v.1 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) c / RatFunc.X)) < 1
  rw [valuation_algebraMap, map_div₀, gauss1_algebraMap_C, gauss1_X, div_one]
  exact_mod_cast hc

lemma redHom_constR (hc : ‖c‖ < 1) (v : Ext C F') (b : HenselComplete.integers C) :
    redHom hc v (constR c b) = algebraMap 𝓀 _ (residue _ b) := by
  rw [redHom_apply]
  change red C (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) b)) v = _
  rw [← IsScalarTower.algebraMap_apply,
    red_algebraMap_C _ (by exact_mod_cast (HenselComplete.mem_integers_iff _).1 b.2)]

/-- Every polynomial in `x̄` is a reduction. -/
lemma exists_redHom_eq_aeval (hc : ‖c‖ < 1) (v : Ext C F') (P : 𝓀[X]) :
    ∃ y : Rint c F', redHom hc v y = aeval (red C (xF C F') v) P := by
  obtain ⟨Q, rfl⟩ := map_surjective _ (residue_surjective (R := HenselComplete.integers C)) P
  refine ⟨∑ i ∈ Finset.range (Q.natDegree + 1), constR c (Q.coeff i) * xR c ^ i, ?_⟩
  rw [map_sum, aeval_eq_sum_range' (n := Q.natDegree + 1)
    (Nat.lt_succ_of_le natDegree_map_le)]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_mul, map_pow, redHom_constR, redHom_xR, coeff_map, Algebra.smul_def]

/-- Reductions of the node chart lie in `k[x̄]`. -/
lemma redHom_algebraMap_mem (hc : ‖c‖ < 1) (v : Ext C F') (a : nodeRing c) :
    redHom hc v (algebraMap (nodeRing c) (Rint c F') a) ∈
      Algebra.adjoin 𝓀 {red C (xF C F') v} := by
  obtain ⟨a, ha⟩ := a
  have hle (b : RatFunc C) (hb : b ∈ nodeRing c) : v.1 (algebraMap (RatFunc C) F' b) ≤ 1 :=
    valuation_algebraMap_nodeRing_le hc v hb
  change red C (algebraMap (RatFunc C) F' a) v ∈ _
  induction ha using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, hb, rfl⟩ | rfl | rfl
    · have hb' : ‖b‖₊ ≤ 1 := by
        have : NormedField.valuation b ≤ 1 := hb
        rwa [NormedField.valuation_apply] at this
      rw [← IsScalarTower.algebraMap_apply, red_algebraMap_C _ hb']
      exact Subalgebra.algebraMap_mem _ _
    · exact Algebra.self_mem_adjoin_singleton _ _
    · have hlt : v.1 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) c / RatFunc.X)) < 1 := by
        rw [valuation_algebraMap, map_div₀, gauss1_algebraMap_C, gauss1_X, div_one]
        exact_mod_cast hc
      rw [(red_eq_zero_iff hlt.le).2 hlt]
      exact zero_mem _
  | zero => simp [red_zero]
  | one => simp [red_one]
  | add a b ha' hb' ha hb =>
    rw [map_add, red_add (hle a ha') (hle b hb')]
    exact add_mem ha hb
  | neg a ha' ha =>
    rw [_root_.map_neg, red_neg (hle a ha')]
    exact neg_mem ha
  | mul a b ha' hb' ha hb =>
    rw [map_mul, red_mul (hle a ha') (hle b hb')]
    exact mul_mem ha hb

/-- Reductions of `R'` are integral over `k[x̄]`. -/
lemma redHom_isIntegral (hc : ‖c‖ < 1) (v : Ext C F') (y : Rint c F') :
    IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) (redHom hc v y) := by
  obtain ⟨p, hm, hp⟩ := y.2
  let ψ : nodeRing c →+* Algebra.adjoin 𝓀 {red C (xF C F') v} :=
    ((redHom hc v).comp (algebraMap (nodeRing c) (Rint c F'))).codRestrict
      (Algebra.adjoin 𝓀 {red C (xF C F') v}).toSubring fun a ↦ redHom_algebraMap_mem hc v a
  refine ⟨p.map ψ, hm.map ψ, ?_⟩
  rw [eval₂_map]
  have h : (algebraMap (Algebra.adjoin 𝓀 {red C (xF C F') v}) _).comp ψ =
      (redHom hc v).comp (algebraMap (nodeRing c) (Rint c F')) := rfl
  rw [h, ← hom_eval₂]
  have h2 : eval₂ (algebraMap (nodeRing c) (Rint c F')) y p = 0 := by
    apply Subtype.ext
    have := hom_eval₂ p (algebraMap (nodeRing c) (Rint c F')) (Rint c F').val.toRingHom y
    exact this.trans hp
  rw [h2, map_zero]

section Poly

/-- A polynomial in `x` with integral coefficients, as an element of `R'`. -/
noncomputable def polyR (c : C) (Q : C[X]) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) : Rint c F' :=
  algebraMap (nodeRing c) (Rint c F') ⟨_, polynomial_mem_nodeRing c hQ⟩

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
lemma coe_polyR (Q : C[X]) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) :
    ((polyR (F' := F') c Q hQ : Rint c F') : F') = aeval (xF C F') Q :=
  (aeval_xF Q).symm

omit [IsAlgClosed C] in
/-- Normalization of a nonzero polynomial to Gauss norm one. -/
lemma exists_normalize {Q : C[X]} (hQ : Q ≠ 0) :
    ∃ γ : C, γ ≠ 0 ∧ ∃ Q' : C[X], Q = Polynomial.C γ * Q' ∧
      Gauss.sup (NormedField.valuation (K := C)) 1 Q' = 1 ∧ ∀ i, ‖Q'.coeff i‖ ≤ 1 := by
  obtain ⟨γ, hγ⟩ := exists_sup_eq Q
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero, Gauss.sup_eq_zero_iff] at hγ
    exact hQ hγ
  refine ⟨γ, hγ0, Polynomial.C γ⁻¹ * Q, by
    rw [← mul_assoc, ← Polynomial.C_mul, mul_inv_cancel₀ hγ0, Polynomial.C_1, one_mul], ?_, ?_⟩
  · rw [Gauss.sup_mul, Gauss.sup_C, hγ, NormedField.valuation_apply, nnnorm_inv,
      inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hγ0)]
  · intro i
    have h := Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1)
      (Polynomial.C γ⁻¹ * Q) i
    rw [Gauss.sup_mul, Gauss.sup_C, hγ, NormedField.valuation_apply, nnnorm_inv,
      inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hγ0)] at h
    have h' : ‖γ‖₊⁻¹ * ‖Q.coeff i‖₊ ≤ 1 := by simpa [Gauss.term] using h
    rw [coeff_C_mul, norm_mul, norm_inv]
    exact_mod_cast h'

end Poly

section Inner

variable {c : C} (hc0 : c ≠ 0)

/-- An extension of the inner Gauss point `w_{0,|c|}` as an extension of `w_{0,1}` to the twist
`Inv c F'`. -/
noncomputable def toInvExt (w' : GaussExtension (0 : C) (invRad hc0 1) F') :
    Ext C (Inv c hc0 F') :=
  ⟨w'.1.comap (toInv hc0).symm.toRingHom, by
    ext φ
    rw [comap_apply, comap_apply]
    have h : (toInv hc0).symm.toRingHom (algebraMap (RatFunc C) (Inv c hc0 F') φ) =
        algebraMap (RatFunc C) F' (inv hc0 φ) := by
      rw [algebraMap_inv_apply]
      exact RingEquiv.symm_apply_apply _ _
    rw [h, ← comap_apply, w'.2, ← gaussRat_inv, inv_inv_apply]⟩

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma toInvExt_apply (w' : GaussExtension (0 : C) (invRad hc0 1) F') (y : F') :
    (toInvExt hc0 w').1 (toInv hc0 y) = w'.1 y := by
  change w'.1 ((toInv hc0).symm (toInv hc0 y)) = _
  rw [RingEquiv.symm_apply_apply]

end Inner

section Frac

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Fractions**: every element of `κ(v)` is a quotient of reductions of `R'`. -/
theorem exists_frac (hc : ‖c‖ < 1) (hc0 : c ≠ 0) (v : Ext C F')
    (α : ResidueField v.1.valuationSubring) :
    ∃ p q : Rint c F', redHom hc v q ≠ 0 ∧ redHom hc v p = α * redHom hc v q := by
  classical
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  haveI : Finite (Ext C (Inv c hc0 F')) := finite_ext (F := Inv c hc0 F') hp hp1
  letI : Fintype (Ext C (Inv c hc0 F')) := Fintype.ofFinite _
  obtain ⟨b, hb, -, hres⟩ := exists_orthonormal_basis' ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F') hp hp1)
  set K : Subfield (ResidueField v.1.valuationSubring) := Subfield.closure (redHom hc v).range
  have hR (y : Rint c F') : redHom hc v y ∈ K := Subfield.subset_closure ⟨y, rfl⟩
  -- polynomials in `x` of Gauss norm one reduce to nonzero elements of `K`
  have hpoly (Q : C[X]) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1)
      (h1 : Gauss.sup (NormedField.valuation (K := C)) 1 Q = 1) :
      redHom hc v (polyR c Q hQ) ≠ 0 := by
    rw [redHom_apply, coe_polyR, Ne, red_eq_zero_iff (by rw [valuation_aeval_xF, h1]),
      valuation_aeval_xF, h1]
    exact lt_irrefl 1
  -- `κ(w_{0,1})` lands in `K`
  have hbase (φ : ResidueField (gauss1 C).valuationSubring) :
      algebraMap _ (ResidueField v.1.valuationSubring) φ ∈ K := by
    obtain ⟨⟨ψ, hψ⟩, rfl⟩ := residue_surjective φ
    have hψ' : gauss1 C ψ ≤ 1 := hψ
    have hD : ψ.denom ≠ 0 := ψ.denom_ne_zero
    obtain ⟨γ, hγ0, D', hD', hD'1, hD'c⟩ := exists_normalize hD
    set N' : C[X] := Polynomial.C γ⁻¹ * ψ.num
    have hD'0 : algebraMap C[X] (RatFunc C) D' ≠ 0 := by
      intro h
      rw [IsFractionRing.to_map_eq_zero_iff] at h
      rw [h, Gauss.sup_zero] at hD'1
      exact zero_ne_one hD'1
    have hγ' : algebraMap C[X] (RatFunc C) (Polynomial.C γ) ≠ 0 := by simpa using hγ0
    have hψN : ψ * algebraMap C[X] (RatFunc C) D' = algebraMap C[X] (RatFunc C) N' := by
      have hden : algebraMap C[X] (RatFunc C) ψ.denom ≠ 0 := by simpa using hD
      have h1 : ψ * algebraMap C[X] (RatFunc C) ψ.denom = algebraMap C[X] (RatFunc C) ψ.num := by
        have := RatFunc.num_div_denom ψ
        rw [div_eq_iff hden] at this
        exact this.symm
      have e1 : algebraMap C[X] (RatFunc C) (Polynomial.C γ⁻¹) *
          algebraMap C[X] (RatFunc C) (Polynomial.C γ) = 1 := by
        rw [← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hγ0, Polynomial.C_1, map_one]
      refine mul_right_cancel₀ hγ' ?_
      rw [mul_assoc, ← map_mul, mul_comm D', ← hD', h1]
      simp only [N', map_mul]
      rw [mul_comm (algebraMap C[X] (RatFunc C) (Polynomial.C γ⁻¹)), mul_assoc, e1, mul_one]
    have hN'1 : Gauss.sup (NormedField.valuation (K := C)) 1 N' ≤ 1 := by
      rw [← gauss1_algebraMap, ← hψN, map_mul, gauss1_algebraMap, hD'1, mul_one]
      exact hψ'
    have hN'c (i : ℕ) : ‖N'.coeff i‖ ≤ 1 := by
      have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) N' i).trans hN'1
      simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply] at this
      exact_mod_cast this
    have hred : algebraMap _ (ResidueField v.1.valuationSubring)
        (residue (gauss1 C).valuationSubring ⟨ψ, hψ⟩) =
        red C (algebraMap (RatFunc C) F' ψ) v := by
      have := red_algebraMap_mul (w := v) ψ hψ' (f := 1) (by simp)
      rw [mul_one, red_one, mul_one] at this
      exact this.symm
    have hψv : v.1 (algebraMap (RatFunc C) F' ψ) ≤ 1 := by rwa [valuation_algebraMap]
    have hD'v : v.1 (aeval (xF C F') D') ≤ 1 := by rw [valuation_aeval_xF, hD'1]
    have hmul : redHom hc v (polyR c N' hN'c) =
        red C (algebraMap (RatFunc C) F' ψ) v * redHom hc v (polyR c D' hD'c) := by
      rw [redHom_apply, redHom_apply, coe_polyR, coe_polyR, ← red_mul hψv hD'v, aeval_xF,
        aeval_xF, ← map_mul, hψN]
    rw [hred, eq_div_of_mul_eq (hpoly D' hD'c hD'1) hmul.symm]
    exact div_mem (hR _) (hR _)
  -- the residues of the orthonormal basis land in `K`
  letI : Algebra C[X] F' := ((algebraMap (RatFunc C) F').comp
    (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples C[X] (RatFunc C)
    (Finset.univ.image b)
  obtain ⟨γ, hγ0, y', hy', hy'1, hy'c⟩ := exists_normalize hy0
  have hint (f : F') (hf : IsIntegral C[X] f) : IsIntegral (Algebra.adjoin C {xF C F'}) f := by
    have hrange : Algebra.adjoin C {xF C F'} = (aeval (xF C F') : C[X] →ₐ[C] F').range :=
      Algebra.adjoin_singleton_eq_range_aeval C (xF C F')
    set ψ : C[X] →+* Algebra.adjoin C {xF C F'} :=
      (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
        (aeval (xF C F') : C[X] →ₐ[C] F').rangeRestrict.toRingHom
    refine IsIntegral.map_of_comp_eq ψ (RingHom.id F') (RingHom.ext fun P ↦ ?_) hf
    change aeval (xF C F') P = algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) P)
    exact aeval_xF P
  have hbasis (l : Fin (inertiaDeg (gauss1 C) v.1)) : red C (b ⟨v, l⟩) v ∈ K := by
    set bl := b ⟨v, l⟩
    have hbl1 : gnorm C bl = 1 := gnorm_basis hb _
    set B := Finset.univ.sup fun w : Ext C (Inv c hc0 F') ↦ w.1 (toInv hc0 bl)
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ‖c‖₊ ^ M * B ≤ 1 := by
      rcases eq_or_ne B 0 with hB | hB
      · exact ⟨0, by simp [hB]⟩
      have hB' : 0 < B := pos_iff_ne_zero.2 hB
      obtain ⟨M, hM⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hB')
        (show ‖c‖₊ < 1 by exact_mod_cast hc)
      refine ⟨M, ?_⟩
      calc ‖c‖₊ ^ M * B ≤ B⁻¹ * B := by gcongr
        _ = 1 := inv_mul_cancel₀ hB
    have hyb : IsIntegral C[X] (y • bl) := hyint bl (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    set z : F' := xF C F' ^ M * aeval (xF C F') y' * bl
    have hzeq : z = algebraMap C F' γ⁻¹ * xF C F' ^ M * (y • bl) := by
      rw [Algebra.smul_def]
      change _ = _ * (algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) y) * bl)
      rw [← aeval_xF, hy', map_mul, aeval_C]
      have : algebraMap C F' γ⁻¹ * algebraMap C F' γ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hγ0, map_one]
      simp only [z]
      linear_combination (xF C F' ^ M * aeval (xF C F') y' * bl) * this.symm
    have hmemA (a : F') (ha : a ∈ Algebra.adjoin C {xF C F'}) :
        IsIntegral (Algebra.adjoin C {xF C F'}) a :=
      isIntegral_algebraMap (x := (⟨a, ha⟩ : Algebra.adjoin C {xF C F'}))
    have hzint : IsIntegral (Algebra.adjoin C {xF C F'}) (xF C F' ^ 0 * z) := by
      rw [pow_zero, one_mul, hzeq]
      refine IsIntegral.mul (IsIntegral.mul (hmemA _ (Subalgebra.algebraMap_mem _ _))
        (hmemA _ (Subalgebra.pow_mem _ (Algebra.self_mem_adjoin_singleton C _) _))) (hint _ hyb)
    have hout : ∀ w : Ext C F', w.1 z ≤ 1 := fun w ↦ by
      simp only [z, map_mul, map_pow, valuation_xF, one_pow, one_mul, valuation_aeval_xF, hy'1]
      exact (le_gnorm w bl).trans hbl1.le
    have hin : ∀ w : GaussExtension (0 : C) (invRad hc0 1) F', w.1 z ≤ 1 := fun w ↦ by
      have hx : w.1 (xF C F') = ‖c‖₊ := by
        change w.1 (algebraMap (RatFunc C) F' RatFunc.X) = _
        rw [← comap_apply, w.2, AnnulusUnit.gaussRat_X, coe_invRad, Units.val_one, div_one]
      have hy : w.1 (aeval (xF C F') y') ≤ 1 := by
        rw [aeval_xF, ← comap_apply, w.2, gaussRat_algebraMap, gauss_apply, taylor_zero]
        refine Gauss.sup_le_iff.2 fun i ↦ ?_
        simp only [Gauss.term, NormedField.valuation_apply]
        have h1 : ‖y'.coeff i‖₊ ≤ 1 := by exact_mod_cast hy'c i
        have h2 : ((invRad hc0 1 : ℝ≥0ˣ) : ℝ≥0) ≤ 1 := by
          rw [coe_invRad, Units.val_one, div_one]; exact_mod_cast hc.le
        exact mul_le_one' h1 (pow_le_one₀ zero_le h2)
      have hb' : w.1 bl ≤ B := by
        rw [← toInvExt_apply hc0 w]
        exact Finset.le_sup (f := fun w : Ext C (Inv c hc0 F') ↦ w.1 (toInv hc0 bl))
          (Finset.mem_univ _)
      simp only [z, map_mul, map_pow, hx]
      calc ‖c‖₊ ^ M * w.1 (aeval (xF C F') y') * w.1 bl ≤ ‖c‖₊ ^ M * 1 * B := by gcongr
        _ ≤ 1 := by rw [mul_one]; exact hM
    have hzR : IsIntegral (nodeRing c) z := isIntegral_of_le hp hp1 hc0 hzint hout hin
    set zR : Rint c F' := ⟨z, hzR⟩
    set q : Rint c F' := xR c ^ M * polyR c y' hy'c
    have hq : redHom hc v q ≠ 0 := by
      rw [map_mul, map_pow, redHom_xR]
      exact mul_ne_zero (pow_ne_zero _ (red_xF_ne_zero' v)) (hpoly y' hy'c hy'1)
    have hzq : redHom hc v zR = redHom hc v q * red C bl v := by
      have hq1 : v.1 (xF C F' ^ M * aeval (xF C F') y') ≤ 1 := by
        rw [map_mul, map_pow, valuation_xF, one_pow, one_mul, valuation_aeval_xF, hy'1]
      rw [redHom_apply, redHom_apply]
      change red C (xF C F' ^ M * aeval (xF C F') y' * bl) v = red C (((xR c ^ M : Rint c F') :
        F') * ((polyR c y' hy'c : Rint c F') : F')) v * _
      rw [SubmonoidClass.coe_pow, coe_xR, coe_polyR, red_mul hq1 ((le_gnorm v bl).trans hbl1.le)]
    have hbl : red C bl v = redHom hc v zR / redHom hc v q :=
      eq_div_of_mul_eq hq (by rw [mul_comm]; exact hzq.symm)
    rw [hbl]
    exact div_mem (hR _) (hR _)
  -- the residues of the basis span `κ(v)`
  obtain ⟨ℓ, hli, hℓ⟩ := hres v
  haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
    (ResidueField v.1.valuationSubring) := finite_residueField
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin]; rfl)
  have hℓK (l : Fin (inertiaDeg (gauss1 C) v.1)) : residue v.1.valuationSubring (ℓ l) ∈ K := by
    have hbl : v.1 (b ⟨v, l⟩) ≤ 1 := (le_gnorm v _).trans (gnorm_basis hb _).le
    have : residue v.1.valuationSubring (ℓ l) = red C (b ⟨v, l⟩) v := by
      rw [red_of_le hbl, eq_comm, ← sub_eq_zero, ← _root_.map_sub, residue_eq_zero_iff,
        Valuation.mem_maximalIdeal_iff]
      exact hℓ l
    rw [this]
    exact hbasis l
  have hαK : α ∈ K := by
    have hα : α ∈ Submodule.span (ResidueField (gauss1 C).valuationSubring)
        (Set.range fun l ↦ residue v.1.valuationSubring (ℓ l)) := by rw [hspan]; trivial
    obtain ⟨φ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hα
    refine sum_mem fun l _ ↦ ?_
    rw [Algebra.smul_def]
    exact mul_mem (hbase _) (hℓK l)
  -- `α` is a fraction
  obtain ⟨a, ha, d, hd, had⟩ := Subfield.mem_closure_iff.1 hαK
  rw [Subring.closure_eq (redHom hc v).range] at ha hd
  obtain ⟨p', rfl⟩ := ha
  obtain ⟨q', rfl⟩ := hd
  by_cases hq' : redHom hc v q' = 0
  · refine ⟨0, 1, by simp, ?_⟩
    rw [← had, hq', div_zero, map_zero, zero_mul]
  · exact ⟨p', q', hq', by rw [← had, div_mul_cancel₀ _ hq']⟩

end Frac

section Span

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- Elements integral over `k[x̄]` lie in every place of `κ(v)` containing `x̄`. -/
lemma isIntegral_mem_V (v : Ext C F') {α : ResidueField v.1.valuationSubring}
    (hα : IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) α)
    {R : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)} (hx : red C (xF C F') v ∈ R.V) :
    α ∈ R.V := by
  set u := R.V.valuation
  have hle : ∀ a ∈ Algebra.adjoin 𝓀 {red C (xF C F') v}, a ∈ R.V := fun a ha ↦ by
    induction ha using Algebra.adjoin_induction with
    | mem x hx' =>
      rw [Set.mem_singleton_iff.1 hx']
      exact hx
    | algebraMap r => exact R.algebraMap_mem r
    | add x y _ _ hx hy => exact add_mem hx hy
    | mul x y _ _ hx hy => exact mul_mem hx hy
  let φ : Algebra.adjoin 𝓀 {red C (xF C F') v} →+* u.integer :=
    { toFun := fun a ↦ ⟨a, (ValuationSubring.valuation_le_one_iff _ _).2 (hle a a.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  have hint : IsIntegral u.integer α := IsIntegral.map_of_comp_eq φ (RingHom.id _) rfl hα
  exact (ValuationSubring.valuation_le_one_iff _ _).1
    ((Valuation.integer.integers u).mem_of_integral hint)

/-- Reductions of `R'` lie in every place of `κ(v)` containing `x̄`. -/
lemma redHom_mem_V' (hc : ‖c‖ < 1) (v : Ext C F') (y : Rint c F')
    {R : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)} (hx : red C (xF C F') v ∈ R.V) :
    redHom hc v y ∈ R.V :=
  isIntegral_mem_V v (redHom_isIntegral hc v y) hx

/-- **The integral closure of `k[x̄]` is spanned over `ρ(R')` by finitely many elements.** -/
theorem exists_span (hc : ‖c‖ < 1) (v : Ext C F') :
    ∃ G : Finset (ResidueField v.1.valuationSubring),
      (∀ g ∈ G, IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) g) ∧
      ∀ α, IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) α →
        ∃ r : ResidueField v.1.valuationSubring → Rint c F',
          α = ∑ g ∈ G, redHom hc v (r g) * g := by
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_red_x (F := F') v)
  obtain ⟨G, hG, hsp⟩ := CurveGenerators.exists_generators (transcendental_red_x (F := F') v)
  refine ⟨G, hG, fun α hα ↦ ?_⟩
  obtain ⟨c', hc'⟩ := hsp α hα
  choose r hr using fun g ↦ exists_redHom_eq_aeval hc v (c' g)
  exact ⟨r, by rw [hc']; exact Finset.sum_congr rfl fun g _ ↦ by rw [hr]⟩

end Span

section Tau

/-- **Clearing poles away from the point.** Let `Q` be a zero of `x̄` on `κ(v)` whose point `P'` is
not the point of any other zero of `x̄` on `κ(v)`. Then every `g ∈ O_Q` becomes integral over
`k[x̄]` after multiplication by the reduction of some `τ ∈ R' ∖ P'`. -/
theorem exists_tau (hc : ‖c‖ < 1) (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v))
    (hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v)), R ≠ Q →
      placeIdeal hc v hR ≠ placeIdeal hc v hQ)
    {g : ResidueField v.1.valuationSubring} (hg : g ∈ Q.V) :
    ∃ τ : Rint c F', τ ∉ placeIdeal hc v hQ ∧
      IsIntegral (Algebra.adjoin 𝓀 {red C (xF C F') v}) (redHom hc v τ * g) := by
  classical
  set xb := red C (xF C F') v
  set P' := placeIdeal hc v hQ
  haveI : P'.IsMaximal := placeIdeal_isMaximal hc v hQ
  have hQx : Q.res xb = 0 := Q.res_eq_zero_of_lt_one (valuation_x_lt_one hQ)
  -- the finitely many poles of `g` where `xb` is regular
  set S : Finset (CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :=
    (CurvePlace.finite_setOf_notMem g).toFinset.filter fun R ↦ xb ∈ R.V
  have hS (R) : R ∈ S ↔ g ∉ R.V ∧ xb ∈ R.V := by
    simp [S, Set.Finite.mem_toFinset]
  -- an element of `R' ∖ P'` vanishing at each such pole
  have hy (R : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (hR : R ∈ S) :
      ∃ y : Rint c F', y ∉ P' ∧ R.valuation (redHom hc v y) < 1 := by
    obtain ⟨hgR, hxR⟩ := (hS R).1 hR
    have hRQ : R ≠ Q := fun h ↦ hgR (h ▸ hg)
    by_cases hz : R ∈ zeros 𝓀 xb
    · have hne := hoth R hz hRQ
      have hnle : ¬ placeIdeal hc v hz ≤ P' := fun hle ↦
        hne ((placeIdeal_isMaximal hc v hz).eq_of_le (Ideal.IsMaximal.ne_top ‹_›) hle)
      obtain ⟨y, hyR, hyP⟩ := Set.not_subset.1 hnle
      refine ⟨y, hyP, ?_⟩
      rw [SetLike.mem_coe, mem_placeIdeal_iff] at hyR
      have := R.valuation_sub_res_lt_one (red_mem_V hc v y hz)
      rwa [hyR, map_zero, sub_zero] at this
    · -- `xb` is a unit at `R`: subtract its residue
      obtain ⟨κ₀, hκ₀⟩ := residue_surjective (R.res xb)
      refine ⟨xR c - constR c κ₀, fun hmem ↦ ?_, ?_⟩
      · rw [mem_placeIdeal_iff] at hmem
        change Q.res (redHom hc v (xR c - constR c κ₀)) = 0 at hmem
        rw [_root_.map_sub, redHom_xR, redHom_constR, hκ₀,
          Q.res_sub_algebraMap (Q.valuation_le_one_iff.1 (valuation_x_lt_one hQ).le), hQx,
          zero_sub, neg_eq_zero] at hmem
        apply hz
        rw [mem_zeros]
        intro hinv
        have h1 := R.valuation_sub_res_lt_one hxR
        rw [hmem, map_zero, sub_zero] at h1
        have h2 := R.valuation_le_one_iff.2 hinv
        rw [map_inv₀] at h2
        have hx0 : xb ≠ 0 := red_xF_ne_zero' v
        have := mul_lt_one_of_nonneg_of_lt_one_left zero_le h1 h2
        rw [mul_inv_cancel₀ ((Valuation.ne_zero_iff _).2 hx0)] at this
        exact lt_irrefl 1 this
      · rw [_root_.map_sub, redHom_xR, redHom_constR, hκ₀]
        exact R.valuation_sub_res_lt_one hxR
  choose! y hyP hyR using hy
  set τ : Rint c F' := ∏ R ∈ S, y R ^ R.poleOrder g
  refine ⟨τ, ?_, ?_⟩
  · intro hτ
    obtain ⟨R, hR, hmem⟩ := (Ideal.IsPrime.prod_mem_iff (hp := inferInstance)).1 hτ
    exact hyP R hR (Ideal.IsPrime.mem_of_pow_mem inferInstance _ hmem)
  · refine CurveGenerators.isIntegral_of_forall_mem fun R hxR ↦ ?_
    by_cases hR : R ∈ S
    · obtain ⟨hgR, -⟩ := (hS R).1 hR
      have h1 : R.valuation (redHom hc v (y R)) ≤ exp (-1) :=
        WithZero.le_exp_of_lt_exp_add_one (by simpa using hyR R hR)
      have hτR : R.valuation (redHom hc v τ) ≤ exp (-(R.poleOrder g : ℤ)) := by
        simp only [τ, map_prod, map_pow]
        rw [← Finset.mul_prod_erase S _ hR]
        calc R.valuation (redHom hc v (y R)) ^ R.poleOrder g *
              ∏ R' ∈ S.erase R, R.valuation (redHom hc v (y R')) ^ R'.poleOrder g ≤
              exp (-1) ^ R.poleOrder g * 1 := by
              refine mul_le_mul' (pow_le_pow_left₀ zero_le h1 _) (Finset.prod_le_one' fun R' _ ↦
                pow_le_one₀ zero_le (R.valuation_le_one_iff.2 (redHom_mem_V' hc v _ hxR)))
          _ = exp (-(R.poleOrder g : ℤ)) := by rw [mul_one, ← exp_nsmul]; simp
      refine R.valuation_le_one_iff.1 ?_
      rw [map_mul, R.valuation_eq_exp_poleOrder hgR]
      calc R.valuation (redHom hc v τ) * exp (R.poleOrder g : ℤ) ≤
            exp (-(R.poleOrder g : ℤ)) * exp (R.poleOrder g : ℤ) := by gcongr
        _ = 1 := by rw [← exp_add, neg_add_cancel, exp_zero]
    · have hgR : g ∈ R.V := by
        by_contra h
        exact hR ((hS R).2 ⟨h, hxR⟩)
      exact mul_mem (redHom_mem_V' hc v _ hxR) hgR

end Tau

end GaussTube

end SemistableReduction
