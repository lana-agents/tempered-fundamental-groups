/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TreeData

/-!
# Reductions of Riemann–Roch spaces on a Gauss tree

Blueprint §9.9, S7.5. Let `T` be tree data and `D_m = m Σᵢ (x - bᵢ)₀` (`divisor`).

* `valuation_mul_prod_le`: for `f ∈ L(m Σⱼ (tⱼ)₀)` and a place `P` where all `tⱼ` are regular,
  `v_P(f Πⱼ tⱼᵐ) ≤ 1`;
* `TypeTwo.red_mem_of_isIntegral`, `TypeTwo.red_mem_of_isIntegral_inv`: G6.5 in the coordinate
  of a vertex, for type-2 valuations: an element integral over `C[t]` (resp. `C[t⁻¹]`) with value
  `≤ 1` at all extensions of the Gauss point of `t` reduces into every place containing `t̄`
  (resp. `t̄⁻¹`).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

section Divisor

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

variable (k) in
/-- The divisor of zeros of `t`. -/
noncomputable def zeroDiv (t : κ) : CurveDivisor k κ := poleDivisor k t⁻¹

lemma valuation_eq_exp_neg_zeroDiv (P : CurvePlace k κ) {t : κ} (ht0 : t ≠ 0) (ht : t ∈ P.V) :
    P.valuation t = exp (-(zeroDiv k t P)) := by
  rw [zeroDiv, poleDivisor_apply]
  by_cases hinv : t⁻¹ ∈ P.V
  · rw [P.poleOrder_eq_zero_iff.2 hinv, Nat.cast_zero, neg_zero, exp_zero]
    have h1 := P.valuation_le_one_iff.2 ht
    have h2 := P.valuation_le_one_iff.2 hinv
    rw [map_inv₀] at h2
    exact le_antisymm h1 ((inv_le_one₀ ((Valuation.pos_iff _).2 ht0)).1 h2)
  · have := P.valuation_eq_exp_poleOrder hinv
    rw [map_inv₀] at this
    rw [← inv_inv (P.valuation t), this, exp_neg]

lemma prod_valuation_pow {ι : Type*} (s : Finset ι) (t : ι → κ) (ht0 : ∀ j, t j ≠ 0) (m : ℕ)
    (P : CurvePlace k κ) (hP : ∀ j ∈ s, t j ∈ P.V) :
    ∏ j ∈ s, P.valuation (t j ^ m) = exp (-(m * ∑ j ∈ s, zeroDiv k (t j) P)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj), map_pow,
      valuation_eq_exp_neg_zeroDiv P (ht0 a) (hP a (Finset.mem_insert_self a s)),
      ← exp_nsmul, ← exp_add]
    congr 1
    simp only [nsmul_eq_mul]
    ring

/-- **Clearing the poles**: for `f ∈ L(m Σⱼ (tⱼ)₀)` and a place `P` where all `tⱼ` are regular,
`v_P(f Πⱼ tⱼᵐ) ≤ 1`. -/
lemma valuation_mul_prod_le {ι : Type*} (s : Finset ι) (t : ι → κ) (ht0 : ∀ j, t j ≠ 0) (m : ℕ)
    {f : κ} (hf : f ∈ rrSpace (m • ∑ j ∈ s, zeroDiv k (t j))) (P : CurvePlace k κ)
    (hP : ∀ j ∈ s, t j ∈ P.V) : P.valuation (f * ∏ j ∈ s, t j ^ m) ≤ 1 := by
  have hfP := hf P
  rw [Finsupp.smul_apply, Finsupp.finsetSum_apply, nsmul_eq_mul] at hfP
  rw [map_mul, map_prod]
  have hprod := prod_valuation_pow s t ht0 m P hP
  rw [hprod]
  calc P.valuation f * exp (-(m * ∑ j ∈ s, zeroDiv k (t j) P)) ≤
      exp (m * ∑ j ∈ s, zeroDiv k (t j) P) * exp (-(m * ∑ j ∈ s, zeroDiv k (t j) P)) := by
        gcongr
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

end Divisor

section Chart

variable {F : Type*} [Field F] [Algebra C F] [IsAlgClosed C] [CharZero C]
  [IsCurveFunctionField C F] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

include hp hp1 in
/-- **G6.5 for type-2 valuations** (chart `t`): if `g` is integral over `C[t]` and has value
`≤ 1` at every extension of the Gauss point of `t`, then `ḡ` lies in every place of `κ(W)`
containing `t̄`. -/
theorem TypeTwo.red_mem_of_isIntegral {t : F} (ht : Transcendental C t) {W : TypeTwo C F}
    (hW : IsOver ht W) {g : F} (hg : ∀ W' : TypeTwo C F, IsOver ht W' → W'.val g ≤ 1)
    (hint : IsIntegral (Algebra.adjoin C {t}) g)
    (Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring)) (hQ : W.red t ∈ Q.V) :
    W.red g ∈ Q.V := by
  letI : Algebra (RatFunc C) F := (coordAlgHom ht).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom ht).commutes c).symm
  have hxF : xF C F = t := xF_coord ht
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ ht)
  haveI : Finite (Ext C F) := finite_ext (F := F) hp hp1
  letI : Fintype (Ext C F) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_orthonormal_basis ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F) hp hp1)
  set v : Ext C F := ⟨W.val, hW⟩
  have hgn : gnorm C g ≤ 1 := gnorm_le_iff.2 fun v' ↦ hg ⟨v'.1, by
      ext c
      rw [comap_apply, valuation_algebraMap_C', NormedField.valuation_apply], by
      letI := hasExtension_C (F := F) v'
      exact Algebra.transcendental_def.2 ⟨_, transcendental_red_x v'⟩⟩ v'.2
  have hint' : IsIntegral (Algebra.adjoin C {xF C F}) g := hxF ▸ hint
  have hx : GaussFibre.red C (xF C F) v ∈ Q.V := by
    rw [hxF]
    exact hQ
  exact GaussFibre.red_mem_of_isIntegral hb hgn hint' v Q.V Q.algebraMap_mem hx

include hp hp1 in
/-- **G6.5 for type-2 valuations** (chart `t⁻¹`). -/
theorem TypeTwo.red_mem_of_isIntegral_inv {t : F} (ht : Transcendental C t) {W : TypeTwo C F}
    (hW : IsOver ht W) {g : F} (hg : ∀ W' : TypeTwo C F, IsOver ht W' → W'.val g ≤ 1)
    (hint : IsIntegral (Algebra.adjoin C {t⁻¹}) g)
    (Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring)) (hQ : W.red t⁻¹ ∈ Q.V) :
    W.red g ∈ Q.V := by
  letI : Algebra (RatFunc C) F := (coordAlgHom ht).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom ht).commutes c).symm
  have hxF : xF C F = t := xF_coord ht
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ ht)
  haveI : Finite (Ext C F) := finite_ext (F := F) hp hp1
  letI : Fintype (Ext C F) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_orthonormal_basis ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := F) hp hp1)
  set v : Ext C F := ⟨W.val, hW⟩
  have hgn : gnorm C g ≤ 1 := gnorm_le_iff.2 fun v' ↦ hg ⟨v'.1, by
      ext c
      rw [comap_apply, valuation_algebraMap_C', NormedField.valuation_apply], by
      letI := hasExtension_C (F := F) v'
      exact Algebra.transcendental_def.2 ⟨_, transcendental_red_x v'⟩⟩ v'.2
  have hint' : IsIntegral (Algebra.adjoin C {(xF C F)⁻¹}) g := hxF ▸ hint
  have hx : GaussFibre.red C (xF C F)⁻¹ v ∈ Q.V := by
    rw [hxF]
    exact hQ
  exact GaussFibre.red_mem_of_isIntegral_inv hb hgn hint' v Q.V Q.algebraMap_mem hx

end Chart

section RedAPI

variable {F : Type*} [Field F] [Algebra C F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

namespace TypeTwo

variable {W : TypeTwo C F} {f g : F}

lemma red_one : W.red (1 : F) = 1 := by
  rw [red_of_le (by simp)]
  exact map_one _

lemma red_neg (hf : W.val f ≤ 1) : W.red (-f) = -W.red f := by
  have hf' : W.val (-f) ≤ 1 := by rwa [Valuation.map_neg]
  rw [red_of_le hf, red_of_le hf', ← _root_.map_neg]
  rfl

lemma red_sub (hf : W.val f ≤ 1) (hg : W.val g ≤ 1) : W.red (f - g) = W.red f - W.red g := by
  have hg' : W.val (-g) ≤ 1 := by rwa [Valuation.map_neg]
  rw [sub_eq_add_neg, red_add hf hg', red_neg hg, sub_eq_add_neg]

lemma red_pow (hf : W.val f ≤ 1) (n : ℕ) : W.red (f ^ n) = W.red f ^ n := by
  induction n with
  | zero => simpa using red_one
  | succ n ih =>
    rw [pow_succ, red_mul (by rw [map_pow]; exact pow_le_one₀ zero_le hf) hf, ih, pow_succ]

lemma red_prod {ι : Type*} (s : Finset ι) (f : ι → F) (hf : ∀ i ∈ s, W.val (f i) ≤ 1) :
    W.red (∏ i ∈ s, f i) = ∏ i ∈ s, W.red (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using red_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, red_mul (hf a (Finset.mem_insert_self a s))
      (by rw [map_prod]; exact Finset.prod_le_one' fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
      ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)]

lemma red_algebraMap (c : C) (hc : ‖c‖ ≤ 1) :
    W.red (algebraMap C F c) = algebraMap 𝓀 (ResidueField W.val.valuationSubring)
      (residue (HenselComplete.integers C) ⟨c, (HenselComplete.mem_integers_iff c).2 hc⟩) := by
  have := red_smul (W := W) (f := 1) c (by exact_mod_cast hc) (by simp)
  rwa [red_one, Algebra.smul_def, mul_one, Algebra.smul_def, mul_one] at this

lemma red_eq_of_sub (hf : W.val f ≤ 1) (hg : W.val g ≤ 1) (h : W.val (f - g) < 1) :
    W.red f = W.red g := by
  rw [← sub_eq_zero, ← red_sub hf hg, red_eq_zero_iff ((Valuation.map_sub _ _ _).trans
    (max_le hf hg))]
  exact h

lemma red_ne_zero (hf : W.val f = 1) : W.red f ≠ 0 := by
  rw [Ne, red_eq_zero_iff hf.le, hf]
  exact lt_irrefl 1

lemma red_inv (hf : W.val f = 1) : W.red f⁻¹ = (W.red f)⁻¹ := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    simp at hf
  have hinv : W.val f⁻¹ = 1 := by rw [map_inv₀, hf, inv_one]
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← red_mul hf.le hinv.le, mul_inv_cancel₀ hf0, red_one]

end TypeTwo

end RedAPI

end SemistableReduction
