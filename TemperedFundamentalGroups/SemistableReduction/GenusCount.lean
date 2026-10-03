/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.InfinityChart

/-!
# Counting Riemann–Roch dimensions over the Gauss point

Blueprint §9.5, G6.5–G6.6. Let `C` be algebraically closed and `F / C(X)` finite, `F` a function
field of one variable over `C` with coordinate `x`, and `w` the extensions of the Gauss valuation
with residue curves `κ(w)`.

* `isIntegral_of_mem_rrSpace`: elements of `L(m (x)_∞)` are integral over `C[x]`, and divided by
  `xᵐ` integral over `C[x⁻¹]` (Chevalley: otherwise a place of `F / C` separates);
* **G6.5** `red_mem_rrSpace`: the reduction of `f ∈ L(m (x)_∞)` with `‖f‖ ≤ 1` lies in
  `L(m (x̄)_∞)` on every residue curve;
* **G6.6** `ell_le_sum_ell`: `ℓ(m (x)_∞) ≤ Σ_w ℓ_{κ(w)}(m (x̄)_∞)` (G6.4), and the **weak genus
  inequality** `sum_genus_le_add_card`: `Σ_w g(κ(w)) ≤ g(F) + #{w} - 1`.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion CurvePlace

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Chevalley

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F] in
/-- An element lying in every place of `F / C` containing `t` is integral over `C[t]`. -/
lemma isIntegral_of_forall_mem {t f : F}
    (h : ∀ P : CurvePlace C F, t ∈ P.V → f ∈ P.V) : IsIntegral (Algebra.adjoin C {t}) f := by
  by_contra hf
  set A := integralClosure (Algebra.adjoin C {t}) F
  have hfA : f ∉ A.toSubring := hf
  haveI : IsIntegrallyClosedIn A.toSubring F := inferInstanceAs (IsIntegrallyClosedIn A F)
  obtain ⟨V, hAV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hfA
  have hmem (y : F) (hy : y ∈ Algebra.adjoin C {t}) : y ∈ V := hAV <| by
    change y ∈ A
    rw [mem_integralClosure_iff]
    exact (isIntegral_algebraMap (x := (⟨y, hy⟩ : Algebra.adjoin C {t})))
  have hC (c : C) : algebraMap C F c ∈ V := hmem _ (Subalgebra.algebraMap_mem _ c)
  have ht : t ∈ V := hmem _ (Algebra.self_mem_adjoin_singleton C t)
  have hne : V ≠ ⊤ := fun h' ↦ hfV (h' ▸ trivial)
  exact hfV (h ⟨V, hC, hne⟩ ht)

end Chevalley

section CurveF

omit [IsUltrametricDist C] in
/-- The image of `C(X)` in `F` is `C(x)`. -/
lemma mem_adjoin_xF_iff (z : F) :
    z ∈ C⟮xF C F⟯ ↔ ∃ φ : RatFunc C, algebraMap (RatFunc C) F φ = z := by
  set φ := IsScalarTower.toAlgHom C (RatFunc C) F
  have h := IntermediateField.adjoin_map C {(RatFunc.X : RatFunc C)} φ
  rw [RatFunc.adjoin_X, Set.image_singleton, IsScalarTower.coe_toAlgHom'] at h
  rw [← h, IntermediateField.mem_map]
  simp [φ]

omit [IsUltrametricDist C] in
lemma finrank_adjoin_xF :
    Module.finrank C⟮xF C F⟯ F = Module.finrank (RatFunc C) F := by
  set E := C⟮xF C F⟯
  let i : RatFunc C ≃+* E :=
    RingEquiv.ofBijective ((algebraMap (RatFunc C) F : _ →+* _).codRestrict E.toSubfield
      fun y ↦ (mem_adjoin_xF_iff _).2 ⟨y, rfl⟩)
      ⟨fun a b h ↦ (algebraMap (RatFunc C) F).injective (congrArg Subtype.val h), fun z ↦ by
        obtain ⟨y, hy⟩ := (mem_adjoin_xF_iff (z : F)).1 z.2
        exact ⟨y, Subtype.ext hy⟩⟩
  exact (Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) (by ext; rfl)).symm

omit [IsUltrametricDist C] in
lemma transcendental_xF : Transcendental C (xF C F) := by
  have h : Transcendental C (RatFunc.X : RatFunc C) := RatFunc.transcendental_X
  rw [← transcendental_algebraMap_iff (algebraMap (RatFunc C) F).injective] at h
  exact h

omit [IsUltrametricDist C] in
/-- A finite extension of `C(X)` is a function field of one variable over `C`. -/
theorem isCurveFunctionField_F [FiniteDimensional (RatFunc C) F] : IsCurveFunctionField C F :=
  ⟨⟨xF C F, transcendental_xF, Module.finite_of_finrank_pos (by
    rw [finrank_adjoin_xF]; exact Module.finrank_pos)⟩⟩

end CurveF

section RR

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField_F

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma xF_notMem_range : xF C F ∉ (algebraMap C F).range := by
  rintro ⟨c, hc⟩
  exact transcendental_xF (hc ▸ isAlgebraic_algebraMap c)

omit [IsUltrametricDist C] in
/-- Elements of `L(m (x)_∞)` are integral over `C[x]`. -/
lemma isIntegral_of_mem_rrSpace {m : ℕ} {f : F}
    (hf : f ∈ rrSpace (m • poleDivisor C (xF C F))) :
    IsIntegral (Algebra.adjoin C {xF C F}) f := by
  refine isIntegral_of_forall_mem fun P hP ↦ P.valuation_le_one_iff.1 ?_
  have := hf P
  rwa [Finsupp.smul_apply, poleDivisor_apply, P.poleOrder_eq_zero_iff.2 hP, Nat.cast_zero,
    smul_zero, exp_zero] at this

omit [IsUltrametricDist C] in
/-- For `f ∈ L(m (x)_∞)`, `f / xᵐ` is integral over `C[x⁻¹]`. -/
lemma isIntegral_div_of_mem_rrSpace {m : ℕ} {f : F}
    (hf : f ∈ rrSpace (m • poleDivisor C (xF C F))) :
    IsIntegral (Algebra.adjoin C {(xF C F)⁻¹}) (f * (xF C F)⁻¹ ^ m) := by
  refine isIntegral_of_forall_mem fun P hP ↦ P.valuation_le_one_iff.1 ?_
  have hfP := hf P
  rw [Finsupp.smul_apply, poleDivisor_apply, nsmul_eq_mul] at hfP
  rw [map_mul, map_pow]
  by_cases hx : xF C F ∈ P.V
  · rw [P.poleOrder_eq_zero_iff.2 hx, Nat.cast_zero, mul_zero, exp_zero] at hfP
    exact mul_le_one' hfP (pow_le_one₀ zero_le (P.valuation_le_one_iff.2 hP))
  · have hv := P.valuation_eq_exp_poleOrder hx
    rw [map_inv₀, hv, ← exp_neg, ← exp_nsmul]
    calc P.valuation f * exp (m • -(P.poleOrder (xF C F) : ℤ)) ≤
        exp (m * P.poleOrder (xF C F) : ℤ) * exp (m • -(P.poleOrder (xF C F) : ℤ)) := by
          gcongr
      _ = 1 := by rw [← exp_add, smul_neg, nsmul_eq_mul, add_neg_cancel, exp_zero]

end RR

section Count

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [Fintype (Ext C F)]

attribute [local instance] isCurveFunctionField_F isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [Fintype (Ext C F)] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma red_inv_xF (w : Ext C F) : red C (xF C F)⁻¹ w = (red C (xF C F) w)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  rw [← red_mul (valuation_xF w).le (valuation_xF_inv w).le, mul_inv_cancel₀, red_one]
  intro h
  have := valuation_xF (F := F) w
  rw [h, map_zero] at this
  exact zero_ne_one this

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] in
lemma gnorm_xF_inv_pow (m : ℕ) : gnorm C ((xF C F)⁻¹ ^ m) ≤ 1 :=
  gnorm_le_iff.2 fun w ↦ by rw [map_pow, valuation_xF_inv, one_pow]

variable {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
include hb

/-- **G6.5**: the reduction of `f ∈ L(m (x)_∞)` with `‖f‖ ≤ 1` lies in `L(m (x̄)_∞)`. -/
theorem red_mem_rrSpace {m : ℕ} {f : F} (hf : f ∈ rrSpace (m • poleDivisor C (xF C F)))
    (hn : gnorm C f ≤ 1) (w : Ext C F) :
    red C f w ∈ rrSpace (m • poleDivisor 𝓀 (red C (xF C F) w)) := by
  intro Q
  rw [Finsupp.smul_apply, poleDivisor_apply, nsmul_eq_mul]
  by_cases hx : red C (xF C F) w ∈ Q.V
  · have := red_mem_of_isIntegral hb hn (isIntegral_of_mem_rrSpace hf) w Q.V
      Q.algebraMap_mem hx
    refine (Q.valuation_le_one_iff.2 this).trans ?_
    rw [← exp_zero, exp_le_exp]
    positivity
  · have hxinv : red C (xF C F)⁻¹ w ∈ Q.V := by
      rw [red_inv_xF]
      exact (Q.V.mem_or_inv_mem _).resolve_left hx
    have hg : gnorm C (f * (xF C F)⁻¹ ^ m) ≤ 1 :=
      (gnorm_mul_le _ _).trans (mul_le_one' hn (gnorm_xF_inv_pow m))
    have hmem := red_mem_of_isIntegral_inv hb hg (isIntegral_div_of_mem_rrSpace hf) w Q.V
      Q.algebraMap_mem hxinv
    have hfw : w.1 f ≤ 1 := (le_gnorm w f).trans hn
    have hxw : w.1 ((xF C F)⁻¹ ^ m) ≤ 1 := by rw [map_pow, valuation_xF_inv, one_pow]
    rw [red_mul hfw hxw, red_pow (valuation_xF_inv w).le, red_inv_xF] at hmem
    have h1 := Q.valuation_le_one_iff.2 hmem
    have hv := Q.valuation_eq_exp_poleOrder hx
    rw [map_mul, map_pow, map_inv₀, hv, ← exp_neg, ← exp_nsmul] at h1
    rw [← mul_one (exp _), ← exp_zero]
    have hpos : (0 : ℤᵐ⁰) < exp (m • -(Q.poleOrder (red C (xF C F) w) : ℤ)) := exp_pos
    calc Q.valuation (red C f w) = Q.valuation (red C f w) *
          exp (m • -(Q.poleOrder (red C (xF C F) w) : ℤ)) *
          exp (m * Q.poleOrder (red C (xF C F) w) : ℤ) := by
          rw [mul_assoc, ← exp_add, smul_neg, nsmul_eq_mul, neg_add_cancel, exp_zero, mul_one]
      _ ≤ 1 * exp (m * Q.poleOrder (red C (xF C F) w) : ℤ) := by gcongr
      _ = _ := by rw [one_mul, exp_zero, mul_one]

omit hb in
variable (C F) in
/-- The product `Π_w L_{κ(w)}(m (x̄)_∞)` of the Riemann–Roch spaces of the residue curves. -/
noncomputable def piRR (m : ℕ) :
    Submodule 𝓀 (Π w : Ext C F, ResidueField w.1.valuationSubring) :=
  Submodule.pi Set.univ fun w ↦ rrSpace (m • poleDivisor 𝓀 (red C (xF C F) w))

omit hb in
/-- `piRR` is the product of the Riemann–Roch spaces. -/
noncomputable def piRREquiv (m : ℕ) :
    piRR C F m ≃ₗ[𝓀] Π w : Ext C F, rrSpace (m • poleDivisor 𝓀 (red C (xF C F) w)) where
  toFun x w := ⟨x.1 w, x.2 w trivial⟩
  invFun y := ⟨fun w ↦ (y w).1, fun w _ ↦ (y w).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

omit hb [Fintype (Ext C F)] in
instance finiteDimensional_piRR [Finite (Ext C F)] (m : ℕ) : FiniteDimensional 𝓀 (piRR C F m) :=
  LinearEquiv.finiteDimensional (piRREquiv m).symm

omit hb in
lemma finrank_piRR (m : ℕ) :
    Module.finrank 𝓀 (piRR C F m) =
      ∑ w : Ext C F, ell (m • poleDivisor 𝓀 (red C (xF C F) w)) := by
  rw [(piRREquiv m).finrank_eq, Module.finrank_pi_fintype]
  rfl

/-- **G6.6** (counting): `ℓ(m (x)_∞) ≤ Σ_w ℓ_{κ(w)}(m (x̄)_∞)`. -/
theorem ell_le_sum_ell (m : ℕ) :
    ell (m • poleDivisor C (xF C F)) ≤
      ∑ w : Ext C F, ell (m • poleDivisor 𝓀 (red C (xF C F) w)) := by
  haveI := nonempty_ext_of_orthonormal hb
  rw [← finrank_piRR]
  exact finrank_le_of_red_mem b hb (rrSpace (m • poleDivisor C (xF C F))) (piRR C F m)
    fun f hf hn w _ ↦ red_mem_rrSpace hb hf hn w

/-- **The weak genus inequality over the Gauss point**:
`Σ_w g(κ(w)) ≤ g(F) + #{w} - 1`, where `w` runs over the extensions of `w_{0,1}`. -/
theorem sum_genus_le_add_card
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F) :
    (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) ≤
      genus C F + Fintype.card (Ext C F) - 1 := by
  classical
  obtain ⟨cF, hcF⟩ := ell_eq_of_le_degree (k := C) (κ := F)
  choose cw hcw using fun w : Ext C F ↦
    ell_eq_of_le_degree (k := 𝓀) (κ := ResidueField w.1.valuationSubring)
  set N := Module.finrank (RatFunc C) F
  set m : ℕ := cF.toNat + ∑ w, (cw w).toNat
  have hN : 1 ≤ N := Module.finrank_pos
  have hdegF : (m • poleDivisor C (xF C F)).degree = m * N := by
    rw [map_nsmul, degree_poleDivisor xF_notMem_range, finrank_adjoin_xF, nsmul_eq_mul]
  have hxw (w : Ext C F) :
      red C (xF C F) w ∉ (algebraMap 𝓀 (ResidueField w.1.valuationSubring)).range := by
    rintro ⟨c, hc⟩
    exact transcendental_red_x w (hc ▸ isAlgebraic_algebraMap c)
  have hfw (w : Ext C F) : 1 ≤ inertiaDeg (gauss1 C) w.1 := by
    haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := finite_residueField
    exact Module.finrank_pos
  have hdegw (w : Ext C F) : (m • poleDivisor 𝓀 (red C (xF C F) w)).degree =
      m * inertiaDeg (gauss1 C) w.1 := by
    rw [map_nsmul, degree_poleDivisor (hxw w), finrank_adjoin_red_x, nsmul_eq_mul]
  have hm1 : cF ≤ m := by
    have := Int.self_le_toNat cF
    push_cast [m]
    have : (0 : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) := Finset.sum_nonneg fun _ _ ↦ by positivity
    linarith
  have hmw (w : Ext C F) : cw w ≤ m := by
    have h1 := Int.self_le_toNat (cw w)
    have h2 : ((cw w).toNat : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) :=
      Finset.single_le_sum (f := fun w ↦ ((cw w).toNat : ℤ)) (fun _ _ ↦ by positivity)
        (Finset.mem_univ w)
    push_cast [m]
    linarith [Int.natCast_nonneg cF.toNat]
  have hF := hcF _ (by
    rw [hdegF]
    nlinarith)
  have hw (w : Ext C F) := hcw w _ (by
    rw [hdegw]
    have := hfw w
    have : (m : ℤ) ≤ m * inertiaDeg (gauss1 C) w.1 := by
      exact_mod_cast Nat.le_mul_of_pos_right m this
    linarith [hmw w])
  have hle := ell_le_sum_ell hb m
  have hle' : (ell (m • poleDivisor C (xF C F)) : ℤ) ≤
      ∑ w : Ext C F, (ell (m • poleDivisor 𝓀 (red C (xF C F) w)) : ℤ) := by
    exact_mod_cast hle
  rw [hF, hdegF] at hle'
  simp only [hw, hdegw] at hle'
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hle'
  have hsumZ : (∑ w : Ext C F, (inertiaDeg (gauss1 C) w.1 : ℤ)) = N := by
    exact_mod_cast hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hle'
  rw [hsumZ] at hle'
  linarith

end Count

end GaussFibre

end SemistableReduction
