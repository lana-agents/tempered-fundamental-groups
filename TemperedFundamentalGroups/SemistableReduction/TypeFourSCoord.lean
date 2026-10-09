/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourCoord
import TemperedFundamentalGroups.SemistableReduction.TypeFourSheet
import TemperedFundamentalGroups.SemistableReduction.TypeFourKummerStep
import TemperedFundamentalGroups.SemistableReduction.TypeTwo

/-!
# The `s`-coordinate

Blueprint §9.12, leaf T4, part (G). For a transcendental `s ∈ F` (`F` finite over `C(x)`),
`SCoord s hs` is `F` with the `C(X)`-algebra structure `X ↦ s` (finite over `C(s)`); the `s`-disc
`D(b, |δ|)` has the chart `DRint 0 1 (Aff b δ (SCoord s hs))`.

* `isTypeFour_scoord`: if `ξ'` lies over a type-4 point of `C(x)`, its restriction `η` to `C(s)`
  is again of type 4 (otherwise `η` is a Gauss valuation, but the residue field of `ξ'` is `k` and
  its value group is `|C^×|`, `TypeFourValued`);
* `coordDense_aff`: density of `C(s)` gives density of `C((s - b)/δ)`;
* **`discDegree_sheet_eq_one`** (B4 in the `s`-coordinate): if `C(s)` is dense in `(F, ξ')`, then
  for every `s`-disc `E* = D(b', |δ|) ∋ η` inside a fixed small disc `E₀` (where distinct
  extensions of `η` have distinct centres, `Splitting.exists_center_injective`), the centre of `ξ'`
  on the chart of `E*` has disc degree one. An extension of `η` centred there has, on the smaller
  ring `R'(E₀)`, the same centre as `ξ'`, hence is `ξ'`; and `ξ'` has local degree one
  (`natDegree_eq_one_of_coordDense`).
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open Splitting GaussFibre DiscCount AffineTwist LocalGlobal GaussLimit

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

/-! ### The field with coordinate `s` -/

section SCoord

variable {F : Type*} [Field F] [Algebra C F]

variable (C) in
/-- `F` with the coordinate `s`: the `C(X)`-algebra structure `X ↦ s`. -/
@[nolint unusedArguments]
def SCoord (s : F) (_hs : Transcendental C s) : Type _ := F

variable {s : F} (hs : Transcendental C s)

instance : Field (SCoord C s hs) := inferInstanceAs (Field F)

instance : Algebra C (SCoord C s hs) := inferInstanceAs (Algebra C F)

noncomputable instance : Algebra (RatFunc C) (SCoord C s hs) :=
  (coordAlgHom hs).toRingHom.toAlgebra

instance : IsScalarTower C (RatFunc C) (SCoord C s hs) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom hs).commutes c).symm

/-- The identity `F → SCoord C s hs`. -/
def toS : F ≃+* SCoord C s hs := RingEquiv.refl F

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma toS_algebraMap (c : C) : toS hs (algebraMap C F c) = algebraMap C (SCoord C s hs) c := rfl

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma algebraMap_scoord (P : C[X]) :
    algebraMap (RatFunc C) (SCoord C s hs) (algebraMap C[X] (RatFunc C) P) =
      toS hs (aeval s P) :=
  coordAlgHom_algebraMap hs P

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma xF_scoord : xF C (SCoord C s hs) = toS hs s := by
  rw [xF, ← RatFunc.algebraMap_X, algebraMap_scoord, aeval_X]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma aeval_xF_scoord (P : C[X]) : aeval (xF C (SCoord C s hs)) P = toS hs (aeval s P) := by
  rw [aeval_xF, algebraMap_scoord]

instance [IsCurveFunctionField C F] : IsCurveFunctionField C (SCoord C s hs) :=
  inferInstanceAs (IsCurveFunctionField C F)

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma transcendental_xF_scoord : Transcendental C (xF C (SCoord C s hs)) := by
  rw [xF_scoord]; exact hs

instance [IsCurveFunctionField C F] : FiniteDimensional (RatFunc C) (SCoord C s hs) :=
  finiteDimensional_of_transcendental (transcendental_xF_scoord hs)

end SCoord

/-! ### The restriction to `C(s)` is of type 4 -/

section TypeFour

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  {ξ' : Valuation F ℝ≥0} {s : F} (hs : Transcendental C s)

/-- `ξ'` on `SCoord C s hs`. -/
noncomputable def valS (ξ' : Valuation F ℝ≥0) : Valuation (SCoord C s hs) ℝ≥0 :=
  ξ'.comap (toS hs).symm.toRingHom

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma valS_apply (y : F) : valS hs ξ' (toS hs y) = ξ' y := rfl

/-- **The restriction of `ξ'` to `C(s)` is of type 4.** -/
theorem isTypeFour_scoord (hξ : IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) :
    IsTypeFour ((valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))) := by
  have hC : ∀ c : C, ξ' (algebraMap C F c) = ‖c‖₊ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, ← Valuation.comap_apply, hξ.map_C,
      NormedField.valuation_apply]
  set η := (valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))
  have hηlin : ∀ b : C, radius η b = ξ' (s - algebraMap C F b) := fun b ↦ by
    change valS hs ξ' (algebraMap (RatFunc C) (SCoord C s hs)
      (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
    rw [algebraMap_scoord, map_sub, aeval_X, aeval_C, valS_apply]
  have hηC : ∀ c : C, η (algebraMap C (RatFunc C) c) = NormedField.valuation c := fun c ↦ by
    change valS hs ξ' (algebraMap (RatFunc C) (SCoord C s hs) (algebraMap C (RatFunc C) c)) = _
    rw [← IsScalarTower.algebraMap_apply, ← toS_algebraMap, valS_apply, hC,
      NormedField.valuation_apply]
  refine ⟨hηC, fun a ↦ ?_⟩
  by_contra! hmin
  have hgauss := eq_gaussRat_of_le hηC hmin
  have hsa : s - algebraMap C F a ≠ 0 := fun h ↦ hs (by
    rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap a)
  obtain ⟨γ, hγ, hγv⟩ := exists_eq_nnnorm hξ (L := F) rfl hsa
  have hy : ξ' ((s - algebraMap C F a) * algebraMap C F γ⁻¹) ≤ 1 := by
    rw [map_mul, hγv, hC, nnnorm_inv, mul_inv_cancel₀ (nnnorm_pos.2 hγ).ne']
  obtain ⟨c, -, hc⟩ := exists_sub_lt_one hξ (L := F) rfl hy
  have hlt : ξ' (s - algebraMap C F (a + γ * c)) < ‖γ‖₊ := by
    have : s - algebraMap C F (a + γ * c) = algebraMap C F γ *
        ((s - algebraMap C F a) * algebraMap C F γ⁻¹ - algebraMap C F c) := by
      rw [mul_sub, ← mul_assoc, mul_comm (algebraMap C F γ), mul_assoc, ← map_mul,
        mul_inv_cancel₀ hγ, map_one, mul_one, map_add, map_mul]
      ring
    rw [this, map_mul, hC]
    calc ‖γ‖₊ * _ < ‖γ‖₊ * 1 := mul_lt_mul_of_pos_left hc (nnnorm_pos.2 hγ)
      _ = ‖γ‖₊ := mul_one _
  have hge : ‖γ‖₊ ≤ ξ' (s - algebraMap C F (a + γ * c)) := by
    rw [← hηlin, radius, hgauss, gaussRat_algebraMap, gauss_X_sub_C, val_radiusUnit, hηlin, hγv]
    exact le_max_right _ _
  exact absurd hlt (not_lt.2 hge)

end TypeFour

/-! ### Discs in the `s`-coordinate -/

section Disc

omit [IsAlgClosed C] in
/-- **Inclusion of disc charts**: `O_C[(x - b₀)/c₀] ⊆ O_C[(x - b')/δ]` if `|δ| ≤ |c₀|` and
`|b' - b₀| ≤ |c₀|` (the disc `D(b', |δ|)` lies in `D(b₀, |c₀|)`). -/
lemma discRing_le_discRing {b₀ c₀ b' δ : C} (hc₀ : c₀ ≠ 0) (hδ : δ ≠ 0) (hδc : ‖δ‖ ≤ ‖c₀‖)
    (hbb : ‖b' - b₀‖ ≤ ‖c₀‖) : discRing b₀ c₀ ≤ discRing b' δ := by
  have hint : ∀ e : C, ‖e‖ ≤ 1 → algebraMap C (RatFunc C) e ∈ discRing b' δ := fun e he ↦
    algebraMap_mem_discRing (by exact_mod_cast he)
  have ht : gaussCoord b' δ ∈ discRing b' δ := Subring.subset_closure (Or.inr rfl)
  refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
  · rintro _ ⟨e, he, rfl⟩
    exact Subring.subset_closure (Or.inl ⟨e, he, rfl⟩)
  · rintro _ rfl
    have hrel : gaussCoord b₀ c₀ = algebraMap C (RatFunc C) (δ / c₀) * gaussCoord b' δ +
        algebraMap C (RatFunc C) ((b' - b₀) / c₀) := by
      rw [gaussCoord_eq, gaussCoord_eq]
      have hδ' : algebraMap C (RatFunc C) δ ≠ 0 := (_root_.map_ne_zero _).2 hδ
      have hc' : algebraMap C (RatFunc C) c₀ ≠ 0 := (_root_.map_ne_zero _).2 hc₀
      simp only [map_div₀, map_inv₀, map_sub]
      field_simp
      ring
    rw [hrel]
    refine add_mem (mul_mem (hint _ ?_) ht) (hint _ ?_)
    · rw [norm_div]; exact div_le_one_of_le₀ hδc (norm_nonneg _)
    · rw [norm_div]; exact div_le_one_of_le₀ hbb (norm_nonneg _)

end Disc

/-! ### The chart of an `s`-disc -/

section Sheet

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] {s : F} (hs : Transcendental C s) (b : C) {δ : C} (hδ : δ ≠ 0)

/-- The identification of `F` with the chart field of the `s`-disc `D(b, |δ|)`. -/
noncomputable def toG : F ≃+* Aff b δ hδ (SCoord C s hs) := (toS hs).trans (toAff hδ)

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
lemma toG_algebraMap (c : C) : toG hs b hδ (algebraMap C F c) = algebraMap C _ c := rfl

/-- `toG` as a `C`-algebra isomorphism. -/
noncomputable def toGC : F ≃ₐ[C] Aff b δ hδ (SCoord C s hs) :=
  { toG hs b hδ with commutes' := fun _ ↦ rfl }

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
lemma aeval_toG (z : F) (P : C[X]) : aeval (toG hs b hδ z) P = toG hs b hδ (aeval z P) :=
  (Polynomial.aeval_algHom_apply (toGC hs b hδ).toAlgHom z P).symm

omit [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F] in
/-- The coordinate of the chart of `D(b, |δ|)` is `(s - b)/δ`. -/
lemma xF_G : xF C (Aff b δ hδ (SCoord C s hs)) =
    toG hs b hδ (algebraMap C F δ⁻¹ * (s - algebraMap C F b)) := by
  rw [xF_aff, gaussCoord_eq, map_mul, map_sub, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]
  change toAff hδ (_ * (xF C (SCoord C s hs) - _)) = _
  rw [xF_scoord]
  rfl

/-- `ξ'` on the chart field of `D(b, |δ|)`. -/
noncomputable def valG (ξ' : Valuation F ℝ≥0) : Valuation (Aff b δ hδ (SCoord C s hs)) ℝ≥0 :=
  ξ'.comap (toG hs b hδ).symm.toRingHom

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
lemma valG_apply (ξ' : Valuation F ℝ≥0) (y : F) : valG hs b hδ ξ' (toG hs b hδ y) = ξ' y := by
  change ξ' ((toG hs b hδ).symm (toG hs b hδ y)) = _
  rw [RingEquiv.symm_apply_apply]

omit [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F] in
/-- Density of `C(s)` gives density of `C((s - b)/δ)`. -/
lemma coordDense_G {ξ' : Valuation F ℝ≥0} (hd : CoordDense C ξ' s) :
    CoordDense C (valG hs b hδ ξ') (xF C (Aff b δ hδ (SCoord C s hs))) := by
  intro y ε hε
  obtain ⟨P, Q, hQ, h⟩ := hd ((toG hs b hδ).symm y) ε hε
  have hcomp : ∀ R : C[X], aeval (xF C (Aff b δ hδ (SCoord C s hs)))
      (R.comp (Polynomial.C δ * X + Polynomial.C b)) = toG hs b hδ (aeval s R) := by
    intro R
    rw [aeval_comp, map_add, map_mul, aeval_C, aeval_C, aeval_X, xF_G, ← toG_algebraMap hs b hδ,
      ← toG_algebraMap hs b hδ, ← map_mul, ← map_add, aeval_toG]
    congr 2
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hδ, map_one, one_mul, sub_add_cancel]
  refine ⟨P.comp (Polynomial.C δ * X + Polynomial.C b), Q.comp (Polynomial.C δ * X +
    Polynomial.C b), ?_, ?_⟩
  · rw [hcomp]; exact (_root_.map_ne_zero _).2 hQ
  · rw [hcomp, hcomp, ← map_div₀, ← RingEquiv.apply_symm_apply (toG hs b hδ) y, ← map_sub,
      valG_apply]
    exact h

end Sheet

/-! ### B4 in the `s`-coordinate -/

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
/-- Integrality passes to larger subrings. -/
lemma isIntegral_of_le_subring {K L : Type*} [Field K] [Field L] [Algebra K L]
    {A B : Subring K} (hAB : A ≤ B) {y : L} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨P, hm, hP⟩ := hy
  refine ⟨P.map (Subring.inclusion hAB), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hP

section SheetDegree

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] [CharZero C]
  {s : F} (hs : Transcendental C s)

attribute [local instance] GaussFibre.isCurveFunctionField_F

/-- **B4 in the `s`-coordinate: the sheet of a small disc.** Let `C(s)` be dense in `(F, ξ')`,
`η = ξ'|_{C(s)}` (of type 4), and `E₀ = D(b₀, |a₀ - b₀|)` a disc around `η` on whose chart distinct
extensions of `η` have distinct centres. For a disc `E* = D(b', |δ|) ∋ η` inside `E₀`, the centre
`P₂` of `ξ'` on the chart of `E*` has disc degree one. -/
theorem discDegree_sheet_eq_one {ξ' : Valuation F ℝ≥0}
    (hξ : IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) (hd : CoordDense C ξ' s)
    {a₀ b₀ : C}
    (hb₀ : radius ((valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))) b₀ <
      radius ((valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))) a₀)
    (hinj : ∀ (ξ₁ ξ₂ : Valuation (SCoord C s hs) ℝ≥0)
      (h₁ : ξ₁.comap (algebraMap (RatFunc C) (SCoord C s hs)) =
        (valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs)))
      (h₂ : ξ₂.comap (algebraMap (RatFunc C) (SCoord C s hs)) =
        (valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))),
      center (isDiscVal_comap (isTypeFour_scoord hs hξ) h₁ hb₀) =
        center (isDiscVal_comap (isTypeFour_scoord hs hξ) h₂ hb₀) → ξ₁ = ξ₂)
    {b' δ : C} (hδ : δ ≠ 0) (hδc : ‖δ‖ ≤ ‖a₀ - b₀‖) (hbb : ‖b' - b₀‖ ≤ ‖a₀ - b₀‖)
    (hin : ξ' (algebraMap C F δ⁻¹ * (s - algebraMap C F b')) < 1)
    (P₂ : Ideal (DRint (0 : C) 1 (Aff b' δ hδ (SCoord C s hs)))) [hP₂ : P₂.IsMaximal]
    (hcen : ∀ y ∈ P₂, valG hs b' hδ ξ' (y : Aff b' δ hδ (SCoord C s hs)) < 1)
    (ν : DiscVal (0 : C) 1) : discDegree ν P₂ = 1 := by
  classical
  haveI : Algebra.IsSeparable (RatFunc C) (Aff b' δ hδ (SCoord C s hs)) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.IsSeparable (RatFunc C) (SCoord C s hs) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  set G := Aff b' δ hδ (SCoord C s hs)
  set ξ₂ := valG hs b' hδ ξ'
  set η := (valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))
  have hC : ∀ c : C, ξ' (algebraMap C F c) = ‖c‖₊ := fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, ← Valuation.comap_apply, hξ.map_C,
      NormedField.valuation_apply]
  have hξ₂ : IsDiscVal (0 : C) 1 (ξ₂.comap (algebraMap (RatFunc C) G)) := by
    refine ⟨fun c ↦ ?_, ?_⟩
    · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, ← toG_algebraMap hs b' hδ,
        valG_apply, hC]
    · rw [Valuation.comap_apply, SmoothVertex.gaussCoord_zero_one]
      change ξ₂ (xF C G) < 1
      rw [xF_G, valG_apply]
      exact hin
  obtain ⟨ν₀, hν₀⟩ : ∃ ν₀ : DiscVal (0 : C) 1, ν₀.val = ξ₂.comap (algebraMap (RatFunc C) G) :=
    ⟨⟨_, hξ₂⟩, rfl⟩
  -- `P₂` is the centre of `ξ'`
  have hPc : P₂ = center hξ₂ :=
    hP₂.eq_of_le (center_isMaximal one_ne_zero hξ₂).ne_top fun y hy ↦ hcen y hy
  rw [discDegree_eq one_ne_zero ν ν₀ P₂]
  obtain ⟨g₀, hg₀⟩ := TypeFour.exists_eq_extValuation' ν₀ (ξ' := ξ₂) hν₀.symm
  have hdeg : g₀.1.natDegree = 1 :=
    natDegree_eq_one_of_coordDense ν₀ g₀ (by rw [hg₀]; exact coordDense_G hs b' hδ hd)
  have hcen₀ : center (isDiscVal_comap_extValuation g₀) = P₂ := by
    rw [hPc]
    ext y
    rw [mem_center_iff, mem_center_iff, hg₀]
  -- the only extension of `η` centred at `P₂` is `ξ'`
  have hc₀ : a₀ - b₀ ≠ 0 := sub_ne_zero_of_radius_lt (isTypeFour_scoord hs hξ) hb₀
  have huniq : ∀ g : Factor (DiscField ν₀) (UniformSpace.Completion (DiscField ν₀)) G,
      center (isDiscVal_comap_extValuation g) = P₂ → g = g₀ := by
    intro g hg
    set w : Valuation (SCoord C s hs) ℝ≥0 := (extValuation g).comap (toAff hδ).toRingHom
    have hw : w.comap (algebraMap (RatFunc C) (SCoord C s hs)) = η := by
      refine Valuation.ext fun φ ↦ ?_
      have h1 := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u ((aff b' δ hδ).symm φ))
        (Splitting.comap_extValuation ν₀ g)
      simp only [Valuation.comap_apply] at h1
      rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply] at h1
      simp only [Valuation.comap_apply]
      change extValuation g (toAff hδ (algebraMap (RatFunc C) (SCoord C s hs) φ)) = _
      rw [h1, hν₀, Valuation.comap_apply]
      change ξ₂ (algebraMap (RatFunc C) G ((aff b' δ hδ).symm φ)) = _
      rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply]
      rfl
    have heq := hinj w (valS hs ξ') hw rfl (by
      ext y
      rw [mem_center_iff, mem_center_iff]
      have hY : IsIntegral (discRing (0 : C) 1) (toAff hδ (y : SCoord C s hs) : G) :=
        (isIntegral_toAff_iff hδ _).2 (isIntegral_of_le_subring
          (discRing_le_discRing hc₀ hδ hδc hbb) y.2)
      have h1 : (⟨_, hY⟩ : DRint (0 : C) 1 G) ∈ center (isDiscVal_comap_extValuation g) ↔
          (⟨_, hY⟩ : DRint (0 : C) 1 G) ∈ center hξ₂ := by rw [hg, hPc]
      rw [mem_center_iff, mem_center_iff] at h1
      exact h1)
    apply extValuation_injective
    rw [hg₀]
    refine Valuation.ext fun z ↦ ?_
    have := congrArg (fun u : Valuation (SCoord C s hs) ℝ≥0 ↦ u ((toAff hδ).symm z)) heq
    simp only [w, Valuation.comap_apply] at this
    change extValuation g (toAff hδ ((toAff hδ).symm z)) = _ at this
    rw [RingEquiv.apply_symm_apply] at this
    rw [this]
    rfl
  rw [discDegree, Finset.sum_eq_single_of_mem g₀
    (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcen₀⟩)
    (fun g hg hne ↦ absurd (huniq g (Finset.mem_filter.1 hg).2) hne), hdeg]

end SheetDegree

end TypeFour

end SemistableReduction
