/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TwoVertexCharts

/-!
# The local `δ`-formula (Arzdorf–Wewers (2.3))

Blueprint §9.12, O12 / R5, step (1). For a finite extension `F` of `C(x)` and `0 < |c| < 1`, let
`T = TwoV c F` (the two-vertex model with vertices `w_{0,1}`, `w_{0,|c|}`, coordinate
`t = x + c/x`) and `G = Aff 0 c F` (the one-vertex model of `w_{0,|c|}`, coordinate `s = x/c`).
Subtracting the genus formulas (S7⁺, `GaussFibre.genus_eq_tot`) of `F` and `T` and identifying
the closed points away from the node by the locality of `δ` (`TwoVertexCharts`):

  **`Δ₀(F) + #Ext(G) = N(T) + Δ(G) + Σ_{w ∈ Ext G} g(κ(w))`** (`local_formula`),

where `Δ₀(F)` is the total `δ` of `F` over `x̄ = 0`, `N(T)` the total `δ` of `T` over the node
`t̄ = 0`, and `Δ(G)` the total `δ` of the finite chart of `G`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace LocalFormula

open GaussFibre TwoVertex AffineTwist ChartLocal TwoVertexCharts FundamentalInequality
  GaussStability

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

attribute [local instance] isCurveFunctionField isCurveFunctionField_F
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-! ### Valuations at transported branches -/

section Transport

variable {F₁ F₂ : Type*} [Field F₁] [Field F₂] [Algebra (RatFunc C) F₁] [Algebra (RatFunc C) F₂]
  [Algebra C F₁] [IsScalarTower C (RatFunc C) F₁] [Algebra C F₂] [IsScalarTower C (RatFunc C) F₂]
  [FiniteDimensional (RatFunc C) F₁] [FiniteDimensional (RatFunc C) F₂]

omit [CharZero C] in
/-- The valuation of a reduction at a transported branch. -/
lemma val_pmap_of {J J' : Type*} {κ : J → Type*} {κ' : J' → Type*} [∀ j, Field (κ j)]
    [∀ j, Field (κ' j)] [∀ j, Algebra 𝓀 (κ j)] [∀ j, Algebra 𝓀 (κ' j)]
    [∀ j, IsCurveFunctionField 𝓀 (κ j)] [∀ j, IsCurveFunctionField 𝓀 (κ' j)]
    (E : CompEmb 𝓀 κ κ') (b : DeltaCount.Branch 𝓀 κ) {x : κ b.1} {y : κ' (E.ι b.1)}
    (h : E.e b.1 x = y) : (E.pmap b).2.valuation y = b.2.valuation x := by
  rw [← h]
  exact CurvePlace.valuation_map_apply _ _ _

end Transport

/-! ### Generic facts for one field -/

section Generic

variable {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]

variable (C K) in
/-- The sum of the genera of the residue curves. -/
noncomputable def gsum : ℤ :=
  ∑ w : Ext C K, (genus 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring) : ℤ)

include hp hp1 in
/-- **The genus formula with arbitrary chart proofs.** -/
theorem genus_formula
    (hΛ₀ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)))
    (hΛi : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K)⁻¹ w) (redRing C K (xF C K)⁻¹)) :
    (genus C K : ℤ) + Fintype.card (Ext C K) - 1 =
      gsum C K + (tot0 C K hΛ₀ fun _ ↦ True : ℕ) +
        (totI C K hΛi fun 𝔫 ↦ (⟨_, hΛi.mem⟩ : redRing C K (xF C K)⁻¹) ∈ 𝔫 : ℕ) := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (F := K) ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := K) hp hp1)
  exact genus_eq_tot hb (sum_inertiaDeg_eq (F := K) hp hp1)

include hp hp1 in
theorem finite_dinf₀
    (hΛ₀ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K))) :
    {𝔫 : Ideal (redRing C K (xF C K)) | 𝔫.IsMaximal ∧
      dinf 𝓀 (fun w : Ext C K ↦ IsLocalRing.ResidueField w.1.valuationSubring) hΛ₀ 𝔫 ≠ 0}.Finite :=
    by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (F := K) ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := K) hp hp1)
  obtain ⟨σ, hσ, hσ0, hσc⟩ := exists_conductor_x hb (sum_inertiaDeg_eq (F := K) hp hp1)
  exact finite_dinf_ne_zero hΛ₀ hσ hσ0 hσc

include hp hp1 in
theorem finite_dinfI
    (hΛi : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K)⁻¹ w) (redRing C K (xF C K)⁻¹)) :
    {𝔫 : Ideal (redRing C K (xF C K)⁻¹) | 𝔫.IsMaximal ∧
      dinf 𝓀 (fun w : Ext C K ↦ IsLocalRing.ResidueField w.1.valuationSubring) hΛi 𝔫 ≠ 0}.Finite :=
    by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (F := K) ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := K) hp hp1)
  obtain ⟨σ, hσ, hσ0, hσc⟩ := exists_conductor_x_inv hb (sum_inertiaDeg_eq (F := K) hp hp1)
  exact finite_dinf_ne_zero hΛi hσ hσ0 hσc

omit [IsAlgClosed C] [CharZero C] [Algebra C K] [IsScalarTower C (RatFunc C) K]
  [FiniteDimensional (RatFunc C) K] [Fintype (GaussFibre.Ext C K)] in
/-- Two elements of value `≤ 1` whose difference has value `< 1` have the same reduction. -/
lemma red_eq_of_sub_lt {w : Ext C K} {f g : K} (hg : w.1 g ≤ 1) (h : w.1 (f - g) < 1) :
    red C f w = red C g w := by
  have : f = g + (f - g) := by ring
  rw [this, red_add hg h.le, (red_eq_zero_iff h.le).2 h, add_zero]

omit [IsAlgClosed C] [CharZero C] [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K]
  in
/-- A unit of reduction `1` lies in no proper ideal of a reduced chart. -/
lemma notMem_of_red_eq_one {t u : K} (hu : u ∈ intRing C K t) (h1 : ∀ w, red C u w = 1)
    {𝔫 : Ideal (redRing C K t)} (h𝔫 : 𝔫 ≠ ⊤) :
    (⟨fun w ↦ red C u w, red_mem_redRing hu⟩ : redRing C K t) ∉ 𝔫 := by
  intro h
  apply h𝔫
  rw [Ideal.eq_top_iff_one]
  convert h using 1
  exact Subtype.ext (funext fun w ↦ (h1 w).symm)

include hp hp1 in
/-- Splitting the finite chart along an element `a`. -/
theorem tot0_split
    (hΛ₀ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)))
    (a : redRing C K (xF C K)) :
    tot0 C K hΛ₀ (fun _ ↦ True) = tot0 C K hΛ₀ (fun 𝔫 ↦ a ∈ 𝔫) + tot0 C K hΛ₀ (fun 𝔫 ↦ a ∉ 𝔫) := by
  rw [tot0, tot0, tot0, ← finsum_dinf_or hΛ₀ (finite_dinf₀ hp hp1 hΛ₀) fun _ _ h h' ↦ h' h]
  refine finsum_mem_congr (Set.ext fun 𝔫 ↦ ?_) fun _ _ ↦ rfl
  simp only [Set.mem_setOf_eq, and_true]
  exact ⟨fun h ↦ ⟨h, em _⟩, fun h ↦ h.1⟩

end Generic

/-! ### The extensions of the Gauss point of `t` -/

section TwoV

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  {c : C} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1)

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιU_injective : Function.Injective (ιU (F := F) hc0 hc1) := fun w₁ w₂ h ↦
  Subtype.ext (Valuation.ext fun x ↦ by rw [← ιU_apply hc0 hc1 w₁, h, ιU_apply])

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιD_injective : Function.Injective (ιD (F := F) hc0 hc1) := fun w₁ w₂ h ↦
  Subtype.ext (Valuation.ext fun x ↦ by rw [← ιD_apply hc0 hc1 w₁, h, ιD_apply])

/-- The extensions of the Gauss point of `t` are the outer and the inner ones. -/
noncomputable def extSum : Ext C F ⊕ Ext C (Aff (0 : C) c hc0 F) ≃ Ext C (TwoV c F) :=
  Equiv.ofBijective (Sum.elim (ιU hc0 hc1) (ιD hc0 hc1)) ⟨by
    rintro (w₁ | w₁) (w₂ | w₂) h
    · exact congrArg Sum.inl (ιU_injective hc0 hc1 h)
    · exact absurd h (ιU_ne_ιD hc0 hc1 w₁ w₂)
    · exact absurd h.symm (ιU_ne_ιD hc0 hc1 w₂ w₁)
    · exact congrArg Sum.inr (ιD_injective hc0 hc1 h), fun w' ↦ by
    rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · exact ⟨Sum.inl w, rfl⟩
    · exact ⟨Sum.inr w, rfl⟩⟩

variable [Fintype (Ext C F)] [Fintype (Ext C (TwoV c F))]
  [Fintype (Ext C (Aff (0 : C) c hc0 F))]

omit [CharZero C] [FiniteDimensional (RatFunc C) F] in
include hc1 in
lemma card_twoV : Fintype.card (Ext C (TwoV c F)) =
    Fintype.card (Ext C F) + Fintype.card (Ext C (Aff (0 : C) c hc0 F)) := by
  rw [← Fintype.card_sum, Fintype.card_congr (extSum hc0 hc1)]

omit [CharZero C] in
include hc1 in
lemma gsum_twoV : gsum C (TwoV c F) = gsum C F + gsum C (Aff (0 : C) c hc0 F) := by
  rw [gsum, ← (extSum hc0 hc1).sum_comp, Fintype.sum_sum_type, gsum, gsum]
  congr 1

/-! #### Values at all extensions of the Gauss point of `t` -/

section Vals

variable (w' : Ext C (TwoV c F))
include hc0 hc1

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
lemma val_xT_le : w'.1 (toTwoV c (xF C F)) ≤ 1 := by
  rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact (valuation_ιU_x hc0 hc1 w).le
  · exact (valuation_ιD_toTwoV_x_lt hc0 hc1 w).le

omit [CharZero C] [Fintype (GaussFibre.Ext C F)] [Fintype (GaussFibre.Ext C (TwoV c F))]
  [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
lemma val_cxT_le : w'.1 (toTwoV c (cxF (F := F) c)) ≤ 1 := by
  rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · rw [ιU_apply, val_cxF_out]; exact_mod_cast hc1.le
  · rw [ιD_toTwoV, val_cxF_in]

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] hc0 in
lemma val_cT_lt : w'.1 (algebraMap C (TwoV c F) c) < 1 := by
  rw [valuation_algebraMap_C']; exact_mod_cast hc1

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
lemma val_qqT_le : w'.1 (toTwoV c (qq (F := F) c)) ≤ 1 := by
  rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · rw [ιU_apply, val_qq_out hc1 (valuation_algebraMap_C' w) (valuation_xF w)]
  · rw [ιD_toTwoV]
    exact (val_qq_in (v := w.1.comap (toAff hc0).toRingHom) hc0 hc1 (val_toAff_C hc0 w)
      (valuation_toAff_x hc0 w)).le.trans (by exact_mod_cast hc1.le)

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
lemma val_rrT_le : w'.1 (toTwoV c (rr (F := F) c)) ≤ 1 := by
  rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · rw [ιU_apply, val_rr_out hc1 (valuation_algebraMap_C' w) (valuation_xF w)]
    exact_mod_cast hc1.le
  · rw [ιD_toTwoV]
    exact (val_rr_in (v := w.1.comap (toAff hc0).toRingHom) hc0 hc1 (val_toAff_C hc0 w)
      (valuation_toAff_x hc0 w)).le

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C F)]
  [Fintype (GaussFibre.Ext C (TwoV c F))] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
lemma val_qqrrT_lt : w'.1 (toTwoV c (qq (F := F) c) * toTwoV c (rr (F := F) c)) < 1 := by
  rw [map_mul]
  rcases ext_cases' hc0 hc1 w' with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · rw [ιU_apply, ιU_apply, val_qq_out hc1 (valuation_algebraMap_C' w) (valuation_xF w),
      val_rr_out hc1 (valuation_algebraMap_C' w) (valuation_xF w), one_mul]
    exact_mod_cast hc1
  · have hq : w.1 (toAff hc0 (qq (F := F) c)) = ‖c‖₊ :=
      val_qq_in (v := w.1.comap (toAff hc0).toRingHom) hc0 hc1 (val_toAff_C hc0 w)
        (valuation_toAff_x hc0 w)
    have hr : w.1 (toAff hc0 (rr (F := F) c)) = 1 :=
      val_rr_in (v := w.1.comap (toAff hc0).toRingHom) hc0 hc1 (val_toAff_C hc0 w)
        (valuation_toAff_x hc0 w)
    rw [ιD_toTwoV, ιD_toTwoV, hq, hr, mul_one]
    exact_mod_cast hc1

end Vals

/-! #### The local formula -/

section Main

-- (the local notation `𝓀` is not usable in `variable` binders: it elaborates to `sorry`)
variable
  (hΛF₀ : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
    (fun w : Ext C F ↦ red C (xF C F) w) (redRing C F (xF C F)))
  (hΛFi : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
    (fun w : Ext C F ↦ red C (xF C F)⁻¹ w) (redRing C F (xF C F)⁻¹))
  (hΛT₀ : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
    (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F)) w)
    (redRing C (TwoV c F) (xF C (TwoV c F))))
  (hΛTi : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
    (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F))⁻¹ w)
    (redRing C (TwoV c F) (xF C (TwoV c F))⁻¹))
  (hΛG₀ : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
    (fun w : Ext C (Aff (0 : C) c hc0 F) ↦ red C (xF C (Aff (0 : C) c hc0 F)) w)
    (redRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F))))

include hp hp1 hΛF₀ hΛG₀ hΛT₀ in
/-- Splitting the finite chart of `T` into the node, the outer and the inner points. -/
lemma tot0_T_split :
    tot0 C (TwoV c F) hΛT₀ (fun _ ↦ True) =
      tot0 C (TwoV c F) hΛT₀ (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C (TwoV c F)) w, hΛT₀.mem⟩ :
        redRing C (TwoV c F) (xF C (TwoV c F))) ∈ 𝔫) +
      (tot0 C (TwoV c F) hΛT₀ (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (xF C F)) w',
        (isLocalIso_outer hc0 hc1 hp hp1 hΛF₀ hΛT₀).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))) ∉ 𝔫) +
      tot0 C (TwoV c F) hΛT₀ (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (cxF (F := F) c)) w',
        (isLocalIso_innerMid hc0 hc1 hp hp1 hΛG₀ hΛT₀).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))) ∉ 𝔫)) := by
  have h := finsum_dinf_split3 hΛT₀ (finite_dinf₀ hp hp1 hΛT₀)
    (a := ⟨fun w' ↦ red C (toTwoV c (xF C F)) w',
      (isLocalIso_outer hc0 hc1 hp hp1 hΛF₀ hΛT₀).mem_u'⟩)
    (b := ⟨fun w' ↦ red C (toTwoV c (cxF (F := F) c)) w',
      (isLocalIso_innerMid hc0 hc1 hp hp1 hΛG₀ hΛT₀).mem_u'⟩)
    (d := ⟨fun w ↦ red C (xF C (TwoV c F)) w, hΛT₀.mem⟩) ?_ ?_ (fun _ ↦ True)
  · simpa only [tot0, and_true] using h
  · refine Subtype.ext (funext fun w' ↦ ?_)
    change red C (xF C (TwoV c F)) w' =
      red C (toTwoV c (xF C F)) w' + red C (toTwoV c (cxF (F := F) c)) w'
    rw [← red_add (val_xT_le hc0 hc1 w') (val_cxT_le hc0 hc1 w'), ← map_add, xF_twoV']
  · refine Subtype.ext (funext fun w' ↦ ?_)
    change red C (toTwoV c (xF C F)) w' * red C (toTwoV c (cxF (F := F) c)) w' = 0
    have hx := TwoVertexCharts.xF_ne_zero (C := C) (F := F)
    have e : toTwoV c (xF C F) * toTwoV c (cxF (F := F) c) = algebraMap C (TwoV c F) c := by
      rw [← map_mul, cxF, mul_div_cancel₀ _ hx]; rfl
    rw [← red_mul (val_xT_le hc0 hc1 w') (val_cxT_le hc0 hc1 w'), e,
      (red_eq_zero_iff (val_cT_lt hc1 w').le).2 (val_cT_lt hc1 w')]

omit [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
include hp hp1 hΛF₀ hΛT₀ in
/-- The outer points of the finite chart of `T` are the points of `F` off `x̄ = 0`. -/
lemma tot0_T_outer :
    tot0 C (TwoV c F) hΛT₀ (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (xF C F)) w',
        (isLocalIso_outer hc0 hc1 hp hp1 hΛF₀ hΛT₀).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))) ∉ 𝔫) =
      tot0 C F hΛF₀ (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C F) w, hΛF₀.mem⟩ :
        redRing C F (xF C F)) ∉ 𝔫) := by
  have h := (isLocalIso_outer (F := F) hc0 hc1 hp hp1 hΛF₀ hΛT₀).finsum_dinf_eq (fun _ ↦ True)
    (fun _ ↦ True) fun _ _ _ ↦ Iff.rfl
  simp only [and_true] at h
  exact h.symm

omit [Fintype (GaussFibre.Ext C F)] in
include hp hp1 hΛG₀ hΛT₀ in
/-- The inner points of the finite chart of `T` are the points of `G` off `s̄ = 0`. -/
lemma tot0_T_inner :
    tot0 C (TwoV c F) hΛT₀ (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (cxF (F := F) c)) w',
        (isLocalIso_innerMid hc0 hc1 hp hp1 hΛG₀ hΛT₀).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))) ∉ 𝔫) =
      tot0 C (Aff (0 : C) c hc0 F) hΛG₀ (fun 𝔫 ↦
        (⟨fun w ↦ red C (xF C (Aff (0 : C) c hc0 F)) w, hΛG₀.mem⟩ :
          redRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F))) ∉ 𝔫) := by
  have h := (isLocalIso_innerMid (F := F) hc0 hc1 hp hp1 hΛG₀ hΛT₀).finsum_dinf_eq (fun _ ↦ True)
    (fun _ ↦ True) fun _ _ _ ↦ Iff.rfl
  simp only [and_true] at h
  exact h.symm

omit [Fintype (Ext C (Aff (0 : C) c hc0 F))] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  [Fintype (GaussFibre.Ext C F)] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma qq_add_rr : qq (F := F) c + rr (F := F) c = 1 := by
  have hD := Dn_ne_zero (F := F) (c := c)
  rw [qq, rr, ← add_div, div_eq_one_iff_eq hD]

include hp hp1 hΛFi hΛG₀ hΛTi in
/-- Splitting the points of `T` over `t = ∞` into the outer and the inner ones. -/
lemma totI_T_split :
    totI C (TwoV c F) hΛTi (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∈ 𝔫) =
      totI C (TwoV c F) hΛTi (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (qq (F := F) c)) w',
        (isLocalIso_outerInf (F := F) hc0 hc1 hp hp1 hΛFi hΛTi).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∉ 𝔫 ∧
          (⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∈ 𝔫) +
      totI C (TwoV c F) hΛTi (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (rr (F := F) c)) w',
        (isLocalIso_innerInf (F := F) hc0 hc1 hp hp1 hΛG₀ hΛTi).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∉ 𝔫 ∧
          (⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∈ 𝔫) := by
  set a : redRing C (TwoV c F) (xF C (TwoV c F))⁻¹ := ⟨fun w' ↦ red C (toTwoV c (qq (F := F) c)) w',
    (isLocalIso_outerInf (F := F) hc0 hc1 hp hp1 hΛFi hΛTi).mem_u'⟩
  set b : redRing C (TwoV c F) (xF C (TwoV c F))⁻¹ := ⟨fun w' ↦ red C (toTwoV c (rr (F := F) c)) w',
    (isLocalIso_innerInf (F := F) hc0 hc1 hp hp1 hΛG₀ hΛTi).mem_u'⟩
  have hab : a + b = 1 := by
    refine Subtype.ext (funext fun w' ↦ ?_)
    change red C (toTwoV c (qq (F := F) c)) w' + red C (toTwoV c (rr (F := F) c)) w' = 1
    rw [← red_add (val_qqT_le hc0 hc1 w') (val_rrT_le hc0 hc1 w'), ← map_add, qq_add_rr,
      map_one, red_one]
  have hab0 : a * b = 0 := by
    refine Subtype.ext (funext fun w' ↦ ?_)
    change red C (toTwoV c (qq (F := F) c)) w' * red C (toTwoV c (rr (F := F) c)) w' = 0
    rw [← red_mul (val_qqT_le hc0 hc1 w') (val_rrT_le hc0 hc1 w'),
      (red_eq_zero_iff (val_qqrrT_lt hc0 hc1 w').le).2 (val_qqrrT_lt hc0 hc1 w')]
  set t : redRing C (TwoV c F) (xF C (TwoV c F))⁻¹ :=
    ⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩
  have h := finsum_dinf_or hΛTi (finite_dinfI hp hp1 hΛTi) (P := fun 𝔫 ↦ a ∉ 𝔫 ∧ t ∈ 𝔫)
    (Q := fun 𝔫 ↦ b ∉ 𝔫 ∧ t ∈ 𝔫) (by
      rintro 𝔫 h ⟨ha, -⟩ ⟨hb, -⟩
      rcases h.isPrime.mem_or_mem (show a * b ∈ 𝔫 by rw [hab0]; exact zero_mem _) with h' | h'
      · exact ha h'
      · exact hb h')
  rw [totI, totI, totI, ← h]
  refine finsum_mem_congr (Set.ext fun 𝔫 ↦ ?_) fun _ _ ↦ rfl
  simp only [Set.mem_setOf_eq]
  refine ⟨fun ⟨h, ht⟩ ↦ ⟨h, ?_⟩, fun ⟨h, h'⟩ ↦ ⟨h, h'.elim And.right And.right⟩⟩
  by_cases ha : a ∈ 𝔫
  · refine Or.inr ⟨fun hb ↦ h.ne_top ?_, ht⟩
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem ha hb
  · exact Or.inl ⟨ha, ht⟩

omit [Fintype (Ext C (Aff (0 : C) c hc0 F))] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  [Fintype (GaussFibre.Ext C F)] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma tinv_sub_xinv : tinv (F := F) c - (xF C F)⁻¹ =
    -(algebraMap C F c * (xF C F)⁻¹ * (Dn (F := F) c)⁻¹) := by
  have hx := TwoVertexCharts.xF_ne_zero (C := C) (F := F)
  have hD := Dn_ne_zero (F := F) (c := c)
  rw [tinv, Dn] at *
  field_simp
  ring

omit [Fintype (Ext C (Aff (0 : C) c hc0 F))] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
  [Fintype (GaussFibre.Ext C F)] [Fintype (GaussFibre.Ext C (TwoV c F))] in
include hc0 in
lemma tinv_sub_sF : tinv (F := F) c - sF (F := F) c =
    -(algebraMap C F c⁻¹ * xF C F ^ 3 * (Dn (F := F) c)⁻¹) := by
  have hD := Dn_ne_zero (F := F) (c := c)
  have hc : algebraMap C F c ≠ 0 := (map_ne_zero_iff _ (algebraMap C F).injective).2 hc0
  rw [tinv, sF, Dn] at *
  rw [map_inv₀]
  field_simp
  ring

omit [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
include hp hp1 hΛFi hΛTi in
/-- The outer points of `T` over `t = ∞` are the points of `F` over `x = ∞`. -/
lemma totI_T_outer :
    totI C (TwoV c F) hΛTi (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (qq (F := F) c)) w',
        (isLocalIso_outerInf (F := F) hc0 hc1 hp hp1 hΛFi hΛTi).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∉ 𝔫 ∧
          (⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∈ 𝔫) =
      totI C F hΛFi (fun 𝔫 ↦
        (⟨fun w ↦ red C (xF C F)⁻¹ w, hΛFi.mem⟩ : redRing C F (xF C F)⁻¹) ∈ 𝔫) := by
  set H := isLocalIso_outerInf (F := F) hc0 hc1 hp hp1 hΛFi hΛTi
  have h := H.finsum_dinf_eq
    (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C F)⁻¹ w, hΛFi.mem⟩ : redRing C F (xF C F)⁻¹) ∈ 𝔫)
    (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩ :
      redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∈ 𝔫) fun 𝔫 h1 h2 ↦
    H.mem_iff_mem_trI h1 h2 _ _ fun b _ _ ↦ by
      obtain ⟨w, Q⟩ := b
      have hred : red C (xF C (TwoV c F))⁻¹ (ιU hc0 hc1 w) =
          red C (toTwoV c (xF C F)⁻¹) (ιU hc0 hc1 w) := by
        refine red_eq_of_sub_lt ?_ ?_
        · rw [ιU_apply, map_inv₀, valuation_xF, inv_one]
        · rw [xF_twoV_inv, ← map_sub, ιU_apply, tinv_sub_xinv, Valuation.map_neg, map_mul,
            map_mul, map_inv₀, map_inv₀, valuation_xF, inv_one, mul_one,
            val_Dn_out hc1 (valuation_algebraMap_C' w) (valuation_xF w), inv_one, mul_one,
            valuation_algebraMap_C']
          exact_mod_cast hc1
      refine (iff_of_eq (congrArg (· < 1) (val_pmap_of (C := C) _ _ ?_))).symm
      exact (extEmb_e_red _ _ _ _ w _).trans hred.symm
  rw [totI, totI, ← h]
  refine finsum_mem_congr (Set.ext fun 𝔫 ↦ ?_) fun _ _ ↦ rfl
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, notMem_of_red_eq_one (U1_mem hc1) (red_U1 hc1) h1.ne_top, h2⟩

omit [Fintype (Ext C F)] [Fintype (Ext C (TwoV c F))] [IsAlgClosed C] [CharZero C]
  [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C (Aff 0 c hc0 F))] in
include hc1 in
lemma red_U1G (w : Ext C (Aff (0 : C) c hc0 F)) : red C (toAff hc0 (U1G (F := F) c)) w = 1 :=
  red_eq_one_of (by rw [← map_one (toAff hc0), ← map_sub]; exact val_U1G_sub_one hc0 hc1 w)

omit [Fintype (GaussFibre.Ext C F)] in
include hp hp1 hΛG₀ hΛTi in
/-- The inner points of `T` over `t = ∞` are the points of `G` over `s = 0`. -/
lemma totI_T_inner :
    totI C (TwoV c F) hΛTi (fun 𝔫 ↦ (⟨fun w' ↦ red C (toTwoV c (rr (F := F) c)) w',
        (isLocalIso_innerInf (F := F) hc0 hc1 hp hp1 hΛG₀ hΛTi).mem_u'⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∉ 𝔫 ∧
          (⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩ :
          redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∈ 𝔫) =
      tot0 C (Aff (0 : C) c hc0 F) hΛG₀ (fun 𝔫 ↦
        (⟨fun w ↦ red C (xF C (Aff (0 : C) c hc0 F)) w, hΛG₀.mem⟩ :
          redRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F))) ∈ 𝔫) := by
  set H := isLocalIso_innerInf (F := F) hc0 hc1 hp hp1 hΛG₀ hΛTi
  have h := H.finsum_dinf_eq
    (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C (Aff (0 : C) c hc0 F)) w, hΛG₀.mem⟩ :
      redRing C (Aff (0 : C) c hc0 F) (xF C (Aff (0 : C) c hc0 F))) ∈ 𝔫)
    (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C (TwoV c F))⁻¹ w, hΛTi.mem⟩ :
      redRing C (TwoV c F) (xF C (TwoV c F))⁻¹) ∈ 𝔫) fun 𝔫 h1 h2 ↦
    H.mem_iff_mem_trI h1 h2 _ _ fun b _ _ ↦ by
      obtain ⟨w, Q⟩ := b
      set v : Valuation F ℝ≥0 := w.1.comap (toAff hc0).toRingHom
      have hv (b : C) : v (algebraMap C F b) = ‖b‖₊ := val_toAff_C hc0 w b
      have hx : v (xF C F) = ‖c‖₊ := valuation_toAff_x hc0 w
      have hred : red C (xF C (TwoV c F))⁻¹ (ιD hc0 hc1 w) =
          red C (φG hc0 (xF C (Aff (0 : C) c hc0 F))) (ιD hc0 hc1 w) := by
        refine red_eq_of_sub_lt ?_ ?_
        · rw [ιD_apply, valuation_xF]
        · have e : φG hc0 (xF C (Aff (0 : C) c hc0 F)) = toTwoV c (sF (F := F) c) := by
            rw [xF_G]
            simp [φG]
          rw [e, xF_twoV_inv, ← map_sub, ιD_toTwoV, tinv_sub_sF hc0]
          change v (-(algebraMap C F c⁻¹ * xF C F ^ 3 * (Dn (F := F) c)⁻¹)) < 1
          rw [Valuation.map_neg, map_mul, map_mul, map_pow, hv, hx,
            map_inv₀ v (Dn (F := F) c), val_Dn_in hc0 hc1 hv hx, nnnorm_inv]
          have hc0' : (‖c‖₊ : ℝ≥0) ≠ 0 := by simpa using hc0
          have : ‖c‖₊⁻¹ * ‖c‖₊ ^ 3 * ‖c‖₊⁻¹ = ‖c‖₊ := by field_simp
          rw [this]
          exact_mod_cast hc1
      refine (iff_of_eq (congrArg (· < 1) (val_pmap_of (C := C) _ _ ?_))).symm
      exact (extEmb_e_red _ _ _ _ w _).trans hred.symm
  rw [totI, tot0, ← h]
  refine finsum_mem_congr (Set.ext fun 𝔫 ↦ ?_) fun _ _ ↦ rfl
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨h1, -, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, notMem_of_red_eq_one (U1G_mem hc0 hc1) (red_U1G hc0 hc1) h1.ne_top, h2⟩

omit [IsUltrametricDist C] [CharZero C] [Fintype (Ext C F)] [Fintype (Ext C (TwoV c F))]
  [Fintype (Ext C (Aff (0 : C) c hc0 F))] in
lemma genus_twoV : genus C (TwoV c F) = genus C F := rfl

include hp hp1 hc1 hΛF₀ hΛFi hΛT₀ hΛTi hΛG₀ in
/-- **The local `δ`-formula** (Arzdorf–Wewers (2.3), summed over the points over `x̄ = 0`):
`Δ₀(F) + #Ext(G) = N(T) + Δ(G) + Σ_{w ∈ Ext G} g(κ(w))`, where `Δ₀(F)` is the total `δ` of `F` over
`x̄ = 0`, `N(T)` the total `δ` of the two-vertex model `T` over the node `t̄ = 0`, and `Δ(G)` the
total `δ` of the finite chart of `G` (the model of `w_{0,|c|}`). -/
theorem local_formula :
    (tot0 C F hΛF₀ (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C F) w, hΛF₀.mem⟩ : redRing C F (xF C F)) ∈ 𝔫) :
        ℤ) +
        Fintype.card (Ext C (Aff (0 : C) c hc0 F)) =
      (tot0 C (TwoV c F) hΛT₀ (fun 𝔫 ↦ (⟨fun w ↦ red C (xF C (TwoV c F)) w, hΛT₀.mem⟩ :
        redRing C (TwoV c F) (xF C (TwoV c F))) ∈ 𝔫) : ℤ) +
      (tot0 C (Aff (0 : C) c hc0 F) hΛG₀ (fun _ ↦ True) : ℤ) + gsum C (Aff (0 : C) c hc0 F) := by
  have hF := genus_formula (K := F) hp hp1 hΛF₀ hΛFi
  have hT := genus_formula (K := TwoV c F) hp hp1 hΛT₀ hΛTi
  rw [genus_twoV, card_twoV hc0 hc1, gsum_twoV hc0 hc1,
    tot0_T_split (hp := hp) (hp1 := hp1) (hc0 := hc0) (hc1 := hc1) (hΛF₀ := hΛF₀) (hΛT₀ := hΛT₀)
      (hΛG₀ := hΛG₀),
    tot0_T_outer (hp := hp) (hp1 := hp1) (hc0 := hc0) (hc1 := hc1) (hΛF₀ := hΛF₀) (hΛT₀ := hΛT₀),
    tot0_T_inner (hp := hp) (hp1 := hp1) (hc0 := hc0) (hc1 := hc1) (hΛG₀ := hΛG₀) (hΛT₀ := hΛT₀),
    totI_T_split (hp := hp) (hp1 := hp1) (hc0 := hc0) (hc1 := hc1) (hΛFi := hΛFi) (hΛTi := hΛTi)
      (hΛG₀ := hΛG₀),
    totI_T_outer (hp := hp) (hp1 := hp1) (hc0 := hc0) (hc1 := hc1) (hΛFi := hΛFi) (hΛTi := hΛTi),
    totI_T_inner (hp := hp) (hp1 := hp1) (hc0 := hc0) (hc1 := hc1) (hΛTi := hΛTi) (hΛG₀ := hΛG₀)]
    at hT
  rw [tot0_split hp hp1 hΛF₀ ⟨fun w ↦ red C (xF C F) w, hΛF₀.mem⟩] at hF
  rw [tot0_split hp hp1 hΛG₀ ⟨fun w ↦ red C (xF C (Aff (0 : C) c hc0 F)) w, hΛG₀.mem⟩]
  push_cast at hF hT ⊢
  linarith

end Main

end TwoV

end LocalFormula

end SemistableReduction
