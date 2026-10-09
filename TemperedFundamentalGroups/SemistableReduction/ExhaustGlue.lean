/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhaustDescent

/-!
# Gluing of exhaustion through a circle of a tube

Blueprint §9.12, O12 / R5. Let `K₁ = Aff a c F` (the disc `|x - a| < |c|`), `0 < |u|, |u'| < 1`,
`D(a, |c u|)` exhausting in `D(a, |c|)` and `D(a, |c u u'|)` exhausting in `D(a, |c u|)`. If the
Gauss point `w_{a,|c u|}` is a circle of a tube and the residue classes of `D[a, |c u|]` off the
centre are good, then `D(a, |c u u'|)` is exhausting in `D(a, |c|)` (`exhaustGlueFor`).

Proof: three local `δ`-formulas (`LocalFormula.local_formula`) for the models `(c, u)`, `(c u, u')`
and `(c, u u')` show that the total `δ` over the node of the third model is the number `n` of
extensions of `w_{a,|c u|}`; the numbers of outer and inner branches of the third model are those
of the first and of the second model, both `n`; hence every point over its node is an ordinary
double point (`NodeBridge.nodeGood_of_tot0_le`).
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal

namespace SemistableReduction

namespace ExhaustGlue

open GaussFibre ChartLocal DeltaCount FundamentalInequality GaussStability AffineTwist
  TwoVertex NodeBridge ChartChange LocalFormula ExhaustGluing ExhaustDescent

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-! ### Same coordinate -/

section Same

variable {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra (RatFunc C) K₁] [Algebra (RatFunc C) K₂]
  [Algebra C K₁] [IsScalarTower C (RatFunc C) K₁] [Algebra C K₂]
  [IsScalarTower C (RatFunc C) K₂] (φ : K₁ ≃+* K₂)
  (hC : ∀ b : C, φ (algebraMap C K₁ b) = algebraMap C K₂ b) (hx : φ (xF C K₁) = xF C K₂)

include hC hx in
omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- Isomorphisms which are `C`-linear and preserve the coordinate are `C(x)`-linear. -/
lemma he_of_x (ψ : RatFunc C) :
    φ (algebraMap (RatFunc C) K₁ ((AlgEquiv.refl : RatFunc C ≃ₐ[C] RatFunc C) ψ)) =
      algebraMap (RatFunc C) K₂ ψ := by
  set φA : K₁ ≃ₐ[C] K₂ := AlgEquiv.ofRingEquiv (f := φ) hC
  have hp (p : C[X]) : φ (algebraMap (RatFunc C) K₁ (algebraMap C[X] (RatFunc C) p)) =
      algebraMap (RatFunc C) K₂ (algebraMap C[X] (RatFunc C) p) := by
    rw [← aeval_xF, ← aeval_xF]
    change φA (aeval (xF C K₁) p) = _
    rw [← Polynomial.aeval_algHom_apply]
    change aeval (φ (xF C K₁)) p = _
    rw [hx]
  change φ (algebraMap (RatFunc C) K₁ ψ) = _
  rw [← RatFunc.num_div_denom ψ, map_div₀, map_div₀, map_div₀, hp, hp]

variable [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂]
  [Fintype (Ext C K₁)] [Fintype (Ext C K₂)]

include hC hx

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) K₁] [FiniteDimensional (RatFunc C) K₂] in
lemma card_ext_eq' : Fintype.card (Ext C K₁) = Fintype.card (Ext C K₂) :=
  card_ext_eq AlgEquiv.refl gauss1_refl φ (he_of_x φ hC hx)

lemma gsum_eq' : gsum C K₁ = gsum C K₂ :=
  gsum_eq AlgEquiv.refl gauss1_refl φ (he_of_x φ hC hx)

lemma sum_zeros_eq :
    ∑ w : Ext C K₁, (PlaceNorm.zeros 𝓀 (red C (xF C K₁) w)).card =
      ∑ w : Ext C K₂, (PlaceNorm.zeros 𝓀 (red C (xF C K₂) w)).card := by
  rw [← (extEquiv AlgEquiv.refl gauss1_refl φ (he_of_x φ hC hx)).sum_comp]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rw [← hx, card_zeros_eq]

lemma tot0_true_eq'
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂))) :
    tot0 C K₂ hΛ₂ (fun _ ↦ True) = tot0 C K₁ hΛ₁ (fun _ ↦ True) :=
  tot0_true_eq AlgEquiv.refl gauss1_refl φ (he_of_x φ hC hx) (u := 1) (β := 0) (by simp)
    (by rw [map_one, one_mul, map_zero, add_zero, hx]) hΛ₁ hΛ₂

lemma tot0_x_eq'
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C K₁ ↦ red C (xF C K₁) w) (redRing C K₁ (xF C K₁)))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C K₂ ↦ red C (xF C K₂) w) (redRing C K₂ (xF C K₂))) :
    tot0 C K₂ hΛ₂ (fun 𝔫 ↦ DiscBridge.xbar hΛ₂ ∈ 𝔫) =
      tot0 C K₁ hΛ₁ (fun 𝔫 ↦ DiscBridge.xbar hΛ₁ ∈ 𝔫) := by
  have hg : algebraMap C K₁ (1 : C) * xF C K₁ + algebraMap C K₁ (0 : C) ∈
      intRing C K₁ (xF C K₁) := by
    rw [map_one, one_mul, map_zero, add_zero]
    exact ⟨TwoVertexCharts.isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _),
      gnorm_le_iff.2 fun w ↦ (valuation_xF w).le⟩
  have h := tot0_x_eq AlgEquiv.refl gauss1_refl φ (he_of_x φ hC hx) (u := 1) (β := 0) (by simp)
    (by rw [map_one, one_mul, map_zero, add_zero, hx]) hΛ₁ hΛ₂ hg
  convert h using 4
  apply Subtype.ext
  funext w
  simp

end Same

/-! ### The three identifications -/

section Ident

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] {a c u u' : C} (hc : c ≠ 0) (hu0 : u ≠ 0) (hu0' : u' ≠ 0)

omit [IsAlgClosed C] in
lemma aff_congr {a a' c c' : C} (h1 : a = a') (h2 : c = c') (hc : c ≠ 0) (hc' : c' ≠ 0)
    (ψ : RatFunc C) : aff a c hc ψ = aff a' c' hc' ψ := by
  subst h1 h2; rfl

/-- `Aff 0 u (Aff a c F) = Aff a (c u) F`. -/
noncomputable def eB : Aff (0 : C) u hu0 (Aff a c hc F) ≃+* Aff a (c * u) (mul_ne_zero hc hu0) F :=
  RingEquiv.refl F

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]
  in
lemma eB_C (b : C) : eB (F := F) hc hu0 (algebraMap C (Aff (0 : C) u hu0 (Aff a c hc F)) b) =
    algebraMap C (Aff a (c * u) (mul_ne_zero hc hu0) F) b := rfl

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma eB_x : eB (F := F) hc hu0 (xF C (Aff (0 : C) u hu0 (Aff a c hc F))) =
    xF C (Aff a (c * u) (mul_ne_zero hc hu0) F) := by
  change algebraMap (RatFunc C) F (aff a c hc (aff 0 u hu0 RatFunc.X)) =
    algebraMap (RatFunc C) F (aff a (c * u) (mul_ne_zero hc hu0) RatFunc.X)
  rw [aff_aff, aff_congr (by ring) rfl _ (mul_ne_zero hc hu0)]

/-- `Aff 0 (u u') (Aff a c F) = Aff 0 u' (Aff a (c u) F)`. -/
noncomputable def eC : Aff (0 : C) (u * u') (mul_ne_zero hu0 hu0') (Aff a c hc F) ≃+*
    Aff (0 : C) u' hu0' (Aff a (c * u) (mul_ne_zero hc hu0) F) :=
  RingEquiv.refl F

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]
  in
lemma eC_C (b : C) : eC (F := F) hc hu0 hu0'
      (algebraMap C (Aff (0 : C) (u * u') (mul_ne_zero hu0 hu0') (Aff a c hc F)) b) =
    algebraMap C (Aff (0 : C) u' hu0' (Aff a (c * u) (mul_ne_zero hc hu0) F)) b := rfl

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma eC_x : eC (F := F) hc hu0 hu0'
      (xF C (Aff (0 : C) (u * u') (mul_ne_zero hu0 hu0') (Aff a c hc F))) =
    xF C (Aff (0 : C) u' hu0' (Aff a (c * u) (mul_ne_zero hc hu0) F)) := by
  change algebraMap (RatFunc C) F (aff a c hc (aff 0 (u * u') _ RatFunc.X)) =
    algebraMap (RatFunc C) F (aff a (c * u) (mul_ne_zero hc hu0) (aff 0 u' hu0' RatFunc.X))
  have h3 := mul_ne_zero (mul_ne_zero hc hu0) hu0'
  rw [aff_aff, aff_aff, aff_congr (a' := a) (c' := c * u * u') (by ring) (by ring) _ h3,
    aff_congr (a := a + c * u * 0) (a' := a) (c' := c * u * u') (by ring) (by ring) _ h3]

/-- `Inv (u u') (Aff a c F) = Inv u' (Aff a (c u) F)`. -/
noncomputable def eA : GaussTube.Inv (u * u') (mul_ne_zero hu0 hu0') (Aff a c hc F) ≃+*
    GaussTube.Inv u' hu0' (Aff a (c * u) (mul_ne_zero hc hu0) F) :=
  RingEquiv.refl F

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]
  in
lemma eA_C (b : C) : eA (F := F) hc hu0 hu0'
      (algebraMap C (GaussTube.Inv (u * u') (mul_ne_zero hu0 hu0') (Aff a c hc F)) b) =
    algebraMap C (GaussTube.Inv u' hu0' (Aff a (c * u) (mul_ne_zero hc hu0) F)) b := rfl

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma eA_x : eA (F := F) hc hu0 hu0'
      (xF C (GaussTube.Inv (u * u') (mul_ne_zero hu0 hu0') (Aff a c hc F))) =
    xF C (GaussTube.Inv u' hu0' (Aff a (c * u) (mul_ne_zero hc hu0) F)) := by
  change algebraMap (RatFunc C) F (aff a c hc (GaussTube.inv (mul_ne_zero hu0 hu0') RatFunc.X)) =
    algebraMap (RatFunc C) F (aff a (c * u) (mul_ne_zero hc hu0) (GaussTube.inv hu0' RatFunc.X))
  congr 1
  rw [GaussTube.inv_apply, GaussTube.inv_apply, GaussTube.invHom_X, GaussTube.invHom_X,
    map_div₀, map_div₀, AlgEquiv.commutes, AlgEquiv.commutes, aff_apply, aff_apply, affHom_X,
    affHom_X, gaussCoord_eq, gaussCoord_eq]
  have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
  have hu' : algebraMap C (RatFunc C) u ≠ 0 := by simpa using hu0
  simp only [map_inv₀, map_mul]
  field_simp

end Ident

/-! ### Gluing -/

section Glue

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- If the residue classes off the centre are good, the total `δ` of the closed-disc chart is the
total `δ` over its centre. -/
lemma tot0_true_eq_center {a c u : C} (hc : c ≠ 0) (hu0 : u ≠ 0)
    [Fintype (Ext C (Aff (0 : C) u hu0 (Aff a c hc F)))]
    (hΛG : IsChart 𝓀 (fun w : Ext C (Aff (0 : C) u hu0 (Aff a c hc F)) ↦
      red C (xF C (Aff (0 : C) u hu0 (Aff a c hc F))) w)
      (redRing C _ (xF C (Aff (0 : C) u hu0 (Aff a c hc F)))))
    (hoff : ∀ β : C, ‖β‖ = 1 → DiscSmooth F (a + c * u * β) (mul_ne_zero hc hu0)) :
    tot0 C _ hΛG (fun _ ↦ True) = tot0 C _ hΛG (fun 𝔫 ↦ DiscBridge.xbar hΛG ∈ 𝔫) := by
  rw [tot0_split hp hp1 hΛG (DiscBridge.xbar hΛG)]
  suffices h : tot0 C _ hΛG (fun 𝔫 ↦ DiscBridge.xbar hΛG ∉ 𝔫) = 0 by rw [h, add_zero]
  rw [tot0, DiscBridge.finsum_mem_eq_zero_iff_nat ((finite_dinf₀ hp hp1 hΛG).subset
    fun 𝔫 h ↦ ⟨h.1.1, h.2⟩)]
  rintro 𝔫 ⟨h𝔫, hx⟩
  by_contra hd
  obtain ⟨β, -, h1, hbad⟩ := bad_class_of_point hp hp1 hc hu0 hΛG h𝔫 hd
  exact hbad (hoff β (h1 hx))

set_option maxHeartbeats 1000000 in
-- three local formulas and their identifications
include hp hp1 in
/-- **Gluing of exhaustion through a circle of a tube** (`ExhaustGlueFor`). -/
theorem exhaustGlueFor : ExhaustGlueFor C F := by
  classical
  intro a c u u' hc hu hu0 hu' hu0' hex1 hex2 hcirc hoff
  set K₁ := Aff a c hc F
  set K₂ := Aff a (c * u) (mul_ne_zero hc hu0) F
  set G₁ := Aff (0 : C) u hu0 K₁
  set G₂ := Aff (0 : C) u' hu0' K₂
  set G₃ := Aff (0 : C) (u * u') (mul_ne_zero hu0 hu0') K₁
  have hu₃ : ‖u * u'‖ < 1 := norm_mul_lt_one hu hu'
  have hu0₃ : u * u' ≠ 0 := mul_ne_zero hu0 hu0'
  -- finiteness
  haveI : Finite (Ext C K₁) := finite_ext (F := K₁) hp hp1
  letI : Fintype (Ext C K₁) := Fintype.ofFinite _
  haveI : Finite (Ext C K₂) := finite_ext (F := K₂) hp hp1
  letI : Fintype (Ext C K₂) := Fintype.ofFinite _
  haveI : Finite (Ext C G₁) := finite_ext (F := G₁) hp hp1
  letI : Fintype (Ext C G₁) := Fintype.ofFinite _
  haveI : Finite (Ext C G₂) := finite_ext (F := G₂) hp hp1
  letI : Fintype (Ext C G₂) := Fintype.ofFinite _
  haveI : Finite (Ext C G₃) := finite_ext (F := G₃) hp hp1
  letI : Fintype (Ext C G₃) := Fintype.ofFinite _
  haveI : Finite (Ext C (TwoV u K₁)) := finite_ext (F := TwoV u K₁) hp hp1
  letI : Fintype (Ext C (TwoV u K₁)) := Fintype.ofFinite _
  haveI : Finite (Ext C (TwoV u' K₂)) := finite_ext (F := TwoV u' K₂) hp hp1
  letI : Fintype (Ext C (TwoV u' K₂)) := Fintype.ofFinite _
  haveI : Finite (Ext C (TwoV (u * u') K₁)) := finite_ext (F := TwoV (u * u') K₁) hp hp1
  letI : Fintype (Ext C (TwoV (u * u') K₁)) := Fintype.ofFinite _
  haveI : Finite (Ext C (GaussTube.Inv u hu0 K₁)) := finite_ext (F := GaussTube.Inv u hu0 K₁) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv u hu0 K₁)) := Fintype.ofFinite _
  haveI : Finite (Ext C (GaussTube.Inv u' hu0' K₂)) :=
    finite_ext (F := GaussTube.Inv u' hu0' K₂) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv u' hu0' K₂)) := Fintype.ofFinite _
  haveI : Finite (Ext C (GaussTube.Inv (u * u') hu0₃ K₁)) :=
    finite_ext (F := GaussTube.Inv (u * u') hu0₃ K₁) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv (u * u') hu0₃ K₁)) := Fintype.ofFinite _
  -- charts
  have hΛK₁ := chart₀ hp hp1 K₁
  have hΛK₁i := chartI hp hp1 K₁
  have hΛK₂ := chart₀ hp hp1 K₂
  have hΛK₂i := chartI hp hp1 K₂
  have hΛG₁ := chart₀ hp hp1 G₁
  have hΛG₂ := chart₀ hp hp1 G₂
  have hΛG₃ := chart₀ hp hp1 G₃
  have hΛT₁ := chart₀ hp hp1 (TwoV u K₁)
  have hΛT₂ := chart₀ hp hp1 (TwoV u' K₂)
  have hΛT₂i := chartI hp hp1 (TwoV u' K₂)
  have hΛT₃ := chart₀ hp hp1 (TwoV (u * u') K₁)
  have hΛT₃i := chartI hp hp1 (TwoV (u * u') K₁)
  -- the circle of a tube at the centre
  have hcen := hcirc a (by rw [sub_self, norm_zero]; exact norm_pos_iff.2 (mul_ne_zero hc hu0))
  have heBC := eB_C (F := F) (a := a) hc hu0
  have heBx := eB_x (F := F) (a := a) hc hu0
  have heCC := eC_C (F := F) (a := a) hc hu0 hu0'
  have heCx := eC_x (F := F) (a := a) hc hu0 hu0'
  have heAC := eA_C (F := F) (a := a) hc hu0 hu0'
  have heAx := eA_x (F := F) (a := a) hc hu0 hu0'
  -- `δ` over `D(a,|c|)` equals `δ` over `D(a,|c u|)`
  have hD : tot0 C K₁ hΛK₁ (fun 𝔫 ↦ DiscBridge.xbar hΛK₁ ∈ 𝔫) =
      tot0 C K₂ hΛK₂ (fun 𝔫 ↦ DiscBridge.xbar hΛK₂ ∈ 𝔫) := by
    rw [tot0_eq_of_exhausting hp hp1 hc hu hu0 hex1 hcen.1 hΛK₁ hΛG₁,
      tot0_true_eq_center hp hp1 hc hu0 hΛG₁ hoff,
      tot0_x_eq' _ heBC heBx hΛG₁ hΛK₂]
  -- the local formulas of the second and the third model
  have LF₂ := local_formula (hp := hp) (hp1 := hp1) (hc0 := hu0') (hc1 := hu') hΛK₂ hΛK₂i hΛT₂
    hΛT₂i hΛG₂
  have LF₃ := local_formula (hp := hp) (hp1 := hp1) (hc0 := hu0₃) (hc1 := hu₃) hΛK₁ hΛK₁i hΛT₃
    hΛT₃i hΛG₃
  have e₁ := card_ext_eq' _ heCC heCx
  have e₂ := tot0_true_eq' _ heCC heCx hΛG₃ hΛG₂
  have e₃ := gsum_eq' _ heCC heCx
  -- the node counts
  have hN₂ := tot0_t_of_nodeGood hu0' hu' hp hp1 hΛT₂ hex2
  have hn : (outerZ (F := K₂) hu0' hu').card = Fintype.card (Ext C K₂) := by
    rw [card_outerZ, ← Finset.card_univ, Finset.card_eq_sum_ones]
    exact Finset.sum_congr rfl fun w _ ↦ hcen.2 w
  have hN₃ : tot0 C (TwoV (u * u') K₁) hΛT₃ (fun 𝔫 ↦ tbar hΛT₃ ∈ 𝔫) =
      Fintype.card (Ext C K₂) := by
    have h3 : (tot0 C (TwoV (u * u') K₁) hΛT₃ (fun 𝔫 ↦ tbar hΛT₃ ∈ 𝔫) : ℤ) =
        tot0 C (TwoV u' K₂) hΛT₂ (fun 𝔫 ↦ tbar hΛT₂ ∈ 𝔫) := by
      have LF₂' := LF₂
      have LF₃' := LF₃
      change (tot0 C K₂ hΛK₂ (fun 𝔫 ↦ DiscBridge.xbar hΛK₂ ∈ 𝔫) : ℤ) + _ =
        (tot0 C (TwoV u' K₂) hΛT₂ (fun 𝔫 ↦ tbar hΛT₂ ∈ 𝔫) : ℤ) + _ + _ at LF₂'
      change (tot0 C K₁ hΛK₁ (fun 𝔫 ↦ DiscBridge.xbar hΛK₁ ∈ 𝔫) : ℤ) + _ =
        (tot0 C (TwoV (u * u') K₁) hΛT₃ (fun 𝔫 ↦ tbar hΛT₃ ∈ 𝔫) : ℤ) + _ + _ at LF₃'
      rw [hD, e₁, ← e₂, e₃] at LF₃'
      linarith
    have := hN₂.2.trans hn
    omega
  refine nodeGood_of_tot0_le hu0₃ hu₃ hp hp1 hΛT₃ hN₃.le ?_ ?_
  · -- outer branches: those of the first model
    have hN₁ := tot0_t_of_nodeGood hu0 hu hp hp1 hΛT₁ hex1
    have h1 : (outerZ (F := K₁) hu0₃ hu₃).card = (outerZ (F := K₁) hu0 hu).card := by
      rw [card_outerZ, card_outerZ]
    rw [h1, ← hN₁.2, hN₁.1, card_innerZ, sum_card_zeros_inv hc hu0 hcen.1]
    exact card_ext_eq' _ heBC heBx
  · -- inner branches: those of the second model
    rw [card_innerZ, sum_zeros_eq _ heAC heAx,
      ← card_innerZ (F := K₂) hu0' hu', ← hN₂.1, hN₂.2, hn]

end Glue

end ExhaustGlue

end SemistableReduction
