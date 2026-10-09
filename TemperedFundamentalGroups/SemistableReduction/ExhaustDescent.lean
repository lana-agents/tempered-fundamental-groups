/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartChange
import TemperedFundamentalGroups.SemistableReduction.ExhaustInterfaces

/-!
# Descent of singularities into an exhausting disc

Blueprint §9.12, O12 / R5. Let `U = {|x - b| < |d|}` and `D = {|x - b| ≤ |d c'|}` (`0 < |c'| < 1`)
be exhausting in `U`, and let the Gauss point `w_{b,|d c'|}` be a disc of a tube (rational residue
curves, one point over `∞` each). By the local `δ`-formula (`LocalFormula.local_formula`) and the
`δ`-count of good nodes (`NodeBridge.tot0_t_of_nodeGood`), the total `δ` over `U` equals the total
`δ` of the chart of `D` (`tot0_eq_of_exhausting`). In particular a singular point over `U` forces a
singular point over a residue class of `D` (`exists_bad_of_exhausting`).
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal

namespace SemistableReduction

namespace ExhaustDescent

open GaussFibre ChartLocal DeltaCount FundamentalInequality GaussStability AffineTwist
  TwoVertex NodeBridge ChartChange LocalFormula ExhaustGluing

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

section Charts

variable (K : Type*) [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]

include hp hp1 in
theorem chart₀ : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)) := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (F := K) ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := K) hp hp1)
  exact isChart_x hb

include hp hp1 in
theorem chartI : IsChart 𝓀 (fun w : Ext C K ↦ red C (xF C K)⁻¹ w) (redRing C K (xF C K)⁻¹) := by
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (F := K) ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := K) hp hp1)
  exact isChart_x_inv hb

end Charts

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

section Tube

omit [CharZero C] [IsAlgClosed C] in
lemma gauss1_refl (ψ : RatFunc C) :
    gauss1 C ((AlgEquiv.refl : RatFunc C ≃ₐ[C] RatFunc C) ψ) = gauss1 C ψ := rfl

variable {a b d c : C} (hd : d ≠ 0) (hc : c ≠ 0)

omit [CharZero C] [FiniteDimensional (RatFunc C) F] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F]
  in
lemma compEquiv_xF :
    compEquiv (F := F) hd hc (xF C (Aff a c hc (Aff b d hd F))) =
      xF C (Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F) := by
  rw [compEquiv_x hd hc, map_one, one_mul, map_zero, add_zero]

variable [Fintype (Ext C (Aff (0 : C) c hc (Aff b d hd F)))]
  [Fintype (Ext C (GaussTube.Inv c hc (Aff b d hd F)))]

omit [Fintype (GaussFibre.Ext C (GaussTube.Inv c hc (Aff b d hd F)))] in
include hp hp1 in
/-- A disc of a tube: the inner residue curves are rational. -/
lemma gsum_eq_zero (htube : IsTubeDisc F b (mul_ne_zero hd hc)) :
    gsum C (Aff (0 : C) c hc (Aff b d hd F)) = 0 := by
  haveI : Finite (Ext C (Aff (b + d * 0) (d * c) (mul_ne_zero hd hc) F)) :=
    finite_ext (F := Aff (b + d * 0) (d * c) (mul_ne_zero hd hc) F) hp hp1
  letI : Fintype (Ext C (Aff (b + d * 0) (d * c) (mul_ne_zero hd hc) F)) := Fintype.ofFinite _
  have htube' : IsTubeDisc F (b + d * 0) (mul_ne_zero hd hc) :=
    (isTubeDisc_congr _ _ (by ring) rfl).2 htube
  have := gsum_eq AlgEquiv.refl gauss1_refl (compEquiv (F := F) (a := 0) (b := b) hd hc)
    (compEquiv_he (F := F) (a := 0) (b := b) hd hc)
  rw [this, gsum]
  exact Finset.sum_eq_zero fun w _ ↦ by rw [(htube' w).1]; rfl

omit [CharZero C] in
/-- A disc of a tube: one inner branch over every inner extension. -/
lemma sum_card_zeros_inv (htube : IsTubeDisc F b (mul_ne_zero hd hc)) :
    ∑ w₂ : Ext C (GaussTube.Inv c hc (Aff b d hd F)),
      (PlaceNorm.zeros 𝓀 (red C (xF C (GaussTube.Inv c hc (Aff b d hd F))) w₂)).card =
      Fintype.card (Ext C (Aff (0 : C) c hc (Aff b d hd F))) := by
  have htube' : IsTubeDisc F (b + d * 0) (mul_ne_zero hd hc) :=
    (isTubeDisc_congr _ _ (by ring) rfl).2 htube
  have h1 (w₂ : Ext C (GaussTube.Inv c hc (Aff b d hd F))) :
      (PlaceNorm.zeros 𝓀 (red C (xF C (GaussTube.Inv c hc (Aff b d hd F))) w₂)).card = 1 := by
    rw [← card_zeros_eq (σInv hc) (gauss1_σInv hc) (invEquiv hc) (invEquiv_he hc), invEquiv_x,
      red_inv_xF]
    set w := extEquiv (σInv hc) (gauss1_σInv hc) (invEquiv hc) (invEquiv_he hc) w₂
    have h2 := card_zeros_eq AlgEquiv.refl gauss1_refl (compEquiv (F := F) (a := 0) (b := b) hd hc)
      (compEquiv_he (F := F) (a := 0) (b := b) hd hc) w
      (xF C (Aff (0 : C) c hc (Aff b d hd F)))⁻¹
    rw [map_inv₀, compEquiv_xF, red_inv_xF, red_inv_xF] at h2
    rw [← h2]
    exact (htube' _).2
  rw [Finset.sum_congr rfl fun w₂ _ ↦ h1 w₂, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_univ]
  exact card_ext_eq (σInv hc) (gauss1_σInv hc) (invEquiv hc) (invEquiv_he hc)

end Tube

section Main

omit [CharZero C] in
lemma discSmooth_congr {a a' c c' : C} (h1 : a = a') (h2 : c = c') (hc : c ≠ 0) (hc' : c' ≠ 0) :
    DiscSmooth F a hc ↔ DiscSmooth F a' hc' := by
  subst h1 h2; rfl

omit [CharZero C] in
/-- `tot0` over the residue point along a composition of affine twists. -/
lemma tot0_comp {a b c d : C} (hd : d ≠ 0) (hc : c ≠ 0)
    [Fintype (Ext C (Aff a c hc (Aff b d hd F)))]
    [Fintype (Ext C (Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F))]
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C (Aff a c hc (Aff b d hd F)) ↦
      red C (xF C (Aff a c hc (Aff b d hd F))) w) (redRing C _ (xF C (Aff a c hc (Aff b d hd F)))))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C (Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F) ↦
      red C (xF C (Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F)) w)
      (redRing C _ (xF C (Aff (b + d * a) (d * c) (mul_ne_zero hd hc) F)))) :
    tot0 C _ hΛ₂ (fun 𝔫 ↦ DiscBridge.xbar hΛ₂ ∈ 𝔫) =
      tot0 C _ hΛ₁ (fun 𝔫 ↦ DiscBridge.xbar hΛ₁ ∈ 𝔫) := by
  have hg : algebraMap C (Aff a c hc (Aff b d hd F)) (1 : C) * xF C (Aff a c hc (Aff b d hd F)) +
      algebraMap C (Aff a c hc (Aff b d hd F)) (0 : C) ∈
        intRing C (Aff a c hc (Aff b d hd F)) (xF C (Aff a c hc (Aff b d hd F))) := by
    rw [map_one, one_mul, map_zero, add_zero]
    exact ⟨TwoVertexCharts.isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _),
      gnorm_le_iff.2 fun w ↦ (valuation_xF w).le⟩
  have h := tot0_x_eq AlgEquiv.refl gauss1_refl (compEquiv hd hc) (compEquiv_he hd hc)
    (u := 1) (β := 0) (by simp) (compEquiv_x hd hc) hΛ₁ hΛ₂ hg
  convert h using 4
  apply Subtype.ext
  funext w
  simp

include hp hp1 in
/-- **The total `δ` over `U` is the total `δ` of the chart of `D`.** -/
theorem tot0_eq_of_exhausting {b d c' : C} (hd : d ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0)
    (hex : IsExhausting b hd hc' hc0' F) (htube : IsTubeDisc F b (mul_ne_zero hd hc0'))
    [Fintype (Ext C (Aff b d hd F))] [Fintype (Ext C (Aff (0 : C) c' hc0' (Aff b d hd F)))]
    (hΛK : IsChart 𝓀 (fun w : Ext C (Aff b d hd F) ↦ red C (xF C (Aff b d hd F)) w)
      (redRing C _ (xF C (Aff b d hd F))))
    (hΛG : IsChart 𝓀 (fun w : Ext C (Aff (0 : C) c' hc0' (Aff b d hd F)) ↦
      red C (xF C (Aff (0 : C) c' hc0' (Aff b d hd F))) w)
      (redRing C _ (xF C (Aff (0 : C) c' hc0' (Aff b d hd F))))) :
    tot0 C _ hΛK (fun 𝔫 ↦ DiscBridge.xbar hΛK ∈ 𝔫) = tot0 C _ hΛG (fun _ ↦ True) := by
  set K := Aff b d hd F
  set G := Aff (0 : C) c' hc0' K
  haveI : Finite (Ext C (TwoV c' K)) := finite_ext (F := TwoV c' K) hp hp1
  letI : Fintype (Ext C (TwoV c' K)) := Fintype.ofFinite _
  haveI : Finite (Ext C (GaussTube.Inv c' hc0' K)) :=
    finite_ext (F := GaussTube.Inv c' hc0' K) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv c' hc0' K)) := Fintype.ofFinite _
  have hΛKi := chartI hp hp1 K
  have hΛT := chart₀ hp hp1 (TwoV c' K)
  have hΛTi := chartI hp hp1 (TwoV c' K)
  have LF := local_formula (hp := hp) (hp1 := hp1) (hc0 := hc0') (hc1 := hc') hΛK hΛKi hΛT hΛTi hΛG
  have hN := (tot0_t_of_nodeGood hc0' hc' hp hp1 hΛT hex).1
  rw [card_innerZ, sum_card_zeros_inv hd hc0' htube] at hN
  have hgs := gsum_eq_zero hp hp1 hd hc0' htube
  have hN' : (tot0 C (TwoV c' K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) : ℤ) = Fintype.card (Ext C G) := by
    exact_mod_cast hN
  have : (tot0 C K hΛK (fun 𝔫 ↦ DiscBridge.xbar hΛK ∈ 𝔫) : ℤ) = tot0 C G hΛG (fun _ ↦ True) := by
    have LF' := LF
    change (tot0 C K hΛK (fun 𝔫 ↦ DiscBridge.xbar hΛK ∈ 𝔫) : ℤ) + _ =
      (tot0 C (TwoV c' K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) : ℤ) + _ + _ at LF'
    rw [hN', hgs] at LF'
    linarith
  exact_mod_cast this

set_option maxHeartbeats 1000000 in
-- three successive changes of coordinates of the chart
include hp hp1 in
/-- A singular point of the chart of `D` lies over a residue class of `D` which is bad; off the
centre, the class is not the central one. -/
lemma bad_class_of_point {b d c' : C} (hd : d ≠ 0) (hc0' : c' ≠ 0)
    [Fintype (Ext C (Aff (0 : C) c' hc0' (Aff b d hd F)))]
    (hΛG : IsChart 𝓀 (fun w : Ext C (Aff (0 : C) c' hc0' (Aff b d hd F)) ↦
      red C (xF C (Aff (0 : C) c' hc0' (Aff b d hd F))) w)
      (redRing C _ (xF C (Aff (0 : C) c' hc0' (Aff b d hd F)))))
    {𝔫 : Ideal (redRing C _ (xF C (Aff (0 : C) c' hc0' (Aff b d hd F))))} (h𝔫 : 𝔫.IsMaximal)
    (hd𝔫 : dinf 𝓀 (fun w : Ext C (Aff (0 : C) c' hc0' (Aff b d hd F)) ↦
      ResidueField w.1.valuationSubring) hΛG 𝔫 ≠ 0) :
    ∃ β : C, ‖β‖ ≤ 1 ∧ (DiscBridge.xbar hΛG ∉ 𝔫 → ‖β‖ = 1) ∧
      ¬ DiscSmooth F (b + d * c' * β) (mul_ne_zero hd hc0') := by
  classical
  set K := Aff b d hd F
  set G := Aff (0 : C) c' hc0' K
  haveI := h𝔫
  obtain ⟨b₀, hb₀⟩ := exists_mem_brs hΛG h𝔫
  have hz := mem_V_of_mem_brs hΛG h𝔫.ne_top hb₀
  obtain ⟨β₀, hβ₀⟩ := IsLocalRing.residue_surjective (b₀.2.res (red C (xF C G) b₀.1))
  set β : C := (β₀ : C) with hβdef
  have hβ : ‖β‖ ≤ 1 := HenselComplete.norm_le_one β₀
  -- the translated chart
  set G' := Aff β 1 one_ne_zero G
  haveI : Finite (Ext C G') := finite_ext (F := G') hp hp1
  letI : Fintype (Ext C G') := Fintype.ofFinite _
  have hΛG' := chart₀ hp hp1 G'
  have hgx : algebraMap C G (1 : C) * xF C G + algebraMap C G (-β) = xF C G - algebraMap C G β := by
    rw [map_one, one_mul, map_neg, sub_eq_add_neg]
  have hg : algebraMap C G (1 : C) * xF C G + algebraMap C G (-β) ∈ intRing C G (xF C G) := by
    rw [hgx]
    refine ⟨TwoVertexCharts.isIntegral_of_mem (sub_mem (Algebra.self_mem_adjoin_singleton C _)
      (Subalgebra.algebraMap_mem _ _)), gnorm_le_iff.2 fun w ↦ ?_⟩
    refine (Valuation.map_sub _ _ _).trans (max_le (valuation_xF w).le ?_)
    rw [valuation_algebraMap_C']
    exact_mod_cast hβ
  have hsh := tot0_x_eq (aff β 1 one_ne_zero) (gauss1_aff_one hβ) (toAff one_ne_zero) shift_he
    (u := 1) (β := -β) (by simp) shift_x hΛG hΛG' hg
  have hg𝔫 : (⟨fun w ↦ red C (algebraMap C G (1 : C) * xF C G + algebraMap C G (-β)) w,
      red_mem_redRing hg⟩ : redRing C G (xF C G)) ∈ 𝔫 := by
    rw [mem_iff_of_mem_brs hΛG h𝔫.ne_top hb₀]
    change b₀.2.valuation (red C (algebraMap C G (1 : C) * xF C G + algebraMap C G (-β)) b₀.1) < 1
    have hβ' : ‖β‖₊ ≤ 1 := by exact_mod_cast hβ
    rw [hgx, red_sub (valuation_xF _).le (by rw [valuation_algebraMap_C']; exact hβ'),
      red_algebraMap_C β hβ']
    have : (residue (HenselComplete.integers C) ⟨β, by simpa using hβ'⟩) =
        b₀.2.res (red C (xF C G) b₀.1) := hβ₀
    rw [this]
    exact b₀.2.valuation_sub_res_lt_one hz
  have hG' : tot0 C G' hΛG' (fun 𝔫 ↦ DiscBridge.xbar hΛG' ∈ 𝔫) ≠ 0 := by
    change tot0 C G' hΛG' (fun 𝔫 ↦ (⟨fun w' ↦ red C (xF C G') w', hΛG'.mem⟩ :
      redRing C G' (xF C G')) ∈ 𝔫) ≠ 0
    rw [hsh]
    intro h0
    have hfin' := (finite_dinf₀ hp hp1 hΛG).subset
      (t := {𝔫 : Ideal (redRing C G (xF C G)) | 𝔫.IsMaximal ∧
      (⟨fun w ↦ red C (algebraMap C G (1 : C) * xF C G + algebraMap C G (-β)) w,
        red_mem_redRing hg⟩ : redRing C G (xF C G)) ∈ 𝔫} ∩
      Function.support (dinf 𝓀 (fun w : Ext C G ↦ ResidueField w.1.valuationSubring) hΛG))
      fun 𝔫 h ↦ ⟨h.1.1, h.2⟩
    exact hd𝔫 ((DiscBridge.finsum_mem_eq_zero_iff_nat hfin').1 h0 𝔫 ⟨h𝔫, hg𝔫⟩)
  -- back to a residue class of `D` in the coordinate of `F`
  set K₄ := Aff (0 + c' * β) (c' * 1) (mul_ne_zero hc0' one_ne_zero) K
  haveI : Finite (Ext C K₄) := finite_ext (F := K₄) hp hp1
  letI : Fintype (Ext C K₄) := Fintype.ofFinite _
  set K₅ := Aff (b + d * (0 + c' * β)) (d * (c' * 1))
    (mul_ne_zero hd (mul_ne_zero hc0' one_ne_zero)) F
  haveI : Finite (Ext C K₅) := finite_ext (F := K₅) hp hp1
  letI : Fintype (Ext C K₅) := Fintype.ofFinite _
  have hΛK₄ := chart₀ hp hp1 K₄
  have hΛK₅ := chart₀ hp hp1 K₅
  have h4 := tot0_comp (F := K) (a := β) (b := 0) (c := 1) (d := c') hc0' one_ne_zero hΛG' hΛK₄
  have h5 := tot0_comp (F := F) (a := 0 + c' * β) (b := b) (c := c' * 1) (d := d) hd
    (mul_ne_zero hc0' one_ne_zero) hΛK₄ hΛK₅
  have hK5 : tot0 C K₅ hΛK₅ (fun 𝔫 ↦ DiscBridge.xbar hΛK₅ ∈ 𝔫) ≠ 0 := by
    rw [h5, h4]; exact hG'
  refine ⟨β, hβ, fun hx ↦ ?_, fun hs ↦ hK5 ((DiscBridge.tot0_eq_zero_iff hp hp1 hΛK₅).2 ?_)⟩
  · refine le_antisymm hβ (not_lt.1 fun hβ1 ↦ hx ?_)
    convert hg𝔫 using 1
    apply Subtype.ext
    funext w
    have hβ1' : ‖β‖₊ < 1 := by exact_mod_cast hβ1
    change red C (xF C G) w = red C (algebraMap C G (1 : C) * xF C G + algebraMap C G (-β)) w
    have hv1 : w.1 (algebraMap C G β) < 1 := by rw [valuation_algebraMap_C']; exact hβ1'
    rw [hgx, red_sub (valuation_xF _).le hv1.le, (red_eq_zero_iff hv1.le).2 hv1, sub_zero]
  · exact (discSmooth_congr (by ring) (by ring) _ _).1 hs


include hp hp1 in
/-- A singular point of the chart of `D` lies over some residue class of `D`. -/
lemma exists_bad_class {b d c' : C} (hd : d ≠ 0) (hc0' : c' ≠ 0)
    [Fintype (Ext C (Aff (0 : C) c' hc0' (Aff b d hd F)))]
    (hΛG : IsChart 𝓀 (fun w : Ext C (Aff (0 : C) c' hc0' (Aff b d hd F)) ↦
      red C (xF C (Aff (0 : C) c' hc0' (Aff b d hd F))) w)
      (redRing C _ (xF C (Aff (0 : C) c' hc0' (Aff b d hd F)))))
    (hK0 : tot0 C _ hΛG (fun _ ↦ True) ≠ 0) :
    ∃ β : C, ‖β‖ ≤ 1 ∧ ¬ DiscSmooth F (b + d * c' * β) (mul_ne_zero hd hc0') := by
  classical
  have hfin := (finite_dinf₀ hp hp1 hΛG).subset
    (t := {𝔫 : Ideal (redRing C _ (xF C (Aff (0 : C) c' hc0' (Aff b d hd F)))) |
      𝔫.IsMaximal ∧ True} ∩ Function.support (dinf 𝓀 (fun w : Ext C (Aff (0 : C) c' hc0'
        (Aff b d hd F)) ↦ ResidueField w.1.valuationSubring) hΛG))
    fun 𝔫 h ↦ ⟨h.1.1, h.2⟩
  obtain ⟨𝔫, ⟨h𝔫, -⟩, hd𝔫⟩ : ∃ 𝔫, (𝔫.IsMaximal ∧ True) ∧ dinf 𝓀 (fun w : Ext C (Aff (0 : C)
      c' hc0' (Aff b d hd F)) ↦ ResidueField w.1.valuationSubring) hΛG 𝔫 ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hK0 ((DiscBridge.finsum_mem_eq_zero_iff_nat hfin).2 hne)
  obtain ⟨β, hβ, -, hbad⟩ := bad_class_of_point hp hp1 hd hc0' hΛG h𝔫 hd𝔫
  exact ⟨β, hβ, hbad⟩

include hp hp1 in
/-- **Descent of singularities into an exhausting disc of a tube** (`ExhaustDescentFor`). -/
theorem exhaustDescentFor : ExhaustDescentFor C F := by
  classical
  intro b d c' hd hc' hc0' hex htube hbad
  set K := Aff b d hd F
  set G := Aff (0 : C) c' hc0' K
  haveI : Finite (Ext C K) := finite_ext (F := K) hp hp1
  letI : Fintype (Ext C K) := Fintype.ofFinite _
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  have hΛK := chart₀ hp hp1 K
  have hΛG := chart₀ hp hp1 G
  have hK0 : tot0 C K hΛK (fun 𝔫 ↦ DiscBridge.xbar hΛK ∈ 𝔫) ≠ 0 := fun h ↦
    hbad ((DiscBridge.tot0_eq_zero_iff hp hp1 hΛK).1 h)
  rw [tot0_eq_of_exhausting hp hp1 hd hc' hc0' hex htube hΛK hΛG] at hK0
  exact exists_bad_class hp hp1 hd hc0' hΛG hK0

end Main

end ExhaustDescent

end SemistableReduction
