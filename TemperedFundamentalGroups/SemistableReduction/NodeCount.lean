/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeBridge

/-!
# Counting points over the node

Blueprint §9.12, O12 / R5. In the reduced chart `Λ_T` of the two-vertex model `TwoV c F` at
`t = x + c/x`, the closed points over the node `t̄ = 0` are the centres of the transported outer
branches (zeros of `x̄`, `outerZ`) and inner branches (zeros of `(c/x)‾`, `innerZ`); every such
point carries at least one of each (`exists_outer_inner`, from the matching of tube degrees, S6).

* **`tot0_t_eq_of_nodeGood`**: if every point over the node is an ordinary double point, the total
  `δ` over the node is the number of inner branches (and of outer branches);
* **`nodeGood_of_tot0_le`**: conversely, if the total `δ` over the node is at most `n` and there
  are exactly `n` outer and `n` inner branches, every point over the node is an ordinary double
  point.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal

namespace SemistableReduction

namespace NodeBridge

open GaussFibre TwoVertex TwoVertexCharts AffineTwist ChartLocal DeltaCount GaussTube
  FundamentalInequality GaussStability

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] {c : C} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1)
  [Fintype (Ext C F)] [Fintype (Ext C (Inv c hc0 F))] [Fintype (Ext C (TwoV c F))]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-- The node: the points of `R'` over the node are good (ordinary double points). -/
def NodeGoodR : Prop :=
  ∀ P' : Ideal (Rint c F), P'.IsMaximal →
    P'.comap (algebraMap (nodeRing c) (Rint c F)) = tubeIdeal c → IsNodeODP hc1 hc0 P'

/-- The outer branches over the node, as branches of `Λ_T`. -/
noncomputable def outerZ :
    Finset (Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)) :=
  (Finset.univ.sigma fun v : Ext C F ↦ PlaceNorm.zeros 𝓀 (red C (xF C F) v)).map
    ⟨(EU hc0 hc1).pmap, (EU hc0 hc1).pmap_injective⟩

/-- The inner branches over the node, as branches of `Λ_T`. -/
noncomputable def innerZ :
    Finset (Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)) :=
  (Finset.univ.sigma fun w₂ : Ext C (Inv c hc0 F) ↦
    PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂)).map
    ⟨(EI hc0 hc1).pmap, (EI hc0 hc1).pmap_injective⟩

omit [CharZero C] [Fintype (GaussFibre.Ext C (GaussTube.Inv c hc0 F))]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma card_outerZ :
    (outerZ (F := F) hc0 hc1).card =
      ∑ v : Ext C F, (PlaceNorm.zeros 𝓀 (red C (xF C F) v)).card := by
  rw [outerZ, Finset.card_map, Finset.card_sigma]

omit [CharZero C] [Fintype (GaussFibre.Ext C F)] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma card_innerZ :
    (innerZ (F := F) hc0 hc1).card =
      ∑ w₂ : Ext C (Inv c hc0 F), (PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂)).card := by
  rw [innerZ, Finset.card_map, Finset.card_sigma]

omit [CharZero C] [Fintype (GaussFibre.Ext C (GaussTube.Inv c hc0 F))]
  [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma mem_outerZ {b : Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)} :
    b ∈ outerZ hc0 hc1 ↔ ∃ (v : Ext C F) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)),
      Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v) ∧ (EU hc0 hc1).pmap ⟨v, Q⟩ = b := by
  simp only [outerZ, Finset.mem_map, Finset.mem_sigma, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨v, Q⟩, hQ, rfl⟩; exact ⟨v, Q, hQ, rfl⟩
  · rintro ⟨v, Q, hQ, rfl⟩; exact ⟨⟨v, Q⟩, hQ, rfl⟩

omit [CharZero C] [Fintype (GaussFibre.Ext C F)] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma mem_innerZ {b : Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)} :
    b ∈ innerZ hc0 hc1 ↔ ∃ (w₂ : Ext C (Inv c hc0 F))
      (Q : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)),
      Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂) ∧ (EI hc0 hc1).pmap ⟨w₂, Q⟩ = b := by
  simp only [innerZ, Finset.mem_map, Finset.mem_sigma, Finset.mem_univ, true_and,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨⟨v, Q⟩, hQ, rfl⟩; exact ⟨v, Q, hQ, rfl⟩
  · rintro ⟨v, Q, hQ, rfl⟩; exact ⟨⟨v, Q⟩, hQ, rfl⟩

omit [CharZero C] [Fintype (GaussFibre.Ext C (TwoV c F))] in
lemma disjoint_outerZ_innerZ : Disjoint (outerZ (F := F) hc0 hc1) (innerZ hc0 hc1) := by
  rw [Finset.disjoint_left]
  intro b hb hb'
  obtain ⟨v, Q, -, rfl⟩ := (mem_outerZ hc0 hc1).1 hb
  obtain ⟨w₂, Q₂, -, e⟩ := (mem_innerZ hc0 hc1).1 hb'
  rw [pmap_U, pmap_I] at e
  exact ιU_ne_ιI hc0 hc1 v w₂ (congrArg Sigma.fst e).symm

section Points

variable (hΛT : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
  (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F)) w) (redRing C (TwoV c F) (xF C (TwoV c F))))

open Classical in
omit [CharZero C] [Fintype (GaussFibre.Ext C (GaussTube.Inv c hc0 F))] in
lemma centerOf_outerZ
    {b : Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)}
    (hb : b ∈ outerZ hc0 hc1) : (centerOf hΛT b).IsMaximal ∧ tbar hΛT ∈ centerOf hΛT b := by
  obtain ⟨v, Q, hQ, rfl⟩ := (mem_outerZ hc0 hc1).1 hb
  rw [pmap_U, centerOf_eq hΛT (b := ⟨ιU hc0 hc1 v, Q.map ((EU hc0 hc1).e v)⟩) (hz_U hc0 hc1 v hQ)]
  refine ⟨center_isMaximal hΛT _ _, ?_⟩
  rw [mem_center]
  change (Q.map ((EU hc0 hc1).e v)).valuation (red C (xF C (TwoV c F)) (ιU hc0 hc1 v)) < 1
  rw [red_t_U, CurvePlace.valuation_map_apply]
  exact PlaceNorm.valuation_x_lt_one hQ

open Classical in
omit [CharZero C] [Fintype (GaussFibre.Ext C F)] in
lemma centerOf_innerZ
    {b : Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)}
    (hb : b ∈ innerZ hc0 hc1) : (centerOf hΛT b).IsMaximal ∧ tbar hΛT ∈ centerOf hΛT b := by
  obtain ⟨w₂, Q, hQ, rfl⟩ := (mem_innerZ hc0 hc1).1 hb
  rw [pmap_I, centerOf_eq hΛT (b := ⟨ιI hc0 hc1 w₂, Q.map ((EI hc0 hc1).e w₂)⟩)
    (hz_I hc0 hc1 w₂ hQ)]
  refine ⟨center_isMaximal hΛT _ _, ?_⟩
  rw [mem_center]
  change (Q.map ((EI hc0 hc1).e w₂)).valuation (red C (xF C (TwoV c F)) (ιI hc0 hc1 w₂)) < 1
  rw [red_t_I, CurvePlace.valuation_map_apply]
  exact PlaceNorm.valuation_x_lt_one hQ

open Classical in
/-- The closed points over the node. -/
noncomputable def nodePts : Finset (Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))) :=
  (outerZ hc0 hc1 ∪ innerZ hc0 hc1).image (centerOf hΛT)

open Classical in
include hp hp1 in
/-- The branches of a point over the node are transported outer or inner branches. -/
lemma mem_union_of_mem_brs {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))}
    [h𝔫 : 𝔫.IsMaximal] (ht : tbar hΛT ∈ 𝔫)
    {b : Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)}
    (hb : b ∈ brs hΛT 𝔫) : b ∈ outerZ hc0 hc1 ∪ innerZ hc0 hc1 := by
  haveI : (𝔫.comap (redT hc0 hc1)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (redT_surjective hc0 hc1 hp hp1)
  have hc := comap_comap_eq hc0 hc1 hΛT ht
  rw [← Ideal.map_comap_of_surjective _ (redT_surjective hc0 hc1 hp hp1) 𝔫] at hb
  rcases brs_cases hc0 hc1 hp hp1 hΛT hc hb with ⟨v, Q, hQ, rfl, -⟩ | ⟨w₂, Q, hQ, rfl, -⟩
  · exact Finset.mem_union_left _ ((mem_outerZ hc0 hc1).2 ⟨v, Q, hQ, rfl⟩)
  · exact Finset.mem_union_right _ ((mem_innerZ hc0 hc1).2 ⟨w₂, Q, hQ, rfl⟩)

open Classical in
include hp hp1 in
lemma mem_nodePts_iff (𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))) :
    𝔫 ∈ nodePts hc0 hc1 hΛT ↔ 𝔫.IsMaximal ∧ tbar hΛT ∈ 𝔫 := by
  classical
  rw [nodePts, Finset.mem_image]
  constructor
  · rintro ⟨b, hb, rfl⟩
    rcases Finset.mem_union.1 hb with hb | hb
    · exact centerOf_outerZ hc0 hc1 hΛT hb
    · exact centerOf_innerZ hc0 hc1 hΛT hb
  · rintro ⟨h𝔫, ht⟩
    obtain ⟨b, hb⟩ := exists_mem_brs hΛT h𝔫
    exact ⟨b, mem_union_of_mem_brs hc0 hc1 hp hp1 hΛT ht hb, hb⟩

open Classical in
include hp hp1 in
/-- The total `δ` over the node as a finite sum. -/
lemma tot0_t_eq_sum :
    tot0 C (TwoV c F) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) =
      ∑ 𝔫 ∈ nodePts hc0 hc1 hΛT,
        dinf 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT 𝔫 := by
  rw [tot0, ← finsum_mem_coe_finset]
  congr 1
  ext 𝔫
  rw [Finset.mem_coe, mem_nodePts_iff hc0 hc1 hp hp1 hΛT]
  rfl

open Classical in
include hp hp1 in
lemma brsF_eq_filter {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))}
    (h𝔫 : 𝔫 ∈ nodePts hc0 hc1 hΛT) :
    brsF hΛT 𝔫 = (outerZ hc0 hc1 ∪ innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫) := by
  obtain ⟨hmax, ht⟩ := (mem_nodePts_iff hc0 hc1 hp hp1 hΛT 𝔫).1 h𝔫
  haveI := hmax
  ext b
  rw [mem_brsF hΛT hmax.ne_top, Finset.mem_filter, mem_brs]
  exact ⟨fun hb ↦ ⟨mem_union_of_mem_brs hc0 hc1 hp hp1 hΛT ht hb, hb⟩, fun h ↦ h.2⟩

open Classical in
omit [Fintype (GaussFibre.Ext C F)] in
include hp hp1 in
lemma dl_le_dinf_T {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))} (h𝔫 : 𝔫.IsMaximal)
    (M : ℕ) :
    dl 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT 𝔫 M ≤
      dinf 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT 𝔫 := by
  obtain ⟨M₁, hM₁⟩ := DiscBridge.exists_forall_dl_eq_dinf_x hp hp1 hΛT
  rw [← hM₁ (max M M₁) (le_max_right _ _) 𝔫 h𝔫]
  exact dl_mono hΛT h𝔫.ne_top (le_max_left _ _)

open Classical in
include hp hp1 in
/-- **Every point over the node lies on an outer and on an inner branch** (matching of tube
degrees, S6). -/
lemma exists_outer_inner {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))}
    (h𝔫 : 𝔫 ∈ nodePts hc0 hc1 hΛT) :
    (∃ b ∈ outerZ hc0 hc1, centerOf hΛT b = 𝔫) ∧ ∃ b ∈ innerZ hc0 hc1, centerOf hΛT b = 𝔫 := by
  obtain ⟨hmax, ht⟩ := (mem_nodePts_iff hc0 hc1 hp hp1 hΛT 𝔫).1 h𝔫
  haveI := hmax
  haveI : Algebra.IsSeparable (RatFunc C) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  set P' := 𝔫.comap (redT hc0 hc1)
  haveI : P'.IsMaximal := Ideal.comap_isMaximal_of_surjective _ (redT_surjective hc0 hc1 hp hp1)
  have hP' := comap_comap_eq hc0 hc1 hΛT ht
  have e : P'.map (redT hc0 hc1) = 𝔫 :=
    Ideal.map_comap_of_surjective _ (redT_surjective hc0 hc1 hp hp1) 𝔫
  refine ⟨?_, ?_⟩
  · obtain ⟨b, hb⟩ := exists_outerBranch hp hp1 hc1 hc0 P' hP'
    have hm := mem_brs_U hc0 hc1 hp hp1 hΛT b.1 b.2.2 hb
    rw [e] at hm
    exact ⟨_, (mem_outerZ hc0 hc1).2 ⟨b.1, b.2.1, b.2.2, rfl⟩, hm⟩
  · haveI : (P'.comap (rintEquiv hc0).symm.toRingHom).IsMaximal :=
      Ideal.comap_isMaximal_of_surjective _ (rintEquiv hc0).symm.surjective
    have hPinv : (P'.comap (rintEquiv hc0).symm.toRingHom).comap
        (algebraMap (nodeRing c) (Rint c (Inv c hc0 F))) = tubeIdeal c := by
      ext a
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have he : (rintEquiv hc0).symm.toRingHom
          (algebraMap (nodeRing c) (Rint c (Inv c hc0 F)) a) =
          algebraMap (nodeRing c) (Rint c F) (invNode hc0 a) := rfl
      rw [he, ← Ideal.mem_comap, hP', invNode_mem_tubeIdeal_iff]
    obtain ⟨b, hb⟩ := exists_outerBranch (F' := Inv c hc0 F) hp hp1 hc1 hc0 _ hPinv
    have hm := mem_brs_I hc0 hc1 hp hp1 hΛT b.1 b.2.2 hb
    rw [e] at hm
    exact ⟨_, (mem_innerZ hc0 hc1).2 ⟨b.1, b.2.1, b.2.2, rfl⟩, hm⟩

open Classical in
include hp hp1 in
lemma card_brsF_eq {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))}
    (h𝔫 : 𝔫 ∈ nodePts hc0 hc1 hΛT) :
    (brsF hΛT 𝔫).card = ((outerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card +
      ((innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card := by
  rw [brsF_eq_filter hc0 hc1 hp hp1 hΛT h𝔫, Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (disjoint_outerZ_innerZ hc0 hc1)

open Classical in
omit [Fintype (GaussFibre.Ext C F)] in
include hp hp1 in
lemma card_sub_one_le_dinf_T {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))}
    (h𝔫 : 𝔫.IsMaximal) :
    (brsF hΛT 𝔫).card - 1 ≤
      dinf 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT 𝔫 := by
  haveI := h𝔫
  exact (card_sub_one_le_dl hΛT (M := 1) le_rfl).trans (dl_le_dinf_T hp hp1 hΛT h𝔫 1)

open Classical in
omit [CharZero C] in
lemma card_outerZ_eq_sum :
    (outerZ (F := F) hc0 hc1).card = ∑ 𝔫 ∈ nodePts hc0 hc1 hΛT,
      ((outerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card :=
  Finset.card_eq_sum_card_fiberwise fun _ hb ↦
    Finset.mem_image_of_mem _ (Finset.mem_union_left _ hb)

open Classical in
omit [CharZero C] in
lemma card_innerZ_eq_sum :
    (innerZ (F := F) hc0 hc1).card = ∑ 𝔫 ∈ nodePts hc0 hc1 hΛT,
      ((innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card :=
  Finset.card_eq_sum_card_fiberwise fun _ hb ↦
    Finset.mem_image_of_mem _ (Finset.mem_union_right _ hb)

open Classical in
include hp hp1 in
/-- At an ordinary double point over the node: one outer branch, one inner branch, `δ = 1`. -/
lemma node_structure {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))}
    (h𝔫 : 𝔫 ∈ nodePts hc0 hc1 hΛT) (hODP : IsNodeODP hc1 hc0 (𝔫.comap (redT hc0 hc1))) :
    dinf 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT 𝔫 = 1 ∧
      ((outerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card = 1 ∧
      ((innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card = 1 := by
  obtain ⟨hmax, ht⟩ := (mem_nodePts_iff hc0 hc1 hp hp1 hΛT 𝔫).1 h𝔫
  haveI := hmax
  haveI : (𝔫.comap (redT hc0 hc1)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (redT_surjective hc0 hc1 hp hp1)
  have hP' := comap_comap_eq hc0 hc1 hΛT ht
  have e : (𝔫.comap (redT hc0 hc1)).map (redT hc0 hc1) = 𝔫 :=
    Ideal.map_comap_of_surjective _ (redT_surjective hc0 hc1 hp hp1) 𝔫
  obtain ⟨v₁, Q₁, hQ₁, w₂, Q₂, hQ₂, hP₁, hP₂, huniq, hdl⟩ :=
    structure_of_isNodeODP hc0 hc1 hp hp1 hΛT hP' hODP
  have hU := mem_brs_U hc0 hc1 hp hp1 hΛT v₁ hQ₁ hP₁
  have hI := mem_brs_I hc0 hc1 hp hp1 hΛT w₂ hQ₂ hP₂
  rw [e] at huniq hdl hU hI
  have hUZ : (EU hc0 hc1).pmap ⟨v₁, Q₁⟩ ∈ outerZ hc0 hc1 :=
    (mem_outerZ hc0 hc1).2 ⟨v₁, Q₁, hQ₁, rfl⟩
  have hIZ : (EI hc0 hc1).pmap ⟨w₂, Q₂⟩ ∈ innerZ hc0 hc1 :=
    (mem_innerZ hc0 hc1).2 ⟨w₂, Q₂, hQ₂, rfl⟩
  have hdisj := disjoint_outerZ_innerZ (F := F) hc0 hc1
  refine ⟨le_antisymm ?_ ?_, Finset.card_eq_one.2 ⟨(EU hc0 hc1).pmap ⟨v₁, Q₁⟩, ?_⟩,
    Finset.card_eq_one.2 ⟨(EI hc0 hc1).pmap ⟨w₂, Q₂⟩, ?_⟩⟩
  · obtain ⟨M₁, hM₁⟩ := DiscBridge.exists_forall_dl_eq_dinf_x hp hp1 hΛT
    rw [← hM₁ M₁ le_rfl 𝔫 hmax]
    exact hdl M₁
  · have hcard : 1 < (brsF hΛT 𝔫).card := Finset.one_lt_card.2
      ⟨_, (mem_brsF hΛT hmax.ne_top).2 hU, _, (mem_brsF hΛT hmax.ne_top).2 hI,
        fun h ↦ Finset.disjoint_left.1 hdisj hUZ (h ▸ hIZ)⟩
    have := card_sub_one_le_dinf_T hp hp1 hΛT hmax
    omega
  · ext b
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb, hbc⟩
      rcases huniq b hbc with h | h
      · exact h
      · exact absurd (h ▸ hIZ) (Finset.disjoint_left.1 hdisj hb)
    · rintro rfl
      exact ⟨hUZ, hU⟩
  · ext b
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hb, hbc⟩
      rcases huniq b hbc with h | h
      · exact absurd (h ▸ hUZ) (Finset.disjoint_right.1 hdisj hb)
      · exact h
    · rintro rfl
      exact ⟨hIZ, hI⟩

open Classical in
include hp hp1 in
/-- **The total `δ` over a good node** is the number of inner (and of outer) branches. -/
theorem tot0_t_of_nodeGood (h : NodeGoodR (F := F) hc0 hc1) :
    tot0 C (TwoV c F) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) = (innerZ (F := F) hc0 hc1).card ∧
      tot0 C (TwoV c F) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) = (outerZ (F := F) hc0 hc1).card := by
  have hst : ∀ 𝔫 ∈ nodePts hc0 hc1 hΛT,
      dinf 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT 𝔫 = 1 ∧
      ((outerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card = 1 ∧
      ((innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card = 1 := fun 𝔫 h𝔫 ↦ by
    obtain ⟨hmax, ht⟩ := (mem_nodePts_iff hc0 hc1 hp hp1 hΛT 𝔫).1 h𝔫
    haveI := hmax
    exact node_structure hc0 hc1 hp hp1 hΛT h𝔫 (h _
      (Ideal.comap_isMaximal_of_surjective _ (redT_surjective hc0 hc1 hp hp1))
      (comap_comap_eq hc0 hc1 hΛT ht))
  rw [tot0_t_eq_sum hc0 hc1 hp hp1 hΛT, card_innerZ_eq_sum hc0 hc1 hΛT,
    card_outerZ_eq_sum hc0 hc1 hΛT]
  exact ⟨Finset.sum_congr rfl fun 𝔫 h𝔫 ↦ (hst 𝔫 h𝔫).1.trans (hst 𝔫 h𝔫).2.2.symm,
    Finset.sum_congr rfl fun 𝔫 h𝔫 ↦ (hst 𝔫 h𝔫).1.trans (hst 𝔫 h𝔫).2.1.symm⟩

open Classical in
include hp hp1 in
/-- **Good nodes from the `δ`-count**: if the total `δ` over the node is at most `n` and there are
exactly `n` outer and `n` inner branches, every point over the node is an ordinary double
point. -/
theorem nodeGood_of_tot0_le {n : ℕ}
    (htot : tot0 C (TwoV c F) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) ≤ n)
    (hU : (outerZ (F := F) hc0 hc1).card = n) (hI : (innerZ (F := F) hc0 hc1).card = n) :
    NodeGoodR (F := F) hc0 hc1 := by
  set NP := nodePts hc0 hc1 hΛT
  set u := fun 𝔫 ↦ ((outerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card
  set i := fun 𝔫 ↦ ((innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = 𝔫)).card
  set d := fun 𝔫 ↦
    dinf 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT 𝔫
  have hu1 : ∀ 𝔫 ∈ NP, 1 ≤ u 𝔫 := fun 𝔫 h𝔫 ↦ by
    obtain ⟨b, hb, hbc⟩ := (exists_outer_inner hc0 hc1 hp hp1 hΛT h𝔫).1
    exact Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨hb, hbc⟩⟩
  have hi1 : ∀ 𝔫 ∈ NP, 1 ≤ i 𝔫 := fun 𝔫 h𝔫 ↦ by
    obtain ⟨b, hb, hbc⟩ := (exists_outer_inner hc0 hc1 hp hp1 hΛT h𝔫).2
    exact Finset.card_pos.2 ⟨b, Finset.mem_filter.2 ⟨hb, hbc⟩⟩
  have hd : ∀ 𝔫 ∈ NP, u 𝔫 + i 𝔫 ≤ d 𝔫 + 1 := fun 𝔫 h𝔫 ↦ by
    have h1 := card_brsF_eq hc0 hc1 hp hp1 hΛT h𝔫
    have h2 := card_sub_one_le_dinf_T hp hp1 hΛT
      ((mem_nodePts_iff hc0 hc1 hp hp1 hΛT 𝔫).1 h𝔫).1
    simp only [u, i, d]
    omega
  have hsu : ∑ 𝔫 ∈ NP, u 𝔫 = n := (card_outerZ_eq_sum hc0 hc1 hΛT).symm.trans hU
  have hsi : ∑ 𝔫 ∈ NP, i 𝔫 = n := (card_innerZ_eq_sum hc0 hc1 hΛT).symm.trans hI
  have hsd : ∑ 𝔫 ∈ NP, d 𝔫 ≤ n := (tot0_t_eq_sum hc0 hc1 hp hp1 hΛT).symm.le.trans htot
  have hm1 : ∑ 𝔫 ∈ NP, (1 : ℕ) ≤ n := hsu ▸ Finset.sum_le_sum hu1
  have hm2 : ∑ 𝔫 ∈ NP, (u 𝔫 + i 𝔫) ≤ ∑ 𝔫 ∈ NP, (d 𝔫 + 1) := Finset.sum_le_sum hd
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hsu, hsi] at hm2
  have hm : ∑ 𝔫 ∈ NP, (1 : ℕ) = n := by omega
  have hu : ∀ 𝔫 ∈ NP, u 𝔫 = 1 := fun 𝔫 h𝔫 ↦
    ((Finset.sum_eq_sum_iff_of_le hu1).1 (hm.trans hsu.symm) 𝔫 h𝔫).symm
  have hi : ∀ 𝔫 ∈ NP, i 𝔫 = 1 := fun 𝔫 h𝔫 ↦
    ((Finset.sum_eq_sum_iff_of_le hi1).1 (hm.trans hsi.symm) 𝔫 h𝔫).symm
  have hd1 : ∀ 𝔫 ∈ NP, 1 ≤ d 𝔫 := fun 𝔫 h𝔫 ↦ by
    have := hd 𝔫 h𝔫; rw [hu 𝔫 h𝔫, hi 𝔫 h𝔫] at this; omega
  have hdeq : ∀ 𝔫 ∈ NP, d 𝔫 = 1 := fun 𝔫 h𝔫 ↦
    ((Finset.sum_eq_sum_iff_of_le hd1).1
      (le_antisymm (Finset.sum_le_sum hd1) (hm ▸ hsd)) 𝔫 h𝔫).symm
  -- every point over the node is an ordinary double point
  intro P' hP'm hP'
  have h𝔫 : P'.map (redT hc0 hc1) ∈ NP :=
    (mem_nodePts_iff hc0 hc1 hp hp1 hΛT _).2
      ⟨map_isMaximal hc0 hc1 hp hp1 hP', tbar_mem_map hc0 hc1 hΛT hP'⟩
  have hcm := comap_map hc0 hc1 hp hp1 hP'
  obtain ⟨β₁, hβ₁⟩ := Finset.card_eq_one.1 (hu _ h𝔫)
  obtain ⟨β₂, hβ₂⟩ := Finset.card_eq_one.1 (hi _ h𝔫)
  have hβ₁m : β₁ ∈ (outerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = P'.map (redT hc0 hc1)) := by
    rw [hβ₁]; exact Finset.mem_singleton_self _
  have hβ₂m : β₂ ∈ (innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = P'.map (redT hc0 hc1)) := by
    rw [hβ₂]; exact Finset.mem_singleton_self _
  obtain ⟨hβ₁Z, hβ₁c⟩ := Finset.mem_filter.1 hβ₁m
  obtain ⟨hβ₂Z, hβ₂c⟩ := Finset.mem_filter.1 hβ₂m
  obtain ⟨v₁, Q₁, hQ₁, rfl⟩ := (mem_outerZ hc0 hc1).1 hβ₁Z
  obtain ⟨w₂, Q₂, hQ₂, rfl⟩ := (mem_innerZ hc0 hc1).1 hβ₂Z
  rw [pmap_U] at hβ₁c
  rw [pmap_I] at hβ₂c
  rw [centerOf_eq hΛT (b := ⟨ιU hc0 hc1 v₁, Q₁.map ((EU hc0 hc1).e v₁)⟩) (hz_U hc0 hc1 v₁ hQ₁)]
    at hβ₁c
  rw [centerOf_eq hΛT (b := ⟨ιI hc0 hc1 w₂, Q₂.map ((EI hc0 hc1).e w₂)⟩) (hz_I hc0 hc1 w₂ hQ₂)]
    at hβ₂c
  have hP₁ : placeIdeal hc1 v₁ hQ₁ = P' := by
    rw [← comap_center_U hc0 hc1 hΛT v₁ hQ₁, ← hcm]
    exact congrArg (Ideal.comap (redT hc0 hc1)) hβ₁c
  have hP₂ : placeIdeal hc1 w₂ hQ₂ = P'.comap (rintEquiv hc0).symm.toRingHom := by
    have h2 := comap_center_I hc0 hc1 hΛT w₂ hQ₂
    have h3 : (ChartLocal.center hΛT (j := ιI hc0 hc1 w₂) (Q₂.map ((EI hc0 hc1).e w₂))
        (hz_I hc0 hc1 w₂ hQ₂)).comap (redT hc0 hc1) = P' := by
      rw [← hcm]; exact congrArg (Ideal.comap (redT hc0 hc1)) hβ₂c
    rw [h3] at h2
    rw [h2, Ideal.comap_comap]
    convert (Ideal.comap_id (placeIdeal hc1 w₂ hQ₂)).symm
    ext y
    exact congrArg Subtype.val ((rintEquiv hc0).apply_symm_apply y)
  refine isNodeODP_of hc0 hc1 hp hp1 hΛT hP' v₁ hQ₁ w₂ hQ₂ hP₁ hP₂ (fun b hb ↦ ?_) fun M ↦ ?_
  · haveI := map_isMaximal hc0 hc1 hp hp1 hP'
    rcases Finset.mem_union.1 (mem_union_of_mem_brs hc0 hc1 hp hp1 hΛT
      (tbar_mem_map hc0 hc1 hΛT hP') hb) with hbZ | hbZ
    · left
      have : b ∈ (outerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = P'.map (redT hc0 hc1)) :=
        Finset.mem_filter.2 ⟨hbZ, hb⟩
      rw [hβ₁, Finset.mem_singleton, pmap_U] at this
      exact this
    · right
      have : b ∈ (innerZ hc0 hc1).filter (fun b ↦ centerOf hΛT b = P'.map (redT hc0 hc1)) :=
        Finset.mem_filter.2 ⟨hbZ, hb⟩
      rw [hβ₂, Finset.mem_singleton, pmap_I] at this
      exact this
  · have := dl_le_dinf_T hp hp1 hΛT (map_isMaximal hc0 hc1 hp hp1 hP') M
    have h1 := hdeq _ h𝔫
    simp only [d] at h1
    omega

end Points

end NodeBridge

end SemistableReduction
