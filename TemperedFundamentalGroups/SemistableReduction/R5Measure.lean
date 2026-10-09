/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NearBoundary
import TemperedFundamentalGroups.SemistableReduction.R5Charts
import TemperedFundamentalGroups.SemistableReduction.S8Interfaces

/-!
# R5: the measure `(δ, -m)` decreases into the smallest exhausting disc

Blueprint §9.10 (R5), §9.12 O6.2; [AW Lemma 2.6, §2.5]. For a residue ball `B = D(a, |c|)⁻` let
`δ(B)` be the total `δ` over `x̄ = 0` of the chart `Aff a c F` (`dl`) and `m(B)` the number of
branches over `x̄ = 0` (`mb`, at most `[F : C(x)]`). The measure `μ(B) = (N + 1) δ(B) + (N - m(B))`
(`N = [F : C(x)]`, the lexicographic order on `(δ, -m)`) does not depend on the representative
(`R5Charts`).

* `isExhausting_transfer`, `edgeGood_of_isExhausting`: exhaustion in one representative is
  exhaustion in every representative (the total `δ` over the node is determined by the local
  formula `LocalFormula.local_formula` through invariants of the open ball and of the disc, and
  exhaustion is a statement about it, `NodeBridge.nodeGood_of_tot0_le`);
* `exists_smaller` (the improvement step): if `D(a, |c u|)` is exhausting in `D(a, |c|)⁻` and
  `μ` does not decrease to the residue class `D(a, |c u|)⁻`, then the local formula forces equality
  everywhere: the residue curves of the Gauss point of `D` are rational with one point over `∞`
  and one over `0`, the other residue classes are good, so `w_{a,|c u|}` is a circle of a tube;
  `GaussTube.belowGerm` and the gluing step `ExhaustGlueFor` give a smaller exhausting disc;
* **`r5MeasureFor_of`**: `ExhaustGlueFor C F → S8A.R5MeasureFor C F`.
-/

open Polynomial IsLocalRing WithZero Metric
open scoped NNReal

namespace SemistableReduction

namespace R5Measure

open GaussFibre ChartLocal DeltaCount FundamentalInequality GaussStability AffineTwist
  TwoVertex NodeBridge ChartChange LocalFormula ExhaustGluing ExhaustDescent

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

section Generic

variable {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]

omit [Fintype (Ext C K)] in
lemma one_le_card_zeros (w : Ext C K) : 1 ≤ (PlaceNorm.zeros 𝓀 (red C (xF C K) w)).card := by
  obtain ⟨Q, hQ⟩ := GaussTube.exists_mem_zeros w
  exact Finset.card_pos.2 ⟨Q, hQ⟩

omit [Fintype (Ext C K)] in
lemma one_le_card_zeros_inv (w : Ext C K) :
    1 ≤ (PlaceNorm.zeros 𝓀 (red C (xF C K) w)⁻¹).card := by
  have hx : (red C (xF C K) w)⁻¹ ∉ (algebraMap 𝓀 (IsLocalRing.ResidueField
      w.1.valuationSubring)).range := fun ⟨a, ha⟩ ↦ transcendental_red_x (F := K) w (by
    rw [← inv_inv (red C (xF C K) w), ← ha, ← map_inv₀]
    exact isAlgebraic_algebraMap _)
  have h := PlaceNorm.sum_ord hx
  rw [Nat.one_le_iff_ne_zero]
  intro H
  rw [Finset.card_eq_zero] at H
  rw [H, Finset.sum_empty] at h
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hx)
  exact Module.finrank_pos.ne' h.symm

lemma card_le_mm : Fintype.card (Ext C K) ≤ mm C K := by
  rw [mm, Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun w _ ↦ one_le_card_zeros w

lemma card_le_ic : Fintype.card (Ext C K) ≤ ic C K := by
  rw [ic, Fintype.card_eq_sum_ones]
  exact Finset.sum_le_sum fun w _ ↦ one_le_card_zeros_inv w

lemma card_zeros_eq_one_of_mm (h : mm C K ≤ Fintype.card (Ext C K)) (w : Ext C K) :
    (PlaceNorm.zeros 𝓀 (red C (xF C K) w)).card = 1 := by
  rw [mm, Fintype.card_eq_sum_ones] at h
  exact ((Finset.sum_eq_sum_iff_of_le fun w _ ↦ one_le_card_zeros w).1
    (le_antisymm (Finset.sum_le_sum fun w _ ↦ one_le_card_zeros w) h) w
    (Finset.mem_univ _)).symm

lemma card_zeros_inv_eq_one_of_ic (h : ic C K ≤ Fintype.card (Ext C K)) (w : Ext C K) :
    (PlaceNorm.zeros 𝓀 (red C (xF C K) w)⁻¹).card = 1 := by
  rw [ic, Fintype.card_eq_sum_ones] at h
  exact ((Finset.sum_eq_sum_iff_of_le fun w _ ↦ one_le_card_zeros_inv w).1
    (le_antisymm (Finset.sum_le_sum fun w _ ↦ one_le_card_zeros_inv w) h) w
    (Finset.mem_univ _)).symm

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
lemma mm_le_finrank : mm C K ≤ Module.finrank (RatFunc C) K := by
  rw [← GaussTube.sum_sum_ord hp hp1, mm]
  refine Finset.sum_le_sum fun w _ ↦ ?_
  rw [Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun Q hQ ↦ PlaceNorm.one_le_ord hQ

end Generic

/-! ### Exhaustion in terms of counts -/

section Exh

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K]
  {v : C} (hv0 : v ≠ 0) (hv1 : ‖v‖ < 1)

omit [CharZero C] in
/-- The inner branches over the node are the branches of `Aff 0 v K` over `∞`. -/
lemma card_innerZ_eq_ic [Fintype (Ext C (GaussTube.Inv v hv0 K))]
    [Fintype (Ext C (Aff (0 : C) v hv0 K))] :
    (innerZ (F := K) hv0 hv1).card = ic C (Aff (0 : C) v hv0 K) := by
  rw [card_innerZ, ic, ← (extEquiv (σInv hv0) (gauss1_σInv hv0) (invEquiv (F := K) hv0)
    (invEquiv_he hv0)).sum_comp]
  refine Finset.sum_congr rfl fun w₂ _ ↦ ?_
  rw [← red_inv_xF, ← invEquiv_x, card_zeros_eq]

variable [Fintype (Ext C K)] [Fintype (Ext C (TwoV v K))] [Fintype (Ext C (Aff (0 : C) v hv0 K))]
  (hΛT : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
    (fun w : Ext C (TwoV v K) ↦ red C (xF C (TwoV v K)) w)
    (redRing C (TwoV v K) (xF C (TwoV v K))))

include hp hp1 in
/-- Over a good node, the total `δ` is the number of branches over `x̄ = 0` and of the inner
branches. -/
lemma exh_counts (hex : NodeGoodR (F := K) hv0 hv1) :
    tot0 C (TwoV v K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) = ic C (Aff (0 : C) v hv0 K) ∧
      tot0 C (TwoV v K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) = mm C K := by
  classical
  haveI : Finite (Ext C (GaussTube.Inv v hv0 K)) := finite_ext (F := GaussTube.Inv v hv0 K) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv v hv0 K)) := Fintype.ofFinite _
  have h := tot0_t_of_nodeGood hv0 hv1 hp hp1 hΛT hex
  rw [card_innerZ_eq_ic, card_outerZ] at h
  exact h

include hp hp1 in
/-- A good node from the counts. -/
lemma nodeGood_of_counts {n : ℕ} (h : tot0 C (TwoV v K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) ≤ n)
    (hm : mm C K = n) (hi : ic C (Aff (0 : C) v hv0 K) = n) : NodeGoodR (F := K) hv0 hv1 := by
  classical
  haveI : Finite (Ext C (GaussTube.Inv v hv0 K)) := finite_ext (F := GaussTube.Inv v hv0 K) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv v hv0 K)) := Fintype.ofFinite _
  refine nodeGood_of_tot0_le hv0 hv1 hp hp1 hΛT h ?_ ?_
  · rw [card_outerZ]; exact hm
  · rw [card_innerZ_eq_ic]; exact hi

end Exh

/-! ### The disc `D(b + d a, |d c|)` in two coordinates -/

section Comp

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  {a d v : C} (hd : d ≠ 0) (hv : v ≠ 0)
  [Fintype (Ext C (Aff (0 : C) v hv (Aff a d hd F)))]
  [Fintype (Ext C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F))]

omit [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [Fintype (Ext C (Aff (0 : C) v hv (Aff a d hd F)))]
  [Fintype (Ext C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F))] in
lemma comp_x :
    xF C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F) =
      compEquiv (F := F) hd hv (algebraMap C (Aff (0 : C) v hv (Aff a d hd F)) (1 : C) *
        xF C (Aff (0 : C) v hv (Aff a d hd F)) +
          algebraMap C (Aff (0 : C) v hv (Aff a d hd F)) (0 : C)) :=
  compEquiv_x hd hv

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma comp_card : Fintype.card (Ext C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F)) =
    Fintype.card (Ext C (Aff (0 : C) v hv (Aff a d hd F))) :=
  (card_ext_eq AlgEquiv.refl gauss1_refl (compEquiv (F := F) hd hv) (compEquiv_he hd hv)).symm

lemma comp_gsum : gsum C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F) =
    gsum C (Aff (0 : C) v hv (Aff a d hd F)) :=
  (gsum_eq AlgEquiv.refl gauss1_refl (compEquiv (F := F) hd hv) (compEquiv_he hd hv)).symm

lemma comp_ic : ic C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F) =
    ic C (Aff (0 : C) v hv (Aff a d hd F)) :=
  ic_eq AlgEquiv.refl gauss1_refl (compEquiv (F := F) hd hv) (compEquiv_he hd hv) norm_one
    (by simp) (comp_x hd hv)

lemma comp_tot0
    (hΛ : IsChart 𝓀 (fun w : Ext C (Aff (0 : C) v hv (Aff a d hd F)) ↦
      red C (xF C (Aff (0 : C) v hv (Aff a d hd F))) w)
      (redRing C _ (xF C (Aff (0 : C) v hv (Aff a d hd F)))))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F) ↦
      red C (xF C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F)) w)
      (redRing C _ (xF C (Aff (a + d * 0) (d * v) (mul_ne_zero hd hv) F)))) :
    tot0 C _ hΛ₂ (fun _ ↦ True) = tot0 C _ hΛ (fun _ ↦ True) :=
  tot0_true_eq AlgEquiv.refl gauss1_refl (compEquiv (F := F) hd hv) (compEquiv_he hd hv) norm_one
    (comp_x hd hv) hΛ hΛ₂

end Comp

/-! ### Exhaustion does not depend on the representative -/

section Transfer

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

set_option maxHeartbeats 1000000 in
-- two local formulas and three changes of coordinates
include hp hp1 in
/-- **Exhaustion does not depend on the representative** of the disc and of the open ball: the
local formula expresses the total `δ` over the node through invariants of the open ball and of
the disc. -/
theorem isExhausting_transfer {a a' c c' v v' : C} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hv1 : ‖v‖ < 1) (hv0 : v ≠ 0) (hv1' : ‖v'‖ < 1) (hv0' : v' ≠ 0)
    (h1 : ‖c‖ = ‖c'‖) (h2 : ‖a - a'‖ < ‖c‖) (h3 : ‖c * v‖ = ‖c' * v'‖)
    (h4 : ‖a - a'‖ ≤ ‖c * v‖) (hex : IsExhausting a hc hv1 hv0 F) :
    IsExhausting a' hc' hv1' hv0' F := by
  classical
  set K := Aff a c hc F
  set K' := Aff a' c' hc' F
  set G := Aff (0 : C) v hv0 K
  set G' := Aff (0 : C) v' hv0' K'
  set G₂ := Aff (a + c * 0) (c * v) (mul_ne_zero hc hv0) F
  set G₂' := Aff (a' + c' * 0) (c' * v') (mul_ne_zero hc' hv0') F
  haveI : Finite (Ext C K) := finite_ext (F := K) hp hp1
  letI : Fintype (Ext C K) := Fintype.ofFinite _
  haveI : Finite (Ext C K') := finite_ext (F := K') hp hp1
  letI : Fintype (Ext C K') := Fintype.ofFinite _
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  haveI : Finite (Ext C G') := finite_ext (F := G') hp hp1
  letI : Fintype (Ext C G') := Fintype.ofFinite _
  haveI : Finite (Ext C G₂) := finite_ext (F := G₂) hp hp1
  letI : Fintype (Ext C G₂) := Fintype.ofFinite _
  haveI : Finite (Ext C G₂') := finite_ext (F := G₂') hp hp1
  letI : Fintype (Ext C G₂') := Fintype.ofFinite _
  haveI : Finite (Ext C (TwoV v K)) := finite_ext (F := TwoV v K) hp hp1
  letI : Fintype (Ext C (TwoV v K)) := Fintype.ofFinite _
  haveI : Finite (Ext C (TwoV v' K')) := finite_ext (F := TwoV v' K') hp hp1
  letI : Fintype (Ext C (TwoV v' K')) := Fintype.ofFinite _
  haveI : Finite (Ext C (GaussTube.Inv v hv0 K)) := finite_ext (F := GaussTube.Inv v hv0 K) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv v hv0 K)) := Fintype.ofFinite _
  haveI : Finite (Ext C (GaussTube.Inv v' hv0' K')) :=
    finite_ext (F := GaussTube.Inv v' hv0' K') hp hp1
  letI : Fintype (Ext C (GaussTube.Inv v' hv0' K')) := Fintype.ofFinite _
  have hΛK := chart₀ hp hp1 K
  have hΛK' := chart₀ hp hp1 K'
  have hΛG := chart₀ hp hp1 G
  have hΛG' := chart₀ hp hp1 G'
  have hΛG₂ := chart₀ hp hp1 G₂
  have hΛG₂' := chart₀ hp hp1 G₂'
  have hΛT := chart₀ hp hp1 (TwoV v K)
  have hΛT' := chart₀ hp hp1 (TwoV v' K')
  have LF := local_formula (hp := hp) (hp1 := hp1) (hc0 := hv0) (hc1 := hv1) hΛK
    (chartI hp hp1 K) hΛT (chartI hp hp1 (TwoV v K)) hΛG
  have LF' := local_formula (hp := hp) (hp1 := hp1) (hc0 := hv0') (hc1 := hv1') hΛK'
    (chartI hp hp1 K') hΛT' (chartI hp hp1 (TwoV v' K')) hΛG'
  change (tot0 C K hΛK (fun 𝔫 ↦ DiscBridge.xbar hΛK ∈ 𝔫) : ℤ) + _ =
    (tot0 C (TwoV v K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) : ℤ) + _ + _ at LF
  change (tot0 C K' hΛK' (fun 𝔫 ↦ DiscBridge.xbar hΛK' ∈ 𝔫) : ℤ) + _ =
    (tot0 C (TwoV v' K') hΛT' (fun 𝔫 ↦ tbar hΛT' ∈ 𝔫) : ℤ) + _ + _ at LF'
  obtain ⟨hNi, hNm⟩ := exh_counts hp hp1 hv0 hv1 hΛT hex
  -- the open ball
  have hdl := tot0_xbar_aff hc hc' h1 h2 hΛK hΛK'
  have hmm : mm C K' = mm C K := mm_aff hc hc' h1 h2
  -- the disc
  have h2' : ‖(a + c * 0) - (a' + c' * 0)‖ ≤ ‖c * v‖ := by simpa using h4
  have hcard : Fintype.card (Ext C G') = Fintype.card (Ext C G) := by
    rw [← comp_card hc' hv0', card_ext_aff _ _ h3 h2', comp_card hc hv0]
  have hgsum : gsum C G' = gsum C G := by
    rw [← comp_gsum hc' hv0', gsum_aff _ _ h3 h2', comp_gsum hc hv0]
  have hic : ic C G' = ic C G := by
    rw [← comp_ic hc' hv0', ic_aff _ _ h3 h2', comp_ic hc hv0]
  have htot : tot0 C G' hΛG' (fun _ ↦ True) = tot0 C G hΛG (fun _ ↦ True) := by
    rw [← comp_tot0 hc' hv0' hΛG' hΛG₂', tot0_true_aff _ _ h3 h2' hΛG₂ hΛG₂',
      comp_tot0 hc hv0 hΛG hΛG₂]
  -- the total `δ` over the node
  have hN : tot0 C (TwoV v' K') hΛT' (fun 𝔫 ↦ tbar hΛT' ∈ 𝔫) =
      tot0 C (TwoV v K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) := by
    rw [hdl, hcard, hgsum, htot] at LF'
    have : (tot0 C (TwoV v' K') hΛT' (fun 𝔫 ↦ tbar hΛT' ∈ 𝔫) : ℤ) =
        tot0 C (TwoV v K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) := by linarith
    exact_mod_cast this
  exact nodeGood_of_counts hp hp1 hv0' hv1' hΛT' (n := mm C K') (by rw [hN, hNm, hmm]) rfl
    (by rw [hic, ← hNi, hNm, hmm])

end Transfer

/-! ### Points of the chart over two residue classes -/

section Classes

lemma finsum_mem_le_of_subset {α : Type*} {f : α → ℕ} {s t : Set α} (h : s ⊆ t)
    (ht : (t ∩ Function.support f).Finite) : ∑ᶠ i ∈ s, f i ≤ ∑ᶠ i ∈ t, f i := by
  rw [← Set.union_sdiff_cancel h, finsum_mem_union' Set.disjoint_sdiff_right
    ((ht.subset (Set.inter_subset_inter_left _ h))) (ht.subset (Set.inter_subset_inter_left _
      Set.sdiff_subset))]
  exact Nat.le_add_right _ _

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {K : Type*} [Field K] [Algebra (RatFunc C) K] [Algebra C K]
  [IsScalarTower C (RatFunc C) K] [FiniteDimensional (RatFunc C) K] [Fintype (Ext C K)]
  (hΛ : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
    (fun w : Ext C K ↦ red C (xF C K) w) (redRing C K (xF C K)))

include hp hp1 in
/-- The total `δ` over two disjoint sets of points is at most the total `δ` of the chart. -/
lemma tot0_add_le {P Q : Ideal (redRing C K (xF C K)) → Prop}
    (hPQ : ∀ 𝔫, 𝔫.IsMaximal → P 𝔫 → Q 𝔫 → False) :
    tot0 C K hΛ P + tot0 C K hΛ Q ≤ tot0 C K hΛ (fun _ ↦ True) := by
  have hfin := finite_dinf₀ hp hp1 hΛ
  have hsub : ∀ R : Ideal (redRing C K (xF C K)) → Prop,
      ({𝔫 | 𝔫.IsMaximal ∧ R 𝔫} ∩ Function.support
        (dinf 𝓀 (fun w : Ext C K ↦ IsLocalRing.ResidueField w.1.valuationSubring) hΛ)).Finite :=
    fun R ↦ hfin.subset fun 𝔫 h ↦ ⟨h.1.1, h.2⟩
  rw [tot0, tot0, tot0, ← finsum_mem_union' (Set.disjoint_left.2 fun 𝔫 h₁ h₂ ↦
    hPQ 𝔫 h₁.1 h₁.2 h₂.2) (hsub P) (hsub Q)]
  exact finsum_mem_le_of_subset (fun 𝔫 h ↦ h.elim (fun h ↦ ⟨h.1, trivial⟩)
    (fun h ↦ ⟨h.1, trivial⟩)) (hsub _)

include hp hp1 in
lemma tot0_le_true (P : Ideal (redRing C K (xF C K)) → Prop) :
    tot0 C K hΛ P ≤ tot0 C K hΛ (fun _ ↦ True) :=
  (Nat.le_add_right _ _).trans (tot0_add_le hp hp1 hΛ (Q := fun _ ↦ False) fun _ _ _ h ↦ h)

omit [CharZero C] [IsAlgClosed C] in
/-- `x̄` and `u x̄ + β̄` (`|u| = |β| = 1`) lie in no common point of the chart. -/
lemma not_mem_both {u β : C} (hu : ‖u‖ = 1) (hβ : ‖β‖ = 1) {𝔫 : Ideal (redRing C K (xF C K))}
    (h𝔫 : 𝔫.IsMaximal) (hx : DiscBridge.xbar hΛ ∈ 𝔫)
    (hl : (⟨fun w ↦ red C (algebraMap C K u * xF C K + algebraMap C K β) w,
      red_mem_redRing (lin_mem_intRing hu hβ.le)⟩ : redRing C K (xF C K)) ∈ 𝔫) : False := by
  set U : redRing C K (xF C K) :=
    ⟨fun w ↦ red C (algebraMap C K u) w, red_mem_redRing (algebraMap_mem_intRing hu.le)⟩
  set B : redRing C K (xF C K) :=
    ⟨fun w ↦ red C (algebraMap C K β) w, red_mem_redRing (algebraMap_mem_intRing hβ.le)⟩
  have hβi : ‖β⁻¹‖ ≤ 1 := by rw [norm_inv, hβ, inv_one]
  set B' : redRing C K (xF C K) :=
    ⟨fun w ↦ red C (algebraMap C K β⁻¹) w, red_mem_redRing (algebraMap_mem_intRing hβi)⟩
  have hβ0 : β ≠ 0 := by rintro rfl; simp at hβ
  have hBB : B * B' = 1 := by
    apply Subtype.ext
    funext w
    change red C (algebraMap C K β) w * red C (algebraMap C K β⁻¹) w = 1
    rw [← red_mul (by rw [valuation_algebraMap_C']; exact nnnorm_le_one_of_eq hβ)
      (by rw [valuation_algebraMap_C']; exact_mod_cast hβi), ← map_mul, mul_inv_cancel₀ hβ0,
      map_one, red_one]
  have e : (⟨fun w ↦ red C (algebraMap C K u * xF C K + algebraMap C K β) w,
      red_mem_redRing (lin_mem_intRing hu hβ.le)⟩ : redRing C K (xF C K)) =
        U * DiscBridge.xbar hΛ + B := by
    apply Subtype.ext
    funext w
    change red C (algebraMap C K u * xF C K + algebraMap C K β) w =
      red C (algebraMap C K u) w * red C (xF C K) w + red C (algebraMap C K β) w
    have h1 : w.1 (algebraMap C K u) ≤ 1 := by
      rw [valuation_algebraMap_C']; exact nnnorm_le_one_of_eq hu
    have h2 : w.1 (algebraMap C K u * xF C K) ≤ 1 := by
      rw [map_mul, valuation_xF, mul_one]; exact h1
    have h3 : w.1 (algebraMap C K β) ≤ 1 := by
      rw [valuation_algebraMap_C']; exact nnnorm_le_one_of_eq hβ
    rw [red_add h2 h3, red_mul h1 (valuation_xF w).le]
  rw [e] at hl
  have hB : B ∈ 𝔫 := by
    have := 𝔫.sub_mem hl (𝔫.mul_mem_left U hx)
    rwa [add_sub_cancel_left] at this
  exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ hB (IsUnit.of_mul_eq_one _ hBB))

end Classes

/-! ### The improvement step -/

section Core

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

set_option maxHeartbeats 2000000 in
-- the local formula and several changes of coordinates
include hp hp1 in
/-- **The improvement step** ([AW Lemma 2.6]): let `D = D(a, |c u|)` be exhausting in
`U = D(a, |c|)⁻`. If the measure `(δ, -m)` of the residue class `D(a, |c u|)⁻` of `D` is not
smaller than that of `U`, then a smaller disc `D(a, |c u e|)` is exhausting in `U`. -/
theorem exists_smaller (hgl : ExhaustGlueFor C F) {a c u : C} (hc : c ≠ 0) (hu1 : ‖u‖ < 1)
    (hu0 : u ≠ 0) (hex : IsExhausting a hc hu1 hu0 F)
    [Fintype (Ext C (Aff a c hc F))]
    [Fintype (Ext C (Aff (a + c * 0) (c * u) (mul_ne_zero hc hu0) F))]
    (hΛB : IsChart 𝓀 (fun w : Ext C (Aff a c hc F) ↦ red C (xF C (Aff a c hc F)) w)
      (redRing C _ (xF C (Aff a c hc F))))
    (hΛB' : IsChart 𝓀 (fun w : Ext C (Aff (a + c * 0) (c * u) (mul_ne_zero hc hu0) F) ↦
      red C (xF C (Aff (a + c * 0) (c * u) (mul_ne_zero hc hu0) F)) w)
      (redRing C _ (xF C (Aff (a + c * 0) (c * u) (mul_ne_zero hc hu0) F))))
    (hge : (Module.finrank (RatFunc C) F + 1) * tot0 C _ hΛB (fun 𝔫 ↦ DiscBridge.xbar hΛB ∈ 𝔫) +
        (Module.finrank (RatFunc C) F - mm C (Aff a c hc F)) ≤
      (Module.finrank (RatFunc C) F + 1) * tot0 C _ hΛB' (fun 𝔫 ↦ DiscBridge.xbar hΛB' ∈ 𝔫) +
        (Module.finrank (RatFunc C) F - mm C (Aff (a + c * 0) (c * u) (mul_ne_zero hc hu0) F))) :
    ∃ (e : C) (he0 : e ≠ 0) (he1 : ‖e‖ < 1),
      IsExhausting a hc (norm_mul_lt_one hu1 he1) (mul_ne_zero hu0 he0) F := by
  classical
  set N := Module.finrank (RatFunc C) F
  set K := Aff a c hc F
  set G := Aff (0 : C) u hu0 K
  set K₁ := Aff (a + c * 0) (c * u) (mul_ne_zero hc hu0) F
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  haveI : Finite (Ext C (TwoV u K)) := finite_ext (F := TwoV u K) hp hp1
  letI : Fintype (Ext C (TwoV u K)) := Fintype.ofFinite _
  haveI : Finite (Ext C (GaussTube.Inv u hu0 K)) := finite_ext (F := GaussTube.Inv u hu0 K) hp hp1
  letI : Fintype (Ext C (GaussTube.Inv u hu0 K)) := Fintype.ofFinite _
  have hΛG := chart₀ hp hp1 G
  have hΛT := chart₀ hp hp1 (TwoV u K)
  have LF := local_formula (hp := hp) (hp1 := hp1) (hc0 := hu0) (hc1 := hu1) hΛB
    (chartI hp hp1 K) hΛT (chartI hp hp1 (TwoV u K)) hΛG
  change (tot0 C K hΛB (fun 𝔫 ↦ DiscBridge.xbar hΛB ∈ 𝔫) : ℤ) + _ =
    (tot0 C (TwoV u K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫) : ℤ) + _ + _ at LF
  obtain ⟨hNi, hNm⟩ := exh_counts hp hp1 hu0 hu1 hΛT hex
  have hcard := comp_card (F := F) (a := a) hc hu0
  have hgsum := comp_gsum (F := F) (a := a) hc hu0
  have hic := comp_ic (F := F) (a := a) hc hu0
  have hΔ := comp_tot0 (F := F) (a := a) hc hu0 hΛG hΛB'
  have hmK : mm C K ≤ N := (mm_le_finrank hp hp1).trans (finrank_aff hc).le
  have hmK₁ : mm C K₁ ≤ N := (mm_le_finrank hp hp1).trans (finrank_aff _).le
  have hicG : Fintype.card (Ext C G) ≤ ic C G := card_le_ic
  have hmm₁ : Fintype.card (Ext C K₁) ≤ mm C K₁ := card_le_mm
  have hδΔ := tot0_le_true hp hp1 hΛB' (fun 𝔫 ↦ DiscBridge.xbar hΛB' ∈ 𝔫)
  have hg : 0 ≤ gsum C G := Finset.sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
  -- the arithmetic of `(δ, -m)`
  set δ := tot0 C K hΛB (fun 𝔫 ↦ DiscBridge.xbar hΛB ∈ 𝔫) with hδ
  set δ' := tot0 C K₁ hΛB' (fun 𝔫 ↦ DiscBridge.xbar hΛB' ∈ 𝔫) with hδ'
  set Δ := tot0 C K₁ hΛB' (fun _ ↦ True) with hΔdef
  set NT := tot0 C (TwoV u K) hΛT (fun 𝔫 ↦ tbar hΛT ∈ 𝔫)
  have hLF : (δ : ℤ) + Fintype.card (Ext C G) = NT + tot0 C G hΛG (fun _ ↦ True) + gsum C G :=
    LF
  have zNi : (NT : ℤ) = ic C G := by exact_mod_cast hNi
  have zNm : (NT : ℤ) = mm C K := by exact_mod_cast hNm
  have zcard : (Fintype.card (Ext C K₁) : ℤ) = Fintype.card (Ext C G) := by exact_mod_cast hcard
  have zic : (ic C K₁ : ℤ) = ic C G := by exact_mod_cast hic
  have zΔ : (Δ : ℤ) = tot0 C G hΛG (fun _ ↦ True) := by exact_mod_cast hΔ
  have zicG : (Fintype.card (Ext C G) : ℤ) ≤ ic C G := by exact_mod_cast hicG
  have zδΔ : (δ' : ℤ) ≤ Δ := by exact_mod_cast hδΔ
  have hle : δ' ≤ δ := by
    have : (δ' : ℤ) ≤ δ := by linarith
    exact_mod_cast this
  have heq : δ' = δ := by
    refine le_antisymm hle (not_lt.1 fun hlt ↦ ?_)
    have h1 : (N + 1) * (δ' + 1) ≤ (N + 1) * δ := Nat.mul_le_mul_left _ hlt
    rw [mul_add, mul_one] at h1
    generalize (N + 1) * δ = X at hge h1
    generalize (N + 1) * δ' = Y at hge h1
    omega
  have hge' : (N + 1) * δ + (N - mm C K) ≤ (N + 1) * δ + (N - mm C K₁) := heq ▸ hge
  have hm₁ : mm C K₁ ≤ mm C K := by omega
  have zeq : (δ' : ℤ) = δ := by exact_mod_cast heq
  have zΔδ : (Δ : ℤ) = δ := by linarith
  have hΔδ : Δ = δ := by exact_mod_cast zΔδ
  have zmn : (mm C K : ℤ) = Fintype.card (Ext C K₁) := by linarith
  have hmn : mm C K = Fintype.card (Ext C K₁) := by exact_mod_cast zmn
  have hicn : ic C G = Fintype.card (Ext C G) := by
    have : (ic C G : ℤ) = Fintype.card (Ext C G) := by linarith
    exact_mod_cast this
  have hg0 : gsum C G = 0 := by linarith
  -- the residue curves of `D`
  have hz1 : ∀ w : Ext C K₁, (PlaceNorm.zeros 𝓀 (red C (xF C K₁) w)).card = 1 :=
    card_zeros_eq_one_of_mm (hm₁.trans hmn.le)
  have hzi : ∀ w : Ext C G, (PlaceNorm.zeros 𝓀 (red C (xF C G) w)⁻¹).card = 1 :=
    card_zeros_inv_eq_one_of_ic hicn.le
  have hgen : ∀ w : Ext C G, genus 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring) = 0 := by
    intro w
    have h := (Finset.sum_eq_zero_iff_of_nonneg (fun w _ ↦ Int.natCast_nonneg _)).1
      hg0 w (Finset.mem_univ _)
    exact_mod_cast h
  have htube : IsTubeDisc F (a + c * 0) (mul_ne_zero hc hu0) := by
    intro w₁
    obtain ⟨w, rfl⟩ := (extEquiv AlgEquiv.refl gauss1_refl (compEquiv (F := F) (a := 0) (b := a)
      hc hu0) (compEquiv_he hc hu0)).surjective w₁
    rw [genus_ext, card_zeros_inv_x _ _ _ _ norm_one (by simp) (comp_x hc hu0)]
    exact ⟨hgen w, hzi w⟩
  have hcirc : IsTubeCircle F a (mul_ne_zero hc hu0) := by
    intro b' hb'
    have h2 : ‖a + c * 0 - b'‖ < ‖c * u‖ := by simpa using hb'
    refine ⟨isTubeDisc_aff _ _ rfl h2.le htube, fun w' ↦ ?_⟩
    obtain ⟨w, rfl⟩ := (extEquiv (repσ (a + c * 0) b' (mul_ne_zero hc hu0) (mul_ne_zero hc hu0))
      (repσ_gauss _ _ rfl h2.le) (repφ (F := F) (a + c * 0) b' (mul_ne_zero hc hu0)
        (mul_ne_zero hc hu0)) (repφ_he _ _)).surjective w'
    haveI : Finite (Ext C (Aff b' (c * u) (mul_ne_zero hc hu0) F)) :=
      finite_ext (F := Aff b' (c * u) (mul_ne_zero hc hu0) F) hp hp1
    letI : Fintype (Ext C (Aff b' (c * u) (mul_ne_zero hc hu0) F)) := Fintype.ofFinite _
    rw [card_zeros_aff _ _ rfl h2 w]
    exact hz1 w
  -- the other residue classes of `D` are good
  have hoff : ∀ β : C, ‖β‖ = 1 → DiscSmooth F (a + c * u * β) (mul_ne_zero hc hu0) := by
    intro β hβ
    set K₃ := Aff (a + c * u * β) (c * u) (mul_ne_zero hc hu0) F
    haveI : Finite (Ext C K₃) := finite_ext (F := K₃) hp hp1
    letI : Fintype (Ext C K₃) := Fintype.ofFinite _
    have hΛK₃ := chart₀ hp hp1 K₃
    have hcu : ‖c * u‖ ≠ 0 := norm_ne_zero_iff.2 (mul_ne_zero hc hu0)
    have hβ₀ : ‖(a + c * 0 - (a + c * u * β)) / (c * u)‖ = 1 := by
      rw [show a + c * 0 - (a + c * u * β) = -(c * u * β) by ring, norm_div, norm_neg,
        norm_mul (c * u), hβ, mul_one, div_self hcu]
    have h2 : ‖a + c * 0 - (a + c * u * β)‖ ≤ ‖c * u‖ := by
      rw [show a + c * 0 - (a + c * u * β) = -(c * u * β) by ring, norm_neg, norm_mul (c * u),
        hβ, mul_one]
    have hu₀ := norm_u_eq (c := c * u) (mul_ne_zero hc hu0) rfl
    have hx := tot0_x_eq (repσ (a + c * 0) (a + c * u * β) (mul_ne_zero hc hu0)
      (mul_ne_zero hc hu0)) (repσ_gauss _ _ rfl h2) (repφ (F := F) (a + c * 0) (a + c * u * β)
        (mul_ne_zero hc hu0) (mul_ne_zero hc hu0)) (repφ_he _ _) hu₀ (repφ_x _ _) hΛB' hΛK₃
      (lin_mem_intRing hu₀ hβ₀.le)
    have hadd := tot0_add_le hp hp1 hΛB' (P := fun 𝔫 ↦ DiscBridge.xbar hΛB' ∈ 𝔫)
      (fun 𝔫 h𝔫 h₁ h₂ ↦ not_mem_both hΛB' hu₀ hβ₀ h𝔫 h₁ h₂)
    have h0 : tot0 C K₃ hΛK₃ (fun 𝔫 ↦ DiscBridge.xbar hΛK₃ ∈ 𝔫) = 0 := by
      change tot0 C K₃ hΛK₃ (fun 𝔫 ↦ (⟨fun w' ↦ red C (xF C K₃) w', hΛK₃.mem⟩ :
        redRing C K₃ (xF C K₃)) ∈ 𝔫) = 0
      rw [hx]
      rw [← hδ', ← hΔdef, hΔδ, ← heq] at hadd
      omega
    exact (DiscBridge.tot0_eq_zero_iff hp hp1 hΛK₃).1 h0
  -- a smaller exhausting disc
  obtain ⟨e, he0, he1, hgerm⟩ := GaussTube.belowGerm hp hp1 (F' := F) a (c * u)
    (mul_ne_zero hc hu0)
  exact ⟨e, he0, he1, hgl a c u e hc hu1 hu0 he1 he0 hex (hgerm e he1 he0 le_rfl) hcirc hoff⟩

end Core

/-! ### The measure -/

section Measure

open BallTree

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Exhaustion in one representative gives a good edge.** -/
theorem edgeGood_of_isExhausting {a c v : C} (hc : c ≠ 0) (hv1 : ‖v‖ < 1) (hv0 : v ≠ 0)
    (hex : IsExhausting a hc hv1 hv0 F) :
    S8A.EdgeGood F (closedBall a ‖c * v‖) (closedBall a ‖c‖) := by
  intro a₀ c₀ c₀' hc₀ hc₀' hc0₀' hD hG
  obtain ⟨h3, h4⟩ :=
    (closedBall_eq_closedBall_iff' (mul_ne_zero hc hv0) (mul_ne_zero hc₀ hc0₀')).1 hD
  obtain ⟨h1, -⟩ := (closedBall_eq_closedBall_iff' hc hc₀).1 hG
  have hcv : ‖c * v‖ < ‖c‖ := by
    rw [norm_mul]; exact mul_lt_of_lt_one_right (norm_pos_iff.2 hc) hv1
  exact isExhausting_transfer hp hp1 hc hc₀ hv1 hv0 hc₀' hc0₀' h1 (h4.trans_lt hcv) h3 h4 hex

variable (F) in
/-- The total `δ` over the open ball `D(a, |c|)⁻`. -/
noncomputable def dl (a c : C) (hc : c ≠ 0) : ℕ :=
  haveI : Finite (Ext C (Aff a c hc F)) := finite_ext (F := Aff a c hc F) hp hp1
  letI : Fintype (Ext C (Aff a c hc F)) := Fintype.ofFinite _
  tot0 C (Aff a c hc F) (chart₀ hp hp1 _) (fun 𝔫 ↦ DiscBridge.xbar (chart₀ hp hp1 _) ∈ 𝔫)

variable (F) in
/-- The number of branches over the open ball `D(a, |c|)⁻`. -/
noncomputable def mb (a c : C) (hc : c ≠ 0) : ℕ :=
  haveI : Finite (Ext C (Aff a c hc F)) := finite_ext (F := Aff a c hc F) hp hp1
  letI : Fintype (Ext C (Aff a c hc F)) := Fintype.ofFinite _
  mm C (Aff a c hc F)

open Classical in
variable (F) in
/-- The measure `(δ, -m)` of the open ball `D(a, |c|)⁻`, encoded in `ℕ` (`m ≤ [F : C(x)]`). -/
noncomputable def μ₀ (a c : C) : ℕ :=
  if hc : c ≠ 0 then (Module.finrank (RatFunc C) F + 1) * dl F hp hp1 a c hc +
    (Module.finrank (RatFunc C) F - mb F hp hp1 a c hc) else 0

open Classical in
variable (F) in
/-- The measure on open balls. -/
noncomputable def μ (S : Set C) : ℕ :=
  if h : ∃ q : C × C, q.2 ≠ 0 ∧ S = ball q.1 ‖q.2‖ then μ₀ F hp hp1 h.choose.1 h.choose.2 else 0

lemma μ₀_congr {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) (h : ball a ‖c‖ = ball a' ‖c'‖) :
    μ₀ F hp hp1 a c = μ₀ F hp hp1 a' c' := by
  obtain ⟨h1, h2⟩ := (ball_eq_ball_iff' hc hc').1 h
  haveI : Finite (Ext C (Aff a c hc F)) := finite_ext (F := Aff a c hc F) hp hp1
  letI : Fintype (Ext C (Aff a c hc F)) := Fintype.ofFinite _
  haveI : Finite (Ext C (Aff a' c' hc' F)) := finite_ext (F := Aff a' c' hc' F) hp hp1
  letI : Fintype (Ext C (Aff a' c' hc' F)) := Fintype.ofFinite _
  have hdl : dl F hp hp1 a' c' hc' = dl F hp hp1 a c hc :=
    tot0_xbar_aff hc hc' h1 h2 (chart₀ hp hp1 _) (chart₀ hp hp1 _)
  have hmb : mb F hp hp1 a' c' hc' = mb F hp hp1 a c hc := mm_aff hc hc' h1 h2
  rw [μ₀, μ₀, dif_pos hc, dif_pos hc', hdl, hmb]

lemma μ_ball {a c : C} (hc : c ≠ 0) : μ F hp hp1 (ball a ‖c‖) = μ₀ F hp hp1 a c := by
  have h : ∃ q : C × C, q.2 ≠ 0 ∧ ball a ‖c‖ = ball q.1 ‖q.2‖ := ⟨(a, c), hc, rfl⟩
  rw [μ, dif_pos h]
  exact (μ₀_congr hp hp1 hc h.choose_spec.1 h.choose_spec.2).symm

include hp hp1 in
/-- **R5** ([AW Lemma 2.6, §2.5]): the measure `(δ, -m)` decreases from a residue ball to every
residue ball of its smallest exhausting disc, given the gluing step `ExhaustGlueFor`. -/
theorem r5MeasureFor_of (hgl : ExhaustGlueFor C F) : S8A.R5MeasureFor C F := by
  classical
  refine ⟨μ F hp hp1, fun b c hc D _ hmin B' hB' _ ↦ ?_⟩
  obtain ⟨-, hDsub, hDedge, hDmin⟩ := hmin
  obtain ⟨a₁, b₁, c₁, hc₁, rfl, hb₁, rfl⟩ := hB'
  have hc₁0 : 0 < ‖c₁‖ := norm_pos_iff.2 hc₁
  have hD : closedBall a₁ ‖c₁‖ = closedBall b₁ ‖c₁‖ :=
    (closedBall_eq_closedBall_iff' hc₁ hc₁).2 ⟨rfl, by
      rw [norm_sub_rev]; exact BallTree.mem_closedBall'.1 hb₁⟩
  rw [hD] at hDsub hDedge hDmin
  have hb₁B : ‖b₁ - b‖ < ‖c‖ := BallTree.mem_ball'.1 (hDsub (mem_closedBall_self hc₁0.le))
  have hc₁c : ‖c₁‖ < ‖c‖ := by
    have h := BallTree.mem_ball'.1 (hDsub (show b₁ + c₁ ∈ closedBall b₁ ‖c₁‖ from
      BallTree.mem_closedBall'.2 (by simp)))
    calc ‖c₁‖ = ‖(b₁ + c₁ - b) + (b - b₁)‖ := by ring_nf
      _ ≤ max ‖b₁ + c₁ - b‖ ‖b - b₁‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < ‖c‖ := max_lt h (by rw [norm_sub_rev]; exact hb₁B)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  set u := c₁ / c with hu
  have hu0 : u ≠ 0 := div_ne_zero hc₁ hc
  have hu1 : ‖u‖ < 1 := by rw [hu, norm_div, div_lt_one hcpos]; exact hc₁c
  have hcu : c * u = c₁ := by rw [hu]; field_simp
  have hball : ball b ‖c‖ = ball b₁ ‖c‖ :=
    (ball_eq_ball_iff' hc hc).2 ⟨rfl, by rw [norm_sub_rev]; exact hb₁B⟩
  have hcl : closedBall b ‖c‖ = closedBall b₁ ‖c‖ :=
    (closedBall_eq_closedBall_iff' hc hc).2 ⟨rfl, by rw [norm_sub_rev]; exact hb₁B.le⟩
  have hex : IsExhausting b₁ hc hu1 hu0 F := hDedge b₁ c u hc hu1 hu0 (by rw [hcu]) hcl
  rw [hball, μ_ball hp hp1 hc, show ball b₁ ‖c₁‖ = ball (b₁ + c * 0) ‖c * u‖ by
    rw [hcu, mul_zero, add_zero], μ_ball hp hp1 (mul_ne_zero hc hu0)]
  by_contra hlt
  push Not at hlt
  rw [μ₀, μ₀, dif_pos hc, dif_pos (mul_ne_zero hc hu0)] at hlt
  haveI : Finite (Ext C (Aff b₁ c hc F)) := finite_ext (F := Aff b₁ c hc F) hp hp1
  letI : Fintype (Ext C (Aff b₁ c hc F)) := Fintype.ofFinite _
  haveI : Finite (Ext C (Aff (b₁ + c * 0) (c * u) (mul_ne_zero hc hu0) F)) :=
    finite_ext (F := Aff (b₁ + c * 0) (c * u) (mul_ne_zero hc hu0) F) hp hp1
  letI : Fintype (Ext C (Aff (b₁ + c * 0) (c * u) (mul_ne_zero hc hu0) F)) := Fintype.ofFinite _
  obtain ⟨e, he0, he1, hexe⟩ := exists_smaller hp hp1 hgl hc hu1 hu0 hex (chart₀ hp hp1 _)
    (chart₀ hp hp1 _) hlt
  have hedge := edgeGood_of_isExhausting hp hp1 hc (norm_mul_lt_one hu1 he1)
    (mul_ne_zero hu0 he0) hexe
  rw [← hcl] at hedge
  have hsub : closedBall b₁ ‖c * (u * e)‖ ⊆ ball b ‖c‖ := by
    refine (closedBall_subset_closedBall ?_).trans hDsub
    rw [← hcu, norm_mul, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (norm_nonneg _) he1.le)
      (norm_nonneg _)
  have h := hDmin _ ⟨b₁, c * (u * e), mul_ne_zero hc (mul_ne_zero hu0 he0), rfl⟩ hsub hedge
  have hmem := h (show b₁ + c₁ ∈ closedBall b₁ ‖c₁‖ from BallTree.mem_closedBall'.2 (by simp))
  rw [BallTree.mem_closedBall', add_sub_cancel_left, ← mul_assoc, hcu, norm_mul] at hmem
  have : ‖c₁‖ * ‖e‖ < ‖c₁‖ := mul_lt_of_lt_one_right hc₁0 he1
  linarith

end Measure

end R5Measure

namespace S8A

/-- **R5** (O6.2): `S8A.R5MeasureFor` from the gluing step `ExhaustGlueFor`
(`R5Measure.r5MeasureFor_of`). -/
theorem r5MeasureFor_of {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
    [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
    (hGl : ExhaustGluing.ExhaustGlueFor C F) : R5MeasureFor C F :=
  R5Measure.r5MeasureFor_of hp hp1 hGl

end S8A

end SemistableReduction
