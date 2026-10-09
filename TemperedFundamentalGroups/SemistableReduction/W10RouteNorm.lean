/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteCenter
import TemperedFundamentalGroups.SemistableReduction.GaussTreeFinite
import TemperedFundamentalGroups.SemistableReduction.GaussTreeSemistable

/-!
# Routing points of the normalized tree model (G4, part 4)

Blueprint §9.7a, step 4 (G4 (ii)). Let `M'` be the normalization in `F' / K(X)` of the tree model
`gaussJoinModel v a c` over a valuation ring of rank one.

* `Routed.isStandardChart`: routed charts are standard charts;
* `normChart_closure_of_isStandardChart`: the normalization of a standard chart is of finite type
  (over a noetherian `O`, `F'/K(X)` finite separable);
* `exists_routed_normChart`: for a chart `B` of `M'` and a valuation subring `W ⊇ B` of `F'` on the
  special fibre, the local ring of `B` at the center of `W` is that of the normalization of a
  routed standard chart contained in `W`.
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel GaussTree

namespace W10Route

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {ι : Type*} {a c : ι → K}

lemma Routed.isStandardChart {W : ValuationSubring (RatFunc K)} {B : Subring (RatFunc K)}
    (h : Routed v a c (RatFunc.X : RatFunc K) W B) :
    IsStandardChart v a c (RatFunc.X : RatFunc K) B := by
  rcases h with ⟨m, rfl, -⟩ | ⟨j, m, hjm, hjne, -, rfl, -⟩ | ⟨ρ, -, rfl, -⟩
  · exact .inl ⟨m, rfl⟩
  · exact .inr (.inr ⟨j, m, hjm, hjne, rfl⟩)
  · exact .inr (.inl ⟨ρ, rfl⟩)

/-- **The normalization of a chart of finite type, with fraction field `K(X)` and integrally closed,
is of finite type** (over a noetherian `O`, in a finite separable `F' / K(X)`). -/
theorem normChart_closure [IsNoetherianRing v.valuationSubring]
    {F' : Type u} [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F']
    [Algebra.IsSeparable (RatFunc K) F']
    {C : Subring (RatFunc K)} (sC : Finset (RatFunc K))
    (hsC : C = Subring.closure ((baseRing (RatFunc K) v.valuationSubring : Set (RatFunc K)) ∪ sC))
    [IsFractionRing C (RatFunc K)] [IsIntegrallyClosed C] :
    ∃ s : Finset F', normChart F' C =
      Subring.closure ((baseRing F' v.valuationSubring : Set F') ∪ s) := by
  classical
  haveI := isNoetherianRing_of_closure sC hsC
  letI : Algebra C F' := ((algebraMap (RatFunc K) F').comp C.subtype).toAlgebra
  haveI : IsScalarTower C (RatFunc K) F' := .of_algebraMap_eq fun _ ↦ rfl
  have hfin := IsIntegralClosure.finite C (RatFunc K) F' (integralClosure C F')
  obtain ⟨s, hs⟩ := hfin.fg_top
  have hEq := integralClosure_toSubring_eq (F' := F') C
  set R' := baseRing F' v.valuationSubring
  have hRC : baseRing (RatFunc K) v.valuationSubring ≤ C := by
    rw [hsC]; exact fun x hx ↦ Subring.subset_closure (Or.inl hx)
  refine ⟨sC.image (algebraMap (RatFunc K) F') ∪ s.image Subtype.val, le_antisymm ?_ ?_⟩
  · intro x hx
    rw [← hEq] at hx
    have hmem : (⟨x, hx⟩ : integralClosure C F') ∈ Submodule.span C (s : Set _) :=
      hs ▸ Submodule.mem_top
    set T := Subring.closure ((R' : Set F') ∪ ↑(sC.image (algebraMap (RatFunc K) F') ∪
      s.image Subtype.val))
    have hCT : ∀ y ∈ C, algebraMap (RatFunc K) F' y ∈ T := by
      intro y hy
      rw [hsC] at hy
      have : (Subring.closure ((baseRing (RatFunc K) v.valuationSubring : Set (RatFunc K)) ∪
          ↑sC)).map (algebraMap (RatFunc K) F') ≤ T := by
        rw [RingHom.map_closure, Set.image_union]
        refine Subring.closure_mono (Set.union_subset_union ?_ ?_)
        · rw [← Subring.coe_map, map_baseRing]
        · intro z hz
          simp only [Finset.coe_union, Finset.coe_image]
          exact Or.inl hz
      exact this ⟨y, hy, rfl⟩
    refine Submodule.span_induction (p := fun (y : integralClosure C F') _ ↦ (y : F') ∈ T)
      ?_ ?_ ?_ ?_ hmem
    · intro y hy
      refine Subring.subset_closure (Or.inr ?_)
      simp only [Finset.coe_union, Finset.coe_image]
      exact Or.inr ⟨y, hy, rfl⟩
    · exact T.zero_mem
    · intro y z _ _ hy hz
      exact T.add_mem hy hz
    · intro r y _ hy
      rw [Algebra.smul_def]
      exact T.mul_mem (hCT r r.2) hy
  · refine Subring.closure_le.2 (Set.union_subset ?_ ?_)
    · intro x hx
      have hx' : x ∈ (baseRing (RatFunc K) v.valuationSubring).map
          (algebraMap (RatFunc K) F') := by
        rw [map_baseRing]
        exact hx
      exact map_le_normChart C (subring_map_mono hRC _ hx')
    · intro x hx
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe] at hx
      rcases hx with ⟨y, hy, rfl⟩ | ⟨y, -, rfl⟩
      · refine map_le_normChart C ⟨y, ?_, rfl⟩
        rw [hsC]
        exact Subring.subset_closure (Or.inr hy)
      · rw [← hEq]
        exact y.2

/-- **Normalized standard charts are of finite type.** -/
theorem normChart_closure_of_isStandardChart [IsNoetherianRing v.valuationSubring]
    {F' : Type u} [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F']
    [Algebra.IsSeparable (RatFunc K) F'] (hc : ∀ i, c i ≠ 0)
    {B : Subring (RatFunc K)} (hB : IsStandardChart v a c (RatFunc.X : RatFunc K) B) :
    ∃ s : Finset F', normChart F' B =
      Subring.closure ((baseRing F' v.valuationSubring : Set F') ∪ s) := by
  obtain ⟨sB, hsB⟩ := IsStandardChart.exists_finset hB
  haveI : IsFractionRing B (RatFunc K) := by
    rcases hB with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, m, -, -, rfl⟩
    · exact (isGaussCoord_coord (hc i)).isFractionRing_of_le le_rfl
    · exact (isGaussCoord_coord (hc i)).inv.isFractionRing_of_le le_rfl
    · exact (isGaussCoord_coord (a := a j) (hc m)).isFractionRing_of_le
        (polyChart_le baseRing_le_nodeChart self_mem_nodeChart)
  haveI : IsIntegrallyClosed B := (isIntegrallyClosed_iff (RatFunc K)).2 fun {x} hx ↦
    ⟨⟨x, IsStandardChart.isIntegral_mem hc hB hx⟩, rfl⟩
  exact normChart_closure sB hsB

/-- **Routing in the normalization**: for a chart `B` of the normalized tree model and a valuation
subring `W ⊇ B` of `F'` with `W ∩ K = O`, the local ring of `B` at the center of `W` is that of
the normalization of a routed standard chart `S`, `normChart F' S ⊆ W`. -/
theorem exists_routed_normChart [Fintype ι] [Nonempty ι] (hc : ∀ i, c i ≠ 0)
    (hconv : IsConvex v a c) (hred : IsReduced v a c)
    {F' : Type u} [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] {B : Subring F'}
    (hB : B ∈ ((gaussJoinModel v a c).normalization F').charts) {W : ValuationSubring F'}
    (hBW : B ≤ W.toSubring) (hWO : W.comap (algebraMap K F') = v.valuationSubring) :
    ∃ S, Routed v a c (RatFunc.X : RatFunc K) (W.comap (algebraMap (RatFunc K) F')) S ∧
      normChart F' S ≤ W.toSubring ∧ localAt B W = localAt (normChart F' S) W := by
  obtain ⟨J, hJ, rfl⟩ := mem_normalization_charts.1 hB
  set W₀ := W.comap (algebraMap (RatFunc K) F')
  have hJW : J ≤ W₀.toSubring := (normChart_le_iff _ _).1 hBW
  have hW₀O : W₀.comap (algebraMap K (RatFunc K)) = v.valuationSubring := by
    rw [comap_comap_algebraMap]; exact hWO
  have hlines : gaussJoinModel v a c = ZariskiModel.lines v fun i ↦
      coord (RatFunc.X : RatFunc K) (a i) (c i) := by
    simp only [gaussJoinModel, gaussCoord_eq_coord (hc _)]
  rw [hlines] at hJ
  obtain ⟨S, hS, hSW, hloc⟩ := exists_routed_of_mem hc hconv hred hW₀O hJ hJW
  refine ⟨S, hS, (normChart_le_iff _ _).2 hSW, ?_⟩
  have h1 : S ≤ localAt J W₀ := hloc ▸ le_localAt
  have h2 : J ≤ localAt S W₀ := hloc.symm ▸ le_localAt
  exact W10Stable.localAt_eq_of_le_localAt (W10Stable.normChart_le_localAt h2)
    (W10Stable.normChart_le_localAt h1)

end W10Route

end SemistableReduction
