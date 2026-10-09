/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTreeNormal

/-!
# Normalizations of the tree of projective lines are of finite type

Blueprint §9.6 (W5), layer M8b. Let `O` be a noetherian valuation ring (a discrete valuation
ring) and `F'/K(X)` finite separable. For a convex reduced family of Gauss valuations, the charts
of `gaussJoinModel` are noetherian (finite type over `O`), integrally closed with fraction field
`K(X)` (`gaussJoinModel_isNormal`), so their integral closures in `F'` are finite over them
(Mathlib's `IsIntegralClosure.finite`, via the trace form). Hence the normalization of the tree
of `ℙ¹`s in `F'` is a normal proper separated Zariski model **of finite type**
(`gaussJoinModel_normalization_isFiniteType`), with vertex set the valuations over the family
(`gaussJoinModel_normalization_vertexSet`).
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel GaussTree

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

/-- A chart of finite type over a noetherian base ring is noetherian. -/
lemma isNoetherianRing_of_closure [IsNoetherianRing v.valuationSubring]
    {C : Subring (RatFunc K)} (s : Finset (RatFunc K))
    (hs : C = Subring.closure
      ((baseRing (RatFunc K) v.valuationSubring : Set (RatFunc K)) ∪ s)) :
    IsNoetherianRing C := by
  have hfg := Subalgebra.fg_adjoin_finset (R := v.valuationSubring) s
  have := isNoetherianRing_of_fg hfg
  have h : (Algebra.adjoin v.valuationSubring (s : Set (RatFunc K))).toSubring = C := by
    rw [hs, toSubring_adjoin]
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.subringCongr h)

/-- The integral closure of `C ⊆ F` in `F'`, for the algebra `C → F → F'`, is `normChart F' C`. -/
lemma integralClosure_toSubring_eq {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    (C : Subring F) :
    letI : Algebra C F' := ((algebraMap F F').comp C.subtype).toAlgebra
    (integralClosure C F').toSubring = normChart F' C := by
  letI : Algebra C F' := ((algebraMap F F').comp C.subtype).toAlgebra
  let e : C ≃+* C.map (algebraMap F F') :=
    C.equivMapOfInjective _ (algebraMap F F').injective
  ext x
  change IsIntegral C x ↔ IsIntegral (C.map (algebraMap F F')) x
  constructor
  · intro hx
    have := hx.map_of_comp_eq e.toRingHom (RingHom.id F') (by ext; rfl)
    simpa using this
  · intro hx
    have := hx.map_of_comp_eq e.symm.toRingHom (RingHom.id F') (by
      ext y
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe, RingHom.id_apply]
      change algebraMap F F' (e.symm y : F) = (y : F')
      have := Subring.coe_equivMapOfInjective_apply C (algebraMap F F')
        (algebraMap F F').injective (e.symm y)
      rw [← this]
      exact congrArg Subtype.val (e.apply_symm_apply y))
    simpa using this

/-- **The normalization of the tree of `ℙ¹`s is of finite type** over a noetherian valuation
ring, in a finite separable extension `F'/K(X)`. -/
theorem gaussJoinModel_normalization_isFiniteType [IsNoetherianRing v.valuationSubring]
    {F' : Type u} [Field F'] [Algebra K F'] [Algebra (RatFunc K) F']
    [IsScalarTower K (RatFunc K) F'] [FiniteDimensional (RatFunc K) F']
    [Algebra.IsSeparable (RatFunc K) F']
    {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → K}
    (hc : ∀ i, c i ≠ 0) (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hrank : ∀ O' : ValuationSubring K, v.valuationSubring ≤ O' →
      O' = v.valuationSubring ∨ O' = ⊤) :
    ((gaussJoinModel v a c).normalization F').IsFiniteType := by
  classical
  intro C' hC'
  obtain ⟨C, hC, rfl⟩ := mem_normalization_charts.1 hC'
  obtain ⟨sC, hsC⟩ := gaussJoinModel_isFiniteType C hC
  haveI := isNoetherianRing_of_closure sC hsC
  -- `C` has fraction field `K(X)`: it contains a chart `O[z]` of a Gauss coordinate
  haveI : IsFractionRing C (RatFunc K) := by
    obtain ⟨f, hf, rfl⟩ := mem_iJoin_charts.1 hC
    obtain ⟨i⟩ := ‹Nonempty ι›
    have hfi : f i ≤ baseRing (RatFunc K) v.valuationSubring ⊔ ⨆ i, f i :=
      (le_iSup f i).trans le_sup_right
    obtain ⟨z, hz, hfz⟩ := exists_eq_polyChart_of_mem_line_charts (hf i)
    rw [hfz] at hfi
    rcases hz with rfl | rfl
    · exact (isGaussCoord_gaussCoord (r := Units.mk0 _ ((v.ne_zero_iff).2 (hc i))) rfl
        |>.isFractionRing_of_le hfi)
    · exact (isGaussCoord_gaussCoord (r := Units.mk0 _ ((v.ne_zero_iff).2 (hc i))) rfl
        |>.inv.isFractionRing_of_le hfi)
  haveI : IsIntegrallyClosed C := (isIntegrallyClosed_iff (RatFunc K)).2 fun {x} hx ↦
    ⟨⟨x, gaussJoinModel_isNormal hc hconv hred hrank C hC x hx⟩, rfl⟩
  letI : Algebra C F' := ((algebraMap (RatFunc K) F').comp C.subtype).toAlgebra
  haveI : IsScalarTower C (RatFunc K) F' := .of_algebraMap_eq fun _ ↦ rfl
  have hfin := IsIntegralClosure.finite C (RatFunc K) F' (integralClosure C F')
  obtain ⟨s, hs⟩ := hfin.fg_top
  have hEq := integralClosure_toSubring_eq (F' := F') C
  set R' := baseRing F' v.valuationSubring
  refine ⟨sC.image (algebraMap (RatFunc K) F') ∪ s.image Subtype.val, le_antisymm ?_ ?_⟩
  · -- the integral closure is generated as a `C`-module by `s`
    intro x hx
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
      exact map_le_normChart C (subring_map_mono ((gaussJoinModel v a c).le_chart C hC) _ hx')
    · intro x hx
      simp only [Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
        Finset.mem_coe] at hx
      rcases hx with ⟨y, hy, rfl⟩ | ⟨y, -, rfl⟩
      · refine map_le_normChart C ⟨y, ?_, rfl⟩
        rw [hsC]
        exact Subring.subset_closure (Or.inr hy)
      · rw [← hEq]
        exact y.2

end SemistableReduction
