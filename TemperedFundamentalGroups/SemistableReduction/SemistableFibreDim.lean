/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NoLoopsPrimes
import TemperedFundamentalGroups.SemistableReduction.SemistableDim

/-!
# The special fibre of a semistable model has dimension at most one

* `topologicalKrullDim_le_one_of_isClosed`: a closed subset `Z` of a quasi-sober `T₀` space has
  dimension `≤ 1` as soon as there is no chain `x₂ ⤳ x₁ ⤳ x₀` of three distinct points of `Z`.
* `ModelCode.topologicalKrullDim_Z_le_one`: for a semistable model `c` over a DVR there is no such
  chain in the special fibre (`IsSemistableAt.not_chain` in an affine neighbourhood of `x₀`).
* `topologicalKrullDim_specialFibre_le_one`: the same after an isomorphism `c ≅ c'` and a base
  change `O → O'` of DVRs, the form of the dimension clause of `Statement.StrongComponentA`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

/-- **Dimension of a closed subset via chains of points.** -/
theorem topologicalKrullDim_le_one_of_isClosed {X : Type*} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {Z : Set X} (hZ : IsClosed Z)
    (H : ∀ x₀ x₁ x₂ : X, x₀ ∈ Z → x₁ ∈ Z → x₂ ∈ Z → x₁ ⤳ x₀ → x₂ ⤳ x₁ → ¬ x₀ ⤳ x₁ →
      ¬ x₁ ⤳ x₂ → False) :
    topologicalKrullDim Z ≤ 1 := by
  haveI : QuasiSober Z := hZ.isClosedEmbedding_subtypeVal.quasiSober
  letI := specializationOrder Z
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints,
    Order.krullDim_le_one_iff]
  intro x
  by_contra hx
  rw [not_or, not_isMin_iff, not_isMax_iff] at hx
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hx
  exact H a x b a.2 x.2 b.2 (ha.1.map continuous_subtype_val) (hb.1.map continuous_subtype_val)
    (fun h ↦ ha.2 (Topology.IsInducing.subtypeVal.specializes_iff.1 h))
    (fun h ↦ hb.2 (Topology.IsInducing.subtypeVal.specializes_iff.1 h))

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {c : TemperedFundamentalGroups.ModelCode O}

/-- **No chains of length two in the special fibre of a semistable model.** -/
theorem not_chain_Z {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsSemistable ϖ c) {x₀ x₁ x₂ : c.scheme}
    (hx₂ : x₂ ∈ Z c) (h₁ : x₁ ⤳ x₀) (h₂ : x₂ ⤳ x₁) (h₁' : ¬ x₀ ⤳ x₁) (h₂' : ¬ x₁ ⤳ x₂) :
    False := by
  obtain ⟨U, hU, hx₀, hs⟩ := hc x₀
  letI := sectionsAlgebra c U
  have hx₁ : x₁ ∈ U := h₁.mem_open U.isOpen hx₀
  have hx₂U : x₂ ∈ U := h₂.mem_open U.isOpen hx₁
  have hind : Topology.IsInducing hU.fromSpec := hU.fromSpec.isOpenEmbedding.isInducing
  have hsp : ∀ {y z : c.scheme} (hy : y ∈ U) (hz : z ∈ U),
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal ≤ (hU.primeIdealOf ⟨z, hz⟩).asIdeal ↔ y ⤳ z := by
    intro y z hy hz
    constructor
    · intro h
      have := hind.specializes_iff.mpr ((PrimeSpectrum.le_iff_specializes _ _).mp h)
      rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
    · intro h
      have : hU.fromSpec (hU.primeIdealOf ⟨y, hy⟩) ⤳ hU.fromSpec (hU.primeIdealOf ⟨z, hz⟩) := by
        rw [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf]; exact h
      exact (PrimeSpectrum.le_iff_specializes _ _).mpr (hind.specializes_iff.mp this)
  have hlt : ∀ {y z : c.scheme} (hy : y ∈ U) (hz : z ∈ U), y ⤳ z → ¬ z ⤳ y →
      (hU.primeIdealOf ⟨y, hy⟩).asIdeal < (hU.primeIdealOf ⟨z, hz⟩).asIdeal :=
    fun hy hz h h' ↦ lt_of_le_not_ge ((hsp hy hz).2 h) fun e ↦ h' ((hsp hz hy).1 e)
  exact IsSemistableAt.not_chain hϖ hs (hlt hx₁ hx₀ h₁ h₁') (hlt hx₂U hx₁ h₂ h₂')
    ((mem_Z_iff hϖ hU hx₂U).1 hx₂)

/-- **The special fibre of a semistable model has dimension at most one.** -/
theorem topologicalKrullDim_Z_le_one {ϖ : O} (hϖ : Irreducible ϖ) (hc : IsSemistable ϖ c) :
    topologicalKrullDim (Z c) ≤ 1 :=
  topologicalKrullDim_le_one_of_isClosed (isClosed_Z c)
    fun _ _ _ _ _ hx₂ h₁ h₂ h₁' h₂' ↦ not_chain_Z hϖ hc hx₂ h₁ h₂ h₁' h₂'

end TemperedFundamentalGroups.SemistableReduction.ModelCode

namespace TemperedFundamentalGroups

/-- **Special fibres after base change of DVRs.** For `f : X ⟶ Spec O'`, a local map `φ : O → O'`
of DVRs with `O → O'` injective and an isomorphism `e : Y ≅ X`, the special fibre of
`e.hom ≫ f ≫ Spec φ` embeds into that of `f`; hence its dimension is at most that of `f`. -/
theorem topologicalKrullDim_specialFibre_comp_le {O O' : Type u} [CommRing O] [CommRing O']
    [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
    (φ : O →+* O') (hφ : Function.Injective φ) {X Y : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of O')) (e : Y ≅ X) :
    topologicalKrullDim (specialFibre (e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom φ))) ≤
      topologicalKrullDim (specialFibre f) := by
  have hmem : ∀ y ∈ specialFibre (e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom φ)),
      e.hom y ∈ specialFibre f := by
    intro y hy
    rw [mem_specialFibre] at hy ⊢
    set p := f (e.hom y)
    have hp : PrimeSpectrum.comap φ p = closedPoint O := by
      rw [← hy, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      rfl
    have hne : p.asIdeal ≠ ⊥ := by
      intro h0
      have := congrArg PrimeSpectrum.asIdeal hp
      rw [PrimeSpectrum.comap_asIdeal, h0, ← RingHom.ker_eq_comap_bot,
        (RingHom.injective_iff_ker_eq_bot φ).1 hφ, closedPoint] at this
      exact IsDiscreteValuationRing.not_a_field' (R := O) this.symm
    apply PrimeSpectrum.ext
    exact ((p.isPrime.isMaximal hne).eq_of_le (maximalIdeal.isMaximal O').ne_top
      (le_maximalIdeal p.isPrime.ne_top))
  let g : specialFibre (e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom φ)) → specialFibre f :=
    fun y ↦ ⟨e.hom y.1, hmem y.1 y.2⟩
  have hg : Topology.IsInducing g := by
    have h1 : Topology.IsInducing (fun y : specialFibre
        (e.hom ≫ f ≫ Spec.map (CommRingCat.ofHom φ)) ↦ e.hom y.1) :=
      (Scheme.homeoOfIso e).isInducing.comp Topology.IsInducing.subtypeVal
    exact Topology.IsInducing.of_comp (by fun_prop) continuous_subtype_val h1
  exact hg.topologicalKrullDim_le

/-- **The dimension clause of `Statement.StrongComponentA`** from semistability of `c'` and
`c.toSpec = e.hom ≫ c'.toSpec ≫ Spec φ`. -/
theorem ModelCode.topologicalKrullDim_le_one_of_iso {O O' : Type u} [CommRing O] [CommRing O']
    [IsDomain O] [IsDiscreteValuationRing O] [IsDomain O'] [IsDiscreteValuationRing O']
    (φ : O →+* O') (hφ : Function.Injective φ) {ϖ' : O'} (hϖ' : Irreducible ϖ')
    {c : ModelCode O} {c' : ModelCode O'} (e : c.scheme ≅ c'.scheme)
    (hc' : SemistableReduction.ModelCode.IsSemistable ϖ' c')
    (he : e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom φ) = c.toSpec) :
    topologicalKrullDim (specialFibre c.toSpec) ≤ 1 := by
  rw [← he]
  exact (topologicalKrullDim_specialFibre_comp_le φ hφ c'.toSpec e).trans
    (SemistableReduction.ModelCode.topologicalKrullDim_Z_le_one hϖ' hc')

end TemperedFundamentalGroups
