/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.CoverLength
import TemperedFundamentalGroups.Topology.UniversalCovering

/-!
# Lengths in universal coverings of curves (Blueprint §10.3.6, item 3)

For the curve configuration of the irreducible components of a noetherian quasi-sober `T₀` space
of dimension `≤ 1` (`curveConfig`), the topological hypotheses of the monotonicity of lengths
(`CurveConfig.tlen_map_le`) hold for every continuous closed map `ψ : Z → Z'` between such
spaces:

* `curveConfig_injective_C`: different components are different sets;
* `curveConfig_contr_or`: a component is either contracted to a point by `ψ`, or mapped onto a
  component, its generic point to a point which is not special (on one component only).
-/

universe u

open Set Topology TopologicalSpace

namespace TemperedFundamentalGroups

variable {Z : Type u} [TopologicalSpace Z] [NoetherianSpace Z] [T0Space Z] [QuasiSober Z]
  {Z' : Type u} [TopologicalSpace Z'] [NoetherianSpace Z'] [T0Space Z'] [QuasiSober Z']

lemma curveConfig_injective_C (hdim : topologicalKrullDim Z ≤ 1) :
    Function.Injective (curveConfig Z hdim).C := fun _ _ h => Subtype.ext h

lemma curveConfig_C (hdim : topologicalKrullDim Z ≤ 1) (i : irreducibleComponents Z) :
    (curveConfig Z hdim).C i = i.1 := rfl

lemma curveConfig_η (hdim : topologicalKrullDim Z ≤ 1) (i : irreducibleComponents Z) :
    (curveConfig Z hdim).η i = i.2.1.genericPoint := rfl

lemma mem_curveConfig_S {hdim : topologicalKrullDim Z ≤ 1} {z : Z} :
    z ∈ (curveConfig Z hdim).S ↔
      ∃ i j : irreducibleComponents Z, i ≠ j ∧ z ∈ i.1 ∧ z ∈ j.1 := Iff.rfl

/-- **Images of components under closed maps** of curves: contracted to a point, or mapped onto
a component with the generic point going to a non-special point. -/
theorem curveConfig_contr_or (hdim : topologicalKrullDim Z ≤ 1)
    (hdim' : topologicalKrullDim Z' ≤ 1) {ψ : Z → Z'} (hψ : Continuous ψ)
    (hψc : IsClosedMap ψ) (i : irreducibleComponents Z)
    (hc : ¬ CurveConfig.Contr (K := curveConfig Z hdim) ψ i) :
    ∃ i', ψ '' (curveConfig Z hdim).C i = (curveConfig Z' hdim').C i' ∧
      ψ ((curveConfig Z hdim).η i) ∉ (curveConfig Z' hdim').S := by
  rw [curveConfig_C, curveConfig_η]
  set η := i.2.1.genericPoint
  have hcl : IsClosed i.1 := isClosed_of_mem_irreducibleComponents i.1 i.2
  have hgen : closure {η} = i.1 := i.2.1.isGenericPoint_genericPoint hcl
  have hirr : IsIrreducible (ψ '' i.1) := i.2.1.image ψ hψ.continuousOn
  have hcl' : IsClosed (ψ '' i.1) := hψc _ hcl
  have himg : closure {ψ η} = ψ '' i.1 := by
    refine subset_antisymm (hcl'.closure_subset_iff.2 (singleton_subset_iff.2
      ⟨η, hgen ▸ subset_closure rfl, rfl⟩)) ?_
    rw [← hgen]
    refine (image_closure_subset_closure_image hψ).trans ?_
    rw [image_singleton]
  have hns : ¬ ∃ y, ψ '' i.1 = {y} := hc
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  -- `ψ '' i.1` is a component: otherwise a chain of three irreducible closed sets
  have heq : ψ '' i.1 = C := by
    by_contra hne
    have hz : ∃ z ∈ ψ '' i.1, z ≠ ψ η := by
      by_contra h
      push Not at h
      exact hns ⟨ψ η, subset_antisymm (fun z hz => h z hz)
        (singleton_subset_iff.2 ⟨η, hgen ▸ subset_closure rfl, rfl⟩)⟩
    obtain ⟨z, hz, hzη⟩ := hz
    let A : IrreducibleCloseds Z' := ⟨closure {z}, isIrreducible_singleton.closure,
      isClosed_closure⟩
    let B : IrreducibleCloseds Z' := ⟨ψ '' i.1, hirr, hcl'⟩
    let C' : IrreducibleCloseds Z' := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
    have hAB : A < B := by
      refine lt_of_le_of_ne (show closure {z} ⊆ ψ '' i.1 from
        hcl'.closure_subset_iff.2 (singleton_subset_iff.2 hz)) fun h => hzη ?_
      have h' : closure {z} = closure {ψ η} := (congrArg SetLike.coe h).trans himg.symm
      exact (inseparable_iff_closure_eq.2 h').eq
    have hBC : B < C' := lt_of_le_of_ne hsub fun h => hne (congrArg SetLike.coe h)
    exact not_lt_lt_of_topologicalKrullDim_le_one hdim' hAB hBC
  refine ⟨⟨C, hC⟩, heq, ?_⟩
  rintro ⟨a, b, hab, ha, hb⟩
  -- a special point is closed
  have hclo : IsClosed ({ψ η} : Set Z') :=
    (curveConfig Z' hdim').isClosed_singleton _ ⟨a, b, hab, ha, hb⟩
  rw [hclo.closure_eq] at himg
  exact hns ⟨ψ η, himg.symm⟩

end TemperedFundamentalGroups
