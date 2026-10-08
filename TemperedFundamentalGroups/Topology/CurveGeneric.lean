/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.UniversalLength
import TemperedFundamentalGroups.Topology.HeightBound

/-!
# Generic points under maps of curves (Blueprint §10.3.8, transport)

* `curveConfig_map_η`: a continuous map sending a component onto a component sends its generic
  point to the generic point.
* `CurveConfig.eq_gen_of`: a point of the tree covering over the (non-special) generic point of
  the component of its component vertex is the generic point of that vertex.
* `curveConfig_eq_univ_of_singleton`: in a connected curve, a component which is a single point
  is the whole space.
* `curveConfig_not_contr_of_homeomorph`: a homeomorphism contracts no component, unless some
  component is a point.
-/

universe u v

open Set TopologicalSpace

namespace TemperedFundamentalGroups

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- A point of the tree covering over the generic point of the component of its (component)
vertex is the generic point of the vertex. -/
lemma eq_gen_of {x : K.Cover r} {i : ι} (h : x.1.2.1.head? = some (.inl i))
    (hx : x.1.1 = K.η i) (hS : K.η i ∉ K.S) : x = gen x.1.2 := by
  refine Cover.ext ?_ ?_
  · rw [gen_fst_of_inl h, hx]
  · rw [gen_of_inl h, incl_of_notMem hS]

end CurveConfig

variable {Z : Type u} [TopologicalSpace Z] [NoetherianSpace Z] [T0Space Z] [QuasiSober Z]
  {Z' : Type u} [TopologicalSpace Z'] [NoetherianSpace Z'] [T0Space Z'] [QuasiSober Z']

/-- **Generic points go to generic points.** -/
lemma curveConfig_map_η (hdim : topologicalKrullDim Z ≤ 1) (hdim' : topologicalKrullDim Z' ≤ 1)
    {ψ : Z → Z'} (hψ : Continuous ψ) {i : irreducibleComponents Z}
    {i' : irreducibleComponents Z'}
    (h : ψ '' (curveConfig Z hdim).C i = (curveConfig Z' hdim').C i') :
    ψ ((curveConfig Z hdim).η i) = (curveConfig Z' hdim').η i' := by
  rw [curveConfig_C, curveConfig_C] at h
  rw [curveConfig_η, curveConfig_η]
  have hcl : IsClosed i.1 := isClosed_of_mem_irreducibleComponents i.1 i.2
  have hcl' : IsClosed i'.1 := isClosed_of_mem_irreducibleComponents i'.1 i'.2
  set η := i.2.1.genericPoint
  set η' := i'.2.1.genericPoint
  have hgen : closure {η} = i.1 := i.2.1.isGenericPoint_genericPoint hcl
  have hgen' : closure {η'} = i'.1 := i'.2.1.isGenericPoint_genericPoint hcl'
  have hηi : η ∈ i.1 := hgen ▸ subset_closure (mem_singleton η)
  have himg : closure {ψ η} = i'.1 := by
    refine subset_antisymm (hcl'.closure_subset_iff.2
      (singleton_subset_iff.2 (h ▸ mem_image_of_mem ψ hηi))) ?_
    rw [← h]
    calc ψ '' i.1 = ψ '' closure {η} := by rw [hgen]
      _ ⊆ closure (ψ '' {η}) := image_closure_subset_closure_image hψ
      _ = closure {ψ η} := by rw [image_singleton]
  exact (inseparable_iff_closure_eq.2 (himg.trans hgen'.symm)).eq

/-- In a connected curve, a component which is a single point is the whole space. -/
lemma curveConfig_eq_univ_of_singleton [ConnectedSpace Z] (hdim : topologicalKrullDim Z ≤ 1)
    {j : irreducibleComponents Z} {z : Z} (hj : (curveConfig Z hdim).C j = {z}) :
    (univ : Set Z) = {z} := by
  rw [curveConfig_C] at hj
  -- `z` lies on no other component
  have hz : ∀ k : irreducibleComponents Z, k ≠ j → z ∉ k.1 := by
    intro k hk hzk
    have hsub : j.1 ⊆ k.1 := hj ▸ singleton_subset_iff.2 hzk
    exact hk (Subtype.ext (subset_antisymm (j.2.2 k.2.1 hsub) hsub))
  have hcl₁ : IsClosed ({z} : Set Z) := hj ▸ isClosed_of_mem_irreducibleComponents j.1 j.2
  have hcl₂ : IsClosed (⋃ k : {k : irreducibleComponents Z // k ≠ j}, k.1.1) :=
    isClosed_iUnion_of_finite fun k => isClosed_of_mem_irreducibleComponents k.1.1 k.1.2
  have hcover : ∀ y : Z, y = z ∨ y ∈ ⋃ k : {k : irreducibleComponents Z // k ≠ j}, k.1.1 := by
    intro y
    obtain ⟨k, hk⟩ := (curveConfig Z hdim).cover y
    by_cases hkj : k = j
    · subst hkj
      left
      have : y ∈ k.1 := hk
      rw [hj] at this
      exact this
    · exact .inr (mem_iUnion.2 ⟨⟨k, hkj⟩, hk⟩)
  have hdisj : Disjoint ({z} : Set Z) (⋃ k : {k : irreducibleComponents Z // k ≠ j}, k.1.1) := by
    rw [disjoint_singleton_left, mem_iUnion]
    rintro ⟨k, hk⟩
    exact hz k.1 k.2 hk
  have hopen : IsOpen ({z} : Set Z) := by
    have : ({z} : Set Z)ᶜ = ⋃ k : {k : irreducibleComponents Z // k ≠ j}, k.1.1 := by
      ext y
      refine ⟨fun hy => (hcover y).resolve_left hy, fun hy hyz => ?_⟩
      exact hdisj.ne_of_mem hyz hy rfl
    rw [← isClosed_compl_iff, this]
    exact hcl₂
  rcases isClopen_iff.1 ⟨hcl₁, hopen⟩ with h | h
  · exact absurd h (singleton_ne_empty z)
  · exact h.symm

omit [TopologicalSpace Z'] [NoetherianSpace Z'] [T0Space Z'] [QuasiSober Z'] in
/-- A homeomorphism of curves contracts no component, unless some component of the source is a
single point. -/
lemma curveConfig_not_contr_of_injective (hdim : topologicalKrullDim Z ≤ 1) {ψ : Z → Z'}
    (hψ : Function.Injective ψ)
    (hns : ∀ (j : irreducibleComponents Z) (z : Z), (curveConfig Z hdim).C j ≠ {z})
    (i : irreducibleComponents Z) : ¬ CurveConfig.Contr (K := curveConfig Z hdim) ψ i := by
  rintro ⟨y, hy⟩
  have hne : ((curveConfig Z hdim).C i).Nonempty := ⟨_, (curveConfig Z hdim).η_mem i⟩
  obtain ⟨z, hz⟩ := hne
  refine hns i z (subset_antisymm (fun w hw => ?_) (singleton_subset_iff.2 hz))
  have h₁ : ψ w ∈ ψ '' (curveConfig Z hdim).C i := ⟨w, hw, rfl⟩
  have h₂ : ψ z ∈ ψ '' (curveConfig Z hdim).C i := ⟨z, hz, rfl⟩
  rw [hy] at h₁ h₂
  exact hψ (h₁.trans h₂.symm)


omit [NoetherianSpace Z'] [T0Space Z'] [QuasiSober Z'] in
/-- The image of a component under a continuous closed map is the closure of the image of its
generic point. -/
lemma curveConfig_image_eq_closure (hdim : topologicalKrullDim Z ≤ 1) {ψ : Z → Z'}
    (hψ : Continuous ψ) (hψc : IsClosedMap ψ) (i : irreducibleComponents Z) :
    ψ '' (curveConfig Z hdim).C i = closure {ψ ((curveConfig Z hdim).η i)} := by
  rw [curveConfig_C, curveConfig_η]
  set η := i.2.1.genericPoint
  have hcl : IsClosed i.1 := isClosed_of_mem_irreducibleComponents i.1 i.2
  have hgen : closure {η} = i.1 := i.2.1.isGenericPoint_genericPoint hcl
  have hηi : η ∈ i.1 := hgen ▸ subset_closure (mem_singleton η)
  refine subset_antisymm ?_ ((hψc _ hcl).closure_subset_iff.2
    (singleton_subset_iff.2 (mem_image_of_mem ψ hηi)))
  calc ψ '' i.1 = ψ '' closure {η} := by rw [hgen]
    _ ⊆ closure (ψ '' {η}) := image_closure_subset_closure_image hψ
    _ = closure {ψ η} := by rw [image_singleton]

end TemperedFundamentalGroups
