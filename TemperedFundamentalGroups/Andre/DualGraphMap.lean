/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.GTransitiveAux
import TemperedFundamentalGroups.SemistableReduction.HarmonicXProof
import TemperedFundamentalGroups.SemistableReduction.SemistableFibreDim

/-!
# Bundled maps of dual graphs (Blueprint §11.2, G4)

For a morphism `ψ : c ⟶ c'` of projective models (over local rings `O₁`, `O₂`) the dual graphs
(`ModelCode.components`, `ModelCode.IsNodePt`, `SemistableReduction/DualGraph.lean`) are related
by a **map of dual graphs** (`ModelCode.IsDualGraphMap`):

* (G1) every component is contracted to a point or mapped onto a component
  (`ModelCode.contracted_or_mem_components`, from closedness of `ψ` and `dim Z c' ≤ 1`);
* (G2, X3) a node not over a node maps to a point on exactly one component;
* (G3, X1 without lengths) **edge lifting**: from every component over a branch `w₁'` of a node
  `y'` of `c'` there is a walk crossing `y'` to a component over the other branch.

The data of the map is `IsDualGraphMap.vertexMap` (components to components `⊕` points) and
`IsDualGraphMap.edgeMap` (nodes to nodes `⊕` points), with incidence compatibility
(`IsDualGraphMap.mem_vertexMap_inl`, …). The metric form (G5) is `ModelCode.IsHarmonicDualGraphMap`:
a map of dual graphs which is moreover x-harmonic (`ModelCode.IsHarmonicX`, (X0)–(X3)).

Main results:

* `ModelCode.mem_components_iff`: components of the dual graph are the images of the irreducible
  components of the special fibre (as a subspace);
* `isHarmonicDualGraphMap_of_harmonicX`: under the hypotheses of `Statement.HarmonicX`
  (unfolded split semistable W-models without loops) and closedness of `ψ`, `ψ` is a harmonic
  map of dual graphs;
* `ModelCode.isClosedMap_of_comp_eq`: closedness of model maps over a common base.
-/

universe u

open CategoryTheory AlgebraicGeometry Set Topology TopologicalSpace

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

section Components

variable {O : Type u} [CommRing O] [IsLocalRing O] {c : TemperedFundamentalGroups.ModelCode O}

/-- Components of the dual graph are closed (over any local ring). -/
lemma isClosed_of_mem_components' {v : Set c.scheme} (hv : v ∈ components c) : IsClosed v := by
  have h := hv.2.2 (closure v) hv.1.closure ((isClosed_Z c).closure_subset_iff.2 hv.2.1)
    subset_closure
  rw [← h]
  exact isClosed_closure

/-- **Components of the dual graph are the irreducible components of the special fibre.** -/
theorem mem_components_iff {v : Set c.scheme} :
    v ∈ components c ↔ v ⊆ Z c ∧ ((↑) ⁻¹' v : Set (Z c)) ∈ irreducibleComponents (Z c) := by
  constructor
  · intro hv
    refine ⟨hv.2.1, WData.isIrreducible_preimage_val hv.1 hv.2.1, fun D hD hsub ↦ ?_⟩
    have hD' : IsIrreducible ((↑) '' D : Set c.scheme) :=
      hD.image _ continuous_subtype_val.continuousOn
    have hDZ : ((↑) '' D : Set c.scheme) ⊆ Z c := by
      rintro _ ⟨z, -, rfl⟩
      exact z.2
    have hvD : v ⊆ (↑) '' D := fun y hy ↦ ⟨⟨y, hv.2.1 hy⟩, hsub hy, rfl⟩
    have := hv.2.2 _ hD' hDZ hvD
    intro z hz
    change z.1 ∈ v
    rw [← this]
    exact ⟨z, hz, rfl⟩
  · rintro ⟨hvZ, hC⟩
    have himg : ((↑) '' ((↑) ⁻¹' v : Set (Z c)) : Set c.scheme) = v := by
      rw [Subtype.image_preimage_coe]
      exact inter_eq_right.2 hvZ
    refine ⟨himg ▸ hC.1.image _ continuous_subtype_val.continuousOn, hvZ,
      fun w hw hwZ hvw ↦ ?_⟩
    have hw' := WData.isIrreducible_preimage_val hw hwZ
    have := hC.2 hw' (preimage_mono hvw)
    refine subset_antisymm (fun y hy ↦ ?_) hvw
    exact this (show (⟨y, hwZ hy⟩ : Z c) ∈ ((↑) ⁻¹' w : Set (Z c)) from hy)

/-- Images of irreducible components of the special fibre are components of the dual graph. -/
lemma image_mem_components {C : Set (Z c)} (hC : C ∈ irreducibleComponents (Z c)) :
    ((↑) '' C : Set c.scheme) ∈ components c := by
  refine mem_components_iff.2 ⟨fun _ ⟨z, _, hz⟩ ↦ hz ▸ z.2, ?_⟩
  rwa [Subtype.preimage_coe_eq_preimage_coe_iff.2 (by rfl), preimage_image_eq _
    Subtype.val_injective]

end Components

section Contraction

variable {O₁ O₂ : Type u} [CommRing O₁] [IsLocalRing O₁] [CommRing O₂] [IsLocalRing O₂]
  {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}

/-- **(G1) Components are contracted or mapped onto components**: for a closed map `ψ` of models
mapping special fibre to special fibre, into a model whose special fibre is noetherian of
dimension `≤ 1`. -/
theorem contracted_or_mem_components (ψ : c.scheme ⟶ c'.scheme) (hcl : IsClosedMap ψ)
    (hZ : ∀ y ∈ Z c, ψ y ∈ Z c') [NoetherianSpace (Z c')] (hdim : topologicalKrullDim (Z c') ≤ 1)
    {v : Set c.scheme} (hv : v ∈ components c) :
    IsContracted' ψ v ∨ ψ '' v ∈ components c' := by
  by_cases hcon : IsContracted' ψ v
  · exact .inl hcon
  refine .inr ?_
  haveI : QuasiSober (Z c') := (isClosed_Z c').isClosedEmbedding_subtypeVal.quasiSober
  have hvcl := isClosed_of_mem_components' hv
  set η := hv.1.genericPoint
  have hη : closure {η} = v := by
    have := hv.1.isGenericPoint_genericPoint_closure
    rw [hvcl.closure_eq] at this
    exact this
  have hηZ : η ∈ Z c := hv.2.1 (hη ▸ subset_closure rfl)
  let f : Z c → Z c' := fun y ↦ ⟨ψ y.1, hZ y.1 y.2⟩
  have hf : Continuous f := (ψ.continuous.comp continuous_subtype_val).subtype_mk _
  have hfc : IsClosedMap f := by
    intro C hC
    have h₁ : IsClosed ((↑) '' C : Set c.scheme) := (isClosed_Z c).isClosedMap_subtype_val _ hC
    convert (hcl _ h₁).preimage continuous_subtype_val using 1
    ext z
    simp only [mem_image, mem_preimage, f]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.1, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
      exact ⟨y, hy, Subtype.ext hz⟩
  set C : Set (Z c) := (↑) ⁻¹' v
  have hCη : closure {(⟨η, hηZ⟩ : Z c)} = C := by
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image, image_singleton]
    change Subtype.val ⁻¹' closure {η} = Subtype.val ⁻¹' v
    rw [hη]
  have himg : ((↑) '' (f '' C) : Set c'.scheme) = ψ '' v := by
    rw [image_image]
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨z.1, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨z, hv.2.1 hz⟩, hz, rfl⟩
  have hnc : ¬ ∃ y, f '' C = {y} := by
    rintro ⟨y, hy⟩
    refine hcon ⟨y.1, ?_⟩
    rw [← himg, hy, image_singleton]
  have := image_mem_irreducibleComponents hdim hf hfc hCη hnc
  rw [← himg]
  exact image_mem_components this

omit [IsLocalRing O₁] in
/-- **Model maps over a common base are closed** (the models are proper). -/
lemma isClosedMap_of_comp_eq {c c' : TemperedFundamentalGroups.ModelCode O₁}
    (ψ : c.scheme ⟶ c'.scheme) (hψ : ψ ≫ c'.toSpec = c.toSpec) : IsClosedMap ψ := by
  haveI : UniversallyClosed (ψ ≫ c'.toSpec) := by rw [hψ]; infer_instance
  haveI : UniversallyClosed ψ := UniversallyClosed.of_comp_of_isSeparated ψ c'.toSpec
  exact ψ.isClosedMap

/-- Model maps over a common base map special fibres to special fibres. -/
lemma mem_Z_of_comp_eq {c c' : TemperedFundamentalGroups.ModelCode O₁}
    (ψ : c.scheme ⟶ c'.scheme) (hψ : ψ ≫ c'.toSpec = c.toSpec) {y : c.scheme} (hy : y ∈ Z c) :
    ψ y ∈ Z c' := by
  change c'.toSpec (ψ y) = _
  rw [← Scheme.Hom.comp_apply, hψ]
  exact hy

/-- The special fibre of a model over a discrete valuation ring is a noetherian space. -/
lemma noetherianSpace_Z {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (c : TemperedFundamentalGroups.ModelCode O) : NoetherianSpace (Z c) := by
  haveI : IsLocallyNoetherian c.scheme := LocallyOfFiniteType.isLocallyNoetherian c.toSpec
  haveI : CompactSpace c.scheme := QuasiCompact.compactSpace_of_compactSpace c.toSpec
  haveI : IsNoetherian c.scheme := {}
  exact NoetherianSpace.set _

end Contraction

section DualGraphMap

variable {O₁ O₂ : Type u} [CommRing O₁] [IsLocalRing O₁] [CommRing O₂] [IsLocalRing O₂]
  {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}

/-- **A map of dual graphs** (Blueprint §11.2, G4) along a morphism of models `ψ : c ⟶ c'`:
* special fibre to special fibre;
* (G1) every component is contracted to a point or mapped onto a component;
* (G2, X3) a node not over a node maps to a point on exactly one component;
* (G3) **edge lifting**: for every node `y'` of `c'` on two components `w₁' ≠ w₂'`, every
  component of `c` over `w₁'` starts a walk crossing `y'` (inner components contracted to `y'`,
  nodes over `y'`) to a component over `w₂'`. -/
structure IsDualGraphMap (ψ : c.scheme ⟶ c'.scheme) : Prop where
  mapsTo_Z : ∀ y ∈ Z c, ψ y ∈ Z c'
  vertex : ∀ v ∈ components c, IsContracted' ψ v ∨ ψ '' v ∈ components c'
  edge : ∀ y : c.scheme, IsNodePt c y → ¬ IsNodePt c' (ψ y) →
    ∃! w', w' ∈ components c' ∧ ψ y ∈ w'
  edgeLift : ∀ y' : c'.scheme, IsNodePt c' y' →
    ∀ w₁' ∈ components c', ∀ w₂' ∈ components c', w₁' ≠ w₂' → y' ∈ w₁' → y' ∈ w₂' →
    ∀ v ∈ components c, ψ '' v = w₁' →
      ∃ w : Walk c, w.v 0 = v ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂'

namespace IsDualGraphMap

variable {ψ : c.scheme ⟶ c'.scheme} (h : IsDualGraphMap ψ)

open Classical in
/-- **The vertex map**: a component goes to its image component, or to the point it is contracted
to. -/
noncomputable def vertexMap (_h : IsDualGraphMap ψ) (v : components c) :
    components c' ⊕ c'.scheme :=
  if hv : ψ '' v.1 ∈ components c' then .inl ⟨_, hv⟩
  else .inr ((_h.vertex v.1 v.2).resolve_right hv).choose

lemma vertexMap_inl {v : components c} {w : components c'} (hv : h.vertexMap v = .inl w) :
    ψ '' v.1 = w.1 := by
  unfold vertexMap at hv
  split_ifs at hv with h'
  · cases hv
    rfl

lemma vertexMap_inr {v : components c} {p : c'.scheme} (hv : h.vertexMap v = .inr p) :
    ψ '' v.1 = {p} := by
  unfold vertexMap at hv
  split_ifs at hv with h'
  cases hv
  exact ((h.vertex v.1 v.2).resolve_right h').choose_spec

lemma vertexMap_of_mem {v : components c} (hv : ψ '' v.1 ∈ components c') :
    h.vertexMap v = .inl ⟨_, hv⟩ := by
  unfold vertexMap
  rw [dif_pos hv]

open Classical in
/-- **The edge map**: a node goes to its image node, or to the (smooth) point it maps to. -/
noncomputable def edgeMap (_h : IsDualGraphMap ψ) (y : {y : c.scheme // IsNodePt c y}) :
    {y' : c'.scheme // IsNodePt c' y'} ⊕ c'.scheme :=
  if hy : IsNodePt c' (ψ y.1) then .inl ⟨_, hy⟩ else .inr (ψ y.1)

lemma edgeMap_inl {y : {y : c.scheme // IsNodePt c y}} {y' : {y' : c'.scheme // IsNodePt c' y'}}
    (hy : h.edgeMap y = .inl y') : ψ y.1 = y'.1 := by
  unfold edgeMap at hy
  split_ifs at hy
  cases hy
  rfl

lemma edgeMap_inr {y : {y : c.scheme // IsNodePt c y}} {p : c'.scheme}
    (hy : h.edgeMap y = .inr p) :
    ψ y.1 = p ∧ ¬ IsNodePt c' p ∧ ∃! w', w' ∈ components c' ∧ p ∈ w' := by
  unfold edgeMap at hy
  split_ifs at hy with h'
  cases hy
  exact ⟨rfl, h', h.edge _ y.2 h'⟩

/-- **Incidence (contracted vertex)**: a node on a contracted component maps to its image point. -/
lemma apply_eq_of_vertexMap_inr {v : components c} {p : c'.scheme}
    (hv : h.vertexMap v = .inr p) {y : c.scheme} (hy : y ∈ v.1) : ψ y = p := by
  have := h.vertexMap_inr hv
  have hm : ψ y ∈ ψ '' v.1 := mem_image_of_mem _ hy
  rwa [this] at hm

/-- **Incidence (edges)**: a node on a component `v` going to a node `y'` gives an incidence of
`y'` with the image of `v`. -/
lemma mem_of_vertexMap_inl_of_edgeMap_inl {v : components c} {w : components c'}
    (hv : h.vertexMap v = .inl w) {y : {y : c.scheme // IsNodePt c y}}
    {y' : {y' : c'.scheme // IsNodePt c' y'}} (hy : h.edgeMap y = .inl y') (hyv : y.1 ∈ v.1) :
    y'.1 ∈ w.1 := by
  rw [← h.edgeMap_inl hy, ← h.vertexMap_inl hv]
  exact mem_image_of_mem _ hyv

/-- **Incidence (edges collapsed to points)**: a node on a component `v` going to a smooth point
`p` gives a point of the image component of `v`, which is the only component through `p`. -/
lemma vertexMap_eq_of_edgeMap_inr {v : components c} {w : components c'}
    (hv : h.vertexMap v = .inl w) {y : {y : c.scheme // IsNodePt c y}} {p : c'.scheme}
    (hy : h.edgeMap y = .inr p) (hyv : y.1 ∈ v.1) :
    p ∈ w.1 ∧ ∀ w' ∈ components c', p ∈ w' → w' = w.1 := by
  obtain ⟨hp, -, w₀, ⟨-, -⟩, huniq⟩ := h.edgeMap_inr hy
  have hpw : p ∈ w.1 := by
    rw [← hp, ← h.vertexMap_inl hv]
    exact mem_image_of_mem _ hyv
  exact ⟨hpw, fun w' hw' hpw' ↦ (huniq w' ⟨hw', hpw'⟩).trans (huniq w.1 ⟨w.2, hpw⟩).symm⟩

end IsDualGraphMap

end DualGraphMap

end TemperedFundamentalGroups.SemistableReduction.ModelCode

namespace TemperedFundamentalGroups.SemistableReduction

open ModelCode

/-- **A harmonic map of dual graphs** (Blueprint §11.2, G4 with G5): a map of dual graphs which is
x-harmonic ((X0) positive x-lengths, (X1) crossing walks of the same total length, (X2) no
shortening, (X3)). -/
def ModelCode.IsHarmonicDualGraphMap {K₁ K₂ L₁ L₂ : Type u} [Field K₁] [Field K₂] [Field L₁]
    [Field L₂] [Algebra K₁ L₁] [Algebra K₂ L₂] (O₁ : ValuationSubring K₁)
    (O₂ : ValuationSubring K₂) [Algebra O₁ L₁] [Algebra O₂ L₂] (ϖ₁ : O₁) (ϖ₂ : O₂) (ϖ₁₀ : L₁)
    (ϖ₂₀ : L₂) (x₁ : L₁) (x₂ : L₂) {c : TemperedFundamentalGroups.ModelCode O₁}
    {c' : TemperedFundamentalGroups.ModelCode O₂} (j₁ : Spec (CommRingCat.of L₁) ⟶ c.scheme)
    (j₂ : Spec (CommRingCat.of L₂) ⟶ c'.scheme) (ψ : c.scheme ⟶ c'.scheme) : Prop :=
  IsDualGraphMap ψ ∧ IsHarmonicX O₁ O₂ ϖ₁ ϖ₂ ϖ₁₀ ϖ₂₀ x₁ x₂ j₁ j₂ ψ

/-- **Maps of unfolded W-models are harmonic maps of dual graphs** (G4): under the hypotheses of
`Statement.HarmonicXS` (split nodes only), for a closed `ψ` (e.g.
`ModelCode.isClosedMap_of_comp_eq` over a common base), `ψ` is a map of dual graphs (G1 from
closedness and `dim Z c' ≤ 1`, G2 from `x3`, G3 from (X1) and the x-length of the target node
from (X0)) which is x-harmonic (`harmonicXS`). -/
theorem isHarmonicDualGraphMap_of_harmonicXS (K : Type u) [Field K] [CharZero K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O) (hϖ : Irreducible ϖ)
    (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    (O₁ : ValuationSubring K₁) (O₂ : ValuationSubring K₂)
    (h₁ : O₁.comap (algebraMap K K₁) = O) (h₂ : O₂.comap (algebraMap K K₂) = O)
    [IsDiscreteValuationRing O₁] [IsDiscreteValuationRing O₂] (ϖ₁ : O₁) (ϖ₂ : O₂)
    (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂)
    (L₁ L₂ : Type u) [Field L₁] [Field L₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
    [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
    [IsScalarTower K L₂ L₁] [FiniteDimensional L₂ L₁]
    [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂] [IsScalarTower O₂ K₂ L₂] (x : L₂)
    (c : TemperedFundamentalGroups.ModelCode O₁) (c' : TemperedFundamentalGroups.ModelCode O₂)
    (ψ : c.scheme ⟶ c'.scheme)
    (j : Spec (CommRingCat.of L₁) ⟶ c.scheme) (j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme)
    (hU₁ : ModelCode.IsUnfolded O₁ (algebraMap L₂ L₁ x) c j)
    (hU₂ : ModelCode.IsUnfolded O₂ x c' j')
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j')
    (hψO : ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy))))
    (hs₁ : ModelCode.IsSemistable ϖ₁ c) (hs₂ : ModelCode.IsSemistable ϖ₂ c')
    (hsplit₁ : ModelCode.HasSplitNodes ϖ₁ c) (hsplit₂ : ModelCode.HasSplitNodes ϖ₂ c')
    (hloops₁ : ModelCode.NoLoops c) (hloops₂ : ModelCode.NoLoops c')
    (hcl : IsClosedMap ψ) :
    IsHarmonicDualGraphMap O₁ O₂ ϖ₁ ϖ₂ (algebraMap K L₁ ϖ) (algebraMap K L₂ ϖ)
      (algebraMap L₂ L₁ x) x j j' ψ := by
  have hX := harmonicXS K O ϖ hϖ K₁ K₂ O₁ O₂ h₁ h₂ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂ x c c' ψ j j' hU₁ hU₂ hj
    hψO hs₁ hs₂ hsplit₁ hsplit₂ hloops₁ hloops₂
  refine ⟨⟨fun y hy ↦ mem_Z_of_over h₁ h₂ hψO hy, fun v hv ↦ ?_, hX.2.2.2, ?_⟩, hX⟩
  · haveI := noetherianSpace_Z c'
    exact contracted_or_mem_components ψ hcl (fun y hy ↦ mem_Z_of_over h₁ h₂ hψO hy)
      (topologicalKrullDim_Z_le_one hϖ₂ hs₂) hv
  · intro y' hy' w₁' hw₁' w₂' hw₂' hne hy₁ hy₂ v hv hψv
    -- the x-length of the target node, from (X0) for `c'`
    obtain ⟨η₂, e₂, he₂, hϖK₂⟩ := exists_ramification h₂ hϖ hϖ₂
    obtain ⟨l', hl'⟩ := (CrossingSource.x0 hU₂ hϖ₂ hsplit₂ hloops₂ he₂ hϖK₂ y' hy').1
    have hL₂ : algebraMap K L₂ (ϖ : K) = algebraMap K₂ L₂ (algebraMap K K₂ ϖ) :=
      IsScalarTower.algebraMap_apply K K₂ L₂ _
    rw [← hL₂] at hl'
    obtain ⟨w, hw0, hcross, hwk, -⟩ := hX.2.1 y' hy' w₁' hw₁' w₂' hw₂' hne hy₁ hy₂ v hv hψv l' hl'
    exact ⟨w, hw0, hcross, hwk⟩

/-- **Maps of unfolded W-models are harmonic maps of dual graphs** (G4): under the hypotheses of
`Statement.HarmonicX`, for a closed `ψ` (e.g. `ModelCode.isClosedMap_of_comp_eq` over a common
base), `ψ` is a map of dual graphs (G1 from closedness and `dim Z c' ≤ 1`, G2 from `x3`, G3 from
(X1) and the x-length of the target node from (X0)) which is x-harmonic (`harmonicX`). -/
theorem isHarmonicDualGraphMap_of_harmonicX (K : Type u) [Field K] [CharZero K]
    (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O) (hϖ : Irreducible ϖ)
    (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    (O₁ : ValuationSubring K₁) (O₂ : ValuationSubring K₂)
    (h₁ : O₁.comap (algebraMap K K₁) = O) (h₂ : O₂.comap (algebraMap K K₂) = O)
    [IsDiscreteValuationRing O₁] [IsDiscreteValuationRing O₂] (ϖ₁ : O₁) (ϖ₂ : O₂)
    (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂)
    (L₁ L₂ : Type u) [Field L₁] [Field L₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
    [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
    [IsScalarTower K L₂ L₁] [FiniteDimensional L₂ L₁]
    [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂] [IsScalarTower O₂ K₂ L₂] (x : L₂)
    (c : TemperedFundamentalGroups.ModelCode O₁) (c' : TemperedFundamentalGroups.ModelCode O₂)
    (ψ : c.scheme ⟶ c'.scheme)
    (j : Spec (CommRingCat.of L₁) ⟶ c.scheme) (j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme)
    (hU₁ : ModelCode.IsUnfolded O₁ (algebraMap L₂ L₁ x) c j)
    (hU₂ : ModelCode.IsUnfolded O₂ x c' j')
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j')
    (hψO : ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy))))
    (hs₁ : ModelCode.IsSemistable ϖ₁ c) (hs₂ : ModelCode.IsSemistable ϖ₂ c')
    (hsplit₁ : ModelCode.IsSplit ϖ₁ c) (hsplit₂ : ModelCode.IsSplit ϖ₂ c')
    (hloops₁ : ModelCode.NoLoops c) (hloops₂ : ModelCode.NoLoops c')
    (hcl : IsClosedMap ψ) :
    IsHarmonicDualGraphMap O₁ O₂ ϖ₁ ϖ₂ (algebraMap K L₁ ϖ) (algebraMap K L₂ ϖ)
      (algebraMap L₂ L₁ x) x j j' ψ :=
  isHarmonicDualGraphMap_of_harmonicXS K O ϖ hϖ K₁ K₂ O₁ O₂ h₁ h₂ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂ x c c' ψ j
    j' hU₁ hU₂ hj hψO hs₁ hs₂ hsplit₁.1 hsplit₂.1 hloops₁ hloops₂ hcl

end TemperedFundamentalGroups.SemistableReduction
