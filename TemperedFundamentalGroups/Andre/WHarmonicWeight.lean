/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.WData
import TemperedFundamentalGroups.SemistableReduction.TwoComponents
import TemperedFundamentalGroups.Topology.UniversalLength

/-!
# x-lengths as harmonic weights on the special fibres of levels (Blueprint §10.3.6, item 4)

Let `D : WData x Lv` be W-model data on a level `Lv` (model `c'`, `e : Lv.c ≅ c'`). The special
fibre `Lv.Z` of the model of the level is identified with that of `c'` (`WData.mem_Z_iff`), its
irreducible components with the components of the dual graph of `c'` (`WData.compSet_mem`), and
— by `Statement.NodeOfTwoComponents` — its special points (points on two components) with node
points of `c'`.

* `WData.weight D ϖ : Lv.Z → ℝ≥0∞`: the **x-length** of the node `e z` of `c'` (normalised by a
  uniformizer `ϖ` of `O`, on the x-line `x`), `0` at points without an x-length;
* `WData.isHarmonicWeight`: for a morphism `m : X ⟶ Y` of the tempered category with W-model data
  on both levels, the weights are harmonic along the map of special fibres
  (`CurveConfig.IsHarmonicWeight`, the hypothesis of `CurveConfig.tlen_map_le`), from (X0) and
  (X2) of `Statement.HarmonicX`;
* `WData.exists_weight_pos`: the weights of the special points are bounded below by a positive
  constant (X0).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

noncomputable section

section Restrict

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] {O : ValuationSubring K}
  {O' : ValuationSubring K'} (hO' : O'.comap (algebraMap K K') = O)

include hO' in
lemma isLocalHom_restrict :
    IsLocalHom ((algebraMap K K').restrict O O' (fun y hy => by rw [← hO'] at hy; exact hy)) := by
  refine ⟨fun a ha => ?_⟩
  have ha0 : (a : K) ≠ 0 := by
    rintro h
    have : a = 0 := Subtype.ext h
    subst this
    rw [map_zero] at ha
    exact not_isUnit_zero ha
  obtain ⟨u, hu⟩ := ha
  have h₁ : ((u⁻¹ : O'ˣ) : O') * ((u : O'ˣ) : O') = 1 := u.inv_mul
  have h₂ : (((u : O'ˣ) : O') : K') = algebraMap K K' (a : K) := by rw [hu]; rfl
  have h₃ : (((u⁻¹ : O'ˣ) : O') : K') = (algebraMap K K' (a : K))⁻¹ := by
    rw [← h₂]
    exact eq_inv_of_mul_eq_one_left (congrArg Subtype.val h₁)
  have h₄ : (a : K)⁻¹ ∈ O'.comap (algebraMap K K') := by
    rw [ValuationSubring.mem_comap, map_inv₀, ← h₃]
    exact SetLike.coe_mem _
  have hinv : (a : K)⁻¹ ∈ O := by rwa [hO'] at h₄
  exact ⟨⟨a, ⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0), Subtype.ext (inv_mul_cancel₀ ha0)⟩,
    rfl⟩

variable [IsDiscreteValuationRing O] [IsDiscreteValuationRing O']

include hO' in
/-- The closed point of `Spec O'` is the only point over the closed point of `Spec O`. -/
lemma spec_restrict_eq_closedPoint_iff (p : Spec (CommRingCat.of O')) :
    Spec.map (CommRingCat.ofHom
        ((algebraMap K K').restrict O O' (fun y hy => by rw [← hO'] at hy; exact hy))) p =
      (IsLocalRing.closedPoint O : PrimeSpectrum O) ↔
    p = (IsLocalRing.closedPoint O' : PrimeSpectrum O') := by
  haveI := isLocalHom_restrict hO'
  constructor
  · intro h
    by_contra hp
    have hbot : p.asIdeal = ⊥ := by
      by_contra hne
      exact hp (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        (Ideal.IsPrime.isMaximal inferInstance hne)))
    have h' := congrArg PrimeSpectrum.asIdeal h
    rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal, hbot] at h'
    have hker : (⊥ : Ideal O').comap ((algebraMap K K').restrict O O'
        (fun y hy => by rw [← hO'] at hy; exact hy)) = ⊥ := by
      refine Ideal.comap_bot_of_injective _ fun a b hab => Subtype.ext ?_
      exact (algebraMap K K').injective (congrArg Subtype.val hab)
    rw [CommRingCat.hom_ofHom, hker] at h'
    exact IsDiscreteValuationRing.not_a_field O h'.symm
  · rintro rfl
    rw [Spec.map_apply, CommRingCat.hom_ofHom]
    exact IsLocalRing.comap_closedPoint _

end Restrict

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {x : R}

namespace WData

variable {Lv : Level O R A} (D : WData x Lv)

/-- **The special fibres agree.** -/
lemma mem_Z_iff [IsDiscreteValuationRing O] (y : Lv.c.scheme) :
    y ∈ specialFibre Lv.c.toSpec ↔ D.e.hom y ∈ SemistableReduction.ModelCode.Z D.c' := by
  rw [mem_specialFibre, ← D.toSpec_eq, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply,
    spec_restrict_eq_closedPoint_iff D.hO']
  rfl

/-- The point of `c'` of a point of the special fibre. -/
def pt (z : Lv.Z) : D.c'.scheme := D.e.hom z.1

lemma pt_injective : Function.Injective D.pt := fun a b h => Subtype.ext (by
  have := congrArg D.e.inv h
  simpa [pt, ← Scheme.Hom.comp_apply] using this)

/-- The set of `c'` of a set of the special fibre. -/
def compSet (C : Set Lv.Z) : Set D.c'.scheme := D.pt '' C

lemma compSet_injective : Function.Injective D.compSet :=
  Set.image_injective.2 D.pt_injective

lemma pt_mem_compSet_iff {C : Set Lv.Z} {z : Lv.Z} : D.pt z ∈ D.compSet C ↔ z ∈ C :=
  D.pt_injective.mem_set_image

lemma continuous_pt : Continuous D.pt :=
  D.e.hom.continuous.comp continuous_subtype_val

lemma isIrreducible_preimage_val {X : Type*} [TopologicalSpace X] {Z w : Set X}
    (hw : IsIrreducible w) (hwZ : w ⊆ Z) : IsIrreducible ((↑) ⁻¹' w : Set Z) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hw.nonempty
    exact ⟨⟨y, hwZ hy⟩, hy⟩
  · rintro _ _ ⟨u, hu, rfl⟩ ⟨v, hv, rfl⟩ ⟨⟨a, ha⟩, haw, hau⟩ ⟨⟨b, hb⟩, hbw, hbv⟩
    obtain ⟨c, hcw, hcu, hcv⟩ := hw.2 u v hu hv ⟨a, haw, hau⟩ ⟨b, hbw, hbv⟩
    exact ⟨⟨c, hwZ hcw⟩, hcw, hcu, hcv⟩

/-- **Irreducible components of the special fibre are components of the dual graph.** -/
lemma compSet_mem [IsDiscreteValuationRing O] {C : Set Lv.Z} (hC : C ∈ irreducibleComponents Lv.Z) :
    D.compSet C ∈ SemistableReduction.ModelCode.components D.c' := by
  refine ⟨hC.1.image _ D.continuous_pt.continuousOn, ?_, fun w hw hwZ hCw => ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact (D.mem_Z_iff z.1).1 z.2
  · -- pull `w` back to the special fibre of the level
    have hwZ' : D.e.inv '' w ⊆ specialFibre Lv.c.toSpec := by
      rintro _ ⟨y, hy, rfl⟩
      rw [D.mem_Z_iff]
      simpa [← Scheme.Hom.comp_apply] using hwZ hy
    have hirr := isIrreducible_preimage_val (hw.image _ D.e.inv.continuous.continuousOn) hwZ'
    have hsub : C ⊆ (↑) ⁻¹' (D.e.inv '' w) := fun z hz => ⟨D.pt z, hCw ⟨z, hz, rfl⟩, by
      simp [pt, ← Scheme.Hom.comp_apply]⟩
    have heq := hC.2 hirr hsub
    apply subset_antisymm _ hCw
    intro y hy
    have hy' : D.e.inv y ∈ specialFibre Lv.c.toSpec := hwZ' ⟨y, hy, rfl⟩
    refine ⟨⟨D.e.inv y, hy'⟩, heq ⟨y, hy, rfl⟩, ?_⟩
    simp [pt, ← Scheme.Hom.comp_apply]

lemma compSet_eq_singleton {C : Set Lv.Z} {y : D.c'.scheme} (h : D.compSet C = {y}) :
    ∃ z, C = {z} := by
  have hy : y ∈ D.compSet C := h ▸ rfl
  obtain ⟨z, hz, rfl⟩ := hy
  refine ⟨z, subset_antisymm (fun z' hz' => ?_) (singleton_subset_iff.2 hz)⟩
  have : D.pt z' ∈ D.compSet C := ⟨z', hz', rfl⟩
  rw [h] at this
  exact D.pt_injective this

variable [IsDiscreteValuationRing O]

/-- **Special points are nodes** (from `Statement.NodeOfTwoComponents`). -/
lemma isNodePt_of_mem_S (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u})
    [NoetherianSpace Lv.Z] [T0Space Lv.Z] [QuasiSober Lv.Z] {hdim : topologicalKrullDim Lv.Z ≤ 1}
    {s : Lv.Z} (hs : s ∈ (curveConfig Lv.Z hdim).S) :
    SemistableReduction.ModelCode.IsNodePt D.c' (D.pt s) := by
  obtain ⟨i, j, hij, hi, hj⟩ := hs
  exact hN D.K' D.O' D.ϖ' D.hϖ' D.c' D.semistable (D.pt s) _ (D.compSet_mem i.2) _
    (D.compSet_mem j.2) (fun h => hij (Subtype.ext (D.compSet_injective h)))
    ⟨s, hi, rfl⟩ ⟨s, hj, rfl⟩

/-- **The weight of a point of the special fibre**: the x-length of the corresponding point of
the W-model (normalised by `ϖ`), `0` if it has none. -/
def weight (ϖ : O) (z : Lv.Z) : ℝ≥0∞ := by
  classical
  exact if h : ∃ l, SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O' D.ϖ' D.c' D.j₁ D.xL
      (D.pt z) l then ENNReal.ofReal (h.choose : ℝ) else 0

omit [IsDiscreteValuationRing O] in
lemma weight_of_exists (ϖ : O) {z : Lv.Z}
    (h : ∃ l, SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O' D.ϖ' D.c' D.j₁ D.xL
      (D.pt z) l) : D.weight ϖ z = ENNReal.ofReal (h.choose : ℝ) := by
  rw [weight, dif_pos h]

end WData

section Harmonic

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
/-- The point of the W-model of the target of the image of a point. -/
lemma WData.map_pt {X Y : TempObj O R A} (m : X ⟶ Y) (D : WData x X.Lv) (D' : WData x Y.Lv)
    (z : X.Lv.Z) : (D.e.inv ≫ m.ψ ≫ D'.e.hom) (D.pt z) =
      D'.pt (specialFibreMap m.ψ m.ψ_toSpec z) := by
  have h : D.e.inv (D.e.hom z.1) = z.1 := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  simp only [WData.pt, Scheme.Hom.comp_apply, h]
  rfl

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] in
lemma WData.image_compSet {X Y : TempObj O R A} (m : X ⟶ Y) (D : WData x X.Lv)
    (D' : WData x Y.Lv) (C : Set X.Lv.Z) :
    (D.e.inv ≫ m.ψ ≫ D'.e.hom) '' D.compSet C =
      D'.compSet (specialFibreMap m.ψ m.ψ_toSpec '' C) := by
  rw [WData.compSet, WData.compSet, Set.image_image, Set.image_image]
  exact Set.image_congr fun z _ => WData.map_pt m D D' z

/-- **x-lengths are harmonic weights** along the map of special fibres of a morphism of the
tempered category between objects with W-model data (from (X0), (X2) of
`Statement.HarmonicX` and `Statement.NodeOfTwoComponents`). -/
theorem WData.isHarmonicWeight (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {X Y : TempObj O R A} (m : X ⟶ Y) (D : WData x X.Lv) (D' : WData x Y.Lv)
    [NoetherianSpace X.Lv.Z] [T0Space X.Lv.Z] [QuasiSober X.Lv.Z]
    [NoetherianSpace Y.Lv.Z] [T0Space Y.Lv.Z] [QuasiSober Y.Lv.Z]
    (hdim : topologicalKrullDim X.Lv.Z ≤ 1) (hdim' : topologicalKrullDim Y.Lv.Z ≤ 1) :
    CurveConfig.IsHarmonicWeight (curveConfig X.Lv.Z hdim) (curveConfig Y.Lv.Z hdim')
      (specialFibreMap m.ψ m.ψ_toSpec) (D.weight ϖ) (D'.weight ϖ) := by
  intro i₀ L y' a b hne hW hnd hnb hψL hint hc₀ hcl ha hb hab hy'S hy'a hy'b
  set ψ' := D.e.inv ≫ m.ψ ≫ D'.e.hom
  set ψs := specialFibreMap m.ψ m.ψ_toSpec
  by_cases hl' : ∃ l', SemistableReduction.ModelCode.IsXLength (D'.ϖL ϖ) D'.O' D'.ϖ' D'.c'
    D'.j₁ D'.xL (D'.pt y') l'
  swap
  · rw [WData.weight, dif_neg hl']
    exact zero_le
  rw [D'.weight_of_exists ϖ hl']
  obtain ⟨H0, -, H2, -⟩ := WData.isHarmonicX hX ϖ hϖ m D D'
  have hS : ∀ j : Fin L.length, L[j.1].1 ∈ (curveConfig X.Lv.Z hdim).S := fun j =>
    (hW.getElem j).1
  have hnode : ∀ j : Fin L.length,
      SemistableReduction.ModelCode.IsNodePt D.c' (D.pt L[j.1].1) := fun j =>
    D.isNodePt_of_mem_S hN (hS j)
  have hl : ∀ j : Fin L.length, ∃ l, SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O'
      D.ϖ' D.c' D.j₁ D.xL (D.pt L[j.1].1) l := fun j => (H0 _ (hnode j)).1
  let w : SemistableReduction.ModelCode.Walk D.c' :=
    { k := L.length
      v := fun j => D.compSet (CurveConfig.cget i₀ L j).1
      x := fun j => D.pt L[j.1].1
      mem_components := fun j => D.compSet_mem (CurveConfig.cget i₀ L j).2
      joins := fun j => by
        refine ⟨hnode j, ⟨_, (hW.getElem j).2.1, rfl⟩, ?_, .inl ?_⟩
        · rw [CurveConfig.cget_succ]
          exact ⟨_, (hW.getElem j).2.2, rfl⟩
        · rw [CurveConfig.cget_succ]
          intro h
          exact hnb.getElem j (Subtype.ext (D.compSet_injective h)) }
  have hy'node : SemistableReduction.ModelCode.IsNodePt D'.c' (D'.pt y') :=
    hN D'.K' D'.O' D'.ϖ' D'.hϖ' D'.c' D'.semistable (D'.pt y') _ (D'.compSet_mem a.2) _
      (D'.compSet_mem b.2) (fun h => hab (Subtype.ext (D'.compSet_injective h)))
      ⟨y', hy'a, rfl⟩ ⟨y', hy'b, rfl⟩
  have hcross : w.Crosses ψ' (D'.pt y') := by
    refine ⟨List.length_pos_iff.2 hne, fun i j hij => ?_, ?_, ?_, fun i h₀ hl => ?_,
      fun i => ?_⟩
    · have h := D.pt_injective hij
      have := (List.Nodup.getElem_inj_iff hnd (i := i.1) (j := j.1)
        (hi := by rw [List.length_map]; exact i.2)
        (hj := by rw [List.length_map]; exact j.2)).1 (by simpa using h)
      exact Fin.ext this
    · rintro ⟨y, hy⟩
      change ψ' '' D.compSet i₀.1 = {y} at hy
      rw [WData.image_compSet] at hy
      obtain ⟨z, hz⟩ := D'.compSet_eq_singleton hy
      exact hc₀ ⟨z, hz⟩
    · rintro ⟨y, hy⟩
      change ψ' '' D.compSet (CurveConfig.cget i₀ L (Fin.last _)).1 = {y} at hy
      rw [WData.image_compSet, CurveConfig.cget_last] at hy
      obtain ⟨z, hz⟩ := D'.compSet_eq_singleton hy
      exact hcl ⟨z, hz⟩
    · obtain ⟨p, hp, hpi⟩ := CurveConfig.cget_mem_dropLast i₀ L i h₀ hl
      change ψ' '' D.compSet (CurveConfig.cget i₀ L i).1 = _
      rw [WData.image_compSet, ← hpi]
      change D'.compSet (ψs '' (curveConfig X.Lv.Z hdim).C p.2) = _
      rw [hint p hp]
      simp [WData.compSet]
    · change ψ' (D.pt L[i.1].1) = _
      rw [WData.map_pt]
      exact congrArg D'.pt (hψL _ (List.getElem_mem _))
  have h0 : ψ' '' w.v 0 = D'.compSet a.1 := by
    change ψ' '' D.compSet i₀.1 = _
    rw [WData.image_compSet]
    exact congrArg D'.compSet ha
  have hlast : ψ' '' w.v (Fin.last w.k) = D'.compSet b.1 := by
    change ψ' '' D.compSet (CurveConfig.cget i₀ L (Fin.last _)).1 = _
    rw [WData.image_compSet, CurveConfig.cget_last]
    exact congrArg D'.compSet hb
  have key := H2 (D'.pt y') hy'node _ (D'.compSet_mem a.2) _ (D'.compSet_mem b.2)
    (fun h => hab (Subtype.ext (D'.compSet_injective h))) ⟨y', hy'a, rfl⟩ ⟨y', hy'b, rfl⟩ w
    hcross h0 hlast (fun j => (hl j).choose) (fun j => (hl j).choose_spec) _ hl'.choose_spec
  have hpos : ∀ j : Fin L.length, (0 : ℝ) ≤ ((hl j).choose : ℝ) := fun j =>
    Rat.cast_nonneg.2 ((H0 _ (hnode j)).2 _ (hl j).choose_spec).le
  calc ENNReal.ofReal (hl'.choose : ℝ)
      ≤ ENNReal.ofReal ((∑ j : Fin L.length, (hl j).choose : ℚ) : ℝ) :=
        ENNReal.ofReal_le_ofReal (by exact_mod_cast key)
    _ = ∑ j : Fin L.length, ENNReal.ofReal ((hl j).choose : ℝ) := by
        rw [Rat.cast_sum, ENNReal.ofReal_sum_of_nonneg fun j _ => hpos j]
    _ = ∑ j : Fin L.length, D.weight ϖ L[j.1].1 := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [D.weight_of_exists ϖ (hl j)]
    _ = (L.map fun p => D.weight ϖ p.1).sum :=
        Fin.sum_univ_fun_getElem L fun p => D.weight ϖ p.1

end Harmonic

end

end TemperedFundamentalGroups
