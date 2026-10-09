/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.WHarmonicWeight
import TemperedFundamentalGroups.Topology.HeightLength

/-!
# Edge lifting with x-lengths on the special fibres of levels (Blueprint §10.3.8, I6)

For a morphism `m : X ⟶ Y` of the tempered category with W-model data `D`, `D'` on both levels,
(X1) of `Statement.HarmonicX` gives **edge lifting with lengths** along the map of special fibres
(`CurveConfig.IsEdgeLifting`, `WData.isEdgeLifting`): every non-contracted component over a
component through a special point `y'` starts a walk of the incidence graph crossing `y'` to a
component over the other component through `y'`, of total x-length the x-length of `y'`. With
`CurveConfig.isWalkLifting_of_isEdgeLifting` this lifts walks of the tree coverings.

* `WData.exists_compSet_eq`: every component of the dual graph of the W-model is the image of
  an irreducible component of the special fibre of the level;
* `CurveConfig.incWalk_ofFn`: walks of the incidence graph from finite families.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open scoped ENNReal

namespace TemperedFundamentalGroups

noncomputable section

namespace CurveConfig

variable {Z : Type*} [TopologicalSpace Z] {ι : Type*} {K : CurveConfig Z ι}

/-- The walk of the incidence graph through the components `c j` and special points `s j`. -/
lemma incWalk_ofFn : ∀ (k : ℕ) (c : Fin (k + 1) → ι) (s : Fin k → Z),
    (∀ j, s j ∈ K.S ∧ s j ∈ K.C (c j.castSucc) ∧ s j ∈ K.C (c j.succ)) →
    IncWalk K (c 0) (List.ofFn fun j => (s j, c j.succ)) ∧
      lastLab (c 0) (List.ofFn fun j => (s j, c j.succ)) = c (Fin.last k)
  | 0, c, s, _ => ⟨trivial, rfl⟩
  | k + 1, c, s, hs => by
    obtain ⟨ih₁, ih₂⟩ := incWalk_ofFn k (fun j => c j.succ) (fun j => s j.succ)
      (fun j => ⟨(hs j.succ).1, (hs j.succ).2.1, (hs j.succ).2.2⟩)
    rw [List.ofFn_succ]
    exact ⟨⟨(hs 0).1, (hs 0).2.1, (hs 0).2.2, ih₁⟩, ih₂⟩

lemma mem_dropLast_ofFn {α : Type*} {k : ℕ} {f : Fin k → α} {p : α}
    (hp : p ∈ (List.ofFn f).dropLast) : ∃ j : Fin k, j.1 + 1 < k ∧ p = f j := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
  have hlen : (List.ofFn f).dropLast.length = k - 1 := by simp
  rw [hlen] at hi
  refine ⟨⟨i, by omega⟩, by simp only; omega, ?_⟩
  rw [List.getElem_dropLast, List.getElem_ofFn]

end CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {x : R}

namespace WData

variable {Lv : Level O R A} (D : WData x Lv) [IsDiscreteValuationRing O]

/-- **Every component of the W-model comes from an irreducible component of the special fibre of
the level.** -/
lemma exists_compSet_eq [NoetherianSpace Lv.Z] {v : Set D.c'.scheme}
    (hv : v ∈ SemistableReduction.ModelCode.components D.c') :
    ∃ C : irreducibleComponents Lv.Z, D.compSet C.1 = v := by
  have hvZ : D.e.inv '' v ⊆ specialFibre Lv.c.toSpec := by
    rintro _ ⟨y, hy, rfl⟩
    rw [D.mem_Z_iff]
    simpa [← Scheme.Hom.comp_apply] using hv.2.1 hy
  have hirr := isIrreducible_preimage_val (hv.1.image _ D.e.inv.continuous.continuousOn) hvZ
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  refine ⟨⟨C, hC⟩, (hv.2.2 _ (D.compSet_mem hC).1 (D.compSet_mem hC).2.1 fun y hy => ?_)⟩
  have hy' : D.e.inv y ∈ specialFibre Lv.c.toSpec := hvZ ⟨y, hy, rfl⟩
  refine ⟨⟨D.e.inv y, hy'⟩, hsub ⟨y, hy, rfl⟩, ?_⟩
  simp [pt, ← Scheme.Hom.comp_apply]

/-- Points of the special fibre of the W-model come from the special fibre of the level. -/
lemma exists_pt_eq {y : D.c'.scheme} (hy : y ∈ SemistableReduction.ModelCode.Z D.c') :
    ∃ z : Lv.Z, D.pt z = y := by
  refine ⟨⟨D.e.inv y, ?_⟩, ?_⟩
  · rw [D.mem_Z_iff]; simpa [← Scheme.Hom.comp_apply] using hy
  · simp [pt, ← Scheme.Hom.comp_apply]

omit [IsDiscreteValuationRing O] in
lemma compSet_singleton (z : Lv.Z) : D.compSet {z} = {D.pt z} := by
  simp [compSet]

end WData

section Lifting

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

/-- A component through a point lying on a second component is not a point. -/
lemma not_isContracted_of_two {O' : Type u} [CommRing O'] [IsLocalRing O']
    {c : TemperedFundamentalGroups.ModelCode O'} {v w : Set c.scheme}
    (hv : v ∈ SemistableReduction.ModelCode.components c)
    (hw : w ∈ SemistableReduction.ModelCode.components c) (hvw : v ≠ w) {y : c.scheme}
    (hyv : y ∈ v) (hyw : y ∈ w) : ¬ ∃ z, v = {z} := by
  rintro ⟨z, rfl⟩
  obtain rfl : y = z := hyv
  exact hvw (hv.2.2 _ hw.1 hw.2.1 (Set.singleton_subset_iff.2 hyw)).symm

/-- **x-lengths of nodes are unique** ((X2) of `Statement.HarmonicX` for the identity, on a
walk with one node). -/
theorem WData.isXLength_unique (hX : SemistableReduction.Statement.HarmonicXS.{u}) (ϖ : O)
    (hϖ : Irreducible ϖ) {X : TempObj O R A} (D : WData x X.Lv) {y : D.c'.scheme}
    (hy : SemistableReduction.ModelCode.IsNodePt D.c' y) {l l' : ℚ}
    (hl : SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O' D.ϖ' D.c' D.j₁ D.xL y l)
    (hl' : SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O' D.ϖ' D.c' D.j₁ D.xL y l') :
    l = l' := by
  obtain ⟨-, -, H2, -⟩ := WData.isHarmonicX hX ϖ hϖ (𝟙 X) D D
  obtain ⟨v₁, hv₁, v₂, hv₂, h₁₂, hy₁, hy₂⟩ := D.noLoops y hy
  have hid : D.e.inv ≫ (𝟙 X : X ⟶ X).ψ ≫ D.e.hom = 𝟙 _ := by
    simp
  have key : ∀ {a b : ℚ},
      SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O' D.ϖ' D.c' D.j₁ D.xL y a →
      SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O' D.ϖ' D.c' D.j₁ D.xL y b → a ≤ b := by
    intro a b ha hb
    let w : SemistableReduction.ModelCode.Walk D.c' :=
      { k := 1
        v := ![v₁, v₂]
        x := ![y]
        mem_components := fun j => by fin_cases j <;> simpa
        joins := fun j => by
          fin_cases j
          exact ⟨hy, hy₁, hy₂, .inl h₁₂⟩ }
    have hcross : w.Crosses (D.e.inv ≫ (𝟙 X : X ⟶ X).ψ ≫ D.e.hom) y := by
      rw [hid]
      refine ⟨le_rfl, fun i j _ => Subsingleton.elim i j, ?_, ?_, fun i h₀ hl => ?_,
        fun i => by fin_cases i; rfl⟩
      · rintro ⟨z, hz⟩
        exact not_isContracted_of_two hv₁ hv₂ h₁₂ hy₁ hy₂ ⟨z, by simpa [w] using hz⟩
      · rintro ⟨z, hz⟩
        exact not_isContracted_of_two hv₂ hv₁ h₁₂.symm hy₂ hy₁ ⟨z, by simpa [w] using hz⟩
      · exact absurd (show i = Fin.last 1 by fin_cases i <;> simp_all) hl
    exact H2 y hy v₁ hv₁ v₂ hv₂ h₁₂ hy₁ hy₂ w hcross (by rw [hid]; simp [w])
      (by rw [hid]; simp [w]) ![b] (fun j => by fin_cases j; exact hb) a ha |>.trans
      (by simp)
  exact le_antisymm (key hl hl') (key hl' hl)

/-- **x-lengths give edge lifting** along the map of special fibres of a morphism of the
tempered category between objects with W-model data ((X0), (X1) of `Statement.HarmonicX` and
`Statement.NodeOfTwoComponents`). -/
theorem WData.isEdgeLifting (hX : SemistableReduction.Statement.HarmonicXS.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u}) (ϖ : O) (hϖ : Irreducible ϖ)
    {X Y : TempObj O R A} (m : X ⟶ Y) (D : WData x X.Lv) (D' : WData x Y.Lv)
    [NoetherianSpace X.Lv.Z] [T0Space X.Lv.Z] [QuasiSober X.Lv.Z]
    [NoetherianSpace Y.Lv.Z] [T0Space Y.Lv.Z] [QuasiSober Y.Lv.Z]
    (hdim : topologicalKrullDim X.Lv.Z ≤ 1) (hdim' : topologicalKrullDim Y.Lv.Z ≤ 1) :
    CurveConfig.IsEdgeLifting (curveConfig X.Lv.Z hdim) (curveConfig Y.Lv.Z hdim')
      (specialFibreMap m.ψ m.ψ_toSpec) (D.weight ϖ) (D'.weight ϖ) := by
  classical
  intro i₀ y' a b hc₀ ha hab hy'S hy'a hy'b
  set ψ' := D.e.inv ≫ m.ψ ≫ D'.e.hom
  set ψs := specialFibreMap m.ψ m.ψ_toSpec
  obtain ⟨H0, H1, -, -⟩ := WData.isHarmonicX hX ϖ hϖ m D D'
  obtain ⟨H0', -⟩ := WData.isHarmonicX hX ϖ hϖ (𝟙 Y) D' D'
  have hy'node : SemistableReduction.ModelCode.IsNodePt D'.c' (D'.pt y') :=
    hN D'.K' D'.O' D'.ϖ' D'.hϖ' D'.c' D'.semistable (D'.pt y') _ (D'.compSet_mem a.2) _
      (D'.compSet_mem b.2) (fun h => hab (Subtype.ext (D'.compSet_injective h)))
      ⟨y', hy'a, rfl⟩ ⟨y', hy'b, rfl⟩
  obtain ⟨hl', -⟩ := H0' _ hy'node
  have hv : ψ' '' D.compSet i₀.1 = D'.compSet a.1 := by
    rw [WData.image_compSet]; exact congrArg D'.compSet ha
  obtain ⟨w, hw0, hcross, hwlast, l, hl, hsum⟩ := H1 (D'.pt y') hy'node _ (D'.compSet_mem a.2) _
    (D'.compSet_mem b.2) (fun h => hab (Subtype.ext (D'.compSet_injective h)))
    ⟨y', hy'a, rfl⟩ ⟨y', hy'b, rfl⟩ _ (D.compSet_mem i₀.2) hv _ hl'.choose_spec
  obtain ⟨hk, hinj, hnc₀, hncl, hinner, hxy⟩ := hcross
  -- components and special points of the walk
  have hcomp : ∀ j, ∃ C : irreducibleComponents X.Lv.Z, D.compSet C.1 = w.v j := fun j =>
    D.exists_compSet_eq (w.mem_components j)
  choose cc hcc using hcomp
  have hpt : ∀ j : Fin w.k, ∃ z : X.Lv.Z, D.pt z = w.x j := fun j =>
    D.exists_pt_eq (w.joins j).1.1
  choose ss hss using hpt
  have hc0 : cc 0 = i₀ := Subtype.ext (D.compSet_injective ((hcc 0).trans hw0))
  have hmem : ∀ j, ss j ∈ (cc j.castSucc).1 ∧ ss j ∈ (cc j.succ).1 := fun j => by
    obtain ⟨-, h₁, h₂, -⟩ := w.joins j
    rw [← hss j, ← hcc] at h₁ h₂
    exact ⟨D.pt_mem_compSet_iff.1 h₁, D.pt_mem_compSet_iff.1 h₂⟩
  have hS : ∀ j, ss j ∈ (curveConfig X.Lv.Z hdim).S := fun j => by
    obtain ⟨hnode, h₁, h₂, h₃⟩ := w.joins j
    rcases h₃ with hne | honly
    · exact ⟨_, _, fun h => hne (by rw [← hcc, ← hcc, h]), (hmem j).1, (hmem j).2⟩
    · obtain ⟨v₁, hv₁, v₂, hv₂, hv₁₂, hx₁, hx₂⟩ := D.noLoops _ hnode
      exact absurd ((honly v₁ hv₁ hx₁).trans (honly v₂ hv₂ hx₂).symm) hv₁₂
  obtain ⟨hW, hlast⟩ := CurveConfig.incWalk_ofFn (K := curveConfig X.Lv.Z hdim) w.k cc ss
    fun j => ⟨hS j, (hmem j).1, (hmem j).2⟩
  rw [hc0] at hW hlast
  have himgC : ∀ j, D'.compSet (ψs '' (cc j).1) = ψ' '' w.v j := fun j => by
    rw [← hcc, WData.image_compSet]
  refine ⟨_, hW, fun p hp => ?_, fun p hp => ?_, ?_, ?_, ?_⟩
  · obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hp
    apply D'.pt_injective
    rw [← WData.map_pt m D D', hss, hxy]
  · obtain ⟨j, hj, rfl⟩ := CurveConfig.mem_dropLast_ofFn hp
    apply D'.compSet_injective
    change D'.compSet (ψs '' (cc j.succ).1) = D'.compSet {y'}
    rw [himgC, D'.compSet_singleton]
    exact hinner _ (Fin.succ_ne_zero _) (fun h => by
      have := congrArg Fin.val h; simp at this; omega)
  · rw [hlast]
    rintro ⟨y, hy⟩
    apply hncl
    refine ⟨D'.pt y, ?_⟩
    rw [← himgC, show ψs '' (cc (Fin.last w.k)).1 = {y} from hy, D'.compSet_singleton]
  · rw [hlast]
    apply D'.compSet_injective
    change D'.compSet (ψs '' (cc (Fin.last w.k)).1) = _
    rw [himgC, hwlast]
    rfl
  · -- the weights
    have hpos : ∀ j : Fin w.k, (0 : ℝ) ≤ (l j : ℝ) := fun j => by
      have hnd : SemistableReduction.ModelCode.IsNodePt D.c' (w.x j) := by
        rw [← hss j]; exact D.isNodePt_of_mem_S hN (hS j)
      exact Rat.cast_nonneg.2 ((H0 _ hnd).2 _ (hl j)).le
    have hwj : ∀ j, D.weight ϖ (ss j) = ENNReal.ofReal (l j : ℝ) := fun j => by
      have hex : ∃ l, SemistableReduction.ModelCode.IsXLength (D.ϖL ϖ) D.O' D.ϖ' D.c' D.j₁
          D.xL (D.pt (ss j)) l := ⟨l j, by rw [hss j]; exact hl j⟩
      rw [D.weight_of_exists ϖ hex]
      congr 2
      have hnd : SemistableReduction.ModelCode.IsNodePt D.c' (D.pt (ss j)) :=
        D.isNodePt_of_mem_S hN (hS j)
      exact_mod_cast WData.isXLength_unique hX ϖ hϖ D hnd hex.choose_spec
        (by rw [hss j]; exact hl j)
    rw [D'.weight_of_exists ϖ hl', List.map_ofFn, List.sum_ofFn]
    simp only [Function.comp_def, hwj]
    rw [← ENNReal.ofReal_sum_of_nonneg fun j _ => hpos j]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Rat.cast_sum, hsum]

end Lifting

end

end TemperedFundamentalGroups
