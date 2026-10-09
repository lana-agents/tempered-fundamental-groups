/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateNodePoints
import TemperedFundamentalGroups.Andre.TateLoop
import TemperedFundamentalGroups.Andre.TateG1
import TemperedFundamentalGroups.Andre.WEdgeLifting

/-!
# The Tate model as a target of `CrossingX1` (HarmonicTate glue)

The target of `Statement.CrossingX1` for `HarmonicTate` is the projective model
`TateObject.tgtModel T = projModelCode O hf` of the function field of the Tate curve, identified
with the Tate model by `TateNormal.modelIso`.

* `TateObject.tpt`, `TateObject.tSet`: points and subsets of the special fibre of `X₀` as points
  and subsets of `tgtModel T`; `tSet_mem`: irreducible components go to components;
* `TateObject.mem_irreducibleComponents_C`, `mem_irreducibleComponents_E`: the line `C` and (for
  `b₆` a unit) the conic `E` are irreducible components of the special fibre;
* `Pres.tateψ`: the model map `c' ⟶ tgtModel T` of a member `Q` with `a : Q.U ⟶ X₀`
  (`c'` the W-model of `Q`), with `Pres.tateψ_image_compSet`;
* `Pres.exists_incWalk_of_crosses`: a walk of the dual graph of the W-model crossing a point of
  `tgtModel T` gives a walk of the incidence graph of the special fibre with special points over
  that point.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace
open SemistableReduction.ProjScheme

namespace TemperedFundamentalGroups

noncomputable section

open TempObj CurveConfig TateObject

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A]
  [MulSemiringAction A R] [Subsingleton A] {x : R}
  (T : TateObject.Data O R) [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))]

namespace TateObject

/-- The projective model of the function field of the Tate curve (the Tate model). -/
abbrev tgtModel : ModelCode O :=
  projModelCode O (TateNormal.hcoords T.π T.b₄ T.b₆ T.π_ne_zero)

/-- The identification of the Tate model with `tgtModel T`. -/
abbrev tIso : (X₀ (A := A) T).Lv.c.scheme ≅ (tgtModel T).scheme :=
  TateNormal.modelIso T.π T.b₄ T.b₆ T.π_ne_zero

/-- A point of the special fibre of `X₀` as a point of `tgtModel T`. -/
def tpt (z : (X₀ (A := A) T).Lv.Z) : (tgtModel T).scheme := (tIso (A := A) T).hom z.1

/-- A subset of the special fibre of `X₀` as a subset of `tgtModel T`. -/
def tSet (S : Set (X₀ (A := A) T).Lv.Z) : Set (tgtModel T).scheme := tpt (A := A) T '' S

lemma tpt_injective : Function.Injective (tpt (A := A) T) := fun a b h => Subtype.ext (by
  have := congrArg (tIso (A := A) T).inv h
  simpa [tpt, ← Scheme.Hom.comp_apply] using this)

lemma tSet_injective : Function.Injective (tSet (A := A) T) :=
  Set.image_injective.2 (tpt_injective T)

lemma tpt_mem_tSet_iff {S : Set (X₀ (A := A) T).Lv.Z} {z : (X₀ (A := A) T).Lv.Z} :
    tpt (A := A) T z ∈ tSet (A := A) T S ↔ z ∈ S :=
  (tpt_injective T).mem_set_image

lemma continuous_tpt : Continuous (tpt (A := A) T) :=
  (tIso (A := A) T).hom.continuous.comp continuous_subtype_val

lemma tIso_toSpec :
    (tIso (A := A) T).hom ≫ (tgtModel T).toSpec = (X₀ (A := A) T).Lv.c.toSpec :=
  TateNormal.modelIso_hom_toSpec T.π T.b₄ T.b₆ T.π_ne_zero

lemma mem_Z_iff (y : (X₀ (A := A) T).Lv.c.scheme) :
    y ∈ specialFibre (X₀ (A := A) T).Lv.c.toSpec ↔
      (tIso (A := A) T).hom y ∈ SemistableReduction.ModelCode.Z (tgtModel T) := by
  rw [mem_specialFibre, ← tIso_toSpec, Scheme.Hom.comp_apply]
  rfl

/-- Irreducible components of the special fibre give components of `tgtModel T`. -/
lemma tSet_mem {C : Set (X₀ (A := A) T).Lv.Z}
    (hC : C ∈ irreducibleComponents (X₀ (A := A) T).Lv.Z) :
    tSet (A := A) T C ∈ SemistableReduction.ModelCode.components (tgtModel T) := by
  refine ⟨hC.1.image _ (continuous_tpt T).continuousOn, ?_, fun w hw hwZ hCw => ?_⟩
  · rintro _ ⟨z, -, rfl⟩
    exact (mem_Z_iff T z.1).1 z.2
  · have hwZ' : (tIso (A := A) T).inv '' w ⊆ specialFibre (X₀ (A := A) T).Lv.c.toSpec := by
      rintro _ ⟨y, hy, rfl⟩
      rw [mem_Z_iff]
      simpa [← Scheme.Hom.comp_apply] using hwZ hy
    have hirr := WData.isIrreducible_preimage_val
      (hw.image _ (tIso (A := A) T).inv.continuous.continuousOn) hwZ'
    have hsub : C ⊆ (↑) ⁻¹' ((tIso (A := A) T).inv '' w) := fun z hz =>
      ⟨tpt (A := A) T z, hCw ⟨z, hz, rfl⟩, by simp [tpt, ← Scheme.Hom.comp_apply]⟩
    have heq := hC.2 hirr hsub
    apply subset_antisymm _ hCw
    intro y hy
    have hy' : (tIso (A := A) T).inv y ∈ specialFibre (X₀ (A := A) T).Lv.c.toSpec :=
      hwZ' ⟨y, hy, rfl⟩
    refine ⟨⟨(tIso (A := A) T).inv y, hy'⟩, heq ⟨y, hy, rfl⟩, ?_⟩
    simp [tpt, ← Scheme.Hom.comp_apply]

/-- `closure {z}` is an irreducible component if a closed set avoiding `z` covers the rest. -/
lemma closure_mem_irreducibleComponents {Z : Type*} [TopologicalSpace Z] {z : Z} {S : Set Z}
    (hS : IsClosed S) (hcov : closure {z} ∪ S = univ) (hz : z ∉ S) :
    closure {z} ∈ irreducibleComponents Z := by
  refine ⟨isIrreducible_singleton.closure, fun W hW hsub => ?_⟩
  rcases isPreirreducible_iff_isClosed_union_isClosed.1 hW.isPreirreducible _ _
    isClosed_closure hS (by rw [hcov]; exact subset_univ _) with h | h
  · exact h
  · exact absurd (h (hsub (subset_closure rfl))) hz

omit [IsDiscreteValuationRing O] [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
lemma mem_irreducibleComponents_C :
    (decomp (A := A) T).C ∈ irreducibleComponents (X₀ (A := A) T).Lv.Z := by
  obtain ⟨zC, hC, hE⟩ := TateModel.exists_closure_eq_Cset (b₄ := T.b₄) (b₆ := T.b₆) T.π_mem
  have h : closure ({zC} : Set (TateModel.Z T.π T.b₄ T.b₆)) ∈
      irreducibleComponents (TateModel.Z T.π T.b₄ T.b₆) :=
    closure_mem_irreducibleComponents (decomp (A := A) T).isClosed_E
      (by rw [hC]; exact (decomp (A := A) T).union) hE
  rw [hC] at h
  exact h

omit [IsDiscreteValuationRing O] [Fact (Squarefree (TateNormal.dpoly T.π T.b₄ T.b₆))] in
lemma mem_irreducibleComponents_E (hb : IsUnit T.b₆) :
    (decomp (A := A) T).E ∈ irreducibleComponents (X₀ (A := A) T).Lv.Z := by
  obtain ⟨zE, hE, hC⟩ := TateModel.exists_closure_eq_Eset (b₄ := T.b₄) T.π_mem hb
  have h : closure ({zE} : Set (TateModel.Z T.π T.b₄ T.b₆)) ∈
      irreducibleComponents (TateModel.Z T.π T.b₄ T.b₆) :=
    closure_mem_irreducibleComponents (decomp (A := A) T).isClosed_C
      (by rw [hE, union_comm]; exact (decomp (A := A) T).union) hC
  rw [hE] at h
  exact h

end TateObject

namespace Pres

variable {Y : TempObj O R A} (Q : Pres x Y) (a : Q.U ⟶ X₀ (A := A) T)

/-- The model map from the W-model of a member to the Tate model `tgtModel T`. -/
def tateψ : Q.D.c'.scheme ⟶ (tgtModel T).scheme := Q.D.e.inv ≫ a.ψ ≫ (tIso (A := A) T).hom

lemma tateψ_pt (z : Q.Lv.Z) :
    Q.tateψ T a (Q.D.pt z) = tpt (A := A) T (specialFibreMap a.ψ a.ψ_toSpec z) := by
  have h : Q.D.e.inv (Q.D.e.hom z.1) = z.1 := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  simp only [tateψ, WData.pt, Scheme.Hom.comp_apply, h]
  rfl

lemma tateψ_image_compSet (S : Set Q.Lv.Z) :
    Q.tateψ T a '' Q.D.compSet S = tSet (A := A) T (specialFibreMap a.ψ a.ψ_toSpec '' S) := by
  rw [WData.compSet, tSet, Set.image_image, Set.image_image]
  exact Set.image_congr fun z _ => Q.tateψ_pt T a z

/-- **Walks crossing a point of the Tate model give walks of the incidence graph** with special
points over that point. -/
lemma exists_incWalk_of_crosses (w : SemistableReduction.ModelCode.Walk Q.D.c')
    (i₀ : irreducibleComponents Q.Lv.Z) (hw0 : w.v 0 = Q.D.compSet i₀.1)
    {y' : (tgtModel T).scheme} (hcross : w.Crosses (Q.tateψ T a) y') :
    ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i₀ L ∧
      (∀ p ∈ L, tpt (A := A) T (specialFibreMap a.ψ a.ψ_toSpec p.1) = y') ∧
      Q.tateψ T a '' w.v (Fin.last w.k) =
        tSet (A := A) T (specialFibreMap a.ψ a.ψ_toSpec ''
          (curveConfig Q.Lv.Z Q.hdim).C (lastLab i₀ L)) := by
  classical
  obtain ⟨-, -, -, -, -, hxy⟩ := hcross
  have hcomp : ∀ j, ∃ C : irreducibleComponents Q.Lv.Z, Q.D.compSet C.1 = w.v j := fun j =>
    Q.D.exists_compSet_eq (w.mem_components j)
  choose cc hcc using hcomp
  have hpt : ∀ j : Fin w.k, ∃ z : Q.Lv.Z, Q.D.pt z = w.x j := fun j =>
    Q.D.exists_pt_eq (w.joins j).1.1
  choose ss hss using hpt
  have hc0 : cc 0 = i₀ := Subtype.ext (Q.D.compSet_injective ((hcc 0).trans hw0))
  have hmem : ∀ j, ss j ∈ (cc j.castSucc).1 ∧ ss j ∈ (cc j.succ).1 := fun j => by
    obtain ⟨-, h₁, h₂, -⟩ := w.joins j
    rw [← hss j, ← hcc] at h₁ h₂
    exact ⟨Q.D.pt_mem_compSet_iff.1 h₁, Q.D.pt_mem_compSet_iff.1 h₂⟩
  have hS : ∀ j, ss j ∈ (curveConfig Q.Lv.Z Q.hdim).S := fun j => by
    obtain ⟨hnode, h₁, h₂, h₃⟩ := w.joins j
    rcases h₃ with hne | honly
    · exact ⟨_, _, fun h => hne (by rw [← hcc, ← hcc, h]), (hmem j).1, (hmem j).2⟩
    · obtain ⟨v₁, hv₁, v₂, hv₂, hv₁₂, hx₁, hx₂⟩ := Q.D.noLoops _ hnode
      exact absurd ((honly v₁ hv₁ hx₁).trans (honly v₂ hv₂ hx₂).symm) hv₁₂
  obtain ⟨hW, hlast⟩ := CurveConfig.incWalk_ofFn (K := curveConfig Q.Lv.Z Q.hdim) w.k cc ss
    fun j => ⟨hS j, (hmem j).1, (hmem j).2⟩
  rw [hc0] at hW hlast
  refine ⟨_, hW, fun p hp => ?_, ?_⟩
  · obtain ⟨j, hj⟩ := List.mem_ofFn.1 hp
    rw [← hj]
    change tpt (A := A) T (specialFibreMap a.ψ a.ψ_toSpec (ss j)) = y'
    rw [← Q.tateψ_pt T a, hss, hxy]
  · rw [hlast, ← hcc, Q.tateψ_image_compSet T a]
    rfl

end Pres

end

end TemperedFundamentalGroups
