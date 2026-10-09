/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.WModelPoints
import TemperedFundamentalGroups.SemistableReduction.CrossingTarget
import TemperedFundamentalGroups.SemistableReduction.NodeDivisors
import TemperedFundamentalGroups.SemistableReduction.CompositeZero

/-!
# Components and nodes of the source (Blueprint §10.3.8, CrossingX1, CX6)

For a split W-model `c` without loops:

* `gp`: the generic point of a component; valuation subrings centred there contain the germs of
  all points of the component and have `ϖ` in their maximal ideal;
* `nodeCore`: the germs at a node form a noetherian local node core, with the divisor lemma;
* `unit_or_unit_node`: on each component through a node exactly one node coordinate is a unit,
  and distinct components have distinct unit coordinates (`unit_ne_node`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {c : TemperedFundamentalGroups.ModelCode O}

/-- The generic point of a component. -/
noncomputable def gp {v : Set c.scheme} (hv : v ∈ components c) : c.scheme :=
  hv.1.genericPoint

lemma closure_gp {v : Set c.scheme} (hv : v ∈ components c) : closure {gp hv} = v := by
  have := hv.1.isGenericPoint_genericPoint_closure
  rwa [(isClosed_of_mem_components hv).closure_eq] at this

lemma gp_specializes {v : Set c.scheme} (hv : v ∈ components c) {z : c.scheme} (hz : z ∈ v) :
    gp hv ⤳ z := by
  rw [specializes_iff_mem_closure, closure_gp]; exact hz

lemma gp_mem {v : Set c.scheme} (hv : v ∈ components c) : gp hv ∈ v := by
  have h := subset_closure (s := {gp hv}) (Set.mem_singleton _)
  rwa [closure_gp hv] at h

omit [IsDiscreteValuationRing O] in
/-- A component containing the closure of a point of the special fibre is that closure. -/
lemma eq_of_subset {v w : Set c.scheme} (hv : v ∈ components c) (hw : w ∈ components c)
    (h : v ⊆ w) : v = w :=
  (hv.2.2 w hw.1 hw.2.1 h).symm

/-- A point of a component is its generic point only if it lies on no other component. -/
lemma gp_ne_of_two {v w₁ w₂ : Set c.scheme} (hv : v ∈ components c) (hw₁ : w₁ ∈ components c)
    (hw₂ : w₂ ∈ components c) (hne : w₁ ≠ w₂) {z : c.scheme} (h₁ : z ∈ w₁) (h₂ : z ∈ w₂) :
    gp hv ≠ z := by
  intro heq
  have hs : ∀ w ∈ components c, z ∈ w → v ⊆ w := fun w hw hzw ↦ by
    rw [← closure_gp hv, heq]
    exact closure_minimal (Set.singleton_subset_iff.2 hzw) (isClosed_of_mem_components hw)
  exact hne ((eq_of_subset hv hw₁ (hs w₁ hw₁ h₁)).symm.trans (eq_of_subset hv hw₂ (hs w₂ hw₂ h₂)))

variable {L : Type u} [Field L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] {x : L}
  {j : Spec (CommRingCat.of L) ⟶ c.scheme}

variable (hW : IsWModel O L x c j)
include hW

omit [IsDiscreteValuationRing O] in
/-- Valuation subrings centred at points contain the germs of their specializations. -/
lemma germs_le {V : ValuationSubring L} {η z : c.scheme} (hV : IsCentre j V η) (h : η ⤳ z) :
    ∀ f ∈ germs c j z, f ∈ V := fun _ hf ↦
  ((isCentre_iff_dominates c j (specializes_of_isWModel hW η) V).1 hV).1
    (germs_anti c j h hf)

/-- `ϖ` is in the maximal ideal at points of the special fibre. -/
lemma valuation_ϖ_lt_one {ϖ : O} (hϖ : Irreducible ϖ) {V : ValuationSubring L}
    {z : c.scheme} (hz : z ∈ Z c) (hV : IsCentre j V z) : V.valuation (algebraMap O L ϖ) < 1 := by
  rw [← baseHom_eq_of_isWModel hW]
  exact valuation_baseHom_lt_one hϖ c j hz hV

omit [IsDiscreteValuationRing O] in
/-- Elements of the base are in all germs. -/
lemma algebraMap_mem_germs (z : c.scheme) (o : O) : algebraMap O L o ∈ germs c j z := by
  rw [← baseHom_eq_of_isWModel hW]; exact baseHom_mem_germs c j z o

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
