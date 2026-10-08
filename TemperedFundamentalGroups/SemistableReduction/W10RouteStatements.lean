/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10TreeStatement
import TemperedFundamentalGroups.SemistableReduction.DVRDescentDisc
import TemperedFundamentalGroups.SemistableReduction.TreeBridge

/-!
# The pointwise descent statements consumed by the routing of G4

Blueprint §9.7a, step 4; §9.12 (O1, O7). The routing of the points of the normalized tree model
over `E` (`W10Route`) reduces `W10.TreeChartsSemistable` to two **pointwise descent statements**
about a single normalized chart. These statements are open; this file contains only the
definitions, so that they can be taken as named hypotheses.

* `W10Route.SmoothDescentStatement` (smooth points, owner: the W10 smooth-descent agent): for
  `G / C(x)` with generators `T`, there is a finite `S ⊆ C` such that for every complete
  discretely valued `E ⊇ S` (`C` algebraic over `E`) and every `E`-form `F₀` of `G`, every point
  `P'` of the vertex chart `DRint 0 1 (Aff β 1 G)` over the residue point `x̄ = β̄` (`‖β‖ ≤ 1`, the
  chart `O_C[x - β] = O_C[x]`) at which the special fibre over `C` is smooth (`IsDiscSmooth`)
  restricts to a semistable point of `DRint 0 1 F₀` over `O_E`. `S` does not depend on `β`.
* `W10Route.NodeDescentStatement` (node points, owner: the O1 agent): the same for the points of
  the node chart `Rint c₀ G` over the node which are ordinary double points over `C`
  (`IsNodeODP`).

The restriction maps are `ιβ : DRint 0 1 F₀ → DRint 0 1 (Aff β 1 G)` and
`ιN : Rint c₀E F₀ → Rint c₀ G`, both `y ↦ χ y`.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section Maps

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

/-- `O[y] = O[y - k]` for `‖k‖ ≤ 1`. -/
lemma polyChart_sub {F : Type u} [Field F] [Algebra C F] (y : F) {k : C} (hk : ‖k‖ ≤ 1) :
    polyChart ν (y - algebraMap C F k) = polyChart ν y := by
  have hkv : ν k ≤ 1 := by
    rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
    simpa using hk
  have hk₁ : ∀ y' : F, algebraMap C F k ∈ polyChart ν y' := fun y' ↦
    algebraMap_mem_of_le_one (v := ν) (baseRing_le_polyChart (v := ν) y') hkv
  apply le_antisymm
  · refine polyChart_le (baseRing_le_polyChart _) ?_
    exact Subring.sub_mem _ (self_mem_polyChart _) (hk₁ y)
  · refine polyChart_le (baseRing_le_polyChart _) ?_
    have := Subring.add_mem _ (self_mem_polyChart (v := ν) (y - algebraMap C F k)) (hk₁ _)
    rwa [sub_add_cancel] at this

variable {G : Type*} [Field G] [Algebra (RatFunc C) G]

/-- **The vertex chart is translation invariant**: for `‖β‖ ≤ 1`, `DRint 0 1 G` and
`DRint 0 1 (Aff β 1 G)` (the integral closures of `O_C[x]` and `O_C[x - β]`) have the same
elements. -/
theorem mem_drint_aff_iff {β : C} (hβ : ‖β‖ ≤ 1) (z : G) :
    toAff (a := β) (c := (1 : C)) one_ne_zero z ∈ DRint (0 : C) 1 (Aff β 1 one_ne_zero G) ↔
      z ∈ DRint (0 : C) 1 G := by
  have h₁ := map_drint_aff (a := β) (F' := G) one_ne_zero
  have h₂ := drint_eq (a := (0 : C)) (c := (1 : C)) (F' := G) one_ne_zero
  have hc : coord (RatFunc.X : RatFunc C) β (1 : C) =
      coord (RatFunc.X : RatFunc C) (0 : C) (1 : C) - algebraMap C (RatFunc C) β := by
    simp [coord]
  rw [hc, polyChart_sub _ hβ, ← h₂] at h₁
  constructor
  · intro h
    change z ∈ (DRint (0 : C) 1 G).toSubring
    rw [← h₁]
    exact ⟨_, h, rfl⟩
  · intro h
    change z ∈ (DRint (0 : C) 1 G).toSubring at h
    rw [← h₁] at h
    obtain ⟨w, hw, rfl⟩ := h
    exact hw

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* G}

variable (χ) in
/-- The restriction `DRint 0 1 F₀ → DRint 0 1 (Aff β 1 G)`, `y ↦ χ y`, of the vertex chart over
`O_E` to the vertex chart over `O_C` in the coordinate `x - β` (`‖β‖ ≤ 1`). -/
noncomputable def ιβ (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : DVRDescent.IsCompat φ χ) {β : C}
    (hβ : ‖β‖ ≤ 1) :
    DRint (0 : E) 1 F₀ →+* DRint (0 : C) 1 (Aff β 1 one_ne_zero G) where
  toFun y := ⟨toAff one_ne_zero (χ y), (mem_drint_aff_iff hβ _).2
    (DVRDescent.ιD χ hφ hχ (F₀ := F₀) y).2⟩
  map_one' := Subtype.ext (by simp [toAff])
  map_mul' x y := Subtype.ext (by simp [toAff])
  map_zero' := Subtype.ext (by simp [toAff])
  map_add' x y := Subtype.ext (by simp [toAff])

@[simp]
lemma coe_ιβ (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : DVRDescent.IsCompat φ χ) {β : C} (hβ : ‖β‖ ≤ 1)
    (y : DRint (0 : E) 1 F₀) :
    ((ιβ χ hφ hχ hβ y : DRint (0 : C) 1 (Aff β 1 one_ne_zero G)) : Aff β 1 one_ne_zero G) =
      toAff one_ne_zero (χ y) := rfl

variable (χ) in
/-- The restriction `Rint c₀E F₀ → Rint c₀ G`, `y ↦ χ y` (`φ c₀E = c₀`), of the node chart over
`O_E` to the node chart over `O_C` (the setting `BE`, `ιB` of O1). -/
noncomputable def ιN (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : DVRDescent.IsCompat φ χ) {c₀E : E} {c₀ : C}
    (hcE : φ c₀E = c₀) : Rint c₀E F₀ →+* Rint c₀ G where
  toFun y := ⟨χ y, by subst hcE; exact (DVRDescent.ιB χ hφ hχ c₀E y).2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma coe_ιN (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : DVRDescent.IsCompat φ χ) {c₀E : E} {c₀ : C}
    (hcE : φ c₀E = c₀) (y : Rint c₀E F₀) : ((ιN χ hφ hχ hcE y : Rint c₀ G) : G) = χ y := rfl

end Maps

/-- **Descent of smooth points** (pointwise, all residue points of a vertex chart). For
`G / C(x)` finite with generators `T`, there is a finite `S ⊆ C` such that: for every complete
discretely valued `E` (perfect residue field) with an isometric `φ : E → C`, `S ⊆ φ(E)`, `C`
algebraic over `E`, every `E`-form `F₀` of `G` (`χ : F₀ → G` compatible, same degree, `T ⊆ χ(F₀)`),
every uniformizer `ϖ` and every `O_E`-algebra structure on `DRint 0 1 F₀` compatible with `F₀`,
and every `β ∈ O_C`: if `P'` is a point of `DRint 0 1 (Aff β 1 G)` over `(𝔪_C, x - β)` at which
the special fibre over `C` is smooth, then `DRint 0 1 F₀` is semistable over `O_E` at `ιβ⁻¹ P'`. -/
def SmoothDescentStatement : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ) (_ : p.Prime) (_ : ‖(p : C)‖ < 1)
    (G : Type u) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
    [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
    (T : Finset G) (_ : Algebra.adjoin (RatFunc C) (T : Set G) = ⊤),
    ∃ S : Finset C, ∀ (E : Type u) [NontriviallyNormedField E] [IsUltrametricDist E]
      [CompleteSpace E] (φ : E →+* C) (hφ : ∀ e, ‖φ e‖ = ‖e‖) (_ : (S : Set C) ⊆ Set.range φ)
      (_ : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
      [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
      [PerfectField (ResidueField (NormedField.valuation (K := E)).valuationSubring)]
      (F₀ : Type u) [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀]
      [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
      [Algebra.IsSeparable (RatFunc E) F₀]
      (χ : F₀ →+* G)
      (hχ : ∀ x, χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) G (ratFuncMap φ x))
      (_ : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
      (_ : (T : Set G) ⊆ Set.range χ)
      (ϖ : (NormedField.valuation (K := E)).valuationSubring) (_ : Irreducible ϖ)
      [Algebra (NormedField.valuation (K := E)).valuationSubring (DRint (0 : E) 1 F₀)]
      (_ : ∀ o, ((algebraMap (NormedField.valuation (K := E)).valuationSubring
        (DRint (0 : E) 1 F₀) o : DRint (0 : E) 1 F₀) : F₀) = algebraMap E F₀ o)
      (β : C) (hβ : ‖β‖ ≤ 1) (P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))),
      P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) =
        discIdeal (0 : C) 1 →
      IsDiscSmooth P' →
      IsSemistableAt ϖ (P'.comap (ιβ χ hφ hχ hβ))

/-- **Descent of node points** (pointwise). For `G / C(x)` finite with generators `T` and a
thickness `c₀` (`0 < ‖c₀‖ < 1`), there is a finite `S ⊆ C` such that, in the setting of
`SmoothDescentStatement` and for `c₀E ∈ E` with `φ c₀E = c₀`: if `P'` is a point of the node chart
`Rint c₀ G` over the node which is an ordinary double point over `C`, then `Rint c₀E F₀` is
semistable over `O_E` at `ιN⁻¹ P'`. -/
def NodeDescentStatement : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ) (_ : p.Prime) (_ : ‖(p : C)‖ < 1)
    (G : Type u) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
    [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
    (T : Finset G) (_ : Algebra.adjoin (RatFunc C) (T : Set G) = ⊤)
    (c₀ : C) (hc : ‖c₀‖ < 1) (hc0 : c₀ ≠ 0),
    ∃ S : Finset C, ∀ (E : Type u) [NontriviallyNormedField E] [IsUltrametricDist E]
      [CompleteSpace E] (φ : E →+* C) (hφ : ∀ e, ‖φ e‖ = ‖e‖) (_ : (S : Set C) ⊆ Set.range φ)
      (_ : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
      [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
      [PerfectField (ResidueField (NormedField.valuation (K := E)).valuationSubring)]
      (F₀ : Type u) [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀]
      [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
      [Algebra.IsSeparable (RatFunc E) F₀]
      (χ : F₀ →+* G)
      (hχ : ∀ x, χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) G (ratFuncMap φ x))
      (_ : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
      (_ : (T : Set G) ⊆ Set.range χ)
      (ϖ : (NormedField.valuation (K := E)).valuationSubring) (_ : Irreducible ϖ)
      (c₀E : E) (hcE : φ c₀E = c₀)
      [Algebra (NormedField.valuation (K := E)).valuationSubring (Rint c₀E F₀)]
      (_ : ∀ o, ((algebraMap (NormedField.valuation (K := E)).valuationSubring
        (Rint c₀E F₀) o : Rint c₀E F₀) : F₀) = algebraMap E F₀ o)
      (P' : Ideal (Rint c₀ G)), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c₀) (Rint c₀ G)) = tubeIdeal c₀ →
      IsNodeODP hc hc0 P' →
      IsSemistableAt ϖ (P'.comap (ιN χ hφ hχ hcE))

end W10Route

end SemistableReduction
