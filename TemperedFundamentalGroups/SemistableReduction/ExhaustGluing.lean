/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Exhausting
import TemperedFundamentalGroups.SemistableReduction.NodeMaximum
import TemperedFundamentalGroups.SemistableReduction.TreeBridge
import TemperedFundamentalGroups.SemistableReduction.NodeUpward
import TemperedFundamentalGroups.SemistableReduction.GaussTreeSemistable
import TemperedFundamentalGroups.SemistableReduction.GaussTreeFinite
import TemperedFundamentalGroups.SemistableReduction.W7Statement

/-!
# Gluing of exhausting discs (O11, O11g)

Blueprint §9.12, O11. For `|c'| ≤ |e| ≤ |u| ≤ 1` the annulus `|c'| ≤ |t| ≤ 1` is the union of the
annuli `|e| ≤ |t| ≤ 1` and `|c'| ≤ |t| ≤ |u|`, and its (normalized) node chart is the intersection
of theirs:

* `nodeRing_eq_inf`: `O_C[x, c'/x] = O_C[x, e/x] ∩ O_C[x/u, c'/x]` (Laurent polynomials with
  Gauss value `≤ 1` at the two ends, `mem_nodeRing_of_mul_pow`);
* `nodeChart_coord_eq_inf`: the same in the coordinate `t = (x - a)/c`;
* `isIntegral_inf_iff`, `normChart_inf`: integrality over the intersection of two integrally
  closed subrings with the same fraction field (minimal polynomials);
* **`mem_rint_iff_and`**: `Rint c' (Aff a c F') = Rint e (Aff a c F') ∩ Rint (c'/u) (Aff a (cu) F')`
  as subsets of `F'`.

Gluing, modulo a valuative characterization of exhaustion (named hypotheses, Blueprint §9.12):

* `IsTubeDisc`, `IsTubeCircle`: the extensions of a Gauss point have rational residue curves with
  one point over `t̄ = ∞` (and one over `t̄ = 0`); `TubeCond a c c'`: every Gauss point of the open
  annulus `|c'| < |t| < 1` (`t = (x - a)/c`) is a circle (on the skeleton) or a disc (off it) of a
  tube; `DiscCond a c`: every Gauss point of the open disc `|t| < 1` is a disc of a tube;
* `tubeCond_of_tubeCond`, `discCond_of_discCond` (formal gluing over overlapping segments),
  `tubeCond_restrict`, `discCond_restrict`;
* (T⇒) `TubeOfExhausting`, (T⇐) `ExhaustingOfTube`, (D⇒) `DiscCondOfSmooth`, (D⇐)
  `SmoothOfDiscCond`: exhaustion (resp. goodness of a disc) is equivalent to the tube (resp. disc)
  condition;
* **`isExhausting_iff_of_le`** (O11): `D ⊂ D(a, |ce|) ⊂ U' ⊂ U` with `D(a, |ce|)` exhausting in `U`:
  `D` is exhausting in `U` iff in `U'`;
* **`discSmooth_iff_of_le`** (O11g): with `D(a, |ce|) ⊂ U'` exhausting in `U`, `U` is good iff `U'`
  is good.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace ExhaustGluing

open GaussTube ZariskiModel

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- A function in the subring generated over `O_C` by functions of Gauss value `≤ 1` has Gauss
value `≤ 1`. -/
lemma gaussRat_le_one_of_mem_closure (s : ℝ≥0ˣ) {S : Set (RatFunc C)} (hS : ∀ g ∈ S, w s g ≤ 1)
    {f : RatFunc C} (hf : f ∈ Subring.closure
      ((baseRing (RatFunc C) (NormedField.valuation (K := C)).valuationSubring :
        Set (RatFunc C)) ∪ S)) : w s f ≤ 1 := by
  have hle : Subring.closure
      ((baseRing (RatFunc C) (NormedField.valuation (K := C)).valuationSubring :
        Set (RatFunc C)) ∪ S) ≤ (w s).valuationSubring.toSubring := by
    refine Subring.closure_le.2 (Set.union_subset ?_ fun g hg ↦ hS g hg)
    rintro _ ⟨o, ho, rfl⟩
    change w s (algebraMap C (RatFunc C) o) ≤ 1
    rw [gaussRat_C]
    have : ν o ≤ 1 := ho
    rwa [NormedField.valuation_apply] at this
  exact hle hf

/-- Elements of the node chart are Laurent polynomials. -/
lemma exists_mul_pow_eq {c : C} {f : RatFunc C} (hf : f ∈ nodeRing c) :
    ∃ (k : ℕ) (Q : C[X]), f * RatFunc.X ^ k = algebraMap C[X] (RatFunc C) Q := by
  induction hf using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, -, rfl⟩ | rfl | rfl
    · exact ⟨0, Polynomial.C b, by simp [RatFunc.algebraMap_C]⟩
    · exact ⟨0, Polynomial.X, by simp⟩
    · refine ⟨1, Polynomial.C c, ?_⟩
      rw [pow_one, div_mul_cancel₀ _ RatFunc.X_ne_zero, RatFunc.algebraMap_C]
      rfl
  | zero => exact ⟨0, 0, by simp⟩
  | one => exact ⟨0, 1, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, Q, hQ⟩ := ha
    obtain ⟨l, R, hR⟩ := hb
    refine ⟨k + l, Q * Polynomial.X ^ l + R * Polynomial.X ^ k, ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, ← hQ, ← hR, RatFunc.algebraMap_X]
    ring
  | neg a _ ha =>
    obtain ⟨k, Q, hQ⟩ := ha
    exact ⟨k, -Q, by rw [map_neg, ← hQ]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, Q, hQ⟩ := ha
    obtain ⟨l, R, hR⟩ := hb
    exact ⟨k + l, Q * R, by rw [map_mul, ← hQ, ← hR]; ring⟩

/-- **Intersection of node charts** (in the coordinate `x`): for `|c'| ≤ |e| ≤ |u| ≤ 1`, the chart
`O_C[x, c'/x]` of the annulus `|c'| ≤ |x| ≤ 1` is the intersection of the charts
`O_C[x, e/x]` and `O_C[x/u, c'/x]` of the annuli `|e| ≤ |x| ≤ 1` and `|c'| ≤ |x| ≤ |u|`. -/
theorem nodeRing_eq_inf {c' e u : C} (hc'0 : c' ≠ 0) (hu0 : u ≠ 0) (hc'e : ‖c'‖ ≤ ‖e‖)
    (heu : ‖e‖ ≤ ‖u‖) (hu1 : ‖u‖ ≤ 1) :
    nodeRing c' = nodeRing e ⊓
      nodeChart ν (RatFunc.X / algebraMap C (RatFunc C) u) (c' / u) := by
  have he0 : e ≠ 0 := norm_pos_iff.1 ((norm_pos_iff.2 hc'0).trans_le hc'e)
  have hX0 : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have hu' : algebraMap C (RatFunc C) u ≠ 0 := by simpa using hu0
  have hwX : ∀ s : ℝ≥0ˣ, w s RatFunc.X = s := gaussRat_X
  set su : ℝ≥0ˣ := Units.mk0 ‖c'‖₊ (by simpa using hc'0)
  refine le_antisymm (le_inf ?_ ?_) fun f ⟨hf₁, hf₂⟩ ↦ ?_
  · exact nodeRing_le hc'e he0
  · refine nodeChart_le baseRing_le_nodeChart ?_ ?_
    · have hmem := mul_mem (baseRing_le_nodeChart (v := NormedField.valuation (K := C))
        (y := RatFunc.X / algebraMap C (RatFunc C) u) (c := c' / u)
        (algebraMap_mem_baseRing' (c := u) (by
          rw [NormedField.valuation_apply]; exact_mod_cast hu1))) self_mem_nodeChart
      rwa [mul_div_cancel₀ _ hu'] at hmem
    · have hmem := div_mem_nodeChart (v := NormedField.valuation (K := C))
        (y := RatFunc.X / algebraMap C (RatFunc C) u) (c := c' / u)
      rwa [map_div₀, div_div_div_cancel_right₀ hu'] at hmem
  · obtain ⟨k, Q, hQ⟩ := exists_mul_pow_eq hf₁
    refine mem_nodeRing_of_mul_pow hc'0 hQ ?_ ?_
    · refine gaussRat_le_one_of_mem_closure 1 ?_ hf₁
      rintro g (rfl | hg)
      · rw [hwX]; rfl
      · rw [Set.mem_singleton_iff] at hg
        rw [hg, map_div₀, gaussRat_C, hwX, Units.val_one, div_one]
        exact_mod_cast heu.trans hu1
    · refine gaussRat_le_one_of_mem_closure _ ?_ hf₂
      rintro g (rfl | hg)
      · rw [map_div₀, gaussRat_C, hwX]
        refine div_le_one_of_le₀ ?_ zero_le
        change ‖c'‖₊ ≤ ‖u‖₊
        exact_mod_cast hc'e.trans heu
      · rw [Set.mem_singleton_iff] at hg
        rw [hg, map_div₀ (algebraMap C (RatFunc C)), div_div_div_cancel_right₀ hu', map_div₀,
          gaussRat_C, hwX]
        change ‖c'‖₊ / ‖c'‖₊ ≤ 1
        exact div_self_le_one _


/-- Ring maps over `C` carry node charts to node charts. -/
lemma map_nodeChart (φ : RatFunc C →ₐ[C] RatFunc C) (z : RatFunc C) (γ : C) :
    (nodeChart ν z γ).map φ.toRingHom = nodeChart ν (φ z) γ := by
  rw [nodeChart, nodeChart, RingHom.map_closure, Set.image_union]
  congr 2
  · ext f
    simp only [baseRing, Subring.coe_map, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
      exact ⟨o, ho, (φ.commutes o).symm⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨_, ⟨o, ho, rfl⟩, φ.commutes o⟩
  · rw [Set.image_insert_eq, Set.image_singleton]
    congr 2
    change φ (algebraMap C (RatFunc C) γ / z) = _
    rw [map_div₀, AlgHom.commutes]

/-- **Intersection of node charts** in the coordinate `t = (x - a)/c`: for `|c'| ≤ |e| ≤ |u| ≤ 1`,
`O_C[t, c'/t] = O_C[t, e/t] ∩ O_C[t/u, c'/t]`. -/
theorem nodeChart_coord_eq_inf {a c c' e u : C} (hc0 : c ≠ 0) (hc'0 : c' ≠ 0) (hu0 : u ≠ 0)
    (hc'e : ‖c'‖ ≤ ‖e‖) (heu : ‖e‖ ≤ ‖u‖) (hu1 : ‖u‖ ≤ 1) :
    nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) c' =
      nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) e ⊓
        nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a (c * u)) (c' / u) := by
  set φ := (AffineTwist.aff a c hc0).toAlgHom
  have hφX : φ RatFunc.X = GaussTree.coord (RatFunc.X : RatFunc C) a c := by
    change AffineTwist.affHom a c hc0 RatFunc.X = _
    rw [AffineTwist.affHom_X, gaussCoord_eq_coord hc0]
  have hφu : φ (RatFunc.X / algebraMap C (RatFunc C) u) =
      GaussTree.coord (RatFunc.X : RatFunc C) a (c * u) := by
    rw [map_div₀, AlgHom.commutes, hφX, GaussTree.coord, GaussTree.coord, map_mul, div_div]
  have h := congrArg (fun S : Subring (RatFunc C) ↦ S.map φ.toRingHom)
    (nodeRing_eq_inf hc'0 hu0 hc'e heu hu1)
  rw [Subring.map_inf _ _ φ.toRingHom (AffineTwist.aff a c hc0).injective] at h
  rw [← hφX, ← hφu, ← map_nodeChart, ← map_nodeChart, ← map_nodeChart]
  exact h

lemma isIntegral_of_subring_le {L E : Type*} [Field L] [CommRing E] [Algebra L E]
    {A B : Subring L} (h : A ≤ B) {y : E} (hy : IsIntegral A y) : IsIntegral B y := by
  obtain ⟨p, hm, hp⟩ := hy
  refine ⟨p.map (Subring.inclusion h), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp

/-- Integrality over the intersection of two integrally closed subrings with fraction field `L`. -/
theorem isIntegral_inf_iff {L E : Type*} [Field L] [Field E] [Algebra L E]
    {A₁ A₂ : Subring L} [IsIntegrallyClosed A₁] [IsFractionRing A₁ L]
    [IsIntegrallyClosed A₂] [IsFractionRing A₂ L] (y : E) :
    IsIntegral (A₁ ⊓ A₂ : Subring L) y ↔ IsIntegral A₁ y ∧ IsIntegral A₂ y := by
  constructor
  · intro h
    exact ⟨isIntegral_of_subring_le inf_le_left h, isIntegral_of_subring_le inf_le_right h⟩
  · rintro ⟨h₁, h₂⟩
    have e₁ := minpoly.isIntegrallyClosed_eq_field_fractions' L h₁
    have e₂ := minpoly.isIntegrallyClosed_eq_field_fractions' L h₂
    have hc : ↑(minpoly L y).coeffs ⊆ ((A₁ ⊓ A₂ : Subring L) : Set L) := fun c hc' ↦ by
      obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc'
      refine ⟨?_, ?_⟩
      · rw [e₁, coeff_map]; exact Subtype.prop _
      · rw [e₂, coeff_map]; exact Subtype.prop _
    refine ⟨(minpoly L y).toSubring _ hc, ?_, ?_⟩
    · exact (monic_toSubring _ _ hc).2 (minpoly.monic (h₁.tower_top (A := L)))
    · have := minpoly.aeval L y
      rw [← map_toSubring _ _ hc, aeval_def, eval₂_map] at this
      exact this

section Normalization

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

omit [IsUltrametricDist C] in
/-- The normalization of the intersection of two integrally closed subrings of `C(x)` with
fraction field `C(x)` is the intersection of their normalizations. -/
theorem normChart_inf {A₁ A₂ : Subring (RatFunc C)} [IsIntegrallyClosed A₁]
    [IsFractionRing A₁ (RatFunc C)] [IsIntegrallyClosed A₂] [IsFractionRing A₂ (RatFunc C)] :
    normChart F' (A₁ ⊓ A₂) = normChart F' A₁ ⊓ normChart F' A₂ := by
  ext y
  rw [← integralClosure_toSubring_eq, ← integralClosure_toSubring_eq,
    ← integralClosure_toSubring_eq]
  exact isIntegral_inf_iff y

end Normalization

section Twisted

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

open AffineTwist TreeBridge

lemma mem_rint_aff_iff {a c : C} (hc0 : c ≠ 0) (c' : C) (y : F') :
    AffineTwist.toAff hc0 y ∈ Rint c' (Aff a c hc0 F') ↔
      y ∈ normChart F' (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) c') := by
  rw [← map_rint_aff hc0 c']
  constructor
  · intro h
    exact ⟨_, h, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact hz

/-- **Intersection of normalized node charts** (twisted form): for `|c'| ≤ |e| ≤ |u| ≤ 1`, the
normalized chart of the annulus `|c'| ≤ |t| ≤ 1` (`t = (x - a)/c`) is the intersection of those of
the annuli `|e| ≤ |t| ≤ 1` and `|c'| ≤ |t| ≤ |u|` (the latter in the coordinate `t/u`). -/
theorem mem_rint_iff_and {a c c' e u : C} (hc0 : c ≠ 0) (hc'0 : c' ≠ 0) (hu0 : u ≠ 0)
    (hc'e : ‖c'‖ ≤ ‖e‖) (heu : ‖e‖ ≤ ‖u‖) (hu1 : ‖u‖ ≤ 1) (y : F') :
    toAff hc0 y ∈ Rint c' (Aff a c hc0 F') ↔
      toAff hc0 y ∈ Rint e (Aff a c hc0 F') ∧
        toAff (mul_ne_zero hc0 hu0) y ∈ Rint (c' / u) (Aff a (c * u) (mul_ne_zero hc0 hu0) F') := by
  have he0 : e ≠ 0 := norm_pos_iff.1 ((norm_pos_iff.2 hc'0).trans_le hc'e)
  have hcu0 : c * u ≠ 0 := mul_ne_zero hc0 hu0
  rw [mem_rint_aff_iff, mem_rint_aff_iff, mem_rint_aff_iff,
    nodeChart_coord_eq_inf hc0 hc'0 hu0 hc'e heu hu1]
  have hg₁ := isGaussCoord_coord (v := ν) (a := a) hc0
  have hg₂ := isGaussCoord_coord (v := ν) (a := a) hcu0
  haveI : IsIntegrallyClosed (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) e) :=
    isIntegrallyClosed_nodeChart hg₁ he0 (by
      rw [NormedField.valuation_apply]; exact_mod_cast heu.trans hu1)
  haveI : IsIntegrallyClosed
      (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a (c * u)) (c' / u)) :=
    isIntegrallyClosed_nodeChart hg₂ (div_ne_zero hc'0 hu0) (by
      rw [NormedField.valuation_apply, nnnorm_div]
      exact div_le_one_of_le₀ (by exact_mod_cast hc'e.trans heu) zero_le)
  haveI : IsFractionRing (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a c) e)
      (RatFunc C) :=
    hg₁.isFractionRing_of_le (polyChart_le baseRing_le_nodeChart self_mem_nodeChart)
  haveI : IsFractionRing
      (nodeChart ν (GaussTree.coord (RatFunc.X : RatFunc C) a (c * u)) (c' / u)) (RatFunc C) :=
    hg₂.isFractionRing_of_le (polyChart_le baseRing_le_nodeChart self_mem_nodeChart)
  rw [normChart_inf]
  rfl

end Twisted

end ExhaustGluing

end SemistableReduction

/-! ### The valuative tube condition and the gluing of exhausting discs -/

namespace SemistableReduction

namespace ExhaustGluing

open GaussTube GaussFibre AffineTwist PlaceNorm

universe u

section Tube

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  (F' : Type*) [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- **A disc of a tube**: every extension `w` of the Gauss point `w_{b,|γ|}` (an extension of
`w_{0,1}` on the twist `Aff b γ F'`, coordinate `t = (x - b)/γ`) has a rational residue curve
with exactly one point over `t̄ = ∞`. Inside the preimage of an open annulus which is a disjoint
union of open annuli, the preimage of every closed disc is a disjoint union of closed discs. -/
def IsTubeDisc (b : C) {γ : C} (hγ : γ ≠ 0) : Prop :=
  ∀ w : Ext C (Aff b γ hγ F'), genus 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring) = 0 ∧
    (zeros 𝓀 (red C (xF C (Aff b γ hγ F')) w)⁻¹).card = 1

/-- **A circle of a tube**: for every centre `b'` of the open disc `|x - b| < |γ|`, the extensions
of the Gauss point `w_{b',|γ|} = w_{b,|γ|}` have rational residue curves with exactly one point
over `t̄ = ∞` and exactly one over `t̄ = 0` (`t = (x - b')/γ`; the point over `0` is the residue
class of `b`). -/
def IsTubeCircle (b : C) {γ : C} (hγ : γ ≠ 0) : Prop :=
  ∀ b' : C, ‖b - b'‖ < ‖γ‖ → IsTubeDisc F' b' hγ ∧ ∀ w : Ext C (Aff b' γ hγ F'),
    (zeros 𝓀 (red C (xF C (Aff b' γ hγ F')) w)).card = 1

/-- **The valuative tube condition** for the open annulus `|c'| < |t| < 1`, `t = (x - a)/c`:
every Gauss point of its skeleton is a circle of a tube, and every Gauss point `w_{a + c β, |c γ|}`
off the skeleton (`|c'| < |β| < 1`, `0 < |γ| < |β|`) is a disc of a tube. -/
def TubeCond (a : C) {c : C} (hc : c ≠ 0) (c' : C) : Prop :=
  (∀ (γ : C) (hγ : γ ≠ 0), ‖c'‖ < ‖γ‖ → ‖γ‖ < 1 → IsTubeCircle F' a (mul_ne_zero hc hγ)) ∧
  ∀ (β γ : C) (hγ : γ ≠ 0), ‖c'‖ < ‖β‖ → ‖β‖ < 1 → ‖γ‖ < ‖β‖ →
    IsTubeDisc F' (a + c * β) (mul_ne_zero hc hγ)

variable {F'}

lemma isTubeDisc_congr {b b' γ γ' : C} (hγ : γ ≠ 0) (hγ' : γ' ≠ 0) (hb : b = b')
    (h : γ = γ') : IsTubeDisc F' b hγ ↔ IsTubeDisc F' b' hγ' := by
  subst hb h
  rfl

lemma isTubeCircle_congr {b b' γ γ' : C} (hγ : γ ≠ 0) (hγ' : γ' ≠ 0) (hb : b = b')
    (h : γ = γ') : IsTubeCircle F' b hγ ↔ IsTubeCircle F' b' hγ' := by
  subst hb h
  rfl

/-- **Gluing of tube conditions** (formal): for `|e| < |u|`, the tube condition for
the annulus `|c'| < |t| < 1` follows from those for `|e| < |t| < 1` and `|c'| < |t| < |u|` (the
latter in the coordinate `t/u`): every Gauss point of the big open annulus lies in one of the
two. -/
theorem tubeCond_of_tubeCond {a c c' e u : C} (hc : c ≠ 0) (hu0 : u ≠ 0) (heu : ‖e‖ < ‖u‖)
    (h₁ : TubeCond F' a hc e) (h₂ : TubeCond F' a (mul_ne_zero hc hu0) (c' / u)) :
    TubeCond F' a hc c' := by
  have hu : 0 < ‖u‖ := norm_pos_iff.2 hu0
  refine ⟨fun γ hγ h1 h2 ↦ ?_, fun β γ hγ h1 h2 h3 ↦ ?_⟩
  · rcases lt_or_ge ‖e‖ ‖γ‖ with he | he
    · exact h₁.1 γ hγ he h2
    · have hγu : γ / u ≠ 0 := div_ne_zero hγ hu0
      refine (isTubeCircle_congr _ _ rfl (by field_simp)).1
        (h₂.1 (γ / u) hγu ?_ ?_)
      · rw [norm_div, norm_div]
        exact div_lt_div_of_pos_right h1 hu
      · rw [norm_div, div_lt_one hu]
        exact he.trans_lt heu
  · rcases lt_or_ge ‖e‖ ‖β‖ with he | he
    · exact h₁.2 β γ hγ he h2 h3
    · have hγu : γ / u ≠ 0 := div_ne_zero hγ hu0
      refine (isTubeDisc_congr _ _ (by field_simp) (by field_simp)).1
        (h₂.2 (β / u) (γ / u) hγu ?_ ?_ ?_)
      · rw [norm_div, norm_div]
        exact div_lt_div_of_pos_right h1 hu
      · rw [norm_div, div_lt_one hu]
        exact he.trans_lt heu
      · rw [norm_div, norm_div]
        exact div_lt_div_of_pos_right h3 hu

/-- Restriction of tube conditions to a sub-annulus `|c'| < |t| < |u|` (in the coordinate
`t/u`). -/
theorem tubeCond_restrict {a c c' u : C} (hc : c ≠ 0) (hu0 : u ≠ 0) (hu1 : ‖u‖ ≤ 1)
    (h : TubeCond F' a hc c') : TubeCond F' a (mul_ne_zero hc hu0) (c' / u) := by
  have hu : 0 < ‖u‖ := norm_pos_iff.2 hu0
  refine ⟨fun γ hγ h1 h2 ↦ ?_, fun β γ hγ h1 h2 h3 ↦ ?_⟩
  · rw [norm_div, div_lt_iff₀ hu] at h1
    refine (isTubeCircle_congr _ _ rfl (by ring)).1
      (h.1 (u * γ) (mul_ne_zero hu0 hγ) (by rw [norm_mul]; linarith) ?_)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hu1).trans_lt h2
  · rw [norm_div, div_lt_iff₀ hu] at h1
    refine (isTubeDisc_congr _ _ (by ring) (by ring)).1
      (h.2 (u * β) (u * γ) (mul_ne_zero hu0 hγ) (by rw [norm_mul]; linarith) ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hu1).trans_lt h2
    · rw [norm_mul, norm_mul]
      exact mul_lt_mul_of_pos_left h3 hu

variable (C F') in
/-- **(T⇒)** (named hypothesis, Blueprint §9.12 O11): the preimage of an annulus whose node points
are all ordinary double points satisfies the valuative tube condition. To be discharged from the
exact node data (`GaussTube.NodeData`) by counting extensions along the tube. -/
def TubeOfExhausting : Prop :=
  ∀ (a c c' : C) (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0),
    IsExhausting a hc hc' hc0' F' → TubeCond F' a hc c'

variable (C F') in
/-- **(T⇐)** (named hypothesis, Blueprint §9.12 O12): if the open annulus satisfies the valuative
tube condition, every node point of its normalized chart is an ordinary double point. Expected
from the local improvement formula (R5). -/
def ExhaustingOfTube : Prop :=
  ∀ (a c c' : C) (hc : c ≠ 0) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0),
    TubeCond F' a hc c' → IsExhausting a hc hc' hc0' F'

/-- **O11: gluing of exhausting discs** (modulo (T⇒) and (T⇐)). For `U = {|x - a| < |c|}`,
`U' = {|x - a| < |c u|}` (`|u| < 1`), `D(a, |c e|) ⊆ U'` (`|e| < |u|`) exhausting in `U`, and
`D = D(a, |c c'|) ⊆ D(a, |c e|)`: `D` is exhausting in `U` iff it is exhausting in `U'`. -/
theorem isExhausting_iff_of_le (hT : TubeOfExhausting C F') (hT' : ExhaustingOfTube C F')
    {a c u e c' : C} (hc0 : c ≠ 0) (hu0 : u ≠ 0) (hu : ‖u‖ < 1) (he0 : e ≠ 0)
    (heu : ‖e‖ < ‖u‖) (hc'0 : c' ≠ 0) (hc'e : ‖c'‖ ≤ ‖e‖)
    (hbig : IsExhausting a hc0 (heu.trans hu) he0 F') :
    IsExhausting a hc0 (hc'e.trans_lt (heu.trans hu)) hc'0 F' ↔
      IsExhausting a (mul_ne_zero hc0 hu0) (c' := c' / u)
        (by rw [norm_div, div_lt_one (norm_pos_iff.2 hu0)]; exact hc'e.trans_lt heu)
        (div_ne_zero hc'0 hu0) F' := by
  constructor
  · intro h
    exact hT' _ _ _ _ _ _ (tubeCond_restrict hc0 hu0 hu.le (hT _ _ _ _ _ _ h))
  · intro h
    exact hT' _ _ _ _ _ _ (tubeCond_of_tubeCond hc0 hu0 heu (hT _ _ _ _ _ _ hbig)
      (hT _ _ _ _ _ _ h))

/-! #### Good residue discs -/

variable (F') in
/-- **The valuative disc condition** for the open disc `|t| < 1`, `t = (x - a)/c`: every Gauss
point inside it is a disc of a tube (the closed discs `D(a, |c γ|)`, `0 < |γ| < 1`, and
`D(a + c β, |c γ|)`, `0 < |γ| < |β| < 1`, are all closed discs in the open disc). -/
def DiscCond (a : C) {c : C} (hc : c ≠ 0) : Prop :=
  (∀ (γ : C) (hγ : γ ≠ 0), ‖γ‖ < 1 → IsTubeDisc F' a (mul_ne_zero hc hγ)) ∧
  ∀ (β γ : C) (hγ : γ ≠ 0), ‖β‖ < 1 → ‖γ‖ < ‖β‖ → IsTubeDisc F' (a + c * β) (mul_ne_zero hc hγ)

variable (F') in
/-- Every point over the open disc `|x - a| < |c|` is smooth (`S8A.DiscGood`, wp-tempered-s8a). -/
def DiscSmooth (a : C) {c : C} (hc : c ≠ 0) : Prop :=
  ∀ P' : Ideal (DiscCount.DRint (0 : C) 1 (Aff a c hc F')), P'.IsMaximal →
    P'.comap (algebraMap (DiscCount.discRing (0 : C) 1)
      (DiscCount.DRint (0 : C) 1 (Aff a c hc F'))) = DiscCount.discIdeal (0 : C) 1 →
      SmoothVertex.IsDiscSmooth P'

/-- Restriction of the disc condition to a smaller concentric disc. -/
theorem discCond_restrict {a c u : C} (hc : c ≠ 0) (hu0 : u ≠ 0) (hu1 : ‖u‖ ≤ 1)
    (h : DiscCond F' a hc) : DiscCond F' a (mul_ne_zero hc hu0) := by
  have hu : 0 < ‖u‖ := norm_pos_iff.2 hu0
  refine ⟨fun γ hγ h1 ↦ ?_, fun β γ hγ h1 h2 ↦ ?_⟩
  · refine (isTubeDisc_congr _ _ rfl (by ring)).1 (h.1 (u * γ) (mul_ne_zero hu0 hγ) ?_)
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hu1).trans_lt h1
  · refine (isTubeDisc_congr _ _ (by ring) (by ring)).1
      (h.2 (u * β) (u * γ) (mul_ne_zero hu0 hγ) ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) hu1).trans_lt h1
    · rw [norm_mul, norm_mul]
      exact mul_lt_mul_of_pos_left h2 hu

/-- **Gluing of disc conditions** (formal): for `|e| < |u|`, the disc condition for
`|t| < 1` follows from the one for `|t| < |u|` and the tube condition for `|e| < |t| < 1`. -/
theorem discCond_of_discCond {a c e u : C} (hc : c ≠ 0) (hu0 : u ≠ 0) (heu : ‖e‖ < ‖u‖)
    (h₁ : TubeCond F' a hc e) (h₂ : DiscCond F' a (mul_ne_zero hc hu0)) :
    DiscCond F' a hc := by
  have hu : 0 < ‖u‖ := norm_pos_iff.2 hu0
  refine ⟨fun γ hγ h1 ↦ ?_, fun β γ hγ h1 h2 ↦ ?_⟩
  · rcases lt_or_ge ‖γ‖ ‖u‖ with hγu | hγu
    · refine (isTubeDisc_congr _ _ rfl (by field_simp)).1
        (h₂.1 (γ / u) (div_ne_zero hγ hu0) ?_)
      rw [norm_div, div_lt_one hu]
      exact hγu
    · exact (h₁.1 γ hγ (heu.trans_le hγu) h1 a
        (by simpa using norm_pos_iff.2 (mul_ne_zero hc hγ))).1
  · rcases lt_or_ge ‖β‖ ‖u‖ with hβu | hβu
    · refine (isTubeDisc_congr _ _ (by field_simp) (by field_simp)).1
        (h₂.2 (β / u) (γ / u) (div_ne_zero hγ hu0) ?_ ?_)
      · rw [norm_div, div_lt_one hu]
        exact hβu
      · rw [norm_div, norm_div]
        exact div_lt_div_of_pos_right h2 hu
    · exact h₁.2 β γ hγ (heu.trans_le hβu) h1 h2

variable (C F') in
/-- **(D⇒)** (named hypothesis, Blueprint §9.12 O11g): over a good open disc the valuative disc
condition holds. -/
def DiscCondOfSmooth : Prop :=
  ∀ (a c : C) (hc : c ≠ 0), DiscSmooth F' a hc → DiscCond F' a hc

variable (C F') in
/-- **(D⇐)** (named hypothesis, Blueprint §9.12 O12): an open disc satisfying the valuative disc
condition is good. -/
def SmoothOfDiscCond : Prop :=
  ∀ (a c : C) (hc : c ≠ 0), DiscCond F' a hc → DiscSmooth F' a hc

/-- **O11g: gluing of good discs** (modulo (T⇒), (D⇒), (D⇐)). For `U = {|x - a| < |c|}`,
`U' = {|x - a| < |c u|}` (`|u| < 1`) and `D(a, |c e|) ⊆ U'` (`|e| < |u|`) exhausting in `U`:
`U` is good iff `U'` is good. -/
theorem discSmooth_iff_of_le (hT : TubeOfExhausting C F') (hD : DiscCondOfSmooth C F')
    (hD' : SmoothOfDiscCond C F') {a c u e : C} (hc0 : c ≠ 0) (hu0 : u ≠ 0) (hu : ‖u‖ < 1)
    (he0 : e ≠ 0) (heu : ‖e‖ < ‖u‖) (hbig : IsExhausting a hc0 (heu.trans hu) he0 F') :
    DiscSmooth F' a hc0 ↔ DiscSmooth F' a (mul_ne_zero hc0 hu0) := by
  constructor
  · intro h
    exact hD' _ _ _ (discCond_restrict hc0 hu0 hu.le (hD _ _ _ h))
  · intro h
    exact hD' _ _ _ (discCond_of_discCond hc0 hu0 heu (hT _ _ _ _ _ _ hbig) (hD _ _ _ h))

end Tube

end ExhaustGluing

end SemistableReduction
