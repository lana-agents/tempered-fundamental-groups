/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeOneGerm

/-!
# The residue class at `∞` of a large disc is good (O6.4)

Blueprint §9.12 O6.4. The residue class at `∞` of `closedBall 0 ‖c‖` is the open disc
`|1/x| < |c⁻¹|` around the classical point `∞`. In the coordinate `c / x` its chart
`Inv 1 (Aff 0 c F)` is the chart `Aff 0 c⁻¹ (Inv 1 F)` of the disc of radius `|c⁻¹|` around `0`
for the inverted field `Inv 1 F` (same `C(X)`-algebra, `S8A.Transport.idData`), so S8.2
(`classicalGoodFor_of`) for `Inv 1 F` at `0` gives `S8A.InftyChartGood F 0 hc` for `‖c‖` large.
-/

open Metric

namespace SemistableReduction

namespace ClassicalSmooth

open GaussFibre DiscCount SmoothVertex AffineTwist

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

/-- Smoothness over the residue point is invariant under isomorphisms over `C(x)`. -/
lemma discGood_of_algebraMap_eq {G₁ G₂ : Type*} [Field G₁] [Field G₂] [Algebra (RatFunc C) G₁]
    [Algebra (RatFunc C) G₂] [Algebra C G₁] [Algebra C G₂] [IsScalarTower C (RatFunc C) G₁]
    [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₁]
    [FiniteDimensional (RatFunc C) G₂] (e : G₂ ≃+* G₁)
    (he : ∀ φ, e (algebraMap (RatFunc C) G₂ φ) = algebraMap (RatFunc C) G₁ φ)
    (h : ∀ P' : Ideal (DRint (0 : C) 1 G₂), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) = discIdeal (0 : C) 1 →
        IsDiscSmooth P') :
    ∀ P' : Ideal (DRint (0 : C) 1 G₁), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₁)) = discIdeal (0 : C) 1 →
        IsDiscSmooth P' :=
  (S8A.Transport.idData e he).discGoodAt_transport h

universe w

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- **O6.4 (centre `0`)**: for `‖c‖` large every point over the residue class at `∞` of
`closedBall 0 ‖c‖` is smooth, from S8.2 for the inverted field `Inv 1 F` at `0`. -/
theorem inftyChartGood_of
    (hK : ∀ a : C, KummerUnramFor.{_, _, w} C (GaussTube.Inv (1 : C) one_ne_zero F) a)
    (hA6 : ∀ (L : Type w) [Field L] [Algebra (RatFunc C) L]
      [Algebra (GaussTube.Inv (1 : C) one_ne_zero F) L]
      [IsScalarTower (RatFunc C) (GaussTube.Inv (1 : C) one_ne_zero F) L] [Algebra C L]
      [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
      [IsGalois (GaussTube.Inv (1 : C) one_ne_zero F) L],
      A6For C (GaussTube.Inv (1 : C) one_ne_zero F) L) :
    ∃ R₀ : ℝ, ∀ (c : C) (hc : c ≠ 0), R₀ ≤ ‖c‖ → S8A.InftyChartGood F 0 hc := by
  obtain ⟨s₀, hs₀, hgood⟩ := classicalGoodFor_of hp hp1 hK hA6 0
  refine ⟨1 / s₀, fun c hc hcR ↦ ?_⟩
  have hc' : c⁻¹ ≠ 0 := inv_ne_zero hc
  have hcs : ‖c⁻¹‖ ≤ s₀ := by
    rw [norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.2 hc) hs₀).2 (by rwa [one_div] at hcR)
  have h2 := (S8A.Transport.ballGood_iff hc').1 (hgood c⁻¹ hc' hcs)
  let e : Aff 0 c⁻¹ hc' (GaussTube.Inv (1 : C) one_ne_zero F) ≃+*
      GaussTube.Inv (1 : C) one_ne_zero (Aff 0 c hc F) := RingEquiv.refl F
  have hσ : (GaussTube.inv (one_ne_zero (α := C))).toAlgHom.comp (aff 0 c⁻¹ hc').toAlgHom =
      (aff 0 c hc).toAlgHom.comp (GaussTube.inv (one_ne_zero (α := C))).toAlgHom := by
    refine ratFunc_algHom_ext ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, aff_apply, GaussTube.inv_apply, affHom_X,
      GaussTube.invHom_X, gaussCoord_eq, map_mul, AlgHom.commutes, map_zero, sub_zero,
      map_div₀, map_one, inv_inv]
    have hX : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
    have hc'' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
    field_simp
    rw [map_div₀, map_one, one_div_one_div]
  refine discGood_of_algebraMap_eq e (fun φ ↦ ?_) h2
  change algebraMap (RatFunc C) F (GaussTube.inv one_ne_zero (aff 0 c⁻¹ hc' φ)) =
    algebraMap (RatFunc C) F (aff 0 c hc (GaussTube.inv one_ne_zero φ))
  exact congrArg (algebraMap (RatFunc C) F) (congrArg (fun χ : RatFunc C →ₐ[C] RatFunc C ↦ χ φ) hσ)

include hp hp1 in
/-- **O6.4** in the S8.A form `S8A.InftyGoodFor`. -/
theorem inftyGoodFor_of
    (hK : ∀ a : C, KummerUnramFor.{_, _, w} C (GaussTube.Inv (1 : C) one_ne_zero F) a)
    (hA6 : ∀ (L : Type w) [Field L] [Algebra (RatFunc C) L]
      [Algebra (GaussTube.Inv (1 : C) one_ne_zero F) L]
      [IsScalarTower (RatFunc C) (GaussTube.Inv (1 : C) one_ne_zero F) L] [Algebra C L]
      [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
      [IsGalois (GaussTube.Inv (1 : C) one_ne_zero F) L],
      A6For C (GaussTube.Inv (1 : C) one_ne_zero F) L) :
    S8A.InftyGoodFor C F :=
  inftyChartGood_of hp hp1 hK hA6

end ClassicalSmooth

end SemistableReduction
