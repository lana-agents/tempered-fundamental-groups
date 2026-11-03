/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeHomDatum
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSpecialHom

/-!
# The morphisms of the lifts reduce to the given maps over `V₀` (MR13 A1 (b))

Under the identification `specialFibreEquiv0 : B₀ ⧸ (ϖ) ≃ C0` of the special fibre of the
algebraized lift over the chart `V₀ = ℙ¹_t ∖ {∞}` (`P1ThreeSpecialFibre`), the morphism
`Datum.algMap f` of the algebraized coverings induced by a morphism of data `f` reduces to its
component `f.φ0` (**`P1Three.Datum.specialFibreEquiv0_algMap`**; the `V₁` analogue is
`Datum.specialFibreEquiv1_algMap`). Steps: the maps of the cusp pieces commute with the bottom
identifications (`Datum.pM_bottom0`, from `CuspTower.pieceMap_bottom`), so the map of the first
two-chart rings at level `0` is `φ0` under `r0Equiv'` (generic:
`NodeEtaleGlue.Overlap.twoChartMap_f0_r0Equiv'`, `Overlap.r0Equiv'_symm_map`).
-/

universe u

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

namespace Datum

variable (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {D D' : Datum O θ a}

/-- **The maps of the cusp pieces commute with the bottom identifications** `C0 → P0 0`. -/
lemma pM_bottom0 (f : D.Hom D') (c : D.S0.C0) :
    pM hϖ hker ha0 ha1 hO f 0 ((bottom0 D.Sp hϖ hker D.S0 D.om hO).toP c) =
      (bottom0 D'.Sp hϖ hker D'.S0 D'.om hO).toP (f.φ0 c) :=
  CuspTower.pieceMap_bottom D.S0 D'.S0 hϖ hker (isSMulRegular_x0 ϖ a) hO
    (cuspNFc a ha0 ha1 D'.S0) f.φ0 (J_Tn_zero_eq_bot hker _) c

variable [IsAdicComplete (Ideal.span {ϖ}) O]

omit [IsAdicComplete (Ideal.span {ϖ}) O] in
lemma specialFibreEquiv0_mk (D : Datum O θ a)
    (L : ProjectiveLine.AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D))
    (b : L.B.Ring0) :
    specialFibreEquiv0 D.Sp hϖ hker D.S0 D.om hO L.hα L.hB (Ideal.Quotient.mk _ b) =
      ((overlap D.Sp hϖ hker D.S0 D.om hO).r0Equiv' hθ.out hO (J_Tn_zero_eq_bot hker _)
        (bottom0 D.Sp hϖ hker D.S0 D.om hO)).symm ((L.α 1).f0 b) :=
  (overlap D.Sp hϖ hker D.S0 D.om hO).specialFibreEquiv0_mk hθ.out hO
    (J_Tn_zero_eq_bot hker _) L.hα L.hB (bottom0 D.Sp hϖ hker D.S0 D.om hO) b

/-- **The reduction of `algMap f` over `V₀` is `φ0`**: under the identifications
`specialFibreEquiv0 : B₀ ⧸ (ϖ) ≃ C0`, the morphism of the algebraized coverings induced by a
morphism of data reduces to its component `φ0`. -/
theorem specialFibreEquiv0_algMap (f : D.Hom D')
    (L : ProjectiveLine.AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D))
    (L' : ProjectiveLine.AdicChartAlgSystem.Algebraization (systemD hϖ hker hO D'))
    (b : L.B.Ring0) :
    specialFibreEquiv0 D'.Sp hϖ hker D'.S0 D'.om hO L'.hα L'.hB
        (Ideal.Quotient.mk _ ((isHom_algMap hϖ hker ha0 ha1 hO f L L').ringHom0 b)) =
      f.φ0 (specialFibreEquiv0 D.Sp hϖ hker D.S0 D.om hO L.hα L.hB (Ideal.Quotient.mk _ b)) := by
  rw [specialFibreEquiv0_mk, specialFibreEquiv0_mk]
  exact (overlap D.Sp hϖ hker D.S0 D.om hO).r0Equiv'_symm_map
    (overlap D'.Sp hϖ hker D'.S0 D'.om hO) hθ.out hO ϖ rfl rfl _ _ _ _ _ _ _ _ _ L L'
    (J_Tn_zero_eq_bot hker _) (J_Tn_zero_eq_bot hker _) (bottom0 D.Sp hϖ hker D.S0 D.om hO)
    (bottom0 D'.Sp hϖ hker D'.S0 D'.om hO) f.φ0.toRingHom
    (fun c ↦ pM_bottom0 hϖ hker ha0 ha1 hO f c) (Lx0Map f)
    (fun c ↦ EtaleTower.CbMap_algebraMap (R0 O a) (x0 O a) f.φ0 c) f.φ1.toRingHom (Lx1Map f)
    (fun c ↦ EtaleTower.CbMap_algebraMap (R1 O a) (y1 O a) f.φ1 c) f.hω
    (fun c ↦ yMap_yEquiv hϖ hker D.Sp D'.Sp hO f.φ1 c) b

end Datum

end

end P1Three

end SemistableReduction
