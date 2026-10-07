/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhInter
import TemperedFundamentalGroups.SemistableReduction.ChartTwist

/-!
# L7: exhausting discs with empty intersection (O6.1c, [AW §4 case (4)])

Blueprint §9.10 (L7), §9.12 O6.1c. If the exhausting discs of a bad residue ball `B` had empty
intersection (their limit a type-4 point or a point of `Ĉ ∖ C`), every Gauss point of `B` would lie
outside some exhausting disc, hence be a disc of a tube by (T⇒); so `B` would satisfy the
valuative disc condition and be good by (D⇐). The type-4 content is therefore entirely in (D⇐),
whose owner uses the leaf `S8A.TypeFourGoodFor`.

* `ExhaustGluing.isTubeDisc_of_norm_sub_le`: `IsTubeDisc` only depends on the Gauss point
  (recentering inside the closed disc, `|b - b'| ≤ |γ|`);
* `S8A.isTubeDisc_of_sInter_eq_empty`;
* **`S8A.l7For_of`**: `TubeOfExhausting C F → SmoothOfDiscCond C F → L7For C F`.
-/

open Metric
open scoped NNReal

namespace SemistableReduction

namespace ExhaustGluing

open GaussTube GaussFibre AffineTwist PlaceNorm CurvePlace

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
/-- The same valuation, seen on two twists with centres at distance `≤ |γ|`. -/
noncomputable def recentre {b b' γ : C} (hγ : γ ≠ 0) (hb : ‖b - b'‖ ≤ ‖γ‖)
    (w : Ext C (Aff b' γ hγ F')) : Ext C (Aff b γ hγ F') :=
  let v := (extAff (a := b') (F' := F') hγ).symm w
  extAff hγ ⟨v.1, v.2.trans (Splitting.gaussRat_eq_of_le (by
    rw [NormedField.valuation_apply, Units.val_mk0]
    exact_mod_cast hb)).symm⟩

/-- The identity between two twists of `F'`. -/
noncomputable def twistId {b b' γ : C} (hγ : γ ≠ 0) : Aff b γ hγ F' ≃+* Aff b' γ hγ F' :=
  (toAff hγ).symm.trans (toAff hγ)

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma recentre_apply {b b' γ : C} (hγ : γ ≠ 0) (hb : ‖b - b'‖ ≤ ‖γ‖)
    (w : Ext C (Aff b' γ hγ F')) (f : Aff b γ hγ F') :
    w.1 (twistId hγ f) = (recentre hγ hb w).1 f := rfl

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma twistId_algebraMap {b b' γ : C} (hγ : γ ≠ 0) (c : C) :
    twistId (F' := F') (b := b) (b' := b') hγ (algebraMap C _ c) = algebraMap C _ c := rfl

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma twistId_xF {b b' γ : C} (hγ : γ ≠ 0) :
    twistId (F' := F') (b := b) (b' := b') hγ (xF C (Aff b γ hγ F')) =
      xF C (Aff b' γ hγ F') + algebraMap (RatFunc C) (Aff b' γ hγ F')
        (algebraMap C (RatFunc C) ((b' - b) / γ)) := by
  change algebraMap (RatFunc C) F' (aff b γ hγ RatFunc.X) =
    algebraMap (RatFunc C) F' (aff b' γ hγ RatFunc.X) + algebraMap (RatFunc C) F'
      (aff b' γ hγ (algebraMap C (RatFunc C) ((b' - b) / γ)))
  rw [← map_add, AlgEquiv.commutes, aff_apply, aff_apply, affHom_X, affHom_X, gaussCoord_eq,
    gaussCoord_eq]
  congr 1
  have h0 : algebraMap C (RatFunc C) γ ≠ 0 := by simpa using hγ
  simp only [map_inv₀, map_div₀, _root_.map_sub]
  field_simp
  ring

/-- **Recentering a disc of a tube**: `IsTubeDisc` depends only on the Gauss point
`w_{b,|γ|} = w_{b',|γ|}`. -/
theorem isTubeDisc_of_norm_sub_le {b b' γ : C} (hγ : γ ≠ 0) (hb : ‖b - b'‖ ≤ ‖γ‖)
    (h : IsTubeDisc F' b hγ) : IsTubeDisc F' b' hγ := by
  intro w
  obtain ⟨hg, hz⟩ := h (recentre hγ hb w)
  have hw : ∀ x, w.1 (twistId hγ x) = (recentre hγ hb w).1 x := recentre_apply hγ hb w
  let e := resAlgEquiv (twistId hγ) (twistId_algebraMap hγ) hw
  refine ⟨(genus_congr e).trans hg, ?_⟩
  rw [← hz]
  -- the reductions of the coordinates differ by a constant
  have hδ : ‖(b' - b) / γ‖₊ ≤ 1 := by
    have : ‖(b' - b) / γ‖ ≤ 1 := by
      rw [norm_div, div_le_one (norm_pos_iff.2 hγ), norm_sub_rev]; exact hb
    exact_mod_cast this
  have hx1 : w.1 (xF C (Aff b' γ hγ F')) ≤ 1 := by rw [xF, valuation_algebraMap, gauss1_X]
  have hc1 : w.1 (algebraMap (RatFunc C) (Aff b' γ hγ F')
      (algebraMap C (RatFunc C) ((b' - b) / γ))) ≤ 1 := by
    rw [valuation_algebraMap_C]; exact_mod_cast hδ
  have hred : e (red C (xF C (Aff b γ hγ F')) (recentre hγ hb w)) =
      red C (xF C (Aff b' γ hγ F')) w + algebraMap 𝓀 _ (IsLocalRing.residue _
        ⟨(b' - b) / γ, (HenselComplete.mem_integers_iff _).2 (by exact_mod_cast hδ)⟩) := by
    rw [resAlgEquiv_red, twistId_xF, red_add hx1 hc1, ← IsScalarTower.algebraMap_apply,
      red_algebraMap_C _ hδ]
  set r : 𝓀 := IsLocalRing.residue _
    ⟨(b' - b) / γ, (HenselComplete.mem_integers_iff _).2 (by exact_mod_cast hδ)⟩
  refine (Finset.card_bij (fun Q _ ↦ Q.map e) (fun Q hQ ↦ ?_)
    (fun Q _ Q' _ h ↦ map_injective _ h) (fun Q hQ ↦ ⟨Q.map e.symm, ?_, map_map_symm e Q⟩)).symm
  · rw [PlaceNorm.mem_zeros, inv_inv] at hQ ⊢
    rw [mem_map_V, ← sub_eq_iff_eq_add.2 hred, map_sub, AlgEquiv.symm_apply_apply]
    intro h
    apply hQ
    have := add_mem h (Q.algebraMap_mem r)
    rwa [AlgEquiv.commutes, sub_add_cancel] at this
  · rw [PlaceNorm.mem_zeros, inv_inv] at hQ ⊢
    rw [mem_map_V, AlgEquiv.symm_symm, hred]
    intro h
    apply hQ
    have := sub_mem h (Q.algebraMap_mem r)
    rwa [add_sub_cancel_right] at this

end ExhaustGluing

namespace S8A

open ExhaustGluing BallTree AffineTwist GaussTube

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

/-- If the exhausting discs of `ball b ‖c‖` have empty intersection, every Gauss point of the
ball is a disc of a tube (it lies outside some exhausting disc, (T⇒)). -/
theorem isTubeDisc_of_sInter_eq_empty (hT : TubeOfExhausting C F) {b c : C} (hc : c ≠ 0)
    (hempty : ⋂₀ ExhSet C F b c = ∅) {z γ : C} (hγ : γ ≠ 0) (hz : ‖z - b‖ < ‖c‖)
    (hγ1 : ‖γ‖ < 1) : IsTubeDisc F z (mul_ne_zero hc hγ) := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
  obtain ⟨D, hD, hzD⟩ : ∃ D ∈ ExhSet C F b c, z ∉ D := by
    by_contra! h
    have : z ∈ ⋂₀ ExhSet C F b c := Set.mem_sInter.2 h
    rw [hempty] at this
    exact this
  obtain ⟨⟨d, e, he, rfl⟩, hDB, hDG⟩ := hD
  have hdb : ‖d - b‖ < ‖c‖ := by
    have := hDB (mem_closedBall_self (norm_nonneg e))
    rwa [mem_ball, dist_eq_norm] at this
  have heb : ‖e‖ < ‖c‖ := by
    have h1 : ‖d + e - b‖ < ‖c‖ := by
      have := hDB (show d + e ∈ closedBall d ‖e‖ from mem_closedBall.2 (by simp [dist_eq_norm]))
      rwa [mem_ball, dist_eq_norm] at this
    have : e = (d + e - b) + -(d - b) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 (by rwa [norm_neg]))
  set c' := e / c with hc'def
  have hc'0 : c' ≠ 0 := div_ne_zero he hc
  have hc'1 : ‖c'‖ < 1 := by rw [norm_div, div_lt_one hcpos]; exact heb
  have hEx : IsExhausting d hc hc'1 hc'0 F := hDG d c c' hc hc'1 hc'0
    (by rw [hc'def, mul_div_cancel₀ _ hc])
    (closedBall_eq_of_norm_sub_le (by rw [norm_sub_rev]; exact hdb.le))
  have hTc := hT _ _ _ _ _ _ hEx
  set β := (z - d) / c with hβdef
  have hzd : ‖e‖ < ‖z - d‖ := by
    by_contra! h'
    exact hzD (mem_closedBall.2 (by rwa [dist_eq_norm]))
  have hzd' : ‖z - d‖ < ‖c‖ := by
    have : z - d = (z - b) + -(d - b) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hz (by rwa [norm_neg]))
  have hβ1 : ‖c'‖ < ‖β‖ := by
    rw [norm_div, norm_div]; exact div_lt_div_of_pos_right hzd hcpos
  have hβ2 : ‖β‖ < 1 := by rw [norm_div, div_lt_one hcpos]; exact hzd'
  have hzβ : d + c * β = z := by rw [hβdef]; field_simp; ring
  rcases lt_or_ge ‖γ‖ ‖β‖ with hγβ | hβγ
  · exact (isTubeDisc_congr _ _ hzβ rfl).1 (hTc.2 β γ hγ hβ1 hβ2 hγβ)
  · have h₁ := (hTc.1 γ hγ (hβ1.trans_le hβγ) hγ1 d (by
      simpa using norm_pos_iff.2 (mul_ne_zero hc hγ))).1
    refine isTubeDisc_of_norm_sub_le _ ?_ h₁
    rw [← hzβ, show d - (d + c * β) = -(c * β) by ring, norm_neg, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left hβγ (norm_nonneg _)

/-- **L7 ([AW §4 case (4)], O6.1c)** from (T⇒) and (D⇐): if the exhausting discs of a residue
ball have empty intersection, all Gauss points of the ball are discs of tubes, so the ball is
good. (The type-4 content is in (D⇐), which uses `TypeFourGoodFor`.) -/
theorem l7For_of (hT : TubeOfExhausting C F) (hD : SmoothOfDiscCond C F) : L7For C F := by
  intro b c hc hbad _ hempty
  apply hbad
  refine (Transport.ballGood_iff hc).2 (hD b c hc ⟨fun γ hγ hγ1 ↦ ?_, fun β γ hγ hβ hγβ ↦ ?_⟩)
  · exact isTubeDisc_of_sInter_eq_empty hT hc hempty hγ (by simpa using norm_pos_iff.2 hc) hγ1
  · refine isTubeDisc_of_sInter_eq_empty hT hc hempty hγ ?_ (hγβ.trans hβ)
    rw [add_sub_cancel_left, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.2 hc) hβ

end S8A

end SemistableReduction
