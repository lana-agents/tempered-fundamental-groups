/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DiscBridge
import TemperedFundamentalGroups.SemistableReduction.ChartTwist
import TemperedFundamentalGroups.SemistableReduction.SmoothTwist
import TemperedFundamentalGroups.SemistableReduction.W10RouteTwist
import TemperedFundamentalGroups.SemistableReduction.S8Transport

/-!
# O6.3: a disc has only finitely many bad residue balls

Blueprint §9.12 O6.3. Let `G / C(x)` be finite. For `β ∈ O_C` the vertex chart of the twist
`Aff β 1 G` (coordinate `x - β`) and the vertex chart of `G` are the same ring with the same
reduced chart (`isLocalIso_aff`, `ChartLocal.IsLocalIso` with `u = u' = 1`); a point over the
residue point of the twist which is not smooth carries `δ ≠ 0` (`DiscBridge.dinf_eq_zero_iff`),
and its transport is a closed point of the reduced chart of `G` with `δ ≠ 0` containing
`x̄ - β̄`. There are only finitely many such closed points (`LocalFormula.finite_dinf₀`, a
conductor element), and each contains `x̄ - β̄` for at most one `β̄`:

* `finite_badResidue`: finitely many residues `β̄` with a non-smooth point over `x̄ = β̄`;
* **`S8A.finiteBadFor`**: `S8A.FiniteBadFor C F` (no hypothesis on `F` beyond finiteness).
-/

open IsLocalRing Metric
open scoped NNReal

namespace SemistableReduction

namespace S8A

namespace FiniteBad

open GaussFibre ChartLocal DeltaCount SmoothVertex DiscCount FundamentalInequality GaussStability
  LocalFormula DiscBridge AffineTwist W10Route

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField isCurveFunctionField_F
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Twist

variable {β : C} (hβ : ‖β‖ ≤ 1)

include hβ in
lemma gauss1_aff_one (ψ : RatFunc C) : gauss1 C (aff β 1 one_ne_zero ψ) = gauss1 C ψ := by
  have h := gauss1_aff_symm (a := β) (c := (1 : C)) (hc0 := one_ne_zero)
    (aff β 1 one_ne_zero ψ)
  rw [AlgEquiv.symm_apply_apply] at h
  rw [h]
  have hu : Units.mk0 ‖(1 : C)‖₊ (nnnorm_ne_zero_iff.2 one_ne_zero) = 1 :=
    Units.ext (by simp)
  rw [hu, Splitting.gaussRat_eq_of_le (b := 0)]
  rw [sub_zero, NormedField.valuation_apply, Units.val_one]
  exact_mod_cast hβ

include hβ in
omit [Algebra C G] [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G] in
/-- Every extension of `w_{0,1}` to `G` is one to the twist `Aff β 1 G`. -/
lemma extUnaff_surjective : Function.Surjective (DVRDescent.extUnaff (G := G) hβ) := fun w ↦
  ⟨⟨w.1, Valuation.ext fun ψ ↦ by
    rw [Valuation.comap_apply]
    change w.1 (algebraMap (RatFunc C) G (aff β 1 one_ne_zero ψ)) = gauss1 C ψ
    rw [← Valuation.comap_apply, w.2]
    exact gauss1_aff_one hβ ψ⟩, rfl⟩

/-- The identity `Aff β 1 G → G`. -/
noncomputable abbrev unAff : Aff β 1 one_ne_zero G ≃+* G := (toAff one_ne_zero).symm

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G] in
lemma unAff_algebraMap (c : C) :
    unAff (β := β) (algebraMap C (Aff β 1 one_ne_zero G) c) = algebraMap C G c := rfl

include hp hp1 hβ in
lemma mem_intRing_unAff [Fintype (Ext C G)] [Fintype (Ext C (Aff β 1 one_ne_zero G))]
    {f : Aff β 1 one_ne_zero G}
    (hf : f ∈ intRing C (Aff β 1 one_ne_zero G) (xF C (Aff β 1 one_ne_zero G))) :
    unAff f ∈ intRing C G (xF C G) := by
  have hD : IsIntegral (discRing (0 : C) 1) f :=
    isIntegral_of_le hp hp1 hf.1 (valuation_le_one_of_mem_intRing hf)
  have hD' : unAff f ∈ DRint (0 : C) 1 G := (mem_drint_aff_iff hβ (unAff f)).1 hD
  exact coe_mem_intRing (⟨unAff f, hD'⟩ : DRint (0 : C) 1 G)

include hp hp1 hβ in
lemma mem_intRing_aff [Fintype (Ext C G)] [Fintype (Ext C (Aff β 1 one_ne_zero G))] {g : G}
    (hg : g ∈ intRing C G (xF C G)) :
    unAff.symm g ∈ intRing C (Aff β 1 one_ne_zero G) (xF C (Aff β 1 one_ne_zero G)) := by
  have hD : IsIntegral (discRing (0 : C) 1) g :=
    isIntegral_of_le hp hp1 hg.1 (valuation_le_one_of_mem_intRing hg)
  have hD' : unAff.symm g ∈ DRint (0 : C) 1 (Aff β 1 one_ne_zero G) :=
    (mem_drint_aff_iff hβ g).2 hD
  exact coe_mem_intRing (⟨unAff.symm g, hD'⟩ : DRint (0 : C) 1 (Aff β 1 one_ne_zero G))

include hp hp1 hβ in
/-- **The reduced charts of `G` and of `Aff β 1 G` agree** (`u = u' = 1`). -/
theorem isLocalIso_aff [Fintype (Ext C G)] [Fintype (Ext C (Aff β 1 one_ne_zero G))]
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C (Aff β 1 one_ne_zero G) ↦
      red C (xF C (Aff β 1 one_ne_zero G)) w)
      (redRing C (Aff β 1 one_ne_zero G) (xF C (Aff β 1 one_ne_zero G))))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C G ↦ red C (xF C G) w) (redRing C G (xF C G))) :
    IsLocalIso hΛ₁ hΛ₂ (extEmb unAff unAff_algebraMap (DVRDescent.extUnaff hβ) (fun _ _ ↦ rfl))
      (fun w ↦ red C 1 w) (fun w' ↦ red C 1 w') :=
  isLocalIso_of (F₁ := Aff β 1 one_ne_zero G) (F₂ := G) unAff unAff_algebraMap
    (DVRDescent.extUnaff hβ) (fun _ _ ↦ rfl) hΛ₁ hΛ₂ (one_mem _) (one_mem _)
    (fun f hf ↦ ⟨0, by rw [pow_zero, one_mul]; exact mem_intRing_unAff (G := G) hp hp1 hβ hf,
      fun w' hw' ↦ absurd (extUnaff_surjective hβ w') hw'⟩)
    (fun g hg ↦ ⟨0, by rw [pow_zero, one_mul]; exact mem_intRing_aff (G := G) hp hp1 hβ hg⟩)
    (fun _ _ _ _ ↦ by rw [map_one, red_one, map_one])
    (fun w' _ _ _ ↦ ⟨extUnaff_surjective hβ w', by rw [map_one, red_one, map_one]⟩)

end Twist

/-! ### Finiteness -/

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] in
lemma xF_unAff (β : C) :
    unAff (xF C (Aff β 1 one_ne_zero G)) = xF C G - algebraMap C G β := by
  change algebraMap (RatFunc C) G (aff β 1 one_ne_zero RatFunc.X) = _
  rw [aff_apply, affHom_X, gaussCoord_eq, inv_one, map_one, one_mul, map_sub,
    ← IsScalarTower.algebraMap_apply C (RatFunc C) G]

/-- A constant of the reduced chart. -/
noncomputable abbrev cst [Fintype (Ext C G)]
    (hΛ : IsChart 𝓀 (fun w : Ext C G ↦ red C (xF C G) w) (redRing C G (xF C G))) (r : 𝓀) :
    redRing C G (xF C G) :=
  ⟨fun _ ↦ algebraMap 𝓀 _ r, hΛ.const r⟩

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) G] in
/-- A closed point contains `x̄ - r̄` for at most one `r̄`. -/
lemma eq_of_mem [Fintype (Ext C G)]
    (hΛ : IsChart 𝓀 (fun w : Ext C G ↦ red C (xF C G) w) (redRing C G (xF C G)))
    {𝔫 : Ideal (redRing C G (xF C G))} (h𝔫 : 𝔫 ≠ ⊤) {r₁ r₂ : 𝓀}
    (h₁ : xbar hΛ - cst hΛ r₁ ∈ 𝔫) (h₂ : xbar hΛ - cst hΛ r₂ ∈ 𝔫) : r₁ = r₂ := by
  by_contra hne
  have hd : cst hΛ (r₂ - r₁) ∈ 𝔫 := by
    have := 𝔫.sub_mem h₁ h₂
    convert this using 1
    exact Subtype.ext (funext fun w ↦ by simp)
  have hu : cst hΛ (r₂ - r₁) * cst hΛ (r₂ - r₁)⁻¹ = 1 := by
    refine Subtype.ext (funext fun w ↦ ?_)
    change algebraMap 𝓀 (ResidueField w.1.valuationSubring) (r₂ - r₁) *
      algebraMap 𝓀 (ResidueField w.1.valuationSubring) (r₂ - r₁)⁻¹ = 1
    rw [← map_mul, mul_inv_cancel₀ (sub_ne_zero.2 (Ne.symm hne)), map_one]
  exact h𝔫 (𝔫.eq_top_of_isUnit_mem hd (isUnit_iff_exists_inv.2 ⟨_, hu⟩))

variable (G) in
/-- The residues `β̄` over which some point of the vertex chart of `Aff β 1 G` is not smooth. -/
def badResidues : Set 𝓀 :=
  {r | ∃ β : HenselComplete.integers C, residue (HenselComplete.integers C) β = r ∧
    ¬ SmoothOver C (Aff (β : C) 1 one_ne_zero G)}

set_option maxHeartbeats 800000 in
-- the transport between the two reduced charts elaborates slowly
include hp hp1 in
/-- **Finitely many bad residue points** of the vertex chart. -/
theorem finite_badResidues : (badResidues (C := C) G).Finite := by
  classical
  haveI := finite_ext (C := C) (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_orthonormal_basis (F := G) ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := G) hp hp1)
  set hΛ := isChart_x hb
  set S := {𝔫 : Ideal (redRing C G (xF C G)) | 𝔫.IsMaximal ∧
      dinf 𝓀 (fun w : Ext C G ↦ ResidueField w.1.valuationSubring) hΛ 𝔫 ≠ 0}
  have hS : S.Finite := finite_dinf₀ hp hp1 hΛ
  refine (hS.biUnion fun 𝔫 h𝔫 ↦ (show {r : 𝓀 | xbar hΛ - cst hΛ r ∈ 𝔫}.Subsingleton from
    fun r₁ h₁ r₂ h₂ ↦ eq_of_mem hΛ h𝔫.1.ne_top h₁ h₂).finite).subset ?_
  rintro _ ⟨β, rfl, hbad⟩
  have hβ : ‖(β : C)‖ ≤ 1 := HenselComplete.norm_le_one β
  set K := Aff (β : C) 1 one_ne_zero G
  haveI := finite_ext (C := C) (F := K) hp hp1
  letI : Fintype (Ext C K) := Fintype.ofFinite _
  obtain ⟨bK, hbK⟩ := exists_orthonormal_basis (F := K) ramificationIdx_eq_one
    (sum_inertiaDeg_eq (F := K) hp hp1)
  set hΛK := isChart_x hbK
  -- a non-smooth point of the twisted chart
  obtain ⟨P', hP'max, hP', hns⟩ : ∃ P' : Ideal (DRint (0 : C) 1 K), P'.IsMaximal ∧
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 K)) = discIdeal (0 : C) 1 ∧
      ¬ IsDiscSmooth P' := by
    by_contra h
    push Not at h
    exact hbad h
  haveI := hP'max
  set 𝔫K := P'.map (redΛ K)
  haveI h𝔫K : 𝔫K.IsMaximal := map_isMaximal hp hp1 hP'
  have hx : xbar hΛK ∈ 𝔫K := xbar_mem_map hΛK hP'
  have hd : dinf 𝓀 (fun w : Ext C K ↦ ResidueField w.1.valuationSubring) hΛK 𝔫K ≠ 0 := by
    intro h0
    have := (dinf_eq_zero_iff hp hp1 hΛK hx).1 h0
    rw [comap_map hp hp1 hP'] at this
    exact hns this
  -- its transport to the chart of `G`
  have H := isLocalIso_aff hp hp1 hβ hΛK hΛ
  have hu : (⟨_, H.mem_u⟩ : redRing C K (xF C K)) ∉ 𝔫K := by
    have : (⟨_, H.mem_u⟩ : redRing C K (xF C K)) = 1 :=
      Subtype.ext (funext fun w ↦ red_one)
    rw [this]
    exact fun h ↦ h𝔫K.ne_top ((Ideal.eq_top_iff_one _).2 h)
  set 𝔫 := trI hΛK hΛ (extEmb unAff unAff_algebraMap (DVRDescent.extUnaff hβ) (fun _ _ ↦ rfl)) 𝔫K
  have hmem : unAff (xF C K) ∈ intRing C G (xF C G) :=
    mem_intRing_unAff hp hp1 hβ (coe_mem_intRing (xD : DRint (0 : C) 1 K))
  have hx' : (⟨_, red_mem_redRing hmem⟩ : redRing C G (xF C G)) ∈ 𝔫 :=
    (H.mem_iff_mem_trI h𝔫K hu (xbar hΛK) ⟨_, red_mem_redRing hmem⟩ fun b _ _ ↦ by
      have h := val_pmap_of (extEmb unAff unAff_algebraMap (DVRDescent.extUnaff hβ)
        (fun _ _ ↦ rfl)) b (extEmb_e_red unAff unAff_algebraMap (DVRDescent.extUnaff hβ)
        (fun _ _ ↦ rfl) b.1 (xF C K))
      exact (iff_of_eq (congrArg (· < 1) h)).symm).1 hx
  have he : (⟨_, red_mem_redRing hmem⟩ : redRing C G (xF C G)) =
      xbar hΛ - cst hΛ (residue _ β) := by
    refine Subtype.ext (funext fun w ↦ ?_)
    change red C (unAff (xF C K)) w = red C (xF C G) w - algebraMap 𝓀 _ (residue _ β)
    have h1 : w.1 (xF C G) ≤ 1 := valuation_le_one_of_mem_intRing (xF_mem_intRing (F := G)) w
    have h2 : w.1 (algebraMap C G β) ≤ 1 := by
      rw [IsScalarTower.algebraMap_apply C (RatFunc C) G, ← Valuation.comap_apply, w.2,
        gauss1_algebraMap_C]
      exact_mod_cast HenselComplete.norm_le_one β
    rw [xF_unAff, red_sub h1 h2, red_algebraMap_C _ (by exact_mod_cast hβ)]
  refine Set.mem_biUnion (x := 𝔫) ⟨H.trI_isMaximal h𝔫K hu, ?_⟩ ?_
  · rw [H.dinf_trI h𝔫K hu]
    exact hd
  · change xbar hΛ - cst hΛ (residue _ β) ∈ 𝔫
    rw [← he]
    exact hx'

end FiniteBad

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

open FiniteBad AffineTwist W10Route in
include hp hp1 in
/-- **O6.3: a disc has only finitely many bad residue balls.** -/
theorem finiteBadFor (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] : FiniteBadFor C F := by
  classical
  rintro _ ⟨a, c, hc, rfl⟩
  set G := Aff a c hc F
  set lift : 𝓀 → HenselComplete.integers C := Function.surjInv (residue_surjective (R :=
    HenselComplete.integers C))
  refine ((finite_badResidues hp hp1 (G := G)).image
    fun r ↦ ball (a + c * (lift r : C)) ‖c‖).subset ?_
  rintro _ ⟨⟨a', b, c', hc', hD, hb, rfl⟩, hbad⟩
  obtain ⟨hcc, -⟩ := (BallTree.closedBall_eq_closedBall_iff' hc hc').1 hD
  rw [← hcc] at hbad ⊢
  have hba : ‖b - a‖ ≤ ‖c‖ := mem_closedBall_iff_norm.1 hb
  set β := (b - a) / c
  have hβ : ‖β‖ ≤ 1 := by
    rw [norm_div, div_le_one (norm_pos_iff.2 hc)]
    exact hba
  have hbβ : b = a + c * β := by
    simp only [β]
    field_simp
    ring
  set βO : HenselComplete.integers C := ⟨β, (HenselComplete.mem_integers_iff _).2 hβ⟩
  refine ⟨residue _ βO, ⟨βO, rfl, fun hsm ↦ hbad ?_⟩, ?_⟩
  · rw [Transport.ballGood_iff hc, hbβ]
    change SmoothOver C (Aff (a + c * β) c hc F)
    have key := smoothOver_congr (C := C) (G := F)
      (algebra_aff_aff_eq (F' := F) (a := a) (β := β) hc)
    exact key (fun _ _ ↦ hsm)
      (inferInstanceAs (IsScalarTower C (RatFunc C) (Aff (a + c * β) c hc F)))
      (inferInstanceAs (FiniteDimensional (RatFunc C) (Aff (a + c * β) c hc F)))
  · have hl : residue _ (lift (residue _ βO)) = residue _ βO :=
      Function.surjInv_eq (residue_surjective (R := HenselComplete.integers C)) _
    have h0 : residue _ (lift (residue _ βO) - βO) = 0 := by rw [map_sub, hl, sub_self]
    rw [residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one] at h0
    change ‖((lift (residue _ βO) : C) - β)‖ < 1 at h0
    change ball (a + c * (lift (residue _ βO) : C)) ‖c‖ = ball b ‖c‖
    refine (IsUltrametricDist.ball_eq_of_mem (mem_ball.2 ?_)).symm
    rw [hbβ, dist_eq_norm, show a + c * (lift (residue _ βO) : C) - (a + c * β) =
      c * (lift (residue _ βO) - β) by ring, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.2 hc) h0

end S8A

end SemistableReduction
