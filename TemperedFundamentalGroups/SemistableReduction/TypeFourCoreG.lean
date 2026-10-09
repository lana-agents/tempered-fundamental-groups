/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourCore
import TemperedFundamentalGroups.SemistableReduction.TypeFourConv
import TemperedFundamentalGroups.SemistableReduction.TypeFourSCoord

/-!
# Smoothness from a topological generator (`CoreGFor`)

Blueprint §9.12, leaf T4, part (G). Let `Bₙ = ball aₙ ‖cₙ‖` be nested with empty intersection,
`ξ'` an extension to `F` of their limit `ξ` (a type-4 point), and `C(s)` dense in `(F, ξ')`.

* `exists_good_coord` (`TypeFourCoord`): we may assume `s` integral over `C[x]` and `x` integral
  over `C[s]`;
* `isTypeFour_scoord`, `exists_center_injective`: a disc `E₀ ∋ η = ξ'|_{C(s)}` in the
  `s`-coordinate on whose chart distinct extensions of `η` have distinct centres;
* `eventually_val_le_one` (`TypeFourConv`): for large `n`, all components through the centre `P₁`
  of `ξ'` on the chart of `Bₙ` lie over `E₀`;
* **`isDiscSmooth_of_close`** (one ball): the components through `P₁` restrict to Gauss points of
  `C(s)` (`GaussLimit.eq_gaussRat_of_le`; a component over a type-4 point of `C(s)` would have
  residue field `k`, `exists_sub_lt_one`); the smallest closed `s`-disc containing them, recentred
  at the residue of `ξ'` (`exists_res_eq`), is an `s`-disc `E* ⊆ E₀` whose Gauss point is one of
  the components; its chart has a sheet at `ξ'` (`discDegree_sheet_eq_one`), and
  `isDiscSmooth_of_sheet` (`TypeFourCore`) applies;
* **`coreGFor`**: `TypeFour.CoreGFor C F`.
-/

open Polynomial Metric
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open GaussFibre DiscCount SmoothVertex AffineTwist LocalGlobal Splitting GaussLimit

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField GaussFibre.isCurveFunctionField_F

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-! ### Transport of integrality -/

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- Integrality over `C[u]` is transported along a `C`-algebra isomorphism. -/
lemma isIntegral_map_adjoin {K₁ K₂ : Type*} [Field K₁] [Field K₂] [Algebra C K₁] [Algebra C K₂]
    (φ : K₁ ≃ₐ[C] K₂) {u y : K₁} (hy : IsIntegral (Algebra.adjoin C {u}) y) {u' : K₂}
    (hu : φ u ∈ Algebra.adjoin C {u'}) : IsIntegral (Algebra.adjoin C {u'}) (φ y) := by
  have hle : (Algebra.adjoin C {u}).map φ.toAlgHom ≤ Algebra.adjoin C {u'} := by
    rw [AlgHom.map_adjoin, Set.image_singleton]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hu)
  let ψ : Algebra.adjoin C {u} →+* Algebra.adjoin C {u'} :=
    { toFun := fun a ↦ ⟨φ a, hle ⟨a, a.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  exact IsIntegral.map_of_comp_eq ψ φ.toRingEquiv.toRingHom (by ext; rfl) hy

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F]

/-- `toAff` as a `C`-algebra isomorphism. -/
noncomputable def toAffC {a c : C} (hc : c ≠ 0) : F ≃ₐ[C] Aff a c hc F :=
  { toAff hc with commutes' := fun _ ↦ rfl }

omit [IsAlgClosed C] in
/-- Integrality over `C[x]` passes to the twisted coordinate. -/
lemma isIntegral_toAff {a c : C} (hc : c ≠ 0) {y : F}
    (hy : IsIntegral (Algebra.adjoin C {xF C F}) y) :
    IsIntegral (Algebra.adjoin C {xF C (Aff a c hc F)}) (toAff (a := a) hc y) := by
  refine isIntegral_map_adjoin (toAffC hc) hy ?_
  have hx1 : xF C (Aff a c hc F) =
      toAff hc (algebraMap C F c⁻¹ * (xF C F - algebraMap C F a)) := by
    rw [xF_aff (hc0 := hc), gaussCoord_eq, map_mul, map_sub, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hx : toAffC (a := a) hc (xF C F) =
      algebraMap C _ c * xF C (Aff a c hc F) + algebraMap C _ a := by
    rw [hx1]
    change toAff hc (xF C F) = toAff hc (algebraMap C F c) * toAff hc _ +
      toAff hc (algebraMap C F a)
    rw [← map_mul, ← map_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hc, map_one, one_mul,
      sub_add_cancel]
  rw [hx]
  exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Algebra.self_mem_adjoin_singleton C _)) (Subalgebra.algebraMap_mem _ _)

/-! ### One ball -/

section Ball

variable [FiniteDimensional (RatFunc C) F] [Algebra.IsSeparable (RatFunc C) F] [CharZero C]
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

omit [Algebra.IsSeparable (RatFunc C) F] [CharZero C] in
/-- **The components restrict to Gauss points of `C(s)`.** -/
theorem exists_gauss {s : F} (hs : Transcendental C s) {a c : C} (hc : c ≠ 0)
    (v : Ext C (Aff a c hc F)) :
    ∃ (β : C) (r : ℝ≥0), 0 < r ∧
      ∀ b : C, v.1 (toAff hc (s - algebraMap C F b)) = max ‖β - b‖₊ r := by
  set u : Valuation (RatFunc C) ℝ≥0 :=
    (v.1.comap (toAff hc).toRingHom).comap (coordAlgHom hs).toRingHom
  have hu : ∀ φ : RatFunc C, u φ = v.1 (toAff hc (coordAlgHom hs φ)) := fun _ ↦ rfl
  have huX : ∀ b : C, radius u b = v.1 (toAff hc (s - algebraMap C F b)) := by
    intro b
    rw [radius, hu, coordAlgHom_algebraMap, map_sub, aeval_X, aeval_C]
  have huC : ∀ b : C, u (algebraMap C (RatFunc C) b) = NormedField.valuation b := by
    intro b
    rw [hu, AlgHom.commutes]
    change v.1 (algebraMap C (Aff a c hc F) b) = _
    rw [valuation_algebraMap_C', NormedField.valuation_apply]
  -- the radius of `u` attains its minimum
  obtain ⟨β, hβ⟩ : ∃ β : C, ∀ b, radius u β ≤ radius u b := by
    by_contra! hnomin
    have hu4 : IsTypeFour u := ⟨huC, hnomin⟩
    -- `u` would be a type-4 point of `C(s)`, so `κ(v) = k`
    set w : Valuation (SCoord C s hs) ℝ≥0 := v.1.comap ((toS hs).symm.trans (toAff hc)).toRingHom
    have hw : w.comap (algebraMap (RatFunc C) (SCoord C s hs)) = u := rfl
    set y : SCoord C s hs := toS hs ((toAff hc).symm (xF C (Aff a c hc F)))
    have hy : w y = 1 := by
      change v.1 (toAff hc ((toS hs).symm (toS hs ((toAff hc).symm (xF C (Aff a c hc F)))))) = 1
      rw [RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply, valuation_xF]
    obtain ⟨c', hc'1, hc'⟩ := exists_sub_lt_one hu4 hw hy.le
    have hlt : v.1 (xF C (Aff a c hc F) - algebraMap C (Aff a c hc F) c') < 1 := by
      change v.1 (toAff hc ((toS hs).symm (y - algebraMap C (SCoord C s hs) c'))) < 1 at hc'
      rwa [map_sub, map_sub, RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply] at hc'
    have hc'1' : ‖c'‖₊ ≤ 1 := by exact_mod_cast hc'1
    have hred : red C (xF C (Aff a c hc F)) v = algebraMap 𝓀 _
        (IsLocalRing.residue (HenselComplete.integers C) ⟨c', by simpa using hc'1'⟩) := by
      have hc'v : v.1 (algebraMap C (Aff a c hc F) c') ≤ 1 := by
        rw [valuation_algebraMap_C']; exact hc'1'
      rw [← red_algebraMap_C c' hc'1', ← sub_eq_zero, ← red_sub (valuation_xF v).le hc'v,
        (red_eq_zero_iff ((Valuation.map_sub _ _ _).trans
          (max_le (valuation_xF v).le hc'v))).2 hlt]
    exact transcendental_red_x v (hred ▸ isAlgebraic_algebraMap _)
  have hgauss := eq_gaussRat_of_le huC hβ
  refine ⟨β, radius u β, (zero_le).lt_of_ne (radius_ne_zero u β).symm, fun b ↦ ?_⟩
  rw [← huX]
  conv_lhs => rw [radius, hgauss]
  rw [gaussRat_algebraMap, gauss_X_sub_C, val_radiusUnit, NormedField.valuation_apply]

omit [Algebra.IsSeparable (RatFunc C) F] in
include hp hp1 in
/-- **Smoothness at the centre on one small ball.** Let `C(s)` be dense in `(F, ξ')`, with `s`
integral over `C[x]` and `x` integral over `C[s]`, let `E₀ = D(b₀, |a₀ - b₀|) ∋ η` be an
`s`-disc on whose chart distinct extensions of `η = ξ'|_{C(s)}` have distinct centres, and `P₁`
the centre of `ξ'` on the chart of `ball a ‖c‖`. If every component through `P₁` lies over the
closed disc of `E₀` (`hF1`), then `P₁` is smooth. -/
theorem isDiscSmooth_of_close {ξ' : Valuation F ℝ≥0}
    (hξ : IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F)))
    {s : F} (hs : Transcendental C s) (hsx : IsIntegral (Algebra.adjoin C {xF C F}) s)
    (hxs : IsIntegral (Algebra.adjoin C {s}) (xF C F)) (hd : CoordDense C ξ' s) {a₀ b₀ : C}
    (hb₀ : radius ((valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))) b₀ <
      radius ((valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))) a₀)
    (hinj : ∀ (ξ₁ ξ₂ : Valuation (SCoord C s hs) ℝ≥0)
      (h₁ : ξ₁.comap (algebraMap (RatFunc C) (SCoord C s hs)) =
        (valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs)))
      (h₂ : ξ₂.comap (algebraMap (RatFunc C) (SCoord C s hs)) =
        (valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))),
      center (isDiscVal_comap (isTypeFour_scoord hs hξ) h₁ hb₀) =
        center (isDiscVal_comap (isTypeFour_scoord hs hξ) h₂ hb₀) → ξ₁ = ξ₂)
    {a c : C} (hc : c ≠ 0)
    (hlt : ξ' (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) a)) < ‖c‖₊)
    (P₁ : Ideal (DRint (0 : C) 1 (Aff a c hc F))) [hP₁ : P₁.IsMaximal]
    (hc₁ : P₁.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff a c hc F))) =
      discIdeal (0 : C) 1)
    (hcen : ∀ y ∈ P₁, ξ' ((toAff hc).symm (y : Aff a c hc F)) < 1)
    (hF1 : ∀ v : Ext C (Aff a c hc F), Through P₁ v →
      v.1 (toAff hc (s - algebraMap C F b₀)) ≤ ‖a₀ - b₀‖₊) :
    IsDiscSmooth P₁ := by
  classical
  haveI : Finite (Ext C (Aff a c hc F)) := finite_ext (F := Aff a c hc F) hp hp1
  letI : Fintype (Ext C (Aff a c hc F)) := Fintype.ofFinite _
  set G₁ := Aff a c hc F
  have hC : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊ := fun b ↦ by
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, ← Valuation.comap_apply, hξ.map_C,
      NormedField.valuation_apply]
  set ξ₁ : Valuation G₁ ℝ≥0 := ξ'.comap (toAff (a := a) hc).symm.toRingHom
  have hξ₁app : ∀ y : F, ξ₁ (toAff (a := a) hc y) = ξ' y := fun y ↦ by
    change ξ' ((toAff (a := a) hc).symm (toAff (a := a) hc y)) = _
    rw [RingEquiv.symm_apply_apply]
  have hx₁ : xF C G₁ = toAff (a := a) hc (algebraMap C F c⁻¹ * (xF C F - algebraMap C F a)) := by
    rw [xF_aff (hc0 := hc), gaussCoord_eq, map_mul, map_sub, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply]
  have hξ₁dv : IsDiscVal (0 : C) 1 (ξ₁.comap (algebraMap (RatFunc C) G₁)) := by
    refine ⟨fun b ↦ ?_, ?_⟩
    · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply]
      change ξ₁ (toAff (a := a) hc (algebraMap C F b)) = _
      rw [hξ₁app, hC]
    · rw [Valuation.comap_apply, SmoothVertex.gaussCoord_zero_one]
      change ξ₁ (xF C G₁) < 1
      rw [hx₁, hξ₁app, map_mul, hC, nnnorm_inv, inv_mul_lt_one₀ (nnnorm_pos.2 hc)]
      have : xF C F - algebraMap C F a =
          algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) a) := by
        rw [map_sub, ← IsScalarTower.algebraMap_apply]
      rw [this]
      exact hlt
  have hP₁c : P₁ = center hξ₁dv :=
    hP₁.eq_of_le (center_isMaximal one_ne_zero hξ₁dv).ne_top fun y hy ↦ hcen y hy
  have hξ₁ : ∀ y : DRint (0 : C) 1 G₁, y ∈ P₁ ↔ ξ₁ (y : G₁) < 1 := fun y ↦ by
    rw [hP₁c, DiscCount.mem_center_iff]
  have hξ₁le : ∀ y : DRint (0 : C) 1 G₁, ξ₁ (y : G₁) ≤ 1 := fun y ↦
    valuation_le_one_of_isIntegral hξ₁dv y.2
  obtain ⟨z, hzP, hz⟩ := exists_away' P₁ hc₁
  -- the components through `P₁` and their Gauss points in `s`
  set T := Finset.univ.filter fun v : Ext C G₁ ↦ Through P₁ v
  have hTmem : ∀ v, v ∈ T ↔ Through P₁ v := fun v ↦ by simp [T]
  obtain ⟨⟨v₀, Q₀, hQ₀⟩, hb₀'⟩ := exists_mem_discBranches hp hp1 P₁ hc₁
  have hv₀T : v₀ ∈ T := (hTmem v₀).2 ⟨Q₀, hQ₀, hb₀'⟩
  choose β r hr hβ using fun v : Ext C G₁ ↦ exists_gauss hs hc v
  set sv : C → G₁ := fun b ↦ toAff (a := a) hc (s - algebraMap C F b)
  have hsv : ∀ v b, v.1 (sv b) = max ‖β v - b‖₊ (r v) := fun v b ↦ hβ v b
  set β₁ := β v₀
  obtain ⟨j, hjT, hj⟩ := T.exists_max_image (fun v ↦ v.1 (sv β₁)) ⟨v₀, hv₀T⟩
  set R := j.1 (sv β₁)
  -- minimality of `R`
  have hRmin : ∀ b : C, ∃ v ∈ T, R ≤ v.1 (sv b) := by
    intro b
    have hRj : R = max ‖β j - β₁‖₊ (r j) := hsv j β₁
    rcases le_total ‖β j - β₁‖₊ (r j) with h | h
    · refine ⟨j, hjT, ?_⟩
      rw [hRj, max_eq_right h, hsv]
      exact le_max_right _ _
    · rw [hRj, max_eq_left h]
      have htri : ‖β j - β₁‖₊ ≤ max ‖β j - b‖₊ ‖β₁ - b‖₊ := by
        rw [show β j - β₁ = (β j - b) + (b - β₁) by ring,
          show ‖β₁ - b‖₊ = ‖b - β₁‖₊ by rw [← nnnorm_neg, neg_sub]]
        exact IsUltrametricDist.nnnorm_add_le_max _ _
      rcases le_total ‖β j - b‖₊ ‖β₁ - b‖₊ with h' | h'
      · refine ⟨v₀, hv₀T, ?_⟩
        rw [max_eq_right h'] at htri
        rw [hsv]
        exact htri.trans (le_max_left _ _)
      · refine ⟨j, hjT, ?_⟩
        rw [max_eq_left h'] at htri
        rw [hsv]
        exact htri.trans (le_max_left _ _)
  have hsβ : s - algebraMap C F β₁ ≠ 0 := fun h ↦ hs (by
    rw [sub_eq_zero] at h; rw [h]; exact isAlgebraic_algebraMap _)
  obtain ⟨δ, hδ, hRδ⟩ := ext_exists_eq_nnnorm j (y := sv β₁)
    (by simp only [sv]; exact (_root_.map_ne_zero _).2 hsβ)
  -- the element `f₀ = (s - β₁)/δ` and its residue at `P₁`
  set f₀ : G₁ := toAff (a := a) hc (algebraMap C F δ⁻¹ * (s - algebraMap C F β₁))
  have hf₀ : ∀ v : Ext C G₁, v.1 f₀ = ‖δ‖₊⁻¹ * v.1 (sv β₁) := fun v ↦ by
    simp only [f₀, sv, map_mul]
    rw [show toAff (a := a) hc (algebraMap C F δ⁻¹) = algebraMap C G₁ δ⁻¹ from rfl,
      valuation_algebraMap_C', nnnorm_inv]
  have hf₀int : IsIntegral (Algebra.adjoin C {xF C G₁}) f₀ :=
    isIntegral_toAff (a := a) hc ((isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ _)).mul
      (hsx.sub (isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ _))))
  have hδpos : 0 < ‖δ‖₊ := nnnorm_pos.2 hδ
  have hRδ' : R = ‖δ‖₊ := hRδ
  have hle_R : ∀ v : Ext C G₁, Through P₁ v → v.1 (sv β₁) ≤ ‖δ‖₊ := fun v hv ↦ by
    rw [← hRδ]; exact hj v ((hTmem v).2 hv)
  have hf₀le : ∀ v : Ext C G₁, Through P₁ v → v.1 f₀ ≤ 1 := fun v hv ↦ by
    rw [hf₀]
    calc ‖δ‖₊⁻¹ * v.1 (sv β₁) ≤ ‖δ‖₊⁻¹ * ‖δ‖₊ := mul_le_mul' le_rfl (hle_R v hv)
      _ = 1 := inv_mul_cancel₀ hδpos.ne'
  obtain ⟨c₀, hc₀ξ, -⟩ := exists_res_eq hp hp1 hc₁ hξ₁ hξ₁le hzP hz hf₀int hf₀le
  -- the disc `E* = D(b', |δ|)`
  set b' : C := β₁ + δ * c₀
  set σF : F := algebraMap C F δ⁻¹ * (s - algebraMap C F b')
  have hδF : algebraMap C F δ⁻¹ * algebraMap C F δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hδ, map_one]
  have hσF : toAff (a := a) hc σF = f₀ - algebraMap C G₁ c₀ := by
    have : σF = algebraMap C F δ⁻¹ * (s - algebraMap C F β₁) - algebraMap C F c₀ := by
      simp only [σF, b', map_add, map_mul]
      linear_combination (-algebraMap C F c₀) * hδF
    rw [this, map_sub]
    rfl
  have hsb' : s - algebraMap C F b' = algebraMap C F δ * σF := by
    simp only [σF]
    linear_combination (-(s - algebraMap C F b')) * hδF
  have hc₀1 : ‖(c₀ : C)‖₊ ≤ 1 := by exact_mod_cast (HenselComplete.mem_integers_iff _).1 c₀.2
  have hH : ∀ v : Ext C G₁, Through P₁ v → v.1 (toAff (a := a) hc σF) ≤ 1 := fun v hv ↦ by
    rw [hσF]
    exact (Valuation.map_sub _ _ _).trans (max_le (hf₀le v hv)
      (by rw [valuation_algebraMap_C']; exact hc₀1))
  have hin : ξ' σF < 1 := by
    rw [← hξ₁app, hσF]
    exact hc₀ξ
  have hsvb' : ∀ v : Ext C G₁, v.1 (sv b') = ‖δ‖₊ * v.1 (toAff (a := a) hc σF) := fun v ↦ by
    have : sv b' = algebraMap C G₁ δ * toAff (a := a) hc σF := by
      simp only [sv]
      rw [hsb', map_mul]
      rfl
    rw [this, map_mul, valuation_algebraMap_C']
  have hH' : ∃ v : Ext C G₁, Through P₁ v ∧ v.1 (toAff (a := a) hc σF) = 1 := by
    by_contra! H
    obtain ⟨v, hvT, hRv⟩ := hRmin b'
    have hv := (hTmem v).1 hvT
    have hlt1 : v.1 (toAff (a := a) hc σF) < 1 := lt_of_le_of_ne (hH v hv) (H v hv)
    rw [hsvb', hRδ'] at hRv
    exact absurd hRv (not_le.2 (mul_lt_of_lt_one_right hδpos hlt1))
  -- `E* ⊆ E₀`
  have hηlin : ∀ b : C, radius ((valS hs ξ').comap (algebraMap (RatFunc C) (SCoord C s hs))) b =
      ξ' (s - algebraMap C F b) := fun b ↦ by
    change valS hs ξ' (algebraMap (RatFunc C) (SCoord C s hs)
      (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
    rw [algebraMap_scoord, map_sub, aeval_X, aeval_C, valS_apply]
  have ha₀b₀ : ξ' (s - algebraMap C F b₀) < ‖a₀ - b₀‖₊ := by
    rw [← hηlin, ← nnnorm_neg, neg_sub, ← radius_eq_nnnorm (isTypeFour_scoord hs hξ) hb₀]
    exact hb₀
  have hδc : ‖δ‖ ≤ ‖a₀ - b₀‖ := by
    obtain ⟨v, hvT, hRv⟩ := hRmin b₀
    have := hRv.trans (hF1 v ((hTmem v).1 hvT))
    rw [hRδ'] at this
    exact_mod_cast this
  have hbb : ‖b' - b₀‖ ≤ ‖a₀ - b₀‖ := by
    have h1 : ξ' (s - algebraMap C F b') < ‖δ‖₊ := by
      rw [hsb', map_mul, hC]
      exact mul_lt_of_lt_one_right hδpos hin
    have h2 : ξ' (algebraMap C F (b' - b₀)) < ‖a₀ - b₀‖₊ := by
      rw [show algebraMap C F (b' - b₀) = (s - algebraMap C F b₀) - (s - algebraMap C F b') by
        rw [map_sub]; ring]
      refine (Valuation.map_sub _ _ _).trans_lt (max_lt ha₀b₀ (h1.trans_le ?_))
      exact_mod_cast hδc
    rw [hC] at h2
    exact_mod_cast h2.le
  -- the chart of `E*`
  set G₂ := Aff b' δ hδ (SCoord C s hs)
  set e : G₂ ≃+* G₁ := (toG hs b' hδ).symm.trans (toAff (a := a) hc)
  have he : ∀ c' : C, e.symm (algebraMap C G₁ c') = algebraMap C G₂ c' := fun _ ↦ rfl
  have heσ : e (xF C G₂) = toAff (a := a) hc σF := by
    rw [xF_G]
    change toAff (a := a) hc ((toG hs b' hδ).symm (toG hs b' hδ σF)) = _
    rw [RingEquiv.symm_apply_apply]
  have hσint : IsIntegral (Algebra.adjoin C {xF C F}) σF :=
    (isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ _)).mul
      (hsx.sub (isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ _)))
  have hσ : IsIntegral (Algebra.adjoin C {xF C G₁}) (e (xF C G₂)) := by
    rw [heσ]; exact isIntegral_toAff hc hσint
  have hτ : IsIntegral (Algebra.adjoin C {xF C G₂}) (e.symm (xF C G₁)) := by
    have hy : IsIntegral (Algebra.adjoin C {s})
        (algebraMap C F c⁻¹ * (xF C F - algebraMap C F a)) :=
      (isIntegral_algebraMap (R := Algebra.adjoin C {s}) (x := ⟨_, Subalgebra.algebraMap_mem _
        c⁻¹⟩)).mul (hxs.sub (isIntegral_algebraMap (R := Algebra.adjoin C {s})
        (x := ⟨_, Subalgebra.algebraMap_mem _ a⟩)))
    have hes : e.symm (xF C G₁) = toGC hs b' hδ (algebraMap C F c⁻¹ * (xF C F -
        algebraMap C F a)) := by
      rw [hx₁]
      change toG hs b' hδ ((toAff (a := a) hc).symm (toAff (a := a) hc _)) = _
      rw [RingEquiv.symm_apply_apply]
      rfl
    rw [hes]
    refine isIntegral_map_adjoin (toGC hs b' hδ) hy ?_
    have hsG : toGC hs b' hδ s = algebraMap C G₂ δ * xF C G₂ + algebraMap C G₂ b' := by
      rw [xF_G]
      change toG hs b' hδ s = toG hs b' hδ (algebraMap C F δ) * toG hs b' hδ _ +
        toG hs b' hδ (algebraMap C F b')
      rw [← map_mul, ← map_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hδ, map_one, one_mul,
        sub_add_cancel]
    rw [hsG]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Algebra.self_mem_adjoin_singleton C _)) (Subalgebra.algebraMap_mem _ _)
  -- the centre of `ξ'` on the chart of `E*`
  have hξ₂dv : IsDiscVal (0 : C) 1
      ((valG hs b' hδ ξ').comap (algebraMap (RatFunc C) G₂)) := by
    refine ⟨fun b ↦ ?_, ?_⟩
    · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, ← toG_algebraMap hs b' hδ,
        valG_apply, hC]
    · rw [Valuation.comap_apply, SmoothVertex.gaussCoord_zero_one]
      change valG hs b' hδ ξ' (xF C G₂) < 1
      rw [xF_G, valG_apply]
      exact hin
  set P₂ := center hξ₂dv
  haveI hP₂ : P₂.IsMaximal := center_isMaximal one_ne_zero hξ₂dv
  have hc₂ := comap_center hξ₂dv
  have hval₂ : ∀ y : G₂, valG hs b' hδ ξ' y = ξ₁ (e y) := fun y ↦ by
    change ξ' ((toG hs b' hδ).symm y) = ξ' ((toAff (a := a) hc).symm
      (toAff (a := a) hc ((toG hs b' hδ).symm y)))
    rw [RingEquiv.symm_apply_apply]
  have hξ₂ : ∀ y : DRint (0 : C) 1 G₂, y ∈ P₂ ↔ ξ₁ (e y) < 1 := fun y ↦ by
    rw [DiscCount.mem_center_iff, hval₂]
  have hξ₂le : ∀ y : DRint (0 : C) 1 G₂, ξ₁ (e y) ≤ 1 := fun y ↦ by
    rw [← hval₂]
    exact valuation_le_one_of_isIntegral hξ₂dv y.2
  have hdeg : ∃ ν : DiscVal (0 : C) 1, discDegree ν P₂ = 1 :=
    ⟨discValHalf, discDegree_sheet_eq_one hs hξ hd hb₀ hinj hδ hδc hbb hin P₂
      (fun y hy ↦ hy) discValHalf⟩
  exact isDiscSmooth_of_sheet hp hp1 e he hσ hτ hc₁ hξ₁ hξ₁le hc₂ hξ₂ hξ₂le hdeg
    (fun v hv ↦ heσ ▸ hH v hv) (by obtain ⟨v, hv, h1⟩ := hH'; exact ⟨v, hv, heσ ▸ h1⟩)

end Ball

/-! ### `CoreGFor` -/

section Main

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **`TypeFour.CoreGFor`**: if `C(s)` is dense in `(F, ξ')` for an extension `ξ'` of the limit
of nested balls `Bₙ` with empty intersection, the centre of `ξ'` on the chart of `Bₙ` is smooth for
all large `n`. -/
theorem coreGFor (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] : CoreGFor C F := by
  intro a c hc hnest hempty ξ' hC hlt s hd
  haveI : Algebra.IsSeparable (RatFunc C) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  -- the restriction of `ξ'` to `C(x)` is a type-4 point
  have hξ : IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F)) := by
    have hCx : ∀ b : C, ξ'.comap (algebraMap (RatFunc C) F) (algebraMap C (RatFunc C) b) =
        ‖b‖₊ := fun b ↦ by
      rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, hC]
    refine ⟨fun b ↦ by rw [hCx, NormedField.valuation_apply], fun b ↦ ?_⟩
    obtain ⟨m, hm⟩ := exists_norm_lt_norm_sub hc hnest hempty b
    refine ⟨a m, ?_⟩
    have hXa : ∀ e : C, algebraMap C[X] (RatFunc C) (X - Polynomial.C e) =
        RatFunc.X - algebraMap C (RatFunc C) e := fun e ↦ by
      rw [map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
    have h1 : radius (ξ'.comap (algebraMap (RatFunc C) F)) (a m) < ‖c m‖₊ := by
      rw [radius, hXa]; exact hlt m
    have h2 : radius (ξ'.comap (algebraMap (RatFunc C) F)) b = ‖a m - b‖₊ := by
      rw [radius, GaussLimit.algebraMap_X_sub_C (a m) b, Valuation.map_add_eq_of_lt_right, hCx]
      rw [hCx, ← nnnorm_neg, neg_sub]
      exact h1.trans (by exact_mod_cast hm)
    rw [h2, ← nnnorm_neg, neg_sub]
    exact h1.trans (by exact_mod_cast hm)
  -- a good generator
  obtain ⟨s', hd', hs', hsx, hxs⟩ := exists_good_coord hξ hd
  have hη := isTypeFour_scoord hs' hξ
  obtain ⟨a₀, ha₀⟩ := Splitting.exists_center_injective (F' := SCoord C s' hs') hη
  obtain ⟨b₀, hb₀⟩ := hη.no_min a₀
  have hηlin : ∀ b : C, radius ((valS hs' ξ').comap (algebraMap (RatFunc C) (SCoord C s' hs')))
      b = ξ' (s' - algebraMap C F b) := fun b ↦ by
    change valS hs' ξ' (algebraMap (RatFunc C) (SCoord C s' hs')
      (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
    rw [algebraMap_scoord, map_sub, aeval_X, aeval_C, valS_apply]
  have hab : a₀ - b₀ ≠ 0 := sub_ne_zero_of_radius_lt hη hb₀
  -- the components through the centres eventually lie over `E₀`
  set g : F := algebraMap C F (a₀ - b₀)⁻¹ * (s' - algebraMap C F b₀)
  have hgint : IsIntegral (Algebra.adjoin C {xF C F}) g :=
    (isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ _)).mul
      (hsx.sub (isIntegral_adjoin_of_mem (Subalgebra.algebraMap_mem _ _)))
  have hgle : ξ' g ≤ 1 := by
    simp only [g]
    rw [map_mul, hC, ← hηlin, nnnorm_inv, inv_mul_le_one₀ (nnnorm_pos.2 hab), ← nnnorm_neg,
      neg_sub, ← radius_eq_nnnorm hη hb₀]
    exact hb₀.le
  obtain ⟨N, hN⟩ := eventually_val_le_one hc hnest hempty hξ hlt hgint hgle
  refine ⟨N, fun n hn P' hP' hcen₀ hcen ↦ ?_⟩
  haveI := hP'
  refine isDiscSmooth_of_close hp hp1 hξ hs' hsx hxs hd' hb₀
    (fun ξ₁ ξ₂ h₁ h₂ ↦ ha₀ a₀ b₀ le_rfl hb₀ ξ₁ ξ₂ h₁ h₂) (hc n) (hlt n) P' hcen₀ hcen ?_
  intro v hv
  have := hN n hn P' hP' hcen v hv
  have hg' : toAff (a := a n) (hc n) g = algebraMap C (Aff (a n) (c n) (hc n) F) (a₀ - b₀)⁻¹ *
      toAff (hc n) (s' - algebraMap C F b₀) := by
    simp only [g, map_mul]; rfl
  rw [hg', map_mul, valuation_algebraMap_C', nnnorm_inv, inv_mul_le_one₀ (nnnorm_pos.2 hab)]
    at this
  exact this

end Main

end TypeFour

end SemistableReduction
