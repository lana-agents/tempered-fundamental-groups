/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.KummerSheet
import TemperedFundamentalGroups.SemistableReduction.Exhausting
import TemperedFundamentalGroups.SemistableReduction.NodeMaximum
import TemperedFundamentalGroups.SemistableReduction.NodeUpwardMain

/-!
# The node chart over a sheet

Blueprint §9.10, L4 (K6, exhaustion). Let `P'` be a degree-one point of `R' = DRint a c L`,
`0 < ‖l‖ < 1`, and `F' ⊇ L`. The node chart of the annulus `|l l₀ c| ≤ |x - a| ≤ |l c|` is
`Rint l₀ (Aff a (l c) F')` (the twist puts the outer vertex at `w_{0,1}`).

* `discRing_le_nodeRing`: `O_C[x] ⊆ O_C[x, c/x]`;
* `nodeMap`: the map `DRint a c L → Rint l₀ (Aff a (l c) F')`;
* `outer_restrict`: an outer branch through a point over `P'` restricts on `L` to the sheet
  extension.
-/

open Polynomial NNReal WithZero

namespace SemistableReduction

namespace KummerAnnulus

open DiscCount GaussTube GaussFibre AffineTwist KummerSheet PlaceNorm

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

lemma discRing_le_nodeRing (c : C) : discRing (0 : C) 1 ≤ nodeRing c := by
  change polyChart _ (gaussCoord (0 : C) 1) ≤ _
  rw [SmoothVertex.gaussCoord_zero_one]
  exact polyChart_le ZariskiModel.baseRing_le_nodeChart (X_mem_nodeRing c)

variable [IsAlgClosed C]
  {L : Type*} [Field L] [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra L F'] [IsScalarTower (RatFunc C) L F']
  [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {a c : C} (hc : c ≠ 0) (ν₀ : DiscVal a c) (P' : Ideal (DRint a c L)) [P'.IsMaximal]
  (h1 : discDegree ν₀ P' = 1) {l : C} (hl0 : l ≠ 0) (hl1 : ‖l‖ < 1) (l₀ : C)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
include hl1 in
lemma isIntegral_nodeMap (y : DRint a c L) :
    IsIntegral (nodeRing l₀) (toAff (mul_ne_zero hl0 hc) (algebraMap L F' (y : L)) :
      Aff a (l * c) (mul_ne_zero hl0 hc) F') := by
  have h1 : IsIntegral (discRing a c) (algebraMap L F' (y : L)) := by
    have := y.2.map (IsScalarTower.toAlgHom (discRing a c) L F')
    simpa using this
  have h2 : IsIntegral (discRing a (l * c)) (algebraMap L F' (y : L)) := by
    rw [mul_comm l c]
    exact drint_le F' hc hl0 hl1.le h1
  have h3 := (isIntegral_toAff_iff (mul_ne_zero hl0 hc) _).2 h2
  exact isIntegral_of_subring_le (discRing_le_nodeRing l₀) h3

include hl1 in
/-- The map `DRint a c L → Rint l₀ (Aff a (l c) F')`. -/
noncomputable def nodeMap : DRint a c L →+* Rint l₀ (Aff a (l * c) (mul_ne_zero hl0 hc) F') where
  toFun y := ⟨toAff (mul_ne_zero hl0 hc) (algebraMap L F' (y : L)),
    isIntegral_nodeMap (F' := F') hc hl0 hl1 l₀ y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma coe_nodeMap (y : DRint a c L) :
    ((nodeMap (F' := F') hc hl0 hl1 l₀ y : Rint l₀ _) : Aff a (l * c) (mul_ne_zero hl0 hc) F') =
      toAff (mul_ne_zero hl0 hc) (algebraMap L F' (y : L)) := rfl

/-! ### Kummer data at a radius -/

variable (p : ℕ) (γ : C) (θ : F') (f : L)

/-- **Purely inseparable Kummer data at the radius `‖l‖`** (the hypotheses of
`KummerSheet.insep_value`): polynomials `f̃, h̃` and `λ` such that `G = f̃ - h̃^p` has terms
`‖Gᵢ‖ ‖l‖^i ≤ ‖λ‖^p` with equality at an index `m` prime to `p`, `‖γ‖ < ‖λ‖ ≤ 1`, and `f̃(t)`
approximates `f` at the sheet extension to better than `‖λ‖^p`. -/
structure InsepData where
  f' : C[X]
  h' : C[X]
  lam : C
  m : ℕ
  hh' : ∀ i, ‖h'.coeff i‖₊ ≤ 1
  hγl : ‖γ‖₊ < ‖lam‖₊
  hl1' : ‖lam‖₊ ≤ 1
  hGle : ∀ i, ‖(f' - h' ^ p).coeff i‖ * ‖l‖ ^ i ≤ ‖lam‖ ^ p
  hGm : ‖(f' - h' ^ p).coeff m‖ * ‖l‖ ^ m = ‖lam‖ ^ p
  hpm : ¬ p ∣ m
  hf : (sheetExt hc ν₀ P' h1 hl0 hl1).1
    (f - algebraMap (RatFunc C) L (aeval (gaussCoord a c) f')) < ‖lam‖₊ ^ p

/-! ### Outer branches over the sheet -/

section Outer

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- **Outer branches over `P'` lie on the sheet**: if `(v, Q)` is an outer branch of the node chart
through a point `P''` over `P'`, then `v` restricts on `L` to the sheet extension. -/
theorem outer_restrict {l₀ : C} (hl₀1 : ‖l₀‖ < 1)
    (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v))
    {P'' : Ideal (Rint l₀ (Aff a (l * c) (mul_ne_zero hl0 hc) F'))}
    (hP : placeIdeal hl₀1 v hQ = P'') (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 l₀) = P') :
    v.1.comap ((toAff (mul_ne_zero hl0 hc)).toRingHom.comp (algebraMap L F')) =
      (sheetExt hc ν₀ P' h1 hl0 hl1).1 := by
  refine eq_sheetExt hc ν₀ P' h1 hl0 hl1 _ ?_ fun y hy ↦ ?_
  · have h2 := ((extAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).symm v).2
    refine Valuation.ext fun φ ↦ ?_
    have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u φ) h2
    simp only [Valuation.comap_apply] at this ⊢
    change v.1 (toAff (mul_ne_zero hl0 hc) (algebraMap L F' (algebraMap (RatFunc C) L φ))) = _
    rw [← IsScalarTower.algebraMap_apply]
    exact this
  · rw [← hP'', Ideal.mem_comap, ← hP, mem_placeIdeal_iff]
    have hle := valuation_le_one_R hl₀1 v (nodeMap (F' := F') hc hl0 hl1 l₀ y)
    have hlt : v.1 ((nodeMap (F' := F') hc hl0 hl1 l₀ y : Rint l₀ _) :
        Aff a (l * c) (mul_ne_zero hl0 hc) F') < 1 := hy
    rw [(red_eq_zero_iff hle).2 hlt, Q.res_zero]

variable [Fact p.Prime] [FiniteDimensional L F']

/-- **The outer extension over the sheet is unique**: two outer branches through points over `P'`
have the same vertex. -/
theorem outer_ext_eq (hp1 : ‖(p : C)‖ < 1) (hγ : γ ^ (p - 1) = -(p : C))
    (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f) {l₀ : C} (hl₀1 : ‖l₀‖ < 1)
    {v₁ v₂ : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F')}
    {Q₁ : CurvePlace 𝓀 (IsLocalRing.ResidueField v₁.1.valuationSubring)}
    {Q₂ : CurvePlace 𝓀 (IsLocalRing.ResidueField v₂.1.valuationSubring)}
    (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v₁))
    (hQ₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v₂))
    {P''₁ P''₂ : Ideal (Rint l₀ (Aff a (l * c) (mul_ne_zero hl0 hc) F'))}
    (hP₁ : placeIdeal hl₀1 v₁ hQ₁ = P''₁) (hP₂ : placeIdeal hl₀1 v₂ hQ₂ = P''₂)
    (h₁ : P''₁.comap (nodeMap (F' := F') hc hl0 hl1 l₀) = P')
    (h₂ : P''₂.comap (nodeMap (F' := F') hc hl0 hl1 l₀) = P') : v₁ = v₂ := by
  have hr₁ := outer_restrict hc ν₀ P' h1 hl0 hl1 hl₀1 v₁ hQ₁ hP₁ h₁
  have hr₂ := outer_restrict hc ν₀ P' h1 hl0 hl1 hl₀1 v₂ hQ₂ hP₂ h₂
  set e := (toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom
  have hu := insep_ext_unique hc ν₀ P' h1 hl0 hl1 p hp1 hγ (v₁ := v₁.1.comap e)
    (v₂ := v₂.1.comap e) (by rw [← Valuation.comap_comp]; exact hr₁)
    (by rw [← Valuation.comap_comp]; exact hr₂) hθ hspan D.hh' D.hγl D.hl1' D.hGle D.hGm D.hpm D.hf
  apply Subtype.ext
  refine Valuation.ext fun y ↦ ?_
  have := congrArg (fun u : Valuation F' ℝ≥0 ↦ u ((toAff (a := a) (mul_ne_zero hl0 hc)).symm y)) hu
  simpa [e] using this

end Outer

end KummerAnnulus

end SemistableReduction
