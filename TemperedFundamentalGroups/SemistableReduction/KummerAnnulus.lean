/-
Copyright (c) 2026 LANA Project. All rights reserved.
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

/-! ### Existence of inner branches -/

section InnerExists

open GaussTube

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable [CharZero C] {E : Type*} [Field E] [Algebra (RatFunc C) E] [Algebra C E]
  [IsScalarTower C (RatFunc C) E] [FiniteDimensional (RatFunc C) E]
  [Algebra.IsSeparable (RatFunc C) E]

/-- Every point of `R'` over the node has an inner branch. -/
lemma exists_innerBranch {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {c : C} (hc : ‖c‖ < 1)
    (hc0 : c ≠ 0) (P : Ideal (Rint c E)) [P.IsMaximal]
    (hP : P.comap (algebraMap (nodeRing c) (Rint c E)) = tubeIdeal c) :
    ∃ b, b ∈ innerBranches hc hc0 P := by
  classical
  haveI : Finite (Ext C E) := finite_ext (F := E) hp hp1
  letI : Fintype (Ext C E) := Fintype.ofFinite _
  haveI : Finite (Ext C (Inv c hc0 E)) := finite_ext (F := Inv c hc0 E) hp hp1
  letI : Fintype (Ext C (Inv c hc0 E)) := Fintype.ofFinite _
  obtain ⟨b, hb⟩ := exists_outerBranch hp hp1 hc hc0 P hP
  have hpos : 0 < vertexDegree hc P := by
    rw [vertexDegree_eq_sum]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun b : OuterBranch C E ↦
      if placeIdeal hc b.1 b.2.2 = P then ord (red C (xF C E) b.1) b.2.1 else 0)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_sigma.2 ⟨Finset.mem_univ b.1,
        Finset.mem_attach _ b.2⟩))
    simp only [hb, if_true]
    exact one_le_ord b.2.2
  rw [vertexDegree_eq_vertexDegree_inv hp hp1 hc hc0 P, vertexDegree_eq_sum] at hpos
  obtain ⟨b', -, hb'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  refine ⟨b', ?_⟩
  by_contra h
  exact hb' (if_neg h)

end InnerExists

/-! ### Gauss points under the affine twist -/

section AffRadius

/-- `w_{0,s} ∘ σ⁻¹ = w_{a, s|c|}` for the affine twist `σ : x ↦ (x - a)/c`. -/
lemma gaussRat_aff_symm {a c : C} (hc0 : c ≠ 0) (s : ℝ≥0ˣ) (φ : RatFunc C) :
    gaussRat (NormedField.valuation (K := C)) 0 s ((aff a c hc0).symm φ) =
      gaussRat (NormedField.valuation (K := C)) a
        (s * Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0)) φ := by
  set w₁ : Valuation (RatFunc C) ℝ≥0 := (gaussRat (NormedField.valuation (K := C)) 0 s).comap
      (aff a c hc0).symm.toRingEquiv.toRingHom
  have hw₁ : ∀ ψ, w₁ ψ = gaussRat (NormedField.valuation (K := C)) 0 s ((aff a c hc0).symm ψ) :=
    fun _ ↦ rfl
  have hC : ∀ b : C, w₁ (algebraMap C (RatFunc C) b) =
      gaussRat (NormedField.valuation (K := C)) a
        (s * Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0)) (algebraMap C (RatFunc C) b) := by
    intro b
    rw [hw₁, AlgEquiv.commutes, gaussRat_algebraMap_C, gaussRat_algebraMap_C]
  have hX : ∀ b : C, w₁ (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) =
      gaussRat (NormedField.valuation (K := C)) a
        (s * Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0))
        (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) := by
    intro b
    have hsymm : (aff a c hc0).symm (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) =
        algebraMap C (RatFunc C) (a - b) - algebraMap C (RatFunc C) (-c) * RatFunc.X := by
      apply (aff a c hc0).injective
      have hb : algebraMap C[X] (RatFunc C) (Polynomial.C b) = algebraMap C (RatFunc C) b := by
        rw [IsScalarTower.algebraMap_apply C C[X] (RatFunc C)]; rfl
      rw [AlgEquiv.apply_symm_apply, map_sub (aff a c hc0), map_mul (aff a c hc0),
        AlgEquiv.commutes, AlgEquiv.commutes, aff_apply, affHom_X, gaussCoord_eq, map_sub,
        RatFunc.algebraMap_X, hb]
      have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
      rw [map_inv₀, map_sub, map_neg]
      field_simp
      ring
    rw [hw₁, hsymm, GaussTube.gaussRat_C_sub_mul_X, gaussRat_algebraMap, gauss_X_sub_C,
      nnnorm_neg, NormedField.valuation_apply]
    simp [mul_comm]
  have h := valuation_ratFunc_ext_of_linear hC hX
  exact congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v φ) h

end AffRadius

/-! ### Zeros in a purely inseparable extension of `k(x)` -/

section Insep

open PlaceNorm CurvePlace IntermediateField

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

lemma mem_V_iff_expo {x : κ} (hx0 : x ≠ 0) {Q : CurvePlace k κ} (hQ : Q ∈ zeros k x)
    {a : k⟮x⟯} (ha : a ≠ 0) : (a : κ) ∈ Q.V ↔ 0 ≤ expo x a := by
  rw [← valuation_le_one_iff, valuation_eq_expo hx0 ha hQ, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  have h1 : (1 : ℤ) ≤ ord x Q := by exact_mod_cast one_le_ord hQ
  constructor
  · intro h
    by_contra h'
    push Not at h'
    nlinarith
  · intro h
    nlinarith

/-- **Zeros in a purely inseparable extension**: if every `p`-th power of `κ` lies in `k(x)`,
then `x` has at most one zero. -/
theorem eq_of_mem_zeros {p : ℕ} (hp : p ≠ 0) {x : κ} (hx0 : x ≠ 0)
    (hpow : ∀ z : κ, z ^ p ∈ k⟮x⟯) {Q₁ Q₂ : CurvePlace k κ} (h₁ : Q₁ ∈ zeros k x)
    (h₂ : Q₂ ∈ zeros k x) : Q₁ = Q₂ := by
  have key : ∀ Q : CurvePlace k κ, Q ∈ zeros k x → ∀ z : κ, z ≠ 0 →
      (z ∈ Q.V ↔ 0 ≤ expo x ⟨z ^ p, hpow z⟩) := by
    intro Q hQ z hz
    have ha : (⟨z ^ p, hpow z⟩ : k⟮x⟯) ≠ 0 := fun h ↦ hz (pow_eq_zero_iff hp |>.1 congr($h.1))
    rw [← mem_V_iff_expo hx0 hQ ha, ← valuation_le_one_iff, ← valuation_le_one_iff, map_pow,
      pow_le_one_iff hp]
  obtain ⟨V₁, hk₁, ht₁⟩ := Q₁
  obtain ⟨V₂, hk₂, ht₂⟩ := Q₂
  congr 1
  ext z
  by_cases hz : z = 0
  · subst hz; exact ⟨fun _ ↦ V₂.zero_mem, fun _ ↦ V₁.zero_mem⟩
  · exact (key _ h₁ z hz).trans (key _ h₂ z hz).symm

end Insep

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

/-- The identification `F' → Inv l₀ (Aff a (l c) F')`. -/
noncomputable def toInner {l₀ : C} (hl₀0 : l₀ ≠ 0) :
    F' →+* Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F') :=
  (toInv (F' := Aff a (l * c) (mul_ne_zero hl0 hc) F') hl₀0).toRingHom.comp
    (toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L]
  [Algebra (RatFunc C) L] [Algebra L F'] [IsScalarTower (RatFunc C) L F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma toInner_algebraMap {l₀ : C} (hl₀0 : l₀ ≠ 0) (φ : RatFunc C) :
    toInner (a := a) (F' := F') hc hl0 hl₀0 (algebraMap (RatFunc C) F' φ) =
      algebraMap (RatFunc C) (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
        (inv hl₀0 ((aff a (l * c) (mul_ne_zero hl0 hc)).symm φ)) := by
  rw [algebraMap_inv_apply, inv_inv_apply, algebraMap_aff_apply, AlgEquiv.apply_symm_apply]
  rfl

omit [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L] [Algebra (RatFunc C) L]
  [Algebra L F'] [IsScalarTower (RatFunc C) L F'] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
/-- The inner vertex restricts to `w_{a, |l l₀ c|}` on `C(x)`. -/
lemma inner_comap {l₀ : C} (hl₀0 : l₀ ≠ 0)
    (v : Ext C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F')))
    (φ : RatFunc C) :
    v.1 (toInner (a := a) (F' := F') hc hl0 hl₀0 (algebraMap (RatFunc C) F' φ)) =
      gaussRat (NormedField.valuation (K := C)) a
        (Units.mk0 ‖l * l₀ * c‖₊ (nnnorm_ne_zero_iff.2
          (mul_ne_zero (mul_ne_zero hl0 hl₀0) hc))) φ := by
  rw [toInner_algebraMap, ← Valuation.comap_apply, v.2, gaussRat_inv, gaussRat_aff_symm]
  congr 2
  ext
  simp [coe_invRad]
  ring

end Outer

section Inner

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- **Inner branches over `P'` lie on the inner sheet**: if `(v, Q)` is an inner branch of the
node chart through a point `P''` over `P'`, then `v` restricts on `L` to the sheet extension at
radius `|l l₀|`. -/
theorem inner_restrict {l₀ : C} (hl₀1 : ‖l₀‖ < 1) (hl₀0 : l₀ ≠ 0)
    (hll1 : ‖l * l₀‖ < 1) (v : Ext C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F')))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) v))
    {P'' : Ideal (Rint l₀ (Aff a (l * c) (mul_ne_zero hl0 hc) F'))}
    (hP : placeIdeal hl₀1 v hQ = P''.comap (rintEquiv hl₀0).symm.toRingHom)
    (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 l₀) = P') :
    v.1.comap ((toInner (a := a) (F' := F') hc hl0 hl₀0).comp (algebraMap L F')) =
      (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 hl₀0) hll1).1 := by
  refine eq_sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 hl₀0) hll1 _ ?_ fun y hy ↦ ?_
  · refine Valuation.ext fun φ ↦ ?_
    simp only [Valuation.comap_apply, RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply, inner_comap]
    rfl
  · rw [← hP'', Ideal.mem_comap]
    have hmem : rintEquiv hl₀0 (nodeMap (F' := F') hc hl0 hl1 l₀ y) ∈
        placeIdeal hl₀1 v hQ := by
      rw [mem_placeIdeal_iff]
      have hle := valuation_le_one_R hl₀1 v (rintEquiv hl₀0 (nodeMap (F' := F') hc hl0 hl1 l₀ y))
      have hlt : v.1 ((rintEquiv hl₀0 (nodeMap (F' := F') hc hl0 hl1 l₀ y) : Rint l₀ _) :
          Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F')) < 1 := hy
      rw [(red_eq_zero_iff hle).2 hlt, Q.res_zero]
    rw [hP, Ideal.mem_comap] at hmem
    simpa using hmem

end Inner

section Outer

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

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

/-- **The inner extension over the inner sheet is unique**: two inner branches through points over
`P'` have the same vertex. -/
theorem inner_ext_eq (hp1 : ‖(p : C)‖ < 1) (hγ : γ ^ (p - 1) = -(p : C))
    (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    {l₀ : C} (hl₀1 : ‖l₀‖ < 1) (hl₀0 : l₀ ≠ 0) (hll1 : ‖l * l₀‖ < 1)
    (D : InsepData hc ν₀ P' h1 (mul_ne_zero hl0 hl₀0) hll1 p γ f)
    {v₁ v₂ : Ext C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F'))}
    {Q₁ : CurvePlace 𝓀 (IsLocalRing.ResidueField v₁.1.valuationSubring)}
    {Q₂ : CurvePlace 𝓀 (IsLocalRing.ResidueField v₂.1.valuationSubring)}
    (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) v₁))
    (hQ₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) v₂))
    {P'' : Ideal (Rint l₀ (Aff a (l * c) (mul_ne_zero hl0 hc) F'))}
    (hP₁ : placeIdeal hl₀1 v₁ hQ₁ = P''.comap (rintEquiv hl₀0).symm.toRingHom)
    (hP₂ : placeIdeal hl₀1 v₂ hQ₂ = P''.comap (rintEquiv hl₀0).symm.toRingHom)
    (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 l₀) = P') : v₁ = v₂ := by
  have hr₁ := inner_restrict hc ν₀ P' h1 hl0 hl1 hl₀1 hl₀0 hll1 v₁ hQ₁ hP₁ hP''
  have hr₂ := inner_restrict hc ν₀ P' h1 hl0 hl1 hl₀1 hl₀0 hll1 v₂ hQ₂ hP₂ hP''
  set e := toInner (a := a) (F' := F') hc hl0 hl₀0
  have hu := insep_ext_unique hc ν₀ P' h1 (mul_ne_zero hl0 hl₀0) hll1 p hp1 hγ
    (v₁ := v₁.1.comap e) (v₂ := v₂.1.comap e) (by rw [← Valuation.comap_comp]; exact hr₁)
    (by rw [← Valuation.comap_comp]; exact hr₂) hθ hspan D.hh' D.hγl D.hl1' D.hGle D.hGm D.hpm D.hf
  apply Subtype.ext
  refine Valuation.ext fun y ↦ ?_
  exact congrArg (fun u : Valuation F' ℝ≥0 ↦ u y) hu

end Outer

/-! ### The residue field of the outer vertex -/

section OuterResidue

open IsLocalRing FundamentalInequality IntermediateField

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- The twisted field as an `L`-algebra (through the untwisted structure). Only a local instance
of low priority: it is generic in `L` and would otherwise shadow `Algebra C (Aff a' c' F')`. -/
@[reducible] noncomputable def algebraAff {a' c' : C} {hc' : c' ≠ 0} :
    Algebra L (Aff a' c' hc' F') := inferInstanceAs (Algebra L F')

attribute [local instance 10] algebraAff

omit [IsUltrametricDist C] [IsAlgClosed C] [Algebra (RatFunc C) L]
  [FiniteDimensional (RatFunc C) L] [Algebra.IsSeparable (RatFunc C) L] [Algebra (RatFunc C) F']
  [IsScalarTower (RatFunc C) L F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma algebraMap_aff_L {a' c' : C} {hc' : c' ≠ 0} (y : L) :
    algebraMap L (Aff a' c' hc' F') y = toAff hc' (algebraMap L F' y) := rfl


omit [FiniteDimensional (RatFunc C) F'] in
omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- **Residues of a sheet lie in `k(x̄)`** (general form): let `E` be a model of `F'` over `C(x)`
in which `C(x)` is moved by `τ`, with `w_{0,1} ∘ τ` the sheet valuation on `C(x)`. Then the image
of the residue field of the sheet extension in the residue field of an extension `v` of `w_{0,1}`
over it is contained in `k(x̄)`. -/
theorem residue_mem_adjoin_of {E : Type*} [Field E] [Algebra (RatFunc C) E] [Algebra C E]
    [IsScalarTower C (RatFunc C) E] [FiniteDimensional (RatFunc C) E] [Algebra L E]
    {l' : C} (hl0' : l' ≠ 0) (hl1' : ‖l'‖ < 1) (τ : RatFunc C → RatFunc C)
    (hτ : ∀ φ, GaussFibre.gauss1 C (τ φ) =
      (sheetExt hc ν₀ P' h1 hl0' hl1').1 (algebraMap (RatFunc C) L φ))
    (hτ' : ∀ φ, algebraMap L E (algebraMap (RatFunc C) L φ) = algebraMap (RatFunc C) E (τ φ))
    (v : Ext C E) (hvS : v.1.comap (algebraMap L E) = (sheetExt hc ν₀ P' h1 hl0' hl1').1)
    [(sheetExt hc ν₀ P' h1 hl0' hl1').1.HasExtension v.1]
    (z : ResidueField (sheetExt hc ν₀ P' h1 hl0' hl1').1.valuationSubring) :
    algebraMap _ (ResidueField v.1.valuationSubring) z ∈ 𝓀⟮red C (xF C E) v⟯ := by
  obtain ⟨y, rfl⟩ := residue_surjective z
  obtain ⟨φ, hφ⟩ := exists_ratFunc_approx hc ν₀ P' h1 hl0' hl1' (y : L) one_pos
  replace hφ : (sheetExt hc ν₀ P' h1 hl0' hl1').1 ((y : L) - algebraMap (RatFunc C) L φ) < 1 := by
    exact_mod_cast hφ
  have hSφ : (sheetExt hc ν₀ P' h1 hl0' hl1').1 (algebraMap (RatFunc C) L φ) ≤ 1 := by
    have := Valuation.map_add (sheetExt hc ν₀ P' h1 hl0' hl1').1
      (algebraMap (RatFunc C) L φ - (y : L)) (y : L)
    rw [sub_add_cancel, Valuation.map_sub_swap] at this
    exact this.trans (max_le hφ.le y.2)
  have hσ : GaussFibre.gauss1 C (τ φ) ≤ 1 := by rw [hτ]; exact hSφ
  have key : v.1 (algebraMap (RatFunc C) E (τ φ) - algebraMap L E (y : L)) < 1 := by
    rw [← hτ', ← map_sub, ← Valuation.comap_apply, hvS, Valuation.map_sub_swap]
    exact hφ
  rw [mem_adjoin_red_x_iff]
  refine ⟨residue _ ⟨τ φ, hσ⟩, ?_⟩
  rw [Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap,
    Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap, ← sub_eq_zero, ← map_sub,
    residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
  exact key

/-- **Residues of the sheet lie in `k(x̄)`**: the image of the residue field of the sheet
extension in the residue field of an outer vertex over it is contained in `k(x̄)`. -/
theorem residue_sheet_mem_adjoin (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (hvS : v.1.comap (algebraMap L (Aff a (l * c) (mul_ne_zero hl0 hc) F')) =
      (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    [(sheetExt hc ν₀ P' h1 hl0 hl1).1.HasExtension v.1]
    (z : ResidueField (sheetExt hc ν₀ P' h1 hl0 hl1).1.valuationSubring) :
    algebraMap _ (ResidueField v.1.valuationSubring) z ∈
      𝓀⟮red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v⟯ := by
  refine residue_mem_adjoin_of hc ν₀ P' h1 hl0 hl1 (aff a (l * c) (mul_ne_zero hl0 hc)).symm
    (fun φ ↦ ?_) (fun φ ↦ ?_) v hvS z
  · rw [gauss1_aff_symm, ← sheet_algebraMap hc ν₀ P' h1 hl0 hl1]
  · rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply, algebraMap_aff_L,
      ← IsScalarTower.algebraMap_apply]

omit [FiniteDimensional (RatFunc C) F'] in
/-- **The residue field at a vertex over a sheet is purely inseparable of exponent one over
`k(x̄)`** (purely inseparable case, general form). -/
theorem pow_mem_adjoin_of [Fact p.Prime] {E : Type*} [Field E] [Algebra (RatFunc C) E]
    [Algebra C E] [IsScalarTower C (RatFunc C) E] [FiniteDimensional (RatFunc C) E] [Algebra L E]
    [FiniteDimensional L E] {l' : C} (hl0' : l' ≠ 0) (hl1' : ‖l'‖ < 1)
    (τ : RatFunc C → RatFunc C)
    (hτ : ∀ φ, GaussFibre.gauss1 C (τ φ) =
      (sheetExt hc ν₀ P' h1 hl0' hl1').1 (algebraMap (RatFunc C) L φ))
    (hτ' : ∀ φ, algebraMap L E (algebraMap (RatFunc C) L φ) = algebraMap (RatFunc C) E (τ φ))
    (hp1 : ‖(p : C)‖ < 1) (hγ : γ ^ (p - 1) = -(p : C)) {θE : E}
    (hθ : θE ^ p = algebraMap L E f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θE ^ (i : ℕ)) = ⊤)
    (D : InsepData hc ν₀ P' h1 hl0' hl1' p γ f) (v : Ext C E)
    (hvS : v.1.comap (algebraMap L E) = (sheetExt hc ν₀ P' h1 hl0' hl1').1)
    (z : ResidueField v.1.valuationSubring) : z ^ p ∈ 𝓀⟮red C (xF C E) v⟯ := by
  haveI := DenseCompletion.hasExtension_of_comap_eq hvS
  obtain ⟨y, hy⟩ := insep_residue_pow_mem hc ν₀ P' h1 hl0' hl1' p hp1 hγ hvS hθ hspan D.hh'
    D.hγl D.hl1' D.hGle D.hGm D.hpm D.hf z
  rw [← hy]
  exact residue_mem_adjoin_of hc ν₀ P' h1 hl0' hl1' τ hτ hτ' v hvS y

omit [FiniteDimensional (RatFunc C) F'] in
/-- **A unique branch at a vertex over a sheet** (purely inseparable case, general form): the
residue field `κ(v)` is purely inseparable of exponent one over `k(x̄)`, so `x̄` has at most one
zero. -/
theorem zero_unique_of [Fact p.Prime] {E : Type*} [Field E] [Algebra (RatFunc C) E]
    [Algebra C E] [IsScalarTower C (RatFunc C) E] [FiniteDimensional (RatFunc C) E] [Algebra L E]
    [FiniteDimensional L E] {l' : C} (hl0' : l' ≠ 0) (hl1' : ‖l'‖ < 1)
    (τ : RatFunc C → RatFunc C)
    (hτ : ∀ φ, GaussFibre.gauss1 C (τ φ) =
      (sheetExt hc ν₀ P' h1 hl0' hl1').1 (algebraMap (RatFunc C) L φ))
    (hτ' : ∀ φ, algebraMap L E (algebraMap (RatFunc C) L φ) = algebraMap (RatFunc C) E (τ φ))
    (hp1 : ‖(p : C)‖ < 1) (hγ : γ ^ (p - 1) = -(p : C)) {θE : E}
    (hθ : θE ^ p = algebraMap L E f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θE ^ (i : ℕ)) = ⊤)
    (D : InsepData hc ν₀ P' h1 hl0' hl1' p γ f) (v : Ext C E)
    (hvS : v.1.comap (algebraMap L E) = (sheetExt hc ν₀ P' h1 hl0' hl1').1)
    {Q₁ Q₂ : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (h₁ : Q₁ ∈ zeros 𝓀 (red C (xF C E) v)) (h₂ : Q₂ ∈ zeros 𝓀 (red C (xF C E) v)) :
    Q₁ = Q₂ := by
  have hx0 : red C (xF C E) v ≠ 0 := fun h0 ↦ transcendental_red_x v (by
    rw [h0]; exact isAlgebraic_zero)
  exact eq_of_mem_zeros (k := 𝓀) (κ := ResidueField v.1.valuationSubring)
    (Fact.out : p.Prime).ne_zero hx0
    (pow_mem_adjoin_of hc ν₀ P' h1 p γ f hl0' hl1' τ hτ hτ' hp1 hγ hθ hspan D v hvS) h₁ h₂

/-- **The outer residue field is purely inseparable of exponent one over `k(x̄)`**. -/
theorem outer_pow_mem_adjoin [Fact p.Prime] [FiniteDimensional L F'] (hp1 : ‖(p : C)‖ < 1)
    (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f)
    (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (hvS : v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    (z : ResidueField v.1.valuationSubring) :
    z ^ p ∈ 𝓀⟮red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v⟯ := by
  set F₁ := Aff a (l * c) (mul_ne_zero hl0 hc) F'
  letI : FiniteDimensional L F₁ := inferInstanceAs (FiniteDimensional L F')
  have hθ₁ : toAff (mul_ne_zero hl0 hc) θ ^ p = algebraMap L F₁ f := by
    rw [← map_pow, hθ]; rfl
  refine pow_mem_adjoin_of hc ν₀ P' h1 p γ f hl0 hl1 (aff a (l * c) (mul_ne_zero hl0 hc)).symm
    (fun φ ↦ ?_) (fun φ ↦ ?_) hp1 hγ hθ₁ hspan D v hvS z
  · rw [gauss1_aff_symm, ← sheet_algebraMap hc ν₀ P' h1 hl0 hl1]
  · rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply, algebraMap_aff_L,
      ← IsScalarTower.algebraMap_apply]

/-- **A unique outer branch at an outer vertex over the sheet** (purely inseparable case). -/
theorem outer_zero_unique [Fact p.Prime] [FiniteDimensional L F'] (hp1 : ‖(p : C)‖ < 1)
    (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f)
    (v : Ext C (Aff a (l * c) (mul_ne_zero hl0 hc) F'))
    (hvS : v.1.comap ((toAff (a := a) (mul_ne_zero hl0 hc) (F' := F')).toRingHom.comp
      (algebraMap L F')) = (sheetExt hc ν₀ P' h1 hl0 hl1).1)
    {Q₁ Q₂ : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (h₁ : Q₁ ∈ zeros 𝓀 (red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v))
    (h₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Aff a (l * c) (mul_ne_zero hl0 hc) F')) v)) :
    Q₁ = Q₂ := by
  set F₁ := Aff a (l * c) (mul_ne_zero hl0 hc) F'
  letI : FiniteDimensional L F₁ := inferInstanceAs (FiniteDimensional L F')
  have hθ₁ : toAff (mul_ne_zero hl0 hc) θ ^ p = algebraMap L F₁ f := by
    rw [← map_pow, hθ]; rfl
  refine zero_unique_of hc ν₀ P' h1 p γ f hl0 hl1 (aff a (l * c) (mul_ne_zero hl0 hc)).symm
    (fun φ ↦ ?_) (fun φ ↦ ?_) hp1 hγ hθ₁ hspan D v hvS h₁ h₂
  · rw [gauss1_aff_symm, ← sheet_algebraMap hc ν₀ P' h1 hl0 hl1]
  · rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply, algebraMap_aff_L,
      ← IsScalarTower.algebraMap_apply]

/-- **A unique inner branch at an inner vertex over the inner sheet** (purely inseparable case,
with Kummer data at the radius `|l l₀|`). -/
theorem inner_zero_unique [Fact p.Prime] [FiniteDimensional L F'] (hp1 : ‖(p : C)‖ < 1)
    (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    {l₀ : C} (hl₀0 : l₀ ≠ 0) (hll1 : ‖l * l₀‖ < 1)
    (D : InsepData hc ν₀ P' h1 (mul_ne_zero hl0 hl₀0) hll1 p γ f)
    (v : Ext C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F')))
    (hvS : v.1.comap ((toInner (a := a) (F' := F') hc hl0 hl₀0).comp (algebraMap L F')) =
      (sheetExt hc ν₀ P' h1 (mul_ne_zero hl0 hl₀0) hll1).1)
    {Q₁ Q₂ : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (h₁ : Q₁ ∈ zeros 𝓀 (red C (xF C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) v))
    (h₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) v)) :
    Q₁ = Q₂ := by
  letI : Algebra L (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F')) :=
    inferInstanceAs (Algebra L F')
  letI : FiniteDimensional L (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F')) :=
    inferInstanceAs (FiniteDimensional L F')
  have hθE : toInner (a := a) (F' := F') hc hl0 hl₀0 θ ^ p =
      algebraMap L (Inv l₀ hl₀0 (Aff a (l * c) (mul_ne_zero hl0 hc) F')) f := by
    rw [← map_pow, hθ]; rfl
  refine zero_unique_of hc ν₀ P' h1 p γ f (mul_ne_zero hl0 hl₀0) hll1
    (fun φ ↦ inv hl₀0 ((aff a (l * c) (mul_ne_zero hl0 hc)).symm φ)) (fun φ ↦ ?_) (fun φ ↦ ?_)
    hp1 hγ hθE hspan D v hvS h₁ h₂
  · rw [sheet_algebraMap, ← inner_comap hc hl0 hl₀0 v φ, toInner_algebraMap,
      ← Valuation.comap_apply, v.2]
  · rw [← toInner_algebraMap hc hl0 hl₀0, IsScalarTower.algebraMap_apply (RatFunc C) L F']
    rfl

/-- **Exactly one outer branch** through a node point over `P'` (purely inseparable case). -/
theorem outerBranches_eq_singleton [CharZero C] [Fact p.Prime] [FiniteDimensional L F']
    (hp1 : ‖(p : C)‖ < 1) (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    (D : InsepData hc ν₀ P' h1 hl0 hl1 p γ f) {l₀ : C} (hl₀1 : ‖l₀‖ < 1) (hl₀0 : l₀ ≠ 0)
    (P'' : Ideal (Rint l₀ (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) [P''.IsMaximal]
    (hnode : P''.comap (algebraMap (nodeRing l₀) _) = tubeIdeal l₀)
    (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 l₀) = P') :
    ∃ b, outerBranches hl₀1 P'' = {b} := by
  obtain ⟨b, hb⟩ := exists_outerBranch (Fact.out : p.Prime) hp1 hl₀1 hl₀0 P'' hnode
  refine ⟨b, Set.eq_singleton_iff_unique_mem.2 ⟨hb, fun b' hb' ↦ ?_⟩⟩
  obtain ⟨v, Q, hQ⟩ := b
  obtain ⟨v', Q', hQ'⟩ := b'
  have hvv : v' = v := outer_ext_eq hc ν₀ P' h1 hl0 hl1 p γ θ f hp1 hγ hθ hspan D hl₀1 hQ' hQ hb'
    hb hP'' hP''
  subst hvv
  have hr := outer_restrict hc ν₀ P' h1 hl0 hl1 hl₀1 v' hQ hb hP''
  have hQQ : Q' = Q := outer_zero_unique hc ν₀ P' h1 hl0 hl1 p γ θ f hp1 hγ hθ hspan D v' hr hQ' hQ
  subst hQQ
  rfl

/-- **Exactly one inner branch** through a node point over `P'` (purely inseparable case at the
radius `|l l₀|`). -/
theorem innerBranches_eq_singleton [CharZero C] [Fact p.Prime] [FiniteDimensional L F']
    (hp1 : ‖(p : C)‖ < 1) (hγ : γ ^ (p - 1) = -(p : C)) (hθ : θ ^ p = algebraMap L F' f)
    (hspan : Submodule.span L (Set.range fun i : Fin p ↦ θ ^ (i : ℕ)) = ⊤)
    {l₀ : C} (hl₀1 : ‖l₀‖ < 1) (hl₀0 : l₀ ≠ 0) (hll1 : ‖l * l₀‖ < 1)
    (D : InsepData hc ν₀ P' h1 (mul_ne_zero hl0 hl₀0) hll1 p γ f)
    (P'' : Ideal (Rint l₀ (Aff a (l * c) (mul_ne_zero hl0 hc) F'))) [P''.IsMaximal]
    (hnode : P''.comap (algebraMap (nodeRing l₀) _) = tubeIdeal l₀)
    (hP'' : P''.comap (nodeMap (F' := F') hc hl0 hl1 l₀) = P') :
    ∃ b, innerBranches hl₀1 hl₀0 P'' = {b} := by
  obtain ⟨b, hb⟩ := exists_innerBranch (Fact.out : p.Prime) hp1 hl₀1 hl₀0 P'' hnode
  refine ⟨b, Set.eq_singleton_iff_unique_mem.2 ⟨hb, fun b' hb' ↦ ?_⟩⟩
  obtain ⟨v, Q, hQ⟩ := b
  obtain ⟨v', Q', hQ'⟩ := b'
  have hvv : v' = v := inner_ext_eq hc ν₀ P' h1 hl0 hl1 p γ θ f hp1 hγ hθ hspan hl₀1 hl₀0 hll1 D
    hQ' hQ hb' hb hP''
  subst hvv
  have hr := inner_restrict hc ν₀ P' h1 hl0 hl1 hl₀1 hl₀0 hll1 v' hQ hb hP''
  have hQQ : Q' = Q := inner_zero_unique hc ν₀ P' h1 hl0 p γ θ f hp1 hγ hθ hspan hl₀0 hll1 D v'
    hr hQ' hQ
  subst hQQ
  rfl

end OuterResidue

end KummerAnnulus

end SemistableReduction
