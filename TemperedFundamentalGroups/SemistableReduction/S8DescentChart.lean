/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8DescentPlace

/-!
# Descent (A6), part 3: the vertex charts of a Galois tower

Blueprint §9.10 A6. Let `C(x) ⊆ E ⊆ L` be finite with `L / E` Galois, group `H`, and
`R_E = DRint 0 1 E ⊆ R_L = DRint 0 1 L` the normalized vertex charts.

* `drintIncl`: the inclusion `R_E → R_L`; `H` acts on `R_L` with invariants `R_E`
  (`isInvariant`), so `H` permutes the points of `R_L` over a point of `R_E` transitively;
* `resBr`: restriction of branches (extension of `w_{0,1}`, place over a zero of `x̄`), compatible
  with points (`comap_placeIdealD`);
* `brVal b f`: the valuation of the reduction of `f` at the branch `b`; transported by `H`.
-/

open IsLocalRing Valuation WithZero
open scoped NNReal Pointwise

namespace SemistableReduction

namespace S8A

namespace Descent

open GaussFibre GaussTube DiscCount SmoothVertex FundamentalInequality PlaceNorm DenseCompletion

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {E L : Type*} [Field E] [Field L] [Algebra (RatFunc C) E] [Algebra (RatFunc C) L]
  [Algebra E L] [IsScalarTower (RatFunc C) E L] [Algebra C E] [Algebra C L]
  [IsScalarTower C (RatFunc C) E] [IsScalarTower C (RatFunc C) L]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-! ### The inclusion of charts and the Galois action -/

section Charts

variable (E L) in
/-- The inclusion `R_E → R_L` of normalized vertex charts. -/
noncomputable def drintIncl : DRint (0 : C) 1 E →+* DRint (0 : C) 1 L where
  toFun y := ⟨algebraMap E L y, IsIntegral.map_of_comp_eq (RingHom.id (discRing (0 : C) 1))
    (algebraMap E L) (RingHom.ext fun φ ↦ IsScalarTower.algebraMap_apply (RatFunc C) E L
      (φ : RatFunc C)) y.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

omit [IsAlgClosed C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] in
lemma coe_drintIncl (y : DRint (0 : C) 1 E) : (drintIncl E L y : L) = algebraMap E L y := rfl

omit [IsAlgClosed C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] in
lemma drintIncl_injective : Function.Injective (drintIncl (C := C) E L) := fun _ _ h ↦
  Subtype.ext ((algebraMap E L).injective (congrArg Subtype.val h))

omit [IsAlgClosed C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] in
lemma drintIncl_algebraMap (φ : discRing (0 : C) 1) :
    drintIncl E L (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 E) φ) =
      algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 L) φ :=
  Subtype.ext (IsScalarTower.algebraMap_apply (RatFunc C) E L (φ : RatFunc C)).symm

/-- `R_L` as an `R_E`-algebra. -/
noncomputable instance algebraDrint : Algebra (DRint (0 : C) 1 E) (DRint (0 : C) 1 L) :=
  (drintIncl E L).toAlgebra

omit [IsAlgClosed C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] in
lemma isIntegral_galois (σ : L ≃ₐ[E] L) {y : L} (hy : IsIntegral (discRing (0 : C) 1) y) :
    IsIntegral (discRing (0 : C) 1) (σ y) :=
  IsIntegral.map_of_comp_eq (RingHom.id (discRing (0 : C) 1)) σ.toRingEquiv.toRingHom
    (RingHom.ext fun φ ↦ by
      change algebraMap (RatFunc C) L φ = σ (algebraMap (RatFunc C) L φ)
      rw [IsScalarTower.algebraMap_apply (RatFunc C) E L, AlgEquiv.commutes]) hy

/-- The Galois group acts on `R_L`. -/
noncomputable instance mulSemiringActionDrint :
    MulSemiringAction (L ≃ₐ[E] L) (DRint (0 : C) 1 L) where
  smul σ y := ⟨σ y, isIntegral_galois σ y.2⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := Subtype.ext (map_zero _)
  smul_add _ _ _ := Subtype.ext (map_add _ _ _)
  smul_one _ := Subtype.ext (map_one _)
  smul_mul _ _ _ := Subtype.ext (map_mul _ _ _)

omit [IsAlgClosed C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] in
lemma coe_smul_drint (σ : L ≃ₐ[E] L) (y : DRint (0 : C) 1 L) : ((σ • y : DRint (0 : C) 1 L) : L) =
    σ y := rfl

instance : SMulCommClass (L ≃ₐ[E] L) (DRint (0 : C) 1 E) (DRint (0 : C) 1 L) where
  smul_comm σ a y := Subtype.ext (by
    change σ (algebraMap E L a * y) = algebraMap E L a * σ y
    rw [map_mul, AlgEquiv.commutes])

variable [FiniteDimensional (RatFunc C) L] [IsGalois E L]

/-- **The invariants of `R_L` are `R_E`.** -/
instance isInvariant :
    Algebra.IsInvariant (DRint (0 : C) 1 E) (DRint (0 : C) 1 L) (L ≃ₐ[E] L) := by
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  refine ⟨fun y hy ↦ ?_⟩
  have hfix : ∀ σ : L ≃ₐ[E] L, σ y = y := fun σ ↦ congrArg Subtype.val (hy σ)
  obtain ⟨e, he⟩ := (IsGalois.mem_bot_iff_fixed (F := E) (y : L)).2 hfix
  have hint : IsIntegral (discRing (0 : C) 1) e := by
    have h := y.2
    rw [← he] at h
    exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (discRing (0 : C) 1) E L)
      (algebraMap E L).injective).1 h
  exact ⟨⟨e, hint⟩, Subtype.ext he⟩

end Charts

/-! ### Normalized discrete valuations -/

section Normalized

omit [IsUltrametricDist C] [IsAlgClosed C]

/-- Two `ℤᵐ⁰`-valued valuations with the same valuation ring, both taking the value `exp (-1)`,
are equal. -/
theorem valuation_eq_of_le_one_iff {K : Type*} [Field K] {v₁ v₂ : Valuation K ℤᵐ⁰}
    (h : ∀ z, v₁ z ≤ 1 ↔ v₂ z ≤ 1) {π₁ π₂ : K} (h₁ : v₁ π₁ = exp (-1)) (h₂ : v₂ π₂ = exp (-1)) :
    v₁ = v₂ := by
  have hunit : ∀ u : K, v₁ u = 1 → v₂ u = 1 := fun u hu ↦ by
    have hu0 : u ≠ 0 := by rintro rfl; simp at hu
    have a1 := (h u).1 hu.le
    have a2 := (h u⁻¹).1 (by rw [map_inv₀, hu, inv_one])
    rw [map_inv₀] at a2
    have hne : v₂ u ≠ 0 := (Valuation.ne_zero_iff _).2 hu0
    exact le_antisymm a1 ((inv_le_one₀ (zero_lt_iff.2 hne)).1 a2)
  have hπ0 : π₁ ≠ 0 := by rintro rfl; rw [map_zero] at h₁; exact exp_ne_zero h₁.symm
  -- `v₂ z = v₂ (π₁) ^ (-log v₁ z)`
  have key : ∀ z : K, z ≠ 0 → v₂ z = v₂ π₁ ^ (-log (v₁ z)) := fun z hz ↦ by
    have hz0 : v₁ z ≠ 0 := (Valuation.ne_zero_iff _).2 hz
    set n := log (v₁ z)
    have hu : v₁ (z * π₁ ^ n) = 1 := by
      rw [map_mul, map_zpow₀, h₁, ← exp_log hz0, ← exp_zsmul, ← exp_add, exp_eq_one]
      simp [n]
    have hz' : z = (z * π₁ ^ n) * π₁ ^ (-n) := by
      rw [mul_assoc, ← zpow_add₀ hπ0, add_neg_cancel, zpow_zero, mul_one]
    rw [hz', map_mul, hunit _ hu, one_mul, map_zpow₀]
  have hlt : v₂ π₁ < 1 := by
    have hn : ¬ v₁ π₁⁻¹ ≤ 1 := by
      rw [map_inv₀, h₁, ← exp_neg, neg_neg, ← exp_zero, exp_le_exp]; omega
    rw [h] at hn
    rw [map_inv₀] at hn
    push Not at hn
    exact (one_lt_inv_iff₀.1 hn).2
  have hne : v₂ π₁ ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
  have hπ20 : π₂ ≠ 0 := by rintro rfl; rw [map_zero] at h₂; exact exp_ne_zero h₂.symm
  have k2 := key π₂ hπ20
  rw [h₂] at k2
  set a := log (v₂ π₁)
  have ha : v₂ π₁ = exp a := (exp_log hne).symm
  have ha0 : a < 0 := by rw [← exp_lt_exp, ← ha, exp_zero]; exact hlt
  rw [ha, ← exp_zsmul] at k2
  have k3 : (-1 : ℤ) = -log (v₁ π₂) • a := exp_injective k2
  have hab : a * (-log (v₁ π₂)) = -1 := by rw [smul_eq_mul] at k3; linarith
  have ha1 : a = -1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_neg_one hab with h | h <;> omega
  ext z
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [key z hz, ha, ha1, ← exp_zsmul, smul_eq_mul, mul_neg_one, neg_neg,
    exp_log ((Valuation.ne_zero_iff _).2 hz)]

/-- **Valuations of transported places**: a ring isomorphism of function fields matching the
valuation rings of two places matches their normalized valuations. -/
theorem valuation_map_of_iso {k κ₁ κ₂ : Type*} [Field k] [Field κ₁] [Field κ₂] [Algebra k κ₁]
    [Algebra k κ₂] [IsAlgClosed k] [IsCurveFunctionField k κ₁] [IsCurveFunctionField k κ₂]
    (φ : κ₁ ≃+* κ₂) {Q₁ : CurvePlace k κ₁} {Q₂ : CurvePlace k κ₂}
    (h : ∀ z, φ z ∈ Q₂.V ↔ z ∈ Q₁.V) (z : κ₁) : Q₂.valuation (φ z) = Q₁.valuation z := by
  obtain ⟨π₁, hπ₁⟩ := Q₁.exists_valuation_eq_exp_neg_one
  obtain ⟨π₂, hπ₂⟩ := Q₂.exists_valuation_eq_exp_neg_one
  have := valuation_eq_of_le_one_iff (v₁ := Q₁.valuation) (v₂ := Q₂.valuation.comap φ.toRingHom)
    (fun z ↦ by
      rw [Valuation.comap_apply, CurvePlace.valuation_le_one_iff, CurvePlace.valuation_le_one_iff]
      exact (h z).symm) hπ₁ (π₂ := φ.symm π₂) (by
      rw [Valuation.comap_apply]
      change Q₂.valuation (φ (φ.symm π₂)) = _
      rw [RingEquiv.apply_symm_apply, hπ₂])
  exact (congrArg (fun v : Valuation κ₁ ℤᵐ⁰ ↦ v z) this).symm

end Normalized

/-! ### Residue fields and branches -/

section Branches

instance hasExtensionResExt (w : Ext C L) : (resExt (E := E) w).1.HasExtension w.1 :=
  hasExtension_of_comap_eq rfl

omit [IsAlgClosed C] in
omit [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E] [IsScalarTower C (RatFunc C) L] in
/-- Reductions are compatible with the inclusion. -/
lemma red_algebraMap (w : Ext C L) (y : E) :
    red C (algebraMap E L y) w =
      algebraMap (ResidueField (resExt (E := E) w).1.valuationSubring)
        (ResidueField w.1.valuationSubring) (red C y (resExt w)) := by
  by_cases h : (resExt (E := E) w).1 y ≤ 1
  · have h' : w.1 (algebraMap E L y) ≤ 1 := h
    rw [red_of_le h, red_of_le h', Valuation.HasExtension.algebraMap_residue_eq_residue_algebraMap]
    rfl
  · have h' : ¬ w.1 (algebraMap E L y) ≤ 1 := h
    unfold red
    rw [dif_neg h, dif_neg h', map_zero]

omit [IsAlgClosed C] in
instance isScalarTower_residue (w : Ext C L) :
    IsScalarTower 𝓀 (ResidueField (resExt (E := E) w).1.valuationSubring)
      (ResidueField w.1.valuationSubring) := by
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  obtain ⟨o, rfl⟩ := residue_surjective r
  have ho : ‖(o : C)‖₊ ≤ 1 := by exact_mod_cast HenselComplete.norm_le_one o
  rw [← red_algebraMap_C (w := resExt (E := E) w) _ ho,
    ← red_algebraMap_C (w := w) _ ho, ← red_algebraMap,
    IsScalarTower.algebraMap_apply C (RatFunc C) L, IsScalarTower.algebraMap_apply (RatFunc C) E L,
    ← IsScalarTower.algebraMap_apply C (RatFunc C) E]

variable [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]

instance finiteDimensional_residue (w : Ext C L) :
    FiniteDimensional (ResidueField (resExt (E := E) w).1.valuationSubring)
      (ResidueField w.1.valuationSubring) := by
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  exact finite_residueField

instance isAlgebraic_residue (w : Ext C L) :
    Algebra.IsAlgebraic (ResidueField (resExt (E := E) w).1.valuationSubring)
      (ResidueField w.1.valuationSubring) :=
  Algebra.IsAlgebraic.of_finite _ _

omit [IsAlgClosed C] in
omit [IsUltrametricDist C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) E]
  [FiniteDimensional (RatFunc C) L] in
lemma xF_eq : xF C L = algebraMap E L (xF C E) :=
  IsScalarTower.algebraMap_apply (RatFunc C) E L RatFunc.X

/-- The restriction of a zero of `x̄` is a zero of `x̄`. -/
lemma mem_zeros_resPlace {w : Ext C L} {Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)} :
    Q ∈ zeros 𝓀 (red C (xF C L) w) ↔
      resPlace (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring) Q ∈
        zeros 𝓀 (red C (xF C E) (resExt w)) := by
  rw [mem_zeros, mem_zeros, mem_resPlace, map_inv₀, ← red_algebraMap, ← xF_eq]

/-- **Restriction of branches.** -/
noncomputable def resBr (b : OuterBranch C L) : OuterBranch C E :=
  ⟨resExt b.1, resPlace b.2.1, mem_zeros_resPlace.1 b.2.2⟩

lemma res_resPlace_eq_zero_iff {w : Ext C L}
    {Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)}
    {z : ResidueField (resExt (E := E) w).1.valuationSubring}
    (hz : z ∈ (resPlace (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring) Q).V) :
    (resPlace (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring) Q).res z = 0 ↔
      Q.res (algebraMap _ (ResidueField w.1.valuationSubring) z) = 0 := by
  rw [CurvePlace.res_eq_zero_iff _ hz, CurvePlace.res_eq_zero_iff _ (mem_resPlace.1 hz),
    valuation_algebraMap]
  have he := one_le_ramIdx (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring) Q
  constructor
  · intro h
    exact pow_lt_one₀ zero_le h (by omega)
  · intro h
    by_contra h'
    push Not at h'
    exact absurd h (not_lt.2 (one_le_pow₀ h'))

set_option maxHeartbeats 2000000 in
-- unfolding the reductions at the restricted branch is slow
/-- **Restriction of branches is compatible with points.** -/
theorem comap_placeIdealD (b : OuterBranch C L) :
    (placeIdealD b.1 b.2.2).comap (drintIncl E L) =
      placeIdealD (resExt (E := E) b.1) (mem_zeros_resPlace.1 b.2.2) := by
  ext y
  rw [Ideal.mem_comap, mem_placeIdealD_iff, mem_placeIdealD_iff]
  have hred : red C (algebraMap E L (y : E)) b.1 =
      algebraMap _ (ResidueField b.1.1.valuationSubring) (red C (y : E) (resExt (E := E) b.1)) :=
    red_algebraMap b.1 (y : E)
  have h1 : (redD b.fst) ((drintIncl E L) y) = red C ((algebraMap E L) (y : E)) b.fst := rfl
  have h2 : (redD (resExt (E := E) b.fst)) y = red C (y : E) (resExt (E := E) b.fst) := rfl
  rw [h1, h2, hred]
  exact (res_resPlace_eq_zero_iff (w := b.1) (Q := b.2.1) (z := redD (resExt (E := E) b.1) y)
    (redD_mem_V _ y (xbar_mem_V _ (mem_zeros_resPlace.1 b.2.2)))).symm

lemma comap_placeIdealD' (b : OuterBranch C L) :
    (placeIdealD b.1 b.2.2).comap (drintIncl E L) = placeIdealD (resBr b).1 (resBr b).2.2 :=
  comap_placeIdealD b

end Branches

/-! ### The Galois action on branches -/

section Action

variable [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]
  [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E] [IsScalarTower C (RatFunc C) L] in
omit [IsUltrametricDist C] in
lemma galois_algebraMap (σ : L ≃ₐ[E] L) (φ : RatFunc C) :
    σ.toRingEquiv (algebraMap (RatFunc C) L φ) = algebraMap (RatFunc C) L φ := by
  change σ (algebraMap (RatFunc C) L φ) = _
  rw [IsScalarTower.algebraMap_apply (RatFunc C) E L, AlgEquiv.commutes]

/-- The transport data of `σ ∈ Gal(L / E)`. -/
noncomputable abbrev gData (σ : L ≃ₐ[E] L) : Transport.Data C L L :=
  Transport.idData σ.toRingEquiv (galois_algebraMap (C := C) σ)

/-- The valuation of the reduction of `f` at the branch `b`. -/
noncomputable def brVal (b : OuterBranch C L) (f : L) : ℤᵐ⁰ := b.2.1.valuation (red C f b.1)

lemma valuation_placeMap (d : Transport.Data C L L) (v : Ext C L)
    (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (z : ResidueField v.1.valuationSubring) :
    (d.placeMap v Q).valuation (d.κmap v z) = Q.valuation z :=
  valuation_map_of_iso (d.κmap v) (fun _ ↦ d.mem_placeMap) z

omit [Algebra C E] [IsScalarTower C (RatFunc C) E] [FiniteDimensional (RatFunc C) E] in
/-- **Branch valuations are transported.** -/
lemma brVal_brMap (σ : L ≃ₐ[E] L) (b : OuterBranch C L) (f : L) :
    brVal ((gData (C := C) σ).brMap b) (σ f) = brVal b f := by
  change (((gData (C := C) σ).placeMap b.1 b.2.1).valuation
    (red C ((gData (C := C) σ).e f) ((gData (C := C) σ).extMap b.1)))
    = _
  rw [Transport.Data.red_map, valuation_placeMap]
  rfl

omit [FiniteDimensional (RatFunc C) E] in
omit [Algebra C E] [IsScalarTower C (RatFunc C) E] in
/-- **Points of transported branches.** -/
lemma placeIdealD_brMap (σ : L ≃ₐ[E] L) (b : OuterBranch C L) :
    placeIdealD ((gData (C := C) σ).brMap b).1 ((gData (C := C) σ).brMap b).2.2 =
      σ • placeIdealD b.1 b.2.2 := by
  ext y
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  exact (gData (C := C) σ).mem_placeIdealD_map (fun _ ↦ Iff.rfl) b.2.2 y

omit [FiniteDimensional (RatFunc C) E] in
omit [IsAlgClosed C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L] in
lemma resExt_extMap (σ : L ≃ₐ[E] L) (w : Ext C L) :
    resExt (E := E) ((gData (C := C) σ).extMap w) = resExt w :=
  Subtype.ext (Valuation.ext fun y ↦ by
    change w.1 (σ.symm (algebraMap E L y)) = w.1 (algebraMap E L y)
    rw [AlgEquiv.commutes])

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) E] in
lemma mem_resPlace_placeMap (σ : L ≃ₐ[E] L) (w : Ext C L)
    (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)) (f : E) :
    red C f (resExt (E := E) ((gData (C := C) σ).extMap w)) ∈
        (resPlace
          (κ₁ := ResidueField (resExt (E := E) ((gData (C := C) σ).extMap w)).1.valuationSubring)
          ((gData (C := C) σ).placeMap w Q)).V ↔
      red C f (resExt (E := E) w) ∈
        (resPlace (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring) Q).V := by
  rw [mem_resPlace, mem_resPlace, ← red_algebraMap, ← red_algebraMap]
  have h : algebraMap E L f = (gData (C := C) σ).e (algebraMap E L f) :=
    (AlgEquiv.commutes σ f).symm
  conv_lhs => rw [h, Transport.Data.red_map]
  exact (gData (C := C) σ).mem_placeMap (v := w) (Q := Q)

/-- **Restriction is invariant under the Galois action.** -/
lemma resBr_brMap (σ : L ≃ₐ[E] L) (b : OuterBranch C L) :
    resBr (E := E) ((gData (C := C) σ).brMap b) = resBr b :=
  Transport.outerBranch_ext (resExt_extMap σ b.1) fun f _ ↦ mem_resPlace_placeMap σ b.1 b.2.1 f

/-- Branch valuations are transported by any transport data on `L`. -/
lemma brVal_dbrMap (d : Transport.Data C L L) (b : OuterBranch C L) (f : L) :
    brVal (d.brMap b) (d.e f) = brVal b f := by
  change (d.placeMap b.1 b.2.1).valuation (red C (d.e f) (d.extMap b.1)) = _
  rw [Transport.Data.red_map, valuation_placeMap]
  rfl

omit [FiniteDimensional (RatFunc C) E] in
/-- Elements outside the point of a branch are units at the branch. -/
lemma brVal_eq_one_of_notMem {b : OuterBranch C L} {y : DRint (0 : C) 1 L}
    (hy : y ∉ placeIdealD b.1 b.2.2) : brVal b (y : L) = 1 := by
  rw [mem_placeIdealD_iff] at hy
  have hV := redD_mem_V b.1 y (xbar_mem_V b.1 b.2.2)
  have h1 := b.2.1.valuation_le_one_iff.2 hV
  refine le_antisymm h1 (not_lt.1 fun hlt ↦ hy ?_)
  exact (CurvePlace.res_eq_zero_iff _ hV).2 hlt

omit [FiniteDimensional (RatFunc C) E] in
/-- Elements of the point of a branch vanish at the branch. -/
lemma brVal_le_of_mem {b : OuterBranch C L} {y : DRint (0 : C) 1 L}
    (hy : y ∈ placeIdealD b.1 b.2.2) : brVal b (y : L) ≤ exp (-1) := by
  rw [mem_placeIdealD_iff] at hy
  have hV := redD_mem_V b.1 y (xbar_mem_V b.1 b.2.2)
  have hlt := (CurvePlace.res_eq_zero_iff _ hV).1 hy
  exact WithZero.le_exp_of_lt_exp_add_one (n := -1) (by
    change b.2.1.valuation (redD b.1 y) < exp (-1 + 1)
    simpa using hlt)

/-- The valuation of the reduction of `g ∈ E` at a branch of `E`. -/
noncomputable def brValE (b' : OuterBranch C E) (g : E) : ℤᵐ⁰ := b'.2.1.valuation (red C g b'.1)

/-- **Branch values of elements of `E`**: `v_Q(f) = v_{Q ∩ κ}(f) ^ e`. -/
lemma brVal_algebraMap (B : OuterBranch C L) (g : E) :
    brVal B (algebraMap E L g) = brValE (resBr (E := E) B) g ^
        ramIdx (κ₁ := ResidueField (resExt (E := E) B.1).1.valuationSubring) B.2.1 := by
  change B.2.1.valuation (red C (algebraMap E L g) B.1) = _
  rw [red_algebraMap B.1 g, valuation_algebraMap]
  rfl

end Action

/-! ### Lifting branches and uniqueness at the point -/

section Lift

variable [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Every branch of `E` lifts to `L`.** -/
theorem exists_resBr_eq (b' : OuterBranch C E) : ∃ B : OuterBranch C L, resBr B = b' := by
  classical
  obtain ⟨v, Q', hQ'⟩ := b'
  haveI := finite_ext (F := L) hp hp1
  letI : Fintype (Ext C L) := Fintype.ofFinite _
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  have hsum := sum_fdeg_eq hp hp1 (L := L) v
  obtain ⟨w, -, hw⟩ : ∃ w ∈ Finset.univ, fdeg v w ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero h] at hsum
    exact Module.finrank_pos.ne' hsum.symm
  have hwv : resExt w = v := by
    by_contra h
    exact hw (fdeg_of_ne h)
  subst hwv
  obtain ⟨S, hS, hsumS⟩ :=
    sum_ramIdx_eq (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring)
      (κ₂ := ResidueField w.1.valuationSubring) Q'
  obtain ⟨Q, hQ⟩ : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hsumS
    exact Module.finrank_pos.ne' hsumS.symm
  have hQQ := (hS Q).1 hQ
  refine ⟨⟨w, Q, mem_zeros_resPlace.2 (by rw [hQQ]; exact hQ')⟩, ?_⟩
  simp only [resBr, hQQ]

omit [CharZero C] in
lemma placeIdealD_isMaximal' (b : OuterBranch C L) : (placeIdealD b.1 b.2.2).IsMaximal :=
  placeIdealD_isMaximal b.1 b.2.2

include hp hp1 in
/-- **Uniqueness of the branch through a point of `R_E`** whose points above are smooth. -/
theorem discBranches_eq_resBr [IsGalois E L] {P' : Ideal (DRint (0 : C) 1 E)}
    {P'' : Ideal (DRint (0 : C) 1 L)} [P''.IsMaximal] (hP'' : P''.comap (drintIncl E L) = P')
    {b'' : OuterBranch C L} (hb : discBranches P'' = {b''}) :
    discBranches P' = {resBr (E := E) b''} := by
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  have hb''P : placeIdealD b''.1 b''.2.2 = P'' := by
    have : b'' ∈ discBranches P'' := by rw [hb]; rfl
    exact this
  ext b'
  constructor
  · intro hb'
    change placeIdealD b'.1 b'.2.2 = P' at hb'
    obtain ⟨B, hB⟩ := exists_resBr_eq (L := L) hp hp1 b'
    haveI := placeIdealD_isMaximal' B
    have hPB : (placeIdealD B.1 B.2.2).comap (drintIncl E L) = P' := by
      rw [comap_placeIdealD', ← hb']
      exact congrArg (fun b : OuterBranch C E ↦ placeIdealD b.1 b.2.2) hB
    obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (DRint (0 : C) 1 E)
      (DRint (0 : C) 1 L) (L ≃ₐ[E] L) (placeIdealD B.1 B.2.2) P'' (hPB.trans hP''.symm)
    have hBσ : (gData (C := C) σ).brMap B ∈ discBranches P'' := by
      change placeIdealD _ _ = P''
      rw [placeIdealD_brMap, hσ]
    rw [hb, Set.mem_singleton_iff] at hBσ
    rw [Set.mem_singleton_iff, ← hB, ← resBr_brMap σ B, hBσ]
  · intro hb'
    rw [Set.mem_singleton_iff] at hb'
    subst hb'
    change placeIdealD _ _ = P'
    rw [← comap_placeIdealD', hb''P, hP'']

omit [FiniteDimensional (RatFunc C) E] [CharZero C] in
omit [IsAlgClosed C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L] in
lemma extMap_eq_smul (σ : L ≃ₐ[E] L) (w : Ext C L) : (gData (C := C) σ).extMap w = σ • w := rfl

omit [FiniteDimensional (RatFunc C) E] [CharZero C] in
omit [Algebra C E] [IsScalarTower C (RatFunc C) E] in
lemma smul_fst_of_brMap_eq {σ : L ≃ₐ[E] L} {B b : OuterBranch C L}
    (h : (gData (C := C) σ).brMap B = b) : σ • B.1 = b.1 := by
  rw [← extMap_eq_smul]
  exact congrArg Sigma.fst h

omit [CharZero C] in
/-- A uniformizer of the base place, as an element of `E`. -/
lemma exists_unif_E (b' : OuterBranch C E) :
    ∃ g : E, b'.2.1.valuation (red C g b'.1) = exp (-1) := by
  obtain ⟨π, hπ⟩ := b'.2.1.exists_valuation_eq_exp_neg_one
  obtain ⟨⟨g, hg⟩, hgπ⟩ := residue_surjective π
  exact ⟨g, by rw [red_of_le hg, hgπ, hπ]⟩

set_option maxHeartbeats 1600000 in
-- the branch data over twisted residue fields make unification slow
set_option synthInstance.maxHeartbeats 200000 in
include hp hp1 in
/-- **The ramification index at a point equals the order of its stabilizer** (all points above
being smooth). -/
theorem ramIdx_eq_card [IsGalois E L] {P' : Ideal (DRint (0 : C) 1 E)}
    {P'' : Ideal (DRint (0 : C) 1 L)} [P''.IsMaximal] (hP'' : P''.comap (drintIncl E L) = P')
    (hsm : ∀ Q : Ideal (DRint (0 : C) 1 L), Q.IsMaximal → Q.comap (drintIncl E L) = P' →
      IsDiscSmooth Q)
    {b'' : OuterBranch C L} (hb : discBranches P'' = {b''}) :
    ramIdx (κ₁ := ResidueField (resExt (E := E) b''.1).1.valuationSubring) b''.2.1 =
      Nat.card (MulAction.stabilizer (L ≃ₐ[E] L) P'') := by
  classical
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  have hP'b := discBranches_eq_resBr hp hp1 hP'' hb
  have hb''P : placeIdealD b''.1 b''.2.2 = P'' := by
    have : b'' ∈ discBranches P'' := by rw [hb]; rfl
    exact this
  -- branches over the branch `b' = resBr b''` lie over `P'`
  have hover : ∀ B : OuterBranch C L, resBr (E := E) B = resBr b'' →
      (placeIdealD B.1 B.2.2).comap (drintIncl E L) = P' := by
    intro B hB
    rw [comap_placeIdealD', congrArg (fun b : OuterBranch C E ↦ placeIdealD b.1 b.2.2) hB]
    have : resBr (E := E) b'' ∈ discBranches P' := by rw [hP'b]; rfl
    exact this
  -- and are carried to `b''` by the Galois group
  have htrans : ∀ B : OuterBranch C L, resBr (E := E) B = resBr b'' →
      ∃ σ : L ≃ₐ[E] L, P'' = σ • placeIdealD B.1 B.2.2 ∧ (gData (C := C) σ).brMap B = b'' := by
    intro B hB
    haveI := placeIdealD_isMaximal' B
    obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq (DRint (0 : C) 1 E)
      (DRint (0 : C) 1 L) (L ≃ₐ[E] L) (placeIdealD B.1 B.2.2) P'' ((hover B hB).trans hP''.symm)
    refine ⟨σ, hσ, ?_⟩
    have hBσ : (gData (C := C) σ).brMap B ∈ discBranches P'' := by
      change placeIdealD _ _ = P''
      rw [placeIdealD_brMap, hσ]
    rwa [hb, Set.mem_singleton_iff] at hBσ
  -- the ramification index is constant over `b'`
  obtain ⟨g, hg⟩ := exists_unif_E (resBr (E := E) b'')
  change brValE (resBr (E := E) b'') g = exp (-1) at hg
  have hval : ∀ B : OuterBranch C L, resBr (E := E) B = resBr b'' →
      brVal B (algebraMap E L g) =
        exp (-(ramIdx (κ₁ := ResidueField (resExt (E := E) B.1).1.valuationSubring) B.2.1 :
          ℤ)) := by
    intro B hB
    have h1 : brValE (resBr (E := E) B) g = exp (-1) :=
      (congrArg (fun b : OuterBranch C E ↦ brValE b g) hB).trans hg
    rw [brVal_algebraMap B g, h1, ← exp_nsmul]
    simp
  have hconst : ∀ B : OuterBranch C L, resBr (E := E) B = resBr b'' →
      ramIdx (κ₁ := ResidueField (resExt (E := E) B.1).1.valuationSubring) B.2.1 =
        ramIdx (κ₁ := ResidueField (resExt (E := E) b''.1).1.valuationSubring) b''.2.1 := by
    intro B hB
    obtain ⟨σ, -, hσ⟩ := htrans B hB
    have h1 := brVal_dbrMap (gData (C := C) σ) B (algebraMap E L g)
    rw [hσ, show (gData (C := C) σ).e (algebraMap E L g) = algebraMap E L g from
      AlgEquiv.commutes σ g, hval b'' rfl, hval B hB] at h1
    have h2 := exp_injective h1
    omega
  -- the places over the base place on the residue curve of `w`
  obtain ⟨w, Q, hQ⟩ := b''
  obtain ⟨S, hS, hsumS⟩ := sum_ramIdx_eq (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring)
    (κ₂ := ResidueField w.1.valuationSubring) (resPlace Q)
  have hzero : ∀ Q₂ ∈ S, Q₂ ∈ zeros 𝓀 (red C (xF C L) w) := fun Q₂ h ↦
    mem_zeros_resPlace.2 (by rw [(hS Q₂).1 h]; exact mem_zeros_resPlace.1 hQ)
  have hresS : ∀ Q₂ (h : Q₂ ∈ S), resBr (E := E) ⟨w, Q₂, hzero Q₂ h⟩ = resBr ⟨w, Q, hQ⟩ := by
    intro Q₂ h
    simp only [resBr, (hS Q₂).1 h]
  set e := ramIdx (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring) Q
  have hsum_e : ∑ Q₂ ∈ S, ramIdx (κ₁ := ResidueField (resExt (E := E) w).1.valuationSubring) Q₂ =
      S.card * e := by
    rw [Finset.sum_congr rfl fun Q₂ h ↦ hconst ⟨w, Q₂, hzero Q₂ h⟩ (hresS Q₂ h),
      Finset.sum_const, smul_eq_mul]
  -- `[κ(w) : κ(v)] = |H_w|`
  have hfd := fdeg_eq_card_stabilizer hp hp1 (E := E) w
  rw [fdeg_of_eq rfl] at hfd
  change Module.finrank _ _ = _ at hfd
  rw [← hsumS, hsum_e] at hfd
  -- the stabilizer of `w` acts on the points over `P'` carrying a branch of `w`
  set Hw := MulAction.stabilizer (L ≃ₐ[E] L) w
  have hstab_le : ∀ σ : L ≃ₐ[E] L, σ • P'' = P'' → σ ∈ Hw := by
    intro σ hσ
    have hB : (gData (C := C) σ).brMap ⟨w, Q, hQ⟩ ∈ discBranches P'' := by
      change placeIdealD _ _ = P''
      rw [placeIdealD_brMap, hb''P, hσ]
    rw [hb, Set.mem_singleton_iff] at hB
    exact smul_fst_of_brMap_eq hB
  -- the point map on `S`
  let f : CurvePlace 𝓀 (ResidueField w.1.valuationSubring) → Ideal (DRint (0 : C) 1 L) :=
    fun Q₂ ↦ if h : Q₂ ∈ zeros 𝓀 (red C (xF C L) w) then placeIdealD w h else ⊥
  have hf : ∀ Q₂ (h : Q₂ ∈ S), f Q₂ = placeIdealD w (hzero Q₂ h) := fun Q₂ h ↦ by
    simp only [f, dif_pos (hzero Q₂ h)]
  have hinj : Set.InjOn f S := by
    intro Q₂ h₂ Q₃ h₃ heq
    rw [Finset.mem_coe] at h₂ h₃
    rw [hf Q₂ h₂, hf Q₃ h₃] at heq
    set P₂ := placeIdealD w (hzero Q₂ h₂)
    haveI : P₂.IsMaximal := placeIdealD_isMaximal _ _
    obtain ⟨b₀, hb₀, -⟩ := hsm P₂ inferInstance (hover ⟨w, Q₂, hzero Q₂ h₂⟩ (hresS Q₂ h₂))
    have m₂ : (⟨w, Q₂, hzero Q₂ h₂⟩ : OuterBranch C L) ∈ discBranches P₂ := rfl
    have m₃ : (⟨w, Q₃, hzero Q₃ h₃⟩ : OuterBranch C L) ∈ discBranches P₂ := heq.symm
    rw [hb₀, Set.mem_singleton_iff] at m₂ m₃
    have := m₂.trans m₃.symm
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and, Subtype.mk.injEq] at this
    exact this
  have horb : MulAction.orbit Hw P'' = ↑(S.image f) := by
    ext P
    rw [Finset.coe_image, Set.mem_image]
    constructor
    · rintro ⟨⟨τ, hτ⟩, rfl⟩
      have hτw : τ • w = w := hτ
      set B := (gData (C := C) τ).brMap ⟨w, Q, hQ⟩ with hBdef
      have hBw : B.1 = w := smul_fst_of_brMap_eq rfl |>.trans hτw
      have hBP : placeIdealD B.1 B.2.2 = τ • P'' := by rw [placeIdealD_brMap, hb''P]
      have hBres : resBr (E := E) B = resBr ⟨w, Q, hQ⟩ := resBr_brMap τ _
      clear_value B
      obtain ⟨w₁, Q₁, h₁⟩ := B
      simp only at hBw
      subst hBw
      have hQ₁ : resPlace (κ₁ := ResidueField (resExt (E := E) w₁).1.valuationSubring) Q₁ =
          resPlace Q := by
        simp only [resBr, Sigma.mk.injEq, heq_eq_eq, true_and, Subtype.mk.injEq] at hBres
        exact hBres
      have hmem : Q₁ ∈ S := (hS Q₁).2 hQ₁
      refine ⟨Q₁, hmem, ?_⟩
      rw [hf Q₁ hmem]
      exact hBP
    · rintro ⟨Q₂, h₂, rfl⟩
      obtain ⟨σ, hσP, hσB⟩ := htrans ⟨w, Q₂, hzero Q₂ h₂⟩ (hresS Q₂ h₂)
      have hσw : σ ∈ Hw := smul_fst_of_brMap_eq hσB
      refine ⟨⟨σ⁻¹, Hw.inv_mem hσw⟩, ?_⟩
      change (σ⁻¹ : L ≃ₐ[E] L) • P'' = f Q₂
      rw [hf Q₂ h₂, hσP, inv_smul_smul]
  have hcard_orb : Nat.card (MulAction.orbit Hw P'') = S.card := by
    rw [Nat.card_coe_set_eq, horb, Set.ncard_coe_finset, Finset.card_image_of_injOn hinj]
  have hstab : Nat.card (MulAction.stabilizer Hw P'') =
      Nat.card (MulAction.stabilizer (L ≃ₐ[E] L) P'') := by
    refine Nat.card_congr
      { toFun := fun τ ↦ ⟨τ.1.1, τ.2⟩
        invFun := fun σ ↦ ⟨⟨σ.1, hstab_le σ.1 σ.2⟩, σ.2⟩
        left_inv := fun τ ↦ rfl
        right_inv := fun σ ↦ rfl }
  have hG : Nat.card (MulAction.orbit Hw P'') * Nat.card (MulAction.stabilizer Hw P'') =
      Nat.card Hw := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.index_mul_card]
  rw [hcard_orb, hstab, ← hfd] at hG
  have hpos : 0 < S.card := Finset.card_pos.2 ⟨Q, (hS Q).2 rfl⟩
  exact (Nat.eq_of_mul_eq_mul_left hpos hG).symm

omit [CharZero C] [FiniteDimensional (RatFunc C) E] in
omit [Algebra C E] [IsScalarTower C (RatFunc C) E] in
lemma brVal_galois (σ : L ≃ₐ[E] L) (b : OuterBranch C L) (y : L) :
    brVal b (σ y) = brVal ((gData (C := C) σ).symm.brMap b) y := by
  have h := brVal_dbrMap (gData (C := C) σ) ((gData (C := C) σ).symm.brMap b) y
  rw [Transport.Data.brMap_brMap_symm] at h
  exact h

omit [CharZero C] [FiniteDimensional (RatFunc C) E] in
omit [Algebra C E] [IsScalarTower C (RatFunc C) E] in
lemma placeIdealD_symm_brMap (σ : L ≃ₐ[E] L) (b : OuterBranch C L) :
    placeIdealD ((gData (C := C) σ).symm.brMap b).1 ((gData (C := C) σ).symm.brMap b).2.2 =
      σ⁻¹ • placeIdealD b.1 b.2.2 := by
  ext y
  rw [Ideal.mem_inv_pointwise_smul_iff]
  exact (gData (C := C) σ).symm.mem_placeIdealD_map (fun _ ↦ Iff.rfl) b.2.2 y

omit [CharZero C] [FiniteDimensional (RatFunc C) E] in
/-- Branch values are multiplicative on `R_L`. -/
lemma brVal_mul (b : OuterBranch C L) (y z : DRint (0 : C) 1 L) :
    brVal b ((y * z : DRint (0 : C) 1 L) : L) = brVal b (y : L) * brVal b (z : L) := by
  change b.2.1.valuation (redD b.1 (y * z)) = b.2.1.valuation (redD b.1 y) *
    b.2.1.valuation (redD b.1 z)
  rw [map_mul, map_mul]

omit [CharZero C] [FiniteDimensional (RatFunc C) E] in
lemma brVal_prod {ι : Type*} (s : Finset ι) (b : OuterBranch C L) (y : ι → DRint (0 : C) 1 L) :
    brVal b ((∏ i ∈ s, y i : DRint (0 : C) 1 L) : L) = ∏ i ∈ s, brVal b (y i : L) := by
  change b.2.1.valuation (redD b.1 (∏ i ∈ s, y i)) = ∏ i ∈ s, b.2.1.valuation (redD b.1 (y i))
  rw [map_prod, map_prod]

omit [CharZero C] [FiniteDimensional (RatFunc C) E] in
/-- Elements of `P''²` have value `≤ exp (-2)` at the branch through `P''`. -/
lemma brVal_le_of_mem_sq {b : OuterBranch C L} {d : DRint (0 : C) 1 L}
    (hd : d ∈ placeIdealD b.1 b.2.2 ^ 2) : brVal b (d : L) ≤ exp (-2) := by
  rw [pow_two] at hd
  refine Submodule.mul_induction_on hd (fun x hx y hy ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [brVal_mul]
    calc brVal b (x : L) * brVal b (y : L) ≤ exp (-1) * exp (-1) :=
          mul_le_mul' (brVal_le_of_mem hx) (brVal_le_of_mem hy)
      _ = exp (-2) := by rw [← exp_add]; norm_num
  · change b.2.1.valuation (redD b.1 (x + y)) ≤ _
    rw [map_add]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)

end Lift

/-! ### A6: smooth points descend -/

section A6

variable [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

set_option maxHeartbeats 1600000 in
-- unification through twisted residue fields
set_option synthInstance.maxHeartbeats 200000 in
include hp hp1 in
/-- **A6: smooth points descend along a Galois extension** `L / E`: if every point of `R_L` over a
point `P'` of `R_E` over the residue point is smooth, so is `P'`. -/
theorem isDiscSmooth_of_galois [IsGalois E L] {P' : Ideal (DRint (0 : C) 1 E)} [P'.IsMaximal]
    (hsm : ∀ Q : Ideal (DRint (0 : C) 1 L), Q.IsMaximal → Q.comap (drintIncl E L) = P' →
      IsDiscSmooth Q) : IsDiscSmooth P' := by
  classical
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  -- a point above
  haveI := Algebra.IsInvariant.isIntegral (DRint (0 : C) 1 E) (DRint (0 : C) 1 L) (L ≃ₐ[E] L)
  obtain ⟨P'', hP''max, hP''⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := DRint (0 : C) 1 L) P' (by
      intro y hy
      rw [RingHom.mem_ker] at hy
      change drintIncl E L y = 0 at hy
      have : y = 0 := drintIncl_injective (by rw [hy, map_zero])
      rw [this]
      exact P'.zero_mem)
  change P''.comap (drintIncl E L) = P' at hP''
  obtain ⟨b'', hb, hjet⟩ := hsm P'' hP''max hP''
  have hb''P : placeIdealD b''.1 b''.2.2 = P'' := by
    have : b'' ∈ discBranches P'' := by rw [hb]; rfl
    exact this
  have hP'b := discBranches_eq_resBr hp hp1 hP'' hb
  have he := ramIdx_eq_card hp hp1 hP'' hsm hb
  -- a uniformizer at `P''`
  obtain ⟨π, hπ⟩ := b''.2.1.exists_valuation_eq_exp_neg_one
  have hπV : π ∈ b''.2.1.V :=
    b''.2.1.valuation_le_one_iff.1 (by rw [hπ, ← exp_zero, exp_le_exp]; omega)
  obtain ⟨y, s, hs, hys⟩ := hjet π hπV
  rw [hb''P.symm] at hs
  have hy : brVal b'' (y : L) = exp (-1) := by
    change b''.2.1.valuation (redD b''.1 y) = _
    have h1 : b''.2.1.valuation (redD b''.1 s) = 1 := brVal_eq_one_of_notMem hs
    rw [hys, map_mul, hπ, h1, mul_one]
  -- the other points over `P'`
  set T : Finset (Ideal (DRint (0 : C) 1 L)) :=
    (Finset.univ.image fun σ : L ≃ₐ[E] L ↦ σ • P'').filter (· ≠ P'')
  have hTmax : ∀ J ∈ T, J.IsMaximal := by
    intro J hJ
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_filter.1 hJ).1
    exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv _ _ σ)
  -- the Chinese remainder theorem
  let I : Option T → Ideal (DRint (0 : C) 1 L) := fun o ↦ o.elim (P'' ^ 2) (fun J ↦ J.1)
  have hcop : Pairwise (Function.onFun IsCoprime I) := by
    rintro (_ | ⟨J, hJ⟩) (_ | ⟨J', hJ'⟩) hne
    · exact absurd rfl hne
    · haveI := hTmax J' hJ'
      change IsCoprime (P'' ^ 2) J'
      exact (Ideal.isCoprime_of_isMaximal (Finset.mem_filter.1 hJ').2.symm).pow_left
    · haveI := hTmax J hJ
      change IsCoprime J (P'' ^ 2)
      exact ((Ideal.isCoprime_of_isMaximal (Finset.mem_filter.1 hJ).2.symm).pow_left).symm
    · haveI := hTmax J hJ
      haveI := hTmax J' hJ'
      change IsCoprime J J'
      exact Ideal.isCoprime_of_isMaximal fun h ↦ hne (by subst h; rfl)
  obtain ⟨s₁, hs₁⟩ := Ideal.exists_forall_sub_mem_ideal hcop
    (fun o : Option T ↦ o.elim y fun _ ↦ 1)
  have hs₁P : s₁ - y ∈ P'' ^ 2 := hs₁ none
  have hs₁T : ∀ J ∈ T, s₁ ∉ J := fun J hJ hmem ↦ by
    have h1 : s₁ - 1 ∈ J := hs₁ (some ⟨J, hJ⟩)
    haveI := hTmax J hJ
    exact Ideal.IsMaximal.ne_top inferInstance (J.eq_top_of_isUnit_mem (by
      have : (1 : DRint (0 : C) 1 L) = s₁ - (s₁ - 1) := by ring
      rw [this]; exact J.sub_mem hmem h1) isUnit_one)
  have hs₁val : brVal b'' (s₁ : L) = exp (-1) := by
    have hd := brVal_le_of_mem_sq (b := b'') (hb''P ▸ hs₁P)
    have : s₁ = y + (s₁ - y) := by ring
    change b''.2.1.valuation (redD b''.1 s₁) = _
    rw [this, map_add, Valuation.map_add_eq_of_lt_left]
    · exact hy
    · change brVal b'' ((s₁ - y : DRint (0 : C) 1 L) : L) < brVal b'' (y : L)
      rw [hy]
      exact hd.trans_lt (by rw [exp_lt_exp]; omega)
  -- the norm
  set t' : DRint (0 : C) 1 L := ∏ σ : L ≃ₐ[E] L, σ • s₁
  have ht'fix : ∀ τ : L ≃ₐ[E] L, τ • t' = t' := fun τ ↦ by
    simp only [t', Finset.smul_prod']
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ ↦ (mul_smul τ σ s₁).symm
  obtain ⟨t₀, ht₀⟩ := Algebra.IsInvariant.isInvariant (A := DRint (0 : C) 1 E) t' ht'fix
  change drintIncl E L t₀ = t' at ht₀
  -- its value at `b''`
  have hfac : ∀ σ : L ≃ₐ[E] L, brVal b'' ((σ • s₁ : DRint (0 : C) 1 L) : L) =
      if σ • P'' = P'' then exp (-1) else 1 := by
    intro σ
    rw [coe_smul_drint, brVal_galois]
    split_ifs with hσ
    · have hB : (gData (C := C) σ).symm.brMap b'' ∈ discBranches P'' := by
        change placeIdealD _ _ = P''
        rw [placeIdealD_symm_brMap, hb''P, inv_smul_eq_iff, hσ]
      rw [hb, Set.mem_singleton_iff] at hB
      rw [hB, hs₁val]
    · refine brVal_eq_one_of_notMem ?_
      rw [placeIdealD_symm_brMap, hb''P]
      refine hs₁T _ (Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨σ⁻¹, Finset.mem_univ _, rfl⟩, ?_⟩)
      intro h
      exact hσ (inv_smul_eq_iff.1 h).symm
  have hval : brVal b'' (t' : L) =
      exp (-(Nat.card (MulAction.stabilizer (L ≃ₐ[E] L) P'') : ℤ)) := by
    rw [brVal_prod, Finset.prod_congr rfl fun σ _ ↦ hfac σ, Finset.prod_ite, Finset.prod_const_one,
      mul_one, Finset.prod_const, ← exp_nsmul, Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [smul_neg, nsmul_eq_mul, mul_one, MulAction.mem_stabilizer_iff]
  -- the norm reduces to a uniformizer at the branch of `P'`
  set b' := resBr (E := E) b''
  have he0 : 1 ≤ Nat.card (MulAction.stabilizer (L ≃ₐ[E] L) P'') := Nat.one_le_iff_ne_zero.2
    (Nat.card_ne_zero.2 ⟨⟨⟨1, one_smul _ _⟩⟩, inferInstance⟩)
  have ht₀val : b'.2.1.valuation (redD b'.1 t₀) = exp (-1) := by
    have h1 := brVal_algebraMap (E := E) b'' (t₀ : E)
    have h2 : algebraMap E L (t₀ : E) = (t' : L) := congrArg Subtype.val ht₀
    rw [h2, hval, he] at h1
    change exp _ = (b'.2.1.valuation (redD b'.1 t₀)) ^ _ at h1
    set n := Nat.card (MulAction.stabilizer (L ≃ₐ[E] L) P'')
    have hx0 : b'.2.1.valuation (redD b'.1 t₀) ≠ 0 := by
      intro h0
      rw [h0, zero_pow (by omega)] at h1
      exact exp_ne_zero h1
    rw [← exp_log hx0, ← exp_nsmul] at h1
    have h3 := exp_injective h1
    rw [← exp_log hx0]
    congr 1
    rw [nsmul_eq_mul] at h3
    have h4 : (n : ℤ) * (log (b'.2.1.valuation (redD b'.1 t₀)) + 1) = 0 := by linarith
    rcases mul_eq_zero.1 h4 with h | h
    · omega
    · omega
  have hb'P : placeIdealD b'.1 b'.2.2 = P' := by
    have : b' ∈ discBranches P' := by rw [hP'b]; rfl
    exact this
  refine ⟨b', hP'b, fun α hα ↦ ?_⟩
  have hoth : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C E) b'.1)), R ≠ b'.2.1 →
      placeIdealD b'.1 hR ≠ placeIdealD b'.1 b'.2.2 := by
    intro R hR hne heq
    have hmem : (⟨b'.1, R, hR⟩ : OuterBranch C E) ∈ discBranches P' := by
      change placeIdealD _ _ = P'
      rw [← hb'P]
      exact heq
    rw [hP'b, Set.mem_singleton_iff, Sigma.ext_iff] at hmem
    exact hne (congrArg Subtype.val (eq_of_heq hmem.2))
  obtain ⟨y, s, hs, hys⟩ := exists_eq_of_uniformizer hp hp1 b'.1 b'.2.2 hoth ht₀val hα
  exact ⟨y, s, hb'P ▸ hs, hys⟩

end A6


end Descent

end S8A

end SemistableReduction
