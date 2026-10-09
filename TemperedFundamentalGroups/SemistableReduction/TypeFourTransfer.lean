/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourSheet

/-!
# Transfer of smoothness along a change of coordinate

Blueprint §9.12, leaf T4, part (G), interface `TypeFour.ChartTransfer` (step (4)).

* `exists_branch_of_ker_le`: a point `P'` of `R' = DRint 0 1 F'` over the residue point lying on
  the component of `v` (`ker (redD v) ≤ P'`) carries a branch `(v, Q)` (a place of `κ(v)`
  dominating the image of `P'`, `Ideal.image_subset_nonunits_valuationSubring`);
* `exists_mem_discBranches`: every point over the residue point carries a branch (B4a and
  `DiscDegreeSum`);
* `notMem_placeIdealD_iff`: `y ∉ P'` iff `ȳ` is a unit at the branch;
* **`chartTransfer`**: the branch through `P₁` is unique (the branch correspondence is injective);
  every other component misses `P₁`, so some `z ∈ R'₁ ∖ P₁` vanishes on all other components;
  elements of the `σ`-chart become elements of `R'₁` after multiplication by a power of `z`
  (maximum principle `SmoothVertex.isIntegral_of_le`), with the transported reductions.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open FundamentalInequality GaussStability GaussFibre GaussTube DiscCount SmoothVertex PlaceNorm
  CurvePlace

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-! ### Branches through a point -/

section Branch

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
/-- `x` lies in every point over the residue point. -/
lemma xD_mem {P' : Ideal (DRint (0 : C) 1 F')}
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) =
      discIdeal (0 : C) 1) : (xD : DRint (0 : C) 1 F') ∈ P' := by
  have hX : (⟨RatFunc.X, X_mem_discRing⟩ : discRing (0 : C) 1) ∈ discIdeal (0 : C) 1 :=
    ⟨Polynomial.X, fun i ↦ by rw [coeff_X]; split_ifs <;> simp,
      by rw [aeval_X, gaussCoord_zero_one], by simp⟩
  rw [← hP', Ideal.mem_comap] at hX
  exact hX

/-- **A point on a component carries a branch of that component.** If `P'` is a maximal ideal
of `R'` over the residue point containing the kernel of the reduction `R' → κ(v)`, some zero `Q`
of `x̄` on `κ(v)` has the point `P'`. -/
theorem exists_branch_of_ker_le (v : Ext C F') (P' : Ideal (DRint (0 : C) 1 F'))
    [hP : P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) =
      discIdeal (0 : C) 1)
    (hker : RingHom.ker (redD v) ≤ P') :
    ∃ (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
      (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)), placeIdealD v hQ = P' := by
  classical
  set φ := (redD v).rangeRestrict
  have hφ : Function.Surjective φ := RingHom.rangeRestrict_surjective _
  have hkerφ : RingHom.ker φ ≤ P' := by rwa [RingHom.ker_rangeRestrict]
  have hmax : (P'.map φ).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hφ hkerφ
  obtain ⟨V, hAV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (P'.map φ) hmax.ne_top
  have hdom : ∀ y, redD v y ∈ V := fun y ↦ hAV ⟨y, rfl⟩
  have hnon : ∀ y ∈ P', V.valuation (redD v y) < 1 := fun y hy ↦
    hV ⟨φ y, Ideal.mem_map_of_mem φ hy, rfl⟩
  have hx0 : red C (xF C F') v ≠ 0 := red_xF_ne_zero' v
  have hxlt : V.valuation (red C (xF C F') v) < 1 := hnon xD (xD_mem hP')
  have hxinv : (red C (xF C F') v)⁻¹ ∉ V := by
    intro h
    have h1 := (ValuationSubring.valuation_le_one_iff _ _).2 h
    rw [map_inv₀] at h1
    have h2 := (inv_le_one₀ ((Valuation.pos_iff _).2 hx0)).1 h1
    exact absurd hxlt (not_lt.2 h2)
  have hVne : V ≠ ⊤ := by
    rintro rfl
    exact hxinv trivial
  set Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring) :=
    ⟨V, fun c ↦ by
      obtain ⟨b, rfl⟩ := residue_surjective c
      rw [← redD_constD]
      exact hdom _, hVne⟩
  have hQ : Q ∈ zeros 𝓀 (red C (xF C F') v) := mem_zeros.2 hxinv
  refine ⟨Q, hQ, (hP.eq_of_le (placeIdealD_isMaximal v hQ).ne_top fun y hy ↦ ?_).symm⟩
  rw [mem_placeIdealD_iff]
  refine Q.res_eq_zero_of_lt_one ?_
  rw [CurvePlace.valuation_lt_one_iff]
  exact hnon y hy

/-- The point `y ∉ P'` of a branch iff the reduction `ȳ` is a unit at the branch. -/
lemma notMem_placeIdealD_iff (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (y : DRint (0 : C) 1 F') :
    y ∉ placeIdealD v hQ ↔ Q.valuation (redD v y) = 1 := by
  have hle : Q.valuation (redD v y) ≤ 1 :=
    Q.valuation_le_one_iff.2 (redD_mem_V v y (xbar_mem_V v hQ))
  rw [mem_placeIdealD_iff]
  constructor
  · intro h
    refine le_antisymm hle (not_lt.1 fun hlt ↦ h (Q.res_eq_zero_of_lt_one hlt))
  · intro h h0
    have := Q.valuation_sub_res_lt_one (Q.valuation_le_one_iff.1 hle)
    rw [h0, map_zero, sub_zero, h] at this
    exact lt_irrefl 1 this

/-- A disc valuation of the open unit disc: the Gauss point `w_{0,1/2}`. -/
noncomputable def discValHalf : DiscVal (0 : C) 1 where
  val := gaussRat (NormedField.valuation (K := C)) 0 (Units.mk0 (1 / 2) (by norm_num))
  isDiscVal := ⟨fun c ↦ by rw [gaussRat_algebraMap_C, NormedField.valuation_apply], by
    rw [SmoothVertex.gaussCoord_zero_one, AnnulusUnit.gaussRat_X]
    change (1 / 2 : ℝ≥0) < 1
    norm_num⟩

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- Elements of `R'` are integral over `C[x]`. -/
lemma isIntegral_adjoin (y : DRint (0 : C) 1 F') :
    IsIntegral (Algebra.adjoin C {xF C F'}) (y : F') := by
  let φ : discRing (0 : C) 1 →+* Algebra.adjoin C {xF C F'} :=
    { toFun := fun a ↦ ⟨algebraMap (RatFunc C) F' a, by
        obtain ⟨Q, -, hQ⟩ := mem_discRing_iff.1 a.2
        rw [← hQ, ← aeval_xF]
        exact Polynomial.aeval_mem_adjoin_singleton C _⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  exact IsIntegral.map_of_comp_eq φ (RingHom.id F') (by ext; rfl) y.2

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Every point over the residue point carries a branch** (B4a and `DiscDegreeSum`). -/
theorem exists_mem_discBranches [Algebra.IsSeparable (RatFunc C) F']
    (P' : Ideal (DRint (0 : C) 1 F')) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 F')) =
      discIdeal (0 : C) 1) :
    (discBranches P').Nonempty := by
  classical
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  have hpos := discDegree_pos one_ne_zero discValHalf P' hP'
  rw [discDegree_eq_vertexDegreeD hp hp1, vertexDegreeD_eq_sum] at hpos
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  by_contra h
  exact hb (if_neg fun hb' ↦ h ⟨b, hb'⟩)

end Branch

/-! ### The transfer -/

section Transfer

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {G₁ G₂ : Type*} [Field G₁] [Algebra (RatFunc C) G₁] [Algebra C G₁]
  [IsScalarTower C (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₁]
  [Field G₂] [Algebra (RatFunc C) G₂] [Algebra C G₂]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₂]
  (e : G₂ ≃+* G₁) (he : ∀ c : C, e.symm (algebraMap C G₁ c) = algebraMap C G₂ c)

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra (RatFunc C) G₁]
  [IsScalarTower C (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₁] [Algebra (RatFunc C) G₂]
  [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₂] in
include he in
lemma e_algebraMap (c : C) : e (algebraMap C G₂ c) = algebraMap C G₁ c := by
  rw [← he, RingEquiv.apply_symm_apply]

omit [IsAlgClosed C] [IsScalarTower C (RatFunc C) G₁] [CharZero C]
  [FiniteDimensional (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₂] in
include he in
/-- Elements of the `σ`-chart are integral over `C[x]` if `σ` is. -/
lemma isIntegral_e (hσ : IsIntegral (Algebra.adjoin C {xF C G₁}) (e (xF C G₂)))
    (y : DRint (0 : C) 1 G₂) : IsIntegral (Algebra.adjoin C {xF C G₁}) (e y) := by
  set A₁ := Algebra.adjoin C {xF C G₁}
  set T := integralClosure A₁ G₁
  have hσT : e (xF C G₂) ∈ T.restrictScalars C := hσ
  have hmem : ∀ Q : C[X], aeval (e (xF C G₂)) Q ∈ T.restrictScalars C := fun Q ↦
    Algebra.adjoin_le (Set.singleton_subset_iff.2 hσT) (Polynomial.aeval_mem_adjoin_singleton C _)
  have he' : ∀ Q : C[X], e (aeval (xF C G₂) Q) = aeval (e (xF C G₂)) Q := fun Q ↦ by
    rw [aeval_eq_sum_range, aeval_eq_sum_range, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, map_pow, e_algebraMap e he]
  let ψ : discRing (0 : C) 1 →+* T :=
    { toFun := fun a ↦ ⟨e (algebraMap (RatFunc C) G₂ a), by
        obtain ⟨Q, -, hQ⟩ := mem_discRing_iff.1 a.2
        rw [← hQ, ← aeval_xF, he']
        exact hmem Q⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hT : IsIntegral T (e y) :=
    IsIntegral.map_of_comp_eq ψ e.toRingHom (by ext; rfl) y.2
  exact isIntegral_trans _ hT

omit [IsAlgClosed C] [CharZero C] [Algebra C G₁] [IsScalarTower C (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₁] in
/-- A uniform power of an element of value `< 1` off one extension pushes a given element below
`1` there. -/
lemma exists_pow_mul_le [Finite (Ext C G₁)] (v₁ : Ext C G₁) {z : G₁}
    (hz : ∀ v : Ext C G₁, v ≠ v₁ → v.1 z < 1) (Y : G₁) :
    ∃ N : ℕ, ∀ v : Ext C G₁, v ≠ v₁ → ∀ M ≥ N, v.1 (z ^ M * Y) ≤ 1 := by
  classical
  letI : Fintype (Ext C G₁) := Fintype.ofFinite _
  have hv : ∀ v : Ext C G₁, ∃ N : ℕ, v ≠ v₁ → ∀ M ≥ N, v.1 (z ^ M * Y) ≤ 1 := by
    intro v
    by_cases hvv : v = v₁
    · exact ⟨0, fun h ↦ absurd hvv h⟩
    by_cases hY : v.1 Y = 0
    · exact ⟨0, fun _ M _ ↦ by rw [map_mul, hY, mul_zero]; exact zero_le⟩
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (pos_iff_ne_zero.2 hY)) (hz v hvv)
    refine ⟨N, fun _ M hM ↦ ?_⟩
    rw [map_mul, map_pow]
    have h1 : v.1 z ^ M ≤ v.1 z ^ N := pow_le_pow_of_le_one zero_le (hz v hvv).le hM
    calc v.1 z ^ M * v.1 Y ≤ (v.1 Y)⁻¹ * v.1 Y := mul_le_mul_left (h1.trans hN.le) _
      _ = 1 := inv_mul_cancel₀ hY
  choose N hN using hv
  exact ⟨Finset.univ.sup N, fun v hv M hM ↦
    hN v hv M ((Finset.le_sup (Finset.mem_univ v)).trans hM)⟩

omit [IsAlgClosed C] [CharZero C] [Algebra C G₁] [IsScalarTower C (RatFunc C) G₁]
  [FiniteDimensional (RatFunc C) G₁] in
/-- Away from the other components: if `P₁` lies on the component of `v₁` only, some
`z ∈ R'₁ ∖ P₁` has value `< 1` at every other extension. -/
lemma exists_away [Finite (Ext C G₁)] (P₁ : Ideal (DRint (0 : C) 1 G₁)) [hP₁ : P₁.IsMaximal]
    (v₁ : Ext C G₁)
    (hcomp : ∀ v : Ext C G₁, v ≠ v₁ → ∃ z : DRint (0 : C) 1 G₁, redD v z = 0 ∧ z ∉ P₁) :
    ∃ z : DRint (0 : C) 1 G₁, z ∉ P₁ ∧ ∀ v : Ext C G₁, v ≠ v₁ → v.1 (z : G₁) < 1 := by
  classical
  letI : Fintype (Ext C G₁) := Fintype.ofFinite _
  choose! zz hzz using hcomp
  refine ⟨(Finset.univ.erase v₁).prod zz, fun hz ↦ ?_, fun v hv ↦ ?_⟩
  · obtain ⟨v, hv, hzv⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP₁.isPrime)).1 hz
    exact (hzz v (Finset.ne_of_mem_erase hv)).2 hzv
  · have h0 : redD v ((Finset.univ.erase v₁).prod zz) = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hv, Finset.mem_univ v⟩) (hzz v hv).1
    rw [redD_apply, red_eq_zero_iff (valuation_le_one_D v _)] at h0
    exact h0

omit [FiniteDimensional (RatFunc C) G₂] in
include hp hp1 he in
/-- **Clearing the other components**: `z^M · e y` lies in `R'₁` for large `M`, with the
transported reduction. -/
lemma exists_lift [Finite (Ext C G₁)]
    (hσ : IsIntegral (Algebra.adjoin C {xF C G₁}) (e (xF C G₂))) {v₁ : Ext C G₁} {v₂ : Ext C G₂}
    (h : ∀ y : G₁, v₂.1 (e.symm y) = v₁.1 y) {z : DRint (0 : C) 1 G₁}
    (hzv : ∀ v : Ext C G₁, v ≠ v₁ → v.1 (z : G₁) < 1) (y : DRint (0 : C) 1 G₂) :
    ∃ N : ℕ, ∀ M ≥ N, ∃ Y : DRint (0 : C) 1 G₁,
      resAlgEquiv e.symm he h (redD v₁ Y) =
        resAlgEquiv e.symm he h (redD v₁ z) ^ M * redD v₂ y := by
  have hv₁e : v₁.1 (e y) ≤ 1 := by
    rw [← h, RingEquiv.symm_apply_apply]
    exact valuation_le_one_D v₂ y
  have hred : resAlgEquiv e.symm he h (red C (e y) v₁) = redD v₂ y := by
    rw [resAlgEquiv_red, RingEquiv.symm_apply_apply]
    rfl
  obtain ⟨N, hN⟩ := exists_pow_mul_le v₁ hzv (e y)
  refine ⟨N, fun M hM ↦ ?_⟩
  have hint : IsIntegral (Algebra.adjoin C {xF C G₁}) ((z : G₁) ^ M * e y) :=
    ((isIntegral_adjoin z).pow M).mul (isIntegral_e e he hσ y)
  have hz1 : v₁.1 (z : G₁) ≤ 1 := valuation_le_one_D _ z
  have hout : ∀ v : Ext C G₁, v.1 ((z : G₁) ^ M * e y) ≤ 1 := by
    intro v
    by_cases hv : v = v₁
    · subst hv
      rw [map_mul, map_pow]
      exact mul_le_one' (pow_le_one' hz1 M) hv₁e
    · exact hN v hv M hM
  refine ⟨⟨_, isIntegral_of_le hp hp1 hint hout⟩, ?_⟩
  rw [redD_apply, red_mul (by rw [map_pow]; exact pow_le_one' hz1 M) hv₁e, red_pow hz1, map_mul,
    map_pow, hred]
  rfl

include hp hp1 in
/-- **The branch through `P₁` is unique** if the branch correspondence sends every branch through
`P₁` to the unique branch through `P₂`. -/
lemma discBranches_eq_singleton [Algebra.IsSeparable (RatFunc C) G₁]
    (P₁ : Ideal (DRint (0 : C) 1 G₁)) [P₁.IsMaximal]
    (hc₁ : P₁.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₁)) = discIdeal (0 : C) 1)
    (b₂ : OuterBranch C G₂)
    (himg : ∀ (v₁ : Ext C G₁) (Q₁ : CurvePlace 𝓀 (ResidueField v₁.1.valuationSubring))
      (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C G₁) v₁)), placeIdealD v₁ hQ₁ = P₁ →
      ∃ (v₂ : Ext C G₂) (h : ∀ y : G₁, v₂.1 (e.symm y) = v₁.1 y)
        (hQ₂ : Q₁.map (resAlgEquiv e.symm he h) ∈ zeros 𝓀 (red C (xF C G₂) v₂)),
        (⟨v₂, _, hQ₂⟩ : OuterBranch C G₂) = b₂) :
    ∃ b₁ : OuterBranch C G₁, discBranches P₁ = {b₁} := by
  obtain ⟨⟨v₁, Q₁, hQ₁⟩, hb₁⟩ := exists_mem_discBranches hp hp1 P₁ hc₁
  refine ⟨⟨v₁, Q₁, hQ₁⟩, Set.eq_singleton_iff_unique_mem.2 ⟨hb₁, ?_⟩⟩
  rintro ⟨v, Q, hQ⟩ hb
  obtain ⟨w₂, h, hQ₂, himg₁⟩ := himg v₁ Q₁ hQ₁ hb₁
  obtain ⟨w₂', h', hQ₂', himg₂⟩ := himg v Q hQ hb
  rw [← himg₂, Sigma.mk.inj_iff] at himg₁
  obtain ⟨rfl, hQeq⟩ := himg₁
  have hQeq' := congrArg Subtype.val (eq_of_heq hQeq)
  obtain rfl : v₁ = v := Subtype.ext (Valuation.ext fun y ↦ by rw [← h y, ← h' y])
  obtain rfl := map_injective _ hQeq'
  rfl

set_option maxHeartbeats 400000 in
-- the destructuring of the branch correspondence (dependent pairs over `resAlgEquiv`) is slow
include hp hp1 he in
/-- **(4) `ChartTransfer`: transfer of smoothness along a change of coordinate.** -/
theorem chartTransfer [Algebra.IsSeparable (RatFunc C) G₁] [Algebra.IsSeparable (RatFunc C) G₂] :
    ChartTransfer e he := by
  intro hσ P₁ P₂ hP₁ hP₂ hc₁ hc₂ hbr hsm
  classical
  haveI : Finite (Ext C G₁) := finite_ext (F := G₁) hp hp1
  obtain ⟨b₂, hS₂, hloc₂⟩ := hsm
  -- the image of a branch through `P₁` is the branch through `P₂`
  have himg : ∀ (v₁ : Ext C G₁) (Q₁ : CurvePlace 𝓀 (ResidueField v₁.1.valuationSubring))
      (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C G₁) v₁)), placeIdealD v₁ hQ₁ = P₁ →
      ∃ (v₂ : Ext C G₂) (h : ∀ y : G₁, v₂.1 (e.symm y) = v₁.1 y)
        (hQ₂ : Q₁.map (resAlgEquiv e.symm he h) ∈ zeros 𝓀 (red C (xF C G₂) v₂)),
        (⟨v₂, _, hQ₂⟩ : OuterBranch C G₂) = b₂ := by
    intro v₁ Q₁ hQ₁ hP
    obtain ⟨v₂, h, hQ₂, hP₂'⟩ := hbr v₁ hQ₁ hP
    refine ⟨v₂, h, hQ₂, ?_⟩
    have : (⟨v₂, _, hQ₂⟩ : OuterBranch C G₂) ∈ discBranches P₂ := hP₂'
    rwa [hS₂] at this
  obtain ⟨⟨v₁, Q₁, hQ₁⟩, hS₁⟩ := discBranches_eq_singleton hp hp1 e he P₁ hc₁ b₂ himg
  have hP₁eq : placeIdealD v₁ hQ₁ = P₁ := by
    have : (⟨v₁, Q₁, hQ₁⟩ : OuterBranch C G₁) ∈ discBranches P₁ := by rw [hS₁]; rfl
    exact this
  refine ⟨⟨v₁, Q₁, hQ₁⟩, hS₁, fun α hα ↦ ?_⟩
  -- the corresponding branch through `P₂`
  obtain ⟨v₂, h, hQ₂, hP₂eq⟩ := hbr v₁ hQ₁ hP₁eq
  have hb₂ : (⟨v₂, _, hQ₂⟩ : OuterBranch C G₂) = b₂ := by
    have : (⟨v₂, _, hQ₂⟩ : OuterBranch C G₂) ∈ discBranches P₂ := hP₂eq
    rwa [hS₂] at this
  subst hb₂
  -- no other component passes through `P₁`
  obtain ⟨z, hzP, hzv⟩ := exists_away P₁ v₁ fun v hv ↦ by
    by_contra! H
    obtain ⟨Q, hQ, hP⟩ := exists_branch_of_ker_le v P₁ hc₁ fun z hz ↦ H z hz
    have hmem : (⟨v, Q, hQ⟩ : OuterBranch C G₁) ∈ discBranches P₁ := hP
    rw [hS₁, Set.mem_singleton_iff] at hmem
    exact hv (congrArg Sigma.fst hmem)
  have hzval : Q₁.valuation (redD v₁ z) = 1 := by
    refine (notMem_placeIdealD_iff v₁ hQ₁ z).1 ?_
    rw [hP₁eq]
    exact hzP
  -- the element of the `σ`-chart
  have hα₂ : resAlgEquiv e.symm he h α ∈ (Q₁.map (resAlgEquiv e.symm he h)).V := by
    rw [mem_map_V, AlgEquiv.symm_apply_apply]
    exact hα
  obtain ⟨y₂, s₂, hs₂, hys⟩ := hloc₂ _ hα₂
  have hs₂val : (Q₁.map (resAlgEquiv e.symm he h)).valuation (redD v₂ s₂) = 1 := by
    refine (notMem_placeIdealD_iff v₂ hQ₂ s₂).1 ?_
    rw [hP₂eq]
    exact hs₂
  -- clearing the other components
  obtain ⟨N₁, hN₁⟩ := exists_lift hp hp1 e he hσ h hzv y₂
  obtain ⟨N₂, hN₂⟩ := exists_lift hp hp1 e he hσ h hzv s₂
  obtain ⟨Y, hY⟩ := hN₁ (max N₁ N₂) (le_max_left _ _)
  obtain ⟨S, hS⟩ := hN₂ (max N₁ N₂) (le_max_right _ _)
  refine ⟨Y, S, ?_, ?_⟩
  · rw [← hP₁eq, notMem_placeIdealD_iff]
    have hSeq : redD v₁ S = redD v₁ z ^ max N₁ N₂ *
        (resAlgEquiv e.symm he h).symm (redD v₂ s₂) := by
      apply (resAlgEquiv e.symm he h).injective
      rw [hS, map_mul, map_pow, AlgEquiv.apply_symm_apply]
    rw [hSeq, map_mul, map_pow, hzval, one_pow, one_mul, ← valuation_map, hs₂val]
  · apply (resAlgEquiv e.symm he h).injective
    rw [hY, map_mul, hS, hys]
    ring

end Transfer

end TypeFour

end SemistableReduction
