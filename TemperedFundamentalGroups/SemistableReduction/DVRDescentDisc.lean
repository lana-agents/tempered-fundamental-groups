/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentKernel
import TemperedFundamentalGroups.SemistableReduction.SmoothVertex
import TemperedFundamentalGroups.SemistableReduction.DVRDescentSpan

/-!
# The descent setting for the vertex (disc) chart (W10, smooth part)

Blueprint §9.12 (O7), the disc-chart analogue of the O1 setting (`DVRDescentSetting`,
`DVRDescentIntegral`, `DVRDescentKernel`). Let `φ : E → C` be isometric and `χ : F₀ → F'`
compatible with `ratFuncMap φ` (`IsCompat`).

* `map_discRingE_le`, `mem_discRing_of_map`: `O_C[x] ∩ E(x) = O_E[x]` (for the norms);
* `BD E F₀ = DRint 0 1 F₀`, the integral closure of `O_E[x]` in `F₀`, and the injective map
  `ιD : BD → R' = DRint 0 1 F'`;
* `isIntegral_of_χD`, `mem_BD_of_χ`: `BD = R' ∩ F₀` (when `F' = C(x)·χ(F₀)` and the degrees agree);
* `bdAlgebra`, `cstD`: the `O_E`-algebra structure of `BD`; `finiteType_BD`: `BD` is of finite
  type over `O_E` (a DVR, `F₀ / E(x)` finite separable);
* **`exists_eq_cst_mulD`** (the kernel of the reduction over `E`): an element of `BD` with value
  `< 1` at every extension of `w_{0,1}` is divisible by `ϖ_E` (`e = 1` and the maximum principle
  `SmoothVertex.isIntegral_of_le`).
-/

open NNReal Polynomial IsLocalRing

namespace SemistableReduction

namespace DVRDescent

open GaussTube DiscCount SmoothVertex FundamentalInequality GaussStability GaussFibre

universe u

section Setting

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}

/-- The vertex chart over `O_E` maps into the vertex chart over `O_C`. -/
theorem map_discRingE_le (hφ : ∀ e, ‖φ e‖ = ‖e‖) :
    (discRing (0 : E) 1).map (ratFuncMap φ) ≤ discRing (0 : C) 1 := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨Q, hQ, rfl⟩ := mem_discRing_iff.1 ha
  rw [ratFuncMap_algebraMap]
  refine mem_discRing_iff.2 ⟨Q.map φ, Gauss.sup_le_iff.2 fun i ↦ ?_, rfl⟩
  simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply, coeff_map]
  have := coeff_le_one_of_sup_le_one hQ i
  rw [NormedField.valuation_apply] at this
  have h : ‖φ (Q.coeff i)‖₊ = ‖Q.coeff i‖₊ := NNReal.eq (hφ _)
  rw [h]
  exact this

/-- **`O_C[x] ∩ E(x) = O_E[x]`.** -/
theorem mem_discRing_of_map (hφ : ∀ e, ‖φ e‖ = ‖e‖) {a : RatFunc E}
    (ha : ratFuncMap φ a ∈ discRing (0 : C) 1) : a ∈ discRing (0 : E) 1 := by
  obtain ⟨Q, hQ, hQa⟩ := mem_discRing_iff.1 ha
  obtain ⟨P, rfl⟩ := exists_eq_algebraMap_of_ratFuncMap φ hQa.symm
  rw [ratFuncMap_algebraMap] at hQa
  have hPQ : Q = P.map φ := IsFractionRing.injective C[X] (RatFunc C) hQa
  subst hPQ
  refine mem_discRing_iff.2 ⟨P, Gauss.sup_le_iff.2 fun i ↦ ?_, rfl⟩
  simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply]
  have := coeff_le_one_of_sup_le_one hQ i
  rw [NormedField.valuation_apply, coeff_map] at this
  have h : ‖φ (P.coeff i)‖₊ = ‖P.coeff i‖₊ := NNReal.eq (hφ _)
  rwa [h] at this

/-- The restriction `O_E[x] → O_C[x]`. -/
noncomputable def discMap (hφ : ∀ e, ‖φ e‖ = ‖e‖) : discRing (0 : E) 1 →+* discRing (0 : C) 1 :=
  ((ratFuncMap φ).comp (discRing (0 : E) 1).subtype).codRestrict _ fun a ↦
    map_discRingE_le hφ ⟨a, a.2, rfl⟩

@[simp]
lemma coe_discMap (hφ : ∀ e, ‖φ e‖ = ‖e‖) (a : discRing (0 : E) 1) :
    (discMap hφ a : RatFunc C) = ratFuncMap φ a :=
  rfl

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']
  (F₀ : Type*) [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* F'}

variable (E) in
/-- The integral closure of the vertex chart `O_E[x]` in `F₀`. -/
noncomputable abbrev BD : Subalgebra (discRing (0 : E) 1) F₀ := DRint (0 : E) 1 F₀

variable {F₀}

/-- Elements of `BD` map to elements integral over the vertex chart over `O_C`. -/
theorem isIntegral_mapD (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) (y : BD E F₀) :
    IsIntegral (discRing (0 : C) 1) (χ y) := by
  obtain ⟨p, hp, hpy⟩ := y.2
  refine ⟨p.map (discMap hφ), hp.map _, ?_⟩
  rw [eval₂_map]
  have : (algebraMap (discRing (0 : C) 1) F').comp (discMap hφ) =
      χ.comp (algebraMap (discRing (0 : E) 1) F₀) := by
    ext a
    change algebraMap (RatFunc C) F' (ratFuncMap φ a) = χ (algebraMap (RatFunc E) F₀ a)
    rw [hχ]
  rw [this, ← hom_eval₂, hpy, map_zero]

variable (χ) in
/-- The map `BD → R'`. -/
noncomputable def ιD (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) :
    BD E F₀ →+* DRint (0 : C) 1 F' where
  toFun y := ⟨χ y, isIntegral_mapD hφ hχ y⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma coe_ιD (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) (y : BD E F₀) :
    ((ιD χ hφ hχ y : DRint (0 : C) 1 F') : F') = χ y := rfl

lemma ιD_injective (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ) :
    Function.Injective (ιD χ hφ hχ (F₀ := F₀)) := by
  intro y z h
  have := congrArg (fun w : DRint (0 : C) 1 F' ↦ (w : F')) h
  simp only [coe_ιD] at this
  exact Subtype.ext (χ.injective this)

variable [FiniteDimensional (RatFunc C) F'] [FiniteDimensional (RatFunc E) F₀]

/-- **Integrality descends** to the vertex chart over `O_E`. -/
theorem isIntegral_of_χD (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤) {y : F₀}
    (hy : IsIntegral (discRing (0 : C) 1) (χ y)) : IsIntegral (discRing (0 : E) 1) y := by
  haveI := isIntegrallyClosed_discRing (a := (0 : C)) (c := (1 : C)) one_ne_zero
  haveI := isFractionRing_discRing (a := (0 : C)) (c := (1 : C)) one_ne_zero
  exact isIntegral_of_isIntegral_map (ratFuncMap φ) χ (discRing (0 : E) 1) (discRing (0 : C) 1)
    (fun z hz ↦ mem_discRing_of_map hφ hz) (minpoly_χ_eq hχ hdeg hθ y) hy

/-- **`BD = R' ∩ F₀`.** -/
theorem mem_BD_of_χ (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤) {y : F₀}
    (hy : χ y ∈ DRint (0 : C) 1 F') : y ∈ BD E F₀ :=
  isIntegral_of_χD hφ hχ hdeg hθ hy

end Setting

/-! ### The `O_E`-algebra structure -/

section Algebra

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀]

/-- `O_E → O_E[x]`. -/
noncomputable def intDisc : HenselComplete.integers E →+* discRing (0 : E) 1 :=
  ((algebraMap E (RatFunc E)).comp (HenselComplete.integers E).subtype).codRestrict _
    fun b ↦ algebraMap_mem_discRing' b

/-- The `O_E`-algebra structure of `BD`. -/
@[reducible] noncomputable def bdAlgebra : Algebra (HenselComplete.integers E) (BD E F₀) :=
  ((algebraMap (discRing (0 : E) 1) (BD E F₀)).comp intDisc).toAlgebra

/-- The constants of `O_E` in `BD`. -/
noncomputable def cstD (e : HenselComplete.integers E) : BD E F₀ :=
  algebraMap (discRing (0 : E) 1) (BD E F₀) (intDisc e)

lemma coe_cstD (e : HenselComplete.integers E) : ((cstD e : BD E F₀) : F₀) = cst (e : E) := rfl

lemma bdAlgebra_algebraMap (e : HenselComplete.integers E) :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    algebraMap (HenselComplete.integers E) (BD E F₀) e = cstD e :=
  rfl

lemma cstD_mul (e e' : HenselComplete.integers E) :
    (cstD (e * e') : BD E F₀) = cstD e * cstD e' := by
  simp [cstD]

lemma cstD_sub (e e' : HenselComplete.integers E) :
    (cstD (e - e') : BD E F₀) = cstD e - cstD e' := by
  simp [cstD]

lemma cstD_one : (cstD 1 : BD E F₀) = 1 := by
  simp [cstD]

/-- `O_E[X] → O_E[x]` is surjective. -/
lemma intDisc_aeval_surjective :
    letI := (intDisc (E := E)).toAlgebra
    Function.Surjective (aeval (R := HenselComplete.integers E)
      (⟨RatFunc.X, X_mem_discRing⟩ : discRing (0 : E) 1)) := by
  letI := (intDisc (E := E)).toAlgebra
  rintro ⟨f, hf⟩
  obtain ⟨Q, hQ, rfl⟩ := mem_discRing_iff.1 hf
  have hcoeff : (↑Q.coeffs : Set E) ⊆ (HenselComplete.integers E).toSubring := by
    intro a ha
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 ha
    exact coeff_le_one_of_sup_le_one hQ n
  refine ⟨Q.toSubring _ hcoeff, Subtype.ext ?_⟩
  change (discRing (0 : E) 1).subtype (eval₂ (algebraMap _ _) _ (Q.toSubring _ hcoeff)) = _
  rw [hom_eval₂]
  have : (discRing (0 : E) 1).subtype.comp
      (algebraMap (HenselComplete.integers E).toSubring (discRing (0 : E) 1)) =
      (algebraMap E (RatFunc E)).comp (HenselComplete.integers E).toSubring.subtype := rfl
  rw [this, ← eval₂_map, map_toSubring, ← aeval_def]
  exact RatFunc.aeval_X_left_eq_algebraMap Q

/-- `BD` is of finite type over `O_E`. -/
theorem finiteType_BD [IsNoetherianRing (HenselComplete.integers E)]
    [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀] :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    Algebra.FiniteType (HenselComplete.integers E) (BD E F₀) := by
  letI := (intDisc (E := E)).toAlgebra
  letI := bdAlgebra (E := E) (F₀ := F₀)
  haveI : IsScalarTower (HenselComplete.integers E) (discRing (0 : E) 1) (BD E F₀) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.FiniteType (HenselComplete.integers E) (discRing (0 : E) 1) :=
    Algebra.FiniteType.of_surjective (aeval _) intDisc_aeval_surjective
  haveI : IsNoetherianRing (discRing (0 : E) 1) :=
    Algebra.FiniteType.isNoetherianRing (HenselComplete.integers E) _
  haveI := isIntegrallyClosed_discRing (a := (0 : E)) (c := (1 : E)) one_ne_zero
  haveI := isFractionRing_discRing (a := (0 : E)) (c := (1 : E)) one_ne_zero
  haveI : Module.Finite (discRing (0 : E) 1) (BD E F₀) :=
    IsIntegralClosure.finite (discRing (0 : E) 1) (RatFunc E) F₀ (BD E F₀)
  exact Algebra.FiniteType.trans (S := discRing (0 : E) 1) inferInstance inferInstance

end Algebra

/-! ### The kernel of the reduction over `E` -/

section Kernel

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  {χ : F₀ →+* F'}

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) F'] in
/-- Elements integral over `O_C[x]` are integral over `C[x]`. -/
lemma isIntegral_adjoin_of_discRing {y : F'} (hy : IsIntegral (discRing (0 : C) 1) y) :
    IsIntegral (Algebra.adjoin C {xF C F'}) y := by
  have hmem : ∀ f : discRing (0 : C) 1,
      algebraMap (RatFunc C) F' f ∈ Algebra.adjoin C {xF C F'} := by
    rintro ⟨f, hf⟩
    obtain ⟨Q, -, rfl⟩ := mem_discRing_iff.1 hf
    change algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) Q) ∈ _
    rw [← aeval_xF, Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨Q, rfl⟩
  let ψ : discRing (0 : C) 1 →+* Algebra.adjoin C {xF C F'} :=
    { toFun := fun f ↦ ⟨algebraMap (RatFunc C) F' f, hmem f⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b ↦ Subtype.ext (by simp) }
  exact IsIntegral.map_of_comp_eq ψ (RingHom.id F') (RingHom.ext fun _ ↦ rfl) hy

include hp hp1 in
/-- **The kernel of the reduction over `E`** for the vertex chart (`e = 1` + the maximum
principle): an element of `BD` whose image has value `< 1` at every extension of `w_{0,1}` is
divisible by `ϖ_E` in `BD`. -/
theorem exists_eq_cst_mulD (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (heo : ∀ (v : Ext C F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    {ϖ : E} (hϖ0 : ϖ ≠ 0) (hϖ : ∀ e : E, ‖e‖ < 1 → ‖e‖ ≤ ‖ϖ‖) {z : BD E F₀}
    (hout : ∀ v : Ext C F', v.1 (χ z) < 1) :
    ∃ y : BD E F₀, (z : F₀) = cst ϖ * y := by
  have hϖF : algebraMap C F' (φ ϖ) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap C F').injective, map_eq_zero_iff _ φ.injective]
    exact hϖ0
  set w : F' := algebraMap C F' (φ ϖ)⁻¹ * χ z
  have hconst : ∀ e : E, ∀ v : Ext C F', v.1 (algebraMap C F' (φ e)) = ‖e‖₊ := by
    intro e v
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', valuation_algebraMap,
      gauss1_algebraMap_C, ← NNReal.coe_inj]
    simp [hφ]
  have hout' : ∀ v : Ext C F', v.1 w ≤ 1 := by
    intro v
    obtain ⟨e, he⟩ := heo v z
    have hvE : vE φ e = ‖e‖₊ := by
      simp [vE, NormedField.valuation_apply, ← NNReal.coe_inj, hφ]
    have hlt := hout v
    rw [he, hvE] at hlt
    have hle : ‖e‖₊ ≤ ‖ϖ‖₊ := by
      have := hϖ e (by exact_mod_cast hlt)
      exact_mod_cast this
    have hϖpos : (0 : ℝ≥0) < ‖ϖ‖₊ := by simpa using hϖ0
    simp only [w, map_mul, map_inv₀, hconst ϖ v, he, hvE]
    rw [inv_mul_le_iff₀ hϖpos, mul_one]
    exact hle
  have hint : IsIntegral (Algebra.adjoin C {xF C F'}) w := by
    refine IsIntegral.mul ?_ (isIntegral_adjoin_of_discRing (isIntegral_mapD hφ hχ z))
    exact isIntegral_algebraMap (x := (⟨_, Subalgebra.algebraMap_mem _ (φ ϖ)⁻¹⟩ :
      Algebra.adjoin C {xF C F'}))
  have hwR := isIntegral_of_le hp hp1 hint hout'
  have hϖ0F : (cst ϖ : F₀) ≠ 0 := by
    intro h
    apply hϖF
    rw [← χ_cst hχ, h, map_zero]
  have hmem : (cst ϖ : F₀)⁻¹ * z ∈ BD E F₀ := by
    refine mem_BD_of_χ hφ hχ hdeg hθ ?_
    rw [map_mul, map_inv₀, χ_cst hχ, ← map_inv₀]
    exact hwR
  refine ⟨⟨_, hmem⟩, ?_⟩
  change (z : F₀) = cst ϖ * ((cst ϖ : F₀)⁻¹ * z)
  rw [← mul_assoc, mul_inv_cancel₀ hϖ0F, one_mul]

end Kernel

/-! ### Vertices without a branch at `P'` -/

section KerNotMem

open ZariskiModel PlaceNorm

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- **Vertices without a branch at `P'` are killed by an element outside `P'`** (vertex chart). -/
theorem exists_mem_ker_notMemD (v : Ext C F') {P' : Ideal (DRint (0 : C) 1 F')} [P'.IsMaximal]
    (hx : xD ∈ P')
    (hno : ∀ Q (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)), placeIdealD v hQ ≠ P') :
    ∃ t : DRint (0 : C) 1 F', redD v t = 0 ∧ t ∉ P' := by
  classical
  by_contra! hk
  set ρ := redD v
  have hker : RingHom.ker ρ.rangeRestrict ≤ P' := fun t ht ↦ hk t (by
    have := congrArg Subtype.val (RingHom.mem_ker.mp ht)
    simpa using this)
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  set 𝔐 : Ideal ρ.range := P'.map ρ.rangeRestrict
  haveI h𝔐 : 𝔐.IsPrime := Ideal.map_isPrime_of_surjective hsurj hker
  have hcomap : 𝔐.comap ρ.rangeRestrict = P' := by
    rw [Ideal.comap_map_of_surjective _ hsurj, sup_eq_left]
    exact fun t ht ↦ hker (RingHom.mem_ker.mpr (Ideal.mem_bot.mp (Ideal.mem_comap.mp ht)))
  obtain ⟨U, hRU, hlt, heq⟩ := exists_valuationSubring_of_isPrime ρ.range 𝔐
  have hU : ∀ t : DRint (0 : C) 1 F', U.valuation (ρ t) < 1 ↔ t ∈ P' := by
    intro t
    constructor
    · intro h
      by_contra ht
      have : ρ.rangeRestrict t ∉ 𝔐 := fun hm ↦ ht (by
        rw [← hcomap]; exact hm)
      have := heq _ this
      simp only [RingHom.coe_rangeRestrict] at this
      exact absurd this h.ne
    · intro ht
      exact hlt _ (Ideal.mem_map_of_mem _ ht)
  have hk' : ∀ a : 𝓀, algebraMap 𝓀 (ResidueField v.1.valuationSubring) a ∈ U := by
    intro a
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine hRU ⟨constD b, ?_⟩
    exact redD_constD v b
  have hxU : U.valuation (red C (xF C F') v) < 1 := (hU xD).mpr hx
  have hx0 := red_xF_ne_zero' (F' := F') v
  have hne : U ≠ ⊤ := by
    intro hUt
    have h1 : U.valuation (red C (xF C F') v)⁻¹ ≤ 1 :=
      (U.valuation_le_one_iff _).mpr (hUt ▸ trivial)
    have h2 : U.valuation (red C (xF C F') v) * U.valuation (red C (xF C F') v)⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hx0, map_one]
    have h3 : U.valuation (red C (xF C F') v) * U.valuation (red C (xF C F') v)⁻¹ < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left zero_le hxU h1
    exact absurd h2 h3.ne
  let Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring) := ⟨U, hk', hne⟩
  have hQ : Q ∈ zeros 𝓀 (red C (xF C F') v) := by
    rw [mem_zeros]
    intro hmem
    have h1 : U.valuation (red C (xF C F') v)⁻¹ ≤ 1 := (U.valuation_le_one_iff _).mpr hmem
    rw [map_inv₀] at h1
    have h2 : (1 : _) < (U.valuation (red C (xF C F') v))⁻¹ :=
      one_lt_inv₀ ((Valuation.pos_iff _).mpr hx0) |>.mpr hxU
    exact absurd h1 (not_le.mpr h2)
  apply hno Q hQ
  refine ((‹P'.IsMaximal›).eq_of_le (placeIdealD_isMaximal v hQ).ne_top ?_).symm
  intro t ht
  rw [mem_placeIdealD_iff]
  refine Q.res_eq_zero_of_lt_one ?_
  rw [CurvePlace.valuation_lt_one_iff]
  exact (hU t).mpr ht

end KerNotMem

/-! ### The reductions of the vertex chart are finitely spanned -/

section Spanning

open ConstantDescent

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- **The reductions of the vertex chart at two vertices are spanned over `k` by finitely many of
them** (times powers of `x`): every subring `B ⊆ R'` containing the `r_j` and `x` spans all
reductions (`ConstantDescent.IsSpanned`). -/
theorem exists_spanningD (v₁ v₂ : Ext C F') :
    ∃ (N : ℕ) (r : Fin N → DRint (0 : C) 1 F'), ∀ B : Subring (DRint (0 : C) 1 F'),
      (∀ j, r j ∈ B) → xD ∈ B → ∀ y, IsSpanned 𝓀 B (redD v₁) (redD v₂) y := by
  classical
  set ρ₁ := redD v₁
  set ρ₂ := redD v₂
  set xb₁ := red C (xF C F') v₁
  set xb₂ := red C (xF C F') v₂
  let κ₁ := ResidueField v₁.1.valuationSubring
  let κ₂ := ResidueField v₂.1.valuationSubring
  let A := 𝓀[X]
  let ψ : A →ₐ[𝓀] κ₁ × κ₂ := aeval ((xb₁, xb₂) : κ₁ × κ₂)
  letI : Algebra A (κ₁ × κ₂) := ψ.toRingHom.toAlgebra
  have hsmul : ∀ (a : A) (m : κ₁ × κ₂), a • m = ψ a * m := fun a m ↦ Algebra.smul_def a m
  have hψ₁ : ∀ a : A, (ψ a).1 = aeval xb₁ a := fun a ↦ by
    have := Polynomial.aeval_algHom_apply (AlgHom.fst 𝓀 κ₁ κ₂) ((xb₁, xb₂) : κ₁ × κ₂) a
    exact this.symm
  have hψ₂ : ∀ a : A, (ψ a).2 = aeval xb₂ a := fun a ↦ by
    have := Polynomial.aeval_algHom_apply (AlgHom.snd 𝓀 κ₁ κ₂) ((xb₁, xb₂) : κ₁ × κ₂) a
    exact this.symm
  have hexp : ∀ {κ : Type _} [Field κ] [Algebra 𝓀 κ] (ρ : DRint (0 : C) 1 F' →+* κ) (xb : κ),
      ρ xD = xb → ∀ (a : A) (r : DRint (0 : C) 1 F'),
      aeval xb a * ρ r = ∑ d ∈ a.support, algebraMap 𝓀 κ (a.coeff d) * ρ (xD ^ d * r) := by
    intro κ _ _ ρ xb hx a r
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [map_mul, map_pow, hx]
    ring
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_red_x (F := F') v₁)
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_red_x (F := F') v₂)
  obtain ⟨G₁, -, hsp₁⟩ := CurveGenerators.exists_generators (transcendental_red_x (F := F') v₁)
  obtain ⟨G₂, -, hsp₂⟩ := CurveGenerators.exists_generators (transcendental_red_x (F := F') v₂)
  let ρ : DRint (0 : C) 1 F' → κ₁ × κ₂ := fun y ↦ (ρ₁ y, ρ₂ y)
  let N : Submodule A (κ₁ × κ₂) :=
    Submodule.span A ((G₁.image fun g ↦ ((g, 0) : κ₁ × κ₂)) ∪ (G₂.image fun g ↦ (0, g)) :
      Finset (κ₁ × κ₂))
  have hle : Submodule.span A (Set.range ρ) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨c₁, hc₁⟩ := hsp₁ _ (redD_isIntegral v₁ y)
    obtain ⟨c₂, hc₂⟩ := hsp₂ _ (redD_isIntegral v₂ y)
    have e : ρ y = ∑ g ∈ G₁, (c₁ g) • ((g, 0) : κ₁ × κ₂)
        + ∑ g ∈ G₂, (c₂ g) • ((0, g) : κ₁ × κ₂) := by
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.fst_sum, hsmul, Prod.fst_mul, mul_zero,
          Finset.sum_const_zero, add_zero, hψ₁]
        exact hc₁
      · simp only [Prod.snd_add, Prod.snd_sum, hsmul, Prod.snd_mul, mul_zero,
          Finset.sum_const_zero, zero_add, hψ₂]
        exact hc₂
    rw [e]
    refine add_mem
      (Submodule.sum_mem _ fun g hg ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.sum_mem _ fun g hg ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    · simp [hg]
    · simp [hg]
  have hNfg : N.FG := Submodule.fg_span (Finset.finite_toSet _)
  haveI : IsNoetherian A N := isNoetherian_of_fg_of_noetherian N hNfg
  have hΛ : (Submodule.span A (Set.range ρ)).FG := isNoetherian_submodule.mp ‹_› _ hle
  obtain ⟨t, ht, htspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hΛ
  choose rr hrr using fun m : t ↦ ht m.2
  refine ⟨t.card, fun j ↦ rr (t.equivFin.symm j), fun B hB hx y ↦ ?_⟩
  have hrrB : ∀ m : t, rr m ∈ B := fun m ↦ by
    have := hB (t.equivFin m)
    simpa using this
  have hmem : ρ y ∈ Submodule.span A (t : Set (κ₁ × κ₂)) := by
    rw [← htspan]; exact Submodule.subset_span ⟨y, rfl⟩
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hmem
  have hsum : ρ y = ∑ m ∈ t.attach, f m • ρ (rr m) := by
    rw [← hf, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hrr m]
  refine GaussTube.isSpanned_of_finset (t.attach.sigma fun m ↦ (f m).support)
    (fun md ↦ (f md.1).coeff md.2) (fun md ↦ xD ^ md.2 * rr md.1)
    (fun md _ ↦ B.mul_mem (B.pow_mem hx _) (hrrB _)) ?_ ?_
  · have := congrArg Prod.fst hsum
    simp only [Prod.fst_sum, hsmul, Prod.fst_mul, hψ₁] at this
    rw [show ρ₁ y = (ρ y).1 from rfl, this, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    exact hexp ρ₁ xb₁ (redD_xD v₁) _ _
  · have := congrArg Prod.snd hsum
    simp only [Prod.snd_sum, hsmul, Prod.snd_mul, hψ₂] at this
    rw [show ρ₂ y = (ρ y).2 from rfl, this, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    exact hexp ρ₂ xb₂ (redD_xD v₂) _ _

end Spanning

end DVRDescent

end SemistableReduction
