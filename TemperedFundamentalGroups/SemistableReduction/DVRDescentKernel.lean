/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentIntegral
import TemperedFundamentalGroups.SemistableReduction.DVRDescentCount
import TemperedFundamentalGroups.SemistableReduction.NodeMaximum
import TemperedFundamentalGroups.SemistableReduction.MonomialExists

/-!
# The kernel of the reduction at a node point over `E` (O1, step (E))

Blueprint §9.12, O1 (S7.9: `ker ρ = ϖ B_𝔭` by `e = 1` and the maximum principle).

* `GaussTube.exists_mem_ker_notMem`: if no zero of `x̄` on the residue curve of an outer vertex
  `v` has the point `P'` (over the node), some element of `R'` reduces to `0` at `v` but does not
  lie in `P'` (otherwise a valuation ring of `κ(v)` dominating the image of `R'` at `P'`, Chevalley,
  would be such a zero).
-/

open NNReal Polynomial IsLocalRing Valuation

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable {c : C} (hc : ‖c‖ < 1)

/-- **Vertices without a branch at `P'` are killed by an element outside `P'`.** -/
theorem exists_mem_ker_notMem (v : Ext C F') {P' : Ideal (Rint c F')} [P'.IsMaximal]
    (hx : xR c ∈ P')
    (hno : ∀ Q (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)), placeIdeal hc v hQ ≠ P') :
    ∃ t : Rint c F', redHom hc v t = 0 ∧ t ∉ P' := by
  classical
  by_contra! hk
  set ρ := redHom hc v
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
  have hU : ∀ t : Rint c F', U.valuation (ρ t) < 1 ↔ t ∈ P' := by
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
  -- the place
  have hk' : ∀ a : 𝓀, algebraMap 𝓀 (ResidueField v.1.valuationSubring) a ∈ U := by
    intro a
    obtain ⟨b, rfl⟩ := residue_surjective a
    refine hRU ⟨constR c b, ?_⟩
    exact redHom_constR hc v b
  have hxU : U.valuation (red C (xF C F') v) < 1 := (hU (xR c)).mpr hx
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
  refine ((‹P'.IsMaximal›).eq_of_le (placeIdeal_isMaximal hc v hQ).ne_top ?_).symm
  intro t ht
  rw [mem_placeIdeal_iff]
  refine Q.res_eq_zero_of_lt_one ?_
  rw [CurvePlace.valuation_lt_one_iff]
  exact (hU t).mpr ht

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- Elements integral over the node chart become integral over `C[x]` after multiplication by a
power of `x`. -/
theorem exists_xF_pow_mul_isIntegral {y : F'} (hy : IsIntegral (nodeRing c) y) :
    ∃ N : ℕ, IsIntegral (Algebra.adjoin C {xF C F'}) (xF C F' ^ N * y) := by
  classical
  obtain ⟨p, hpm, hpy⟩ := hy
  choose k Q hkQ using fun i ↦ exists_mul_pow_eq (p.coeff i).2
  set K := (Finset.range (p.natDegree + 1)).sup k
  letI : Algebra C[X] F' := ((algebraMap (RatFunc C) F').comp
    (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  set p' : (RatFunc C)[X] := p.map (nodeRing c).subtype
  have hp'm : p'.Monic := hpm.map _
  have hp'y : aeval y p' = 0 := by
    rw [aeval_def, eval₂_map]
    exact hpy
  set q := p'.scaleRoots (RatFunc.X ^ K)
  have hq : aeval (xF C F' ^ K * y) q = 0 := by
    have := scaleRoots_aeval_eq_zero (r := (RatFunc.X : RatFunc C) ^ K) hp'y
    rwa [map_pow] at this
  have hqm : q.Monic := (monic_scaleRoots_iff _).mpr hp'm
  have hlift : q ∈ Polynomial.lifts (algebraMap C[X] (RatFunc C)) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    by_cases hi : i ≤ p'.natDegree
    · rcases hi.lt_or_eq with hi | rfl
      · have hn : p'.natDegree = p.natDegree := natDegree_map_eq_of_injective
          (nodeRing c).subtype_injective _
        have hki : k i ≤ K * (p'.natDegree - i) := by
          have h1 : k i ≤ K := Finset.le_sup (f := k)
            (Finset.mem_range.mpr (by rw [← hn]; omega))
          exact h1.trans (Nat.le_mul_of_pos_right _ (by omega))
        refine ⟨Q i * Polynomial.X ^ (K * (p'.natDegree - i) - k i), ?_⟩
        rw [map_mul, map_pow, RatFunc.algebraMap_X, ← hkQ i, mul_assoc, ← pow_add,
          Nat.add_sub_cancel' hki, ← pow_mul]
        simp [p', coeff_map]
      · rw [Nat.sub_self, pow_zero, mul_one, hp'm.coeff_natDegree]
        exact ⟨1, map_one _⟩
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp hi), zero_mul]
      exact ⟨0, map_zero _⟩
  obtain ⟨q₀, hq₀, -, hq₀m⟩ := lifts_and_natDegree_eq_and_monic hlift hqm
  have hint : IsIntegral C[X] (xF C F' ^ K * y) := by
    refine ⟨q₀, hq₀m, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap (RatFunc C), hq₀]
    exact hq
  refine ⟨K, ?_⟩
  have hrange : Algebra.adjoin C {xF C F'} = (aeval (xF C F') : C[X] →ₐ[C] F').range :=
    Algebra.adjoin_singleton_eq_range_aeval C (xF C F')
  set ψ : C[X] →+* Algebra.adjoin C {xF C F'} :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
      (aeval (xF C F') : C[X] →ₐ[C] F').rangeRestrict.toRingHom
  refine IsIntegral.map_of_comp_eq ψ (RingHom.id F') (RingHom.ext fun P ↦ ?_) hint
  change aeval (xF C F') P = algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) P)
  exact aeval_xF P

end GaussTube

end SemistableReduction

namespace SemistableReduction

namespace DVRDescent

open GaussTube FundamentalInequality GaussStability GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  {χ : F₀ →+* F'}

/-- The image of `ϖ ∈ E` in `F₀`. -/
noncomputable abbrev cst (e : E) : F₀ := algebraMap (RatFunc E) F₀ (algebraMap E (RatFunc E) e)

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [IsUltrametricDist E]
  [FiniteDimensional (RatFunc C) F'] [FiniteDimensional (RatFunc E) F₀] in
lemma χ_cst (hχ : IsCompat φ χ) (e : E) : χ (cst e : F₀) = algebraMap C F' (φ e) := by
  rw [hχ, ratFuncMap_algebraMap_C, ← IsScalarTower.algebraMap_apply]

include hp hp1 in
/-- **The kernel of the reduction over `E`** (`e = 1` + the maximum principle): an element of
`B_E` whose image has value `< 1` at every vertex (outer and inner) is divisible by `ϖ_E` in
`B_E`. -/
theorem exists_eq_cst_mul (hφ : ∀ e, ‖φ e‖ = ‖e‖) (hχ : IsCompat φ χ)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤) {c₀ : E} (hc0 : c₀ ≠ 0)
    (hc1 : ‖c₀‖ ≤ 1) (hc0' : φ c₀ ≠ 0)
    (heo : ∀ (v : Ext C F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    (hei : ∀ (v : GaussExtension (0 : C) (invRad hc0' 1) F') (f : F₀), ∃ e, v.1 (χ f) = vE φ e)
    {ϖ : E} (hϖ0 : ϖ ≠ 0) (hϖ : ∀ e : E, ‖e‖ < 1 → ‖e‖ ≤ ‖ϖ‖) {z : BE F₀ c₀}
    (hout : ∀ v : Ext C F', v.1 (χ z) < 1)
    (hin : ∀ v : GaussExtension (0 : C) (invRad hc0' 1) F', v.1 (χ z) < 1) :
    ∃ y : BE F₀ c₀, (z : F₀) = cst ϖ * y := by
  have hϖF : algebraMap C F' (φ ϖ) ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (algebraMap C F').injective, map_eq_zero_iff _ φ.injective]
    exact hϖ0
  set w : F' := algebraMap C F' (φ ϖ)⁻¹ * χ z
  -- the bound at a vertex
  have hbound : ∀ (v : Valuation F' ℝ≥0), v (algebraMap C F' (φ ϖ)) = ‖ϖ‖₊ →
      (∀ e : E, v (algebraMap C F' (φ e)) = vE φ e) → v (χ z) < 1 →
      (∃ e, v (χ z) = vE φ e) → v w ≤ 1 := by
    intro v hvϖ _ hlt ⟨e, he⟩
    have hvE : vE φ e = ‖e‖₊ := by
      simp [vE, NormedField.valuation_apply, ← NNReal.coe_inj, hφ]
    rw [he, hvE] at hlt
    have hle : ‖e‖₊ ≤ ‖ϖ‖₊ := by
      have := hϖ e (by exact_mod_cast hlt)
      exact_mod_cast this
    have hϖpos : (0 : ℝ≥0) < ‖ϖ‖₊ := by simpa using hϖ0
    simp only [w, map_mul, map_inv₀, hvϖ, he, hvE]
    rw [inv_mul_le_iff₀ hϖpos, mul_one]
    exact hle
  have hconst : ∀ e : E, ∀ v : Ext C F', v.1 (algebraMap C F' (φ e)) = ‖e‖₊ := by
    intro e v
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', valuation_algebraMap,
      gauss1_algebraMap_C, ← NNReal.coe_inj]
    simp [hφ]
  have hconst' : ∀ e : E, ∀ v : GaussExtension (0 : C) (invRad hc0' 1) F',
      v.1 (algebraMap C F' (φ e)) = ‖e‖₊ := by
    intro e v
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F', ← comap_apply, v.2,
      gaussRat_algebraMap_C, NormedField.valuation_apply, ← NNReal.coe_inj]
    simp [hφ]
  have hout' : ∀ v : Ext C F', v.1 w ≤ 1 := fun v ↦
    hbound v.1 (hconst ϖ v) (fun e ↦ by
      rw [hconst e v]; simp [vE, NormedField.valuation_apply, ← NNReal.coe_inj, hφ])
      (hout v) (heo v z)
  have hin' : ∀ v : GaussExtension (0 : C) (invRad hc0' 1) F', v.1 w ≤ 1 := fun v ↦
    hbound v.1 (hconst' ϖ v) (fun e ↦ by
      rw [hconst' e v]; simp [vE, NormedField.valuation_apply, ← NNReal.coe_inj, hφ])
      (hin v) (hei v z)
  -- integrality
  obtain ⟨N, hN⟩ := exists_xF_pow_mul_isIntegral (isIntegral_map hφ hχ z)
  have hint : IsIntegral (Algebra.adjoin C {xF C F'}) (xF C F' ^ N * w) := by
    have : xF C F' ^ N * w = algebraMap C F' (φ ϖ)⁻¹ * (xF C F' ^ N * χ z) := by
      simp only [w]; ring
    rw [this]
    refine IsIntegral.mul ?_ hN
    exact isIntegral_algebraMap (x := (⟨_, Subalgebra.algebraMap_mem _ (φ ϖ)⁻¹⟩ :
      Algebra.adjoin C {xF C F'}))
  have hwR := isIntegral_of_le hp hp1 hc0' hint hout' hin'
  -- descend
  have hϖ0F : (cst ϖ : F₀) ≠ 0 := by
    intro h
    apply hϖF
    rw [← χ_cst hχ, h, map_zero]
  have hmem : (cst ϖ : F₀)⁻¹ * z ∈ BE F₀ c₀ := by
    refine mem_BE_of_χ hφ hχ hdeg hθ hc0 hc1 ?_
    rw [map_mul, map_inv₀, χ_cst hχ, ← map_inv₀]
    exact hwR
  refine ⟨⟨_, hmem⟩, ?_⟩
  change (z : F₀) = cst ϖ * ((cst ϖ : F₀)⁻¹ * z)
  rw [← mul_assoc, mul_inv_cancel₀ hϖ0F, one_mul]

end DVRDescent

end SemistableReduction
