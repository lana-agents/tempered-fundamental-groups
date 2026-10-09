/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteSteps

/-!
# Routed charts over `E` (G4, part 7)

Blueprint §9.7a, step 4 (G4 (ii)). `routedStep`: for a valuation subring `W'` of `F'` over `O_C`
and `W = χ⁻¹ W'`, the normalization in `F₀` of a routed standard chart `S` of the `E`-tree
(`Routed`, at the restriction of `W` to `E(x)`) is semistable at the center of `W`, given the
pointwise descent on the twists of `F'` (hypotheses `hvert`, `hroot`, `hedge`, stated over `E`).
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section Val

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

lemma val_le_one_iff_norm (x : E) : νE x ≤ 1 ↔ ‖x‖ ≤ 1 := by
  rw [NormedField.valuation_apply, ← NNReal.coe_le_coe]
  simp

lemma val_lt_val_iff_norm (x y : E) : νE x < νE y ↔ ‖x‖ < ‖y‖ := by
  rw [NormedField.valuation_apply, NormedField.valuation_apply, ← NNReal.coe_lt_coe]
  simp

end Val

section Routed

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F' : Type u} [Field F'] [Algebra (RatFunc C) F']
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F₀ : Type u} [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀] [IsScalarTower E (RatFunc E) F₀]
  {χ : F₀ →+* F'} (hχ : DVRDescent.IsCompat φ χ)
  {ϖ : (NormedField.valuation (K := E)).valuationSubring}

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

set_option hygiene false in
local notation "O_E" => (NormedField.valuation (K := E)).valuationSubring

set_option hygiene false in
local notation "ψ" => algebraMap (RatFunc C) F'

omit [IsUltrametricDist C] [IsUltrametricDist E] in
lemma ratFuncMap_coord (aE cE : E) :
    ratFuncMap φ (coord (RatFunc.X : RatFunc E) aE cE) =
      coord (RatFunc.X : RatFunc C) (φ aE) (φ cE) := by
  simp only [coord, map_div₀, map_sub, DVRDescent.ratFuncMap_X, ratFuncMap_algebraMap_C]

omit [IsUltrametricDist C] [IsUltrametricDist E] [Algebra E F₀]
  [IsScalarTower E (RatFunc E) F₀] in
include hχ in
lemma val_comap_lt_one_iff (W' : ValuationSubring F') (f : RatFunc E) :
    ((W'.comap χ).comap (algebraMap (RatFunc E) F₀)).valuation f < 1 ↔
      W'.valuation (ψ (ratFuncMap φ f)) < 1 := by
  rw [comap_val_lt_one_iff, comap_val_lt_one_iff, hχ]

omit [IsUltrametricDist C] [IsUltrametricDist E] [Algebra E F₀]
  [IsScalarTower E (RatFunc E) F₀] in
include hχ in
lemma val_comap_eq_one_iff (W' : ValuationSubring F') (f : RatFunc E) :
    ((W'.comap χ).comap (algebraMap (RatFunc E) F₀)).valuation f = 1 ↔
      W'.valuation (ψ (ratFuncMap φ f)) = 1 := by
  rw [comap_val_eq_one_iff, comap_val_eq_one_iff, hχ]

omit [IsUltrametricDist C] [IsUltrametricDist E] [Algebra E F₀]
  [IsScalarTower E (RatFunc E) F₀] in
include hχ in
lemma mem_comap_iff' (W' : ValuationSubring F') (f : RatFunc E) :
    f ∈ (W'.comap χ).comap (algebraMap (RatFunc E) F₀) ↔ ψ (ratFuncMap φ f) ∈ W' := by
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, hχ]

variable {ι : Type*} {aE cE : ι → E}

lemma norm_div_lt_one_of_edge (hcE : ∀ i, cE i ≠ 0) (hred : IsReduced νE aE cE) {j m : ι}
    (hjm : DiscLE νE aE cE j m) (hjne : j ≠ m) : ‖cE j / cE m‖ < 1 := by
  have hlt : νE (cE j) < νE (cE m) := lt_of_le_of_ne hjm.1 fun he ↦
    hjne (hred j m hjm (discLE_symm_of_eq hjm he))
  rw [val_lt_val_iff_norm] at hlt
  rw [norm_div, div_lt_one (norm_pos_iff.2 (hcE m))]
  exact hlt

include hφ hχ in
/-- **Routed charts over `E`.** -/
theorem routedStep [Finite ι] [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
    (hcE : ∀ i, cE i ≠ 0) (hc : ∀ i, φ (cE i) ≠ 0) (hred : IsReduced νE aE cE)
    (hvert : ∀ m (β : C) (hβ : ‖β‖ ≤ 1),
      (∀ j, DiscLE νE aE cE j m → j ≠ m → ‖β - φ ((aE j - aE m) / cE m)‖ = 1) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F'))),
        P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1)
          (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F')))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff (aE m) (cE m) (hcE m) F₀)
        IsSemistableAt ϖ (P'.comap (ιβ (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) hβ)))
    (hroot : ∀ ρ, (∀ i, DiscLE νE aE cE i ρ) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F')))), P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F'))))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E)
          (F₀ := Inv (1 : E) one_ne_zero (Aff (aE ρ) (cE ρ) (hcE ρ) F₀))
        IsSemistableAt ϖ (P'.comap (ιβ (χInvAff χ (hcE ρ) (hc ρ)) hφ
          (isCompat_χInvAff (hcE ρ) (hc ρ) hχ rfl rfl) (by simp : ‖(0 : C)‖ ≤ 1))))
    (hedge : ∀ j m, DiscLE νE aE cE j m → j ≠ m →
      (∀ k, DiscLE νE aE cE j k → DiscLE νE aE cE k m → k = j ∨ k = m) →
      ∀ [Algebra O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀))],
      (∀ o, ((algebraMap O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) o :
        Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) : Aff (aE j) (cE m) (hcE m) F₀) =
          toAff (hcE m) (algebraMap E F₀ o)) →
      ∀ P' : Ideal (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F')),
        P'.IsMaximal →
        P'.comap (algebraMap (nodeRing (φ (cE j) / φ (cE m)))
          (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F'))) =
            tubeIdeal (φ (cE j) / φ (cE m)) →
        IsSemistableAt ϖ (P'.comap (ιN (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) (map_div₀ φ (cE j) (cE m)))))
    (W' : ValuationSubring F') (hO : IsOverOC C W') {S : Subring (RatFunc E)}
    (hS : Routed νE aE cE (RatFunc.X : RatFunc E)
      ((W'.comap χ).comap (algebraMap (RatFunc E) F₀)) S)
    [Algebra O_E (normChart F₀ S)]
    (hBc : ∀ o, ((algebraMap O_E (normChart F₀ S) o : normChart F₀ S) : F₀) = algebraMap E F₀ o)
    (hSW : normChart F₀ S ≤ (W'.comap χ).toSubring) :
    IsSemistableAt ϖ (centerIdeal _ (W'.comap χ) hSW) := by
  classical
  haveI := Fintype.ofFinite ι
  rcases hS with ⟨m, rfl, hm, hunit⟩ | ⟨j, m, hjm, hjne, hedg, rfl, hu, hcu⟩ | ⟨ρ, hρ, rfl, hρu⟩
  · -- a vertex chart
    set D : Finset C := (Finset.univ.filter fun j ↦ DiscLE νE aE cE j m ∧ j ≠ m).image
      fun j ↦ φ ((aE j - aE m) / cE m) with hDdef
    have hX : ψ (coord (RatFunc.X : RatFunc C) (φ (aE m)) (φ (cE m))) ∈ W' := by
      rw [← ratFuncMap_coord, ← mem_comap_iff' hχ]
      exact hm
    have hD : ∀ δ ∈ D, ‖δ‖ ≤ 1 ∧ W'.valuation (ψ (coord (RatFunc.X : RatFunc C) (φ (aE m))
        (φ (cE m))) - ψ (algebraMap C (RatFunc C) δ)) = 1 := by
      intro δ hδ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hδ
      obtain ⟨hjm, hjne⟩ := (Finset.mem_filter.1 hj).2
      refine ⟨?_, ?_⟩
      · rw [hφ, ← val_le_one_iff_norm]
        exact (hjm.div_le_one hcE).2
      · rw [← ratFuncMap_coord, ← ratFuncMap_algebraMap_C, ← map_sub, ← map_sub,
          ← val_comap_eq_one_iff hχ]
        exact hunit j hjm hjne
    refine vertexStep hφ hχ (hcE m) (hc m) rfl rfl W' hO hX D hD
      (fun β hβ hfar ↦ hvert m β hβ fun j hjm hjne ↦ hfar _ (Finset.mem_image_of_mem _
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hjm, hjne⟩))) hBc hSW
  · -- an edge chart
    have hX : W'.valuation (ψ (coord (RatFunc.X : RatFunc C) (φ (aE j)) (φ (cE m)))) < 1 := by
      rw [← ratFuncMap_coord, ← val_comap_lt_one_iff hχ]
      exact hu
    have hcX : W'.valuation (ψ (algebraMap C (RatFunc C) (φ (cE j) / φ (cE m))) /
        ψ (coord (RatFunc.X : RatFunc C) (φ (aE j)) (φ (cE m)))) < 1 := by
      rw [← map_div₀ φ, ← ratFuncMap_algebraMap_C, ← ratFuncMap_coord, ← map_div₀, ← map_div₀,
        ← val_comap_lt_one_iff hχ]
      exact hcu
    have hc₀ : ‖φ (cE j) / φ (cE m)‖ < 1 := by
      rw [← map_div₀, hφ]
      exact norm_div_lt_one_of_edge hcE hred hjm hjne
    exact edgeStep hφ hχ (hcE m) (hc m) rfl rfl hc₀ (div_ne_zero (hc j) (hc m))
      (map_div₀ φ (cE j) (cE m)) W' hO hX hcX (hedge j m hjm hjne hedg) hBc hSW
  · -- the chart at `∞` of the root
    have hX : W'.valuation (ψ (coord (RatFunc.X : RatFunc C) (φ (aE ρ)) (φ (cE ρ)))⁻¹) < 1 := by
      rw [← ratFuncMap_coord, ← map_inv₀, ← val_comap_lt_one_iff hχ]
      exact hρu
    exact rootStep hφ hχ (hcE ρ) (hc ρ) rfl rfl W' hO hX (hroot ρ hρ) hBc hSW

omit [IsUltrametricDist C] [IsUltrametricDist E] in
include hχ in
lemma χ_algebraMap_E [Algebra C F'] [IsScalarTower C (RatFunc C) F'] (e : E) :
    χ (algebraMap E F₀ e) = algebraMap C F' (φ e) := by
  rw [IsScalarTower.algebraMap_apply E (RatFunc E) F₀, hχ, ratFuncMap_algebraMap_C,
    ← IsScalarTower.algebraMap_apply]

/-- Generization: if `W₂ ⊆ W` then `𝔪_W ∩ W₂ ⊆ 𝔪_{W₂}`. -/
lemma val_lt_one_of_le {K : Type*} [Field K] {W₂ W : ValuationSubring K} (h : W₂ ≤ W) {z : K}
    (hz₂ : z ∈ W₂) (hz : W.valuation z < 1) : W₂.valuation z < 1 := by
  refine lt_of_le_of_ne ((W₂.valuation_le_one_iff _).2 hz₂) fun h1 ↦ ?_
  obtain ⟨hz0, -, hinv⟩ := (valuation_eq_one_iff_mem_and_inv_mem W₂).1 h1
  have : W.valuation z = 1 :=
    (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨hz0, h hz₂, h hinv⟩
  rw [this] at hz
  exact lt_irrefl _ hz

include hφ hχ in
/-- **The charts of the normalized `E`-tree model are semistable**, given the pointwise descent
on the twists of `F'` (special fibre: `routedStep` after lifting `W` to `F'`; generic fibre:
refinement `exists_le_special` and generization). -/
theorem chartsSemistable [Fintype ι] [Nonempty ι] [IsAlgClosed C] [Algebra C F']
    [IsScalarTower C (RatFunc C) F'] [CompleteSpace E]
    (halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
    [IsDiscreteValuationRing O_E] (hϖ : Irreducible ϖ)
    [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀]
    [Algebra O_E F₀] [IsScalarTower O_E E F₀]
    (hcE : ∀ i, cE i ≠ 0) (hc : ∀ i, φ (cE i) ≠ 0) (hconv : IsConvex νE aE cE)
    (hred : IsReduced νE aE cE)
    (hvert : ∀ m (β : C) (hβ : ‖β‖ ≤ 1),
      (∀ j, DiscLE νE aE cE j m → j ≠ m → ‖β - φ ((aE j - aE m) / cE m)‖ = 1) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F'))),
        P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1)
          (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff (φ (aE m)) (φ (cE m)) (hc m) F')))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff (aE m) (cE m) (hcE m) F₀)
        IsSemistableAt ϖ (P'.comap (ιβ (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) hβ)))
    (hroot : ∀ ρ, (∀ i, DiscLE νE aE cE i ρ) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F')))), P'.IsMaximal →
        P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff (0 : C) 1 one_ne_zero
          (Inv (1 : C) one_ne_zero (Aff (φ (aE ρ)) (φ (cE ρ)) (hc ρ) F'))))) =
            discIdeal (0 : C) 1 →
        letI := DVRDescent.bdAlgebra (E := E)
          (F₀ := Inv (1 : E) one_ne_zero (Aff (aE ρ) (cE ρ) (hcE ρ) F₀))
        IsSemistableAt ϖ (P'.comap (ιβ (χInvAff χ (hcE ρ) (hc ρ)) hφ
          (isCompat_χInvAff (hcE ρ) (hc ρ) hχ rfl rfl) (by simp : ‖(0 : C)‖ ≤ 1))))
    (hedge : ∀ j m, DiscLE νE aE cE j m → j ≠ m →
      (∀ k, DiscLE νE aE cE j k → DiscLE νE aE cE k m → k = j ∨ k = m) →
      ∀ [Algebra O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀))],
      (∀ o, ((algebraMap O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) o :
        Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) : Aff (aE j) (cE m) (hcE m) F₀) =
          toAff (hcE m) (algebraMap E F₀ o)) →
      ∀ P' : Ideal (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F')),
        P'.IsMaximal →
        P'.comap (algebraMap (nodeRing (φ (cE j) / φ (cE m)))
          (Rint (φ (cE j) / φ (cE m)) (Aff (φ (aE j)) (φ (cE m)) (hc m) F'))) =
            tubeIdeal (φ (cE j) / φ (cE m)) →
        IsSemistableAt ϖ (P'.comap (ιN (χAff χ (hcE m) (hc m)) hφ
          (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) (map_div₀ φ (cE j) (cE m)))))
    {Cc : Subring F₀} (hCc : Cc ∈ ((gaussJoinModel νE aE cE).normalization F₀).charts)
    [Algebra O_E Cc] (hCcc : ∀ o, ((algebraMap O_E Cc o : Cc) : F₀) = algebraMap O_E F₀ o) :
    IsSemistable ϖ Cc := by
  classical
  have hfin := gaussJoinModel_normalization_isFiniteType (F' := F₀) hcE hconv hred
    (eq_or_eq_top_of_le hϖ)
  have hproper := normalization_isProper (F' := F₀)
    (gaussJoinModel_isProper (v := νE) (a := aE) (c := cE))
  have hsep := normalization_isSeparated (F' := F₀)
    (gaussJoinModel_isSeparated (v := νE) (a := aE) (c := cE))
  -- the special fibre
  have hspecial : ∀ W : ValuationSubring F₀, W.comap (algebraMap E F₀) = O_E →
      ∀ B ∈ ((gaussJoinModel νE aE cE).normalization F₀).charts, ∀ [Algebra O_E B],
      (∀ o, ((algebraMap O_E B o : B) : F₀) = algebraMap O_E F₀ o) →
      ∀ hBW : B ≤ W.toSubring, IsSemistableAt ϖ (centerIdeal B W hBW) := by
    intro W hW B hB _ hBc hBW
    obtain ⟨W', rfl, hW'O⟩ := exists_lift hφ (χ_algebraMap_E hχ) halg W hW
    have hO : IsOverOC C W' := isOverOC_of_comap W' hW'O
    obtain ⟨S, hS, hSW, hloc⟩ := exists_routed_normChart hcE hconv hred hB hBW hW
    have hRS : baseRing F₀ O_E ≤ normChart F₀ S := by
      rw [← map_baseRing (F := RatFunc E)]
      exact (subring_map_mono (IsStandardChart.baseRing_le (Routed.isStandardChart hS)) _).trans
        (map_le_normChart S)
    letI : Algebra O_E (normChart F₀ S) := chartAlgebra hRS
    have hBcS : ∀ o, ((algebraMap O_E (normChart F₀ S) o : normChart F₀ S) : F₀) =
        algebraMap O_E F₀ o := fun _ ↦ rfl
    have h1 := routedStep hφ hχ hcE hc hred hvert hroot hedge W' hO hS
      (fun o ↦ (hBcS o).trans (IsScalarTower.algebraMap_apply O_E E F₀ o)) hSW
    obtain ⟨sS, hsS⟩ := normChart_closure_of_isStandardChart (F' := F₀) hcE
      (Routed.isStandardChart hS)
    obtain ⟨sB, hsB⟩ := hfin B hB
    exact isSemistableAt_of_localAt_eq hBcS hBc hRS
      (((gaussJoinModel νE aE cE).normalization F₀).le_chart B hB) sS sB hsS hsB hSW hBW hloc h1
  intro 𝔭 _
  obtain ⟨W, hCW, rfl⟩ := exists_centerIdeal_eq Cc 𝔭
  have hRC := ((gaussJoinModel νE aE cE).normalization F₀).le_chart Cc hCc
  have hOW : O_E ≤ W.comap (algebraMap E F₀) := baseRing_le_iff.1 (hRC.trans hCW)
  rcases eq_or_eq_top_of_le hϖ _ hOW with hW | hW
  · exact hspecial W hW Cc hCc hCcc hCW
  -- the generic fibre
  have hWE : ∀ e : E, algebraMap E F₀ e ∈ W := fun e ↦ by
    have : e ∈ W.comap (algebraMap E F₀) := by rw [hW]; trivial
    exact this
  obtain ⟨W₂, hW₂W, hW₂⟩ := exists_le_special W hWE hϖ
  obtain ⟨B, hB, hBW₂⟩ := hproper W₂ (baseRing_le_iff.2 hW₂.ge)
  have hRB := ((gaussJoinModel νE aE cE).normalization F₀).le_chart B hB
  letI : Algebra O_E B := chartAlgebra hRB
  have hBc : ∀ o, ((algebraMap O_E B o : B) : F₀) = algebraMap O_E F₀ o := fun _ ↦ rfl
  have hBW : B ≤ W.toSubring := fun x hx ↦ hW₂W (hBW₂ hx)
  have h3 : IsSemistableAt ϖ (centerIdeal B W hBW) :=
    (hspecial W₂ hW₂ B hB hBc hBW₂).of_le fun z hz ↦ by
      rw [mem_centerIdeal_iff] at hz ⊢
      exact val_lt_one_of_le hW₂W (hBW₂ z.2) hz
  obtain ⟨sB, hsB⟩ := hfin B hB
  obtain ⟨sC, hsC⟩ := hfin Cc hCc
  exact isSemistableAt_of_localAt_eq hBc hCcc hRB hRC sB sC hsB hsC hBW hCW
    (hsep.localAt_eq hCc hB hCW hBW) h3

end Routed

end W10Route

end SemistableReduction
