/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteMain

/-!
# The three routed charts over `E` (G4, part 6)

Blueprint §9.7a, step 4 (G4 (ii)). Let `W'` be a valuation subring of `F'` over `O_C` and
`W = χ⁻¹ W'` its restriction to the `E`-form `F₀`. For each kind of routed standard chart `S`
over `E` (`Routed`), semistability of the normalization `normChart F₀ S` at the center of `W`
follows from the pointwise statements on the corresponding twist of `F'`:

* `vertexStep`: the vertex chart `O_E[(x - aE)/cE]` (twist `Aff a c F'`, `vertexCase`);
* `rootStep`: the chart `O_E[((x - aE)/cE)⁻¹]` at `∞` (twist `Inv 1 (Aff a c F')`, `closedCase`
  at `β = 0`);
* `edgeStep`: the edge chart `O_E[u, c'/u]` (twist `Aff a c F'`, `nodeCase`).

In each case the normalized chart is identified with the twisted chart (`chartEquiv`) and
semistability is transferred (`isSemistableAt_transfer`).
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section Twists

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {F : Type*} [Field F]
  [Algebra (RatFunc K) F]

lemma algebraMap_aff_X' {a c : K} (hc : c ≠ 0) :
    algebraMap (RatFunc K) (Aff a c hc F) RatFunc.X =
      toAff hc (algebraMap (RatFunc K) F (coord (RatFunc.X : RatFunc K) a c)) := by
  rw [algebraMap_aff_apply, aff_apply, affHom_X, gaussCoord_eq_coord hc]

lemma algebraMap_aff_C {a c : K} (hc : c ≠ 0) (k : K) :
    algebraMap (RatFunc K) (Aff a c hc F) (algebraMap K (RatFunc K) k) =
      toAff hc (algebraMap (RatFunc K) F (algebraMap K (RatFunc K) k)) := by
  rw [algebraMap_aff_apply, AlgEquiv.commutes]

lemma algebraMap_inv_aff_X {a c : K} (hc : c ≠ 0) :
    algebraMap (RatFunc K) (Inv (1 : K) one_ne_zero (Aff a c hc F)) RatFunc.X =
      toInv one_ne_zero (toAff hc
        (algebraMap (RatFunc K) F (coord (RatFunc.X : RatFunc K) a c)⁻¹)) := by
  rw [algebraMap_inv_apply, inv_apply, invHom_X, map_one, map_div₀, map_one,
    algebraMap_aff_X', map_inv₀, one_div]
  rfl

lemma algebraMap_inv_aff_C {a c : K} (hc : c ≠ 0) (k : K) :
    algebraMap (RatFunc K) (Inv (1 : K) one_ne_zero (Aff a c hc F))
        (algebraMap K (RatFunc K) k) =
      toInv one_ne_zero (toAff hc (algebraMap (RatFunc K) F (algebraMap K (RatFunc K) k))) := by
  rw [algebraMap_inv_apply, AlgEquiv.commutes, algebraMap_aff_C]

end Twists

section Steps

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

set_option hygiene false in
local notation "κ" k => algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) k)

lemma isOverOC_aff' {a c : C} (hc : c ≠ 0) {W' : ValuationSubring F'} (hO : IsOverOC C W') :
    @IsOverOC C inferInstance (Aff a c hc F') inferInstance inferInstance W' := by
  intro k
  change W'.valuation (ψ (aff a c hc (algebraMap C _ k))) ≤ 1 ↔ _
  rw [AlgEquiv.commutes]
  exact hO k

lemma isOverOC_inv_aff {a c : C} (hc : c ≠ 0) {W' : ValuationSubring F'} (hO : IsOverOC C W') :
    @IsOverOC C inferInstance (Inv (1 : C) one_ne_zero (Aff a c hc F')) inferInstance
      inferInstance W' := by
  intro k
  change W'.valuation (ψ (aff a c hc (inv one_ne_zero (algebraMap C _ k)))) ≤ 1 ↔ _
  rw [AlgEquiv.commutes, AlgEquiv.commutes]
  exact hO k

/-- The `O_E`-algebra structures of the twisted vertex chart and of a normalized chart agree
along `toAff`. -/
lemma toAff_algebraMap_bd {aE cE : E} (hcE : cE ≠ 0) (o : O_E) :
    toAff hcE (algebraMap E F₀ (o : E)) =
      (((letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff aE cE hcE F₀);
        algebraMap O_E (DVRDescent.BD E (Aff aE cE hcE F₀)) o) :
          DVRDescent.BD E (Aff aE cE hcE F₀)) : Aff aE cE hcE F₀) := by
  change _ = algebraMap (RatFunc E) (Aff aE cE hcE F₀) (algebraMap E (RatFunc E) (o : E))
  rw [algebraMap_aff_C, ← IsScalarTower.algebraMap_apply]

include hφ hχ in
/-- **Vertex charts**: semistability of `normChart F₀ O_E[(x - aE)/cE]` at the center of
`W = χ⁻¹ W'`, if `(x - a)/c ∈ W'`, the child directions `D` are `W'`-units and the descent holds
at the points of the twisted vertex charts off `D`. -/
theorem vertexStep [IsAlgClosed C] {aE cE : E} (hcE : cE ≠ 0) {a c : C} (hc : c ≠ 0)
    (ha : φ aE = a) (hcc : φ cE = c) (W' : ValuationSubring F') (hO : IsOverOC C W')
    (hX : ψ (coord (RatFunc.X : RatFunc C) a c) ∈ W') (D : Finset C)
    (hD : ∀ δ ∈ D, ‖δ‖ ≤ 1 ∧ W'.valuation (ψ (coord (RatFunc.X : RatFunc C) a c) - κ δ) = 1)
    (hsm : ∀ (β : C) (hβ : ‖β‖ ≤ 1), (∀ δ ∈ D, ‖β - δ‖ = 1) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff a c hc F'))), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1)
        (DRint (0 : C) 1 (Aff β 1 one_ne_zero (Aff a c hc F')))) = discIdeal (0 : C) 1 →
      letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff aE cE hcE F₀)
      IsSemistableAt ϖ (P'.comap (ιβ (χAff χ hcE hc) hφ (isCompat_χAff hcE hc hχ ha hcc) hβ)))
    [Algebra O_E (normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)))]
    (hBc : ∀ o, ((algebraMap O_E (normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)))
      o : normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE))) : F₀) =
        algebraMap E F₀ o)
    (hBW : normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)) ≤
      (W'.comap χ).toSubring) :
    IsSemistableAt ϖ (centerIdeal _ (W'.comap χ) hBW) := by
  letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff aE cE hcE F₀)
  obtain ⟨𝔮, h𝔮, hle⟩ := vertexCase (G := Aff a c hc F') hφ (isCompat_χAff hcE hc hχ ha hcc)
    (W' : ValuationSubring (Aff a c hc F')) (isOverOC_aff' hc hO)
    (by rw [algebraMap_aff_X']; exact hX) D
    (fun δ hδ ↦ ⟨(hD δ hδ).1, by
      rw [algebraMap_aff_X', algebraMap_aff_C, ← map_sub]; exact (hD δ hδ).2⟩) hsm
  refine isSemistableAt_transfer (chartEquiv (toAff hcE) _ (DRint (0 : E) 1 (Aff aE cE hcE F₀))
    (mem_normChart_poly_iff hcE)) (fun o ↦ Subtype.ext ?_) h𝔮 fun z hz ↦ hle _ ?_
  · rw [coe_chartEquiv, hBc]
    exact toAff_algebraMap_bd hcE o
  · rw [mem_centerIdeal_iff, comap_val_lt_one_iff] at hz
    exact hz

omit [IsUltrametricDist C] in
/-- The same for the inversion of the twist. -/
lemma toInv_algebraMap_bd {aE cE : E} (hcE : cE ≠ 0) (o : O_E) :
    toInv one_ne_zero (toAff hcE (algebraMap E F₀ (o : E))) =
      (((letI := DVRDescent.bdAlgebra (E := E) (F₀ := Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀));
        algebraMap O_E (DVRDescent.BD E (Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀))) o) :
          DVRDescent.BD E (Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀))) :
            Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀)) := by
  change _ = algebraMap (RatFunc E) (Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀))
    (algebraMap E (RatFunc E) (o : E))
  rw [algebraMap_inv_aff_C, ← IsScalarTower.algebraMap_apply]

include hφ hχ in
/-- **The chart at `∞` of the root**: semistability of `normChart F₀ O_E[((x - aE)/cE)⁻¹]` at
the center of `W = χ⁻¹ W'`, if `((x - a)/c)⁻¹ ∈ 𝔪_W'` and the descent holds at the points of
the vertex chart of `Inv 1 (Aff a c F')` over `x = 0`. -/
theorem rootStep {aE cE : E} (hcE : cE ≠ 0) {a c : C} (hc : c ≠ 0)
    (ha : φ aE = a) (hcc : φ cE = c) (W' : ValuationSubring F') (hO : IsOverOC C W')
    (hX : W'.valuation (ψ (coord (RatFunc.X : RatFunc C) a c)⁻¹) < 1)
    (hsm : ∀ P' : Ideal (DRint (0 : C) 1
        (Aff (0 : C) 1 one_ne_zero (Inv (1 : C) one_ne_zero (Aff a c hc F')))), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1
        (Aff (0 : C) 1 one_ne_zero (Inv (1 : C) one_ne_zero (Aff a c hc F'))))) =
          discIdeal (0 : C) 1 →
      letI := DVRDescent.bdAlgebra (E := E) (F₀ := Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀))
      IsSemistableAt ϖ (P'.comap (ιβ (χInvAff χ hcE hc) hφ (isCompat_χInvAff hcE hc hχ ha hcc)
        (by simp : ‖(0 : C)‖ ≤ 1))))
    [Algebra O_E (normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)⁻¹))]
    (hBc : ∀ o, ((algebraMap O_E
      (normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)⁻¹)) o :
        normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)⁻¹)) : F₀) =
          algebraMap E F₀ o)
    (hBW : normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)⁻¹) ≤
      (W'.comap χ).toSubring) :
    IsSemistableAt ϖ (centerIdeal _ (W'.comap χ) hBW) := by
  letI := DVRDescent.bdAlgebra (E := E) (F₀ := Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀))
  obtain ⟨𝔮, h𝔮, hle⟩ := closedCase (G := Inv (1 : C) one_ne_zero (Aff a c hc F')) hφ
    (isCompat_χInvAff hcE hc hχ ha hcc)
    (W' : ValuationSubring (Inv (1 : C) one_ne_zero (Aff a c hc F'))) (isOverOC_inv_aff hc hO)
    (β := 0) (by simp) (by rw [map_zero, map_zero, sub_zero, algebraMap_inv_aff_X]; exact hX) hsm
  have hmem : ∀ z, z ∈ normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)⁻¹) ↔
      ((toAff hcE).trans (toInv one_ne_zero)) z ∈
        DRint (0 : E) 1 (Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀)) := fun z ↦ by
    rw [RingEquiv.trans_apply]
    exact mem_normChart_inv_iff hcE z
  let e := chartEquiv ((toAff hcE).trans (toInv one_ne_zero)) _
    (DRint (0 : E) 1 (Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀))) hmem
  have he : ∀ o, e (algebraMap O_E _ o) = algebraMap O_E _ o := fun o ↦ by
    apply Subtype.ext
    rw [coe_chartEquiv, hBc, RingEquiv.trans_apply]
    exact toInv_algebraMap_bd hcE o
  have hχe : ∀ z, χInvAff (aE := aE) (a := a) χ hcE hc ((e z : DRint (0 : E) 1
      (Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀))) : Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀)) =
        toInv one_ne_zero (toAff hc (χ (z : F₀))) := fun z ↦ by
    rw [coe_chartEquiv, RingEquiv.trans_apply, χInvAff_toInv]
  refine isSemistableAt_transfer e he h𝔮 fun z hz ↦ hle _ ?_
  rw [mem_centerIdeal_iff, comap_val_lt_one_iff] at hz
  rw [hχe]
  exact hz

omit [IsScalarTower E (RatFunc E) F₀] in
include hφ hχ in
/-- **Edge charts**: semistability of `normChart F₀ O_E[u, c₀E/u]` (`u = (x - aE)/cE`) at the
center of `W = χ⁻¹ W'`, if `u, c₀/u ∈ 𝔪_W'` and the descent holds at the node points of
`Rint c₀ (Aff a c F')`, for every compatible `O_E`-algebra structure on the twisted chart. -/
theorem edgeStep {aE cE : E} (hcE : cE ≠ 0) {a c : C} (hc : c ≠ 0)
    (ha : φ aE = a) (hcc : φ cE = c) {c₀ : C} (hc₀ : ‖c₀‖ < 1) (hc₀0 : c₀ ≠ 0) {c₀E : E}
    (hc₀E : φ c₀E = c₀) (W' : ValuationSubring F') (hO : IsOverOC C W')
    (hX : W'.valuation (ψ (coord (RatFunc.X : RatFunc C) a c)) < 1)
    (hcX : W'.valuation ((κ c₀) / ψ (coord (RatFunc.X : RatFunc C) a c)) < 1)
    (hnode : ∀ [Algebra O_E (Rint c₀E (Aff aE cE hcE F₀))],
      (∀ o, ((algebraMap O_E (Rint c₀E (Aff aE cE hcE F₀)) o : Rint c₀E (Aff aE cE hcE F₀)) :
        Aff aE cE hcE F₀) = toAff hcE (algebraMap E F₀ o)) →
      ∀ P' : Ideal (Rint c₀ (Aff a c hc F')), P'.IsMaximal →
        P'.comap (algebraMap (nodeRing c₀) (Rint c₀ (Aff a c hc F'))) = tubeIdeal c₀ →
        IsSemistableAt ϖ (P'.comap (ιN (χAff χ hcE hc) hφ (isCompat_χAff hcE hc hχ ha hcc) hc₀E)))
    [Algebra O_E (normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E))]
    (hBc : ∀ o, ((algebraMap O_E
      (normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E)) o :
        normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E)) : F₀) =
          algebraMap E F₀ o)
    (hBW : normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E) ≤
      (W'.comap χ).toSubring) :
    IsSemistableAt ϖ (centerIdeal _ (W'.comap χ) hBW) := by
  let e := chartEquiv (toAff hcE) _ (Rint c₀E (Aff aE cE hcE F₀)) (mem_normChart_node_iff hcE c₀E)
  letI : Algebra O_E (Rint c₀E (Aff aE cE hcE F₀)) :=
    (e.toRingHom.comp (algebraMap O_E
      (normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E)))).toAlgebra
  have hRc : ∀ o, ((algebraMap O_E (Rint c₀E (Aff aE cE hcE F₀)) o :
      Rint c₀E (Aff aE cE hcE F₀)) : Aff aE cE hcE F₀) = toAff hcE (algebraMap E F₀ o) := by
    intro o
    change toAff hcE ((algebraMap O_E
      (normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E)) o :
        normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E)) : F₀) = _
    rw [hBc]
  obtain ⟨𝔮, h𝔮, hle⟩ := nodeCase (G := Aff a c hc F') hφ (isCompat_χAff hcE hc hχ ha hcc)
    hc₀ hc₀0 hc₀E (W' : ValuationSubring (Aff a c hc F')) (isOverOC_aff' hc hO)
    (by rw [algebraMap_aff_X']; exact hX)
    (by rw [map_div₀, algebraMap_aff_C, algebraMap_aff_X', ← map_div₀]; exact hcX) (hnode hRc)
  have he : ∀ o, e (algebraMap O_E
      (normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c₀E)) o) =
        algebraMap O_E (Rint c₀E (Aff aE cE hcE F₀)) o := fun _ ↦ rfl
  refine isSemistableAt_transfer e he h𝔮 fun z hz ↦ hle _ ?_
  rw [mem_centerIdeal_iff, comap_val_lt_one_iff] at hz
  exact hz

end Steps

end W10Route

end SemistableReduction
