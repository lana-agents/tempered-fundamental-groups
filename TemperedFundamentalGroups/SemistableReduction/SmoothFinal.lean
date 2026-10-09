/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothResidue
import TemperedFundamentalGroups.SemistableReduction.SmoothHyps

/-!
# Descent of smooth points: the general case (W10, smooth part (4))

Blueprint §9.12 (O7). For `κ_E` perfect and `C` algebraic over `E`:

* `isSemistableAt_of_isDiscSmooth_residue`: a smooth point of the twisted vertex chart
  `DRint 0 1 (Aff β 1 G)` over `(𝔪_C, x - β)` (any `β ∈ O_C`) restricts to a semistable point of
  the vertex chart over `O_E` (hypotheses `hinj`, `hgen`, `hspan`, `hθ`, `hdeg` for `E`). Proof:
  an unramified `E' ⊇ E` contains a lift `β'` of `β̄` and makes the point rational
  (`Unramified.exists_unrData`); the point is transported to the chart in `x - β'`
  (`S8A.Transport.repData`); `isSemistableAt_of_isDiscSmooth_aff` over `E'`; descent along the
  étale map `BD E F₀ → BD E' F₀'` (`UnrChart.etale_j`, `IsSemistableAt.comap_of_baseChange`).
* **`W10Route.smoothDescentStatement`**: `W10Route.SmoothDescentStatement` holds (with the set `S`
  of `SmoothHyps.exists_finset_smoothHyps`).
-/

open Polynomial IsLocalRing

set_option linter.unusedSectionVars false

namespace SemistableReduction

namespace DVRDescent

open GaussTube DiscCount SmoothVertex FundamentalInequality GaussStability GaussFibre PlaceNorm
  ConstantDescent AffineTwist Unramified

universe u

/-- `IsSpanned` is monotone in the subring. -/
lemma isSpanned_mono {k R κ₁ κ₂ : Type*} [Field k] [CommRing R] [Field κ₁] [Field κ₂]
    [Algebra k κ₁] [Algebra k κ₂] {B B' : Subring R} (hBB' : B ≤ B') {ρ₁ : R →+* κ₁}
    {ρ₂ : R →+* κ₂} {y : R} (h : IsSpanned k B ρ₁ ρ₂ y) : IsSpanned k B' ρ₁ ρ₂ y := by
  obtain ⟨n, lam, b, hb, h₁, h₂⟩ := h
  exact ⟨n, lam, b, fun j ↦ hBB' (hb j), h₁, h₂⟩

/-! ### Changing the representative of a residue point -/

section TransportAff

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-- The identity maps `F' → Aff a c F'` all have the same underlying function. -/
lemma toAff_eq_toAff {a a' c c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0) (z : G) :
    ((toAff (a := a) hc z : Aff a c hc G) : G) = ((toAff (a := a') hc' z : Aff a' c' hc' G) : G) :=
  rfl

/-- **A point over `x̄ = β̄` in the chart in `x - β` is a point in the chart in `x - β'`**
(`‖β' - β‖ < 1`): maximality, the residue point and smoothness are preserved, and the two ideals
have the same elements of `G`. -/
theorem exists_transport_aff {β β' : C} (hββ' : ‖β' - β‖ < 1)
    (P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1)
      (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) = discIdeal (0 : C) 1)
    (hsm : IsDiscSmooth P') :
    ∃ P'' : Ideal (DRint (0 : C) 1 (Aff β' 1 one_ne_zero G)), P''.IsMaximal ∧
      P''.comap (algebraMap (discRing (0 : C) 1)
        (DRint (0 : C) 1 (Aff β' 1 one_ne_zero G))) = discIdeal (0 : C) 1 ∧
      IsDiscSmooth P'' ∧
      ∀ (y : DRint (0 : C) 1 (Aff β' 1 one_ne_zero G))
        (y' : DRint (0 : C) 1 (Aff β 1 one_ne_zero G)),
        ((y : Aff β' 1 one_ne_zero G) : G) = ((y' : Aff β 1 one_ne_zero G) : G) →
          (y ∈ P'' ↔ y' ∈ P') := by
  let d := S8A.Transport.repData (F := G) (a := β') (a' := β) (c := 1) (c' := 1) one_ne_zero
    one_ne_zero rfl (by simpa using hββ')
  have hD := d.ψ_mem_discRing_iff
  refine ⟨P'.comap (d.symm.icMap (d.symm_hA hD)), ?_, ?_, d.isDiscSmooth_comap hD hsm, ?_⟩
  · exact Ideal.comap_isMaximal_of_surjective _
      (fun y ↦ ⟨d.icMap hD y, d.icMap_symm_icMap hD y⟩)
  · ext φ
    rw [Ideal.mem_comap, Ideal.mem_comap, ← d.symm.chartHom_mem_discIdeal_iff, ← hP',
      Ideal.mem_comap]
    have : d.symm.icMap (d.symm_hA hD)
        (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β' 1 one_ne_zero G)) φ) =
        algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))
          (d.symm.chartHom d.symm.ψ_mem_discRing_iff φ) :=
      Subtype.ext (d.symm.he φ)
    rw [this]
  · intro y y' h
    rw [Ideal.mem_comap]
    have he : ∀ z : Aff β' 1 one_ne_zero G,
        ((d.symm.e z : Aff β 1 one_ne_zero G) : G) = (z : G) := fun z ↦ rfl
    have : d.symm.icMap (d.symm_hA hD) y = y' := by
      apply Subtype.ext
      rw [S8A.Transport.Data.coe_icMap]
      exact (he _).trans h
    rw [this]

end TransportAff

section Residue

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {G : Type u} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
  {F₀ : Type u} [Field F₀] [Algebra (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀] {χ : F₀ →+* G} (hχ : IsCompat φ χ)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "O_E" => HenselComplete.integers E
local notation "O_C" => HenselComplete.integers C

include hφ in
/-- The residue field of `C` is algebraic over that of `E` when `C` is algebraic over `E`. -/
lemma isAlgebraic_residue (halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E C) (z : 𝓀) :
    letI := (DVRDescent.ψ hφ).toAlgebra
    IsAlgebraic (ResidueField O_E) z := by
  letI := φ.toAlgebra
  have hV : (O_C).comap (algebraMap E C) = O_E := by
    ext e
    rw [ValuationSubring.mem_comap, HenselComplete.mem_integers_iff,
      HenselComplete.mem_integers_iff]
    change ‖φ e‖ ≤ 1 ↔ _
    rw [hφ]
  have h := isAlgebraic_residueField (K := E) (Ω := C) hV
  have heq : residueAlgebra hV = (DVRDescent.ψ hφ).toAlgebra := by
    refine Algebra.algebra_ext _ _ fun a ↦ ?_
    obtain ⟨a, rfl⟩ := residue_surjective a
    rfl
  rw [heq] at h
  exact h.isAlgebraic z

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) G] in
lemma placeHomD_constD' {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
    [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] [IsAlgClosed C]
    (v : Ext C F') {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (b : O_C) :
    placeHomD v hQ (constD b) = residue O_C b := by
  change Q.res (redD v (constD b)) = _
  rw [redD_constD, Q.res_algebraMap]

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) G]
  [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀] in
lemma ιβ_cstD {β : C} (hβ : ‖β‖ ≤ 1) (e : O_E) :
    W10Route.ιβ χ hφ hχ hβ (cstD e) = constD ⟨φ e, norm_map_le_one hφ e⟩ := by
  apply Subtype.ext
  change toAff one_ne_zero (χ (cst (e : E))) =
    algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) (algebraMap C (RatFunc C) (φ e))
  rw [χ_cst hχ, algebraMap_aff_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]

omit [IsAlgClosed C] [CharZero C] [FiniteDimensional (RatFunc C) G]
  [FiniteDimensional (RatFunc E) F₀] [Algebra.IsSeparable (RatFunc E) F₀] in
lemma ιβ_xD {β : C} (hβ : ‖β‖ ≤ 1) :
    W10Route.ιβ χ hφ hχ hβ xD = xD + constD ⟨β, (HenselComplete.mem_integers_iff _).2 hβ⟩ := by
  apply Subtype.ext
  change toAff one_ne_zero (χ (algebraMap (RatFunc E) F₀ RatFunc.X)) =
    algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X +
      algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) (algebraMap C (RatFunc C) β)
  rw [hχ, ratFuncMap_X, ← map_add, algebraMap_aff_apply, map_add, AlgEquiv.commutes, aff_apply,
    affHom_X, gaussCoord_eq, inv_one, map_one, one_mul, sub_add_cancel]

set_option maxHeartbeats 1000000 in
-- the assembly juggles the charts over `E`, `E'` and two twists of `G`
include hp hp1 hφ hχ in
/-- **(S) at an arbitrary residue point** (`κ_E` perfect, `C` algebraic over `E`). -/
theorem isEtaleLocallyAt_of_isDiscSmooth_residue [IsDiscreteValuationRing O_E]
    [PerfectField (ResidueField O_E)] (halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (hinj : ∀ W W' : Ext C G, W.1.comap χ = W'.1.comap χ → W = W')
    (hgen : ∀ W : Ext C G, IntermediateField.adjoin 𝓀
      (resE χ W : Set (ResidueField W.1.valuationSubring)) = ⊤)
    (hspan : ∀ v₁ v₂ : Ext C G, ∀ y,
      IsSpanned 𝓀 (ιD χ hφ hχ (F₀ := F₀)).range (redD v₁) (redD v₂) y)
    {ϖ : O_E} (hϖ : Irreducible ϖ) {β : C} (hβ : ‖β‖ ≤ 1)
    (P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1)
      (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) = discIdeal (0 : C) 1)
    (hsm : IsDiscSmooth P') :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    IsEtaleLocallyAt O_E O_E[X] (P'.comap (W10Route.ιβ χ hφ hχ hβ)) := by
  classical
  letI := bdAlgebra (E := E) (F₀ := F₀)
  haveI := finiteType_BD (E := E) (F₀ := F₀)
  -- the branch at `P'` and the value map
  obtain ⟨⟨v, Q, hQ⟩, hb, hloc⟩ := hsm
  have hPQ : placeIdealD v hQ = P' := by
    have : (⟨v, Q, hQ⟩ : OuterBranch C (Aff β 1 one_ne_zero G)) ∈ discBranches P' := by
      rw [hb]; exact Set.mem_singleton _
    exact this
  have hmemP : ∀ y, y ∈ P' ↔ placeHomD v hQ y = 0 := fun y ↦ by
    rw [← hPQ]; rfl
  set val : BD E F₀ →+* 𝓀 := (placeHomD v hQ).comp (W10Route.ιβ χ hφ hχ hβ) with hval
  have hval_cst : ∀ e : O_E, val (cstD e) = residue O_C ⟨φ e, norm_map_le_one hφ e⟩ := by
    intro e
    rw [hval, RingHom.comp_apply, ιβ_cstD hφ hχ hβ e, placeHomD_constD']
  have hval_x : val xD = residue O_C ⟨β, (HenselComplete.mem_integers_iff _).2 hβ⟩ := by
    have hxP := xD_mem (F' := Aff β 1 one_ne_zero G) hP'
    rw [hval, RingHom.comp_apply, ιβ_xD hφ hχ hβ, map_add, (hmemP _).1 hxP, zero_add,
      placeHomD_constD']
  -- generators of `BD` and an unramified extension making the values rational
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := O_E) (A := BD E F₀)
  obtain ⟨D, hD⟩ :=
    Unramified.exists_unrData hφ (s.image val) fun z _ ↦ isAlgebraic_residue hφ halg z
  obtain ⟨rE, hrE⟩ : ∃ rE : HenselComplete.integers D.F →+* 𝓀,
      rE = (residue O_C).comp (DVRDescent.intMap (φ := D.φ') D.norm_φ') := ⟨_, rfl⟩
  have hrE_alg : ∀ e : O_E, rE (algebraMap O_E (HenselComplete.integers D.F) e) =
      residue O_C ⟨φ e, norm_map_le_one hφ e⟩ := by
    intro e
    rw [hrE, RingHom.comp_apply]
    congr 1
    apply Subtype.ext
    change D.φ' (algebraMap E D.F e) = φ e
    exact D.φ'_algebraMap e
  have hvalr : ∀ z : BD E F₀, val z ∈ rE.range := by
    intro z
    have hz : z ∈ Algebra.adjoin O_E (s : Set (BD E F₀)) := hs ▸ Algebra.mem_top
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨e', he'⟩ := hD (val z) (Finset.mem_image_of_mem _ hz)
      exact ⟨e', by rw [hrE]; exact he'⟩
    | algebraMap e =>
      refine ⟨algebraMap O_E (HenselComplete.integers D.F) e, ?_⟩
      rw [hrE_alg]
      exact (hval_cst e).symm
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  obtain ⟨βE, hβE⟩ := hvalr xD
  rw [hval_x, hrE] at hβE
  have hβ' : ‖D.φ' βE - β‖ < 1 := by
    have h0 : residue O_C (DVRDescent.intMap (φ := D.φ') D.norm_φ' βE -
        ⟨β, (HenselComplete.mem_integers_iff _).2 hβ⟩) = 0 := by
      rw [map_sub]; exact sub_eq_zero.2 hβE
    rw [residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one] at h0
    exact h0
  -- the extension `E'` and the `E'`-form `F₀' = F₀[β]`
  haveI := D.isDiscreteValuationRing
  haveI : Fact (Irreducible (Unramified.UnrChart.g₁ D χ)) :=
    ⟨Unramified.UnrChart.irreducible_g₁ D hχ⟩
  letI := Unramified.UnrChart.algRat D hχ
  obtain ⟨hfin', hdeg'⟩ := Unramified.UnrChart.finiteDimensional_and_finrank D hχ hdeg hθ
  haveI := hfin'
  haveI : CharZero D.F :=
    ⟨fun m n h ↦ Nat.cast_injective (R := C) (by simpa using congrArg D.φ' h)⟩
  haveI : CharZero (RatFunc D.F) :=
    charZero_of_injective_algebraMap (algebraMap D.F (RatFunc D.F)).injective
  haveI : Algebra.IsSeparable (RatFunc D.F) (Unramified.UnrChart.F₀' D χ) := inferInstance
  let χ' := Unramified.UnrChart.χ' D χ
  have hχ' : IsCompat D.φ' χ' := Unramified.UnrChart.isCompat D hχ
  have hχχ' : ∀ f, χ' (Unramified.UnrChart.of₀ D χ f) = χ f := Unramified.UnrChart.χ'_of₀ D χ
  have hcomp : χ'.comp (Unramified.UnrChart.of₀ D χ) = χ := RingHom.ext hχχ'
  have hθ' : Algebra.adjoin (RatFunc C) {χ' (Unramified.UnrChart.of₀ D χ θ₀)} = ⊤ := by
    rw [hχχ']; exact hθ
  have hinj' : ∀ W W' : Ext C G, W.1.comap χ' = W'.1.comap χ' → W = W' := by
    intro W W' h
    apply hinj
    rw [← hcomp, Valuation.comap_comp, Valuation.comap_comp, h]
  have hgen' : ∀ W : Ext C G, IntermediateField.adjoin 𝓀
      (resE χ' W : Set (ResidueField W.1.valuationSubring)) = ⊤ := by
    intro W
    rw [eq_top_iff, ← hgen W]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨Unramified.UnrChart.of₀ D χ f, by rw [hχχ']; exact hf, by rw [hχχ']⟩
  have hspan' : ∀ v₁ v₂ : Ext C G, ∀ y,
      IsSpanned 𝓀 (ιD χ' D.norm_φ' hχ' (F₀ := Unramified.UnrChart.F₀' D χ)).range
        (redD v₁) (redD v₂) y := by
    intro v₁ v₂ y
    refine isSpanned_mono ?_ (hspan v₁ v₂ y)
    rintro _ ⟨z, rfl⟩
    exact ⟨Unramified.UnrChart.j D hχ z, Subtype.ext (hχχ' z)⟩
  -- the point in the chart in `x - β'`, `β' = φ' βE`
  obtain ⟨P'', hP''max, hP''c, hsm'', hPP⟩ :=
    exists_transport_aff hβ' P' hP' ⟨⟨v, Q, hQ⟩, hb, hloc⟩
  haveI := hP''max
  -- its values are rational over `E'`
  obtain ⟨ι₁, hι₁⟩ : ∃ ι₁ : BD D.F (Unramified.UnrChart.F₀' D χ) →+*
      DRint (0 : C) 1 (Aff β 1 one_ne_zero G), ι₁ = W10Route.ιβ χ' D.norm_φ' hχ' hβ := ⟨_, rfl⟩
  obtain ⟨val₁, hval₁⟩ : ∃ val₁ : BD D.F (Unramified.UnrChart.F₀' D χ) →+* 𝓀,
      val₁ = (placeHomD v hQ).comp ι₁ := ⟨_, rfl⟩
  have hval₁_j : ∀ z, val₁ (Unramified.UnrChart.j D hχ z) = val z := by
    intro z
    have : ι₁ (Unramified.UnrChart.j D hχ z) = W10Route.ιβ χ hφ hχ hβ z := by
      rw [hι₁]
      exact Subtype.ext (by
        change toAff one_ne_zero (χ' (Unramified.UnrChart.of₀ D χ z)) = toAff one_ne_zero (χ z)
        rw [hχχ'])
    rw [hval₁, RingHom.comp_apply, this, hval, RingHom.comp_apply]
  have hval₁_cst : ∀ e : HenselComplete.integers D.F, val₁ (cstD e) = rE e := by
    intro e
    rw [hval₁, RingHom.comp_apply, hι₁, ιβ_cstD D.norm_φ' hχ' hβ e, placeHomD_constD', hrE]
    rfl
  have hval₁r : ∀ z, val₁ z ∈ rE.range := by
    intro z
    letI : Algebra (BD E F₀) (Unramified.UnrChart.BD' D hχ) :=
      (Unramified.UnrChart.j D hχ).toAlgebra
    have hz := Unramified.UnrChart.mem_adjoin_rr D hχ z
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      rw [Set.mem_singleton_iff.1 hz]
      exact ⟨D.rI, (hval₁_cst _).symm⟩
    | algebraMap z =>
      change val₁ (Unramified.UnrChart.j D hχ z) ∈ _
      rw [hval₁_j]
      exact hvalr z
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have hrat : ∀ z : BD D.F (Unramified.UnrChart.F₀' D χ), ∃ e : HenselComplete.integers D.F,
      W10Route.ιβ χ' D.norm_φ' hχ' (norm_φ_le D.norm_φ' βE) (z - cstD e) ∈ P'' := by
    intro z
    obtain ⟨e, he⟩ := hval₁r z
    refine ⟨e, (hPP _ (ι₁ (z - cstD e)) (by
      rw [hι₁, W10Route.coe_ιβ, W10Route.coe_ιβ]
      exact toAff_eq_toAff _ _ _)).2 ?_⟩
    rw [hmemP]
    rw [← RingHom.comp_apply, ← hval₁]
    rw [map_sub, hval₁_cst, he, sub_self]
  -- semistability over `O_{E'}`
  have hS := isEtaleLocallyAt_of_isDiscSmooth_aff hp hp1 D.norm_φ' hχ' hdeg' hθ' hinj' hgen'
    hspan' (D.irreducible_algebraMap hϖ) βE P'' hP''c hsm'' hrat
  -- descent along the étale `BD E F₀ → BD E' F₀'`
  letI := bdAlgebra (E := D.F) (F₀ := Unramified.UnrChart.F₀' D χ)
  letI : Algebra O_E (Unramified.UnrChart.BD' D hχ) :=
    ((algebraMap (HenselComplete.integers D.F) (Unramified.UnrChart.BD' D hχ)).comp
      (algebraMap O_E (HenselComplete.integers D.F))).toAlgebra
  haveI : IsScalarTower O_E (HenselComplete.integers D.F) (Unramified.UnrChart.BD' D hχ) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let ψj : BD E F₀ →ₐ[O_E] Unramified.UnrChart.BD' D hχ :=
    { Unramified.UnrChart.j D hχ with
      commutes' := fun e ↦ Subtype.ext (by
        change Unramified.UnrChart.of₀ D χ (algebraMap (RatFunc E) F₀
            (algebraMap E (RatFunc E) e)) =
          algebraMap (RatFunc D.F) (Unramified.UnrChart.F₀' D χ)
            (algebraMap D.F (RatFunc D.F) (algebraMap E D.F e))
        rw [Unramified.UnrChart.algRat_algebraMap_C, Unramified.UnrChart.ιE_algebraMap]
        rfl) }
  have h := hS.poly_comap_of_baseChange ((RingHom.etale_algebraMap).2 D.etale) ψj
    (Unramified.UnrChart.etale_j D hχ)
  convert h using 1
  ext z
  rw [Ideal.mem_comap, Ideal.mem_comap, Ideal.mem_comap]
  exact (hPP _ _ (hχχ' z)).symm

set_option maxHeartbeats 1000000 in
-- the assembly juggles the charts over `E`, `E'` and two twists of `G`
include hp hp1 hφ hχ in
/-- **(S) at an arbitrary residue point**, semistable form of
`isEtaleLocallyAt_of_isDiscSmooth_residue`. -/
theorem isSemistableAt_of_isDiscSmooth_residue [IsDiscreteValuationRing O_E]
    [PerfectField (ResidueField O_E)] (halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (hinj : ∀ W W' : Ext C G, W.1.comap χ = W'.1.comap χ → W = W')
    (hgen : ∀ W : Ext C G, IntermediateField.adjoin 𝓀
      (resE χ W : Set (ResidueField W.1.valuationSubring)) = ⊤)
    (hspan : ∀ v₁ v₂ : Ext C G, ∀ y,
      IsSpanned 𝓀 (ιD χ hφ hχ (F₀ := F₀)).range (redD v₁) (redD v₂) y)
    {ϖ : O_E} (hϖ : Irreducible ϖ) {β : C} (hβ : ‖β‖ ≤ 1)
    (P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1)
      (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) = discIdeal (0 : C) 1)
    (hsm : IsDiscSmooth P') :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    IsSemistableAt ϖ (P'.comap (W10Route.ιβ χ hφ hχ hβ)) :=
  letI := bdAlgebra (E := E) (F₀ := F₀)
  .inr (isEtaleLocallyAt_of_isDiscSmooth_residue hp hp1 hφ hχ halg hdeg hθ hinj hgen hspan hϖ hβ P'
    hP' hsm)

end Residue

end DVRDescent

namespace W10Route

open DVRDescent

/-- **Descent of smooth points** (Blueprint §9.7a, step 4, smooth part): with the set `S` of
`DVRDescent.SmoothHyps.exists_finset_smoothHyps`, `isSemistableAt_of_isDiscSmooth_residue`
applies at every residue point. -/
theorem smoothDescentStatement : SmoothDescentStatement.{u} := by
  intro C _ _ _ _ p hp hp1 G _ _ _ _ _ T hT
  obtain ⟨S, hS⟩ := SmoothHyps.exists_finset_smoothHyps.{u, u, u} (C := C) (G := G) hp hp1 hT
  refine ⟨S, ?_⟩
  intro E _ _ _ φ hφ hSφ halg _ _ F₀ _ _ _ _ _ _ χ hχ hdeg hTχ ϖ hϖ inst hinst β hβ P' hmax hP'
    hsm
  obtain ⟨⟨θ₀, hθ⟩, hinj, hgen, hspan⟩ := hS φ hφ hSφ χ hχ hdeg hTχ
  have hI : inst = bdAlgebra (E := E) (F₀ := F₀) := by
    refine Algebra.algebra_ext _ _ fun o ↦ Subtype.ext ?_
    rw [hinst]
    exact (IsScalarTower.algebraMap_apply E (RatFunc E) F₀ o).trans rfl
  subst hI
  haveI := hmax
  exact isSemistableAt_of_isDiscSmooth_residue hp hp1 hφ hχ halg hdeg hθ hinj hgen hspan hϖ hβ P'
    hP' hsm

end W10Route

end SemistableReduction
