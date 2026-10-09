/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.UnramifiedChart
import TemperedFundamentalGroups.SemistableReduction.W10RouteStatements
import TemperedFundamentalGroups.SemistableReduction.S8Transport

/-!
# Smooth points over a residue point `x̄ = β̄` (W10, smooth part)

Blueprint §9.12 (O7). The vertex chart `DRint 0 1 G` of `C(x)` is the same ring as
`DRint 0 1 (Aff β 1 G)` for `‖β‖ ≤ 1` (`W10Route.mem_drint_aff_iff`); a point over the residue
point `x̄ = β̄` lies over the disc ideal of the twisted chart.

* `ratFuncMap_aff`: the twist `x ↦ x - b` commutes with `ratFuncMap φ`;
* `isSemistableAt_of_isDiscSmooth_aff` (**(S) at a residue point `b̄`, `b ∈ E`**): the descent
  of smooth points of the twisted chart `DRint 0 1 (Aff b 1 G)` to the untwisted chart over `O_E`,
  for `b ∈ O_E` and a `κ_E`-rational point (the hypotheses `hinj`, `hgen`, `hspan`, `hθ` are
  those of the untwisted `G`).
-/

open Polynomial IsLocalRing

set_option linter.unusedSectionVars false

namespace SemistableReduction

namespace DVRDescent

open GaussTube DiscCount SmoothVertex FundamentalInequality GaussStability GaussFibre PlaceNorm
  ConstantDescent AffineTwist

universe u

section Twist

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}

/-- The twist `x ↦ x - b` commutes with `ratFuncMap φ`. -/
lemma ratFuncMap_aff (b : E) (f : RatFunc E) :
    ratFuncMap φ (aff b 1 one_ne_zero f) = aff (φ b) 1 one_ne_zero (ratFuncMap φ f) := by
  have := ratFunc_ringHom_ext (f := (ratFuncMap φ).comp (aff b 1 one_ne_zero).toRingHom)
    (g := (aff (φ b) 1 one_ne_zero).toRingHom.comp (ratFuncMap φ)) (fun a ↦ by
      change ratFuncMap φ (aff b 1 one_ne_zero (algebraMap E (RatFunc E) a)) =
        aff (φ b) 1 one_ne_zero (ratFuncMap φ (algebraMap E (RatFunc E) a))
      rw [AlgEquiv.commutes, ratFuncMap_algebraMap_C, AlgEquiv.commutes])
    (by
      change ratFuncMap φ (aff b 1 one_ne_zero RatFunc.X) =
        aff (φ b) 1 one_ne_zero (ratFuncMap φ RatFunc.X)
      rw [ratFuncMap_X, aff_apply, aff_apply, affHom_X, affHom_X, gaussCoord_eq, gaussCoord_eq,
        map_mul, _root_.map_sub, ratFuncMap_algebraMap_C, ratFuncMap_algebraMap_C, ratFuncMap_X,
        map_inv₀, map_one, inv_one])
  exact congrArg (fun h ↦ h f) this

variable {G : Type*} [Field G] [Algebra (RatFunc C) G]
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* G}

variable (χ) in
/-- The twisted embedding `Aff b 1 F₀ → Aff (φ b) 1 G`. -/
noncomputable def χAff (b : E) :
    Aff b 1 one_ne_zero F₀ →+* Aff (φ b) 1 one_ne_zero G :=
  (toAff one_ne_zero).toRingHom.comp (χ.comp (toAff one_ne_zero).symm.toRingHom)

lemma χAff_apply (b : E) (f : F₀) :
    χAff (φ := φ) χ b (toAff one_ne_zero f) = toAff one_ne_zero (χ f) := rfl

lemma isCompat_aff (hχ : IsCompat φ χ) (b : E) : IsCompat φ (χAff (φ := φ) χ b) := by
  intro f
  rw [algebraMap_aff_apply, χAff_apply, hχ, ratFuncMap_aff, algebraMap_aff_apply]

end Twist

section ExtAff

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G]

/-- Extensions of `w_{0,1}` to the twist `Aff β 1 G` are extensions to `G` (`‖β‖ ≤ 1`). -/
def extUnaff {β : C} (hβ : ‖β‖ ≤ 1) (W : Ext C (Aff β 1 one_ne_zero G)) : Ext C G :=
  ⟨W.1, Valuation.ext fun ψ ↦ by
    have h := congrArg (fun w : Valuation (RatFunc C) NNReal ↦ w ((aff β 1 one_ne_zero).symm ψ))
      W.2
    simp only [Valuation.comap_apply, algebraMap_aff_apply, AlgEquiv.apply_symm_apply] at h
    rw [Valuation.comap_apply]
    refine h.trans ?_
    rw [gauss1_aff_symm]
    have hu : Units.mk0 ‖(1 : C)‖₊ (nnnorm_ne_zero_iff.2 one_ne_zero) = 1 :=
      Units.ext (by simp)
    rw [hu, Splitting.gaussRat_eq_of_le (b := 0)]
    rw [sub_zero, NormedField.valuation_apply, Units.val_one]
    exact_mod_cast hβ⟩

lemma extUnaff_val {β : C} (hβ : ‖β‖ ≤ 1) (W : Ext C (Aff β 1 one_ne_zero G)) :
    (extUnaff hβ W).1 = W.1 := rfl

end ExtAff

section RationalAff

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

include hφ in
lemma norm_φ_le (b : HenselComplete.integers E) : ‖φ b‖ ≤ 1 := by
  rw [hφ]; exact HenselComplete.norm_le_one b

/-- Generation over `C(x)` is invariant under the twist. -/
lemma adjoin_aff_eq_top {β : C} {y : G} (h : Algebra.adjoin (RatFunc C) {y} = ⊤) :
    Algebra.adjoin (RatFunc C) {toAff (a := β) (c := 1) one_ne_zero y} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  have hz : (toAff one_ne_zero).symm z ∈ Algebra.adjoin (RatFunc C) {y} := h ▸ Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz ⊢
  obtain ⟨P, hP⟩ := hz
  refine ⟨P.map (aff β 1 one_ne_zero).symm.toRingEquiv.toRingHom, ?_⟩
  change aeval _ _ = z
  rw [aeval_def, eval₂_map]
  have : (algebraMap (RatFunc C) (Aff β 1 one_ne_zero G)).comp
      (aff β 1 one_ne_zero).symm.toRingEquiv.toRingHom =
      (toAff one_ne_zero).toRingHom.comp (algebraMap (RatFunc C) G) := by
    ext ψ
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [algebraMap_aff_apply]
    change toAff one_ne_zero (algebraMap (RatFunc C) G
      (aff β 1 one_ne_zero ((aff β 1 one_ne_zero).symm ψ))) = _
    rw [AlgEquiv.apply_symm_apply]
    rfl
  rw [this]
  change eval₂ ((toAff one_ne_zero).toRingHom.comp (algebraMap (RatFunc C) G))
    ((toAff (a := β) (c := 1) one_ne_zero).toRingHom y) P = z
  rw [← hom_eval₂]
  change toAff one_ne_zero (aeval y P) = z
  change aeval y P = (toAff one_ne_zero).symm z at hP
  rw [hP]
  rfl

include hp hp1 hφ hχ in
/-- **(S) at a residue point `b̄`, `b ∈ O_E`**: a smooth `κ_E`-rational point of the twisted chart
`DRint 0 1 (Aff b 1 G)` over `(𝔪_C, x - b)` restricts to a point of the untwisted vertex chart
over `O_E` at which it is étale-locally `O_E[u]`. -/
theorem isEtaleLocallyAt_of_isDiscSmooth_aff [IsDiscreteValuationRing (HenselComplete.integers E)]
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (hinj : ∀ W W' : Ext C G, W.1.comap χ = W'.1.comap χ → W = W')
    (hgen : ∀ W : Ext C G, IntermediateField.adjoin 𝓀
      (resE χ W : Set (ResidueField W.1.valuationSubring)) = ⊤)
    (hspan : ∀ v₁ v₂ : Ext C G, ∀ y,
      IsSpanned 𝓀 (ιD χ hφ hχ (F₀ := F₀)).range (redD v₁) (redD v₂) y)
    {ϖ : HenselComplete.integers E} (hϖ : Irreducible ϖ) (b : HenselComplete.integers E)
    (P' : Ideal (DRint (0 : C) 1 (Aff (φ b) 1 one_ne_zero G))) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1)
      (DRint (0 : C) 1 (Aff (φ b) 1 one_ne_zero G))) = discIdeal (0 : C) 1)
    (hsm : IsDiscSmooth P')
    (hrat : ∀ z : BD E F₀, ∃ e : HenselComplete.integers E,
      W10Route.ιβ χ hφ hχ (norm_φ_le hφ b) (z - cstD e) ∈ P') :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    IsEtaleLocallyAt (HenselComplete.integers E) (HenselComplete.integers E)[X]
      (P'.comap (W10Route.ιβ χ hφ hχ (norm_φ_le hφ b))) := by
  letI := bdAlgebra (E := E) (F₀ := F₀)
  have hb := norm_φ_le hφ b
  have hb₀ : ‖(b : E)‖ ≤ 1 := HenselComplete.norm_le_one b
  -- the twisted setting over `E`
  let χt := χAff (φ := φ) (G := G) χ (b : E)
  have hχt : IsCompat φ χt := isCompat_aff hχ b
  haveI : CharZero E := ⟨fun m n h ↦ Nat.cast_injective (R := C) (by simpa using congrArg φ h)⟩
  haveI : Algebra.IsSeparable (RatFunc E) (Aff (b : E) 1 one_ne_zero F₀) := inferInstance
  have hdeg_t : Module.finrank (RatFunc E) (Aff (b : E) 1 one_ne_zero F₀) =
      Module.finrank (RatFunc C) (Aff (φ b) 1 one_ne_zero G) := by
    rw [finrank_aff, finrank_aff, hdeg]
  have hθ_t : Algebra.adjoin (RatFunc C) {χt (toAff one_ne_zero θ₀)} = ⊤ := by
    have := adjoin_aff_eq_top (C := C) (G := G) (β := φ b) hθ
    exact this
  have hinj_t : ∀ W W' : Ext C (Aff (φ b) 1 one_ne_zero G),
      W.1.comap χt = W'.1.comap χt → W = W' := by
    intro W W' h
    have := hinj (extUnaff hb W) (extUnaff hb W') h
    have h2 := congrArg Subtype.val this
    exact Subtype.ext h2
  have hgen_t : ∀ W : Ext C (Aff (φ b) 1 one_ne_zero G), IntermediateField.adjoin 𝓀
      (resE χt W : Set (ResidueField W.1.valuationSubring)) = ⊤ := fun W ↦ hgen (extUnaff hb W)
  -- the twisted vertex charts are the same rings
  have hmemE : ∀ z : F₀, toAff (a := (b : E)) one_ne_zero z ∈
      BD E (Aff (b : E) 1 one_ne_zero F₀) ↔ z ∈ BD E F₀ :=
    W10Route.mem_drint_aff_iff hb₀
  have hmemC : ∀ z : G, toAff (a := φ b) one_ne_zero z ∈
      DRint (0 : C) 1 (Aff (φ b) 1 one_ne_zero G) ↔
      z ∈ DRint (0 : C) 1 G := W10Route.mem_drint_aff_iff hb
  have hspan_t : ∀ v₁ v₂ : Ext C (Aff (φ b) 1 one_ne_zero G), ∀ y,
      IsSpanned 𝓀 (ιD χt hφ hχt (F₀ := (Aff (b : E) 1 one_ne_zero F₀))).range
        (redD v₁) (redD v₂) y := by
    intro v₁ v₂ y
    obtain ⟨n, lam, bb, hbb, h₁, h₂⟩ := hspan (extUnaff hb v₁) (extUnaff hb v₂)
      ⟨y.1, (hmemC _).1 y.2⟩
    choose z hz using hbb
    refine ⟨n, lam, fun j ↦ ⟨(bb j).1, (hmemC _).2 (bb j).2⟩, fun j ↦
      ⟨⟨(z j).1, (hmemE _).2 (z j).2⟩, Subtype.ext ?_⟩, h₁, h₂⟩
    have := congrArg Subtype.val (hz j)
    exact this
  have hcst : ∀ e : HenselComplete.integers E,
      ((cstD e : BD E (Aff (b : E) 1 one_ne_zero F₀)) : Aff (b : E) 1 one_ne_zero F₀) =
        toAff one_ne_zero ((cstD e : BD E F₀) : F₀) := by
    intro e
    change algebraMap (RatFunc E) (Aff (b : E) 1 one_ne_zero F₀) (algebraMap E (RatFunc E) e) = _
    rw [algebraMap_aff_apply, AlgEquiv.commutes]
    rfl
  have hrat_t : ∀ z : BD E (Aff (b : E) 1 one_ne_zero F₀), ∃ e : HenselComplete.integers E,
      ιD χt hφ hχt (z - cstD e) ∈ P' := by
    intro z
    obtain ⟨e, he⟩ := hrat ⟨(toAff one_ne_zero).symm z.1, (hmemE _).1 z.2⟩
    refine ⟨e, ?_⟩
    convert he using 1
    apply Subtype.ext
    change χt ((z : Aff (b : E) 1 one_ne_zero F₀) - (cstD e : BD E (Aff (b : E) 1 one_ne_zero F₀)))
      = toAff one_ne_zero (χ ((toAff one_ne_zero).symm (z : Aff (b : E) 1 one_ne_zero F₀) -
        (cstD e : BD E F₀)))
    rw [hcst]
    rfl
  have hS := isEtaleLocallyAt_of_isDiscSmooth hp hp1 hφ hχt hdeg_t hθ_t hinj_t hgen_t hspan_t hϖ
    P' hP' hsm hrat_t
  -- transport back to the untwisted chart
  letI := bdAlgebra (E := E) (F₀ := Aff (b : E) 1 one_ne_zero F₀)
  let κ : BD E F₀ →ₐ[HenselComplete.integers E] BD E (Aff (b : E) 1 one_ne_zero F₀) :=
    { toFun := fun z ↦ ⟨toAff one_ne_zero z.1, (hmemE _).2 z.2⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl
      commutes' := fun e ↦ Subtype.ext (hcst e).symm }
  have hκ : κ.toRingHom.Etale := RingHom.Etale.of_bijective
    ⟨fun z z' h ↦ by
      have h2 := congrArg Subtype.val h
      exact Subtype.ext h2,
      fun z ↦ ⟨⟨(toAff one_ne_zero).symm z.1, (hmemE _).1 z.2⟩, rfl⟩⟩
  have h := hS.of_etale_of_comap κ hκ
  rw [Ideal.comap_comap] at h
  exact h

include hp hp1 hφ hχ in
/-- Semistable form of `isEtaleLocallyAt_of_isDiscSmooth_aff`. -/
theorem isSemistableAt_of_isDiscSmooth_aff [IsDiscreteValuationRing (HenselComplete.integers E)]
    (hdeg : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
    {θ₀ : F₀} (hθ : Algebra.adjoin (RatFunc C) {χ θ₀} = ⊤)
    (hinj : ∀ W W' : Ext C G, W.1.comap χ = W'.1.comap χ → W = W')
    (hgen : ∀ W : Ext C G, IntermediateField.adjoin 𝓀
      (resE χ W : Set (ResidueField W.1.valuationSubring)) = ⊤)
    (hspan : ∀ v₁ v₂ : Ext C G, ∀ y,
      IsSpanned 𝓀 (ιD χ hφ hχ (F₀ := F₀)).range (redD v₁) (redD v₂) y)
    {ϖ : HenselComplete.integers E} (hϖ : Irreducible ϖ) (b : HenselComplete.integers E)
    (P' : Ideal (DRint (0 : C) 1 (Aff (φ b) 1 one_ne_zero G))) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1)
      (DRint (0 : C) 1 (Aff (φ b) 1 one_ne_zero G))) = discIdeal (0 : C) 1)
    (hsm : IsDiscSmooth P')
    (hrat : ∀ z : BD E F₀, ∃ e : HenselComplete.integers E,
      W10Route.ιβ χ hφ hχ (norm_φ_le hφ b) (z - cstD e) ∈ P') :
    letI := bdAlgebra (E := E) (F₀ := F₀)
    IsSemistableAt ϖ (P'.comap (W10Route.ιβ χ hφ hχ (norm_φ_le hφ b))) :=
  letI := bdAlgebra (E := E) (F₀ := F₀)
  .inr (isEtaleLocallyAt_of_isDiscSmooth_aff hp hp1 hφ hχ hdeg hθ hinj hgen hspan hϖ b P' hP' hsm
    hrat)

end RationalAff

end DVRDescent

end SemistableReduction
