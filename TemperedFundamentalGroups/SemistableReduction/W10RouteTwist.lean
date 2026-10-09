/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RoutePoints
import TemperedFundamentalGroups.SemistableReduction.SmoothLemma

/-!
# Points of the vertex and node charts over `C` (G4, part 3)

Blueprint §9.7a, step 4 (G4 (ii)).

* `SmoothOver C G`: all points of `DRint 0 1 G` over `(𝔪_C, x)` are smooth (the form of the
  clauses of `W7.IsSemistableTree`); it only depends on the `C(x)`-algebra structure
  (`smoothOver_congr`), so it transports between `Aff (a + c β) c F'` and `Aff β 1 (Aff a c F')`
  (`smoothOver_aff_aff`) and between `G` and `Aff 0 1 G` (`smoothOver_aff_zero`).
* `isSemistableAt_transfer`: semistability transfers along isomorphisms of `O`-algebras and to
  generizations.
* `closedCase`, `vertexCase`, `nodeCase`: for a valuation subring `W'` of `G` over `O_C`, the
  restriction to an `E`-chart of the center of `W'` lies in a semistable point, given the
  pointwise descent at the points over `C` (closed points of vertex charts over `x - β ∈ 𝔪_W'`;
  generic points of components, by going up to a closed point in a free residue direction; node
  points).
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section Congr

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

variable (C) in
/-- All points of the vertex chart `DRint 0 1 G` over `(𝔪_C, x)` are smooth. -/
def SmoothOver (G : Type*) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
    [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G] : Prop :=
  ∀ P' : Ideal (DRint (0 : C) 1 G), P'.IsMaximal →
    P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) = discIdeal (0 : C) 1 →
    IsDiscSmooth P'

/-- `SmoothOver` only depends on the `C(x)`-algebra structure. -/
theorem smoothOver_congr {G : Type*} [Field G] [Algebra C G] {i₁ i₂ : Algebra (RatFunc C) G}
    (h : i₁ = i₂) :
    (letI := i₁; ∀ (_ : IsScalarTower C (RatFunc C) G) (_ : FiniteDimensional (RatFunc C) G),
      SmoothOver C G) →
    (letI := i₂; ∀ (_ : IsScalarTower C (RatFunc C) G) (_ : FiniteDimensional (RatFunc C) G),
      SmoothOver C G) := by
  subst h
  exact id

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma aff_aff {a c β : C} (hc : c ≠ 0) (f : RatFunc C) :
    aff a c hc (aff β 1 one_ne_zero f) = aff (a + c * β) c hc f := by
  have h := congrArg (fun g : RatFunc C →ₐ[C] RatFunc C ↦ g f)
    (ratFunc_algHom_ext (φ := ((aff a c hc).toAlgHom.comp (aff β 1 one_ne_zero).toAlgHom))
      (ψ := (aff (a + c * β) c hc).toAlgHom) (by
        change aff a c hc (aff β 1 one_ne_zero RatFunc.X) = aff (a + c * β) c hc RatFunc.X
        rw [aff_apply, aff_apply, aff_apply, affHom_X, affHom_X, affHom_gaussCoord,
          gaussCoord_eq, gaussCoord_eq]
        have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
        simp only [map_add, map_mul, inv_one, map_one, one_mul, map_inv₀]
        field_simp
        ring))
  simpa using h

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
/-- The two twists `Aff β 1 (Aff a c F')` and `Aff (a + c β) c F'` are the same `C(x)`-algebra. -/
lemma algebra_aff_aff_eq {a c β : C} (hc : c ≠ 0) :
    (inferInstance : Algebra (RatFunc C) (Aff β 1 one_ne_zero (Aff a c hc F'))) =
      (inferInstance : Algebra (RatFunc C) (Aff (a + c * β) c hc F')) := by
  refine Algebra.algebra_ext _ _ fun f ↦ ?_
  change algebraMap (RatFunc C) F' (aff a c hc (aff β 1 one_ne_zero f)) =
    algebraMap (RatFunc C) F' (aff (a + c * β) c hc f)
  rw [aff_aff]

/-- W7's smoothness of `Aff (a + c β) c F'` is smoothness of `Aff β 1 (Aff a c F')`. -/
theorem smoothOver_aff_aff {a c β : C} (hc : c ≠ 0)
    (h : SmoothOver C (Aff (a + c * β) c hc F')) :
    SmoothOver C (Aff β 1 one_ne_zero (Aff a c hc F')) := by
  have key := smoothOver_congr (C := C) (G := F')
    (algebra_aff_aff_eq (F' := F') (a := a) (β := β) hc).symm
  exact key (fun _ _ ↦ h)
    (inferInstanceAs (IsScalarTower C (RatFunc C) (Aff β 1 one_ne_zero (Aff a c hc F'))))
    (inferInstanceAs (FiniteDimensional (RatFunc C) (Aff β 1 one_ne_zero (Aff a c hc F'))))

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma aff_zero_one (f : RatFunc C) : aff (0 : C) 1 one_ne_zero f = f := by
  have h := congrArg (fun g : RatFunc C →ₐ[C] RatFunc C ↦ g f)
    (ratFunc_algHom_ext (φ := (aff (0 : C) 1 one_ne_zero).toAlgHom) (ψ := AlgHom.id C _) (by
      change aff (0 : C) 1 one_ne_zero RatFunc.X = RatFunc.X
      rw [aff_apply, affHom_X, gaussCoord_zero_one]))
  simpa using h

/-- Smoothness of `G` is smoothness of `Aff 0 1 G`. -/
theorem smoothOver_aff_zero (h : SmoothOver C F') :
    SmoothOver C (Aff (0 : C) 1 one_ne_zero F') := by
  have heq : (inferInstance : Algebra (RatFunc C) F') =
      (inferInstance : Algebra (RatFunc C) (Aff (0 : C) 1 one_ne_zero F')) := by
    refine Algebra.algebra_ext _ _ fun f ↦ ?_
    change algebraMap (RatFunc C) F' f = algebraMap (RatFunc C) F' (aff 0 1 one_ne_zero f)
    rw [aff_zero_one]
  have key := smoothOver_congr (C := C) (G := F') heq
  exact key (fun _ _ ↦ h)
    (inferInstanceAs (IsScalarTower C (RatFunc C) (Aff (0 : C) 1 one_ne_zero F')))
    (inferInstanceAs (FiniteDimensional (RatFunc C) (Aff (0 : C) 1 one_ne_zero F')))

end Congr

/-! ### The three kinds of points over `C` -/

section Cases

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {G : Type u} [Field G] [Algebra (RatFunc C) G]
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] {φ : E →+* C}
  (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F₀ : Type u} [Field F₀] [Algebra (RatFunc E) F₀] {χ : F₀ →+* G}
  (hχ : DVRDescent.IsCompat φ χ)
  {ϖ : (NormedField.valuation (K := E)).valuationSubring}

set_option hygiene false in
local notation "ψ" => algebraMap (RatFunc C) G

set_option hygiene false in
local notation "κ" k => algebraMap (RatFunc C) G (algebraMap C (RatFunc C) k)

omit [IsUltrametricDist C] in
lemma norm_sub_le_max' [IsUltrametricDist C] (x y : C) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max x (-y)

/-- **Semistability transfers along `O`-isomorphisms and to generizations.** -/
theorem isSemistableAt_transfer {O : Type u} [CommRing O] {ϖ : O} {A B : Type u} [CommRing A]
    [CommRing B] [Algebra O A] [Algebra O B] (e : A ≃+* B)
    (he : ∀ o, e (algebraMap O A o) = algebraMap O B o) {𝔭 : Ideal A} [𝔭.IsPrime]
    {𝔮 : Ideal B} (h : IsSemistableAt ϖ 𝔮) (hle : ∀ z ∈ 𝔭, e z ∈ 𝔮) : IsSemistableAt ϖ 𝔭 := by
  have h' := IsSemistableAt.of_etale_of_comap (AlgEquiv.ofRingEquiv (f := e) he).toAlgHom
    (RingHom.Etale.of_bijective e.bijective) h
  exact IsSemistableAt.of_le h' fun z hz ↦ hle z hz

lemma isOverOC_aff {W' : ValuationSubring G} (hO : IsOverOC C W') (β : C) :
    @IsOverOC C inferInstance (Aff β (1 : C) one_ne_zero G) inferInstance inferInstance W' := by
  intro k
  change W'.valuation (algebraMap (RatFunc C) G (aff β 1 one_ne_zero (algebraMap C _ k))) ≤ 1 ↔ _
  rw [AlgEquiv.commutes]
  exact hO k

lemma algebraMap_aff_X (β : C) :
    algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X =
      toAff one_ne_zero (ψ RatFunc.X - κ β) := by
  change ψ (aff β 1 one_ne_zero RatFunc.X) = _
  rw [aff_apply, affHom_X, gaussCoord_eq, inv_one, map_one, one_mul, map_sub]
  rfl

include hφ hχ in
/-- **Node points**: if `x, c₀/x ∈ 𝔪_W'` and the descent applies at the node points of
`Rint c₀ G`, the center of `W'` restricts to a prime of `Rint c₀E F₀` contained in a semistable
one. -/
theorem nodeCase {c₀ : C} (hc : ‖c₀‖ < 1) (hc0 : c₀ ≠ 0) {c₀E : E} (hcE : φ c₀E = c₀)
    [Algebra (NormedField.valuation (K := E)).valuationSubring (Rint c₀E F₀)]
    (W' : ValuationSubring G) (hO : IsOverOC C W') (hX : W'.valuation (ψ RatFunc.X) < 1)
    (hcX : W'.valuation (ψ (algebraMap C (RatFunc C) c₀ / RatFunc.X)) < 1)
    (hnode : ∀ P' : Ideal (Rint c₀ G), P'.IsMaximal →
      P'.comap (algebraMap (nodeRing c₀) (Rint c₀ G)) = tubeIdeal c₀ →
      IsSemistableAt ϖ (P'.comap (ιN χ hφ hχ hcE))) :
    ∃ 𝔮 : Ideal (Rint c₀E F₀), IsSemistableAt ϖ 𝔮 ∧
      ∀ y : Rint c₀E F₀, W'.valuation (χ y) < 1 → y ∈ 𝔮 := by
  have hcomap := comap_centerI_rint hc hc0 hO hX hcX
  haveI := tubeIdeal_isMaximal hc hc0
  haveI : (centerI W' (Rint c₀ G) (rint_le hO hX hcX)).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hcomap]; infer_instance)
  exact ⟨_, hnode _ inferInstance hcomap, fun y hy ↦ hy⟩

variable [Algebra (NormedField.valuation (K := E)).valuationSubring (DRint (0 : E) 1 F₀)]

include hφ hχ in
/-- **Closed points of a vertex chart**: if `x - β ∈ 𝔪_W'` and the descent applies at the points
of `DRint 0 1 (Aff β 1 G)` over `(𝔪_C, x - β)`, the center of `W'` restricts to a prime of
`DRint 0 1 F₀` contained in a semistable one. -/
theorem closedCase (W' : ValuationSubring G) (hO : IsOverOC C W') {β : C} (hβ : ‖β‖ ≤ 1)
    (hXβ : W'.valuation (ψ RatFunc.X - κ β) < 1)
    (hsm : ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G)), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) =
        discIdeal (0 : C) 1 → IsSemistableAt ϖ (P'.comap (ιβ χ hφ hχ hβ))) :
    ∃ 𝔮 : Ideal (DRint (0 : E) 1 F₀), IsSemistableAt ϖ 𝔮 ∧
      ∀ y : DRint (0 : E) 1 F₀, W'.valuation (χ y) < 1 → y ∈ 𝔮 := by
  let Wβ : ValuationSubring (Aff β 1 one_ne_zero G) := W'
  have hOβ : IsOverOC C Wβ := isOverOC_aff hO β
  have hXβ' : Wβ.valuation (algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X) < 1 := by
    rw [algebraMap_aff_X]; exact hXβ
  have hcomap := comap_centerI_drint hOβ hXβ'
  haveI : (centerI Wβ (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))
      (drint_le hOβ ((Wβ.valuation_le_one_iff _).1 hXβ'.le))).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
      (by rw [hcomap]; exact discIdeal_isMaximal one_ne_zero)
  exact ⟨_, hsm _ inferInstance hcomap, fun y hy ↦ hy⟩

include hφ hχ in
/-- **Points of a vertex chart off the child directions** `D`: closed points (some `x - β ∈ 𝔪_W'`)
and the generic points of the components (all `x - β` units; going up to a closed point in a
free residue direction). -/
theorem vertexCase [IsAlgClosed C] (W' : ValuationSubring G) (hO : IsOverOC C W')
    (hX : ψ RatFunc.X ∈ W') (D : Finset C)
    (hD : ∀ δ ∈ D, ‖δ‖ ≤ 1 ∧ W'.valuation (ψ RatFunc.X - κ δ) = 1)
    (hsm : ∀ (β : C) (hβ : ‖β‖ ≤ 1), (∀ δ ∈ D, ‖β - δ‖ = 1) →
      ∀ P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G)), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) =
        discIdeal (0 : C) 1 → IsSemistableAt ϖ (P'.comap (ιβ χ hφ hχ hβ))) :
    ∃ 𝔮 : Ideal (DRint (0 : E) 1 F₀), IsSemistableAt ϖ 𝔮 ∧
      ∀ y : DRint (0 : E) 1 F₀, W'.valuation (χ y) < 1 → y ∈ 𝔮 := by
  by_cases hcl : ∃ β : C, ‖β‖ ≤ 1 ∧ W'.valuation (ψ RatFunc.X - κ β) < 1
  · obtain ⟨β, hβ, hXβ⟩ := hcl
    refine closedCase hφ hχ W' hO hβ hXβ (hsm β hβ fun δ hδ ↦ ?_)
    obtain ⟨hδ1, hδu⟩ := hD δ hδ
    have hval : W'.valuation (κ (β - δ)) = 1 := by
      have : (κ (β - δ)) = (ψ RatFunc.X - κ δ) - (ψ RatFunc.X - κ β) := by
        simp only [map_sub]; ring
      rw [this, Valuation.map_sub_eq_of_lt_left _ (by rw [hδu]; exact hXβ), hδu]
    have hle : ‖β - δ‖ ≤ 1 := (norm_sub_le_max' _ _).trans (max_le hβ hδ1)
    refine le_antisymm hle (not_lt.1 fun hlt ↦ ?_)
    rw [← hO.lt_one_iff, hval] at hlt
    exact lt_irrefl _ hlt
  · push Not at hcl
    obtain ⟨β, hβ, hfar⟩ := exists_far D fun δ hδ ↦ (hD δ hδ).1
    have hnc : ∀ δ ∈ D, ‖β - δ‖ = 1 := fun δ hδ ↦ le_antisymm
      ((norm_sub_le_max' _ _).trans (max_le hβ (hD δ hδ).1)) (hfar δ hδ)
    let Wβ : ValuationSubring (Aff β 1 one_ne_zero G) := W'
    have hOβ : IsOverOC C Wβ := isOverOC_aff hO β
    have hXβ : algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X ∈ Wβ := by
      rw [algebraMap_aff_X]
      exact sub_mem hX (hO.mem hβ)
    have hgen : ∀ b : C, ‖b‖ ≤ 1 → Wβ.valuation
        (algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) RatFunc.X -
          algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) (algebraMap C (RatFunc C) b)) = 1 := by
      intro b hb
      have e : algebraMap (RatFunc C) (Aff β 1 one_ne_zero G) (algebraMap C (RatFunc C) b) =
          toAff one_ne_zero (κ b) := by
        change ψ (aff β 1 one_ne_zero _) = _
        rw [AlgEquiv.commutes]; rfl
      rw [algebraMap_aff_X, e]
      change W'.valuation (ψ RatFunc.X - (κ β) - (κ b)) = 1
      have : ψ RatFunc.X - (κ β) - (κ b) = ψ RatFunc.X - κ (β + b) := by
        simp only [map_add]; ring
      rw [this]
      have hβb : ‖β + b‖ ≤ 1 := (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hβ hb)
      exact le_antisymm ((W'.valuation_le_one_iff _).2 (sub_mem hX (hO.mem hβb))) (hcl _ hβb)
    have hle := comap_centerI_drint_le hOβ hXβ hgen
    haveI := discIdeal_isMaximal (a := (0 : C)) one_ne_zero
    obtain ⟨Q, hQI, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (discIdeal (0 : C) 1) _ hle
    haveI := hQp
    haveI : Q.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _
      (by rw [hQc]; exact discIdeal_isMaximal one_ne_zero)
    exact ⟨_, hsm β hβ hnc Q inferInstance hQc, fun y hy ↦ hQI hy⟩

end Cases

end W10Route

end SemistableReduction
