/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeEtale
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0SpecialCompat
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0PatchSpecial
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueReduced
import TemperedFundamentalGroups.SemistableReduction.TateChartReduced

/-!
# The special fibre of the lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` (MR13 A1, reduction)

For the M2 lift `(N, B, α)` of a tame covering of `ℙ¹_k ∖ {0, 1, ā}` given by `Sp`, `S0`, `ω`
(`P1ThreeGlue`, `P1ThreeFlat`, `P1ThreeEtale`), the reduction of the algebraized covering is the
given covering, chart by chart, with its glueing datum and its structure maps (instances of the
generic `NodeEtaleGlue.Overlap.specialFibreEquiv0/1`, `specialFibre01_r0/r1`,
`specialFibreEquiv0/1_ψ`; the bottom level of the base charts `R0/ϖ`, `R1/ϖ` has `J = 0`):

* **`P1Three.specialFibreEquiv1`**: `B₁ ⧸ (ϖ) ≃ C1` (over `V₁ = ℙ¹ ∖ {0, 1, a}`);
* **`P1Three.specialFibreEquiv0`**: `B₀ ⧸ (ϖ) ≃ C0` (over `V₀`, the chart of the three cusps; bottom
  identification of the cusp patch `CuspTower.cuspInput … |>.bottom`);
* `P1Three.specialFibre01_r1`, `specialFibre01_r0`: restricting to the overlap and reducing gives
  `C1 → C1[1/ȳ]` and `C0 → C0[1/x̄] ≃ω C1[1/ȳ]`;
* **`P1Three.specialFibreEquiv1_ψ`**, `specialFibreEquiv0_ψ`: the reduction of the structure map
  `ψ : ℙ¹_t → 𝒴` is the structure map `R_i → C_i` of the given covering;
* `P1Three.isReduced_Ts_R1`, **`P1Three.isReduced_C1`**: `R1/J` (the coordinate ring of
  `ℙ¹_k ∖ {0, 1, ā}`) and the étale covering `C1` of it are reduced;
* **`P1Three.connected_lift_of_special`**: if `C1` has only the trivial idempotents (a connected
  étale cover of `V₁ ⊗ k`), the generic fibre `B₁[1/ϖ]` of the lift has only the trivial
  idempotents (`connected_lift` transported along `specialFibreEquiv1`).

This is item (a) of the A1/A2/B4 list in MR13-plan (run 11): with it the lifting step of the
"lifting half" of tame specialisation ([SGA1] XIII, proof of Cor 2.12) lifts the given special
covering, and connectedness passes from the special to the generic fibre.
-/

universe u

open Polynomial

namespace SemistableReduction

/-- An algebra `C` over a reduced Noetherian ring `A` which is étale after inverting a unit is
reduced. -/
theorem isReduced_of_etale_away {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] [IsReduced A] (x : A) (hx : IsUnit x)
    (h : (Localization.awayMap (algebraMap A C) x).Etale) : IsReduced C := by
  letI := (Localization.awayMap (algebraMap A C) x).toAlgebra
  haveI : Algebra.Etale (Localization.Away x) (Localization.Away (algebraMap A C x)) := h
  haveI : IsReduced (Localization.Away x) :=
    isReduced_of_isLocalization (S := Localization.Away x) (Submonoid.powers x)
  haveI : IsNoetherianRing (Localization.Away x) :=
    IsLocalization.isNoetherianRing (Submonoid.powers x) _ inferInstance
  haveI := EtaleReduced.isReduced_of_etale (Localization.Away x)
    (Localization.Away (algebraMap A C x))
  let f := IsLocalization.atUnit C (Localization.Away (algebraMap A C x)) (algebraMap A C x)
    (hx.map _)
  have hf : ∀ c, f c = algebraMap C (Localization.Away (algebraMap A C x)) c := fun c ↦ by
    simpa using f.commutes c
  refine isReduced_of_injective (algebraMap C (Localization.Away (algebraMap A C x)))
    fun p q hpq ↦ f.injective ?_
  rw [hf, hf, hpq]

namespace P1Three

open TateLevel AdmissibleLift

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O] (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))
  (ω : OmegaC Sp S0.C0) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

omit hθ [IsNoetherianRing O] in
include hker in
/-- `J = 0` on the bottom level of a `ϖ`-adic tower of charts. -/
lemma J_Tn_zero_eq_bot (T : Type u) [CommRing T] [Algebra O T] :
    J θ (R := EtaleTower.Tn ϖ T 0) = ⊥ := by
  simpa using EtaleTower.hJ (T := T) hker 0

/-- The bottom identification of the cusp patch over `V₀`. -/
def bottom0 : (overlap Sp hϖ hker S0 ω hO).P0.Bottom 0 :=
  (CuspTower.cuspInput S0 hϖ hker (isSMulRegular_x0 ϖ a)).bottom hθ.out hO
    (J_Tn_zero_eq_bot hker _)

omit hθ [IsNoetherianRing O] in
include hϖ hker in
/-- **The special fibre of `V₁` is reduced**: `R1/J = R1/ϖ = (O/ϖ)[Y][s]/(Ḡ₁)`, the coordinate
ring of `ℙ¹ ∖ {0, 1, ā}` over the field `O/ϖ = k` (a Dedekind domain, `isDedekindDomain_R1`). -/
theorem isReduced_Ts_R1 (hθs : Function.Surjective θ) : IsReduced (EtaleTower.Ts θ (R1 O a)) := by
  have hk : RingHom.ker θ = Ideal.span {ϖ} :=
    le_antisymm hker (Ideal.span_le.2 (Set.singleton_subset_iff.2 hϖ))
  haveI : (Ideal.span {ϖ}).IsMaximal := hk ▸ RingHom.ker_isMaximal_of_surjective θ hθs
  letI : Field (O ⧸ Ideal.span {ϖ}) := Ideal.Quotient.field _
  haveI := isDedekindDomain_R1 (Ideal.Quotient.mk (Ideal.span {ϖ}) a)
  have h := isReduced_quotient_adjoinRoot ϖ (G1 O a) (by
    rw [map_G1]
    infer_instance)
  have e : J θ (R := R1 O a) = Ideal.span {algebraMap O (R1 O a) ϖ} := by
    rw [J, hk, Ideal.map_span, Set.image_singleton]
  exact isReduced_of_injective (Ideal.quotEquivOfEq e).toRingHom (Ideal.quotEquivOfEq e).injective

include hϖ hker in
/-- **The covering `C1` of `V₁ ⊗ k` is reduced** (étale over the reduced `R1/J`). -/
theorem isReduced_C1 : IsReduced Sp.C1 :=
  haveI := isReduced_Ts_R1 hϖ hker (a := a) hθ.out
  isReduced_of_etale_away _ (by rw [map_one]; exact isUnit_one) Sp.etale

variable {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)}
  (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
    LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
  (hB : ∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n))

/-- **The special fibre of the lift over `V₁` is the given covering**: `B₁ ⧸ (ϖ) ≃ C1`. -/
def specialFibreEquiv1 : B.Ring1 ⧸ Ideal.span {B.const1 ϖ} ≃+* Sp.C1 :=
  NodeEtaleGlue.Overlap.specialFibreEquiv1 (V := overlap Sp hϖ hker S0 ω hO) hθ.out hO rfl hα hB
    (J_Tn_zero_eq_bot hker _)

/-- **The special fibre of the lift over `V₀` is the given covering**: `B₀ ⧸ (ϖ) ≃ C0`. -/
def specialFibreEquiv0 : B.Ring0 ⧸ Ideal.span {B.const0 ϖ} ≃+* S0.C0 :=
  (overlap Sp hϖ hker S0 ω hO).specialFibreEquiv0 hθ.out hO rfl hα hB (J_Tn_zero_eq_bot hker _)
    (bottom0 Sp hϖ hker S0 ω hO)

/-- The special fibre of the lift over the overlap: `B₀₁ → C1[1/ȳ]`. -/
def specialFibre01 :=
  (overlap Sp hϖ hker S0 ω hO).specialFibre01 hθ.out hO (B := B) (α := α) rfl
    (J_Tn_zero_eq_bot hker _)

/-- **Restriction from `V₁` reduces to the localization** `C1 → C1[1/ȳ]`. -/
theorem specialFibre01_r1 (b : B.Ring1) :
    specialFibre01 Sp hϖ hker S0 ω hO (α := α) (B.r1Hom b) =
      algebraMap (input Sp hϖ hker).C1 _
        (specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB (Ideal.Quotient.mk _ b)) :=
  NodeEtaleGlue.Overlap.specialFibre01_r1 (overlap Sp hϖ hker S0 ω hO) hθ.out hO hα hB
    (J_Tn_zero_eq_bot hker _) rfl b

/-- **Restriction from `V₀` reduces to `C0 → C0[1/x̄] ≃ω C1[1/ȳ]`**: the glueing datum `ω` is the
reduction of the algebraized covering. -/
theorem specialFibre01_r0 (b : B.Ring0) :
    specialFibre01 Sp hϖ hker S0 ω hO (α := α) (B.r0Hom b) =
      (overlap Sp hϖ hker S0 ω hO).ω (algebraMap (overlap Sp hϖ hker S0 ω hO).C0 _
        (specialFibreEquiv0 Sp hϖ hker S0 ω hO hα hB (Ideal.Quotient.mk _ b))) :=
  NodeEtaleGlue.Overlap.specialFibre01_r0 (overlap Sp hϖ hker S0 ω hO) hθ.out hO hα hB
    (J_Tn_zero_eq_bot hker _) rfl (bottom0 Sp hϖ hker S0 ω hO) b

variable {ψ : ProjectiveLine.ChartModule.Hom (twoChart O a).chartModule N}
  (hψα : ∀ n, (α (n + 1)).comp ψ = structureMaps Sp hϖ hker S0 ω hO n)

include hψα in
/-- **The special fibre over `V₁` is linear over `ℙ¹_t`**: the reduction of the structure map is
`R1 → C1`. -/
theorem specialFibreEquiv1_ψ (r : R1 O a) :
    specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB (Ideal.Quotient.mk _ (ψ.f1 r)) =
      (letI := (input Sp hϖ hker).algC10 0
       algebraMap (input Sp hϖ hker).B0 (input Sp hϖ hker).C1 r) :=
  NodeEtaleGlue.Overlap.specialFibreEquiv1_ψ (overlap Sp hϖ hker S0 ω hO) hθ.out hO hα hB
    (J_Tn_zero_eq_bot hker _) (baseMap Sp hϖ hker S0 ω hO) rfl hψα r

include hψα in
/-- **The special fibre over `V₀` is linear over `ℙ¹_t`**: the reduction of the structure map is
`R0 → C0`. -/
theorem specialFibreEquiv0_ψ (r : R0 O a) :
    specialFibreEquiv0 Sp hϖ hker S0 ω hO hα hB (Ideal.Quotient.mk _ (ψ.f0 r)) =
      (letI := (overlap Sp hϖ hker S0 ω hO).algC0' 0
       algebraMap (overlap Sp hϖ hker S0 ω hO).B0' (overlap Sp hϖ hker S0 ω hO).C0 r) :=
  NodeEtaleGlue.Overlap.specialFibreEquiv0_ψ (overlap Sp hϖ hker S0 ω hO) hθ.out hO hα hB
    (J_Tn_zero_eq_bot hker _) (baseMap Sp hϖ hker S0 ω hO) rfl (bottom0 Sp hϖ hker S0 ω hO)
    hψα r

include hα hB in
/-- **Connected special cover ⇒ connected generic fibre of the lift**: if the covering `C1` of
`V₁ ⊗ k` has only the trivial idempotents, so has the generic fibre `B₁[1/ϖ]` (`C1` is reduced,
`isReduced_C1`). -/
theorem connected_lift_of_special [IsDomain O] (hϖ0 : ϖ ≠ 0)
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x1)]
    (hconn : ∀ e : Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1)
    {e : Localization.Away (B.const1 ϖ)} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  obtain ⟨f⟩ : Nonempty (B.Ring1 ⧸ Ideal.span {B.const1 ϖ} ≃+* Sp.C1) :=
    ⟨specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB⟩
  haveI := isReduced_C1 Sp hϖ hker
  refine connected_lift hϖ hϖ0 (isReduced_of_injective f.toRingHom f.injective)
    (fun x hx ↦ ?_) he
  rcases hconn (f x) (hx.map f) with h | h
  · left
    have h' := congrArg f.symm h
    rwa [RingEquiv.symm_apply_apply, map_zero] at h'
  · right
    have h' := congrArg f.symm h
    rwa [RingEquiv.symm_apply_apply, map_one] at h'

end

end P1Three

end SemistableReduction
