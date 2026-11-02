/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeFlat
import TemperedFundamentalGroups.SemistableReduction.P1ThreeDedekind
import TemperedFundamentalGroups.SemistableReduction.TateEtale

/-!
# The generic fibre of the lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` (MR13 A1)

For the M2 lift of a tame covering of `ℙ¹_k ∖ {0, 1, ā}` (given by `Sp`, `S0`, `ω`,
`P1ThreeGlue`) and its flat algebraization `(N, B, α)` (`P1Three.exists_flat_algebraization`):

* **`P1Three.baseMap`**: the model `P1Three.twoChart` maps to the charts of the covering by the
  identities (`R0 = B0'`, `R1 = B0`, `R01 = W0`), with structure maps `structureMaps n` of the
  levels; **`P1Three.exists_flat_algebraization_structureMap`**: the algebraization receives a
  morphism of chart algebras `ψ : twoChart.algStr → B` reducing to them (the structure map
  `𝒴 → ℙ¹_t` of the lifted covering);
* **`P1Three.kills_lift`**: `X` kills `Ω[B₀⁄R0]` and `Ω[B₁⁄R1] = 0`; hence
  **`P1Three.formallyUnramified_lift`**: `B₁` is formally unramified over `R1` — the lift is
  unramified over all of `V₁ = ℙ¹_O ∖ {0, 1, a}`, not only on the generic fibre (the covering of the
  special fibre has no marked points over `V₁`; the cusp patch lives over `V₀` and is killed by
  the cusp coordinate `X`, `CuspTower.kills_cuspPiece`);
* **`P1Three.etale_lift`** (`O` a discrete valuation ring): `B₁[1/ϖ]` is **étale over
  `R1[1/ϖ]`, the coordinate ring of `U_K = ℙ¹_K ∖ {0, 1, a}`** (`GenericEtale`, with the Dedekind
  property `P1Three.isDedekindDomain_away_R1_of_dvr`), and finite over it
  (**`P1Three.finite_lift`**).

So the generic fibre of the lift is a finite étale cover of `U_K`: the lifting step of the
"lifting half" of tame specialisation for `U = ℙ¹ ∖ {three points}` ([SGA1] XIII, proof of
Cor 2.12), cf. MR13-plan Route B, A1.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace P1Three

open TateLevel

noncomputable section

section Model

variable (O : Type u) [CommRing O] (a : O)

/-- The first chart module of the model is finite over `O[X]`. -/
theorem finite_x0 : Module.Finite O[X] (Module.AEval' (twoChart O a).chartModule.x0) :=
  TwoChartGlue.finite_aeval_mulLeft _ (finite_aeval_x0 O a)

/-- The second chart module of the model is finite over `O[X]`. -/
theorem finite_x1 : Module.Finite O[X] (Module.AEval' (twoChart O a).chartModule.x1) :=
  TwoChartGlue.finite_aeval_mulLeft _ (finite_aeval_y1 O a)

lemma aeval_y1 (p : O[X]) : aeval (y1 O a) p = algebraMap O[X] (R1 O a) p := by
  rw [y1, ← AdjoinRoot.algebraMap_eq, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]

lemma aeval_x0 (p : O[X]) : aeval (x0 O a) p = algebraMap O[X] (R0 O a) p := by
  rw [x0, ← AdjoinRoot.algebraMap_eq, Polynomial.aeval_algebraMap_apply, aeval_X_left_apply]

variable {O a}

/-- The structure map of the second chart composed with `O[X] → R1` is `polyHom1`. -/
lemma algR1_comp {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {ψ : ProjectiveLine.ChartModule.Hom (twoChart O a).chartModule N}
    (hψ : (twoChart O a).algStr.IsHom B ψ) :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    (algebraMap (R1 O a) B.Ring1).comp (algebraMap O[X] (R1 O a)) = B.polyHom1 := by
  refine RingHom.ext fun p ↦ ?_
  change hψ.ringHom1 ((ProjectiveLine.TwoChartRings.ring1Equiv (twoChart O a)).symm
    (algebraMap O[X] (R1 O a) p)) = _
  rw [← aeval_y1, show aeval (y1 O a) p = aeval (twoChart O a).y p from rfl,
    ProjectiveLine.ChartModule.AlgStr.ring1Equiv_symm_aeval, hψ.ringHom1_polyHom1]

end Model

/-- The completion along a unit is the zero ring. -/
lemma subsingleton_hat {R : Type u} [CommRing R] {f : R} (hf : IsUnit f) :
    Subsingleton (FormalPatchLevel.Hat f) := by
  have h : Ideal.span {f} = ⊤ := Ideal.span_singleton_eq_top.mpr hf
  refine ⟨fun x y ↦ AdicCompletion.ext fun n ↦ ?_⟩
  have : Subsingleton (R ⧸ (Ideal.span {f} ^ n • ⊤ : Submodule R R)) := by
    rw [h, Ideal.top_pow, Submodule.top_smul]
    exact Submodule.Quotient.subsingleton_iff.mpr rfl
  exact Subsingleton.elim _ _

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O] (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))
  (ω : OmegaC Sp S0.C0) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-! ### The structure map -/

/-- **The model maps to the charts of the covering by the identities** (`R0 = B0'`, `R1 = B0`,
`R01 = W0`). -/
def baseMap : NodeEtaleGlue.Overlap.BaseMap (overlap Sp hϖ hker S0 ω hO) (twoChart O a) where
  a0 := RingHom.id (R0 O a)
  a1 := RingHom.id (R1 O a)
  a01 := RingHom.id (R01 O a)
  hO0 _ := rfl
  hO1 _ := rfl
  hx := rfl
  hy := rfl
  h0 _ := rfl
  h1 _ := rfl

/-- **The structure maps of the levels of the covering to the model**, as maps into the level
`n + 1` of `system`. -/
def structureMaps (n : ℕ) :
    ProjectiveLine.ChartModule.Hom (twoChart O a).chartModule
      ((system Sp hϖ hker S0 ω hO).M (n + 1)) :=
  (baseMap Sp hϖ hker S0 ω hO).βS hθ.out hO n rfl

variable [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) O]
  (hϖ0 : ϖ ≠ 0)

include hϖ0 in
/-- **The structure map of the algebraized covering**: the flat algebraization `(N, B, α)`
(`exists_flat_algebraization`) receives a morphism of chart algebras `ψ` from the model
reducing to the structure maps of the levels. -/
theorem exists_flat_algebraization_structureMap :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n), ((system Sp hϖ hker S0 ω hO).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) ∧
      ∃ ψ : ProjectiveLine.ChartModule.Hom (twoChart O a).chartModule N,
        (twoChart O a).algStr.IsHom B ψ ∧
        ∀ n, (α (n + 1)).comp ψ = structureMaps Sp hϖ hker S0 ω hO n := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1⟩ :=
    exists_flat_algebraization Sp hϖ hker S0 ω hO hϖ0
  haveI := finite_x0 O a
  haveI := finite_x1 O a
  haveI : IsAdicComplete (Ideal.span {(overlap Sp hϖ hker S0 ω hO).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  exact ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1,
    (baseMap Sp hϖ hker S0 ω hO).exists_structureMap' hθ.out hO rfl hα hc hB⟩

/-! ### Differentials and étaleness -/

variable {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
  [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)}
  (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
    LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
  (hB : ∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n))
  {ψ : ProjectiveLine.ChartModule.Hom (twoChart O a).chartModule N}
  (hψ : (twoChart O a).algStr.IsHom B ψ)
  (hψα : ∀ n, (α (n + 1)).comp ψ = structureMaps Sp hϖ hker S0 ω hO n)

omit [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] in
include hα hB hψ hψα in
/-- **The differentials of the lift**: `X` kills `Ω[B₀⁄R0]` and `Ω[B₁⁄R1] = 0` (`1` kills it). -/
theorem kills_lift :
    (letI : Algebra (R0 O a) B.Ring0 := B.algR0 hψ;
      KaehlerLocal.Kills (R0 O a) (B.const0 1 * B.X0 ^ 1)) ∧
      (letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ;
        KaehlerLocal.Kills (R1 O a) (B.const1 1)) := by
  haveI : IsAdicComplete (Ideal.span {(overlap Sp hϖ hker S0 ω hO).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  have hG : ∀ n, KaehlerLocal.Kills ((input Sp hϖ hker).R n)
      (algebraMap ((input Sp hϖ hker).R n) ((input Sp hϖ hker).T.G hθ.out n)
        (algebraMap ((input Sp hϖ hker).B n) ((input Sp hϖ hker).R n)
          (algebraMap (input Sp hϖ hker).B0 ((input Sp hϖ hker).B n)
            (letI := (overlap Sp hϖ hker S0 ω hO).algOB0;
              algebraMap O (input Sp hϖ hker).B0 1)))) := fun n ↦ by
    haveI : Subsingleton (FormalPatchLevel.Hat ((input Sp hϖ hker).T.f n)) :=
      subsingleton_hat (by
        change IsUnit (Ideal.Quotient.mk _ (algebraMap (R1 O a) (Rc1 O a) 1))
        rw [map_one, map_one]
        exact isUnit_one)
    exact ((input Sp hϖ hker).T.level n).kills_G hθ.out hO (fun j ↦ isEmptyElim j)
      (fun _ ↦ ⟨0, Subsingleton.elim _ _⟩)
  have hP : ∀ n, KaehlerLocal.Kills ((overlap Sp hϖ hker S0 ω hO).B' n)
      (algebraMap ((overlap Sp hϖ hker S0 ω hO).B' n) ((overlap Sp hϖ hker S0 ω hO).P0.P n)
        (algebraMap (overlap Sp hϖ hker S0 ω hO).B0' ((overlap Sp hϖ hker S0 ω hO).B' n)
          (algebraMap O (overlap Sp hϖ hker S0 ω hO).B0' 1 *
            (overlap Sp hϖ hker S0 ω hO).x0 ^ 1))) := fun n ↦
    CuspTower.kills_cuspPiece S0 hϖ hker (isSMulRegular_x0 ϖ a) hO n 1 _
      (by rw [map_one, pow_one]; rfl)
  exact NodeEtaleGlue.Overlap.kills_shift hθ.out hO rfl hα hB (baseMap Sp hϖ hker S0 ω hO)
    (TateGlue0.formallyUnramified_id _) (TateGlue0.formallyUnramified_id _) hψ hψα le_rfl hG hP

omit [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] in
include hα hB hψ hψα in
/-- **The lift is unramified over `V₁ = ℙ¹_O ∖ {0, 1, a}`**: `B₁` is formally unramified over
`R1`. -/
theorem formallyUnramified_lift :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    Algebra.FormallyUnramified (R1 O a) B.Ring1 := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  have h := (kills_lift Sp hϖ hker S0 ω hO hα hB hψ hψα).2
  rw [map_one] at h
  exact ⟨⟨fun x y ↦ by rw [← one_smul B.Ring1 x, h x, ← one_smul B.Ring1 y, h y]⟩⟩

omit [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) O]
  [IsNoetherianRing O] [Module.Finite O[X] (Module.AEval' N.x0)] in
/-- `B₁` is finite over `R1`. -/
theorem finite_ring1 :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    Module.Finite (R1 O a) B.Ring1 := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI : Algebra O[X] B.Ring1 := B.polyHom1.toAlgebra
  haveI : IsScalarTower O[X] (R1 O a) B.Ring1 :=
    IsScalarTower.of_algebraMap_eq' (algR1_comp hψ).symm
  haveI := B.finite_polyHom1
  exact Module.Finite.of_restrictScalars_finite O[X] (R1 O a) B.Ring1

omit [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) O]
  [IsNoetherianRing O] [Module.Finite O[X] (Module.AEval' N.x0)]
  [Module.Finite O[X] (Module.AEval' N.x1)] in
/-- The structure map of the second chart on constants. -/
lemma algR1_const (c : O) :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    algebraMap (R1 O a) B.Ring1 (algebraMap O (R1 O a) c) = B.const1 c := by
  have h := RingHom.congr_fun (algR1_comp hψ) (C c)
  rw [RingHom.comp_apply, ← aeval_y1, aeval_C] at h
  rw [h]
  simp [ProjectiveLine.ChartModule.AlgStr.polyHom1]

omit [IsDomain O] [(Ideal.span {ϖ}).IsMaximal] [IsAdicComplete (Ideal.span {ϖ}) O]
  [IsNoetherianRing O] [Module.Finite O[X] (Module.AEval' N.x0)] in
/-- **The generic fibre of the lift is finite over `U_K`**: `B₁[1/ϖ]` is finite over `R1[1/ϖ]`
(for any algebra structure compatible with `ψ`). -/
theorem finite_lift :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    letI : Algebra (R1 O a) (Localization.Away (B.const1 ϖ)) :=
      ((algebraMap B.Ring1 _).comp (algebraMap (R1 O a) B.Ring1)).toAlgebra
    ∀ [Algebra (Localization.Away (algebraMap O (R1 O a) ϖ)) (Localization.Away (B.const1 ϖ))]
      [@IsScalarTower (R1 O a) (Localization.Away (algebraMap O (R1 O a) ϖ))
        (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
      Module.Finite (Localization.Away (algebraMap O (R1 O a) ϖ))
        (Localization.Away (B.const1 ϖ)) := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI : Algebra (R1 O a) (Localization.Away (B.const1 ϖ)) :=
    ((algebraMap B.Ring1 _).comp (algebraMap (R1 O a) B.Ring1)).toAlgebra
  haveI : @IsScalarTower (R1 O a) B.Ring1 (Localization.Away (B.const1 ϖ))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro _ _
  haveI := finite_ring1 hψ
  haveI : IsLocalization (Algebra.algebraMapSubmonoid B.Ring1
      (Submonoid.powers (algebraMap O (R1 O a) ϖ))) (Localization.Away (B.const1 ϖ)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    rw [algR1_const hψ]
    infer_instance
  exact Module.Finite.of_isLocalization (R1 O a) B.Ring1
    (Submonoid.powers (algebraMap O (R1 O a) ϖ))

variable [IsDiscreteValuationRing O]

omit [(Ideal.span {ϖ}).IsMaximal] in
include hα hB hψ hψα hϖ0 in
/-- **The generic fibre of the lift is étale over `U_K = ℙ¹_K ∖ {0, 1, a}`**: `B₁[1/ϖ]` is étale
over `R1[1/ϖ]` (for any algebra structure compatible with `ψ`). -/
theorem etale_lift [Module.Flat O[X] (Module.AEval' N.x1)] :
    letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
    letI : Algebra (R1 O a) (Localization.Away (B.const1 ϖ)) :=
      ((algebraMap B.Ring1 _).comp (algebraMap (R1 O a) B.Ring1)).toAlgebra
    ∀ [Algebra (Localization.Away (algebraMap O (R1 O a) ϖ)) (Localization.Away (B.const1 ϖ))]
      [@IsScalarTower (R1 O a) (Localization.Away (algebraMap O (R1 O a) ϖ))
        (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
      Algebra.Etale (Localization.Away (algebraMap O (R1 O a) ϖ))
        (Localization.Away (B.const1 ϖ)) := by
  letI : Algebra (R1 O a) B.Ring1 := B.algR1 hψ
  letI : Algebra (R1 O a) (Localization.Away (B.const1 ϖ)) :=
    ((algebraMap B.Ring1 _).comp (algebraMap (R1 O a) B.Ring1)).toAlgebra
  haveI : @IsScalarTower (R1 O a) B.Ring1 (Localization.Away (B.const1 ϖ))
      Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  intro _ _
  have hu : ¬IsUnit ϖ := fun hu ↦ by simpa [hϖ] using hu.map θ
  haveI := isDedekindDomain_away_R1_of_dvr hϖ0 hu a
  haveI := formallyUnramified_lift Sp hϖ hker S0 ω hO hα hB hψ hψα
  haveI : Algebra.FormallyUnramified (R1 O a) (Localization.Away (B.const1 ϖ)) :=
    haveI : Algebra.FormallyUnramified B.Ring1 (Localization.Away (B.const1 ϖ)) :=
      Algebra.FormallyUnramified.of_isLocalization (Submonoid.powers (B.const1 ϖ))
    Algebra.FormallyUnramified.comp (R1 O a) B.Ring1 _
  have hx : algebraMap O[X] (R1 O a) (C ϖ) = algebraMap O (R1 O a) ϖ := by
    rw [← aeval_y1, aeval_C]
  exact B.etale_away1 (C_ne_zero.2 hϖ0) hx _ (algR1_comp hψ) (B.const1 ϖ) _

end

end P1Three

end SemistableReduction
