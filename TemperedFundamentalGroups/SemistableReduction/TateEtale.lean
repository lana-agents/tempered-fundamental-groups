/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateKaehler
import TemperedFundamentalGroups.SemistableReduction.TateGenericFibre

/-!
# The generic fibre of the algebraized Tate coverings is étale (Blueprint §12.8, M2.5 (f))

For the flat algebraization `(N, B, α)` of a Tate covering with its structure map
`ψ : (TateTwoChart.twoChart ..).algStr → B` to the Tate model (`TateGlue0.exists_normalisedModel`,
`exists_normalisedModel_cusp`), where the covering of the node chart has no cusp factors
(`IsEmpty cov₀.κ`), the generic fibre of the covering is étale over the generic fibre of the Tate
model outside the cusp divisor:

* **`TateGlue0.etale_overlap`** (covering étale over `D(1 + h)`): `B₀[1/ϖ]` is étale over
  `T0[1/ϖ]` and `B₁[1/ϖ]` is étale over `T1[1/ϖ]`;
* **`TateGlue0.etale_overlapCusp`** (covering ramified at the cusp `h = 0`): `B₀[1/(ϖ X)]`
  (`X ↦ h`) is étale over `T0[1/(ϖ h)]` and `B₁[1/ϖ]` is étale over `T1[1/ϖ]`;
* **`TateGlue0.exists_etale_normalisedModel`**, **`exists_etale_normalisedModel_cusp`**: the
  normalised models of `exists_normalisedModel(_cusp)` together with these étaleness statements.

The algebra structure between the two localizations is any one compatible with the structure map
(it is unique: a localization map is an epimorphism).

The hypotheses are those of the Dedekind property of the generic fibre of the Tate model
(`TateTwoChart.isDedekindDomain_away_T0_of_dvr`): `O` a discrete valuation ring, `(3 : O) ≠ 0`,
and `TateNormal.tateE π b₄ b₆ ≠ 0` (the generic fibre is smooth; this is not implied by the
remaining hypotheses, e.g. `b₄ = b₆ = 0`, `t = κ = 1`); `π ≠ 0` and `ϖ` not a unit follow from
`π = ε ϖᵐ`, `ε` a unit, `ϖ ≠ 0` and `θ ϖ = 0`. For the actual Tate parameters (an elliptic curve
`y² + xy = x³ + π² b₄ x + π² b₆` over a field of characteristic zero, e.g. IUT's
`TateOrbicurve.IsTate`) both `(3 : O) ≠ 0` and `E ≠ 0` hold (`Δ = −π² E` is a unit:
`TateNormal.tateE_ne_zero_of_isElliptic`, `TateOrbicurve.IsTate.tateE_ne_zero`), and
**`TateGlue0.exists_etale_normalisedModel_of_isElliptic`**,
**`exists_etale_normalisedModel_cusp_of_isElliptic`** take the curve instead of these two
hypotheses.

## Proof

* **`GenericEtale.etale_away`** (generic): let `T` be a finite algebra over a domain `P`, `S` a
  finite flat `P`-algebra with a compatible `T`-algebra structure, `p ≠ 0` in `P`, `T'` the
  localization of `T` away from `p`, and `S'` a localization of `S` away from some element which
  is formally unramified over `T`. If `T'` is a Dedekind domain, `S'` is étale over `T'`:
  formally unramified over `T'` (`Algebra.FormallyUnramified.of_restrictScalars`), of finite
  presentation (finite type over the noetherian `T'`), and flat: `S'` is flat over `P[1/p]`
  (`Module.flat_iff_of_isLocalization`), `T'` is integral over `P[1/p]`
  (`isIntegral_localization`), hence `S'` is flat over the Dedekind domain `T'`
  (`PlaneCurve.flat_of_isIntegral`); then `Algebra.Etale.of_formallyUnramified_of_flat`.
* `P = O[X]`, `T = T_i`, `S = B_i` with the `O[X]`-structure `polyHom` (finite and flat:
  `AlgStr.finite_polyHom0`, **`AlgStr.flat_polyHom0`**), `p = ϖ` (resp. `ϖ X` on the cusp chart);
  formal unramifiedness is `TateGlue0.formallyUnramified_overlap(Cusp)`, the Dedekind property
  `TateTwoChart.isDedekindDomain_away_T0_of_dvr` (and its localization at `h` on the cusp chart).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace GenericEtale

variable {P T : Type u} [CommRing P] [IsDomain P] [CommRing T] [Algebra P T] [Module.Finite P T]
  {p : P} (hp : p ≠ 0) {x : T} (hx : algebraMap P T p = x)
  (T' : Type u) [CommRing T'] [Algebra T T'] [IsLocalization.Away x T'] [IsDedekindDomain T']

include hp hx in
/-- **Generic étaleness of a finite flat cover.** -/
theorem etale_away (S : Type u) [CommRing S] [Algebra T S] [Algebra P S] [IsScalarTower P T S]
    [Module.Finite P S] [Module.Flat P S] (s : S) (S' : Type u) [CommRing S'] [Algebra S S']
    [IsLocalization.Away s S'] [Algebra T S'] [IsScalarTower T S S'] [Algebra T' S']
    [IsScalarTower T T' S'] [Algebra.FormallyUnramified T S'] : Algebra.Etale T' S' := by
  subst hx
  haveI : Algebra.FormallyUnramified T' S' := Algebra.FormallyUnramified.of_restrictScalars T T' S'
  -- finite presentation
  haveI : Algebra.FiniteType T S := Algebra.FiniteType.of_restrictScalars_finiteType P T S
  haveI : Algebra.FinitePresentation S S' := IsLocalization.Away.finitePresentation (S := S') s
  haveI : Algebra.FiniteType T S' := Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  haveI : Algebra.FiniteType T' S' := Algebra.FiniteType.of_restrictScalars_finiteType T T' S'
  haveI : Algebra.FinitePresentation T' S' := Algebra.FinitePresentation.of_finiteType.mp
    inferInstance
  -- flatness
  let P' := Localization.Away p
  haveI : IsDomain P' :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hp)
  letI : Algebra P' T' := (IsLocalization.Away.map P' T' (algebraMap P T) p).toAlgebra
  letI : Algebra P' S' := ((algebraMap T' S').comp (algebraMap P' T')).toAlgebra
  haveI : IsScalarTower P' T' S' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsLocalization (Algebra.algebraMapSubmonoid T (Submonoid.powers p)) T' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  haveI : Algebra.IsIntegral P T := Algebra.IsIntegral.of_finite P T
  have hi := isIntegral_localization (R := P) (S := T) (M := Submonoid.powers p) (Rₘ := P')
    (Sₘ := T')
  haveI : Algebra.IsIntegral P' T' := ⟨fun y ↦ hi y⟩
  letI : Algebra P S' := ((algebraMap S S').comp (algebraMap P S)).toAlgebra
  haveI : IsScalarTower P S S' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower P P' S' := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change algebraMap S S' (algebraMap P S a) =
      algebraMap T' S' (IsLocalization.Away.map P' T' (algebraMap P T) p (algebraMap P P' a))
    rw [IsLocalization.Away.map, IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply T T' S',
      IsScalarTower.algebraMap_apply P T S, ← IsScalarTower.algebraMap_apply T S S']
  haveI : Module.Flat S S' := IsLocalization.flat S' (Submonoid.powers s)
  haveI : Module.Flat P S' := Module.Flat.trans P S S'
  haveI : Module.Flat P' S' :=
    (Module.flat_iff_of_isLocalization P' (Submonoid.powers p) S').mpr inferInstance
  haveI : Module.Flat T' S' := PlaneCurve.flat_of_isIntegral P' T' S'
  exact Algebra.Etale.of_formallyUnramified_of_flat

end GenericEtale

end SemistableReduction

namespace ProjectiveLine

namespace ChartModule

namespace AlgStr

variable {A : Type u} [CommRing A] {M : ChartModule A} (B : AlgStr M)

/-- `B₀` is a flat `A[X]`-algebra (through `polyHom0`) if `M₀` is a flat `A[X]`-module. -/
theorem flat_polyHom0 [Module.Flat A[X] (Module.AEval' M.x0)] :
    letI := B.polyHom0.toAlgebra
    Module.Flat A[X] B.Ring0 := by
  letI := B.polyHom0.toAlgebra
  let f : Module.AEval' M.x0 →ₗ[A[X]] B.Ring0 :=
    { toFun := fun v ↦ B.toRing0 ((Module.AEval'.of M.x0).symm v)
      map_add' := fun v w ↦ by rw [map_add]; rfl
      map_smul' := fun p v ↦ by
        rw [Module.AEval.of_symm_smul, RingHom.id_apply, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        exact B.toRing0_aeval p _ }
  have hf : Function.Bijective f := by
    refine ⟨fun v w h ↦ (Module.AEval'.of M.x0).symm.injective h, fun m ↦
      ⟨Module.AEval'.of M.x0 (B.ofRing0 m), ?_⟩⟩
    change B.toRing0 ((Module.AEval'.of M.x0).symm (Module.AEval'.of M.x0 (B.ofRing0 m))) = m
    rw [LinearEquiv.symm_apply_apply]
    rfl
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective f hf).symm

/-- `B₁` is a flat `A[X]`-algebra (through `polyHom1`) if `M₁` is a flat `A[X]`-module. -/
theorem flat_polyHom1 [Module.Flat A[X] (Module.AEval' M.x1)] :
    letI := B.polyHom1.toAlgebra
    Module.Flat A[X] B.Ring1 := by
  letI := B.polyHom1.toAlgebra
  let f : Module.AEval' M.x1 →ₗ[A[X]] B.Ring1 :=
    { toFun := fun v ↦ B.toRing1 ((Module.AEval'.of M.x1).symm v)
      map_add' := fun v w ↦ by rw [map_add]; rfl
      map_smul' := fun p v ↦ by
        rw [Module.AEval.of_symm_smul, RingHom.id_apply, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        exact B.toRing1_aeval p _ }
  have hf : Function.Bijective f := by
    refine ⟨fun v w h ↦ (Module.AEval'.of M.x1).symm.injective h, fun m ↦
      ⟨Module.AEval'.of M.x1 (B.ofRing1 m), ?_⟩⟩
    change B.toRing1 ((Module.AEval'.of M.x1).symm (Module.AEval'.of M.x1 (B.ofRing1 m))) = m
    rw [LinearEquiv.symm_apply_apply]
    rfl
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective f hf).symm

variable [IsDomain A] {T : Type u} [CommRing T] [Algebra A[X] T] [Module.Finite A[X] T]
  {q : A[X]} (hq : q ≠ 0) {x : T} (hx : algebraMap A[X] T q = x)
  (T' : Type u) [CommRing T'] [Algebra T T'] [IsLocalization.Away x T'] [IsDedekindDomain T']

include hq hx in
/-- **Generic étaleness on the first chart**: if `T` is a finite `A[X]`-algebra through which
`polyHom0` factors, `B₀[1/s]` is formally unramified over `T`, and `T' = T[1/q]` (`q ∈ A[X]`
nonzero) is a Dedekind domain, then `B₀[1/s]` is étale over `T'`. -/
theorem etale_away0 [Module.Finite A[X] (Module.AEval' M.x0)]
    [Module.Flat A[X] (Module.AEval' M.x0)] [Algebra T B.Ring0]
    (hT : (algebraMap T B.Ring0).comp (algebraMap A[X] T) = B.polyHom0) (s : B.Ring0)
    (S' : Type u) [CommRing S'] [Algebra B.Ring0 S'] [IsLocalization.Away s S'] [Algebra T S']
    [IsScalarTower T B.Ring0 S'] [Algebra T' S'] [IsScalarTower T T' S']
    [Algebra.FormallyUnramified T S'] : Algebra.Etale T' S' := by
  letI : Algebra A[X] B.Ring0 := B.polyHom0.toAlgebra
  haveI : IsScalarTower A[X] T B.Ring0 := IsScalarTower.of_algebraMap_eq' hT.symm
  haveI := B.finite_polyHom0
  haveI := B.flat_polyHom0
  exact SemistableReduction.GenericEtale.etale_away hq hx T' B.Ring0 s S'

include hq hx in
/-- **Generic étaleness on the second chart** (as `etale_away0`). -/
theorem etale_away1 [Module.Finite A[X] (Module.AEval' M.x1)]
    [Module.Flat A[X] (Module.AEval' M.x1)] [Algebra T B.Ring1]
    (hT : (algebraMap T B.Ring1).comp (algebraMap A[X] T) = B.polyHom1) (s : B.Ring1)
    (S' : Type u) [CommRing S'] [Algebra B.Ring1 S'] [IsLocalization.Away s S'] [Algebra T S']
    [IsScalarTower T B.Ring1 S'] [Algebra T' S'] [IsScalarTower T T' S']
    [Algebra.FormallyUnramified T S'] : Algebra.Etale T' S' := by
  letI : Algebra A[X] B.Ring1 := B.polyHom1.toAlgebra
  haveI : IsScalarTower A[X] T B.Ring1 := IsScalarTower.of_algebraMap_eq' hT.symm
  haveI := B.finite_polyHom1
  haveI := B.flat_polyHom1
  exact SemistableReduction.GenericEtale.etale_away hq hx T' B.Ring1 s S'

end AlgStr

end ChartModule

end ProjectiveLine

namespace SemistableReduction

namespace TateTwoChart

variable {O : Type u} [CommRing O] (π b₄ t κ : O)

/-- The `O[X]`-algebra structure of `T0` is evaluation at `h`. -/
lemma algebraMap_T0 (p : O[X]) : algebraMap O[X] (T0 π b₄ t κ) p = aeval (h0 π b₄ t κ) p := by
  rw [h0, ← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, aeval_X_left_apply]

/-- The `O[X]`-algebra structure of `T1` is evaluation at `h'`. -/
lemma algebraMap_T1 (p : O[X]) : algebraMap O[X] (T1 π b₄ t κ) p = aeval (h1 π b₄ t κ) p := by
  rw [h1, ← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, aeval_X_left_apply]

lemma algebraMap_C_T0 (a : O) :
    algebraMap O[X] (T0 π b₄ t κ) (C a) = algebraMap O (T0 π b₄ t κ) a := by
  rw [AdjoinRoot.algebraMap_eq, of_C]

lemma algebraMap_C_T1 (a : O) :
    algebraMap O[X] (T1 π b₄ t κ) (C a) = algebraMap O (T1 π b₄ t κ) a := by
  rw [AdjoinRoot.algebraMap_eq, of_C]

lemma algebraMap_C_mul_X_T0 (a : O) :
    algebraMap O[X] (T0 π b₄ t κ) (C a * X) = algebraMap O (T0 π b₄ t κ) a * h0 π b₄ t κ := by
  rw [map_mul, algebraMap_C_T0, AdjoinRoot.algebraMap_eq]

variable {π b₄ t κ}

/-- The structure map of the first chart composed with `O[X] → T0` is `polyHom0`. -/
lemma algR0_comp {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {ψ : ProjectiveLine.ChartModule.Hom (twoChart π b₄ t κ).chartModule N}
    (hψ : (twoChart π b₄ t κ).algStr.IsHom B ψ) :
    letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
    (algebraMap (T0 π b₄ t κ) B.Ring0).comp (algebraMap O[X] (T0 π b₄ t κ)) = B.polyHom0 := by
  refine RingHom.ext fun p ↦ ?_
  change hψ.ringHom0 ((ProjectiveLine.TwoChartRings.ring0Equiv (twoChart π b₄ t κ)).symm
    (algebraMap O[X] (T0 π b₄ t κ) p)) = _
  rw [algebraMap_T0]
  rw [show aeval (h0 π b₄ t κ) p = aeval (twoChart π b₄ t κ).x p from rfl,
    ProjectiveLine.ChartModule.AlgStr.ring0Equiv_symm_aeval, hψ.ringHom0_polyHom0]

/-- The structure map of the second chart composed with `O[X] → T1` is `polyHom1`. -/
lemma algR1_comp {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
    {ψ : ProjectiveLine.ChartModule.Hom (twoChart π b₄ t κ).chartModule N}
    (hψ : (twoChart π b₄ t κ).algStr.IsHom B ψ) :
    letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ
    (algebraMap (T1 π b₄ t κ) B.Ring1).comp (algebraMap O[X] (T1 π b₄ t κ)) = B.polyHom1 := by
  refine RingHom.ext fun p ↦ ?_
  change hψ.ringHom1 ((ProjectiveLine.TwoChartRings.ring1Equiv (twoChart π b₄ t κ)).symm
    (algebraMap O[X] (T1 π b₄ t κ) p)) = _
  rw [algebraMap_T1]
  rw [show aeval (h1 π b₄ t κ) p = aeval (twoChart π b₄ t κ).y p from rfl,
    ProjectiveLine.ChartModule.AlgStr.ring1Equiv_symm_aeval, hψ.ringHom1_polyHom1]

variable [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0)

include hϖ in
/-- `h` is nonzero in the generic fibre `T0[1/ϖ]`. -/
lemma algebraMap_h0_ne_zero :
    algebraMap (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (h0 π b₄ t κ) ≠
      0 := by
  intro h
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (algebraMap O (T0 π b₄ t κ) ϖ)) _ _).mp h
  have hdeg : (G0 π b₄ t κ).degree ≠ 0 := by
    have h3 : (G0 π b₄ t κ).natDegree = 3 := by
      unfold G0
      compute_degree!
    rw [degree_eq_natDegree (monic_G0 π b₄ t κ).ne_zero, h3]
    decide
  have e : AdjoinRoot.of (G0 π b₄ t κ) (C ϖ ^ n * X) = AdjoinRoot.of (G0 π b₄ t κ) 0 := by
    rw [map_mul, map_pow, of_C, map_zero]
    exact hn
  exact mul_ne_zero (pow_ne_zero n (C_ne_zero.2 hϖ)) X_ne_zero
    (AdjoinRoot.of.injective_of_degree_ne_zero hdeg e)

include hϖ in
/-- **The generic fibre of the Tate model outside the cusp divisor**: if `T0[1/ϖ]` is a Dedekind
domain, so is `T0[1/(ϖ h)]`. -/
theorem isDedekindDomain_away_mul_h0
    [IsDedekindDomain (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))] :
    IsDedekindDomain (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ)) := by
  set D := Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)
  have hle := powers_le_nonZeroDivisors_of_noZeroDivisors (algebraMap_h0_ne_zero (π := π)
    (b₄ := b₄) (t := t) (κ := κ) hϖ)
  haveI : IsDomain (Localization.Away (algebraMap (T0 π b₄ t κ) D (h0 π b₄ t κ))) :=
    IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain (Localization.Away (algebraMap (T0 π b₄ t κ) D (h0 π b₄ t κ))) :=
    IsLocalization.isDedekindDomain D hle _
  exact PlaneCurve.isDedekindDomain_of_ringEquiv (IsLocalization.algEquiv
    (Submonoid.powers (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ)) _
    (Localization.Away (algebraMap (T0 π b₄ t κ) D (h0 π b₄ t κ)))).toRingEquiv

end TateTwoChart

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsAdicComplete (Ideal.span {ϖ}) O]
  [IsEmpty cov₀.κ] [IsDomain O] [IsDiscreteValuationRing O]
  (hϖ0 : ϖ ≠ 0) (h3 : (3 : O) ≠ 0) (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)

omit [IsNoetherianRing O] [IsAdicComplete (Ideal.span {ϖ}) O] [IsEmpty cov₀.κ]
  [IsDiscreteValuationRing O] in
include hπ hε hϖ0 in
lemma pi_ne_zero : π ≠ 0 :=
  hπ ▸ mul_ne_zero (right_ne_zero_of_mul_eq_one hε) (pow_ne_zero _ hϖ0)

omit [IsNoetherianRing O] [IsAdicComplete (Ideal.span {ϖ}) O] [IsEmpty cov₀.κ] [IsDomain O]
  [IsDiscreteValuationRing O] hθ in
include hϖ in
lemma not_isUnit_varpi : ¬IsUnit ϖ := fun hu ↦ by
  simpa [hϖ] using hu.map θ

include hπ' hm hϖ0 h3 hE in
/-- **M2.5 (f) for the Tate covering étale over `D(1 + h)`: the generic fibre is étale.** For the
flat algebraization of `exists_normalisedModel` with its structure map `ψ`, `B₀[1/ϖ]` is étale over
`T0[1/ϖ]` and `B₁[1/ϖ]` is étale over `T1[1/ϖ]` (for any algebra structure compatible with `ψ`). -/
theorem etale_overlap (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x0)]
    [Module.Flat O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n))
    {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N}
    (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = structureMaps hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω n) :
    (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
      letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
        ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
      ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
          (Localization.Away (B.const0 ϖ))]
        [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
          (Localization.Away (B.const0 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
          (Localization.Away (B.const0 ϖ))) ∧
    (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
      letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
        ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
      ∀ [Algebra (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
          (Localization.Away (B.const1 ϖ))]
        [@IsScalarTower (T1 π b₄ t κ) (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
          (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
          (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨hu0, hu1⟩ :=
    formallyUnramified_overlap hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω hα hB hψ hψα
  have hπ0 := pi_ne_zero hπ hε hϖ0
  have hu := not_isUnit_varpi hϖ
  haveI := isDedekindDomain_away_T0_of_dvr (t := t) (κ := κ) hϖ0 hu hκ h3 hπ0 hE
  haveI := isDedekindDomain_away_T1_of_dvr (t := t) (κ := κ) hϖ0 hu hκ h3 hπ0 hE
  constructor
  · letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
    letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
      ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra
    haveI : @IsScalarTower (T0 π b₄ t κ) B.Ring0 (Localization.Away (B.const0 ϖ))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    intro _ _
    haveI := hu0
    exact B.etale_away0 (C_ne_zero.2 hϖ0) (algebraMap_C_T0 π b₄ t κ ϖ) _ (algR0_comp hψ)
      (B.const0 ϖ) _
  · letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ
    letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
      ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra
    haveI : @IsScalarTower (T1 π b₄ t κ) B.Ring1 (Localization.Away (B.const1 ϖ))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    intro _ _
    haveI := hu1
    exact B.etale_away1 (C_ne_zero.2 hϖ0) (algebraMap_C_T1 π b₄ t κ ϖ) _ (algR1_comp hψ)
      (B.const1 ϖ) _

include hπ' hm hϖ0 h3 hE in
/-- **M2.5 (f) for the Tate covering ramified at the cusp: the generic fibre is étale outside the
cusp divisor.** For the flat algebraization of `exists_normalisedModel_cusp` with its structure
map `ψ`, `B₀[1/(ϖ X)]` (`X ↦ h`) is étale over `T0[1/(ϖ h)]` and `B₁[1/ϖ]` is étale over
`T1[1/ϖ]` (for any algebra structure compatible with `ψ`). -/
theorem etale_overlapCusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x0)]
    [Module.Flat O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N
      ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n))
    {ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N}
    (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n) :
    (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
      letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ * B.X0)) :=
        ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
      ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
          (Localization.Away (B.const0 ϖ * B.X0))]
        [@IsScalarTower (T0 π b₄ t κ)
          (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
          (Localization.Away (B.const0 ϖ * B.X0)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
          (Localization.Away (B.const0 ϖ * B.X0))) ∧
    (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
      letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
        ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
      ∀ [Algebra (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
          (Localization.Away (B.const1 ϖ))]
        [@IsScalarTower (T1 π b₄ t κ) (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
          (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
          (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨hu0, hu1⟩ :=
    formallyUnramified_overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω hα hB hψ hψα
  have hπ0 := pi_ne_zero hπ hε hϖ0
  have hu := not_isUnit_varpi hϖ
  haveI := isDedekindDomain_away_T0_of_dvr (t := t) (κ := κ) hϖ0 hu hκ h3 hπ0 hE
  haveI := isDedekindDomain_away_T1_of_dvr (t := t) (κ := κ) hϖ0 hu hκ h3 hπ0 hE
  haveI := isDedekindDomain_away_mul_h0 (π := π) (b₄ := b₄) (t := t) (κ := κ) hϖ0
  constructor
  · letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
    letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ * B.X0)) :=
      ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra
    haveI : @IsScalarTower (T0 π b₄ t κ) B.Ring0 (Localization.Away (B.const0 ϖ * B.X0))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    intro _ _
    haveI := hu0
    exact B.etale_away0 (mul_ne_zero (C_ne_zero.2 hϖ0) X_ne_zero)
      (algebraMap_C_mul_X_T0 π b₄ t κ ϖ) _ (algR0_comp hψ) (B.const0 ϖ * B.X0) _
  · letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ
    letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
      ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra
    haveI : @IsScalarTower (T1 π b₄ t κ) B.Ring1 (Localization.Away (B.const1 ϖ))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    intro _ _
    haveI := hu1
    exact B.etale_away1 (C_ne_zero.2 hϖ0) (algebraMap_C_T1 π b₄ t κ ϖ) _ (algR1_comp hψ)
      (B.const1 ϖ) _

include hπ' hm hϖ0 h3 hE in
/-- **M2.5 (e), (f) for the Tate covering étale over `D(1 + h)`.** The normalised model of
`exists_normalisedModel` (flat algebraization `(N, B, α)` with structure map `ψ`, `B_i` the
integral closure of `T_i` in `B_i[1/ϖ]`) whose generic fibre is étale over the generic fibre of
the Tate model: `B_i[1/ϖ]` is étale over `T_i[1/ϖ]` (`etale_overlap`). -/
theorem exists_etale_normalisedModel [(Ideal.span {ϖ}).IsMaximal] (Sp0 : Special0 θ π b₄ t κ)
    (ω : Omega hκ hπ Sp Sp0) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) ∧
      ∃ (ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N)
        (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ),
        (∀ n, (α (n + 1)).comp ψ = structureMaps hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω n) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          IsIntegralClosure B.Ring0 (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          IsIntegralClosure B.Ring1 (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
              (Localization.Away (B.const0 ϖ))]
            [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
              (Localization.Away (B.const0 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
                (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ))]
            [@IsScalarTower (T1 π b₄ t κ) (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
                (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, hi0, hi1⟩ :=
    exists_normalisedModel hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sp0 ω
  haveI := hf0
  haveI := hf1
  obtain ⟨he0, he1⟩ := etale_overlap hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 h3 hE Sp0 ω hα hB hψ hψα
  exact ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, hi0, hi1, he0, he1⟩

include hπ' hm hϖ0 h3 hE in
/-- **M2.5 (e), (f) for the Tate covering ramified at the cusp.** The normalised model of
`exists_normalisedModel_cusp` whose generic fibre is étale over the generic fibre of the Tate model
outside the cusp divisor: `B₀[1/(ϖ X)]` over `T0[1/(ϖ h)]` and `B₁[1/ϖ]` over `T1[1/ϖ]`
(`etale_overlapCusp`). -/
theorem exists_etale_normalisedModel_cusp [(Ideal.span {ϖ}).IsMaximal]
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) ∧
      ∃ (ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N)
        (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ),
        (∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          IsIntegralClosure B.Ring0 (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          IsIntegralClosure B.Ring1 (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ * B.X0)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
              (Localization.Away (B.const0 ϖ * B.X0))]
            [@IsScalarTower (T0 π b₄ t κ)
              (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
              (Localization.Away (B.const0 ϖ * B.X0)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
                (Localization.Away (B.const0 ϖ * B.X0))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ))]
            [@IsScalarTower (T1 π b₄ t κ) (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
                (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, hi0, hi1⟩ :=
    exists_normalisedModel_cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 Sc ω
  haveI := hf0
  haveI := hf1
  obtain ⟨he0, he1⟩ := etale_overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 h3 hE Sc ω
    hα hB hψ hψα
  exact ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, hi0, hi1, he0, he1⟩

include hπ' hm hϖ0 in
/-- **`exists_etale_normalisedModel` for the actual Tate parameters.** If `π, b₄, b₆` are the
parameters of an elliptic curve `W : y² + xy = x³ + π² b₄ x + π² b₆` over a field `K` of
characteristic zero receiving `O` (for IUT: `TateOrbicurve.IsTate`, `K = Frac O`), the hypotheses
`(3 : O) ≠ 0` and `TateNormal.tateE π b₄ b₆ ≠ 0` of `exists_etale_normalisedModel` hold
(`TateNormal.three_ne_zero_of_charZero`, `TateNormal.tateE_ne_zero_of_isElliptic`). -/
theorem exists_etale_normalisedModel_of_isElliptic [(Ideal.span {ϖ}).IsMaximal]
    {K : Type*} [Field K] [CharZero K] (φ : O →+* K) (W : WeierstrassCurve K) [W.IsElliptic]
    (h₁ : W.a₁ = 1) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = φ (π ^ 2 * b₄))
    (h₆ : W.a₆ = φ (π ^ 2 * b₆)) (Sp0 : Special0 θ π b₄ t κ)
    (ω : Omega hκ hπ Sp Sp0) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((system hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) ∧
      ∃ (ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N)
        (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ),
        (∀ n, (α (n + 1)).comp ψ = structureMaps hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω n) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          IsIntegralClosure B.Ring0 (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          IsIntegralClosure B.Ring1 (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
              (Localization.Away (B.const0 ϖ))]
            [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
              (Localization.Away (B.const0 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
                (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ))]
            [@IsScalarTower (T1 π b₄ t κ) (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
                (Localization.Away (B.const1 ϖ))) :=
  exists_etale_normalisedModel hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0
    (TemperedFundamentalGroups.TateNormal.three_ne_zero_of_charZero φ)
    (TemperedFundamentalGroups.TateNormal.tateE_ne_zero_of_isElliptic φ W h₁ h₂ h₃ h₄ h₆) Sp0 ω

include hπ' hm hϖ0 in
/-- **`exists_etale_normalisedModel_cusp` for the actual Tate parameters** (an elliptic curve
`W : y² + xy = x³ + π² b₄ x + π² b₆` over a field of characteristic zero receiving `O`). -/
theorem exists_etale_normalisedModel_cusp_of_isElliptic [(Ideal.span {ϖ}).IsMaximal]
    {K : Type*} [Field K] [CharZero K] (φ : O →+* K) (W : WeierstrassCurve K) [W.IsElliptic]
    (h₁ : W.a₁ = 1) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = φ (π ^ 2 * b₄))
    (h₆ : W.a₆ = φ (π ^ 2 * b₆))
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) :
    ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ m n (h : m ≤ n),
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).tr h).comp (α n) = α m) ∧
      (∀ n, B.IsHom ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).alg n) (α n)) ∧
      Module.Flat O[X] (Module.AEval' N.x0) ∧ Module.Flat O[X] (Module.AEval' N.x1) ∧
      ∃ (ψ : ProjectiveLine.ChartModule.Hom (TateTwoChart.twoChart π b₄ t κ).chartModule N)
        (hψ : (TateTwoChart.twoChart π b₄ t κ).algStr.IsHom B ψ),
        (∀ n, (α (n + 1)).comp ψ = structureMapsCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω n) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          IsIntegralClosure B.Ring0 (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          IsIntegralClosure B.Ring1 (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) ∧
        (letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ;
          letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ * B.X0)) :=
            ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
              (Localization.Away (B.const0 ϖ * B.X0))]
            [@IsScalarTower (T0 π b₄ t κ)
              (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
              (Localization.Away (B.const0 ϖ * B.X0)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * h0 π b₄ t κ))
                (Localization.Away (B.const0 ϖ * B.X0))) ∧
        (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
          letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
            ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
          ∀ [Algebra (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ))]
            [@IsScalarTower (T1 π b₄ t κ) (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
              (Localization.Away (B.const1 ϖ)) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
            Algebra.Etale (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))
                (Localization.Away (B.const1 ϖ))) :=
  exists_etale_normalisedModel_cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0
    (TemperedFundamentalGroups.TateNormal.three_ne_zero_of_charZero φ)
    (TemperedFundamentalGroups.TateNormal.tateE_ne_zero_of_isElliptic φ W h₁ h₂ h₃ h₄ h₆) Sc ω

end TateGlue0

end SemistableReduction
