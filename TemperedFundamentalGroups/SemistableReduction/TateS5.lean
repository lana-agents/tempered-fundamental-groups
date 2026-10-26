/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateEtale
import TemperedFundamentalGroups.SemistableReduction.TateAffineCusp
import TemperedFundamentalGroups.SemistableReduction.TateSpecial1
import TemperedFundamentalGroups.SemistableReduction.TateCuspSpecial
import TemperedFundamentalGroups.SemistableReduction.TateOmegaNorm

/-!
# The special-fibre data of a tame cover of the Tate curve (MR12 S5, instantiation)

Let `O` be a complete discrete valuation ring of characteristic zero (uniformizer `ϖ`, residue
field `k` algebraically closed), `π = ε ϖᵐ` (`ε` a unit, `m = q M'`), `T0`, `T1` the two charts
of the Tate model with overlap `T01`, node chart `NR = T1[1/D]` and cusp chart `Rc = T0[1/(1 + h)]`,
`K` their common function field and `L / K` a finite Galois extension with
`[L : K]` prime to `q` and dividing `e`, `μ_{M'}, μ_e ⊆ K`, `M'` and `e` invertible in `k`. Let
`B₀`, `B₁` be the normalisations of `T0`, `T1` in `L`, `Bn = B₁[1/D]` and `Bc = B₀[1/(1 + h)]`.

**Hypothesis `hunr` (debt D3/A1, stated once on the two charts):** `B₀`, `B₁` are unramified
over `T0`, `T1` at every prime whose contraction `p` lies strictly inside a maximal ideal
containing `ϖ`, except (on `T0`) for `p = (h, z)`, the origin section (the cusp).

Then:

* **`TateS5.sp`** `= TateGlue1.special1` (the special-fibre covering over `V₁`), **`TateS5.sc`**
  `= TateCuspCov.cuspSpecial` (over the cusp chart), **`TateS5.om`** `= TateGlue0.omegaNormC`
  (the overlap datum), with `TateS5.sc_cuspOverOrigin`;
* `TateS5.hunr_Bc`: the hypothesis `hunr` of the cusp chart from the global one (at a point
  `𝔪 ∋ z` of the special fibre, `(h, z) = (h)` locally since `z q₀ = π κ h (b₄ z² + h²)` and `q₀`
  is a unit at `𝔪`);
* `TateS5.covTate_e_dvd`: the ramification indices over the nodes divide `M'` (hence `m`), so
  `π' j = ϖ^(m / e j)` is an `e j`-th root of `ϖᵐ`;
* **`TateS5.exists_etale_normalisedModel`**: the M2 lift of these data
  (`TateGlue0.exists_etale_normalisedModel_cusp_of_isElliptic`) for the actual Tate parameters
  (an elliptic curve `y² + xy = x³ + π² b₄ x + π² b₆` over a field of characteristic zero
  receiving `O`), together with T1a: the glued generic fibre is finite étale over `E ∖ {0}`
  (`TateAffine.finite_etale_gluedK_cusp`).

`IsUnit b₆` (lead decision (i) after continuation 31) excludes the 3-gon case of the special
fibre of the cusp chart. It holds for IUT's curves: `q_v` has a `2l`-th root ([IUTchI],
Example 3.2, (iv)), so `v(q_v)` is even and the normal form `a₆ = ϖ^(2k) ε` gives the Tate
presentation `π = ϖᵏ`, `b₆ = ε` a unit (`TateOrbicurve.isTate_isUnit_of_normalForm_even`).

The data `sp`, `sc`, `om` are definitions all the way down to the chosen local Kummer data at the
nodes and the cusp (`FormalKummer.KummerNormAtData`, `FormalKummer.CuspNormAtData`; refactor R1),
so that the level-`n` Kummer forms of S6 can be compared with their `kummer` fields.
-/

universe u

open Module Polynomial

namespace SemistableReduction

namespace TateS5

open TateTwoChart TateTwoChartNode TateGlue0 TateLevel
open AdmissibleLift (J)
open FormalKummer (Cs)

noncomputable section

section Hunr

variable {O : Type u} [CommRing O] {π b₄ t κ b₆ : O} (hκ : κ * (t ^ 2 - b₆) = 1)
  {B₀ : Type u} [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀]
  {B : Type u} [CommRing B] [Algebra (RcT π b₄ t κ) B] [Algebra B₀ B]
  [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
  (hB : ∀ x, algebraMap (RcT π b₄ t κ) B (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) x) =
    algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))

include hκ in
/-- In the local ring of `Rc` at a point `𝔪 ∋ z`, the origin section `(h, z)` is `(h)`. -/
lemma map_span_h0_z0 (P : Ideal (RcT π b₄ t κ)) [P.IsPrime]
    (hz : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ P) :
    (Ideal.span {h0 π b₄ t κ, z0 π b₄ t κ}).map
        ((algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)).comp
          (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ))) =
      Ideal.span {algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)
        (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))} := by
  set f := (algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)).comp
    (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ))
  have hsC : algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)
      (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ)) = f (h0 π b₄ t κ) :=
    rfl
  rw [Ideal.map_span, Set.image_pair, hsC]
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (by simp))
  rintro x (rfl | rfl)
  · exact Ideal.subset_span rfl
  · have hq : IsUnit (f (TateT0Regular.q0 π b₄ t κ)) :=
      IsLocalization.map_units (Localization.AtPrime P)
        (⟨_, TateCuspCov.q0_notMem hκ P hz⟩ : P.primeCompl)
    obtain ⟨u, hu⟩ := hq.exists_right_inv
    have h := congrArg f (TateT0Regular.z0_mul_q0 (π := π) (b₄ := b₄) (t := t) (κ := κ))
    rw [map_mul] at h
    refine Ideal.mem_span_singleton'.2 ⟨f (algebraMap O _ π * (algebraMap O _ κ *
      (algebraMap O _ b₄ * z0 π b₄ t κ ^ 2 + h0 π b₄ t κ ^ 2))) * u, ?_⟩
    calc _ = f (algebraMap O (T0 π b₄ t κ) π * (algebraMap O _ κ * (algebraMap O _ b₄ *
          h0 π b₄ t κ * z0 π b₄ t κ ^ 2 + h0 π b₄ t κ ^ 3))) * u := by
          simp only [map_mul, map_add, map_pow]; ring
      _ = f (z0 π b₄ t κ) := by rw [← h, mul_assoc, hu, mul_one]

include hκ hB in
/-- **The cusp-chart hypothesis `hunr` from the global one on `T0`**: if `B₀` is unramified over
`T0` at every prime whose contraction lies strictly inside a maximal ideal containing `ϖ`,
except over the origin section `(h, z)`, then `B = B₀[1/(1 + h)]` satisfies the hypothesis `hunr`
of `TateCuspCov.covCusp`. -/
theorem hunr_Bc {ϖ : O}
    (hunr₀ : ∀ (P : Ideal (T0 π b₄ t κ)) [P.IsMaximal], algebraMap O (T0 π b₄ t κ) ϖ ∈ P →
      ∀ (Q : Ideal B₀) [Q.IsPrime], Q.comap (algebraMap (T0 π b₄ t κ) B₀) < P →
        Q.comap (algebraMap (T0 π b₄ t κ) B₀) ≠ Ideal.span {h0 π b₄ t κ, z0 π b₄ t κ} →
        Algebra.IsUnramifiedAt (T0 π b₄ t κ) Q)
    (P : Ideal (RcT π b₄ t κ)) [P.IsMaximal] (hϖP : algebraMap O (RcT π b₄ t κ) ϖ ∈ P)
    (Q : Ideal B) [Q.IsPrime] (hQ : Q.comap (algebraMap (RcT π b₄ t κ) B) < P)
    (hz : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ P →
      (Q.comap (algebraMap (RcT π b₄ t κ) B)).map
          (algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)) ≠
        Ideal.span {algebraMap (RcT π b₄ t κ) (Localization.AtPrime P)
          (CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ))}) :
    Algebra.IsUnramifiedAt (RcT π b₄ t κ) Q := by
  letI : Algebra (T0 π b₄ t κ) B :=
    ((algebraMap B₀ B).comp (algebraMap (T0 π b₄ t κ) B₀)).toAlgebra
  haveI : IsScalarTower (T0 π b₄ t κ) (RcT π b₄ t κ) B :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower (T0 π b₄ t κ) B₀ B := IsScalarTower.of_algebraMap_eq' rfl
  refine NormAway.isUnramifiedAt (B₁ := B₀) (TateGlue0.c0 π b₄ t κ) Q ?_
  set Qc := Q.comap (algebraMap (RcT π b₄ t κ) B)
  set p := Qc.comap (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ))
  have hc : (Q.comap (algebraMap B₀ B)).comap (algebraMap (T0 π b₄ t κ) B₀) = p := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    simp only [p, Qc, Ideal.comap_comap]
    rw [← IsScalarTower.algebraMap_eq]
  have hP' : P.comap (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ)) ≠ ⊤ :=
    Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal _ hP'
  have hlt : p < P.comap (algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ)) := by
    refine lt_of_le_of_ne (Ideal.comap_mono hQ.le) fun heq ↦ hQ.ne ?_
    haveI : Qc.IsPrime := Ideal.comap_isPrime _ _
    rw [← IsLocalization.map_under (Submonoid.powers (TateGlue0.c0 π b₄ t κ)) (RcT π b₄ t κ) Qc,
      ← IsLocalization.map_under (Submonoid.powers (TateGlue0.c0 π b₄ t κ)) (RcT π b₄ t κ) P]
    exact congrArg _ heq
  have hϖM : algebraMap O (T0 π b₄ t κ) ϖ ∈ M :=
    hPM (by rwa [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply])
  refine hunr₀ M hϖM _ (hc ▸ lt_of_lt_of_le hlt hPM) fun hpc ↦ ?_
  rw [hc] at hpc
  have hzP : algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ) ∈ P := by
    have h1 : z0 π b₄ t κ ∈ p := hpc ▸ Ideal.subset_span (by simp)
    exact hQ.le h1
  apply hz hzP
  haveI : Qc.IsPrime := Ideal.comap_isPrime _ _
  rw [← IsLocalization.map_under (Submonoid.powers (TateGlue0.c0 π b₄ t κ)) (RcT π b₄ t κ) Qc]
  change (p.map _).map _ = _
  rw [Ideal.map_map, hpc]
  exact map_span_h0_z0 hκ P hzP

end Hunr

section Lift

open TateAffine

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
  [IsEmpty cov₀.κ]

/-- **The M2 lift of a Tate covering ramified at the cusp, with its generic fibre**, as a
predicate on the special-fibre data `Sp`, `Sc`, `ω`: the conclusion of
`TateGlue0.exists_etale_normalisedModel_cusp` together with T1a
(`TateGlue0.finite_etale_gluedK_cusp`: the glued generic fibre is finite étale over `E ∖ {0}`). -/
def LiftCusp (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) : Prop :=
  ∃ (N : ProjectiveLine.ChartModule O) (_ : Module.Finite O[X] (Module.AEval' N.x0))
      (_ : Module.Finite O[X] (Module.AEval' N.x1))
      (B : ProjectiveLine.ChartModule.AlgStr N)
      (α : ∀ n, ProjectiveLine.ChartModule.Hom N
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
        LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤) ∧
      (∀ a b (h : a ≤ b),
        ((systemCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).tr h).comp (α b) = α a) ∧
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
                (Localization.Away (B.const1 ϖ))) ∧
        (letI := algA b₄ ϖ hκ (iota0 hψ);
          letI := algB b₄ hκ (pi_dvd hπ hε) (iota1 hψ);
          Module.Finite (AK π b₄ b₆ ϖ)
              (gluedK b₄ hκ (pi_dvd hπ hε) (hc0_chart hψ) (hc1_chart hψ)) ∧
            Algebra.Etale (AK π b₄ b₆ ϖ)
              (gluedK b₄ hκ (pi_dvd hπ hε) (hc0_chart hψ) (hc1_chart hψ)))

variable [IsDomain O] [IsDiscreteValuationRing O] [(Ideal.span {ϖ}).IsMaximal]

include hπ' hm in
/-- **The M2 lift of a Tate covering ramified at the cusp exists** (`LiftCusp`), if the ramified
cusp factors lie over the cusp (`CuspOverOrigin`). -/
theorem liftCusp (hϖ0 : ϖ ≠ 0) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (hSc : CuspOverOrigin Sc) (ω : OmegaC hκ hπ Sp Sc.C0) :
    LiftCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω := by
  obtain ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, hi0, hi1, he0, he1⟩ :=
    exists_etale_normalisedModel_cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 h3 hE Sc ω
  haveI := hN0
  haveI := hN1
  haveI := hf0
  haveI := hf1
  exact ⟨N, hN0, hN1, B, α, hα, hc, hB, hf0, hf1, ψ, hψ, hψα, hi0, hi1, he0, he1,
    finite_etale_gluedK_cusp hκ hπ hε hϖ π' hπ' hker Sp hm hO hϖ0 h3 hE Sc hSc ω hα hB hψ hψα⟩

end Lift

section Data

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsAlgClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m]


variable (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
  (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) (hb₆ : IsUnit b₆)
  {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t
      κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) = algebraMap (T1 (ε * ϖ ^ m) b₄ t
      κ) K x)
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ M') {ζe : K} (hζe : IsPrimitiveRoot ζe e)
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (hL : (finrank K L).Coprime q) (hd : finrank K L ∣ e)
  [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (NR b₄
      b₆ ϖ m ε) L] [IsScalarTower (NR b₄ b₆ ϖ m ε) K L]
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (T0 (ε
      * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) L]
  [Algebra (T01 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t
      κ) L]
  (hρ : ∀ x, algebraMap (T01 (ε * ϖ ^ m) b₄ t κ) L (rho0 (ε * ϖ ^ m) b₄ t κ x) = algebraMap (T0 (ε
      * ϖ ^ m) b₄ t κ) L x)
  (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L]
  (Bn : Type u) [CommRing Bn] [Algebra (NR b₄ b₆ ϖ m ε) Bn] [Algebra Bn L] [IsScalarTower (NR b₄ b₆
      ϖ m ε) Bn L]
  [Algebra B₁ Bn] [IsScalarTower B₁ Bn L]
  [IsLocalization.Away (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ (DT (ε * ϖ ^ m) b₄ t κ)) Bn]
  (hBn : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) Bn (toNode b₄ hκ rfl x) = algebraMap B₁ Bn (algebraMap
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁ x))
  (B₀ : Type u) [CommRing B₀] [Algebra (T0 (ε * ϖ ^ m) b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower
      (T0 (ε * ϖ ^ m) b₄ t κ) B₀ L]
  [IsIntegralClosure B₀ (T0 (ε * ϖ ^ m) b₄ t κ) L]
  (Bc : Type u) [CommRing Bc] [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) Bc] [Algebra Bc L] [IsScalarTower
      (RcT (ε * ϖ ^ m) b₄ t κ) Bc L]
  [Algebra B₀ Bc] [IsScalarTower B₀ Bc L]
  [IsLocalization.Away (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)) Bc]
  (hBc : ∀ x, algebraMap (RcT (ε * ϖ ^ m) b₄ t κ) Bc (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε *
      ϖ ^ m) b₄ t κ) x) = algebraMap B₀ Bc (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ x))
  (hunr₁ : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T1 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
    Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁) < P → Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄
      t κ) Q)
  (hunr₀ : ∀ (P : Ideal (T0 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T0 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₀) [Q.IsPrime],
    Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀) < P →
      Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀) ≠
        Ideal.span {h0 (ε * ϖ ^ m) b₄ t κ, z0 (ε * ϖ ^ m) b₄ t κ} →
      Algebra.IsUnramifiedAt (T0 (ε * ϖ ^ m) b₄ t κ) Q)
  (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (h0 (ε * ϖ ^ m) b₄ t
        κ))))

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] in
include hker in
lemma θ_pow : θ (ϖ ^ m) = 0 := by
  rw [map_pow, RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self ϖ),
    zero_pow (NeZero.ne m)]

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] in
include hker in
lemma θ_ϖ : θ ϖ = 0 := RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self ϖ)

omit [IsAlgClosed k] in
include hϖ hker in
/-- Elements of `O` outside `ker θ` are units. -/
lemma isUnit_of_θ_ne_zero (x : O) (hx : θ x ≠ 0) : IsUnit x := by
  by_contra h
  have hm : x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal x).2 h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, ← hker] at hm
  exact hx hm

variable {K L B₁ Bn B₀ Bc}

/-- **The special-fibre covering over `V₁`** (`TateGlue1.special1`). -/
abbrev sp :=
  TateGlue1.special1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ Bn hBn hunr₁
    (θ_pow hker) τ

/-- The node covering of `sp` (`TateGlue1.covTate`). -/
abbrev cov :=
  TateGlue1.covTate hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ Bn hBn hunr₁
    (θ_pow hker) τ

/-- The node covering has no cusp factors. -/
instance isEmpty_cov_κ :
    IsEmpty (cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).κ :=
  inferInstanceAs (IsEmpty Empty)

/-- **The ramification indices over the nodes divide `M'`.** -/
theorem covTate_e_dvd (j : (cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).ι) :
    (cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).e j ∣ M' := by
  haveI := TateGlue1.isFractionRing_NR hϖ hκ hε h3 hE K hK
  haveI := TateGlue1.isIntegralClosure_B hϖ hκ hε K hK L B₁ Bn
  exact covNR_e_dvd hϖ hker (.of_mul_eq_one_right εi hε) h3 hE hqM hq hM' hM'k K hζ L hL Bn
    (TateGlue1.hunr_B hκ hε B₁ Bn hBn hunr₁) (θ_pow hker) _ j

/-- `π' j = ϖ^(m / e j)`, an `e j`-th root of `ϖᵐ` (`piP_pow`). -/
abbrev piP (j : (cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).ι) : O :=
  ϖ ^ (m / (cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).e j)

lemma piP_pow (j : (cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).ι) :
    piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ j ^
      (cov hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).e j = ϖ ^ m := by
  rw [← pow_mul, Nat.div_mul_cancel ((covTate_e_dvd hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
    hL hBn hunr₁ τ j).trans (Dvd.intro_left q hqM))]

/-- **The cusp special-fibre data** (`TateCuspCov.cuspSpecial`, `B = Bc`, hypothesis `hunr` from
`hunr₀`, `hunr_Bc`). -/
abbrev sc :=
  TateCuspCov.cuspSpecial hϖ hker rfl (Nat.one_le_iff_ne_zero.2 (NeZero.ne m))
    (.of_mul_eq_one_right εi hε) h3 hE hκ hb₆ he K hζe L hd Bc
    (fun P _ hϖP Q _ hQ hz ↦ hunr_Bc hκ hBc hunr₀ P hϖP Q hQ hz) φ₀ B₀ hBc

/-- **The ramified cusp factors of `sc` lie over the cusp** (`TateCuspCov.cuspOverOrigin`). -/
theorem sc_cuspOverOrigin :
    CuspOverOrigin (sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀) :=
  TateCuspCov.cuspOverOrigin hϖ hker rfl (Nat.one_le_iff_ne_zero.2 (NeZero.ne m))
    (.of_mul_eq_one_right εi hε) h3 hE hκ hb₆ he K hζe L hd Bc
    (fun P _ hϖP Q _ hQ hz ↦ hunr_Bc hκ hBc hunr₀ P hϖP Q hQ hz) φ₀ B₀ hBc

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [NeZero m] in
include hρ in
lemma h0_ne_zero : algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) L (h0 (ε * ϖ ^ m) b₄ t κ) ≠ 0 := by
  rw [← hρ]
  exact ((isUnit_rho0_h0 _ _ _ _).map (algebraMap (T01 (ε * ϖ ^ m) b₄ t κ) L)).ne_zero

omit [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [NeZero m] in
lemma h1_ne_zero : algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) L (h1 (ε * ϖ ^ m) b₄ t κ) ≠ 0 := by
  rw [IsScalarTower.algebraMap_apply (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t κ) L]
  exact ((IsLocalization.Away.algebraMap_isUnit _).map _).ne_zero

/-- **The overlap datum `ω`** (`TateGlue0.omegaNormC`, `C1 = B₁/J` on the nose). -/
abbrev om : OmegaC hκ rfl (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
    (sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀).C0 :=
  omegaNormC hκ rfl (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
    (L := L) (B₀ := B₀) (B₁ := B₁) AlgEquiv.refl hρ (h0_ne_zero hρ) h1_ne_zero

variable [IsAdicComplete (Ideal.span {ϖ}) O]

/-- **MR12 S5: the M2 lift of a tame cover of the Tate curve.** For the special-fibre data
`sp`, `sc`, `om` of a tame Galois cover `L` of the function field (see the module docstring;
hypothesis `hunr` = debt D3/A1), with `π' j = ϖ^(m / e j)`: the adic system of special-fibre
levels has a flat algebraization `(N, B, α)` with a structure map `ψ` from the Tate model, whose
charts are the normalisations of `T0`, `T1` in their generic fibres, étale over `T0[1/(ϖ h)]`,
`T1[1/ϖ]`, and whose glued generic fibre is a finite étale algebra over the coordinate ring of
`E ∖ {0}` (`TateGlue0.LiftCusp`). For the actual Tate parameters `h3`, `hE` follow from the curve
(`TateNormal.three_ne_zero_of_charZero`, `TateNormal.tateE_ne_zero_of_isElliptic`). -/
theorem liftCusp_tame :
    LiftCusp hκ rfl hε (θ_ϖ hker) (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
      (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (sp hϖ hker hκ hε
      h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (NeZero.ne m)
      (isUnit_of_θ_ne_zero hϖ hker) (sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀) (om hϖ hker
        hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀) := by
  haveI : (Ideal.span {ϖ}).IsMaximal := by
    rw [← (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ]
    infer_instance
  exact liftCusp hκ rfl hε (θ_ϖ hker) (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁
      τ) (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (sp hϖ hker hκ
      hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (NeZero.ne m)
    (isUnit_of_θ_ne_zero hϖ hker) hϖ.ne_zero h3 hE (sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀
      φ₀) (sc_cuspOverOrigin hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀) (om hϖ hker hκ hε h3
      hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀)

end Data

end

end TateS5

end SemistableReduction
