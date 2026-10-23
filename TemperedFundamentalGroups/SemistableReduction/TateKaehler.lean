/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.OverlapKaehler
import TemperedFundamentalGroups.SemistableReduction.TateNormalisedModel

/-!
# The generic fibre of the algebraized Tate coverings is unramified (Blueprint §12.8, M2.5 (f))

For the flat algebraization `(N, B, α)` of a Tate covering with its structure map
`ψ : (TateTwoChart.twoChart ..).algStr → B` to the Tate model (`TateGlue0.exists_normalisedModel`,
`exists_normalisedModel_cusp`), where the covering of the node chart has no cusp factors
(`IsEmpty cov₀.κ`; the cusp of the Tate curve lies in `V₀ ∖ V₁`):

* **`TateGlue0.kills_overlap`**: `ϖᵐ` kills `Ω[B₀⁄T0]` and `Ω[B₁⁄T1]` (covering étale over
  `D(1 + h)`); **`TateGlue0.kills_overlapCusp`**: `ϖᵐ h` kills `Ω[B₀⁄T0]` and `ϖᵐ` kills
  `Ω[B₁⁄T1]` (covering ramified at the cusp `h = 0`). Here `ϖᵐ = π'ⱼ^(eⱼ-1) π'ⱼ` on the Kummer
  factors of the node chart (`NodeEtaleGlue.Overlap.kills_G`), the étale lifts over `D(1 + h)` are
  unramified and the cusp patch is killed by the cusp coordinate `h`
  (`NodeEtaleGlue.PatchInput.kills_piece`); `NodeEtaleGlue.Overlap.kills_shift` transports this to
  the algebraization (along `system_eq` by `subst`).
* **`TateGlue0.formallyUnramified_overlap`**, **`formallyUnramified_overlapCusp`**: on the
  generic fibre outside the cusp divisor the algebraized covering is formally unramified over the
  Tate model: `B₀[1/ϖ]` over `T0` and `B₁[1/ϖ]` over `T1` (étale case), `B₀[1/(ϖ X)]` over `T0`
  (`X ↦ h`) and `B₁[1/ϖ]` over `T1` (cusp case).
-/

universe u

open Polynomial

namespace KaehlerLocal

variable (R : Type u) {S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- **Inverting an element with a power killing the differentials**: if `xᵐ` (`m ≠ 0`) kills
`Ω[S⁄R]`, then `S[1/x]` is formally unramified over `R`. -/
theorem formallyUnramified_away_of_pow {x : S} {m : ℕ} (hm : m ≠ 0) (hx : Kills R (x ^ m))
    (S' : Type u) [CommRing S'] [Algebra S S'] [IsLocalization.Away x S'] [Algebra R S']
    [IsScalarTower R S S'] : Algebra.FormallyUnramified R S' := by
  have h := IsLocalization.Away.mul_of_isUnit (S := S') x (x ^ (m - 1))
    (by rw [map_pow]; exact IsLocalization.Away.algebraMap_pow_isUnit x _)
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h
  exact ⟨KaehlerKill.subsingleton_away hx S'⟩

end KaehlerLocal

namespace SemistableReduction

namespace CuspTower

open TateLevel EtaleTower

variable {O : Type u} [CommRing O] {ϖ : O} {T0' : Type u} [CommRing T0'] [Algebra O T0']
  {c0 x0 : T0'} {k : Type u} [Field k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  (Sc : CuspSpecial T0' c0 x0 (θ := θ)) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing T0']
  (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The differentials of the cusp patch**: a multiple `a x₀` of the cusp coordinate kills the
differentials of the cusp patch over `D(c₀)` at every level (`PatchInput.kills_piece`). -/
theorem kills_cuspPiece (n : ℕ) (a d : T0') (hd : d = a * x0) :
    KaehlerLocal.Kills (Tn ϖ T0' n) (algebraMap (Tn ϖ T0' n) ((cuspPiece Sc hϖ hker hx hO).P n)
      (algebraMap T0' (Tn ϖ T0' n) d)) := by
  subst hd
  refine (cuspInput Sc hϖ hker hx).kills_piece hθ.out hO n _ fun _ ↦
    ⟨algebraMap ((cuspInput Sc hϖ hker hx).R n) _
      (Ideal.Quotient.mk _ (algebraMap T0' (Rc T0' c0) a)), ?_⟩
  have e : algebraMap (Tn ϖ T0' n) ((cuspInput Sc hϖ hker hx).R n)
      (algebraMap T0' (Tn ϖ T0' n) (a * x0)) =
      (Ideal.Quotient.mk _ (sC T0' c0 x0) : (cuspInput Sc hϖ hker hx).R n) *
        (Ideal.Quotient.mk _ (algebraMap T0' (Rc T0' c0) a) :
          (cuspInput Sc hϖ hker hx).R n) := by
    change quotMap (IsScalarTower.toAlgHom O T0' (Rc T0' c0)) (EtaleTower.Iv ϖ n)
      (Ideal.Quotient.mk _ (a * x0)) = _
    rw [quotMap_mk, map_mul, map_mul, mul_comm]
    rfl
  rw [e]
  exact map_mul _ _ _

end CuspTower

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel

noncomputable section

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

/-- The identity of a ring as an algebra is formally unramified (the base maps of the Tate
coverings are identities). -/
lemma formallyUnramified_id (R : Type u) [CommRing R] :
    letI := (RingHom.id R).toAlgebra; Algebra.FormallyUnramified R R :=
  letI := (RingHom.id R).toAlgebra
  ⟨KaehlerDifferential.subsingleton_of_surjective R R fun x ↦ ⟨x, rfl⟩⟩

omit [IsNoetherianRing O] [IsAdicComplete (Ideal.span {ϖ}) O] in
include hπ' in
/-- `ϖᵐ` is a multiple of `π'ⱼ^(eⱼ-1)` for every Kummer factor of the node chart. -/
lemma pow_eq_mul (j : cov₀.ι) : ∃ r : O, ϖ ^ m = π' j ^ (cov₀.e j - 1) * r :=
  ⟨π' j, by rw [pow_sub_one_mul (cov₀.e_pos j).ne', hπ']⟩

variable [IsEmpty cov₀.κ]

include hπ' in
/-- **The differentials of the algebraized Tate covering étale over `D(1 + h)`**: for the flat
algebraization `(N, B, α)` with the structure map `ψ` (`exists_normalisedModel`), `ϖᵐ` kills
`Ω[B₀⁄T0]` and `Ω[B₁⁄T1]`. -/
theorem kills_overlap (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
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
      KaehlerLocal.Kills (T0 π b₄ t κ) (B.const0 (ϖ ^ m))) ∧
    (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
      KaehlerLocal.Kills (T1 π b₄ t κ) (B.const1 (ϖ ^ m))) := by
  haveI : IsAdicComplete (Ideal.span {(overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  have h := NodeEtaleGlue.Overlap.kills_shift hθ.out hO
    (system_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω) hα hB
    (baseMap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω) (formallyUnramified_id _)
    (formallyUnramified_id _) hψ hψα (c := ϖ ^ m) (j := 0) zero_le_one
    (fun n ↦ (overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).kills_G hθ.out hO n
      (pow_eq_mul π' hπ'))
    (fun n ↦ by
      haveI : Algebra.FormallyEtale (EtaleTower.Tn ϖ (T0 π b₄ t κ) n) (E0 Sp0 hϖ hker n).E :=
        inferInstance
      exact fun _ ↦ Subsingleton.elim
        (α := Ω[(E0 Sp0 hϖ hker n).E⁄EtaleTower.Tn ϖ (T0 π b₄ t κ) n]) _ _)
  rw [pow_zero, mul_one] at h
  exact h

include hπ' in
/-- **The differentials of the algebraized Tate covering ramified at the cusp**: for the flat
algebraization `(N, B, α)` with the structure map `ψ` (`exists_normalisedModel_cusp`), `ϖᵐ X`
(`X ↦ h`) kills `Ω[B₀⁄T0]` and `ϖᵐ` kills `Ω[B₁⁄T1]`. -/
theorem kills_overlapCusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
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
      KaehlerLocal.Kills (T0 π b₄ t κ) (B.const0 (ϖ ^ m) * B.X0)) ∧
    (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
      KaehlerLocal.Kills (T1 π b₄ t κ) (B.const1 (ϖ ^ m))) := by
  haveI : IsAdicComplete
      (Ideal.span {(overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).ϖ}) O :=
    ‹IsAdicComplete (Ideal.span {ϖ}) O›
  have hP : ∀ n, KaehlerLocal.Kills (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
      (algebraMap (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
        ((CuspTower.cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO).P n)
        (algebraMap (T0 π b₄ t κ) (EtaleTower.Tn ϖ (T0 π b₄ t κ) n)
          (algebraMap O (T0 π b₄ t κ) (ϖ ^ m) * h0 π b₄ t κ ^ 1))) := fun n ↦
    CuspTower.kills_cuspPiece Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ) hO n _ _
      (by rw [pow_one])
  have h := NodeEtaleGlue.Overlap.kills_shift hθ.out hO
    (systemCusp_eq hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) hα hB
    (baseMapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω) (formallyUnramified_id _)
    (formallyUnramified_id _) hψ hψα (c := ϖ ^ m) (j := 1) le_rfl
    (fun n ↦ (overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).kills_G hθ.out hO n
      (pow_eq_mul π' hπ'))
    hP
  rw [pow_one] at h
  exact h

include hπ' hm in
/-- **The generic fibre of the algebraized Tate covering étale over `D(1 + h)` is unramified**:
for the flat algebraization of `exists_normalisedModel`, `B₀[1/ϖ]` is formally unramified over
`T0` and `B₁[1/ϖ]` over `T1`. -/
theorem formallyUnramified_overlap (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
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
      Algebra.FormallyUnramified (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ))) ∧
    (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
      letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
        ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
      Algebra.FormallyUnramified (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨h0, h1⟩ := kills_overlap hκ hπ hε hϖ π' hπ' hker Sp hm hO Sp0 ω hα hB hψ hψα
  constructor
  · letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
    letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ)) :=
      ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra
    haveI : @IsScalarTower (T0 π b₄ t κ) B.Ring0 (Localization.Away (B.const0 ϖ))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact KaehlerLocal.formallyUnramified_away_of_pow (T0 π b₄ t κ) (x := B.const0 ϖ) hm
      (by rw [← map_pow]; exact h0) _
  · letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ
    letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
      ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra
    haveI : @IsScalarTower (T1 π b₄ t κ) B.Ring1 (Localization.Away (B.const1 ϖ))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact KaehlerLocal.formallyUnramified_away_of_pow (T1 π b₄ t κ) (x := B.const1 ϖ) hm
      (by rw [← map_pow]; exact h1) _

include hπ' hm in
/-- **The generic fibre of the algebraized Tate covering ramified at the cusp is unramified
outside the cusp divisor**: for the flat algebraization of `exists_normalisedModel_cusp`,
`B₀[1/(ϖ X)]` (`X ↦ h`) is formally unramified over `T0` and `B₁[1/ϖ]` over `T1`. -/
theorem formallyUnramified_overlapCusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0)
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
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
      Algebra.FormallyUnramified (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ * B.X0))) ∧
    (letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ;
      letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
        ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra;
      Algebra.FormallyUnramified (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ))) := by
  obtain ⟨h0, h1⟩ := kills_overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm hO Sc ω hα hB hψ hψα
  constructor
  · letI : Algebra (T0 π b₄ t κ) B.Ring0 := B.algR0 hψ
    letI : Algebra (T0 π b₄ t κ) (Localization.Away (B.const0 ϖ * B.X0)) :=
      ((algebraMap B.Ring0 _).comp (algebraMap (T0 π b₄ t κ) B.Ring0)).toAlgebra
    haveI : @IsScalarTower (T0 π b₄ t κ) B.Ring0 (Localization.Away (B.const0 ϖ * B.X0))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have e : (B.const0 ϖ * B.X0) ^ m = B.const0 (ϖ ^ m) * B.X0 * B.X0 ^ (m - 1) := by
      rw [mul_pow, map_pow, mul_assoc, ← pow_succ', Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr hm)]
    exact KaehlerLocal.formallyUnramified_away_of_pow (T0 π b₄ t κ)
      (x := B.const0 ϖ * B.X0) hm (by rw [e]; exact KaehlerLocal.kills_mul _ h0 _) _
  · letI : Algebra (T1 π b₄ t κ) B.Ring1 := B.algR1 hψ
    letI : Algebra (T1 π b₄ t κ) (Localization.Away (B.const1 ϖ)) :=
      ((algebraMap B.Ring1 _).comp (algebraMap (T1 π b₄ t κ) B.Ring1)).toAlgebra
    haveI : @IsScalarTower (T1 π b₄ t κ) B.Ring1 (Localization.Away (B.const1 ϖ))
        Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
      IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    exact KaehlerLocal.formallyUnramified_away_of_pow (T1 π b₄ t κ) (x := B.const1 ϖ) hm
      (by rw [← map_pow]; exact h1) _

end

end TateGlue0

end SemistableReduction
