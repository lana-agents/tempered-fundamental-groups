/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KaehlerTowerLocal
import TemperedFundamentalGroups.SemistableReduction.LevelKaehlerSplit

/-!
# The differentials of the algebraized covering, killed by a local element (M2.5 (f), T1b)

Generic over `NodeEtaleGlue.Overlap`: **`Overlap.kills_local`** — for a flat algebraization
`(N, B, α)` of `V.system` with a structure map `ψ` from the base model `D` (as in
`Overlap.kills_shift`), if `ϖᵐ` kills the node patches, `ϖᵐ x₀` and `ϖᵐ a0(d)` kill the piece
`P0 n` at all levels (for an element `d` of the first chart of the base), and `1 − ϖ b` is a unit
modulo `X` in `B₀`, then `ϖᵐ d` kills `Ω[B₀⁄D.R0]` (`TwoChartTower.kills_local0`).
-/

universe u

open Polynomial

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} {V : Overlap I} (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [IsNoetherianRing O]

omit [IsNoetherianRing O] in
/-- The levels of the first chart are killed by `c · a0(d)` if the piece `P0 n` is. -/
theorem kills_level0 {D : ProjectiveLine.TwoChartRings O} (b : BaseMap V D)
    (hu0 : letI := b.a0.toAlgebra; Algebra.FormallyUnramified D.R0 V.B0')
    {c : O} (n : ℕ)
    (hG : KaehlerLocal.Kills (I.R n) (algebraMap (I.R n) (I.T.G hθ n)
      (algebraMap (I.B n) (I.R n)
        (algebraMap I.B0 (I.B n) (letI := V.algOB0; algebraMap O I.B0 c)))))
    (d : D.R0)
    (hP : KaehlerLocal.Kills (V.B' n) (algebraMap (V.B' n) (V.P0.P n)
      (algebraMap V.B0' (V.B' n) (algebraMap O V.B0' c * b.a0 d)))) :
    letI := (b.β hθ hO n).f0.toRingHom.toAlgebra
    KaehlerLocal.Kills D.R0
      (algebraMap O (V.twoChart hθ hO n).R0 c * (b.β hθ hO n).f0 d) := by
  letI := V.algOB0
  have hc : algebraMap V.B0' V.W0 (algebraMap O V.B0' c) =
      algebraMap I.B0 V.W0 (algebraMap O I.B0 c) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have hY : KaehlerLocal.Kills I.B0 (algebraMap I.B0 (I.Y hθ n) (algebraMap O I.B0 c)) :=
    I.kills_Y hθ hO V.surjB n hG
  letI := V.alg0'Q hθ n
  letI := V.alg0'E n
  letI := V.alg0'M n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  haveI := V.towerOE n
  haveI := V.towerOM n
  letI := b.a0.toAlgebra
  letI : Algebra D.R0 (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) :=
    (b.β hθ hO n).f0.toRingHom.toAlgebra
  haveI : IsScalarTower D.R0 V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := hu0
  have h := V.kills_R0 hθ hO n hc hY (b.a0 d) hP
  have e : algebraMap O (V.twoChart hθ hO n).R0 c * (b.β hθ hO n).f0 d =
      algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n))
        (algebraMap O V.B0' c * b.a0 d) := by
    have e0 : algebraMap O (V.twoChart hθ hO n).R0 c =
        algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO n) (V.ρ0b n)) (algebraMap O V.B0' c) :=
      Subtype.ext (Prod.ext (IsScalarTower.algebraMap_apply O V.B0' (V.Q hθ n) c)
        (IsScalarTower.algebraMap_apply O V.B0' (V.P0.P n) c))
    rw [map_mul, e0]
    rfl
  have h2 := KaehlerLocal.kills_of_base D.R0 V.B0' h
  rw [← e] at h2
  exact h2

include hO in
/-- **The differentials of the algebraized covering killed by a local element** (see the
module docstring). -/
theorem kills_local {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})}
    (hS : V.system hθ hO = S) [IsAdicComplete (Ideal.span {V.ϖ}) O]
    {N : ProjectiveLine.ChartModule O} [Module.Finite O[X] (Module.AEval' N.x0)]
    [Module.Finite O[X] (Module.AEval' N.x1)] {B : ProjectiveLine.ChartModule.AlgStr N}
    {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n))
    {D : ProjectiveLine.TwoChartRings O} (b : BaseMap V D)
    (hu0 : letI := b.a0.toAlgebra; Algebra.FormallyUnramified D.R0 V.B0')
    (hu1 : letI := b.a1.toAlgebra; Algebra.FormallyUnramified D.R1 I.B0)
    {ψ : ProjectiveLine.ChartModule.Hom D.chartModule N} (hψ : D.algStr.IsHom B ψ)
    (hψα : ∀ n, (α (n + 1)).comp ψ = b.βS hθ hO n hS)
    [IsNoetherianRing B.Ring0]
    [letI := B.algR0 hψ; Module.Finite B.Ring0 Ω[B.Ring0⁄D.R0]]
    {m : ℕ}
    (hG : ∀ n, KaehlerLocal.Kills (I.R n) (algebraMap (I.R n) (I.T.G hθ n)
      (algebraMap (I.B n) (I.R n)
        (algebraMap I.B0 (I.B n) (letI := V.algOB0; algebraMap O I.B0 (V.ϖ ^ m))))))
    (hPx : ∀ n, KaehlerLocal.Kills (V.B' n) (algebraMap (V.B' n) (V.P0.P n)
      (algebraMap V.B0' (V.B' n) (algebraMap O V.B0' (V.ϖ ^ m) * V.x0 ^ 1))))
    (d : D.R0)
    (hPd : ∀ n, KaehlerLocal.Kills (V.B' n) (algebraMap (V.B' n) (V.P0.P n)
      (algebraMap V.B0' (V.B' n) (algebraMap O V.B0' (V.ϖ ^ m) * b.a0 d))))
    (hunit : ∀ y : B.Ring0, ∃ u s, (1 - B.const0 V.ϖ * y) * u = 1 + B.X0 * s) :
    letI := B.algR0 hψ
    KaehlerLocal.Kills D.R0 (B.const0 (V.ϖ ^ m) * algebraMap D.R0 B.Ring0 d) := by
  have hX := (kills_shift hθ hO hS hα hB b hu0 hu1 hψ hψα (c := V.ϖ ^ m) (j := 1) le_rfl hG
    hPx).1
  rw [pow_one] at hX
  subst hS
  exact TwoChartTower.kills_local0 (E := fun n ↦ V.twoChart hθ hO n) rfl hα hB hψ hψα hX
    (fun n ↦ kills_level0 hθ hO b hu0 n (hG n) d (hPd n)) hunit

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
