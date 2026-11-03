/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeGeomConnected
import TemperedFundamentalGroups.SemistableReduction.GenericConnectedLocalize

/-!
# The generic fibre of the lift stays connected over `E = O'[1/ϖ']` (MR13 A1 (c), (f) step 3)

**`P1Three.connected_lift_tensor`**: for the M2 lift `(N, B, α)` of a tame covering of
`ℙ¹_k ∖ {0, 1, ā}` with `C1` connected, and `O'`, `ϖ'` as in `connected_lift_baseChange`
(`O → O'/ϖ'` onto with kernel `(ϖ)`), the base change `E ⊗_O B₁` of the second chart to
`E = O'[1/ϖ']` has only the trivial idempotents (`GenericConnected.eq_zero_or_eq_one_tensor`:
`E ⊗_O B₁` is the localization of `O'[X] ⊗_{O[X]} B₁` away from `ϖ'`). For `E = K'` a finite
extension of `K = O[1/ϖ]` this is `K' ⊗_K B₁[1/ϖ]`, and
`IdempotentAlgebraicBaseChange.eq_zero_or_eq_one` passes to `K̄`.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ : O} {a : O}
  (Sp : Special1 O θ a) (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  [IsNoetherianRing O] (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ))
  (ω : OmegaC Sp S0.C0) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((system Sp hϖ hker S0 ω hO).M n)}
  (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
    LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
    LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
  (hB : ∀ n, B.IsHom ((system Sp hϖ hker S0 ω hO).alg n) (α n))

/-- The second chart of the lift as an `O`-algebra (through `O[X]`, `polyHom1`). -/
@[reducible] def algO1 (B : ProjectiveLine.ChartModule.AlgStr N) : Algebra O B.Ring1 :=
  letI := algX1 B
  ((algebraMap O[X] B.Ring1).comp (algebraMap O O[X])).toAlgebra

include hα hB in
/-- **The generic fibre of the lift stays connected over `E = O'[1/ϖ']`**: if `C1` has only the
trivial idempotents, so has `E ⊗_O B₁` (for `O'`, `ϖ'` with `O → O'/ϖ'` onto with kernel `(ϖ)`). -/
theorem connected_lift_tensor
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x1)]
    {O' : Type u} [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] [Algebra O O'] {ϖ' : O'}
    (hϖ'0 : ϖ' ≠ 0) (hϖ'u : ¬IsUnit ϖ')
    (hs : Function.Surjective (algebraMap O (O' ⧸ Ideal.span {ϖ'})))
    (hk : RingHom.ker (algebraMap O (O' ⧸ Ideal.span {ϖ'})) = Ideal.span {ϖ})
    (hconn : ∀ e : Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1)
    (E : Type u) [CommRing E] [Algebra O' E] [Algebra O E] [IsScalarTower O O' E]
    [IsLocalization.Away ϖ' E] {e : (letI := algO1 B; E ⊗[O] B.Ring1)}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  letI := algX1 B
  letI := algO1 B
  haveI : IsScalarTower O O[X] B.Ring1 := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact GenericConnected.eq_zero_or_eq_one_tensor E ϖ'
    (fun S _ _ _ {_} he' ↦ connected_lift_baseChange Sp hϖ hker S0 ω hO hα hB hϖ'0 hϖ'u hs hk hconn
      S he') he

end

end P1Three

end SemistableReduction
