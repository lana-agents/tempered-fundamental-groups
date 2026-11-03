/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeGeomConnectedTensor
import TemperedFundamentalGroups.SemistableReduction.IdempotentAlgebraicBaseChange
import TemperedFundamentalGroups.SemistableReduction.FiniteExtensionDVR

/-!
# Geometric connectedness of the generic fibre of the lift (MR13 A1 (c), (f) step 3)

**`P1Three.connected_lift_algebraic`**: for the M2 lift `(N, B, α)` of a tame covering of
`ℙ¹_k ∖ {0, 1, ā}` over a discrete valuation ring `O` with algebraically closed residue field `k`
and perfect fraction field `K` (e.g. of characteristic `0`), if `C1` is connected then for every
algebraic extension `L / K` (e.g. `L = K̄`) the ring `L ⊗_O B₁ = L ⊗_K B₁[1/ϖ]` has only the trivial
idempotents: the generic fibre of the lift is geometrically connected.

Proof: `L ⊗_O B₁ ≃ L ⊗_K (K ⊗_O B₁)` (`Algebra.TensorProduct.cancelBaseChange`), so by
`IdempotentAlgebraicBaseChange.eq_zero_or_eq_one` it suffices to treat finite subextensions `E`,
where `E ⊗_K (K ⊗_O B₁) ≃ E ⊗_O B₁`; for these `FiniteExtensionDVR.elim` gives a discrete valuation
ring `O' ⊆ E` with `O → O'/ϖ'` onto with kernel `(ϖ)` and `E = O'[1/ϖ']` (no residue extension,
since `k` is algebraically closed), and `P1Three.connected_lift_tensor` applies.
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

omit hθ [IsNoetherianRing O] in
include hϖ hker in
/-- The kernel of the residue map is `(ϖ)`. -/
lemma ker_theta_eq : RingHom.ker θ = Ideal.span {ϖ} :=
  le_antisymm hker ((Ideal.span_singleton_le_iff_mem _).2 hϖ)

include hα hB in
/-- **The generic fibre of the lift is geometrically connected**: if `C1` has only the trivial
idempotents, then so has `L ⊗_O B₁` for every algebraic extension `L` of `K = Frac O` (`O` a
discrete valuation ring with uniformizer `ϖ`, residue field `k` algebraically closed, `K`
perfect). -/
theorem connected_lift_algebraic [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k]
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x1)]
    (hϖ0 : ϖ ≠ 0) (K : Type u) [Field K] [Algebra O K] [IsFractionRing O K] [PerfectField K]
    (hconn : ∀ e : Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1)
    (L : Type u) [Field L] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
    [Algebra.IsAlgebraic K L] {e : (letI := algO1 B; L ⊗[O] B.Ring1)}
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  letI := algO1 B
  haveI : IsDedekindDomain O := inferInstance
  -- reduce to `L ⊗_K (K ⊗_O B₁)`
  let f : L ⊗[K] (K ⊗[O] B.Ring1) ≃ₐ[L] L ⊗[O] B.Ring1 :=
    Algebra.TensorProduct.cancelBaseChange O K L L B.Ring1
  have he' : IsIdempotentElem (f.symm e) := he.map f.symm
  have key := IdempotentAlgebraicBaseChange.eq_zero_or_eq_one (K := K) (L := L)
    (B := K ⊗[O] B.Ring1) (fun E _ y hy ↦ by
      let g : E ⊗[K] (K ⊗[O] B.Ring1) ≃ₐ[E] E ⊗[O] B.Ring1 :=
        Algebra.TensorProduct.cancelBaseChange O K E E B.Ring1
      have hgy : IsIdempotentElem (g y) := hy.map g
      have hg : g y = 0 ∨ g y = 1 :=
        FiniteExtensionDVR.elim hθ.out (ker_theta_eq hϖ hker) hϖ0 K E _
          fun O' _ _ _ _ ϖ' hϖ'0 hϖ'u hs hk _ _ _ ↦
            connected_lift_tensor Sp hϖ hker S0 ω hO hα hB hϖ'0 hϖ'u hs hk hconn E hgy
      rcases hg with h | h
      · left
        simpa using congrArg g.symm h
      · right
        simpa using congrArg g.symm h) he'
  rcases key with h | h
  · left
    simpa using congrArg f h
  · right
    simpa using congrArg f h

end

end P1Three

end SemistableReduction
