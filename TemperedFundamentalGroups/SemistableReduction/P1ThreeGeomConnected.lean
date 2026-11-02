/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialFibre
import TemperedFundamentalGroups.SemistableReduction.GenericConnectedBaseChange

/-!
# Geometric connectedness of the lift of a tame cover of `ℙ¹_k ∖ {0, 1, ā}` (MR13 A1 (c))

For the M2 lift `(N, B, α)` of a tame covering of `ℙ¹_k ∖ {0, 1, ā}` (`P1ThreeGlue`), with
`C1` connected: for every Noetherian domain `O'` over `O` with a nonzero nonunit `ϖ'` such that
`O → O'/ϖ'` is surjective with kernel `(ϖ)` (e.g. the ring of integers of a totally ramified
finite extension `K'/K`, with uniformizer `ϖ'`), the base change `O'[X] ⊗_{O[X]} B₁` of the second
chart has connected generic fibre: **`P1Three.connected_lift_baseChange`**
(`GenericConnected.isIdempotentElem_away_baseChange`, its special fibre is `B₁/ϖ ≃ C1`,
`specialFibreEquiv1`, reduced by `isReduced_C1`).

`(O'[X] ⊗_{O[X]} B₁)[1/ϖ'] = K' ⊗_K B₁[1/ϖ]`, so the generic fibre of the lift stays connected
over every totally ramified `K'/K`; when `k` is algebraically closed every finite extension of
the complete discretely valued `K` is totally ramified, so this is the geometric connectedness
(`L ∩ K̄ = K`) needed in Route B, B4 (MR13-plan, run 11, item (c)).
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

/-- The second chart of the lift as an `O[X]`-algebra (`polyHom1`). -/
@[reducible] def algX1 (B : ProjectiveLine.ChartModule.AlgStr N) : Algebra O[X] B.Ring1 :=
  B.polyHom1.toAlgebra

/-- **The base change** `O'[X] ⊗_{O[X]} B₁` of the second chart of the lift. -/
abbrev BC1 (O' : Type u) [CommRing O'] [Algebra O O'] (B : ProjectiveLine.ChartModule.AlgStr N) :
    Type u :=
  letI := GenericConnected.algPoly (R := O) (R' := O')
  letI := algX1 B
  O'[X] ⊗[O[X]] B.Ring1

instance (O' : Type u) [CommRing O'] [Algebra O O'] (B : ProjectiveLine.ChartModule.AlgStr N) :
    CommRing (BC1 O' B) :=
  letI := GenericConnected.algPoly (R := O) (R' := O')
  letI := algX1 B
  inferInstanceAs (CommRing (O'[X] ⊗[O[X]] B.Ring1))

instance (O' : Type u) [CommRing O'] [Algebra O O'] (B : ProjectiveLine.ChartModule.AlgStr N) :
    Algebra O'[X] (BC1 O' B) :=
  letI := GenericConnected.algPoly (R := O) (R' := O')
  letI := algX1 B
  inferInstanceAs (Algebra O'[X] (O'[X] ⊗[O[X]] B.Ring1))

include hα hB in
/-- **Geometric connectedness of the generic fibre at finite level**: if `C1` has only the trivial
idempotents, then for `O'` over `O` with `O → O'/ϖ'` surjective with kernel `(ϖ)`, the generic
fibre `(O'[X] ⊗_{O[X]} B₁)[1/ϖ']` of the base change has only the trivial idempotents. -/
theorem connected_lift_baseChange
    [Module.Finite O[X] (Module.AEval' N.x1)] [Module.Flat O[X] (Module.AEval' N.x1)]
    {O' : Type u} [CommRing O'] [IsDomain O'] [IsNoetherianRing O'] [Algebra O O'] {ϖ' : O'}
    (hϖ'0 : ϖ' ≠ 0) (hϖ'u : ¬IsUnit ϖ')
    (hs : Function.Surjective (algebraMap O (O' ⧸ Ideal.span {ϖ'})))
    (hk : RingHom.ker (algebraMap O (O' ⧸ Ideal.span {ϖ'})) = Ideal.span {ϖ})
    (hconn : ∀ e : Sp.C1, IsIdempotentElem e → e = 0 ∨ e = 1)
    (S : Type u) [CommRing S] [Algebra (BC1 O' B) S]
    [IsLocalization.Away (algebraMap O'[X] (BC1 O' B) (C ϖ')) S]
    {e : S} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  letI := GenericConnected.algPoly (R := O) (R' := O')
  letI := algX1 B
  haveI := B.finite_polyHom1
  haveI := B.flat_polyHom1
  have hc : algebraMap O[X] B.Ring1 (C ϖ) = B.const1 ϖ := by
    simp [ProjectiveLine.ChartModule.AlgStr.polyHom1, RingHom.algebraMap_toAlgebra]
  obtain ⟨f⟩ : Nonempty (B.Ring1 ⧸ Ideal.span {B.const1 ϖ} ≃+* Sp.C1) :=
    ⟨specialFibreEquiv1 Sp hϖ hker S0 ω hO hα hB⟩
  haveI := isReduced_C1 Sp hϖ hker
  have hred : IsReduced (B.Ring1 ⧸ Ideal.span {B.const1 ϖ}) :=
    isReduced_of_injective f.toRingHom f.injective
  have hconn' : ∀ x : B.Ring1 ⧸ Ideal.span {B.const1 ϖ}, IsIdempotentElem x → x = 0 ∨ x = 1 :=
    fun x hx ↦ by
      rcases hconn (f x) (hx.map f) with h | h
      · left
        have h' := congrArg f.symm h
        rwa [RingEquiv.symm_apply_apply, map_zero] at h'
      · right
        have h' := congrArg f.symm h
        rwa [RingEquiv.symm_apply_apply, map_one] at h'
  rw [← hc] at hred hconn'
  exact GenericConnected.isIdempotentElem_away_baseChange
    (GenericConnected.surjective_polyQuot hs) (GenericConnected.ker_polyQuot hk)
    (C_ne_zero.2 hϖ'0) (fun h ↦ hϖ'u (Polynomial.isUnit_C.mp h)) hred hconn' S he

end

end P1Three

end SemistableReduction
