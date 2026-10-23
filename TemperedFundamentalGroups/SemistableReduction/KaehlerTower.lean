/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KaehlerAlgStr
import TemperedFundamentalGroups.SemistableReduction.TwoChartStructureMap

/-!
# From the levels to the algebraization: killing the differentials (Blueprint §12.8, M2.5 (f))

For a flat algebraization `(N, B, α)` of a tower of two-chart rings `E n` (`systemShift`) with a
structure map `φ : D.algStr → B` to a base model `D` reducing to the level maps
`β n : D → E n` (`α (n+1) ∘ φ = β n`): if a constant `c` kills the differentials of every level
`(E n).R_i` over `D.R_i` (on the first chart `c xʲ`, `j ≤ 1`), then it kills the differentials of
the algebraization, `Ω[B_i⁄D.R_i]` (**`TwoChartTower.kills_shift`**). The levels are the
reductions `B_i ⧸ Iⁿ⁺¹ B_i` (`TwoChartTower.quotEquivShift0/1`), compatibly with the base
(`KaehlerLocal.kills_of_equiv`), and `AlgStr.IsHom.kills_of_quot` applies.
-/

universe u

open Polynomial

namespace KaehlerLocal

variable {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S'] [Algebra R S] [Algebra R S']

/-- Killing the differentials is invariant under isomorphisms of algebras. -/
lemma kills_of_equiv (e : S ≃ₐ[R] S') {s : S} (hs : Kills R (e s)) : Kills R s := by
  letI : Algebra S S' := e.toRingHom.toAlgebra
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun r ↦ (e.commutes r).symm
  haveI : IsLocalization.Away (1 : S) S' :=
    IsLocalization.away_of_isUnit_of_bijective S' isUnit_one e.bijective
  exact kills_of_away R (ι := Unit) (a := fun _ ↦ 1) (by simp) (fun _ ↦ S') fun _ ↦ hs

end KaehlerLocal

namespace SemistableReduction

namespace TwoChartTower

open ProjectiveLine ProjectiveLine.ChartModule

variable {A : Type u} [CommRing A] {E : ℕ → TwoChartRings A}
  {e : ∀ n, TwoChartMap (E (n + 1)) (E n)} {I : Ideal A} [IsNoetherianRing A] [IsAdicComplete I A]
  {he0 : ∀ n, Function.Surjective (e n).f0} {he1 : ∀ n, Function.Surjective (e n).f1}
  {hker0 : ∀ n, RingHom.ker (e n).f0 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R0)}
  {hker1 : ∀ n, RingHom.ker (e n).f1 = (I ^ (n + 1)).map (algebraMap A (E (n + 1)).R1)}
  {hkill0 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥}
  {hkill1 : ∀ n, (I ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥}
  {hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0)}
  {hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)}
  {N : ChartModule A} [Module.Finite A[X] (Module.AEval' N.x0)]
  [Module.Finite A[X] (Module.AEval' N.x1)] {B : AlgStr N}
  {α : ∀ n, Hom N ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).M n)}

/-- **Differentials killed on all levels are killed on the algebraization**: if `c xʲ` (`j ≤ 1`)
kills `Ω[(E n).R0⁄D.R0]` and `c` kills `Ω[(E n).R1⁄D.R1]` for all `n` (the `D.R_i`-algebra
structures given by the level maps `β n`), then `c Xʲ` kills `Ω[B₀⁄D.R0]` and `c` kills
`Ω[B₁⁄D.R1]`. -/
theorem kills_shift (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n))
    {D : TwoChartRings A} {φ : Hom D.chartModule N} (h : D.algStr.IsHom B φ)
    {β : ∀ n, TwoChartMap D (E n)} (hβ : ∀ n, (α (n + 1)).comp φ = (β n).toHom)
    {c : A} {j : ℕ} (hj : j ≤ 1)
    (h0 : ∀ n, letI := (β n).f0.toRingHom.toAlgebra
      KaehlerLocal.Kills D.R0 (algebraMap A (E n).R0 c * (E n).x ^ j))
    (h1 : ∀ n, letI := (β n).f1.toRingHom.toAlgebra
      KaehlerLocal.Kills D.R1 (algebraMap A (E n).R1 c)) :
    (letI := B.algR0 h; KaehlerLocal.Kills D.R0 (B.const0 c * B.X0 ^ j)) ∧
      (letI := B.algR1 h; KaehlerLocal.Kills D.R1 (B.const1 c)) := by
  refine h.kills_of_quot I hj (fun n ↦ ?_) (fun n ↦ ?_)
  · letI := B.algR0 h
    rcases n with _ | n
    · haveI : Subsingleton (B.Ring0 ⧸ (I ^ 0).map B.const0) :=
        Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top])
      exact fun ω ↦ Subsingleton.elim (α := Ω[(B.Ring0 ⧸ (I ^ 0).map B.const0)⁄D.R0]) _ _
    letI := (β n).f0.toRingHom.toAlgebra
    let eq : (B.Ring0 ⧸ (I ^ (n + 1)).map B.const0) ≃ₐ[D.R0] (E n).R0 :=
      AlgEquiv.ofRingEquiv (f := quotEquivShift0 hα hB n) fun d ↦ by
        change (α (n + 1)).f0 (φ.f0 d) = (β n).f0 d
        exact Hom.f0_eq_of_eq (hβ n) d
    refine KaehlerLocal.kills_of_equiv eq ?_
    have hX : quotEquivShift0 hα hB n (Ideal.Quotient.mk _ B.X0) = (E n).x :=
      ((hB (n + 1)).ringHom0_X0).trans ((E n).ring0Equiv_X0)
    change KaehlerLocal.Kills D.R0 (quotEquivShift0 hα hB n (Ideal.Quotient.mk _ _))
    rw [map_mul, map_pow, map_mul, map_pow, quotEquivShift0_const0, hX]
    exact h0 n
  · letI := B.algR1 h
    rcases n with _ | n
    · haveI : Subsingleton (B.Ring1 ⧸ (I ^ 0).map B.const1) :=
        Ideal.Quotient.subsingleton_iff.2 (by rw [pow_zero, Ideal.one_eq_top, Ideal.map_top])
      exact fun ω ↦ Subsingleton.elim (α := Ω[(B.Ring1 ⧸ (I ^ 0).map B.const1)⁄D.R1]) _ _
    letI := (β n).f1.toRingHom.toAlgebra
    let eq : (B.Ring1 ⧸ (I ^ (n + 1)).map B.const1) ≃ₐ[D.R1] (E n).R1 :=
      AlgEquiv.ofRingEquiv (f := quotEquivShift1 hα hB n) fun d ↦ by
        change (α (n + 1)).f1 (φ.f1 d) = (β n).f1 d
        exact Hom.f1_eq_of_eq (hβ n) d
    refine KaehlerLocal.kills_of_equiv eq ?_
    change KaehlerLocal.Kills D.R1 (quotEquivShift1 hα hB n (Ideal.Quotient.mk _ _))
    rw [show quotEquivShift1 hα hB n (Ideal.Quotient.mk _ (B.const1 c)) = algebraMap A (E n).R1 c
      from ((hB (n + 1)).ringHom1_const1 c).trans ((E n).ring1Equiv_const1 c)]
    exact h1 n

/-- **The generic fibre of the algebraization is unramified over the base model** (outside
`V(Xʲ)` on the first chart): under the hypotheses of `kills_shift`, `B₀[1/(c Xʲ)]` is formally
unramified over `D.R0` and `B₁[1/c]` over `D.R1` (`KaehlerKill.subsingleton_away`); for `c = ϖ^m`
this is the generic fibre. -/
theorem formallyUnramified_shift (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = I ^ n • ⊤)
    (hB : ∀ n, B.IsHom
      ((systemShift I E e he0 he1 hker0 hker1 hkill0 hkill1 hfin0 hfin1).alg n) (α n))
    {D : TwoChartRings A} {φ : Hom D.chartModule N} (h : D.algStr.IsHom B φ)
    {β : ∀ n, TwoChartMap D (E n)} (hβ : ∀ n, (α (n + 1)).comp φ = (β n).toHom)
    {c : A} {j : ℕ} (hj : j ≤ 1)
    (h0 : ∀ n, letI := (β n).f0.toRingHom.toAlgebra
      KaehlerLocal.Kills D.R0 (algebraMap A (E n).R0 c * (E n).x ^ j))
    (h1 : ∀ n, letI := (β n).f1.toRingHom.toAlgebra
      KaehlerLocal.Kills D.R1 (algebraMap A (E n).R1 c)) :
    (letI := B.algR0 h;
      Algebra.FormallyUnramified D.R0 (Localization.Away (B.const0 c * B.X0 ^ j))) ∧
    (letI := B.algR1 h;
      Algebra.FormallyUnramified D.R1 (Localization.Away (B.const1 c))) := by
  obtain ⟨k0, k1⟩ := kills_shift hα hB h hβ hj h0 h1
  constructor
  · letI := B.algR0 h
    exact ⟨KaehlerKill.subsingleton_away k0 _⟩
  · letI := B.algR1 h
    exact ⟨KaehlerKill.subsingleton_away k1 _⟩

end TwoChartTower

end SemistableReduction
