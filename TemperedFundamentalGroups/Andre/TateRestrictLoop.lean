/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictObject
import TemperedFundamentalGroups.Andre.TateLoop

/-!
# The base loop for the restricted Tate object (Blueprint §10.3.8, `v(q) = 1`, B3g)

`Pres.HarmonicTateR`: the analogue of `Pres.HarmonicTate` for the restricted Tate object `X₀'`
(decomposition `decompR`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Set TopologicalSpace

namespace TemperedFundamentalGroups

open CurveConfig

noncomputable section

open TempObj TateRestrict RamifiedQuadratic SemistableReduction.W10Apply

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)
  [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero K]
  (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  (R : Type u) [CommRing R] [Algebra K R] [IsReduced R] {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A] {xW : R}

namespace Pres

variable {Y : TempObj O R A} (Q : Pres xW Y)

/-- **`HarmonicTate` for the restricted Tate object** `X₀'` (`v(q) = 1`): as `Pres.HarmonicTate`,
for the decomposition `decompR` of its special fibre. -/
def HarmonicTateR (ℰ : Set (Set (specialFibre (modelR hϖ b₄ b₆).toSpec)))
    (a : Q.U ⟶ X₀' hϖ b₄ b₆ R heqR A) : Prop :=
  (∀ i : irreducibleComponents Q.Lv.Z,
    specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i = (decompR hϖ b₄ b₆).C →
    ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∈ (decompR hϖ b₄ b₆).Cp) ∧
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C (lastLab i L) ∈ ℰ) ∧
  (∀ i : irreducibleComponents Q.Lv.Z,
    specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C i ∈ ℰ →
    ∃ L : List (Q.Lv.Z × irreducibleComponents Q.Lv.Z),
      IncWalk (curveConfig Q.Lv.Z Q.hdim) i L ∧
      (∀ p ∈ L, specialFibreMap a.ψ a.ψ_toSpec p.1 ∉ (decompR hϖ b₄ b₆).Cp) ∧
      specialFibreMap a.ψ a.ψ_toSpec '' (curveConfig Q.Lv.Z Q.hdim).C (lastLab i L) =
        (decompR hϖ b₄ b₆).C)

end Pres

end

end TemperedFundamentalGroups
