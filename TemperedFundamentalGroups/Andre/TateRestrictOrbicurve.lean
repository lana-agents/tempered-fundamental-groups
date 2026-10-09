/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictLevel
import TemperedFundamentalGroups.Andre.TateOrbicurve

/-!
# The data of `X₀'` for IUT's orbicurves (`v(q) = 1`)

`W : y² + xy = x³ + ϖ b₄ x + ϖ b₆` (`IsTate1`, `ϖ` a uniformizer). The generic point `(x, y)` lies
in `R = geomOrbicurveRing W ℓ M` (`heqR_of_isTate1`), `x` is transcendental, and over
`O' = O_{K(√ϖ)}` the Tate data `(√ϖ, b₄, b₆)` have squarefree `d` when `W` is elliptic
(`squarefree_of_isTate1`).
-/

universe u

open WeierstrassCurve

namespace TemperedFundamentalGroups

open Orbicurve RamifiedQuadratic SemistableReduction.W10Apply

namespace TateOrbicurve

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} (W : WeierstrassCurve K)

/-- `W` is the curve `y² + xy = x³ + ϖ b₄ x + ϖ b₆`. -/
structure IsTate1 (ϖ b₄ b₆ : O) : Prop where
  a₁ : W.a₁ = 1
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = (ϖ : K) * b₄
  a₆ : W.a₆ = (ϖ : K) * b₆

variable {W}

lemma equation_gen_of_isTate1 {ϖ b₄ b₆ : O} (hW : IsTate1 W ϖ b₄ b₆) :
    yGen W ^ 2 + xGen W * yGen W = xGen W ^ 3 +
      algebraMap K (funField W) ((ϖ : K) * b₄) * xGen W +
      algebraMap K (funField W) ((ϖ : K) * b₆) := by
  have h := equation_gen W
  rw [Affine.equation_iff] at h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, hW.a₁, hW.a₂,
    hW.a₃, hW.a₄, hW.a₆, map_one, map_zero] at h
  linear_combination h

variable (W) [DecidableEq K]

/-- The coordinate `x` in `R = geomOrbicurveRing W ℓ M`. -/
def xR (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) : geomOrbicurveRing W ℓ M :=
  ⟨xGen W, algebraMap_mem_ringAway _⟩

/-- The coordinate `y` in `R = geomOrbicurveRing W ℓ M`. -/
def yR (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) : geomOrbicurveRing W ℓ M :=
  ⟨yGen W, algebraMap_mem_ringAway _⟩

variable {W}

lemma heqR_of_isTate1 {ϖ b₄ b₆ : O} (hW : IsTate1 W ϖ b₄ b₆) (ℓ : ℕ)
    (M : AddSubgroup W.toAffine.Point) :
    yR W ℓ M ^ 2 + xR W ℓ M * yR W ℓ M = xR W ℓ M ^ 3 +
      algebraMap K (geomOrbicurveRing W ℓ M) ((ϖ : K) * b₄) * xR W ℓ M +
      algebraMap K (geomOrbicurveRing W ℓ M) ((ϖ : K) * b₆) :=
  Subtype.ext (by simpa [xR, yR] using equation_gen_of_isTate1 hW)

lemma transcendental_xR (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) :
    Transcendental K (xR W ℓ M) :=
  Orbicurve.transcendental_subalgebra _ _ (transcendental_xGen W)

omit [DecidableEq K] in
/-- **`d` is squarefree over `O'`** for an elliptic curve `IsTate1 W ϖ b₄ b₆`. -/
lemma squarefree_of_isTate1 [CharZero K] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [W.IsElliptic] {ϖ b₄ b₆ : O}
    (hW : IsTate1 W ϖ b₄ b₆) :
    Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)) := by
  haveI : IsDiscreteValuationRing (O' ϖ) := isDiscreteValuationRing_OE O _
  have h2 : (2 : O' ϖ) ≠ 0 := fun h ↦ two_ne_zero (congrArg Subtype.val h : ((2 : O' ϖ) : K' ϖ) = 0)
  refine TateNormal.squarefree_dpoly _ _ _ h2 fun hΔ ↦ ?_
  have e := TateNormal.Δ_eq_tateDisc (π := sO ϖ) (b₄ := algebraMap O (O' ϖ) b₄)
    (b₆ := algebraMap O (O' ϖ) b₆) (O' ϖ).subtype (W.baseChange (K' ϖ))
    (by simp [hW.a₁]) (by simp [hW.a₂]) (by simp [hW.a₃])
    (by
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₄, hW.a₄, map_mul, map_pow]
      rw [show (O' ϖ).subtype (sO ϖ) = s ϖ from rfl, s_sq]
      rfl)
    (by
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₆, hW.a₆, map_mul, map_pow]
      rw [show (O' ϖ).subtype (sO ϖ) = s ϖ from rfl, s_sq]
      rfl)
  rw [hΔ, map_zero, WeierstrassCurve.baseChange, map_Δ] at e
  exact W.isUnit_Δ.ne_zero ((algebraMap K (K' ϖ)).injective (e.trans (map_zero _).symm))

end

end TateOrbicurve

end TemperedFundamentalGroups
