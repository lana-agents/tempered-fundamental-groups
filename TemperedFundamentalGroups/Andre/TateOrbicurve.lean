/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateObject
import TemperedFundamentalGroups.Orbicurve.GeomStable

/-!
# `X₀` for the coordinate ring of `E ∖ (E[ℓ] + M)`

Let `E : y² + xy = x³ + π² b₄ x + π² b₆` over `K` (`a₁ = 1`, `a₂ = a₃ = 0`) with `π ∈ O` a nonzero
non-unit and `b₄, b₆ ∈ O`. The generic point `(x, y)` of `E` lies in every subalgebra of the
function field containing the coordinate ring, in particular in the ring
`R = geomOrbicurveRing W ℓ M` of `Y = E ∖ (E[ℓ] + M)`. This gives the data
`TateObject.Data O R` (`TateOrbicurve.data`), hence the object `X₀` over the level `(R, 1)`, its
deck torsor and the continuous character `temperedPi1 → ℤ` for `[Y / A]` with `A` trivial
(`TateOrbicurve.character`).
-/

universe u

open WeierstrassCurve

namespace TemperedFundamentalGroups

open Orbicurve

namespace TateOrbicurve

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} (W : WeierstrassCurve K)

/-- `W` is the curve `y² + xy = x³ + π² b₄ x + π² b₆`. -/
structure IsTate (π b₄ b₆ : O) : Prop where
  a₁ : W.a₁ = 1
  a₂ : W.a₂ = 0
  a₃ : W.a₃ = 0
  a₄ : W.a₄ = (π : K) ^ 2 * b₄
  a₆ : W.a₆ = (π : K) ^ 2 * b₆

variable {W}

lemma equation_gen_of_isTate {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) :
    yGen W ^ 2 + xGen W * yGen W = xGen W ^ 3 +
      algebraMap K (funField W) ((π : K) ^ 2 * b₄) * xGen W +
      algebraMap K (funField W) ((π : K) ^ 2 * b₆) := by
  have h := equation_gen W
  rw [Affine.equation_iff] at h
  simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, hW.a₁, hW.a₂,
    hW.a₃, hW.a₄, hW.a₆, map_one, map_zero] at h
  linear_combination h

/-- The data of `X₀` for a subalgebra of the function field containing the coordinates. -/
def dataOfSubalgebra {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O) (S : Subalgebra K (funField W)) (hx : xGen W ∈ S)
    (hy : yGen W ∈ S) : TateObject.Data O S where
  π := π
  b₄ := b₄
  b₆ := b₆
  π_ne_zero := hπ
  π_mem := hπm
  x := ⟨xGen W, hx⟩
  y := ⟨yGen W, hy⟩
  equation := Subtype.ext (by simpa using equation_gen_of_isTate hW)

variable [DecidableEq K]

/-- **The data of `X₀` for the orbicurve ring** `R = geomOrbicurveRing W ℓ M` of
`E ∖ (E[ℓ] + M)`. -/
def data {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O) (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) :
    TateObject.Data O (geomOrbicurveRing W ℓ M) :=
  dataOfSubalgebra hW hπ hπm _ (algebraMap_mem_ringAway _) (algebraMap_mem_ringAway _)

variable (A : Type u) [Group A] [Subsingleton A] (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point)
  [MulSemiringAction A (geomOrbicurveRing W ℓ M)]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra (geomOrbicurveRing W ℓ M) Ω]
  [IsScalarTower K (geomOrbicurveRing W ℓ M) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The continuous character `temperedPi1 → ℤ`** of the Tate curve minus `E[ℓ] + M`
(scheme case: `A` trivial), defined by the deck torsor `X₀`. -/
def character {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O) :
    temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV →* Multiplicative ℤ :=
  TateObject.character (data hW hπ hπm ℓ M) V hV

lemma continuous_character {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O) :
    Continuous (character A ℓ M V hV hW hπ hπm) :=
  TateObject.continuous_character _ V hV

end

end TateOrbicurve

namespace Orbicurve

/-- Transcendence passes to any subalgebra containing the element. -/
lemma transcendental_subalgebra {K : Type u} [Field K] {A : Type u} [CommRing A] [Algebra K A]
    (S : Subalgebra K A) {a : A} (ha : a ∈ S) (h : Transcendental K a) :
    Transcendental K (⟨a, ha⟩ : S) := by
  rw [transcendental_iff_injective] at h ⊢
  have : S.val.comp (Polynomial.aeval (⟨a, ha⟩ : S)) = Polynomial.aeval a :=
    Polynomial.algHom_ext (by simp)
  exact fun p q hpq ↦ h (by rw [← this]; simp [hpq])

end Orbicurve

namespace TateOrbicurve

variable {K : Type u} [Field K] {O : ValuationSubring K} {W : WeierstrassCurve K} [DecidableEq K]

/-- **For the IUT data, `T.x` is transcendental over `K`** (the non-degeneracy condition of
Blueprint §10.3.8). -/
theorem transcendental_data_x {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O) (ℓ : ℕ) (M : AddSubgroup W.toAffine.Point) :
    Transcendental K (data hW hπ hπm ℓ M).x :=
  Orbicurve.transcendental_subalgebra _ _ (transcendental_xGen W)

end TateOrbicurve

end TemperedFundamentalGroups
