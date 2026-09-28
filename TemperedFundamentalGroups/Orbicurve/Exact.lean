/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Orbicurve.GeomStable

/-!
# `ringAway W 𝒮` is the coordinate ring of the open complement

Let `𝒮 ⊆ W(k̄)` be a finite set of geometric points, stable under `P ↦ -P` and under
`Gal(k̄/k)`. Then `𝒮 ∖ {0}` is the geometric zero set of a function `Ψ(x)` of `x` alone
(`exists_polynomial_zeroSet`): `Ψ` is the product of the minimal polynomials over `k` of the
`x`-coordinates of the affine points of `𝒮`.

## Main statements

* `exists_polynomial_zeroSet`: a finite, symmetric, Galois stable `𝒮` is the zero set of some
  `Ψ(x)`, `0 ≠ Ψ ∈ k[X]`.
-/

universe u

open Polynomial WeierstrassCurve WeierstrassCurve.Affine

namespace TemperedFundamentalGroups.Orbicurve

noncomputable section

variable {k : Type u} [Field k] {W : WeierstrassCurve k}

/-! ### Galois stable sets of geometric points -/

variable (W) in
/-- A set of geometric points is *Galois stable* if it is stable under `Aut(k̄/k)`. -/
def IsGaloisStable (𝒮 : Set (GeomPoint W)) : Prop :=
  ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, ∀ P ∈ 𝒮,
    Point.map (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) P ∈ 𝒮

/-- Two affine geometric points with conjugate `x`-coordinates are, up to sign, conjugate. -/
lemma exists_map_eq_or_neg {P Q : GeomPoint W} (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : aeval (xOf Q) (minpoly k (xOf P)) = 0) :
    ∃ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k,
      Q = Point.map (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) P ∨
        Q = -Point.map (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) P := by
  have hint : IsIntegral k (xOf P) := Algebra.IsIntegral.isIntegral _
  have hmin : minpoly k (xOf Q) = minpoly k (xOf P) :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hint) h (minpoly.monic hint)).symm
  obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure k)).mp hmin)
  refine ⟨σ, ?_⟩
  have hσP : Point.map (σ : AlgebraicClosure k →ₐ[k] AlgebraicClosure k) P ≠ 0 := by
    rwa [Ne, map_eq_zero_iff]
  rw [eq_some_xOf_yOf hQ, eq_some_xOf_yOf hσP]
  refine Point.X_eq_iff.mp ?_
  rw [xOf_map, ← hσ]
  rfl

/-- **A finite, symmetric, Galois stable set of geometric points is the zero set of a function
of `x`.** -/
theorem exists_polynomial_zeroSet {𝒮 : Set (GeomPoint W)} (hfin : 𝒮.Finite)
    (hneg : ∀ P ∈ 𝒮, -P ∈ 𝒮) (hgal : IsGaloisStable W 𝒮) :
    ∃ Ψ : k[X], Ψ ≠ 0 ∧
      zeroSet W (algebraMap k[X] W.toAffine.CoordinateRing Ψ) = 𝒮 \ {0} := by
  classical
  set s := hfin.toFinset.filter (· ≠ 0)
  refine ⟨∏ P ∈ s, minpoly k (xOf P), Finset.prod_ne_zero_iff.mpr fun P _ =>
    minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
  ext Q
  simp only [mem_zeroSet, evalPt_algebraMap_polynomial, map_prod, Finset.prod_eq_zero_iff,
    Set.mem_sdiff, Set.mem_singleton_iff, s, Finset.mem_filter, Set.Finite.mem_toFinset]
  constructor
  · rintro ⟨hQ, P, ⟨hP𝒮, hP⟩, h⟩
    refine ⟨?_, hQ⟩
    obtain ⟨σ, rfl | rfl⟩ := exists_map_eq_or_neg hP hQ h
    exacts [hgal σ P hP𝒮, hneg _ (hgal σ P hP𝒮)]
  · rintro ⟨hQ𝒮, hQ⟩
    exact ⟨hQ, Q, ⟨hQ𝒮, hQ⟩, minpoly.aeval k _⟩

end

end TemperedFundamentalGroups.Orbicurve
