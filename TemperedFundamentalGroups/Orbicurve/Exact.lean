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

Whenever `𝒮 ∖ {0}` is the zero set of some `0 ≠ D ∈ k[W]`, the ring `ringAway W 𝒮` of functions
regular away from `{0} ∪ 𝒮` is the localization `k[W][D⁻¹]` (`isLocalization_away_ringAway`,
`ringAwayEquiv`), i.e. `Spec (ringAway W 𝒮)` is the open subscheme `D(D) = W ∖ ({0} ∪ 𝒮)` of the
affine curve. The key input is the Nullstellensatz in `k[W]`
(`exists_pow_mem_span_of_zeroSet_subset`): if all geometric zeros of `h` are zeros of `D`, then
`D^n ∈ (h)` for some `n`, so that `h⁻¹ ∈ k[W][D⁻¹]`.

## Main statements

* `exists_polynomial_zeroSet`: a finite, symmetric, Galois stable `𝒮` is the zero set of some
  `Ψ(x)`, `0 ≠ Ψ ∈ k[X]`.
* `exists_pow_mem_span_of_zeroSet_subset`: the Nullstellensatz on the affine curve.
* `isLocalization_away_ringAway`, `ringAwayEquiv`: `ringAway W 𝒮 = k[W][D⁻¹]` if
  `zeroSet W D = 𝒮 ∖ {0}`.
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

/-! ### The Nullstellensatz on the affine curve -/

/-- A maximal ideal `𝔪` of a finitely generated `k`-algebra `R` is the kernel of a `k`-algebra
map `R → k̄` (Zariski's lemma). -/
theorem exists_algHom_eq_zero_iff {R : Type*} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    (𝔪 : Ideal R) [𝔪.IsMaximal] :
    ∃ χ : R →ₐ[k] AlgebraicClosure k, ∀ r, χ r = 0 ↔ r ∈ 𝔪 := by
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite k (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ 𝔪)
  haveI : Algebra.IsAlgebraic k (R ⧸ 𝔪) := Algebra.IsAlgebraic.of_finite k _
  refine ⟨(IsAlgClosed.lift : (R ⧸ 𝔪) →ₐ[k] AlgebraicClosure k).comp
    (Ideal.Quotient.mkₐ k 𝔪), fun r => ?_⟩
  rw [AlgHom.comp_apply, map_eq_zero, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]

instance : Algebra.FiniteType k W.toAffine.CoordinateRing :=
  inferInstanceAs (Algebra.FiniteType k (AdjoinRoot W.toAffine.polynomial))

variable [W.IsElliptic]

/-- **Nullstellensatz on the affine curve.** If every geometric zero of `h ∈ k[W]` is a zero of
`D`, then some power of `D` is a multiple of `h`. -/
theorem exists_pow_mem_span_of_zeroSet_subset {h D : W.toAffine.CoordinateRing}
    (hsub : zeroSet W h ⊆ zeroSet W D) : ∃ n : ℕ, D ^ n ∈ Ideal.span {h} := by
  haveI : IsJacobsonRing W.toAffine.CoordinateRing := isJacobsonRing_of_finiteType (A := k)
  have : D ∈ (Ideal.span {h}).jacobson := by
    refine Ideal.mem_sInf.mpr fun 𝔪 ⟨hle, h𝔪⟩ => ?_
    obtain ⟨χ, hχ⟩ := exists_algHom_eq_zero_iff (k := k) 𝔪
    have hχh : χ h = 0 := (hχ h).mpr (hle (Ideal.mem_span_singleton_self h))
    obtain ⟨_, hD⟩ := hsub ⟨pointOfC_ne_zero χ, by rw [evalPt_pointOfC]; exact hχh⟩
    rw [evalPt_pointOfC] at hD
    exact (hχ D).mp hD
  rwa [← Ideal.radical_eq_jacobson] at this

/-! ### `ringAway W 𝒮` as a localization of `k[W]` -/

section Localization

variable {𝒮 : Set (GeomPoint W)} {D : W.toAffine.CoordinateRing}

/-- If `𝒮 ∖ {0}` is the zero set of `D ≠ 0`, then `ringAway W 𝒮 = k[W][D⁻¹]` inside `k(W)`. -/
theorem ringAway_eq_range (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0}) :
    ringAway W 𝒮 = (locMap D hD).range := by
  have hD𝒮 : zeroSet W D ⊆ 𝒮 := h𝒮 ▸ Set.sdiff_subset
  refine le_antisymm (ringAway_le (algebraMap_mem_range_locMap hD) fun h hh => ?_) ?_
  · obtain ⟨n, hn⟩ := exists_pow_mem_span_of_zeroSet_subset (h := h) (D := D)
      fun Q hQ => h𝒮 ▸ ⟨hh hQ, ne_zero_of_mem_zeroSet hQ⟩
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hn
    have hι := congrArg (algebraMap _ (funField W)) hb
    rw [map_mul, map_pow] at hι
    have hne : algebraMap _ (funField W) D ^ n ≠ 0 :=
      pow_ne_zero _ ((_root_.map_ne_zero_iff _ (injective_algebraMap_funField W)).mpr hD)
    rw [← hι] at hne
    refine (mem_range_locMap hD).mpr ⟨b, n, ?_⟩
    rw [inv_pow, ← hι, mul_inv, ← mul_assoc, mul_inv_cancel₀ (left_ne_zero_of_mul hne), one_mul]
  · intro f hf
    obtain ⟨a, n, rfl⟩ := (mem_range_locMap hD).mp hf
    exact mul_mem (algebraMap_mem_ringAway a) (pow_mem (inv_mem_ringAway hD𝒮) n)

/-- If `𝒮 ∖ {0}` is the zero set of `D ≠ 0`, then `ringAway W 𝒮 ≃ k[W][D⁻¹]`: the spectrum of
`ringAway W 𝒮` is the open `D(D) = W ∖ ({0} ∪ 𝒮)` of the affine curve. -/
def ringAwayEquiv (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0}) :
    Localization.Away D ≃ₐ[k] ringAway W 𝒮 :=
  (AlgEquiv.ofInjective _ (injective_locMap hD)).trans
    (Subalgebra.equivOfEq _ _ (ringAway_eq_range hD h𝒮).symm)

@[simp] lemma coe_ringAwayEquiv (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0})
    (z : Localization.Away D) : (ringAwayEquiv hD h𝒮 z : funField W) = locMap D hD z :=
  rfl

lemma ringAwayEquiv_algebraMap (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0})
    (c : W.toAffine.CoordinateRing) :
    (ringAwayEquiv hD h𝒮 (algebraMap _ _ c) : funField W) = algebraMap _ (funField W) c := by
  rw [coe_ringAwayEquiv, locMap_algebraMap]

end Localization

/-- The `k[W]`-algebra structure of `ringAway W 𝒮 ⊇ k[W]`. -/
instance (𝒮 : Set (GeomPoint W)) : Algebra W.toAffine.CoordinateRing (ringAway W 𝒮) :=
  ((algebraMap W.toAffine.CoordinateRing (funField W)).codRestrict (ringAway W 𝒮)
    algebraMap_mem_ringAway).toAlgebra

omit [W.IsElliptic] in
@[simp] lemma coe_algebraMap_ringAway (𝒮 : Set (GeomPoint W)) (c : W.toAffine.CoordinateRing) :
    (algebraMap W.toAffine.CoordinateRing (ringAway W 𝒮) c : funField W) =
      algebraMap _ (funField W) c :=
  rfl

omit [W.IsElliptic] in
instance (𝒮 : Set (GeomPoint W)) :
    IsScalarTower k W.toAffine.CoordinateRing (ringAway W 𝒮) :=
  IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (IsScalarTower.algebraMap_apply _ _ _ a)

/-- **Exactness.** If `𝒮 ∖ {0}` is the zero set of `D ≠ 0`, then `ringAway W 𝒮` is the
localization of `k[W]` away from `D`. -/
theorem isLocalization_away_ringAway {𝒮 : Set (GeomPoint W)} {D : W.toAffine.CoordinateRing}
    (hD : D ≠ 0) (h𝒮 : zeroSet W D = 𝒮 \ {0}) : IsLocalization.Away D (ringAway W 𝒮) := by
  have hD𝒮 : zeroSet W D ⊆ 𝒮 := h𝒮 ▸ Set.sdiff_subset
  have hιD : algebraMap _ (funField W) D ≠ 0 :=
    (_root_.map_ne_zero_iff _ (injective_algebraMap_funField W)).mpr hD
  refine IsLocalization.Away.mk D ?_ (fun s => ?_) (fun a b hab => ⟨0, ?_⟩)
  · exact isUnit_iff_exists_inv.mpr
      ⟨⟨_, inv_mem_ringAway hD𝒮⟩, Subtype.ext (mul_inv_cancel₀ hιD)⟩
  · have hs : (s : funField W) ∈ (locMap D hD).range := ringAway_eq_range hD h𝒮 ▸ s.2
    obtain ⟨a, n, hs⟩ := (mem_range_locMap hD).mp hs
    refine ⟨n, a, Subtype.ext ?_⟩
    rw [Subalgebra.coe_mul, Subalgebra.coe_pow, coe_algebraMap_ringAway,
      coe_algebraMap_ringAway, hs, inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hιD),
      mul_one]
  · rw [pow_zero, one_mul, one_mul]
    exact injective_algebraMap_funField W (congrArg Subtype.val hab)

end

end TemperedFundamentalGroups.Orbicurve
