/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Tempered.Level
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdjoinRoot

/-!
# The quadratic level `R[X] ⧸ (X² - c)` with its involution (Blueprint §10.3.8, `v(q) = 1`, B3a)

For a commutative ring `R` with `2` and `c` units and a trivial group `A`:

* `QuadraticLevel.B`: the coded algebra `R[X₀] ⧸ (X₀² - c)` (`LevelRing R 1 I`), finite
  (`≅ AdjoinRoot (X² - c)`, monic) and étale (`≅` the standard étale algebra of
  `(X² - c, 1)`, since `2X · X/(2c) - (X² - c)/c = 1`);
* `QuadraticLevel.σ`: the involution `X₀ ↦ -X₀`;
* `QuadraticLevel.level`: the level `(B, ⟨σ⟩)` of `[Spec R / A]`.
-/

universe u

open Polynomial Pi1.Orbifold

namespace TemperedFundamentalGroups.QuadraticLevel

noncomputable section

variable {R : Type u} [CommRing R] (c : R)

/-- The relation `X₀² - c`. -/
def I : Ideal (MvPolynomial (Fin 1) R) :=
  Ideal.span {MvPolynomial.X 0 ^ 2 - MvPolynomial.C c}

/-- The algebra `R[X₀] ⧸ (X₀² - c)`. -/
abbrev B : Type u := LevelRing R 1 (I c)

/-- The class of `X₀`. -/
def x : B c := Ideal.Quotient.mk _ (MvPolynomial.X 0)

lemma x_sq : x c ^ 2 = algebraMap R (B c) c := by
  have h : (MvPolynomial.X 0 ^ 2 - MvPolynomial.C c : MvPolynomial (Fin 1) R) ∈ I c :=
    Ideal.subset_span rfl
  have := Ideal.Quotient.eq_zero_iff_mem.2 h
  rw [map_sub, map_pow, sub_eq_zero] at this
  exact this

/-- The polynomial `X² - c`. -/
abbrev f : R[X] := X ^ 2 - Polynomial.C c

lemma monic_f : (f c).Monic := monic_X_pow_sub_C _ two_ne_zero

lemma aeval_x : aeval (x c) (f c) = 0 := by
  rw [map_sub, map_pow, aeval_X, aeval_C, x_sq, sub_self]

/-- Maps out of `B c` are determined by the image of `x`. -/
lemma algHom_ext {S : Type*} [CommRing S] [Algebra R S] {φ ψ : B c →ₐ[R] S}
    (h : φ (x c) = ψ (x c)) : φ = ψ := by
  refine Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext fun i ↦ ?_)
  rw [Subsingleton.elim i 0]
  exact h

/-- The map `B c → S` sending `x` to a root `s` of `X² - c`. -/
def lift {S : Type*} [CommRing S] [Algebra R S] (s : S) (hs : aeval s (f c) = 0) :
    B c →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval fun _ ↦ s) (fun a ha ↦ by
    have hle : I c ≤ RingHom.ker (MvPolynomial.aeval (R := R) fun _ : Fin 1 ↦ s).toRingHom := by
      rw [I, Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_pow,
        MvPolynomial.aeval_X, MvPolynomial.aeval_C]
      simpa [f] using hs
    exact hle ha)

@[simp] lemma lift_x {S : Type*} [CommRing S] [Algebra R S] (s : S) (hs : aeval s (f c) = 0) :
    lift c s hs (x c) = s := by
  simp [lift, x]

/-- `B c ≃ AdjoinRoot (X² - c)`. -/
def equivAdjoinRoot : B c ≃ₐ[R] AdjoinRoot (f c) :=
  AlgEquiv.ofAlgHom (lift c (AdjoinRoot.root (f c)) (by
      rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]))
    (AdjoinRoot.liftAlgHom (f c) (Algebra.ofId R (B c)) (x c) (by
      exact aeval_x c))
    (AdjoinRoot.algHom_ext (by simp))
    (algHom_ext c (by simp))

instance finite : Module.Finite R (B c) :=
  haveI := (AdjoinRoot.powerBasis' (monic_f c)).finite
  Module.Finite.equiv (equivAdjoinRoot c).symm.toLinearEquiv

variable {c} (h2 : IsUnit (2 : R)) (hc : IsUnit c)

/-- The standard étale pair `(X² - c, 1)`. -/
def pair : StandardEtalePair R where
  f := f c
  monic_f := monic_f c
  g := 1
  cond := by
    obtain ⟨u, hu⟩ := h2.mul hc
    refine ⟨Polynomial.C (↑u⁻¹ : R) * X, Polynomial.C (-(↑u⁻¹ : R) * 2), 0, ?_⟩
    rw [pow_zero, derivative_sub, derivative_X_pow, derivative_C, sub_zero]
    have hu' : (↑u⁻¹ : R) * (2 * c) = 1 := by rw [← hu, Units.inv_mul]
    trans Polynomial.C ((↑u⁻¹ : R) * (2 * c))
    · simp only [f, map_mul, map_neg, Nat.cast_ofNat, map_ofNat]
      ring
    · rw [hu', map_one]

/-- `B c ≃` the standard étale algebra of `(X² - c, 1)`. -/
def equivStandard : B c ≃ₐ[R] (pair h2 hc).Ring :=
  AlgEquiv.ofAlgHom (lift c (pair h2 hc).X (pair h2 hc).hasMap_X.1)
    ((pair h2 hc).lift (x c) ⟨aeval_x c, by simp [pair]⟩)
    ((pair h2 hc).hom_ext (by simp))
    (algHom_ext c (by simp))

include h2 hc in
lemma etale : Algebra.Etale R (B c) :=
  Algebra.Etale.of_equiv (equivStandard h2 hc).symm

variable (c) in
lemma aeval_neg_x : aeval (-x c) (f c) = 0 := by
  have e : (-x c) ^ 2 = x c ^ 2 := by ring
  rw [map_sub, map_pow, aeval_X, aeval_C, e, x_sq, sub_self]

variable (c) in
/-- **The involution** `x ↦ -x`. -/
def σ : B c ≃ₐ[R] B c :=
  AlgEquiv.ofAlgHom (lift c (-x c) (aeval_neg_x c)) (lift c (-x c) (aeval_neg_x c))
    (algHom_ext c (by simp)) (algHom_ext c (by simp))

variable (c) in
@[simp] lemma σ_x : σ c (x c) = -x c := lift_x c _ (aeval_neg_x c)

variable (c) in
lemma σ_σ (b : B c) : σ c (σ c b) = b := by
  have : (σ c).toAlgHom.comp (σ c).toAlgHom = AlgHom.id R (B c) :=
    algHom_ext c (by simp)
  exact AlgHom.congr_fun this b

variable (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A]

variable (c) in
/-- The involution as a semilinear automorphism over `1 ∈ A`. -/
def σS : SemilinearAut R A (B c) :=
  ⟨1, (σ c).toRingEquiv, fun r ↦ by simp⟩

/-- **The level `(R[x]/(x² - c), ⟨σ⟩)`** of `[Spec R / A]` (`A` trivial). -/
def level : FiniteLevel R A where
  n := 1
  I := I c
  etale := etale h2 hc
  finite := finite c
  H := Subgroup.zpowers (σS (c := c) (A := A))
  surjective _ := ⟨1, Subgroup.one_mem _, Subsingleton.elim _ _⟩

end

end TemperedFundamentalGroups.QuadraticLevel
