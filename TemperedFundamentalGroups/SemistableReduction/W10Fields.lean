/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The function fields of a finite cover of the x-line after an extension of constants

Blueprint §9.7a (W10 assembly, step 2). Let `A` be a finite torsion-free `K[X]`-algebra (in W10:
the cover `B`, finite over the x-line `K[x] ⊆ R`) and `M / K` a field extension (`M = E` or
`M = K̄`).

* `BX K M A := M[X] ⊗_{K[X]} A` (this is `M ⊗_K A`), free over `M[X]`;
* `LX K M A := M(X) ⊗_{M[X]} BX`, the localization of `BX` at the nonzero polynomials
  (`isLocalization_LX`), a finite `M(X)`-algebra; `BX → LX` is injective (`injective_toLX`);
* if `BX` is reduced, `LX` is the product of the fields `Comp K M A 𝔪 = LX ⧸ 𝔪` over its maximal
  ideals (`equivPi`), each finite over `M(X)`;
* if moreover `BX` is integrally closed in `LX`, then `BX` is the product of its images
  `D 𝔪 ⊆ Comp 𝔪` (`bijective_toPiD`), and every element of `Comp 𝔪` integral over `M[X]` lies in
  `D 𝔪` (`mem_D_of_isIntegral`).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace W10Fields

variable (K : Type u) [Field K] (M : Type u) [Field M] [Algebra K M]

/-- `K[X] → M[X]`, coefficientwise. -/
noncomputable abbrev polyAlgebra : Algebra K[X] M[X] :=
  (Polynomial.mapRingHom (algebraMap K M)).toAlgebra

attribute [local instance] polyAlgebra

variable (A : Type u) [CommRing A] [Algebra K[X] A]

/-- `M ⊗_K A`, realized as `M[X] ⊗_{K[X]} A`. -/
def BX : Type u := M[X] ⊗[K[X]] A

namespace BX

noncomputable instance : CommRing (BX K M A) := inferInstanceAs (CommRing (M[X] ⊗[K[X]] A))

noncomputable instance : Algebra M[X] (BX K M A) := inferInstanceAs (Algebra M[X] (M[X] ⊗[K[X]] A))

/-- `A → M ⊗_K A`. -/
noncomputable def ofA : A →+* BX K M A :=
  (Algebra.TensorProduct.includeRight : A →ₐ[K[X]] M[X] ⊗[K[X]] A).toRingHom

instance [Module.Finite K[X] A] : Module.Finite M[X] (BX K M A) :=
  inferInstanceAs (Module.Finite M[X] (M[X] ⊗[K[X]] A))

instance [Module.Free K[X] A] : Module.Free M[X] (BX K M A) :=
  inferInstanceAs (Module.Free M[X] (M[X] ⊗[K[X]] A))

end BX

/-- The localization `M(X) ⊗_{M[X]} (M ⊗_K A)` of `M ⊗_K A` at the nonzero polynomials. -/
def LX : Type u := RatFunc M ⊗[M[X]] BX K M A

namespace LX

noncomputable instance : CommRing (LX K M A) :=
  inferInstanceAs (CommRing (RatFunc M ⊗[M[X]] BX K M A))

noncomputable instance : Algebra (RatFunc M) (LX K M A) :=
  inferInstanceAs (Algebra (RatFunc M) (RatFunc M ⊗[M[X]] BX K M A))

noncomputable instance : Algebra M[X] (LX K M A) :=
  inferInstanceAs (Algebra M[X] (RatFunc M ⊗[M[X]] BX K M A))

instance : IsScalarTower M[X] (RatFunc M) (LX K M A) :=
  inferInstanceAs (IsScalarTower M[X] (RatFunc M) (RatFunc M ⊗[M[X]] BX K M A))

noncomputable instance : Algebra (BX K M A) (LX K M A) :=
  Algebra.TensorProduct.rightAlgebra

instance : IsScalarTower M[X] (BX K M A) (LX K M A) :=
  Algebra.TensorProduct.right_isScalarTower

instance [Module.Finite K[X] A] : Module.Finite (RatFunc M) (LX K M A) :=
  inferInstanceAs (Module.Finite (RatFunc M) (RatFunc M ⊗[M[X]] BX K M A))

instance isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X])) (LX K M A) :=
  IsLocalization.tensorRight (RatFunc M) (nonZeroDivisors M[X])

instance [Module.Finite K[X] A] : IsArtinianRing (LX K M A) :=
  IsArtinianRing.of_finite (RatFunc M) (LX K M A)

end LX

section TorsionFree

variable [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A]

/-- Nonzero polynomials are nonzerodivisors of `M ⊗_K A`. -/
lemma algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X]) ≤
      nonZeroDivisors (BX K M A) := by
  rintro _ ⟨q, hq, rfl⟩
  have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
  rw [mem_nonZeroDivisors_iff_right]
  intro z hz
  rw [mul_comm, ← Algebra.smul_def] at hz
  exact (smul_eq_zero.1 hz).resolve_left hq0

/-- `M ⊗_K A → M(X) ⊗_{M[X]} (M ⊗_K A)` is injective. -/
lemma injective_toLX : Function.Injective (algebraMap (BX K M A) (LX K M A)) :=
  IsLocalization.injective (LX K M A) (algebraMapSubmonoid_le K M A)

omit [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A] in
/-- `LX` is reduced if `M ⊗_K A` is. -/
lemma isReduced_LX [IsReduced (BX K M A)] : IsReduced (LX K M A) :=
  isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X]))
    (LX K M A) (inferInstanceAs (IsReduced (BX K M A)))

end TorsionFree

/-! ### The components -/

instance (𝔪 : MaximalSpectrum (LX K M A)) : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal

/-- The component `LX ⧸ 𝔪` (a field). -/
abbrev Comp (𝔪 : MaximalSpectrum (LX K M A)) : Type u := LX K M A ⧸ 𝔪.asIdeal

noncomputable instance (𝔪 : MaximalSpectrum (LX K M A)) : Field (Comp K M A 𝔪) :=
  Ideal.Quotient.field _

instance [Module.Finite K[X] A] (𝔪 : MaximalSpectrum (LX K M A)) :
    FiniteDimensional (RatFunc M) (Comp K M A 𝔪) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ (RatFunc M) 𝔪.asIdeal).toLinearMap
    Ideal.Quotient.mk_surjective

instance [Module.Finite K[X] A] : Finite (MaximalSpectrum (LX K M A)) :=
  inferInstance

/-- `LX` is the product of its components. -/
noncomputable def equivPi [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A]
    [IsReduced (BX K M A)] :
    LX K M A ≃ₐ[LX K M A] ∀ 𝔪 : MaximalSpectrum (LX K M A), Comp K M A 𝔪 :=
  haveI := isReduced_LX K M A
  IsArtinianRing.equivPi (LX K M A)

/-- The image `D 𝔪` of `M ⊗_K A` in the component `𝔪`. -/
noncomputable def D (𝔪 : MaximalSpectrum (LX K M A)) : Subring (Comp K M A 𝔪) :=
  ((Ideal.Quotient.mk 𝔪.asIdeal).comp (algebraMap (BX K M A) (LX K M A))).range

/-- The map `M ⊗_K A → Π 𝔪, D 𝔪`. -/
noncomputable def toPiD : BX K M A →+* ∀ 𝔪, D K M A 𝔪 :=
  RingHom.pi fun 𝔪 ↦ ((Ideal.Quotient.mk 𝔪.asIdeal).comp
    (algebraMap (BX K M A) (LX K M A))).rangeRestrict

section Normal

variable [Module.Finite K[X] A] [Module.IsTorsionFree K[X] A] [IsReduced (BX K M A)]

lemma equivPi_apply (y : LX K M A) (𝔪 : MaximalSpectrum (LX K M A)) :
    equivPi K M A y 𝔪 = Ideal.Quotient.mk 𝔪.asIdeal y :=
  haveI := isReduced_LX K M A
  IsArtinianRing.equivPi_apply (LX K M A) y 𝔪

open scoped Classical in
/-- The idempotent of the component `𝔪`. -/
noncomputable def idem (𝔪 : MaximalSpectrum (LX K M A)) : LX K M A :=
  (equivPi K M A).symm (Pi.single 𝔪 1)

open scoped Classical in
lemma mk_idem (𝔪 𝔫 : MaximalSpectrum (LX K M A)) :
    Ideal.Quotient.mk 𝔫.asIdeal (idem K M A 𝔪) = Pi.single (M := fun 𝔪 ↦ Comp K M A 𝔪) 𝔪 1 𝔫 := by
  rw [← equivPi_apply, idem, AlgEquiv.apply_symm_apply]

lemma isIntegral_idem (𝔪 : MaximalSpectrum (LX K M A)) : IsIntegral (BX K M A) (idem K M A 𝔪) := by
  classical
  have : idem K M A 𝔪 * idem K M A 𝔪 = idem K M A 𝔪 := by
    rw [idem, ← map_mul]
    congr 1
    ext 𝔫
    by_cases h : 𝔫 = 𝔪
    · subst h; simp
    · simp [h]
  refine ⟨X ^ 2 - X, monic_X_pow_sub (degree_X_le.trans_lt (by norm_num)), ?_⟩
  rw [eval₂_sub, eval₂_X_pow, eval₂_X, pow_two, this, sub_self]

variable (hn : IsIntegrallyClosedIn (BX K M A) (LX K M A))

include hn in
lemma exists_idem (𝔪 : MaximalSpectrum (LX K M A)) :
    ∃ ε : BX K M A, algebraMap (BX K M A) (LX K M A) ε = idem K M A 𝔪 :=
  (IsIntegrallyClosedIn.isIntegral_iff (R := BX K M A) (A := LX K M A)).1 (isIntegral_idem K M A 𝔪)

include hn in
/-- **`M ⊗_K A` is the product of its images in the components** (normality). -/
theorem bijective_toPiD : Function.Bijective (toPiD K M A) := by
  classical
  constructor
  · intro b b' h
    apply injective_toLX K M A
    apply (equivPi K M A).injective
    ext 𝔫
    have := congrArg Subtype.val (congrFun h 𝔫)
    rw [equivPi_apply, equivPi_apply]
    exact this
  · intro d
    haveI := Fintype.ofFinite (MaximalSpectrum (LX K M A))
    choose b hb using fun 𝔪 ↦ (d 𝔪).2
    choose ε hε using exists_idem K M A hn
    refine ⟨∑ 𝔪, ε 𝔪 * b 𝔪, ?_⟩
    ext 𝔫
    change Ideal.Quotient.mk 𝔫.asIdeal (algebraMap (BX K M A) (LX K M A) (∑ 𝔪, ε 𝔪 * b 𝔪)) = _
    simp only [map_sum, map_mul, hε, mk_idem]
    rw [Finset.sum_eq_single 𝔫]
    · simp only [Pi.single_eq_same, one_mul]
      exact hb 𝔫
    · intro 𝔪 _ h
      simp [Ne.symm h]
    · simp

include hn in
/-- **The components of `M ⊗_K A` are integrally closed over `M[X]`**: every element of the
component `𝔪` integral over `M[X]` lies in `D 𝔪`. -/
theorem mem_D_of_isIntegral (𝔪 : MaximalSpectrum (LX K M A)) {z : Comp K M A 𝔪}
    (hz : IsIntegral M[X] z) : z ∈ D K M A 𝔪 := by
  classical
  obtain ⟨p, hpm, hp⟩ := hz
  set w := (equivPi K M A).symm (Pi.single 𝔪 z)
  have hw : IsIntegral M[X] w := by
    refine ⟨X * p, monic_X.mul hpm, ?_⟩
    apply (equivPi K M A).injective
    set φ := (equivPi K M A).toAlgHom.restrictScalars M[X]
    have h := Polynomial.aeval_algHom_apply φ w (X * p)
    change φ (aeval w (X * p)) = φ 0
    rw [← h, map_zero]
    have hφw : φ w = Pi.single 𝔪 z := (equivPi K M A).apply_symm_apply _
    rw [hφw]
    ext 𝔫
    have h' : (aeval (Pi.single 𝔪 z) (X * p)) 𝔫 =
        aeval ((Pi.single 𝔪 z : ∀ 𝔪, Comp K M A 𝔪) 𝔫) (X * p) :=
      (Polynomial.aeval_algHom_apply (Pi.evalAlgHom M[X] (fun 𝔪 ↦ Comp K M A 𝔪) 𝔫) _ _).symm
    rw [h', Pi.zero_apply]
    by_cases h𝔫 : 𝔫 = 𝔪
    · subst h𝔫
      rw [Pi.single_eq_same, map_mul, aeval_X, aeval_def, hp, mul_zero]
    · rw [Pi.single_eq_of_ne h𝔫, map_mul, aeval_X, zero_mul]
  obtain ⟨b, hb⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := BX K M A) (A := LX K M A)).1
    (hw.tower_top)
  refine ⟨b, ?_⟩
  change Ideal.Quotient.mk 𝔪.asIdeal (algebraMap (BX K M A) (LX K M A) b) = z
  rw [hb, ← equivPi_apply, AlgEquiv.apply_symm_apply, Pi.single_eq_same]

end Normal

end W10Fields

end SemistableReduction
