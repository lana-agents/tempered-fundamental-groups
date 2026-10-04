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

noncomputable instance : Algebra M (LX K M A) :=
  inferInstanceAs (Algebra M (RatFunc M ⊗[M[X]] BX K M A))

instance : IsScalarTower M (RatFunc M) (LX K M A) :=
  inferInstanceAs (IsScalarTower M (RatFunc M) (RatFunc M ⊗[M[X]] BX K M A))

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

/-! ### Change of constants -/

section BaseChange

variable {M} {M' : Type u} [Field M'] [Algebra K M'] [Algebra M M'] [IsScalarTower K M M']

/-- `M[X] → M'[X]` as a `K[X]`-algebra map. -/
noncomputable def polyMap : M[X] →ₐ[K[X]] M'[X] :=
  { Polynomial.mapRingHom (algebraMap M M') with
    commutes' := fun q ↦ by
      change (q.map (algebraMap K M)).map (algebraMap M M') = q.map (algebraMap K M')
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] }

lemma polyMap_apply (q : M[X]) : polyMap K (M := M) (M' := M') q = q.map (algebraMap M M') := rfl

variable (M M')

/-- `M ⊗_K A → M' ⊗_K A`. -/
noncomputable def bxMap : BX K M A →+* BX K M' A :=
  (Algebra.TensorProduct.map (polyMap K (M := M) (M' := M')) (AlgHom.id K[X] A)).toRingHom

variable {M M'}

lemma bxMap_algebraMap (q : M[X]) :
    bxMap K M A M' (algebraMap M[X] (BX K M A) q) =
      algebraMap M'[X] (BX K M' A) (q.map (algebraMap M M')) := by
  change bxMap K M A M' (q ⊗ₜ 1 : M[X] ⊗[K[X]] A) = (q.map (algebraMap M M') ⊗ₜ 1 : M'[X] ⊗[K[X]] A)
  rfl

lemma bxMap_ofA (a : A) : bxMap K M A M' (BX.ofA K M A a) = BX.ofA K M' A a := by
  change bxMap K M A M' (1 ⊗ₜ a : M[X] ⊗[K[X]] A) = (1 ⊗ₜ a : M'[X] ⊗[K[X]] A)
  change (polyMap K (M := M) (M' := M') 1 ⊗ₜ a : M'[X] ⊗[K[X]] A) = _
  rw [map_one]

lemma map_algebraMapSubmonoid_le :
    Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X]) ≤
      (Algebra.algebraMapSubmonoid (BX K M' A) (nonZeroDivisors M'[X])).comap
        (bxMap K M A M') := by
  rintro _ ⟨q, hq, rfl⟩
  refine ⟨q.map (algebraMap M M'), mem_nonZeroDivisors_of_ne_zero ?_, (bxMap_algebraMap K A q).symm⟩
  exact (Polynomial.map_ne_zero_iff (algebraMap M M').injective).2 (nonZeroDivisors.ne_zero hq)

variable (M M')

/-- `LX K M A → LX K M' A`. -/
noncomputable def lxMap : LX K M A →+* LX K M' A :=
  IsLocalization.map (LX K M' A) (bxMap K M A M') (map_algebraMapSubmonoid_le K A)

variable {M M'}

lemma lxMap_algebraMap (b : BX K M A) :
    lxMap K M A M' (algebraMap (BX K M A) (LX K M A) b) =
      algebraMap (BX K M' A) (LX K M' A) (bxMap K M A M' b) :=
  IsLocalization.map_eq _ _

variable (M M')

/-- The contraction of a maximal ideal of `LX K M' A` (a maximal ideal: `LX K M A` is artinian). -/
noncomputable def contrMax [Module.Finite K[X] A] (𝔪 : MaximalSpectrum (LX K M' A)) :
    MaximalSpectrum (LX K M A) :=
  ⟨𝔪.asIdeal.comap (lxMap K M A M'), IsArtinianRing.isMaximal_of_isPrime _⟩

/-- The map of components `LX K M A ⧸ (𝔪 ∩ LX K M A) → LX K M' A ⧸ 𝔪`. -/
noncomputable def compMap [Module.Finite K[X] A] (𝔪 : MaximalSpectrum (LX K M' A)) :
    Comp K M A (contrMax K M A M' 𝔪) →+* Comp K M' A 𝔪 :=
  Ideal.quotientMap 𝔪.asIdeal (lxMap K M A M') le_rfl

variable {M M'}

lemma compMap_mk [Module.Finite K[X] A] (𝔪 : MaximalSpectrum (LX K M' A)) (y : LX K M A) :
    compMap K M A M' 𝔪 (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk 𝔪.asIdeal (lxMap K M A M' y) :=
  rfl

end BaseChange

/-! ### The cover over `K` itself -/

section OverK

/-- The localization `K(X) ⊗_{K[X]} A` of `A` at the nonzero polynomials. -/
def LB : Type u := RatFunc K ⊗[K[X]] A

namespace LB

noncomputable instance : CommRing (LB K A) := inferInstanceAs (CommRing (RatFunc K ⊗[K[X]] A))

noncomputable instance : Algebra (RatFunc K) (LB K A) :=
  inferInstanceAs (Algebra (RatFunc K) (RatFunc K ⊗[K[X]] A))

noncomputable instance : Algebra K (LB K A) :=
  inferInstanceAs (Algebra K (RatFunc K ⊗[K[X]] A))

instance : IsScalarTower K (RatFunc K) (LB K A) :=
  inferInstanceAs (IsScalarTower K (RatFunc K) (RatFunc K ⊗[K[X]] A))

noncomputable instance : Algebra K[X] (LB K A) :=
  inferInstanceAs (Algebra K[X] (RatFunc K ⊗[K[X]] A))

instance : IsScalarTower K[X] (RatFunc K) (LB K A) :=
  inferInstanceAs (IsScalarTower K[X] (RatFunc K) (RatFunc K ⊗[K[X]] A))

noncomputable instance : Algebra A (LB K A) := Algebra.TensorProduct.rightAlgebra

instance : IsScalarTower K[X] A (LB K A) := Algebra.TensorProduct.right_isScalarTower

instance [Module.Finite K[X] A] : Module.Finite (RatFunc K) (LB K A) :=
  inferInstanceAs (Module.Finite (RatFunc K) (RatFunc K ⊗[K[X]] A))

instance isLocalization :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors K[X])) (LB K A) :=
  IsLocalization.tensorRight (RatFunc K) (nonZeroDivisors K[X])

instance [Module.Finite K[X] A] : IsArtinianRing (LB K A) :=
  IsArtinianRing.of_finite (RatFunc K) (LB K A)

end LB

instance (𝔪 : MaximalSpectrum (LB K A)) : 𝔪.asIdeal.IsMaximal := 𝔪.isMaximal

/-- A component of `A` over `K`. -/
abbrev CompB (𝔪 : MaximalSpectrum (LB K A)) : Type u := LB K A ⧸ 𝔪.asIdeal

noncomputable instance (𝔪 : MaximalSpectrum (LB K A)) : Field (CompB K A 𝔪) :=
  Ideal.Quotient.field _

lemma ofA_algebraMap (p : K[X]) :
    BX.ofA K M A (algebraMap K[X] A p) =
      algebraMap M[X] (BX K M A) (p.map (algebraMap K M)) := by
  change ((1 : M[X]) ⊗ₜ (algebraMap K[X] A p) : M[X] ⊗[K[X]] A) =
    (p.map (algebraMap K M) ⊗ₜ 1 : M[X] ⊗[K[X]] A)
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Algebra.smul_def, mul_one]
  rfl

lemma ofA_mem_algebraMapSubmonoid :
    Algebra.algebraMapSubmonoid A (nonZeroDivisors K[X]) ≤
      (Algebra.algebraMapSubmonoid (BX K M A) (nonZeroDivisors M[X])).comap (BX.ofA K M A) := by
  rintro _ ⟨p, hp, rfl⟩
  refine ⟨p.map (algebraMap K M), mem_nonZeroDivisors_of_ne_zero ?_, (ofA_algebraMap K M A p).symm⟩
  exact (Polynomial.map_ne_zero_iff (algebraMap K M).injective).2 (nonZeroDivisors.ne_zero hp)

/-- `K(X) ⊗_{K[X]} A → M(X) ⊗_{M[X]} (M ⊗_K A)`. -/
noncomputable def lbMap : LB K A →+* LX K M A :=
  IsLocalization.map (LX K M A) (BX.ofA K M A) (ofA_mem_algebraMapSubmonoid K M A)

lemma lbMap_algebraMap (a : A) :
    lbMap K M A (algebraMap A (LB K A) a) = algebraMap (BX K M A) (LX K M A) (BX.ofA K M A a) :=
  IsLocalization.map_eq _ _

/-- The contraction of a maximal ideal of `LX K M A` to `LB K A`. -/
noncomputable def contrB [Module.Finite K[X] A] (𝔪 : MaximalSpectrum (LX K M A)) :
    MaximalSpectrum (LB K A) :=
  ⟨𝔪.asIdeal.comap (lbMap K M A), IsArtinianRing.isMaximal_of_isPrime _⟩

/-- The map of components `CompB (𝔪 ∩ LB) → Comp 𝔪`. -/
noncomputable def compBMap [Module.Finite K[X] A] (𝔪 : MaximalSpectrum (LX K M A)) :
    CompB K A (contrB K M A 𝔪) →+* Comp K M A 𝔪 :=
  Ideal.quotientMap 𝔪.asIdeal (lbMap K M A) le_rfl

lemma compBMap_mk [Module.Finite K[X] A] (𝔪 : MaximalSpectrum (LX K M A)) (y : LB K A) :
    compBMap K M A 𝔪 (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk 𝔪.asIdeal (lbMap K M A y) :=
  rfl

end OverK

end W10Fields

end SemistableReduction
