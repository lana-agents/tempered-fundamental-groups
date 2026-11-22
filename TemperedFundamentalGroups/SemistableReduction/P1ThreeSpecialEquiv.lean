/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeSpecialMk

/-!
# Special data over `V₁` from a finite étale algebra over an isomorphic base (MR13 step 7, D1)

Given a ring isomorphism `e : R ≃+* T/J` and a finite étale `R`-algebra `C` (e.g. the vertex chart
`(B/𝔓)[1/ḡ]` over `R = (T1/P_ℓ)[1/ḡ] ≅ R1/J`), **`P1Three.CuspChart.Special.ofEquiv e C`** is the
`CuspChart.Special θ T 1 1` with `C1 = C`, the `T/J`-algebra structure `algVia e C` through `e⁻¹`
(`Special.ofEtale`). We record:

* **`finrank_ofEquiv`**: `rank_{T/J} C1 = rank_R C`;
* **`autVia`**: an `R`-algebra automorphism of `C` is a `T/J`-algebra automorphism of `C1`
  (`autVia_apply`, `autVia_one`, `autVia_mul`);
* **`isIdempotentElem_ofEquiv`**: `C1` is connected if `C` is a domain.
-/

universe u

namespace SemistableReduction

namespace P1Three

namespace CuspChart

noncomputable section

open AdmissibleLift EtaleTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {T : Type u} [CommRing T] [Algebra O T] {R : Type u} [CommRing R] (e : R ≃+* Ts θ T)
  (C : Type u) [CommRing C] [Algebra R C]

/-- `C` as a `T/J`-algebra through `e⁻¹ : T/J ≃ R`. -/
abbrev algVia : Algebra (Ts θ T) C := ((algebraMap R C).comp e.symm.toRingHom).toAlgebra

lemma finite_via [Module.Finite R C] :
    letI := algVia e C
    Module.Finite (Ts θ T) C := by
  letI := algVia e C
  exact RingHom.finite_algebraMap.mp (RingHom.Finite.comp
    (RingHom.finite_algebraMap.mpr inferInstance)
    (RingHom.Finite.of_surjective _ e.symm.surjective))

lemma etale_via [Algebra.Etale R C] :
    letI := algVia e C
    Algebra.Etale (Ts θ T) C := by
  letI := algVia e C
  exact RingHom.etale_algebraMap.mp (RingHom.Etale.respectsIso.2 _ e.symm
    (RingHom.etale_algebraMap.mpr inferInstance))

lemma finrank_via :
    letI := algVia e C
    Module.finrank (Ts θ T) C = Module.finrank R C := by
  letI := algVia e C
  refine Algebra.finrank_eq_of_equiv_equiv e.symm (RingEquiv.refl C) ?_
  ext x
  simp [RingHom.algebraMap_toAlgebra]

/-- An `R`-algebra automorphism of `C` as a `T/J`-algebra automorphism. -/
def autVia (σ : C ≃ₐ[R] C) :
    letI := algVia e C
    C ≃ₐ[Ts θ T] C :=
  letI := algVia e C
  { σ.toRingEquiv with
    commutes' := fun x ↦ by
      change σ (algebraMap R C (e.symm x)) = algebraMap R C (e.symm x)
      exact σ.commutes _ }

lemma autVia_apply (σ : C ≃ₐ[R] C) (x : C) : autVia e C σ x = σ x := rfl

lemma autVia_one : autVia e C (1 : C ≃ₐ[R] C) = (letI := algVia e C; AlgEquiv.refl) := rfl

lemma autVia_mul (σ τ : C ≃ₐ[R] C) :
    autVia e C (σ * τ) = (letI := algVia e C; (autVia e C τ).trans (autVia e C σ)) := rfl

variable [Fact (Function.Surjective θ)]

/-- **The special datum over `T` given by a finite étale algebra over a ring isomorphic to
`T/J`**: `Special.ofEtale C` for the `T/J`-algebra structure `algVia e C`. -/
def Special.ofEquiv [Module.Finite R C] [Algebra.Etale R C] : Special θ T 1 1 :=
  letI := algVia e C
  haveI := finite_via e C
  haveI := etale_via e C
  Special.ofEtale C

/-- The `T/J`-algebra structure of `Special.ofEquiv e C` is `algVia e C`. -/
lemma Special.algebraMap_ofEquiv [Module.Finite R C] [Algebra.Etale R C] (x : Ts θ T) :
    algebraMap (Ts θ T) (Special.ofEquiv e C).C1 x = algebraMap R C (e.symm x) := rfl

/-- **The degree of `Special.ofEquiv e C` is `rank_R C`.** -/
theorem Special.finrank_ofEquiv [Module.Finite R C] [Algebra.Etale R C] :
    Module.finrank (Ts θ T) (Special.ofEquiv e C).C1 = Module.finrank R C :=
  finrank_via e C

/-- **`Special.ofEquiv e C` is connected if `C` is a domain.** -/
theorem Special.isIdempotentElem_ofEquiv [Module.Finite R C] [Algebra.Etale R C] [IsDomain C]
    (x : (Special.ofEquiv e C).C1) (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 :=
  haveI : IsDomain (Special.ofEquiv e C).C1 := ‹IsDomain C›
  IsIdempotentElem.iff_eq_zero_or_one.mp hx

/-- An `R`-algebra automorphism of `C` as an endomorphism of `Special.ofEquiv e C`. -/
def Special.autOfEquiv [Module.Finite R C] [Algebra.Etale R C] (σ : C ≃ₐ[R] C) :
    (Special.ofEquiv e C).C1 →ₐ[Ts θ T] (Special.ofEquiv e C).C1 :=
  letI := algVia e C
  (autVia e C σ).toAlgHom

lemma Special.autOfEquiv_apply [Module.Finite R C] [Algebra.Etale R C] (σ : C ≃ₐ[R] C)
    (x : C) : Special.autOfEquiv e C σ x = σ x := by
  rfl

end

end CuspChart

end P1Three

end SemistableReduction
