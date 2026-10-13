/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Lifting monogenic étale algebras along a complete ideal (Blueprint §12.8, M2.2, monogenic case)

Let `A` be a ring, complete for the `I`-adic topology (`IsAdicComplete I A`), and
`B₀ = (A/I)[X]/(f₀)` a monogenic étale `A/I`-algebra: `f₀` monic with `f₀'` a unit in `B₀`.
Then `B₀` lifts to a finite free étale `A`-algebra (`exists_lift`): for any monic lift `f` of
`f₀`, `B = A[X]/(f)` is finite free over `A` (monic), `B/IB ≅ B₀`
(`AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot`), and `B` is étale over `A`: `f'(x)` is a
unit of `B` because it is a unit modulo `IB` and `IB` lies in the Jacobson radical of `B`
(`map_le_jacobson`: `B` is integral over `A`, so maximal ideals of `B` contract to maximal ideals
of `A`, which contain `I ⊆ J(A)` by completeness).

This is the monogenic case of the topological invariance of the étale site along a complete
ideal (every finite étale algebra over a local ring is a product of monogenic ones only after
étale localisation, so the general case M2.2 needs more).

* `map_le_jacobson`: `IB ⊆ J(B)` for `B` integral over `A` and `I ⊆ J(A)`;
* `isUnit_of_isUnit_mk`: units modulo an ideal inside the Jacobson radical are units;
* `etale_of_isUnit`: `A[X]/(f)` is étale over `A` when `f` is monic and `f'(x)` is a unit;
* **`exists_lift`**.
-/

open Polynomial

namespace SemistableReduction

namespace EtaleLift

variable {A : Type*} [CommRing A]

/-- **`IB ⊆ J(B)`** for an integral extension `A → B` and `I ⊆ J(A)`. -/
theorem map_le_jacobson {B : Type*} [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    {I : Ideal A} (hI : I ≤ (⊥ : Ideal A).jacobson) :
    I.map (algebraMap A B) ≤ (⊥ : Ideal B).jacobson := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have hc : (M.comap (algebraMap A B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
  have := hI ha
  rw [Ideal.jacobson, Ideal.mem_sInf] at this
  exact this ⟨bot_le, hc⟩

/-- **Units modulo an ideal inside the Jacobson radical are units.** -/
theorem isUnit_of_isUnit_mk {B : Type*} [CommRing B] {J : Ideal B}
    (hJ : J ≤ (⊥ : Ideal B).jacobson) {x : B} (hx : IsUnit (Ideal.Quotient.mk J x)) : IsUnit x := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk J), Ideal.Quotient.eq] at hy
  have h := Ideal.isUnit_of_sub_one_mem_jacobson_bot (x * y) (hJ hy)
  exact isUnit_of_mul_isUnit_left h

/-- The standard étale pair `(f, 1)` for a monic `f` whose derivative is a unit at the root. -/
noncomputable def pairOf {f : A[X]} (hf : f.Monic)
    (hd : IsUnit (aeval (AdjoinRoot.root f) (derivative f))) : StandardEtalePair A where
  f := f
  monic_f := hf
  g := 1
  cond := by
    obtain ⟨u, hu⟩ := hd.exists_right_inv
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective u
    rw [AdjoinRoot.aeval_eq, ← map_mul, ← map_one (AdjoinRoot.mk f), AdjoinRoot.mk_eq_mk] at hu
    obtain ⟨q, hq⟩ := hu
    exact ⟨p, -q, 0, by rw [pow_zero]; linear_combination hq⟩

/-- **`A[X]/(f)` is étale over `A`** for `f` monic with `f'(x)` a unit. -/
theorem etale_of_isUnit {f : A[X]} (hf : f.Monic)
    (hd : IsUnit (aeval (AdjoinRoot.root f) (derivative f))) : Algebra.Etale A (AdjoinRoot f) := by
  let P := pairOf hf hd
  have hmap : P.HasMap (AdjoinRoot.root f) :=
    ⟨by simp [P, pairOf], by simp [P, pairOf]⟩
  let ψ : AdjoinRoot f →ₐ[A] P.Ring := AdjoinRoot.liftAlgHom f (Algebra.ofId A P.Ring) P.X
    P.hasMap_X.1
  have h1 : (P.lift _ hmap).comp ψ = AlgHom.id A (AdjoinRoot f) :=
    AdjoinRoot.algHom_ext (by simp [ψ])
  have h2 : ψ.comp (P.lift _ hmap) = AlgHom.id A P.Ring :=
    P.hom_ext (by simp [ψ])
  haveI : Algebra.IsStandardEtale A (AdjoinRoot f) :=
    ⟨⟨⟨P, AdjoinRoot.root f, hmap, Function.bijective_iff_has_inverse.2
      ⟨ψ, fun z => AlgHom.congr_fun h2 z, fun z => AlgHom.congr_fun h1 z⟩⟩⟩⟩
  infer_instance

variable (I : Ideal A) [IsAdicComplete I A] [Nontrivial (A ⧸ I)]

/-- **Lifting monogenic étale algebras along a complete ideal.** -/
theorem exists_lift (f₀ : (A ⧸ I)[X]) (hm : f₀.Monic)
    (hd : IsUnit (aeval (AdjoinRoot.root f₀) (derivative f₀))) :
    ∃ f : A[X], f.Monic ∧ f.map (Ideal.Quotient.mk I) = f₀ ∧ Algebra.Etale A (AdjoinRoot f) ∧
      Module.Finite A (AdjoinRoot f) ∧ Module.Free A (AdjoinRoot f) ∧
      Nonempty ((AdjoinRoot f ⧸ I.map (AdjoinRoot.of f)) ≃+*
        (A ⧸ I)[X] ⧸ Ideal.span {f₀}) := by
  obtain ⟨f, hmap, -, hfm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.lifts_iff_coeff_lifts _ |>.2 fun n => Ideal.Quotient.mk_surjective _) hm
  subst hmap
  have hfin : Module.Finite A (AdjoinRoot f) := (AdjoinRoot.powerBasis' hfm).finite
  have hfree : Module.Free A (AdjoinRoot f) :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' hfm).basis
  refine ⟨f, hfm, rfl, ?_, hfin, hfree, ⟨AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I f⟩⟩
  apply etale_of_isUnit hfm
  have hJ : I.map (AdjoinRoot.of f) ≤ (⊥ : Ideal (AdjoinRoot f)).jacobson := by
    rw [← AdjoinRoot.algebraMap_eq]
    exact map_le_jacobson (IsAdicComplete.le_jacobson_bot I)
  refine isUnit_of_isUnit_mk hJ ?_
  let e := AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I f
  have he : e (Ideal.Quotient.mk _ (aeval (AdjoinRoot.root f) (derivative f))) =
      aeval (AdjoinRoot.root (f.map (Ideal.Quotient.mk I)))
        (derivative (f.map (Ideal.Quotient.mk I))) := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot_mk_of,
      AdjoinRoot.aeval_eq, Polynomial.derivative_map]
    rfl
  have : IsUnit (e (Ideal.Quotient.mk _ (aeval (AdjoinRoot.root f) (derivative f)))) := by
    rw [he]
    exact hd
  exact (MulEquiv.isUnit_map e.toMulEquiv).1 this

end EtaleLift

end SemistableReduction
