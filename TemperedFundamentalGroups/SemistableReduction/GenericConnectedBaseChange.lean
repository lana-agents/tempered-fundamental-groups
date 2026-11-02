/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.GenericConnected
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Connectedness of the generic fibre after base change (MR13 A1 (c))

Let `B` be a finite flat algebra over a ring `A`, `π ∈ A`, and `A → A'` a map to a Noetherian
domain with a nonzero nonunit `π' ∈ A'` such that `A → A'/π'` is surjective with kernel `(π)`
(the residue rings agree, e.g. `A = O[X]`, `A' = O'[X]` for a totally ramified extension of
discrete valuation rings `O ⊆ O'` with uniformizers `π`, `π'`). Then

* **`GenericConnected.quotEquivBaseChange`**: `(A' ⊗_A B)/π' ≃ B/π`
  (`(A'/π') ⊗_{A'} (A' ⊗_A B) = (A'/π') ⊗_A B = (A/π) ⊗_A B`);
* **`GenericConnected.isIdempotentElem_away_baseChange`**: if `B/π` is reduced and has only the
  trivial idempotents, so has `(A' ⊗_A B)[1/π']` (`isIdempotentElem_away` over `A'`).

For the lift of a tame covering of `ℙ¹_k ∖ {0, 1, ā}` (`P1Three`) this is the geometric
connectedness of the generic fibre at finite level: the base change of the generic fibre to a
totally ramified extension `K'/K` stays connected (item (c) of the A1/A2/B4 list in MR13-plan,
run 11; unramified extensions are trivial when `k` is algebraically closed).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace GenericConnected

noncomputable section

variable {A A' B : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [CommRing B] [Algebra A B]
  {π : A} {π' : A'}
  (hsurj : Function.Surjective (algebraMap A (A' ⧸ Ideal.span {π'})))
  (hker : RingHom.ker (algebraMap A (A' ⧸ Ideal.span {π'})) = Ideal.span {π})

/-- **The special fibre of the base change**: `(A' ⊗_A B)/π' ≃ B/π` if `A → A'/π'` is
surjective with kernel `(π)`. -/
def quotEquivBaseChange :
    (A' ⊗[A] B) ⧸ Ideal.span {algebraMap A' (A' ⊗[A] B) π'} ≃+*
      B ⧸ Ideal.span {algebraMap A B π} :=
  let I' : Ideal A' := Ideal.span {π'}
  let e1 : (A' ⊗[A] B) ⧸ Ideal.span {algebraMap A' (A' ⊗[A] B) π'} ≃+*
      (A' ⧸ I') ⊗[A'] (A' ⊗[A] B) :=
    (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A' ⊗[A] B) I').toRingEquiv
  let e2 : (A' ⧸ I') ⊗[A'] (A' ⊗[A] B) ≃+* (A' ⧸ I') ⊗[A] B :=
    (Algebra.TensorProduct.cancelBaseChange A A' (A' ⧸ I') (A' ⧸ I') B).toRingEquiv
  let q : (A ⧸ Ideal.span {π}) ≃ₐ[A] (A' ⧸ I') :=
    (Ideal.quotientEquivAlgOfEq A hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A (A' ⧸ I')) hsurj)
  let e3 : (A' ⧸ I') ⊗[A] B ≃+* (A ⧸ Ideal.span {π}) ⊗[A] B :=
    (Algebra.TensorProduct.congr q.symm AlgEquiv.refl).toRingEquiv
  let e4 : (A ⧸ Ideal.span {π}) ⊗[A] B ≃+* B ⧸ Ideal.span {algebraMap A B π} :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (Ideal.span {π})).symm.toRingEquiv.trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton]))
  ((e1.trans e2).trans e3).trans e4

variable [IsDomain A'] [IsNoetherianRing A'] [Module.Finite A B] [Module.Flat A B]

include hsurj hker in
/-- **Connected special fibre ⇒ connected generic fibre after base change**: if `B/π` is
reduced and has only the trivial idempotents, so has `(A' ⊗_A B)[1/π']`. -/
theorem isIdempotentElem_away_baseChange (hπ' : π' ≠ 0) (hπu : ¬IsUnit π')
    (hred : IsReduced (B ⧸ Ideal.span {algebraMap A B π}))
    (hconn : ∀ e : B ⧸ Ideal.span {algebraMap A B π}, IsIdempotentElem e → e = 0 ∨ e = 1)
    (S : Type*) [CommRing S] [Algebra (A' ⊗[A] B) S]
    [IsLocalization.Away (algebraMap A' (A' ⊗[A] B) π') S]
    {e : S} (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  obtain ⟨E⟩ : Nonempty ((A' ⊗[A] B) ⧸ Ideal.span {algebraMap A' (A' ⊗[A] B) π'} ≃+*
      B ⧸ Ideal.span {algebraMap A B π}) := ⟨quotEquivBaseChange hsurj hker⟩
  refine isIdempotentElem_away hπ' hπu S (isReduced_of_injective E.toRingHom E.injective)
    (fun x hx ↦ ?_) he
  rcases hconn (E x) (hx.map E) with h | h
  · left
    have h' := congrArg E.symm h
    rwa [RingEquiv.symm_apply_apply, map_zero] at h'
  · right
    have h' := congrArg E.symm h
    rwa [RingEquiv.symm_apply_apply, map_one] at h'


section Polynomial

open Polynomial

variable {R R' : Type*} [CommRing R] [CommRing R'] [Algebra R R'] {π : R} {π' : R'}
  (hs : Function.Surjective (algebraMap R (R' ⧸ Ideal.span {π'})))
  (hk : RingHom.ker (algebraMap R (R' ⧸ Ideal.span {π'})) = Ideal.span {π})

/-- `R[X]` over `R'[X]` (coefficientwise). -/
@[reducible] def algPoly : Algebra R[X] R'[X] := (mapRingHom (algebraMap R R')).toAlgebra

omit [Algebra R R'] in
lemma map_C_span (x : R') : Ideal.map (C : R' →+* R'[X]) (Ideal.span {x}) = Ideal.span {C x} := by
  rw [Ideal.map_span, Set.image_singleton]

lemma algebraMap_polyQuot_eq : letI := algPoly (R := R) (R' := R')
    algebraMap R[X] (R'[X] ⧸ Ideal.span {C π'}) =
      ((Ideal.quotEquivOfEq (map_C_span π')).toRingHom.comp
        (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {π'})).toRingHom).comp
        (mapRingHom (algebraMap R (R' ⧸ Ideal.span {π'}))) := by
  letI := algPoly (R := R) (R' := R')
  refine RingHom.ext fun p ↦ ?_
  have h1 : p.map (algebraMap R (R' ⧸ Ideal.span {π'})) =
      (p.map (algebraMap R R')).map (Ideal.Quotient.mk _) := by
    rw [Polynomial.map_map]
    rfl
  change Ideal.Quotient.mk _ (mapRingHom (algebraMap R R') p) =
    Ideal.quotEquivOfEq (map_C_span π') (Ideal.polynomialQuotientEquivQuotientPolynomial _
      (p.map (algebraMap R (R' ⧸ Ideal.span {π'}))))
  rw [h1, Ideal.polynomialQuotientEquivQuotientPolynomial_map_mk, Ideal.quotEquivOfEq_mk]
  rfl

include hs in
/-- **Residue condition for polynomial rings**, surjectivity. -/
theorem surjective_polyQuot : letI := algPoly (R := R) (R' := R')
    Function.Surjective (algebraMap R[X] (R'[X] ⧸ Ideal.span {C π'})) := by
  letI := algPoly (R := R) (R' := R')
  rw [algebraMap_polyQuot_eq]
  exact ((Ideal.quotEquivOfEq (map_C_span π')).surjective.comp
    (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {π'})).surjective).comp
    (Polynomial.map_surjective (algebraMap R (R' ⧸ Ideal.span {π'})) hs)

include hk in
/-- **Residue condition for polynomial rings**, kernel. -/
theorem ker_polyQuot : letI := algPoly (R := R) (R' := R')
    RingHom.ker (algebraMap R[X] (R'[X] ⧸ Ideal.span {C π'})) = Ideal.span {C π} := by
  letI := algPoly (R := R) (R' := R')
  rw [algebraMap_polyQuot_eq, RingHom.ker_comp_of_injective _
    ((Ideal.quotEquivOfEq (map_C_span π')).injective.comp
      (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {π'})).injective),
    Polynomial.ker_mapRingHom, hk, map_C_span]

end Polynomial

end

end GenericConnected

end SemistableReduction
