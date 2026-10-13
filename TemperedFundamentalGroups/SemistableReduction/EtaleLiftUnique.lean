/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleLiftMonogenic
import TemperedFundamentalGroups.SemistableReduction.CompleteFree
import Mathlib.RingTheory.Henselian

/-!
# Uniqueness of the lifts of monogenic étale algebras (Blueprint §12.8, M2.2, monogenic case)

Let `A` be `I`-adically complete and `f, f'` monic polynomials over `A` with the same reduction
modulo `I`, both étale (`f'(x)` a unit in `A[X]/(f)`, and likewise for `f'`). Then
**`A[X]/(f) ≅ A[X]/(f')`** as `A`-algebras (`equivOfLift`): the lift of `exists_lift` is unique
up to isomorphism.

Proof: `B' = A[X]/(f')` is finite free, hence `IB'`-adically complete (`CompleteFree`), hence a
Henselian pair; the root of `f'` is a root of `f` modulo `IB'` with unit derivative, so Hensel's
lemma gives a root of `f` in `B'`, i.e. a map `A[X]/(f) → B'`, and symmetrically a map back.
The composites send the root to a root of the same polynomial congruent to it modulo the
Jacobson radical, which is the root itself (`eq_of_isRoot_of_sub_mem`, from the Taylor expansion
`f(r + y) = f(r) + f'(r) y + k y²`).

* `isUnit_add_of_mem_jacobson`, `eq_of_isRoot_of_sub_mem`;
* `aeval_sub_mem_of_map_eq`: polynomials with the same reduction take values congruent mod `IB`;
* **`equivOfLift`**, and `hom_eq`: the isomorphism is unique among maps lifting the identity
  on the roots modulo `IB`.
-/

open Polynomial

namespace SemistableReduction

namespace EtaleLift

/-- `u + j` is a unit for a unit `u` and `j` in the Jacobson radical. -/
theorem isUnit_add_of_mem_jacobson {B : Type*} [CommRing B] {u j : B} (hu : IsUnit u)
    (hj : j ∈ (⊥ : Ideal B).jacobson) : IsUnit (u + j) := by
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h := Ideal.mem_jacobson_bot.1 hj v
  have he : u + j = u * (j * v + 1) := by linear_combination (-j) * hv
  rw [he]
  exact hu.mul h

/-- **Roots congruent modulo the Jacobson radical, with a unit derivative, are equal.** -/
theorem eq_of_isRoot_of_sub_mem {B : Type*} [CommRing B] (f : B[X]) {r r' : B}
    (hr : f.IsRoot r) (hr' : f.IsRoot r') (hd : IsUnit (f.derivative.eval r))
    (hrr : r' - r ∈ (⊥ : Ideal B).jacobson) : r' = r := by
  obtain ⟨k, hk⟩ := Polynomial.binomExpansion f r (r' - r)
  rw [add_sub_cancel, hr'.eq_zero, hr.eq_zero, zero_add] at hk
  have hu : IsUnit (f.derivative.eval r + k * (r' - r)) :=
    isUnit_add_of_mem_jacobson hd (Ideal.mul_mem_left _ k hrr)
  have h0 : (r' - r) * (f.derivative.eval r + k * (r' - r)) = 0 := by linear_combination -hk
  have := (hu.mul_left_eq_zero).1 h0
  exact sub_eq_zero.1 this

variable {A : Type*} [CommRing A] {I : Ideal A}

/-- Polynomials with the same reduction modulo `I` take values congruent modulo `IB`. -/
theorem aeval_sub_mem_of_map_eq {B : Type*} [CommRing B] [Algebra A B] {f g : A[X]}
    (h : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I)) (x : B) :
    aeval x f - aeval x g ∈ I.map (algebraMap A B) := by
  rw [← map_sub, aeval_eq_sum_range]
  refine Ideal.sum_mem _ fun i _ => ?_
  rw [Algebra.smul_def]
  refine Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ?_)
  have := congrArg (fun p => p.coeff i) h
  simp only [coeff_map] at this
  rw [coeff_sub]
  exact Ideal.Quotient.eq.1 this

variable (I) [IsAdicComplete I A]

/-- `A[X]/(g)` is `IB`-adically complete for `g` monic (`CompleteFree`). -/
theorem isAdicComplete_adjoinRoot {g : A[X]} (hg : g.Monic) :
    IsAdicComplete (I.map (algebraMap A (AdjoinRoot g))) (AdjoinRoot g) :=
  CompleteFree.isAdicComplete_map I (AdjoinRoot.powerBasis' hg).basis

theorem map_le_jacobson_adjoinRoot {g : A[X]} (hg : g.Monic) :
    I.map (algebraMap A (AdjoinRoot g)) ≤ (⊥ : Ideal (AdjoinRoot g)).jacobson :=
  haveI := isAdicComplete_adjoinRoot I hg
  IsAdicComplete.le_jacobson_bot _

/-- **Hensel**: for `f, g` monic with the same reduction and `g` étale, there is an `A`-algebra
map `A[X]/(f) → A[X]/(g)` sending the root of `f` to a lift of the root of `g` modulo `IB`. -/
theorem exists_hom {f g : A[X]} (hf : f.Monic) (hg : g.Monic)
    (h : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I))
    (hdg : IsUnit (aeval (AdjoinRoot.root g) (derivative g))) :
    ∃ φ : AdjoinRoot f →ₐ[A] AdjoinRoot g,
      φ (AdjoinRoot.root f) - AdjoinRoot.root g ∈ I.map (algebraMap A (AdjoinRoot g)) := by
  haveI := isAdicComplete_adjoinRoot I hg
  set J := I.map (algebraMap A (AdjoinRoot g))
  have hJ : J ≤ (⊥ : Ideal (AdjoinRoot g)).jacobson := IsAdicComplete.le_jacobson_bot J
  have hg0 : aeval (AdjoinRoot.root g) g = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have h0 : (f.map (algebraMap A (AdjoinRoot g))).eval (AdjoinRoot.root g) ∈ J := by
    have := aeval_sub_mem_of_map_eq h (AdjoinRoot.root g)
    rwa [hg0, sub_zero, aeval_def, ← eval_map] at this
  have hd : IsUnit ((f.map (algebraMap A (AdjoinRoot g))).derivative.eval
      (AdjoinRoot.root g)) := by
    have hD : (derivative f).map (Ideal.Quotient.mk I) =
        (derivative g).map (Ideal.Quotient.mk I) := by
      rw [← derivative_map, h, derivative_map]
    have hu := isUnit_add_of_mem_jacobson hdg 
      (hJ (aeval_sub_mem_of_map_eq hD (AdjoinRoot.root g)))
    rw [add_sub_cancel] at hu
    rwa [derivative_map, eval_map, ← aeval_def]
  obtain ⟨a, ha, haJ⟩ := HenselianRing.is_henselian (I := J) _ (hf.map _) _ h0
    (hd.map (Ideal.Quotient.mk J))
  have ha' : f.eval₂ (Algebra.ofId A (AdjoinRoot g) : A →+* AdjoinRoot g) a = 0 := by
    rw [← ha.eq_zero, eval_map]
    rfl
  exact ⟨AdjoinRoot.liftAlgHom f (Algebra.ofId A _) a ha', by simpa using haJ⟩

/-- The composite of two Hensel maps is the identity. -/
theorem comp_eq_id {f g : A[X]} (hf : f.Monic)
    (hdf : IsUnit (aeval (AdjoinRoot.root f) (derivative f)))
    (φ : AdjoinRoot f →ₐ[A] AdjoinRoot g) (ψ : AdjoinRoot g →ₐ[A] AdjoinRoot f)
    (hφ : φ (AdjoinRoot.root f) - AdjoinRoot.root g ∈ I.map (algebraMap A (AdjoinRoot g)))
    (hψ : ψ (AdjoinRoot.root g) - AdjoinRoot.root f ∈ I.map (algebraMap A (AdjoinRoot f))) :
    ψ.comp φ = AlgHom.id A (AdjoinRoot f) := by
  apply AdjoinRoot.algHom_ext
  have hmem : ψ (φ (AdjoinRoot.root f)) - AdjoinRoot.root f ∈
      I.map (algebraMap A (AdjoinRoot f)) := by
    have h1 : ψ (φ (AdjoinRoot.root f) - AdjoinRoot.root g) ∈
        I.map (algebraMap A (AdjoinRoot f)) := by
      have := Ideal.mem_map_of_mem (ψ : AdjoinRoot g →+* AdjoinRoot f) hφ
      rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this
    have := Ideal.add_mem _ h1 hψ
    rwa [map_sub, sub_add_sub_cancel] at this
  have hroot : (f.map (algebraMap A (AdjoinRoot f))).IsRoot (ψ (φ (AdjoinRoot.root f))) := by
    rw [IsRoot.def, eval_map, ← aeval_def, aeval_algHom_apply, aeval_algHom_apply,
      AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, map_zero, map_zero]
  have hroot' : (f.map (algebraMap A (AdjoinRoot f))).IsRoot (AdjoinRoot.root f) := by
    rw [IsRoot.def, eval_map, ← aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hd : IsUnit ((f.map (algebraMap A (AdjoinRoot f))).derivative.eval
      (AdjoinRoot.root f)) := by
    rwa [derivative_map, eval_map, ← aeval_def]
  exact eq_of_isRoot_of_sub_mem _ hroot' hroot hd (map_le_jacobson_adjoinRoot I hf hmem)

/-- **Uniqueness of the isomorphism**: two `A`-algebra maps `A[X]/(f) → A[X]/(g)` sending the root
of `f` to lifts of the root of `g` modulo `IB` are equal. -/
theorem hom_eq {f g : A[X]} (hg : g.Monic)
    (h : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I))
    (hdg : IsUnit (aeval (AdjoinRoot.root g) (derivative g)))
    (φ₁ φ₂ : AdjoinRoot f →ₐ[A] AdjoinRoot g)
    (h₁ : φ₁ (AdjoinRoot.root f) - AdjoinRoot.root g ∈ I.map (algebraMap A (AdjoinRoot g)))
    (h₂ : φ₂ (AdjoinRoot.root f) - AdjoinRoot.root g ∈ I.map (algebraMap A (AdjoinRoot g))) :
    φ₁ = φ₂ := by
  apply AdjoinRoot.algHom_ext
  set J := I.map (algebraMap A (AdjoinRoot g))
  have hJ := map_le_jacobson_adjoinRoot I hg
  have hroot : ∀ φ : AdjoinRoot f →ₐ[A] AdjoinRoot g,
      (f.map (algebraMap A (AdjoinRoot g))).IsRoot (φ (AdjoinRoot.root f)) := fun φ => by
    rw [IsRoot.def, eval_map, ← aeval_def, aeval_algHom_apply, AdjoinRoot.aeval_eq,
      AdjoinRoot.mk_self, map_zero]
  have hD : (derivative f).map (Ideal.Quotient.mk I) =
      (derivative g).map (Ideal.Quotient.mk I) := by
    rw [← derivative_map, h, derivative_map]
  -- `f'(φ₁ x) ≡ f'(x_g) ≡ g'(x_g)` modulo `IB`, so it is a unit
  have hd : IsUnit ((f.map (algebraMap A (AdjoinRoot g))).derivative.eval
      (φ₁ (AdjoinRoot.root f))) := by
    have hu := isUnit_add_of_mem_jacobson hdg
      (hJ (aeval_sub_mem_of_map_eq hD (AdjoinRoot.root g)))
    rw [add_sub_cancel, aeval_def, ← eval_map, ← derivative_map] at hu
    set p := (f.map (algebraMap A (AdjoinRoot g))).derivative
    obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub (φ₁ (AdjoinRoot.root f)) (AdjoinRoot.root g) p
    have hm : p.eval (φ₁ (AdjoinRoot.root f)) - p.eval (AdjoinRoot.root g) ∈
        (⊥ : Ideal (AdjoinRoot g)).jacobson := by
      rw [hc]
      exact hJ (J.mul_mem_right c h₁)
    have := isUnit_add_of_mem_jacobson hu hm
    rwa [add_sub_cancel] at this
  have h₁₂ : φ₂ (AdjoinRoot.root f) - φ₁ (AdjoinRoot.root f) ∈ (⊥ : Ideal _).jacobson := by
    have := J.sub_mem h₂ h₁
    rw [sub_sub_sub_cancel_right] at this
    exact hJ this
  exact (eq_of_isRoot_of_sub_mem _ (hroot φ₁) (hroot φ₂) hd h₁₂).symm

/-- **Uniqueness of monogenic étale lifts**: two monic étale lifts of the same polynomial over
`A/I` give isomorphic `A`-algebras. -/
noncomputable def equivOfLift {f g : A[X]} (hf : f.Monic) (hg : g.Monic)
    (h : f.map (Ideal.Quotient.mk I) = g.map (Ideal.Quotient.mk I))
    (hdf : IsUnit (aeval (AdjoinRoot.root f) (derivative f)))
    (hdg : IsUnit (aeval (AdjoinRoot.root g) (derivative g))) :
    AdjoinRoot f ≃ₐ[A] AdjoinRoot g :=
  let φ := (exists_hom I hf hg h hdg).choose
  let ψ := (exists_hom I hg hf h.symm hdf).choose
  have hφ := (exists_hom I hf hg h hdg).choose_spec
  have hψ := (exists_hom I hg hf h.symm hdf).choose_spec
  AlgEquiv.ofAlgHom φ ψ (comp_eq_id I hg hdg ψ φ hψ hφ) (comp_eq_id I hf hdf φ ψ hφ hψ)

end EtaleLift

end SemistableReduction
