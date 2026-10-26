/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Finiteness.Basic

/-!
# The finite zero set of a function on a special fibre (MR12 T2 S5.5)

Let `R` be a Jacobson ring and `f ∈ R` with `R/(f)` Artinian (e.g. finite-dimensional over a
field). Then the maximal ideals containing `f` (`FormalPoints.Pts f`) form a finite set, and their
intersection lies in the radical of `(f)` (**`FormalPoints.iInf_le_radical`**): exactly the data
`hinj`, `hf`, `hrad` of `CompletionProd` / `FormalKummer.exists_cusp` for the index type
`Pts f`, without enumerating the points; over an algebraically closed field the points are
rational (`FormalPoints.algebraMap_surjective_quot`).
-/

namespace SemistableReduction

namespace FormalPoints

variable {R : Type*} [CommRing R] (f : R)

/-- The maximal ideals containing `f`. -/
def Pts : Type _ := {P : Ideal R // P.IsMaximal ∧ f ∈ P}

/-- The ideal of a point. -/
def Pts.ideal {f : R} (P : Pts f) : Ideal R := P.1

instance (P : Pts f) : P.ideal.IsMaximal := P.2.1

lemma Pts.mem {f : R} (P : Pts f) : f ∈ P.ideal := P.2.2

lemma ideal_injective : Function.Injective (Pts.ideal (f := f)) := fun _ _ h ↦ Subtype.ext h

/-- **Finitely many points** if `R/(f)` is Artinian. -/
instance [IsArtinianRing (R ⧸ Ideal.span {f})] : Finite (Pts f) := by
  have hfin := IsArtinianRing.setOf_isMaximal_finite (R ⧸ Ideal.span {f})
  haveI := hfin.to_subtype
  refine Finite.of_injective (β := {I : Ideal (R ⧸ Ideal.span {f}) | I.IsMaximal})
    (fun P ↦ ⟨P.1.map (Ideal.Quotient.mk _), ?_⟩) ?_
  · have hle : Ideal.span {f} ≤ P.1 := (Ideal.span_singleton_le_iff_mem _).2 P.2.2
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      P.2.1).resolve_left fun htop ↦ P.2.1.ne_top ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {f}))) htop
    rwa [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.2 hle, Ideal.comap_top] at this
  · intro P Q h
    have h' := congrArg (fun I : {I : Ideal (R ⧸ Ideal.span {f}) | I.IsMaximal} ↦
      I.1.comap (Ideal.Quotient.mk (Ideal.span {f}))) h
    simp only at h'
    have hP : Ideal.span {f} ≤ P.1 := (Ideal.span_singleton_le_iff_mem _).2 P.2.2
    have hQ : Ideal.span {f} ≤ Q.1 := (Ideal.span_singleton_le_iff_mem _).2 Q.2.2
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.2 hP, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, sup_eq_left.2 hQ] at h'
    exact Subtype.ext h'

/-- **The points cut out `f` up to radical** (`R` Jacobson). -/
theorem iInf_le_radical [IsJacobsonRing R] :
    ⨅ P : Pts f, P.ideal ≤ (Ideal.span {f}).radical := by
  rw [Ideal.radical_eq_jacobson]
  refine le_sInf fun J ⟨hJ, hJm⟩ ↦ iInf_le_of_le ⟨J, hJm, ?_⟩ le_rfl
  exact (Ideal.span_singleton_le_iff_mem _).1 hJ

/-- **Rational points**: over an algebraically closed field `k`, every maximal ideal of a finite
type `k`-algebra has residue field `k` (Nullstellensatz). -/
theorem algebraMap_surjective_quot {k : Type*} [Field k] [IsAlgClosed k] [Algebra k R]
    [Algebra.FiniteType k R] (P : Ideal R) [P.IsMaximal] :
    Function.Surjective (algebraMap k (R ⧸ P)) := by
  letI := Ideal.Quotient.field P
  haveI : Algebra.FiniteType k (R ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P)
      Ideal.Quotient.mk_surjective
  haveI := finite_of_finite_type_of_isJacobsonRing k (R ⧸ P)
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := R ⧸ P)).2

section Artinian

open Polynomial

variable {O k : Type*} [CommRing O] [Field k] (θ : O →+* k) (S : Type*) [CommRing S]
  [Algebra O[X] S]

/-- `O[X] → k`, `p ↦ θ (p(0))`. -/
noncomputable def evZero : O[X] →+* k := eval₂RingHom θ 0

lemma evZero_surjective (hθ : Function.Surjective θ) : Function.Surjective (evZero θ) :=
  fun c ↦ by
    obtain ⟨o, rfl⟩ := hθ c
    exact ⟨C o, by simp [evZero]⟩

/-- **A finite `O[X]`-algebra killed by `ker θ` and `X` is Artinian** (it is finite over
`O[X]/(ker θ, X) ≅ k`). -/
theorem isArtinianRing_of_finite (hθ : Function.Surjective θ) [Module.Finite O[X] S]
    (hker : ∀ o, θ o = 0 → algebraMap O[X] S (C o) = 0) (hX : algebraMap O[X] S X = 0) :
    IsArtinianRing S := by
  set I := RingHom.ker (evZero θ)
  haveI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (evZero_surjective θ hθ)
  have hI : I ≤ RingHom.ker (algebraMap O[X] S) := by
    intro p hp
    rw [RingHom.mem_ker] at hp ⊢
    have hp0 : θ (p.coeff 0) = 0 := by
      rw [← hp, evZero, coe_eval₂RingHom, eval₂_at_zero]
    obtain ⟨q, hq⟩ := X_dvd_iff.mpr (show (p - C (p.coeff 0)).coeff 0 = 0 by simp)
    rw [show p = C (p.coeff 0) + X * q by rw [← hq]; ring, map_add, map_mul, hX, zero_mul,
      add_zero, hker _ hp0]
  letI : Field (O[X] ⧸ I) := Ideal.Quotient.field I
  letI : Algebra (O[X] ⧸ I) S := (Ideal.Quotient.lift I (algebraMap O[X] S) hI).toAlgebra
  haveI : IsScalarTower O[X] (O[X] ⧸ I) S := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.Finite (O[X] ⧸ I) S := Module.Finite.of_restrictScalars_finite O[X] _ S
  exact IsArtinianRing.of_finite (O[X] ⧸ I) S

end Artinian

end FormalPoints

end SemistableReduction
