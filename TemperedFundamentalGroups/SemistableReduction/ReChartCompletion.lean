/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CompletionEtale
import Mathlib.RingTheory.AdjoinRoot

/-!
# Re-charting the formal local data of a covering (generic commutative algebra)

Two generic steps of re-charting the Kummer data of an admissible covering along the marked
points (MR13 (e2), the cusp factors of the datum `S0` of `P1Three` from those of a covering given
in other coordinates):

* **`ReChart.hatAwayEquiv`**: the completion along `f` does not change under localization away
  from an element `a` which is a unit modulo `f` (`V(f) ⊆ D(a)`):
  `R^∧_{(f)} ≃ R[1/a]^∧_{(f)}` (`CompletionEtale.equiv`; `comap_span_away`,
  `surjective_mk_away`), compatible with the maps from `R` (`hatAwayEquiv_algebraMap`);
* **`ReChart.rootScale`**: a change of the coordinate at the marked points by an `e`-th power of a
  unit does not change the cusp factor: `A[X]/(X^e − u^e t) ≃ₐ[A] A[X]/(X^e − t)`, `X ↦ u X`.
-/

universe u

open Polynomial

namespace ReChart

noncomputable section

/-! ### Completion along `f` and localization away from a unit modulo `f` -/

section Away

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (f a : R)
  [IsLocalization.Away a S] (h : IsUnit (Ideal.Quotient.mk (Ideal.span {f}) a))
include h

lemma comap_span_away :
    (Ideal.span {algebraMap R S f}).comap (algebraMap R S) = Ideal.span {f} := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hx
    obtain ⟨y, hy⟩ := hx
    obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers a) y
    simp only at hz
    have h1 : algebraMap R S (x * a ^ n) = algebraMap R S (z * f) := by
      rw [map_mul, ← hy, mul_right_comm, hz, ← map_mul]
    obtain ⟨⟨_, m, rfl⟩, hm⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers a) S).mp h1
    simp only at hm
    have h2 : Ideal.Quotient.mk (Ideal.span {f}) (a ^ m * (x * a ^ n)) = 0 := by
      rw [hm, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f))
    rw [map_mul, map_mul, map_pow, map_pow] at h2
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have hu := (h.pow m).mul (h.pow n)
    have h3 : (Ideal.Quotient.mk (Ideal.span {f}) a ^ m *
        Ideal.Quotient.mk (Ideal.span {f}) a ^ n) * Ideal.Quotient.mk (Ideal.span {f}) x = 0 := by
      rw [← h2]
      ring
    exact (hu.mul_right_eq_zero).mp h3
  · rw [← Ideal.map_le_iff_le_comap, Ideal.map_span, Set.image_singleton]

lemma surjective_mk_away :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {algebraMap R S f})).comp
      (algebraMap R S)) := by
  intro y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨⟨z, ⟨_, n, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers a) s
  simp only at hz
  obtain ⟨b, hb⟩ := h.exists_left_inv
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  rw [← map_mul, ← map_one (Ideal.Quotient.mk _), Ideal.Quotient.eq,
    Ideal.mem_span_singleton] at hb
  have h4 : b * a - 1 ∣ (b * a) ^ n - 1 := by
    simpa using sub_dvd_pow_sub_pow (b * a) 1 n
  obtain ⟨c, hc⟩ := dvd_trans hb h4
  refine ⟨z * b ^ n, ?_⟩
  rw [RingHom.comp_apply, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  refine ⟨s * algebraMap R S c, ?_⟩
  have hz' : algebraMap R S z = s * algebraMap R S a ^ n := by rw [← hz, map_pow]
  calc algebraMap R S (z * b ^ n) - s = s * algebraMap R S ((b * a) ^ n - 1) := by
        rw [map_mul, hz', map_sub, map_pow, map_pow, map_one, map_mul]; ring
    _ = _ := by rw [hc, map_mul]; ring

/-- **The completion along `f` is unchanged by localizing away from a unit modulo `f`.** -/
def hatAwayEquiv : AdicCompletion (Ideal.span {f}) R ≃+*
    AdicCompletion (Ideal.span {algebraMap R S f}) S :=
  haveI : Algebra.FormallyEtale R S := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers a)
  SemistableReduction.CompletionEtale.equiv _ _ (comap_span_away f a h) (surjective_mk_away f a h)

lemma hatAwayEquiv_algebraMap (r : R) :
    hatAwayEquiv (S := S) f a h (algebraMap R _ r) = algebraMap S _ (algebraMap R S r) := by
  haveI : Algebra.FormallyEtale R S := Algebra.FormallyEtale.of_isLocalization (Submonoid.powers a)
  exact SemistableReduction.CompletionEtale.equiv_algebraMap (comap_span_away f a h)
    (surjective_mk_away f a h) r

end Away

/-! ### Scaling the coordinate of a cusp factor -/

section Root

variable {A : Type u} [CommRing A] (e : ℕ)

lemma root_pow_eq (t : A) : (AdjoinRoot.root (X ^ e - C t)) ^ e = AdjoinRoot.of _ t := by
  have h := AdjoinRoot.eval₂_root (X ^ e - C t)
  rwa [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h

/-- `X ↦ v X` from `A[X]/(X^e − t')` to `A[X]/(X^e − t)` if `t' = v^e t`. -/
def rootScaleHom (v t' t : A) (ht : t' = v ^ e * t) :
    AdjoinRoot (X ^ e - C t') →ₐ[A] AdjoinRoot (X ^ e - C t) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (AdjoinRoot.of _ v * AdjoinRoot.root _) (by
    rw [eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow, root_pow_eq, ht]
    change _ - algebraMap A _ (v ^ e * t) = 0
    rw [AdjoinRoot.algebraMap_eq, map_mul, map_pow, sub_self])

lemma rootScaleHom_root (v t' t : A) (ht : t' = v ^ e * t) :
    rootScaleHom e v t' t ht (AdjoinRoot.root _) = AdjoinRoot.of _ v * AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

variable (u : Aˣ) (t : A)

/-- **Scaling the coordinate by a unit**: `A[X]/(X^e − u^e t) ≃ₐ[A] A[X]/(X^e − t)`, `X ↦ u X`. -/
def rootScale : AdjoinRoot (X ^ e - C ((u : A) ^ e * t)) ≃ₐ[A] AdjoinRoot (X ^ e - C t) :=
  AlgEquiv.ofAlgHom (rootScaleHom e (u : A) _ t rfl)
    (rootScaleHom e ((u⁻¹ : Aˣ) : A) t _ (by
      rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]))
    (AdjoinRoot.algHom_ext (by
      simp only [AlgHom.comp_apply, rootScaleHom_root, map_mul, ← AdjoinRoot.algebraMap_eq,
        AlgHom.commutes, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp))
    (AdjoinRoot.algHom_ext (by
      simp only [AlgHom.comp_apply, rootScaleHom_root, map_mul, ← AdjoinRoot.algebraMap_eq,
        AlgHom.commutes, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul]
      simp))

lemma rootScale_root :
    rootScale e u t (AdjoinRoot.root _) = AdjoinRoot.of _ (u : A) * AdjoinRoot.root _ :=
  rootScaleHom_root e (u : A) _ t rfl

end Root

end

end ReChart
