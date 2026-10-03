/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CurveIntegralClosure
import TemperedFundamentalGroups.SemistableReduction.CurveDivisor

/-!
# Generators of integral closures on curves

Blueprint §9.9, S7.7. Let `κ / k` be a field and `t ∈ κ` transcendental over the perfect field `k`
with `κ` finite over `k(t)`.

* `isIntegral_of_forall_mem`: an element in every place of `κ / k` containing `t` is integral over
  `k[t]` (Chevalley);
* `exists_generators`: there are finitely many `gᵢ`, integral over `k[t]`, such that every element
  integral over `k[t]` is `Σ cᵢ(t) gᵢ` (`CurveIntegralClosure.isNoetherian_integralClosure` in the
  coordinate `t`).
-/

open Polynomial
open scoped IntermediateField nonZeroDivisors

namespace SemistableReduction

namespace CurveGenerators

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]

/-- An element lying in every place of `κ / k` containing `t` is integral over `k[t]`. -/
lemma isIntegral_of_forall_mem {t f : κ}
    (h : ∀ P : CurvePlace k κ, t ∈ P.V → f ∈ P.V) : IsIntegral (Algebra.adjoin k {t}) f := by
  by_contra hf
  set A := integralClosure (Algebra.adjoin k {t}) κ
  have hfA : f ∉ A.toSubring := hf
  haveI : IsIntegrallyClosedIn A.toSubring κ := inferInstanceAs (IsIntegrallyClosedIn A κ)
  obtain ⟨V, hAV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hfA
  have hmem (y : κ) (hy : y ∈ Algebra.adjoin k {t}) : y ∈ V := hAV <| by
    change y ∈ A
    rw [mem_integralClosure_iff]
    exact (isIntegral_algebraMap (x := (⟨y, hy⟩ : Algebra.adjoin k {t})))
  have hC (c : k) : algebraMap k κ c ∈ V := hmem _ (Subalgebra.algebraMap_mem _ c)
  have ht : t ∈ V := hmem _ (Algebra.self_mem_adjoin_singleton k t)
  have hne : V ≠ ⊤ := fun h' ↦ hfV (h' ▸ trivial)
  exact hfV (h ⟨V, hC, hne⟩ ht)

/-- An element integral over `k[t] ⊆ κ` is a root of a monic polynomial in `k[X][T]` evaluated at
`X = t`. -/
lemma exists_monic_of_isIntegral {t f : κ} (hint : IsIntegral (Algebra.adjoin k {t}) f) :
    ∃ P : k[X][X], P.Monic ∧ eval₂ (aeval t : k[X] →ₐ[k] κ).toRingHom f P = 0 := by
  obtain ⟨p, hpm, hp⟩ := hint
  have hrange : Algebra.adjoin k {t} = (aeval t : k[X] →ₐ[k] κ).range :=
    Algebra.adjoin_singleton_eq_range_aeval k t
  set ψ : k[X] →+* Algebra.adjoin k {t} :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
      (aeval t : k[X] →ₐ[k] κ).rangeRestrict.toRingHom
  have hψ : Function.Surjective ψ :=
    (Subalgebra.equivOfEq _ _ hrange.symm).surjective.comp (AlgHom.rangeRestrict_surjective _)
  have hlift : p ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    exact fun n ↦ hψ _
  obtain ⟨P, hPmap, -, hPm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hpm
  refine ⟨P, hPm, ?_⟩
  have hcomp : (Algebra.adjoin k {t}).val.toRingHom.comp ψ =
      (aeval t : k[X] →ₐ[k] κ).toRingHom := by
    ext Q
    · simp [ψ]
    · simp [ψ]
  rw [← hcomp, ← eval₂_map, hPmap]
  exact hp

variable [PerfectField k] {t : κ} (ht : Transcendental k t)

omit [PerfectField k] in
include ht in
lemma nonZeroDivisors_le_comap_aeval : k[X]⁰ ≤ κ⁰.comap (aeval t : k[X] →ₐ[k] κ) :=
  nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (transcendental_iff_injective.1 ht)

include ht in
/-- **Generators of the integral closure of `k[t]`** (`k` perfect). -/
theorem exists_generators [FiniteDimensional k⟮t⟯ κ] :
    ∃ G : Finset κ, (∀ g ∈ G, IsIntegral (Algebra.adjoin k {t}) g) ∧
      ∀ α, IsIntegral (Algebra.adjoin k {t}) α →
        ∃ c : κ → k[X], α = ∑ g ∈ G, aeval t (c g) * g := by
  classical
  -- the coordinate `t`
  set φ : RatFunc k →ₐ[k] κ := RatFunc.liftAlgHom (aeval t) (nonZeroDivisors_le_comap_aeval ht)
  have hφ (P : k[X]) : φ (algebraMap k[X] (RatFunc k) P) = aeval t P := by
    have := RatFunc.liftAlgHom_apply_div (aeval t) (nonZeroDivisors_le_comap_aeval ht) P 1
    simpa [φ] using this
  letI : Algebra (RatFunc k) κ := φ.toRingHom.toAlgebra
  letI : Algebra k[X] κ := (aeval t : k[X] →ₐ[k] κ).toRingHom.toAlgebra
  haveI : IsScalarTower k[X] (RatFunc k) κ := IsScalarTower.of_algebraMap_eq fun P ↦ (hφ P).symm
  -- finiteness over `k(X)`
  have hmem (z : κ) : z ∈ k⟮t⟯ ↔ ∃ ψ : RatFunc k, φ ψ = z := by
    have h := IntermediateField.adjoin_map k {(RatFunc.X : RatFunc k)} φ
    have hX : φ RatFunc.X = t := by
      rw [← RatFunc.algebraMap_X, hφ, aeval_X]
    rw [RatFunc.adjoin_X, Set.image_singleton, hX] at h
    rw [← h, IntermediateField.mem_map]
    simp
  haveI : FiniteDimensional (RatFunc k) κ := by
    set E := k⟮t⟯
    let i : RatFunc k ≃+* E :=
      RingEquiv.ofBijective ((φ.toRingHom : RatFunc k →+* κ).codRestrict E.toSubfield
        fun y ↦ (hmem _).2 ⟨y, rfl⟩)
        ⟨fun a b h ↦ φ.toRingHom.injective (congrArg Subtype.val h), fun z ↦ by
          obtain ⟨y, hy⟩ := (hmem (z : κ)).1 z.2
          exact ⟨y, Subtype.ext hy⟩⟩
    have hfr : Module.finrank (RatFunc k) κ = Module.finrank E κ :=
      Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) (by ext; rfl)
    exact Module.finite_of_finrank_pos (by rw [hfr]; exact Module.finrank_pos)
  haveI := CurveIntegralClosure.isNoetherian_integralClosure (k := k) (L := κ)
  obtain ⟨G₀, hG₀⟩ := IsNoetherian.noetherian (R := k[X]) (⊤ : Submodule k[X]
    (integralClosure k[X] κ))
  -- integrality over `k[X]` vs over `k[t]`
  have hrange : Algebra.adjoin k {t} = (aeval t : k[X] →ₐ[k] κ).range :=
    Algebra.adjoin_singleton_eq_range_aeval k t
  set ψ : k[X] →+* Algebra.adjoin k {t} :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
      (aeval t : k[X] →ₐ[k] κ).rangeRestrict.toRingHom
  have hint (α : κ) : IsIntegral (Algebra.adjoin k {t}) α ↔ IsIntegral k[X] α := by
    constructor
    · intro h
      obtain ⟨P, hPm, hP⟩ := exists_monic_of_isIntegral h
      exact ⟨P, hPm, hP⟩
    · intro h
      refine IsIntegral.map_of_comp_eq ψ (RingHom.id κ) ?_ h
      ext P <;> rfl
  set G : Finset κ := G₀.image fun g ↦ ((g : integralClosure k[X] κ) : κ)
  refine ⟨G, fun g hg ↦ ?_, fun α hα ↦ ?_⟩
  · obtain ⟨g₀, -, rfl⟩ := Finset.mem_image.1 hg
    exact (hint _).2 g₀.2
  · have hα' : (⟨α, (hint α).1 hα⟩ : integralClosure k[X] κ) ∈
        Submodule.span k[X] (G₀ : Set (integralClosure k[X] κ)) := by
      rw [hG₀]; trivial
    have := Submodule.mem_map_of_mem (f := (integralClosure k[X] κ).val.toLinearMap) hα'
    rw [Submodule.map_span] at this
    have hset : (integralClosure k[X] κ).val.toLinearMap '' (G₀ : Set _) = (G : Set κ) := by
      simp only [G, Finset.coe_image]
      rfl
    rw [hset] at this
    obtain ⟨c, -, hc⟩ := Submodule.mem_span_finset.1 this
    exact ⟨c, hc.symm⟩

end CurveGenerators

end SemistableReduction
