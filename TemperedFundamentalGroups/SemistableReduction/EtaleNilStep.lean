/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleNil
import TemperedFundamentalGroups.SemistableReduction.LevelTower

/-!
# Maps of étale lifts over consecutive levels (Blueprint §12.8, M2.3 (f), tower)

Let `R → R'` be a surjection (e.g. `T/ϖⁿ⁺²T → T/ϖⁿ⁺¹T`) with kernel `K`, `J ⊆ R` an ideal with
`J R'` nilpotent, `B` a formally étale `R`-algebra and `B'` a formally étale `R'`-algebra.

**`EtaleNil.surjective_of_red`**, **`EtaleNil.ker_of_red`**: an `R`-algebra map `φ : B → B'` whose
reduction `B/JB → B'/JB'` is bijective is surjective with kernel `K B`. (The base change
`R' ⊗_R B → B'` is a map of formally étale `R'`-algebras with bijective reduction, hence
bijective by `EtaleNil.bijective_of_red`.) This gives the successor maps of a tower of étale
lifts of one special fibre.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace EtaleNil

noncomputable section

variable {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
  (hq : Function.Surjective (algebraMap R R')) (J : Ideal R) {m : ℕ}
  (hJ : J.map (algebraMap R R') ^ m = ⊥)
  {B B' : Type u} [CommRing B] [CommRing B'] [Algebra R B] [Algebra R' B'] [Algebra R B']
  [IsScalarTower R R' B'] [Algebra.FormallyEtale R B] [Algebra.FormallyEtale R' B']
  (φ : B →ₐ[R] B')
  (hsurj : ∀ y : B', ∃ x : B, Ideal.Quotient.mk (JB J B') (φ x) = Ideal.Quotient.mk _ y)
  (hinj : ∀ x : B, φ x ∈ JB J B' → x ∈ JB J B)

omit [Algebra.FormallyEtale R B] [Algebra.FormallyEtale R' B'] in
lemma JB_eq : JB (J.map (algebraMap R R')) B' = JB J B' := by
  rw [JB, JB, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- The base change `R' ⊗_R B → B'` of `φ`. -/
def bc : R' ⊗[R] B →ₐ[R'] B' :=
  Algebra.TensorProduct.lift (Algebra.ofId R' B') φ fun _ _ ↦ Commute.all _ _

omit [Algebra.FormallyEtale R B] [Algebra.FormallyEtale R' B'] in
lemma bc_one_tmul (x : B) : bc (R' := R') φ ((1 : R') ⊗ₜ x) = φ x := by
  simp [bc]

include hq hJ hsurj hinj in
lemma bijective_bc : Function.Bijective (bc (R' := R') φ) := by
  refine bijective_of_red (J.map (algebraMap R R')) hJ (bc (R' := R') φ)
    ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, rfl⟩ := FormalGlueingQuot.exists_one_tmul hq x
    obtain ⟨b, rfl⟩ := FormalGlueingQuot.exists_one_tmul hq y
    rw [red_mk, red_mk, Ideal.Quotient.eq, JB_eq, bc_one_tmul, bc_one_tmul,
      ← map_sub] at hxy
    rw [Ideal.Quotient.eq, ← tmul_sub]
    have h := Ideal.mem_map_of_mem
      (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B).toRingHom (hinj _ hxy)
    rw [JB, Ideal.map_map] at h
    have e : (algebraMap R' (R' ⊗[R] B)).comp (algebraMap R R') =
        (Algebra.TensorProduct.includeRight : B →ₐ[R] R' ⊗[R] B).toRingHom.comp
          (algebraMap R B) := by
      refine RingHom.ext fun r ↦ ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [← IsScalarTower.algebraMap_apply]
      exact (AlgHom.commutes _ r).symm
    rw [JB, Ideal.map_map, e]
    exact h
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, hx⟩ := hsurj y
    refine ⟨Ideal.Quotient.mk _ ((1 : R') ⊗ₜ x), ?_⟩
    rw [red_mk, bc_one_tmul]
    have : JB (J.map (algebraMap R R')) B' = JB J B' := JB_eq (R' := R') J
    rw [Ideal.Quotient.eq] at hx ⊢
    rwa [this]

include hq hJ hsurj hinj in
/-- **The map is surjective.** -/
theorem surjective_of_red : Function.Surjective φ := fun y ↦ by
  obtain ⟨x, hx⟩ := (bijective_bc hq J hJ φ hsurj hinj).2 y
  obtain ⟨a, rfl⟩ := FormalGlueingQuot.exists_one_tmul hq x
  exact ⟨a, by rw [← hx, bc_one_tmul]⟩

include hq hJ hsurj hinj in
/-- **The kernel of the map is `(ker q) B`.** -/
theorem ker_of_red :
    RingHom.ker φ = (RingHom.ker (algebraMap R R')).map (algebraMap R B) := by
  rw [← LevelStep.ker_includeRight hq]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker, ← bc_one_tmul (R' := R') φ x]
  change bc (R' := R') φ ((1 : R') ⊗ₜ x) = 0 ↔ (1 : R') ⊗ₜ x = 0
  exact ⟨fun h ↦ (bijective_bc hq J hJ φ hsurj hinj).1 (h.trans (map_zero _).symm),
    fun h ↦ by rw [h, map_zero]⟩

end

end EtaleNil

end SemistableReduction
