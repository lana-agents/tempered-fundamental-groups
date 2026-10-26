/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Residue fields of étale algebras

Let `R → S` be étale, `𝔪 ⊆ R` maximal and `𝔫 ⊆ S` a prime lying over `𝔪`.

* `SemistableReduction.EtaleResidue.isMaximal_of_etale`: `𝔫` is maximal.
* `SemistableReduction.EtaleResidue.surjective_of_isSepClosed`: if `R ⧸ 𝔪` is separably
  closed, then `R → S ⧸ 𝔫` is surjective, i.e. the residue field extension is trivial.

Both follow from the fact that `κ(𝔫)` is a finite separable extension of `κ(𝔪)`
(`Algebra.IsUnramifiedAt`).
-/

namespace SemistableReduction

namespace EtaleResidue

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.Etale R S]
  (𝔪 : Ideal R) [𝔪.IsMaximal] (𝔫 : Ideal S) [𝔫.IsPrime]

/-- Separable closedness transports along ring isomorphisms. -/
theorem isSepClosed_of_ringEquiv {k k' : Type*} [Field k] [Field k'] (e : k ≃+* k')
    [IsSepClosed k] : IsSepClosed k' := by
  refine IsSepClosed.of_exists_root _ fun p _ hirr hsep ↦ ?_
  have hdeg : (p.map (e.symm : k' →+* k)).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective e.symm.injective]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root _ hdeg (hsep.map (f := (e.symm : k' →+* k)))
  refine ⟨e x, ?_⟩
  have := hx.map (f := (e : k →+* k'))
  have hc : (e : k →+* k').comp (e.symm : k' →+* k) = RingHom.id k' := by ext; simp
  rwa [Polynomial.map_map, hc, Polynomial.map_id] at this

theorem isMaximal_of_etale (h : 𝔫.comap (algebraMap R S) = 𝔪) : 𝔫.IsMaximal := by
  letI : 𝔫.LiesOver 𝔪 := ⟨h.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver 𝔪 𝔫
  have : Module.Finite R 𝔫.ResidueField := Module.Finite.trans 𝔪.ResidueField _
  have : Algebra.IsIntegral R (S ⧸ 𝔫) := by
    refine ⟨fun x ↦ ?_⟩
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R (S ⧸ 𝔫) 𝔫.ResidueField)
      𝔫.injective_algebraMap_quotient_residueField).mp ?_
    exact Algebra.IsIntegral.isIntegral _
  have hmax : (⊥ : Ideal (S ⧸ 𝔫)).IsMaximal := by
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) _ ?_
    rw [← RingHom.ker_eq_comap_bot, IsScalarTower.algebraMap_eq R S (S ⧸ 𝔫),
      ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker, h]
    infer_instance
  exact Ideal.Quotient.maximal_of_isField _ (Ring.isField_iff_maximal_bot.mpr hmax)

theorem surjective_of_isSepClosed (h : 𝔫.comap (algebraMap R S) = 𝔪)
    [hsc : letI := Ideal.Quotient.field 𝔪; IsSepClosed (R ⧸ 𝔪)] :
    Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S)) := by
  letI := Ideal.Quotient.field 𝔪
  letI : 𝔫.LiesOver 𝔪 := ⟨h.symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver 𝔪 𝔫
  have : IsSepClosed 𝔪.ResidueField := isSepClosed_of_ringEquiv
    (RingEquiv.ofBijective _ 𝔪.bijective_algebraMap_quotient_residueField)
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨a, ha⟩ := IsSepClosed.algebraMap_surjective 𝔪.ResidueField 𝔫.ResidueField
    (algebraMap S _ s)
  obtain ⟨r, rfl⟩ := 𝔪.algebraMap_residueField_surjective a
  refine ⟨r, 𝔫.injective_algebraMap_quotient_residueField ?_⟩
  rw [RingHom.comp_apply, Ideal.algebraMap_quotient_residueField_mk,
    Ideal.algebraMap_quotient_residueField_mk, ← ha,
    ← IsScalarTower.algebraMap_apply R S, ← IsScalarTower.algebraMap_apply R 𝔪.ResidueField]

/-- Variant of `surjective_of_isSepClosed` where `R ⧸ 𝔪` is a quotient of a separably closed
field `k`. -/
theorem surjective_of_isSepClosed' (h : 𝔫.comap (algebraMap R S) = 𝔪) {k : Type*} [Field k]
    [IsSepClosed k] (ρ : k →+* R ⧸ 𝔪) (hρ : Function.Surjective ρ) :
    Function.Surjective ((Ideal.Quotient.mk 𝔫).comp (algebraMap R S)) := by
  letI := Ideal.Quotient.field 𝔪
  have : IsSepClosed (R ⧸ 𝔪) :=
    isSepClosed_of_ringEquiv (RingEquiv.ofBijective ρ ⟨ρ.injective, hρ⟩)
  exact surjective_of_isSepClosed 𝔪 𝔫 h

end EtaleResidue

end SemistableReduction
