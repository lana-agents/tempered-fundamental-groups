/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Jacobson.Ring

/-!
# Étaleness of a special fibre from étaleness at its points

Let `S` be a finite type algebra over a Noetherian ring `A`, `I` an ideal of `A`, `S̄ = S/IS` the
fibre over `A/I` and `g ∈ S`.

* `EtaleQuot.etale_quot_away`: if `S_g` is étale over `A`, then `S̄_ḡ` is étale over `A/I`
  (étaleness is stable under base change; the square `A → S_g`, `A/I → S̄_ḡ` is a pushout,
  pasted from `S ⊗_A A/I = S̄` and the localization square).
* **`EtaleQuot.etale_quot_of_isEtaleAt`**: if `S` is étale over `A` at every prime `Q ⊇ IS` with
  `g ∉ Q`, then `S̄_ḡ` is étale over `A/I`.
* **`EtaleQuot.etale_quot_of_isEtaleAt_maximal`**: the same when `A/I` is a Jacobson ring, from
  the maximal ideals `Q ⊇ IS` with `g ∉ Q` only (the étale locus is open, so stable under
  generization).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace EtaleQuot

noncomputable section

variable {A S : Type u} [CommRing A] [CommRing S] [Algebra A S] (I : Ideal A)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- The fibre `S ⊗_A A/I = S/IS`: the square `A → S`, `A/I → S/IS` is a pushout. -/
instance isPushout_quot : Algebra.IsPushout A S (A ⧸ I) (S ⧸ I.map (algebraMap A S)) := by
  refine Algebra.IsPushout.of_equiv (h := TensorProduct.isPushout)
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm ?_
  ext a
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
    ((1 : S) ⊗ₜ[A] Ideal.Quotient.mk I a) = Ideal.Quotient.mk _ (algebraMap A S a)
  rw [AlgEquiv.symm_apply_eq, Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← map_one (Ideal.Quotient.mk I),
    ]
  rw [map_one, ← Algebra.algebraMap_eq_smul_one]
  rfl

variable (g : S)

/-- `S_g → S̄_ḡ`. -/
abbrev algAway : Algebra (Localization.Away g)
    (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) :=
  (Localization.awayMap (Ideal.Quotient.mk (I.map (algebraMap A S))) g).toAlgebra

attribute [local instance] algAway

instance : IsScalarTower S (Localization.Away g)
    (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = Localization.awayMap (Ideal.Quotient.mk (I.map (algebraMap A S))) g
      (algebraMap S _ x)
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    rfl

instance : IsScalarTower A (Localization.Away g)
    (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A S (Localization.Away g),
      ← IsScalarTower.algebraMap_apply S (Localization.Away g),
      IsScalarTower.algebraMap_apply A S]

instance : IsScalarTower A (A ⧸ I)
    (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) :=
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply A (S ⧸ I.map (algebraMap A S)),
      IsScalarTower.algebraMap_apply (A ⧸ I) (S ⧸ I.map (algebraMap A S))]
    rfl

instance isLocalization_quot_away :
    IsLocalization (Algebra.algebraMapSubmonoid (S ⧸ I.map (algebraMap A S))
      (Submonoid.powers g)) (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) := by
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  exact Localization.isLocalization

/-- **`S̄_ḡ = S_g ⊗_A A/I`.** -/
instance isPushout_quot_away : Algebra.IsPushout A (Localization.Away g) (A ⧸ I)
    (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) := by
  haveI : Algebra.IsPushout S (Localization.Away g) (S ⧸ I.map (algebraMap A S))
      (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers g) (Localization.Away g)
      (S ⧸ I.map (algebraMap A S)) _).symm
  exact (Algebra.IsPushout.comp_iff A S (A ⧸ I) (S ⧸ I.map (algebraMap A S))).2 this

/-- **Étaleness passes to the fibre**: `S_g` étale over `A` ⇒ `S̄_ḡ` étale over `A/I`. -/
theorem etale_quot_away [Algebra.Etale A (Localization.Away g)] :
    Algebra.Etale (A ⧸ I) (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) :=
  RingHom.etale_algebraMap.mp (RingHom.Etale.isStableUnderBaseChange A (Localization.Away g)
    (A ⧸ I) _ (RingHom.etale_algebraMap.mpr inferInstance))

variable [Algebra.FinitePresentation A S]
  [Algebra.FinitePresentation (A ⧸ I) (S ⧸ I.map (algebraMap A S))]

/-- A prime of the fibre at which `S` is étale over `A` is in the étale locus of the fibre. -/
lemma mem_etaleLocus_quot (Q : PrimeSpectrum (S ⧸ I.map (algebraMap A S)))
    (h : Algebra.IsEtaleAt A (Q.asIdeal.comap (Ideal.Quotient.mk (I.map (algebraMap A S))))) :
    Q ∈ Algebra.etaleLocus (A ⧸ I) (S ⧸ I.map (algebraMap A S)) := by
  obtain ⟨g', hg', hE⟩ := Algebra.exists_etale_of_isEtaleAt (R := A)
    (Q.asIdeal.comap (Ideal.Quotient.mk (I.map (algebraMap A S))))
  haveI := etale_quot_away I g'
  exact (Algebra.basicOpen_subset_etaleLocus_iff_etale (R := A ⧸ I)
    (f := Ideal.Quotient.mk (I.map (algebraMap A S)) g')).2 inferInstance
    ((PrimeSpectrum.mem_basicOpen _ _).2 hg')

/-- **The fibre is étale where `S` is**: if `S` is étale over `A` at every prime `Q ⊇ IS` with
`g ∉ Q`, then `S̄_ḡ` is étale over `A/I`. -/
theorem etale_quot_of_isEtaleAt
    (h : ∀ (Q : Ideal S) [Q.IsPrime], I.map (algebraMap A S) ≤ Q → g ∉ Q →
      Algebra.IsEtaleAt A Q) :
    Algebra.Etale (A ⧸ I) (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) := by
  rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
  intro Q hQ
  refine mem_etaleLocus_quot I Q (h _ ?_ hQ)
  intro x hx
  rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
  exact Q.asIdeal.zero_mem

/-- **The same from the maximal ideals**, for a Jacobson fibre: if `S` is étale over `A` at every
maximal ideal `Q ⊇ IS` with `g ∉ Q`, then `S̄_ḡ` is étale over `A/I`. -/
theorem etale_quot_of_isEtaleAt_maximal [IsJacobsonRing (S ⧸ I.map (algebraMap A S))]
    (h : ∀ (Q : Ideal S) [Q.IsMaximal], I.map (algebraMap A S) ≤ Q → g ∉ Q →
      Algebra.IsEtaleAt A Q) :
    Algebra.Etale (A ⧸ I) (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A S)) g)) := by
  rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
  intro Q hQ
  have hQ' : Ideal.Quotient.mk (I.map (algebraMap A S)) g ∉ Q.asIdeal :=
    (PrimeSpectrum.mem_basicOpen _ _).1 hQ
  -- a maximal ideal above `Q` avoiding `ḡ`
  rw [← (IsJacobsonRing.out' _ (Ideal.IsPrime.isRadical Q.2)), Ideal.jacobson,
    Submodule.mem_sInf] at hQ'
  simp only [Set.mem_setOf_eq, not_forall] at hQ'
  obtain ⟨M, ⟨hQM, hM⟩, hgM⟩ := hQ'
  haveI : (Ideal.comap (Ideal.Quotient.mk (I.map (algebraMap A S))) M).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  have hmem : (⟨M, hM.isPrime⟩ : PrimeSpectrum _) ∈
      Algebra.etaleLocus (A ⧸ I) (S ⧸ I.map (algebraMap A S)) := by
    refine mem_etaleLocus_quot I ⟨M, hM.isPrime⟩ (h _ ?_ hgM)
    intro x hx
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hx]
    exact M.zero_mem
  exact Algebra.isOpen_etaleLocus.stableUnderGeneralization
    ((PrimeSpectrum.le_iff_specializes Q ⟨M, hM.isPrime⟩).1 hQM) hmem

end

end EtaleQuot

end SemistableReduction
