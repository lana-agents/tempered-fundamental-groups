/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Decomposition groups at unramified primes with separable residue extension (generic)

MR13 step 7, D1 (S1): the decomposition group `Γ_v` of a component of the special fibre of a
Galois cover acts faithfully on the component, with degree `|Γ_v|`. Mathlib's
`Ideal.card_stabilizer_eq_card_inertia_mul_finrank` and `Ideal.card_inertia_eq_ramificationIdxIn`
assume a perfect residue field (to make the residue extension Galois); the residue field of the
generic point of a component in characteristic `p` (e.g. `k(h')`) is not perfect, so we prove
the versions with a **separable** residue extension instead (the proofs are Mathlib's):

* **`GaloisComponent.card_stabilizer_eq_card_inertia_mul_inertiaDeg`**:
  `|Stab_G(P)| = |I_G(P)| · f(P | p)`;
* **`GaloisComponent.card_inertia_eq_ramificationIdxIn`**: `|I_G(P)| = e(p)` (finite flat
  extension of domains);
* **`GaloisComponent.inertia_eq_bot`**: if `e(p) = 1` the inertia group is trivial;
* **`GaloisComponent.card_stabilizer_eq_inertiaDeg`**: then `|Stab_G(P)| = f(P | p)`;
* **`GaloisComponent.stabilizerHom_bijective`**: then `Stab_G(P) → Aut_{A/p}(B/P)` is bijective
  (Mathlib's surjectivity, injectivity from the trivial inertia).
-/

open Algebra Module

namespace SemistableReduction

namespace GaloisComponent

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

open scoped Pointwise

attribute [local instance] Ideal.Quotient.field in
/-- **`|Stab_G(P)| = |I_G(P)| · f(P | p)`** for a separable residue extension (Mathlib's
`Ideal.card_stabilizer_eq_card_inertia_mul_finrank` with `PerfectField` replaced by
separability). -/
theorem card_stabilizer_eq_card_inertia_mul_inertiaDeg (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime]
    (hsep : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsSeparable p.ResidueField P.ResidueField) :
    Nat.card (MulAction.stabilizer G P) = Nat.card (Ideal.inertia G P) * P.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  haveI := hsep
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : Normal p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField
  have : IsGalois p.ResidueField P.ResidueField := isGalois_iff.mpr ⟨inferInstance, this⟩
  have : Module.Finite p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.finite_of_isInvariant G p P p.ResidueField P.ResidueField
  have : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P p.ResidueField P.ResidueField).toEquiv
  rw [Ideal.inertiaDeg_eq p P, ← IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField,
    ← this, ← ((Ideal.inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Ideal.inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

/-- `#{P' | p} · |I_G(P)| · f(P | p) = |G|` (separable residue extension). -/
lemma ncard_primesOver_mul_card_inertia_mul_inertiaDeg (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime]
    (hsep : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsSeparable p.ResidueField P.ResidueField) :
    (p.primesOver S).ncard * Nat.card (Ideal.inertia G P) * P.inertiaDeg R = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_inertiaDeg p P hsep,
    ← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

variable [IsDomain R] [IsDomain S] [Module.Finite R S] [Module.Flat R S]

/-- **`|I_G(P)| = e(p)`** (separable residue extension). -/
lemma card_inertia_eq_ramificationIdxIn (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime]
    [P.IsPrime] (hsep : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsSeparable p.ResidueField P.ResidueField) :
    Nat.card (Ideal.inertia G P) = Ideal.ramificationIdxIn p S := by
  have H := ncard_primesOver_mul_card_inertia_mul_inertiaDeg (G := G) p P hsep
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard ≠ 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S ≠ 0 := by grind [Nat.card_pos]
  rwa [← Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,
    mul_assoc, mul_right_inj' h1, mul_left_inj' h2] at H

/-- **Unramified ⇒ trivial inertia**: if `e(p) = 1` and the residue extension is separable, the
inertia group of `P` is trivial. -/
theorem inertia_eq_bot (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    (hsep : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsSeparable p.ResidueField P.ResidueField) (he : Ideal.ramificationIdxIn p S = 1) :
    Ideal.inertia G P = ⊥ :=
  Subgroup.eq_bot_of_card_eq _ ((card_inertia_eq_ramificationIdxIn p P hsep).trans he)

/-- **`|Stab_G(P)| = f(P | p)`** at an unramified prime with separable residue extension. -/
theorem card_stabilizer_eq_inertiaDeg (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime]
    [P.IsPrime] (hsep : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsSeparable p.ResidueField P.ResidueField)
    (he : Ideal.ramificationIdxIn p S = 1) :
    Nat.card (MulAction.stabilizer G P) = P.inertiaDeg R := by
  rw [card_stabilizer_eq_card_inertia_mul_inertiaDeg p P hsep,
    card_inertia_eq_ramificationIdxIn p P hsep, he, one_mul]

/-- **The decomposition group acts faithfully on the component**: at an unramified prime with
separable residue extension, `Stab_G(P) → Aut_{R/p}(S/P)` is bijective. -/
theorem stabilizerHom_bijective (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPrime]
    [P.IsPrime] (hsep : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsSeparable p.ResidueField P.ResidueField)
    (he : Ideal.ramificationIdxIn p S = 1) :
    Function.Bijective (Ideal.Quotient.stabilizerHom P p G) := by
  refine ⟨?_, Ideal.Quotient.stabilizerHom_surjective G p P⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hk : g ∈ (Ideal.Quotient.stabilizerHom P p G).ker := hg
  rw [Ideal.Quotient.ker_stabilizerHom] at hk
  have hI : (g : G) ∈ Ideal.inertia G P := fun x ↦ hk x
  rw [inertia_eq_bot p P hsep he, Subgroup.mem_bot] at hI
  exact Subtype.ext hI

end GaloisComponent

end SemistableReduction
