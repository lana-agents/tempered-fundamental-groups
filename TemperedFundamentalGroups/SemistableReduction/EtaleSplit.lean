/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Etale.QuasiFinite
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.LocalRing.Etale

/-!
# Finite étale covers acquire sections étale locally

Let `R → C` be a finite local homomorphism of local rings inducing an isomorphism of residue
fields, `C → B` finite étale and `Q` a prime of `B` over the closed point of `C`. We construct an
étale neighbourhood `(R', P)` of the closed point of `R` and a prime `P₁` of `R' ⊗[R] C` over `P`
such that `B` acquires a `C`-algebra section after base change to `(R' ⊗[R] C)_{P₁}`.

* `SemistableReduction.EtaleSplit.surjective_algebraMap_residueField_of_forall_sub_mem`: if
  every element of `T` is congruent modulo `q` to an element of `A`, then `κ(p) → κ(q)` is
  surjective.
* `SemistableReduction.EtaleSplit.exists_ringHom_localization_of_isIdempotentElem`: a finite
  étale `A`-algebra `T` with an idempotent `e` cutting out a unique prime `P` over `p` with
  trivial residue field extension has an `A`-algebra map `T → A_p`.
* `SemistableReduction.EtaleSplit.exists_etale_section`: the main result.

The proof: a standard étale `R`-algebra `R₀` realises the residue field `κ(Q)` (primitive
element theorem), then Stacks 00UJ (`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`)
applied to the finite `R₀`-algebra `R₀ ⊗[R] B` at the kernel of `R₀ ⊗[R] B → κ(Q)` isolates a
local factor with trivial residue field extension, which is then isomorphic to the base after
localisation (`Localization.localRingHom_surjective_of_primesOver_eq_singleton` and freeness).
-/

open TensorProduct Polynomial

namespace SemistableReduction

namespace EtaleSplit

/-- If every element of `T` is congruent modulo `q` to an element of `A`, the map of residue
fields `κ(p) → κ(q)` is surjective. -/
theorem surjective_algebraMap_residueField_of_forall_sub_mem {A T : Type*} [CommRing A]
    [CommRing T] [Algebra A T] (p : Ideal A) [p.IsPrime] (q : Ideal T) [q.IsPrime]
    [q.LiesOver p] [Algebra (Localization.AtPrime p) (Localization.AtPrime q)]
    [Localization.AtPrime.IsLiesOverAlgebra p q]
    (h : ∀ t : T, ∃ a : A, t - algebraMap A T a ∈ q) :
    Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
  have key : ∀ x : T ⧸ q, algebraMap (T ⧸ q) q.ResidueField x ∈
      (algebraMap p.ResidueField q.ResidueField).fieldRange := by
    intro x
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, ha⟩ := h t
    refine ⟨algebraMap A p.ResidueField a, ?_⟩
    rw [Ideal.algebraMap_quotient_residueField_mk, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply A T q.ResidueField, eq_comm, ← sub_eq_zero, ← map_sub,
      Ideal.algebraMap_residueField_eq_zero]
    exact ha
  intro z
  obtain ⟨x, y, -, rfl⟩ := IsFractionRing.div_surjective (T ⧸ q) z
  exact div_mem (key x) (key y)

/-- Let `T` be a finite étale `A`-algebra, `p` a prime of `A`, `e` an idempotent of `T` and `P`
the unique prime of `T` over `p` not containing `e`. If every element of `T` is congruent
modulo `P` to an element of `A` (trivial residue field extension), then there is an
`A`-algebra homomorphism `T → A_p`. -/
theorem exists_ringHom_localization_of_isIdempotentElem {A T : Type*} [CommRing A] [CommRing T]
    [Algebra A T] [Module.Finite A T] [Algebra.Etale A T] (p : Ideal A) [p.IsPrime] {e : T}
    (he : IsIdempotentElem e) (P : Ideal T) [P.IsPrime] [P.LiesOver p] (heP : e ∉ P)
    (huniq : ∀ P' : Ideal T, P'.IsPrime → P'.LiesOver p → e ∉ P' → P' = P)
    (hres : ∀ t : T, ∃ a : A, t - algebraMap A T a ∈ P) :
    ∃ φ : T →+* Localization.AtPrime p, φ.comp (algebraMap A T) = algebraMap A _ := by
  let E := Localization.Away e
  have hdisj : Disjoint (Submonoid.powers e : Set T) P :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime e).mpr heP
  let q : Ideal E := P.map (algebraMap T E)
  have : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers e) E P ‹_› hdisj
  have hqP : q.under T = P := IsLocalization.under_map_of_isPrime_disjoint (.powers e) E ‹_› hdisj
  have : q.LiesOver P := ⟨hqP.symm⟩
  have : q.LiesOver p := .trans q P p
  have hsurj : Function.Surjective (algebraMap T E) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  have : Module.Finite A E :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom A T E).toLinearMap hsurj
  have hprimes : p.primesOver E = {q} := by
    ext Q
    refine ⟨fun ⟨hQ, hQp⟩ ↦ ?_, ?_⟩
    · have heQ : e ∉ Q.under T := fun h ↦ hQ.ne_top
        (Ideal.eq_top_of_isUnit_mem _ h (IsLocalization.Away.algebraMap_isUnit e))
      have := huniq _ inferInstance inferInstance heQ
      rw [Set.mem_singleton_iff, ← IsLocalization.map_under (.powers e) E Q, this]
    · rintro rfl
      exact ⟨inferInstance, inferInstance⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  have hres' : Function.Surjective (algebraMap p.ResidueField q.ResidueField) := by
    refine surjective_algebraMap_residueField_of_forall_sub_mem p q fun x ↦ ?_
    obtain ⟨t, rfl⟩ := hsurj x
    obtain ⟨a, ha⟩ := hres t
    exact ⟨a, by
      rw [IsScalarTower.algebraMap_apply A T E, ← map_sub]
      exact Ideal.mem_map_of_mem _ ha⟩
  have h₁ : Function.Surjective
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.localRingHom_surjective_of_primesOver_eq_singleton hprimes hres'
  have := Localization.finite_of_primesOver_eq_singleton hprimes
  have : Module.Free (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.free_of_flat_of_isLocalRing
  have h₂ : Function.Injective
      (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    FaithfulSMul.algebraMap_injective _ _
  let iso := RingEquiv.ofBijective
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) ⟨h₂, h₁⟩
  refine ⟨iso.symm.toRingHom.comp
    ((algebraMap E (Localization.AtPrime q)).comp (algebraMap T E)), ?_⟩
  ext a
  apply iso.injective
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply, iso, RingEquiv.ofBijective_apply]
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

/-- The preimage of an ideal under an `R`-algebra homomorphism has the same contraction to `R`. -/
theorem under_comap_algHom {R X Y F : Type*} [CommRing R] [CommRing X] [CommRing Y]
    [Algebra R X] [Algebra R Y] [FunLike F X Y] [AlgHomClass F R X Y] (f : F) (I : Ideal Y) :
    (I.comap f).under R = I.under R := by
  ext r
  simp [Ideal.under, AlgHomClass.commutes]

section Main

attribute [local instance] Algebra.TensorProduct.rightAlgebra

universe u

/-- The main construction behind `exists_etale_section`, given an étale `R`-algebra `R₀` with a
surjection `R₀ → κ(Q)`: Stacks 00UJ applied to `R₀ ⊗[R] B` at the kernel of `R₀ ⊗[R] B → κ(Q)`
isolates a factor of `(R' ⊗[R] C) ⊗[C] B` with trivial residue field extension. -/
theorem exists_etale_section_of_surjective {R C B R₀ : Type u} [CommRing R] [CommRing C]
    [CommRing B] [CommRing R₀] [Algebra R C] [Algebra C B] [Algebra R B] [IsScalarTower R C B]
    [Algebra R R₀] [Algebra.Etale R R₀] [IsLocalRing R] [IsLocalRing C]
    [IsLocalHom (algebraMap R C)] [Module.Finite R C] [Module.Finite C B] [Algebra.Etale C B]
    (Q : Ideal B) [Q.IsPrime] [Q.LiesOver (IsLocalRing.maximalIdeal C)]
    (φ₀ : R₀ →ₐ[R] Q.ResidueField) (hφ₀ : Function.Surjective φ₀) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver (IsLocalRing.maximalIdeal R)) (P₁ : Ideal (R' ⊗[R] C))
      (_ : P₁.IsPrime) (_ : P₁.LiesOver P) (ψ : B →+* Localization.AtPrime P₁),
      ψ.comp (algebraMap C B) = (algebraMap (R' ⊗[R] C) (Localization.AtPrime P₁)).comp
        Algebra.TensorProduct.includeRight.toRingHom := by
  classical
  haveI : Module.Finite R B := .trans C B
  -- The prime `q₀` of `R₀ ⊗[R] B`, the kernel of `R₀ ⊗[R] B → κ(Q)`.
  let Φ : R₀ ⊗[R] B →ₐ[R] Q.ResidueField :=
    Algebra.TensorProduct.lift φ₀ (IsScalarTower.toAlgHom R B Q.ResidueField)
      (fun _ _ ↦ Commute.all _ _)
  let q₀ : Ideal (R₀ ⊗[R] B) := RingHom.ker Φ
  have : q₀.IsPrime := RingHom.ker_isPrime _
  have hq₀R : q₀.under R = IsLocalRing.maximalIdeal R := by
    rw [(Ideal.LiesOver.trans Q (IsLocalRing.maximalIdeal C) (IsLocalRing.maximalIdeal R)).over]
    ext r
    simp only [Ideal.under, Ideal.mem_comap, q₀, RingHom.mem_ker, AlgHom.commutes]
    rw [IsScalarTower.algebraMap_apply R B Q.ResidueField, Ideal.algebraMap_residueField_eq_zero]
  have hres₀ : ∀ t : R₀ ⊗[R] B, ∃ r₀ : R₀, t - algebraMap R₀ _ r₀ ∈ q₀ := by
    intro t
    obtain ⟨r₀, hr₀⟩ := hφ₀ (Φ t)
    refine ⟨r₀, ?_⟩
    rw [RingHom.mem_ker, map_sub, ← hr₀]
    simp [Φ]
  -- Stacks 00UJ for the finite `R₀`-algebra `R₀ ⊗[R] B` at `q₀`.
  obtain ⟨R', _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', -, -, H⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (q₀.under R₀) q₀
  letI : Algebra R R' := ((algebraMap R₀ R').comp (algebraMap R R₀)).toAlgebra
  haveI : IsScalarTower R R₀ R' := .of_algebraMap_eq' rfl
  haveI : Algebra.Etale R R' := .comp R R₀ R'
  haveI : (q₀.under R₀).LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨by rw [Ideal.under_under, hq₀R]⟩
  haveI : P.LiesOver (IsLocalRing.maximalIdeal R) := .trans P (q₀.under R₀) _
  have hres' : ∀ t : R' ⊗[R₀] (R₀ ⊗[R] B), ∃ r : R', t - algebraMap R' _ r ∈ P' := by
    intro t
    induction t with
    | zero => exact ⟨0, by simp⟩
    | tmul r t =>
      obtain ⟨r₀, hr₀⟩ := hres₀ t
      refine ⟨r * algebraMap R₀ R' r₀, ?_⟩
      have h₁ : (Algebra.TensorProduct.includeRight t : R' ⊗[R₀] (R₀ ⊗[R] B)) -
          algebraMap R' _ (algebraMap R₀ R' r₀) ∈ P' := by
        rw [← hP'q, Ideal.mem_comap] at hr₀
        rw [← IsScalarTower.algebraMap_apply, ← (Algebra.TensorProduct.includeRight :
          R₀ ⊗[R] B →ₐ[R₀] R' ⊗[R₀] (R₀ ⊗[R] B)).commutes r₀, ← map_sub]
        exact hr₀
      convert Ideal.mul_mem_left _ (algebraMap R' (R' ⊗[R₀] (R₀ ⊗[R] B)) r) h₁ using 1
      rw [mul_sub, ← map_mul]
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by convert add_mem ha hb using 1; rw [map_add]; ring⟩
  -- Transport to `(R' ⊗[R] C) ⊗[C] B` and split off the factor cut out by `e`.
  let Ξ : R' ⊗[R₀] (R₀ ⊗[R] B) ≃ₐ[R'] (R' ⊗[R] C) ⊗[C] B :=
    (Algebra.TensorProduct.cancelBaseChange R R₀ R' R' B).trans
      (Algebra.IsPushout.cancelBaseChangeAlg R R' C (R' ⊗[R] C) B).symm
  let PT : Ideal ((R' ⊗[R] C) ⊗[C] B) := P'.comap Ξ.symm
  have hPT : PT.under R' = P := by
    change (P'.comap Ξ.symm).under R' = P
    rw [under_comap_algHom Ξ.symm P', ← Ideal.over_def P' P]
  let P₁ : Ideal (R' ⊗[R] C) := PT.under (R' ⊗[R] C)
  have hP₁ : P₁.LiesOver P := ⟨by rw [Ideal.under_under, hPT]⟩
  have huniq : ∀ P'' : Ideal ((R' ⊗[R] C) ⊗[C] B), P''.IsPrime → P''.LiesOver P₁ →
      Ξ e ∉ P'' → P'' = PT := by
    intro P'' _ _ heP''
    have : (P''.comap Ξ).LiesOver P := ⟨by
      rw [under_comap_algHom Ξ P'', ← Ideal.under_under (B := R' ⊗[R] C),
        ← Ideal.over_def P'' P₁, Ideal.under_under, hPT]⟩
    have hP'' := H (P''.comap Ξ) inferInstance this (by simpa using heP'')
    ext x
    simp [PT, ← hP'']
  have hres : ∀ t : (R' ⊗[R] C) ⊗[C] B, ∃ c : R' ⊗[R] C, t - algebraMap _ _ c ∈ PT := by
    intro t
    obtain ⟨r, hr⟩ := hres' (Ξ.symm t)
    refine ⟨algebraMap R' (R' ⊗[R] C) r, ?_⟩
    change Ξ.symm (t - algebraMap _ _ (algebraMap R' (R' ⊗[R] C) r)) ∈ P'
    rw [map_sub, ← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
    exact hr
  obtain ⟨φ, hφ⟩ := exists_ringHom_localization_of_isIdempotentElem P₁ (he.map Ξ) PT
    (by simpa [PT] using heP') huniq hres
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, inferInstance, inferInstance, P₁,
    inferInstance, hP₁, φ.comp (Algebra.TensorProduct.includeRight (R := C)
      (A := R' ⊗[R] C) (B := B)).toRingHom, ?_⟩
  rw [← hφ]
  ext c
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply]
  congr 1
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (R := C) (A := R' ⊗[R] C) (B := B) c).symm

/-- **Finite étale covers split étale locally.** Let `R → C` be a finite local homomorphism of
local rings inducing a bijection of residue fields, `B` a finite étale `C`-algebra and `Q` a prime
of `B` over the closed point of `C`. Then there are an étale `R`-algebra `R'`, a prime `P` of `R'`
over the closed point of `R` and a prime `P₁` of `R' ⊗[R] C` over `P` such that `B → C` has a
section after base change to `(R' ⊗[R] C)_{P₁}`, i.e. a ring homomorphism
`ψ : B → (R' ⊗[R] C)_{P₁}` compatible with `C → R' ⊗[R] C`. -/
theorem exists_etale_section {R C B : Type u} [CommRing R] [CommRing C] [CommRing B]
    [Algebra R C] [Algebra C B] [Algebra R B] [IsScalarTower R C B] [IsLocalRing R]
    [IsLocalRing C] [IsLocalHom (algebraMap R C)] [Module.Finite R C]
    (hκ : Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R C)))
    [Module.Finite C B] [Algebra.Etale C B] (Q : Ideal B) [Q.IsPrime]
    [Q.LiesOver (IsLocalRing.maximalIdeal C)] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver (IsLocalRing.maximalIdeal R)) (P₁ : Ideal (R' ⊗[R] C))
      (_ : P₁.IsPrime) (_ : P₁.LiesOver P) (ψ : B →+* Localization.AtPrime P₁),
      ψ.comp (algebraMap C B) = (algebraMap (R' ⊗[R] C) (Localization.AtPrime P₁)).comp
        Algebra.TensorProduct.includeRight.toRingHom := by
  -- A standard étale `R`-algebra `R₀` with a surjection onto `κ(Q)`.
  set mC := IsLocalRing.maximalIdeal C
  letI := Localization.AtPrime.algebraOfLiesOver mC Q
  have hRk : Function.Surjective (algebraMap R mC.ResidueField) := by
    intro y
    obtain ⟨c, rfl⟩ := Ideal.algebraMap_residueField_surjective mC y
    obtain ⟨r, hr⟩ := hκ.2 (IsLocalRing.residue C c)
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    refine ⟨r, ?_⟩
    rw [IsScalarTower.algebraMap_apply R C mC.ResidueField, eq_comm, ← sub_eq_zero, ← map_sub,
      Ideal.algebraMap_residueField_eq_zero, ← IsLocalRing.residue_eq_zero_iff, map_sub, ← hr,
      IsLocalRing.ResidueField.map_residue, sub_self]
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element mC.ResidueField Q.ResidueField
  have hθi : IsIntegral mC.ResidueField θ := .of_finite _ θ
  obtain ⟨f, hfg, -, hfm⟩ := lifts_and_natDegree_eq_and_monic
    (f := algebraMap R mC.ResidueField) (p := minpoly mC.ResidueField θ)
    ((lifts_iff_coeff_lifts _).mpr fun n ↦ hRk _) (minpoly.monic hθi)
  let P₀ : StandardEtalePair R := ⟨f, hfm, derivative f, ⟨1, 0, 1, by ring⟩⟩
  have hθP : P₀.HasMap θ := by
    refine ⟨?_, ?_⟩
    · change aeval θ f = 0
      rw [← aeval_map_algebraMap mC.ResidueField, hfg]
      exact minpoly.aeval _ θ
    · change IsUnit (aeval θ (derivative f))
      rw [isUnit_iff_ne_zero, ← aeval_map_algebraMap mC.ResidueField, ← derivative_map, hfg]
      exact (Algebra.IsSeparable.isSeparable mC.ResidueField θ).aeval_derivative_ne_zero
        (minpoly.aeval _ θ)
  refine exists_etale_section_of_surjective Q (P₀.lift θ hθP) fun z ↦ ?_
  have hz : z ∈ Algebra.adjoin mC.ResidueField {θ} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hθi.isAlgebraic, hθ]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  obtain ⟨p', rfl⟩ := Polynomial.map_surjective (algebraMap R mC.ResidueField) hRk p
  refine ⟨aeval P₀.X p', ?_⟩
  rw [← Polynomial.aeval_algHom_apply, P₀.lift_X]
  simp [aeval_map_algebraMap]

end Main

end EtaleSplit

end SemistableReduction
