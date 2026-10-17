/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Exactness
import TemperedFundamentalGroups.SemistableReduction.CompleteFree
import TemperedFundamentalGroups.SemistableReduction.EtaleLiftHom

/-!
# Adic completeness of finite modules over a complete Noetherian ring (Blueprint §12.8, M2.2)

Let `A` be a Noetherian ring, `I`-adically complete. Then every finite `A`-module `M` is
`I`-adically complete (`isAdicComplete_of_finite`), and every finite `A`-algebra `B` is
`IB`-adically complete (`isAdicComplete_map_of_finite`). This is Stacks, Lemma 10.96.11
(Tag 031B: a finite module `M` over an `I`-adically complete ring with `⋂ Iⁿ M = 0` is complete),
with `⋂ Iⁿ M = 0` supplied by Krull's intersection theorem.

Proof: `M` is `I`-adically Hausdorff by Krull's intersection theorem (`I ⊆ J(A)`,
Mathlib's `IsHausdorff.of_le_jacobson`), and precomplete as a quotient of a finite free module
`A^n` (which is complete by `CompleteFree.isAdicComplete_of_basis`): the adic completion is
exact on surjections (`AdicCompletion.map_surjective`), so `M → M^` is surjective.

Consequences: reduction modulo `I` is fully faithful on finite étale `A`-algebras
(**`finiteEtaleHomEquiv`**), and (**`finiteEtaleEquivOfQuot`**): two finite étale `A`-algebras with
isomorphic reductions modulo `I` are isomorphic by a unique isomorphism lifting the given one — the
completeness hypotheses of `EtaleLift.algEquivOfQuot` are automatic over a complete Noetherian base.
This is the uniqueness half of M2.2 in the form needed for the formal patching (M2.3).
-/

namespace SemistableReduction

namespace CompleteFinite

variable {A : Type*} [CommRing A] (I : Ideal A)

/-- **Precompleteness passes to quotients**: the image of a precomplete module under a
surjective linear map is precomplete. -/
theorem isPrecomplete_of_surjective {M N : Type*} [AddCommGroup M] [Module A M] [AddCommGroup N]
    [Module A N] [IsPrecomplete I M] (f : M →ₗ[A] N) (hf : Function.Surjective f) :
    IsPrecomplete I N := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨x, rfl⟩ := AdicCompletion.map_surjective I hf y
  obtain ⟨m, rfl⟩ := AdicCompletion.of_surjective I M x
  exact ⟨f m, by rw [AdicCompletion.map_of]⟩

/-- **Complete Nakayama** (Stacks, Lemma 10.96.12, Tag 031D, for an algebra): if `A` is
`I`-adically complete, `B` is an `A`-algebra which is `I`-adically Hausdorff and `B/IB` is a
finite `A`-module, then `B` is a finite `A`-module. Lifts of generators of `B/IB` generate `B`
(`surjective_of_mkQ_comp_surjective`). -/
theorem finite_of_finite_quotient [IsAdicComplete I A] (B : Type*) [CommRing B] [Algebra A B]
    [IsHausdorff I B] [Module.Finite A (B ⧸ I.map (algebraMap A B))] : Module.Finite A B := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A (B ⧸ I.map (algebraMap A B))
  choose c hc using fun k : Fin n ↦ Ideal.Quotient.mk_surjective (f (Pi.single k 1))
  let g : (Fin n → A) →ₗ[A] B := (Pi.basisFun A (Fin n)).constr A c
  have hg : ∀ v, Ideal.Quotient.mk _ (g v) = f v := by
    intro v
    change (Ideal.Quotient.mkₐ A (I.map (algebraMap A B))).toLinearMap.comp g v = f v
    congr 1
    refine (Pi.basisFun A (Fin n)).ext fun k ↦ ?_
    simp [g, hc k]
  haveI : IsPrecomplete I (Fin n → A) :=
    (CompleteFree.isAdicComplete_of_basis I (Pi.basisFun A (Fin n))).toIsPrecomplete
  have hs : Function.Surjective ((I • ⊤ : Submodule A B).mkQ ∘ₗ g) := by
    intro y
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨v, hv⟩ := hf (Ideal.Quotient.mk _ z)
    refine ⟨v, ?_⟩
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.mkQ_apply,
      Submodule.Quotient.eq, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
      ← Ideal.Quotient.eq, hg, hv]
  exact Module.Finite.of_surjective g (surjective_of_mkQ_comp_surjective hs)

variable [IsNoetherianRing A] [IsAdicComplete I A]

/-- **A finite module over a complete Noetherian ring is complete** (Stacks, Tag 031B). -/
theorem isAdicComplete_of_finite (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] :
    IsAdicComplete I M := by
  haveI : IsHausdorff I M := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  haveI : IsPrecomplete I (Fin n → A) :=
    (CompleteFree.isAdicComplete_of_basis I (Pi.basisFun A (Fin n))).toIsPrecomplete
  haveI := isPrecomplete_of_surjective I f hf
  exact { toIsHausdorff := ‹_›, toIsPrecomplete := ‹_› }

/-- **A finite algebra over a complete Noetherian ring is `IB`-adically complete.** -/
theorem isAdicComplete_map_of_finite (B : Type*) [CommRing B] [Algebra A B] [Module.Finite A B] :
    IsAdicComplete (I.map (algebraMap A B)) B :=
  (IsAdicComplete.map_algebraMap_iff _ _).mpr (isAdicComplete_of_finite I B)

section Equiv

variable {B B' : Type*} [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B']
  [Module.Finite A B] [Module.Finite A B'] [Algebra.FormallyEtale A B]
  [Algebra.FormallyEtale A B']

/-- **Uniqueness of finite étale lifts over a complete Noetherian base**: an isomorphism of the
reductions modulo `I` of two finite (formally) étale `A`-algebras lifts to an isomorphism. -/
noncomputable def finiteEtaleEquivOfQuot
    (e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A] (B' ⧸ I.map (algebraMap A B'))) : B ≃ₐ[A] B' :=
  haveI := isAdicComplete_map_of_finite I B
  haveI := isAdicComplete_map_of_finite I B'
  EtaleLift.algEquivOfQuot I e

lemma mkₐ_comp_finiteEtaleEquivOfQuot
    (e : (B ⧸ I.map (algebraMap A B)) ≃ₐ[A] (B' ⧸ I.map (algebraMap A B'))) :
    (Ideal.Quotient.mkₐ A _).comp (finiteEtaleEquivOfQuot I e).toAlgHom =
      e.toAlgHom.comp (Ideal.Quotient.mkₐ A _) :=
  haveI := isAdicComplete_map_of_finite I B
  haveI := isAdicComplete_map_of_finite I B'
  EtaleLift.mkₐ_comp_algEquivOfQuot I e

omit [IsNoetherianRing A] [IsAdicComplete I A] [Module.Finite A B] [Algebra.FormallyEtale A B] in
lemma algebraMap_quot_eq_zero {a : A} (ha : a ∈ I) :
    algebraMap A (B ⧸ I.map (algebraMap A B)) a = 0 :=
  (Ideal.Quotient.eq_zero_iff_mem).2 (Ideal.mem_map_of_mem _ ha)

omit [Module.Finite A B] [Algebra.FormallyEtale A B] in
/-- Maps out of `B/IB` into an `A`-algebra killed by `I` are the maps out of `B`. -/
noncomputable def quotHomEquiv {C : Type*} [CommRing C] [Algebra A C]
    (hC : ∀ a ∈ I, algebraMap A C a = 0) :
    (B ⧸ I.map (algebraMap A B) →ₐ[A] C) ≃ (B →ₐ[A] C) where
  toFun φ := φ.comp (Ideal.Quotient.mkₐ A _)
  invFun g := Ideal.Quotient.liftₐ _ g fun x hx ↦ by
    have : I.map (algebraMap A B) ≤ RingHom.ker g :=
      Ideal.map_le_iff_le_comap.2 fun a ha ↦ by
        rw [Ideal.mem_comap, RingHom.mem_ker]
        exact (g.commutes a).trans (hC a ha)
    exact this hx
  left_inv φ := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  right_inv g := by
    ext x
    rfl

/-- **Full faithfulness of reduction on finite étale algebras** over a complete Noetherian base
(with `exists_finite_etale_lift`, the equivalence of Stacks, Tag 09ZL, for complete Noetherian
`(A, I)`): `A`-algebra maps `B → B'` are the `A`-algebra maps `B/IB → B'/IB'`. -/
noncomputable def finiteEtaleHomEquiv :
    (B →ₐ[A] B') ≃ (B ⧸ I.map (algebraMap A B) →ₐ[A] B' ⧸ I.map (algebraMap A B')) :=
  haveI := isAdicComplete_map_of_finite I B'
  (EtaleLift.homEquiv (I.map (algebraMap A B'))).trans
    (quotHomEquiv I fun _ ha ↦ algebraMap_quot_eq_zero I ha).symm

omit [Module.Finite A B] [Algebra.FormallyEtale A B'] in
lemma finiteEtaleHomEquiv_apply_mk (g : B →ₐ[A] B') (x : B) :
    finiteEtaleHomEquiv I g (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (g x) := rfl

end Equiv

end CompleteFinite

end SemistableReduction
