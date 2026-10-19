/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib

/-!
# Étale algebras over reduced Noetherian rings are reduced

* **`EtaleReduced.isReduced_of_etale`**: an étale algebra `E` over a reduced Noetherian ring `A`
  is reduced.

## Proof

`A` has finitely many minimal primes `p`, each `A_p` is a field (a reduced local ring of
dimension `0`), and `A → ∏_p A_p` is injective (the minimal primes of a reduced ring intersect in
`0`). Since `E` is flat over `A`, `E = A ⊗[A] E → (∏_p A_p) ⊗[A] E = ∏_p A_p ⊗[A] E` is injective,
and every `A_p ⊗[A] E` is étale over the field `A_p`, hence reduced
(`Algebra.FormallyUnramified.isReduced_of_field`).
-/

open TensorProduct

namespace SemistableReduction

namespace EtaleReduced

variable {A : Type*} [CommRing A]

/-- The localization of a reduced ring at a minimal prime is a field. -/
lemma isField_localization [IsReduced A] (p : minimalPrimes A) :
    haveI : p.1.IsPrime := p.2.1.1
    IsField (Localization.AtPrime p.1) := by
  haveI : p.1.IsPrime := p.2.1.1
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p.1) := .of_isLocalization _ p.2 _
  exact Ring.KrullDimLE.isField_of_isReduced

/-- In a reduced ring, an element vanishing at all minimal primes is zero. -/
lemma eq_zero_of_forall_minimalPrimes [IsReduced A] {a : A} (h : ∀ p ∈ minimalPrimes A, a ∈ p) :
    a = 0 := by
  have ha : a ∈ sInf (minimalPrimes A) := Submodule.mem_sInf.2 h
  rw [minimalPrimes, Ideal.sInf_minimalPrimes] at ha
  obtain ⟨n, hn⟩ := ha
  exact IsReduced.eq_zero a ⟨n, (Submodule.mem_bot _).1 hn⟩

variable (A) (E : Type*) [CommRing E] [Algebra A E]

/-- **An étale algebra over a reduced Noetherian ring is reduced.** -/
theorem isReduced_of_etale [IsNoetherianRing A] [IsReduced A] [Algebra.Etale A E] :
    IsReduced E := by
  haveI : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  haveI : Fintype (minimalPrimes A) := Fintype.ofFinite _
  classical
  haveI (p : minimalPrimes A) : p.1.IsPrime := p.2.1.1
  let L : minimalPrimes A → Type _ := fun p ↦ Localization.AtPrime p.1
  -- `A → ∏ A_p` is injective
  let f : A →ₗ[A] ∀ p, L p := LinearMap.pi fun p ↦ (Algebra.linearMap A (L p))
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro a ha
    rw [LinearMap.mem_ker] at ha
    rw [Submodule.mem_bot]
    refine eq_zero_of_forall_minimalPrimes fun p hp ↦ ?_
    have h0 : algebraMap A (L ⟨p, hp⟩) a = 0 := congrFun ha ⟨p, hp⟩
    haveI : p.IsPrime := hp.1.1
    obtain ⟨⟨s, hs⟩, hsa⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl _ a).1 h0
    exact (‹p.IsPrime›.mem_or_mem_of_mul_eq_zero hsa).resolve_left hs
  have hinj := Module.Flat.rTensor_preserves_injective_linearMap (M := E) f hf
  -- every `A_p ⊗ E` is reduced
  have hred : ∀ p, IsReduced (L p ⊗[A] E) := fun p ↦ by
    letI : Field (L p) := (isField_localization p).toField
    exact Algebra.FormallyUnramified.isReduced_of_field (L p) (L p ⊗[A] E)
  refine ⟨fun x hx ↦ ?_⟩
  have key : ∀ p, (1 : L p) ⊗ₜ[A] x = 0 := fun p ↦ by
    have : IsNilpotent ((1 : L p) ⊗ₜ[A] x) :=
      hx.map (Algebra.TensorProduct.includeRight : E →ₐ[A] L p ⊗[A] E)
    exact (hred p).eq_zero _ this
  have h1 : LinearMap.rTensor E f ((1 : A) ⊗ₜ[A] x) = 0 := by
    apply (TensorProduct.piLeft A E L).injective
    ext p
    simp only [LinearMap.rTensor_tmul, map_zero, TensorProduct.piLeft, Pi.zero_apply,
      LinearEquiv.trans_apply, TensorProduct.comm_tmul, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul,
      LinearEquiv.piCongrRight_apply]
    have hf1 : f 1 p = 1 := by simp [f]
    rw [hf1]
    exact key p
  have h2 : (1 : A) ⊗ₜ[A] x = 0 := hinj (by rw [h1, map_zero])
  have := congrArg (TensorProduct.lid A E) h2
  simpa using this

end EtaleReduced

end SemistableReduction
