/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Killing the Kähler differentials (Blueprint §12.8, M2.5 (f), generic algebra)

Generic algebra for the generic-fibre étaleness of the normalised model: an `R`-algebra `S` whose
module of differentials `Ω[S⁄R]` is killed by an element `c` is formally unramified after
inverting `c`, and the killing can be checked modulo an ideal coming from the base.

* **`KaehlerDifferential.mem_smul_top_of_map_eq_zero`**: for an ideal `I` of a ring `A` below
  `R`, a differential of `S` vanishing in `Ω[(S ⧸ I S)⁄R]` lies in `I Ω[S⁄R]` (the conormal
  sequence `I/I² → (S ⧸ I S) ⊗ Ω[S⁄R] → Ω[(S ⧸ I S)⁄R] → 0`,
  `KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange`, and `d(I S) ⊆ I Ω[S⁄R]`
  because `d` kills the image of `A`);
* **`KaehlerDifferential.smul_mem_smul_top_of_quot`**: if `c` kills `Ω[(S ⧸ I S)⁄R]`, then
  `c Ω[S⁄R] ⊆ I Ω[S⁄R]`;
* **`KaehlerKill.formallyUnramified_away`**: if `c ∈ S` kills `Ω[S⁄R]`, then `S[1/c]` is formally
  unramified over every `R' ` between `R` and `S[1/c]` (`Ω[S[1/c]⁄R] = Ω[S⁄R][1/c]`,
  `KaehlerDifferential.isLocalizedModule_map`);
* **`KaehlerKill.etale_away`**: if moreover `S[1/c]` is flat and of finite presentation over
  `R'`, it is étale over `R'` (`Algebra.Etale.of_formallyUnramified_of_flat`, Stacks 08WD).
-/

universe u

open TensorProduct

namespace KaehlerDifferential

variable {A R S : Type u} [CommRing A] [CommRing R] [CommRing S] [Algebra A R] [Algebra R S]
  [Algebra A S] [IsScalarTower A R S] (I : Ideal A)

/-- `d` maps the extended ideal `I S` into `I Ω[S⁄R]`. -/
lemma D_mem_smul_top {x : S} (hx : x ∈ I.map (algebraMap A S)) :
    D R S x ∈ I.map (algebraMap A S) • (⊤ : Submodule S Ω[S⁄R]) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, -, rfl⟩ := hy
    rw [IsScalarTower.algebraMap_apply A R S, Derivation.map_algebraMap]
    exact zero_mem _
  | zero => simp
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul s y hy ih =>
    rw [smul_eq_mul, Derivation.leibniz]
    refine add_mem (Submodule.smul_mem _ s ih) ?_
    exact Submodule.smul_mem_smul hy Submodule.mem_top

/-- **Differentials modulo an ideal of the base**: a differential of `S` vanishing in
`Ω[(S ⧸ I S)⁄R]` lies in `I Ω[S⁄R]`. -/
theorem mem_smul_top_of_map_eq_zero {ω : Ω[S⁄R]}
    (hω : map R R S (S ⧸ I.map (algebraMap A S)) ω = 0) :
    ω ∈ I.map (algebraMap A S) • (⊤ : Submodule S Ω[S⁄R]) := by
  set J := I.map (algebraMap A S)
  have hsurj : Function.Surjective (algebraMap S (S ⧸ J)) := Ideal.Quotient.mk_surjective
  have hker : (1 : S ⧸ J) ⊗ₜ[S] ω ∈ LinearMap.range (kerCotangentToTensor R S (S ⧸ J)) := by
    rw [range_kerCotangentToTensor R S (S ⧸ J) hsurj]
    change mapBaseChange R S (S ⧸ J) ((1 : S ⧸ J) ⊗ₜ[S] ω) = 0
    rw [mapBaseChange_tmul, one_smul, hω]
  obtain ⟨y, hy⟩ := hker
  obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective _ y
  rw [kerCotangentToTensor_toCotangent] at hy
  have hxJ : (x : S) ∈ J := by
    have h : (algebraMap S (S ⧸ J)) (x : S) = 0 := x.2
    exact Ideal.Quotient.eq_zero_iff_mem.1 h
  have hD := D_mem_smul_top (R := R) I hxJ
  have h0 : (1 : S ⧸ J) ⊗ₜ[S] (ω - D R S x) = 0 := by rw [tmul_sub, hy, sub_self]
  have h1 := congrArg (quotTensorEquivQuotSMul Ω[S⁄R] J) h0
  rw [map_zero, ← map_one (Ideal.Quotient.mk J), quotTensorEquivQuotSMul_mk_tmul, one_smul,
    Submodule.Quotient.mk_eq_zero] at h1
  simpa using add_mem h1 hD

/-- If `c` kills `Ω[(S ⧸ I S)⁄R]`, then `c Ω[S⁄R] ⊆ I Ω[S⁄R]`. -/
theorem smul_mem_smul_top_of_quot {c : S}
    (hc : ∀ ω : Ω[(S ⧸ I.map (algebraMap A S))⁄R],
      Ideal.Quotient.mk (I.map (algebraMap A S)) c • ω = 0) (ω : Ω[S⁄R]) :
    c • ω ∈ I.map (algebraMap A S) • (⊤ : Submodule S Ω[S⁄R]) := by
  refine mem_smul_top_of_map_eq_zero I ?_
  rw [map_smul]
  exact hc _

end KaehlerDifferential

namespace KaehlerKill

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] {c : S}
  (hc : ∀ ω : Ω[S⁄R], c • ω = 0) (S' : Type u) [CommRing S'] [Algebra S S']
  [IsLocalization.Away c S'] [Algebra R S'] [IsScalarTower R S S']

include hc in
/-- If `c` kills `Ω[S⁄R]`, then `Ω[S[1/c]⁄R] = 0`. -/
lemma subsingleton_away : Subsingleton Ω[S'⁄R] := by
  refine ⟨fun z z' ↦ ?_⟩
  suffices h : ∀ z : Ω[S'⁄R], z = 0 by rw [h z, h z']
  intro z
  obtain ⟨⟨ω, s⟩, hs⟩ := IsLocalizedModule.surj (Submonoid.powers c)
    (KaehlerDifferential.map R R S S') z
  have hmap : KaehlerDifferential.map R R S S' ω = 0 := by
    have h1 : c • KaehlerDifferential.map R R S S' ω = 0 := by rw [← map_smul, hc, map_zero]
    have hu := IsLocalizedModule.map_units (KaehlerDifferential.map R R S S')
      (⟨c, Submonoid.mem_powers c⟩ : Submonoid.powers c)
    exact (Module.End.isUnit_iff _).1 hu |>.1 (h1.trans (map_zero _).symm)
  have h2 : s.1 • z = 0 := by rw [← hmap]; exact hs
  have hu := IsLocalizedModule.map_units (KaehlerDifferential.map R R S S') s
  exact (Module.End.isUnit_iff _).1 hu |>.1 (h2.trans (map_zero _).symm)

include hc in
/-- **Formal unramifiedness after inverting a killer of the differentials**: if `c` kills
`Ω[S⁄R]`, then `S[1/c]` is formally unramified over every `R'` between `R` and `S[1/c]`. -/
theorem formallyUnramified_away (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' S']
    [IsScalarTower R R' S'] : Algebra.FormallyUnramified R' S' := by
  haveI : Algebra.FormallyUnramified R S' := ⟨subsingleton_away hc S'⟩
  exact Algebra.FormallyUnramified.of_restrictScalars R R' S'

include hc in
/-- **Étaleness after inverting a killer of the differentials**: if `c` kills `Ω[S⁄R]` and
`S[1/c]` is flat and of finite presentation over `R'` (between `R` and `S[1/c]`), then `S[1/c]`
is étale over `R'`. -/
theorem etale_away (R' : Type u) [CommRing R'] [Algebra R R'] [Algebra R' S']
    [IsScalarTower R R' S'] [Algebra.FinitePresentation R' S'] [Module.Flat R' S'] :
    Algebra.Etale R' S' := by
  haveI := formallyUnramified_away hc S' R'
  exact Algebra.Etale.of_formallyUnramified_of_flat

end KaehlerKill
