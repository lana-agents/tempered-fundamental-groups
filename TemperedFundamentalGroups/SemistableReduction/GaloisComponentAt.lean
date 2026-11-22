/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.GaloisComponent
import TemperedFundamentalGroups.SemistableReduction.GaloisLocalization
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Decomposition groups of unramified primes over a discrete valuation point (generic)

MR13 step 7, D1 (S1c). Let `G` be a Galois group of a finite extension of domains `B/A`
(`IsGaloisGroup G A B`), `p` a prime of `A` with `A_p` a discrete valuation ring (the generic
point of a component of the special fibre, e.g. the line `ℓ` in the Tate chart `T1`) and `P` a
prime of `B` over `p` at which `B/A` is unramified (`Algebra.IsUnramifiedAt A P`; for a Galois
Tate cover this is `CovData.hunr₁`). Then (localising at `p`, where `B_p` is finite flat over the
discrete valuation ring `A_p`, `GaloisLocalization`, and applying `GaloisComponent` there):

* **`GaloisComponent.inertia_eq_bot_of_isUnramifiedAt`**: the inertia group of `P` is trivial;
* **`GaloisComponent.card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt`**: `|Stab_G(P)| = f(P | p)`;
* **`GaloisComponent.stabilizerHom_bijective_of_isUnramifiedAt`**: the decomposition group acts
  faithfully on the component ring, `Stab_G(P) ≃ Aut_{A/p}(B/P)`.
-/

open Algebra
open scoped Pointwise

namespace SemistableReduction

namespace GaloisComponent

variable {A B G : Type*} [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [Algebra A B]
  [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B] [Module.Finite A B]
  [FaithfulSMul A B]

open GaloisLocalization

omit [IsDomain A] [IsDomain B] [Finite G] [Module.Finite A B] [FaithfulSMul A B] in
/-- An element of `G` acting trivially modulo `P` acts trivially modulo `P B_M`. -/
lemma mem_inertia_map (M : Submonoid A) (P : Ideal B) [P.IsPrime]
    (hd : Disjoint (↑(Algebra.algebraMapSubmonoid B M) : Set B) ↑P) {σ : G}
    (hσ : σ ∈ Ideal.inertia G P) :
    σ ∈ Ideal.inertia G (P.map (algebraMap B (BM B M))) := by
  have hP' := IsLocalization.isPrime_of_isPrime_disjoint (Algebra.algebraMapSubmonoid B M)
    (BM B M) P ‹_› hd
  intro x
  obtain ⟨b, ⟨_, m, hm, rfl⟩, rfl⟩ :=
    IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B M) x
  set y := IsLocalization.mk' (BM B M) b
    (⟨algebraMap A B m, m, hm, rfl⟩ : Algebra.algebraMapSubmonoid B M)
  have hy : y * algebraMap B (BM B M) (algebraMap A B m) = algebraMap B (BM B M) b :=
    IsLocalization.mk'_spec _ _ _
  have hσy : (σ • y) * algebraMap B (BM B M) (algebraMap A B m) =
      algebraMap B (BM B M) (σ • b) := by
    have h := congrArg (σ • ·) hy
    simp only [smul_mul', smul_algebraMap', smul_algebraMap] at h
    exact h
  have hmem : (σ • y - y) * algebraMap B (BM B M) (algebraMap A B m) ∈
      P.map (algebraMap B (BM B M)) := by
    rw [sub_mul, hσy, hy, ← map_sub]
    exact Ideal.mem_map_of_mem _ (hσ b)
  rcases hP'.mem_or_mem hmem with h | h
  · exact h
  · exfalso
    rw [IsLocalization.mem_map_algebraMap_iff (Algebra.algebraMapSubmonoid B M)] at h
    obtain ⟨⟨c, ⟨_, n, hn, rfl⟩⟩, hc⟩ := h
    have hc' : algebraMap B (BM B M) (algebraMap A B m * algebraMap A B n) =
        algebraMap B (BM B M) c := by
      rw [map_mul, ← hc, mul_comm]
    obtain ⟨⟨_, r, hr, rfl⟩, hr'⟩ := (IsLocalization.eq_iff_exists
      (Algebra.algebraMapSubmonoid B M) (BM B M)).1 hc'
    have hin : algebraMap A B r * (algebraMap A B m * algebraMap A B n) ∈ P := by
      rw [hr']
      exact P.mul_mem_left _ c.2
    have hM : algebraMap A B (r * (m * n)) ∈ (Algebra.algebraMapSubmonoid B M : Set B) :=
      ⟨r * (m * n), M.mul_mem hr (M.mul_mem hm hn), rfl⟩
    rw [map_mul, map_mul] at hM
    exact Set.disjoint_left.1 hd hM hin

variable (p : Ideal A) [p.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime p)]
  (P : Ideal B) [P.IsPrime] [P.LiesOver p] [Algebra.IsUnramifiedAt A P]

omit [IsDomain A] [IsDomain B] [Module.Finite A B] [FaithfulSMul A B]
  [IsDiscreteValuationRing (Localization.AtPrime p)] [P.IsPrime] [Algebra.IsUnramifiedAt A P] in
/-- `algebraMapSubmonoid B (A ∖ p)` is disjoint from `P`. -/
lemma disjoint_primeCompl :
    Disjoint (↑(Algebra.algebraMapSubmonoid B p.primeCompl) : Set B) ↑P := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, hm, rfl⟩ hmP
  exact hm (by rw [Ideal.over_def P p]; exact Ideal.mem_comap.2 hmP)

include p in
/-- **Unramified ⇒ trivial inertia** (`A_p` a discrete valuation ring, `B/A` finite with
Galois group `G`). -/
theorem inertia_eq_bot_of_isUnramifiedAt : Ideal.inertia G P = ⊥ := by
  set M := p.primeCompl
  have hM : Algebra.algebraMapSubmonoid B M ≤ nonZeroDivisors B := by
    apply le_nonZeroDivisors_of_noZeroDivisors
    rintro ⟨m, hm, h0⟩
    exact hm ((FaithfulSMul.algebraMap_injective A B (h0.trans (map_zero _).symm)) ▸ p.zero_mem)
  have hinj : Function.Injective (algebraMap B (BM B M)) := IsLocalization.injective _ hM
  haveI : IsDomain (BM B M) := IsLocalization.isDomain_of_le_nonZeroDivisors (BM B M) hM
  haveI : IsGaloisGroup G (Localization M) (BM B M) := isGaloisGroup B M hinj
  have hinjA : Function.Injective (algebraMap (Localization M) (BM B M)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
    have h1 : algebraMap (Localization M) (BM B M) (IsLocalization.mk' (Localization M) a s) *
        algebraMap A (BM B M) s = algebraMap A (BM B M) a := by
      rw [IsScalarTower.algebraMap_apply A (Localization M) (BM B M) (s : A), ← map_mul,
        IsLocalization.mk'_spec, ← IsScalarTower.algebraMap_apply]
    rw [hx, zero_mul, IsScalarTower.algebraMap_apply A B (BM B M)] at h1
    have h3 : algebraMap A B a = 0 := hinj (by rw [map_zero]; exact h1.symm)
    have h2 : a = 0 := FaithfulSMul.algebraMap_injective A B (h3.trans (map_zero _).symm)
    rw [h2, IsLocalization.mk'_zero]
  haveI : FaithfulSMul (Localization M) (BM B M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hinjA
  haveI : Module.Flat (Localization M) (BM B M) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout,
      ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  have hd := disjoint_primeCompl p P
  set P' := P.map (algebraMap B (BM B M))
  haveI hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint _ _ P ‹_› hd
  haveI : P'.LiesOver P :=
    ⟨(IsLocalization.under_map_of_isPrime_disjoint _ (BM B M) ‹_› hd).symm⟩
  haveI : Algebra.FormallyUnramified B (BM B M) :=
    .of_isLocalization (Algebra.algebraMapSubmonoid B M)
  haveI : Algebra.IsUnramifiedAt B P' :=
    Algebra.FormallyUnramified.comp B (BM B M) (Localization.AtPrime P')
  haveI : Algebra.IsUnramifiedAt A P' := Algebra.IsUnramifiedAt.comp P P'
  haveI : Algebra.IsUnramifiedAt (Localization M) P' :=
    Algebra.IsUnramifiedAt.of_restrictScalars A P'
  set p' := P'.under (Localization M)
  haveI : P'.LiesOver p' := ⟨rfl⟩
  have hsep : letI := Localization.AtPrime.algebraOfLiesOver p' P'
      Algebra.IsSeparable p'.ResidueField P'.ResidueField := by
    letI := Localization.AtPrime.algebraOfLiesOver p' P'
    infer_instance
  have he : Ideal.ramificationIdxIn p' (BM B M) = 1 := by
    rw [Ideal.ramificationIdxIn_eq_ramificationIdx p' P' G]
    exact Ideal.ramificationIdx_eq_one P' _
  have hbot := inertia_eq_bot (G := G) p' P' hsep he
  rw [eq_bot_iff] at hbot ⊢
  exact fun σ hσ ↦ hbot (mem_inertia_map M P hd hσ)

include p in
/-- **`|Stab_G(P)| = f(P | p)`** at an unramified prime over a discrete valuation point. -/
theorem card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt :
    Nat.card (MulAction.stabilizer G P) = P.inertiaDeg A := by
  have hsep : letI := Localization.AtPrime.algebraOfLiesOver p P
      Algebra.IsSeparable p.ResidueField P.ResidueField := by
    letI := Localization.AtPrime.algebraOfLiesOver p P
    infer_instance
  rw [card_stabilizer_eq_card_inertia_mul_inertiaDeg p P hsep,
    inertia_eq_bot_of_isUnramifiedAt p P, Subgroup.card_bot, one_mul]

include p in
/-- **The decomposition group acts faithfully on the component**: `Stab_G(P) → Aut_{A/p}(B/P)`
is bijective at an unramified prime over a discrete valuation point. -/
theorem stabilizerHom_bijective_of_isUnramifiedAt :
    Function.Bijective (Ideal.Quotient.stabilizerHom P p G) := by
  refine ⟨?_, Ideal.Quotient.stabilizerHom_surjective G p P⟩
  rw [injective_iff_map_eq_one]
  intro g hg
  have hk : g ∈ (Ideal.Quotient.stabilizerHom P p G).ker := hg
  rw [Ideal.Quotient.ker_stabilizerHom] at hk
  have hI : (g : G) ∈ Ideal.inertia G P := fun x ↦ hk x
  rw [inertia_eq_bot_of_isUnramifiedAt p P, Subgroup.mem_bot] at hI
  exact Subtype.ext hI

end GaloisComponent

end SemistableReduction
