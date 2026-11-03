/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.LocalProperties.Basic

/-!
# Generic ranks in towers and along the special fibre (generic; MR13 (f), degree lemma)

Ranks of modules over commutative domains (`Module.finrank`, the rank over the fraction field):

* **`GenericRank.finrank_eq_mul`**: for a finite injective extension of domains `A → A'` and an
  `A'`-module `M`, `rank_A M = rank_A A' · rank_{A'} M`;
* **`GenericRank.isBaseChange_of_surjective`**: a surjection `f : M → N` with kernel `I • M`
  (`I = ker (R → S)`, `R → S` onto) is a base change of `M` to `S`;
* **`GenericRank.finrank_eq_of_isBaseChange`**: for a domain `P`, a finite flat `P`-module `M` and
  a base change `M → N` to a domain `P̄`, `rank_{P̄} N = rank_P M` (the rank of a finite flat module
  is constant on `Spec P`, `Module.rankAtStalk`);
* **`GenericRank.finrank_eq_of_fibre`**: the combination used for the lift of a tame cover: a finite
  `R`-algebra `B`, flat over a subring `P ⊆ R` with `R` finite free over `P`, and its reduction
  `B → C` over `P → P̄`, `R → R̄` (with `[R̄ : P̄] = [R : P] ≠ 0`) have the same rank:
  `rank_R B = rank_{R̄} C`.
-/

universe u

open Module nonZeroDivisors TensorProduct

namespace SemistableReduction

namespace GenericRank

section Tower

variable (A A' M : Type*) [CommRing A] [CommRing A'] [IsDomain A] [IsDomain A'] [Algebra A A']
  [AddCommGroup M] [Module A M] [Module A' M] [IsScalarTower A A' M]

/-- **Tower law for ranks over domains**: `rank_A M = rank_A A' · rank_{A'} M` for a finite
injective extension of domains `A → A'` and an `A'`-module `M`. -/
theorem finrank_eq_mul (hinj : Function.Injective (algebraMap A A')) [Module.Finite A A'] :
    finrank A M = finrank A A' * finrank A' M := by
  let S' : Submonoid A' := Algebra.algebraMapSubmonoid A' A⁰
  have hS' : S' ≤ A'⁰ := map_le_nonZeroDivisors_of_injective _ hinj le_rfl
  let F := FractionRing A
  let L := Localization S'
  haveI : IsDomain L := IsLocalization.isDomain_localization hS'
  haveI : Algebra.IsIntegral A A' := Algebra.IsIntegral.of_finite A A'
  have hint := isIntegral_localization (R := A) (S := A') (M := A⁰)
    (Rₘ := F) (Sₘ := L)
  letI : Algebra F L := (IsLocalization.map L (algebraMap A A')
    (show A⁰ ≤ S'.comap _ from A⁰.le_comap_map) : F →+* L).toAlgebra
  haveI : Algebra.IsIntegral F L := ⟨hint⟩
  letI : Field L := (isField_of_isIntegral_of_isField' (R := F) (Field.toIsField F)).toField
  haveI : IsScalarTower A F L := IsScalarTower.of_algebraMap_eq fun x ↦ by
    change algebraMap A L x = IsLocalization.map L (algebraMap A A') _ (algebraMap A F x)
    rw [IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]
  -- the localized module `N = L ⊗_{A'} M`
  let N := L ⊗[A'] M
  let f : M →ₗ[A'] N := TensorProduct.mk A' L M 1
  haveI : IsLocalizedModule S' f := inferInstance
  haveI : IsLocalizedModule A⁰ (f.restrictScalars A) := IsLocalizedModule.restrictScalars A⁰ f
  -- the same for `A' → L`
  let g : A' →ₗ[A'] L := Algebra.linearMap A' L
  haveI : IsLocalizedModule S' g := (isLocalizedModule_iff_isLocalization).2 inferInstance
  haveI : IsLocalizedModule A⁰ (g.restrictScalars A) := IsLocalizedModule.restrictScalars A⁰ g
  have h1 : finrank A M = finrank F N := by
    rw [← IsLocalizedModule.finrank_eq A⁰ (f.restrictScalars A) le_rfl]
    exact (congrArg Cardinal.toNat (IsLocalization.rank_eq F A⁰ le_rfl (N := N))).symm
  have h2 : finrank A A' = finrank F L := by
    rw [← IsLocalizedModule.finrank_eq A⁰ (g.restrictScalars A) le_rfl]
    exact (congrArg Cardinal.toNat (IsLocalization.rank_eq F A⁰ le_rfl (N := L))).symm
  have h3 : finrank A' M = finrank L N := by
    rw [← IsLocalizedModule.finrank_eq S' f hS']
    exact (congrArg Cardinal.toNat (IsLocalization.rank_eq L S' hS' (N := N))).symm
  rw [h1, h2, h3, Module.finrank_mul_finrank]

end Tower

section Quotient

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- **A surjection with kernel `I • M` is a base change to `S = R/I`**: for `R → S` onto with
kernel `I` and `f : M → N` onto with kernel `I • ⊤`, `N = S ⊗_R M`. -/
theorem isBaseChange_of_surjective (hS : Function.Surjective (algebraMap R S)) (f : M →ₗ[R] N)
    (hf : Function.Surjective f) (hker : LinearMap.ker f = (RingHom.ker (algebraMap R S)) • ⊤) :
    IsBaseChange S f := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ g
  have hle : LinearMap.ker f ≤ LinearMap.ker g := by
    rw [hker, Submodule.smul_le]
    intro r hr m _
    rw [LinearMap.mem_ker, map_smul, ← algebraMap_smul S r (g m), RingHom.mem_ker.1 hr, zero_smul]
  have key : ∀ m m', f m = f m' → g m = g m' := fun m m' hmm ↦ by
    have h0 : m - m' ∈ LinearMap.ker g := hle (by rw [LinearMap.mem_ker, map_sub, hmm, sub_self])
    rw [LinearMap.mem_ker] at h0
    calc g m = g (m' + (m - m')) := by rw [add_sub_cancel]
      _ = g m' := by rw [map_add, h0, add_zero]
  let h' : N →ₗ[S] Q :=
    { toFun := fun n ↦ g (hf n).choose
      map_add' := fun x y ↦ by
        rw [← map_add]
        exact key _ _ (by rw [(hf _).choose_spec, map_add, (hf x).choose_spec, (hf y).choose_spec])
      map_smul' := fun s n ↦ by
        obtain ⟨r, rfl⟩ := hS s
        rw [RingHom.id_apply, algebraMap_smul S r (g (hf n).choose), ← map_smul g r]
        exact key _ _ (by
          rw [(hf _).choose_spec, map_smul f r, (hf n).choose_spec, algebraMap_smul]) }
  have hh : ∀ m, h' (f m) = g m := fun m ↦ key _ _ (hf (f m)).choose_spec
  refine ⟨h', LinearMap.ext fun m ↦ hh m, fun g' hg' ↦ LinearMap.ext fun n ↦ ?_⟩
  obtain ⟨m, rfl⟩ := hf n
  exact (LinearMap.congr_fun hg' m).trans (hh m).symm

end Quotient

section Fibre

variable {P Pb M N : Type*} [CommRing P] [IsDomain P] [CommRing Pb] [IsDomain Pb] [Algebra P Pb]
  [AddCommGroup M] [Module P M] [Module.Finite P M] [Module.Flat P M]
  [AddCommGroup N] [Module P N] [Module Pb N] [IsScalarTower P Pb N]

/-- The rank of a finite flat module over a domain at any prime is its (generic) rank. -/
lemma rankAtStalk_eq_finrank (q : PrimeSpectrum P) : rankAtStalk M q = finrank P M := by
  haveI := q.isPrime
  rw [← Ideal.finrank_fiber_eq_rankAtStalk q.asIdeal, Ideal.finrank_fiber_eq_finrank]

/-- **The rank of a finite flat module is preserved by base change to a domain**:
`rank_{P̄} N = rank_P M` for `M → N` a base change along `P → P̄` (`P`, `P̄` domains). -/
theorem finrank_eq_of_isBaseChange {f : M →ₗ[P] N} (hf : IsBaseChange Pb f) :
    finrank Pb N = finrank P M := by
  let Kb := FractionRing Pb
  let g : N →ₗ[Pb] Kb ⊗[Pb] N := TensorProduct.mk Pb Kb N 1
  have hg : IsBaseChange Kb g := TensorProduct.isBaseChange Pb N Kb
  have hgf := hf.comp hg
  have h1 : finrank Kb (Kb ⊗[Pb] N) = finrank Pb N :=
    hg.finrank_eq (R := Pb) (T := Kb)
  have h2 := rankAtStalk_isBaseChange hgf (⊥ : PrimeSpectrum Kb)
  rw [rankAtStalk_eq_finrank_of_free, rankAtStalk_eq_finrank] at h2
  rw [← h1]
  exact h2

end Fibre

section Reduction

variable {P R B Pb Rb C : Type*} [CommRing P] [CommRing R] [CommRing B] [CommRing Pb] [CommRing Rb]
  [CommRing C] [IsDomain P] [IsDomain R] [IsDomain Pb] [IsDomain Rb]
  [Algebra P R] [Algebra R B] [Algebra P B] [IsScalarTower P R B]
  [Algebra Pb Rb] [Algebra Rb C] [Algebra Pb C] [IsScalarTower Pb Rb C] [Algebra P Pb]
  [Module.Finite P R] [Module.Finite Pb Rb] [Module.Finite P B] [Module.Flat P B]

/-- **The rank of a finite flat lift equals the rank of its reduction**: `B` an `R`-module, finite
flat over `P ⊆ R` (`R` finite over `P`), `C` an `R̄`-module (`R̄` finite over `P̄`) with
`[R : P] = [R̄ : P̄] ≠ 0`, and `g : B → C` onto, `P`-semilinear over `P ↠ P̄`, with kernel
`ker (P → P̄) • B`: then `rank_R B = rank_{R̄} C`. -/
theorem finrank_eq_of_reduction (hR : Function.Injective (algebraMap P R))
    (hRb : Function.Injective (algebraMap Pb Rb))
    (hd : finrank P R = finrank Pb Rb) (hd0 : finrank P R ≠ 0)
    (hS : Function.Surjective (algebraMap P Pb)) (g : B →+ C) (hg : Function.Surjective g)
    (hgs : ∀ (p : P) (b : B), g (p • b) = algebraMap P Pb p • g b)
    (hker : ∀ b, g b = 0 → b ∈ (RingHom.ker (algebraMap P Pb) • ⊤ : Submodule P B)) :
    finrank R B = finrank Rb C := by
  letI : Module P C := Module.compHom C (algebraMap P Pb)
  haveI : IsScalarTower P Pb C := ⟨fun x y z ↦ by
    change (x • y) • z = algebraMap P Pb x • y • z
    rw [Algebra.smul_def x y, mul_smul]⟩
  let f : B →ₗ[P] C := { toFun := g, map_add' := g.map_add, map_smul' := hgs }
  have hf : IsBaseChange Pb f := by
    refine isBaseChange_of_surjective hS f hg (le_antisymm (fun b hb ↦ hker b hb) ?_)
    rw [Submodule.smul_le]
    intro r hr b _
    rw [LinearMap.mem_ker]
    change g (r • b) = 0
    rw [hgs, RingHom.mem_ker.1 hr, zero_smul]
  have h1 := finrank_eq_of_isBaseChange hf
  rw [finrank_eq_mul P R B hR, finrank_eq_mul Pb Rb C hRb, hd] at h1
  rw [← hd] at h1
  exact (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hd0) h1).symm

end Reduction

end GenericRank

end SemistableReduction
