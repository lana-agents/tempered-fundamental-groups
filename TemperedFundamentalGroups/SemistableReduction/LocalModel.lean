/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Node

/-!
# Étale-local models of semistable curves (affine charts)

Blueprint §9.2 (ii), layer (a). Ring-theoretic (affine chart) formulation of "`𝒳` is a
semistable `O`-curve": every point has an étale neighbourhood which is also an étale
neighbourhood of a point of one of the standard local models

* the node `Node O (ϖ ^ n) = O[u, v] ⧸ (u v - ϖ ^ n)` (`n = 0` is allowed: then it is the smooth
  `O[u, u⁻¹]`), or
* the affine line `O[u]`.

Definitions:

* `IsEtaleLocallyAt O M 𝔭`: the `O`-algebra `A` at the prime `𝔭` is étale-locally isomorphic to
  the `O`-algebra `M`: there are a ring `C`, étale ring maps `g : A → C` and `f : M → C` agreeing
  on `O`, and a prime `𝔮` of `C` with `g⁻¹ 𝔮 = 𝔭` (a common étale neighbourhood).
* `IsSemistableAt ϖ 𝔭`: `A` is étale-locally at `𝔭` a node `Node O (ϖ ^ n)` or `O[X]`.
* `IsSemistable ϖ A`: `A` is semistable at every prime.

All rings (`O`, `A`, the models and the neighbourhoods `C`) live in one universe, as required by
Mathlib's `RingHom.StableUnderComposition`. A marked divisor (sections through the smooth locus)
is not yet part of the definition.

Results:

* `IsEtaleLocallyAt.refl`, `isSemistableAt_node`, `isSemistableAt_polynomial`: the models are
  semistable at every prime;
* `IsEtaleLocallyAt.of_etale_of_comap` (descent from an étale neighbourhood: if `A → A'` is étale
  and `A'` is étale-locally `M` at `𝔭'`, then `A` is étale-locally `M` at `𝔭' ∩ A`) and
  `IsEtaleLocallyAt.of_etale` (ascent along étale maps, via the base change `A' ⊗_A C`);
  similarly for `IsSemistableAt` and `IsSemistable`;
* `exists_isPrime_tensorProduct`: primes of `B` and `C` over the same prime of `A` come from a
  prime of `B ⊗_A C`.
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

/-- If `P ⊆ B` and `Q ⊆ C` are primes over the same prime of `A`, there is a prime of `B ⊗_A C`
lying over both (a point of the fibre product `Spec B ×_{Spec A} Spec C`). -/
theorem exists_isPrime_tensorProduct {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] (P : Ideal B) [P.IsPrime] (Q : Ideal C) [Q.IsPrime]
    (h : P.comap (algebraMap A B) = Q.comap (algebraMap A C)) :
    ∃ R : Ideal (B ⊗[A] C), R.IsPrime ∧
      R.comap (Algebra.TensorProduct.includeLeftRingHom) = P ∧
      R.comap (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom = Q := by
  set p := Q.comap (algebraMap A C)
  set fB : p.ResidueField →+* P.ResidueField :=
    Ideal.ResidueField.map p P (algebraMap A B) h.symm with hfB
  set fC : p.ResidueField →+* Q.ResidueField :=
    Ideal.ResidueField.map p Q (algebraMap A C) rfl with hfC
  letI := fB.toAlgebra
  letI := fC.toAlgebra
  have e₁ (a : A) : algebraMap A P.ResidueField a =
      algebraMap p.ResidueField P.ResidueField (algebraMap A p.ResidueField a) := by
    rw [RingHom.algebraMap_toAlgebra, hfB, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  have e₂ (a : A) : algebraMap A Q.ResidueField a =
      algebraMap p.ResidueField Q.ResidueField (algebraMap A p.ResidueField a) := by
    rw [RingHom.algebraMap_toAlgebra, hfC, Ideal.ResidueField.map_algebraMap,
      ← IsScalarTower.algebraMap_apply]
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (P.ResidueField ⊗[p.ResidueField] Q.ResidueField)
  let gB : B →ₐ[A] P.ResidueField ⊗[p.ResidueField] Q.ResidueField :=
    { toRingHom := Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap B P.ResidueField)
      commutes' := fun a ↦ by
        rw [Algebra.TensorProduct.algebraMap_apply, IsScalarTower.algebraMap_apply A B]
        rfl }
  let gC : C →ₐ[A] P.ResidueField ⊗[p.ResidueField] Q.ResidueField :=
    { toRingHom := (Algebra.TensorProduct.includeRight.toRingHom).comp
        (algebraMap C Q.ResidueField)
      commutes' := fun a ↦ by
        rw [Algebra.TensorProduct.algebraMap_apply, e₁, Algebra.TensorProduct.tmul_one_eq_one_tmul,
          ← e₂, IsScalarTower.algebraMap_apply A C]
        rfl }
  let Φ := Algebra.TensorProduct.lift gB gC fun _ _ ↦ Commute.all _ _
  have hbotB : M.comap (Algebra.TensorProduct.includeLeftRingHom :
      P.ResidueField →+* P.ResidueField ⊗[p.ResidueField] Q.ResidueField) = ⊥ :=
    Ideal.eq_bot_of_prime _
  have hbotC : M.comap (Algebra.TensorProduct.includeRight :
      Q.ResidueField →ₐ[p.ResidueField] P.ResidueField ⊗[p.ResidueField] Q.ResidueField).toRingHom
      = ⊥ :=
    Ideal.eq_bot_of_prime _
  refine ⟨M.comap Φ.toRingHom, Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have : Φ.toRingHom.comp Algebra.TensorProduct.includeLeftRingHom =
        Algebra.TensorProduct.includeLeftRingHom.comp (algebraMap B P.ResidueField) := by
      ext b
      simp [Φ, gB, gC]
    rw [Ideal.comap_comap, this, ← Ideal.comap_comap, hbotB, ← RingHom.ker_eq_comap_bot,
      Ideal.ker_algebraMap_residueField]
  · have : Φ.toRingHom.comp (Algebra.TensorProduct.includeRight : C →ₐ[A] B ⊗[A] C).toRingHom =
        (Algebra.TensorProduct.includeRight.toRingHom).comp (algebraMap C Q.ResidueField) := by
      ext c
      simp [Φ, gB, gC]
    rw [Ideal.comap_comap, this, ← Ideal.comap_comap, hbotC, ← RingHom.ker_eq_comap_bot,
      Ideal.ker_algebraMap_residueField]

variable (O : Type u) [CommRing O]

/-- The `O`-algebra `A` is **étale-locally isomorphic to the `O`-algebra `M` at the prime `𝔭`**:
there are a ring `C`, étale ring maps `g : A → C` and `f : M → C` agreeing on `O`, and a prime
`𝔮` of `C` with `g⁻¹ 𝔮 = 𝔭` (`Spec C` is a common étale neighbourhood of `𝔭 ∈ Spec A` and of a
point of `Spec M`). -/
def IsEtaleLocallyAt (M : Type u) [CommRing M] [Algebra O M] {A : Type u} [CommRing A]
    [Algebra O A] (𝔭 : Ideal A) : Prop :=
  ∃ (C : Type u) (_ : CommRing C) (g : A →+* C) (f : M →+* C) (𝔮 : Ideal C),
    g.Etale ∧ f.Etale ∧ 𝔮.IsPrime ∧ 𝔮.comap g = 𝔭 ∧
      f.comp (algebraMap O M) = g.comp (algebraMap O A)

variable {O}

/-- The `O`-algebra `A` is **semistable at `𝔭`** (with respect to the uniformizer `ϖ`): it is
étale-locally at `𝔭` a node `O[u, v] ⧸ (u v - ϖ ^ n)` or the affine line `O[u]`. -/
def IsSemistableAt (ϖ : O) {A : Type u} [CommRing A] [Algebra O A] (𝔭 : Ideal A) : Prop :=
  (∃ n : ℕ, IsEtaleLocallyAt O (Node O (ϖ ^ n)) 𝔭) ∨ IsEtaleLocallyAt O O[X] 𝔭

/-- The `O`-algebra `A` is **semistable** (an affine chart of a semistable `O`-curve): it is
semistable at every prime. -/
def IsSemistable (ϖ : O) (A : Type u) [CommRing A] [Algebra O A] : Prop :=
  ∀ 𝔭 : Ideal A, 𝔭.IsPrime → IsSemistableAt ϖ 𝔭

namespace IsEtaleLocallyAt

variable {M : Type u} [CommRing M] [Algebra O M]

/-- `M` is étale-locally `M` at every prime. -/
theorem refl (𝔭 : Ideal M) [𝔭.IsPrime] : IsEtaleLocallyAt O M 𝔭 :=
  ⟨M, inferInstance, RingHom.id M, RingHom.id M, 𝔭, .of_bijective Function.bijective_id,
    .of_bijective Function.bijective_id, inferInstance, Ideal.comap_id 𝔭, rfl⟩

variable {A A' : Type u} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

/-- **Descent from an étale neighbourhood.** If `φ : A → A'` is étale and `A'` is étale-locally
`M` at `𝔭'`, then `A` is étale-locally `M` at `φ⁻¹ 𝔭'`. -/
theorem of_etale_of_comap (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) {𝔭' : Ideal A'}
    (h : IsEtaleLocallyAt O M 𝔭') : IsEtaleLocallyAt O M (𝔭'.comap φ.toRingHom) := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp⟩ := h
  refine ⟨C, inferInstance, g.comp φ.toRingHom, f, 𝔮,
    RingHom.Etale.stableUnderComposition _ _ hφ hg,
    hf, h𝔮, by rw [← Ideal.comap_comap, hcomap], ?_⟩
  rw [hcomp, RingHom.comp_assoc]
  exact congrArg g.comp (AlgHom.comp_algebraMap φ).symm

/-- **Ascent along étale maps.** If `φ : A → A'` is étale, `𝔭'` is a prime of `A'` and `A` is
étale-locally `M` at `φ⁻¹ 𝔭'`, then `A'` is étale-locally `M` at `𝔭'` (the étale neighbourhood
is the base change `A' ⊗_A C`). -/
theorem of_etale (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) (𝔭' : Ideal A') [𝔭'.IsPrime]
    (h : IsEtaleLocallyAt O M (𝔭'.comap φ.toRingHom)) : IsEtaleLocallyAt O M 𝔭' := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp⟩ := h
  letI : Algebra A A' := φ.toRingHom.toAlgebra
  letI : Algebra A C := g.toAlgebra
  have hA' : Algebra.Etale A A' := hφ
  have hC : Algebra.Etale A C := hg
  obtain ⟨R, hR, hR₁, hR₂⟩ := exists_isPrime_tensorProduct (A := A) 𝔭' 𝔮 hcomap.symm
  -- `A' → A' ⊗_A C` is étale (base change of `A → C`)
  have hl : (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] C).Etale :=
    RingHom.Etale.isStableUnderBaseChange.tensorProduct A' hg
  -- `C → A' ⊗_A C` is étale (base change of `A → A'`, composed with the swap)
  have hr : (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom.Etale := by
    have h₁ : (Algebra.TensorProduct.includeLeftRingHom : C →+* C ⊗[A] A').Etale :=
      RingHom.Etale.isStableUnderBaseChange.tensorProduct C hφ
    have e : (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom =
        (Algebra.TensorProduct.comm A C A').toRingHom.comp
          Algebra.TensorProduct.includeLeftRingHom := by
      ext c
      simp
    rw [e]
    exact RingHom.Etale.stableUnderComposition _ _ h₁
      (RingHom.Etale.of_bijective (Algebra.TensorProduct.comm A C A').bijective)
  refine ⟨A' ⊗[A] C, inferInstance, Algebra.TensorProduct.includeLeftRingHom,
    (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom.comp f, R, hl,
    RingHom.Etale.stableUnderComposition f
      (Algebra.TensorProduct.includeRight : C →ₐ[A] A' ⊗[A] C).toRingHom hf hr, hR, hR₁, ?_⟩
  rw [RingHom.comp_assoc, hcomp, ← RingHom.comp_assoc]
  ext o
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  change 1 ⊗ₜ[A] (algebraMap A C (algebraMap O A o)) = _
  rw [← AlgHom.commutes φ o]
  exact (Algebra.TensorProduct.tmul_one_eq_one_tmul (algebraMap O A o)).symm

end IsEtaleLocallyAt

namespace IsSemistableAt

variable {ϖ : O}

/-- The node `O[u, v] ⧸ (u v - ϖ ^ n)` is semistable at every prime. -/
theorem node (n : ℕ) (𝔭 : Ideal (Node O (ϖ ^ n))) [𝔭.IsPrime] : IsSemistableAt ϖ 𝔭 :=
  .inl ⟨n, .refl 𝔭⟩

/-- The affine line `O[u]` is semistable at every prime. -/
theorem polynomial (𝔭 : Ideal O[X]) [𝔭.IsPrime] : IsSemistableAt ϖ 𝔭 :=
  .inr (.refl 𝔭)

variable {A A' : Type u} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

/-- Semistability descends from étale neighbourhoods. -/
theorem of_etale_of_comap (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) {𝔭' : Ideal A'}
    (h : IsSemistableAt ϖ 𝔭') : IsSemistableAt ϖ (𝔭'.comap φ.toRingHom) := by
  rcases h with ⟨n, h⟩ | h
  · exact .inl ⟨n, h.of_etale_of_comap φ hφ⟩
  · exact .inr (h.of_etale_of_comap φ hφ)

/-- Semistability ascends along étale maps. -/
theorem of_etale (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) (𝔭' : Ideal A') [𝔭'.IsPrime]
    (h : IsSemistableAt ϖ (𝔭'.comap φ.toRingHom)) : IsSemistableAt ϖ 𝔭' := by
  rcases h with ⟨n, h⟩ | h
  · exact .inl ⟨n, .of_etale φ hφ 𝔭' h⟩
  · exact .inr (.of_etale φ hφ 𝔭' h)

end IsSemistableAt

namespace IsSemistable

variable {ϖ : O}

/-- The node `O[u, v] ⧸ (u v - ϖ ^ n)` is semistable. -/
theorem node (n : ℕ) : IsSemistable ϖ (Node O (ϖ ^ n)) := fun 𝔭 _ ↦ .node n 𝔭

/-- The affine line `O[u]` is semistable. -/
theorem polynomial : IsSemistable ϖ O[X] := fun 𝔭 _ ↦ .polynomial 𝔭

variable {A A' : Type u} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

/-- An étale `A`-algebra of a semistable `A` is semistable. -/
theorem of_etale (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) (h : IsSemistable ϖ A) :
    IsSemistable ϖ A' := fun 𝔭' _ ↦ .of_etale φ hφ 𝔭' (h _ inferInstance)

end IsSemistable

end SemistableReduction
