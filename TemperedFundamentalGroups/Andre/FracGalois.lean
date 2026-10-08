/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.FracMap
import TemperedFundamentalGroups.Andre.GaloisClass

/-!
# Fraction fields of Galois levels (Blueprint §10.3.8, I4)

Let `B₀ → B` be a map `φ` of finite étale `R`-algebras which are domains, with fraction fields
`F₀` and `L` (`L / F₀` through `fracMap`). Suppose `B` is connected and `Aut_R(B)` acts
transitively on the geometric fibre `B →ₐ[R] Ω` over an algebraically closed field `Ω`. Then
(`FracGalois.isGalois_and_surjective`):

* `L / F₀` is Galois, and
* every `τ ∈ Gal(L / F₀)` is induced by an `R`-algebra automorphism `σ` of `B` fixing `B₀`
  (`σ ∘ φ = φ`).

Proof (counting): `B` is finite étale over `B₀` of rank `m = [L : F₀]` (`L` is the localization
of `B` at the nonzero elements of `B₀`). Over the point `t₀ ∘ φ` of `B₀`, the split algebra
`Ω ⊗_{B₀} B ≅ Ω^m` has `m` distinct points `B →ₐ[B₀] Ω`; each is `t₀ ∘ σ` for some `σ`, and `σ`
fixes `B₀` by rigidity (`algHom_eq_of_comp_eq`). So `Aut_{B₀}(B)` has at least `m` elements and
injects into `Gal(L / F₀)`, which has at most `m` elements.
-/

universe u

open nonZeroDivisors TensorProduct

namespace TemperedFundamentalGroups

noncomputable section

namespace FracGalois

section Count

variable {B₀ B : Type u} [CommRing B₀] [CommRing B] [Algebra B₀ B] [Algebra.Etale B₀ B]
  [Module.Finite B₀ B] [IsDomain B₀] {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra B₀ Ω]

/-- **A finite étale algebra over a domain has at least `rank` geometric points** over every
geometric point of the base. -/
theorem exists_injective_fin :
    ∃ f : Fin (Module.finrank B₀ B) → (B →ₐ[B₀] Ω), Function.Injective f := by
  let T := Ω ⊗[B₀] B
  obtain ⟨n, ⟨e⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun Ω T
  have hn : n = Module.finrank B₀ B := by
    have h1 : Module.finrank Ω T = n := by
      rw [e.toLinearEquiv.finrank_eq, Module.finrank_fin_fun]
    let p : PrimeSpectrum Ω := ⟨⊥, Ideal.isPrime_bot⟩
    have h2 := Module.rankAtStalk_baseChange (R := B₀) (M := B) (S := Ω) p
    rw [Module.rankAtStalk_eq_finrank_of_free] at h2
    rw [← h1]
    refine h2.trans ?_
    set q := p.comap (algebraMap B₀ Ω)
    rw [← Ideal.finrank_fiber_eq_rankAtStalk q.asIdeal, Ideal.finrank_fiber_eq_finrank]
  subst hn
  let f : Fin (Module.finrank B₀ B) → (B →ₐ[B₀] Ω) := fun i =>
    (((Pi.evalAlgHom Ω (fun _ => Ω) i).comp e.toAlgHom).restrictScalars B₀).comp
      Algebra.TensorProduct.includeRight
  refine ⟨f, fun i j hij => ?_⟩
  have hT : (Pi.evalAlgHom Ω (fun _ => Ω) i).comp e.toAlgHom =
      (Pi.evalAlgHom Ω (fun _ => Ω) j).comp e.toAlgHom := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    exact hij
  have h := congrArg (fun g => g (e.symm (Pi.single i 1))) hT
  have h' : (Pi.single i (1 : Ω) : Fin _ → Ω) i = (Pi.single i (1 : Ω) : Fin _ → Ω) j := by
    simpa using h
  by_contra hne
  rw [Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at h'
  exact one_ne_zero h'

end Count

section Galois

variable {R B₀ B : Type u} [CommRing R] [CommRing B₀] [CommRing B] [Algebra R B₀] [Algebra R B]
  [Algebra.Etale R B₀] [Module.Finite R B₀] [Algebra.Etale R B] [Module.Finite R B]
  [IsDomain B₀] [IsDomain B]
  (F₀ L : Type u) [Field F₀] [Field L] [Algebra B₀ F₀] [IsFractionRing B₀ F₀]
  [Algebra B L] [IsFractionRing B L]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]

/-- **Galois property of the fraction fields** of a level map into a connected level whose
automorphisms act transitively on a geometric fibre: `L / F₀` is Galois and every element of its
Galois group comes from an `R`-algebra automorphism of `B` fixing `B₀`. -/
theorem isGalois_and_exists (φ : B₀ →ₐ[R] B) (t₀ : B →ₐ[R] Ω)
    (hgal : ∀ t : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t₀.comp (σ : B →ₐ[R] B) = t)
    (hidem : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) :
    letI := (fracMap F₀ L φ).toAlgebra
    IsGalois F₀ L ∧ ∀ τ : L ≃ₐ[F₀] L, ∃ σ : B ≃ₐ[R] B, (σ : B →ₐ[R] B).comp φ = φ ∧
      ∀ b, τ (algebraMap B L b) = algebraMap B L (σ b) := by
  letI : Algebra F₀ L := (fracMap F₀ L φ).toAlgebra
  letI : Algebra B₀ B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R B₀ B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : Algebra.Etale B₀ B := Algebra.Etale.of_restrictScalars R B₀ B
  haveI : Module.Finite B₀ B := Module.Finite.of_restrictScalars_finite R B₀ B
  letI : Algebra B₀ L := ((algebraMap B L).comp (algebraMap B₀ B)).toAlgebra
  haveI : IsScalarTower B₀ B L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower B₀ F₀ L :=
    IsScalarTower.of_algebraMap_eq fun b => (fracMap_algebraMap φ b).symm
  haveI : FiniteDimensional F₀ L := finiteDimensional_fracMap F₀ L φ
  have hφinj : Function.Injective φ := injective_of_flat_finite φ
  haveI : FaithfulSMul B₀ B := (faithfulSMul_iff_algebraMap_injective B₀ B).2 hφinj
  have hrank : Module.finrank F₀ L = Module.finrank B₀ B := by
    have h1 : Module.finrank B₀ L = Module.finrank B₀ B :=
      IsLocalizedModule.finrank_eq (p := B₀⁰)
        (f := (IsScalarTower.toAlgHom B₀ B L).toLinearMap) le_rfl
    have h2 : Module.rank F₀ L = Module.rank B₀ L := IsLocalization.rank_eq F₀ B₀⁰ le_rfl
    rw [← h1, Module.finrank, Module.finrank, h2]
  letI : Algebra B₀ Ω := (t₀.comp φ).toRingHom.toAlgebra
  haveI : IsScalarTower R B₀ Ω := IsScalarTower.of_algebraMap_eq fun r => by
    change _ = t₀ (φ (algebraMap R B₀ r))
    rw [φ.commutes, t₀.commutes]
  obtain ⟨f, hf⟩ := exists_injective_fin (B₀ := B₀) (B := B) (Ω := Ω)
  have hlift : ∀ g : B →ₐ[B₀] Ω, ∃ σ : B ≃ₐ[B₀] B,
      t₀.comp ((σ : B →ₐ[B₀] B).restrictScalars R) = g.restrictScalars R := by
    intro g
    obtain ⟨σ, hσ⟩ := hgal (g.restrictScalars R)
    have hσφ : (σ : B →ₐ[R] B).comp φ = φ := by
      refine algHom_eq_of_comp_eq hidem _ _ t₀ ?_
      ext b
      have := congrArg (fun t => t (φ b)) hσ
      simp only [AlgHom.comp_apply] at this ⊢
      rw [this]
      exact g.commutes b
    refine ⟨{ σ with commutes' := fun b => congrArg (fun h => h b) hσφ }, ?_⟩
    ext b
    exact congrArg (fun t => t b) hσ
  choose σf hσf using fun i => hlift (f i)
  have hσinj : Function.Injective σf := fun i j h => hf (by
    have h' := (hσf i).symm.trans (h ▸ hσf j)
    ext b
    exact congrArg (fun t => t b) h')
  have hι := IsFractionRing.fieldEquivOfAlgEquivHom_injective B₀ B F₀ L
  haveI : Finite (B ≃ₐ[B₀] B) := Finite.of_injective _ hι
  have hcardGal : Nat.card (L ≃ₐ[F₀] L) ≤ Module.finrank B₀ B := by
    rw [← hrank]
    exact (Nat.card_le_card_of_injective _ AlgEquiv.coe_toAlgHom_injective).trans
      (card_algHom_le_finrank F₀ L L)
  have hcardH : Module.finrank B₀ B ≤ Nat.card (B ≃ₐ[B₀] B) := by
    simpa using Nat.card_le_card_of_injective σf hσinj
  have hbij := hι.bijective_of_nat_card_le (hcardGal.trans hcardH)
  refine ⟨IsGalois.of_card_aut_eq_finrank (F := F₀) (E := L) ?_, fun τ => ?_⟩
  · rw [hrank]
    exact le_antisymm hcardGal (hcardH.trans (Nat.card_le_card_of_injective _ hι))
  · obtain ⟨σ', rfl⟩ := hbij.2 τ
    refine ⟨σ'.restrictScalars R, ?_, fun b => ?_⟩
    · ext b
      exact σ'.commutes b
    · exact IsFractionRing.fieldEquivOfAlgEquiv_algebraMap F₀ L L σ' b

end Galois

end FracGalois

end

end TemperedFundamentalGroups
