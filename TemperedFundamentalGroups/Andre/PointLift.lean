/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.FracGalois
import TemperedFundamentalGroups.Andre.GaloisClass

/-!
# Lifting geometric points along maps of finite étale algebras

For a map `φ : B₀ → B` of finite étale `R`-algebras with `B₀` a domain and `B ≠ 0`, every
geometric point `B₀ → Ω` (`Ω` algebraically closed) lifts to `B` (`exists_comp_eq_of_etale`),
since the split algebra `Ω ⊗_{B₀} B` has `rank ≥ 1` points.
-/

universe u

namespace TemperedFundamentalGroups

/-- **Lifting geometric points** along a map of finite étale algebras out of a domain. -/
theorem exists_comp_eq_of_etale {R B₀ B Ω : Type u} [CommRing R] [CommRing B₀] [CommRing B]
    [Algebra R B₀] [Algebra R B] [Algebra.Etale R B₀] [Module.Finite R B₀] [Algebra.Etale R B]
    [Module.Finite R B] [IsDomain B₀] [Nontrivial B] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (φ : B₀ →ₐ[R] B) (t₀ : B₀ →ₐ[R] Ω) : ∃ t : B →ₐ[R] Ω, t.comp φ = t₀ := by
  letI : Algebra B₀ B := φ.toRingHom.toAlgebra
  haveI : IsScalarTower R B₀ B := IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  haveI : Algebra.Etale B₀ B := Algebra.Etale.of_restrictScalars R B₀ B
  haveI : Module.Finite B₀ B := Module.Finite.of_restrictScalars_finite R B₀ B
  letI : Algebra B₀ Ω := t₀.toRingHom.toAlgebra
  haveI : IsScalarTower R B₀ Ω := IsScalarTower.of_algebraMap_eq fun r => (t₀.commutes r).symm
  obtain ⟨f, -⟩ := FracGalois.exists_injective_fin (B₀ := B₀) (B := B) (Ω := Ω)
  let g := f ⟨0, Module.finrank_pos⟩
  exact ⟨g.restrictScalars R, AlgHom.ext fun b => g.commutes b⟩


/-- **Extending automorphisms**: for a connected `B` on whose geometric fibre `Aut_R(B)` acts
transitively, every automorphism `σ₀` of `B₀` lifts along `φ : B₀ → B`. -/
theorem exists_aut_comp_eq {R B₀ B Ω : Type u} [CommRing R] [CommRing B₀] [CommRing B]
    [Algebra R B₀] [Algebra R B] [Algebra.Etale R B₀] [Module.Finite R B₀] [Algebra.Etale R B]
    [Module.Finite R B] [IsDomain B₀] [Nontrivial B] [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (hidem : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hgal : ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t')
    (t : B →ₐ[R] Ω) (φ : B₀ →ₐ[R] B) (σ₀ : B₀ →ₐ[R] B₀) :
    ∃ σ : B ≃ₐ[R] B, (σ : B →ₐ[R] B).comp φ = φ.comp σ₀ := by
  obtain ⟨t', ht'⟩ := exists_comp_eq_of_etale φ ((t.comp φ).comp σ₀)
  obtain ⟨σ, hσ⟩ := hgal t t'
  refine ⟨σ, algHom_eq_of_comp_eq hidem _ _ t ?_⟩
  rw [← AlgHom.comp_assoc, hσ, ht', AlgHom.comp_assoc]

end TemperedFundamentalGroups
