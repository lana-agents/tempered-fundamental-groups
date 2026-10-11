/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGaloisLevel
import TemperedFundamentalGroups.Andre.Refinement

/-!
# Domination by orbifold Galois objects: the core (Blueprint §11.3, G6, orbifold case)

`dom_coreO`: given a scheme level `Lv₁` satisfying the conditions of `galClassO` and finitely
many pointed objects `(X_k, x_k)` of `[Spec R / A]` with algebra maps `m_k : B_k → B₁` through
the base point and model maps `dom_k : 𝒯₁ → 𝒯_k`, the object `Ind_1^S Z̃` for the fibre product
`S = A ×_A Π_k H_k` (`fibProd`, mapping to every `H_k` over `A`) dominates all `(X_k, x_k)`:
the level maps are `OrbGal.indℓ`, the covering maps are lifts (`exists_hom_preMap`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

section FibProd

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]
  {n : ℕ} (L : Fin n → FiniteLevel R A)

/-- **The fibre product `A ×_A Π_k H_k`** of the level groups over `A`. -/
def fibProd : Subgroup (A × Π k, (L k).H) where
  carrier := {p | ∀ k, ((p.2 k : (L k).H) : SemilinearAut R A (L k).B).a = p.1}
  mul_mem' {p q} hp hq k := by
    change ((p.2 k * q.2 k : (L k).H) : SemilinearAut R A (L k).B).a = p.1 * q.1
    rw [Subgroup.coe_mul, SemilinearAut.mul_a, hp k, hq k]
  one_mem' k := rfl
  inv_mem' {p} hp k := by
    change (((p.2 k)⁻¹ : (L k).H) : SemilinearAut R A (L k).B).a = p.1⁻¹
    rw [Subgroup.coe_inv, SemilinearAut.inv_a, hp k]

/-- The map to `A`. -/
def fibα : fibProd L →* A := (MonoidHom.fst _ _).comp (fibProd L).subtype

lemma fibα_surjective : Function.Surjective (fibα L) := fun a => by
  choose h hh ha using fun k => (L k).surjective a
  exact ⟨⟨(a, fun k => ⟨h k, hh k⟩), fun k => ha k⟩, rfl⟩

/-- The map to `H_k`. -/
def fibθ (k : Fin n) : fibProd L →* (L k).H :=
  (Pi.evalMonoidHom _ k).comp ((MonoidHom.snd _ _).comp (fibProd L).subtype)

lemma fibθ_a (k : Fin n) (s : fibProd L) :
    ((fibθ L k s : (L k).H) : SemilinearAut R A (L k).B).a = fibα L s := s.2 k

instance [IsNoetherianRing R] [Finite A] : Finite (fibProd L) := by
  haveI : ∀ k, Finite (L k).H := fun k => (L k).finite_H
  exact Subtype.finite

end FibProd

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R] [IsNoetherianRing R] [Finite A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (A₁ : Type u) [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

open OrbGal in
/-- **The core of domination** by orbifold Galois objects. -/
theorem dom_coreO {n : ℕ} (P : Fin n → Σ X : TempObj O R A, (tempFibre O R A V hV).obj X)
    (Lv₁ : Level O R A₁) [Subsingleton Lv₁.L.H] [TopologicalSpace.NoetherianSpace Lv₁.Z]
    [T0Space Lv₁.Z] [QuasiSober Lv₁.Z] [ConnectedSpace Lv₁.Z]
    (hdim : topologicalKrullDim Lv₁.Z ≤ 1) (z₀ : Lv₁.Z)
    (hgal : ∀ t t' : Lv₁.L.B →ₐ[R] Ω, ∃ σ : Lv₁.L.B ≃ₐ[R] Lv₁.L.B,
      t.comp (σ : Lv₁.L.B →ₐ[R] Lv₁.L.B) = t')
    (hidem : ∀ e : Lv₁.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hsym : ∀ a : A, ∃ γ : SemilinearAut R A Lv₁.L.B, γ.a = a)
    (hact : ∀ γ : SemilinearAut R A Lv₁.L.B, ∃ ψ : Lv₁.c.scheme ⟶ Lv₁.c.scheme,
      ψ ≫ Lv₁.c.toSpec = Lv₁.c.toSpec ∧
      Lv₁.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : Lv₁.L.B →+* Lv₁.L.B)) ≫ Lv₁.j)
    (hss : IsSemistableLevel Lv₁) [hdom : IsSchemeTheoreticallyDominant Lv₁.j]
    (t₀ : Lv₁.L.B →ₐ[R] Ω)
    (m : ∀ k, (P k).1.Lv.L.B →ₐ[R] Lv₁.L.B)
    (hm : ∀ k, t₀.comp (m k) = (Quotient.out (P k).2 : PreFibre Ω V hV (P k).1).1.1)
    (dom : ∀ k, Lv₁.c.scheme ⟶ (P k).1.Lv.c.scheme)
    (hdS : ∀ k, dom k ≫ (P k).1.Lv.c.toSpec = Lv₁.c.toSpec)
    (hdj : ∀ k, Lv₁.j ≫ dom k =
      Spec.map (CommRingCat.ofHom (m k : (P k).1.Lv.L.B →+* Lv₁.L.B)) ≫ (P k).1.Lv.j) :
    ∃ G, galClassO O R A Ω A₁ G ∧ Nonempty ((tempFibre O R A V hV).obj G) ∧
      ∀ k, ∃ (f : G ⟶ (P k).1) (u : (tempFibre O R A V hV).obj G),
        (tempFibre O R A V hV).map f u = (P k).2 := by
  classical
  let L : Fin n → FiniteLevel R A := fun k => (P k).1.Lv.L
  let X₁ : TempObj O R A₁ := universalObj Lv₁ hdim z₀
  haveI : Nontrivial Lv₁.L.B := t₀.domain_nontrivial
  haveI : Nontrivial X₁.Lv.L.B := ‹Nontrivial Lv₁.L.B›
  haveI : Subsingleton X₁.Lv.L.H := ‹Subsingleton Lv₁.L.H›
  haveI : IsSchemeTheoreticallyDominant X₁.Lv.j := hdom
  haveI : Fintype (fibProd L) := Fintype.ofFinite _
  let D : IndData (μ₁ A A₁) X₁ := data X₁ (fibProd L) (fibα L) (fibα_surjective L)
  have hX : IndFaithful X₁ := indFaithful
  let hp := universalCovering.isUniversalCovering.{u, u, u} hdim z₀
  let hc := hp.countable_fibre
  haveI := hp.connectedSpace
  obtain ⟨e₀, he₀⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv₁.sp V hV t₀)
  let q₀ := basePre D hX hp hc V hV t₀ e₀ he₀
  refine ⟨OrbGal.obj D hX hp hc, ⟨Lv₁, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, hdim, z₀, D, hX, ⟨t₀⟩, hgal, hidem, hsym, hact, hss, hdom,
    ⟨Iso.refl _⟩⟩, ⟨Quotient.mk _ q₀⟩, fun k => ?_⟩
  obtain ⟨f, -, hf⟩ := exists_hom_preMap V hV (Lv := D.lv hX)
    (hp := isUniversalCovering_proj D hX hp) (hc := countable_proj D hX hc)
    (indℓ D hX (m k) (fibθ L k) (fibθ_a L k) (hdS k) (hdj k))
    (indℓ_isEquivariant D hX (m k) (fibθ L k) (fibθ_a L k) (hdS k) (hdj k)) q₀ e₀ rfl
    (Quotient.out (P k).2) (by
      refine AlgHom.ext fun b => ?_
      change t₀ (D.ev 1 (indF D (m k) (fibθ L k) (fibθ_a L k) b)) = _
      rw [ev₁_indF, ← hm k]
      rfl)
  refine ⟨f, Quotient.mk _ q₀, ?_⟩
  change Quotient.mk _ (preMap V hV f q₀) = (P k).2
  rw [hf]
  exact Quotient.out_eq _

end

end TemperedFundamentalGroups
