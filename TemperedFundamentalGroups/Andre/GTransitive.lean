/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.GTransitiveAux
import TemperedFundamentalGroups.SemistableReduction.GaloisReduction

/-!
# G-transitivity (Blueprint §10.3.8, I4)

Let `Lv` be a level whose ring `B` is a connected domain, with `Aut_R(B)` acting transitively on
the geometric fibre `B →ₐ[R] Ω` (`Ω` algebraically closed), every `σ ∈ Aut_R(B)` extending to a
model endomorphism `ψσ` over `O` (`j ≫ ψσ = Spec σ ≫ j`), and `j` scheme-theoretically dominant.
Let `Lv₀` be a second level, with a level map `φ : B₀ → B` (`B₀` a domain) and a model map
`ψ : 𝒯 ⟶ 𝒯₀` over `O` with `j ≫ ψ = Spec φ ≫ j₀` (the shape of a morphism of tempered
coverings). Assume the special fibre `Z₀` of `𝒯₀` is a noetherian `T₀` quasi-sober space of
dimension `≤ 1` and that **at the generic point of every irreducible component of `Z₀` the
centre determines the valuation** of `F₀ = Frac B₀` (`ValuativeCentre.CentreDetermines`; true if
the local ring there is a valuation ring of `F₀`, e.g. a DVR with fraction field `F₀`).

**`exists_aut_image_eq`**: if `v, v'` are irreducible components of the special fibre `Z` of `𝒯`,
`v` not contracted by `ψ`, with the same image in `Z₀`, then some `σ ∈ Aut_R(B)` with `σ ∘ φ = φ`
has a model endomorphism `ψσ` mapping `v` onto `v'`.

Proof (valuations). Let `η, η'` be the generic points of `v, v'`; they are centres of valuation
subrings `W, W'` of `L = Frac B` (`exists_isCentre`, `j` dominant). Their restrictions to `F₀`
have centre `ψ η = ψ η'`, the generic point of the component `ψ(v)` (`isCentre_comap`), hence
coincide. `L / F₀` is Galois with group `Aut_{B₀}(B)` (`FracGalois.isGalois_and_exists`), so
`τ W' = W` for some `τ` (`GaloisReduction.exists_smul_eq`), induced by `σ`. Then `ψσ η` is the
centre of `τ⁻¹ W = W'`, i.e. `ψσ η = η'` (`centre_unique`), and `ψσ(v) = closure {ψσ η} = v'`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Set Topology TopologicalSpace
open scoped Pointwise

namespace TemperedFundamentalGroups

open ValuativeCentre

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- **G-transitivity** (Blueprint §10.3.8, I4): components of the special fibre of a Galois
level with the same (non-contracted) image under a model map `ψ` over a level map `φ : B₀ → B`
are conjugate under the model action of `Aut_{B₀}(B) = {σ ∈ Aut_R(B) | σ ∘ φ = φ}`. -/
theorem exists_aut_image_eq {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω]
    (Lv Lv₀ : Level O R A) [IsDomain Lv.L.B] [IsDomain Lv₀.L.B]
    [IsSchemeTheoreticallyDominant Lv.j] (t₀ : Lv.L.B →ₐ[R] Ω)
    (hgal : ∀ t : Lv.L.B →ₐ[R] Ω, ∃ σ : Lv.L.B ≃ₐ[R] Lv.L.B,
      t₀.comp (σ : Lv.L.B →ₐ[R] Lv.L.B) = t)
    (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hact : ∀ σ : Lv.L.B ≃ₐ[R] Lv.L.B, ∃ ψ : Lv.c.scheme ⟶ Lv.c.scheme,
      ψ ≫ Lv.c.toSpec = Lv.c.toSpec ∧
      Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j)
    (F₀ : Type u) [Field F₀] [Algebra Lv₀.L.B F₀] [IsFractionRing Lv₀.L.B F₀]
    (L : Type u) [Field L] [Algebra Lv.L.B L] [IsFractionRing Lv.L.B L]
    [NoetherianSpace Lv₀.Z] [T0Space Lv₀.Z] [QuasiSober Lv₀.Z]
    (hdim₀ : topologicalKrullDim Lv₀.Z ≤ 1)
    (hval₀ : ∀ ζ : Lv₀.Z, closure {ζ} ∈ irreducibleComponents Lv₀.Z →
      CentreDetermines (Lv₀.gen F₀) (ζ : Lv₀.c.scheme))
    (φ : Lv₀.L.B →ₐ[R] Lv.L.B) (ψ : Lv.c.scheme ⟶ Lv₀.c.scheme)
    (hψ : ψ ≫ Lv₀.c.toSpec = Lv.c.toSpec)
    (hjψ : Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (φ : Lv₀.L.B →+* Lv.L.B)) ≫ Lv₀.j)
    [QuasiSober Lv.Z] {v v' : Set Lv.Z} (hv : v ∈ irreducibleComponents Lv.Z)
    (hv' : v' ∈ irreducibleComponents Lv.Z)
    (hc : ¬ ∃ y, specialFibreMap ψ hψ '' v = {y})
    (heq : specialFibreMap ψ hψ '' v = specialFibreMap ψ hψ '' v') :
    ∃ σ : Lv.L.B ≃ₐ[R] Lv.L.B, (σ : Lv.L.B →ₐ[R] Lv.L.B).comp φ = φ ∧
      ∃ (ψσ : Lv.c.scheme ⟶ Lv.c.scheme) (hψσ : ψσ ≫ Lv.c.toSpec = Lv.c.toSpec),
        Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j ∧
        specialFibreMap ψσ hψσ '' v = v' := by
  haveI := Lv.L.etale
  haveI := Lv.L.finite
  haveI := Lv₀.L.etale
  haveI := Lv₀.L.finite
  haveI : FaithfulSMul Lv.L.B L :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective Lv.L.B L)
  letI : Algebra F₀ L := (fracMap F₀ L φ).toAlgebra
  obtain ⟨hGal, hτ⟩ := FracGalois.isGalois_and_exists F₀ L φ t₀ hgal hidem
  haveI : FiniteDimensional F₀ L := finiteDimensional_fracMap F₀ L φ
  -- generic points
  have hη : closure {hv.1.genericPoint} = v :=
    hv.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents v hv)
  have hη' : closure {hv'.1.genericPoint} = v' :=
    hv'.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents v' hv')
  set η := hv.1.genericPoint
  set η' := hv'.1.genericPoint
  have hcont := continuous_specialFibreMap ψ hψ
  have hclosed := isClosedMap_specialFibreMap' ψ hψ
  have hζ : specialFibreMap ψ hψ η = specialFibreMap ψ hψ η' := by
    rw [image_eq_closure hcont hclosed hη, image_eq_closure hcont hclosed hη'] at heq
    exact (inseparable_iff_closure_eq.2 heq).eq
  have hcomp : closure {specialFibreMap ψ hψ η} ∈ irreducibleComponents Lv₀.Z := by
    rw [← image_eq_closure hcont hclosed hη]
    exact image_mem_irreducibleComponents hdim₀ hcont hclosed hη hc
  have hdet := hval₀ _ hcomp
  -- the valuations with centres `η`, `η'`
  obtain ⟨W, hW⟩ := exists_isCentre (Lv.gen L) (Lv.gen_specializes L (η : Lv.c.scheme))
  obtain ⟨W', hW'⟩ := exists_isCentre (Lv.gen L) (Lv.gen_specializes L (η' : Lv.c.scheme))
  have hW₀ := Level.isCentre_comap Lv Lv₀ φ (fracMap F₀ L φ) (fracMap_algebraMap φ) ψ hjψ hW
  have hW₀' := Level.isCentre_comap Lv Lv₀ φ (fracMap F₀ L φ) (fracMap_algebraMap φ) ψ hjψ hW'
  have hcomap : W'.comap (algebraMap F₀ L) = W.comap (algebraMap F₀ L) := by
    refine hdet _ _ ?_ hW₀
    have h' : (specialFibreMap ψ hψ η' : Lv₀.c.scheme) = (specialFibreMap ψ hψ η :) := by
      rw [hζ]
    exact h' ▸ hW₀'
  obtain ⟨τ, hτW⟩ := SemistableReduction.GaloisReduction.exists_smul_eq W' W hcomap
  obtain ⟨σ, hσφ, hσ⟩ := hτ τ
  obtain ⟨ψσ, hψσ, hjσ⟩ := hact σ
  refine ⟨σ, hσφ, ψσ, hψσ, hjσ, ?_⟩
  have hmove : ψσ (η : Lv.c.scheme) = (η' : Lv.c.scheme) := by
    obtain ⟨l, hl, hlη⟩ := hW
    have hr : ∀ x : W, τ.symm (x : L) ∈ W' := by
      intro x
      have hx : (x : L) ∈ τ • W' := hτW ▸ x.2
      exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.1 hx
    let r : W →+* W' := (τ.symm.toRingHom.comp W.subtype).codRestrict W'.toSubring hr
    haveI : IsLocalHom r := ⟨fun a ha => by
      obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ha
      have hb' : τ.symm (a : L) * (b : L) = 1 := congrArg Subtype.val hb
      have hbW : τ (b : L) ∈ W := hτW ▸ ValuationSubring.smul_mem_pointwise_smul τ _ W' b.2
      refine isUnit_iff_exists_inv.2 ⟨⟨_, hbW⟩, Subtype.ext ?_⟩
      change (a : L) * τ (b : L) = 1
      have := congrArg τ hb'
      rwa [map_mul, AlgEquiv.apply_symm_apply, map_one] at this⟩
    have hl'' : genMap W' ≫ (Spec.map (CommRingCat.ofHom r) ≫ l ≫ ψσ) = Lv.gen L := by
      have e₁ : genMap W' ≫ Spec.map (CommRingCat.ofHom r) =
          Spec.map (CommRingCat.ofHom (τ.symm : L →+* L)) ≫ genMap W := by
        rw [genMap, genMap, ← Spec.map_comp, ← Spec.map_comp]
        rfl
      rw [← Category.assoc (genMap W') (Spec.map (CommRingCat.ofHom r)) (l ≫ ψσ), e₁,
        Category.assoc, ← Category.assoc (genMap W) l ψσ, hl]
      simp only [Level.gen, Category.assoc]
      have e₂ : CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B) ≫
          CommRingCat.ofHom (algebraMap Lv.L.B L) =
          CommRingCat.ofHom (algebraMap Lv.L.B L) ≫ CommRingCat.ofHom (τ : L →+* L) :=
        CommRingCat.hom_ext (RingHom.ext fun b => (hσ b).symm)
      have e₃ : CommRingCat.ofHom (τ : L →+* L) ≫ CommRingCat.ofHom (τ.symm : L →+* L) = 𝟙 _ :=
        CommRingCat.hom_ext (RingHom.ext fun x => τ.symm_apply_apply x)
      have hS : Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B L)) ≫
          Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) =
          Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫
            Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B L)) := by
        rw [← Spec.map_comp, ← Spec.map_comp, e₂]
      have hT : Spec.map (CommRingCat.ofHom (τ.symm : L →+* L)) ≫
          Spec.map (CommRingCat.ofHom (τ : L →+* L)) = 𝟙 _ := by
        rw [← Spec.map_comp, e₃, Spec.map_id]
      rw [hjσ, ← Category.assoc (Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B L))), hS,
        Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom (τ.symm : L →+* L))), hT,
        Category.id_comp]
    have hcen := centre_unique Lv.c.toSpec ⟨_, hl'', rfl⟩ hW'
    have hcp : Spec.map (CommRingCat.ofHom r) (closedPoint W') = closedPoint W :=
      IsLocalRing.comap_closedPoint r
    simp only [Scheme.Hom.comp_apply] at hcen
    rw [hcp, hlη] at hcen
    exact hcen
  rw [image_eq_closure (continuous_specialFibreMap ψσ hψσ) (isClosedMap_specialFibreMap' ψσ hψσ)
    hη]
  have : specialFibreMap ψσ hψσ η = η' := Subtype.ext hmove
  rw [this, hη']

end

end TemperedFundamentalGroups
