/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGaloisRigid
import TemperedFundamentalGroups.Andre.GaloisClass

/-!
# The class of orbifold Galois objects (Blueprint §11.3, G6, orbifold case)

`galClassO O R A Ω A₁`: tempered coverings of `[Spec R / A]` isomorphic to
`OrbGal.obj D hX hp hc = Ind_1^S Z̃` where

* `Lv₁` is a scheme level (over the trivial group `A₁`, trivial `H`) whose algebra `B` has a
  geometric point, is connected, Galois over `R`, and **Galois over `[Spec R / A]`** (every
  `a ∈ A` lifts to a semilinear automorphism of `B`), every semilinear automorphism of `B`
  extending to the model, with `j` scheme-theoretically dominant and a semistable model whose
  special fibre satisfies the hypotheses of N1 and is connected;
* `Z̃ = universalCovering` of the special fibre of `Lv₁`;
* `D` is any induction data `(S, α : S ↠ A)` on `U_{Lv₁}`.

**(gal)** `isGaloisClass_galClassO` (`OrbGal.exists_iso_fibreMap`) and **(rig)**
`isRigid_galClassO` (`OrbGal.fibreMap_eq_of_eq`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit OrbGal

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]

section Inst

variable {A₁ : Type u} [Group A₁] [MulSemiringAction A₁ R] (Lv : Level O R A₁) [Finite Lv.L.H]
  [TopologicalSpace.NoetherianSpace Lv.Z] [T0Space Lv.Z] [QuasiSober Lv.Z]
  (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z)

instance [h : Subsingleton Lv.L.H] : Subsingleton (universalObj Lv hdim z₀).Lv.L.H := h

instance : Finite (universalObj Lv hdim z₀).Lv.L.H := ‹Finite Lv.L.H›

end Inst

variable (O R A) in
/-- **The class of orbifold Galois objects** (induced from Galois-over-`[Spec R / A]` scheme
levels). -/
def galClassO (Ω : Type u) [Field Ω] [Algebra R Ω] (A₁ : Type u) [Group A₁] [Subsingleton A₁]
    [MulSemiringAction A₁ R] : ObjectProperty (TempObj O R A) := fun X =>
  ∃ (Lv₁ : Level O R A₁) (_ : Subsingleton Lv₁.L.H) (_ : TopologicalSpace.NoetherianSpace Lv₁.Z)
    (_ : T0Space Lv₁.Z) (_ : QuasiSober Lv₁.Z) (_ : ConnectedSpace Lv₁.Z)
    (hdim : topologicalKrullDim Lv₁.Z ≤ 1) (z₀ : Lv₁.Z)
    (D : IndData (μ₁ A A₁) (universalObj Lv₁ hdim z₀))
    (hX : IndFaithful (universalObj Lv₁ hdim z₀)),
    Nonempty (Lv₁.L.B →ₐ[R] Ω) ∧
    (∀ t t' : Lv₁.L.B →ₐ[R] Ω, ∃ σ : Lv₁.L.B ≃ₐ[R] Lv₁.L.B,
      t.comp (σ : Lv₁.L.B →ₐ[R] Lv₁.L.B) = t') ∧
    (∀ e : Lv₁.L.B, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
    (∀ a : A, ∃ γ : SemilinearAut R A Lv₁.L.B, γ.a = a) ∧
    (∀ γ : SemilinearAut R A Lv₁.L.B, ∃ ψ : Lv₁.c.scheme ⟶ Lv₁.c.scheme,
      ψ ≫ Lv₁.c.toSpec = Lv₁.c.toSpec ∧
      Lv₁.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : Lv₁.L.B →+* Lv₁.L.B)) ≫ Lv₁.j) ∧
    IsSemistableLevel Lv₁ ∧ IsSchemeTheoreticallyDominant Lv₁.j ∧
    Nonempty (X ≅ OrbGal.obj D hX (universalCovering.isUniversalCovering.{u, u, u} hdim z₀)
      (universalCovering.isUniversalCovering.{u, u, u} hdim z₀).countable_fibre)

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (A₁ : Type u) [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

/-- A base point `(t₀, e₀)` exists: `t₀` a geometric point of `B`, `e₀ ∈ Z̃` over its
specialization (`Z̃ → Z` is surjective, `Z` being connected). -/
lemma exists_base {Lv₁ : Level O R A₁} [ConnectedSpace Lv₁.Z] {E : Type u} [TopologicalSpace E]
    {p : E → Lv₁.Z} (hp : IsUniversalCovering.{u, u, u, u} p) (h : Nonempty (Lv₁.L.B →ₐ[R] Ω)) :
    ∃ (t₀ : Lv₁.L.B →ₐ[R] Ω) (e₀ : E), p e₀ = Lv₁.sp V hV t₀ := by
  obtain ⟨t₀⟩ := h
  haveI := hp.connectedSpace
  obtain ⟨e₀, he₀⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv₁.sp V hV t₀)
  exact ⟨t₀, e₀, he₀⟩

/-- **(gal)** for `galClassO`. -/
theorem isGaloisClass_galClassO :
    IsGaloisClass (tempFibre O R A V hV) (galClassO O R A Ω A₁) := by
  rintro X ⟨Lv₁, _, _, _, _, _, hdim, z₀, D, hX, hne, hgal, -, hsym, hact, -, hdom, ⟨e⟩⟩ x y
  haveI : IsSchemeTheoreticallyDominant (universalObj Lv₁ hdim z₀).Lv.j := hdom
  obtain ⟨t₀, e₀, he₀⟩ := exists_base V hV A₁
    (universalCovering.isUniversalCovering.{u, u, u} hdim z₀) hne
  obtain ⟨π, hπ⟩ := OrbGal.exists_iso_fibreMap (X₁ := universalObj Lv₁ hdim z₀) D hX
    (universalCovering.isUniversalCovering.{u, u, u} hdim z₀)
    (universalCovering.isUniversalCovering.{u, u, u} hdim z₀).countable_fibre V hV hgal hsym
    hact t₀ e₀ he₀ (fibreMap V hV e.hom x) (fibreMap V hV e.hom y)
  refine ⟨e ≪≫ π ≪≫ e.symm, ?_⟩
  rw [Iso.trans_hom, Iso.trans_hom, Functor.map_comp_apply, Functor.map_comp_apply, Iso.symm_hom]
  simp only [tempFibre_map_apply]
  exact (congrArg (fibreMap V hV e.inv) hπ).trans
    (Iso.hom_inv_id_apply ((tempFibre O R A V hV).mapIso e) y)

/-- **(rig)** for `galClassO`. -/
theorem isRigid_galClassO : IsRigid (tempFibre O R A V hV) (galClassO O R A Ω A₁) := by
  rintro X ⟨Lv₁, _, _, _, _, _, hdim, z₀, D, hX, hne, hgal, hidem, hsym, hact, -, hdom, ⟨e⟩⟩
    Y f f' g hg
  haveI : IsSchemeTheoreticallyDominant (universalObj Lv₁ hdim z₀).Lv.j := hdom
  obtain ⟨t₀, e₀, he₀⟩ := exists_base V hV A₁
    (universalCovering.isUniversalCovering.{u, u, u} hdim z₀) hne
  have key := OrbGal.fibreMap_eq_of_eq (X₁ := universalObj Lv₁ hdim z₀) D hX
    (universalCovering.isUniversalCovering.{u, u, u} hdim z₀)
    (universalCovering.isUniversalCovering.{u, u, u} hdim z₀).countable_fibre V hV hidem t₀ e₀
    he₀ (e.inv ≫ f) (e.inv ≫ f') hgal hsym hact (fibreMap V hV e.hom g)
    (by
      simp only [← tempFibre_map_apply, ← Functor.map_comp_apply, Iso.hom_inv_id_assoc]
      exact hg)
  have h₁ : (tempFibre O R A V hV).map (e.inv ≫ f) = (tempFibre O R A V hV).map (e.inv ≫ f') :=
    congrArg TypeCat.ofHom key
  rw [← e.hom_inv_id_assoc f, ← e.hom_inv_id_assoc f', Functor.map_comp _ e.hom (e.inv ≫ f),
    Functor.map_comp _ e.hom (e.inv ≫ f'), h₁]

end

end TemperedFundamentalGroups
