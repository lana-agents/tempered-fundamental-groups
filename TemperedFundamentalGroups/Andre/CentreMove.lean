/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.GTransitive

/-!
# Model automorphisms move centres of valuations (Blueprint §12.8, M2.6)

`Level.map_centre_of_smul_eq`: if a level automorphism `σ` with model automorphism `ψσ` induces
`τ` on a fraction field `L` of the level ring, and `τ • W' = W` for valuation subrings `W, W'`
of `L` with centres `x`, `x'`, then `ψσ x = x'` (the argument `hmove` of
`exists_aut_image_eq`). In particular `ψσ` fixes the centre of a `τ`-stable valuation subring.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped Pointwise

namespace TemperedFundamentalGroups

open ValuativeCentre

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- **Model automorphisms move centres along the induced field automorphism.** -/
theorem Level.map_centre_of_smul_eq (Lv : Level O R A) (L : Type u) [Field L]
    [Algebra Lv.L.B L] (σ : Lv.L.B ≃ₐ[R] Lv.L.B) (ψσ : Lv.c.scheme ⟶ Lv.c.scheme)
    (hψσ : ψσ ≫ Lv.c.toSpec = Lv.c.toSpec)
    (hjσ : Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j)
    (τ : L ≃+* L) (hσ : ∀ b, τ (algebraMap Lv.L.B L b) = algebraMap Lv.L.B L (σ b))
    {W W' : ValuationSubring L} {x x' : Lv.c.scheme} (hW : IsCentre (Lv.gen L) W x)
    (hW' : IsCentre (Lv.gen L) W' x') (hτW : τ • W' = W) : ψσ x = x' := by
  have _ := hψσ
  obtain ⟨l, hl, hlη⟩ := hW
  have hr : ∀ y : W, τ.symm (y : L) ∈ W' := by
    intro y
    have hy : (y : L) ∈ τ • W' := hτW ▸ y.2
    exact ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem.1 hy
  let r : W →+* W' := (τ.symm.toRingHom.comp W.subtype).codRestrict W'.toSubring hr
  haveI : IsLocalHom r := ⟨fun a ha => by
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ha
    have hb' : τ.symm (a : L) * (b : L) = 1 := congrArg Subtype.val hb
    have hbW : τ (b : L) ∈ W := hτW ▸ ValuationSubring.smul_mem_pointwise_smul τ _ W' b.2
    refine isUnit_iff_exists_inv.2 ⟨⟨_, hbW⟩, Subtype.ext ?_⟩
    change (a : L) * τ (b : L) = 1
    have := congrArg τ hb'
    rwa [map_mul, RingEquiv.apply_symm_apply, map_one] at this⟩
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
      CommRingCat.hom_ext (RingHom.ext fun y => τ.symm_apply_apply y)
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
  have hcp : Spec.map (CommRingCat.ofHom r) (IsLocalRing.closedPoint W') =
      IsLocalRing.closedPoint W :=
    IsLocalRing.comap_closedPoint r
  simp only [Scheme.Hom.comp_apply] at hcen
  rw [hcp, hlη] at hcen
  exact hcen

end TemperedFundamentalGroups
