/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateRestrictObject
import TemperedFundamentalGroups.Andre.HeightW

/-!
# Model maps to the restricted Tate object are unique up to `ρ(σ)` (`v(q) = 1`, B3h)

For a member `U` with connected level ring and scheme-theoretically dominant `j`, two morphisms
`f, f' : U ⟶ X₀'` have level maps `R[t]/(t² - ϖ) → B` which agree or differ by `σ`
(`QuadraticLevel.eq_or_eq_comp_σ_of_idem`); accordingly `f'.ψ = f.ψ` or `f'.ψ = f.ψ ≫ ρ(σ)`
(`ψ_eq_comp_ρσ`). Hence `Pres.ModelUnique` holds for `X₀'` (`modelUnique'`): the quantities
`tateNuG`, `HCWG` built on model maps are `σ`-invariant (proved, not assumed).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Pi1.Orbifold

namespace TemperedFundamentalGroups.TateRestrict

open RamifiedQuadratic SemistableReduction.W10Apply TempObj SemistableReduction.ProjScheme

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} {ϖ : O} (hϖ : Irreducible ϖ)
  [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero K] (b₄ b₆ : O)
  [Fact (Squarefree (TateNormal.dpoly (sO ϖ) (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆)))]
  (R : Type u) [CommRing R] [Algebra K R] {x y : R}
  (heqR : y ^ 2 + x * y = x ^ 3 + algebraMap K R (ϖ * b₄) * x + algebraMap K R (ϖ * b₆))
  (A : Type u) [Group A] [MulSemiringAction A R] [Subsingleton A]

/-- `ρ(σ)` as an isomorphism of the model of `X₀'`. -/
def ρσX : (X₀' hϖ b₄ b₆ R heqR A).Lv.c.scheme ≅ (X₀' hϖ b₄ b₆ R heqR A).Lv.c.scheme where
  hom := (ρσ hϖ b₄ b₆).hom
  inv := (ρσ hϖ b₄ b₆).inv
  hom_inv_id := (ρσ hϖ b₄ b₆).hom_inv_id
  inv_hom_id := (ρσ hϖ b₄ b₆).inv_hom_id

lemma ρσX_toSpec : (ρσX hϖ b₄ b₆ R heqR A).hom ≫ (X₀' hϖ b₄ b₆ R heqR A).Lv.c.toSpec =
    (X₀' hϖ b₄ b₆ R heqR A).Lv.c.toSpec :=
  ρσ_toSpec hϖ b₄ b₆

/-- `σ` on the level ring of `X₀'`. -/
def σLv : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.B →+* (X₀' hϖ b₄ b₆ R heqR A).Lv.L.B :=
  (QuadraticLevel.σ (cR (ϖ := ϖ) R) : BR (ϖ := ϖ) R →+* BR (ϖ := ϖ) R)

lemma ρσX_j : Spec.map (CommRingCat.ofHom (σLv hϖ b₄ b₆ R heqR A)) ≫
    (X₀' hϖ b₄ b₆ R heqR A).Lv.j =
      (X₀' hϖ b₄ b₆ R heqR A).Lv.j ≫ (ρσX hϖ b₄ b₆ R heqR A).hom := by
  have hσ : ((QuadraticLevel.σ (cR (ϖ := ϖ) R)).toRingEquiv.symm :
      BR (ϖ := ϖ) R →+* BR (ϖ := ϖ) R) = σLv hϖ b₄ b₆ R heqR A :=
    RingHom.ext fun b ↦ σB_symm R b
  have := ρσ_j hϖ R b₄ b₆ heqR
  rw [hσ] at this
  exact this

/-- If the level maps differ by `σ`, the model maps differ by `ρ(σ)`. -/
lemma ψ_eq_comp_ρσ {U : TempObj O R A} [IsSchemeTheoreticallyDominant U.Lv.j]
    (f f' : U ⟶ X₀' hϖ b₄ b₆ R heqR A)
    (h : f'.φ.f = f.φ.f.comp (QuadraticLevel.σ (cR (ϖ := ϖ) R)).toAlgHom) :
    f'.ψ = f.ψ ≫ (ρσX hϖ b₄ b₆ R heqR A).hom := by
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    (X₀' hϖ b₄ b₆ R heqR A).Lv.c.toSpec
    (by rw [f'.ψ_toSpec, Category.assoc, ρσX_toSpec, f.ψ_toSpec]) U.Lv.j ?_
  have e1 : Spec.map (CommRingCat.ofHom (f'.φ.f : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.B →+* U.Lv.L.B)) =
      Spec.map (CommRingCat.ofHom (f.φ.f : (X₀' hϖ b₄ b₆ R heqR A).Lv.L.B →+* U.Lv.L.B)) ≫
        Spec.map (CommRingCat.ofHom (σLv hϖ b₄ b₆ R heqR A)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, h]
    rfl
  rw [f'.j_ψ, e1, Category.assoc, ρσX_j, ← Category.assoc, ← f.j_ψ, Category.assoc]

/-- **Model maps to `X₀'` are unique up to `ρ(σ)`.** -/
theorem modelUnique' [IsReduced R] {xW : R} :
    Pres.ModelUnique xW (X₀' hϖ b₄ b₆ R heqR A) := by
  intro X P f f'
  haveI : IsSchemeTheoreticallyDominant P.U.Lv.j := P.dom
  rcases QuadraticLevel.eq_or_eq_comp_σ_of_idem (isUnit_two (K := K) R) (isUnit_cR hϖ R)
    P.idem f.φ.f f'.φ.f with h | h
  · refine ⟨Homeomorph.refl _, fun z ↦ Subtype.ext ?_⟩
    change f'.ψ z.1 = f.ψ z.1
    rw [show f'.ψ = f.ψ from
      ext_of_isSchemeTheoreticallyDominant_of_isSeparated (X₀' hϖ b₄ b₆ R heqR A).Lv.c.toSpec
        (by rw [f'.ψ_toSpec, f.ψ_toSpec]) P.U.Lv.j (by rw [f'.j_ψ, f.j_ψ, h])]
  · refine ⟨specialFibreHomeomorph (ρσX hϖ b₄ b₆ R heqR A) (ρσX_toSpec hϖ b₄ b₆ R heqR A),
      fun z ↦ Subtype.ext ?_⟩
    change f'.ψ z.1 = (ρσX hϖ b₄ b₆ R heqR A).hom (f.ψ z.1)
    rw [ψ_eq_comp_ρσ hϖ b₄ b₆ R heqR A f f' h]
    rfl

/-! ### The model map determines the level map -/

/-- The structure map of the model of `X₀'` to `Spec O'`. -/
def τR : (X₀' hϖ b₄ b₆ R heqR A).Lv.c.scheme ⟶ Spec (CommRingCat.of (O' ϖ)) :=
  (isoR hϖ b₄ b₆).hom ≫ (projModelCode (O' ϖ) (TateNormal.hcoords (sO ϖ)
    (algebraMap O (O' ϖ) b₄) (algebraMap O (O' ϖ) b₆) (sO_ne_zero hϖ))).toSpec

/-- `φB` with codomain the level ring of `X₀'`. -/
def φBX : O' ϖ →+* (X₀' hϖ b₄ b₆ R heqR A).Lv.L.B := φB hϖ R

@[reassoc]
lemma j_τR : (X₀' hϖ b₄ b₆ R heqR A).Lv.j ≫ τR hϖ b₄ b₆ R heqR A =
    Spec.map (CommRingCat.ofHom (φBX hϖ b₄ b₆ R heqR A)) := by
  rw [τR]
  change jR hϖ R b₄ b₆ heqR ≫ _ = _
  rw [jR, jO, Category.assoc]
  erw [Iso.inv_hom_id_assoc, TateNormal.jChart_toSpec]
  rfl

lemma ρσX_τR : (ρσX hϖ b₄ b₆ R heqR A).hom ≫ τR hϖ b₄ b₆ R heqR A =
    τR hϖ b₄ b₆ R heqR A ≫ Spec.map (CommRingCat.ofHom (σO hϖ)) := by
  change ((isoR hϖ b₄ b₆).hom ≫ ρR' hϖ b₄ b₆ ≫ (isoR hϖ b₄ b₆).inv) ≫
    (isoR hϖ b₄ b₆).hom ≫ _ = ((isoR hϖ b₄ b₆).hom ≫ _) ≫ _
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [ρ'_toSpec]

/-- **The model map determines the level map** (for a connected level ring and dominant `j`):
`ρ(σ)` moves the structure map to `Spec O'` by `σ`, `√ϖ ↦ -√ϖ`. -/
lemma φf_eq_of_ψ_eq {U : TempObj O R A} [IsSchemeTheoreticallyDominant U.Lv.j]
    (hidem : ∀ e : U.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (f f' : U ⟶ X₀' hϖ b₄ b₆ R heqR A) (hψ : f'.ψ = f.ψ) : f'.φ.f = f.φ.f := by
  rcases QuadraticLevel.eq_or_eq_comp_σ_of_idem (isUnit_two (K := K) R) (isUnit_cR hϖ R)
    hidem f.φ.f f'.φ.f with h | h
  · exact h
  have key : f.ψ ≫ (ρσX hϖ b₄ b₆ R heqR A).hom = f.ψ :=
    (ψ_eq_comp_ρσ hϖ b₄ b₆ R heqR A f f' h).symm.trans hψ
  have e : U.Lv.j ≫ f.ψ ≫ τR hϖ b₄ b₆ R heqR A =
      U.Lv.j ≫ f.ψ ≫ τR hϖ b₄ b₆ R heqR A ≫ Spec.map (CommRingCat.ofHom (σO hϖ)) := by
    rw [← ρσX_τR, ← Category.assoc f.ψ, key]
  simp only [← Category.assoc] at e
  rw [f.j_ψ] at e
  simp only [Category.assoc] at e
  rw [j_τR, j_τR_assoc, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp] at e
  have e2 := congrArg (fun φ ↦ φ.hom (sO ϖ)) (Spec.map_injective e)
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at e2
  change f.φ.f (φB hϖ R (sO ϖ)) = f.φ.f (φB hϖ R (σO hϖ (sO ϖ))) at e2
  rw [σO_sO, map_neg] at e2
  erw [map_neg] at e2
  rw [φB_sO] at e2
  have hu : IsUnit ((2 : U.Lv.L.B) * f.φ.f (QuadraticLevel.x (cR (ϖ := ϖ) R))) := by
    refine IsUnit.mul ?_ ((isUnit_t hϖ R).map f.φ.f)
    have := (isUnit_two (K := K) R).map (algebraMap R U.Lv.L.B)
    rwa [map_ofNat] at this
  have h0 : (2 : U.Lv.L.B) * f.φ.f (QuadraticLevel.x (cR (ϖ := ϖ) R)) = 0 := by
    linear_combination e2
  rw [h0] at hu
  haveI : Subsingleton U.Lv.L.B := subsingleton_of_zero_eq_one (isUnit_zero_iff.1 hu)
  exact AlgHom.ext fun _ ↦ Subsingleton.elim _ _

end

end TemperedFundamentalGroups.TateRestrict
