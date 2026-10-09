/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Final
import TemperedFundamentalGroups.SemistableReduction.W10Coords
import TemperedFundamentalGroups.SemistableReduction.W10Component
import TemperedFundamentalGroups.SemistableReduction.W10Stable
import TemperedFundamentalGroups.SemistableReduction.W10Dom
import TemperedFundamentalGroups.SemistableReduction.W10Compare

/-!
# The output of `StrongA` from a semistable Gauss tree over `E`

Blueprint §9.7a, step 4–5. `strongA_body_of_tree`: over a finite Galois `E / K` with the norm of a
complete discretely valued field, a convex reduced Gauss tree `(aE, cE)` over `E` which is
`Gal(E/K)`-stable, whose normalized tree models in the components of `E ⊗_K B` have semistable
charts, and whose vertices contain the residue-transcendental centres of the given models
(`hV'`), give the existential conclusion of `Statement.StrongA` (via `W10Component`,
`W10Stable`, `W10Dom`, `W10Coords` and `strongA_body_of_data`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits Polynomial TensorProduct

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields ProjScheme ZariskiModel W10Discs

attribute [local instance] polyAlgebra compAlgO

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

variable {K : Type u} [Field K] [CharZero K] (O : ValuationSubring K)
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B]
  [Module.IsTorsionFree K[X] B] [Algebra K B] [IsScalarTower K K[X] B] [Algebra.Smooth K B]
  {E : Type u} [NontriviallyNormedField E] [IsUltrametricDist E] [Algebra K E]

omit [CharZero K] [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] [Algebra K B]
  [IsScalarTower K K[X] B] [Algebra.Smooth K B] [IsUltrametricDist E] in
/-- The semilinearity of `φh`. -/
lemma φh_algebraMap_ratFunc {G : Type u} [Group G] (β : G →* (B ≃ₐ[K[X]] B)) [IsReduced (BX K E B)]
    (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)) (x : RatFunc E) :
    compEquiv (σh β h) 𝔫 (algebraMap (RatFunc E) (Comp K E B (πh β h 𝔫)) x) =
      algebraMap (RatFunc E) (Comp K E B 𝔫)
        (ratFuncMap (((αH (G := G) h⁻¹ : E ≃ₐ[K] E) : E ≃+* E) : E →+* E) x) := by
  change Ideal.Quotient.mk _ (σh β h (algebraMap (RatFunc E) (LX K E B) x)) =
    Ideal.Quotient.mk _ (algebraMap (RatFunc E) (LX K E B) _)
  congr 1
  exact lxEquiv_algebraMap_ratFunc _ _ x

/-- **The output of `StrongA` from a semistable Galois-stable Gauss tree over `E`.** -/
theorem strongA_body_of_tree
    {G : Type u} [Group G] [MulSemiringAction G B] [SMulCommClass G K B]
    (β : G →* (B ≃ₐ[K[X]] B))
    (hβ : ∀ g, (β g).restrictScalars K = MulSemiringAction.toAlgAut G K B g)
    [FiniteDimensional K E] [IsGalois K E]
    (hO' : (νE).valuationSubring.comap (algebraMap K E) = O)
    [IsDiscreteValuationRing (νE).valuationSubring] (ϖ' : (νE).valuationSubring)
    (hϖ' : Irreducible ϖ')
    (hσO' : ∀ σ : E ≃ₐ[K] E, ∀ y ∈ (νE).valuationSubring, σ y ∈ (νE).valuationSubring)
    (hiso : ∀ σ : E ≃ₐ[K] E, ∀ x, νE (σ x) = νE x)
    {r : ℕ} (θ : Fin r → (νE).valuationSubring) (hθ0 : ∀ s, (θ s : E) ≠ 0)
    (hθint : ∀ s, letI := algebraOO' O E (νE).valuationSubring hO'; IsIntegral O (θ s))
    (hθgen : ∀ y : (νE).valuationSubring, (y : E) ∈ Subring.closure
      ((((algebraMap K E).comp O.subtype).range : Set E) ∪ Set.range fun s ↦ (θ s : E)))
    {ιt : Type} [Fintype ιt] [Nonempty ιt] (aE cE : ιt → E) (hcE : ∀ i, cE i ≠ 0)
    (hconv : GaussTree.IsConvex νE aE cE) (hred : GaussTree.IsReduced νE aE cE)
    (hstab : ∀ σ : E ≃ₐ[K] E, ∀ i, ∃ i', νE (σ (cE i)) = νE (cE i') ∧
      νE (σ (aE i) - aE i') ≤ νE (cE i'))
    (hcharts : ∀ 𝔪 : MaximalSpectrum (LX K E B),
      ∀ Cc ∈ ((gaussJoinModel νE aE cE).normalization (Comp K E B 𝔪)).charts,
        ∀ [Algebra (νE).valuationSubring Cc],
          (∀ o, ((algebraMap (νE).valuationSubring Cc o : Cc) : Comp K E B 𝔪) =
            algebraMap (νE).valuationSubring (Comp K E B 𝔪) o) → IsSemistable ϖ' Cc)
    (I : Type u) [Finite I] (c₀ : I → ModelCode O)
    (j₀ : ∀ i, Spec (CommRingCat.of B) ⟶ (c₀ i).scheme)
    {nK : I → MaximalSpectrum (LB K B) → ℕ} {fK : ∀ i 𝔫, Fin (nK i 𝔫 + 1) → CompB K B 𝔫}
    (hfK : ∀ i 𝔫 j, fK i 𝔫 j ≠ 0)
    (ιK : ∀ i 𝔫, (projModelCode O (hfK i 𝔫)).scheme ⟶ (c₀ i).scheme)
    (hιK : ∀ i 𝔫, genericPt O (hfK i 𝔫) ≫ ιK i 𝔫 =
      Spec.map (CommRingCat.ofHom (toCompB 𝔫)) ≫ j₀ i)
    (hιOK : ∀ i 𝔫, ιK i 𝔫 ≫ (c₀ i).toSpec = (projModelCode O (hfK i 𝔫)).toSpec)
    (hV' : ∀ i 𝔪, ∀ W' ∈ RT (νE).valuationSubring
      ((projModel (baseRing (Comp K E B 𝔪) (νE).valuationSubring)
        (fE (f := fK i) 𝔪)).charts : Set (Subring (Comp K E B 𝔪))), ∃ j,
      W'.comap (algebraMap (RatFunc E) (Comp K E B 𝔪)) = (gaussRat νE (aE j)
        (Units.mk0 (νE (cE j)) ((Valuation.ne_zero_iff _).2 (hcE j)))).valuationSubring) :
    ∃ (O' : ValuationSubring E) (_ : O'.comap (algebraMap K E) = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c' : TemperedFundamentalGroups.ModelCode O') (c : TemperedFundamentalGroups.ModelCode O)
      (e : c.scheme ≅ c'.scheme)
      (j : Spec (CommRingCat.of (TensorProduct K E B)) ⟶ c.scheme)
      (act : G × (E ≃ₐ[K] E) →* Aut c.scheme)
      (dom : ∀ i, c.scheme ⟶ (c₀ i).scheme),
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ' c' ∧
      e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K E).restrict O O' (fun x hx => by
          rw [← ‹O'.comap (algebraMap K E) = O›] at hx; exact hx))) = c.toSpec ∧
      IsSchemeTheoreticallyDominant j ∧
      j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeftRingHom).comp ((algebraMap K E).comp O.subtype))) ∧
      (∀ gσ : G × (E ≃ₐ[K] E), (act gσ).hom ≫ c.toSpec = c.toSpec) ∧
      (∀ gσ : G × (E ≃ₐ[K] E),
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr (gσ.2⁻¹)
          (MulSemiringAction.toAlgAut G K B gσ.1⁻¹)).toRingHom) ≫ j = j ≫ (act gσ).hom) ∧
      (∀ i, j ≫ dom i = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct K E B)) ≫ j₀ i) ∧
      (∀ i, dom i ≫ (c₀ i).toSpec = c.toSpec) := by
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI := isReduced_BX K E B
  have hn := isIntegrallyClosedIn_BX K E B
  -- the semistable model of every component
  have hcomp (𝔪 : MaximalSpectrum (LX K E B)) := exists_component_model (F₀ := Comp K E B 𝔪)
    hcE hconv hred ϖ' (hcharts 𝔪) (D K E B 𝔪) (fun z hz ↦ mem_D_of_isIntegral K E B hn 𝔪 hz)
    (by
      rintro _ ⟨o, rfl⟩
      refine ⟨algebraMap E (BX K E B) (o : E), ?_⟩
      change Ideal.Quotient.mk _ (algebraMap (BX K E B) (LX K E B)
        (algebraMap E[X] (BX K E B) (Polynomial.C (o : E)))) =
          Ideal.Quotient.mk _ (algebraMap E (LX K E B) (o : E))
      congr 1
      rw [← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply E[X] (RatFunc E) (LX K E B),
        IsScalarTower.algebraMap_apply E (RatFunc E) (LX K E B), RatFunc.algebraMap_C]
      rfl)
  choose n g hg hpts hss hroot using hcomp
  have hR₁ (𝔪 : MaximalSpectrum (LX K E B)) : (algebraMap O (Comp K E B 𝔪)).range ≤
      baseRing (Comp K E B 𝔪) (νE).valuationSubring := by
    rintro _ ⟨o, rfl⟩
    refine ⟨algebraMap K E o, ?_, rfl⟩
    change algebraMap K E o ∈ (νE).valuationSubring
    rw [← ValuationSubring.mem_comap, hO']
    exact o.2
  have hR (𝔪 : MaximalSpectrum (LX K E B)) : (algebraMap O (Comp K E B 𝔪)).range ≤
      (algebraMap (νE).valuationSubring (Comp K E B 𝔪)).range := by
    rintro _ ⟨o, rfl⟩
    refine ⟨⟨algebraMap K E o, ?_⟩, rfl⟩
    rw [← ValuationSubring.mem_comap, hO']
    exact o.2
  refine strongA_body_of_data O β hβ E (νE).valuationSubring hO' ϖ' hϖ' hn hσO' n hg hss hroot
    (fun h 𝔫 ↦ ?_) θ hθ0 hθint hθgen I c₀ j₀ (fun i ↦ ?_)
  · exact W10Stable.exists_projChart_map_le
      (((αH (G := G) h⁻¹ : E ≃ₐ[K] E) : E ≃+* E)) (hiso _) hcE hred (hstab _)
      (compEquiv (σh β h) 𝔫) (φh_algebraMap_ratFunc β h 𝔫) (hpts (πh β h 𝔫)) (hpts 𝔫)
  · refine ⟨fun 𝔪 ↦ nK i (contrB K E B 𝔪), fE (f := fK i), fE_ne_zero (hfK i),
      ιE O (c₀ i) (hfK i) (ιK i), ιE_toSpec O (c₀ i) (hfK i) (ιK i) (hιOK i),
      genericPt_ιE O (c₀ i) (j₀ i) (hfK i) (ιK i) (hιK i), fun 𝔪 l ↦ ?_⟩
    exact W10Dom.locallyDominates_of_tree (fun j ↦ rfl) hconv hred (hV' i 𝔪) (hR₁ 𝔪) (hR 𝔪)
      (hpts 𝔪) l

end W10Assembly

end SemistableReduction
