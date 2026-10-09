/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussValTransfer
import TemperedFundamentalGroups.SemistableReduction.XHarmonic
import TemperedFundamentalGroups.SemistableReduction.W10Scheme

/-!
# The W10 component models are W-models

Blueprint §10.3.8 (StrongComponentA (a)). `isWModelOf_projModelCode`: a projective model
`projModelCode O' g` whose points are those of the normalization of a Gauss tree model (for any
valuation `v` with valuation subring `O'`, e.g. the norm valuation of `E`) is the W-model
(`ModelCode.IsWModelOf`) on the x-line `x = X`, with generic point `genericPt`. The x-line
structure `xLineAlgebra` is the given `E(X)`-structure (`xLineAlgebra_eq`).
-/

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace TemperedFundamentalGroups.SemistableReduction

open _root_.SemistableReduction _root_.SemistableReduction.ProjScheme

variable {E : Type u} [Field E] (O' : ValuationSubring E) {L : Type u} [Field L] [Algebra E L]

omit [Algebra E L] in
lemma projModel_points_congr {R R' : Subring L} (h : R = R') {n : ℕ} (g : Fin (n + 1) → L) :
    (ZariskiModel.projModel R g).points = (ZariskiModel.projModel R' g).points := by
  subst h; rfl

omit [Algebra E L] in
/-- Normalizations only depend on the algebra structure through its value. -/
lemma normalization_points_congr {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F]
    [Algebra K F'] {O : ValuationSubring K} (M : ZariskiModel (baseRing F O))
    (i₁ i₂ : Algebra F F') (h : i₁ = i₂) (t₁ : letI := i₁; IsScalarTower K F F')
    (t₂ : letI := i₂; IsScalarTower K F F') :
    (letI := i₁; haveI := t₁; (M.normalization F').points) =
      (letI := i₂; haveI := t₂; (M.normalization F').points) := by
  subst h
  rfl

/-- The x-line structure of `L` is its given `E(X)`-structure when `x` is the image of `X`. -/
lemma xLineAlgebra_eq [inst : Algebra (RatFunc E) L] [IsScalarTower E (RatFunc E) L]
    (hx : Transcendental E (algebraMap (RatFunc E) L RatFunc.X)) :
    xLineAlgebra L hx = inst := by
  set x := algebraMap (RatFunc E) L RatFunc.X with hxdef
  have hle : nonZeroDivisors E[X] ≤ (nonZeroDivisors L).comap (aeval x : E[X] →ₐ[E] L) :=
    fun p hp ↦ by
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq] at hp ⊢
      exact fun h ↦ hp ((injective_iff_map_eq_zero _).mp
        (transcendental_iff_injective.mp hx) p h)
  have hlift : ∀ p : E[X], RatFunc.liftAlgHom (aeval x) hle (algebraMap E[X] (RatFunc E) p) =
      aeval x p := fun p => by
    have := RatFunc.liftAlgHom_apply_div (aeval x) hle p 1
    rwa [map_one, div_one, map_one, div_one] at this
  have key : (RatFunc.liftAlgHom (aeval x) hle).toRingHom = algebraMap (RatFunc E) L := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors E[X]) ?_
    refine Polynomial.ringHom_ext (fun e => ?_) ?_
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hlift, aeval_C, IsScalarTower.algebraMap_apply E (RatFunc E) L]
      congr 1
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [hlift, aeval_X, RatFunc.algebraMap_X]
  exact Algebra.algebra_ext _ _ (RingHom.congr_fun key)

/-- **The projective models of the W10 components are W-models** (`ModelCode.IsWModelOf`) on
the x-line `x = X`, given the points of the normalized Gauss tree model for a valuation `v` with
valuation subring `O'`. -/
theorem isWModelOf_projModelCode [inst : Algebra (RatFunc E) L] [IsScalarTower E (RatFunc E) L]
    [FiniteDimensional (RatFunc E) L] [Algebra O' L] [IsScalarTower O' E L]
    (hx : Transcendental E (algebraMap (RatFunc E) L RatFunc.X)) {ι : Type} [Fintype ι]
    (a b : ι → E) (hb : ∀ i, b i ≠ 0) {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation E Γ) (hv : v.valuationSubring = O') {n : ℕ} {g : Fin (n + 1) → L}
    (hg : ∀ i, g i ≠ 0)
    (hpts : (ZariskiModel.projModel (algebraMap O' L).range g).points =
      ((gaussJoinModel v a b).normalization L).points) :
    ModelCode.IsWModelOf O' L (algebraMap (RatFunc E) L RatFunc.X) hx a b (projModelCode O' hg)
      (genericPt O' hg) := by
  have h := xLineAlgebra_eq hx
  unfold ModelCode.IsWModelOf
  have hR : baseRing L O'.valuation.valuationSubring = (algebraMap O' L).range := by
    rw [ValuationSubring.valuationSubring_valuation]
    ext y
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨o, ho⟩, IsScalarTower.algebraMap_apply O' E L _⟩
    · rintro ⟨o, rfl⟩
      exact ⟨o, o.2, (IsScalarTower.algebraMap_apply O' E L o).symm⟩
  refine ⟨by rw [h]; exact Algebra.IsAlgebraic.of_finite _ _, hb, n, g, hg, ?_, Iso.refl _,
    by simp, ?_⟩
  · rw [projModel_points_congr hR, hpts]
    refine (ZariskiModel.points_eq_of_charts_eq _ _
      (ZariskiModel.normalization_charts_eq _ _ ?_)).trans
      (normalization_points_congr (gaussJoinModel O'.valuation a b) inst (xLineAlgebra L hx)
        h.symm inferInstance _)
    exact gaussJoinModel_charts_congr
      (hv.trans (ValuationSubring.valuationSubring_valuation O').symm) a b
  · simp only [Iso.refl_hom, Category.comp_id]
    rfl

end TemperedFundamentalGroups.SemistableReduction
