/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Discs
import TemperedFundamentalGroups.SemistableReduction.ModelDomination
import TemperedFundamentalGroups.SemistableReduction.W10Points
import TemperedFundamentalGroups.SemistableReduction.WModelChart
import TemperedFundamentalGroups.SemistableReduction.GaussTreeFinite

/-!
# Domination of the given models by the tree models

Blueprint §9.7a (W10 assembly, the dominations `dom`).

* **(G1)** `exists_mem_RT_comap_eq`: residue-transcendental centres on charts over `O_v ∩ K` lift
  along `χ : L' → L` to residue-transcendental centres over `O_v` on corresponding charts.
* **(G2)** `exists_chart_le_of_points`: M10 (`dominates_of_vertexSet_subset`) for the normalized
  tree model `X` over a DVR (vertex set `gaussJoinModel_normalization_vertexSet`): if every
  residue-transcendental centre on the charts of a proper model `Y` of finite type lies over a
  tree vertex, every local ring of `X` contains a chart of `Y`. Side conditions:
  `normalization_charts_frac`, `trdeg_le_one`. `locallyDominates_of_tree`: the `hdom` form of
  `W10Assembly` (`locallyDominates_of_points`).
-/

open Polynomial IsLocalRing

namespace SemistableReduction

open ZariskiModel W10Discs

namespace W10Dom

section Lift

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation Ω Γ₀}
  {L' L : Type*} [Field L'] [Field L] [Algebra (RatFunc K) L'] [Algebra (RatFunc Ω) L]
  [Algebra K L'] [IsScalarTower K (RatFunc K) L'] [Algebra Ω L] [IsScalarTower Ω (RatFunc Ω) L]
  {χ : L' →+* L}
  (hχ : ∀ x, χ (algebraMap (RatFunc K) L' x) =
    algebraMap (RatFunc Ω) L (ratFuncMap (algebraMap K Ω) x))

include hχ in
lemma χ_algebraMap (k : K) : χ (algebraMap K L' k) = algebraMap Ω L (algebraMap K Ω k) := by
  rw [IsScalarTower.algebraMap_apply K (RatFunc K) L', hχ, ratFuncMap_algebraMap_C,
    ← IsScalarTower.algebraMap_apply]

include hχ in
/-- **(G1) Lifting residue-transcendental centres.** Let `Ω/K` be algebraic with `O_v` the only
extension of `O_v ∩ K` to `Ω`, and let every chart `B` of `L'` have a corresponding chart `B'` of
`L` with `χ B ⊆ B' ⊆ O_v[χ B]`. Every residue-transcendental centre `W'` over `O_v ∩ K` on the
charts of `L'` is the restriction of a residue-transcendental centre over `O_v` on the charts of
`L`. -/
theorem exists_mem_RT_comap_eq [Algebra.IsAlgebraic K Ω]
    (huniq : ∀ V : ValuationSubring Ω, V.comap (algebraMap K Ω) =
      v.valuationSubring.comap (algebraMap K Ω) → V = v.valuationSubring)
    {chartsE : Set (Subring L')} {chartsC : Set (Subring L)}
    (hY : ∀ B ∈ chartsE, ∃ B' ∈ chartsC, (∀ z ∈ B, χ z ∈ B') ∧
      B' ≤ Subring.closure ((baseRing L v.valuationSubring : Set L) ∪ χ '' B))
    {W' : ValuationSubring L'} (hW' : W' ∈ RT (v.valuationSubring.comap (algebraMap K Ω)) chartsE) :
    ∃ W ∈ RT v.valuationSubring chartsC, W.comap χ = W' := by
  obtain ⟨hW'K, B, hB, hBW', z, hzB, hz⟩ := hW'
  letI : Algebra L' L := χ.toAlgebra
  obtain ⟨W, hW⟩ := TemperedFundamentalGroups.ValuationSubring.exists_comap_eq (Ω := L) W'
  have hWχ : W.comap χ = W' := hW
  set OK := v.valuationSubring.comap (algebraMap K Ω)
  -- `W ∩ Ω = O_v`
  have hcomp : (algebraMap Ω L).comp (algebraMap K Ω) = χ.comp (algebraMap K L') :=
    RingHom.ext fun k ↦ (χ_algebraMap hχ k).symm
  have hWΩ : W.comap (algebraMap Ω L) = v.valuationSubring := by
    refine huniq _ ?_
    rw [ValuationSubring.comap_comap, hcomp, ← ValuationSubring.comap_comap, hWχ, hW'K]
  obtain ⟨B', hB', hBB', hB'le⟩ := hY B hB
  have hBW : ∀ y ∈ B, χ y ∈ W := fun y hy ↦ by
    have : y ∈ W.comap χ := hWχ ▸ hBW' hy
    exact this
  have hB'W : B' ≤ W.toSubring := by
    refine hB'le.trans (Subring.closure_le.2 (Set.union_subset ?_ ?_))
    · rintro _ ⟨o, ho, rfl⟩
      have : o ∈ W.comap (algebraMap Ω L) := by rw [hWΩ]; exact ho
      exact this
    · rintro _ ⟨y, hy, rfl⟩
      exact hBW y hy
  refine ⟨W, ⟨hWΩ, B', hB', hB'W, χ z, hBB' z hzB, ?_⟩, hWχ⟩
  -- residue transcendence
  letI : Algebra K L := ((algebraMap Ω L).comp (algebraMap K Ω)).toAlgebra
  have hWK : W.comap (algebraMap K L) = OK := by
    change W.comap ((algebraMap Ω L).comp (algebraMap K Ω)) = OK
    rw [← ValuationSubring.comap_comap, hWΩ]
  have hO : v.valuationSubring.comap (algebraMap K Ω) = OK := rfl
  have hzW : χ z ∈ W := hBW z hzB
  have hzW' : z ∈ W' := hBW' hzB
  letI := residueAlgebra hW'K
  letI := residueAlgebra hWK
  letI := residueAlgebra hWΩ
  letI := residueAlgebra hO
  letI := residueAlgebra (K := L') (F := L) hWχ
  haveI : IsScalarTower (ResidueField OK) (ResidueField v.valuationSubring)
      (ResidueField W) := by
    refine IsScalarTower.of_algebraMap_eq' (Ideal.Quotient.ringHom_ext (RingHom.ext fun o ↦ ?_))
    change ResidueField.map _ (residue _ o) = ResidueField.map _ (ResidueField.map _ (residue _ o))
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
    congr 1
  haveI : IsScalarTower (ResidueField OK) (ResidueField W') (ResidueField W) := by
    refine IsScalarTower.of_algebraMap_eq' (Ideal.Quotient.ringHom_ext (RingHom.ext fun o ↦ ?_))
    change ResidueField.map _ (residue _ o) = ResidueField.map _ (ResidueField.map _ (residue _ o))
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (χ_algebraMap hχ o).symm
  haveI := isAlgebraic_residueField hO
  have ht' := (isResidueTranscendental_iff hW'K hzW').1 hz
  have himg : algebraMap (ResidueField W') (ResidueField W) (residue W' ⟨z, hzW'⟩) =
      residue W ⟨χ z, hzW⟩ := by
    change ResidueField.map _ (residue _ _) = _
    rw [ResidueField.map_residue]
    rfl
  have ht : Transcendental (ResidueField OK) (residue W ⟨χ z, hzW⟩) := by
    rw [← himg]
    intro halg
    exact ht' ((isAlgebraic_algHom_iff (IsScalarTower.toAlgHom (ResidueField OK)
      (ResidueField W') (ResidueField W)) (RingHom.injective _)).1 halg)
  rw [isResidueTranscendental_iff hWΩ hzW]
  exact fun halg ↦ ht (halg.restrictScalars (R := ResidueField OK))

end Lift

section Dom

universe u

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}
  {F₀ : Type u} [Field F₀] [Algebra K F₀] [Algebra (RatFunc K) F₀]
  [IsScalarTower K (RatFunc K) F₀]
  {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → K}

/-- The charts of the normalized tree model have fraction field `F₀`. -/
theorem normalization_charts_frac [Algebra.IsAlgebraic (RatFunc K) F₀] (hc : ∀ i, c i ≠ 0) :
    ∀ C ∈ ((gaussJoinModel v a c).normalization F₀).charts, ∀ x : F₀,
      ∃ p ∈ C, ∃ q ∈ C, q ≠ 0 ∧ x = p / q := by
  intro C hC f
  obtain ⟨A, hA, rfl⟩ := mem_normalization_charts.1 hC
  haveI : IsFractionRing A (RatFunc K) := by
    refine IsFractionRing.of_field _ _ fun z ↦ ?_
    have hz : z ∈ Subfield.closure (A : Set (RatFunc K)) := by
      rw [TemperedFundamentalGroups.SemistableReduction.subfield_closure_gaussChart_eq_top hc hA]
      trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Subfield.mem_closure_iff.mp hz
    rw [Subring.closure_eq] at hp hq
    exact ⟨⟨p, hp⟩, ⟨q, hq⟩, rfl⟩
  let φ := algebraMap (RatFunc K) F₀
  letI : Algebra A F₀ := (φ.comp A.subtype).toAlgebra
  haveI : IsScalarTower A (RatFunc K) F₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hfA : IsAlgebraic A f := (IsFractionRing.isAlgebraic_iff A (RatFunc K) F₀).mpr
    (Algebra.IsAlgebraic.isAlgebraic f)
  obtain ⟨d, hd0, hdi⟩ := hfA.exists_integral_multiple
  let ψ : A →+* A.map φ := (φ.comp A.subtype).codRestrict (A.map φ) fun z ↦ ⟨z, z.2, rfl⟩
  letI : Algebra A (A.map φ) := ψ.toAlgebra
  haveI : IsScalarTower A (A.map φ) F₀ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hint : IsIntegral (A.map φ) (d • f) := hdi.tower_top
  have hmem : d • f ∈ normChart F₀ A := hint
  have hdmem : φ d ∈ normChart F₀ A := map_le_normChart A ⟨d, d.2, rfl⟩
  have hd0' : φ d ≠ 0 := by
    rw [map_ne_zero_iff _ φ.injective]
    exact fun h ↦ hd0 (Subtype.ext h)
  refine ⟨_, hmem, _, hdmem, hd0', ?_⟩
  rw [Algebra.smul_def]
  change f = (φ d * f) / φ d
  rw [mul_div_cancel_left₀ _ hd0']

lemma trdeg_le_one [Algebra.IsAlgebraic (RatFunc K) F₀] : Algebra.trdeg K F₀ ≤ 1 := by
  have := trdeg_add_eq K (RatFunc K) (A := F₀)
  rw [trdeg_eq_zero (R := RatFunc K) (A := F₀), add_zero, trdeg_ratFunc] at this
  exact this.symm.le

variable [IsDiscreteValuationRing v.valuationSubring] [FiniteDimensional (RatFunc K) F₀]
  [Algebra.IsSeparable (RatFunc K) F₀]

/-- **(G2) Domination by the normalized tree model** (M10 + the vertex set of the tree model):
if every residue-transcendental centre over `O_v` on the charts of a proper model `Y` of finite
type lies over a Gauss valuation `w_{a i, r i}` of the tree, every local ring of the normalized
tree model contains a chart of `Y`. -/
theorem exists_chart_le_of_points {r : ι → Γ₀ˣ} (hc : ∀ i, v (c i) = r i)
    (hconv : GaussTree.IsConvex v a c) (hred : GaussTree.IsReduced v a c)
    {Y : ZariskiModel (baseRing F₀ v.valuationSubring)} (hY : Y.IsProper) (hYf : Y.IsFiniteType)
    (hV' : ∀ W' ∈ RT v.valuationSubring (Y.charts : Set (Subring F₀)), ∃ i,
      W'.comap (algebraMap (RatFunc K) F₀) = (gaussRat v (a i) (r i)).valuationSubring) :
    ∀ P ∈ ((gaussJoinModel v a c).normalization F₀).points, ∃ B ∈ Y.charts, B ≤ P := by
  have hc0 : ∀ i, c i ≠ 0 := fun i h ↦ (r i).ne_zero (by rw [← hc i, h, map_zero])
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
  refine ZariskiModel.dominates_of_vertexSet_subset trdeg_le_one
    (normalization_isSeparated gaussJoinModel_isSeparated) normalization_isNormal
    (gaussJoinModel_normalization_isFiniteType hc0 hconv hred (eq_or_eq_top_of_le hϖ))
    (normalization_charts_frac hc0) hY hYf ?_
  intro W hW B hB hBW z hz hRT
  rw [gaussJoinModel_normalization_vertexSet hc]
  exact hV' W ⟨hW, B, hB, hBW, z, hz, hRT⟩

/-- **(G2), `hdom` form.** If the projective model of `g` over `R₂` has the points of the
normalized tree model, then its charts locally dominate the charts of `f` over `R₁ ⊆ R₂`,
`R₁ ⊆ O_v` (`LocallyDominates`, the hypothesis `hdom` of `W10Assembly`). -/
theorem locallyDominates_of_tree {r : ι → Γ₀ˣ} (hc : ∀ i, v (c i) = r i)
    (hconv : GaussTree.IsConvex v a c) (hred : GaussTree.IsReduced v a c)
    {m : ℕ} {f : Fin (m + 1) → F₀}
    (hV' : ∀ W' ∈ RT v.valuationSubring
      ((projModel (baseRing F₀ v.valuationSubring) f).charts : Set (Subring F₀)), ∃ i,
      W'.comap (algebraMap (RatFunc K) F₀) = (gaussRat v (a i) (r i)).valuationSubring)
    {R₁ R₂ : Subring F₀} (hR₁ : R₁ ≤ baseRing F₀ v.valuationSubring) (hR : R₁ ≤ R₂)
    {n : ℕ} {g : Fin (n + 1) → F₀}
    (hp : (projModel R₂ g).points = ((gaussJoinModel v a c).normalization F₀).points)
    (l : Fin (n + 1)) :
    ProjScheme.LocallyDominates R₁ (RingHom.id F₀) (projChart R₂ g l).subtype f := by
  refine ProjScheme.locallyDominates_of_points (RingHom.id F₀) (fun y hy ↦ hR hy) ?_ l
  intro Q hQ
  rw [hp] at hQ
  obtain ⟨B, hB, hBQ⟩ := exists_chart_le_of_points hc hconv hred projModel_isProper
    projModel_isFiniteType hV' Q hQ
  obtain ⟨i, rfl⟩ := mem_projModel_charts.1 hB
  refine ⟨i, fun y hy ↦ hBQ ?_⟩
  exact (projChart_le ((hR₁).trans (base_le_projChart i)) fun j ↦ div_mem_projChart i j) hy

end Dom

end W10Dom

end SemistableReduction
