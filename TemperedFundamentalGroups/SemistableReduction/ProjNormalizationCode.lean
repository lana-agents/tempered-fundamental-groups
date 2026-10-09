/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjNormalization
import TemperedFundamentalGroups.SemistableReduction.ProjScheme
import TemperedFundamentalGroups.SemistableReduction.ChartLocalization
import TemperedFundamentalGroups.SemistableReduction.SegreModel

/-!
# Normalizations of projective models are projective model codes

Blueprint §9.6 (W5), layer M9c. Let `O` be a valuation subring of `K` (`O = v.valuationSubring`),
`F ⊇ K` and `F'/F` fields, and `f : ι → F` a finite nonempty family of nonzero functions. If the
normalization `M'` of the projective model `M = projModel O f` in `F'` is of finite type (M8b: `O`
noetherian and `F'/F` finite separable), then there are homogeneous coordinates
`g : Fin (n + 1) → F'` (`normCoord`: the products `f k f i ^ N` and `b f i ^ (N + 1)` for
generators `b` of the charts of `M'`, `ProjNormalization.lean`) such that

* every chart of `M'` is a chart of `projModel O g` (`projChart_normCoord`), and the two models
  have the same points (`points_projModel_normCoord`): the normalization *is* the projective model
  of `g`;
* if the charts of `M'` are semistable, so is the model code `projModelCode O g` (a closed
  subscheme of `ℙⁿ_O`, the form of W10): `exists_projModelCode_normalization`.

This applies to the tree of projective lines: `gaussJoinModel v a c` is the projective model of a
Segre family (`gaussJoinModel_eq_projModel`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace SemistableReduction

open ZariskiModel

/-- Reindexing a family along an equivalence does not change its charts. -/
lemma projChart_comp_equiv {F : Type*} [Field F] {R : Subring F} {κ κ' : Type*} (g : κ → F)
    (e : κ' ≃ κ) (i : κ') : projChart R (g ∘ e) i = projChart R g (e i) := by
  unfold projChart
  congr 2
  exact e.surjective.range_comp (fun l ↦ g l / g (e i))

section Points

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] {O : ValuationSubring K} {ι : Type*} [Fintype ι]
  [Nonempty ι] {f : ι → F} {κ : Type*} [Fintype κ] {g : κ → F'}

omit [Fintype ι] [Fintype κ] in
/-- If every chart of the normalization of `projModel f` is a chart of `projModel g`, then every
local ring of a chart of `projModel g` is the local ring of a chart of the normalization. -/
lemma exists_localAt_projChart_eq [Finite ι] [Finite κ] (hg : ∀ l, g l ≠ 0)
    (hchart : ∀ j, ∃ l, projChart (baseRing F' O) g l = normChart F' (projChart (baseRing F O) f j))
    (l : κ) {W : ValuationSubring F'} (hW : projChart (baseRing F' O) g l ≤ W.toSubring) :
    ∃ j, normChart F' (projChart (baseRing F O) f j) ≤ W.toSubring ∧
      localAt (projChart (baseRing F' O) g l) W =
        localAt (normChart F' (projChart (baseRing F O) f j)) W := by
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  have hRW : baseRing F' O ≤ W.toSubring := (base_le_projChart l).trans hW
  obtain ⟨A, hA, hAW⟩ := projModel_isProper (R := baseRing F O) (f := f) _ (baseRing_le_comap hRW)
  obtain ⟨j, rfl⟩ := mem_projModel_charts.1 hA
  have hBW := (normChart_le_iff _ W).2 hAW
  obtain ⟨l', hl'⟩ := hchart j
  have : Nonempty κ := ⟨l⟩
  refine ⟨j, hBW, ?_⟩
  rw [← hl', ← center_eq (projModel_isProper (f := g)) (projModel_isSeparated hg) hRW
    (mem_projModel_charts.2 ⟨l, rfl⟩) hW,
    center_eq (projModel_isProper (f := g)) (projModel_isSeparated hg) hRW
    (mem_projModel_charts.2 ⟨l', rfl⟩) (hl' ▸ hBW)]

/-- The projective model of `g` and the normalization of `projModel f` have the same points. -/
theorem points_projModel_eq (hg : ∀ l, g l ≠ 0)
    (hchart : ∀ j, ∃ l,
      projChart (baseRing F' O) g l = normChart F' (projChart (baseRing F O) f j)) :
    (projModel (baseRing F' O) g).points =
      ((projModel (baseRing F O) f).normalization F').points := by
  ext B
  constructor
  · rintro ⟨C, hC, W, hCW, rfl⟩
    obtain ⟨l, rfl⟩ := mem_projModel_charts.1 hC
    obtain ⟨j, hBW, he⟩ := exists_localAt_projChart_eq hg hchart l hCW
    exact ⟨_, mem_normalization_charts.2 ⟨_, mem_projModel_charts.2 ⟨j, rfl⟩, rfl⟩, W, hBW,
      he.symm⟩
  · rintro ⟨C, hC, W, hCW, rfl⟩
    obtain ⟨A, hA, rfl⟩ := mem_normalization_charts.1 hC
    obtain ⟨j, rfl⟩ := mem_projModel_charts.1 hA
    obtain ⟨l, hl⟩ := hchart j
    exact ⟨_, mem_projModel_charts.2 ⟨l, hl⟩, W, hCW, rfl⟩

end Points

section Semistable

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [Algebra v.valuationSubring F']
  [IsScalarTower v.valuationSubring K F'] {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → F}
  {κ : Type*} [Fintype κ] {g : κ → F'}

lemma range_algebraMap_eq_baseRing :
    (algebraMap v.valuationSubring F').range = baseRing F' v.valuationSubring := by
  ext x
  constructor
  · rintro ⟨o, rfl⟩
    rw [IsScalarTower.algebraMap_apply v.valuationSubring K F']
    exact ⟨o, o.2, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨o, ho⟩, ?_⟩
    rw [IsScalarTower.algebraMap_apply v.valuationSubring K F']
    rfl

omit [Fintype κ] in
/-- If the charts of the normalization are semistable (and of finite type), so are all charts of
`projModel g`. -/
theorem projChart_isSemistable_of_normalization [Finite κ] (hg : ∀ l, g l ≠ 0)
    (hchart : ∀ j, ∃ l, projChart (baseRing F' v.valuationSubring) g l =
      normChart F' (projChart (baseRing F v.valuationSubring) f j))
    (hfin : ((projModel (baseRing F v.valuationSubring) f).normalization F').IsFiniteType)
    {ϖ : v.valuationSubring}
    (hss : ∀ C ∈ ((projModel (baseRing F v.valuationSubring) f).normalization F').charts,
      ∀ [Algebra v.valuationSubring C], (∀ o, ((algebraMap v.valuationSubring C o : C) : F') =
        algebraMap v.valuationSubring F' o) → IsSemistable ϖ C)
    (l : κ) [Algebra v.valuationSubring (projChart (baseRing F' v.valuationSubring) g l)]
    (hl : ∀ o, ((algebraMap v.valuationSubring _ o :
      projChart (baseRing F' v.valuationSubring) g l) : F') = algebraMap v.valuationSubring F' o) :
    SemistableReduction.IsSemistable ϖ (projChart (baseRing F' v.valuationSubring) g l) := by
  have := Fintype.ofFinite κ
  intro 𝔭 h𝔭
  obtain ⟨W, hCW, hcen⟩ := exists_centerIdeal_eq _ 𝔭
  obtain ⟨j, hBW, he⟩ := exists_localAt_projChart_eq hg hchart l hCW
  set B := normChart F' (projChart (baseRing F v.valuationSubring) f j)
  have hBmem : B ∈ ((projModel (baseRing F v.valuationSubring) f).normalization F').charts :=
    mem_normalization_charts.2 ⟨_, mem_projModel_charts.2 ⟨j, rfl⟩, rfl⟩
  have hRB : baseRing F' v.valuationSubring ≤ B :=
    ((projModel (baseRing F v.valuationSubring) f).normalization F').le_chart B hBmem
  letI : Algebra v.valuationSubring B := chartAlgebra hRB
  have hBc : ∀ o, ((algebraMap v.valuationSubring B o : B) : F') =
      algebraMap v.valuationSubring F' o := fun _ ↦ rfl
  obtain ⟨sB, hsB⟩ := hfin B hBmem
  obtain ⟨sC, hsC⟩ := projModel_isFiniteType (R := baseRing F' v.valuationSubring) (f := g) _
    (mem_projModel_charts.2 ⟨l, rfl⟩)
  have hBs : IsSemistableAt ϖ (centerIdeal B W hBW) := hss B hBmem hBc _ inferInstance
  have := isSemistableAt_of_localAt_eq hBc hl hRB (base_le_projChart l) sB sC hsB hsC hBW hCW he hBs
  rwa [hcen] at this

/-- **Normalizations of projective models are projective model codes (M9c).** Let `M` be the
projective model of a finite nonempty family `f` of nonzero functions on `F` over `O`, and assume
its normalization `M'` in `F'` is of finite type (M8b). Then there are homogeneous coordinates
`g : Fin (n + 1) → F'` whose projective model has the charts of `M'` among its charts and the same
points as `M'`; and if the charts of `M'` are semistable (e.g. M7c and the local analysis W8), the
model code `projModelCode O g` (a closed subscheme of `ℙⁿ_O`) is semistable. -/
theorem exists_projModelCode_normalization (hf : ∀ i, f i ≠ 0)
    (hfin : ((projModel (baseRing F v.valuationSubring) f).normalization F').IsFiniteType) :
    ∃ (n : ℕ) (g : Fin (n + 1) → F') (hg : ∀ l, g l ≠ 0),
      ((projModel (baseRing F v.valuationSubring) f).normalization F').charts ⊆
        (projModel (baseRing F' v.valuationSubring) g).charts ∧
      (projModel (baseRing F' v.valuationSubring) g).points =
        ((projModel (baseRing F v.valuationSubring) f).normalization F').points ∧
      ∀ ϖ : v.valuationSubring,
        (∀ C ∈ ((projModel (baseRing F v.valuationSubring) f).normalization F').charts,
          ∀ [Algebra v.valuationSubring C], (∀ o, ((algebraMap v.valuationSubring C o : C) : F') =
            algebraMap v.valuationSubring F' o) → IsSemistable ϖ C) →
        TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ
          (ProjScheme.projModelCode v.valuationSubring hg) := by
  classical
  -- generators of the charts `B_j` over `A_j`
  have hgen (j : ι) : ∃ s : Finset F', normChart F' (projChart (baseRing F v.valuationSubring) f j)
      = Subring.closure (((projChart (baseRing F v.valuationSubring) f j).map
        (algebraMap F F') : Set F') ∪ s) := by
    obtain ⟨s, hs⟩ := hfin _ (mem_normalization_charts.2
      ⟨_, mem_projModel_charts.2 ⟨j, rfl⟩, rfl⟩)
    refine ⟨s, le_antisymm ?_ ?_⟩
    · rw [hs]
      refine Subring.closure_mono (Set.union_subset_union_left _ ?_)
      rw [← map_baseRing (F := F)]
      exact subring_map_mono (base_le_projChart j) _
    · refine Subring.closure_le.2 (Set.union_subset (map_le_normChart _) fun b hb ↦ ?_)
      rw [hs]
      exact Subring.subset_closure (Or.inr hb)
  choose s hs using hgen
  set g₀ := normCoord (baseRing F v.valuationSubring) s hf
  have hg₀ : ∀ l, g₀ l ≠ 0 := normCoord_ne_zero hf
  have hR : (baseRing F v.valuationSubring).map (algebraMap F F') =
      baseRing F' v.valuationSubring := map_baseRing
  have hchart₀ (j : ι) : projChart (baseRing F' v.valuationSubring) g₀ (.inl (j, j)) =
      normChart F' (projChart (baseRing F v.valuationSubring) f j) := by
    rw [← hR]
    exact projChart_normCoord hf hs j
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Fintype.card_ne_zero (α := NormIdx s))
  let e : Fin (n + 1) ≃ NormIdx s := ((Fintype.equivFin (NormIdx s)).trans (finCongr hn)).symm
  set g := g₀ ∘ e
  have hg : ∀ l, g l ≠ 0 := fun l ↦ hg₀ (e l)
  have hcharte (l : Fin (n + 1)) : projChart (baseRing F' v.valuationSubring) g l =
      projChart (baseRing F' v.valuationSubring) g₀ (e l) := projChart_comp_equiv g₀ e l
  have hchart (j : ι) : ∃ l, projChart (baseRing F' v.valuationSubring) g l =
      normChart F' (projChart (baseRing F v.valuationSubring) f j) :=
    ⟨e.symm (.inl (j, j)), by rw [hcharte, e.apply_symm_apply, hchart₀]⟩
  refine ⟨n, g, hg, fun C hC ↦ ?_, points_projModel_eq hg hchart, fun ϖ hss ↦ ?_⟩
  · obtain ⟨A, hA, rfl⟩ := mem_normalization_charts.1 hC
    obtain ⟨j, rfl⟩ := mem_projModel_charts.1 hA
    obtain ⟨l, hl⟩ := hchart j
    exact mem_projModel_charts.2 ⟨l, hl⟩
  · refine projModelCode_isSemistable _ range_algebraMap_eq_baseRing hg ϖ fun l ↦ ?_
    letI := ProjScheme.projChartAlgebra (f := g) _ (range_algebraMap_eq_baseRing (v := v)) l
    exact projChart_isSemistable_of_normalization hg hchart hfin hss l fun _ ↦ rfl

end Semistable

section Gauss

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

lemma gaussCoord_ne_zero {a c : K} (hc : c ≠ 0) : gaussCoord a c ≠ 0 := by
  rw [gaussCoord, gaussLin]
  refine (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).2
    (mul_ne_zero ?_ (Polynomial.X_sub_C_ne_zero a))
  simpa using hc

/-- **The tree of projective lines is projective**: `gaussJoinModel v a c` is the projective model
of the Segre family of the Gauss coordinates (so M9c applies to its normalizations). -/
theorem gaussJoinModel_eq_projModel {ι : Type*} [Fintype ι] [DecidableEq ι] {a c : ι → K}
    (hc : ∀ i, c i ≠ 0) :
    gaussJoinModel v a c = projModel (baseRing (RatFunc K) v.valuationSubring)
      (segre fun i ↦ gaussCoord (a i) (c i)) :=
  lines_eq_projModel fun i ↦ gaussCoord_ne_zero (hc i)

end Gauss

end SemistableReduction
