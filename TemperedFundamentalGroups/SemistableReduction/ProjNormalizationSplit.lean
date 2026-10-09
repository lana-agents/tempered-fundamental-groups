/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Component
import TemperedFundamentalGroups.SemistableReduction.ChartLocalizationSplit
import TemperedFundamentalGroups.SemistableReduction.ProjChartGerms

/-!
# Split nodes of the projective model codes (scheme level)

Blueprint §10.3.8 (split nodes for `ModelCode.IsSplit`).

* `projModelCode_hasSplitNodes`: if every chart `R[f j / f i]` of a projective model is split
  semistable at every prime (étale-locally `O[X]` or a split node), the model code
  `projModelCode O hf` has split nodes: a node point is not étale-locally `O[X]`
  (`ModelCode.IsNodePt`), so in the chart containing it it is a split node.
* `projChart_isSplitSemistable_of_normalization`, `exists_projModelCode_normalization_split`: the
  split forms of M9c (`exists_projModelCode_normalization`, with the same coordinates `g`).
* `exists_component_model_split`: the split form of `exists_component_model` (W10): given that
  the charts of the normalized tree model are split semistable (`W10.TreeChartsSplit`), the model
  code of the component has split nodes.
-/

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace SemistableReduction

open ZariskiModel ProjScheme

section Scheme

variable {O : Type u} [CommRing O] [IsLocalRing O] {F : Type u} [Field F] [Algebra O F]

/-- **Split nodes of projective models.** If every chart `R[f j / f i]` of the projective model
of `f` (with its `O`-algebra structure) is split semistable at every prime, the model code
`projModelCode O hf` has split nodes. -/
theorem projModelCode_hasSplitNodes {n : ℕ} {f : Fin (n + 1) → F} (R : Subring F)
    (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0) (ϖ : O)
    (h : ∀ i, letI := projChartAlgebra (f := f) R hR i;
      ∀ 𝔭 : Ideal (projChart R f i), 𝔭.IsPrime → IsSplitSemistableAt ϖ 𝔭) :
    TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ
      (projModelCode O hf) := by
  intro x hx
  have hi := (exists_mem_chartOpen (O := O) hf x).choose_spec
  set i := (exists_mem_chartOpen (O := O) hf x).choose
  refine ⟨chartOpen O hf i, isAffineOpen_chartOpen (O := O) hf i, hi, ?_⟩
  letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
    (projModelCode O hf) (chartOpen O hf i)
  letI := projChartAlgebra (f := f) R hR i
  set e := chartEquiv R hR hf i
  set P := ((isAffineOpen_chartOpen hf i).primeIdealOf ⟨x, hi⟩).asIdeal
  have hQ : (P.comap e.symm.toAlgHom.toRingHom).IsPrime := Ideal.comap_isPrime _ _
  have hs := IsSplitSemistableAt.of_etale_of_comap e.toAlgHom
    (RingHom.Etale.of_bijective e.bijective) (h i _ hQ)
  have hP : (P.comap e.symm.toAlgHom.toRingHom).comap e.toAlgHom.toRingHom = P := by
    ext y
    simp [Ideal.mem_comap]
  rw [hP] at hs
  rcases hs with hs | hs
  · exact absurd ⟨chartOpen O hf i, isAffineOpen_chartOpen (O := O) hf i, hi, hs⟩ hx.2
  · obtain ⟨m, C, _, g, f', 𝔮, hg, hf', h𝔮, hc, hO, -, -, hsurj⟩ := hs
    exact ⟨m, C, inferInstance, g, f', 𝔮, hg, hf', h𝔮, hc, hO, hsurj⟩

end Scheme

section Loc

/-- The localization of `A ⊆ W` at the center of `W` is the local ring `localAt A W`. -/
lemma locAt_centerIdeal {F : Type*} [Field F] (A : Subring F) (W : ValuationSubring F)
    (h : A ≤ W.toSubring) : locAt A (centerIdeal A W h) = localAt A W := by
  have hunit : ∀ b : A, b ∉ centerIdeal A W h ↔ W.valuation (b : F) = 1 := fun b ↦ by
    rw [mem_centerIdeal_iff, not_lt]
    exact ⟨fun hb ↦ le_antisymm ((W.valuation_le_one_iff _).2 (h b.2)) hb, fun hb ↦ hb.ge⟩
  ext x
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    have hb0 : (b : F) ≠ 0 := fun h0 ↦ hb (by
      rw [show b = 0 from Subtype.ext h0]; exact zero_mem _)
    refine ⟨b, b.2, (hunit b).1 hb, ?_⟩
    rw [div_mul_cancel₀ _ hb0]; exact a.2
  · rintro ⟨s, hs, hsW, hxs⟩
    have hs0 : s ≠ 0 := by rintro rfl; simp at hsW
    refine ⟨⟨x * s, hxs⟩, ⟨s, hs⟩, (hunit ⟨s, hs⟩).2 hsW, ?_⟩
    simp [mul_div_cancel_right₀ _ hs0]

/-- `locAt_centerIdeal` for a prime given as a center. -/
lemma locAt_eq_localAt {F : Type*} [Field F] {A : Subring F} {W : ValuationSubring F}
    {h : A ≤ W.toSubring} {Q : Ideal A} [Q.IsPrime] (hQ : centerIdeal A W h = Q) :
    locAt A Q = localAt A W := by
  subst hQ
  exact locAt_centerIdeal A W h

end Loc

section Semistable

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [Algebra v.valuationSubring F']
  [IsScalarTower v.valuationSubring K F'] {ι : Type*} [Fintype ι] [Nonempty ι] {f : ι → F}
  {κ : Type*} [Fintype κ] {g : κ → F'}

omit [Fintype κ] in
/-- If the charts of the normalization are split semistable (and of finite type), so are all
charts of `projModel g`. -/
theorem projChart_isSplitSemistable_of_normalization [Finite κ] (hg : ∀ l, g l ≠ 0)
    (hchart : ∀ j, ∃ l, projChart (baseRing F' v.valuationSubring) g l =
      normChart F' (projChart (baseRing F v.valuationSubring) f j))
    (hfin : ((projModel (baseRing F v.valuationSubring) f).normalization F').IsFiniteType)
    {ϖ : v.valuationSubring} (hϖ : IsLocalRing.maximalIdeal v.valuationSubring ≤ Ideal.span {ϖ})
    (hss : ∀ C ∈ ((projModel (baseRing F v.valuationSubring) f).normalization F').charts,
      ∀ [Algebra v.valuationSubring C], (∀ o, ((algebraMap v.valuationSubring C o : C) : F') =
        algebraMap v.valuationSubring F' o) → ∀ 𝔭 : Ideal C, 𝔭.IsPrime → IsSplitSemistableAt ϖ 𝔭)
    (l : κ) [Algebra v.valuationSubring (projChart (baseRing F' v.valuationSubring) g l)]
    (hl : ∀ o, ((algebraMap v.valuationSubring _ o :
      projChart (baseRing F' v.valuationSubring) g l) : F') = algebraMap v.valuationSubring F' o) :
    ∀ 𝔭 : Ideal (projChart (baseRing F' v.valuationSubring) g l), 𝔭.IsPrime →
      IsSplitSemistableAt ϖ 𝔭 := by
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
  have hBs : IsSplitSemistableAt ϖ (centerIdeal B W hBW) := hss B hBmem hBc _ inferInstance
  have := isSplitSemistableAt_of_localAt_eq hϖ hBc hl hRB (base_le_projChart l) sB sC hsB hsC hBW
    hCW he hBs
  rwa [hcen] at this

/-- **M9c, split form**: `exists_projModelCode_normalization`, and if the charts of the
normalization are split semistable at every prime, the model code has split nodes. The original
statement:
**Normalizations of projective models are projective model codes (M9c).** Let `M` be the
projective model of a finite nonempty family `f` of nonzero functions on `F` over `O`, and assume
its normalization `M'` in `F'` is of finite type (M8b). Then there are homogeneous coordinates
`g : Fin (n + 1) → F'` whose projective model has the charts of `M'` among its charts and the same
points as `M'`; and if the charts of `M'` are semistable (e.g. M7c and the local analysis W8), the
model code `projModelCode O g` (a closed subscheme of `ℙⁿ_O`) is semistable. -/
theorem exists_projModelCode_normalization_split (hf : ∀ i, f i ≠ 0)
    (hfin : ((projModel (baseRing F v.valuationSubring) f).normalization F').IsFiniteType) :
    ∃ (n : ℕ) (g : Fin (n + 1) → F') (hg : ∀ l, g l ≠ 0),
      ((projModel (baseRing F v.valuationSubring) f).normalization F').charts ⊆
        (projModel (baseRing F' v.valuationSubring) g).charts ∧
      (projModel (baseRing F' v.valuationSubring) g).points =
        ((projModel (baseRing F v.valuationSubring) f).normalization F').points ∧
      (∀ ϖ : v.valuationSubring,
        (∀ C ∈ ((projModel (baseRing F v.valuationSubring) f).normalization F').charts,
          ∀ [Algebra v.valuationSubring C], (∀ o, ((algebraMap v.valuationSubring C o : C) : F') =
            algebraMap v.valuationSubring F' o) → IsSemistable ϖ C) →
        TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ
          (ProjScheme.projModelCode v.valuationSubring hg)) ∧
      (∀ ϖ : v.valuationSubring, IsLocalRing.maximalIdeal v.valuationSubring ≤ Ideal.span {ϖ} →
        (∀ C ∈ ((projModel (baseRing F v.valuationSubring) f).normalization F').charts,
          ∀ [Algebra v.valuationSubring C], (∀ o, ((algebraMap v.valuationSubring C o : C) : F') =
            algebraMap v.valuationSubring F' o) → ∀ 𝔭 : Ideal C, 𝔭.IsPrime →
              IsSplitSemistableAt ϖ 𝔭) →
        TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ
          (ProjScheme.projModelCode v.valuationSubring hg)) ∧
      ∀ y : (ProjScheme.projModelCode v.valuationSubring hg).scheme,
        ∃ B ∈ ((projModel (baseRing F v.valuationSubring) f).normalization F').charts,
        ∃ (W : ValuationSubring F') (hBW : B ≤ W.toSubring),
          TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
              (ProjScheme.projModelCode v.valuationSubring hg)
              (ProjScheme.genericPt v.valuationSubring hg) y = (localAt B W : Set F') ∧
          ∀ [Algebra v.valuationSubring B], (∀ o, ((algebraMap v.valuationSubring B o : B) : F') =
            algebraMap v.valuationSubring F' o) →
            IsEtaleLocallyAt v.valuationSubring v.valuationSubring[X] (centerIdeal B W hBW) →
            TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSmoothPt
              (ProjScheme.projModelCode v.valuationSubring hg) y := by
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
  refine ⟨n, g, hg, fun C hC ↦ ?_, points_projModel_eq hg hchart, fun ϖ hss ↦ ?_,
    fun ϖ hϖ hsp ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨A, hA, rfl⟩ := mem_normalization_charts.1 hC
    obtain ⟨j, rfl⟩ := mem_projModel_charts.1 hA
    obtain ⟨l, hl⟩ := hchart j
    exact mem_projModel_charts.2 ⟨l, hl⟩
  · refine projModelCode_isSemistable _ range_algebraMap_eq_baseRing hg ϖ fun l ↦ ?_
    letI := ProjScheme.projChartAlgebra (f := g) _ (range_algebraMap_eq_baseRing (v := v)) l
    exact projChart_isSemistable_of_normalization hg hchart hfin hss l fun _ ↦ rfl
  · refine projModelCode_hasSplitNodes _ range_algebraMap_eq_baseRing hg ϖ fun l ↦ ?_
    letI := ProjScheme.projChartAlgebra (f := g) _ (range_algebraMap_eq_baseRing (v := v)) l
    exact projChart_isSplitSemistable_of_normalization hg hchart hfin hϖ hsp l fun _ ↦ rfl
  · -- the germs at `y` are a local ring of a chart of the normalization
    have hR' := range_algebraMap_eq_baseRing (v := v) (F' := F')
    obtain ⟨i, hi⟩ := exists_mem_chartOpen (O := v.valuationSubring) hg y
    rw [← opensRange_chartι (baseRing F' v.valuationSubring) hR' hg i] at hi
    obtain ⟨Q, rfl⟩ := hi
    obtain ⟨W, hCW, hcen⟩ := exists_centerIdeal_eq (projChart (baseRing F' v.valuationSubring) g i)
      Q.asIdeal
    obtain ⟨j, hBW, he⟩ := exists_localAt_projChart_eq hg hchart i hCW
    have hBmem : normChart F' (projChart (baseRing F v.valuationSubring) f j) ∈
        ((projModel (baseRing F v.valuationSubring) f).normalization F').charts :=
      mem_normalization_charts.2 ⟨_, mem_projModel_charts.2 ⟨j, rfl⟩, rfl⟩
    refine ⟨_, hBmem, W, hBW, ?_, ?_⟩
    · rw [germs_chartι (baseRing F' v.valuationSubring) hR' hg i Q, locAt_eq_localAt hcen, he]
    · intro _ hBc hsm
      letI := projChartAlgebra (f := g) (baseRing F' v.valuationSubring) hR' i
      obtain ⟨sB, hsB⟩ := hfin _ hBmem
      obtain ⟨sC, hsC⟩ := projModel_isFiniteType (R := baseRing F' v.valuationSubring) (f := g) _
        (mem_projModel_charts.2 ⟨i, rfl⟩)
      have hRB : baseRing F' v.valuationSubring ≤
          normChart F' (projChart (baseRing F v.valuationSubring) f j) :=
        ((projModel (baseRing F v.valuationSubring) f).normalization F').le_chart _ hBmem
      have h1 := isEtaleLocallyAt_of_localAt_eq hBc (fun _ ↦ rfl) hRB (base_le_projChart i) sB sC
        hsB hsC hBW hCW he hsm
      rw [hcen] at h1
      letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
        (projModelCode v.valuationSubring hg) (chartOpen v.valuationSubring hg i)
      have hU := isAffineOpen_chartOpen (O := v.valuationSubring) hg i
      have hy : chartι (baseRing F' v.valuationSubring) hR' hg i Q ∈
          chartOpen v.valuationSubring hg i := by
        rw [← opensRange_chartι (baseRing F' v.valuationSubring) hR' hg i]; exact ⟨Q, rfl⟩
      refine ⟨chartOpen v.valuationSubring hg i, hU, hy, ?_⟩
      let e := chartEquiv (baseRing F' v.valuationSubring) hR' hg i
      have hprime : hU.primeIdealOf ⟨_, hy⟩ = Spec.map e.toRingEquiv.toCommRingCatIso.hom Q := by
        apply hU.fromSpec.isOpenEmbedding.injective
        rw [IsAffineOpen.fromSpec_primeIdealOf]
        change chartι (baseRing F' v.valuationSubring) hR' hg i Q = _
        rw [chartι, Scheme.Hom.comp_apply]
      have h2 := IsEtaleLocallyAt.of_etale_of_comap e.toAlgHom
        (RingHom.Etale.of_bijective e.bijective) h1
      convert h2 using 1
      rw [hprime]
      ext b
      rw [Spec.map_apply]
      rfl

end Semistable

section Component

variable {E : Type u} [Field E] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation E Γ₀} [IsDiscreteValuationRing v.valuationSubring]
  {F₀ : Type u} [Field F₀] [Algebra E F₀] [Algebra (RatFunc E) F₀]
  [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
  [Algebra.IsSeparable (RatFunc E) F₀] [Algebra v.valuationSubring F₀]
  [IsScalarTower v.valuationSubring E F₀] [Algebra E[X] F₀] [IsScalarTower E[X] (RatFunc E) F₀]
  {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → E}

/-- **The semistable model of one component, split form**: `exists_component_model`, and if the
charts of the normalized tree model are split semistable at every prime, the model code has split
nodes (`ModelCode.HasSplitNodes`). -/
theorem exists_component_model_split (hc : ∀ i, c i ≠ 0) (hconv : GaussTree.IsConvex v a c)
    (hred : GaussTree.IsReduced v a c) (ϖ : v.valuationSubring)
    (hcharts : ∀ Cc ∈ ((gaussJoinModel v a c).normalization F₀).charts,
      ∀ [Algebra v.valuationSubring Cc], (∀ o, ((algebraMap v.valuationSubring Cc o : Cc) : F₀) =
        algebraMap v.valuationSubring F₀ o) → IsSemistable ϖ Cc)
    (hϖ : Irreducible ϖ)
    (hsplit : ∀ Cc ∈ ((gaussJoinModel v a c).normalization F₀).charts,
      ∀ [Algebra v.valuationSubring Cc], (∀ o, ((algebraMap v.valuationSubring Cc o : Cc) : F₀) =
        algebraMap v.valuationSubring F₀ o) → ∀ 𝔭 : Ideal Cc, 𝔭.IsPrime →
          IsSplitSemistableAt ϖ 𝔭)
    (D : Subring F₀) (hD : ∀ z : F₀, IsIntegral E[X] z → z ∈ D)
    (hRD : (algebraMap v.valuationSubring F₀).range ≤ D) :
    ∃ (n : ℕ) (g : Fin (n + 1) → F₀) (hg : ∀ l, g l ≠ 0),
      (projModel (algebraMap v.valuationSubring F₀).range g).points =
        ((gaussJoinModel v a c).normalization F₀).points ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ
        (projModelCode v.valuationSubring hg) ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ
        (projModelCode v.valuationSubring hg) ∧
      (∀ y : (projModelCode v.valuationSubring hg).scheme,
        ∃ B ∈ ((gaussJoinModel v a c).normalization F₀).charts,
        ∃ (W : ValuationSubring F₀) (hBW : B ≤ W.toSubring),
          TemperedFundamentalGroups.SemistableReduction.ModelCode.germs
              (projModelCode v.valuationSubring hg) (genericPt v.valuationSubring hg) y =
            (localAt B W : Set F₀) ∧
          ∀ [Algebra v.valuationSubring B], (∀ o, ((algebraMap v.valuationSubring B o : B) : F₀) =
            algebraMap v.valuationSubring F₀ o) →
            IsEtaleLocallyAt v.valuationSubring v.valuationSubring[X] (centerIdeal B W hBW) →
            TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSmoothPt
              (projModelCode v.valuationSubring hg) y) ∧
      LocallyDominates (algebraMap v.valuationSubring F₀).range (RingHom.id F₀) D.subtype g := by
  classical
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.valuationSubring
  have hfin := gaussJoinModel_normalization_isFiniteType (F' := F₀) hc hconv hred
    (eq_or_eq_top_of_le hϖ₀)
  have hcz : ∀ i, gaussCoord (a i) (c i) ≠ 0 := fun i ↦ gaussCoord_ne_zero (hc i)
  rw [gaussJoinModel_eq_projModel (v := v) hc] at hfin hcharts hsplit ⊢
  obtain ⟨n, g, hg, hch, hpts, hss, hsp, hbr⟩ := exists_projModelCode_normalization_split
    (F := RatFunc E) (f := segre fun i ↦ gaussCoord (a i) (c i)) (segre_ne_zero hcz) hfin
  have hR := range_algebraMap_eq_baseRing (v := v) (F' := F₀)
  refine ⟨n, g, hg, ?_, hss ϖ hcharts, hsp ϖ hϖ.maximalIdeal_eq.le hsplit, hbr, ?_⟩
  · rw [hR]; exact hpts
  · -- the root chart: the normalization of the Segre chart at `σ = false`
    set A := projChart (baseRing (RatFunc E) v.valuationSubring)
      (segre fun i ↦ gaussCoord (a i) (c i)) (fun _ ↦ false) with hAdef
    have hAeq : A = segreChart v (fun i ↦ gaussCoord (a i) (c i)) (fun _ ↦ false) :=
      projChart_segre hcz _
    have hA : normChart F₀ A ∈
        ((projModel (baseRing (RatFunc E) v.valuationSubring)
          (segre fun i ↦ gaussCoord (a i) (c i))).normalization F₀).charts :=
      mem_normalization_charts.2 ⟨A, mem_projModel_charts.2 ⟨_, rfl⟩, rfl⟩
    obtain ⟨l, hl⟩ := mem_projModel_charts.1 (hch hA)
    refine locallyDominates_root D hD hRD (A := A) (fun t ht ↦ ?_) (l := l) ?_
    · rw [hAeq] at ht
      exact mem_range_of_mem_segreChart (fun i ↦ ⟨gaussLin (a i) (c i), rfl⟩) ht
    · rw [hR]; exact hl

end Component

end SemistableReduction
