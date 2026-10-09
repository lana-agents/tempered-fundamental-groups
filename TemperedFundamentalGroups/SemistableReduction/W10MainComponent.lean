/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Main
import TemperedFundamentalGroups.SemistableReduction.W10ComponentTree
import TemperedFundamentalGroups.SemistableReduction.W10LineX
import TemperedFundamentalGroups.SemistableReduction.W10TreeUnfolded
import TemperedFundamentalGroups.SemistableReduction.StrongComponentAS
import TemperedFundamentalGroups.SemistableReduction.W10TreeUnfoldedProof
import TemperedFundamentalGroups.SemistableReduction.StrongAProof
import TemperedFundamentalGroups.SemistableReduction.W10RouteFinal

/-!
# W10 with components: `Statement.StrongComponentAS` (modulo Zariski connectedness)

Blueprint §10.3.8. `strongComponentAS_of_W7_of_tree`: the strengthened copy of
`strongA_of_W7_of_tree` (W10Main) on the given `G`-invariant x-line, from W7, the descent of the
tree charts (G4), `W10.TreeComponentsUnfolded` (split nodes, no loops, unfolded component models)
and `Statement.ZariskiConnected` (connected special fibres of the summands);
`Statement.strongComponentAS_of`: from `ZariskiConnected` alone. The dimension clause
is unconditional (`ModelCode.topologicalKrullDim_le_one_of_iso`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits Polynomial TensorProduct IsLocalRing

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields ProjScheme ZariskiModel W10Discs

attribute [local instance] polyAlgebra

set_option maxHeartbeats 800000 in
-- a single long proof: the W10 assembly with the component inputs (instance-heavy applications)
theorem strongComponentAS_of_W7_of_tree (h7 : W7.Statement.{u, u})
    (htree : W10.TreeChartsSemistable.{u}) (hU : W10.TreeComponentsUnfolded.{u})
    (hZ : TemperedFundamentalGroups.SemistableReduction.Statement.ZariskiConnected.{u}) :
    TemperedFundamentalGroups.SemistableReduction.Statement.StrongComponentAS.{u} := by
  intro K _ _ O _ _ _ p hp hpO R _ _ _ _ hR x hfin B _ _ _ _ _ _ G _ _ _ _ _ _ hequiv hxG I _ c₀
    j₀ hj₀
  -- the x-line (given)
  letI := W10Line.lineAlgebra K (B := B) x
  haveI := W10Line.finite_line (K := K) (B := B) hfin
  haveI := W10Line.isTorsionFree_line (K := K) (B := B) hR hfin
  haveI := W10Line.isScalarTower_line (K := K) (B := B) x
  haveI := W10Line.smooth_B (K := K) (R := R) (B := B)
  -- coordinates of the given models over `K`
  have hcoord := fun i 𝔫 ↦ exists_coordsK O (c₀ i) (j₀ i) (hj₀ i) 𝔫
  choose nK fK hfK ιK hιK hιOK using hcoord
  -- the norms
  letI := DVRNorm.normedField O
  letI := DVRNorm.normedFieldAlgCl O
  haveI := DVRNorm.isUltrametricDist_algCl O
  -- the discs `V₀`
  let chartsU : ∀ 𝔪' : MaximalSpectrum (LX K (AlgebraicClosure K) B),
      Set (Subring (Comp K (AlgebraicClosure K) B 𝔪')) :=
    fun 𝔪' ↦ ⋃ i, W10Gal.chartsC O B (fK i) 𝔪'
  haveI : Finite I := ‹Finite I›
  have hfinU : ∀ 𝔪', (RT (NormedField.valuation (K := AlgebraicClosure K)).valuationSubring
      (chartsU 𝔪')).Finite := fun 𝔪' ↦
    (Set.finite_iUnion fun i ↦ W10Gal.hfin_chartsC O B (fK i) 𝔪').subset (RT_iUnion_subset _ _)
  have htrU : ∀ τ ∈ Set.range (fun τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K ↦
      τ.toRingEquiv), ∃ (π : MaximalSpectrum (LX K (AlgebraicClosure K) B) →
        MaximalSpectrum (LX K (AlgebraicClosure K) B))
        (σ : ∀ k, Comp K _ B (π k) ≃+* Comp K _ B k),
        (∀ k φ, σ k (algebraMap (RatFunc (AlgebraicClosure K)) _ φ) =
          algebraMap (RatFunc (AlgebraicClosure K)) _
            (ratFuncMap (τ : AlgebraicClosure K →+* AlgebraicClosure K) φ)) ∧
        ∀ k, ∀ Bc ∈ chartsU k, Bc.comap (σ k : Comp K _ B (π k) →+* _) ∈ chartsU (π k) := by
    rintro _ ⟨τ, rfl⟩
    refine ⟨W10Gal.galMax B τ, W10Gal.galEquiv B τ, fun k φ ↦ W10Gal.galEquiv_algebraMap B τ k φ,
      fun k Bc hBc ↦ ?_⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hBc
    exact Set.mem_iUnion.2 ⟨i, W10Gal.comap_mem_chartsC O B (fK i) τ k Bc hi⟩
  obtain ⟨n₀, a₀, c₀', hc₀', hV0, hstab0⟩ := exists_V0 (Comp K (AlgebraicClosure K) B) chartsU
    hfinU _ (W10Gal.hinv_gal) (W10Gal.hiso_gal O) htrU
  have hst : ∀ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      W7.DiscsLE (fun k ↦ τ (a₀ k)) c₀' a₀ c₀' := fun τ ↦ by
    have h := hstab0 τ.toRingEquiv ⟨τ, rfl⟩
    simpa only [AlgEquiv.coe_ringEquiv] using h
  -- W7
  obtain ⟨ιt, _, _, a, c, hc, hconv, hred, hle, hss, hstabT⟩ :=
    W10Apply.exists_semistableTree O hp hpO B h7
      (fun 𝔪 ↦ W10DefinedOver.definedOverDVR O (Comp K (AlgebraicClosure K) B 𝔪)) a₀ c₀' hc₀' hst
  -- G4 on every component over `C`
  have hT := fun 𝔪' ↦ W10Gen.exists_generators_comp K B (AlgebraicClosure K) 𝔪'
  choose T hTgen hTK using hT
  have hS := fun 𝔪' ↦ htree (AlgebraicClosure K) p hp (DVRNorm.norm_natCast_lt_one O hpO)
    (Comp K (AlgebraicClosure K) B 𝔪') ιt a c hc hconv hred (hss 𝔪') (T 𝔪') (hTgen 𝔪')
  choose S hS using hS
  have hS' := fun 𝔪' ↦ hU (AlgebraicClosure K) p hp (DVRNorm.norm_natCast_lt_one O hpO)
    (Comp K (AlgebraicClosure K) B 𝔪') ιt a c hc hconv hred (hss 𝔪') (T 𝔪') (hTgen 𝔪')
  choose S' hS' using hS'
  -- the comparison of the components
  obtain ⟨Scmp, hcmp⟩ := exists_finset_compare_of_smooth K (C := AlgebraicClosure K) B
  -- the field `E`
  haveI : Fintype (MaximalSpectrum (LX K (AlgebraicClosure K) B)) := Fintype.ofFinite _
  classical
  let Sall : Finset (AlgebraicClosure K) :=
    (((Finset.univ.biUnion S ∪ Finset.univ.biUnion S') ∪ Scmp) ∪
    Finset.univ.image a) ∪ Finset.univ.image c
  obtain ⟨E, hEfin, hEgal, hSE⟩ := W10Apply.exists_isGalois Sall
  haveI hST : IsScalarTower K E (AlgebraicClosure K) := inferInstance
  have halg₀ : Algebra.IsAlgebraic E (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.tower_top (K := K) E
  have haE : ∀ i, a i ∈ E := fun i ↦ hSE (by simp [Sall])
  have hcE : ∀ i, c i ∈ E := fun i ↦ hSE (by simp [Sall])
  have hSmE : ∀ 𝔪', (S 𝔪' : Set (AlgebraicClosure K)) ⊆ E := fun 𝔪' z hz ↦
    hSE (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_biUnion.2 ⟨𝔪', Finset.mem_univ _, hz⟩))))))
  have hSmE' : ∀ 𝔪', (S' 𝔪' : Set (AlgebraicClosure K)) ⊆ E := fun 𝔪' z hz ↦
    hSE (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_biUnion.2 ⟨𝔪', Finset.mem_univ _, hz⟩))))))
  have hcmpE := hcmp E fun z hz ↦ hSE (Finset.mem_coe.2 (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_union_right _ hz))))
  letI := W10Apply.normedFieldE O E
  haveI := W10Apply.isUltrametricDist_E O E
  haveI := W10Apply.completeSpace_E O E
  haveI := W10Gal.isDiscreteValuationRing_E O E
  haveI : PerfectField (ResidueField (NormedField.valuation (K := E)).valuationSubring) := by
    rw [W10Gal.valuationSubring_E O E]
    exact W10Gal.perfectField_residueField_OE O E
  -- the tree over `E`
  let φ : E →+* AlgebraicClosure K := algebraMap E (AlgebraicClosure K)
  have hφ : ∀ e, ‖φ e‖ = ‖e‖ := fun e ↦ (W10Apply.norm_coe O E e).symm
  let aE : ιt → E := fun i ↦ ⟨a i, haE i⟩
  let cE : ιt → E := fun i ↦ ⟨c i, hcE i⟩
  have haE' : ∀ i, φ (aE i) = a i := fun _ ↦ rfl
  have hcE' : ∀ i, φ (cE i) = c i := fun _ ↦ rfl
  have hcE0 : ∀ i, cE i ≠ 0 := fun i h ↦ hc i (by rw [← hcE' i, h, map_zero])
  have hvE : (NormedField.valuation (K := E)).valuationSubring = W10Apply.OE O E :=
    W10Gal.valuationSubring_E O E
  have hO' : (NormedField.valuation (K := E)).valuationSubring.comap (algebraMap K E) = O := by
    rw [hvE]; exact W10Apply.comap_OE O E
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible
    (NormedField.valuation (K := E)).valuationSubring
  have hσO' : ∀ σ : E ≃ₐ[K] E, ∀ y ∈ (NormedField.valuation (K := E)).valuationSubring,
      σ y ∈ (NormedField.valuation (K := E)).valuationSubring := by
    rw [hvE]; exact fun σ y hy ↦ W10Apply.algEquiv_mem_OE O E σ hy
  have hext : ∀ σ : E ≃ₐ[K] E, ∃ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      ∀ e, τ (φ e) = φ (σ e) := fun σ ↦ W10Apply.exists_extend E σ
  have hiso : ∀ σ : E ≃ₐ[K] E, ∀ e, NormedField.valuation (σ e) = NormedField.valuation e := by
    intro σ e
    obtain ⟨τ, hτ⟩ := hext σ
    rw [NormedField.valuation_apply, NormedField.valuation_apply]
    refine NNReal.eq ?_
    simp only [coe_nnnorm]
    rw [← hφ, ← hφ, ← hτ, DVRNorm.norm_algEquiv_apply]
  -- generators of `O'` over `O`
  obtain ⟨r, θ, hθ0, hθmem, hθint, hθgen⟩ := W10Apply.exists_generators O E
  let θ' : Fin r → (NormedField.valuation (K := E)).valuationSubring :=
    fun s ↦ ⟨θ s, by rw [hvE]; exact hθmem s⟩
  have hθint' : ∀ s, letI := algebraOO' O E (NormedField.valuation (K := E)).valuationSubring hO'
      IsIntegral O (θ' s) := by
    intro s
    letI := algebraOO' O E (NormedField.valuation (K := E)).valuationSubring hO'
    let f : (NormedField.valuation (K := E)).valuationSubring →ₐ[O] E :=
      { (NormedField.valuation (K := E)).valuationSubring.subtype with commutes' := fun _ ↦ rfl }
    exact (isIntegral_algHom_iff f Subtype.val_injective).1 (hθint s)
  have hθgen' : ∀ y : (NormedField.valuation (K := E)).valuationSubring, (y : E) ∈
      Subring.closure ((((algebraMap K E).comp O.subtype).range : Set E) ∪
        Set.range fun s ↦ (θ' s : E)) := by
    intro y
    have hy : (y : E) ∈ W10Apply.OE O E := hvE ▸ y.2
    exact hθgen hy
  -- the tree over `E` is convex, reduced and `Gal(E/K)`-stable
  have hconvE := isConvex_descent φ hφ haE' hcE' hconv
  have hredE := isReduced_descent φ hφ haE' hcE' hred
  have hstabE : ∀ σ : E ≃ₐ[K] E, ∀ i, ∃ i', NormedField.valuation (σ (cE i)) =
      NormedField.valuation (cE i') ∧
      NormedField.valuation (σ (aE i) - aE i') ≤ NormedField.valuation (cE i') := by
    intro σ i
    obtain ⟨τ, hτ⟩ := hext σ
    exact stab_descent φ hφ haE' hcE' (σ : E →+* E) (τ : AlgebraicClosure K →+* AlgebraicClosure K)
      hτ (DVRNorm.norm_algEquiv_apply O τ) (hstabT τ) i
  -- the charts of the normalized tree models over `E` are semistable (G4)
  have halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E (AlgebraicClosure K) := halg₀
  have hSφ : ∀ 𝔪', (S 𝔪' : Set (AlgebraicClosure K)) ⊆ Set.range φ := fun 𝔪' z hz ↦
    ⟨⟨z, hSmE 𝔪' hz⟩, rfl⟩
  have hSφ' : ∀ 𝔪', (S' 𝔪' : Set (AlgebraicClosure K)) ⊆ Set.range φ := fun 𝔪' z hz ↦
    ⟨⟨z, hSmE' 𝔪' hz⟩, rfl⟩
  have hTχ : ∀ 𝔪', (T 𝔪' : Set _) ⊆ Set.range (compMap K E B (AlgebraicClosure K) 𝔪') :=
    fun 𝔪' t ht ↦ W10Gen.range_compBMap_le_range_compMap K B E 𝔪' (hTK 𝔪' t ht)
  have hcharts : ∀ 𝔪 : MaximalSpectrum (LX K E B),
      ∀ Cc ∈ ((gaussJoinModel (NormedField.valuation (K := E)) aE cE).normalization
        (Comp K E B 𝔪)).charts,
        ∀ [Algebra (NormedField.valuation (K := E)).valuationSubring Cc],
          (∀ o, ((algebraMap (NormedField.valuation (K := E)).valuationSubring Cc o : Cc) :
            Comp K E B 𝔪) = algebraMap (NormedField.valuation (K := E)).valuationSubring
              (Comp K E B 𝔪) o) → IsSemistable ϖ' Cc := by
    intro 𝔪
    obtain ⟨𝔪', rfl⟩ := hcmpE.1.2 𝔪
    exact hS 𝔪' E φ hφ (hSφ 𝔪') halg aE cE haE' hcE' (Comp K E B (contrMax K E B _ 𝔪'))
      (compMap K E B (AlgebraicClosure K) 𝔪') (W10Gal.hχ_compMap B E 𝔪') (hcmpE.2 𝔪').2
      (hTχ 𝔪') ϖ' hϖ'
  -- the residue-transcendental centres of the given models are vertices
  haveI := halg₀
  have hcomapν : (NormedField.valuation (K := AlgebraicClosure K)).valuationSubring.comap
      (algebraMap E (AlgebraicClosure K)) = (NormedField.valuation (K := E)).valuationSubring := by
    rw [hvE]; exact W10Gal.comap_OC_eq O E
  have hV' : ∀ i 𝔪, ∀ W' ∈ RT (NormedField.valuation (K := E)).valuationSubring
      ((projModel (baseRing (Comp K E B 𝔪) (NormedField.valuation (K := E)).valuationSubring)
        (fE (f := fK i) 𝔪)).charts : Set (Subring (Comp K E B 𝔪))), ∃ j,
      W'.comap (algebraMap (RatFunc E) (Comp K E B 𝔪)) = (gaussRat (NormedField.valuation (K := E))
        (aE j) (Units.mk0 (NormedField.valuation (cE j))
          ((Valuation.ne_zero_iff _).2 (hcE0 j)))).valuationSubring := by
    intro i 𝔪 W' hW'
    obtain ⟨𝔪', rfl⟩ := hcmpE.1.2 𝔪
    have hW'' : W' ∈ RT ((NormedField.valuation (K := AlgebraicClosure K)).valuationSubring.comap
        (algebraMap E (AlgebraicClosure K)))
        (W10Gal.chartsM B (fK i) (W10Apply.OE O E) (contrMax K E B (AlgebraicClosure K) 𝔪')) := by
      rw [hcomapν]
      convert hW' using 2
      ext Bc
      rw [W10Gal.chartsM, Finset.mem_coe, mem_projModel_charts, hvE]
      rfl
    obtain ⟨W, hW, hWχ⟩ := W10Dom.exists_mem_RT_comap_eq (W10Gal.hχ_compMap B E 𝔪')
      (W10Gal.huniq_E O E) (W10Gal.hY_compMap O B (fK i) E 𝔪') hW''
    have hWU : W ∈ RT (NormedField.valuation (K := AlgebraicClosure K)).valuationSubring
        (chartsU 𝔪') :=
      RT_mono _ (Set.subset_iUnion (fun i ↦ W10Gal.chartsC O B (fK i) 𝔪') i) hW
    obtain ⟨k, hk⟩ := hV0 𝔪' W hWU
    obtain ⟨j, hj⟩ := comap_comap_eq_gauss φ hφ haE' hcE' (W10Gal.hχ_compMap B E 𝔪') hc hcE0
      hc₀' hle hk
    exact ⟨j, hWχ ▸ hj⟩
  -- the component models over `E` are split, without loops and unfolded
  have hunf : ∀ (𝔪 : MaximalSpectrum (LX K E B)) (n : ℕ) (g : Fin (n + 1) → Comp K E B 𝔪)
      (hg : ∀ l, g l ≠ 0),
      (projModel (algebraMap (NormedField.valuation (K := E)).valuationSubring
        (Comp K E B 𝔪)).range g).points =
        ((gaussJoinModel (NormedField.valuation (K := E)) aE cE).normalization
          (Comp K E B 𝔪)).points →
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ'
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg) →
      TemperedFundamentalGroups.SemistableReduction.ModelCode.HasSplitNodes ϖ'
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg) ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.NoLoops
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg) ∧
      TemperedFundamentalGroups.SemistableReduction.ModelCode.IsUnfolded
        (NormedField.valuation (K := E)).valuationSubring
        (ψ (K := K) (B := B) (E := E) (1 ⊗ₜ algebraMap R B x) 𝔪)
        (projModelCode (NormedField.valuation (K := E)).valuationSubring hg)
        (genericPt (NormedField.valuation (K := E)).valuationSubring hg) := by
    intro 𝔪 n g hg hpts hss𝔪
    have hxX : algebraMap R B x = algebraMap K[X] B X := by
      rw [W10Line.lineAlgebra_algebraMap, aeval_X]
    rw [hxX, ψ_one_tmul_X]
    obtain ⟨𝔪', rfl⟩ := hcmpE.1.2 𝔪
    exact hS' 𝔪' E φ hφ (hSφ' 𝔪') halg aE cE haE' hcE' (Comp K E B (contrMax K E B _ 𝔪'))
      (compMap K E B (AlgebraicClosure K) 𝔪') (W10Gal.hχ_compMap B E 𝔪') (hcmpE.2 𝔪').2
      (hTχ 𝔪') ϖ' hϖ' n g hg hpts hss𝔪
  -- the conclusion
  obtain ⟨O', hO'', hdvr, ϖ'', hϖ'', c', cc, e, j, act, dom, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉,
      h₁₀⟩ :=
    strongComponentA_body_of_tree O hZ (W10Line.lineAct (K := K) hequiv hxG)
      (W10Line.lineAct_restrictScalars (K := K) hequiv hxG) hO' ϖ' hϖ' hσO' hiso θ' hθ0 hθint'
      hθgen' aE cE hcE0 hconvE hredE hstabE hcharts I c₀ j₀ hfK ιK hιK hιOK hV'
      (algebraMap R B x) hunf
  exact ⟨E, inferInstance, inferInstance, hEfin, hEgal, O', hO'', hdvr, ϖ'', hϖ'', c', cc, e, j,
    act, dom, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀⟩

end W10Assembly

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction.Statement

/-- **`StrongComponentAS` from Zariski connectedness**: W7, G4, G4′ and the component models
(`W10.treeComponentsUnfolded`) are proved. -/
theorem strongComponentAS_of (hZ : ZariskiConnected.{u}) : StrongComponentAS.{u} :=
  _root_.SemistableReduction.W10Assembly.strongComponentAS_of_W7_of_tree
    _root_.SemistableReduction.W7.statement
    _root_.SemistableReduction.W10Route.treeChartsSemistable
    _root_.SemistableReduction.W10.treeComponentsUnfolded hZ

end TemperedFundamentalGroups.SemistableReduction.Statement
