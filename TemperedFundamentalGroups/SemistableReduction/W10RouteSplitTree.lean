/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteSplitSpecial
import TemperedFundamentalGroups.SemistableReduction.W10RouteTree
import TemperedFundamentalGroups.SemistableReduction.NodeDescentSplit
import TemperedFundamentalGroups.SemistableReduction.SmoothDescentSplit

/-!
# G4′: the classification of the points of the normalized tree model over `E`

Blueprint §10.3.8 (split nodes). **`W10.TreeChartsSplit`**: `W10.TreeChartsSemistable` with the
conclusion strengthened to the classification `W10Route.SplitClass` of every prime of every chart:
étale-locally `O_E[X]`, or a split node lying over the node of an edge chart of the tree (with the
same local ring as the normalized edge chart at a valuation `W` centered there). In particular
every chart is split semistable (`IsSplitSemistableAt`), hence semistable.

* `W10Route.treeChartsSplit_of`: `SmoothDescentSplitStatement → W10.TreeChartsSplit` (the routing
  of `treeChartsSemistable_of`, with the split node descent `nodeDescentSplitStatement`);
* `W10Route.treeChartsSplit : W10.TreeChartsSplit` (with `smoothDescentSplitStatement`);
* `W10Route.treeChartsSemistable_of_split`: `W10.TreeChartsSplit → W10.TreeChartsSemistable`.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10

/-- **G4′: the classification of the points of the charts of the normalized tree model over
`E`.** As `TreeChartsSemistable`, with the conclusion `W10Route.SplitClass` at every prime. -/
def TreeChartsSplit : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ) (_ : p.Prime) (_ : ‖(p : C)‖ < 1)
    (F' : Type u) [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
    [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
    (ι : Type) [Fintype ι] [Nonempty ι] (a c : ι → C) (hc : ∀ i, c i ≠ 0)
    (_ : GaussTree.IsConvex (NormedField.valuation (K := C)) a c)
    (_ : GaussTree.IsReduced (NormedField.valuation (K := C)) a c)
    (_ : W7.IsSemistableTree a c hc F')
    (T : Finset F') (_ : Algebra.adjoin (RatFunc C) (T : Set F') = ⊤),
    ∃ S : Finset C, ∀ (E : Type u) [NontriviallyNormedField E] [IsUltrametricDist E]
      [CompleteSpace E] (φ : E →+* C) (_ : ∀ e, ‖φ e‖ = ‖e‖) (_ : (S : Set C) ⊆ Set.range φ)
      (_ : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
      [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
      [PerfectField (ResidueField (NormedField.valuation (K := E)).valuationSubring)]
      (aE cE : ι → E) (_ : ∀ i, φ (aE i) = a i) (_ : ∀ i, φ (cE i) = c i)
      (F₀ : Type u) [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀]
      [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
      [Algebra.IsSeparable (RatFunc E) F₀]
      [Algebra (NormedField.valuation (K := E)).valuationSubring F₀]
      [IsScalarTower (NormedField.valuation (K := E)).valuationSubring E F₀]
      (χ : F₀ →+* F')
      (_ : ∀ x, χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) F' (ratFuncMap φ x))
      (_ : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) F')
      (_ : (T : Set F') ⊆ Set.range χ)
      (ϖ : (NormedField.valuation (K := E)).valuationSubring) (_ : Irreducible ϖ),
      ∀ Cc ∈ ((gaussJoinModel (NormedField.valuation (K := E)) aE cE).normalization F₀).charts,
        ∀ [Algebra (NormedField.valuation (K := E)).valuationSubring Cc],
          (∀ o, ((algebraMap (NormedField.valuation (K := E)).valuationSubring Cc o : Cc) : F₀) =
            algebraMap (NormedField.valuation (K := E)).valuationSubring F₀ o) →
          ∀ 𝔭 : Ideal Cc, 𝔭.IsPrime → W10Route.SplitClass aE cE ϖ Cc 𝔭

end W10

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

/-- **G4′: the points of the charts of the normalized tree model over `E` are classified**
(`SplitClass`), given the smooth descent in the smooth form (the node descent in the split form
is `nodeDescentSplitStatement`). -/
theorem treeChartsSplit_of (hS : SmoothDescentSplitStatement.{u}) :
    W10.TreeChartsSplit.{u} := by
  classical
  intro C _ _ _ _ p hp hp1 F' _ _ _ _ _ ι _ _ a c hc hconv hred hss T hT
  -- the finite sets of constants for the twists of `F'`
  choose Sv hSv using fun i ↦ hS C p hp hp1 (Aff (a i) (c i) (hc i) F')
    (T.map (toAff (a := a i) (hc i)).toEquiv.toEmbedding) (adjoin_aff_eq_top (hc i) hT)
  choose Sr hSr using fun i ↦ hS C p hp hp1 (Inv (1 : C) one_ne_zero (Aff (a i) (c i) (hc i) F'))
    (T.map ((toAff (a := a i) (hc i)).trans (toInv (c := (1 : C)) one_ne_zero)).toEquiv.toEmbedding)
    (adjoin_inv_aff_eq_top (hc i) hT)
  choose Se hSe using fun j m (h : ‖c j / c m‖ < 1) ↦ nodeDescentSplitStatement C p hp hp1
    (Aff (a j) (c m) (hc m) F')
    (T.map (toAff (a := a j) (hc m)).toEquiv.toEmbedding) (adjoin_aff_eq_top (hc m) hT)
    (c j / c m) h (div_ne_zero (hc j) (hc m))
  refine ⟨Finset.univ.biUnion Sv ∪ Finset.univ.biUnion Sr ∪ Finset.univ.biUnion
    (fun jm : ι × ι ↦ if h : ‖c jm.1 / c jm.2‖ < 1 then Se jm.1 jm.2 h else ∅), ?_⟩
  intro E _ _ _ φ hφ hSφ halg _ _ aE cE ha hcc F₀ _ _ _ _ _ _ _ _ χ hχ hdeg hTχ ϖ hϖ Cc hCc _
    hCcc
  have hv : ∀ m, (Sv m : Set C) ⊆ Set.range φ := fun m x hx ↦ hSφ (Finset.mem_union_left _
    (Finset.mem_union_left _ (Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hx⟩)))
  have hr : ∀ m, (Sr m : Set C) ⊆ Set.range φ := fun m x hx ↦ hSφ (Finset.mem_union_left _
    (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hx⟩)))
  have he : ∀ j m h, (Se j m h : Set C) ⊆ Set.range φ := fun j m h x hx ↦ hSφ
    (Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨(j, m), Finset.mem_univ _, by
      simp only [dif_pos h]; exact hx⟩))
  clear hSφ
  obtain rfl : a = fun i ↦ φ (aE i) := funext fun i ↦ (ha i).symm
  obtain rfl : c = fun i ↦ φ (cE i) := funext fun i ↦ (hcc i).symm
  have hcE : ∀ i, cE i ≠ 0 := fun i h ↦ hc i (by simp [h])
  haveI : CharZero E := φ.charZero
  have hconvE := isConvex_of_map hφ hconv
  have hredE := isReduced_of_map hφ hred
  -- the generators lie in the twisted `E`-forms
  have hTv : ∀ i j, ((T.map (toAff (a := φ (aE i)) (hc j)).toEquiv.toEmbedding :
      Finset (Aff (φ (aE i)) (φ (cE j)) (hc j) F')) : Set (Aff (φ (aE i)) (φ (cE j)) (hc j) F')) ⊆
        Set.range (χAff (aE := aE i) χ (hcE j) (hc j)) := by
    intro i j
    rw [Finset.coe_map]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨s, rfl⟩ := hTχ ht
    exact ⟨toAff (hcE j) s, rfl⟩
  have hTr : ∀ i, ((T.map ((toAff (a := φ (aE i)) (hc i)).trans
      (toInv (c := (1 : C)) one_ne_zero)).toEquiv.toEmbedding :
        Finset (Inv (1 : C) one_ne_zero (Aff (φ (aE i)) (φ (cE i)) (hc i) F'))) :
          Set (Inv (1 : C) one_ne_zero (Aff (φ (aE i)) (φ (cE i)) (hc i) F'))) ⊆
        Set.range (χInvAff (aE := aE i) χ (hcE i) (hc i)) := by
    intro i
    rw [Finset.coe_map]
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨s, rfl⟩ := hTχ ht
    exact ⟨toInv one_ne_zero (toAff (hcE i) s), rfl⟩
  refine chartsSplit hφ hχ halg hϖ hcE hc hconvE hredE ?_ ?_ ?_ hCc hCcc
  · -- vertex charts
    intro m β hβ hfar P' hmax hP'
    have hsm : IsDiscSmooth P' := by
      refine smoothOver_aff_aff (hc m) (hss.smooth m β hβ fun j hj ↦ ?_) P' hmax hP'
      have h1 := hfar j ((discLE_map_iff hφ).1 hj.1) hj.2.1
      have : φ (aE m) + φ (cE m) * β - φ (aE j) =
          φ (cE m) * (β - φ ((aE j - aE m) / cE m)) := by
        rw [map_div₀, map_sub, mul_sub, mul_div_cancel₀ _ (hc m)]
        ring
      rw [this, norm_mul, h1, mul_one]
    haveI := isSeparable_of_charZero (E := E) (Aff (aE m) (cE m) (hcE m) F₀)
    letI := DVRDescent.bdAlgebra (E := E) (F₀ := Aff (aE m) (cE m) (hcE m) F₀)
    exact hSv m E φ hφ (hv m) halg (Aff (aE m) (cE m) (hcE m) F₀) (χAff χ (hcE m) (hc m))
      (isCompat_χAff (hcE m) (hc m) hχ rfl rfl) (by rw [finrank_aff, finrank_aff]; exact hdeg)
      (hTv m m) ϖ hϖ (fun o ↦ (IsScalarTower.algebraMap_apply E (RatFunc E) _ o).symm) β hβ P'
      hmax hP' hsm
  · -- the charts at `∞` of the root
    intro ρ hρ P' hmax hP'
    have hne : ∀ m, ¬IsEdge (fun i ↦ φ (aE i)) (fun i ↦ φ (cE i)) ρ m := fun m hm ↦
      hm.2.1 (hredE ρ m ((discLE_map_iff hφ).1 hm.1) (hρ m))
    have hsm : IsDiscSmooth P' := smoothOver_aff_zero (hss.root ρ hne) P' hmax hP'
    haveI := isSeparable_of_charZero (E := E)
      (Inv (1 : E) one_ne_zero (Aff (aE ρ) (cE ρ) (hcE ρ) F₀))
    letI := DVRDescent.bdAlgebra (E := E)
      (F₀ := Inv (1 : E) one_ne_zero (Aff (aE ρ) (cE ρ) (hcE ρ) F₀))
    exact hSr ρ E φ hφ (hr ρ) halg (Inv (1 : E) one_ne_zero (Aff (aE ρ) (cE ρ) (hcE ρ) F₀))
      (χInvAff χ (hcE ρ) (hc ρ)) (isCompat_χInvAff (hcE ρ) (hc ρ) hχ rfl rfl)
      (by rw [finrank_inv, finrank_aff, finrank_inv, finrank_aff]; exact hdeg) (hTr ρ) ϖ hϖ
      (fun o ↦ (IsScalarTower.algebraMap_apply E (RatFunc E) _ o).symm) 0 (by simp) P' hmax hP'
      hsm
  · -- edge charts
    intro j m hjm hjne hedg
    haveI := isSeparable_of_charZero (E := E) (Aff (aE j) (cE m) (hcE m) F₀)
    intro _ hRc P' hmax hP'
    have h1 : ‖φ (cE j) / φ (cE m)‖ < 1 := by
      rw [← map_div₀, hφ]
      exact norm_div_lt_one_of_edge hcE hredE hjm hjne
    have hedgeC : IsEdge (fun i ↦ φ (aE i)) (fun i ↦ φ (cE i)) j m :=
      ⟨(discLE_map_iff hφ).2 hjm, hjne, fun k hjk hkm ↦
        hedg k ((discLE_map_iff hφ).1 hjk) ((discLE_map_iff hφ).1 hkm)⟩
    have hodp := hss.node j m hedgeC h1 (div_ne_zero (hc j) (hc m)) P' hmax hP'
    have hRc' : ∀ o, ((algebraMap O_E (Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) o :
        Rint (cE j / cE m) (Aff (aE j) (cE m) (hcE m) F₀)) : Aff (aE j) (cE m) (hcE m) F₀) =
          algebraMap E (Aff (aE j) (cE m) (hcE m) F₀) o := hRc
    exact hSe j m h1 E φ hφ (he j m h1) halg (Aff (aE j) (cE m) (hcE m) F₀)
      (χAff χ (hcE m) (hc m)) (isCompat_χAff (hcE m) (hc m) hχ rfl rfl)
      (by rw [finrank_aff, finrank_aff]; exact hdeg) (hTv j m) ϖ hϖ (cE j / cE m)
      (map_div₀ φ (cE j) (cE m)) hRc' P' hmax hP' hodp

/-- **G4′** (unconditional). -/
theorem treeChartsSplit : W10.TreeChartsSplit.{u} :=
  treeChartsSplit_of smoothDescentSplitStatement

/-- G4′ implies G4. -/
theorem treeChartsSemistable_of_split (h : W10.TreeChartsSplit.{u}) :
    W10.TreeChartsSemistable.{u} := by
  intro C _ _ _ _ p hp hp1 F' _ _ _ _ _ ι _ _ a c hc hconv hred hss T hT
  obtain ⟨S, hS⟩ := h C p hp hp1 F' ι a c hc hconv hred hss T hT
  refine ⟨S, ?_⟩
  intro E _ _ _ φ hφ hSφ halg _ _ aE cE ha hcc F₀ _ _ _ _ _ _ _ _ χ hχ hdeg hTχ ϖ hϖ Cc hCc _
    hCcc 𝔭 _
  exact (hS E φ hφ hSφ halg aE cE ha hcc F₀ χ hχ hdeg hTχ ϖ hϖ Cc hCc hCcc 𝔭
    inferInstance).isSplitSemistableAt.isSemistableAt

end W10Route

end SemistableReduction
