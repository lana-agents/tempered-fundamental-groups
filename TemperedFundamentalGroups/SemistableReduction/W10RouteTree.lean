/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteSpecial

/-!
# G4: `W10.TreeChartsSemistable` from the pointwise descent statements

Blueprint §9.7a, step 4 (G4 (ii)). **`W10Route.treeChartsSemistable_of`**:
`SmoothDescentStatement → NodeDescentStatement → W10.TreeChartsSemistable`.

The finite set `S` of constants is the union of the sets given by the descent statements for the
twists of `F'` attached to the tree: `Aff (a i) (c i) F'` (vertex charts), `Inv 1 (Aff (a i) (c i)
F')` (charts at `∞`) and `Aff (a j) (c m) F'` with thickness `c j / c m` (edge charts), with the
generators `T` transported to the twists (`adjoin_map_eq_top`). Over `E`, the hypotheses of
`chartsSemistable` are the descent statements applied to the twists of the `E`-form, at the
points which are smooth, resp. ordinary double points, by `W7.IsSemistableTree`.
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

set_option hygiene false in
local notation "O_E" => (NormedField.valuation (K := E)).valuationSubring

/-- Generators of an algebra generate it after a ring isomorphism mapping constants to
constants. -/
lemma adjoin_map_eq_top {R G G' : Type*} [CommRing R] [CommRing G] [CommRing G'] [Algebra R G]
    [Algebra R G'] (e : G ≃+* G') (he : ∀ r, ∃ r', e (algebraMap R G r) = algebraMap R G' r')
    {T : Set G} (hT : Algebra.adjoin R T = ⊤) : Algebra.adjoin R (e '' T) = ⊤ := by
  refine eq_top_iff.2 fun y _ ↦ ?_
  clear ‹y ∈ ⊤›
  obtain ⟨x, rfl⟩ := e.surjective y
  have hy : x ∈ Algebra.adjoin R T := hT ▸ Algebra.mem_top
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
  | algebraMap r =>
    obtain ⟨r', h⟩ := he r
    rw [h]
    exact Subalgebra.algebraMap_mem _ r'
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

section Gen

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F' : Type u} [Field F'] [Algebra (RatFunc C) F']

lemma adjoin_aff_eq_top {a c : C} (hc : c ≠ 0) {T : Finset F'}
    (hT : Algebra.adjoin (RatFunc C) (T : Set F') = ⊤) :
    Algebra.adjoin (RatFunc C)
      ((T.map (toAff (a := a) hc).toEquiv.toEmbedding : Finset (Aff a c hc F')) :
        Set (Aff a c hc F')) = ⊤ := by
  rw [Finset.coe_map]
  refine adjoin_map_eq_top (toAff hc) (fun r ↦ ⟨(aff a c hc).symm r, ?_⟩) hT
  rw [algebraMap_aff_apply, AlgEquiv.apply_symm_apply]

lemma adjoin_inv_aff_eq_top {a c : C} (hc : c ≠ 0) {T : Finset F'}
    (hT : Algebra.adjoin (RatFunc C) (T : Set F') = ⊤) :
    Algebra.adjoin (RatFunc C)
      ((T.map ((toAff (a := a) hc).trans (toInv (c := (1 : C)) one_ne_zero)).toEquiv.toEmbedding :
        Finset (Inv (1 : C) one_ne_zero (Aff a c hc F'))) :
          Set (Inv (1 : C) one_ne_zero (Aff a c hc F'))) = ⊤ := by
  rw [Finset.coe_map]
  refine adjoin_map_eq_top ((toAff hc).trans (toInv one_ne_zero))
    (fun r ↦ ⟨(inv one_ne_zero).symm ((aff a c hc).symm r), ?_⟩) hT
  rw [algebraMap_inv_apply, algebraMap_aff_apply, AlgEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]
  rfl

end Gen

/-- **G4 (ii): the charts of the normalized tree model over `E` are semistable**, given the
pointwise descent statements for smooth points and for node points. -/
theorem treeChartsSemistable_of (hS : SmoothDescentStatement.{u})
    (hN : NodeDescentStatement.{u}) : W10.TreeChartsSemistable.{u} := by
  classical
  intro C _ _ _ _ p hp hp1 F' _ _ _ _ _ ι _ _ a c hc hconv hred hss T hT
  -- the finite sets of constants for the twists of `F'`
  choose Sv hSv using fun i ↦ hS C p hp hp1 (Aff (a i) (c i) (hc i) F')
    (T.map (toAff (a := a i) (hc i)).toEquiv.toEmbedding) (adjoin_aff_eq_top (hc i) hT)
  choose Sr hSr using fun i ↦ hS C p hp hp1 (Inv (1 : C) one_ne_zero (Aff (a i) (c i) (hc i) F'))
    (T.map ((toAff (a := a i) (hc i)).trans (toInv (c := (1 : C)) one_ne_zero)).toEquiv.toEmbedding)
    (adjoin_inv_aff_eq_top (hc i) hT)
  choose Se hSe using fun j m (h : ‖c j / c m‖ < 1) ↦ hN C p hp hp1 (Aff (a j) (c m) (hc m) F')
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
  refine chartsSemistable hφ hχ halg hϖ hcE hc hconvE hredE ?_ ?_ ?_ hCc hCcc
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

end W10Route

end SemistableReduction
