/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10SigmaLocal
import TemperedFundamentalGroups.SemistableReduction.W10Points
import TemperedFundamentalGroups.SemistableReduction.W10Code
import TemperedFundamentalGroups.SemistableReduction.W10Action
import TemperedFundamentalGroups.SemistableReduction.W10Union
import TemperedFundamentalGroups.SemistableReduction.StrongA

/-!
# The scheme-theoretic assembly of W10

Blueprint §9.7a, step 5. Fix a finite extension `E / K` with a discrete valuation ring `O' ⊆ E`
over `O`, and for every component `𝔪` of `E ⊗_K B` (`W10Fields`) homogeneous coordinates
`g 𝔪` of a semistable projective `O'`-model of the function field `Comp 𝔪`. Then:

* `c' := projSigma O' g` (semistable: `isSemistable_c'`), `c` the corresponding projective
  `O`-model (multi-`θ` base change, `W10Code`) and `e : c ≅ c'` over `O` (`e_toSpec`).

Further sections build `j`, the action and the dominations.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits Polynomial TensorProduct

namespace SemistableReduction

namespace W10Assembly

open TemperedFundamentalGroups W10Fields ProjScheme

attribute [local instance] polyAlgebra

section Models

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (B : Type u) [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B]
  (E : Type u) [Field E] [Algebra K E] (O' : ValuationSubring E)
  (hO' : O'.comap (algebraMap K E) = O)

/-- The components of `E ⊗_K B` form a finite type. -/
noncomputable instance : Fintype (MaximalSpectrum (LX K E B)) := Fintype.ofFinite _

/-- `O → O'`. -/
noncomputable def algOO' : O →+* O' :=
  (algebraMap K E).restrict O O' (fun x hx ↦ by rw [← hO'] at hx; exact hx)

/-- The `O`-algebra structure of a component. -/
noncomputable abbrev compAlgO (𝔪 : MaximalSpectrum (LX K E B)) : Algebra O (Comp K E B 𝔪) :=
  ((algebraMap E (Comp K E B 𝔪)).comp ((algebraMap K E).comp O.subtype)).toAlgebra

attribute [local instance] compAlgO

/-- The `O`-algebra structure of `O'`. -/
noncomputable abbrev algebraOO' : Algebra O O' := (algOO' O E O' hO').toAlgebra

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] in
lemma isScalarTower_comp (𝔪 : MaximalSpectrum (LX K E B)) :
    letI := algebraOO' O E O' hO'
    IsScalarTower O O' (Comp K E B 𝔪) :=
  letI := algebraOO' O E O' hO'
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable {B E} (n : MaximalSpectrum (LX K E B) → ℕ)
  {g : ∀ 𝔪, Fin (n 𝔪 + 1) → Comp K E B 𝔪} (hg : ∀ 𝔪 j, g 𝔪 j ≠ 0)

/-- The semistable `O'`-model: the disjoint union of the projective models of the `g 𝔪`. -/
noncomputable abbrev c' : ModelCode O' := projSigma O' hg

variable {r : ℕ} (θ : Fin r → O') (hθ0 : ∀ s, (θ s : E) ≠ 0)

/-- The generators `θ` in a component. -/
noncomputable def θc (𝔪 : MaximalSpectrum (LX K E B)) : Fin r → Comp K E B 𝔪 :=
  fun s ↦ algebraMap O' (Comp K E B 𝔪) (θ s)

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] in
include hθ0 in
lemma θc_ne_zero (𝔪 : MaximalSpectrum (LX K E B)) (s : Fin r) : θc O' θ 𝔪 s ≠ 0 := by
  change algebraMap E (Comp K E B 𝔪) (θ s : E) ≠ 0
  exact (_root_.map_ne_zero _).2 (hθ0 s)

/-- The model over `O`: the disjoint union of the projective `O`-models of the families
`(θ_s g_l)`. -/
noncomputable abbrev c : ModelCode O :=
  projSigma O (fun 𝔪 k ↦ thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪) k)

variable (hθint : ∀ s, letI := algebraOO' O E O' hO'; IsIntegral O (θ s))
  (hθgen : ∀ y : O', (y : E) ∈ Subring.closure
    ((((algebraMap K E).comp O.subtype).range : Set E) ∪ Set.range fun s ↦ (θ s : E)))

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] in
include hθint in
lemma θc_isIntegral (𝔪 : MaximalSpectrum (LX K E B)) (s : Fin r) : IsIntegral O (θc O' θ 𝔪 s) := by
  letI := algebraOO' O E O' hO'
  haveI := isScalarTower_comp O B E O' hO' 𝔪
  exact (hθint s).map (IsScalarTower.toAlgHom O O' (Comp K E B 𝔪))

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] in
include hθgen in
lemma range_le_closure (𝔪 : MaximalSpectrum (LX K E B)) :
    (algebraMap O' (Comp K E B 𝔪)).range ≤ Subring.closure
      (((algebraMap O (Comp K E B 𝔪)).range : Set (Comp K E B 𝔪)) ∪ Set.range (θc O' θ 𝔪)) := by
  rintro _ ⟨y, rfl⟩
  have h : algebraMap E (Comp K E B 𝔪) (y : E) ∈ (Subring.closure _).map
      (algebraMap E (Comp K E B 𝔪)) := Subring.mem_map.2 ⟨_, hθgen y, rfl⟩
  rw [RingHom.map_closure, Set.image_union] at h
  change algebraMap E (Comp K E B 𝔪) (y : E) ∈ _
  refine Subring.closure_mono (Set.union_subset_union ?_ ?_) h
  · rintro _ ⟨_, ⟨o, rfl⟩, rfl⟩
    exact ⟨o, rfl⟩
  · rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, rfl⟩

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] in
include hO' in
lemma range_le_range (𝔪 : MaximalSpectrum (LX K E B)) :
    (algebraMap O (Comp K E B 𝔪)).range ≤ (algebraMap O' (Comp K E B 𝔪)).range := by
  rintro _ ⟨o, rfl⟩
  exact ⟨algOO' O E O' hO' o, rfl⟩

/-- The componentwise base change isomorphisms. -/
noncomputable def eComp (𝔪 : MaximalSpectrum (LX K E B)) :
    (projModelCode O (thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪))).scheme ≅
      (projModelCode O' (hg 𝔪)).scheme :=
  baseChangeIsoFin rfl rfl (θc_ne_zero O' θ hθ0 𝔪) (θc_isIntegral O O' hO' θ hθint 𝔪)
    (fun s ↦ ⟨θ s, rfl⟩) (range_le_closure O O' θ hθgen 𝔪) (range_le_range O O' hO' 𝔪)
    (hg 𝔪)

/-- **`c ≅ c'`.** -/
noncomputable def e : (c O O' n hg θ hθ0).scheme ≅ (c' O' n hg).scheme :=
  sigmaIsoOfIso _ _ (eComp O O' hO' n hg θ hθ0 hθint hθgen)

omit [Module.IsTorsionFree K[X] B] in
/-- `e` lies over `Spec O' ⟶ Spec O`. -/
theorem e_toSpec :
    (e O O' hO' n hg θ hθ0 hθint hθgen).hom ≫ (c' O' n hg).toSpec ≫
      Spec.map (CommRingCat.ofHom (algOO' O E O' hO')) = (c O O' n hg θ hθ0).toSpec := by
  refine ModelCode.sigma_hom_ext _ fun 𝔪 ↦ ?_
  rw [e, reassoc_of% sigmaι_sigmaIsoOfIso, reassoc_of% ModelCode.sigmaι_toSpec,
    ModelCode.sigmaι_toSpec]
  letI := algebraOO' O E O' hO'
  haveI := isScalarTower_comp O B E O' hO' 𝔪
  exact baseChangeIsoFin_toSpec _ _ _ _ _ _ _ _

omit [Module.IsTorsionFree K[X] B] in
/-- `c'` is semistable if its summands are. -/
theorem isSemistable_c' (ϖ' : O')
    (hss : ∀ 𝔪, TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ'
      (projModelCode O' (hg 𝔪))) :
    TemperedFundamentalGroups.SemistableReduction.ModelCode.IsSemistable ϖ' (c' O' n hg) :=
  TemperedFundamentalGroups.SemistableReduction.ModelCode.isSemistable_sigma _ ϖ' hss

end Models

end W10Assembly

end SemistableReduction
