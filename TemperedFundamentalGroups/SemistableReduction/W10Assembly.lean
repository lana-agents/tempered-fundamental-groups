/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10SigmaLocal
import TemperedFundamentalGroups.SemistableReduction.W10Points
import TemperedFundamentalGroups.SemistableReduction.W10Code
import TemperedFundamentalGroups.SemistableReduction.W10Action
import TemperedFundamentalGroups.SemistableReduction.W10Compare
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

open TemperedFundamentalGroups W10Fields ProjScheme ZariskiModel

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

omit [Module.IsTorsionFree K[X] B] in
/-- `e` is compatible with the generic points. -/
theorem genericPtSigma_e :
    genericPtSigma O (fun 𝔪 k ↦ thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪) k) ≫
        (e O O' hO' n hg θ hθ0 hθint hθgen).hom = genericPtSigma O' hg := by
  rw [← cancel_epi (sigmaSpec.{u, u} fun 𝔪 : MaximalSpectrum (LX K E B) ↦
    CommRingCat.of (Comp K E B 𝔪))]
  refine Sigma.hom_ext _ _ fun 𝔪 ↦ ?_
  rw [ι_sigmaSpec_assoc, ι_sigmaSpec_assoc, reassoc_of% SpecMap_eval_genericPtSigma, e,
    sigmaι_sigmaIsoOfIso, SpecMap_eval_genericPtSigma, eComp,
    reassoc_of% genericPt_comp_baseChangeIsoFin]

end Models

section J

variable {K : Type u} [Field K] (O : ValuationSubring K)
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B]
  {E : Type u} [Field E] [Algebra K E] (O' : ValuationSubring E)
  [IsReduced (BX K E B)] (hn : IsIntegrallyClosedIn (BX K E B) (LX K E B))

/-- `M ⊗_K B ≅ ∏ 𝔪, D 𝔪` (normality). -/
noncomputable def piD : BX K E B ≃+* (∀ 𝔪, D K E B 𝔪) :=
  RingEquiv.ofBijective (toPiD K E B) (bijective_toPiD K E B hn)

/-- The map `BX → ∏ Comp`. -/
noncomputable def toPi : BX K E B →+* (∀ 𝔪 : MaximalSpectrum (LX K E B), Comp K E B 𝔪) :=
  RingHom.pi fun 𝔪 ↦ (Ideal.Quotient.mk 𝔪.asIdeal).comp (algebraMap (BX K E B) (LX K E B))

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] [IsReduced (BX K E B)] in
lemma piSubtype_comp_toPiD :
    (piSubtype (D K E B)).comp (toPiD K E B) = toPi (K := K) (B := B) (E := E) :=
  rfl

variable (n : MaximalSpectrum (LX K E B) → ℕ) {g : ∀ 𝔪, Fin (n 𝔪 + 1) → Comp K E B 𝔪}
  (hg : ∀ 𝔪 j, g 𝔪 j ≠ 0)
  (hroot : ∀ 𝔪, LocallyDominates (algebraMap O' (Comp K E B 𝔪)).range (RingHom.id _)
    (D K E B 𝔪).subtype (g 𝔪))

/-- **`j` on `M ⊗_K B`**, into the semistable model. -/
noncomputable def jc' : Spec (CommRingCat.of (BX K E B)) ⟶ (c' O' n hg).scheme :=
  Spec.map (CommRingCat.ofHom (piD hn).symm.toRingHom) ≫ jSigma hg (D K E B) hroot

lemma toPi_jc' :
    Spec.map (CommRingCat.ofHom (toPi (K := K) (B := B) (E := E))) ≫ jc' O' hn n hg hroot =
      genericPtSigma O' hg := by
  rw [jc', ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← piSubtype_comp_toPiD, RingHom.comp_assoc]
  have : (toPiD K E B).comp (piD hn).symm.toRingHom = RingHom.id _ := by
    exact RingHom.ext fun x ↦ (piD hn).apply_symm_apply x
  rw [this, RingHom.comp_id, SpecMap_comp_jSigma]

instance : IsSchemeTheoreticallyDominant (jc' O' hn n hg hroot) := by
  have : IsIso (CommRingCat.ofHom (piD hn).symm.toRingHom) :=
    (piD hn).symm.toCommRingCatIso.isIso_hom
  unfold jc'; infer_instance

end J

section Act

variable {K : Type u} [Field K]
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B]
  {E : Type u} [Field E] [Algebra K E] (O' : ValuationSubring E) [IsReduced (BX K E B)]
  {G : Type u} [Group G] (β : G →* (B ≃ₐ[K[X]] B))

/-- The group `G × Gal(E/K)`. -/
noncomputable abbrev H (G E : Type u) [Group G] [Field E] [Algebra K E] := G × (E ≃ₐ[K] E)

/-- Its action on the constants. -/
noncomputable abbrev αH : H (K := K) G E →* (E ≃ₐ[K] E) := MonoidHom.snd _ _

/-- Its action on the cover. -/
noncomputable abbrev βH : H (K := K) G E →* (B ≃ₐ[K[X]] B) := β.comp (MonoidHom.fst _ _)

/-- The ring automorphism `σ_h := lxAct (h⁻¹)` of `LX`. -/
noncomputable abbrev σh (h : H (K := K) G E) : LX K E B ≃+* LX K E B :=
  lxAct K E B (αH (G := G)) (βH β) h⁻¹

/-- The permutation of the components. -/
noncomputable abbrev πh (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)) :
    MaximalSpectrum (LX K E B) :=
  comapMax (σh β h) 𝔫

/-- The isomorphisms of components. -/
noncomputable abbrev φh (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)) :
    Comp K E B (πh β h 𝔫) →+* Comp K E B 𝔫 :=
  (compEquiv (σh β h) 𝔫 : Comp K E B (πh β h 𝔫) →+* Comp K E B 𝔫)

lemma sigmaRingHom_φh (h : H (K := K) G E) :
    sigmaRingHom (πh β h) (φh β h) =
      (piAct K E B (αH (G := G)) (βH β) h⁻¹ : (∀ 𝔪, Comp K E B 𝔪) →+* (∀ 𝔪, Comp K E B 𝔪)) := by
  ext z 𝔫
  change compEquiv (σh β h) 𝔫 (z (comapMax (σh β h) 𝔫)) = _
  rw [RingEquiv.coe_toRingHom, piAct_apply]

variable (hσO' : ∀ σ : E ≃ₐ[K] E, ∀ y ∈ O', σ y ∈ O')

/-- The action of `h⁻¹` on `O'`. -/
noncomputable def τh (h : H (K := K) G E) : O' →+* O' :=
  ((αH (G := G) h⁻¹ : E ≃ₐ[K] E) : E →+* E).restrict O' O' (hσO' _)

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] [IsReduced (BX K E B)] in
include hσO' in
lemma φh_algebraMap (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)) (o : O') :
    φh β h 𝔫 (algebraMap O' (Comp K E B (πh β h 𝔫)) o) =
      algebraMap O' (Comp K E B 𝔫) (τh O' hσO' h o) := by
  change compEquiv (σh β h) 𝔫 (Ideal.Quotient.mk _ (algebraMap E (LX K E B) (o : E))) =
    Ideal.Quotient.mk _ (algebraMap E (LX K E B) ((αH (G := G) h⁻¹ : E ≃ₐ[K] E) (o : E)))
  rw [compEquiv_mk]
  congr 1
  exact lxEquiv_algebraMap_const _ _ _

variable (n : MaximalSpectrum (LX K E B) → ℕ) {g : ∀ 𝔪, Fin (n 𝔪 + 1) → Comp K E B 𝔪}
  (hg : ∀ 𝔪 j, g 𝔪 j ≠ 0)
  (hact : ∀ (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)),
    ∀ Q ∈ (projModel (algebraMap O' (Comp K E B 𝔫)).range (g 𝔫)).points, ∃ i,
      ∀ y ∈ projChart (algebraMap O' (Comp K E B (πh β h 𝔫))).range (g (πh β h 𝔫)) i,
        φh β h 𝔫 y ∈ Q)

omit [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B] [IsReduced (BX K E B)] in
include hσO' hact in
lemma locallyDominates_act (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B))
    (l : Fin (n 𝔫 + 1)) :
    LocallyDominates (algebraMap O' (Comp K E B (πh β h 𝔫))).range (φh β h 𝔫)
      (projChart (algebraMap O' (Comp K E B 𝔫)).range (g 𝔫) l).subtype (g (πh β h 𝔫)) := by
  refine locallyDominates_of_points (φh β h 𝔫) ?_ (hact h 𝔫) l
  rintro _ ⟨o, rfl⟩
  rw [φh_algebraMap O' β hσO']
  exact ⟨_, rfl⟩

/-- The action of `h` on the semistable model `c'` (semilinear over `O'`). -/
noncomputable def actc' (h : H (K := K) G E) : (c' O' n hg).scheme ⟶ (c' O' n hg).scheme :=
  homSigmaLocal hg hg (πh β h) (φh β h) (locallyDominates_act O' β hσO' n hact h)


lemma genericPtSigma_actc' (h : H (K := K) G E) :
    genericPtSigma O' hg ≫ actc' O' β hσO' n hg hact h =
      Spec.map (CommRingCat.ofHom
        (piAct K E B (αH (G := G)) (βH β) h⁻¹).toRingHom) ≫ genericPtSigma O' hg := by
  rw [actc', genericPtSigma_comp_homSigmaLocal, sigmaRingHom_φh]
  rfl

omit [Module.IsTorsionFree K[X] B] [IsReduced (BX K E B)] in
lemma actc'_toSpec (h : H (K := K) G E) :
    actc' O' β hσO' n hg hact h ≫ (c' O' n hg).toSpec =
      (c' O' n hg).toSpec ≫ Spec.map (CommRingCat.ofHom (τh O' hσO' h)) :=
  homSigmaLocal_toSpec _ _ _ _ _ _ fun 𝔫 ↦ RingHom.ext (φh_algebraMap O' β hσO' h 𝔫)

end Act

section ActC

variable {K : Type u} [Field K] (O : ValuationSubring K)
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B]
  {E : Type u} [Field E] [Algebra K E] (O' : ValuationSubring E)
  (hO' : O'.comap (algebraMap K E) = O) [IsReduced (BX K E B)]
  {G : Type u} [Group G] (β : G →* (B ≃ₐ[K[X]] B))
  (hσO' : ∀ σ : E ≃ₐ[K] E, ∀ y ∈ O', σ y ∈ O')
  (n : MaximalSpectrum (LX K E B) → ℕ) {g : ∀ 𝔪, Fin (n 𝔪 + 1) → Comp K E B 𝔪}
  (hg : ∀ 𝔪 j, g 𝔪 j ≠ 0)
  (hact : ∀ (h : H (K := K) G E) (𝔫 : MaximalSpectrum (LX K E B)),
    ∀ Q ∈ (projModel (algebraMap O' (Comp K E B 𝔫)).range (g 𝔫)).points, ∃ i,
      ∀ y ∈ projChart (algebraMap O' (Comp K E B (πh β h 𝔫))).range (g (πh β h 𝔫)) i,
        φh β h 𝔫 y ∈ Q)
  {r : ℕ} (θ : Fin r → O') (hθ0 : ∀ s, (θ s : E) ≠ 0)
  (hθint : ∀ s, letI := algebraOO' O E O' hO'; IsIntegral O (θ s))
  (hθgen : ∀ y : O', (y : E) ∈ Subring.closure
    ((((algebraMap K E).comp O.subtype).range : Set E) ∪ Set.range fun s ↦ (θ s : E)))

attribute [local instance] compAlgO

/-- The generic point of `c`. -/
noncomputable abbrev γc : Spec (CommRingCat.of (∀ 𝔪 : MaximalSpectrum (LX K E B), Comp K E B 𝔪)) ⟶
    (c O O' n hg θ hθ0).scheme :=
  genericPtSigma O (fun 𝔪 k ↦ thetasFamily_ne_zero (θc_ne_zero O' θ hθ0 𝔪) (hg 𝔪) k)

/-- The endomorphisms of `c` transported from `c'`. -/
noncomputable def actC (h : H (K := K) G E) :
    (c O O' n hg θ hθ0).scheme ⟶ (c O O' n hg θ hθ0).scheme :=
  (e O O' hO' n hg θ hθ0 hθint hθgen).hom ≫ actc' O' β hσO' n hg hact h ≫
    (e O O' hO' n hg θ hθ0 hθint hθgen).inv

lemma γc_actC (h : H (K := K) G E) :
    γc O O' n hg θ hθ0 ≫ actC O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen h =
      Spec.map (CommRingCat.ofHom
        (piAct K E B (αH (G := G)) (βH β) h⁻¹).toRingHom) ≫ γc O O' n hg θ hθ0 := by
  have h1 := genericPtSigma_e O O' hO' n hg θ hθ0 hθint hθgen
  have h2 : genericPtSigma O' hg ≫ (e O O' hO' n hg θ hθ0 hθint hθgen).inv =
      γc O O' n hg θ hθ0 := by rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [actC, reassoc_of% h1, reassoc_of% genericPtSigma_actc', h2]

/-- **The action of `G × Gal(E/K)` on `c`.** -/
noncomputable def act : H (K := K) G E →* Aut (c O O' n hg θ hθ0).scheme :=
  actOfGenericPt (γc O O' n hg θ hθ0) (piAct K E B (αH (G := G)) (βH β))
    (actC O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen)
    (γc_actC O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen)

lemma act_hom (h : H (K := K) G E) :
    (act O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen h).hom =
      actC O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen h := rfl

include hO' in
lemma τh_comp_algOO' (h : H (K := K) G E) :
    (τh O' hσO' h).comp (algOO' O E O' hO') = algOO' O E O' hO' := by
  ext o
  change (αH (G := G) h⁻¹ : E ≃ₐ[K] E) (algebraMap K E o) = algebraMap K E o
  exact AlgEquiv.commutes _ _

/-- The action on `c` lies over `Spec O`. -/
theorem act_toSpec (h : H (K := K) G E) :
    (act O O' hO' β hσO' n hg hact θ hθ0 hθint hθgen h).hom ≫ (c O O' n hg θ hθ0).toSpec =
      (c O O' n hg θ hθ0).toSpec := by
  rw [act_hom, actC, ← e_toSpec O O' hO' n hg θ hθ0 hθint hθgen]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [reassoc_of% actc'_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    τh_comp_algOO' O O' hO' hσO' h]

end ActC

section JC

variable {K : Type u} [Field K] (O : ValuationSubring K)
  {B : Type u} [CommRing B] [Algebra K[X] B] [Module.Finite K[X] B] [Module.IsTorsionFree K[X] B]
  [Algebra K B] [IsScalarTower K K[X] B]
  {E : Type u} [Field E] [Algebra K E] (O' : ValuationSubring E)
  (hO' : O'.comap (algebraMap K E) = O) [IsReduced (BX K E B)]
  (hn : IsIntegrallyClosedIn (BX K E B) (LX K E B))
  (n : MaximalSpectrum (LX K E B) → ℕ) {g : ∀ 𝔪, Fin (n 𝔪 + 1) → Comp K E B 𝔪}
  (hg : ∀ 𝔪 j, g 𝔪 j ≠ 0)
  (hroot : ∀ 𝔪, LocallyDominates (algebraMap O' (Comp K E B 𝔪)).range (RingHom.id _)
    (D K E B 𝔪).subtype (g 𝔪))
  {r : ℕ} (θ : Fin r → O') (hθ0 : ∀ s, (θ s : E) ≠ 0)
  (hθint : ∀ s, letI := algebraOO' O E O' hO'; IsIntegral O (θ s))
  (hθgen : ∀ y : O', (y : E) ∈ Subring.closure
    ((((algebraMap K E).comp O.subtype).range : Set E) ∪ Set.range fun s ↦ (θ s : E)))

omit [Algebra K B] [IsScalarTower K K[X] B] in
lemma toPi_injective : Function.Injective (toPi (K := K) (B := B) (E := E)) := by
  intro x y hxy
  apply injective_toLX K E B
  apply (equivPi K E B).injective
  ext 𝔪
  rw [equivPi_apply, equivPi_apply]
  exact congrFun hxy 𝔪

/-- The generic point of `E ⊗_K B`: `E ⊗_K B → ∏ Comp`. -/
noncomputable def ψ : TensorProduct K E B →+* (∀ 𝔪 : MaximalSpectrum (LX K E B), Comp K E B 𝔪) :=
  (toPi (K := K) (B := B) (E := E)).comp (tensorEquiv K E B).toRingHom

lemma ψ_injective : Function.Injective (ψ (K := K) (B := B) (E := E)) :=
  (toPi_injective).comp (tensorEquiv K E B).injective

instance : IsReduced (TensorProduct K E B) :=
  isReduced_of_injective (tensorEquiv K E B).toRingHom (tensorEquiv K E B).injective

instance isDominant_SpecMap_ψ :
    IsDominant (Spec.map (CommRingCat.ofHom (ψ (K := K) (B := B) (E := E)))) :=
  isDominant_SpecMap_of_injective _ ψ_injective

/-- **The morphism `j : Spec (E ⊗_K B) ⟶ c`.** -/
noncomputable def jC : Spec (CommRingCat.of (TensorProduct K E B)) ⟶ (c O O' n hg θ hθ0).scheme :=
  Spec.map (CommRingCat.ofHom (tensorEquiv K E B).symm.toRingHom) ≫ jc' O' hn n hg hroot ≫
    (e O O' hO' n hg θ hθ0 hθint hθgen).inv

/-- `j` restricts to the generic point of `c`. -/
theorem SpecMap_ψ_jC :
    Spec.map (CommRingCat.ofHom (ψ (K := K) (B := B) (E := E))) ≫
        jC O O' hO' hn n hg hroot θ hθ0 hθint hθgen = γc O O' n hg θ hθ0 := by
  have h1 := genericPtSigma_e O O' hO' n hg θ hθ0 hθint hθgen
  have h2 : genericPtSigma O' hg ≫ (e O O' hO' n hg θ hθ0 hθint hθgen).inv =
      γc O O' n hg θ hθ0 := by rw [← h1, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [jC, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have : (ψ (K := K) (B := B) (E := E)).comp (tensorEquiv K E B).symm.toRingHom =
      toPi (K := K) (B := B) (E := E) := by
    ext x : 1
    simp [ψ]
  rw [this, reassoc_of% toPi_jc', h2]

instance : IsSchemeTheoreticallyDominant (jC O O' hO' hn n hg hroot θ hθ0 hθint hθgen) := by
  have : IsIso (CommRingCat.ofHom (tensorEquiv K E B).symm.toRingHom) :=
    (tensorEquiv K E B).symm.toRingEquiv.toCommRingCatIso.isIso_hom
  unfold jC; infer_instance

/-- Morphisms out of `Spec (E ⊗_K B)` into a separated scheme are determined on the generic
point. -/
lemma hom_ext_ψ {Y : Scheme.{u}} [Y.IsSeparated]
    {a b : Spec (CommRingCat.of (TensorProduct K E B)) ⟶ Y}
    (h : Spec.map (CommRingCat.ofHom (ψ (K := K) (B := B) (E := E))) ≫ a =
      Spec.map (CommRingCat.ofHom (ψ (K := K) (B := B) (E := E))) ≫ b) : a = b :=
  ext_of_isDominant _ h

end JC

end W10Assembly

end SemistableReduction
