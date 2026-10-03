/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Scheme

/-!
# Finite disjoint unions of model codes

Blueprint §9.7 (W10 assembly, scheme realization, item 3b).

* `LinearEmbedding.linMap e : ℙᵐ_O ⟶ ℙᴺ_O` for an injection `e : Fin (m + 1) ↪ Fin (N + 1)` of
  coordinates (`x_{e i} ↦ y_i`, the other coordinates `↦ 0`), via `Proj.map`: a closed immersion
  over `Spec O`, whose image lies in `V(x_j : j ∉ range e)`; for disjoint ranges the images are
  disjoint.
-/

universe u

open CategoryTheory AlgebraicGeometry Limits MvPolynomial HomogeneousLocalization Graded

namespace SemistableReduction

open TemperedFundamentalGroups

attribute [local instance] MvPolynomial.gradedAlgebra

namespace LinearEmbedding

variable {O : Type u} [CommRing O] {m N : ℕ} (e : Fin (m + 1) ↪ Fin (N + 1))

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

/-- The coordinates: `x_{e i} ↦ y_i`, `x_j ↦ 0` for `j ∉ range e`. -/
noncomputable def coordMap : Fin (N + 1) → MvPolynomial (Fin (m + 1)) O :=
  Function.extend e X 0

lemma coordMap_apply (i : Fin (m + 1)) : coordMap (O := O) e (e i) = X i :=
  e.injective.extend_apply _ _ _

lemma coordMap_of_notMem {j : Fin (N + 1)} (h : j ∉ Set.range e) :
    coordMap (O := O) e j = 0 :=
  Function.extend_apply' _ _ _ fun ⟨i, hi⟩ ↦ h ⟨i, hi⟩

lemma isHomogeneous_coordMap (j : Fin (N + 1)) : (coordMap (O := O) e j).IsHomogeneous 1 := by
  by_cases h : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := h
    rw [coordMap_apply]
    exact isHomogeneous_X O i
  · rw [coordMap_of_notMem e h]
    exact isHomogeneous_zero _ _ _

/-- The graded ring map `O[x₀, …, x_N] → O[y₀, …, y_m]`. -/
noncomputable def gradedHom : (𝒜 N) →+*ᵍ (𝒜 m) where
  toRingHom := (aeval (coordMap (O := O) e)).toRingHom
  map_mem {i x} hx := by
    have hx' : x.IsHomogeneous i := (mem_homogeneousSubmodule _ _).1 hx
    have := hx'.aeval (coordMap (O := O) e) (isHomogeneous_coordMap e)
    rw [one_mul] at this
    exact (mem_homogeneousSubmodule _ _).2 this

lemma gradedHom_apply (x : MvPolynomial (Fin (N + 1)) O) :
    gradedHom e x = aeval (coordMap (O := O) e) x := rfl

lemma gradedHom_X_apply (i : Fin (m + 1)) : gradedHom (O := O) e (X (e i)) = X i := by
  rw [gradedHom_apply, aeval_X, coordMap_apply]

lemma gradedHom_X_of_notMem {j : Fin (N + 1)} (h : j ∉ Set.range e) :
    gradedHom (O := O) e (X j) = 0 := by
  rw [gradedHom_apply, aeval_X, coordMap_of_notMem e h]

lemma gradedHom_rename (a : MvPolynomial (Fin (m + 1)) O) :
    gradedHom (O := O) e (rename e a) = a := by
  rw [gradedHom_apply, aeval_rename]
  have : coordMap (O := O) e ∘ e = X := funext (coordMap_apply e)
  rw [this, aeval_X_left_apply]

lemma irrelevant_le_span_X {k : ℕ} :
    (HomogeneousIdeal.irrelevant (𝒜 k)).toIdeal ≤
      Ideal.span (Set.range (X : Fin (k + 1) → MvPolynomial (Fin (k + 1)) O)) :=
  ProjScheme.irrelevant_le_span_X

lemma irrelevant_le_map :
    HomogeneousIdeal.irrelevant (𝒜 m) ≤ (HomogeneousIdeal.irrelevant (𝒜 N)).map (gradedHom e) := by
  rw [← toIdeal_le_toIdeal_iff, HomogeneousIdeal.toIdeal_map]
  refine irrelevant_le_span_X.trans (Ideal.span_le.2 ?_)
  rintro _ ⟨i, rfl⟩
  rw [← gradedHom_X_apply]
  refine Ideal.mem_map_of_mem _ ?_
  change GradedRing.proj (𝒜 N) 0 (X (e i)) = 0
  rw [GradedRing.proj_apply]
  have : (X (e i) : MvPolynomial (Fin (N + 1)) O) ∈ (𝒜 N) 1 :=
    (mem_homogeneousSubmodule _ _).2 (isHomogeneous_X O _)
  rw [DirectSum.decompose_of_mem_ne (𝒜 N) this one_ne_zero]

variable (O) in
/-- The linear embedding `ℙᵐ_O ⟶ ℙᴺ_O`. -/
noncomputable def linMap : projSpace O m ⟶ projSpace O N :=
  Proj.map (gradedHom e) (irrelevant_le_map e)

lemma X_mem' {k : ℕ} (j : Fin (k + 1)) : (X j : MvPolynomial (Fin (k + 1)) O) ∈ (𝒜 k) 1 :=
  ProjScheme.X_mem j

lemma awayMap_surjective (j : Fin (N + 1)) :
    Function.Surjective (Away.map (gradedHom (O := O) e) (X j)) := by
  intro z
  by_cases h : j ∈ Set.range e
  · obtain ⟨i, rfl⟩ := h
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (𝒜 m) (map_mem (gradedHom e) (X_mem' (e i))) z
    have ha' : a.IsHomogeneous (n • 1) := (mem_homogeneousSubmodule _ _).1 ha
    refine ⟨Away.mk (𝒜 N) (X_mem' (e i)) n (rename e a)
      ((mem_homogeneousSubmodule _ _).2 (ha'.rename_isHomogeneous)), ?_⟩
    rw [Away.map_mk]
    congr 1
    exact gradedHom_rename e a
  · have : Subsingleton (Localization.Away (gradedHom (O := O) e (X j))) :=
      IsLocalization.subsingleton (M := Submonoid.powers (gradedHom (O := O) e (X j)))
        ⟨1, by dsimp only; rw [pow_one, gradedHom_X_of_notMem e h]⟩
    exact ⟨0, HomogeneousLocalization.val_injective _ (Subsingleton.elim _ _)⟩

lemma isPullback_awayι (j : Fin (N + 1)) :
    IsPullback (Spec.map (CommRingCat.ofHom (Away.map (gradedHom (O := O) e) (X j))))
      (Proj.awayι (𝒜 m) (gradedHom e (X j)) (map_mem (gradedHom e) (X_mem' j)) one_pos)
      (ProjScheme.stdι O N j) (linMap O e) := by
  refine IsOpenImmersion.isPullback _ _ _ _
    (Proj.awayι_comp_map (gradedHom e) (irrelevant_le_map e) one_pos (X j) (X_mem' j))
    ((congrArg (linMap O e ⁻¹ᵁ ·) (Proj.opensRange_awayι (𝒜 N) (X j) (X_mem' j) one_pos)).trans
      (Proj.opensRange_awayι (𝒜 m) _ (map_mem (gradedHom e) (X_mem' j)) one_pos).symm)

variable (O N) in
/-- The standard open cover of `ℙᴺ_O` by the `D₊(x_j)`. -/
noncomputable def stdCover : (projSpace O N).OpenCover :=
  Scheme.Cover.mkOfCovers (Fin (N + 1)) (fun j ↦ Spec (CommRingCat.of (Away (𝒜 N) (X j))))
    (fun j ↦ ProjScheme.stdι O N j) (fun x ↦ by
      have htop := Proj.iSup_basicOpen_eq_top (𝒜 N) _ (irrelevant_le_span_X (O := O) (k := N))
      have hx : x ∈ ⨆ j, Proj.basicOpen (𝒜 N) (X j) := by rw [htop]; trivial
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      rw [← Proj.opensRange_awayι (𝒜 N) (X j) (X_mem' j) one_pos] at hj
      obtain ⟨y, hy⟩ := hj
      exact ⟨j, y, hy⟩)

/-- **The linear embedding is a closed immersion.** -/
instance isClosedImmersion_linMap : IsClosedImmersion (linMap O e) := by
  refine IsZariskiLocalAtTarget.of_openCover (stdCover O N) fun (j : Fin (N + 1)) ↦ ?_
  have h := (isPullback_awayι (O := O) e j).flip
  change IsClosedImmersion (pullback.snd (linMap O e) (ProjScheme.stdι O N j))
  have := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (Away.map (gradedHom (O := O) e) (X j))) (awayMap_surjective (O := O) e j)
  have key : IsClosedImmersion (h.isoPullback.inv ≫
    Spec.map (CommRingCat.ofHom (Away.map (gradedHom (O := O) e) (X j)))) := inferInstance
  exact h.isoPullback_inv_snd ▸ key

lemma linMap_apply (q : projSpace O m) :
    ((linMap O e q : projSpace O N) : ProjectiveSpectrum (𝒜 N)).asHomogeneousIdeal =
      (q : ProjectiveSpectrum (𝒜 m)).asHomogeneousIdeal.comap (gradedHom e) :=
  rfl

lemma exists_X_notMem {k : ℕ} (q : ProjectiveSpectrum (𝒜 k)) :
    ∃ i, (X i : MvPolynomial (Fin (k + 1)) O) ∉ q.asHomogeneousIdeal := by
  by_contra! h
  apply q.not_irrelevant_le
  rw [← toIdeal_le_toIdeal_iff]
  exact irrelevant_le_span_X.trans (Ideal.span_le.2 (Set.range_subset_iff.2 h))

/-- **Linear embeddings with disjoint coordinate ranges have disjoint images.** -/
theorem linMap_ne {m' : ℕ} (e' : Fin (m' + 1) ↪ Fin (N + 1))
    (h : Disjoint (Set.range e) (Set.range e')) (q : projSpace O m) (q' : projSpace O m') :
    linMap O e q ≠ linMap O e' q' := by
  intro hq
  obtain ⟨i, hi⟩ := exists_X_notMem (q : ProjectiveSpectrum (𝒜 m))
  have h₁ : (X (e i) : MvPolynomial (Fin (N + 1)) O) ∉
      ((linMap O e q : projSpace O N) : ProjectiveSpectrum (𝒜 N)).asHomogeneousIdeal := by
    rw [linMap_apply]
    change gradedHom (O := O) e (X (e i)) ∉ (q : ProjectiveSpectrum (𝒜 m)).asHomogeneousIdeal
    rwa [gradedHom_X_apply]
  apply h₁
  rw [hq, linMap_apply]
  change gradedHom (O := O) e' (X (e i)) ∈ (q' : ProjectiveSpectrum (𝒜 m')).asHomogeneousIdeal
  rw [gradedHom_X_of_notMem e' (Set.disjoint_left.1 h ⟨i, rfl⟩)]
  exact zero_mem _

lemma awayMap_fromZeroRingHom_algebraMap (j : Fin (N + 1)) (o : O) :
    Away.map (gradedHom (O := O) e) (X j)
      (fromZeroRingHom (𝒜 N) _ (algebraMap O ((𝒜 N) 0) o)) =
    fromZeroRingHom (𝒜 m) _ (algebraMap O ((𝒜 m) 0) o) := by
  apply HomogeneousLocalization.val_injective
  change Localization.mk _ _ = Localization.mk _ _
  congr 1
  · change gradedHom e (C o) = C o
    rw [gradedHom_apply, aeval_C]
    rfl
  · ext1
    change gradedHom e 1 = 1
    exact map_one _

lemma awayι_toSpec {k : ℕ} {s : MvPolynomial (Fin (k + 1)) O} (hs : s ∈ (𝒜 k) 1) :
    Proj.awayι (𝒜 k) s hs one_pos ≫ projSpace.toSpec O k = Spec.map (CommRingCat.ofHom
      ((fromZeroRingHom (𝒜 k) (Submonoid.powers s)).comp (algebraMap O ((𝒜 k) 0)))) := by
  change Proj.awayι (𝒜 k) s hs one_pos ≫ Proj.toSpecZero _ ≫ _ = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp, CommRingCat.ofHom_comp]

/-- **The linear embedding lies over `Spec O`.** -/
theorem linMap_toSpec : linMap O e ≫ projSpace.toSpec O N = projSpace.toSpec O m := by
  have hcov (x : projSpace O m) : ∃ (j : Fin (N + 1)) (y : Spec (CommRingCat.of
      (Away (𝒜 m) (gradedHom e (X j))))),
      Proj.awayι (𝒜 m) (gradedHom e (X j)) (map_mem (gradedHom e) (X_mem' j)) one_pos y = x := by
    obtain ⟨i, hi⟩ := exists_X_notMem (x : ProjectiveSpectrum (𝒜 m))
    have : x ∈ Proj.basicOpen (𝒜 m) (gradedHom (O := O) e (X (e i))) := by
      rw [gradedHom_X_apply]; exact hi
    rw [← Proj.opensRange_awayι (𝒜 m) _ (map_mem (gradedHom e) (X_mem' (e i))) one_pos] at this
    obtain ⟨y, hy⟩ := this
    exact ⟨e i, y, hy⟩
  let 𝒱 : (projSpace O m).OpenCover := Scheme.Cover.mkOfCovers (Fin (N + 1))
    (fun j ↦ Spec (CommRingCat.of (Away (𝒜 m) (gradedHom e (X j)))))
    (fun j ↦ Proj.awayι (𝒜 m) (gradedHom e (X j)) (map_mem (gradedHom e) (X_mem' j)) one_pos)
    hcov (fun j ↦ inferInstanceAs (IsOpenImmersion
      (Proj.awayι (𝒜 m) (gradedHom e (X j)) (map_mem (gradedHom e) (X_mem' j)) one_pos)))
  refine 𝒱.hom_ext _ _ fun (j : Fin (N + 1)) ↦ ?_
  have h1 : Proj.awayι (𝒜 m) _ (map_mem (gradedHom e) (X_mem' j)) one_pos ≫ linMap O e =
      Spec.map (CommRingCat.ofHom (Away.map (gradedHom e) (X j))) ≫ ProjScheme.stdι O N j :=
    Proj.awayι_comp_map (gradedHom e) (irrelevant_le_map e) one_pos (X j) (X_mem' j)
  change Proj.awayι (𝒜 m) _ (map_mem (gradedHom e) (X_mem' j)) one_pos ≫ linMap O e ≫ _ =
    Proj.awayι (𝒜 m) _ (map_mem (gradedHom e) (X_mem' j)) one_pos ≫ _
  rw [reassoc_of% h1, ProjScheme.stdι_toSpec, awayι_toSpec, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (RingHom.ext fun o ↦ awayMap_fromZeroRingHom_algebraMap e j o)

end LinearEmbedding

section SigmaClosed

open scoped Function

variable {σ : Type*} [Small.{u} σ] [Finite σ] (Y : σ → Scheme.{u})

/-- A finite family of closed immersions with pairwise disjoint images glues to a closed immersion
of the coproduct. -/
theorem isClosedImmersion_sigmaDesc {P : Scheme.{u}} (α : ∀ i, Y i ⟶ P)
    [∀ i, IsClosedImmersion (α i)] (hα : Pairwise (Disjoint on (Set.range <| α ·))) :
    IsClosedImmersion (Sigma.desc α) := by
  have hS : SurjectiveOnStalks (Sigma.desc α) := by
    refine IsZariskiLocalAtSource.of_openCover (sigmaOpenCover Y) fun (i : σ) ↦ ?_
    change SurjectiveOnStalks (Sigma.ι Y i ≫ Sigma.desc α)
    rw [Sigma.ι_desc]
    infer_instance
  have hpt (x : (∐ Y : Scheme.{u})) : ∃ i y, Sigma.ι Y i y = x := (sigmaOpenCover Y).exists_eq x
  have happ (i) (y : Y i) : Sigma.desc α (Sigma.ι Y i y) = α i y := by
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc]
  refine { toSurjectiveOnStalks := hS, isClosedEmbedding := ?_ }
  refine .of_continuous_injective_isClosedMap (Sigma.desc α).continuous ?_ ?_
  · intro x x' h
    obtain ⟨i, y, rfl⟩ := hpt x
    obtain ⟨j, y', rfl⟩ := hpt x'
    rw [happ, happ] at h
    obtain rfl : i = j := by
      by_contra hij
      exact Set.disjoint_iff_forall_ne.mp (hα hij) ⟨y, rfl⟩ ⟨y', h.symm⟩ rfl
    rw [(α i).isClosedEmbedding.injective h]
  · intro C hC
    have : Sigma.desc α '' C = ⋃ i, α i '' (Sigma.ι Y i ⁻¹' C) := by
      ext z
      simp only [Set.mem_image, Set.mem_iUnion, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        obtain ⟨i, y, rfl⟩ := hpt x
        exact ⟨i, y, hx, (happ i y).symm⟩
      · rintro ⟨i, y, hy, rfl⟩
        exact ⟨_, hy, happ i y⟩
    rw [this]
    exact isClosed_iUnion_of_finite fun i ↦
      (α i).isClosedEmbedding.isClosedMap _ (hC.preimage (Sigma.ι Y i).continuous)

end SigmaClosed

namespace ModelCode

open LinearEmbedding

variable {O : Type u} [CommRing O] {r : ℕ} (c : Fin r → TemperedFundamentalGroups.ModelCode O)

/-- The ambient dimension of the disjoint union: `ℙᴺ` with `N + 1 = ∑ (m_k + 1) + 1`. -/
def sigmaDim : ℕ := ∑ k, ((c k).m + 1)

/-- The block of coordinates of the `k`-th summand. -/
def sigmaEmb (k : Fin r) : Fin ((c k).m + 1) ↪ Fin (sigmaDim c + 1) where
  toFun i := Fin.castSucc (finSigmaFinEquiv (n := fun k ↦ (c k).m + 1) ⟨k, i⟩)
  inj' i i' h := by
    have := finSigmaFinEquiv.injective (Fin.castSucc_injective _ h)
    simpa using this

lemma disjoint_range_sigmaEmb {k l : Fin r} (h : k ≠ l) :
    Disjoint (Set.range (sigmaEmb c k)) (Set.range (sigmaEmb c l)) := by
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ e
  have := congrArg Sigma.fst (finSigmaFinEquiv.injective (Fin.castSucc_injective _ e))
  exact h this

/-- The closed immersion of the `k`-th summand into `ℙᴺ_O`. -/
noncomputable def sigmaIncl (k : Fin r) : (c k).scheme ⟶ projSpace O (sigmaDim c) :=
  (c k).I.subschemeι ≫ linMap O (sigmaEmb c k)

instance (k : Fin r) : IsClosedImmersion (sigmaIncl c k) := by
  have h₁ : IsClosedImmersion (c k).I.subschemeι := inferInstance
  have h₂ := isClosedImmersion_linMap (O := O) (sigmaEmb c k)
  exact MorphismProperty.comp_mem @IsClosedImmersion _ _ h₁ h₂

/-- The closed immersion `∐ c_k ⟶ ℙᴺ_O`. -/
noncomputable def sigmaMap : (∐ fun k ↦ (c k).scheme) ⟶ projSpace O (sigmaDim c) :=
  Sigma.desc (sigmaIncl c)

instance isClosedImmersion_sigmaMap : IsClosedImmersion (sigmaMap c) := by
  refine isClosedImmersion_sigmaDesc _ _ fun k l hkl ↦ ?_
  change Disjoint (Set.range (sigmaIncl c k)) (Set.range (sigmaIncl c l))
  rw [Set.disjoint_iff_forall_ne]
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  simp only [sigmaIncl, Scheme.Hom.comp_apply]
  exact linMap_ne _ _ (disjoint_range_sigmaEmb c hkl) _ _

/-- **(3b) The disjoint union of finitely many model codes**, as one model code: the image of
`∐ c_k ⟶ ℙᴺ_O` (the summands embedded linearly in disjoint blocks of coordinates). -/
noncomputable def sigma : TemperedFundamentalGroups.ModelCode O :=
  ⟨sigmaDim c, (sigmaMap c).ker⟩

/-- **(3b)** The disjoint union code is the coproduct. -/
noncomputable def sigmaIso : (∐ fun k ↦ (c k).scheme) ≅ (sigma c).scheme :=
  @asIso _ _ _ _ (sigmaMap c).toImage
    (IsClosedImmersion.instIsIsoSchemeToImage (sigmaMap c))

/-- The summand inclusions `c_k ⟶ sigma c`. -/
noncomputable def sigmaι (k : Fin r) : (c k).scheme ⟶ (sigma c).scheme :=
  Sigma.ι (fun k ↦ (c k).scheme) k ≫ (sigmaIso c).hom

instance (k : Fin r) : IsOpenImmersion (sigmaι c k) :=
  have : IsOpenImmersion (Sigma.ι (fun k ↦ (c k).scheme) k) :=
    (sigmaOpenCover (fun k ↦ (c k).scheme)).map_prop k
  IsOpenImmersion.comp _ _

/-- **(3b)** The disjoint union code lies over `Spec O`: its summands are over `Spec O`. -/
theorem sigmaι_toSpec (k : Fin r) : sigmaι c k ≫ (sigma c).toSpec = (c k).toSpec := by
  change Sigma.ι (fun k ↦ (c k).scheme) k ≫ (sigmaMap c).toImage ≫ (sigmaMap c).imageι ≫
    projSpace.toSpec O _ = _
  rw [Scheme.Hom.toImage_imageι_assoc, sigmaMap, Sigma.ι_desc_assoc, sigmaIncl, Category.assoc,
    linMap_toSpec]
  rfl

lemma sigma_hom_ext {Z : Scheme.{u}} {a b : (sigma c).scheme ⟶ Z}
    (h : ∀ k, sigmaι c k ≫ a = sigmaι c k ≫ b) : a = b := by
  rw [← cancel_epi (sigmaIso c).hom]
  exact Sigma.hom_ext _ _ fun k ↦ by simpa [sigmaι] using h k

end ModelCode

end SemistableReduction
