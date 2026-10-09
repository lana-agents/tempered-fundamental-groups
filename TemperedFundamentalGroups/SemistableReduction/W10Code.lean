/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Sigma
import TemperedFundamentalGroups.SemistableReduction.W10Scheme

/-!
# Base change along several generators; closed immersions into model codes

Blueprint §9.7 (W10 assembly, scheme realization).

* **(T2) Multi-θ base change** `ProjScheme.baseChangeIsoFin`: for `O → O'` whose image `R'` in `F`
  lies in `R[θ_1, …, θ_r]` (`θ_s ≠ 0` integral over `O`, `θ_s ∈ R'`, `R ⊆ R'`), the projective
  `O'`-model of `g` is isomorphic to the projective `O`-model of the family of all products
  `θ_s g_l` (`θ_0 = 1`, `thetasFamily`), compatibly with the generic points
  (`genericPt_comp_baseChangeIsoFin`) and over `Spec O` (`baseChangeIsoFin_toSpec`). This
  generalizes `ProjScheme.baseChangeIso` (one generator), e.g. to `O_E` finite over a complete DVR
  but not monogenic.
* **(T4) Closed immersions into a model code** `exists_closedImmersion_projModelCode`: an
  `F`-point `j₀` of a model code `c₀` over `Spec O` is the generic point of a projective model code
  `projModelCode O hf` embedded into `c₀` by a closed immersion over `Spec O`. The point lands in a
  standard chart `D₊(x_i)` (`exists_chart`); ring maps out of `(O[x]_{x_i})₀` are determined by
  `O` and the `x_k / x_i` (`away_ringHom_ext`), so the point has coordinates `f` (`f_i = 1`); the
  nonzero ones give `toProj` followed by a linear embedding (`toProj_linMap`), and `ι` is the
  induced map of scheme-theoretic images (`IdealSheafData.subschemeMap`).
-/

universe u

open CategoryTheory AlgebraicGeometry Limits

namespace SemistableReduction

open TemperedFundamentalGroups ProjScheme

namespace ProjScheme

section BaseChangeFin

variable {r n : ℕ}

/-- The index set of `thetasFamily`: pairs `(s, l)` with `s ≤ r`, `l ≤ n`. -/
def thetasEquiv (r n : ℕ) : Fin ((r + 1) * n + r + 1) ≃ Fin (r + 1) × Fin (n + 1) :=
  (finCongr (by ring)).trans finProdFinEquiv.symm

/-- The family of all products `θ_s g_l`, where `θ_0 = 1`. -/
def thetasFamily {F : Type*} [MulOneClass F] (θ : Fin r → F) (g : Fin (n + 1) → F) :
    Fin ((r + 1) * n + r + 1) → F :=
  fun k ↦ (Fin.cons 1 θ : Fin (r + 1) → F) (thetasEquiv r n k).1 * g (thetasEquiv r n k).2

lemma thetasFamily_apply {F : Type*} [MulOneClass F] (θ : Fin r → F) (g : Fin (n + 1) → F)
    (s : Fin (r + 1)) (l : Fin (n + 1)) :
    thetasFamily θ g ((thetasEquiv r n).symm (s, l)) =
      (Fin.cons 1 θ : Fin (r + 1) → F) s * g l := by
  simp [thetasFamily]

lemma thetasFamily_ne_zero {F : Type*} [Field F] {θ : Fin r → F} (hθ0 : ∀ s, θ s ≠ 0)
    {g : Fin (n + 1) → F} (hg : ∀ j, g j ≠ 0) (k : Fin ((r + 1) * n + r + 1)) :
    thetasFamily θ g k ≠ 0 := by
  refine mul_ne_zero ?_ (hg _)
  refine Fin.cases (motive := fun s ↦ (Fin.cons 1 θ : Fin (r + 1) → F) s ≠ 0) ?_ (fun s ↦ ?_) _
  · simp
  · simpa using hθ0 s

variable {O O' : Type u} [CommRing O] [CommRing O'] {F : Type u} [Field F] [Algebra O F]
  [Algebra O' F] {g : Fin (n + 1) → F} {R R' : Subring F} {θ : Fin r → F}

lemma cons_mem {A : Subring F} (h : ∀ s, θ s ∈ A) (s : Fin (r + 1)) :
    (Fin.cons 1 θ : Fin (r + 1) → F) s ∈ A :=
  Fin.cases (motive := fun s ↦ (Fin.cons 1 θ : Fin (r + 1) → F) s ∈ A) (by simp [one_mem])
    (fun s ↦ by simpa using h s) s

omit [Algebra O F] [Algebra O' F] in
lemma dominates_thetasFamily (hθR' : ∀ s, θ s ∈ R') (hRR' : R ≤ R') :
    Dominates R R' (RingHom.id F) (thetasFamily θ g) g := by
  refine dominates_of_forall _ _ (fun x hx ↦ hRR' hx) fun j ↦
    ⟨(thetasEquiv r n).symm (0, j), fun k ↦ ?_⟩
  obtain ⟨⟨s, l⟩, rfl⟩ := (thetasEquiv r n).symm.surjective k
  rw [thetasFamily_apply, thetasFamily_apply, RingHom.id_apply, Fin.cons_zero, one_mul,
    mul_div_assoc]
  exact mul_mem (base_le_projChart j (cons_mem hθR' s)) (div_mem_projChart j l)

lemma thetasFamily_dominates (hR : (algebraMap O F).range = R) (hθ0 : ∀ s, θ s ≠ 0)
    (hθ : ∀ s, IsIntegral O (θ s)) (hg : ∀ j, g j ≠ 0)
    (hR' : R' ≤ Subring.closure ((R : Set F) ∪ Set.range θ)) :
    Dominates R' R (RingHom.id F) g (thetasFamily θ g) := by
  set θ' : Fin (r + 1) → F := Fin.cons 1 θ
  set e := thetasEquiv r n
  have hθ'0 (s : Fin (r + 1)) : θ' s ≠ 0 :=
    Fin.cases (motive := fun s ↦ θ' s ≠ 0) (by simp [θ']) (fun s ↦ by simpa [θ'] using hθ0 s) s
  intro k
  obtain ⟨⟨s, j⟩, rfl⟩ := e.symm.surjective k
  -- the ratios `θ' t / θ' s` lie in the chart
  have hratio (t : Fin (r + 1)) : θ' t / θ' s ∈ projChart R (thetasFamily θ g) (e.symm (s, j)) := by
    have := div_mem_projChart (R := R) (f := thetasFamily θ g) (e.symm (s, j)) (e.symm (t, j))
    rwa [thetasFamily_apply, thetasFamily_apply, mul_div_mul_right _ _ (hg j)] at this
  have hs : θ' s ∈ projChart R (thetasFamily θ g) (e.symm (s, j)) := by
    refine Fin.cases (motive := fun s' ↦ s' = s → θ' s ∈ _) (fun h ↦ ?_) (fun s' h ↦ ?_) s rfl
    · subst h
      simp [θ', one_mem]
    · subst h
      refine mem_of_inv_mem_of_isIntegral (O := O) (fun o ↦ base_le_projChart _
        (hR ▸ ⟨o, rfl⟩)) (by simpa [θ'] using hθ s') ?_
      have := hratio 0
      rwa [show θ' 0 = 1 from rfl, one_div] at this
  have hbase : ∀ x ∈ R', x ∈ projChart R (thetasFamily θ g) (e.symm (s, j)) := by
    refine fun x hx ↦ (Subring.closure_le.2 (Set.union_subset (base_le_projChart _) ?_)) (hR' hx)
    rintro _ ⟨t, rfl⟩
    have h := mul_mem (hratio t.succ) hs
    rwa [div_mul_cancel₀ _ (hθ'0 s)] at h
  refine ⟨j, fun x hx ↦ (projChart_le hbase fun l ↦ ?_) hx⟩
  have := div_mem_projChart (R := R) (f := thetasFamily θ g) (e.symm (s, j)) (e.symm (s, l))
  rwa [thetasFamily_apply, thetasFamily_apply, mul_div_mul_left _ _ (hθ'0 s)] at this

variable (hR : (algebraMap O F).range = R) (hR' : (algebraMap O' F).range = R')
  (hθ0 : ∀ s, θ s ≠ 0) (hθ : ∀ s, IsIntegral O (θ s)) (hθR' : ∀ s, θ s ∈ R')
  (hR'le : R' ≤ Subring.closure ((R : Set F) ∪ Set.range θ)) (hRR' : R ≤ R')
  (hg : ∀ j, g j ≠ 0)

/-- **(T2) Base change along several generators.** If the image `R'` of `O'` in `F` lies in
`R[θ_1, …, θ_r]` (`θ_s ≠ 0` integral over `O`, `θ_s ∈ R'`, `R ⊆ R'`), the projective `O'`-model
of `g` is isomorphic to the projective `O`-model of `(θ_s g_l)_{s, l}` (`θ_0 = 1`). -/
noncomputable def baseChangeIsoFin :
    (projModelCode O (thetasFamily_ne_zero hθ0 hg)).scheme ≅ (projModelCode O' hg).scheme :=
  isoOfDominates hR' hR hg (thetasFamily_ne_zero hθ0 hg) (RingEquiv.refl F)
    (thetasFamily_dominates hR hθ0 hθ hg hR'le) (dominates_thetasFamily hθR' hRR')

theorem genericPt_comp_baseChangeIsoFin :
    genericPt O (thetasFamily_ne_zero hθ0 hg) ≫
        (baseChangeIsoFin hR hR' hθ0 hθ hθR' hR'le hRR' hg).hom =
      genericPt O' hg := by
  rw [baseChangeIsoFin, isoOfDominates_hom, genericPt_comp_homOfDominates]
  exact (congrArg (· ≫ genericPt O' hg) (Spec.map_id (CommRingCat.of F))).trans
    (Category.id_comp _)

theorem baseChangeIsoFin_toSpec [Algebra O O'] [IsScalarTower O O' F] :
    (baseChangeIsoFin hR hR' hθ0 hθ hθR' hR'le hRR' hg).hom ≫ (projModelCode O' hg).toSpec ≫
      Spec.map (CommRingCat.ofHom (algebraMap O O')) =
      (projModelCode O (thetasFamily_ne_zero hθ0 hg)).toSpec := by
  refine hom_ext_genericPt _ ?_
  rw [reassoc_of% genericPt_comp_baseChangeIsoFin, reassoc_of% genericPt_toSpec,
    genericPt_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

end BaseChangeFin

end ProjScheme

section ClosedImmersion

open MvPolynomial HomogeneousLocalization Graded

attribute [local instance] MvPolynomial.gradedAlgebra

lemma eval₂_mul_of_isHomogeneous {σ R S : Type*} [Finite σ] [CommSemiring R] [CommSemiring S]
    (h : R →+* S) (x : σ → S) (w : S) {a : MvPolynomial σ R} {n : ℕ} (ha : a.IsHomogeneous n) :
    eval₂ h (fun k ↦ x k * w) a = w ^ n * eval₂ h x a := by
  have := Fintype.ofFinite σ
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  by_cases hd : coeff d a = 0
  · simp [hd]
  have hdeg : d.degree = n := by
    by_contra h
    exact hd (ha.coeff_eq_zero h)
  rw [Finsupp.degree_eq_sum] at hdeg
  simp_rw [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring

variable {O : Type u} [CommRing O] {N : ℕ}

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

lemma X_mem_one_smul (k : Fin (N + 1)) :
    (X k : MvPolynomial (Fin (N + 1)) O) ∈ (𝒜 N) (1 • 1) := by
  simpa using ProjScheme.X_mem (O := O) k

variable (O) in
/-- The element `x_k / x_i` of `(O[x]_{x_i})₀`. -/
noncomputable def awayX (i k : Fin (N + 1)) : Away (𝒜 N) (X i) :=
  Away.mk (𝒜 N) (ProjScheme.X_mem i) 1 (X k) (X_mem_one_smul k)

variable (O) in
/-- The element `1 / x_i` of `O[x]_{x_i}`. -/
noncomputable def invX (i : Fin (N + 1)) :
    Localization.Away (X i : MvPolynomial (Fin (N + 1)) O) :=
  Localization.mk 1 ⟨X i, Submonoid.mem_powers _⟩

lemma localization_mk_eq (i : Fin (N + 1)) (a : MvPolynomial (Fin (N + 1)) O) (n : ℕ)
    (h : X i ^ n ∈ Submonoid.powers (X i : MvPolynomial (Fin (N + 1)) O)) :
    (Localization.mk a ⟨X i ^ n, h⟩ : Localization.Away (X i : MvPolynomial (Fin (N + 1)) O)) =
      algebraMap (MvPolynomial (Fin (N + 1)) O)
        (Localization.Away (X i : MvPolynomial (Fin (N + 1)) O)) a * invX O i ^ n := by
  rw [invX, Localization.mk_pow, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul,
    one_pow, mul_one, one_mul]
  congr 1

lemma away_mk_eq_eval₂ (i : Fin (N + 1)) (n : ℕ) (a : MvPolynomial (Fin (N + 1)) O)
    (ha : a ∈ (𝒜 N) (n • 1)) :
    Away.mk (𝒜 N) (ProjScheme.X_mem i) n a ha =
      eval₂ ((fromZeroRingHom (𝒜 N) _).comp (algebraMap O ((𝒜 N) 0))) (awayX O i) a := by
  apply HomogeneousLocalization.val_injective
  have ha' : a.IsHomogeneous n := by simpa using ha
  set L := Localization.Away (X i : MvPolynomial (Fin (N + 1)) O)
  have h1 : (algebraMap (Away (𝒜 N) (X i)) L).comp
      ((fromZeroRingHom (𝒜 N) _).comp (algebraMap O ((𝒜 N) 0))) =
      (algebraMap (MvPolynomial (Fin (N + 1)) O) L).comp C := by
    ext o
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← Localization.mk_one_eq_algebraMap]
    rfl
  have h2 : (algebraMap (Away (𝒜 N) (X i)) L) ∘ awayX O i = fun k ↦
      algebraMap (MvPolynomial (Fin (N + 1)) O) L (X k) * invX O i := by
    funext k
    rw [Function.comp_apply, HomogeneousLocalization.algebraMap_apply, awayX, Away.val_mk,
      localization_mk_eq, pow_one]
  rw [← HomogeneousLocalization.algebraMap_apply, ← HomogeneousLocalization.algebraMap_apply,
    eval₂_comp_left, h1, h2, eval₂_mul_of_isHomogeneous _ _ _ ha',
    show (fun k ↦ algebraMap (MvPolynomial (Fin (N + 1)) O) L (X k)) =
      algebraMap (MvPolynomial (Fin (N + 1)) O) L ∘ X from rfl, ← eval₂_comp_left, eval₂_eta,
    HomogeneousLocalization.algebraMap_apply, Away.val_mk, localization_mk_eq, mul_comm]

/-- Ring maps out of `(O[x]_{x_i})₀` agree if they agree on `O` and on the `x_k / x_i`. -/
lemma away_ringHom_ext {A : Type*} [CommRing A] (i : Fin (N + 1)) {ψ₁ ψ₂ : Away (𝒜 N) (X i) →+* A}
    (hO : ψ₁.comp ((fromZeroRingHom (𝒜 N) _).comp (algebraMap O ((𝒜 N) 0))) =
      ψ₂.comp ((fromZeroRingHom (𝒜 N) _).comp (algebraMap O ((𝒜 N) 0))))
    (hX : ∀ k, ψ₁ (awayX O i k) = ψ₂ (awayX O i k)) : ψ₁ = ψ₂ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (𝒜 N) (ProjScheme.X_mem i) z
  rw [away_mk_eq_eval₂, eval₂_comp_left, eval₂_comp_left, hO]
  congr 1
  funext k
  exact hX k


lemma awayX_self (i : Fin (N + 1)) : awayX O i i = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [awayX, Away.val_mk, HomogeneousLocalization.val_one]
  convert Localization.mk_self (⟨X i ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers
    (X i : MvPolynomial (Fin (N + 1)) O)) using 2
  simp

variable {F : Type u} [Field F] [Algebra O F]

lemma fromZero_algebraMap_eq (i : Fin (N + 1)) (o : O) :
    (fromZeroRingHom (𝒜 N) (Submonoid.powers (X i))) (algebraMap O ((𝒜 N) 0) o) =
      Away.mk (𝒜 N) (ProjScheme.X_mem i) 0 (C o) (by simp) := by
  rw [away_mk_eq_eval₂, eval₂_C]
  rfl

omit [Algebra O F] in
/-- **Coordinates of an `F`-point of `ℙᴺ_O`**: it factors through a standard chart `D₊(x_i)`. -/
lemma exists_chart (J : Spec (CommRingCat.of F) ⟶ projSpace O N) :
    ∃ (i : Fin (N + 1)) (φ : Away (𝒜 N) (X i) →+* F),
      J = Spec.map (CommRingCat.ofHom φ) ≫ ProjScheme.stdι O N i := by
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of F)) := inferInstance
  have htop := Proj.iSup_basicOpen_eq_top (𝒜 N) _ (ProjScheme.irrelevant_le_span_X (O := O)
    (m := N))
  have hx : J x ∈ ⨆ i, Proj.basicOpen (𝒜 N) (X i) := by rw [htop]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have hr : Set.range J ⊆ Set.range (ProjScheme.stdι O N i) := by
    rintro _ ⟨y, rfl⟩
    rw [Subsingleton.elim y x]
    rw [← Proj.opensRange_awayι (𝒜 N) (X i) (ProjScheme.X_mem i) one_pos] at hi
    exact hi
  refine ⟨i, (Spec.preimage (IsOpenImmersion.lift (ProjScheme.stdι O N i) J hr)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

lemma evalHom_gradedHom {m : ℕ} (e : Fin (m + 1) ↪ Fin (N + 1)) (f : Fin (N + 1) → F)
    (hf0 : ∀ j ∉ Set.range e, f j = 0) (a : MvPolynomial (Fin (N + 1)) O) :
    ProjScheme.evalHom (fun k ↦ f (e k)) (LinearEmbedding.gradedHom e a) =
      ProjScheme.evalHom f a := by
  induction a using MvPolynomial.induction_on with
  | C o =>
    rw [LinearEmbedding.gradedHom_apply, aeval_C, MvPolynomial.algebraMap_eq]
    simp [ProjScheme.evalHom]
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add]
  | mul_X p j hp =>
    rw [map_mul, map_mul, hp, map_mul]
    congr 1
    by_cases hj : j ∈ Set.range e
    · obtain ⟨k, rfl⟩ := hj
      rw [LinearEmbedding.gradedHom_X_apply]
      simp [ProjScheme.evalHom]
    · rw [LinearEmbedding.gradedHom_X_of_notMem e hj]
      simp [ProjScheme.evalHom, hf0 j hj]

/-- The point with coordinates `f ∘ e`, followed by the linear embedding `e`, is the point with
coordinates `f` (when `f` vanishes off the range of `e`), on the chart `D₊(x_i)`. -/
lemma toProj_linMap {m : ℕ} (e : Fin (m + 1) ↪ Fin (N + 1)) (f : Fin (N + 1) → F)
    (hf0 : ∀ j ∉ Set.range e, f j = 0) (hf : ∀ k, f (e k) ≠ 0) {i : Fin (N + 1)} (k0 : Fin (m + 1))
    (hk0 : e k0 = i) (hu : IsUnit (ProjScheme.evalHom f (X i : MvPolynomial (Fin (N + 1)) O))) :
    ProjScheme.toProj O (f := fun k ↦ f (e k)) hf ≫ LinearEmbedding.linMap O e =
      Spec.map (CommRingCat.ofHom (ProjScheme.awayEval f (X i) hu)) ≫ ProjScheme.stdι O N i := by
  subst hk0
  have hs : (X k0 : MvPolynomial (Fin (m + 1)) O) = LinearEmbedding.gradedHom e (X (e k0)) :=
    (LinearEmbedding.gradedHom_X_apply e k0).symm
  have hu' : IsUnit (ProjScheme.evalHom (fun k ↦ f (e k))
      (LinearEmbedding.gradedHom e (X (e k0)) : MvPolynomial (Fin (m + 1)) O)) := by
    rwa [evalHom_gradedHom e f hf0]
  have h1 : Proj.awayι (𝒜 m) _ (map_mem (LinearEmbedding.gradedHom e)
      (LinearEmbedding.X_mem' (e k0))) one_pos ≫ LinearEmbedding.linMap O e =
      Spec.map (CommRingCat.ofHom (Away.map (LinearEmbedding.gradedHom e) (X (e k0)))) ≫
        ProjScheme.stdι O N (e k0) :=
    Proj.awayι_comp_map (LinearEmbedding.gradedHom e) (LinearEmbedding.irrelevant_le_map e)
      one_pos (X (e k0)) (LinearEmbedding.X_mem' (e k0))
  rw [ProjScheme.toProj_eq hf k0]
  change (Spec.map _ ≫ Proj.awayι (𝒜 m) (X k0) (ProjScheme.X_mem k0) one_pos) ≫ _ = _
  rw [ProjScheme.SpecMap_awayEval_awayι_congr hs _ hu' _
      (map_mem (LinearEmbedding.gradedHom e) (LinearEmbedding.X_mem' (e k0))) one_pos,
    Category.assoc, h1, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (𝒜 N) (ProjScheme.X_mem (e k0)) z
  rw [RingHom.comp_apply, Away.map_mk, ProjScheme.awayEval_mk, ProjScheme.awayEval_mk,
    evalHom_gradedHom e f hf0, evalHom_gradedHom e f hf0]


/-- **(T4) Closed immersions into a given model code.** An `F`-point `j₀` of a model code `c₀`
over `Spec O` is the generic point of a projective model code `projModelCode O hf` (with
`hf : ∀ i, f i ≠ 0`) which embeds into `c₀` by a closed immersion `ι` over `Spec O`. (The
coordinates `f` are the nonzero homogeneous coordinates of `j₀` in the ambient `ℙᵐ_O` of `c₀`,
and `ι` is the restriction of the corresponding linear embedding.) -/
theorem exists_closedImmersion_projModelCode (c₀ : TemperedFundamentalGroups.ModelCode O)
    (j₀ : Spec (CommRingCat.of F) ⟶ c₀.scheme)
    (hj₀ : j₀ ≫ c₀.toSpec = Spec.map (CommRingCat.ofHom (algebraMap O F))) :
    ∃ (n : ℕ) (f : Fin (n + 1) → F) (hf : ∀ i, f i ≠ 0)
      (ι : (ProjScheme.projModelCode O hf).scheme ⟶ c₀.scheme), IsClosedImmersion ι ∧
      ProjScheme.genericPt O hf ≫ ι = j₀ ∧
      ι ≫ c₀.toSpec = (ProjScheme.projModelCode O hf).toSpec := by
  classical
  set J := j₀ ≫ c₀.I.subschemeι with hJdef
  have hJ : J ≫ projSpace.toSpec O c₀.m = Spec.map (CommRingCat.ofHom (algebraMap O F)) := by
    rw [hJdef, Category.assoc]
    exact hj₀
  obtain ⟨i, φ, hφ⟩ := exists_chart J
  have hφO : φ.comp ((fromZeroRingHom (𝒜 c₀.m) _).comp (algebraMap O ((𝒜 c₀.m) 0))) =
      algebraMap O F := by
    have h := hJ
    rw [hφ, Category.assoc, ProjScheme.stdι_toSpec, ← Spec.map_comp] at h
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h)
  set f : Fin (c₀.m + 1) → F := fun k ↦ φ (awayX O i k) with hfdef
  have hfi : f i = 1 := by simp [hfdef, awayX_self]
  have hu : IsUnit (ProjScheme.evalHom f (X i : MvPolynomial (Fin (c₀.m + 1)) O)) := by
    simp [ProjScheme.evalHom, hfi]
  have hφeq : φ = ProjScheme.awayEval f (X i) hu := by
    refine away_ringHom_ext i ?_ fun k ↦ ?_
    · rw [hφO]
      ext o
      rw [RingHom.comp_apply, RingHom.comp_apply, fromZero_algebraMap_eq, ProjScheme.awayEval_mk]
      simp [ProjScheme.evalHom]
    · conv_rhs => rw [awayX, ProjScheme.awayEval_mk]
      simp only [ProjScheme.evalHom, coe_eval₂Hom, eval₂_X, pow_one, hfi, div_one]
      rfl
  set S := Finset.univ.filter (fun k ↦ f k ≠ 0) with hS
  have hiS : i ∈ S := by simp [hS, hfi]
  set n := S.card - 1
  have hcard : S.card = n + 1 := (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 ⟨i, hiS⟩)).symm
  let e : Fin (n + 1) ↪ Fin (c₀.m + 1) := (S.orderEmbOfFin hcard).toEmbedding
  have hrange : Set.range e = S := Finset.range_orderEmbOfFin S hcard
  have hf' (k : Fin (n + 1)) : f (e k) ≠ 0 :=
    (Finset.mem_filter.1 (S.orderEmbOfFin_mem hcard k)).2
  have hf0 : ∀ j ∉ Set.range e, f j = 0 := by
    intro j hj
    rw [hrange] at hj
    by_contra h
    exact hj (by simp [hS, h])
  obtain ⟨k0, hk0⟩ : i ∈ Set.range e := by rw [hrange]; exact hiS
  have hJeq : J = ProjScheme.toProj O (f := fun k ↦ f (e k)) hf' ≫ LinearEmbedding.linMap O e := by
    rw [toProj_linMap e f hf0 hf' k0 hk0 hu, hφ, hφeq]
  have H : c₀.I ≤ (ProjScheme.toProj O (f := fun k ↦ f (e k)) hf').ker.map
      (LinearEmbedding.linMap O e) := by
    rw [Scheme.IdealSheafData.map_ker, ← hJeq]
    calc c₀.I = c₀.I.subschemeι.ker := (Scheme.IdealSheafData.ker_subschemeι _).symm
      _ = (⊥ : Scheme.IdealSheafData _).map c₀.I.subschemeι :=
        (Scheme.IdealSheafData.map_bot _).symm
      _ ≤ j₀.ker.map c₀.I.subschemeι := Scheme.IdealSheafData.map_mono _ bot_le
      _ = J.ker := Scheme.IdealSheafData.map_ker _ _
  let ι := Scheme.IdealSheafData.subschemeMap _ c₀.I (LinearEmbedding.linMap O e) H
  have hι : ι ≫ c₀.I.subschemeι =
      (ProjScheme.toProj O (f := fun k ↦ f (e k)) hf').imageι ≫ LinearEmbedding.linMap O e :=
    Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ _
  refine ⟨n, _, hf', ι, ?_, ?_, ?_⟩
  · haveI : IsClosedImmersion (ι ≫ c₀.I.subschemeι) := by rw [hι]; infer_instance
    exact IsClosedImmersion.of_comp_isClosedImmersion ι c₀.I.subschemeι
  · have h := congrArg (ProjScheme.genericPt O hf' ≫ ·) hι
    refine (cancel_mono c₀.I.subschemeι).1 ((Category.assoc _ _ _).trans (h.trans ?_))
    change (ProjScheme.toProj O _).toImage ≫ (ProjScheme.toProj O _).imageι ≫ _ = J
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, ← hJeq]
  · change ι ≫ c₀.I.subschemeι ≫ projSpace.toSpec O c₀.m =
      (ProjScheme.toProj O _).imageι ≫ projSpace.toSpec O n
    rw [reassoc_of% hι, LinearEmbedding.linMap_toSpec]

end ClosedImmersion

end SemistableReduction
