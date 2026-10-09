/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10Scheme
import TemperedFundamentalGroups.SemistableReduction.ModelGerms

/-!
# Germs at the points of the standard charts of projective models

For a projective model `projModelCode O hf` of homogeneous coordinates `f` in a field `F`, with
standard charts `Spec R[f j / f i] ⟶` (`ProjScheme.chartι`):

* `SemistableReduction.locAt A Q`: the localization `A_Q ⊆ F` of a subring `A` at a prime `Q`;
* `ProjScheme.chartι_imageι`: the chart composed with the embedding into `ℙᵐ_O` is the standard
  chart `Spec (O[x]_{x_i})₀ ⟶ ℙᵐ_O` through `(O[x]_{x_i})₀ → R[f j / f i]`;
* `ProjScheme.mem_imageι_chartι_iff`: a homogeneous `g` of positive degree `e` lies in the
  homogeneous prime of (the image of) the point `Q` of the chart iff `g(f) / f i ^ e ∈ Q`;
* `ProjScheme.germs_chartι`: the germs at the point `Q` are `R[f j / f i]_Q`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace SemistableReduction

open TemperedFundamentalGroups

/-! ### Localizations of subrings at primes -/

section Loc

variable {F : Type*} [Field F] (A : Subring F) (Q : Ideal A) [Q.IsPrime]

omit [Q.IsPrime] in
lemma ne_zero_of_notMem {b : A} (hb : b ∉ Q) : (b : F) ≠ 0 := fun h =>
  hb (by rw [show b = 0 from Subtype.ext h]; exact zero_mem _)

/-- The localization `A_Q ⊆ F` of a subring at a prime, as a subring of `F`. -/
def locAt : Subring F where
  carrier := {f | ∃ a b : A, b ∉ Q ∧ f = (a : F) / b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => ?_, ?_⟩
    · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      exacts [hb h, hb' h]
    · push_cast; rw [div_mul_div_comm]
  one_mem' := ⟨1, 1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * b' + b * a', b * b', fun h => ?_, ?_⟩
    · rcases Ideal.IsPrime.mem_or_mem inferInstance h with h | h
      exacts [hb h, hb' h]
    · push_cast
      rw [div_add_div _ _ (ne_zero_of_notMem A Q hb) (ne_zero_of_notMem A Q hb')]
  zero_mem' := ⟨0, 1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩
  neg_mem' := by
    rintro _ ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; ring⟩

variable {A Q}

lemma mem_locAt_of_mem {x : F} (hx : x ∈ A) : x ∈ locAt A Q :=
  ⟨⟨x, hx⟩, 1, fun h => Ideal.IsPrime.ne_top inferInstance ((Ideal.eq_top_iff_one _).2 h),
    by simp⟩

lemma inv_mem_locAt {b : A} (hb : b ∉ Q) : (b : F)⁻¹ ∈ locAt A Q :=
  ⟨1, b, hb, by simp⟩

/-- Elements of `Q` are non-units of `A_Q`. -/
lemma mul_ne_one_of_mem {x : F} (hx : x ∈ A) (hxQ : (⟨x, hx⟩ : A) ∈ Q) :
    ∀ z ∈ locAt A Q, x * z ≠ 1 := by
  rintro _ ⟨a, b, hb, rfl⟩ h
  have hb0 := ne_zero_of_notMem A Q hb
  rw [mul_div_assoc', div_eq_one_iff_eq hb0] at h
  apply hb
  have : b = ⟨x, hx⟩ * a := Subtype.ext (by rw [← h]; rfl)
  rw [this]
  exact Ideal.mul_mem_right _ _ hxQ

/-- Quotients `N / M` with `N ∈ Q`, `M ∉ Q` are non-units of `A_Q`. -/
lemma div_mul_ne_one {N M : A} (hN : N ∈ Q) (hM : M ∉ Q) :
    ∀ z ∈ locAt A Q, (N : F) / M * z ≠ 1 := by
  rintro _ ⟨a, b, hb, rfl⟩ h
  have hb0 := ne_zero_of_notMem A Q hb
  have hM0 := ne_zero_of_notMem A Q hM
  rw [div_mul_div_comm, div_eq_one_iff_eq (mul_ne_zero hM0 hb0)] at h
  have : M * b = N * a := Subtype.ext (by push_cast; rw [h])
  rcases Ideal.IsPrime.mem_or_mem inferInstance (this ▸ Ideal.mul_mem_right a Q hN) with h' | h'
  exacts [hM h', hb h']

end Loc

namespace ProjScheme

variable {O : Type u} [CommRing O] {F : Type u} [Field F] [Algebra O F] {m : ℕ}
  (R : Subring F) {f : Fin (m + 1) → F}

attribute [local instance] MvPolynomial.gradedAlgebra

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

/-- The generic point of `Spec` of a subring of a field is dense. -/
instance isDominant_SpecMap_subtype (S : Subring F) :
    IsDominant (Spec.map (CommRingCat.ofHom S.subtype)) := by
  rw [isDominant_iff]
  have hgen : (⟨⊥, Ideal.isPrime_bot⟩ : Spec (CommRingCat.of S)) ∈
      Set.range (Spec.map (CommRingCat.ofHom S.subtype)).base := by
    refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
    apply PrimeSpectrum.ext
    ext z
    rw [Spec.map_apply]
    change S.subtype z ∈ (⊥ : Ideal F) ↔ z ∈ (⊥ : Ideal S)
    simp only [Ideal.mem_bot, Subring.subtype_apply, ZeroMemClass.coe_eq_zero]
  refine Dense.mono (Set.singleton_subset_iff.2 hgen) ?_
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun x => ?_
  rw [← specializes_iff_mem_closure]
  exact (PrimeSpectrum.le_iff_specializes (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) x).1 bot_le

instance projSpace_isSeparated : (projSpace O m).IsSeparated :=
  ⟨by rw [← Limits.terminal.comp_from (projSpace.toSpec O m)]; infer_instance⟩

variable (hR : (algebraMap O F).range = R) (hf : ∀ i, f i ≠ 0)

/-- `(O[x]_{x_i})₀ → R[f j / f i]`. -/
noncomputable def chartAway (i : Fin (m + 1)) : Away (𝒜 m) (X i) →+* projChart R f i :=
  (awayEval f (X i) (isUnit_evalHom_X (O := O) f (hf i))).codRestrict _ fun z => by
    rw [← range_awayEval f R hR (hf i)]; exact ⟨z, rfl⟩

/-- **The chart composed with the embedding is the standard chart of projective space.** -/
theorem chartι_imageι (i : Fin (m + 1)) :
    chartι R hR hf i ≫ (toProj O hf).imageι =
      Spec.map (CommRingCat.ofHom (chartAway R hR hf i)) ≫ stdι O m i := by
  refine ext_of_isDominant (Spec.map (CommRingCat.ofHom (projChart R f i).subtype)) ?_
  rw [← Category.assoc, ← toImage_eq_SpecMap_comp_chartι R hR hf i]
  refine (Scheme.Hom.toImage_imageι (toProj O hf)).trans ?_
  rw [toProj_eq hf i, ← Category.assoc, ← Spec.map_comp]
  rfl

omit [Algebra O F] in
/-- Membership of a homogeneous element in a point of the standard chart `D₊(x_i)`. -/
lemma mem_stdι_iff (i : Fin (m + 1)) (P : Spec (CommRingCat.of (Away (𝒜 m) (X i))))
    {g : MvPolynomial (Fin (m + 1)) O} {e : ℕ} (hg : g ∈ (𝒜 m) e) (he : 0 < e) :
    g ∈ (stdι O m i P).asHomogeneousIdeal ↔
      Away.isLocalizationElem (X_mem (O := O) (m := m) i) hg ∈ P.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen (𝒜 m) (X_mem (O := O) (m := m) i) one_pos hg he
  have h' : P ∈ stdι O m i ⁻¹ᵁ Proj.basicOpen (𝒜 m) g ↔
      P ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem (O := O) (m := m) i) hg) := by
    rw [← h]
    rfl
  rw [← not_iff_not]
  exact h'

/-- **Membership in the points of a chart**: for `g` homogeneous of positive degree `e`, `g` lies
in the homogeneous prime of the image in `ℙᵐ` of the point `Q` of the chart `R[f j / f i]` iff
`g(f) / f i ^ e ∈ Q`. -/
theorem mem_imageι_chartι_iff (i : Fin (m + 1)) (Q : Spec (CommRingCat.of (projChart R f i)))
    {g : MvPolynomial (Fin (m + 1)) O} {e : ℕ} (hg : g ∈ (𝒜 m) e) (he : 0 < e) :
    g ∈ ((toProj O hf).imageι (chartι R hR hf i Q)).asHomogeneousIdeal ↔
      ∃ h : evalHom f g / f i ^ e ∈ projChart R f i, (⟨_, h⟩ : projChart R f i) ∈ Q.asIdeal := by
  have hpt : (toProj O hf).imageι (chartι R hR hf i Q) =
      stdι O m i (Spec.map (CommRingCat.ofHom (chartAway R hR hf i)) Q) := by
    have := congrArg (fun φ : Spec (CommRingCat.of (projChart R f i)) ⟶ projSpace O m => φ Q)
      (chartι_imageι R hR hf i)
    simp only [Scheme.Hom.comp_apply] at this
    exact this
  rw [hpt, mem_stdι_iff i _ hg he, Spec.map_apply]
  change chartAway R hR hf i _ ∈ Q.asIdeal ↔ _
  have hval : (chartAway R hR hf i (Away.isLocalizationElem (X_mem (O := O) (m := m) i) hg) : F) =
      evalHom f g / f i ^ e := by
    change awayEval f (X i) _ _ = _
    rw [Away.isLocalizationElem, awayEval_mk]
    simp [evalHom]
  constructor
  · intro h
    refine ⟨hval ▸ (chartAway R hR hf i _).2, ?_⟩
    convert h using 1
    exact Subtype.ext hval.symm
  · rintro ⟨h, hQ⟩
    convert hQ using 1
    exact Subtype.ext hval

/-- **The germs at a point of a chart** are the localization of the chart at the point. -/
theorem germs_chartι (i : Fin (m + 1)) (Q : Spec (CommRingCat.of (projChart R f i))) :
    TemperedFundamentalGroups.SemistableReduction.ModelCode.germs (projModelCode O hf)
        (genericPt O hf) (chartι R hR hf i Q) = (locAt (projChart R f i) Q.asIdeal : Set F) := by
  classical
  letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
    (projModelCode O hf) (chartOpen O hf i)
  letI := projChartAlgebra (f := f) R hR i
  have hU : IsAffineOpen (chartOpen O hf i) := isAffineOpen_chartOpen hf i
  have hy : chartι R hR hf i Q ∈ chartOpen O hf i := by
    rw [← opensRange_chartι R hR hf i]; exact ⟨Q, rfl⟩
  have h : ⊤ ≤ genericPt O hf ⁻¹ᵁ chartOpen O hf i := top_le_toImage_preimage_chartOpen hf i
  let e := chartEquiv R hR hf i
  have htoL : ∀ s, TemperedFundamentalGroups.SemistableReduction.ModelCode.toL
      (genericPt O hf) h s = (e s : F) := fun s => rfl
  have hinj : Function.Injective (TemperedFundamentalGroups.SemistableReduction.ModelCode.toL
      (genericPt O hf) h) := fun a b hab => by
    rw [htoL, htoL] at hab
    exact e.injective (Subtype.ext hab)
  rw [TemperedFundamentalGroups.SemistableReduction.ModelCode.germs_eq_of_isAffineOpen _ hU hy h
    hinj]
  -- the prime of the point
  have hprime : hU.primeIdealOf ⟨_, hy⟩ =
      Spec.map e.toRingEquiv.toCommRingCatIso.hom Q := by
    apply hU.fromSpec.isOpenEmbedding.injective
    rw [IsAffineOpen.fromSpec_primeIdealOf]
    change chartι R hR hf i Q = _
    rw [chartι, Scheme.Hom.comp_apply]
  have key : ∀ b, b ∈ (hU.primeIdealOf ⟨_, hy⟩).asIdeal ↔ e b ∈ Q.asIdeal := fun b => by
    rw [hprime, Spec.map_apply]
    rfl
  ext z
  constructor
  · rintro ⟨a, b, hb, rfl⟩
    exact ⟨e a, e b, fun h' => hb ((key b).2 h'), by rw [htoL, htoL]⟩
  · rintro ⟨a, b, hb, rfl⟩
    refine ⟨e.symm a, e.symm b, fun h' => hb ?_, by rw [htoL, htoL, e.apply_symm_apply,
      e.apply_symm_apply]⟩
    have := (key _).1 h'
    rwa [e.apply_symm_apply] at this

end ProjScheme

end SemistableReduction
