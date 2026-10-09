/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateModelCharts

/-!
# The Tate model is normal and flat

Let `O` be a discrete valuation ring with uniformizer `π`, and `b₄ b₆ ∈ O` such that
`d = X² + 4 (π X³ + π b₄ X + b₆)` is squarefree in `O[X]` (e.g. `2 ≠ 0` in `O` and the
discriminant of `E : y² + xy = x³ + π² b₄ x + π² b₆` is nonzero, `TateNormal.squarefree_dpoly`).
The model `TateModel.model π b₄ b₆` (the reduced closed subscheme of `ℙ²_O` on
`V(v²w + uvw − πu³ − πb₄uw² − b₆w³)`) satisfies:

* `TateModel.stalk_isDomain_isIntegrallyClosed` **(N)**: every stalk is an integrally closed
  domain;
* `TateModel.flat_toSpec` **(F)**: `model.toSpec` is flat;

i.e. the hypotheses of the fibre clause of `SemistableReduction.Statement.StrongComponent`
(variants `..._of_tateDisc` assume `2 ≠ 0` and `Δ ≠ 0` instead of `d` squarefree).

Proof: `V(F)` is the closure of the generic point `[a : b : 1]` of `Spec L ⟶ ℙ²_O`, `L` the
function field (`TateNormal.closure_range_toProj`, from the homogeneous kernel computation
`TateNormal.F_dvd_of_eval_eq_zero`), so the model is the projective model
`SemistableReduction.ProjScheme.projModelCode` of `[a : b : 1]` (`TateNormal.model_eq`), whose
standard charts are the subrings `O[x_j / x_i] ⊆ L`. These are integrally closed
(`Andre/TateModelCharts.lean`) and torsion free, hence flat, over `O`; the stalks are their
localizations.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open SemistableReduction.ProjScheme

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (2 + 1)) O
local notation "L" => TateField π b₄ b₆

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Membership of a homogeneous element in a point of the standard chart `D₊(x_i)`. -/
lemma mem_stdι_iff (i : Fin (2 + 1)) (P : Spec (CommRingCat.of (Away 𝒜 (X i))))
    {g : MvPolynomial (Fin (2 + 1)) O} {e : ℕ} (hg : g ∈ 𝒜 e) (he : 0 < e) :
    g ∈ (stdι O 2 i P).asHomogeneousIdeal ↔
      Away.isLocalizationElem (X_mem (O := O) (m := 2) i) hg ∈ P.asIdeal := by
  have h := Proj.awayι_preimage_basicOpen 𝒜 (X_mem (O := O) (m := 2) i) one_pos hg he
  have h' : P ∈ stdι O 2 i ⁻¹ᵁ Proj.basicOpen 𝒜 g ↔
      P ∈ PrimeSpectrum.basicOpen (Away.isLocalizationElem (X_mem (O := O) (m := 2) i) hg) := by
    rw [← h]
    rfl
  rw [← not_iff_not]
  exact h'

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma F_mem : TateModel.F π b₄ b₆ ∈ 𝒜 3 :=
  (mem_homogeneousSubmodule _ _).2 (TateModel.isHomogeneous_F π b₄ b₆)

lemma hcoords (hπ : π ≠ 0) : ∀ i, coords π b₄ b₆ i ≠ 0 := coords_ne_zero π b₄ b₆ hπ

/-- The kernel of `(O[x]_{x_i})₀ → L` is contained in every prime containing `F / x_i³`. -/
lemma ker_awayEval_le (hπ : π ≠ 0) (i : Fin (2 + 1)) (P : Ideal (Away 𝒜 (X i))) [P.IsPrime]
    (hF : Away.isLocalizationElem (X_mem (O := O) (m := 2) i) (F_mem π b₄ b₆) ∈ P) :
    RingHom.ker (awayEval (coords π b₄ b₆) (X i)
      (isUnit_evalHom_X (O := O) _ (hcoords π b₄ b₆ hπ i))) ≤ P := by
  classical
  intro z hz
  obtain ⟨n, g, hg, rfl⟩ := Away.mk_surjective 𝒜 (X_mem (O := O) (m := 2) i) z
  rw [RingHom.mem_ker, awayEval_mk] at hz
  have hXi : evalHom (coords π b₄ b₆) (X i : MvPolynomial (Fin (2 + 1)) O) ≠ 0 := by
    simpa [evalHom] using hcoords π b₄ b₆ hπ i
  have hg0 : MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) g = 0 := by
    have := (div_eq_zero_iff.1 hz).resolve_right (pow_ne_zero _ hXi)
    simpa [evalHom] using this
  have hgh : g.IsHomogeneous n := by simpa using hg
  obtain ⟨h, rfl⟩ := F_dvd_of_eval_eq_zero π b₄ b₆ hπ hgh hg0
  have hg' : TateModel.F π b₄ b₆ * h ∈ 𝒜 n := by simpa using hg
  have hdec := DirectSum.coe_decompose_mul_of_left_mem 𝒜 (b := h) n (F_mem π b₄ b₆)
  rw [DirectSum.decompose_of_mem_same 𝒜 hg'] at hdec
  split_ifs at hdec with h3
  · set h' := (DirectSum.decompose 𝒜 h (n - 3) : MvPolynomial (Fin (2 + 1)) O)
    have hh' : h' ∈ 𝒜 ((n - 3) • 1) := by
      simp only [smul_eq_mul, mul_one]; exact (DirectSum.decompose 𝒜 h (n - 3)).2
    have : Away.mk 𝒜 (X_mem (O := O) (m := 2) i) n (TateModel.F π b₄ b₆ * h) hg =
        Away.isLocalizationElem (X_mem (O := O) (m := 2) i) (F_mem π b₄ b₆) *
          Away.mk 𝒜 (X_mem (O := O) (m := 2) i) (n - 3) h' hh' := by
      apply val_injective
      simp only [Away.val_mk, val_mul, Localization.mk_mul, pow_one]
      rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
      rw [hdec, ← pow_add, Nat.add_sub_cancel' h3]
    rw [this]
    exact Ideal.mul_mem_right _ _ hF
  · have : Away.mk 𝒜 (X_mem (O := O) (m := 2) i) n (TateModel.F π b₄ b₆ * h) hg = 0 := by
      apply val_injective
      simp only [Away.val_mk, val_zero]
      rw [hdec, Localization.mk_zero]
    rw [this]
    exact zero_mem _

/-- **The closure of the generic point of the Tate model is `V(F)`.** -/
theorem closure_range_toProj (hπ : π ≠ 0) :
    closure (Set.range (toProj O (hcoords π b₄ b₆ hπ))) =
      {y : projSpace O 2 | TateModel.F π b₄ b₆ ∈ y.asHomogeneousIdeal} := by
  set hf := hcoords π b₄ b₆ hπ
  have hclosed : IsClosed {y : projSpace O 2 | TateModel.F π b₄ b₆ ∈ y.asHomogeneousIdeal} := by
    have e : {y : projSpace O 2 | TateModel.F π b₄ b₆ ∈ y.asHomogeneousIdeal} =
        ((TateModel.cubicSet π b₄ b₆ : Set (Proj 𝒜)) : Set (projSpace O 2)) := by
      ext y
      exact not_not.symm
    rw [e]
    exact (TateModel.cubicSet π b₄ b₆).isClosed
  apply le_antisymm
  · refine closure_minimal ?_ hclosed
    rintro _ ⟨x, rfl⟩
    change TateModel.F π b₄ b₆ ∈ (toProj O hf x).asHomogeneousIdeal
    rw [toProj_eq hf 0, Scheme.Hom.comp_apply, mem_stdι_iff 0 _ (F_mem π b₄ b₆) three_pos,
      Spec.map_apply]
    change awayEval _ _ _ _ ∈ x.asIdeal
    rw [Away.isLocalizationElem, awayEval_mk]
    have hF := eval_F π b₄ b₆
    simp only [pow_one, evalHom, MvPolynomial.coe_eval₂Hom, hF, zero_div]
    exact zero_mem _
  · intro y hy
    obtain ⟨i, hi⟩ := exists_X_notMem y
    have hy' : y ∈ (stdι O 2 i).opensRange := by
      change y ∈ (Proj.awayι 𝒜 (X i) (X_mem i) one_pos).opensRange
      rw [Proj.opensRange_awayι]
      exact hi
    obtain ⟨P, rfl⟩ := hy'
    have hF : Away.isLocalizationElem (X_mem (O := O) (m := 2) i) (F_mem π b₄ b₆) ∈ P.asIdeal :=
      (mem_stdι_iff i P (F_mem π b₄ b₆) three_pos).1 hy
    set x : Spec (CommRingCat.of L) := ⟨⊥, Ideal.isPrime_bot⟩
    have hsp : (Spec.map (CommRingCat.ofHom (awayEval (coords π b₄ b₆) (X i)
        (isUnit_evalHom_X (O := O) _ (hf i))))) x ⤳ P := by
      refine (PrimeSpectrum.le_iff_specializes _ _).1 ?_
      intro z hz
      rw [Spec.map_apply] at hz
      exact ker_awayEval_le π b₄ b₆ hπ i P.asIdeal hF hz
    have := hsp.map (stdι O 2 i).continuous
    rw [← Scheme.Hom.comp_apply, ← toProj_eq hf i, specializes_iff_mem_closure] at this
    exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self x)) this

/-- **The Tate model is the closure of its generic point**: its (reduced) ideal sheaf is the kernel
of `Spec L ⟶ ℙ²_O`, `[a : b : 1]`. -/
theorem modelIdeal_eq_ker (hπ : π ≠ 0) :
    TateModel.modelIdeal π b₄ b₆ = (toProj O (hcoords π b₄ b₆ hπ)).ker := by
  set hf := hcoords π b₄ b₆ hπ
  haveI : QuasiCompact (toProj O hf) := by
    have : QuasiCompact (toProj O hf ≫ projSpace.toSpec O 2) := by
      rw [toProj_toSpec]
      infer_instance
    exact .of_comp _ (projSpace.toSpec O 2)
  have hrad : (toProj O hf).ker.radical = (toProj O hf).ker :=
    le_antisymm (TateModel.radical_ker_le _) (Scheme.IdealSheafData.le_radical _)
  rw [← hrad, ← Scheme.IdealSheafData.vanishingIdeal_support]
  unfold TateModel.modelIdeal
  congr 1
  apply TopologicalSpace.Closeds.ext
  change ((TateModel.cubicSet π b₄ b₆ : Set (Proj 𝒜)) : Set (projSpace O 2)) =
    ((toProj O hf).ker.support : Set (projSpace O 2))
  rw [Scheme.Hom.support_ker, closure_range_toProj π b₄ b₆ hπ]
  ext y
  exact not_not

/-- **The Tate model as the projective model of its function field.** -/
theorem model_eq (hπ : π ≠ 0) :
    TateModel.model π b₄ b₆ = projModelCode O (hcoords π b₄ b₆ hπ) := by
  unfold TateModel.model projModelCode
  rw [modelIdeal_eq_ker π b₄ b₆ hπ]

lemma intClosedIn_chart (hπ : Irreducible π) (i : Fin (2 + 1)) :
    IntClosedIn (chart π b₄ b₆ i) := by
  fin_cases i
  · exact intClosedIn_chart_zero π b₄ b₆ hπ
  · exact intClosedIn_chart_one π b₄ b₆ hπ
  · exact intClosedIn_chart_two π b₄ b₆

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma algebraMap_O_injective : Function.Injective (algebraMap O L) := by
  rw [IsScalarTower.algebraMap_eq O (Polynomial O) L]
  exact (algebraMap_injective π b₄ b₆).comp (Polynomial.C_injective)

/-- **The charts of the Tate model are flat over `O`.** -/
lemma flat_chart (i : Fin (2 + 1)) :
    letI := SemistableReduction.ProjScheme.projChartAlgebra (f := coords π b₄ b₆)
      (baseRing π b₄ b₆) rfl i
    Module.Flat O (chart π b₄ b₆ i) := by
  letI := SemistableReduction.ProjScheme.projChartAlgebra (f := coords π b₄ b₆)
    (baseRing π b₄ b₆) rfl i
  haveI : Module.IsTorsionFree O (chart π b₄ b₆ i) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    intro x y h
    exact algebraMap_O_injective π b₄ b₆ (congrArg Subtype.val h)
  infer_instance

/-- **(N) The stalks of the Tate model are integrally closed domains.** -/
theorem stalk_isDomain_isIntegrallyClosed (hπ : Irreducible π)
    (x : (TateModel.model π b₄ b₆).scheme) :
    IsDomain ((TateModel.model π b₄ b₆).scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed ((TateModel.model π b₄ b₆).scheme.presheaf.stalk x) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set hf := hcoords π b₄ b₆ hπ0
  revert x
  rw [model_eq π b₄ b₆ hπ0]
  intro x
  obtain ⟨i, hi⟩ := exists_mem_chartOpen (O := O) hf x
  set U := chartOpen O hf i
  have hU : IsAffineOpen U := isAffineOpen_chartOpen hf i
  letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra
    (projModelCode O hf) U
  letI := SemistableReduction.ProjScheme.projChartAlgebra (f := coords π b₄ b₆)
    (baseRing π b₄ b₆) rfl i
  set e := chartEquiv (baseRing π b₄ b₆) rfl hf i
  haveI : IsDomain (chart π b₄ b₆ i) := inferInstance
  haveI : IsIntegrallyClosed (chart π b₄ b₆ i) :=
    (intClosedIn_chart π b₄ b₆ hπ i).isIntegrallyClosed
  haveI : IsDomain Γ((projModelCode O hf).scheme, U) := e.toRingEquiv.toMulEquiv.isDomain
  haveI : IsIntegrallyClosed Γ((projModelCode O hf).scheme, U) :=
    IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  letI : Algebra Γ((projModelCode O hf).scheme, U) ((projModelCode O hf).scheme.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨x, hi⟩
  haveI := hU.isLocalization_stalk ⟨x, hi⟩
  have hM := (hU.primeIdealOf ⟨x, hi⟩).asIdeal.primeCompl_le_nonZeroDivisors
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ hM,
    isIntegrallyClosed_of_isLocalization _ _ hM⟩

/-- **(F) The Tate model is flat over `O`.** -/
theorem flat_toSpec (hπ : Irreducible π) : Flat (TateModel.model π b₄ b₆).toSpec := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  set hf := hcoords π b₄ b₆ hπ0
  rw [model_eq π b₄ b₆ hπ0]
  set c := projModelCode O hf
  refine HasRingHomProperty.of_iSup_eq_top (P := @Flat)
    (fun i ↦ ⟨chartOpen O hf i, isAffineOpen_chartOpen hf i⟩) ?_ fun i ↦ ?_
  · refine top_le_iff.1 fun x _ ↦ ?_
    obtain ⟨i, hi⟩ := exists_mem_chartOpen (O := O) hf x
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  · letI := TemperedFundamentalGroups.SemistableReduction.ModelCode.sectionsAlgebra c
      (chartOpen O hf i)
    letI := SemistableReduction.ProjScheme.projChartAlgebra (f := coords π b₄ b₆)
      (baseRing π b₄ b₆) rfl i
    haveI := flat_chart π b₄ b₆ i
    haveI : Module.Flat O Γ(c.scheme, chartOpen O hf i) :=
      Module.Flat.of_linearEquiv (chartEquiv (baseRing π b₄ b₆) rfl hf i).toLinearEquiv
    have h1 : (algebraMap O Γ(c.scheme, chartOpen O hf i)).Flat :=
      RingHom.flat_algebraMap_iff.2 inferInstance
    have h2 : (algebraMap O Γ(c.scheme, chartOpen O hf i)) =
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫
          c.toSpec.appLE ⊤ (chartOpen O hf i) le_top).hom := rfl
    have h3 : (c.toSpec.appLE ⊤ (chartOpen O hf i) le_top).hom =
        (algebraMap O Γ(c.scheme, chartOpen O hf i)).comp
          (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom := by
      rw [h2, CommRingCat.hom_comp, RingHom.comp_assoc, ← CommRingCat.hom_comp,
        Iso.hom_inv_id, CommRingCat.hom_id, RingHom.comp_id]
    change (c.toSpec.appLE ⊤ (chartOpen O hf i) le_top).hom.Flat
    rw [h3]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso _)) h1

end

end TemperedFundamentalGroups.TateNormal

namespace TemperedFundamentalGroups.TateModel

open TateNormal

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π b₄ b₆ : O}

/-- **(N) The stalks of the Tate model are integrally closed domains**, for `π` a uniformizer and
`d = X² + 4 (π X³ + π b₄ X + b₆)` squarefree. -/
theorem stalk_isDomain_isIntegrallyClosed (hπ : Irreducible π)
    (hd : Squarefree (dpoly π b₄ b₆)) (x : (model π b₄ b₆).scheme) :
    IsDomain ((model π b₄ b₆).scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed ((model π b₄ b₆).scheme.presheaf.stalk x) :=
  haveI : Fact (Squarefree (dpoly π b₄ b₆)) := ⟨hd⟩
  TateNormal.stalk_isDomain_isIntegrallyClosed π b₄ b₆ hπ x

/-- **(F) The Tate model is flat over `O`**, for `π` a uniformizer and
`d = X² + 4 (π X³ + π b₄ X + b₆)` squarefree. -/
theorem flat_toSpec (hπ : Irreducible π) (hd : Squarefree (dpoly π b₄ b₆)) :
    Flat (model π b₄ b₆).toSpec :=
  haveI : Fact (Squarefree (dpoly π b₄ b₆)) := ⟨hd⟩
  TateNormal.flat_toSpec π b₄ b₆ hπ

/-- **(N)** for a curve of Tate type with `2 ≠ 0` and nonzero discriminant. -/
theorem stalk_isDomain_isIntegrallyClosed_of_tateDisc (hπ : Irreducible π) (h2 : (2 : O) ≠ 0)
    (hΔ : tateDisc π b₄ b₆ ≠ 0) (x : (model π b₄ b₆).scheme) :
    IsDomain ((model π b₄ b₆).scheme.presheaf.stalk x) ∧
      IsIntegrallyClosed ((model π b₄ b₆).scheme.presheaf.stalk x) :=
  stalk_isDomain_isIntegrallyClosed hπ (squarefree_dpoly π b₄ b₆ h2 hΔ) x

/-- **(F)** for a curve of Tate type with `2 ≠ 0` and nonzero discriminant. -/
theorem flat_toSpec_of_tateDisc (hπ : Irreducible π) (h2 : (2 : O) ≠ 0)
    (hΔ : tateDisc π b₄ b₆ ≠ 0) : Flat (model π b₄ b₆).toSpec :=
  flat_toSpec hπ (squarefree_dpoly π b₄ b₆ h2 hΔ)

end TemperedFundamentalGroups.TateModel
