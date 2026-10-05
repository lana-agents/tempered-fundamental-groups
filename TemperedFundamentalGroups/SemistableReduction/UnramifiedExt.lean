/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothBaseChange
import TemperedFundamentalGroups.SemistableReduction.DVRDescentCount

/-!
# Unramified extensions of a discretely valued field inside `C` (W10, smooth part (2))

Blueprint §9.12 (O7). Let `E` be a non-archimedean field whose ring of integers `O_E` is a DVR,
`φ : E → C` an isometric embedding, `g ∈ O_E[X]` monic, irreducible over `E`, with
`g' p₁ + g p₂ ≡ 1` modulo `𝔪_E` (e.g. `ḡ` separable), and `β ∈ C` a root of `g`
(`UnrData`). Then `E' = E[X] ⧸ (g)` (`UnrData.F`) with the norm induced by `φ' : E' → C`,
`root ↦ β`, is a non-archimedean field with:

* `UnrData.integers_eq`: `O_{E'} = O_E[root]`;
* `UnrData.isDiscreteValuationRing`: `O_{E'}` is a DVR, and a uniformizer of `O_E` stays one;
* `UnrData.etale`: `O_E → O_{E'}` is étale (standard étale, `etale_of_aeval_eq_zero`).
-/

open Polynomial IsLocalRing

set_option linter.unusedSectionVars false

namespace SemistableReduction

namespace Unramified

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

local notation "O_E" => HenselComplete.integers E

variable (φ : E →+* C) in
/-- The data of an unramified extension of `E` inside `C`. -/
structure UnrData where
  isom : ∀ e, ‖φ e‖ = ‖e‖
  /-- The defining polynomial. -/
  g : O_E[X]
  monic : g.Monic
  irred_res : Irreducible (g.map (residue O_E))
  /-- Coefficients witnessing separability of `ḡ`. -/
  p₁ : O_E[X]
  /-- Coefficients witnessing separability of `ḡ`. -/
  p₂ : O_E[X]
  hres : (derivative g * p₁ + g * p₂).map (residue O_E) = 1
  /-- The root in `C`. -/
  β : C
  root : g.eval₂ (φ.comp (O_E).subtype) β = 0

variable {φ : E →+* C} (D : UnrData φ)

namespace UnrData

lemma irred : Irreducible (D.g.map (algebraMap O_E E)) :=
  (D.monic.irreducible_iff_irreducible_map_fraction_map).1
    (D.monic.irreducible_of_irreducible_map _ D.g D.irred_res)

instance : Fact (Irreducible (D.g.map (algebraMap O_E E))) := ⟨D.irred⟩

/-- The extension field `E' = E[X] ⧸ (g)`. -/
abbrev F : Type _ := AdjoinRoot (D.g.map (algebraMap O_E E))

/-- The root of `g` in `E'`. -/
noncomputable def r : D.F := AdjoinRoot.root (D.g.map (algebraMap O_E E))

lemma root_map : (D.g.map (algebraMap O_E E)).eval₂ φ D.β = 0 := by
  rw [eval₂_map]
  exact D.root

/-- The embedding `E' → C`, `root ↦ β`. -/
noncomputable def φ' : D.F →+* C := AdjoinRoot.lift φ D.β D.root_map

lemma φ'_algebraMap (e : E) : D.φ' (algebraMap E D.F e) = φ e :=
  AdjoinRoot.lift_of D.root_map

lemma φ'_r : D.φ' D.r = D.β := AdjoinRoot.lift_root D.root_map

/-- The norm of `E'`, induced from `C`. -/
noncomputable instance : NontriviallyNormedField D.F :=
  { NormedField.induced D.F C D.φ' D.φ'.injective with
    non_trivial := by
      obtain ⟨e, he⟩ := NontriviallyNormedField.non_trivial (α := E)
      refine ⟨algebraMap E D.F e, ?_⟩
      change 1 < ‖D.φ' (algebraMap E D.F e)‖
      rwa [φ'_algebraMap, D.isom] }

lemma norm_def (z : D.F) : ‖z‖ = ‖D.φ' z‖ := rfl

lemma norm_φ' (z : D.F) : ‖D.φ' z‖ = ‖z‖ := rfl

lemma norm_algebraMap (e : E) : ‖algebraMap E D.F e‖ = ‖e‖ := by
  rw [norm_def, φ'_algebraMap, D.isom]

instance : IsUltrametricDist D.F :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun a b ↦ by
    simp only [norm_def, map_add]
    exact IsUltrametricDist.norm_add_le_max _ _

local notation "O_C" => HenselComplete.integers C
local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "kv" => ResidueField (HenselComplete.integers E)

/-- `O_E → O_C`. -/
noncomputable abbrev ιO : O_E →+* O_C := DVRDescent.intMap D.isom

/-- `κ_E → 𝓀`. -/
noncomputable abbrev ψ : kv →+* 𝓀 := DVRDescent.ψ D.isom

lemma coe_ιO (a : O_E) : ((D.ιO a : O_C) : C) = φ a := rfl

lemma β_mem : D.β ∈ O_C := by
  have hint : IsIntegral O_C D.β := by
    refine ⟨D.g.map D.ιO, D.monic.map _, ?_⟩
    rw [eval₂_map]
    exact D.root
  exact (Valuation.valuationSubring.integers (NormedField.valuation (K := C))).mem_of_integral hint

/-- `β` as an element of `O_C`. -/
noncomputable def b : O_C := ⟨D.β, D.β_mem⟩

lemma coe_aeval_b (q : O_E[X]) :
    ((aeval D.b (q.map D.ιO) : O_C) : C) = q.eval₂ (φ.comp (O_E).subtype) D.β := by
  rw [aeval_def, eval₂_map, ← (O_C).subtype_apply, hom_eval₂]
  rfl

lemma aeval_b_g : aeval D.b (D.g.map D.ιO) = 0 := by
  apply Subtype.ext
  rw [coe_aeval_b, D.root]
  rfl

lemma residue_aeval_b (q : O_E[X]) :
    residue O_C (aeval D.b (q.map D.ιO)) =
      aeval (residue O_C D.b) ((q.map (residue O_E)).map D.ψ) := by
  rw [aeval_def, aeval_def, eval₂_map, eval₂_map, eval₂_map, hom_eval₂]
  congr 1

/-- The minimal polynomial of `β̄` over `κ_E` is `ḡ`. -/
lemma minpoly_residue_b :
    letI := D.ψ.toAlgebra
    minpoly kv (residue O_C D.b) = D.g.map (residue O_E) := by
  letI := D.ψ.toAlgebra
  refine (minpoly.eq_of_irreducible_of_monic D.irred_res ?_ (D.monic.map _)).symm
  have := D.residue_aeval_b D.g
  rw [D.aeval_b_g, map_zero, aeval_def, eval₂_map] at this
  have e : (algebraMap 𝓀 𝓀).comp D.ψ = algebraMap kv 𝓀 := by ext; rfl
  rw [e] at this
  rw [aeval_def]
  exact this.symm

/-- **Orthonormality**: a polynomial of degree `< deg g` with integral coefficients, one of them a
unit, has value of norm `1` at the root. -/
lemma norm_aeval_eq_one (q : O_E[X]) (hq : q.natDegree < D.g.natDegree)
    (hu : ∃ i, IsUnit (q.coeff i)) : ‖aeval D.r (q.map (algebraMap O_E E))‖ = 1 := by
  letI := D.ψ.toAlgebra
  have hval : D.φ' (aeval D.r (q.map (algebraMap O_E E))) =
      ((aeval D.b (q.map D.ιO) : O_C) : C) := by
    rw [coe_aeval_b, aeval_def, hom_eval₂, eval₂_map]
    congr 1
    · ext a
      exact D.φ'_algebraMap a
    · exact D.φ'_r
  rw [norm_def, hval]
  rw [← HenselComplete.isUnit_iff_norm_eq_one]
  by_contra hnu
  have h0 : residue O_C (aeval D.b (q.map D.ιO)) = 0 := (residue_eq_zero_iff _).2 hnu
  rw [residue_aeval_b] at h0
  obtain ⟨i, hi⟩ := hu
  have hq0 : q.map (residue O_E) ≠ 0 := by
    intro h
    have := congrArg (fun p ↦ p.coeff i) h
    simp only [coeff_map, coeff_zero] at this
    exact ((residue_eq_zero_iff _).1 this) hi
  have e : (algebraMap 𝓀 𝓀).comp D.ψ = algebraMap kv 𝓀 := by ext; rfl
  rw [aeval_def, eval₂_map, e] at h0
  have hdeg := minpoly.degree_le_of_ne_zero kv (residue O_C D.b) hq0 (by
    rw [aeval_def]; exact h0)
  rw [minpoly_residue_b] at hdeg
  have h1 : (q.map (residue O_E)).degree < (D.g.map (residue O_E)).degree := by
    refine degree_lt_degree ?_
    rw [D.monic.natDegree_map]
    exact (natDegree_map_le).trans_lt hq
  exact absurd hdeg (not_le.2 h1)

lemma natDegree_pos : 0 < D.g.natDegree := by
  have h := D.irred.natDegree_pos
  rwa [D.monic.natDegree_map] at h

lemma aeval_r_eq_mk (q : E[X]) :
    aeval D.r q = AdjoinRoot.mk (D.g.map (algebraMap O_E E)) q := AdjoinRoot.aeval_eq q

lemma aeval_r_g : aeval D.r (D.g.map (algebraMap O_E E)) = 0 := by
  rw [aeval_r_eq_mk, AdjoinRoot.mk_self]

lemma eq_zero_of_aeval_r (q : E[X]) (hq : q.natDegree < D.g.natDegree)
    (h : aeval D.r q = 0) : q = 0 := by
  rw [aeval_r_eq_mk, AdjoinRoot.mk_eq_zero] at h
  refine eq_zero_of_dvd_of_degree_lt h ?_
  rw [D.monic.degree_map]
  by_cases hq0 : q = 0
  · rw [hq0, degree_zero, degree_eq_natDegree D.monic.ne_zero]
    exact WithBot.bot_lt_coe _
  · rw [degree_eq_natDegree hq0, degree_eq_natDegree D.monic.ne_zero]
    exact_mod_cast hq

lemma exists_aeval_r (z : D.F) :
    ∃ q : E[X], q.natDegree < D.g.natDegree ∧ z = aeval D.r q := by
  obtain ⟨Q, rfl⟩ := AdjoinRoot.mk_surjective z
  refine ⟨Q %ₘ D.g.map (algebraMap O_E E), ?_, ?_⟩
  · by_cases h0 : Q %ₘ D.g.map (algebraMap O_E E) = 0
    · rw [h0, natDegree_zero]; exact D.natDegree_pos
    · rw [← D.monic.natDegree_map (algebraMap O_E E)]
      exact natDegree_lt_natDegree h0 (degree_modByMonic_lt _ (D.monic.map _))
  · rw [aeval_r_eq_mk, AdjoinRoot.mk_eq_mk]
    have h := modByMonic_add_div Q (D.g.map (algebraMap O_E E))
    refine ⟨Q /ₘ D.g.map (algebraMap O_E E), ?_⟩
    linear_combination h.symm

lemma norm_r_le : ‖D.r‖ ≤ 1 := by
  rw [norm_def, φ'_r]
  exact (HenselComplete.mem_integers_iff _).1 D.β_mem

lemma norm_aeval_le (q : E[X]) {M : ℝ} (hM : ∀ i, ‖q.coeff i‖ ≤ M) (hM0 : 0 ≤ M) :
    ‖aeval D.r q‖ ≤ M := by
  rw [aeval_eq_sum_range]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hM0 fun i _ ↦ ?_
  rw [Algebra.smul_def, norm_mul, norm_algebraMap, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) D.norm_r_le)
    |>.trans (hM i)

/-- Lift a polynomial with integral coefficients. -/
lemma exists_lift (Q : E[X]) (hQ : ∀ i, ‖Q.coeff i‖ ≤ 1) :
    ∃ q : O_E[X], q.map (algebraMap O_E E) = Q ∧ q.natDegree = Q.natDegree := by
  have hcoeff : (↑Q.coeffs : Set E) ⊆ (O_E).toSubring := by
    intro a ha
    obtain ⟨n, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 ha
    exact (HenselComplete.mem_integers_iff _).2 (hQ n)
  refine ⟨Q.toSubring _ hcoeff, map_toSubring _ _ _, ?_⟩
  conv_rhs => rw [← map_toSubring Q _ hcoeff]
  exact (natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective O_E E) _).symm

/-- **The integers of `E'`**: `‖z‖ ≤ 1` iff `z` is an `O_E`-polynomial of degree `< deg g` in
the root. -/
theorem norm_le_one_iff (z : D.F) :
    ‖z‖ ≤ 1 ↔ ∃ q : O_E[X], q.natDegree < D.g.natDegree ∧
      z = aeval D.r (q.map (algebraMap O_E E)) := by
  constructor
  · intro hz
    obtain ⟨Q, hQd, rfl⟩ := D.exists_aeval_r z
    by_cases hle : ∀ i, ‖Q.coeff i‖ ≤ 1
    · obtain ⟨q, hq, hqd⟩ := exists_lift Q hle
      exact ⟨q, hqd ▸ hQd, by rw [hq]⟩
    · exfalso
      push Not at hle
      obtain ⟨i₀, hi₀⟩ := hle
      have hne : (Finset.range D.g.natDegree).Nonempty := ⟨0, by simp [D.natDegree_pos]⟩
      obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image _ (fun i ↦ ‖Q.coeff i‖) hne
      have hcoeff : ∀ i, ‖Q.coeff i‖ ≤ ‖Q.coeff j‖ := by
        intro i
        by_cases hi : i < D.g.natDegree
        · exact hjmax i (Finset.mem_range.2 hi)
        · rw [coeff_eq_zero_of_natDegree_lt (by omega), norm_zero]; exact norm_nonneg _
      have hc1 : 1 < ‖Q.coeff j‖ := hi₀.trans_le (hcoeff i₀)
      have hc0 : Q.coeff j ≠ 0 := by
        intro h; rw [h, norm_zero] at hc1; linarith
      set Q' := Polynomial.C (Q.coeff j)⁻¹ * Q
      have hQ' : ∀ i, ‖Q'.coeff i‖ ≤ 1 := by
        intro i
        rw [coeff_C_mul, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.2 hc0), mul_one]
        exact hcoeff i
      obtain ⟨q', hq', hq'd⟩ := exists_lift Q' hQ'
      have hunit : IsUnit (q'.coeff j) := by
        rw [HenselComplete.isUnit_iff_norm_eq_one]
        have := congrArg (fun p ↦ p.coeff j) hq'
        simp only [coeff_map] at this
        change ‖algebraMap O_E E (q'.coeff j)‖ = 1
        rw [this, coeff_C_mul, inv_mul_cancel₀ hc0, norm_one]
      have hdeg : q'.natDegree < D.g.natDegree := by
        rw [hq'd]
        exact (natDegree_C_mul_le _ _).trans_lt hQd
      have h1 := D.norm_aeval_eq_one q' hdeg ⟨j, hunit⟩
      rw [hq', map_mul, aeval_C, norm_mul, norm_algebraMap, norm_inv,
        inv_mul_eq_one₀ (norm_ne_zero_iff.2 hc0)] at h1
      rw [← h1] at hz
      linarith
  · rintro ⟨q, -, rfl⟩
    refine D.norm_aeval_le _ (fun i ↦ ?_) zero_le_one
    rw [coeff_map]
    exact HenselComplete.norm_le_one _

/-- Elements of norm `< 1` are divisible by `ϖ`. -/
theorem exists_eq_mul_of_norm_lt_one {ϖ : O_E} (hϖ : Irreducible ϖ)
    [IsDiscreteValuationRing O_E] {z : D.F} (hz : ‖z‖ < 1) :
    ∃ w : D.F, ‖w‖ ≤ 1 ∧ z = algebraMap E D.F ϖ * w := by
  obtain ⟨q, hqd, rfl⟩ := (D.norm_le_one_iff z).1 hz.le
  have hmem : ∀ i, q.coeff i ∈ maximalIdeal O_E := by
    intro i
    by_contra h
    have hu : IsUnit (q.coeff i) := by
      by_contra h'
      exact h ((mem_maximalIdeal _).2 h')
    have := D.norm_aeval_eq_one q hqd ⟨i, hu⟩
    linarith
  rw [hϖ.maximalIdeal_eq] at hmem
  choose c hc using fun i ↦ Ideal.mem_span_singleton'.1 (hmem i)
  set q' : O_E[X] := ∑ i ∈ Finset.range (q.natDegree + 1), Polynomial.monomial i (c i)
  have hq : q = Polynomial.C ϖ * q' := by
    ext i
    simp only [q', coeff_C_mul, finsetSum_coeff, coeff_monomial, Finset.sum_ite_eq',
      Finset.mem_range]
    split_ifs with h
    · rw [← hc i, mul_comm]
    · rw [coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]
  refine ⟨aeval D.r (q'.map (algebraMap O_E E)), ?_, ?_⟩
  · refine D.norm_aeval_le _ (fun i ↦ ?_) zero_le_one
    rw [coeff_map]
    exact HenselComplete.norm_le_one _
  · rw [hq, Polynomial.map_mul, map_C, map_mul, aeval_C]
    rfl

local notation "O_F" => HenselComplete.integers D.F

/-- The `O_E`-algebra structure of `O_{E'}`. -/
noncomputable instance : Algebra O_E O_F :=
  (((algebraMap E D.F).comp (O_E).subtype).codRestrict _ fun a ↦ by
    rw [HenselComplete.mem_integers_iff]
    simp only [RingHom.coe_comp, Function.comp_apply, ValuationSubring.coe_subtype]
    rw [norm_algebraMap]
    exact HenselComplete.norm_le_one a).toAlgebra

lemma coe_algebraMap_OF (a : O_E) : ((algebraMap O_E O_F a : O_F) : D.F) = algebraMap E D.F a := rfl

/-- The root as an element of `O_{E'}`. -/
noncomputable def rI : O_F := ⟨D.r, (HenselComplete.mem_integers_iff _).2 D.norm_r_le⟩

lemma coe_aeval_rI (q : O_E[X]) :
    ((aeval D.rI q : O_F) : D.F) = aeval D.r (q.map (algebraMap O_E E)) := by
  rw [aeval_def, ← (O_F).subtype_apply, hom_eval₂, aeval_def, eval₂_map]
  rfl

lemma exists_aeval_rI (z : O_F) :
    ∃ q : O_E[X], q.natDegree < D.g.natDegree ∧ z = aeval D.rI q := by
  obtain ⟨q, hqd, hq⟩ := (D.norm_le_one_iff z).1 ((HenselComplete.mem_integers_iff _).1 z.2)
  exact ⟨q, hqd, Subtype.ext (by rw [coe_aeval_rI]; exact hq)⟩

lemma adjoin_rI : Algebra.adjoin O_E {D.rI} = ⊤ := by
  rw [eq_top_iff]
  intro z _
  obtain ⟨q, -, rfl⟩ := D.exists_aeval_rI z
  rw [Algebra.adjoin_singleton_eq_range_aeval]
  exact ⟨q, rfl⟩

lemma aeval_rI_g : aeval D.rI D.g = 0 := Subtype.ext (by rw [coe_aeval_rI, aeval_r_g]; rfl)

instance : Module.Finite O_E O_F := by
  refine ⟨⟨(Finset.range D.g.natDegree).image (fun i ↦ D.rI ^ i), ?_⟩⟩
  rw [eq_top_iff]
  intro z _
  obtain ⟨q, hqd, rfl⟩ := D.exists_aeval_rI z
  rw [aeval_eq_sum_range' hqd]
  refine Submodule.sum_mem _ fun i hi ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
  exact ⟨i, hi, rfl⟩

variable [IsDiscreteValuationRing (HenselComplete.integers E)]

instance : IsNoetherianRing O_F :=
  haveI : Algebra.FiniteType O_E O_F := inferInstance
  Algebra.FiniteType.isNoetherianRing O_E O_F

/-- **The uniformizer stays a uniformizer**: the maximal ideal of `O_{E'}` is `(ϖ)`. -/
theorem maximalIdeal_eq {ϖ : O_E} (hϖ : Irreducible ϖ) :
    maximalIdeal O_F = Ideal.span {algebraMap O_E O_F ϖ} := by
  apply le_antisymm
  · intro z hz
    have hz' : ‖(z : D.F)‖ < 1 := (HenselComplete.mem_maximalIdeal_iff_norm_lt_one z).1 hz
    obtain ⟨w, hw, hzw⟩ := D.exists_eq_mul_of_norm_lt_one hϖ hz'
    rw [Ideal.mem_span_singleton']
    exact ⟨⟨w, (HenselComplete.mem_integers_iff _).2 hw⟩, Subtype.ext (by
      rw [hzw, mul_comm]; rfl)⟩
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      HenselComplete.mem_maximalIdeal_iff_norm_lt_one, coe_algebraMap_OF, norm_algebraMap]
    exact (HenselComplete.mem_maximalIdeal_iff_norm_lt_one ϖ).1
      ((mem_maximalIdeal _).2 hϖ.not_isUnit)

/-- **`O_{E'}` is a DVR.** -/
theorem isDiscreteValuationRing : IsDiscreteValuationRing O_F := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O_E
  have hnf : ¬ IsField O_F := by
    intro hF
    have h := isField_iff_maximalIdeal_eq.1 hF
    rw [D.maximalIdeal_eq hϖ, Ideal.span_singleton_eq_bot] at h
    have : ((algebraMap O_E O_F ϖ : O_F) : D.F) = 0 := by rw [h]; rfl
    rw [coe_algebraMap_OF, map_eq_zero_iff _ (algebraMap E D.F).injective] at this
    exact hϖ.ne_zero (Subtype.ext this)
  exact ((IsDiscreteValuationRing.TFAE O_F hnf).out 1 0).mp (inferInstance : ValuationRing O_F)

/-- A uniformizer of `O_E` is a uniformizer of `O_{E'}`. -/
theorem irreducible_algebraMap {ϖ : O_E} (hϖ : Irreducible ϖ) :
    Irreducible (algebraMap O_E O_F ϖ) := by
  haveI := D.isDiscreteValuationRing
  refine IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ ?_ (D.maximalIdeal_eq hϖ)
  intro h
  have : ((algebraMap O_E O_F ϖ : O_F) : D.F) = 0 := by rw [h]; rfl
  rw [coe_algebraMap_OF, map_eq_zero_iff _ (algebraMap E D.F).injective] at this
  exact hϖ.ne_zero (Subtype.ext this)

omit [IsDiscreteValuationRing (HenselComplete.integers E)] in
lemma norm_sum_lt_one {ι : Type*} (s : Finset ι) (f : ι → D.F) (h : ∀ i ∈ s, ‖f i‖ < 1) :
    ‖∑ i ∈ s, f i‖ < 1 := by
  have := Valuation.map_sum_lt (NormedField.valuation (K := D.F)) one_ne_zero
    (fun i hi ↦ by
      rw [NormedField.valuation_apply]
      exact_mod_cast h i hi : ∀ i ∈ s, NormedField.valuation (f i) < 1)
  rw [NormedField.valuation_apply] at this
  exact_mod_cast this

/-- **`O_E → O_{E'}` is étale** (standard étale). -/
theorem etale : Algebra.Etale O_E O_F := by
  refine etale_of_aeval_eq_zero D.monic D.p₁ D.p₂ D.aeval_rI_g ?_ D.adjoin_rI ?_
  · -- `h = g' p₁ + g p₂ ≡ 1`, so `h(root)` has norm `1`
    rw [HenselComplete.isUnit_iff_norm_eq_one, coe_aeval_rI]
    set h := derivative D.g * D.p₁ + D.g * D.p₂
    have hlt : ∀ i, ‖((h - 1).map (algebraMap O_E E)).coeff i‖ < 1 := by
      intro i
      rw [coeff_map]
      refine (HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).1 ((residue_eq_zero_iff _).1 ?_)
      have := congrArg (fun p ↦ p.coeff i) D.hres
      simp only [coeff_map] at this
      rw [coeff_sub, map_sub, this, ← coeff_map, Polynomial.map_one, sub_self]
    have hsmall : ‖aeval D.r ((h - 1).map (algebraMap O_E E))‖ < 1 := by
      rw [aeval_eq_sum_range]
      refine D.norm_sum_lt_one _ _ fun i _ ↦ ?_
      rw [Algebra.smul_def, norm_mul, norm_algebraMap, norm_pow]
      exact (mul_le_of_le_one_right (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) D.norm_r_le)).trans_lt (hlt i)
    have heq : aeval D.r (h.map (algebraMap O_E E)) =
        1 + aeval D.r ((h - 1).map (algebraMap O_E E)) := by
      simp [Polynomial.map_sub]
    rw [heq, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hsmall.ne'),
      norm_one]
    exact max_eq_left hsmall.le
  · intro q hq h0
    have hqd : q.natDegree < D.g.natDegree := by
      by_cases hq0 : q = 0
      · rw [hq0, natDegree_zero]; exact D.natDegree_pos
      · exact natDegree_lt_natDegree hq0 hq
    have h1 : aeval D.r (q.map (algebraMap O_E E)) = 0 := by
      rw [← coe_aeval_rI, h0]; rfl
    have := D.eq_zero_of_aeval_r _ ((natDegree_map_le).trans_lt hqd) h1
    exact Polynomial.map_injective _ (FaithfulSMul.algebraMap_injective O_E E)
      (this.trans (Polynomial.map_zero _).symm)

end UnrData

end Unramified

end SemistableReduction
