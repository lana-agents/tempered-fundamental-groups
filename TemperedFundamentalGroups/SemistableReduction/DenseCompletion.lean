/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.FundamentalInequality

/-!
# Dense subfields and completions of rank-one valued fields

Blueprint §9.4, B1. Let `B` be a non-archimedean normed field and `j : A →+* B` a ring
homomorphism from a field `A` with dense image; let `v` be the induced valuation on `A`
(`v a = ‖j a‖₊`). Then

* `valueGroup_eq_of_denseRange`: `v` and the norm valuation of `B` have the same value group;
* `residueEquiv`: `j` induces an isomorphism of residue fields.

Consequently ramification index and inertia degree can be computed after completing
(`ramificationIdx_eq_of_denseRange`, `inertiaDeg_eq_of_denseRange`): for a square of dense
embeddings `F → K`, `F' → L` with `L / K` a normed algebra, `e(F' | F) = e(L | K)` and
`f(F' | F) = f(L | K)`.

For the completion `\hat F = UniformSpace.Completion F` of a non-archimedean normed field
(`completion_valueGroup`, `completionResidueEquiv`): `\hat F` is again non-archimedean (and
nontrivially normed if `F` is), with the same values and the same residue field.

Finally `Valuation.toAbsoluteValue` turns a real valuation `w : Valuation F ℝ≥0` into an absolute
value; `WithAbs w.toAbsoluteValue` is then a non-archimedean normed field whose norm valuation is
`w` (`valuation_withAbs`). This is how a Gauss valuation with real values becomes a normed field.
-/

open IsLocalRing Valuation NNReal

namespace SemistableReduction

open FundamentalInequality

namespace DenseCompletion

section Dense

variable {A B : Type*} [Field A] [NormedField B] [IsUltrametricDist B] (j : A →+* B)
  (v : Valuation A ℝ≥0)

/-- In an ultrametric normed group, `‖a - b‖ < ‖b‖` forces `‖a‖ = ‖b‖`. -/
lemma norm_eq_of_norm_sub_lt {a b : B} (h : ‖a - b‖ < ‖b‖) : ‖a‖ = ‖b‖ := by
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h.ne
  rw [sub_add_cancel, max_eq_right h.le] at this
  exact this

omit [IsUltrametricDist B] in
lemma exists_norm_sub_lt (hj : DenseRange j) (b : B) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : A, ‖j a - b‖ < ε := by
  obtain ⟨a, ha⟩ := Metric.denseRange_iff.1 hj b ε hε
  exact ⟨a, by rwa [dist_comm, dist_eq_norm] at ha⟩

variable {j v}

/-- **Dense subfields have the same values.** -/
theorem valueGroup_eq_of_denseRange (hv : ∀ a, v a = ‖j a‖₊) (hj : DenseRange j) :
    valueGroup v = valueGroup (NormedField.valuation (K := B)) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, ha⟩
    exact ⟨j a, by rw [NormedField.valuation_apply, ← hv, ha]⟩
  · rintro g ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact g.ne_zero (by rw [← hb, map_zero])
    obtain ⟨a, ha⟩ := exists_norm_sub_lt j hj b (norm_pos_iff.2 hb0)
    refine ⟨a, ?_⟩
    rw [← hb, hv, NormedField.valuation_apply]
    exact NNReal.eq (norm_eq_of_norm_sub_lt ha)

variable (hv : ∀ a, v a = ‖j a‖₊)
include hv

/-- The map of valuation rings induced by `j`. -/
noncomputable def integersHom :
    v.valuationSubring →+* (NormedField.valuation (K := B)).valuationSubring :=
  (j.comp v.valuationSubring.subtype).codRestrict (NormedField.valuation (K := B)).valuationSubring
    fun x ↦ by
      change NormedField.valuation (j x) ≤ 1
      rw [NormedField.valuation_apply, ← hv]
      exact x.2

@[simp]
lemma coe_integersHom (x : v.valuationSubring) : (integersHom hv x : B) = j x := rfl

instance isLocalHom_integersHom : IsLocalHom (integersHom hv) := by
  refine ⟨fun x hx ↦ ?_⟩
  rw [(Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one] at hx ⊢
  change NormedField.valuation (j x) = 1 at hx
  rw [NormedField.valuation_apply, ← hv] at hx
  exact hx

/-- The map of residue fields induced by `j`. -/
noncomputable def residueHom :
    ResidueField v.valuationSubring →+*
      ResidueField (NormedField.valuation (K := B)).valuationSubring :=
  ResidueField.map (integersHom hv)

@[simp]
lemma residueHom_residue (x : v.valuationSubring) :
    residueHom hv (residue _ x) = residue _ (integersHom hv x) :=
  ResidueField.map_residue _ _

omit hv in
/-- A residue class of the valuation ring of `B` is represented by any element at distance
`< 1`. -/
lemma residue_eq_of_norm_sub_lt_one {x y : (NormedField.valuation (K := B)).valuationSubring}
    (h : ‖(x : B) - y‖ < 1) : residue _ x = residue _ y := by
  rw [← sub_eq_zero, ← _root_.map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.valuationSubring.integers _).isUnit_iff_valuation_eq_one]
  change ¬ NormedField.valuation ((x : B) - y) = 1
  rw [NormedField.valuation_apply]
  intro h1
  have : ‖(x : B) - y‖ = 1 := congrArg NNReal.toReal h1
  exact h.ne this

lemma residueHom_surjective (hj : DenseRange j) : Function.Surjective (residueHom hv) := by
  intro r
  obtain ⟨b, rfl⟩ := residue_surjective r
  obtain ⟨a, ha⟩ := exists_norm_sub_lt j hj (b : B) one_pos
  have hb : ‖(b : B)‖ ≤ 1 := b.2
  have haO : v a ≤ 1 := by
    rw [hv]
    change ‖j a‖ ≤ 1
    have := IsUltrametricDist.norm_add_le_max (j a - b) (b : B)
    rw [sub_add_cancel] at this
    exact this.trans (max_le ha.le hb)
  refine ⟨residue _ ⟨a, haO⟩, ?_⟩
  rw [residueHom_residue]
  exact residue_eq_of_norm_sub_lt_one ha

/-- **Dense subfields have the same residue field.** -/
noncomputable def residueEquiv (hj : DenseRange j) :
    ResidueField v.valuationSubring ≃+*
      ResidueField (NormedField.valuation (K := B)).valuationSubring :=
  RingEquiv.ofBijective (residueHom hv) ⟨(residueHom hv).injective, residueHom_surjective hv hj⟩

@[simp]
lemma residueEquiv_residue (hj : DenseRange j) (x : v.valuationSubring) :
    residueEquiv hv hj (residue _ x) = residue _ (integersHom hv x) :=
  residueHom_residue hv x

end Dense

section Tower

/-- A normed algebra over a normed field: the norm valuation of `L` restricts to that of `K`. -/
lemma comap_valuation_algebraMap {K L : Type*} [NormedField K] [IsUltrametricDist K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] :
    (NormedField.valuation (K := L)).comap (algebraMap K L) = NormedField.valuation (K := K) := by
  ext x
  simp only [comap_apply, NormedField.valuation_apply]
  exact congrArg _ (NNReal.eq (norm_algebraMap' L x))

/-- A valuation extends its restriction (stated for an equality of valuations). -/
lemma hasExtension_of_comap_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {v : Valuation K Γ} {w : Valuation L Γ}
    (h : w.comap (algebraMap K L) = v) : v.HasExtension w :=
  ⟨by rw [← h]; exact Valuation.IsEquiv.refl⟩

instance hasExtension_normedField {K L : Type*} [NormedField K] [IsUltrametricDist K]
    [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L] :
    (NormedField.valuation (K := K)).HasExtension (NormedField.valuation (K := L)) :=
  hasExtension_of_comap_eq comap_valuation_algebraMap

variable {F F' K L : Type*} [Field F] [Field F'] [Algebra F F']
  [NormedField K] [IsUltrametricDist K] [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
  {i : F →+* K} {j : F' →+* L}
  (hij : ∀ x, j (algebraMap F F' x) = algebraMap K L (i x))
  (hi : DenseRange i) (hj : DenseRange j)
  {v : Valuation F ℝ≥0} {w : Valuation F' ℝ≥0}
  (hv : ∀ a, v a = ‖i a‖₊) (hw : ∀ a, w a = ‖j a‖₊)
include hij hi hj hw

/-- **The ramification index does not change under dense embeddings.** -/
theorem ramificationIdx_eq_of_denseRange :
    ramificationIdx F w = ramificationIdx K (NormedField.valuation (K := L)) := by
  have h1 : valueGroup (w.comap (algebraMap F F')) =
      valueGroup ((NormedField.valuation (K := L)).comap (algebraMap K L)) := by
    rw [comap_valuation_algebraMap]
    refine valueGroup_eq_of_denseRange (fun a ↦ ?_) hi
    rw [comap_apply, hw, hij, NNReal.eq_iff, coe_nnnorm, coe_nnnorm, norm_algebraMap']
  rw [ramificationIdx, ramificationIdx, h1, valueGroup_eq_of_denseRange hw hj]

include hv in
/-- **The inertia degree does not change under dense embeddings.** -/
theorem inertiaDeg_eq_of_denseRange [v.HasExtension w] :
    inertiaDeg v w =
      inertiaDeg (NormedField.valuation (K := K)) (NormedField.valuation (K := L)) := by
  refine Algebra.finrank_eq_of_equiv_equiv (residueEquiv hv hi) (residueEquiv hw hj) ?_
  ext r
  obtain ⟨x, rfl⟩ := residue_surjective r
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, residueEquiv_residue]
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap,
    HasExtension.algebraMap_residue_eq_residue_algebraMap, residueEquiv_residue]
  congr 1
  ext
  simp only [coe_integersHom, HasExtension.coe_algebraMap_valuationSubring_eq]
  exact (hij x).symm

end Tower

section Completion

open UniformSpace

variable (F : Type*) [NormedField F] [IsUltrametricDist F]

instance isUltrametricDist_completion : IsUltrametricDist (Completion F) :=
  IsUltrametricDist.of_normedAlgebra F

/-- The completion of a nontrivially normed field is nontrivially normed. -/
noncomputable instance nontriviallyNormedField_completion (F : Type*) [NontriviallyNormedField F] :
    NontriviallyNormedField (Completion F) where
  __ : NormedField (Completion F) := inferInstance
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := F)
    ⟨x, by rwa [Completion.norm_coe]⟩

omit [IsUltrametricDist F] in
lemma algebraMap_completion (x : F) : algebraMap F (Completion F) x = x := by
  rw [Completion.algebraMap_def]
  rfl

omit [IsUltrametricDist F] in
lemma denseRange_algebraMap_completion : DenseRange (algebraMap F (Completion F)) := by
  have : (algebraMap F (Completion F) : F → Completion F) = (↑) :=
    funext (algebraMap_completion F)
  rw [this]
  exact Completion.denseRange_coe

lemma valuation_eq_norm_algebraMap_completion (x : F) :
    NormedField.valuation x = ‖algebraMap F (Completion F) x‖₊ := by
  rw [NormedField.valuation_apply, algebraMap_completion, NNReal.eq_iff, coe_nnnorm, coe_nnnorm,
    Completion.norm_coe]

/-- **B1.** The completion has the same values. -/
theorem completion_valueGroup :
    valueGroup (NormedField.valuation (K := F)) =
      valueGroup (NormedField.valuation (K := Completion F)) :=
  valueGroup_eq_of_denseRange (valuation_eq_norm_algebraMap_completion F)
    (denseRange_algebraMap_completion F)

/-- **B1.** The completion has the same residue field. -/
noncomputable def completionResidueEquiv :
    ResidueField (NormedField.valuation (K := F)).valuationSubring ≃+*
      ResidueField (NormedField.valuation (K := Completion F)).valuationSubring :=
  residueEquiv (valuation_eq_norm_algebraMap_completion F) (denseRange_algebraMap_completion F)

end Completion

section RealValuation

variable {F : Type*} [Field F]

/-- A real valuation as an absolute value. -/
noncomputable def _root_.Valuation.toAbsoluteValue (w : Valuation F ℝ≥0) :
    AbsoluteValue F ℝ where
  toFun x := w x
  map_mul' x y := by simp
  nonneg' x := (w x).2
  eq_zero' x := by simp
  add_le' x y := by
    have := w.map_add x y
    have h : ((max (w x) (w y) : ℝ≥0) : ℝ) ≤ (w x : ℝ) + w y := by
      rw [NNReal.coe_max]
      exact max_le (le_add_of_nonneg_right (w y).2) (le_add_of_nonneg_left (w x).2)
    exact (NNReal.coe_le_coe.2 this).trans h

@[simp]
lemma _root_.Valuation.toAbsoluteValue_apply (w : Valuation F ℝ≥0) (x : F) :
    w.toAbsoluteValue x = w x := rfl

instance isUltrametricDist_withAbs (w : Valuation F ℝ≥0) :
    IsUltrametricDist (WithAbs w.toAbsoluteValue) :=
  IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y ↦ by
    simp only [WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_add, Valuation.toAbsoluteValue_apply]
    rw [← NNReal.coe_max, NNReal.coe_le_coe]
    exact w.map_add _ _

lemma valuation_withAbs (w : Valuation F ℝ≥0) (x : WithAbs w.toAbsoluteValue) :
    NormedField.valuation x = w x.ofAbs :=
  NNReal.eq (by rw [NormedField.valuation_apply, coe_nnnorm, WithAbs.norm_eq_apply_ofAbs]; rfl)

end RealValuation

end DenseCompletion

end SemistableReduction
