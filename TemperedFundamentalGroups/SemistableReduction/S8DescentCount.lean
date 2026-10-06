/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8Galois
import TemperedFundamentalGroups.SemistableReduction.FundamentalInequalitySum
import TemperedFundamentalGroups.SemistableReduction.GaloisReduction

/-!
# Descent (A6), part 1: residue degrees in a tower

Blueprint §9.10 A6, §9.12 O6.6. Let `C(x) ⊆ E ⊆ L` be finite extensions. Every extension `w` of
the Gauss point `w_{0,1}` to `L` restricts to an extension `resExt w` to `E`.

* `sum_fibre_inertiaDeg_le`: the fundamental inequality over the base `(E, v)` (`v` an extension
  of `w_{0,1}` to `E`, made a normed field `VField v = WithAbs v`):
  `Σ_{w | v} f(w | v) ≤ [L : E]`;
* `inertiaDeg_gauss1_eq_mul`: residue degrees multiply in the tower;
* **`sum_fibre_inertiaDeg_eq`** (W4 over `E`): `Σ_{w | v} f(w | v) = [L : E]`, by comparing the
  W4 counts for `L` and `E` over `C(x)`;
* **`inertiaDeg_eq_card_stabilizer`**: for `L / E` Galois with group `H`, `f(w | v) = |H_w|`
  (`H` acts transitively on the extensions of `v`, A1).
-/

open IsLocalRing Valuation
open scoped NNReal Pointwise

namespace SemistableReduction

open FundamentalInequality

namespace S8A

namespace Descent

open GaussFibre GaussStability LocalGlobal DenseCompletion

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E L : Type*} [Field E] [Field L] [Algebra (RatFunc C) E] [Algebra (RatFunc C) L]
  [Algebra E L] [IsScalarTower (RatFunc C) E L]

/-- Restriction of extensions of `w_{0,1}` from `L` to `E`. -/
noncomputable def resExt (w : Ext C L) : Ext C E :=
  ⟨w.1.comap (algebraMap E L), Valuation.ext fun φ ↦ by
    rw [comap_apply, comap_apply, ← IsScalarTower.algebraMap_apply, ← comap_apply, w.2]⟩

lemma resExt_apply (w : Ext C L) (y : E) : (resExt w).1 y = w.1 (algebraMap E L y) := rfl

/-! ### The base `(E, v)` as a normed field -/

/-- `E` with the absolute value of an extension `v` of `w_{0,1}`. -/
abbrev VField (v : Ext C E) : Type _ := WithAbs v.1.toAbsoluteValue

lemma valuation_vField (v : Ext C E) (x : VField v) :
    NormedField.valuation x = v.1 x.ofAbs :=
  valuation_withAbs v.1 x

noncomputable instance (v : Ext C E) : NontriviallyNormedField (VField v) where
  __ : NormedField (VField v) := inferInstance
  non_trivial := by
    obtain ⟨c, hc⟩ := NontriviallyNormedField.non_trivial (α := C)
    refine ⟨WithAbs.toAbs _ (algebraMap (RatFunc C) E (algebraMap C (RatFunc C) c)), ?_⟩
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_toAbs, Valuation.toAbsoluteValue_apply,
      valuation_algebraMap_C, coe_nnnorm]
    exact hc

omit [Algebra (RatFunc C) L] [IsScalarTower (RatFunc C) E L] in
lemma algebraMap_vField_apply (v : Ext C E) (x : VField v) :
    algebraMap (VField v) L x = algebraMap E L x.ofAbs := rfl

omit [Algebra (RatFunc C) L] [IsScalarTower (RatFunc C) E L] in
lemma comap_vField (v : Ext C E) (w : Valuation L ℝ≥0) :
    w.comap (algebraMap (VField v) L) = NormedField.valuation (K := VField v) ↔
      w.comap (algebraMap E L) = v.1 := by
  constructor
  · intro h
    ext y
    have := congrArg (fun u : Valuation (VField v) ℝ≥0 ↦ u (WithAbs.toAbs _ y)) h
    simp only [comap_apply, algebraMap_vField_apply] at this
    rw [comap_apply, this, valuation_vField]
  · intro h
    ext x
    have := congrArg (fun u : Valuation E ℝ≥0 ↦ u x.ofAbs) h
    simp only [comap_apply] at this
    rw [comap_apply, algebraMap_vField_apply, valuation_vField, this]

/-- The fibre of the restriction over `v`. -/
abbrev Fibre (v : Ext C E) : Type _ := {w : Ext C L // resExt w = v}

/-- The extensions of the norm of `VField v` are the extensions of `w_{0,1}` over `v`. -/
noncomputable def fibreEquiv (v : Ext C E) : Extension (VField v) L ≃ Fibre (L := L) v where
  toFun w := ⟨⟨w.1, Valuation.ext fun φ ↦ by
      rw [comap_apply, IsScalarTower.algebraMap_apply (RatFunc C) E L]
      have := congrArg (fun u : Valuation E ℝ≥0 ↦ u (algebraMap (RatFunc C) E φ))
        ((comap_vField v w.1).1 w.2)
      simp only [comap_apply] at this
      rw [this, valuation_algebraMap]⟩,
    Subtype.ext ((comap_vField v w.1).1 w.2)⟩
  invFun w := ⟨w.1.1, (comap_vField v w.1.1).2 (congrArg Subtype.val w.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Algebra (RatFunc C) L] [IsScalarTower (RatFunc C) E L] in
omit [Algebra (RatFunc C) L] [IsScalarTower (RatFunc C) E L] in
lemma inertiaDeg_vField (v : Ext C E) (w : Extension (VField v) L) :
    haveI : v.1.HasExtension w.1 := hasExtension_of_comap_eq ((comap_vField v w.1).1 w.2)
    inertiaDeg (NormedField.valuation (K := VField v)) w.1 = inertiaDeg v.1 w.1 := by
  haveI : v.1.HasExtension w.1 := hasExtension_of_comap_eq ((comap_vField v w.1).1 w.2)
  let e : (NormedField.valuation (K := VField v)).valuationSubring ≃+* v.1.valuationSubring :=
    { toFun := fun x ↦ ⟨x.1.ofAbs, by
        have := x.2
        rwa [mem_valuationSubring_iff, valuation_vField] at this⟩
      invFun := fun y ↦ ⟨WithAbs.toAbs _ y.1, by
        rw [mem_valuationSubring_iff, valuation_vField]
        exact y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine Algebra.finrank_eq_of_equiv_equiv (IsLocalRing.ResidueField.mapEquiv e)
    (RingEquiv.refl _) ?_
  ext r
  obtain ⟨x, rfl⟩ := residue_surjective r
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap,
    HasExtension.algebraMap_residue_eq_residue_algebraMap]
  rfl

open Classical in
/-- The relative residue degree `f(w | v)` (`0` if `w` does not lie over `v`). -/
noncomputable def fdeg (v : Ext C E) (w : Ext C L) : ℕ :=
  if h : resExt w = v then
    @inertiaDeg E L _ _ _ ℝ≥0 ℝ≥0 _ _ v.1 w.1 (hasExtension_of_comap_eq (congrArg Subtype.val h))
  else 0

lemma fdeg_of_eq {v : Ext C E} {w : Ext C L} (h : resExt w = v) :
    fdeg v w = @inertiaDeg E L _ _ _ ℝ≥0 ℝ≥0 _ _ v.1 w.1
      (hasExtension_of_comap_eq (congrArg Subtype.val h)) := by
  classical
  rw [fdeg, dif_pos h]

lemma fdeg_of_ne {v : Ext C E} {w : Ext C L} (h : resExt w ≠ v) : fdeg v w = 0 := by
  classical
  rw [fdeg, dif_neg h]

/-- **Residue degrees multiply in the tower** `C(x) ⊆ E ⊆ L`. -/
theorem inertiaDeg_gauss1_eq_mul (w : Ext C L) :
    inertiaDeg (gauss1 C) w.1 =
      inertiaDeg (gauss1 C) (resExt (E := E) w).1 * fdeg (resExt (E := E) w) w := by
  rw [fdeg_of_eq rfl]
  letI : (resExt (E := E) w).1.HasExtension w.1 :=
    hasExtension_of_comap_eq (congrArg Subtype.val (rfl : resExt (E := E) w = resExt w))
  haveI : IsScalarTower (ResidueField (gauss1 C).valuationSubring)
      (ResidueField (resExt (E := E) w).1.valuationSubring)
      (ResidueField w.1.valuationSubring) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    obtain ⟨x, rfl⟩ := residue_surjective r
    rw [HasExtension.algebraMap_residue_eq_residue_algebraMap,
      HasExtension.algebraMap_residue_eq_residue_algebraMap,
      HasExtension.algebraMap_residue_eq_residue_algebraMap]
    congr 1
    ext
    change algebraMap (RatFunc C) L x = algebraMap E L (algebraMap (RatFunc C) E x)
    rw [← IsScalarTower.algebraMap_apply]
  exact (Module.finrank_mul_finrank _ _ _).symm

section Ineq

variable [FiniteDimensional E L] [Algebra.IsSeparable E L]

instance [Finite (Ext C L)] (v : Ext C E) : Finite (Fibre (L := L) v) :=
  Subtype.finite

/-- **The fundamental inequality over `(E, v)`**: `Σ_{w | v} f(w | v) ≤ [L : E]`. -/
theorem sum_fdeg_le [Fintype (Ext C L)] (v : Ext C E) :
    ∑ w : Ext C L, fdeg v w ≤ Module.finrank E L := by
  classical
  have hfin : Module.finrank (VField v) L = Module.finrank E L :=
    Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv _) (RingEquiv.refl L) (by ext; rfl)
  haveI : FiniteDimensional (VField v) L := Module.finite_of_finrank_pos (by
    rw [hfin]; exact Module.finrank_pos)
  haveI : Algebra.IsSeparable (VField v) L :=
    Algebra.IsSeparable.of_equiv_equiv (WithAbs.equiv _).symm (RingEquiv.refl L) (by ext; rfl)
  haveI : Finite (Extension (VField v) L) := Finite.of_equiv _ (fibreEquiv v).symm
  letI : Fintype (Extension (VField v) L) := Fintype.ofFinite _
  have h := finsum_ramificationIdx_mul_inertiaDeg_le (F := VField v) (F' := L)
  rw [finsum_eq_sum_of_fintype, hfin] at h
  refine le_trans (le_of_eq ?_) (le_trans (Finset.sum_le_sum fun x _ ↦
    Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (ramificationIdx_ne_zero x.1))) h)
  -- the sum over the fibre
  have h1 : ∑ w : Ext C L, fdeg v w = ∑ x : Fibre (L := L) v, fdeg v x.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun w ↦ resExt w = v) (by simp),
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    split_ifs with h
    · rfl
    · exact fdeg_of_ne h
  rw [h1, ← Equiv.sum_comp (fibreEquiv v)]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [fdeg_of_eq (fibreEquiv v x).2, inertiaDeg_vField]
  rfl

end Ineq

section W4

variable [IsAlgClosed C] [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]

include hp hp1 in
/-- **W4 over `E`**: `Σ_{w | v} f(w | v) = [L : E]` for every extension `v` of `w_{0,1}` to
`E`. -/
theorem sum_fdeg_eq [Fintype (Ext C L)] (v : Ext C E) :
    ∑ w : Ext C L, fdeg v w = Module.finrank E L := by
  classical
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  haveI : Algebra.IsSeparable E L := Algebra.isSeparable_tower_top_of_isSeparable (RatFunc C) E L
  haveI := finite_ext (F := E) hp hp1
  letI : Fintype (Ext C E) := Fintype.ofFinite _
  set n := Module.finrank E L
  set g : Ext C E → ℕ := fun v ↦ inertiaDeg (gauss1 C) v.1
  have hle : ∀ v : Ext C E, ∑ w : Ext C L, fdeg v w ≤ n := sum_fdeg_le
  have hL := sum_inertiaDeg_eq (F := L) hp hp1
  have hE := sum_inertiaDeg_eq (F := E) hp hp1
  have htower : Module.finrank (RatFunc C) L = Module.finrank (RatFunc C) E * n :=
    (Module.finrank_mul_finrank (RatFunc C) E L).symm
  -- group the extensions of `L` by their restriction
  have hgroup : ∑ w : Ext C L, inertiaDeg (gauss1 C) w.1 =
      ∑ v : Ext C E, g v * ∑ w : Ext C L, fdeg v w := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [inertiaDeg_gauss1_eq_mul (E := E) w, Finset.sum_eq_single (resExt w)]
    · intro v _ hv
      rw [fdeg_of_ne (Ne.symm hv), mul_zero]
    · simp
  rw [hgroup, htower, ← hE, Finset.sum_mul] at hL
  have hpos : ∀ v : Ext C E, 0 < g v := fun v ↦ by
    haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField v.1.valuationSubring) := finite_residueField
    exact Module.finrank_pos
  have heq := (Finset.sum_eq_sum_iff_of_le fun v _ ↦
    Nat.mul_le_mul_left (g v) (hle v)).1 hL v (Finset.mem_univ v)
  exact le_antisymm (hle v) (Nat.le_of_mul_le_mul_left heq.ge (hpos v))

end W4

/-! ### The Galois action on the extensions -/

section Galois

/-- `σ • w = w ∘ σ⁻¹`. -/
noncomputable instance : MulAction (L ≃ₐ[E] L) (Ext C L) where
  smul σ w := ⟨w.1.comap σ.symm.toRingHom, Valuation.ext fun φ ↦ by
    change w.1 (σ.symm (algebraMap (RatFunc C) L φ)) = _
    rw [IsScalarTower.algebraMap_apply (RatFunc C) E L, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply, valuation_algebraMap]⟩
  one_smul w := rfl
  mul_smul σ τ w := rfl

lemma smul_apply (σ : L ≃ₐ[E] L) (w : Ext C L) (y : L) : (σ • w).1 y = w.1 (σ.symm y) := rfl

lemma resExt_smul (σ : L ≃ₐ[E] L) (w : Ext C L) : resExt (E := E) (σ • w) = resExt w :=
  Subtype.ext (Valuation.ext fun y ↦ by
    change w.1 (σ.symm (algebraMap E L y)) = w.1 (algebraMap E L y)
    rw [AlgEquiv.commutes])

lemma valuationSubring_smul (σ : L ≃ₐ[E] L) (w : Ext C L) :
    (σ • w).1.valuationSubring = σ • w.1.valuationSubring := by
  ext y
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, mem_valuationSubring_iff,
    mem_valuationSubring_iff, smul_apply, AlgEquiv.smul_def]
  rfl

variable [FiniteDimensional (RatFunc C) L] [IsAlgClosed C]

/-- **A1 for extensions of `w_{0,1}`**: the extensions over `v` form one orbit. -/
theorem exists_smul_eq_of_resExt [IsGalois E L] {w₁ w₂ : Ext C L}
    (h : resExt (E := E) w₁ = resExt w₂) : ∃ σ : L ≃ₐ[E] L, σ • w₁ = w₂ := by
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  have hc : w₁.1.valuationSubring.comap (algebraMap E L) =
      w₂.1.valuationSubring.comap (algebraMap E L) := by
    ext y
    simp only [ValuationSubring.mem_comap, mem_valuationSubring_iff]
    rw [← resExt_apply, ← resExt_apply, h]
  obtain ⟨σ, hσ⟩ := GaloisReduction.exists_smul_eq _ _ hc
  refine ⟨σ, eq_of_le (ramificationIdx_eq_one _) fun a ha ↦ ?_⟩
  have : a ∈ (σ • w₁).1.valuationSubring := (mem_valuationSubring_iff _ _).2 ha
  rw [valuationSubring_smul, hσ] at this
  exact (mem_valuationSubring_iff _ _).1 this

omit [FiniteDimensional (RatFunc C) L] [IsAlgClosed C] in
/-- `f(σ w | v) = f(w | v)`. -/
lemma fdeg_smul (v : Ext C E) (σ : L ≃ₐ[E] L) (w : Ext C L) : fdeg v (σ • w) = fdeg v w := by
  by_cases h : resExt w = v
  · have h' : resExt (σ • w) = v := (resExt_smul σ w).trans h
    rw [fdeg_of_eq h, fdeg_of_eq h']
    letI : v.1.HasExtension w.1 := hasExtension_of_comap_eq (congrArg Subtype.val h)
    letI : v.1.HasExtension (σ • w).1 := hasExtension_of_comap_eq (congrArg Subtype.val h')
    let e : w.1.valuationSubring ≃+* (σ • w).1.valuationSubring :=
      { toFun := fun x ↦ ⟨σ x, by
          change w.1 (σ.symm (σ x)) ≤ 1
          rw [AlgEquiv.symm_apply_apply]; exact x.2⟩
        invFun := fun x ↦ ⟨σ.symm x, x.2⟩
        left_inv := fun x ↦ Subtype.ext (σ.symm_apply_apply _)
        right_inv := fun x ↦ Subtype.ext (σ.apply_symm_apply _)
        map_mul' := fun _ _ ↦ Subtype.ext (map_mul σ _ _)
        map_add' := fun _ _ ↦ Subtype.ext (map_add σ _ _) }
    refine (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl _)
      (IsLocalRing.ResidueField.mapEquiv e) ?_).symm
    ext r
    obtain ⟨x, rfl⟩ := residue_surjective r
    simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.refl_apply, IsLocalRing.ResidueField.mapEquiv_apply,
      HasExtension.algebraMap_residue_eq_residue_algebraMap, IsLocalRing.ResidueField.map_residue]
    congr 1
    ext
    exact (AlgEquiv.commutes σ (x : E)).symm
  · rw [fdeg_of_ne h, fdeg_of_ne fun h' ↦ h ((resExt_smul σ w).symm.trans h')]

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [FiniteDimensional (RatFunc C) E]

include hp hp1 in
/-- **`f(w | v) = |H_w|`** for `L / E` Galois with group `H`. -/
theorem fdeg_eq_card_stabilizer [IsGalois E L] (w : Ext C L) :
    fdeg (resExt (E := E) w) w = Nat.card (MulAction.stabilizer (L ≃ₐ[E] L) w) := by
  classical
  haveI : FiniteDimensional E L := FiniteDimensional.right (RatFunc C) E L
  haveI := finite_ext (F := E) hp hp1
  haveI := finite_ext (F := L) hp hp1
  letI : Fintype (Ext C E) := Fintype.ofFinite _
  letI : Fintype (Ext C L) := Fintype.ofFinite _
  have hsum := sum_fdeg_eq hp hp1 (L := L) (resExt (E := E) w)
  -- the fibre is the orbit of `w`
  have horb : ∀ w' : Ext C L, resExt (E := E) w' = resExt w ↔
      w' ∈ MulAction.orbit (L ≃ₐ[E] L) w := by
    intro w'
    constructor
    · intro h
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_resExt h.symm
      exact ⟨σ, hσ⟩
    · rintro ⟨σ, rfl⟩
      exact resExt_smul σ w
  have hfib : ∑ w' : Ext C L, fdeg (resExt (E := E) w) w' =
      Nat.card (MulAction.orbit (L ≃ₐ[E] L) w) * fdeg (resExt (E := E) w) w := by
    rw [← Finset.sum_filter_of_ne (p := fun w' ↦ w' ∈ MulAction.orbit (L ≃ₐ[E] L) w)
      fun w' _ hw' ↦ by
        by_contra h
        exact hw' (fdeg_of_ne fun h' ↦ h ((horb w').1 h'))]
    have hc : ∀ w' ∈ Finset.univ.filter (fun w' ↦ w' ∈ MulAction.orbit (L ≃ₐ[E] L) w),
        fdeg (resExt (E := E) w) w' = fdeg (resExt (E := E) w) w := by
      intro w' hw'
      obtain ⟨σ, hσ⟩ := (Finset.mem_filter.1 hw').2
      rw [← hσ]
      exact fdeg_smul _ σ w
    rw [Finset.sum_congr rfl hc, Finset.sum_const, smul_eq_mul, Nat.card_eq_fintype_card,
      Fintype.card_subtype]
  have hG : Nat.card (MulAction.orbit (L ≃ₐ[E] L) w) *
      Nat.card (MulAction.stabilizer (L ≃ₐ[E] L) w) = Module.finrank E L := by
    rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer, Subgroup.index_mul_card,
      IsGalois.card_aut_eq_finrank]
  rw [hfib, ← hG] at hsum
  haveI : Nonempty (MulAction.orbit (L ≃ₐ[E] L) w) := ⟨⟨w, MulAction.mem_orbit_self w⟩⟩
  exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := MulAction.orbit (L ≃ₐ[E] L) w)) hsum

end Galois

end Descent

end S8A

end SemistableReduction
