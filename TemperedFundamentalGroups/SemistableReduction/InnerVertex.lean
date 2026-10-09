/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.VertexMatch

/-!
# The inner vertex of an annulus: the inversion `x ↦ c/x`

Blueprint §9.9, W7 layer S6 (inner vertex). The inversion `σ_c : C(x) → C(x)`, `x ↦ c/x`, is an
involution of `C(x)` over `C` (`inv`), it exchanges the Gauss points `w_{0,s}` and `w_{0,|c|/s}`
(`gaussRat_inv`), preserves the node chart `O_C[x, c/x]` (`map_nodeRing`) and the open segment
`(|c|, 1)`. Twisting the `C(x)`-algebra structure of `F'` by `σ_c` (`Inv c F'`) turns the inner
vertex `w_{0,|c|}` into the outer vertex `w_{0,1}`, so `VertexMatch` applies to the inner vertex.
-/

open Polynomial IsLocalRing Valuation
open scoped NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]

section Inversion

variable {c : C} (hc0 : c ≠ 0)

/-- `p ↦ p(c/X)`, injective since `c/X` is transcendental. -/
noncomputable def invPoly (c : C) : C[X] →ₐ[C] RatFunc C :=
  aeval (algebraMap C (RatFunc C) c / RatFunc.X)

omit [IsUltrametricDist C] in
include hc0 in
lemma invPoly_injective : Function.Injective (invPoly c) := by
  have ht : Transcendental C (algebraMap C (RatFunc C) c / RatFunc.X) := by
    intro halg
    have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
    have hX : (RatFunc.X : RatFunc C) = algebraMap C (RatFunc C) c *
        (algebraMap C (RatFunc C) c / RatFunc.X)⁻¹ := by
      rw [inv_div, mul_div_cancel₀ _ hc']
    have : IsAlgebraic C (RatFunc.X : RatFunc C) := by
      rw [hX]
      exact (isAlgebraic_algebraMap (R := C) (A := RatFunc C) c).mul halg.inv
    exact RatFunc.transcendental_X this
  exact (injective_iff_map_eq_zero _).2 fun p hp ↦ by
    by_contra h
    exact ht ⟨p, h, hp⟩

include hc0 in
/-- The inversion `x ↦ c/x` of `C(x)` as an algebra homomorphism. -/
noncomputable def invHom : RatFunc C →ₐ[C] RatFunc C :=
  RatFunc.liftAlgHom (invPoly c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (invPoly_injective hc0))

omit [IsUltrametricDist C] in
lemma invHom_algebraMap (p : C[X]) :
    invHom hc0 (algebraMap C[X] (RatFunc C) p) =
      aeval (algebraMap C (RatFunc C) c / RatFunc.X) p := by
  have := RatFunc.liftAlgHom_apply_div (invPoly c)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (invPoly_injective hc0)) p 1
  simpa [invPoly, invHom] using this

omit [IsUltrametricDist C] in
lemma invHom_X : invHom hc0 RatFunc.X = algebraMap C (RatFunc C) c / RatFunc.X := by
  simpa using invHom_algebraMap hc0 Polynomial.X

omit [IsUltrametricDist C] in
lemma invHom_invHom (φ : RatFunc C) : invHom hc0 (invHom hc0 φ) = φ := by
  have hp (p : C[X]) : invHom hc0 (invHom hc0 (algebraMap C[X] (RatFunc C) p)) =
      algebraMap C[X] (RatFunc C) p := by
    rw [invHom_algebraMap, ← Polynomial.aeval_algHom_apply, map_div₀, AlgHom.commutes,
      invHom_X]
    have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
    rw [div_div_cancel₀ hc, ← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply,
      aeval_X_left_apply]
  rw [← RatFunc.num_div_denom φ, map_div₀, map_div₀, hp, hp]

/-- The inversion `x ↦ c/x`, an involution of `C(x)`. -/
noncomputable def inv : RatFunc C ≃ₐ[C] RatFunc C :=
  AlgEquiv.ofAlgHom (invHom hc0) (invHom hc0) (AlgHom.ext (invHom_invHom hc0))
    (AlgHom.ext (invHom_invHom hc0))

omit [IsUltrametricDist C] in
lemma inv_apply (φ : RatFunc C) : inv hc0 φ = invHom hc0 φ := rfl

omit [IsUltrametricDist C] in
lemma inv_inv_apply (φ : RatFunc C) : inv hc0 (inv hc0 φ) = φ := invHom_invHom hc0 φ

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

/-- The inverse radius `|c| / s`. -/
noncomputable def invRad (hc0 : c ≠ 0) (s : ℝ≥0ˣ) : ℝ≥0ˣ :=
  Units.mk0 ‖c‖₊ (by simpa using hc0) * s⁻¹

omit [IsUltrametricDist C] in
lemma coe_invRad (s : ℝ≥0ˣ) : ((invRad hc0 s : ℝ≥0ˣ) : ℝ≥0) = ‖c‖₊ / s := by
  simp [invRad, div_eq_mul_inv]

lemma gaussRat_X_sub_C (s : ℝ≥0ˣ) (b : C) :
    w s (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) = max ‖b‖₊ (s : ℝ≥0) := by
  rw [gaussRat_algebraMap, gauss_X_sub_C, zero_sub, Valuation.map_neg, NormedField.valuation_apply]

lemma gaussRat_C_sub_mul_X (s : ℝ≥0ˣ) (b : C) :
    w s (algebraMap C (RatFunc C) c - algebraMap C (RatFunc C) b * RatFunc.X) =
      max ‖c‖₊ (‖b‖₊ * s) := by
  rcases eq_or_ne b 0 with rfl | hb
  · rw [map_zero, zero_mul, sub_zero, gaussRat_C]
    simp
  have : algebraMap C (RatFunc C) c - algebraMap C (RatFunc C) b * RatFunc.X =
      algebraMap C (RatFunc C) (-b) * algebraMap C[X] (RatFunc C) (X - Polynomial.C (c / b)) := by
    have hcb : algebraMap C[X] (RatFunc C) (Polynomial.C (c / b)) =
        algebraMap C (RatFunc C) c / algebraMap C (RatFunc C) b := by
      rw [← map_div₀, IsScalarTower.algebraMap_apply C C[X] (RatFunc C) (c / b)]; rfl
    have hb' : algebraMap C (RatFunc C) b ≠ 0 := by simpa using hb
    rw [_root_.map_sub, RatFunc.algebraMap_X, hcb, _root_.map_neg]
    field_simp
    ring
  rw [this, map_mul, gaussRat_C, gaussRat_X_sub_C, nnnorm_neg, mul_max_of_nonneg _ _ zero_le,
    nnnorm_div, mul_div_cancel₀ _ (by simpa using hb)]

variable [IsAlgClosed C]

/-- **The inversion exchanges the Gauss points `w_{0,s}` and `w_{0,|c|/s}`.** -/
theorem gaussRat_inv (s : ℝ≥0ˣ) (φ : RatFunc C) : w s (inv hc0 φ) = w (invRad hc0 s) φ := by
  have h := valuation_ratFunc_ext_of_linear (w₁ := (w s).comap (inv hc0).toRingHom)
    (w₂ := w (invRad hc0 s)) (fun b ↦ ?_) (fun b ↦ ?_)
  · exact congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v φ) h
  · change w s (inv hc0 (algebraMap C (RatFunc C) b)) = w (invRad hc0 s) (algebraMap C _ b)
    rw [AlgEquiv.commutes, gaussRat_C, gaussRat_C]
  · change w s (inv hc0 (algebraMap C[X] (RatFunc C) (X - Polynomial.C b))) = _
    have hb : algebraMap C[X] (RatFunc C) (Polynomial.C b) = algebraMap C (RatFunc C) b := by
      rw [IsScalarTower.algebraMap_apply C C[X] (RatFunc C)]; rfl
    rw [gaussRat_X_sub_C, _root_.map_sub, RatFunc.algebraMap_X, hb, _root_.map_sub,
      AlgEquiv.commutes, inv_apply, invHom_X, coe_invRad]
    have hX : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
    have : algebraMap C (RatFunc C) c / RatFunc.X - algebraMap C (RatFunc C) b =
        (algebraMap C (RatFunc C) c - algebraMap C (RatFunc C) b * RatFunc.X) / RatFunc.X := by
      field_simp
    rw [this, map_div₀, gaussRat_C_sub_mul_X, AnnulusUnit.gaussRat_X]
    rw [← max_div_div_right zero_le, mul_div_cancel_right₀ _ (by simp)]
    exact max_comm _ _

/-! ### The node chart is stable under the inversion -/

omit [IsAlgClosed C] in
lemma inv_mem_nodeRing {a : RatFunc C} (ha : a ∈ nodeRing c) : inv hc0 a ∈ nodeRing c := by
  induction ha using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨b, hb, rfl⟩ | rfl | rfl
    · refine baseRing_le_nodeChart ⟨b, hb, ?_⟩
      change algebraMap C (RatFunc C) b = inv hc0 (algebraMap C (RatFunc C) b)
      rw [AlgEquiv.commutes]
    · rw [inv_apply, invHom_X]
      exact div_mem_nodeChart (v := NormedField.valuation (K := C))
    · rw [map_div₀, AlgEquiv.commutes, inv_apply, invHom_X]
      have hc : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc0
      rw [div_div_cancel₀ hc]
      exact self_mem_nodeChart (v := NormedField.valuation (K := C))
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [_root_.map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/-- The inversion restricted to the node chart. -/
noncomputable def invNode : nodeRing c →+* nodeRing c :=
  ((inv hc0).toRingHom.restrict (nodeRing c) (nodeRing c) fun _ ha ↦ inv_mem_nodeRing hc0 ha)

omit [IsAlgClosed C] in
lemma coe_invNode (a : nodeRing c) : (invNode hc0 a : RatFunc C) = inv hc0 a := rfl

omit [IsAlgClosed C] [IsUltrametricDist C] in
lemma invRad_mem_segment {s : ℝ≥0ˣ} (hs : s ∈ segment c) : invRad hc0 s ∈ segment c := by
  obtain ⟨h1, h2⟩ := hs
  have hc' : (0 : ℝ≥0) < ‖c‖₊ := by simpa using hc0
  have hs0 : (0 : ℝ≥0) < (s : ℝ≥0) := by simp
  refine ⟨?_, ?_⟩ <;> rw [coe_invRad]
  · rw [lt_div_iff₀ hs0]
    calc ‖c‖₊ * s < ‖c‖₊ * 1 := mul_lt_mul_of_pos_left h2 hc'
      _ = ‖c‖₊ := mul_one _
  · rw [div_lt_one hs0]
    exact h1

/-! ### The twisted extension -/

section Twist

variable (c) in
/-- `F'` with its `C(x)`-algebra structure twisted by the inversion `x ↦ c/x`: the inner
vertex of the annulus becomes the outer one. -/
def Inv (_hc0 : c ≠ 0) (F' : Type*) : Type _ := F'

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F']

instance : Field (Inv c hc0 F') := inferInstanceAs (Field F')

noncomputable instance : Algebra (RatFunc C) (Inv c hc0 F') :=
  ((algebraMap (RatFunc C) F').comp (inv hc0).toRingHom).toAlgebra

variable [Algebra C F'] [IsScalarTower C (RatFunc C) F']

instance : Algebra C (Inv c hc0 F') := inferInstanceAs (Algebra C F')

/-- The identity `F' → Inv c F'`. -/
noncomputable def toInv : F' ≃+* Inv c hc0 F' := RingEquiv.refl F'

omit [IsUltrametricDist C] in
omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma algebraMap_inv_apply (φ : RatFunc C) :
    algebraMap (RatFunc C) (Inv c hc0 F') φ = toInv hc0 (algebraMap (RatFunc C) F' (inv hc0 φ)) :=
  rfl

instance : IsScalarTower C (RatFunc C) (Inv c hc0 F') :=
  IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [algebraMap_inv_apply, AlgEquiv.commutes, ← IsScalarTower.algebraMap_apply]
    rfl

omit [IsUltrametricDist C] in
omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma finrank_inv : Module.finrank (RatFunc C) (Inv c hc0 F') = Module.finrank (RatFunc C) F' :=
  (Algebra.finrank_eq_of_equiv_equiv (inv hc0).toRingEquiv (toInv hc0) (by
    ext φ
    change algebraMap (RatFunc C) F' (inv hc0 (inv hc0 φ)) = _
    rw [inv_inv_apply]; rfl)).symm

instance [FiniteDimensional (RatFunc C) F'] : FiniteDimensional (RatFunc C) (Inv c hc0 F') :=
  Module.finite_of_finrank_pos (by rw [finrank_inv]; exact Module.finrank_pos)

/-- Extensions of `w_{0,s}` to `F'` are the extensions of `w_{0,|c|/s}` to the twist. -/
noncomputable def extInv (s : ℝ≥0ˣ) :
    GaussExtension (0 : C) s F' ≃ GaussExtension (0 : C) (invRad hc0 s) (Inv c hc0 F') where
  toFun v := ⟨v.1.comap (toInv hc0).symm.toRingHom, Valuation.ext fun φ ↦ by
    rw [comap_apply, comap_apply, algebraMap_inv_apply]
    change v.1 ((toInv hc0).symm (toInv hc0 (algebraMap (RatFunc C) F' (inv hc0 φ)))) = _
    rw [RingEquiv.symm_apply_apply, ← comap_apply, v.2, gaussRat_inv]⟩
  invFun v := ⟨v.1.comap (toInv hc0).toRingHom, Valuation.ext fun φ ↦ by
    rw [comap_apply, comap_apply]
    have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u (inv hc0 φ)) v.2
    simp only [comap_apply, algebraMap_inv_apply, inv_inv_apply] at this
    change v.1 (toInv hc0 (algebraMap (RatFunc C) F' φ)) = _
    rw [this, ← gaussRat_inv hc0 s, inv_inv_apply]⟩
  left_inv v := rfl
  right_inv v := rfl

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma ramificationIdx_extInv {s : ℝ≥0ˣ} (v : GaussExtension (0 : C) s F') :
    ramificationIdx (RatFunc C) (extInv hc0 s v).1 = ramificationIdx (RatFunc C) v.1 := by
  have h1 : valueGroup (extInv hc0 s v).1 = valueGroup v.1 := by
    ext g
    simp only [mem_valueGroup_iff]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨(toInv hc0).symm x, hx⟩, fun ⟨x, hx⟩ ↦ ⟨toInv hc0 x, by
      change v.1 ((toInv hc0).symm (toInv hc0 x)) = g
      rw [RingEquiv.symm_apply_apply, hx]⟩⟩
  have h2 : valueGroup ((extInv hc0 s v).1.comap (algebraMap (RatFunc C) (Inv c hc0 F'))) =
      valueGroup (v.1.comap (algebraMap (RatFunc C) F')) := by
    ext g
    simp only [mem_valueGroup_iff, comap_apply]
    constructor
    · rintro ⟨x, hx⟩
      refine ⟨inv hc0 x, ?_⟩
      rw [← hx, algebraMap_inv_apply]
      change _ = v.1 ((toInv hc0).symm (toInv hc0 _))
      rw [RingEquiv.symm_apply_apply]
      rfl
    · rintro ⟨x, hx⟩
      refine ⟨inv hc0 x, ?_⟩
      rw [← hx, algebraMap_inv_apply, inv_inv_apply]
      change v.1 ((toInv hc0).symm (toInv hc0 _)) = _
      rw [RingEquiv.symm_apply_apply]
      rfl
  rw [ramificationIdx, ramificationIdx, h1, h2]

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma inertiaDeg_extInv {s : ℝ≥0ˣ} (v : GaussExtension (0 : C) s F') :
    inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 (invRad hc0 s)) (extInv hc0 s v).1 =
      inertiaDeg (gaussRat (NormedField.valuation (K := C)) 0 s) v.1 := by
  let e₁ : (w (invRad hc0 s)).valuationSubring ≃+* (w s).valuationSubring :=
    { toFun := fun x ↦ ⟨inv hc0 x, by
        rw [mem_valuationSubring_iff, gaussRat_inv]; exact x.2⟩
      invFun := fun y ↦ ⟨inv hc0 y, by
        rw [mem_valuationSubring_iff, ← gaussRat_inv, inv_inv_apply]; exact y.2⟩
      left_inv := fun x ↦ Subtype.ext (inv_inv_apply hc0 x)
      right_inv := fun y ↦ Subtype.ext (inv_inv_apply hc0 y)
      map_mul' := fun x y ↦ Subtype.ext (map_mul _ _ _)
      map_add' := fun x y ↦ Subtype.ext (map_add _ _ _) }
  let e₂ : (extInv hc0 s v).1.valuationSubring ≃+* v.1.valuationSubring :=
    { toFun := fun x ↦ ⟨(toInv hc0).symm x.1, x.2⟩
      invFun := fun y ↦ ⟨toInv hc0 y.1, y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine Algebra.finrank_eq_of_equiv_equiv (IsLocalRing.ResidueField.mapEquiv e₁)
    (IsLocalRing.ResidueField.mapEquiv e₂) ?_
  ext r
  obtain ⟨x, rfl⟩ := residue_surjective r
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap,
    HasExtension.algebraMap_residue_eq_residue_algebraMap,
    IsLocalRing.ResidueField.map_residue]
  rfl

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma isIntegral_toInv_iff (y : F') :
    IsIntegral (nodeRing c) (toInv hc0 y) ↔ IsIntegral (nodeRing c) y := by
  constructor
  · intro h
    have := IsIntegral.map_of_comp_eq (invNode hc0) (toInv hc0).symm.toRingHom
      (by ext a; change algebraMap (RatFunc C) F' (inv hc0 a) = _; rfl) h
    simpa using this
  · intro h
    exact IsIntegral.map_of_comp_eq (invNode hc0) (toInv hc0).toRingHom
      (by
        ext a
        change toInv hc0 (algebraMap (RatFunc C) F' (inv hc0 (inv hc0 a))) = _
        rw [inv_inv_apply]; rfl) h

/-- The integral closures of the node chart in `F'` and in its twist coincide. -/
noncomputable def rintEquiv : Rint c F' ≃+* Rint c (Inv c hc0 F') where
  toFun y := ⟨toInv hc0 y.1, (isIntegral_toInv_iff hc0 y.1).2 y.2⟩
  invFun y := ⟨(toInv hc0).symm y.1, (isIntegral_toInv_iff hc0 ((toInv hc0).symm y.1)).1
    (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
lemma center_extInv {s : ℝ≥0ˣ} (hs : s ∈ segment c) (v : GaussExtension (0 : C) s F') :
    center hs v = (center (invRad_mem_segment hc0 hs) (extInv hc0 s v)).comap
      (rintEquiv hc0).toRingHom := by
  ext y
  rw [Ideal.mem_comap, mem_center_iff, mem_center_iff]
  rfl

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [FiniteDimensional (RatFunc C) F'] [Algebra.IsSeparable (RatFunc C) F']

instance : Algebra.IsSeparable (RatFunc C) (Inv c hc0 F') :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
omit [CharZero C] [FiniteDimensional (RatFunc C) F'] [Algebra.IsSeparable (RatFunc C) F'] in
/-- The tube degree is invariant under the twist (`s ↦ |c|/s`). -/
theorem tubeDegree_inv {s : ℝ≥0ˣ} (hs : s ∈ segment c) [Fintype (GaussExtension (0 : C) s F')]
    (P' : Ideal (Rint c F')) :
    letI : Fintype (GaussExtension (0 : C) (invRad hc0 s) (Inv c hc0 F')) :=
      Fintype.ofEquiv _ (extInv hc0 s)
    tubeDegree hs P' = tubeDegree (invRad_mem_segment hc0 hs)
      (P'.comap (rintEquiv hc0).symm.toRingHom) := by
  classical
  letI : Fintype (GaussExtension (0 : C) (invRad hc0 s) (Inv c hc0 F')) :=
    Fintype.ofEquiv _ (extInv hc0 s)
  rw [tubeDegree, tubeDegree, Finset.sum_filter, Finset.sum_filter]
  refine Fintype.sum_equiv (extInv hc0 s) _ _ fun v ↦ ?_
  rw [ramificationIdx_extInv hc0 v, inertiaDeg_extInv hc0 v, center_extInv hc0 hs v]
  set X := center (invRad_mem_segment hc0 hs) (extInv hc0 s v)
  have hcond : Ideal.comap (rintEquiv hc0).toRingHom X = P' ↔
      X = Ideal.comap (rintEquiv hc0).symm.toRingHom P' := by
    constructor
    · intro h
      ext y
      rw [Ideal.mem_comap, ← h, Ideal.mem_comap]
      change _ ↔ (rintEquiv hc0) ((rintEquiv hc0).symm y) ∈ X
      rw [RingEquiv.apply_symm_apply]
    · intro h
      ext y
      rw [Ideal.mem_comap, h, Ideal.mem_comap]
      change (rintEquiv hc0).symm ((rintEquiv hc0) y) ∈ P' ↔ _
      rw [RingEquiv.symm_apply_apply]
  by_cases h : X = Ideal.comap (rintEquiv hc0).symm.toRingHom P'
  · rw [if_pos (hcond.2 h), if_pos h]
  · rw [if_neg (mt hcond.1 h), if_neg h]

omit [Algebra.IsSeparable (RatFunc C) F'] in
include hp hp1 in
/-- **Matching at the inner vertex (S6).** The tube degree of a maximal ideal `P'` of `R'` over
the node equals the vertex degree, for the twist `x ↦ c/x`, of the corresponding ideal: the sum
of `ord_Q (c/x)‾` over the branches of the inner component (zeros of the residue of `c/x` on the
residue curves of `w_{0,|c|}`) through `P'`. -/
theorem tubeDegree_eq_vertexDegree_inv (hc : ‖c‖ < 1) {s : ℝ≥0ˣ} (hs : s ∈ segment c) {cs : C}
    (hcs : NormedField.valuation cs = (s : ℝ≥0)) [Fintype (GaussExtension (0 : C) s F')]
    [Fintype (Ext C (Inv c hc0 F'))] (P' : Ideal (Rint c F')) [P'.IsMaximal] :
    tubeDegree hs P' =
      vertexDegree (F' := Inv c hc0 F') hc (P'.comap (rintEquiv hc0).symm.toRingHom) := by
  letI : Fintype (GaussExtension (0 : C) (invRad hc0 s) (Inv c hc0 F')) :=
    Fintype.ofEquiv _ (extInv hc0 s)
  haveI : (P'.comap (rintEquiv hc0).symm.toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ (rintEquiv hc0).symm.surjective
  rw [tubeDegree_inv hc0 hs P']
  exact tubeDegree_eq_vertexDegree hp hp1 hc hc0 (invRad_mem_segment hc0 hs) (cs := c / cs)
    (by rw [NormedField.valuation_apply, nnnorm_div, coe_invRad, ← hcs,
      NormedField.valuation_apply]) _

end Twist

end Inversion

end GaussTube

end SemistableReduction
