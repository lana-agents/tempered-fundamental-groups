/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DiscBridge
import TemperedFundamentalGroups.SemistableReduction.NodeUpwardMain
import TemperedFundamentalGroups.SemistableReduction.InvSwap

/-!
# Points over the node and the reduced chart of the two-vertex model

Blueprint §9.12, O12 / R5. Let `0 < |c| < 1`, `R' = Rint c F` the integral closure of the node
chart `O_C[x, c/x]` in `F` and `Λ_T = redRing (TwoV c F) t ⊆ Π_{w'} κ(w')` the reduced chart of
the two-vertex model at `t = x + c/x` (`LocalFormula`). The extensions of the Gauss point of `t`
are the outer extensions `ιU v` (`v ∣ w_{0,1}`) and the inner ones `ιI w₂` (`w₂` an extension of
`w_{0,1}` to the inversion `Inv c F`, i.e. of `w_{0,|c|}`).

* `R'` and `intRing (TwoV c F) t` coincide (`mem_rint_iff`); the reduction `redT : R' → Λ_T` is
  surjective, and its kernel lies in every point over the node;
* points of `R'` over the node correspond to the closed points of `Λ_T` containing `t̄`;
* outer (inner) branches of `P'` correspond to the branches of `redT(P')` on outer (inner)
  components;
* **`isNodeODP_iff`**: `P'` is an ordinary double point iff its image has exactly one outer and one
  inner branch and `δ = 1` at every jet order.
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal

namespace SemistableReduction

namespace NodeBridge

open GaussFibre TwoVertex TwoVertexCharts AffineTwist ChartLocal DeltaCount GaussTube
  FundamentalInequality GaussStability

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] {c : C} (hc0 : c ≠ 0) (hc1 : ‖c‖ < 1)

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

/-! ### The node chart -/

section Node

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma X_mem_tubeIdeal : (⟨RatFunc.X, X_mem_nodeRing c⟩ : nodeRing c) ∈ tubeIdeal c :=
  fun s hs ↦ by
    change gaussRat ν 0 s RatFunc.X < 1
    rw [gaussRat_X]; exact hs.2

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma divX_mem_tubeIdeal :
    (⟨_, div_X_mem_nodeRing c⟩ : nodeRing c) ∈ tubeIdeal c := fun s hs ↦ by
  change gaussRat ν 0 s (algebraMap C (RatFunc C) c / RatFunc.X) < 1
  rw [map_div₀, gaussRat_C, gaussRat_X]
  exact (div_lt_one (by simp)).2 hs.1

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
/-- Every element of the node chart is `b + x f + (c/x) g` with `|b| ≤ 1`. -/
theorem exists_decomp {a : RatFunc C} (ha : a ∈ nodeRing c) :
    ∃ b : C, ‖b‖ ≤ 1 ∧ ∃ f ∈ nodeRing c, ∃ g ∈ nodeRing c,
      a = algebraMap C (RatFunc C) b + RatFunc.X * f +
        (algebraMap C (RatFunc C) c / RatFunc.X) * g := by
  have hX := X_mem_nodeRing c
  have hv := div_X_mem_nodeRing c
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨b, hb, rfl⟩ | rfl | rfl
    · refine ⟨b, ?_, 0, zero_mem _, 0, zero_mem _, by simp⟩
      have : NormedField.valuation b ≤ 1 := hb
      rw [NormedField.valuation_apply] at this
      exact_mod_cast this
    · exact ⟨0, by simp, 1, one_mem _, 0, zero_mem _, by simp⟩
    · exact ⟨0, by simp, 0, zero_mem _, 1, one_mem _, by simp⟩
  | zero => exact ⟨0, by simp, 0, zero_mem _, 0, zero_mem _, by simp⟩
  | one => exact ⟨1, by simp, 0, zero_mem _, 0, zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb, f, hf, g, hg, rfl⟩ := hx
    obtain ⟨b', hb', f', hf', g', hg', rfl⟩ := hy
    refine ⟨b + b', (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hb hb'),
      f + f', add_mem hf hf', g + g', add_mem hg hg', ?_⟩
    rw [map_add]; ring
  | neg x _ hx =>
    obtain ⟨b, hb, f, hf, g, hg, rfl⟩ := hx
    refine ⟨-b, by simpa using hb, -f, neg_mem hf, -g, neg_mem hg, ?_⟩
    rw [map_neg]; ring
  | mul x y hx' hy' hx hy =>
    obtain ⟨b, hb, f, hf, g, hg, rfl⟩ := hx
    obtain ⟨b', hb', f', hf', g', hg', rfl⟩ := hy
    have hbN : algebraMap C (RatFunc C) b ∈ nodeRing c := algebraMap_mem_nodeRing hb
    refine ⟨b * b', by rw [norm_mul]; exact mul_le_one₀ hb (norm_nonneg _) hb',
      algebraMap C (RatFunc C) b * f' + f * (algebraMap C (RatFunc C) b' + RatFunc.X * f' +
        (algebraMap C (RatFunc C) c / RatFunc.X) * g'),
      add_mem (mul_mem hbN hf') (mul_mem hf hy'),
      algebraMap C (RatFunc C) b * g' + g * (algebraMap C (RatFunc C) b' + RatFunc.X * f' +
        (algebraMap C (RatFunc C) c / RatFunc.X) * g'),
      add_mem (mul_mem hbN hg') (mul_mem hg hy'), ?_⟩
    rw [map_mul]; ring

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]
  [IsUltrametricDist C] in
include hc0 hc1 in
/-- The open segment `|c| < s < 1` is nonempty. -/
lemma exists_mem_segment : ∃ s : ℝ≥0ˣ, s ∈ segment c := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have hc0' : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hr2 : ‖r‖ ^ 2 = ‖c‖ := by rw [← norm_pow, hr]
  have hr0 : 0 < ‖r‖ := by nlinarith [norm_nonneg r]
  have hr1 : ‖r‖ < 1 := by nlinarith [norm_nonneg r]
  have hrc : ‖c‖ < ‖r‖ := by nlinarith [norm_nonneg r]
  exact ⟨Units.mk0 ‖r‖₊ (by simpa using hr0.ne'),
    show ‖c‖₊ < ‖r‖₊ by rw [← NNReal.coe_lt_coe]; simpa using hrc,
    show ‖r‖₊ < 1 by rw [← NNReal.coe_lt_coe]; simpa using hr1⟩

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] in
include hc0 hc1 in
/-- The constant of an element of the node ideal is small. -/
lemma norm_lt_of_mem_tubeIdeal {a : nodeRing c} (ha : a ∈ tubeIdeal c) {b : C}
    {f g : RatFunc C} (hf : f ∈ nodeRing c) (hg : g ∈ nodeRing c)
    (h : (a : RatFunc C) = algebraMap C (RatFunc C) b + RatFunc.X * f +
      (algebraMap C (RatFunc C) c / RatFunc.X) * g) : ‖b‖ < 1 := by
  have he : algebraMap C (RatFunc C) b = (a : RatFunc C) - RatFunc.X * f -
      (algebraMap C (RatFunc C) c / RatFunc.X) * g := by rw [h]; ring
  set a' : nodeRing c := a - ⟨RatFunc.X, X_mem_nodeRing c⟩ * ⟨f, hf⟩ -
    ⟨_, div_X_mem_nodeRing c⟩ * ⟨g, hg⟩
  have ha' : (a' : RatFunc C) = algebraMap C (RatFunc C) b := by rw [he]; rfl
  have hmem : a' ∈ tubeIdeal c :=
    sub_mem (sub_mem ha (Ideal.mul_mem_right _ _ (X_mem_tubeIdeal (c := c))))
      (Ideal.mul_mem_right _ _ (divX_mem_tubeIdeal (c := c)))
  obtain ⟨σ, hσ⟩ := exists_mem_segment hc0 hc1
  have := hmem σ hσ
  rw [ha', gaussRat_C] at this
  exact_mod_cast this

end Node

/-! ### The inner extensions -/

section Inner

omit [IsAlgClosed C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
omit [IsUltrametricDist C] in
lemma invRad_one_eq : invRad hc0 1 = rc hc0 := by
  ext
  simp [coe_invRad]

/-- An extension of `w_{0,1}` to `Inv c F`, as an extension of `w_{0,|c|}` to `F`. -/
noncomputable def innerExt (w₂ : Ext C (Inv c hc0 F)) : GaussExtension (0 : C) (rc hc0) F :=
  ⟨w₂.1.comap (toInv hc0).toRingHom, (comap_toInv_eq hc0 w₂).trans (by rw [invRad_one_eq])⟩

/-- Inner extensions of the Gauss point of `t`. -/
noncomputable def ιI (w₂ : Ext C (Inv c hc0 F)) : Ext C (TwoV c F) :=
  extD hc0 hc1 (innerExt hc0 w₂)

/-- The identity `Inv c F → TwoV c F`. -/
noncomputable def φI : Inv c hc0 F ≃+* TwoV c F := (toInv hc0).symm.trans (toTwoV c)

omit [FiniteDimensional (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιI_apply (w₂ : Ext C (Inv c hc0 F)) (y : Inv c hc0 F) :
    (ιI hc0 hc1 w₂).1 (φI hc0 y) = w₂.1 y := rfl

omit [FiniteDimensional (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιI_apply' (w₂ : Ext C (Inv c hc0 F)) (y : F) :
    (ιI hc0 hc1 w₂).1 (toTwoV c y) = w₂.1 (toInv hc0 y) := rfl

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [Algebra (RatFunc C) F]
  [IsScalarTower C (RatFunc C) F] in
lemma φI_algebraMap_C (b : C) :
    φI hc0 (algebraMap C (Inv c hc0 F) b) = algebraMap C (TwoV c F) b := rfl

omit [FiniteDimensional (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
/-- Every extension of the Gauss point of `t` is outer or inner. -/
lemma ext_cases_I (w' : Ext C (TwoV c F)) :
    (∃ v, ιU hc0 hc1 v = w') ∨ ∃ w₂, ιI hc0 hc1 w₂ = w' := by
  rcases ext_cases hc0 hc1 w' with h | h
  · exact Or.inl ⟨⟨_, h⟩, rfl⟩
  · refine Or.inr ⟨toInvExt hc0 ⟨_, h.trans (by rw [invRad_one_eq])⟩, ?_⟩
    exact Subtype.ext (Valuation.ext fun _ ↦ rfl)

omit [FiniteDimensional (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιU_ne_ιI (v : Ext C F) (w₂ : Ext C (Inv c hc0 F)) : ιU hc0 hc1 v ≠ ιI hc0 hc1 w₂ := by
  intro h
  have h1 := valuation_ιU_x hc0 hc1 v
  have h2 : (ιI hc0 hc1 w₂).1 (toTwoV c (xF C F)) = ‖c‖₊ := by
    change (innerExt hc0 w₂).1 (xF C F) = ‖c‖₊
    have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u RatFunc.X) (innerExt hc0 w₂).2
    simp only [Valuation.comap_apply] at this
    rw [show xF C F = algebraMap (RatFunc C) F RatFunc.X from rfl, this, gaussRat_X]
    rfl
  rw [h, h2] at h1
  have : ‖c‖₊ < 1 := by exact_mod_cast hc1
  exact this.ne h1

omit [FiniteDimensional (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F] in
lemma ιI_injective : Function.Injective (ιI (F := F) hc0 hc1) := fun w₁ w₂ h ↦
  Subtype.ext (Valuation.ext fun y ↦ by
    rw [← ιI_apply hc0 hc1 w₁, ← ιI_apply hc0 hc1 w₂, h])

end Inner

/-! ### `R'` inside the two-vertex model -/

section Rint

lemma toTwoV_mem_iC {a : RatFunc C} (ha : a ∈ nodeRing c) :
    toTwoV c (algebraMap (RatFunc C) F a) ∈
      integralClosure (Algebra.adjoin C {xF C (TwoV c F)}) (TwoV c F) := by
  induction ha using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨b, hb, rfl⟩ | rfl | rfl
    · rw [← IsScalarTower.algebraMap_apply, toTwoV_algebraMap_C]
      exact isIntegral_of_mem (Subalgebra.algebraMap_mem _ b)
    · exact isIntegral_xT
    · have e : toTwoV c (algebraMap (RatFunc C) F (algebraMap C (RatFunc C) c / RatFunc.X)) =
          xF C (TwoV c F) - toTwoV c (xF C F) := by
        rw [xF_twoV', ← map_sub, add_sub_cancel_left, map_div₀,
          ← IsScalarTower.algebraMap_apply]
      rw [e]
      exact (isIntegral_of_mem (Algebra.self_mem_adjoin_singleton C _)).sub isIntegral_xT
  | zero => rw [map_zero, map_zero]; exact zero_mem _
  | one => rw [map_one, map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add, map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, map_neg]; exact neg_mem hx
  | mul x y _ _ hx hy => rw [map_mul, map_mul]; exact mul_mem hx hy

/-- Elements of `R'` are integral over `C[t]`. -/
lemma isIntegral_T (y : Rint c F) :
    IsIntegral (Algebra.adjoin C {xF C (TwoV c F)}) (toTwoV c (y : F)) := by
  set A := Algebra.adjoin C {xF C (TwoV c F)}
  let φ : nodeRing c →+* integralClosure A (TwoV c F) :=
    { toFun := fun a ↦ ⟨toTwoV c (algebraMap (RatFunc C) F a), toTwoV_mem_iC a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b ↦ Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b ↦ Subtype.ext (by simp) }
  have h : IsIntegral (integralClosure A (TwoV c F)) (toTwoV c (y : F)) :=
    IsIntegral.map_of_comp_eq φ (toTwoV c).toRingHom (RingHom.ext fun _ ↦ rfl) y.2
  exact isIntegral_trans _ h

include hc0 hc1 in
lemma val_le_one_T (y : Rint c F) (w' : Ext C (TwoV c F)) : w'.1 (toTwoV c (y : F)) ≤ 1 := by
  rcases ext_cases_I hc0 hc1 w' with ⟨v, rfl⟩ | ⟨w₂, rfl⟩
  · rw [ιU_apply]
    exact valuation_le_one_R hc1 v y
  · rw [ιI_apply']
    exact valuation_le_one_R hc1 w₂ (rintEquiv hc0 y)

variable [Fintype (Ext C (TwoV c F))]

include hc0 hc1 in
lemma mem_intRing_T (y : Rint c F) :
    toTwoV c (y : F) ∈ intRing C (TwoV c F) (xF C (TwoV c F)) :=
  ⟨isIntegral_T y, gnorm_le_iff.2 (val_le_one_T hc0 hc1 y)⟩

/-- The reduction of `R'` at an extension of the Gauss point of `t`. -/
noncomputable def redW (w' : Ext C (TwoV c F)) :
    Rint c F →+* ResidueField w'.1.valuationSubring where
  toFun y := red C (toTwoV c (y : F)) w'
  map_one' := by simp [red_one]
  map_mul' y z := by
    simp only [Subalgebra.coe_mul, map_mul]
    exact red_mul (val_le_one_T hc0 hc1 y w') (val_le_one_T hc0 hc1 z w')
  map_zero' := by simp [red_zero]
  map_add' y z := by
    simp only [Subalgebra.coe_add, map_add]
    exact red_add (val_le_one_T hc0 hc1 y w') (val_le_one_T hc0 hc1 z w')

/-- The reduction `R' → Λ_T`. -/
noncomputable def redT : Rint c F →+* redRing C (TwoV c F) (xF C (TwoV c F)) where
  toFun y := ⟨fun w' ↦ red C (toTwoV c (y : F)) w', red_mem_redRing (mem_intRing_T hc0 hc1 y)⟩
  map_one' := Subtype.ext (funext fun w' ↦ map_one (redW hc0 hc1 w'))
  map_mul' a b := Subtype.ext (funext fun w' ↦ map_mul (redW hc0 hc1 w') a b)
  map_zero' := Subtype.ext (funext fun w' ↦ map_zero (redW hc0 hc1 w'))
  map_add' a b := Subtype.ext (funext fun w' ↦ map_add (redW hc0 hc1 w') a b)

lemma redT_apply (y : Rint c F) (w' : Ext C (TwoV c F)) :
    (redT hc0 hc1 y).1 w' = red C (toTwoV c (y : F)) w' := rfl

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 hc0 hc1 in
/-- **`R' = intRing (TwoV c F) t`**: the maximum principle for the node chart. -/
lemma isIntegral_of_mem_intRing {f : F}
    (hf : toTwoV c f ∈ intRing C (TwoV c F) (xF C (TwoV c F))) : IsIntegral (nodeRing c) f := by
  have hg' : IsIntegral (Algebra.adjoin C {xF C F + algebraMap C F c / xF C F}) f := by
    have := hf.1
    rw [xF_twoV'] at this
    exact this
  have hx0 := GaussFibre.xF_ne_zero (C := C) (F := F)
  obtain ⟨N, hN⟩ := ChartBounds.exists_pow_mul_isIntegral (u := xF C F)
    (S := Algebra.adjoin C {xF C F}) (Algebra.self_mem_adjoin_singleton C _) (by
      have : xF C F * (xF C F + algebraMap C F c / xF C F) =
          xF C F ^ 2 + algebraMap C F c := by field_simp
      rw [this]
      exact add_mem (pow_mem (Algebra.self_mem_adjoin_singleton C _) 2)
        (Subalgebra.algebraMap_mem _ c)) hg'
  refine GaussTube.isIntegral_of_le hp hp1 hc0 hN (fun v ↦ ?_) (fun v ↦ ?_)
  · rw [← ιU_apply hc0 hc1 v]
    exact (le_gnorm _ _).trans hf.2
  · have : (extD hc0 hc1 ⟨v.1, v.2.trans (by rw [invRad_one_eq])⟩).1 (toTwoV c f) = v.1 f := rfl
    rw [← this]
    exact (le_gnorm _ _).trans hf.2

include hp hp1 in
lemma redT_surjective : Function.Surjective (redT (F := F) hc0 hc1) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨(toTwoV c).symm f, isIntegral_of_mem_intRing hc0 hc1 hp hp1 hf⟩, rfl⟩

include hp hp1 in
/-- **The kernel of `R' → Λ_T` lies in every point over the node.** -/
lemma ker_le {P' : Ideal (Rint c F)} [hP'm : P'.IsMaximal]
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F)) = tubeIdeal c) :
    RingHom.ker (redT (F := F) hc0 hc1) ≤ P' := by
  intro y hy
  have hy0 : ∀ w' : Ext C (TwoV c F), w'.1 (toTwoV c (y : F)) < 1 := fun w' ↦ by
    have := congrArg (fun a : redRing C (TwoV c F) (xF C (TwoV c F)) ↦ a.1 w')
      (RingHom.mem_ker.1 hy)
    exact (red_eq_zero_iff (val_le_one_T hc0 hc1 y w')).1 this
  have hp0 : (p : C) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hpn : (0 : ℝ≥0) < ‖(p : C)‖₊ := nnnorm_pos.2 hp0
  have hg : gnorm C (toTwoV c (y : F)) < 1 := (gnorm_lt_iff one_pos).2 hy0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpn hg
  set z : F := algebraMap C F (p : C)⁻¹ * (y : F) ^ n
  have hzT : toTwoV c z ∈ intRing C (TwoV c F) (xF C (TwoV c F)) := by
    refine ⟨?_, gnorm_le_iff.2 fun w' ↦ ?_⟩
    · change IsIntegral _ (algebraMap C (TwoV c F) (p : C)⁻¹ * toTwoV c (y : F) ^ n)
      exact (isIntegral_of_mem (Subalgebra.algebraMap_mem _ _)).mul ((isIntegral_T y).pow n)
    · change w'.1 (algebraMap C (TwoV c F) (p : C)⁻¹ * toTwoV c (y : F) ^ n) ≤ 1
      rw [map_mul, map_pow, valuation_algebraMap_C', nnnorm_inv]
      have h1 : w'.1 (toTwoV c (y : F)) ^ n ≤ gnorm C (toTwoV c (y : F)) ^ n :=
        pow_le_pow_left₀ zero_le (le_gnorm w' _) n
      calc ‖(p : C)‖₊⁻¹ * w'.1 (toTwoV c (y : F)) ^ n ≤ ‖(p : C)‖₊⁻¹ * ‖(p : C)‖₊ :=
            mul_le_mul_right (h1.trans hn.le) _
        _ = 1 := inv_mul_cancel₀ hpn.ne'
  set zR : Rint c F := ⟨z, isIntegral_of_mem_intRing hc0 hc1 hp hp1 hzT⟩
  have hpN : algebraMap C (RatFunc C) (p : C) ∈ nodeRing c := algebraMap_mem_nodeRing hp1.le
  have hpT : (⟨_, hpN⟩ : nodeRing c) ∈ tubeIdeal c := fun s _ ↦ by
    change gaussRat ν 0 s (algebraMap C (RatFunc C) (p : C)) < 1
    rw [gaussRat_C]; exact_mod_cast hp1
  have hpP : algebraMap (nodeRing c) (Rint c F) ⟨_, hpN⟩ ∈ P' := by
    rw [← Ideal.mem_comap, hP']; exact hpT
  have heq : y ^ n = algebraMap (nodeRing c) (Rint c F) ⟨_, hpN⟩ * zR := by
    apply Subtype.ext
    change (y : F) ^ n = algebraMap (RatFunc C) F (algebraMap C (RatFunc C) (p : C)) * z
    rw [← IsScalarTower.algebraMap_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hp0,
      map_one, one_mul]
  have : y ^ n ∈ P' := heq ▸ P'.mul_mem_right _ hpP
  exact hP'm.isPrime.mem_of_pow_mem n this

end Rint

/-! ### Points over the node -/

section Points

variable [Fintype (Ext C (TwoV c F))] [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-- `x` in the node chart. -/
noncomputable abbrev xN : nodeRing c := ⟨RatFunc.X, X_mem_nodeRing c⟩
/-- `c/x` in the node chart. -/
noncomputable abbrev vN : nodeRing c := ⟨_, div_X_mem_nodeRing c⟩

omit [FiniteDimensional (RatFunc C) F] [Fintype (GaussFibre.Ext C (TwoV c F))] [CharZero C] in
lemma toTwoV_xN_add_vN :
    toTwoV c ((algebraMap (nodeRing c) (Rint c F) (xN + vN) : Rint c F) : F) =
      xF C (TwoV c F) := by
  rw [xF_twoV']
  change toTwoV c (algebraMap (RatFunc C) F (RatFunc.X + algebraMap C (RatFunc C) c / RatFunc.X))
    = _
  rw [map_add, map_div₀, ← IsScalarTower.algebraMap_apply]

/-- The element `t̄` of the reduced chart. -/
noncomputable abbrev tbar
    (hΛT : IsChart 𝓀 (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F)) w)
      (redRing C (TwoV c F) (xF C (TwoV c F)))) :
    redRing C (TwoV c F) (xF C (TwoV c F)) := ⟨fun w ↦ red C (xF C (TwoV c F)) w, hΛT.mem⟩

variable (hΛT : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
  (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F)) w) (redRing C (TwoV c F) (xF C (TwoV c F))))

omit [CharZero C] in
lemma redT_t : redT hc0 hc1 (algebraMap (nodeRing c) (Rint c F) (xN + vN)) = tbar hΛT :=
  Subtype.ext (funext fun w' ↦ by rw [redT_apply, toTwoV_xN_add_vN])

omit [IsAlgClosed C] [CharZero C] in
lemma t_mem_tubeIdeal : (xN + vN : nodeRing c) ∈ tubeIdeal c :=
  add_mem (X_mem_tubeIdeal (c := c)) (divX_mem_tubeIdeal (c := c))

section P

variable {P' : Ideal (Rint c F)} [hP'm : P'.IsMaximal]
  (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F)) = tubeIdeal c)
include hP'

include hp hp1 in
lemma comap_map : (P'.map (redT hc0 hc1)).comap (redT hc0 hc1) = P' := by
  rw [Ideal.comap_map_of_surjective _ (redT_surjective hc0 hc1 hp hp1), ← RingHom.ker_eq_comap_bot,
    sup_eq_left]
  exact ker_le hc0 hc1 hp hp1 hP'

include hp hp1 in
lemma map_isMaximal : (P'.map (redT hc0 hc1)).IsMaximal :=
  (Ideal.map_eq_top_or_isMaximal_of_surjective _ (redT_surjective hc0 hc1 hp hp1) hP'm).resolve_left
    fun h ↦ hP'm.ne_top (by rw [← comap_map hc0 hc1 hp hp1 hP', h, Ideal.comap_top])

omit hP'm [CharZero C] in
lemma tbar_mem_map : tbar hΛT ∈ P'.map (redT hc0 hc1) := by
  rw [← redT_t hc0 hc1 hΛT]
  refine Ideal.mem_map_of_mem _ ?_
  rw [← Ideal.mem_comap, hP']
  exact t_mem_tubeIdeal

end P

omit [CharZero C] in
/-- A maximal ideal containing `t̄` pulls back to a point over the node. -/
lemma comap_comap_eq {𝔫 : Ideal (redRing C (TwoV c F) (xF C (TwoV c F)))} [h𝔫 : 𝔫.IsMaximal]
    (ht : tbar hΛT ∈ 𝔫) :
    (𝔫.comap (redT hc0 hc1)).comap (algebraMap (nodeRing c) (Rint c F)) = tubeIdeal c := by
  set ι := algebraMap (nodeRing c) (Rint c F)
  have hxv : redT hc0 hc1 (ι xN) * redT hc0 hc1 (ι vN) = 0 := by
    rw [← map_mul, ← map_mul]
    apply Subtype.ext
    funext w'
    rw [redT_apply]
    change red C (toTwoV c (algebraMap (RatFunc C) F
      (RatFunc.X * (algebraMap C (RatFunc C) c / RatFunc.X)))) w' = 0
    rw [mul_div_cancel₀ _ RatFunc.X_ne_zero, ← IsScalarTower.algebraMap_apply,
      toTwoV_algebraMap_C,
      (red_eq_zero_iff (by rw [valuation_algebraMap_C']; exact_mod_cast hc1.le)).2
        (by rw [valuation_algebraMap_C']; exact_mod_cast hc1)]
  have hsum : redT hc0 hc1 (ι xN) + redT hc0 hc1 (ι vN) ∈ 𝔫 := by
    rw [← map_add, ← map_add, redT_t hc0 hc1 hΛT]; exact ht
  have hx𝔫 : redT hc0 hc1 (ι xN) ∈ 𝔫 ∧ redT hc0 hc1 (ι vN) ∈ 𝔫 := by
    rcases h𝔫.isPrime.mem_or_mem (hxv ▸ 𝔫.zero_mem) with h | h
    · exact ⟨h, by simpa using sub_mem hsum h⟩
    · exact ⟨by simpa using sub_mem hsum h, h⟩
  refine ((tubeIdeal_isMaximal hc1 hc0).eq_of_le ?_ fun a ha ↦ ?_).symm
  · intro h
    apply h𝔫.ne_top
    rw [Ideal.eq_top_iff_one] at h ⊢
    simpa using h
  · obtain ⟨b, hb, f, hf, g, hg, hdec⟩ := exists_decomp a.2
    have hb1 := norm_lt_of_mem_tubeIdeal hc0 hc1 ha hf hg hdec
    have hbN : algebraMap C (RatFunc C) b ∈ nodeRing c := algebraMap_mem_nodeRing hb
    have ha' : ι a = ι ⟨_, hbN⟩ + ι xN * ι ⟨f, hf⟩ + ι vN * ι ⟨g, hg⟩ := by
      rw [← map_mul, ← map_mul, ← map_add, ← map_add]
      congr 1
      exact Subtype.ext hdec
    rw [Ideal.mem_comap, Ideal.mem_comap, ha', map_add, map_add, map_mul, map_mul]
    refine add_mem (add_mem ?_ (Ideal.mul_mem_right _ _ hx𝔫.1)) (Ideal.mul_mem_right _ _ hx𝔫.2)
    convert 𝔫.zero_mem
    apply Subtype.ext
    funext w'
    rw [redT_apply]
    change red C (toTwoV c (algebraMap (RatFunc C) F (algebraMap C (RatFunc C) b))) w' = 0
    rw [← IsScalarTower.algebraMap_apply, toTwoV_algebraMap_C,
      (red_eq_zero_iff (by rw [valuation_algebraMap_C']; exact_mod_cast hb)).2
        (by rw [valuation_algebraMap_C']; exact_mod_cast hb1)]

end Points

end NodeBridge

end SemistableReduction
