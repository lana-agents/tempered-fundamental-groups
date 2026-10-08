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

/-! ### Branches -/

section Branches

variable [Fintype (Ext C (TwoV c F))] [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

omit [Fintype (Ext C (TwoV c F))] [CharZero C] in
/-- Residues along isomorphisms of function fields. -/
lemma res_map {κ κ' : Type*} [Field κ] [Field κ'] [Algebra 𝓀 κ] [Algebra 𝓀 κ']
    [IsCurveFunctionField 𝓀 κ] [IsCurveFunctionField 𝓀 κ'] (e : κ ≃ₐ[𝓀] κ')
    (Q : CurvePlace 𝓀 κ) {a : κ'} (ha : a ∈ (Q.map e).V) : (Q.map e).res a = Q.res (e.symm a) := by
  refine (Q.map e).res_eq_of_valuation_sub_lt_one ?_
  rw [CurvePlace.valuation_map, map_sub, AlgEquiv.commutes]
  exact Q.valuation_sub_res_lt_one ha

/-- The outer components. -/
noncomputable abbrev EU : CompEmb 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
    (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) where
  ι := ιU hc0 hc1
  inj := (extEmb (toTwoV (F' := F) c) toTwoV_algebraMap_C (ιU (F := F) hc0 hc1)
    (ιU_apply hc0 hc1)).inj
  e w := resAlgEquiv (toTwoV (F' := F) c) toTwoV_algebraMap_C (ιU_apply hc0 hc1 w)

/-- The inner components. -/
noncomputable abbrev EI :
    CompEmb 𝓀 (fun w : Ext C (Inv c hc0 F) ↦ ResidueField w.1.valuationSubring)
      (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) where
  ι := ιI hc0 hc1
  inj := ιI_injective hc0 hc1
  e w := resAlgEquiv (φI hc0) (φI_algebraMap_C hc0) (ιI_apply hc0 hc1 w)

omit [Fintype (Ext C (TwoV c F))] [CharZero C] [FiniteDimensional (RatFunc C) F] in
lemma EU_e_red (v : Ext C F) (f : F) :
    (EU hc0 hc1).e v (red C f v) = red C (toTwoV c f) (ιU hc0 hc1 v) :=
  resAlgEquiv_red (toTwoV (F' := F) c) toTwoV_algebraMap_C (ιU_apply hc0 hc1 v) f

omit [Fintype (Ext C (TwoV c F))] [CharZero C] [FiniteDimensional (RatFunc C) F] in
lemma EI_e_red (w₂ : Ext C (Inv c hc0 F)) (f : Inv c hc0 F) :
    (EI hc0 hc1).e w₂ (red C f w₂) = red C (φI hc0 f) (ιI hc0 hc1 w₂) :=
  resAlgEquiv_red (φI hc0) (φI_algebraMap_C hc0) (ιI_apply hc0 hc1 w₂) f

omit [Fintype (Ext C (TwoV c F))] [CharZero C] [FiniteDimensional (RatFunc C) F] in
lemma pmap_U (v : Ext C F) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :
    (EU hc0 hc1).pmap ⟨v, Q⟩ =
      (⟨ιU hc0 hc1 v, Q.map ((EU hc0 hc1).e v)⟩ :
        Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)) := rfl

omit [Fintype (Ext C (TwoV c F))] [CharZero C] [FiniteDimensional (RatFunc C) F] in
lemma pmap_I (w₂ : Ext C (Inv c hc0 F)) (Q : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)) :
    (EI hc0 hc1).pmap ⟨w₂, Q⟩ =
      (⟨ιI hc0 hc1 w₂, Q.map ((EI hc0 hc1).e w₂)⟩ :
        Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)) := rfl

omit [Fintype (Ext C (TwoV c F))] [CharZero C] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] in
lemma val_ιI_x (w₂ : Ext C (Inv c hc0 F)) : (ιI hc0 hc1 w₂).1 (toTwoV c (xF C F)) = ‖c‖₊ := by
  change (innerExt hc0 w₂).1 (xF C F) = ‖c‖₊
  have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u RatFunc.X) (innerExt hc0 w₂).2
  simp only [Valuation.comap_apply] at this
  rw [show xF C F = algebraMap (RatFunc C) F RatFunc.X from rfl, this, gaussRat_X]
  rfl

omit [Fintype (Ext C (TwoV c F))] [CharZero C] [FiniteDimensional (RatFunc C) F] in
/-- `t̄` on an outer component is `x̄`. -/
lemma red_t_U (v : Ext C F) :
    red C (xF C (TwoV c F)) (ιU hc0 hc1 v) = (EU hc0 hc1).e v (red C (xF C F) v) := by
  have h1 : (ιU hc0 hc1 v).1 (toTwoV c (xF C F)) ≤ 1 := (valuation_ιU_x hc0 hc1 v).le
  have h2 : (ιU hc0 hc1 v).1 (toTwoV c (algebraMap C F c / xF C F)) < 1 := by
    rw [ιU_apply, map_div₀, valuation_algebraMap_C', valuation_xF, div_one]
    exact_mod_cast hc1
  rw [EU_e_red, xF_twoV', map_add, red_add h1 h2.le, (red_eq_zero_iff h2.le).2 h2, add_zero]

omit [Fintype (Ext C (TwoV c F))] [CharZero C] [FiniteDimensional (RatFunc C) F] in
/-- `t̄` on an inner component is the residue of `c/x`. -/
lemma red_t_I (w₂ : Ext C (Inv c hc0 F)) :
    red C (xF C (TwoV c F)) (ιI hc0 hc1 w₂) =
      (EI hc0 hc1).e w₂ (red C (xF C (Inv c hc0 F)) w₂) := by
  have h1 : (ιI hc0 hc1 w₂).1 (toTwoV c (xF C F)) < 1 := by
    rw [val_ιI_x]; exact_mod_cast hc1
  have e : φI hc0 (xF C (Inv c hc0 F)) = toTwoV c (algebraMap C F c / xF C F) := by
    rw [GaussTube.xF_inv]
    change toTwoV c (algebraMap (RatFunc C) F (algebraMap C (RatFunc C) c / RatFunc.X)) = _
    rw [map_div₀, ← IsScalarTower.algebraMap_apply]
  have h2 : (ιI hc0 hc1 w₂).1 (toTwoV c (algebraMap C F c / xF C F)) ≤ 1 := by
    rw [← e, ιI_apply]
    exact (valuation_xF w₂).le
  rw [EI_e_red, e, xF_twoV', map_add, red_add h1.le h2, (red_eq_zero_iff h1.le).2 h1,
    zero_add]

variable (hΛT : IsChart (IsLocalRing.ResidueField (HenselComplete.integers C))
  (fun w : Ext C (TwoV c F) ↦ red C (xF C (TwoV c F)) w) (redRing C (TwoV c F) (xF C (TwoV c F))))

omit [Fintype (Ext C (TwoV c F))] [CharZero C] in
lemma hz_U (v : Ext C F) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v)) :
    red C (xF C (TwoV c F)) (ιU hc0 hc1 v) ∈ (Q.map ((EU hc0 hc1).e v)).V := by
  rw [red_t_U]
  exact (CurvePlace.mem_map_V _ _).2 (by
    rw [AlgEquiv.symm_apply_apply]; exact SmoothVertex.xbar_mem_V v hQ)

omit [Fintype (Ext C (TwoV c F))] [CharZero C] in
lemma hz_I (w₂ : Ext C (Inv c hc0 F)) {Q : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂)) :
    red C (xF C (TwoV c F)) (ιI hc0 hc1 w₂) ∈ (Q.map ((EI hc0 hc1).e w₂)).V := by
  rw [red_t_I]
  exact (CurvePlace.mem_map_V _ _).2 (by
    rw [AlgEquiv.symm_apply_apply]; exact SmoothVertex.xbar_mem_V w₂ hQ)

omit [CharZero C] in
/-- The centre of an outer branch, pulled back to `R'`. -/
lemma comap_center_U (v : Ext C F) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v)) :
    (ChartLocal.center hΛT (j := ιU hc0 hc1 v) (Q.map ((EU hc0 hc1).e v))
      (hz_U hc0 hc1 v hQ)).comap (redT hc0 hc1) = placeIdeal hc1 v hQ := by
  ext y
  rw [Ideal.mem_comap, mem_center, redT_apply, ← EU_e_red, CurvePlace.valuation_map_apply,
    mem_placeIdeal_iff, CurvePlace.res_eq_zero_iff Q (red_mem_V hc1 v y hQ)]

omit [CharZero C] in
/-- The centre of an inner branch, pulled back to `R'`. -/
lemma comap_center_I (w₂ : Ext C (Inv c hc0 F))
    {Q : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂)) :
    (ChartLocal.center hΛT (j := ιI hc0 hc1 w₂) (Q.map ((EI hc0 hc1).e w₂))
      (hz_I hc0 hc1 w₂ hQ)).comap (redT hc0 hc1) =
      (placeIdeal hc1 w₂ hQ).comap (rintEquiv hc0).toRingHom := by
  ext y
  rw [Ideal.mem_comap, mem_center, redT_apply, Ideal.mem_comap]
  change (Q.map ((EI hc0 hc1).e w₂)).valuation (red C (φI hc0 (toInv hc0 (y : F)))
    (ιI hc0 hc1 w₂)) < 1 ↔ _
  rw [← EI_e_red, CurvePlace.valuation_map_apply]
  exact (CurvePlace.res_eq_zero_iff Q (red_mem_V hc1 w₂ (rintEquiv hc0 y) hQ)).symm.trans
    (mem_placeIdeal_iff hc1 w₂ hQ _).symm

section P

variable {P' : Ideal (Rint c F)} [hP'm : P'.IsMaximal]
  (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F)) = tubeIdeal c)
include hP'

omit hP'm hP' in
include hp hp1 in
/-- An outer branch of `P'` is a branch of `redT(P')`. -/
lemma mem_brs_U (v : Ext C F) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v)) (h : placeIdeal hc1 v hQ = P') :
    (EU hc0 hc1).pmap ⟨v, Q⟩ ∈ brs hΛT (P'.map (redT hc0 hc1)) := by
  have h2 := (comap_center_U hc0 hc1 hΛT v hQ).trans h
  have h1 := Ideal.map_comap_of_surjective (redT hc0 hc1) (redT_surjective hc0 hc1 hp hp1)
    (ChartLocal.center hΛT (j := ιU hc0 hc1 v) (Q.map ((EU hc0 hc1).e v)) (hz_U hc0 hc1 v hQ))
  rw [h2] at h1
  rw [mem_brs, centerOf_eq hΛT (b := (EU hc0 hc1).pmap ⟨v, Q⟩) (hz_U hc0 hc1 v hQ)]
  exact h1.symm

omit hP'm hP' in
include hp hp1 in
/-- An inner branch of `P'` is a branch of `redT(P')`. -/
lemma mem_brs_I (w₂ : Ext C (Inv c hc0 F)) {Q : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂))
    (h : placeIdeal hc1 w₂ hQ = P'.comap (rintEquiv hc0).symm.toRingHom) :
    (EI hc0 hc1).pmap ⟨w₂, Q⟩ ∈ brs hΛT (P'.map (redT hc0 hc1)) := by
  have h2 : (ChartLocal.center hΛT (j := ιI hc0 hc1 w₂) (Q.map ((EI hc0 hc1).e w₂))
      (hz_I hc0 hc1 w₂ hQ)).comap (redT hc0 hc1) = P' := by
    rw [comap_center_I hc0 hc1 hΛT w₂ hQ, h, Ideal.comap_comap]
    convert Ideal.comap_id P'
    ext y
    exact congrArg Subtype.val ((rintEquiv hc0).symm_apply_apply y)
  have h1 := Ideal.map_comap_of_surjective (redT hc0 hc1) (redT_surjective hc0 hc1 hp hp1)
    (ChartLocal.center hΛT (j := ιI hc0 hc1 w₂) (Q.map ((EI hc0 hc1).e w₂)) (hz_I hc0 hc1 w₂ hQ))
  rw [h2] at h1
  rw [mem_brs, centerOf_eq hΛT (b := (EI hc0 hc1).pmap ⟨w₂, Q⟩) (hz_I hc0 hc1 w₂ hQ)]
  exact h1.symm

include hp hp1 in
/-- **The branches of `redT(P')`**: transported outer branches of `P'` and transported inner
branches of `P'`. -/
lemma brs_cases {b : Branch 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring)}
    (hb : b ∈ brs hΛT (P'.map (redT hc0 hc1))) :
    (∃ (v : Ext C F) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
        (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v)),
        (EU hc0 hc1).pmap ⟨v, Q⟩ = b ∧ placeIdeal hc1 v hQ = P') ∨
      ∃ (w₂ : Ext C (Inv c hc0 F)) (Q : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring))
        (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂)),
        (EI hc0 hc1).pmap ⟨w₂, Q⟩ = b ∧
          placeIdeal hc1 w₂ hQ = P'.comap (rintEquiv hc0).symm.toRingHom := by
  have hne := (map_isMaximal hc0 hc1 hp hp1 hP').ne_top
  have hlt := (mem_iff_of_mem_brs hΛT hne hb (tbar hΛT)).1 (tbar_mem_map hc0 hc1 hΛT hP')
  have hz := mem_V_of_mem_brs hΛT hne hb
  obtain ⟨w', Q'⟩ := b
  rcases ext_cases_I hc0 hc1 w' with ⟨v, rfl⟩ | ⟨w₂, rfl⟩
  · obtain ⟨Q, rfl⟩ : ∃ Q, Q.map ((EU hc0 hc1).e v) = Q' :=
      ⟨Q'.map ((EU hc0 hc1).e v).symm, CurvePlace.map_map_symm _ _⟩
    have hx0 : red C (xF C F) v ≠ 0 := red_xF_ne_zero' v
    have hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v) := by
      refine DiscBridge.mem_zeros_of_lt hx0 ?_
      have := hlt
      change (Q.map ((EU hc0 hc1).e v)).valuation (red C (xF C (TwoV c F)) (ιU hc0 hc1 v)) < 1
        at this
      rwa [red_t_U, CurvePlace.valuation_map_apply] at this
    refine Or.inl ⟨v, Q, hQ, rfl, ?_⟩
    rw [← comap_center_U hc0 hc1 hΛT v hQ, ← comap_map hc0 hc1 hp hp1 hP']
    congr 1
    exact (centerOf_eq hΛT (b := (EU hc0 hc1).pmap ⟨v, Q⟩) (hz_U hc0 hc1 v hQ)).symm.trans hb
  · obtain ⟨Q, rfl⟩ : ∃ Q, Q.map ((EI hc0 hc1).e w₂) = Q' :=
      ⟨Q'.map ((EI hc0 hc1).e w₂).symm, CurvePlace.map_map_symm _ _⟩
    have hx0 : red C (xF C (Inv c hc0 F)) w₂ ≠ 0 := red_xF_ne_zero' w₂
    have hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂) := by
      refine DiscBridge.mem_zeros_of_lt hx0 ?_
      have := hlt
      change (Q.map ((EI hc0 hc1).e w₂)).valuation (red C (xF C (TwoV c F)) (ιI hc0 hc1 w₂)) < 1
        at this
      rwa [red_t_I, CurvePlace.valuation_map_apply] at this
    refine Or.inr ⟨w₂, Q, hQ, rfl, ?_⟩
    have hc : ChartLocal.center hΛT (j := ιI hc0 hc1 w₂) (Q.map ((EI hc0 hc1).e w₂))
        (hz_I hc0 hc1 w₂ hQ) = P'.map (redT hc0 hc1) :=
      (centerOf_eq hΛT (b := (EI hc0 hc1).pmap ⟨w₂, Q⟩) (hz_I hc0 hc1 w₂ hQ)).symm.trans hb
    have h2 := comap_center_I hc0 hc1 hΛT w₂ hQ
    rw [hc, comap_map hc0 hc1 hp hp1 hP'] at h2
    rw [h2, Ideal.comap_comap]
    convert (Ideal.comap_id (placeIdeal hc1 w₂ hQ)).symm
    ext y
    exact congrArg Subtype.val ((rintEquiv hc0).apply_symm_apply y)

omit [CharZero C] hP' in
lemma redT_U (y : Rint c F) (v : Ext C F) :
    (redT hc0 hc1 y).1 (ιU hc0 hc1 v) = (EU hc0 hc1).e v (redHom hc1 v y) :=
  (EU_e_red hc0 hc1 v (y : F)).symm

omit [CharZero C] hP' in
lemma redT_I (y : Rint c F) (w₂ : Ext C (Inv c hc0 F)) :
    (redT hc0 hc1 y).1 (ιI hc0 hc1 w₂) = (EI hc0 hc1).e w₂ (redHomInv hc1 hc0 w₂ y) :=
  (EI_e_red hc0 hc1 w₂ (toInv hc0 (y : F))).symm

include hp hp1 in
/-- Quotients by elements outside `P'` lie in the local ring of `redT(P')`. -/
lemma div_mem_locSet {y s : Rint c F} (hs : s ∉ P') :
    (fun w' ↦ (redT hc0 hc1 y).1 w' / (redT hc0 hc1 s).1 w') ∈
      locSet (P'.map (redT hc0 hc1)) := by
  refine ⟨redT hc0 hc1 (s * s), fun h ↦ ?_, ?_⟩
  · have : s * s ∈ P' := by rw [← comap_map hc0 hc1 hp hp1 hP']; exact h
    exact hs ((hP'm.isPrime.mem_or_mem this).elim id id)
  · have e : (redT hc0 hc1 (s * s)).1 * (fun w' ↦ (redT hc0 hc1 y).1 w' / (redT hc0 hc1 s).1 w') =
        (redT hc0 hc1 (s * y)).1 := by
      funext w'
      change redW hc0 hc1 w' (s * s) * (redW hc0 hc1 w' y / redW hc0 hc1 w' s) =
        redW hc0 hc1 w' (s * y)
      rw [map_mul, map_mul]
      by_cases h : redW hc0 hc1 w' s = 0
      · rw [h]; ring
      · field_simp
    rw [e]
    exact (redT hc0 hc1 (s * y)).2

omit [CharZero C] hP' [Fintype (GaussFibre.Ext C (TwoV c F))] hP'm in
lemma redHom_ne_zero (v : Ext C F) {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v)) (h : placeIdeal hc1 v hQ = P') {s : Rint c F}
    (hs : s ∉ P') : redHom hc1 v s ≠ 0 := fun h0 ↦ hs <| by
  rw [← h, mem_placeIdeal_iff]
  change Q.res (redHom hc1 v s) = 0
  rw [h0, Q.res_zero]

omit [CharZero C] hP' [Fintype (GaussFibre.Ext C (TwoV c F))] hP'm in
lemma redHomInv_ne_zero (w₂ : Ext C (Inv c hc0 F))
    {Q : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring)}
    (hQ : Q ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂))
    (h : placeIdeal hc1 w₂ hQ = P'.comap (rintEquiv hc0).symm.toRingHom) {s : Rint c F}
    (hs : s ∉ P') : redHomInv hc1 hc0 w₂ s ≠ 0 := fun h0 ↦ hs <| by
  have : rintEquiv hc0 s ∈ placeIdeal hc1 w₂ hQ := by
    rw [mem_placeIdeal_iff]
    change Q.res (redHomInv hc1 hc0 w₂ s) = 0
    rw [h0, Q.res_zero]
  rw [h, Ideal.mem_comap] at this
  simpa using this

set_option maxHeartbeats 2000000 in
-- the residue fields of the transported branches are only unfolded at default transparency
include hp hp1 in
/-- **Ordinary double points in the reduced two-vertex chart**: the image of an ordinary double
point has one transported outer branch, one transported inner branch, and `δ ≤ 1` at every jet
order. -/
theorem structure_of_isNodeODP (h : IsNodeODP hc1 hc0 P') :
    ∃ (v₁ : Ext C F) (Q₁ : CurvePlace 𝓀 (ResidueField v₁.1.valuationSubring))
      (hQ₁ : Q₁ ∈ PlaceNorm.zeros 𝓀 (red C (xF C F) v₁))
      (w₂ : Ext C (Inv c hc0 F)) (Q₂ : CurvePlace 𝓀 (ResidueField w₂.1.valuationSubring))
      (hQ₂ : Q₂ ∈ PlaceNorm.zeros 𝓀 (red C (xF C (Inv c hc0 F)) w₂)),
      placeIdeal hc1 v₁ hQ₁ = P' ∧
      placeIdeal hc1 w₂ hQ₂ = P'.comap (rintEquiv hc0).symm.toRingHom ∧
      (∀ b ∈ brs hΛT (P'.map (redT hc0 hc1)),
        b = (EU hc0 hc1).pmap ⟨v₁, Q₁⟩ ∨ b = (EI hc0 hc1).pmap ⟨w₂, Q₂⟩) ∧
      ∀ M, dl 𝓀 (fun w' : Ext C (TwoV c F) ↦ ResidueField w'.1.valuationSubring) hΛT
        (P'.map (redT hc0 hc1)) M ≤ 1 := by
  classical
  obtain ⟨⟨v₁, Q₁, hQ₁⟩, ⟨w₂, Q₂, hQ₂⟩, h₁, h₂, hfp⟩ := h
  have hP₁ : placeIdeal hc1 v₁ hQ₁ = P' := by
    have : (⟨v₁, Q₁, hQ₁⟩ : OuterBranch C F) ∈ outerBranches hc1 P' := by rw [h₁]; rfl
    exact this
  have hP₂ : placeIdeal hc1 w₂ hQ₂ = P'.comap (rintEquiv hc0).symm.toRingHom := by
    have : (⟨w₂, Q₂, hQ₂⟩ : OuterBranch C (Inv c hc0 F)) ∈ innerBranches hc1 hc0 P' := by
      rw [h₂]; rfl
    exact this
  have huniq : ∀ b ∈ brs hΛT (P'.map (redT hc0 hc1)),
      b = (EU hc0 hc1).pmap ⟨v₁, Q₁⟩ ∨ b = (EI hc0 hc1).pmap ⟨w₂, Q₂⟩ := by
    intro b hb
    rcases brs_cases hc0 hc1 hp hp1 hΛT hP' hb with ⟨v, Q, hQ, rfl, hPv⟩ | ⟨w, Q, hQ, rfl, hPw⟩
    · left
      have : (⟨v, Q, hQ⟩ : OuterBranch C F) ∈ outerBranches hc1 P' := hPv
      rw [h₁, Set.mem_singleton_iff] at this
      cases this
      rfl
    · right
      have : (⟨w, Q, hQ⟩ : OuterBranch C (Inv c hc0 F)) ∈ innerBranches hc1 hc0 P' := hPw
      rw [h₂, Set.mem_singleton_iff] at this
      cases this
      rfl
  refine ⟨v₁, Q₁, hQ₁, w₂, Q₂, hQ₂, hP₁, hP₂, huniq, fun M ↦ ?_⟩
  have hU₀ := mem_brs_U hc0 hc1 hp hp1 hΛT v₁ hQ₁ hP₁
  have hI₀ := mem_brs_I hc0 hc1 hp hp1 hΛT w₂ hQ₂ hP₂
  have h𝔫' : (P'.map (redT hc0 hc1)).IsMaximal := map_isMaximal hc0 hc1 hp hp1 hP'
  have hdiv : ∀ {y s : Rint c F}, s ∉ P' →
      (fun w' ↦ (redT hc0 hc1 y).1 w' / (redT hc0 hc1 s).1 w') ∈
        locSet (P'.map (redT hc0 hc1)) := fun hs ↦ div_mem_locSet hc0 hc1 hp hp1 hP' hs
  generalize P'.map (redT hc0 hc1) = 𝔫 at huniq hU₀ hI₀ h𝔫' hdiv ⊢
  haveI h𝔫 : 𝔫.IsMaximal := h𝔫'
  have hne := h𝔫.ne_top
  have hS : ∀ b ∈ brsF hΛT 𝔫,
      b = ⟨ιU hc0 hc1 v₁, Q₁.map ((EU hc0 hc1).e v₁)⟩ ∨
        b = ⟨ιI hc0 hc1 w₂, Q₂.map ((EI hc0 hc1).e w₂)⟩ := fun b hb ↦ by
    have := huniq b ((mem_brsF hΛT hne).1 hb)
    rwa [pmap_U, pmap_I] at this
  have hne12 : ιI hc0 hc1 w₂ ≠ ιU hc0 hc1 v₁ := (ιU_ne_ιI hc0 hc1 v₁ w₂).symm
  haveI := finiteDimensional_regAt_quot hΛT.tr (fun b hb ↦ mem_V_of_mem_brsF hΛT hne hb) M
    (locSpace 𝓀 𝔫)
  obtain ⟨e₁, he₁def⟩ : ∃ e : Π w' : Ext C (TwoV c F), ResidueField w'.1.valuationSubring,
      e = Pi.single (ιU hc0 hc1 v₁) 1 := ⟨_, rfl⟩
  have he₁U : e₁ (ιU hc0 hc1 v₁) = 1 := by rw [he₁def]; exact Pi.single_eq_same _ _
  have he₁I : e₁ (ιI hc0 hc1 w₂) = 0 := by rw [he₁def]; exact Pi.single_eq_of_ne hne12 _
  have he₁ : e₁ ∈ regAt 𝓀 _ (brsF hΛT 𝔫) := fun b hb ↦ by
    rcases hS b hb with rfl | rfl
    · change e₁ (ιU hc0 hc1 v₁) ∈ _
      rw [he₁U]; exact one_mem _
    · change e₁ (ιI hc0 hc1 w₂) ∈ _
      rw [he₁I]; exact zero_mem _
  refine finrank_le_one (Submodule.Quotient.mk ⟨e₁, he₁⟩) fun x ↦ ?_
  obtain ⟨⟨a, ha⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [pmap_U] at hU₀
  rw [pmap_I] at hI₀
  have haU := ha _ ((mem_brsF hΛT hne).2 hU₀)
  have haI := ha _ ((mem_brsF hΛT hne).2 hI₀)
  obtain ⟨l, hl⟩ : ∃ l : 𝓀, l = (Q₁.map ((EU hc0 hc1).e v₁)).res (a (ιU hc0 hc1 v₁)) -
      (Q₂.map ((EI hc0 hc1).e w₂)).res (a (ιI hc0 hc1 w₂)) := ⟨_, rfl⟩
  refine ⟨l, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  -- the element `a' = a - l e₁` has equal residues at the two branches
  obtain ⟨a', ha'def⟩ : ∃ a' : Π w' : Ext C (TwoV c F), ResidueField w'.1.valuationSubring,
      a' = a - l • e₁ := ⟨_, rfl⟩
  have ha'U : a' (ιU hc0 hc1 v₁) = a (ιU hc0 hc1 v₁) - algebraMap 𝓀 _ l := by
    rw [ha'def, Pi.sub_apply, Pi.smul_apply, he₁U, Algebra.smul_def, mul_one]
  have ha'I : a' (ιI hc0 hc1 w₂) = a (ιI hc0 hc1 w₂) := by
    rw [ha'def, Pi.sub_apply, Pi.smul_apply, he₁I, smul_zero, sub_zero]
  have hα₁V : a' (ιU hc0 hc1 v₁) ∈ (Q₁.map ((EU hc0 hc1).e v₁)).V := by
    rw [ha'U]; exact sub_mem haU ((Q₁.map ((EU hc0 hc1).e v₁)).algebraMap_mem l)
  have hα₂V : a' (ιI hc0 hc1 w₂) ∈ (Q₂.map ((EI hc0 hc1).e w₂)).V := by
    rw [ha'I]; exact haI
  have hres : (Q₁.map ((EU hc0 hc1).e v₁)).res (a' (ιU hc0 hc1 v₁)) =
      (Q₂.map ((EI hc0 hc1).e w₂)).res (a' (ιI hc0 hc1 w₂)) := by
    rw [ha'I, ha'U]
    refine (Q₁.map ((EU hc0 hc1).e v₁)).res_eq_of_valuation_sub_lt_one ?_
    have : a (ιU hc0 hc1 v₁) - algebraMap 𝓀 _ l -
        algebraMap 𝓀 _ ((Q₂.map ((EI hc0 hc1).e w₂)).res (a (ιI hc0 hc1 w₂))) =
        a (ιU hc0 hc1 v₁) -
          algebraMap 𝓀 _ ((Q₁.map ((EU hc0 hc1).e v₁)).res (a (ιU hc0 hc1 v₁))) := by
      rw [sub_sub, ← map_add, hl, sub_add_cancel]
    rw [this]
    exact (Q₁.map ((EU hc0 hc1).e v₁)).valuation_sub_res_lt_one haU
  have hα₁ : ((EU hc0 hc1).e v₁).symm (a' (ιU hc0 hc1 v₁)) ∈ Q₁.V :=
    (CurvePlace.mem_map_V _ _).1 hα₁V
  have hα₂ : ((EI hc0 hc1).e w₂).symm (a' (ιI hc0 hc1 w₂)) ∈ Q₂.V :=
    (CurvePlace.mem_map_V _ _).1 hα₂V
  have hres' : Q₁.res (((EU hc0 hc1).e v₁).symm (a' (ιU hc0 hc1 v₁))) =
      Q₂.res (((EI hc0 hc1).e w₂).symm (a' (ιI hc0 hc1 w₂))) := by
    rw [← res_map _ _ hα₁V, hres, res_map _ _ hα₂V]
  obtain ⟨y, s, hsP, hy₁, hy₂⟩ := hfp _ hα₁ _ hα₂ hres'
  have hs₁ := redHom_ne_zero hc1 v₁ hQ₁ hP₁ hsP
  have hs₂ := redHomInv_ne_zero hc0 hc1 w₂ hQ₂ hP₂ hsP
  obtain ⟨o, ho_def⟩ : ∃ o : Π w' : Ext C (TwoV c F), ResidueField w'.1.valuationSubring,
      o = fun w' ↦ (redT hc0 hc1 y).1 w' / (redT hc0 hc1 s).1 w' := ⟨_, rfl⟩
  have hoL : o ∈ locSpace 𝓀 𝔫 := subset_locSpace 𝔫 (ho_def ▸ hdiv hsP)
  have hoU : o (ιU hc0 hc1 v₁) = a' (ιU hc0 hc1 v₁) := by
    rw [ho_def]
    change (redT hc0 hc1 y).1 (ιU hc0 hc1 v₁) / (redT hc0 hc1 s).1 (ιU hc0 hc1 v₁) = _
    rw [redT_U, redT_U, hy₁, map_mul, mul_div_cancel_right₀ _
      ((map_ne_zero ((EU hc0 hc1).e v₁)).2 hs₁)]
    exact AlgEquiv.apply_symm_apply _ _
  have hoI : o (ιI hc0 hc1 w₂) = a' (ιI hc0 hc1 w₂) := by
    rw [ho_def]
    change (redT hc0 hc1 y).1 (ιI hc0 hc1 w₂) / (redT hc0 hc1 s).1 (ιI hc0 hc1 w₂) = _
    rw [redT_I, redT_I, hy₂, map_mul, mul_div_cancel_right₀ _
      ((map_ne_zero ((EI hc0 hc1).e w₂)).2 hs₂)]
    exact AlgEquiv.apply_symm_apply _ _
  have hmem : a' ∈ locSpace 𝓀 𝔫 ⊔ jetKer 𝓀 _ M (brsF hΛT 𝔫) := by
    have : a' = o + (a' - o) := by ring
    rw [this]
    refine add_mem (Submodule.mem_sup_left hoL) (Submodule.mem_sup_right fun b hb ↦ ?_)
    rcases hS b hb with rfl | rfl
    · change (Q₁.map ((EU hc0 hc1).e v₁)).valuation
        (a' (ιU hc0 hc1 v₁) - o (ιU hc0 hc1 v₁)) ≤ _
      rw [hoU, sub_self, map_zero]; exact zero_le
    · change (Q₂.map ((EI hc0 hc1).e w₂)).valuation
        (a' (ιI hc0 hc1 w₂) - o (ιI hc0 hc1 w₂)) ≤ _
      rw [hoI, sub_self, map_zero]; exact zero_le
  have : ((l • (⟨e₁, he₁⟩ : regAt 𝓀 _ (brsF hΛT 𝔫)) - ⟨a, ha⟩ :
      regAt 𝓀 _ (brsF hΛT 𝔫)) : Π w' : Ext C (TwoV c F), ResidueField w'.1.valuationSubring) =
      -a' := by
    rw [ha'def]
    simp
  rw [Submodule.coe_subtype, this]
  exact neg_mem hmem

end P

end Branches

end NodeBridge

end SemistableReduction
