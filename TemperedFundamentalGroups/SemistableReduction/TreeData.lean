/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DeltaGenus
import TemperedFundamentalGroups.SemistableReduction.NodeDouble

/-!
# Coordinates of a Gauss tree

Blueprint §9.9, S7.5. Let `F' / C(x)` be finite. A type-2 valuation `W` of `F'` *lies over the
Gauss point of a coordinate `t`* (`IsOver`) if `W(Q(t)) = ‖Q‖_{Gauss}`.

* `isOver_affine`, `isOver_inv`: lying over the Gauss point of `t` is the same as lying over that
  of `α t + β` (`|α| = 1`, `|β| ≤ 1`), or of `t⁻¹`;
* `comap_eq_gaussRat_of_isOver`: over the Gauss point of `(x - a) / c` means extending
  `w_{a, |c|}`; distinct discs have disjoint sets of extensions (`eq_of_isOver_of_isOver`);
* `finite_isOver`: the extensions of the Gauss point of a coordinate are finite (W4);
* `TreeData`: a finite family of discs `D(aᵢ, |cᵢ|)` with edges (parent ⊋ child) and points `bᵢ`
  in the free residue directions of the vertices, recording the combinatorics used by the
  δ-count; its vertex coordinates `vc i = (x - aᵢ) / cᵢ`, edge coordinates
  `ec e = (x - a_{child}) / c_{parent}`, and the vertex set `S` of all extensions.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra C F]

section IsOver

/-- Values of polynomials in a coordinate over whose Gauss point `W` lies. -/
lemma IsOver.valuation_aeval {x : F} {hx : Transcendental C x} {W : TypeTwo C F}
    (h : IsOver hx W) (Q : C[X]) :
    W.val (aeval x Q) = Gauss.sup (NormedField.valuation (K := C)) 1 Q := by
  have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u (algebraMap C[X] (RatFunc C) Q)) h
  simp only [comap_apply] at this
  change W.val (coordAlgHom hx (algebraMap C[X] (RatFunc C) Q)) = _ at this
  rw [coordAlgHom_algebraMap, gauss1_algebraMap] at this
  exact this

lemma IsOver.valuation_sub {x : F} {hx : Transcendental C x} {W : TypeTwo C F}
    (h : IsOver hx W) (β : C) : W.val (x - algebraMap C F β) = max ‖β‖₊ 1 := by
  have := h.valuation_aeval (X - Polynomial.C β)
  rw [_root_.map_sub, aeval_X, aeval_C] at this
  rw [this, ← gauss1_algebraMap, gaussRat_algebraMap, gauss_X_sub_C, zero_sub, Valuation.map_neg,
    NormedField.valuation_apply, Units.val_one]

lemma IsOver.valuation_self {x : F} {hx : Transcendental C x} {W : TypeTwo C F}
    (h : IsOver hx W) : W.val x = 1 := by
  simpa using h.valuation_sub 0

lemma isOver_congr {t t' : F} (h : t = t') (ht : Transcendental C t)
    (ht' : Transcendental C t') (W : TypeTwo C F) : IsOver ht W ↔ IsOver ht' W := by
  subst h
  rfl

variable [IsAlgClosed C]

/-- A criterion for lying over the Gauss point of `x`: the values of `x - β` are right. -/
lemma isOver_of_valuation_sub {x : F} (hx : Transcendental C x) {W : TypeTwo C F}
    (h : ∀ β : C, W.val (x - algebraMap C F β) = max ‖β‖₊ 1) : IsOver hx W := by
  refine valuation_ratFunc_ext_of_linear (fun e ↦ ?_) fun β ↦ ?_
  · simp only [comap_apply]
    change W.val (coordAlgHom hx (algebraMap C (RatFunc C) e)) = _
    rw [AlgHom.commutes, TypeTwo.valuation_algebraMap, gauss1_algebraMap_C]
  · simp only [comap_apply]
    change W.val (coordAlgHom hx (algebraMap C[X] (RatFunc C) (X - Polynomial.C β))) = _
    rw [coordAlgHom_algebraMap, _root_.map_sub, aeval_X, aeval_C, h, gaussRat_algebraMap,
      gauss_X_sub_C, zero_sub, Valuation.map_neg, NormedField.valuation_apply, Units.val_one]

omit [IsAlgClosed C] in
lemma max_norm_sub_one {b β : C} (hβ : ‖β‖ ≤ 1) : max ‖b - β‖₊ 1 = max ‖b‖₊ 1 := by
  have hβ' : ‖β‖₊ ≤ 1 := by exact_mod_cast hβ
  have hle : ‖b - β‖₊ ≤ max ‖b‖₊ ‖β‖₊ := by
    rw [sub_eq_add_neg, ← nnnorm_neg β]
    exact IsUltrametricDist.nnnorm_add_le_max _ _
  rcases le_total ‖b‖₊ 1 with hb | hb
  · rw [max_eq_right hb, max_eq_right (hle.trans (max_le hb hβ'))]
  · rcases eq_or_lt_of_le hb with hb1 | hb1
    · rw [← hb1, max_self, max_eq_right (hle.trans (max_le hb1.symm.le hβ'))]
    · have : ‖b - β‖₊ = ‖b‖₊ := by
        rw [sub_eq_add_neg]
        have hne : ‖b‖₊ ≠ ‖-β‖₊ := by rw [nnnorm_neg]; exact ne_of_gt (hβ'.trans_lt hb1)
        rw [IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm hne, nnnorm_neg,
          max_eq_left (hβ'.trans hb1.le)]
      rw [this]

/-- **Affine change of coordinates**: lying over the Gauss point of `t` is the same as lying over
that of `α t + β` for `|α| = 1`, `|β| ≤ 1`. -/
lemma isOver_affine {t : F} (ht : Transcendental C t) {α β : C} (hα : ‖α‖ = 1) (hβ : ‖β‖ ≤ 1)
    (ht' : Transcendental C (algebraMap C F α * t + algebraMap C F β)) {W : TypeTwo C F}
    (h : IsOver ht W) : IsOver ht' W := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp at hα
  refine isOver_of_valuation_sub ht' fun b ↦ ?_
  have heq : algebraMap C F α * t + algebraMap C F β - algebraMap C F b =
      algebraMap C F α * (t - algebraMap C F ((b - β) / α)) := by
    rw [mul_sub, ← map_mul, mul_div_cancel₀ _ hα0, _root_.map_sub]
    ring
  rw [heq, map_mul, TypeTwo.valuation_algebraMap, h.valuation_sub]
  have hα' : ‖α‖₊ = 1 := by ext; simpa using hα
  rw [hα', one_mul, nnnorm_div, hα', div_one, max_norm_sub_one hβ]

/-- **Inversion**: lying over the Gauss point of `t` is the same as lying over that of `t⁻¹`. -/
lemma isOver_inv {t : F} (ht : Transcendental C t) (ht' : Transcendental C t⁻¹)
    {W : TypeTwo C F} (h : IsOver ht W) : IsOver ht' W := by
  refine isOver_of_valuation_sub ht' fun b ↦ ?_
  have ht0 : t ≠ 0 := by
    rintro rfl
    exact ht (isAlgebraic_zero)
  rcases eq_or_ne b 0 with rfl | hb
  · simp [map_inv₀, h.valuation_self]
  have heq : t⁻¹ - algebraMap C F b = -(algebraMap C F b) * (t - algebraMap C F b⁻¹) * t⁻¹ := by
    rw [map_inv₀]
    have hb' : algebraMap C F b ≠ 0 := by simpa using hb
    field_simp
    ring
  rw [heq, map_mul, map_mul, Valuation.map_neg, TypeTwo.valuation_algebraMap, h.valuation_sub,
    map_inv₀, h.valuation_self, inv_one, mul_one, nnnorm_inv]
  have hb' : ‖b‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 hb
  rcases le_total ‖b‖₊ 1 with h1 | h1
  · rw [max_eq_right h1, max_eq_left (one_le_inv₀ (pos_iff_ne_zero.2 hb') |>.2 h1),
      mul_inv_cancel₀ hb']
  · rw [max_eq_left h1, max_eq_right (inv_le_one_of_one_le₀ h1), mul_one]

end IsOver

section Gauss

variable [IsAlgClosed C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]

variable (C F) in
/-- The vertex coordinate `(x - a) / c`. -/
noncomputable def vcoord (a c : C) : F := (xF C F - algebraMap C F a) / algebraMap C F c

omit [IsUltrametricDist C] [IsAlgClosed C] [IsScalarTower C (RatFunc C) F] in
lemma xF_eq_vcoord {a c : C} (hc : c ≠ 0) :
    xF C F = algebraMap C F c * vcoord C F a c + algebraMap C F a := by
  have : algebraMap C F c ≠ 0 := by simpa using hc
  simp only [vcoord]
  field_simp
  ring

/-- **Over the Gauss point of `(x - a)/c` means extending `w_{a,|c|}`.** -/
lemma comap_eq_gaussRat_of_isOver {a c : C} (hc : c ≠ 0) (hx : Transcendental C (vcoord C F a c))
    {W : TypeTwo C F} (h : IsOver hx W) :
    W.val.comap (algebraMap (RatFunc C) F) =
      gaussRat (NormedField.valuation (K := C)) a (Units.mk0 ‖c‖₊ (by simpa using hc)) := by
  refine valuation_ratFunc_ext_of_linear (fun e ↦ ?_) fun β ↦ ?_
  · rw [comap_apply, ← IsScalarTower.algebraMap_apply, TypeTwo.valuation_algebraMap,
      gaussRat_algebraMap_C, NormedField.valuation_apply]
  · have hc' : algebraMap C F c ≠ 0 := by simpa using hc
    have heq : algebraMap (RatFunc C) F (algebraMap C[X] (RatFunc C) (X - Polynomial.C β)) =
        algebraMap C F c * (vcoord C F a c - algebraMap C F ((β - a) / c)) := by
      rw [_root_.map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C,
        _root_.map_sub, ← IsScalarTower.algebraMap_apply, show algebraMap (RatFunc C) F RatFunc.X = xF C F from rfl,
        xF_eq_vcoord (a := a) hc]
      simp only [map_div₀, _root_.map_sub]
      field_simp
      ring
    rw [comap_apply, heq, map_mul, TypeTwo.valuation_algebraMap, h.valuation_sub,
      gaussRat_algebraMap, gauss_X_sub_C, NormedField.valuation_apply, Units.val_mk0, nnnorm_div,
      ← nnnorm_neg (a - β), neg_sub]
    have hc0 : ‖c‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 hc
    rw [mul_max_of_nonneg _ _ zero_le, mul_div_cancel₀ _ hc0, mul_one]

/-- Distinct discs have disjoint sets of extensions. -/
lemma eq_of_isOver_of_isOver {a c a' c' : C} (hc : c ≠ 0) (hc' : c' ≠ 0)
    (hx : Transcendental C (vcoord C F a c)) (hx' : Transcendental C (vcoord C F a' c'))
    {W : TypeTwo C F} (h : IsOver hx W) (h' : IsOver hx' W) :
    ‖c‖ = ‖c'‖ ∧ ‖a - a'‖ ≤ ‖c‖ := by
  have e := (comap_eq_gaussRat_of_isOver hc hx h).symm.trans (comap_eq_gaussRat_of_isOver hc' hx' h')
  have h1 := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦
    u (algebraMap C[X] (RatFunc C) (X - Polynomial.C a))) e
  have h2 := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦
    u (algebraMap C[X] (RatFunc C) (X - Polynomial.C a'))) e
  simp only [gaussRat_algebraMap, gauss_X_sub_C, sub_self, map_zero, NormedField.valuation_apply,
    Units.val_mk0] at h1 h2
  rw [max_eq_right zero_le] at h1
  rw [max_eq_right zero_le] at h2
  have hsw : ‖a - a'‖₊ = ‖a' - a‖₊ := by rw [← nnnorm_neg, neg_sub]
  have hc1 : ‖c'‖₊ ≤ ‖c‖₊ := h1 ▸ le_max_right _ _
  have hc2 : ‖c‖₊ ≤ ‖c'‖₊ := h2 ▸ le_max_right _ _
  have hr : ‖c‖₊ = ‖c'‖₊ := le_antisymm hc2 hc1
  refine ⟨by simpa using congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) hr, ?_⟩
  have : ‖a' - a‖₊ ≤ ‖c‖₊ := h1 ▸ le_max_left _ _
  rw [← hsw] at this
  exact_mod_cast this

end Gauss

section Finite

variable [IsAlgClosed C] [CharZero C] [IsCurveFunctionField C F]
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- The type-2 valuations over the Gauss point of a coordinate are finitely many (W4). -/
lemma finite_isOver {x : F} (hx : Transcendental C x) :
    {W : TypeTwo C F | IsOver hx W}.Finite := by
  letI : Algebra (RatFunc C) F := (coordAlgHom hx).toRingHom.toAlgebra
  haveI : IsScalarTower C (RatFunc C) F :=
    IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom hx).commutes c).symm
  have hxF : xF C F = x := xF_coord hx
  haveI := finiteDimensional_of_transcendental (C := C) (F := F) (hxF ▸ hx)
  haveI : Finite (Ext C F) := finite_ext (F := F) hp hp1
  refine ((Set.finite_range fun v : Ext C F ↦ v.1).preimage (f := TypeTwo.val)
    fun W _ W' _ h ↦ TypeTwo.val_injective h).subset fun W hW ↦ ⟨⟨W.val, hW⟩, rfl⟩

end Finite

section Transcendental

variable [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F]

omit [IsUltrametricDist C] in
lemma transcendental_vcoord [FiniteDimensional (RatFunc C) F] {a c : C} (hc : c ≠ 0) :
    Transcendental C (vcoord C F a c) := by
  intro halg
  apply transcendental_xF (C := C) (F := F)
  rw [xF_eq_vcoord (a := a) hc]
  exact ((isAlgebraic_algebraMap c).mul halg).add (isAlgebraic_algebraMap a)

omit [IsUltrametricDist C] [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F] in
lemma transcendental_inv {t : F} (ht : Transcendental C t) : Transcendental C t⁻¹ := fun h ↦
  ht (by simpa using h.inv)

end Transcendental

/-! ### Tree data -/

namespace TreeCount

/-- **Combinatorial data of a Gauss tree** with points `bᵢ` in free residue directions: discs
`D(aᵢ, |cᵢ|)` (pairwise distinct), edges `e` from a parent disc to a strictly smaller child disc
(each vertex has at most one parent edge; the child discs of a vertex lie in distinct residue
directions), and points `bᵢ ∈ D(aᵢ, |cᵢ|)` in a residue direction of `i` containing no child,
such that every other `bⱼ` in the disc of `i` lies in the direction of a child, all `bⱼ` lie in
the disc of a parentless vertex, and no `bⱼ` lies in the open annulus of an edge or in the open
residue disc of a child direction outside the child disc. -/
structure TreeData (C : Type*) [NontriviallyNormedField C] where
  /-- The vertices. -/
  ι : Type
  /-- The edges. -/
  E : Type
  [fintypeι : Fintype ι]
  [decEqι : DecidableEq ι]
  [nonemptyι : Nonempty ι]
  [fintypeE : Fintype E]
  [decEqE : DecidableEq E]
  /-- The centers. -/
  a : ι → C
  /-- The radii. -/
  c : ι → C
  /-- The points in the free directions. -/
  b : ι → C
  /-- The parent of an edge. -/
  par : E → ι
  /-- The child of an edge. -/
  chi : E → ι
  hc : ∀ i, c i ≠ 0
  hred : ∀ i j, ‖c i‖ = ‖c j‖ → ‖a i - a j‖ ≤ ‖c i‖ → i = j
  hedge_c : ∀ e, ‖c (chi e)‖ < ‖c (par e)‖
  hedge_a : ∀ e, ‖a (chi e) - a (par e)‖ ≤ ‖c (par e)‖
  hchi : ∀ e e', chi e = chi e' → e = e'
  hdir : ∀ e e', par e = par e' → e ≠ e' → ‖a (chi e) - a (chi e')‖ = ‖c (par e)‖
  hb_mem : ∀ i, ‖b i - a i‖ ≤ ‖c i‖
  hb_free : ∀ e, ‖b (par e) - a (chi e)‖ = ‖c (par e)‖
  hb_dir : ∀ i j, j ≠ i → ‖b j - a i‖ ≤ ‖c i‖ → ∃ e, par e = i ∧ ‖b j - a (chi e)‖ < ‖c i‖
  hroot : ∀ i, (∀ e, chi e ≠ i) → ∀ j, ‖b j - a i‖ ≤ ‖c i‖
  hb_edge : ∀ e j, ‖b j - a (chi e)‖ ≤ ‖c (chi e)‖ ∨ ‖c (par e)‖ ≤ ‖b j - a (chi e)‖

attribute [instance] TreeData.fintypeι TreeData.decEqι TreeData.nonemptyι TreeData.fintypeE
  TreeData.decEqE

variable (T : TreeData C)

/-- The node parameter `c_{child} / c_{parent}` of an edge. -/
noncomputable def TreeData.ce (e : T.E) : C := T.c (T.chi e) / T.c (T.par e)

omit [IsUltrametricDist C] in
lemma TreeData.ce_ne_zero (e : T.E) : T.ce e ≠ 0 := div_ne_zero (T.hc _) (T.hc _)

omit [IsUltrametricDist C] in
lemma TreeData.norm_ce_lt_one (e : T.E) : ‖T.ce e‖ < 1 := by
  rw [TreeData.ce, norm_div, div_lt_one (norm_pos_iff.2 (T.hc _))]
  exact T.hedge_c e

section Coordinates

variable {F' : Type*} [Field F'] [Algebra C F'] [Algebra (RatFunc C) F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

variable (F') in
/-- The coordinate `(x - aᵢ) / cᵢ` of a vertex. -/
noncomputable def TreeData.vc (i : T.ι) : F' := vcoord C F' (T.a i) (T.c i)

variable (F') in
/-- The coordinate `(x - a_{child}) / c_{parent}` of an edge (outer side). -/
noncomputable def TreeData.ec (e : T.E) : F' := vcoord C F' (T.a (T.chi e)) (T.c (T.par e))

omit [IsUltrametricDist C] in
lemma TreeData.hvc (i : T.ι) : Transcendental C (T.vc F' i) := transcendental_vcoord (T.hc i)

omit [IsUltrametricDist C] in
lemma TreeData.hec (e : T.E) : Transcendental C (T.ec F' e) := transcendental_vcoord (T.hc _)

omit [IsUltrametricDist C] in
lemma TreeData.hinner (e : T.E) : Transcendental C (algebraMap C F' (T.ce e) / T.ec F' e) := by
  rw [div_eq_mul_inv]
  intro h
  apply transcendental_inv (T.hec (F' := F') e)
  have hce : algebraMap C F' (T.ce e) ≠ 0 := by simpa using T.ce_ne_zero e
  have := (isAlgebraic_algebraMap (R := C) (A := F') (T.ce e)⁻¹).mul h
  rwa [map_inv₀, ← mul_assoc, inv_mul_cancel₀ hce, one_mul] at this

omit [IsUltrametricDist C] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma TreeData.ec_eq (e : T.E) : T.ec F' e = algebraMap C F' 1 * T.vc F' (T.par e) +
    algebraMap C F' (-((T.a (T.chi e) - T.a (T.par e)) / T.c (T.par e))) := by
  have hc : algebraMap C F' (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  simp only [TreeData.ec, TreeData.vc, vcoord, map_one, one_mul, _root_.map_neg, map_div₀,
    _root_.map_sub]
  field_simp
  ring

omit [IsUltrametricDist C] [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] in
lemma TreeData.inner_eq (e : T.E) :
    algebraMap C F' (T.ce e) / T.ec F' e = (T.vc F' (T.chi e))⁻¹ := by
  have hc : algebraMap C F' (T.c (T.par e)) ≠ 0 := by simpa using T.hc (T.par e)
  have hc' : algebraMap C F' (T.c (T.chi e)) ≠ 0 := by simpa using T.hc (T.chi e)
  simp only [TreeData.ec, TreeData.vc, vcoord, TreeData.ce, map_div₀, inv_div]
  rcases eq_or_ne (xF C F' - algebraMap C F' (T.a (T.chi e))) 0 with h | h
  · simp [h]
  · field_simp

variable [IsAlgClosed C]

lemma TreeData.isOver_ec_iff (e : T.E) (W : TypeTwo C F') :
    IsOver (T.hvc (F' := F') (T.par e)) W ↔ IsOver (T.hec (F' := F') e) W := by
  have hβ : ‖-((T.a (T.chi e) - T.a (T.par e)) / T.c (T.par e))‖ ≤ 1 := by
    rw [norm_neg, norm_div, div_le_one (norm_pos_iff.2 (T.hc _))]
    exact T.hedge_a e
  constructor
  · intro h
    have := isOver_affine (T.hvc (F' := F') (T.par e)) (α := 1) (by simp) hβ
      (by rw [← T.ec_eq (F' := F') e]; exact T.hec e) h
    exact (isOver_congr (T.ec_eq (F' := F') e).symm _ _ W).1 this
  · intro h
    have hvc : T.vc F' (T.par e) = algebraMap C F' 1 * T.ec F' e +
        algebraMap C F' ((T.a (T.chi e) - T.a (T.par e)) / T.c (T.par e)) := by
      rw [T.ec_eq (F' := F') e, map_one, one_mul, one_mul, _root_.map_neg, neg_add_cancel_right]
    have hβ' : ‖(T.a (T.chi e) - T.a (T.par e)) / T.c (T.par e)‖ ≤ 1 := by simpa using hβ
    have := isOver_affine (T.hec (F' := F') e) (α := 1) (by simp) hβ'
      (by rw [← hvc]; exact T.hvc _) h
    exact (isOver_congr hvc.symm _ _ W).1 this

lemma TreeData.isOver_inner_iff (e : T.E) (W : TypeTwo C F') :
    IsOver (T.hvc (F' := F') (T.chi e)) W ↔ IsOver (T.hinner (F' := F') e) W := by
  constructor
  · intro h
    have := isOver_inv (T.hvc (F' := F') (T.chi e))
      (by rw [← T.inner_eq (F' := F') e]; exact T.hinner e) h
    exact (isOver_congr (T.inner_eq (F' := F') e).symm _ _ W).1 this
  · intro h
    have h' := isOver_inv (T.hinner (F' := F') e) (transcendental_inv (T.hinner e)) h
    have heq : (algebraMap C F' (T.ce e) / T.ec F' e)⁻¹ = T.vc F' (T.chi e) := by
      rw [T.inner_eq (F' := F') e, inv_inv]
    exact (isOver_congr heq _ _ W).1 h'

end Coordinates

section Vertices

variable {F' : Type*} [Field F'] [Algebra C F'] [Algebra (RatFunc C) F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F'] [IsAlgClosed C] [CharZero C]
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

attribute [local instance] isCurveFunctionField_F

open Classical in
variable (F') in
/-- The vertex set: all extensions of the Gauss points of the tree. -/
noncomputable def TreeData.S : Finset (TypeTwo C F') :=
  Finset.univ.biUnion fun i ↦ (finite_isOver hp hp1 (T.hvc (F' := F') i)).toFinset

lemma TreeData.mem_S (W : TypeTwo C F') :
    W ∈ TreeData.S T F' hp hp1 ↔ ∃ i, IsOver (T.hvc (F' := F') i) W := by
  classical
  simp [TreeData.S]

omit [CharZero C] in
/-- A type-2 valuation lies over at most one vertex. -/
lemma TreeData.eq_of_isOver {i j : T.ι} {W : TypeTwo C F'} (hi : IsOver (T.hvc (F' := F') i) W)
    (hj : IsOver (T.hvc (F' := F') j) W) : i = j := by
  obtain ⟨h1, h2⟩ := eq_of_isOver_of_isOver (T.hc i) (T.hc j) (T.hvc i) (T.hvc j) hi hj
  exact T.hred i j h1 h2

end Vertices

end TreeCount

end SemistableReduction
