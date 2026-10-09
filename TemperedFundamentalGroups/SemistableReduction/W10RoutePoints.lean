/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteStatements
import TemperedFundamentalGroups.SemistableReduction.VertexDescent
import TemperedFundamentalGroups.SemistableReduction.GaussClassification

/-!
# Points of the normalized charts over `C` from valuation rings (G4, part 2)

Blueprint §9.7a, step 4 (G4 (ii)). Let `G / C(x)` and `W'` a valuation subring of `G` lying over
`O_C` (`IsOverOC`). Its center `centerI A W'` on a chart `A ⊆ W'` is a prime ideal.

* **vertex charts** `DRint 0 1 G`: if `x ∈ W'`, the chart lies in `W'` (`drint_le`); if `x ∈ 𝔪_W'`,
  the center lies over `(𝔪_C, x)` (`comap_centerI_drint`) and is maximal; if `x - b` is a
  `W'`-unit for every `b ∈ O_C` (a Gauss point), the center lies over a prime contained in
  `(𝔪_C, x)` (`comap_centerI_drint_le`), so some maximal ideal over `(𝔪_C, x)` contains it
  (`exists_maximal_over_discIdeal`);
* **node charts** `Rint c G`: if `x, c/x ∈ 𝔪_W'`, the chart lies in `W'` and the center lies over
  the node (`comap_centerI_rint`) and is maximal.
* `exists_lift`: lying over from a complete discretely valued `E ⊆ C` (`C / E` algebraic): a
  valuation subring `W` of an `E`-form `F₀` with `W ∩ E = O_E` is the restriction of a valuation
  subring `W'` of `F'` with `W' ∩ C = O_C` (Chevalley + unique extension over a complete base).
-/

universe u

open IsLocalRing Polynomial
open scoped NNReal

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section Center

variable {G : Type*} [Field G] (W' : ValuationSubring G)

/-- The center `{z ∈ A : z ∈ 𝔪_W'}` of a valuation subring `W' ⊇ A` on a subalgebra `A`. -/
def centerI {R : Type*} [CommRing R] [Algebra R G] (A : Subalgebra R G)
    (h : ∀ z : A, (z : G) ∈ W') : Ideal A where
  carrier := {z | W'.valuation (z : G) < 1}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at hx hy ⊢
    exact (Valuation.map_add _ _ _).trans_lt (max_lt hx hy)
  zero_mem' := by simp
  smul_mem' r z hz := by
    simp only [smul_eq_mul, Set.mem_setOf_eq, Subalgebra.coe_mul, map_mul] at hz ⊢
    exact mul_lt_one_of_nonneg_of_lt_one_right ((W'.valuation_le_one_iff _).2 (h r)) zero_le hz

variable {W'}

lemma mem_centerI {R : Type*} [CommRing R] [Algebra R G] {A : Subalgebra R G}
    {h : ∀ z : A, (z : G) ∈ W'} {z : A} : z ∈ centerI W' A h ↔ W'.valuation (z : G) < 1 :=
  Iff.rfl

instance centerI_isPrime {R : Type*} [CommRing R] [Algebra R G] (A : Subalgebra R G)
    (h : ∀ z : A, (z : G) ∈ W') : (centerI W' A h).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, mem_centerI]
    simp
  mem_or_mem' {x y} hxy := by
    rw [mem_centerI, Subalgebra.coe_mul, map_mul] at hxy
    by_contra hne
    push Not at hne
    rw [mem_centerI, mem_centerI, not_lt, not_lt] at hne
    have h1 : W'.valuation (x : G) = 1 := le_antisymm ((W'.valuation_le_one_iff _).2 (h x)) hne.1
    have h2 : W'.valuation (y : G) = 1 := le_antisymm ((W'.valuation_le_one_iff _).2 (h y)) hne.2
    rw [h1, h2, mul_one] at hxy
    exact lt_irrefl _ hxy

end Center

section OverOC

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] (W' : ValuationSubring G)

set_option hygiene false in
local notation "ψ" => algebraMap (RatFunc C) G

set_option hygiene false in
local notation "κ" k => algebraMap (RatFunc C) G (algebraMap C (RatFunc C) k)

variable (C) in
/-- `W'` lies over `O_C`. -/
def IsOverOC : Prop := ∀ k : C, W'.valuation (κ k) ≤ 1 ↔ ‖k‖ ≤ 1

variable {W'}

omit [IsUltrametricDist C] in
lemma IsOverOC.lt_one_iff (hO : IsOverOC C W') (k : C) : W'.valuation (κ k) < 1 ↔ ‖k‖ < 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hinv : (κ k⁻¹) = (κ k)⁻¹ := by simp
  have h := hO k⁻¹
  rw [hinv, map_inv₀, norm_inv] at h
  have hpos : 0 < W'.valuation (κ k) := by
    rw [zero_lt_iff, Ne, map_eq_zero, map_eq_zero, map_eq_zero]
    exact hk
  rw [inv_le_one₀ hpos, inv_le_one₀ (norm_pos_iff.2 hk)] at h
  rw [← not_le, h, not_le]

omit [IsUltrametricDist C] in
lemma IsOverOC.mem (hO : IsOverOC C W') {k : C} (hk : ‖k‖ ≤ 1) : (κ k) ∈ W' :=
  (W'.valuation_le_one_iff _).1 ((hO k).2 hk)

omit [IsUltrametricDist C] in
lemma IsOverOC.val_eq_one (hO : IsOverOC C W') {k : C} (hk : ‖k‖ = 1) : W'.valuation (κ k) = 1 :=
  le_antisymm ((hO k).2 hk.le)
    (not_lt.1 fun h ↦ by rw [hO.lt_one_iff, hk] at h; exact lt_irrefl _ h)

omit [IsUltrametricDist C] in
lemma mem_of_isIntegral {R : Type*} [CommRing R] [Algebra R G] (f : R →+* W')
    (hf : ∀ r, ((f r : W') : G) = algebraMap R G r) {z : G} (hz : IsIntegral R z) : z ∈ W' := by
  have hint : IsIntegral W' z := IsIntegral.map_of_comp_eq f (RingHom.id G)
    (RingHom.ext fun r ↦ by change ((f r : W') : G) = algebraMap R G r; exact hf r) hz
  have : IsIntegrallyClosedIn W' G := inferInstance
  obtain ⟨w, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.1 hint
  exact w.2

/-! ### Vertex charts -/

lemma map_mem_of_mem_discRing (hO : IsOverOC C W') (hX : ψ RatFunc.X ∈ W') {f : RatFunc C}
    (hf : f ∈ discRing (0 : C) 1) : ψ f ∈ W' := by
  induction hf using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨o, ho, rfl⟩ | hz
    · refine hO.mem ?_
      have : NormedField.valuation (K := C) o ≤ 1 := ho
      rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at this
      simpa using this
    · rw [Set.mem_singleton_iff.1 hz, gaussCoord_zero_one]
      exact hX
  | zero => simp
  | one => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

/-- The disc chart into `W'`. -/
noncomputable def discToW (hO : IsOverOC C W') (hX : ψ RatFunc.X ∈ W') :
    discRing (0 : C) 1 →+* W' where
  toFun f := ⟨ψ f, map_mem_of_mem_discRing hO hX f.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' f g := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

/-- **The vertex chart lies in `W'`** when `x ∈ W'`. -/
theorem drint_le (hO : IsOverOC C W') (hX : ψ RatFunc.X ∈ W') (z : DRint (0 : C) 1 G) :
    (z : G) ∈ W' :=
  mem_of_isIntegral (discToW hO hX) (fun _ ↦ rfl) z.2

/-- Every element of `O_C[x]` is a constant plus an element of `(𝔪_C, x)`. -/
lemma exists_sub_mem_discIdeal (f : discRing (0 : C) 1) :
    ∃ Q : C[X], Gauss.sup (NormedField.valuation (K := C)) 1 Q ≤ 1 ∧
      algebraMap C[X] (RatFunc C) Q = f ∧
      ∃ h : algebraMap C (RatFunc C) (Q.coeff 0) ∈ discRing (0 : C) 1,
        f - ⟨_, h⟩ ∈ discIdeal (0 : C) 1 := by
  obtain ⟨Q, hQ, hQf⟩ := mem_discRing_iff.1 f.2
  have hQ0 : ‖Q.coeff 0‖ ≤ 1 := by
    have := nnnorm_coeff_le_one hQ 0
    exact_mod_cast this
  have hmem : algebraMap C (RatFunc C) (Q.coeff 0) ∈ discRing (0 : C) 1 :=
    mem_discRing_iff.2 ⟨Polynomial.C (Q.coeff 0), by
      rw [Gauss.sup_C, NormedField.valuation_apply, ← NNReal.coe_le_coe]
      simpa using hQ0, by rw [ratFunc_algebraMap_C]⟩
  refine ⟨Q, hQ, hQf, hmem, Q - Polynomial.C (Q.coeff 0), fun i ↦ ?_, ?_, ?_⟩
  · rw [coeff_sub, coeff_C]
    split_ifs with hi
    · subst hi; simp
    · rw [sub_zero]; exact nnnorm_coeff_le_one hQ i
  · rw [gaussCoord_zero_one, RatFunc.aeval_X_left_eq_algebraMap, map_sub, hQf,
      ratFunc_algebraMap_C]
    rfl
  · simp

/-- Constants in `(𝔪_C, x)` have norm `< 1`. -/
lemma norm_lt_one_of_mem_discIdeal {k : C}
    (hk : algebraMap C (RatFunc C) k ∈ discRing (0 : C) 1)
    (h : (⟨_, hk⟩ : discRing (0 : C) 1) ∈ discIdeal (0 : C) 1) : ‖k‖ < 1 := by
  obtain ⟨Q, -, hQa, hQ0⟩ := h
  rw [gaussCoord_zero_one, RatFunc.aeval_X_left_eq_algebraMap] at hQa
  have hQa' : algebraMap C[X] (RatFunc C) Q = algebraMap C[X] (RatFunc C) (Polynomial.C k) := by
    rw [ratFunc_algebraMap_C]; exact hQa
  have := IsFractionRing.injective C[X] (RatFunc C) hQa'
  subst this
  have : ‖k‖₊ < 1 := by simpa using hQ0
  exact_mod_cast this

/-- Elements of `(𝔪_C, x)` lie in `𝔪_W'` when `x ∈ 𝔪_W'`. -/
lemma val_lt_one_of_mem_discIdeal (hO : IsOverOC C W') (hX : W'.valuation (ψ RatFunc.X) < 1)
    {f : discRing (0 : C) 1} (hf : f ∈ discIdeal (0 : C) 1) : W'.valuation (ψ f) < 1 := by
  obtain ⟨Q, hQ, hQa, hQ0⟩ := hf
  rw [gaussCoord_zero_one, RatFunc.aeval_X_left_eq_algebraMap] at hQa
  rw [← hQa]
  have hdecomp : algebraMap C[X] (RatFunc C) Q =
      algebraMap C (RatFunc C) (Q.coeff 0) +
        RatFunc.X * algebraMap C[X] (RatFunc C) Q.divX := by
    conv_lhs => rw [← X_mul_divX_add Q]
    rw [map_add, map_mul, RatFunc.algebraMap_X, ratFunc_algebraMap_C, add_comm]
  have hdiv : ψ (algebraMap C[X] (RatFunc C) Q.divX) ∈ W' := by
    refine map_mem_of_mem_discRing hO ((W'.valuation_le_one_iff _).1 hX.le) ?_
    refine mem_discRing_iff.2 ⟨Q.divX, Gauss.sup_le_iff.2 fun i ↦ ?_, rfl⟩
    simp only [Gauss.term, Units.val_one, one_pow, mul_one, coeff_divX,
      NormedField.valuation_apply]
    exact hQ (i + 1)
  rw [hdecomp, map_add, map_mul]
  refine (Valuation.map_add _ _ _).trans_lt (max_lt ((hO.lt_one_iff _).2 (by exact_mod_cast hQ0))
    ?_)
  rw [map_mul]
  exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hX ((W'.valuation_le_one_iff _).2 hdiv)

/-- **Closed points of vertex charts**: if `x ∈ 𝔪_W'`, the center of `W'` on `DRint 0 1 G` lies
over `(𝔪_C, x)`. -/
theorem comap_centerI_drint (hO : IsOverOC C W') (hX : W'.valuation (ψ RatFunc.X) < 1) :
    (centerI W' (DRint (0 : C) 1 G)
        (drint_le hO ((W'.valuation_le_one_iff _).1 hX.le))).comap
      (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) = discIdeal (0 : C) 1 := by
  ext f
  rw [Ideal.mem_comap, mem_centerI]
  change W'.valuation (ψ f) < 1 ↔ _
  obtain ⟨Q, -, -, hmem, hsub⟩ := exists_sub_mem_discIdeal f
  have hfk : (f : RatFunc C) = (f - ⟨_, hmem⟩ : discRing (0 : C) 1) +
      algebraMap C (RatFunc C) (Q.coeff 0) := by simp
  have hsmall := val_lt_one_of_mem_discIdeal hO hX hsub
  constructor
  · intro h
    have hk : W'.valuation (κ (Q.coeff 0)) < 1 := by
      have : (κ (Q.coeff 0)) = ψ f - ψ ((f - ⟨_, hmem⟩ : discRing (0 : C) 1) : RatFunc C) := by
        rw [hfk, map_add]; ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt h hsmall)
    have hk' : (⟨_, hmem⟩ : discRing (0 : C) 1) ∈ discIdeal (0 : C) 1 := by
      refine ⟨Polynomial.C (Q.coeff 0), fun i ↦ ?_, ?_, ?_⟩
      · rw [coeff_C]
        split_ifs
        · have := (hO.lt_one_iff _).1 hk
          rw [← NNReal.coe_le_coe]
          simpa using this.le
        · simp
      · rw [gaussCoord_zero_one, RatFunc.aeval_X_left_eq_algebraMap, ratFunc_algebraMap_C]
      · have := (hO.lt_one_iff _).1 hk
        simpa [← NNReal.coe_lt_coe] using this
    have := Ideal.add_mem _ hsub hk'
    simpa using this
  · intro h
    exact val_lt_one_of_mem_discIdeal hO hX h

/-- **Gauss points of vertex charts**: if every `x - b`, `b ∈ O_C`, is a `W'`-unit, the center
of `W'` on `DRint 0 1 G` lies over a prime contained in `(𝔪_C, x)`. -/
theorem comap_centerI_drint_le [IsAlgClosed C] (hO : IsOverOC C W') (hX : ψ RatFunc.X ∈ W')
    (hgen : ∀ b : C, ‖b‖ ≤ 1 → W'.valuation (ψ RatFunc.X - κ b) = 1) :
    (centerI W' (DRint (0 : C) 1 G) (drint_le hO hX)).comap
      (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) ≤ discIdeal (0 : C) 1 := by
  -- `W'` restricts to the Gauss valuation `w_{0,1}` (for the induced valuation of `C`)
  set v : Valuation C W'.ValueGroup := (W'.valuation.comap ψ).comap (algebraMap C (RatFunc C))
  set w : Valuation (RatFunc C) W'.ValueGroup := W'.valuation.comap ψ
  have hv : ∀ k : C, v k ≤ 1 ↔ ‖k‖ ≤ 1 := hO
  have hw : w = gaussRat v 0 1 := by
    refine valuation_ratFunc_ext_of_linear (fun k ↦ ?_) fun b ↦ ?_
    · rw [gaussRat_algebraMap_C]; rfl
    · rw [gaussRat_algebraMap, gauss_X_sub_C, zero_sub, Valuation.map_neg, Units.val_one]
      have hXb : algebraMap C[X] (RatFunc C) (X - Polynomial.C b) =
          RatFunc.X - algebraMap C (RatFunc C) b := by
        rw [map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
      change W'.valuation (ψ _) = _
      rw [hXb, map_sub]
      by_cases hb : ‖b‖ ≤ 1
      · rw [hgen b hb, max_eq_right ((hv b).2 hb)]
      · have hvb : 1 < v b := lt_of_not_ge fun h ↦ hb ((hv b).1 h)
        have hX1 : W'.valuation (ψ RatFunc.X) ≤ 1 := (W'.valuation_le_one_iff _).2 hX
        rw [Valuation.map_sub_eq_of_lt_right _ (hX1.trans_lt hvb), max_eq_left hvb.le]
        rfl
  intro f hf
  rw [Ideal.mem_comap, mem_centerI] at hf
  change W'.valuation (ψ f) < 1 at hf
  obtain ⟨Q, hQ, hQf, hmem, hsub⟩ := exists_sub_mem_discIdeal f
  by_cases hQ0 : ‖Q.coeff 0‖ < 1
  · have hk' : (⟨_, hmem⟩ : discRing (0 : C) 1) ∈ discIdeal (0 : C) 1 := by
      refine ⟨Polynomial.C (Q.coeff 0), fun i ↦ ?_, ?_, ?_⟩
      · rw [coeff_C]
        split_ifs
        · rw [← NNReal.coe_le_coe]; simpa using hQ0.le
        · simp
      · rw [gaussCoord_zero_one, RatFunc.aeval_X_left_eq_algebraMap, ratFunc_algebraMap_C]
      · simpa [← NNReal.coe_lt_coe] using hQ0
    have := Ideal.add_mem _ hsub hk'
    simpa using this
  · exfalso
    have hQ1 : ‖Q.coeff 0‖ = 1 := le_antisymm (by
      have := nnnorm_coeff_le_one hQ 0
      exact_mod_cast this) (not_lt.1 hQ0)
    have hval : W'.valuation (ψ f) = gauss v 0 1 Q := by
      change w f = _
      rw [hw, ← hQf, gaussRat_algebraMap]
    have hge : 1 ≤ gauss v 0 1 Q := by
      rw [gauss_apply, taylor_zero]
      refine le_trans ?_ (Gauss.term_le_sup Q 0)
      simp only [Gauss.term, pow_zero, mul_one]
      exact (hO.val_eq_one hQ1).ge
    rw [hval] at hf
    exact lt_irrefl _ (hf.trans_le hge)

/-! ### Node charts -/

variable {c : C}

/-- Every element of the node chart is a constant plus an element small on the open segment and
in `𝔪_W'` (when `x, c/x ∈ 𝔪_W'`). -/
lemma exists_const_W (hO : IsOverOC C W') (hX : W'.valuation (ψ RatFunc.X) < 1)
    (hcX : W'.valuation (ψ (algebraMap C (RatFunc C) c / RatFunc.X)) < 1)
    {f : RatFunc C} (hf : f ∈ nodeRing c) :
    ∃ k : C, ‖k‖ ≤ 1 ∧ (∀ s ∈ segment c,
      gaussRat (NormedField.valuation (K := C)) 0 s (f - algebraMap C (RatFunc C) k) < 1) ∧
      W'.valuation (ψ (f - algebraMap C (RatFunc C) k)) < 1 := by
  have hk1 : ∀ {k : C}, ‖k‖ ≤ 1 → ∀ s : ℝ≥0ˣ,
      gaussRat (NormedField.valuation (K := C)) 0 s (algebraMap C (RatFunc C) k) ≤ 1 := by
    intro k hk s
    rw [gaussRat_algebraMap_C, NormedField.valuation_apply, ← NNReal.coe_le_coe]
    simpa using hk
  induction hf using Subring.closure_induction with
  | mem z hz =>
    rcases hz with ⟨o, ho, rfl⟩ | hz
    · refine ⟨o, ?_, fun s _ ↦ by simp, by simp⟩
      have : NormedField.valuation (K := C) o ≤ 1 := ho
      rw [NormedField.valuation_apply, ← NNReal.coe_le_coe] at this
      simpa using this
    · rcases hz with rfl | hz
      · refine ⟨0, by simp, fun s hs ↦ ?_, by simpa using hX⟩
        rw [map_zero, sub_zero, gaussRat_X]
        exact hs.2
      · rw [Set.mem_singleton_iff] at hz
        subst hz
        refine ⟨0, by simp, fun s hs ↦ ?_, by simpa using hcX⟩
        rw [map_zero, sub_zero, map_div₀, gaussRat_X, gaussRat_algebraMap_C,
          NormedField.valuation_apply, div_lt_one (by simp)]
        exact hs.1
  | zero => exact ⟨0, by simp, fun s _ ↦ by simp, by simp⟩
  | one => exact ⟨1, by simp, fun s _ ↦ by simp, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k₁, hk₁, hs₁, hw₁⟩ := ha
    obtain ⟨k₂, hk₂, hs₂, hw₂⟩ := hb
    have he : a + b - algebraMap C (RatFunc C) (k₁ + k₂) =
        (a - algebraMap C (RatFunc C) k₁) + (b - algebraMap C (RatFunc C) k₂) := by
      rw [map_add]; ring
    refine ⟨k₁ + k₂, (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hk₁ hk₂),
      fun s hs ↦ ?_, ?_⟩
    · rw [he]
      exact (Valuation.map_add _ _ _).trans_lt (max_lt (hs₁ s hs) (hs₂ s hs))
    · rw [he, map_add]
      exact (Valuation.map_add _ _ _).trans_lt (max_lt hw₁ hw₂)
  | neg a _ ha =>
    obtain ⟨k, hk, hs, hw⟩ := ha
    have he : -a - algebraMap C (RatFunc C) (-k) = -(a - algebraMap C (RatFunc C) k) := by
      rw [map_neg]; ring
    refine ⟨-k, by simpa using hk, fun s hs' ↦ ?_, ?_⟩
    · rw [he, Valuation.map_neg]; exact hs s hs'
    · rw [he, map_neg, Valuation.map_neg]; exact hw
  | mul a b _ _ ha hb =>
    obtain ⟨k₁, hk₁, hs₁, hw₁⟩ := ha
    obtain ⟨k₂, hk₂, hs₂, hw₂⟩ := hb
    have he : a * b - algebraMap C (RatFunc C) (k₁ * k₂) =
        (a - algebraMap C (RatFunc C) k₁) * (b - algebraMap C (RatFunc C) k₂) +
          algebraMap C (RatFunc C) k₁ * (b - algebraMap C (RatFunc C) k₂) +
          algebraMap C (RatFunc C) k₂ * (a - algebraMap C (RatFunc C) k₁) := by
      rw [map_mul]; ring
    refine ⟨k₁ * k₂, by rw [norm_mul]; exact mul_le_one₀ hk₁ (norm_nonneg _) hk₂,
      fun s hs ↦ ?_, ?_⟩
    · rw [he]
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_add _ _ _).trans_lt
        (max_lt ?_ ?_)) ?_) <;> rw [map_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (hs₁ s hs) (hs₂ s hs).le
      · exact mul_lt_one_of_nonneg_of_lt_one_right (hk1 hk₁ s) zero_le (hs₂ s hs)
      · exact mul_lt_one_of_nonneg_of_lt_one_right (hk1 hk₂ s) zero_le (hs₁ s hs)
    · have e1 : ψ (a * b - algebraMap C (RatFunc C) (k₁ * k₂)) =
          ψ (a - algebraMap C (RatFunc C) k₁) * ψ (b - algebraMap C (RatFunc C) k₂) +
            (κ k₁) * ψ (b - algebraMap C (RatFunc C) k₂) +
            (κ k₂) * ψ (a - algebraMap C (RatFunc C) k₁) := by
        rw [he]; simp only [map_add, map_mul]
      rw [e1]
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ((Valuation.map_add _ _ _).trans_lt
        (max_lt ?_ ?_)) ?_) <;> rw [Valuation.map_mul]
      · exact mul_lt_one_of_nonneg_of_lt_one_left zero_le hw₁ hw₂.le
      · exact mul_lt_one_of_nonneg_of_lt_one_right ((hO k₁).2 hk₁) zero_le hw₂
      · exact mul_lt_one_of_nonneg_of_lt_one_right ((hO k₂).2 hk₂) zero_le hw₁

omit [IsUltrametricDist C] in
/-- The open segment is nonempty. -/
lemma segment_nonempty (hc : ‖c‖ < 1) (hc0 : c ≠ 0) : (segment c).Nonempty := by
  obtain ⟨t, ht1, ht2⟩ := exists_between hc
  refine ⟨Units.mk0 ⟨t, (norm_nonneg c).trans ht1.le⟩ ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun x : ℝ≥0 ↦ (x : ℝ)) h
    simp only [NNReal.coe_zero] at this
    exact (norm_pos_iff.2 hc0).ne' (le_antisymm (this ▸ ht1.le) (norm_nonneg c))
  · change ‖c‖₊ < ⟨t, _⟩
    exact_mod_cast ht1
  · change (⟨t, _⟩ : ℝ≥0) < 1
    exact_mod_cast ht2

/-- The node chart into `W'`. -/
noncomputable def nodeToW (hO : IsOverOC C W') (hX : W'.valuation (ψ RatFunc.X) < 1)
    (hcX : W'.valuation (ψ (algebraMap C (RatFunc C) c / RatFunc.X)) < 1) :
    nodeRing c →+* W' where
  toFun f := ⟨ψ f, by
    obtain ⟨k, hk, -, hw⟩ := exists_const_W hO hX hcX f.2
    have : ψ f = ψ (f - algebraMap C (RatFunc C) k) + κ k := by rw [map_sub]; ring
    rw [this]
    exact add_mem ((W'.valuation_le_one_iff _).1 hw.le) (hO.mem hk)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' f g := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' f g := Subtype.ext (by simp)

/-- **The node chart lies in `W'`** when `x, c/x ∈ 𝔪_W'`. -/
theorem rint_le (hO : IsOverOC C W') (hX : W'.valuation (ψ RatFunc.X) < 1)
    (hcX : W'.valuation (ψ (algebraMap C (RatFunc C) c / RatFunc.X)) < 1) (z : Rint c G) :
    (z : G) ∈ W' :=
  mem_of_isIntegral (nodeToW hO hX hcX) (fun _ ↦ rfl) z.2

/-- **Node points**: if `x, c/x ∈ 𝔪_W'`, the center of `W'` on `Rint c G` lies over the node. -/
theorem comap_centerI_rint (hc : ‖c‖ < 1) (hc0 : c ≠ 0) (hO : IsOverOC C W')
    (hX : W'.valuation (ψ RatFunc.X) < 1)
    (hcX : W'.valuation (ψ (algebraMap C (RatFunc C) c / RatFunc.X)) < 1) :
    (centerI W' (Rint c G) (rint_le hO hX hcX)).comap
      (algebraMap (nodeRing c) (Rint c G)) = tubeIdeal c := by
  obtain ⟨s₀, hs₀⟩ := segment_nonempty hc hc0
  ext f
  rw [Ideal.mem_comap, mem_centerI]
  change W'.valuation (ψ f) < 1 ↔ _
  obtain ⟨k, hk, hs, hw⟩ := exists_const_W hO hX hcX f.2
  have hsplit : (f : RatFunc C) = (f - algebraMap C (RatFunc C) k) + algebraMap C (RatFunc C) k :=
    by ring
  have hiff₁ : W'.valuation (ψ f) < 1 ↔ ‖k‖ < 1 := by
    rw [← hO.lt_one_iff]
    have e : ψ f = ψ (f - algebraMap C (RatFunc C) k) + (κ k) := by rw [map_sub]; ring
    constructor
    · intro h
      have : (κ k) = ψ f - ψ (f - algebraMap C (RatFunc C) k) := by rw [e]; ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt h hw)
    · intro h
      rw [e]
      exact (Valuation.map_add _ _ _).trans_lt (max_lt hw h)
  rw [hiff₁]
  constructor
  · intro h s hs'
    rw [hsplit]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt (hs s hs') ?_)
    rw [gaussRat_algebraMap_C, NormedField.valuation_apply]
    exact_mod_cast h
  · intro h
    have h1 := h s₀ hs₀
    have : algebraMap C (RatFunc C) k = (f : RatFunc C) - (f - algebraMap C (RatFunc C) k) := by
      ring
    have h2 : gaussRat (NormedField.valuation (K := C)) 0 s₀ (algebraMap C (RatFunc C) k) < 1 := by
      rw [this]
      exact (Valuation.map_sub _ _ _).trans_lt (max_lt h1 (hs s₀ hs₀))
    rw [gaussRat_algebraMap_C, NormedField.valuation_apply] at h2
    exact_mod_cast h2

end OverOC

/-! ### Lying over -/

section Lift

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E] [CompleteSpace E]
  {φ : E →+* C} (hφ : ∀ e, ‖φ e‖ = ‖e‖)
  {F₀ F' : Type*} [Field F₀] [Field F'] [Algebra E F₀] [Algebra C F']
  {χ : F₀ →+* F'} (hχE : ∀ e, χ (algebraMap E F₀ e) = algebraMap C F' (φ e))

include hφ hχE in
/-- **Lying over** (`C / E` algebraic, `E` complete): a valuation subring `W` of `F₀` with
`W ∩ E = O_E` is the restriction along `χ` of a valuation subring `W'` of `F'` with
`W' ∩ C = O_C`. -/
theorem exists_lift (halg : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
    (W : ValuationSubring F₀)
    (hW : W.comap (algebraMap E F₀) = (NormedField.valuation (K := E)).valuationSubring) :
    ∃ W' : ValuationSubring F', W'.comap χ = W ∧
      W'.comap (algebraMap C F') = (NormedField.valuation (K := C)).valuationSubring := by
  letI : Algebra F₀ F' := χ.toAlgebra
  obtain ⟨W', hW'⟩ := TemperedFundamentalGroups.ValuationSubring.exists_comap_eq (Ω := F') W
  refine ⟨W', hW', ?_⟩
  letI : Algebra E C := φ.toAlgebra
  have h₁ : (W'.comap (algebraMap C F')).comap (algebraMap E C) =
      (NormedField.valuation (K := E)).valuationSubring := by
    rw [ValuationSubring.comap_comap]
    have : (algebraMap C F').comp (algebraMap E C) = χ.comp (algebraMap E F₀) :=
      RingHom.ext fun e ↦ (hχE e).symm
    rw [this, ← ValuationSubring.comap_comap]
    change (W'.comap (algebraMap F₀ F')).comap _ = _
    rw [hW', hW]
  have h₂ : (NormedField.valuation (K := C)).valuationSubring.comap (algebraMap E C) =
      (NormedField.valuation (K := E)).valuationSubring := by
    ext e
    simp only [ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff,
      NormedField.valuation_apply]
    change ‖φ e‖₊ ≤ 1 ↔ ‖e‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, hφ]
  exact eq_of_comap_eq_of_completeSpace h₁ h₂

end Lift

end W10Route

end SemistableReduction
