/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Connectedness

/-!
# The special fibre over the Gauss point: gluing conditions and connectedness

Blueprint §9.5, G6.7 and G8.1 (infrastructure). For `t ∈ {x, x⁻¹}`, the reductions of the
elements of `F` of norm `≤ 1` integral over `C[t]` form a subring `redRing t ⊆ Π_w κ(w)` (the
coordinate ring of an affine chart of the special fibre, mapped to its normalization). Two
residue curves `w, w'` are joined (`Edge`) if there are places `Q` of `κ(w)` and `Q'` of `κ(w')`
dominating the same
ideal of `redRing t` (a common closed point of the special fibre).

* `CurvePlace.res`: the residue map `O_Q → k` of a place;
* `res_eq_of_edge`: along an edge, the residues at `Q` and `Q'` of every element of `redRing t`
  agree (the gluing condition);
* `exists_place_of_isMaximal`, `not_isField_range`: maximal ideals of `redRing t` over a
  component `w` are cut out by places of `κ(w)` (input for G8.1, the cut lemma, still open).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion

namespace CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ)

open Classical in
/-- The residue map of a place (`0` outside the valuation ring). -/
noncomputable def res (y : κ) : k :=
  if h : y ∈ Q.V then Classical.choose (Q.exists_valuation_sub_lt_one h) else 0

lemma valuation_sub_res_lt_one {y : κ} (hy : y ∈ Q.V) :
    Q.valuation (y - algebraMap k κ (Q.res y)) < 1 := by
  rw [res, dif_pos hy]
  exact Classical.choose_spec (Q.exists_valuation_sub_lt_one hy)

lemma res_eq_of_valuation_sub_lt_one {y : κ} {c : k} (h : Q.valuation (y - algebraMap k κ c) < 1) :
    Q.res y = c := by
  have hy : y ∈ Q.V := by
    have : y = (y - algebraMap k κ c) + algebraMap k κ c := by ring
    rw [this]
    exact add_mem (Q.valuation_le_one_iff.1 h.le) (Q.algebraMap_mem c)
  by_contra hne
  have h1 := Q.valuation_sub_res_lt_one hy
  have h2 : Q.valuation (algebraMap k κ (c - Q.res y)) < 1 := by
    have : algebraMap k κ (c - Q.res y) = (y - algebraMap k κ (Q.res y)) -
        (y - algebraMap k κ c) := by rw [_root_.map_sub]; ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt h1 h)
  have hne' : c - Q.res y ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  rw [valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one hne'] at h2
  exact lt_irrefl _ h2

lemma res_algebraMap (c : k) : Q.res (algebraMap k κ c) = c :=
  Q.res_eq_of_valuation_sub_lt_one (by simp)

lemma res_add {y z : κ} (hy : y ∈ Q.V) (hz : z ∈ Q.V) : Q.res (y + z) = Q.res y + Q.res z := by
  refine Q.res_eq_of_valuation_sub_lt_one ?_
  have : y + z - algebraMap k κ (Q.res y + Q.res z) =
      (y - algebraMap k κ (Q.res y)) + (z - algebraMap k κ (Q.res z)) := by rw [map_add]; ring
  rw [this]
  exact (Valuation.map_add _ _ _).trans_lt
    (max_lt (Q.valuation_sub_res_lt_one hy) (Q.valuation_sub_res_lt_one hz))

lemma res_smul {y : κ} (hy : y ∈ Q.V) (c : k) : Q.res (c • y) = c * Q.res y := by
  refine Q.res_eq_of_valuation_sub_lt_one ?_
  have : c • y - algebraMap k κ (c * Q.res y) =
      algebraMap k κ c * (y - algebraMap k κ (Q.res y)) := by
    rw [Algebra.smul_def, map_mul]; ring
  rw [this, map_mul]
  exact (mul_le_of_le_one_left' (Q.valuation_algebraMap_le_one c)).trans_lt
    (Q.valuation_sub_res_lt_one hy)

end CurvePlace

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [Fintype (Ext C F)]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Rings

variable (C F) in
/-- The elements of `F` of norm `≤ 1` integral over `C[t]`. -/
def intRing (t : F) : Subring F where
  carrier := {f | IsIntegral (Algebra.adjoin C {t}) f ∧ gnorm C f ≤ 1}
  mul_mem' ha hb := ⟨ha.1.mul hb.1, (gnorm_mul_le _ _).trans (mul_le_one' ha.2 hb.2)⟩
  one_mem' := ⟨isIntegral_one, gnorm_le_iff.2 fun w ↦ by simp⟩
  add_mem' ha hb := ⟨ha.1.add hb.1, (gnorm_add_le _ _).trans (max_le ha.2 hb.2)⟩
  zero_mem' := ⟨isIntegral_zero, by simp⟩
  neg_mem' ha := ⟨ha.1.neg, by rw [gnorm_neg]; exact ha.2⟩

omit [IsScalarTower C (RatFunc C) F] in
lemma valuation_le_one_of_mem_intRing {t f : F} (hf : f ∈ intRing C F t) (w : Ext C F) :
    w.1 f ≤ 1 :=
  (le_gnorm w f).trans hf.2

variable (C F) in
/-- The reductions of `intRing t`: a subring of `Π_w κ(w)`. -/
def redRing (t : F) : Subring (Π w : Ext C F, ResidueField w.1.valuationSubring) where
  carrier := {a | ∃ f ∈ intRing C F t, (fun w ↦ red C f w) = a}
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_mem hf hg, funext fun w ↦ red_mul (valuation_le_one_of_mem_intRing hf w)
      (valuation_le_one_of_mem_intRing hg w)⟩
  one_mem' := ⟨1, one_mem _, funext fun w ↦ red_one⟩
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, add_mem hf hg, funext fun w ↦ red_add (valuation_le_one_of_mem_intRing hf w)
      (valuation_le_one_of_mem_intRing hg w)⟩
  zero_mem' := ⟨0, zero_mem _, funext fun w ↦ red_zero⟩
  neg_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, neg_mem hf, funext fun w ↦ red_neg (valuation_le_one_of_mem_intRing hf w)⟩

omit [IsScalarTower C (RatFunc C) F] in
lemma red_mem_redRing {t f : F} (hf : f ∈ intRing C F t) :
    (fun w ↦ red C f w) ∈ redRing C F t :=
  ⟨f, hf, rfl⟩

/-- The constants lie in `redRing t`. -/
lemma algebraMap_mem_redRing (t : F) (c : 𝓀) :
    (fun w : Ext C F ↦ algebraMap 𝓀 (ResidueField w.1.valuationSubring) c) ∈ redRing C F t := by
  obtain ⟨γ, rfl⟩ := residue_surjective c
  have hγ : ‖(γ : C)‖₊ ≤ 1 := by
    have := (HenselComplete.mem_integers_iff _).1 γ.2
    exact_mod_cast this
  refine ⟨algebraMap C F γ, ⟨?_, gnorm_le_iff.2 fun w ↦ ?_⟩, funext fun w ↦ ?_⟩
  · exact isIntegral_algebraMap (x := (⟨algebraMap C F γ, Subalgebra.algebraMap_mem _ _⟩ :
      Algebra.adjoin C {t}))
  · rw [valuation_algebraMap_C']
    exact hγ
  · rw [red_algebraMap_C (γ : C) hγ]

end Rings

section Edge

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

variable (C F) in
/-- `w` and `w'` are joined through `redRing t`: there are places `Q` of `κ(w)` and `Q'` of
`κ(w')` containing the images of `redRing t` whose maximal ideals cut out the same ideal of
`redRing t` (a common closed point of the chart). -/
def Edge (t : F) (w w' : Ext C F) : Prop :=
  ∃ (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring))
    (Q' : CurvePlace 𝓀 (ResidueField w'.1.valuationSubring)),
    (∀ a ∈ redRing C F t, a w ∈ Q.V) ∧ (∀ a ∈ redRing C F t, a w' ∈ Q'.V) ∧
    ∀ a ∈ redRing C F t, (Q.valuation (a w) < 1 ↔ Q'.valuation (a w') < 1)

/-- **The gluing condition**: along an edge, the residues of the elements of `redRing t` at
`Q` and at `Q'` agree. -/
lemma res_eq_of_edge {t : F} {w w' : Ext C F}
    {Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)}
    {Q' : CurvePlace 𝓀 (ResidueField w'.1.valuationSubring)}
    (hQ : ∀ a ∈ redRing C F t, a w ∈ Q.V)
    (hQQ' : ∀ a ∈ redRing C F t, (Q.valuation (a w) < 1 ↔ Q'.valuation (a w') < 1))
    {a : Π w : Ext C F, ResidueField w.1.valuationSubring} (ha : a ∈ redRing C F t) :
    Q.res (a w) = Q'.res (a w') := by
  set c := Q.res (a w)
  set b := a - fun v : Ext C F ↦ algebraMap 𝓀 (ResidueField v.1.valuationSubring) c
  have hb : b ∈ redRing C F t := sub_mem ha (algebraMap_mem_redRing t c)
  have h1 : Q.valuation (b w) < 1 := Q.valuation_sub_res_lt_one (hQ a ha)
  have h2 := (hQQ' b hb).1 h1
  exact (Q'.res_eq_of_valuation_sub_lt_one h2).symm

end Edge

section Places

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

variable (t : F) (w : Ext C F)

/-- The projection of `redRing t` to `κ(w)`. -/
noncomputable abbrev proj : redRing C F t →+* ResidueField w.1.valuationSubring :=
  (Pi.evalRingHom (fun v : Ext C F ↦ ResidueField v.1.valuationSubring) w).comp
    (redRing C F t).subtype

/-- A maximal ideal of `redRing t` containing the kernel of the projection to `κ(w)` is
dominated by a place of `κ(w)` containing the image, provided the image is not a field. -/
lemma exists_place_of_isMaximal (𝔫 : Ideal (redRing C F t)) [h𝔫 : 𝔫.IsMaximal]
    (hker : RingHom.ker (proj t w) ≤ 𝔫) (hnf : ¬ IsField (proj t w).range) :
    ∃ Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring),
      (∀ a ∈ redRing C F t, a w ∈ Q.V) ∧
      ∀ a (ha : a ∈ redRing C F t), (Q.valuation (a w) < 1 ↔ (⟨a, ha⟩ : redRing C F t) ∈ 𝔫) := by
  classical
  set A := (proj t w).range
  set φ := (proj t w).rangeRestrict
  have hφ : Function.Surjective φ := RingHom.rangeRestrict_surjective _
  have hkerφ : RingHom.ker φ ≤ 𝔫 := by rwa [RingHom.ker_rangeRestrict]
  have hmax : (𝔫.map φ).IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le hφ hkerφ
  obtain ⟨V, hAV, hV⟩ := Ideal.image_subset_nonunits_valuationSubring (𝔫.map φ) hmax.ne_top
  have hmemA (a) (ha : a ∈ redRing C F t) : a w ∈ A := ⟨⟨a, ha⟩, rfl⟩
  have hVne : V ≠ ⊤ := by
    rintro rfl
    apply hnf
    rw [Ring.isField_iff_maximal_bot]
    convert hmax
    symm
    rw [eq_bot_iff]
    intro y hy
    have : ((y : A) : ResidueField w.1.valuationSubring) ∈
        (⊤ : ValuationSubring (ResidueField w.1.valuationSubring)).nonunits := hV ⟨y, hy, rfl⟩
    rw [ValuationSubring.mem_nonunits_iff] at this
    rw [Ideal.mem_bot]
    by_contra hy0
    have hy0' : ((y : A) : ResidueField w.1.valuationSubring) ≠ 0 := fun h ↦ hy0 (Subtype.ext h)
    have h1 : (⊤ : ValuationSubring (ResidueField w.1.valuationSubring)).valuation (y : A) = 1 := by
      refine le_antisymm ((ValuationSubring.valuation_le_one_iff _ _).2 trivial) ?_
      have h2 := (ValuationSubring.valuation_le_one_iff _ _).2
        (show ((y : A) : ResidueField w.1.valuationSubring)⁻¹ ∈
          (⊤ : ValuationSubring (ResidueField w.1.valuationSubring)) from trivial)
      rw [map_inv₀] at h2
      exact (inv_le_one₀ ((Valuation.pos_iff _).2 hy0')).1 h2
    rw [h1] at this
    exact lt_irrefl _ this
  set Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring) :=
    ⟨V, fun c ↦ hAV (hmemA _ (algebraMap_mem_redRing t c)), hVne⟩
  have hdom (a) (ha : a ∈ redRing C F t) : a w ∈ Q.V := hAV (hmemA a ha)
  have hback (a) (ha : a ∈ redRing C F t) (h : (⟨a, ha⟩ : redRing C F t) ∈ 𝔫) :
      Q.valuation (a w) < 1 := by
    rw [CurvePlace.valuation_lt_one_iff, ← ValuationSubring.mem_nonunits_iff]
    exact hV ⟨φ ⟨a, ha⟩, Ideal.mem_map_of_mem φ h, rfl⟩
  refine ⟨Q, hdom, fun a ha ↦ ⟨fun h ↦ ?_, hback a ha⟩⟩
  -- the ideal cut out by `Q` contains `𝔫`, hence equals it
  let J : Ideal (redRing C F t) :=
    { carrier := {r | Q.valuation (proj t w r) < 1}
      add_mem' := fun {r s} hr hs ↦ by
        simp only [Set.mem_setOf_eq, map_add] at hr hs ⊢
        exact (Valuation.map_add _ _ _).trans_lt (max_lt hr hs)
      zero_mem' := by simp
      smul_mem' := fun c r hr ↦ by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at hr ⊢
        exact (mul_le_of_le_one_left' (Q.valuation_le_one_iff.2 (hdom _ c.2))).trans_lt hr }
  have hJ : J ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one]
    change ¬ Q.valuation 1 < 1
    simp
  have hle : 𝔫 ≤ J := fun r hr ↦ hback r r.2 hr
  have := h𝔫.eq_of_le hJ hle
  rw [this]
  exact h

end Places

section Cut

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField
  isCurveFunctionField_F

omit [FiniteDimensional (RatFunc C) F] in
/-- The image of `redRing t` in `κ(w)` is not a field, if it contains `t̄ ≠ 0` with `t̄⁻¹ ∉ k`
and lies in every place containing `t̄`. -/
lemma not_isField_range (t : F) (w : Ext C F) (ht : t ∈ intRing C F t)
    (ht0 : red C t w ≠ 0)
    (htr : (red C t w)⁻¹ ∉ (algebraMap 𝓀 (ResidueField w.1.valuationSubring)).range)
    (hdom : ∀ Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring), red C t w ∈ Q.V →
      ∀ a ∈ redRing C F t, a w ∈ Q.V) :
    ¬ IsField (proj t w).range := by
  intro hfield
  set y : (proj t w).range := ⟨red C t w, ⟨⟨_, red_mem_redRing ht⟩, rfl⟩⟩
  have hy0 : y ≠ 0 := fun h ↦ ht0 (congrArg Subtype.val h)
  obtain ⟨z, hz⟩ := hfield.mul_inv_cancel hy0
  have hz' : (z : ResidueField w.1.valuationSubring) = (red C t w)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    exact congrArg Subtype.val hz
  obtain ⟨Q, hQ⟩ := CurvePlace.exists_not_mem htr
  have hyQ : red C t w ∈ Q.V := (Q.V.mem_or_inv_mem _).resolve_right hQ
  obtain ⟨⟨a, ha⟩, haz⟩ := z.2
  have : (z : ResidueField w.1.valuationSubring) ∈ Q.V := by
    rw [← haz]
    exact hdom Q hyQ a ha
  rw [hz'] at this
  exact hQ this

end Cut

end GaussFibre

end SemistableReduction
