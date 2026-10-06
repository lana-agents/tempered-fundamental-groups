/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartTransport
import TemperedFundamentalGroups.SemistableReduction.SectionLocal

/-!
# Transport of extensions of Gauss points and of reduced charts along twists

Blueprint §9.12, O12 / R5, step (1)(a). The twists `Aff`, `Inv`, `TwoV` of a finite extension `F'`
of `C(x)` have the same underlying field with different `C(x)`-algebra structures. A ring
isomorphism `φ : F₁ ≃ F₂` over `C` and a map `ι : Ext C F₁ → Ext C F₂` with `(ι w) ∘ φ = w` induce
isomorphisms of the residue curves (`resAlgEquiv`, without any `rfl` between twisted residue
fields) and hence a `ChartLocal.CompEmb` (`extEmb`) under which reductions correspond
(`Φ_red`, `Ψ_red`). `isLocalIso_of` reduces `ChartLocal.IsLocalIso` for two reduced charts
`redRing` to statements in the fields.

Also: invariance of the genus of a function field of one variable under isomorphisms
(`genus_congr`).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

/-! ### Invariance of the genus -/

namespace CurvePlace

variable {k κ κ' : Type*} [Field k] [Field κ] [Field κ'] [Algebra k κ] [Algebra k κ']
  [IsAlgClosed k] [IsCurveFunctionField k κ] [IsCurveFunctionField k κ']

/-- Transport of divisors. -/
noncomputable def mapDiv (e : κ ≃ₐ[k] κ') (D : CurveDivisor k κ) : CurveDivisor k κ' :=
  D.mapDomain (map e)

omit [IsAlgClosed k] [IsCurveFunctionField k κ] [IsCurveFunctionField k κ'] in
lemma mapDiv_apply (e : κ ≃ₐ[k] κ') (D : CurveDivisor k κ) (Q : CurvePlace k κ) :
    mapDiv e D (Q.map e) = D Q :=
  Finsupp.mapDomain_apply (map_injective e) D Q

omit [IsAlgClosed k] [IsCurveFunctionField k κ] [IsCurveFunctionField k κ'] in
lemma mapDiv_apply' (e : κ ≃ₐ[k] κ') (D : CurveDivisor k κ) (Q' : CurvePlace k κ') :
    mapDiv e D Q' = D (Q'.map e.symm) := by
  conv_lhs => rw [← map_map_symm e Q']
  exact mapDiv_apply e D _

omit [IsAlgClosed k] [IsCurveFunctionField k κ] [IsCurveFunctionField k κ'] in
lemma degree_mapDiv (e : κ ≃ₐ[k] κ') (D : CurveDivisor k κ) :
    (mapDiv e D).degree = D.degree := by
  rw [mapDiv, Finsupp.degree_mapDomain]

lemma mem_rrSpace_mapDiv (e : κ ≃ₐ[k] κ') (D : CurveDivisor k κ) (f : κ') :
    f ∈ rrSpace (mapDiv e D) ↔ e.symm f ∈ rrSpace D := by
  constructor
  · intro h Q
    have := h (Q.map e)
    rwa [mapDiv_apply, valuation_map] at this
  · intro h Q'
    rw [mapDiv_apply', ← map_map_symm e Q', valuation_map, map_map_symm]
    exact h _

lemma ell_mapDiv (e : κ ≃ₐ[k] κ') (D : CurveDivisor k κ) : ell (mapDiv e D) = ell D := by
  have h : rrSpace (mapDiv e D) = (rrSpace D).map e.toLinearEquiv.toLinearMap := by
    ext f
    rw [mem_rrSpace_mapDiv, Submodule.mem_map_equiv]
    rfl
  rw [ell, ell, h, LinearEquiv.finrank_map_eq]

lemma riemannDefect_mapDiv (e : κ ≃ₐ[k] κ') (D : CurveDivisor k κ) :
    riemannDefect (mapDiv e D) = riemannDefect D := by
  rw [riemannDefect, riemannDefect, degree_mapDiv, ell_mapDiv]

/-- **The genus is invariant under isomorphisms.** -/
theorem genus_congr (e : κ ≃ₐ[k] κ') : genus k κ' = genus k κ := by
  have h : (⨆ D : CurveDivisor k κ', riemannDefect D) =
      ⨆ D : CurveDivisor k κ, riemannDefect D := by
    refine le_antisymm (ciSup_le fun D' ↦ ?_) (ciSup_le fun D ↦ ?_)
    · have := riemannDefect_mapDiv e.symm D'
      rw [← this]
      exact le_ciSup bddAbove_riemannDefect _
    · rw [← riemannDefect_mapDiv e D]
      exact le_ciSup bddAbove_riemannDefect _
  rw [genus, genus, h]

end CurvePlace

/-! ### Residue fields along ring isomorphisms -/

namespace GaussFibre

open ChartLocal DeltaCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F₁ F₂ : Type*} [Field F₁] [Field F₂]

/-- The valuation subrings of corresponding valuations are isomorphic. -/
def vsEquiv (φ : F₁ ≃+* F₂) {w₁ : Valuation F₁ ℝ≥0} {w₂ : Valuation F₂ ℝ≥0}
    (h : ∀ x, w₂ (φ x) = w₁ x) : w₁.valuationSubring ≃+* w₂.valuationSubring where
  toFun x := ⟨φ x, by
    change w₂ (φ x) ≤ 1
    rw [h]; exact x.2⟩
  invFun y := ⟨φ.symm y, by
    change w₁ (φ.symm y) ≤ 1
    rw [← h, RingEquiv.apply_symm_apply]; exact y.2⟩
  left_inv x := Subtype.ext (φ.symm_apply_apply x.1)
  right_inv y := Subtype.ext (φ.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul φ x.1 y.1)
  map_add' x y := Subtype.ext (map_add φ x.1 y.1)

/-- The residue fields of corresponding valuations are isomorphic. -/
noncomputable def resEquiv (φ : F₁ ≃+* F₂) {w₁ : Valuation F₁ ℝ≥0} {w₂ : Valuation F₂ ℝ≥0}
    (h : ∀ x, w₂ (φ x) = w₁ x) :
    ResidueField w₁.valuationSubring ≃+* ResidueField w₂.valuationSubring :=
  ResidueField.mapEquiv (vsEquiv φ h)

lemma resEquiv_residue (φ : F₁ ≃+* F₂) {w₁ : Valuation F₁ ℝ≥0} {w₂ : Valuation F₂ ℝ≥0}
    (h : ∀ x, w₂ (φ x) = w₁ x) (x : w₁.valuationSubring) :
    resEquiv φ h (residue _ x) = residue _ (vsEquiv φ h x) :=
  ResidueField.map_residue _ _

variable [Algebra (RatFunc C) F₁] [Algebra (RatFunc C) F₂]

lemma resEquiv_red (φ : F₁ ≃+* F₂) {w₁ : Ext C F₁} {w₂ : Ext C F₂}
    (h : ∀ x, w₂.1 (φ x) = w₁.1 x) (f : F₁) : resEquiv φ h (red C f w₁) = red C (φ f) w₂ := by
  by_cases hf : w₁.1 f ≤ 1
  · rw [red_of_le hf, red_of_le (by rw [h]; exact hf), resEquiv_residue]
    rfl
  · have hf' : ¬ w₂.1 (φ f) ≤ 1 := by rw [h]; exact hf
    rw [red, dif_neg hf, red, dif_neg hf', map_zero]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable [Algebra C F₁] [IsScalarTower C (RatFunc C) F₁] [Algebra C F₂]
  [IsScalarTower C (RatFunc C) F₂]

/-- The residue curves of corresponding extensions are isomorphic over `k`. -/
noncomputable def resAlgEquiv (φ : F₁ ≃+* F₂) (hφC : ∀ c : C, φ (algebraMap C F₁ c) =
    algebraMap C F₂ c) {w₁ : Ext C F₁} {w₂ : Ext C F₂} (h : ∀ x, w₂.1 (φ x) = w₁.1 x) :
    ResidueField w₁.1.valuationSubring ≃ₐ[𝓀] ResidueField w₂.1.valuationSubring :=
  AlgEquiv.ofRingEquiv (f := resEquiv φ h) fun r ↦ by
    obtain ⟨β, rfl⟩ := residue_surjective r
    have hβ : ‖(β : C)‖₊ ≤ 1 := by
      have := (HenselComplete.mem_integers_iff _).1 β.2
      exact_mod_cast this
    have h1 := red_algebraMap_C (F := F₁) (w := w₁) (β : C) hβ
    have h2 := red_algebraMap_C (F := F₂) (w := w₂) (β : C) hβ
    rw [← h1, ← h2, resEquiv_red, hφC]

lemma resAlgEquiv_red (φ : F₁ ≃+* F₂) (hφC : ∀ c : C, φ (algebraMap C F₁ c) =
    algebraMap C F₂ c) {w₁ : Ext C F₁} {w₂ : Ext C F₂} (h : ∀ x, w₂.1 (φ x) = w₁.1 x) (f : F₁) :
    resAlgEquiv φ hφC h (red C f w₁) = red C (φ f) w₂ :=
  resEquiv_red φ h f

/-- **The embedding of components** induced by `φ` and `ι : Ext C F₁ → Ext C F₂` with
`(ι w) ∘ φ = w`. -/
noncomputable def extEmb (φ : F₁ ≃+* F₂) (hφC : ∀ c : C, φ (algebraMap C F₁ c) =
    algebraMap C F₂ c) (ι : Ext C F₁ → Ext C F₂) (hι : ∀ w x, (ι w).1 (φ x) = w.1 x) :
    CompEmb 𝓀 (fun w : Ext C F₁ ↦ ResidueField w.1.valuationSubring)
      (fun w : Ext C F₂ ↦ ResidueField w.1.valuationSubring) where
  ι := ι
  inj w w' hw := by
    refine Subtype.ext (Valuation.ext fun x ↦ ?_)
    rw [← hι w x, ← hι w' x, hw]
  e w := resAlgEquiv φ hφC (hι w)

variable (φ : F₁ ≃+* F₂) (hφC : ∀ c : C, φ (algebraMap C F₁ c) = algebraMap C F₂ c)
  (ι : Ext C F₁ → Ext C F₂) (hι : ∀ w x, (ι w).1 (φ x) = w.1 x)

lemma extEmb_ι : (extEmb φ hφC ι hι).ι = ι := rfl

lemma extEmb_e_red (w : Ext C F₁) (f : F₁) :
    (extEmb φ hφC ι hι).e w (red C f w) = red C (φ f) (ι w) :=
  resEquiv_red φ (hι w) f

/-- `Φ` of a reduction is the reduction of the image, if the latter vanishes off the image. -/
lemma Φ_red (f : F₁) (hoff : ∀ w', (¬ ∃ w, ι w = w') → red C (φ f) w' = 0) :
    (extEmb φ hφC ι hι).Φ (fun w ↦ red C f w) = fun w' ↦ red C (φ f) w' :=
  (extEmb φ hφC ι hι).Φ_ext (fun w ↦ extEmb_e_red φ hφC ι hι w f) hoff

lemma Ψ_red (g : F₂) :
    (extEmb φ hφC ι hι).Ψ (fun w' ↦ red C g w') = fun w ↦ red C (φ.symm g) w := by
  funext w
  change ((extEmb φ hφC ι hι).e w).symm (red C g (ι w)) = _
  rw [AlgEquiv.symm_apply_eq, extEmb_e_red, RingEquiv.apply_symm_apply]

section LocalIso

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F₁] [FiniteDimensional (RatFunc C) F₂]
  [Fintype (Ext C F₁)] [Fintype (Ext C F₂)]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-- **Reduced charts which agree after inverting `U₁`, `U₂`**, in terms of the fields. -/
theorem isLocalIso_of {z₁ : F₁} {z₂ : F₂}
    (hΛ₁ : IsChart 𝓀 (fun w : Ext C F₁ ↦ red C z₁ w) (redRing C F₁ z₁))
    (hΛ₂ : IsChart 𝓀 (fun w : Ext C F₂ ↦ red C z₂ w) (redRing C F₂ z₂))
    {U₁ : F₁} {U₂ : F₂} (hU₁ : U₁ ∈ intRing C F₁ z₁) (hU₂ : U₂ ∈ intRing C F₂ z₂)
    (hfwd : ∀ f ∈ intRing C F₁ z₁, ∃ N : ℕ, U₂ ^ N * φ f ∈ intRing C F₂ z₂ ∧
      ∀ w', (¬ ∃ w, ι w = w') → w'.1 (U₂ ^ N * φ f) < 1)
    (hbwd : ∀ g ∈ intRing C F₂ z₂, ∃ N : ℕ, U₁ ^ N * φ.symm g ∈ intRing C F₁ z₁)
    (hunit : ∀ (w : Ext C F₁) (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)),
      red C z₁ w ∈ Q.V → Q.valuation (red C U₁ w) = 1 →
        Q.valuation (red C (φ.symm U₂) w) = 1)
    (hunit' : ∀ (w' : Ext C F₂) (Q : CurvePlace 𝓀 (ResidueField w'.1.valuationSubring)),
      red C z₂ w' ∈ Q.V → Q.valuation (red C U₂ w') = 1 →
        (∃ w, ι w = w') ∧ Q.valuation (red C (φ U₁) w') = 1) :
    IsLocalIso hΛ₁ hΛ₂ (extEmb φ hφC ι hι) (fun w ↦ red C U₁ w) (fun w' ↦ red C U₂ w') where
  mem_u := red_mem_redRing hU₁
  mem_u' := red_mem_redRing hU₂
  fwd := by
    rintro _ ⟨f, hf, rfl⟩
    obtain ⟨N, hN, hoff⟩ := hfwd f hf
    refine ⟨N, ⟨_, hN, funext fun w' ↦ ?_⟩⟩
    have hU₂w := valuation_le_one_of_mem_intRing hU₂ w'
    by_cases h : ∃ w, ι w = w'
    · obtain ⟨w, rfl⟩ := h
      have hf' : (ι w).1 (φ f) ≤ 1 := by rw [hι]; exact valuation_le_one_of_mem_intRing hf w
      rw [Pi.mul_apply, Pi.pow_apply,
        red_mul (by rw [map_pow]; exact pow_le_one₀ zero_le hU₂w) hf', red_pow hU₂w]
      change _ = _ * (extEmb φ hφC ι hι).Φ _ ((extEmb φ hφC ι hι).ι w)
      rw [CompEmb.Φ_apply, extEmb_e_red]
      rfl
    · rw [Pi.mul_apply, CompEmb.Φ_apply_of_not _ h, mul_zero,
        (red_eq_zero_iff (valuation_le_one_of_mem_intRing hN w')).2 (hoff w' h)]
  bwd := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨N, hN⟩ := hbwd g hg
    refine ⟨N, ⟨_, hN, funext fun w ↦ ?_⟩⟩
    have hU₁w := valuation_le_one_of_mem_intRing hU₁ w
    have hg' : w.1 (φ.symm g) ≤ 1 := by
      rw [← hι w, RingEquiv.apply_symm_apply]; exact valuation_le_one_of_mem_intRing hg (ι w)
    rw [Ψ_red, Pi.mul_apply, Pi.pow_apply,
      red_mul (by rw [map_pow]; exact pow_le_one₀ zero_le hU₁w) hg', red_pow hU₁w]
  unit := by
    rintro ⟨w, Q⟩ hz hu
    rw [Ψ_red]
    exact hunit w Q hz hu
  unit' := by
    rintro ⟨w', Q⟩ hz hu
    obtain ⟨⟨w, rfl⟩, h⟩ := hunit' w' Q hz hu
    change Q.valuation ((extEmb φ hφC ι hι).Φ _ ((extEmb φ hφC ι hι).ι w)) = 1
    rw [CompEmb.Φ_apply, extEmb_e_red]
    exact h

end LocalIso

/-! ### The genus formula with intrinsic local `δ`-invariants -/

section Formula

open FundamentalInequality GaussStability LatticeReduction

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [Fintype (Ext C F)]
  {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
  (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F)

attribute [local instance] isCurveFunctionField isCurveFunctionField_F
  DiscreteCoefficients.isAlgClosed_residueField

variable (F) in
/-- The total `δ` of the chart at `0` over a set of closed points. -/
noncomputable def tot0
    (hΛ : IsChart 𝓀 (fun w : Ext C F ↦ red C (xF C F) w) (redRing C F (xF C F)))
    (P : Ideal (redRing C F (xF C F)) → Prop) : ℕ :=
  ∑ᶠ (𝔫 : Ideal (redRing C F (xF C F))) (_ : 𝔫 ∈ {𝔫 | 𝔫.IsMaximal ∧ P 𝔫}),
    dinf 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) hΛ 𝔫

variable (F) in
/-- The total `δ` of the chart at `∞` over a set of closed points. -/
noncomputable def totI
    (hΛ : IsChart 𝓀 (fun w : Ext C F ↦ red C (xF C F)⁻¹ w) (redRing C F (xF C F)⁻¹))
    (P : Ideal (redRing C F (xF C F)⁻¹) → Prop) : ℕ :=
  ∑ᶠ (𝔫 : Ideal (redRing C F (xF C F)⁻¹)) (_ : 𝔫 ∈ {𝔫 | 𝔫.IsMaximal ∧ P 𝔫}),
    dinf 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) hΛ 𝔫

include hsum in
open Classical in
/-- **The genus formula with intrinsic local `δ`-invariants** (S7⁺):
`g(F) + #{w} - 1 = Σ_w g(κ(w)) + Σ_{y finite} δ_y + Σ_{y over x̄ = ∞} δ_y`. -/
theorem genus_eq_tot [CharZero C] :
    (genus C F : ℤ) + Fintype.card (Ext C F) - 1 =
      (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) +
        (tot0 F (isChart_x hb) fun _ ↦ True : ℕ) +
        (totI F (isChart_x_inv hb) fun 𝔫 ↦
          (⟨_, (isChart_x_inv hb).mem⟩ : redRing C F (xF C F)⁻¹) ∈ 𝔫 : ℕ) := by
  obtain ⟨σ₀, hσ₀, hσ₀0, hσ₀c⟩ := exists_conductor_x hb hsum
  obtain ⟨σi, hσi, hσi0, hσic⟩ := exists_conductor_x_inv hb hsum
  obtain ⟨M₀, hM₀⟩ := genus_eq_sum_delta_of_conductor hb hsum hσ₀ hσ₀0 hσ₀c hσi hσi0 hσic
  set hΛ₀ := isChart_x hb
  set hΛi := isChart_x_inv hb
  set Pi : Ideal (redRing C F (xF C F)⁻¹) → Prop :=
    fun 𝔫 ↦ (⟨_, hΛi.mem⟩ : redRing C F (xF C F)⁻¹) ∈ 𝔫
  have hG : 0 ≤ ∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ) :=
    Finset.sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
  set B := (genus C F : ℕ) + Fintype.card (Ext C F)
  have hB₀ (M : ℕ) (hM : M₀ ≤ M) :
      ∑ y ∈ (points hΛ₀ σ₀).filter (fun _ ↦ True), delta 𝓀 _ hΛ₀ σ₀ y M ≤ B := by
    have h := hM₀ M hM
    rw [Finset.filter_true_of_mem fun _ _ ↦ trivial]
    have h1 : (0 : ℤ) ≤ ∑ y ∈ (points hΛi σi).filter (fun y ↦ (⟨_, hΛi.mem⟩ :
        redRing C F (xF C F)⁻¹) ∈ y), (delta 𝓀 _ hΛi σi y M : ℤ) :=
      Finset.sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
    have h2 : ((∑ y ∈ points hΛ₀ σ₀, delta 𝓀 _ hΛ₀ σ₀ y M : ℕ) : ℤ) ≤ B := by
      push_cast; simp only [B]; push_cast; linarith
    exact_mod_cast h2
  have hBi (M : ℕ) (hM : M₀ ≤ M) :
      ∑ y ∈ (points hΛi σi).filter Pi, delta 𝓀 _ hΛi σi y M ≤ B := by
    have h := hM₀ M hM
    have h1 : (0 : ℤ) ≤ ∑ y ∈ points hΛ₀ σ₀, (delta 𝓀 _ hΛ₀ σ₀ y M : ℤ) :=
      Finset.sum_nonneg fun _ _ ↦ Int.natCast_nonneg _
    have h2 : ((∑ y ∈ (points hΛi σi).filter Pi, delta 𝓀 _ hΛi σi y M : ℕ) : ℤ) ≤ B := by
      push_cast; simp only [B, Pi]; push_cast; linarith
    exact_mod_cast h2
  obtain ⟨M₁, hM₁⟩ := exists_forall_dl_eq_dinf hΛ₀ hσ₀ hσ₀0 hσ₀c (fun _ ↦ True) hB₀
  obtain ⟨M₂, hM₂⟩ := exists_forall_dl_eq_dinf hΛi hσi hσi0 hσic Pi hBi
  set M := max (max M₀ M₁) M₂
  have h := hM₀ M ((le_max_left _ _).trans (le_max_left _ _))
  have e₀ : ∑ y ∈ points hΛ₀ σ₀, delta 𝓀 _ hΛ₀ σ₀ y M = tot0 F hΛ₀ fun _ ↦ True := by
    have := sum_delta_eq_finsum hΛ₀ hσ₀ hσ₀0 hσ₀c (fun _ ↦ True) M
    rw [Finset.filter_true_of_mem fun _ _ ↦ trivial] at this
    rw [this, tot0]
    exact finsum_mem_congr rfl fun 𝔫 h𝔫 ↦
      hM₁ M ((le_max_right _ _).trans (le_max_left _ _)) 𝔫 h𝔫.1 trivial
  have ei : ∑ y ∈ (points hΛi σi).filter Pi, delta 𝓀 _ hΛi σi y M = totI F hΛi Pi := by
    rw [sum_delta_eq_finsum hΛi hσi hσi0 hσic Pi M, totI]
    exact finsum_mem_congr rfl fun 𝔫 h𝔫 ↦ hM₂ M (le_max_right _ _) 𝔫 h𝔫.1 h𝔫.2
  rw [h]
  have e₀' := congrArg (fun n : ℕ ↦ (n : ℤ)) e₀
  have ei' := congrArg (fun n : ℕ ↦ (n : ℤ)) ei
  push_cast at e₀' ei'
  rw [e₀', ← ei']

end Formula

end GaussFibre

end SemistableReduction
