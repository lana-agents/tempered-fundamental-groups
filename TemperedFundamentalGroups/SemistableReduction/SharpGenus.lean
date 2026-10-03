/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SpecialFibre
import TemperedFundamentalGroups.SemistableReduction.GraphCount

/-!
# The genus inequality over the Gauss point

Blueprint §9.5, G8.1, G6.7 and the sharp inequality over one Gauss point.

* **G8.1** `cut`: the residue curves over the Gauss point form a connected graph: every
  nonempty proper set `S` of extensions has an edge (a common closed point of the special fibre,
  in the chart `x` or `x⁻¹`) leaving it. Otherwise the Chinese remainder theorem in `redRing x`
  and `redRing x⁻¹` produces `e, e'` reducing to the indicator of `S`, contradicting `no_split`.
* **G6.7** `ell_add_card_sub_one_le`: `ℓ(m (x)_∞) + #{w} - 1 ≤ Σ_w ℓ_{κ(w)}(m (x̄)_∞)`: the
  reductions satisfy the gluing conditions along the edges, and `#{w} - 1` of them are
  independent (`GraphCount.add_card_sub_one_le_finrank`).
* `sum_genus_le`: **`Σ_w g(κ(w)) ≤ g(F)`** over the Gauss point.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability LatticeReduction DenseCompletion

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [Fintype (Ext C F)]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

section Split

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-- Either an edge of the chart `t` leaves `S`, or some `e ∈ intRing t` reduces to the indicator
of `S` (Chinese remainder theorem in `redRing t`). -/
lemma exists_edge_or_indicator (t : F) (hnf : ∀ w : Ext C F, ¬ IsField (proj t w).range)
    (S : Finset (Ext C F)) :
    (∃ w ∈ S, ∃ w' ∉ S, Edge C F t w w') ∨
      ∃ e ∈ intRing C F t, (∀ w ∈ S, red C e w = 1) ∧ ∀ w ∉ S, red C e w = 0 := by
  classical
  set I : Ideal (redRing C F t) := S.inf fun w ↦ RingHom.ker (proj t w)
  set J : Ideal (redRing C F t) := Sᶜ.inf fun w ↦ RingHom.ker (proj t w)
  by_cases h : I ⊔ J = ⊤
  · right
    have h1 : (1 : redRing C F t) ∈ I ⊔ J := h ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h1
    obtain ⟨e, he, hred⟩ := b.2
    have hw (w : Ext C F) :
        (b : Π v : Ext C F, ResidueField v.1.valuationSubring) w = red C e w := by
      rw [← hred]
    have hsum (w : Ext C F) := congrArg (fun r : redRing C F t ↦
      (r : Π v : Ext C F, ResidueField v.1.valuationSubring) w) hab
    refine ⟨e, he, fun w hwS ↦ ?_, fun w hwS ↦ ?_⟩
    · have h0 : proj t w a = 0 := (Finset.inf_le (f := fun w ↦ RingHom.ker (proj t w)) hwS) ha
      change (a : Π v : Ext C F, ResidueField v.1.valuationSubring) w = 0 at h0
      have := hsum w
      simp only [Subring.coe_add, Pi.add_apply, OneMemClass.coe_one, Pi.one_apply, h0,
        zero_add] at this
      rw [← hw, this]
    · have h0 : proj t w b = 0 := (Finset.inf_le (f := fun w ↦ RingHom.ker (proj t w))
        (Finset.mem_compl.2 hwS)) hb
      rw [← hw]
      exact h0
  · left
    obtain ⟨𝔫, h𝔫, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨w, hwS, hw⟩ := (h𝔫.isPrime.inf_le' (s := S)).1 (le_sup_left.trans hle)
    obtain ⟨w', hw'S, hw'⟩ := (h𝔫.isPrime.inf_le' (s := Sᶜ)).1 (le_sup_right.trans hle)
    obtain ⟨Q, hQ, hQ𝔫⟩ := exists_place_of_isMaximal t w 𝔫 hw (hnf w)
    obtain ⟨Q', hQ', hQ'𝔫⟩ := exists_place_of_isMaximal t w' 𝔫 hw' (hnf w')
    exact ⟨w, hwS, w', Finset.mem_compl.1 hw'S, Q, Q', hQ, hQ', fun a ha ↦
      (hQ𝔫 a ha).trans (hQ'𝔫 a ha).symm⟩

end Split

section Cut

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField
  isCurveFunctionField_F

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [Fintype (Ext C F)] in
lemma red_xF_ne_zero (w : Ext C F) : red C (xF C F) w ≠ 0 := by
  rw [Ne, red_eq_zero_iff (valuation_xF w).le, valuation_xF]
  exact lt_irrefl 1

omit [Fintype (Ext C F)] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma red_xF_notMem_range (w : Ext C F) :
    red C (xF C F) w ∉ (algebraMap 𝓀 (ResidueField w.1.valuationSubring)).range := by
  rintro ⟨c, hc⟩
  exact transcendental_red_x w (hc ▸ isAlgebraic_algebraMap c)

omit [Fintype (Ext C F)] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma inv_red_xF_notMem_range (w : Ext C F) :
    (red C (xF C F) w)⁻¹ ∉ (algebraMap 𝓀 (ResidueField w.1.valuationSubring)).range := by
  rintro ⟨c, hc⟩
  exact red_xF_notMem_range w ⟨c⁻¹, by rw [map_inv₀, hc, inv_inv]⟩

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]
  [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F] [Fintype (Ext C F)] in
lemma isIntegral_self_adjoin (t : F) : IsIntegral (Algebra.adjoin C {t}) t :=
  isIntegral_algebraMap (x := (⟨t, Algebra.self_mem_adjoin_singleton C t⟩ : Algebra.adjoin C {t}))

omit [IsScalarTower C (RatFunc C) F] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma xF_mem_intRing : xF C F ∈ intRing C F (xF C F) :=
  ⟨isIntegral_self_adjoin _, gnorm_le_iff.2 fun w ↦ (valuation_xF w).le⟩

omit [IsScalarTower C (RatFunc C) F] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma xF_inv_mem_intRing : (xF C F)⁻¹ ∈ intRing C F (xF C F)⁻¹ :=
  ⟨isIntegral_self_adjoin _, gnorm_le_iff.2 fun w ↦ (valuation_xF_inv w).le⟩

variable {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
include hb

lemma not_isField_x (w : Ext C F) : ¬ IsField (proj (xF C F) w).range :=
  not_isField_range _ w xF_mem_intRing (red_xF_ne_zero w) (inv_red_xF_notMem_range w)
    fun Q hQ _ ⟨_, hf, hfa⟩ ↦ hfa ▸ red_mem_of_isIntegral hb hf.2 hf.1 w Q.V Q.algebraMap_mem hQ

lemma not_isField_x_inv (w : Ext C F) : ¬ IsField (proj (xF C F)⁻¹ w).range := by
  refine not_isField_range _ w xF_inv_mem_intRing ?_ ?_ fun Q hQ _ ⟨_, hf, hfa⟩ ↦
    hfa ▸ red_mem_of_isIntegral_inv hb hf.2 hf.1 w Q.V Q.algebraMap_mem hQ
  · rw [red_inv_xF]
    exact inv_ne_zero (red_xF_ne_zero w)
  · rw [red_inv_xF, inv_inv]
    exact red_xF_notMem_range w

variable [CompleteSpace C] [CharZero C]

/-- **G8.1** (connectedness of the graph of residue curves): every nonempty proper set of
extensions of the Gauss valuation has an edge leaving it, in one of the two charts. -/
theorem cut (S : Finset (Ext C F)) (hS : S.Nonempty) (hSu : S ≠ Finset.univ) :
    ∃ w ∈ S, ∃ w' ∉ S, Edge C F (xF C F) w w' ∨ Edge C F (xF C F)⁻¹ w w' := by
  classical
  rcases exists_edge_or_indicator (xF C F) (not_isField_x hb) S with
    ⟨w, hw, w', hw', h⟩ | ⟨e, he, he1, he0⟩
  · exact ⟨w, hw, w', hw', Or.inl h⟩
  rcases exists_edge_or_indicator (xF C F)⁻¹ (not_isField_x_inv hb) S with
    ⟨w, hw, w', hw', h⟩ | ⟨e', he', he'1, he'0⟩
  · exact ⟨w, hw, w', hw', Or.inr h⟩
  exfalso
  have hle (w : Ext C F) : w.1 e ≤ 1 := valuation_le_one_of_mem_intRing he w
  have hle' (w : Ext C F) : w.1 e' ≤ 1 := valuation_le_one_of_mem_intRing he' w
  have hsub {g : F} (hg : ∀ w : Ext C F, w.1 g ≤ 1) (w : Ext C F) (h1 : red C g w = 1) :
      w.1 (g - 1) < 1 := by
    have hg1 : w.1 (g - 1) ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le (hg w) (by simp))
    rw [← red_eq_zero_iff hg1, red_sub (hg w) (by simp), h1, red_one, sub_self]
  have hzero {g : F} (hg : ∀ w : Ext C F, w.1 g ≤ 1) (w : Ext C F) (h0 : red C g w = 0) :
      w.1 g < 1 := (red_eq_zero_iff (hg w)).1 h0
  have := no_split hb he.1 he'.1 he.2 he'.2 fun w ↦ by
    by_cases hwS : w ∈ S
    · exact Or.inl ⟨hsub hle w (he1 w hwS), hsub hle' w (he'1 w hwS)⟩
    · exact Or.inr ⟨hzero hle w (he0 w hwS), hzero hle' w (he'0 w hwS)⟩
  obtain ⟨w₀, hw₀⟩ := hS
  obtain ⟨w₁, -, hw₁⟩ : ∃ w₁ ∈ Finset.univ, w₁ ∉ S := by
    by_contra! h
    exact hSu (Finset.eq_univ_of_forall fun w ↦ h w (Finset.mem_univ w))
  rcases this with h | h
  · have h1 := h w₁
    rw [← red_eq_zero_iff ((Valuation.map_sub _ _ _).trans (max_le (hle w₁) (by simp))),
      red_sub (hle w₁) (by simp), he0 w₁ hw₁, red_one, zero_sub, neg_eq_zero] at h1
    exact one_ne_zero h1
  · have h0 := h w₀
    rw [← red_eq_zero_iff (hle w₀), he1 w₀ hw₀] at h0
    exact one_ne_zero h0

end Cut

end GaussFibre

end SemistableReduction
