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

namespace CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ)

/-- An element of `L(m (y)_∞)` is regular at the places where `y` is. -/
lemma mem_V_of_mem_rrSpace {m : ℕ} {y a : κ} (hy : y ∈ Q.V)
    (ha : a ∈ rrSpace (m • poleDivisor k y)) : a ∈ Q.V := by
  refine Q.valuation_le_one_iff.1 ((ha Q).trans ?_)
  rw [Finsupp.smul_apply, poleDivisor_apply, Q.poleOrder_eq_zero_iff.2 hy, Nat.cast_zero,
    smul_zero, exp_zero]

/-- For `a ∈ L(m (y)_∞)`, `a / yᵐ` is regular at the places where `1/y` is. -/
lemma mul_inv_pow_mem_V {m : ℕ} {y a : κ} (hy : y⁻¹ ∈ Q.V)
    (ha : a ∈ rrSpace (m • poleDivisor k y)) : a * y⁻¹ ^ m ∈ Q.V := by
  refine Q.valuation_le_one_iff.1 ?_
  have haQ := ha Q
  rw [Finsupp.smul_apply, poleDivisor_apply, nsmul_eq_mul] at haQ
  rw [map_mul, map_pow]
  by_cases hyQ : y ∈ Q.V
  · rw [Q.poleOrder_eq_zero_iff.2 hyQ, Nat.cast_zero, mul_zero, exp_zero] at haQ
    exact mul_le_one' haQ (pow_le_one₀ zero_le (Q.valuation_le_one_iff.2 hy))
  · rw [map_inv₀, Q.valuation_eq_exp_poleOrder hyQ, ← exp_neg, ← exp_nsmul]
    calc Q.valuation a * exp (m • -(Q.poleOrder y : ℤ)) ≤
        exp (m * Q.poleOrder y : ℤ) * exp (m • -(Q.poleOrder y : ℤ)) := by gcongr
      _ = 1 := by rw [← exp_add, smul_neg, nsmul_eq_mul, add_neg_cancel, exp_zero]

lemma one_mem_rrSpace_nsmul (m : ℕ) (y : κ) : (1 : κ) ∈ rrSpace (m • poleDivisor k y) := by
  intro P
  rw [map_one, ← exp_zero, exp_le_exp, Finsupp.smul_apply, poleDivisor_apply]
  positivity

lemma pow_mem_rrSpace_nsmul (m : ℕ) (y : κ) : y ^ m ∈ rrSpace (m • poleDivisor k y) := by
  intro P
  rw [map_pow, Finsupp.smul_apply, poleDivisor_apply, exp_nsmul]
  exact pow_le_pow_left₀ zero_le (P.valuation_le_exp_poleOrder y) m

lemma res_zero : Q.res (0 : κ) = 0 := by
  simpa using Q.res_algebraMap 0

lemma res_one : Q.res (1 : κ) = 1 := by
  simpa using Q.res_algebraMap 1

end CurvePlace

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

section Glue

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField
  isCurveFunctionField_F

/-- The gluing functional `a ↦ res_Q(a_w τ_w) - res_{Q'}(a_{w'} τ_{w'})` on `Π_w L(m (x̄)_∞)`. -/
noncomputable def glue (m : ℕ) (τ : Π w : Ext C F, ResidueField w.1.valuationSubring)
    {w w' : Ext C F} (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring))
    (Q' : CurvePlace 𝓀 (ResidueField w'.1.valuationSubring))
    (hQ : ∀ a ∈ piRR C F m, a w * τ w ∈ Q.V) (hQ' : ∀ a ∈ piRR C F m, a w' * τ w' ∈ Q'.V) :
    Module.Dual 𝓀 (piRR C F m) where
  toFun a := Q.res (a.1 w * τ w) - Q'.res (a.1 w' * τ w')
  map_add' a b := by
    simp only [Submodule.coe_add, Pi.add_apply, add_mul]
    rw [Q.res_add (hQ _ a.2) (hQ _ b.2), Q'.res_add (hQ' _ a.2) (hQ' _ b.2)]
    ring
  map_smul' c a := by
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_mul_assoc, RingHom.id_apply,
      smul_eq_mul]
    rw [Q.res_smul (hQ _ a.2), Q'.res_smul (hQ' _ a.2)]
    ring

omit [Fintype (Ext C F)] in
lemma glue_apply (m : ℕ) (τ : Π w : Ext C F, ResidueField w.1.valuationSubring)
    {w w' : Ext C F} (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring))
    (Q' : CurvePlace 𝓀 (ResidueField w'.1.valuationSubring)) (hQ hQ')
    (a : piRR C F m) :
    glue m τ Q Q' hQ hQ' a = Q.res (a.1 w * τ w) - Q'.res (a.1 w' * τ w') := rfl

variable (C F) in
/-- The span of the reductions of `{f ∈ L(m (x)_∞) | ‖f‖ ≤ 1}` in `Π_w L(m (x̄)_∞)`. -/
noncomputable def redSpan (m : ℕ) : Submodule 𝓀 (piRR C F m) :=
  Submodule.span 𝓀 {a | ∃ f ∈ rrSpace (m • poleDivisor C (xF C F)), gnorm C f ≤ 1 ∧
    a.1 = fun w ↦ red C f w}

variable (C F) in
/-- Two distinct residue curves meeting in one of the charts. -/
def Adj (w w' : Ext C F) : Prop :=
  w ≠ w' ∧ (Edge C F (xF C F) w w' ∨ Edge C F (xF C F)⁻¹ w w')

/-- **G6.7** (one gluing condition): along an edge there is a functional vanishing on the
reductions, with a test vector supported at the second vertex. -/
lemma exists_glue (m : ℕ) {w w' : Ext C F} (h : Adj C F w w') :
    ∃ (φ : Module.Dual 𝓀 (piRR C F m)) (tv : piRR C F m), (∀ a ∈ redSpan C F m, φ a = 0) ∧
      φ tv ≠ 0 ∧ (∀ a : piRR C F m, a.1 w = 0 → a.1 w' = 0 → φ a = 0) ∧
      ∀ v, v ≠ w' → tv.1 v = 0 := by
  classical
  obtain ⟨hne, hE | hE⟩ := h
  · -- the chart `x`, no twist
    obtain ⟨Q, Q', hQ, hQ', hQQ'⟩ := hE
    have hx : red C (xF C F) w ∈ Q.V := hQ _ (red_mem_redRing xF_mem_intRing)
    have hx' : red C (xF C F) w' ∈ Q'.V := hQ' _ (red_mem_redRing xF_mem_intRing)
    set τ : Π v : Ext C F, ResidueField v.1.valuationSubring := fun _ ↦ 1
    have hm (a) (ha : a ∈ piRR C F m) : a w * τ w ∈ Q.V := by
      rw [mul_one]
      exact Q.mem_V_of_mem_rrSpace hx (ha w trivial)
    have hm' (a) (ha : a ∈ piRR C F m) : a w' * τ w' ∈ Q'.V := by
      rw [mul_one]
      exact Q'.mem_V_of_mem_rrSpace hx' (ha w' trivial)
    have htv : (Pi.single w' 1 : Π v : Ext C F, ResidueField v.1.valuationSubring) ∈
        piRR C F m := fun v _ ↦ by
      by_cases hv : v = w'
      · subst hv
        rw [Pi.single_eq_same]
        exact CurvePlace.one_mem_rrSpace_nsmul m _
      · rw [Pi.single_eq_of_ne hv]
        exact zero_mem _
    refine ⟨glue m τ Q Q' hm hm', ⟨_, htv⟩, fun a ha ↦ ?_, ?_, fun a h1 h2 ↦ ?_, fun v hv ↦ ?_⟩
    · refine (Submodule.span_le (p := LinearMap.ker (glue m τ Q Q' hm hm'))).2 ?_ ha
      rintro _ ⟨f, hf, hn, hfa⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, glue_apply, hfa]
      simp only [τ, mul_one, sub_eq_zero]
      exact res_eq_of_edge hQ hQQ' (red_mem_redRing ⟨isIntegral_of_mem_rrSpace hf, hn⟩)
    · rw [glue_apply]
      simp only [τ, Pi.single_eq_of_ne hne, Pi.single_eq_same, zero_mul, one_mul,
        CurvePlace.res_zero, CurvePlace.res_one, zero_sub, ne_eq, neg_eq_zero, one_ne_zero,
        not_false_eq_true]
    · rw [glue_apply, h1, h2, zero_mul, zero_mul, CurvePlace.res_zero, CurvePlace.res_zero,
        sub_zero]
    · exact Pi.single_eq_of_ne hv _
  · -- the chart `x⁻¹`, twisted by `x̄⁻ᵐ`
    obtain ⟨Q, Q', hQ, hQ', hQQ'⟩ := hE
    set τ : Π v : Ext C F, ResidueField v.1.valuationSubring :=
      fun v ↦ (red C (xF C F) v)⁻¹ ^ m
    have hx : (red C (xF C F) w)⁻¹ ∈ Q.V := by
      rw [← red_inv_xF]
      exact hQ _ (red_mem_redRing xF_inv_mem_intRing)
    have hx' : (red C (xF C F) w')⁻¹ ∈ Q'.V := by
      rw [← red_inv_xF]
      exact hQ' _ (red_mem_redRing xF_inv_mem_intRing)
    have hm (a) (ha : a ∈ piRR C F m) : a w * τ w ∈ Q.V :=
      Q.mul_inv_pow_mem_V hx (ha w trivial)
    have hm' (a) (ha : a ∈ piRR C F m) : a w' * τ w' ∈ Q'.V :=
      Q'.mul_inv_pow_mem_V hx' (ha w' trivial)
    have htv : (Pi.single w' (red C (xF C F) w' ^ m) :
        Π v : Ext C F, ResidueField v.1.valuationSubring) ∈ piRR C F m := fun v _ ↦ by
      by_cases hv : v = w'
      · subst hv
        rw [Pi.single_eq_same]
        exact CurvePlace.pow_mem_rrSpace_nsmul m _
      · rw [Pi.single_eq_of_ne hv]
        exact zero_mem _
    refine ⟨glue m τ Q Q' hm hm', ⟨_, htv⟩, fun a ha ↦ ?_, ?_, fun a h1 h2 ↦ ?_, fun v hv ↦ ?_⟩
    · refine (Submodule.span_le (p := LinearMap.ker (glue m τ Q Q' hm hm'))).2 ?_ ha
      rintro _ ⟨f, hf, hn, hfa⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, glue_apply, hfa, sub_eq_zero]
      have hfw (v : Ext C F) : v.1 f ≤ 1 := (le_gnorm v f).trans hn
      have hxw (v : Ext C F) : v.1 ((xF C F)⁻¹ ^ m) ≤ 1 := by
        rw [map_pow, valuation_xF_inv, one_pow]
      have hred (v : Ext C F) : red C f v * τ v = red C (f * (xF C F)⁻¹ ^ m) v := by
        rw [red_mul (hfw v) (hxw v), red_pow (valuation_xF_inv v).le, red_inv_xF]
      have hint : f * (xF C F)⁻¹ ^ m ∈ intRing C F (xF C F)⁻¹ :=
        ⟨isIntegral_div_of_mem_rrSpace hf,
          (gnorm_mul_le _ _).trans (mul_le_one' hn (gnorm_xF_inv_pow m))⟩
      simp only [hred]
      exact res_eq_of_edge hQ hQQ' (red_mem_redRing hint)
    · rw [glue_apply]
      have hx0 : red C (xF C F) w' ≠ 0 := red_xF_ne_zero w'
      simp only [Pi.single_eq_of_ne hne, Pi.single_eq_same, zero_mul, τ, ← mul_pow,
        mul_inv_cancel₀ hx0, one_pow, CurvePlace.res_zero, CurvePlace.res_one, zero_sub,
        ne_eq, neg_eq_zero, one_ne_zero, not_false_eq_true]
    · rw [glue_apply, h1, h2, zero_mul, zero_mul, CurvePlace.res_zero, CurvePlace.res_zero,
        sub_zero]
    · exact Pi.single_eq_of_ne hv _

end Glue

section Sharp

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] [CompleteSpace C] [CharZero C]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField
  isCurveFunctionField_F

variable {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
include hb

/-- **G6.7** (counting with gluing conditions):
`ℓ(m (x)_∞) + #{w} - 1 ≤ Σ_w ℓ_{κ(w)}(m (x̄)_∞)`. -/
theorem ell_add_card_sub_one_le (m : ℕ) :
    ell (m • poleDivisor C (xF C F)) + (Fintype.card (Ext C F) - 1) ≤
      ∑ w : Ext C F, ell (m • poleDivisor 𝓀 (red C (xF C F) w)) := by
  classical
  haveI := nonempty_ext_of_orthonormal hb
  choose! φ tv hφW hφt hφsupp htv using fun (w w' : Ext C F) (h : Adj C F w w') ↦
    exists_glue (C := C) m h
  have hcount := GraphCount.add_card_sub_one_le_finrank (redSpan C F m) (Adj C F)
    (fun S hS hSu ↦ by
      obtain ⟨w, hw, w', hw', h⟩ := cut hb S hS hSu
      exact ⟨w, hw, w', hw', fun h' ↦ hw' (h' ▸ hw), h⟩)
    φ tv hφW hφt fun i j i' j' hij hij' h1 h2 ↦
      hφsupp i j hij _ (htv i' j' hij' i (Ne.symm h1)) (htv i' j' hij' j (Ne.symm h2))
  rw [← finrank_piRR]
  refine le_trans (Nat.add_le_add_right ?_ _) hcount
  set W := (redSpan C F m).map (piRR C F m).subtype
  have hW : Module.finrank 𝓀 W = Module.finrank 𝓀 (redSpan C F m) :=
    (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq.symm
  rw [← hW]
  exact finrank_le_of_red_mem b hb (rrSpace (m • poleDivisor C (xF C F))) W
    fun f hf hn ↦ ⟨⟨_, fun w _ ↦ red_mem_rrSpace hb hf hn w⟩,
      Submodule.subset_span ⟨f, hf, hn, rfl⟩, rfl⟩

/-- **The genus inequality over the Gauss point**: `Σ_w g(κ(w)) ≤ g(F)`, the sum over the
extensions `w` of the Gauss valuation `w_{0,1}` of `C(X)` to `F` (`C` complete, algebraically
closed of characteristic `0`; `F` with an orthonormal `C(X)`-basis, e.g. by W4). -/
theorem sum_genus_le
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F) :
    (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) ≤ genus C F := by
  classical
  haveI := nonempty_ext_of_orthonormal hb
  obtain ⟨cF, hcF⟩ := ell_eq_of_le_degree (k := C) (κ := F)
  choose cw hcw using fun w : Ext C F ↦
    ell_eq_of_le_degree (k := 𝓀) (κ := ResidueField w.1.valuationSubring)
  set N := Module.finrank (RatFunc C) F
  set m : ℕ := cF.toNat + ∑ w, (cw w).toNat
  have hN : 1 ≤ N := Module.finrank_pos
  have hdegF : (m • poleDivisor C (xF C F)).degree = m * N := by
    rw [map_nsmul, degree_poleDivisor xF_notMem_range, finrank_adjoin_xF, nsmul_eq_mul]
  have hfw (w : Ext C F) : 1 ≤ inertiaDeg (gauss1 C) w.1 := by
    haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := finite_residueField
    exact Module.finrank_pos
  have hdegw (w : Ext C F) : (m • poleDivisor 𝓀 (red C (xF C F) w)).degree =
      m * inertiaDeg (gauss1 C) w.1 := by
    rw [map_nsmul, degree_poleDivisor (red_xF_notMem_range w), finrank_adjoin_red_x,
      nsmul_eq_mul]
  have hm1 : cF ≤ m := by
    have := Int.self_le_toNat cF
    push_cast [m]
    have : (0 : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) := Finset.sum_nonneg fun _ _ ↦ by positivity
    linarith
  have hmw (w : Ext C F) : cw w ≤ m := by
    have h1 := Int.self_le_toNat (cw w)
    have h2 : ((cw w).toNat : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) :=
      Finset.single_le_sum (f := fun w ↦ ((cw w).toNat : ℤ)) (fun _ _ ↦ by positivity)
        (Finset.mem_univ w)
    push_cast [m]
    linarith [Int.natCast_nonneg cF.toNat]
  have hF := hcF _ (by
    rw [hdegF]
    nlinarith)
  have hw (w : Ext C F) := hcw w _ (by
    rw [hdegw]
    have := hfw w
    have : (m : ℤ) ≤ m * inertiaDeg (gauss1 C) w.1 := by
      exact_mod_cast Nat.le_mul_of_pos_right m this
    linarith [hmw w])
  have hle := ell_add_card_sub_one_le hb m
  have hcard : 1 ≤ Fintype.card (Ext C F) := Fintype.card_pos
  have hle' : (ell (m • poleDivisor C (xF C F)) : ℤ) + (Fintype.card (Ext C F) - 1) ≤
      ∑ w : Ext C F, (ell (m • poleDivisor 𝓀 (red C (xF C F) w)) : ℤ) := by
    have := Nat.cast_le (α := ℤ) |>.2 hle
    push_cast [Nat.cast_sub hcard] at this
    exact this
  rw [hF, hdegF] at hle'
  simp only [hw, hdegw] at hle'
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hle'
  have hsumZ : (∑ w : Ext C F, (inertiaDeg (gauss1 C) w.1 : ℤ)) = N := by
    exact_mod_cast hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hle'
  rw [hsumZ] at hle'
  linarith

end Sharp

end GaussFibre

end SemistableReduction
