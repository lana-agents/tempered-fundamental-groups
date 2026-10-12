/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.VertexDescent
import TemperedFundamentalGroups.SemistableReduction.ZariskiModel

/-!
# Branches of different radii are not swapped (Blueprint §12.7, missing theorem M3, algebra)

Let `L` be a field over `K'`, `O' ⊆ K'` a discrete valuation ring with uniformizer `ϖ'`, and
`W₁, W₂` valuation subrings of `L` over `O'` which restrict to Gauss points of the x-line with
the same centre `a` and radii `|β ϖ'^α| > |β ϖ'^(α + N)|`: `x - a = β ϖ'^α t` with `t`
residually transcendental at `W₁` and `t / ϖ'^N ∈ W₂` (the two branches of a node of an
unfolded W-model, `UnfoldedNodeGerm`). A field endomorphism `σ` of `L` fixing `x` and a subfield
`K₀` over which `K'` is algebraic (and containing an element `ϖ₀ = η ϖ'^e₀`, `e₀ ≥ 1`) cannot
carry `W₂` onto `W₁` (`g ∈ W₂ ↔ σ g ∈ W₁`): `σ` preserves the absolute values of constants
(`valuation_map_eq`), so `|x - σ a|_{W₁} = |x - a|_{W₂} < |β ϖ'^α|`, and then the residue of `t`
at `W₁` would be that of the algebraic element `(σ a - a) / (β ϖ'^α)`
(`not_valuation_sub_lt_one`).

This is the input for "no branch inversions" of the tree tower of a curve: stage-group elements
act over the x-line (`σ x = x`, `σ` is `K`-linear), so an element fixing a node cannot exchange
its two branches.
-/

open Polynomial

namespace SemistableReduction

variable {K' L : Type*} [Field K'] [Field L] [Algebra K' L]

/-- An element residually transcendental at `W` is not congruent to an algebraic element. -/
theorem not_valuation_sub_lt_one {O : ValuationSubring K'} {W : ValuationSubring L}
    (hW : W.comap (algebraMap K' L) = O) {t z : L} (ht : IsResidueTranscendental O W t)
    (hz : z ∈ W) (halg : IsAlgebraic K' z) : ¬ W.valuation (t - z) < 1 := by
  intro hlt
  have htW := ht.1
  have hres : IsLocalRing.residue W ⟨t, htW⟩ = IsLocalRing.residue W ⟨z, hz⟩ := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
      ValuationSubring.valuation_lt_one_iff]
    exact hlt
  rw [isResidueTranscendental_iff hW htW, hres] at ht
  exact not_isResidueTranscendental_of_isAlgebraic halg ((isResidueTranscendental_iff hW hz).2 ht)

/-- `v(x) < 1` for `x ∈ W` with `x⁻¹ ∉ W`. -/
lemma valuation_lt_one_of_inv_notMem {W : ValuationSubring L} {g : L} (hg : g ∈ W)
    (hg' : g⁻¹ ∉ W) : W.valuation g < 1 := by
  refine lt_of_le_of_ne ((W.valuation_le_one_iff g).2 hg) fun h ↦ hg' ?_
  rw [← W.valuation_le_one_iff, map_inv₀, h, inv_one]

/-- In a valuation subring, `a b = 1` forces `v(a) = 1`. -/
lemma valuation_eq_one_of_mul_eq_one {W : ValuationSubring L} {g h : L} (hg : g ∈ W) (hh : h ∈ W)
    (hgh : g * h = 1) : W.valuation g = 1 := by
  refine le_antisymm ((W.valuation_le_one_iff g).2 hg) ?_
  calc (1 : _) = W.valuation g * W.valuation h := by rw [← map_mul, hgh, map_one]
    _ ≤ W.valuation g * 1 := mul_le_mul_right ((W.valuation_le_one_iff h).2 hh) _
    _ = W.valuation g := mul_one _

variable {K₀ : Type*} [Field K₀] [Algebra K₀ K'] [Algebra K₀ L] [IsScalarTower K₀ K' L]
  {O' : ValuationSubring K'} [IsDiscreteValuationRing O'] {ϖ' : O'}
  {W₁ W₂ : ValuationSubring L}

/-- **A map carrying `W₂` onto `W₁` and fixing `K₀` preserves the absolute values of constants**
(`ϖ₀ ∈ K₀` is a power of `ϖ'` up to a unit). -/
theorem valuation_map_eq (hϖ' : Irreducible ϖ') (h₁ : W₁.comap (algebraMap K' L) = O')
    (h₂ : W₂.comap (algebraMap K' L) = O') {ϖ₀ : K₀} {e₀ : ℕ} {η : O'ˣ} (he₀ : 1 ≤ e₀)
    (hϖ₀ : algebraMap K₀ K' ϖ₀ = (η : K') * (ϖ' : K') ^ e₀) (σ : L →+* L)
    (hσK : ∀ k : K₀, σ (algebraMap K₀ L k) = algebraMap K₀ L k)
    (hσ : ∀ g, g ∈ W₂ ↔ σ g ∈ W₁) (k : K') :
    W₁.valuation (σ (algebraMap K' L k)) = W₁.valuation (algebraMap K' L k) := by
  have hmem : ∀ (W : ValuationSubring L), W.comap (algebraMap K' L) = O' → ∀ o : O',
      algebraMap K' L (o : K') ∈ W := fun W hW o ↦ by
    rw [← ValuationSubring.mem_comap, hW]; exact o.2
  -- units of `O'`
  have hunit : ∀ w : O'ˣ, W₁.valuation (σ (algebraMap K' L ((w : O') : K'))) = 1 ∧
      W₁.valuation (algebraMap K' L ((w : O') : K')) = 1 := fun w ↦ by
    have hw : ((w : O') : K') * ((w⁻¹ : O'ˣ) : O') = 1 := by
      rw [← Subring.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]; rfl
    have hwL : algebraMap K' L ((w : O') : K') * algebraMap K' L ((w⁻¹ : O'ˣ) : O') = 1 := by
      rw [← map_mul, hw, map_one]
    refine ⟨valuation_eq_one_of_mul_eq_one ((hσ _).1 (hmem W₂ h₂ _))
      ((hσ _).1 (hmem W₂ h₂ (w⁻¹ : O'ˣ))) (by rw [← map_mul, hwL, map_one]), ?_⟩
    exact valuation_eq_one_of_mul_eq_one (hmem W₁ h₁ _) (hmem W₁ h₁ (w⁻¹ : O'ˣ)) hwL
  have he0 : e₀ ≠ 0 := by omega
  -- elements of `O'`
  have hO : ∀ o : O', W₁.valuation (σ (algebraMap K' L (o : K'))) =
      W₁.valuation (algebraMap K' L (o : K')) := by
    intro o
    rcases eq_or_ne o 0 with rfl | ho
    · simp
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ho hϖ'
    set w : O'ˣ := u ^ e₀ * η⁻¹ ^ m
    have hk : ((↑u * ϖ' ^ m : O') : K') ^ e₀ = ((w : O') : K') * algebraMap K₀ K' ϖ₀ ^ m := by
      have hηi : (((η⁻¹ : O'ˣ) : O') : K') * ((η : O') : K') = 1 := by
        rw [← Subring.coe_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]; rfl
      have hηm : ((((η⁻¹ : O'ˣ) : O') : K') * ((η : O') : K')) ^ m = 1 := by
        rw [hηi, one_pow]
      rw [hϖ₀]
      simp only [w, Units.val_mul, Units.val_pow_eq_pow_val]
      push_cast
      linear_combination (-(((u : O') : K') ^ e₀ * (ϖ' : K') ^ (e₀ * m))) * hηm
    have hkL := congrArg (algebraMap K' L) hk
    rw [map_pow, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] at hkL
    have hσkL := congrArg σ hkL
    rw [map_pow, map_mul, map_pow, hσK] at hσkL
    have h₁' := congrArg W₁.valuation hσkL
    have h₂' := congrArg W₁.valuation hkL
    rw [map_pow, map_mul, map_pow, (hunit w).1, one_mul] at h₁'
    rw [map_pow, map_mul, map_pow, (hunit w).2, one_mul, ← h₁'] at h₂'
    exact (pow_left_inj₀ zero_le zero_le he0).1 h₂'.symm
  rcases O'.mem_or_inv_mem k with hk | hk
  · exact hO ⟨k, hk⟩
  · have := hO ⟨k⁻¹, hk⟩
    simp only [map_inv₀] at this
    exact inv_inj.1 this

/-- **No swap of branches of different radii (M3, algebra).** Let `x - a = β t ϖ'^α` with `t`
residually transcendental at `W₁` and `t / ϖ'^N ∈ W₂` (`N ≥ 1`: the Gauss points of radii
`|β ϖ'^α|` and `|β ϖ'^(α+N)|` with centre `a`). A field endomorphism `σ` of `L` fixing `x` and
`K₀` (with `K'` algebraic over `K₀`) does not carry `W₂` onto `W₁`. -/
theorem not_branch_swap [Algebra.IsAlgebraic K₀ K'] (hϖ' : Irreducible ϖ')
    (h₁ : W₁.comap (algebraMap K' L) = O') (h₂ : W₂.comap (algebraMap K' L) = O') {x t : L}
    {a β : K'} {α N : ℕ} (hβ : β ≠ 0) (hN : 1 ≤ N)
    (hcoord : x - algebraMap K' L a =
      algebraMap K' L β * (t * algebraMap K' L (ϖ' : K') ^ α))
    (ht₁ : IsResidueTranscendental O' W₁ t) (ht₂ : t / algebraMap K' L (ϖ' : K') ^ N ∈ W₂)
    {ϖ₀ : K₀} {e₀ : ℕ} {η : O'ˣ} (he₀ : 1 ≤ e₀)
    (hϖ₀ : algebraMap K₀ K' ϖ₀ = (η : K') * (ϖ' : K') ^ e₀) (σ : L →+* L)
    (hσK : ∀ k : K₀, σ (algebraMap K₀ L k) = algebraMap K₀ L k) (hσx : σ x = x)
    (hσ : ∀ g, g ∈ W₂ ↔ σ g ∈ W₁) : False := by
  set p := algebraMap K' L (ϖ' : K') with hp
  have hϖ0 : (ϖ' : K') ≠ 0 := by exact_mod_cast hϖ'.ne_zero
  have hp0 : p ≠ 0 := by simpa [hp] using hϖ0
  set c₀ : K' := β * (ϖ' : K') ^ α
  have hc₀ : c₀ ≠ 0 := mul_ne_zero hβ (pow_ne_zero _ hϖ0)
  set c := algebraMap K' L c₀
  have hc : c ≠ 0 := by simpa [c] using hc₀
  have hcoord' : x - algebraMap K' L a = c * t := by
    rw [hcoord]; simp only [c, c₀, map_mul, map_pow]; ring
  -- `σ ϖ'` is not a unit of `W₁`
  have hpW₂ : p ∈ W₂ := by rw [← ValuationSubring.mem_comap, h₂]; exact ϖ'.2
  have hpinv : p⁻¹ ∉ W₂ := by
    intro h
    rw [hp, ← map_inv₀, ← ValuationSubring.mem_comap, h₂] at h
    apply hϖ'.not_isUnit
    refine IsUnit.of_mul_eq_one (⟨_, h⟩ : O') (Subtype.ext ?_)
    simp [hϖ0]
  have hσp : W₁.valuation (σ p) < 1 := by
    refine valuation_lt_one_of_inv_notMem ((hσ p).1 hpW₂) fun h ↦ hpinv ?_
    rw [hσ, map_inv₀]; exact h
  -- the value of `x - σ a`
  have hσt : W₁.valuation (σ (t / p ^ N)) ≤ 1 :=
    (W₁.valuation_le_one_iff _).2 ((hσ _).1 ht₂)
  have hxσ : x - σ (algebraMap K' L a) = σ c * σ p ^ N * σ (t / p ^ N) := by
    rw [show x - σ (algebraMap K' L a) = σ (x - algebraMap K' L a) by rw [map_sub, hσx],
      hcoord', ← map_pow, ← map_mul, ← map_mul, mul_assoc, mul_div_cancel₀ _ (pow_ne_zero _ hp0)]
  have hcv : W₁.valuation c ≠ 0 := by simpa using hc
  have hlt : W₁.valuation (x - σ (algebraMap K' L a)) < W₁.valuation c := by
    rw [hxσ, map_mul, map_mul, map_pow, valuation_map_eq hϖ' h₁ h₂ he₀ hϖ₀ σ hσK hσ c₀]
    calc W₁.valuation c * W₁.valuation (σ p) ^ N * W₁.valuation (σ (t / p ^ N))
        ≤ W₁.valuation c * W₁.valuation (σ p) ^ N := mul_le_of_le_one_right' hσt
      _ < W₁.valuation c * 1 := by
          refine mul_lt_mul_of_pos_left (pow_lt_one₀ zero_le hσp (by omega)) ?_
          exact zero_lt_iff.2 hcv
      _ = W₁.valuation c := mul_one _
  -- the algebraic element congruent to `t`
  set z := (σ (algebraMap K' L a) - algebraMap K' L a) / c
  have htz : t - z = (x - σ (algebraMap K' L a)) / c := by
    have ht : t = (x - algebraMap K' L a) / c := by rw [hcoord', mul_div_cancel_left₀ _ hc]
    rw [ht]
    simp only [z]
    field_simp
    ring
  have hlt' : W₁.valuation (t - z) < 1 := by
    rw [htz, map_div₀]
    exact (div_lt_one₀ (zero_lt_iff.2 hcv)).2 hlt
  have hzW : z ∈ W₁ := by
    have : z = t - (t - z) := by ring
    rw [this]
    exact W₁.sub_mem ht₁.1 ((W₁.valuation_le_one_iff _).1 hlt'.le)
  have halg : IsAlgebraic K' z := by
    let σA : L →ₐ[K₀] L := { σ with commutes' := hσK }
    have h₀ : IsAlgebraic K₀ (algebraMap K' L a) :=
      (Algebra.IsAlgebraic.isAlgebraic a).algebraMap
    have h₀' : IsAlgebraic K' (σ (algebraMap K' L a)) := (h₀.algHom σA).tower_top K'
    rw [isAlgebraic_iff_isIntegral] at h₀' ⊢
    have hz : z = (σ (algebraMap K' L a) - algebraMap K' L a) * algebraMap K' L c₀⁻¹ := by
      simp [z, c, div_eq_mul_inv]
    rw [hz]
    exact (h₀'.sub isIntegral_algebraMap).mul isIntegral_algebraMap
  exact not_valuation_sub_lt_one h₁ ht₁ hzW halg hlt'

end SemistableReduction
