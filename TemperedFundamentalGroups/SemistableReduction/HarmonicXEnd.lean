/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.HarmonicXNode

/-!
# Exponents at components over the branches of `y'` (Blueprint §9.7, X1/X2)

`end_exponent`: a component `V` of `c` mapping onto a component `w'` of `c'` has centre valuation
restricting to that of `w'` (`centreDetermines_gp`). So if `w'` is the branch of the node `y'`
on which its coordinate `u'` is a unit, the exponent of `u'` along `V` is `0`; if it is the
other branch (`u' = ϖ₂ ^ n'`), the exponent `E` satisfies `E e₂ = e₁ n'`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode _root_.SemistableReduction

variable {K K₁ K₂ L₁ L₂ : Type u} [Field K] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
  [Algebra K K₁] [Algebra K K₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
  [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
  [IsScalarTower K L₂ L₁]
  {O₁ : ValuationSubring K₁} {O₂ : ValuationSubring K₂} [IsDiscreteValuationRing O₁]
  [IsDiscreteValuationRing O₂] [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂]
  [IsScalarTower O₂ K₂ L₂]

/-- **The centre valuation of a component over a component restricts to its centre valuation.** -/
lemma comap_Wc {ϖ₂ : O₂} (hϖ₂ : Irreducible ϖ₂) {x₁ : L₁} {x : L₂}
    {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}
    {ψ : c.scheme ⟶ c'.scheme} {j : Spec (CommRingCat.of L₁) ⟶ c.scheme}
    {j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme} (hW : IsWModel O₁ L₁ x₁ c j)
    (hW' : IsWModel O₂ L₂ x c' j')
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j')
    {V : Set c.scheme} (hV : V ∈ components c) {w' : Set c'.scheme} (hw' : w' ∈ components c')
    (hψV : ψ '' V = w') : (Wc hW hV).comap (algebraMap L₂ L₁) = Wc hW' hw' := by
  have hc := IsCentre.comap j j' ψ hj (Wc_spec hW hV)
  have hη : ψ (gp hV) = gp hw' := map_genericPoint ψ (by rw [closure_gp hV, closure_gp hw', hψV])
  rw [hη] at hc
  exact centreDetermines_gp hW' hϖ₂ hw' _ _ hc (Wc_spec hW' hw')

/-- **Exponents at components over the branches of `y'`.** -/
theorem end_exponent {ϖ₁ : O₁} {ϖ₂ : O₂} (hϖ₁ : Irreducible ϖ₁) (hϖ₂ : Irreducible ϖ₂) {ϖ : K}
    {η₁ : O₁ˣ} {η₂ : O₂ˣ} {e₁ e₂ : ℕ}
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂) {x₁ : L₁} {x : L₂}
    {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}
    {ψ : c.scheme ⟶ c'.scheme} {j : Spec (CommRingCat.of L₁) ⟶ c.scheme}
    {j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme} (hW : IsWModel O₁ L₁ x₁ c j)
    (hW' : IsWModel O₂ L₂ x c' j')
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j')
    {Q : Subring L₂} {u' v' : L₂} {n' : ℕ} {ι₂ : O₂ →+* L₂} {W₁' W₂' : ValuationSubring L₂}
    (HB' : NodeBranches O₂ ϖ₂ Q ι₂ u' v' n' W₁' W₂')
    {V : Set c.scheme} (hV : V ∈ components c) {w' : Set c'.scheme} (hw' : w' ∈ components c')
    (hψV : ψ '' V = w') {E : ℕ}
    (hE : (Wc hW hV).valuation (algebraMap L₂ L₁ u') =
      (Wc hW hV).valuation (algebraMap O₁ L₁ ϖ₁) ^ E) :
    (Wc hW' hw' = W₁' → E = 0) ∧ (Wc hW' hw' = W₂' → E * e₂ = e₁ * n') := by
  set W := Wc hW hV
  have hcomap := comap_Wc hϖ₂ hW hW' hj hV hw' hψV
  have hϖL : algebraMap K₁ L₁ (ϖ₁ : K₁) = algebraMap O₁ L₁ ϖ₁ := algebraMap_O_K ϖ₁
  have hWϖ : W.valuation (algebraMap O₁ L₁ ϖ₁) < 1 :=
    valuation_ϖ_lt_one hW hϖ₁ (hV.2.1 (gp_mem hV)) (Wc_spec hW hV)
  have hW0 : W.valuation (algebraMap O₁ L₁ ϖ₁) ≠ 0 := by
    rw [← hϖL]; simpa using fun h ↦ hϖ₁.ne_zero (Subtype.ext h)
  have hO₁W : ∀ o : O₁, algebraMap K₁ L₁ (o : K₁) ∈ W := fun o ↦ by
    rw [algebraMap_O_K]
    exact ((isCentre_iff_dominates c j (specializes_of_isWModel hW _) W).1
      (Wc_spec hW hV)).1 (algebraMap_mem_germs hW _ o)
  have hO₂W : ∀ o : O₂, algebraMap L₂ L₁ (algebraMap K₂ L₂ (o : K₂)) ∈ W := fun o ↦ by
    change algebraMap K₂ L₂ (o : K₂) ∈ W.comap (algebraMap L₂ L₁)
    rw [hcomap, algebraMap_O_K]
    exact ((isCentre_iff_dominates c' j' (specializes_of_isWModel hW' _) _).1
      (Wc_spec hW' hw')).1 (algebraMap_mem_germs hW' _ o)
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h1 : (W.comap (algebraMap L₂ L₁)).valuation u' = 1 := by
      rw [hcomap, h]; exact NodeBranches.isLogValue_zero_iff.1 HB'.mono₁.2.2.1
    rw [_root_.SemistableReduction.valuation_comap_eq_one_iff, hE] at h1
    exact pow_inj hW0 hWϖ (h1.trans (pow_zero _).symm)
  · have h1 : (W.comap (algebraMap L₂ L₁)).valuation u' =
        (W.comap (algebraMap L₂ L₁)).valuation (algebraMap K₂ L₂ (ϖ₂ : K₂)) ^ n' := by
      rw [hcomap, h]; exact (NodeBranches.isLogValue_nat_iff n').1 HB'.mono₂.2.2.1
    have h2 : W.valuation (algebraMap L₂ L₁ u') =
        W.valuation (algebraMap L₂ L₁ (algebraMap K₂ L₂ (ϖ₂ : K₂))) ^ n' := by
      have h1' : (W.comap (algebraMap L₂ L₁)).valuation u' =
          (W.comap (algebraMap L₂ L₁)).valuation (algebraMap K₂ L₂ (ϖ₂ : K₂) ^ n') := by
        rw [map_pow (W.comap (algebraMap L₂ L₁)).valuation]; exact h1
      have := le_antisymm ((comap_valuation_le_iff _ _ _ _).1 h1'.le)
        ((comap_valuation_le_iff _ _ _ _).1 h1'.ge)
      rw [this, map_pow (algebraMap L₂ L₁), map_pow W.valuation]
    obtain ⟨ζ, hζ, hζ', hζ0, hζϖ⟩ := exists_zeta (P := W.toSubring) hϖK₁ hϖK₂ hO₁W hO₂W
    have hWζ : W.valuation ζ = 1 := (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨hζ0, hζ, hζ'⟩
    have h3 : W.valuation (algebraMap O₁ L₁ ϖ₁) ^ (E * e₂) =
        W.valuation (algebraMap O₁ L₁ ϖ₁) ^ (e₁ * n') := by
      rw [pow_mul, ← hE, h2, ← pow_mul, mul_comm n' e₂, pow_mul, ← map_pow, hζϖ, map_mul, hWζ,
        one_mul, map_pow, hϖL, ← pow_mul]
    exact pow_inj hW0 hWϖ h3

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
