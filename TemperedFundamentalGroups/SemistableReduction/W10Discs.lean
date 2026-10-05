/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.AbhyankarInequality
import TemperedFundamentalGroups.SemistableReduction.GaussModel
import TemperedFundamentalGroups.SemistableReduction.VertexDescent

/-!
# Type-2 valuation subrings of `C(X)` are Gauss valuation rings

Blueprint §9.7a, step 3 (the discs `V₀` of the dominated models). Over an algebraically closed
field `K` with a valuation `v`, a valuation subring `W` of `K(X)` with `W ∩ K = O_v` whose residue
field is transcendental over that of `v` (`IsTypeTwo`) is the valuation ring of a Gauss valuation
`w_{a, |c|}` (`exists_eq_gaussRat_valuationSubring`). This is W2 + W3 (`GaussClassification`,
`AbhyankarInequality`) in the language of valuation subrings.
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace W10Discs

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {v : Valuation K Γ₀} {w : Valuation L Γ₁} [v.HasExtension w]

open ValuationResidue in
/-- Transcendence of a residue, elementwise: the residue of `y` is transcendental over `κ(v)` iff
`w (P(y)) = 1` for every integral polynomial `P` with nonzero reduction. -/
lemma transcendental_residue_iff (y : w.valuationSubring) :
    Transcendental (ResidueField v.valuationSubring) (residue w.valuationSubring y) ↔
      ∀ P : v.valuationSubring[X], P.map (residue v.valuationSubring) ≠ 0 →
        w (aeval (y : L) (P.map (algebraMap v.valuationSubring K))) = 1 := by
  rw [transcendental_iff]
  constructor
  · intro h P hP
    rw [← coe_aeval, ← residue_ne_zero_iff, residue_aeval]
    exact fun h0 ↦ hP (h _ h0)
  · intro h p hp
    by_contra hp0
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue v.valuationSubring)
      residue_surjective p
    have := h P hp0
    rw [← coe_aeval, ← residue_ne_zero_iff, residue_aeval] at this
    exact this hp

section Classification

variable {K : Type*} [Field K] [IsAlgClosed K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {W : ValuationSubring (RatFunc K)}

/-- **Type-2 valuation subrings of `K(X)` are Gauss valuation rings** (`K` algebraically closed):
if `W ∩ K = O_v` and `W` is of type 2 over `O_v`, then `W = O_{w_{a, v(c)}}` for some `a` and
`c ≠ 0`. -/
theorem exists_eq_gaussRat_valuationSubring
    (hW : W.comap (algebraMap K (RatFunc K)) = v.valuationSubring)
    (hT : IsTypeTwo v.valuationSubring W) :
    ∃ (a c : K) (hc : c ≠ 0), W = (gaussRat v a
      (Units.mk0 (v c) ((Valuation.ne_zero_iff v).2 hc))).valuationSubring := by
  set w := W.valuation
  set v' := w.comap (algebraMap K (RatFunc K))
  haveI : v'.HasExtension w := ⟨Valuation.IsEquiv.refl⟩
  have hwW : w.valuationSubring = W := ValuationSubring.valuationSubring_valuation W
  have hv'O : v'.valuationSubring = v.valuationSubring := by
    rw [← hW]
    ext x
    change w (algebraMap K (RatFunc K) x) ≤ 1 ↔ algebraMap K (RatFunc K) x ∈ W
    exact W.valuation_le_one_iff _
  rw [← hv'O] at hT
  obtain ⟨z, hzW, hz⟩ := hT
  have hzw : z ∈ w.valuationSubring := by rw [hwW]; exact hzW
  have htr : Algebra.Transcendental (ResidueField v'.valuationSubring)
      (ResidueField w.valuationSubring) := by
    rw [Algebra.transcendental_def]
    refine ⟨residue w.valuationSubring ⟨z, hzw⟩, (transcendental_residue_iff _).2 fun P hP ↦ ?_⟩
    exact hz P hP
  have hΓ : ∀ f : RatFunc K, ∃ c : K, w f = v' c := fun f ↦
    exists_eq_of_transcendental trdeg_ratFunc.le htr f
  obtain ⟨a, c, hc0, hy, htr'⟩ :=
    exists_residue_gaussLin_transcendental (v := v') (w := w) (fun _ ↦ rfl) hΓ htr
  have hyRT : IsResidueTranscendental v'.valuationSubring W (gaussCoord a c) :=
    ⟨by rw [← hwW]; exact hy, fun P hP ↦ (transcendental_residue_iff ⟨_, hy⟩).1 htr' P hP⟩
  rw [hv'O] at hyRT
  exact ⟨a, c, hc0, (isGaussCoord_gaussCoord (v := v) (a := a) rfl).eq_of_isResidueTranscendental
    hW hyRT⟩

end Classification

section Restriction

open ZariskiModel

variable {K M F : Type*} [Field K] [Field M] [Field F] [Algebra K M] [Algebra M F] [Algebra K F]
  [IsScalarTower K M F] {O : ValuationSubring K} {W : ValuationSubring F}

lemma comap_comap_eq (hW : W.comap (algebraMap K F) = O) :
    (W.comap (algebraMap M F)).comap (algebraMap K M) = O := by
  rw [ValuationSubring.comap_comap, ← IsScalarTower.algebraMap_eq, hW]

/-- **Restrictions of type-2 valuation subrings along algebraic extensions are of type 2.** -/
theorem isTypeTwo_comap [Algebra.IsAlgebraic M F] (hW : W.comap (algebraMap K F) = O)
    (hT : IsTypeTwo O W) : IsTypeTwo O (W.comap (algebraMap M F)) := by
  set W' := W.comap (algebraMap M F)
  have hW' : W'.comap (algebraMap K M) = O := comap_comap_eq hW
  have hWW' : W.comap (algebraMap M F) = W' := rfl
  by_contra hnot
  letI A₁ := residueAlgebra hW'
  letI A₂ := residueAlgebra hWW'
  letI A₃ := residueAlgebra hW
  haveI : IsScalarTower (ResidueField O) (ResidueField W') (ResidueField W) := by
    refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
    obtain ⟨o, rfl⟩ := residue_surjective r
    change ResidueField.map (toVal hW) (residue O o) =
      ResidueField.map (toVal hWW') (ResidueField.map (toVal hW') (residue O o))
    rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue]
    congr 1
    exact Subtype.ext (by simp [IsScalarTower.algebraMap_apply K M F])
  haveI h₁ : Algebra.IsAlgebraic (ResidueField O) (ResidueField W') := by
    refine ⟨fun r ↦ ?_⟩
    obtain ⟨m, rfl⟩ := residue_surjective r
    by_contra hr
    exact hnot ⟨m, (isResidueTranscendental_iff hW' m.2).2 hr⟩
  haveI h₂ : Algebra.IsAlgebraic (ResidueField W') (ResidueField W) :=
    isAlgebraic_residueField hWW'
  haveI := Algebra.IsAlgebraic.trans (ResidueField O) (ResidueField W') (ResidueField W)
  obtain ⟨z, hz⟩ := hT
  exact ((isResidueTranscendental_iff hW hz.1).1 hz) (Algebra.IsAlgebraic.isAlgebraic _)

end Restriction

end W10Discs

end SemistableReduction
