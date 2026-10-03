/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SectionGenus
import TemperedFundamentalGroups.SemistableReduction.ChartLocal

/-!
# The total `δ` as a sum of local `δ`-invariants

Blueprint §9.9, S7⁺.7 (concrete part). The reduced charts `redRing x` and `redRing x⁻¹` of the
special fibre are affine charts in the sense of `ChartLocal.IsChart` (`isChart_x`,
`isChart_x_inv`), with conductor elements (`exists_conductor`, from the finiteness of the
normalization `CurveGenerators.exists_generators` and the surjectivity of the reduction
`exists_red_eq`).
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability CurvePlace LatticeReduction DeltaCount ChartLocal

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] [Fintype (Ext C F)]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField_F isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

/-- **Surjectivity of the reduction** onto `Π_w κ(w)` (orthonormal basis with residues, G6.3). -/
theorem exists_red_eq
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F)
    (y : Π w : Ext C F, ResidueField w.1.valuationSubring) :
    ∃ f : F, gnorm C f ≤ 1 ∧ ∀ w, red C f w = y w := by
  classical
  obtain ⟨b, hb, hsep, hres⟩ := exists_orthonormal_basis' ramificationIdx_eq_one hsum
  choose ℓ hℓli hℓ using hres
  set K₀ := ResidueField (gauss1 C).valuationSubring
  -- coordinates of `y w` in the residue basis
  have hcoord (w : Ext C F) : ∃ c : Fin (inertiaDeg (gauss1 C) w.1) → K₀,
      y w = ∑ l, c l • residue w.1.valuationSubring (ℓ w l) := by
    haveI : Module.Finite K₀ (ResidueField w.1.valuationSubring) := finite_residueField
    have hcard : Fintype.card (Fin (inertiaDeg (gauss1 C) w.1)) =
        Module.finrank K₀ (ResidueField w.1.valuationSubring) := by
      rw [Fintype.card_fin]; rfl
    haveI : Nonempty (Fin (inertiaDeg (gauss1 C) w.1)) :=
      ⟨⟨0, (Module.finrank_pos (R := K₀) (M := ResidueField w.1.valuationSubring))⟩⟩
    set B := basisOfLinearIndependentOfCardEqFinrank (hℓli w) hcard
    refine ⟨fun l ↦ B.repr (y w) l, ?_⟩
    conv_lhs => rw [← B.sum_repr (y w)]
    simp [B]
  choose c hc using hcoord
  choose φ hφ using fun (w : Ext C F) (l : Fin (inertiaDeg (gauss1 C) w.1)) ↦
    residue_surjective (c w l)
  set f := ∑ i : OIndex C F, (φ i.1 i.2 : RatFunc C) • b i
  refine ⟨f, ?_, fun w ↦ ?_⟩
  · rw [hb]
    exact Finset.sup_le fun i _ ↦ (φ i.1 i.2).2
  · have hb1 (i : OIndex C F) : gnorm C (b i) ≤ 1 := by
      have := hb (Pi.single i 1)
      simp only [Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at this
      rw [this]
      exact Finset.sup_le fun j _ ↦ by split_ifs <;> simp
    have hbw (i : OIndex C F) : w.1 (b i) ≤ 1 := (le_gnorm w _).trans (hb1 i)
    have hterm (i : OIndex C F) : w.1 ((φ i.1 i.2 : RatFunc C) • b i) ≤ 1 := by
      rw [Algebra.smul_def, map_mul, valuation_algebraMap]
      exact mul_le_one' (φ i.1 i.2).2 (hbw i)
    rw [red_sum _ _ fun i _ ↦ hterm i, hc w]
    rw [Fintype.sum_sigma]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ w)]
    have hzero : ∑ w' ∈ Finset.univ.erase w, ∑ l : Fin (inertiaDeg (gauss1 C) w'.1),
        red C ((φ w' l : RatFunc C) • b ⟨w', l⟩) w = 0 := by
      refine Finset.sum_eq_zero fun w' hw' ↦ Finset.sum_eq_zero fun l _ ↦ ?_
      have hlt : w.1 (b ⟨w', l⟩) < 1 := hsep ⟨w', l⟩ w (Finset.ne_of_mem_erase hw').symm
      rw [Algebra.smul_def, red_algebraMap_mul _ (φ w' l).2 (hbw _),
        (red_eq_zero_iff hlt.le).2 hlt, mul_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    rw [Algebra.smul_def, red_algebraMap_mul _ (φ w l).2 (hbw _), Algebra.smul_def, ← hφ w l]
    congr 1
    have hl : w.1 (ℓ w l : F) ≤ 1 := (ℓ w l).2
    have hd := hℓ w l
    have : b ⟨w, l⟩ = (b ⟨w, l⟩ - ℓ w l) + ℓ w l := by ring
    rw [this, red_add hd.le hl, (red_eq_zero_iff hd.le).2 hd, zero_add, red_of_le hl]

section Chart

variable {ζ : RatFunc C} (hζ : IsCoord F ζ)
include hζ

omit [FiniteDimensional (RatFunc C) F] in
/-- The reduced chart ring is an affine chart, given G6.5 for the coordinate. -/
theorem isChart_redRing
    (hle : ∀ a ∈ intRing C F (algebraMap (RatFunc C) F ζ), ∀ (w : Ext C F)
      (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)),
        red C (algebraMap (RatFunc C) F ζ) w ∈ Q.V → red C a w ∈ Q.V) :
    IsChart 𝓀 (fun w : Ext C F ↦ red C (algebraMap (RatFunc C) F ζ) w)
      (redRing C F (algebraMap (RatFunc C) F ζ)) where
  const c := algebraMap_mem_redRing _ c
  mem := red_mem_redRing (by simpa using aeval_coord_mem_intRing hζ (P := X) (by simp [sup_X]))
  le := by
    rintro _ ⟨a, ha, rfl⟩ w Q hQ
    exact hle a ha w Q hQ
  tr w := transcendental_red_coord hζ w

/-- Polynomials in `z̄` lie in the reduced chart ring. -/
lemma aeval_red_mem_redRing (P : 𝓀[X]) :
    (fun w : Ext C F ↦ aeval (red C (algebraMap (RatFunc C) F ζ) w) P) ∈
      redRing C F (algebraMap (RatFunc C) F ζ) := by
  obtain ⟨Q, hQ, rfl⟩ := exists_redPoly_eq (C := C) P
  exact ⟨_, aeval_coord_mem_intRing hζ hQ, funext fun w ↦ red_aeval_coord hζ hQ w⟩

/-- Every element of `Π_w κ(w)` times a nonzero polynomial in `z̄` lies in the reduced chart
ring. -/
lemma exists_aeval_mul_mem_redRing
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F)
    (y : Π w : Ext C F, ResidueField w.1.valuationSubring) :
    ∃ μ : 𝓀[X], μ ≠ 0 ∧ (fun w : Ext C F ↦ aeval (red C (algebraMap (RatFunc C) F ζ) w) μ) * y ∈
      redRing C F (algebraMap (RatFunc C) F ζ) := by
  obtain ⟨f, hf, hfy⟩ := exists_red_eq hsum y
  obtain ⟨P, hP0, hPint⟩ := hζ.mul_integral f
  obtain ⟨c, hc⟩ := exists_sup_eq P
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hc
    exact (sup_pos_of_ne_zero hP0).ne' hc
  set P' := Polynomial.C c⁻¹ * P
  have hP' : Gauss.sup (NormedField.valuation (K := C)) 1 P' = 1 := by
    rw [← hζ.gauss, map_mul, aeval_C, map_mul, gauss1_algebraMap_C, hζ.gauss, hc, nnnorm_inv,
      inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hc0)]
  have hmem : aeval (algebraMap (RatFunc C) F ζ) P' * f ∈
      intRing C F (algebraMap (RatFunc C) F ζ) := by
    refine ⟨?_, (gnorm_mul_le _ _).trans (mul_le_one' ?_ hf)⟩
    · have : aeval (algebraMap (RatFunc C) F ζ) P' * f = aeval (algebraMap (RatFunc C) F ζ)
          (Polynomial.C c⁻¹) * (aeval (algebraMap (RatFunc C) F ζ) P * f) := by
        rw [map_mul, mul_assoc]
      rw [this]
      exact (isIntegral_aeval_coord (F := F) (ζ := ζ) _).mul hPint
    · exact gnorm_le_iff.2 fun w ↦ by rw [valuation_aeval_coord hζ, hP']
  refine ⟨redPoly P', fun h ↦ (sup_lt_one_of_redPoly_eq_zero hP'.le h).ne hP', ?_⟩
  refine ⟨_, hmem, funext fun w ↦ ?_⟩
  rw [red_mul ((valuation_aeval_coord hζ P' w).trans_le hP'.le) ((le_gnorm w f).trans hf),
    red_aeval_coord hζ hP'.le w, hfy w]
  rfl

/-- **A conductor element** of the reduced chart ring. -/
theorem exists_conductor
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F)
    (hch : IsChart 𝓀 (fun w : Ext C F ↦ red C (algebraMap (RatFunc C) F ζ) w)
      (redRing C F (algebraMap (RatFunc C) F ζ))) :
    ∃ σ ∈ redRing C F (algebraMap (RatFunc C) F ζ), (∀ w, σ w ≠ 0) ∧
      ∀ v ∈ regRing 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
        (fun w : Ext C F ↦ red C (algebraMap (RatFunc C) F ζ) w),
        σ * v ∈ redRing C F (algebraMap (RatFunc C) F ζ) := by
  classical
  set z := algebraMap (RatFunc C) F ζ
  set Λ := redRing C F z
  -- generators of the normalizations of the components
  have hgen (w : Ext C F) := by
    haveI := IsCurveFunctionField.finiteDimensional_adjoin (k := 𝓀) (hch.tr w)
    exact CurveGenerators.exists_generators (hch.tr w)
  choose G hGint hG using hgen
  -- denominators of the generators
  have hden (p : Σ w : Ext C F, ResidueField w.1.valuationSubring) :
      ∃ μ : 𝓀[X], μ ≠ 0 ∧ (fun w : Ext C F ↦ aeval (red C z w) μ) * Pi.single p.1 p.2 ∈ Λ :=
    exists_aeval_mul_mem_redRing hζ hsum _
  choose μ hμ0 hμ using hden
  set T : Finset (Σ w : Ext C F, ResidueField w.1.valuationSubring) :=
    Finset.univ.sigma G
  set Mμ := ∏ p ∈ T, μ p
  have hM0 : Mμ ≠ 0 := Finset.prod_ne_zero_iff.2 fun p _ ↦ hμ0 p
  set σ : Π w : Ext C F, ResidueField w.1.valuationSubring := fun w ↦ aeval (red C z w) Mμ
  refine ⟨σ, aeval_red_mem_redRing hζ Mμ, fun w h ↦ hch.tr w ⟨Mμ, hM0, h⟩, fun v hv ↦ ?_⟩
  -- decompose `v` along the generators
  have hcomp (w : Ext C F) : ∃ c : ResidueField w.1.valuationSubring → 𝓀[X],
      v w = ∑ g ∈ G w, aeval (red C z w) (c g) * g :=
    hG w (v w) (CurveGenerators.isIntegral_of_forall_mem fun Q hQ ↦ hv w Q hQ)
  choose c hc using hcomp
  have hv' : v = ∑ p ∈ T, (fun w ↦ aeval (red C z w) (c p.1 p.2)) * Pi.single p.1 p.2 := by
    funext w
    simp only [T, Finset.sum_sigma, Finset.sum_apply, Pi.mul_apply]
    rw [Finset.sum_eq_single w (fun w' _ hw' ↦ Finset.sum_eq_zero fun g _ ↦ by
      rw [Pi.single_eq_of_ne (Ne.symm hw'), mul_zero]) (by simp), hc w]
    exact Finset.sum_congr rfl fun g _ ↦ by rw [Pi.single_eq_same]
  rw [hv', Finset.mul_sum]
  refine sum_mem fun p hp ↦ ?_
  obtain ⟨M', hM'⟩ := Finset.dvd_prod_of_mem μ hp
  replace hM' : Mμ = μ p * M' := hM'
  have : σ * ((fun w ↦ aeval (red C z w) (c p.1 p.2)) * Pi.single p.1 p.2) =
      (fun w ↦ aeval (red C z w) (M' * c p.1 p.2)) *
        ((fun w ↦ aeval (red C z w) (μ p)) * Pi.single p.1 p.2) := by
    funext w
    simp only [Pi.mul_apply]
    rw [show σ w = aeval (red C z w) Mμ from rfl, hM', map_mul, map_mul]
    ring
  rw [this]
  exact mul_mem (aeval_red_mem_redRing hζ _) (hμ p)

end Chart

end GaussFibre

end SemistableReduction
