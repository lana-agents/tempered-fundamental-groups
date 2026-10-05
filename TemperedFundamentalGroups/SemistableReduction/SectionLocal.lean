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

omit [Algebra C F] [IsScalarTower C (RatFunc C) F] in
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

omit [FiniteDimensional (RatFunc C) F] [IsAlgClosed C] in
/-- The reduced chart ring is an affine chart, given G6.5 for the coordinate. -/
theorem isChart_redRing
    (hle : ∀ a ∈ intRing C F (algebraMap (RatFunc C) F ζ), ∀ (w : Ext C F)
      (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)),
        red C (algebraMap (RatFunc C) F ζ) w ∈ Q.V → red C a w ∈ Q.V) :
    IsChart 𝓀 (fun w : Ext C F ↦ red C (algebraMap (RatFunc C) F ζ) w)
      (redRing C F (algebraMap (RatFunc C) F ζ)) where
  const c := algebraMap_mem_redRing _ c
  mem := red_mem_redRing (by simpa using aeval_coord_mem_intRing hζ (P := X) (by simp))
  le := by
    rintro _ ⟨a, ha, rfl⟩ w Q hQ
    exact hle a ha w Q hQ
  tr w := transcendental_red_coord hζ w

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
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

section PiRR

omit [Fintype (Ext C F)] in
lemma piRR_mem_V {m : ℕ} {v : Π w : Ext C F, ResidueField w.1.valuationSubring}
    (hv : v ∈ piRR C F m) (w : Ext C F) (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring))
    (hQ : red C (xF C F) w ∈ Q.V) : v w ∈ Q.V := by
  have := hv w trivial Q
  rw [Finsupp.smul_apply, poleDivisor_apply, Q.poleOrder_eq_zero_iff.2 hQ] at this
  simp only [Nat.cast_zero, smul_zero, exp_zero] at this
  exact Q.valuation_le_one_iff.1 this

omit [Fintype (Ext C F)] in
lemma piRR_mem_V_inv {m : ℕ} {v : Π w : Ext C F, ResidueField w.1.valuationSubring}
    (hv : v ∈ piRR C F m) (w : Ext C F) (Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring))
    (hQ : red C (xF C F)⁻¹ w ∈ Q.V) : red C (xF C F)⁻¹ w ^ m * v w ∈ Q.V := by
  rw [red_inv_xF] at hQ ⊢
  by_cases hx : red C (xF C F) w ∈ Q.V
  · exact mul_mem (pow_mem hQ _) (piRR_mem_V hv w Q hx)
  · rw [← Q.valuation_le_one_iff, map_mul, map_pow, map_inv₀, Q.valuation_eq_exp_poleOrder hx]
    have := hv w trivial Q
    rw [Finsupp.smul_apply, poleDivisor_apply, nsmul_eq_mul] at this
    calc (exp (Q.poleOrder (red C (xF C F) w) : ℤ))⁻¹ ^ m * Q.valuation (v w) ≤
        (exp (Q.poleOrder (red C (xF C F) w) : ℤ))⁻¹ ^ m *
          exp ((m : ℤ) * Q.poleOrder (red C (xF C F) w)) := by gcongr
      _ = 1 := by
        rw [← exp_neg, ← exp_nsmul, ← exp_add, nsmul_eq_mul]
        ring_nf
        exact exp_zero

end PiRR

section Main

variable {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
  (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F)
include hb

/-- The reduced chart at `0` is an affine chart. -/
theorem isChart_x :
    IsChart 𝓀 (fun w : Ext C F ↦ red C (xF C F) w) (redRing C F (xF C F)) :=
  isChart_redRing isCoord_X fun _ ha w Q hQ ↦
    red_mem_of_isIntegral hb ha.2 ha.1 w Q.V Q.algebraMap_mem hQ

/-- The reduced chart at `∞` is an affine chart. -/
theorem isChart_x_inv :
    IsChart 𝓀 (fun w : Ext C F ↦ red C (xF C F)⁻¹ w) (redRing C F (xF C F)⁻¹) := by
  have h := isChart_redRing (isCoord_X_inv (C := C) (F := F)) fun a ha w Q hQ ↦ by
    rw [algebraMap_X_inv] at ha hQ
    exact red_mem_of_isIntegral_inv hb ha.2 ha.1 w Q.V Q.algebraMap_mem hQ
  rwa [algebraMap_X_inv] at h

include hsum in
lemma exists_conductor_x : ∃ σ ∈ redRing C F (xF C F), (∀ w, σ w ≠ 0) ∧
    ∀ v ∈ regRing 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
      (fun w : Ext C F ↦ red C (xF C F) w), σ * v ∈ redRing C F (xF C F) :=
  exists_conductor isCoord_X hsum (isChart_x hb)

include hsum in
lemma exists_conductor_x_inv : ∃ σ ∈ redRing C F (xF C F)⁻¹, (∀ w, σ w ≠ 0) ∧
    ∀ v ∈ regRing 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
      (fun w : Ext C F ↦ red C (xF C F)⁻¹ w), σ * v ∈ redRing C F (xF C F)⁻¹ := by
  have h := exists_conductor (isCoord_X_inv (C := C) (F := F)) hsum (by
    rw [algebraMap_X_inv]; exact isChart_x_inv hb)
  rwa [algebraMap_X_inv] at h

set_option maxHeartbeats 1000000 in
-- the dimension count over the closed points of both charts elaborates slowly
open Classical in
include hsum in
/-- **The genus formula with local `δ`-invariants** for given conductor elements `σ₀`, `σ_∞` of
the two reduced charts (S7⁺.7): for `M ≫ 0`,
`g(F) + #{w} - 1 = Σ_w g(κ(w)) + Σ_y δ_y^{(M)}`, where `y` runs over the closed points of the
chart at `0` containing `σ₀` and the closed points of the chart at `∞` over `x̄ = ∞` containing
`σ_∞`. -/
theorem genus_eq_sum_delta_of_conductor [CharZero C] {σ₀ σi : Π w : Ext C F,
      ResidueField w.1.valuationSubring}
    (hσ₀ : σ₀ ∈ redRing C F (xF C F)) (hσ₀0 : ∀ w, σ₀ w ≠ 0)
    (hσ₀c : ∀ v ∈ regRing 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
      (fun w : Ext C F ↦ red C (xF C F) w), σ₀ * v ∈ redRing C F (xF C F))
    (hσi : σi ∈ redRing C F (xF C F)⁻¹) (hσi0 : ∀ w, σi w ≠ 0)
    (hσic : ∀ v ∈ regRing 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
      (fun w : Ext C F ↦ red C (xF C F)⁻¹ w), σi * v ∈ redRing C F (xF C F)⁻¹) :
    ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (genus C F : ℤ) + Fintype.card (Ext C F) - 1 =
        (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) +
        (∑ y ∈ points (isChart_x hb) σ₀,
          (delta 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) (isChart_x hb) σ₀ y M
            : ℤ)) +
        ∑ y ∈ (points (isChart_x_inv hb) σi).filter
            (fun y ↦ (⟨_, (isChart_x_inv hb).mem⟩ : redRing C F (xF C F)⁻¹) ∈ y),
          (delta 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) (isChart_x_inv hb) σi
            y M : ℤ) := by
  classical
  set hΛ₀ := isChart_x hb
  set hΛi := isChart_x_inv hb
  obtain ⟨M₁, hM₁⟩ := mem_of_forall_mem_sup hΛ₀ hσ₀ hσ₀0 hσ₀c
  obtain ⟨M₂, hM₂⟩ := mem_of_forall_mem_sup hΛi hσi hσi0 hσic
  obtain ⟨m₀, hm₀⟩ := genus_add_card_sub_one_eq hb hsum
  refine ⟨max M₁ M₂, fun M hM ↦ ?_⟩
  set Y₀ := points hΛ₀ σ₀
  set Yi := (points hΛi σi).filter
    (fun y ↦ (⟨_, hΛi.mem⟩ : redRing C F (xF C F)⁻¹) ∈ y)
  -- the branches, and a residue `ā` avoided by the branches at `0`
  set S₀ := Y₀.biUnion fun y ↦ branches hΛ₀ σ₀ y
  set Si := Yi.biUnion fun y ↦ branches hΛi σi y
  obtain ⟨ab, hab⟩ := Infinite.exists_notMem_finset
    (S₀.image fun b ↦ b.2.res (red C (xF C F) b.1))
  set T₀ : (w : Ext C F) → Finset (CurvePlace 𝓀 (ResidueField w.1.valuationSubring)) :=
    fun w ↦ S₀.preimage (fun Q ↦ (⟨w, Q⟩ : Branch 𝓀 _)) fun _ _ _ _ h ↦
      eq_of_heq (Sigma.mk.inj_iff.1 h).2
  set Ti : (w : Ext C F) → Finset (CurvePlace 𝓀 (ResidueField w.1.valuationSubring)) :=
    fun w ↦ Si.preimage (fun Q ↦ (⟨w, Q⟩ : Branch 𝓀 _)) fun _ _ _ _ h ↦
      eq_of_heq (Sigma.mk.inj_iff.1 h).2
  have hT₀ (w : Ext C F) : ∀ Q ∈ T₀ w, red C (xF C F) w ∈ Q.V ∧ Q.res (red C (xF C F) w) ≠ ab :=
    fun Q hQ ↦ by
      have hb' : (⟨w, Q⟩ : Branch 𝓀 _) ∈ S₀ := Finset.mem_preimage.1 hQ
      obtain ⟨y, hy, hyb⟩ := Finset.mem_biUnion.1 hb'
      refine ⟨mem_V_of_mem_branches hΛ₀ (isMaximal_of_mem_points hΛ₀ hy).ne_top hyb,
        fun h ↦ hab (Finset.mem_image.2 ⟨_, hb', h⟩)⟩
  have hTi (w : Ext C F) : ∀ Q ∈ Ti w, red C (xF C F) w ∉ Q.V := fun Q hQ hxQ ↦ by
    have hb' : (⟨w, Q⟩ : Branch 𝓀 _) ∈ Si := Finset.mem_preimage.1 hQ
    obtain ⟨y, hy, hyb⟩ := Finset.mem_biUnion.1 hb'
    obtain ⟨hy1, hz⟩ := Finset.mem_filter.1 hy
    have hne := (isMaximal_of_mem_points hΛi hy1).ne_top
    have hcen : centerOf hΛi ⟨w, Q⟩ = y := (Finset.mem_filter.1 hyb).2
    have hzQ := mem_V_of_mem_branches hΛi hne hyb
    unfold centerOf at hcen
    rw [dif_pos hzQ] at hcen
    rw [← hcen, mem_center] at hz
    change Q.valuation (red C (xF C F)⁻¹ w) < 1 at hz
    rw [red_inv_xF, map_inv₀] at hz
    have h1 := Q.valuation_le_one_iff.2 hxQ
    have hx0 : red C (xF C F) w ≠ 0 := fun h ↦ transcendental_red_x w (h ▸ isAlgebraic_zero)
    have hpos : 0 < Q.valuation (red C (xF C F) w) := (Valuation.pos_iff _).2 hx0
    exact absurd ((inv_lt_one₀ hpos).1 hz) (not_lt.2 h1)
  choose m₁ hm₁ using fun w : Ext C F ↦
    exists_jet_twist (transcendental_red_x w) ab (T₀ w) (Ti w) (hT₀ w) (hTi w) M
  set m := max m₀ (Finset.univ.sup m₁)
  obtain ⟨hHW, hgen⟩ := hm₀ m (le_max_left _ _)
  have hmw (w : Ext C F) : m₁ w ≤ m :=
    (Finset.le_sup (f := m₁) (Finset.mem_univ w)).trans (le_max_right _ _)
  set W := piRR C F m
  set H := secSpace C F m
  -- the local quotients
  let A₀ (y : Y₀) := regAt 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
    (branches hΛ₀ σ₀ y.1)
  let Ai (y : Yi) := regAt 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring)
    (branches hΛi σi y.1)
  let B₀ (y : Y₀) : Submodule 𝓀 (A₀ y) :=
    (locSpace 𝓀 y.1 ⊔ jetKer 𝓀 _ M (branches hΛ₀ σ₀ y.1)).comap (A₀ y).subtype
  let Bi (y : Yi) : Submodule 𝓀 (Ai y) :=
    (locSpace 𝓀 y.1 ⊔ jetKer 𝓀 _ M (branches hΛi σi y.1)).comap (Ai y).subtype
  have hne₀ (y : Y₀) : y.1 ≠ ⊤ := (isMaximal_of_mem_points hΛ₀ y.2).ne_top
  have hnei (y : Yi) : y.1 ≠ ⊤ :=
    (isMaximal_of_mem_points hΛi (Finset.mem_filter.1 y.2).1).ne_top
  have hfin₀ (y : Y₀) : FiniteDimensional 𝓀 (A₀ y ⧸ B₀ y) :=
    finiteDimensional_regAt_quot hΛ₀.tr (fun b hb ↦ mem_V_of_mem_branches hΛ₀ (hne₀ y) hb) M _
  have hfini (y : Yi) : FiniteDimensional 𝓀 (Ai y ⧸ Bi y) :=
    finiteDimensional_regAt_quot hΛi.tr (fun b hb ↦ mem_V_of_mem_branches hΛi (hnei y) hb) M _
  -- the local maps
  have hW₀ (y : Y₀) : W ≤ A₀ y := fun v hv b hb ↦
    piRR_mem_V hv b.1 b.2 (mem_V_of_mem_branches hΛ₀ (hne₀ y) hb)
  let mi : (Π w : Ext C F, ResidueField w.1.valuationSubring) →ₗ[𝓀]
      (Π w : Ext C F, ResidueField w.1.valuationSubring) :=
    { toFun := fun v w ↦ red C (xF C F)⁻¹ w ^ m * v w
      map_add' := fun v v' ↦ funext fun w ↦ mul_add _ _ _
      map_smul' := fun c v ↦ funext fun w ↦ by
        change red C (xF C F)⁻¹ w ^ m * (c • v w) = c • (red C (xF C F)⁻¹ w ^ m * v w)
        rw [Algebra.smul_def, Algebra.smul_def]
        ring }
  have hmi (v : Π w : Ext C F, ResidueField w.1.valuationSubring) :
      mi v = fun w ↦ red C (xF C F)⁻¹ w ^ m * v w := rfl
  have hWi (y : Yi) (v : W) : mi v ∈ Ai y := fun b hb ↦ by
    rw [hmi]
    exact piRR_mem_V_inv v.2 b.1 b.2 (mem_V_of_mem_branches hΛi (hnei y) hb)
  let φ₀ (y : Y₀) : W →ₗ[𝓀] A₀ y := Submodule.inclusion (hW₀ y)
  let φi (y : Yi) : W →ₗ[𝓀] Ai y := LinearMap.codRestrict _ (mi.comp W.subtype) (hWi y)
  -- the kernel lies in `H`
  have hker (v : W) (h₀ : ∀ y, φ₀ y v ∈ B₀ y) (hi : ∀ y, φi y v ∈ Bi y) :
      (v : Π w : Ext C F, ResidueField w.1.valuationSubring) ∈ H := by
    have hv := v.2
    have hv₀ : (v : Π w : Ext C F, ResidueField w.1.valuationSubring) ∈
        regRing 𝓀 _ (fun w : Ext C F ↦ red C (xF C F) w) := fun w Q hQ ↦ piRR_mem_V hv w Q hQ
    have hvΛ : (v : Π w : Ext C F, ResidueField w.1.valuationSubring) ∈ redRing C F (xF C F) :=
      hM₁ M (le_of_max_le_left hM) _ hv₀ fun y hy ↦ by
        exact h₀ ⟨y, hy⟩
    let u := mi v
    have hu : u ∈ regRing 𝓀 _ (fun w : Ext C F ↦ red C (xF C F)⁻¹ w) := fun w Q hQ ↦ by
      change red C (xF C F)⁻¹ w ^ m * (v : Π w : Ext C F, ResidueField w.1.valuationSubring) w ∈ Q.V
      exact piRR_mem_V_inv hv w Q hQ
    obtain ⟨a, ha, hav⟩ := hvΛ
    obtain ⟨D, hD⟩ := exists_pow_mul_mem_intRing_x_inv ha
    have huΛ : u ∈ redRing C F (xF C F)⁻¹ := hM₂ M (le_of_max_le_right hM) u hu fun y hy ↦ by
      by_cases hz : (⟨_, hΛi.mem⟩ : redRing C F (xF C F)⁻¹) ∈ y
      · exact hi ⟨y, Finset.mem_filter.2 ⟨hy, hz⟩⟩
      · refine Submodule.mem_sup_left (subset_locSpace (k := 𝓀) y ⟨⟨_, hΛi.mem⟩ ^ D, ?_, ?_⟩)
        · haveI := (isMaximal_of_mem_points hΛi hy).isPrime
          exact fun h ↦ hz (Ideal.IsPrime.mem_of_pow_mem inferInstance D h)
        · have hmem : (fun w ↦ red C ((xF C F)⁻¹ ^ m) w) *
              (fun w ↦ red C ((xF C F)⁻¹ ^ D * a) w) ∈ redRing C F (xF C F)⁻¹ :=
            mul_mem (red_mem_redRing (pow_mem_intRing_x_inv m)) (red_mem_redRing hD)
          convert hmem using 1
          funext w
          have hxw : w.1 (xF C F)⁻¹ ≤ 1 := (valuation_xF_inv w).le
          have haw : w.1 a ≤ 1 := (le_gnorm w a).trans ha.2
          have hxDw : w.1 ((xF C F)⁻¹ ^ D) ≤ 1 := by
            rw [map_pow]; exact pow_le_one₀ zero_le hxw
          simp only [Pi.mul_apply, SubmonoidClass.coe_pow, Pi.pow_apply, u, hmi, ← hav]
          rw [red_pow hxw, red_mul hxDw haw, red_pow hxw]
          ring
    refine ⟨⟨a, ha, hav⟩, u, huΛ, fun w ↦ ?_⟩
    have hx0 : red C (xF C F) w ≠ 0 := fun h ↦ transcendental_red_x w (h ▸ isAlgebraic_zero)
    simp only [u, hmi, red_inv_xF]
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx0, one_pow, one_mul]
  have hcount := finrank_le_finrank_add_sum_quot W H hHW A₀ B₀ hfin₀ Ai Bi hfini φ₀ φi hker
  -- the reverse inequality: `H` lies in the kernel, and the local maps are jointly onto
  have hH (v : W) (hvH : (v : Π w : Ext C F, ResidueField w.1.valuationSubring) ∈ H) :
      (∀ y, φ₀ y v ∈ B₀ y) ∧ ∀ y, φi y v ∈ Bi y := by
    obtain ⟨hv₀, u, hu, huv⟩ := hvH
    refine ⟨fun y ↦ Submodule.mem_sup_left (subset_locSpace (k := 𝓀) y.1
      ⟨1, fun h ↦ hne₀ y ((Ideal.eq_top_iff_one _).2 h), ?_⟩), fun y ↦ ?_⟩
    · change (1 : redRing C F (xF C F)).1 * (v : Π w : Ext C F, ResidueField w.1.valuationSubring)
        ∈ _
      simpa using hv₀
    have hmu : mi v = u := by
      funext w
      change red C (xF C F)⁻¹ w ^ m * (v : Π w : Ext C F, ResidueField w.1.valuationSubring) w
        = u w
      have hx0 : red C (xF C F) w ≠ 0 := fun h ↦ transcendental_red_x w (h ▸ isAlgebraic_zero)
      rw [huv w, red_inv_xF, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hx0, one_pow, one_mul]
    refine Submodule.mem_sup_left (subset_locSpace (k := 𝓀) y.1
      ⟨1, fun h ↦ hnei y ((Ideal.eq_top_iff_one _).2 h), ?_⟩)
    change (1 : redRing C F (xF C F)⁻¹).1 * mi v ∈ _
    rw [hmu]
    simpa using hu
  have hsurj (a₀ : ∀ y, A₀ y) (ai : ∀ y, Ai y) : ∃ v : W,
      (∀ y, φ₀ y v - a₀ y ∈ B₀ y) ∧ ∀ y, φi y v - ai y ∈ Bi y := by
    set τ₀ : (w : Ext C F) → CurvePlace 𝓀 (ResidueField w.1.valuationSubring) →
        ResidueField w.1.valuationSubring := fun w Q ↦
      ∑ y : Y₀, if (⟨w, Q⟩ : Branch 𝓀 _) ∈ branches hΛ₀ σ₀ y.1 then (a₀ y).1 w else 0
    set τi : (w : Ext C F) → CurvePlace 𝓀 (ResidueField w.1.valuationSubring) →
        ResidueField w.1.valuationSubring := fun w Q ↦
      ∑ y : Yi, if (⟨w, Q⟩ : Branch 𝓀 _) ∈ branches hΛi σi y.1 then (ai y).1 w else 0
    -- the sums collapse
    have hcol₀ (y : Y₀) (b : Branch 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring))
        (hb : b ∈ branches hΛ₀ σ₀ y.1) : τ₀ b.1 b.2 = (a₀ y).1 b.1 := by
      refine (Finset.sum_eq_single y (fun y' _ hy' ↦ if_neg fun h ↦ hy' (Subtype.ext ?_))
        (by simp)).trans (if_pos hb)
      exact ((Finset.mem_filter.1 h).2).symm.trans (Finset.mem_filter.1 hb).2
    have hcoli (y : Yi) (b : Branch 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring))
        (hb : b ∈ branches hΛi σi y.1) : τi b.1 b.2 = (ai y).1 b.1 := by
      refine (Finset.sum_eq_single y (fun y' _ hy' ↦ if_neg fun h ↦ hy' (Subtype.ext ?_))
        (by simp)).trans (if_pos hb)
      exact ((Finset.mem_filter.1 h).2).symm.trans (Finset.mem_filter.1 hb).2
    have hreg₀ (w : Ext C F) : ∀ Q ∈ T₀ w, τ₀ w Q ∈ Q.V := fun Q _ ↦
      sum_mem fun y _ ↦ by
        split_ifs with h
        · exact (a₀ y).2 _ h
        · exact zero_mem _
    have hregi (w : Ext C F) : ∀ Q ∈ Ti w, τi w Q ∈ Q.V := fun Q _ ↦
      sum_mem fun y _ ↦ by
        split_ifs with h
        · exact (ai y).2 _ h
        · exact zero_mem _
    choose f hf hf₀ hfi using fun w ↦ hm₁ w m (hmw w) (τ₀ w) (τi w) (hreg₀ w) (hregi w)
    refine ⟨⟨f, fun w _ ↦ hf w⟩, fun y ↦ ?_, fun y ↦ ?_⟩
    · refine Submodule.mem_sup_right fun b hb ↦ ?_
      change b.2.valuation (f b.1 - (a₀ y).1 b.1) ≤ _
      rw [← hcol₀ y b hb]
      exact hf₀ b.1 b.2 (Finset.mem_preimage.2 (Finset.mem_biUnion.2 ⟨y.1, y.2, hb⟩))
    · refine Submodule.mem_sup_right fun b hb ↦ ?_
      change b.2.valuation (red C (xF C F)⁻¹ b.1 ^ m * f b.1 - (ai y).1 b.1) ≤ _
      rw [← hcoli y b hb, red_inv_xF]
      exact hfi b.1 b.2 (Finset.mem_preimage.2 (Finset.mem_biUnion.2 ⟨y.1, y.2, hb⟩))
  have hcount2 := finrank_add_sum_le_of_surj W H hHW A₀ B₀ hfin₀ Ai Bi hfini φ₀ φi hH hsurj
  rw [hgen]
  clear hker hgen hHW hH hsurj
  have e₀ : ∑ y : Y₀, Module.finrank 𝓀 (A₀ y ⧸ B₀ y) =
      ∑ y ∈ Y₀, delta 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) hΛ₀ σ₀ y M :=
    Finset.sum_coe_sort Y₀ (fun y ↦ delta 𝓀 _ hΛ₀ σ₀ y M)
  have ei : ∑ y : Yi, Module.finrank 𝓀 (Ai y ⧸ Bi y) =
      ∑ y ∈ Yi, delta 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) hΛi σi y M :=
    Finset.sum_coe_sort Yi (fun y ↦ delta 𝓀 _ hΛi σi y M)
  rw [e₀, ei] at hcount hcount2
  have key := (Nat.cast_le (α := ℤ)).2 hcount
  have key2 := (Nat.cast_le (α := ℤ)).2 hcount2
  push_cast at key key2
  linarith

open Classical in
include hsum in
/-- **The genus formula with local `δ`-invariants** (S7⁺.7): there are conductor elements `σ₀`,
`σ_∞` of the two reduced charts such that for `M ≫ 0`,
`g(F) + #{w} - 1 = Σ_w g(κ(w)) + Σ_y δ_y^{(M)}`, where `y` runs over the closed points of the
chart at `0` containing `σ₀` and the closed points of the chart at `∞` over `x̄ = ∞` containing
`σ_∞` (every closed point with `δ_y ≠ 0` is among them). Equivalently
`g(F) = 1 + Σ_w (g(κ(w)) - 1) + Σ_y δ_y`. -/
theorem exists_genus_eq_sum_delta [CharZero C] :
    ∃ σ₀ ∈ redRing C F (xF C F), ∃ σi ∈ redRing C F (xF C F)⁻¹, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
      (genus C F : ℤ) + Fintype.card (Ext C F) - 1 =
        (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) +
        (∑ y ∈ points (isChart_x hb) σ₀,
          (delta 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) (isChart_x hb) σ₀ y M
            : ℤ)) +
        ∑ y ∈ (points (isChart_x_inv hb) σi).filter
            (fun y ↦ (⟨_, (isChart_x_inv hb).mem⟩ : redRing C F (xF C F)⁻¹) ∈ y),
          (delta 𝓀 (fun w : Ext C F ↦ ResidueField w.1.valuationSubring) (isChart_x_inv hb) σi
            y M : ℤ) := by
  obtain ⟨σ₀, hσ₀, hσ₀0, hσ₀c⟩ := exists_conductor_x hb hsum
  obtain ⟨σi, hσi, hσi0, hσic⟩ := exists_conductor_x_inv hb hsum
  exact ⟨σ₀, hσ₀, σi, hσi,
    genus_eq_sum_delta_of_conductor hb hsum hσ₀ hσ₀0 hσ₀c hσi hσi0 hσic⟩

end Main

end GaussFibre

end SemistableReduction
