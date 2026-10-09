/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothDiscCoord
import TemperedFundamentalGroups.SemistableReduction.TubeSkeleton

/-!
# (D⇒): good open discs satisfy the valuative disc condition

Blueprint §9.12, O11g (D⇒). If every point over the open disc `|x - a| < |c|` is smooth
(`ExhaustGluing.DiscSmooth`), then every Gauss point inside it is a disc of a tube
(`ExhaustGluing.DiscCond`): an extension `w` of `w_{a + cβ, |cγ|}` is, on the twist by `(a, c)`, a
valuation over a disc valuation with a residually transcendental element; lemma (L)
(`SmoothDisc.exists_disc_coord`, `SmoothDisc.tube_of_coord`) gives a rational residue curve with
one point over `t̄ = ∞`.

* `ExhaustGluing.affId_xF`: `x = γ x' + β` between the twists `(a, c)` and `(a + cβ, cγ)`;
* `ExhaustGluing.isTubeDisc_of_discSmooth`;
* **`ExhaustGluing.discCondOfSmooth`**: `DiscCondOfSmooth C F'` (no further hypotheses besides
  `C` algebraically closed of characteristic `0` with `‖p‖ < 1`).
-/

open Polynomial IsLocalRing WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace ExhaustGluing

open GaussTube GaussFibre GaussStability AffineTwist PlaceNorm SmoothDisc DiscCount SmoothVertex

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] in
/-- `x` of the twist `(a, c)` in the twist `(a + cβ, cγ)`: `x = γ x' + β`. -/
lemma affId_xF {a c β γ : C} (hc : c ≠ 0) (hγ : γ ≠ 0) :
    affId (F' := F') (a := a) (a' := a + c * β) hc (mul_ne_zero hc hγ) (xF C (Aff a c hc F')) =
      algebraMap C (Aff (a + c * β) (c * γ) (mul_ne_zero hc hγ) F') γ *
        xF C (Aff (a + c * β) (c * γ) (mul_ne_zero hc hγ) F') +
      algebraMap C (Aff (a + c * β) (c * γ) (mul_ne_zero hc hγ) F') β := by
  rw [xF_aff, xF_aff]
  have hg : gaussCoord a c = algebraMap C (RatFunc C) γ * gaussCoord (a + c * β) (c * γ) +
      algebraMap C (RatFunc C) β := by
    rw [gaussCoord_eq, gaussCoord_eq]
    have hc' : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
    have hγ' : algebraMap C (RatFunc C) γ ≠ 0 := by simpa using hγ
    simp only [map_inv₀, map_mul, map_add]
    field_simp
    ring
  change toAff (mul_ne_zero hc hγ) (algebraMap (RatFunc C) F' (gaussCoord a c)) = _
  rw [hg, map_add, map_mul, map_add, map_mul, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]
  rfl

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
include hp hp1

/-- **Discs inside a good open disc.** If every point over the open disc `|x - a| < |c|` is
smooth, then every Gauss point `w_{a + cβ, |cγ|}` (`|β| < 1`, `0 < |γ| < 1`) is a disc of a tube:
lemma (L) at the point below each extension. -/
theorem isTubeDisc_of_discSmooth {a c : C} (hc : c ≠ 0) (hsm : DiscSmooth F' a hc) {β γ : C}
    (hβ : ‖β‖ < 1) (hγ : γ ≠ 0) (hγ1 : ‖γ‖ < 1) :
    IsTubeDisc F' (a + c * β) (mul_ne_zero hc hγ) := by
  intro w
  set K := Aff (a + c * β) (c * γ) (mul_ne_zero hc hγ) F'
  set G := Aff a c hc F'
  set ι : G ≃+* K := affId (F' := F') (a := a) (a' := a + c * β) hc (mul_ne_zero hc hγ)
  let ιa : G ≃ₐ[C] K := { ι with commutes' := fun _ ↦ rfl }
  have hιa (y : G) : ιa y = ι y := rfl
  have hιq (y : G) (Q : C[X]) : aeval (ιa y) Q = ι (aeval y Q) :=
    aeval_algHom_apply ιa.toAlgHom y Q
  set W : Valuation G ℝ≥0 := w.1.comap ι.toRingHom
  have hWι (y : G) : W y = w.1 (ι y) := rfl
  have hιx := affId_xF (F' := F') (a := a) (β := β) hc hγ
  have hwC (b : C) : w.1 (algebraMap C K b) = ‖b‖₊ := valuation_algebraMap_C' w b
  -- `W` lies over a disc valuation
  have hW : IsDiscVal (0 : C) 1 (W.comap (algebraMap (RatFunc C) G)) := by
    refine ⟨fun b ↦ ?_, ?_⟩
    · rw [Valuation.comap_apply, ← IsScalarTower.algebraMap_apply, hWι]
      exact hwC b
    · rw [gaussCoord_zero_one, Valuation.comap_apply]
      change W (xF C G) < 1
      rw [hWι, hιx]
      refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
      · rw [map_mul, hwC, valuation_xF, mul_one]
        exact_mod_cast hγ1
      · rw [hwC]
        exact_mod_cast hβ
  -- a residually transcendental element
  have hy₀ : ∀ Q : C[X], W (aeval (ι.symm (xF C K)) Q) =
      Gauss.sup (NormedField.valuation (K := C)) 1 Q := fun Q ↦ by
    rw [hWι, ← hιq, hιa, RingEquiv.apply_symm_apply, aeval_xF,
      ← Valuation.comap_apply, w.2, gauss1_algebraMap]
  obtain ⟨Z, ha, hb, hc'⟩ := exists_disc_coord hp hp1 hsm W hW hy₀
  refine tube_of_coord w (Z := ιa Z) (fun Q ↦ ?_) (fun f ↦ ?_) ?_
  · rw [hιq, ← hWι]
    exact ha Q
  · obtain ⟨A, B, hB0, hAB⟩ := hb (ι.symm f)
    refine ⟨A, B, ?_, ?_⟩
    · rw [hιq]
      exact (map_ne_zero ι).2 hB0
    · rw [hιq, hιq, ← map_div₀,
        ← RingEquiv.apply_symm_apply ι f, ← map_sub, ← hWι]
      exact hAB
  · have hγpos : (0 : ℝ) < ‖γ‖ := norm_pos_iff.2 hγ
    obtain ⟨H, hH⟩ := hc' ‖γ‖ hγpos
    refine ⟨Polynomial.C γ⁻¹ * (H - Polynomial.C β), ?_⟩
    have hγK : algebraMap C K γ ≠ 0 := by simpa using hγ
    have hxK : xF C K = algebraMap C K γ⁻¹ * (ι (xF C G) - algebraMap C K β) := by
      rw [hιx, add_sub_cancel_right, map_inv₀, inv_mul_cancel_left₀ hγK]
    have heq : xF C K - aeval (ιa Z) (Polynomial.C γ⁻¹ * (H - Polynomial.C β)) =
        algebraMap C K γ⁻¹ * ι (xF C G - aeval Z H) := by
      rw [hxK, map_mul, aeval_C, map_sub, aeval_C, hιq, map_sub]
      ring
    rw [heq, map_mul, hwC, ← hWι, nnnorm_inv]
    have hγ0 : (0 : ℝ≥0) < ‖γ‖₊ := nnnorm_pos.2 hγ
    rw [inv_mul_lt_iff₀ hγ0, mul_one]
    exact_mod_cast hH

/-- **(D⇒)** `DiscCondOfSmooth` (Blueprint §9.12 O11g): over a good open disc the valuative disc
condition holds. -/
theorem discCondOfSmooth : DiscCondOfSmooth C F' := fun a c hc hsm ↦
  ⟨fun γ hγ h1 ↦ (isTubeDisc_congr _ _ (by ring) rfl).1
      (isTubeDisc_of_discSmooth hp hp1 hc hsm (β := 0) (by simp) hγ h1),
    fun β γ hγ h1 h2 ↦ isTubeDisc_of_discSmooth hp hp1 hc hsm h1 hγ (h2.trans h1)⟩

end ExhaustGluing
end SemistableReduction
