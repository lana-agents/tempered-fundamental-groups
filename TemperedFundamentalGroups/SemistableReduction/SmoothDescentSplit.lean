/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothFinal

/-!
# Descent of smooth points, smooth form

Blueprint §9.7a, step 4; §10.3.8 (StrongComponentA (a)). `W10Route.SmoothDescentSplitStatement`
is `W10Route.SmoothDescentStatement` with the conclusion strengthened from `IsSemistableAt` to
"étale-locally the affine line" (`IsEtaleLocallyAt O_E O_E[X]`), and
`W10Route.smoothDescentSplitStatement` proves it (from `isEtaleLocallyAt_of_isDiscSmooth_residue`).
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge DVRDescent

/-- **Descent of smooth points, smooth form** (pointwise): as `SmoothDescentStatement`, with the
descended point étale-locally the affine line over `O_E`. -/
def SmoothDescentSplitStatement : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ) (_ : p.Prime) (_ : ‖(p : C)‖ < 1)
    (G : Type u) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
    [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
    (T : Finset G) (_ : Algebra.adjoin (RatFunc C) (T : Set G) = ⊤),
    ∃ S : Finset C, ∀ (E : Type u) [NontriviallyNormedField E] [IsUltrametricDist E]
      [CompleteSpace E] (φ : E →+* C) (hφ : ∀ e, ‖φ e‖ = ‖e‖) (_ : (S : Set C) ⊆ Set.range φ)
      (_ : letI := φ.toAlgebra; Algebra.IsAlgebraic E C)
      [IsDiscreteValuationRing (NormedField.valuation (K := E)).valuationSubring]
      [PerfectField (ResidueField (NormedField.valuation (K := E)).valuationSubring)]
      (F₀ : Type u) [Field F₀] [Algebra (RatFunc E) F₀] [Algebra E F₀]
      [IsScalarTower E (RatFunc E) F₀] [FiniteDimensional (RatFunc E) F₀]
      [Algebra.IsSeparable (RatFunc E) F₀]
      (χ : F₀ →+* G)
      (hχ : ∀ x, χ (algebraMap (RatFunc E) F₀ x) = algebraMap (RatFunc C) G (ratFuncMap φ x))
      (_ : Module.finrank (RatFunc E) F₀ = Module.finrank (RatFunc C) G)
      (_ : (T : Set G) ⊆ Set.range χ)
      (ϖ : (NormedField.valuation (K := E)).valuationSubring) (_ : Irreducible ϖ)
      [Algebra (NormedField.valuation (K := E)).valuationSubring (DRint (0 : E) 1 F₀)]
      (_ : ∀ o, ((algebraMap (NormedField.valuation (K := E)).valuationSubring
        (DRint (0 : E) 1 F₀) o : DRint (0 : E) 1 F₀) : F₀) = algebraMap E F₀ o)
      (β : C) (hβ : ‖β‖ ≤ 1) (P' : Ideal (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))),
      P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff β 1 one_ne_zero G))) =
        discIdeal (0 : C) 1 →
      IsDiscSmooth P' →
      IsEtaleLocallyAt (NormedField.valuation (K := E)).valuationSubring
        (NormedField.valuation (K := E)).valuationSubring[X] (P'.comap (ιβ χ hφ hχ hβ))

/-- **Descent of smooth points, smooth form.** -/
theorem smoothDescentSplitStatement : SmoothDescentSplitStatement.{u} := by
  intro C _ _ _ _ p hp hp1 G _ _ _ _ _ T hT
  obtain ⟨S, hS⟩ := SmoothHyps.exists_finset_smoothHyps.{u, u, u} (C := C) (G := G) hp hp1 hT
  refine ⟨S, ?_⟩
  intro E _ _ _ φ hφ hSφ halg _ _ F₀ _ _ _ _ _ _ χ hχ hdeg hTχ ϖ hϖ inst hinst β hβ P' hmax hP'
    hsm
  obtain ⟨⟨θ₀, hθ⟩, hinj, hgen, hspan⟩ := hS φ hφ hSφ χ hχ hdeg hTχ
  have hI : inst = bdAlgebra (E := E) (F₀ := F₀) := by
    refine Algebra.algebra_ext _ _ fun o ↦ Subtype.ext ?_
    rw [hinst]
    exact (IsScalarTower.algebraMap_apply E (RatFunc E) F₀ o).trans rfl
  subst hI
  haveI := hmax
  exact isEtaleLocallyAt_of_isDiscSmooth_residue hp hp1 hφ hχ halg hdeg hθ hinj hgen hspan hϖ hβ P'
    hP' hsm

end W10Route

end SemistableReduction
