/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AlgStrRingHom01
import TemperedFundamentalGroups.SemistableReduction.NormalisedModel
import TemperedFundamentalGroups.SemistableReduction.KaehlerAlgStr
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Points of the second chart extend to the overlap and the first chart (generic; MR13 A2⁻)

For a chart algebra `B` over `A` (rings `B₀`, `B₁`, `B₀₁` of `𝒴` over `Spec A[X]`, `Spec A[Y]` and
the overlap) and a ring map `u : B₁ → Ω` with `u(Y)` a unit:

* **`AlgStr.lift01 u hu : B₀₁ → Ω`** (`B₀₁ = B₁[1/Y]`), `lift01_r1Hom`, `ext01`; **`AlgStr.lift0`**
  `= lift01 ∘ r0Hom : B₀ → Ω`;
* **`AlgStr.IsHom.lift0_equivariant`**: for an endomorphism `h : B → B` of chart algebras and
  `σ : Ω → Ω` with `σ ∘ u = u ∘ h₁`, also `σ ∘ lift0 = lift0 ∘ h₀`;
* **`AlgStr.mem_of_X0`**: if `u₀ : B₀ → Ω` (`Ω` a field, `B₀` finite over `A[X]`) maps the
  constants and `X` into a valuation subring `W`, it maps all of `B₀` into `W`.

Used for "A2⁻" (MR13-plan, run 16): a geometric point `φ` of the generic fibre of the lift over
`V₁` extends to the cusp chart `B₀`; at a place `W` over a cusp, the residue map of `W` composed
with `lift0 φ` is the point `χ` of `P1Three.Datum.exists_fixed_special_point`, and inertia
elements of `W` satisfy its hypothesis.
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

namespace AlgStr

variable {A : Type u} [CommRing A] {M : ChartModule A} (B : AlgStr M) {Ω : Type*} [CommRing Ω]

/-- **The extension of `u : B₁ → Ω` to the overlap `B₀₁ = B₁[1/Y]`** (`u(Y)` a unit). -/
noncomputable def lift01 (u : B.Ring1 →+* Ω) (hu : IsUnit (u B.X1)) : B.Ring01 →+* Ω :=
  letI := B.r1Hom.toAlgebra
  haveI := B.isLocalization_r1
  IsLocalization.Away.lift B.X1 hu

lemma lift01_r1Hom (u : B.Ring1 →+* Ω) (hu : IsUnit (u B.X1)) (b : B.Ring1) :
    B.lift01 u hu (B.r1Hom b) = u b := by
  letI := B.r1Hom.toAlgebra
  haveI := B.isLocalization_r1
  exact IsLocalization.lift_eq _ b

/-- Maps out of the overlap are determined on the second chart. -/
lemma ext01 (f g : B.Ring01 →+* Ω) (h : ∀ b, f (B.r1Hom b) = g (B.r1Hom b)) : f = g := by
  letI := B.r1Hom.toAlgebra
  haveI := B.isLocalization_r1
  exact IsLocalization.ringHom_ext (Submonoid.powers B.X1) (RingHom.ext h)

/-- **The extension of `u : B₁ → Ω` to the first chart `B₀`** (through the overlap). -/
noncomputable def lift0 (u : B.Ring1 →+* Ω) (hu : IsUnit (u B.X1)) : B.Ring0 →+* Ω :=
  (B.lift01 u hu).comp B.r0Hom

lemma lift0_apply (u : B.Ring1 →+* Ω) (hu : IsUnit (u B.X1)) (b : B.Ring0) :
    B.lift0 u hu b = B.lift01 u hu (B.r0Hom b) :=
  rfl

/-- **Inverse coordinates**: if `r0Hom b₀ · r1Hom b₁ = 1` on the overlap, then
`lift0 u (b₀) · u (b₁) = 1`. -/
lemma lift0_mul_eq_one (u : B.Ring1 →+* Ω) (hu : IsUnit (u B.X1)) {b₀ : B.Ring0} {b₁ : B.Ring1}
    (h : B.r0Hom b₀ * B.r1Hom b₁ = 1) : B.lift0 u hu b₀ * u b₁ = 1 := by
  rw [lift0_apply, ← lift01_r1Hom B u hu b₁, ← map_mul, h, map_one]

/-- `lift0 u (X) = u(Y)⁻¹`. -/
lemma lift0_X0_mul (u : B.Ring1 →+* Ω) (hu : IsUnit (u B.X1)) : B.lift0 u hu B.X0 * u B.X1 = 1 :=
  B.lift0_mul_eq_one u hu (by rw [B.r0Hom_X0, B.r1Hom_X1, B.T01_mul_Tinv])

/-- For a morphism of chart algebras from a model `D`: elements inverse to each other on the
overlap of `D` map to elements inverse to each other on the overlap of `B`. -/
lemma IsHom.r0Hom_mul_r1Hom {D : TwoChartRings A} {φ : Hom D.chartModule M}
    (h : D.algStr.IsHom B φ) {m₀ : D.R0} {m₁ : D.R1} (hm : D.ρ0 m₀ * D.ρ1 m₁ = 1) :
    B.r0Hom (h.ringHom0 ((TwoChartRings.ring0Equiv D).symm m₀)) *
      B.r1Hom (h.ringHom1 ((TwoChartRings.ring1Equiv D).symm m₁)) = 1 := by
  rw [← h.ringHom01_ρ0, ← h.ringHom01_ρ1, ← map_mul, hm, map_one]

variable {B}

/-- **Equivariance of the extension**: for an endomorphism `h` of `B` and `σ : Ω → Ω` with
`σ ∘ u = u ∘ h₁` on `B₁`, also `σ ∘ lift0 u = lift0 u ∘ h₀` on `B₀`. -/
theorem IsHom.lift0_equivariant {φ : Hom M M} (h : B.IsHom B φ) (u : B.Ring1 →+* Ω)
    (hu : IsUnit (u B.X1)) (σ : Ω →+* Ω) (hσ : ∀ b, σ (u b) = u (h.ringHom1 b)) (b : B.Ring0) :
    σ (B.lift0 u hu b) = B.lift0 u hu (h.ringHom0 b) := by
  have key : σ.comp (B.lift01 u hu) = (B.lift01 u hu).comp h.ringHom01' :=
    B.ext01 _ _ fun c ↦ by
      rw [RingHom.comp_apply, RingHom.comp_apply, lift01_r1Hom, hσ, h.ringHom01'_r1Hom,
        lift01_r1Hom]
  rw [lift0_apply, lift0_apply, ← RingHom.comp_apply, key, RingHom.comp_apply,
    h.ringHom01'_r0Hom]

variable (B)

/-- **Integrality into a valuation subring**: a ring map `u₀ : B₀ → Ω` (`B₀` finite over `A[X]`)
sending the constants and `X` into a valuation subring `W` sends all of `B₀` into `W`. -/
theorem mem_of_X0 [Module.Finite A[X] (Module.AEval' M.x0)] {Ω : Type*} [Field Ω]
    (W : ValuationSubring Ω) (u : B.Ring0 →+* Ω) (hc : ∀ a, u (B.const0 a) ∈ W)
    (hX : u B.X0 ∈ W) (b : B.Ring0) : u b ∈ W := by
  letI := B.polyHom0.toAlgebra
  haveI := B.finite_polyHom0
  have hpoly : ∀ p : A[X], u (algebraMap A[X] B.Ring0 p) ∈ W := fun p ↦ by
    change u (Polynomial.eval₂ B.const0 B.X0 p) ∈ W
    rw [Polynomial.hom_eval₂]
    induction p using Polynomial.induction_on with
    | C a => simpa using hc a
    | add p q hp hq => rw [Polynomial.eval₂_add]; exact W.add_mem _ _ hp hq
    | monomial n a h =>
      rw [pow_succ, ← mul_assoc, Polynomial.eval₂_mul_X]
      exact W.mul_mem _ _ h hX
  let φ : A[X] →+* W := (u.comp (algebraMap A[X] B.Ring0)).codRestrict W.toSubring hpoly
  have hint : IsIntegral W (u b) :=
    IsIntegral.map_of_comp_eq φ u (RingHom.ext fun p ↦ rfl)
      (Algebra.IsIntegral.isIntegral (R := A[X]) b)
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  rw [← hy]
  exact y.2

end AlgStr

end ChartModule

end ProjectiveLine
