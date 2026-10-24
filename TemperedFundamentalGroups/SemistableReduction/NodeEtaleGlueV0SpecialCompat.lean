/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0SpecialR0
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Base

/-!
# The special fibre of the algebraized covering as a chart datum (Blueprint §12.8, M2.5 (b))

For a flat algebraization `(N, B, α)` of `S = V.system` (generic over `NodeEtaleGlue.Overlap`)
with `J = 0` on the bottom base chart and a bottom identification of the piece over `D(c₀)`, the
chart-wise identifications `B₀ ⧸ (ϖ) ≃ C0`, `B₁ ⧸ (ϖ) ≃ C1` (`specialFibreEquiv0/1`) are
compatible with the rest of the chart description of the special-fibre covering:

* **the overlap** (`specialFibre01`: `B₀₁ → (E 0).R01 = Q 0 ≃ C1[1/x̄₁]`):
  `specialFibre01_r1`: restriction from `V₁` is the localization `C1 → C1[1/x̄₁]`;
  `specialFibre01_r0`: restriction from `V₀` is `C0 → C0[1/x̄₀] ≃ω C1[1/x̄₁]` — so the glueing
  datum `ω` of the special-fibre covering is the reduction of the overlap of the algebraization;
* **the structure maps to the base model** (`BaseMap`): for a structure map `ψ : D → B` reducing
  to the level maps `β n` (`BaseMap.exists_structureMap'`), `specialFibreEquiv0_ψ`,
  `specialFibreEquiv1_ψ`: the reduction of `ψ` is the structure map `D.R_i → B0', B0 → C_i` of
  the special-fibre covering (the isomorphisms are linear over the base model).
-/

universe u

open Polynomial

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

namespace Overlap

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-! ### The bottom level -/

lemma fst_r0Equiv {n : ℕ} (hJ0 : J θ (R := I.B n) = ⊥) (bot : V.P0.Bottom n) (c : V.C0) :
    letI := V.algC0' n; letI := V.alg0'Q hθ n; letI := V.alg0'E n; letI := V.alg0'M n
    ZariskiTwo.fst (V.ρ0a hθ hO n) (V.ρ0b n) (V.r0Equiv hθ hO hJ0 bot c) =
      V.eQ hθ hO hJ0 (V.ω (algebraMap V.C0 (Localization.Away (algebraMap V.Bs' V.C0 V.x0s)) c)) :=
  rfl

variable {S : ProjectiveLine.AdicChartAlgSystem (Ideal.span {V.ϖ})}
  {N : ProjectiveLine.ChartModule O} {B : ProjectiveLine.ChartModule.AlgStr N}
  {α : ∀ n, ProjectiveLine.ChartModule.Hom N (S.M n)}

/-- **The special fibre of the algebraized covering over the overlap**:
`B₀₁ → (E 0).R01 = Q 0 ≃ C1[1/x̄₁]`. -/
def specialFibre01 (hS : V.system hθ hO = S) (hJ0 : J θ (R := I.B 0) = ⊥) :
    B.Ring01 → Localization.Away (algebraMap I.Bs I.C1 V.x1s) := by
  subst hS
  exact fun z ↦ (V.eQ hθ hO hJ0).symm ((α 1).f01 z)

variable (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom (S.alg n) (α n)) (hJ0 : J θ (R := I.B 0) = ⊥)

/-- `specialFibre01` for `S = V.system`. -/
lemma specialFibre01_rfl {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((V.system hθ hO).M n)}
    (z : B.Ring01) :
    V.specialFibre01 hθ hO (α := α) rfl hJ0 z = (V.eQ hθ hO hJ0).symm ((α 1).f01 z) := rfl

/-- The restriction maps of the bottom level of `V.system`. -/
lemma system_r1 (y : I.Y hθ 0) :
    ((V.system hθ hO).M 1).r1 y = algebraMap (I.Y hθ 0) (V.Q hθ 0) y := rfl

lemma system_r0 (y : (V.twoChart hθ hO 0).R0) :
    ((V.system hθ hO).M 1).r0 y = (V.twoChart hθ hO 0).ρ0 y := rfl

lemma specialFibreEquiv1_mk {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((V.system hθ hO).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((V.system hθ hO).alg n) (α n)) (b : B.Ring1) :
    specialFibreEquiv1 hθ hO rfl hα hB hJ0 (Ideal.Quotient.mk _ b) =
      (letI := I.algC10 0; (I.yEquiv hθ hO hJ0).symm ((α 1).f1 b)) := rfl

lemma specialFibreEquiv0_mk {α : ∀ n, ProjectiveLine.ChartModule.Hom N ((V.system hθ hO).M n)}
    (hα : ∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
      LinearMap.ker (α n).f0 = Ideal.span {V.ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {V.ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((V.system hθ hO).alg n) (α n)) (bot : V.P0.Bottom 0) (b : B.Ring0) :
    V.specialFibreEquiv0 hθ hO rfl hα hB hJ0 bot (Ideal.Quotient.mk _ b) =
      (V.r0Equiv' hθ hO hJ0 bot).symm ((α 1).f0 b) := rfl

/-- **The restriction from `V₁` to the overlap reduces to the localization** `C1 → C1[1/x̄₁]`. -/
theorem specialFibre01_r1 (hS : V.system hθ hO = S) (b : B.Ring1) :
    V.specialFibre01 hθ hO (α := α) hS hJ0 (B.r1Hom b) =
      algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
        (specialFibreEquiv1 hθ hO hS hα hB hJ0 (Ideal.Quotient.mk _ b)) := by
  subst hS
  letI := I.algC10 0
  rw [specialFibre01_rfl, B.r1Hom_apply, (α 1).comm_r1, system_r1, RingEquiv.symm_apply_eq,
    eQ_algebraMap, specialFibreEquiv1_mk, AlgEquiv.apply_symm_apply]

/-- **The restriction from `V₀` to the overlap reduces to `C0 → C0[1/x̄₀] ≃ω C1[1/x̄₁]`**: the
glueing datum `ω` of the special-fibre covering is the reduction of the algebraization. -/
theorem specialFibre01_r0 (hS : V.system hθ hO = S) (bot : V.P0.Bottom 0) (b : B.Ring0) :
    V.specialFibre01 hθ hO (α := α) hS hJ0 (B.r0Hom b) =
      V.ω (algebraMap V.C0 (Localization.Away (algebraMap V.Bs' V.C0 V.x0s))
        (V.specialFibreEquiv0 hθ hO hS hα hB hJ0 bot (Ideal.Quotient.mk _ b))) := by
  subst hS
  rw [specialFibre01_rfl, B.r0Hom_apply, (α 1).comm_r0, system_r0, RingEquiv.symm_apply_eq,
    specialFibreEquiv0_mk]
  obtain ⟨c, hc⟩ : ∃ c, V.r0Equiv' hθ hO hJ0 bot c = ((α 1).f0 b : (V.twoChart hθ hO 0).R0) :=
    ⟨_, (V.r0Equiv' hθ hO hJ0 bot).apply_symm_apply _⟩
  rw [← hc, RingEquiv.symm_apply_apply]
  exact V.fst_r0Equiv hθ hO hJ0 bot c

/-! ### Linearity over the base model -/

variable {D : ProjectiveLine.TwoChartRings O} (bm : BaseMap V D)
  {ψ : ProjectiveLine.ChartModule.Hom D.chartModule N}

/-- **The special fibre over `V₁` is linear over the base model**: the reduction of the
structure map `ψ` is `D.R1 → B0 → C1`. -/
theorem specialFibreEquiv1_ψ (hS : V.system hθ hO = S)
    (hc : ∀ n, (α (n + 1)).comp ψ = bm.βS hθ hO n hS) (r : D.R1) :
    specialFibreEquiv1 hθ hO hS hα hB hJ0 (Ideal.Quotient.mk _ (ψ.f1 r)) =
      (letI := I.algC10 0; algebraMap I.B0 I.C1 (bm.a1 r)) := by
  subst hS
  letI := I.algC10 0
  have h : (α 1).f1 (ψ.f1 r) = algebraMap I.B0 (I.Y hθ 0) (bm.a1 r) :=
    congrArg (fun φ : ProjectiveLine.ChartModule.Hom _ _ ↦ φ.f1 r) (hc 0)
  change (I.yEquiv hθ hO hJ0).symm ((α 1).f1 (ψ.f1 r)) = _
  rw [h, AlgEquiv.symm_apply_eq, AlgEquiv.commutes]

/-- **The special fibre over `V₀` is linear over the base model**: the reduction of the
structure map `ψ` is `D.R0 → B0' → C0`. -/
theorem specialFibreEquiv0_ψ (hS : V.system hθ hO = S) (bot : V.P0.Bottom 0)
    (hc : ∀ n, (α (n + 1)).comp ψ = bm.βS hθ hO n hS) (r : D.R0) :
    V.specialFibreEquiv0 hθ hO hS hα hB hJ0 bot (Ideal.Quotient.mk _ (ψ.f0 r)) =
      (letI := V.algC0' 0; algebraMap V.B0' V.C0 (bm.a0 r)) := by
  subst hS
  letI := V.algC0' 0
  letI := V.alg0'Q hθ 0
  letI := V.alg0'E 0
  letI := V.alg0'M 0
  have h : (α 1).f0 (ψ.f0 r) =
      algebraMap V.B0' (ZariskiTwo.glued (V.ρ0a hθ hO 0) (V.ρ0b 0)) (bm.a0 r) :=
    congrArg (fun φ : ProjectiveLine.ChartModule.Hom _ _ ↦ φ.f0 r) (hc 0)
  change (V.r0Equiv hθ hO hJ0 bot).symm ((α 1).f0 (ψ.f0 r)) = _
  rw [h, AlgEquiv.symm_apply_eq, AlgEquiv.commutes]

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
