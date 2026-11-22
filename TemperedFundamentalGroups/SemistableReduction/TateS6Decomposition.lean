/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Components
import TemperedFundamentalGroups.SemistableReduction.GaloisComponentAt
import TemperedFundamentalGroups.SemistableReduction.ComponentChart
import TemperedFundamentalGroups.SemistableReduction.PurityLocal
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Decomposition groups of the components of a Galois Tate cover (generic over `CovData`)

MR13 step 7, D1 (S1c). For a cover `C : TateS6.CovData` over two-chart rings `D` with `D.R1` a
Noetherian integrally closed domain with fraction field `K`:

* **`TateS6.CovData.isGaloisGroup_B₁`**: `Gal(C.L/K)` is a Galois group of `C.B₁ / D.R1`;
  **`finite_B₁`**: `C.B₁` is finite over `D.R1`;
* at a prime `p` of `D.R1` with `(D.R1)_p` a discrete valuation ring lying strictly below a
  maximal ideal containing `ϖ1` (e.g. the generic point of the line `ℓ` of the Tate chart) and a
  prime `Q` of `C.B₁` over `p` (a component over `ℓ`): `C.B₁` is unramified at `Q`
  (**`isUnramifiedAt_of_lt`**, from `CovData.hunr₁`), the inertia group of `Q` is trivial
  (**`inertia_eq_bot`**), `|Stab(Q)| = f(Q | p)` (**`card_stabilizer_eq_inertiaDeg`**) and the
  decomposition group acts faithfully on the component ring, `Stab(Q) ≃ Aut_{D.R1/p}(C.B₁/Q)`
  (**`stabilizerHom_bijective`**).
-/

universe u

open Module
open scoped Pointwise

namespace SemistableReduction

namespace TateS6

noncomputable section

namespace CovData

variable {A : Type u} [CommRing A] {K : Type u} [Field K] {D : ProjectiveLine.TwoChartRings A}
  {Rn Rc : Type u} [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] {toN : D.R1 → Rn} {dT : D.R1} {c0 : D.R0} {ϖ1 : D.R1} {ϖ0 : D.R0}
  {I0 : Ideal D.R0} {q e : ℕ} (C : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e)
  [IsDomain D.R1] [IsFractionRing D.R1 K] [IsIntegrallyClosed D.R1]

/-- **`Gal(C.L/K)` is a Galois group of `C.B₁ / D.R1`.** -/
theorem isGaloisGroup_B₁ : IsGaloisGroup (C.L ≃ₐ[K] C.L) D.R1 C.B₁ where
  faithful := ⟨fun {σ τ} h ↦ by
    haveI := IsIntegralClosure.isLocalization D.R1 K C.L C.B₁
    have h' : (σ : C.L →+* C.L).comp (algebraMap C.B₁ C.L) =
        (τ : C.L →+* C.L).comp (algebraMap C.B₁ C.L) := RingHom.ext fun b ↦ by
      simp only [RingHom.comp_apply, RingHom.coe_coe]
      rw [← algebraMap_smul_B₁, ← algebraMap_smul_B₁, h b]
    have h2 := IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid C.B₁
      (nonZeroDivisors D.R1)) h'
    exact AlgEquiv.ext fun x ↦ DFunLike.congr_fun h2 x⟩
  commutes := inferInstance
  isInvariant := isInvariant_B₁ C

/-- `C.B₁` is finite over `D.R1`. -/
theorem finite_B₁ [IsNoetherianRing D.R1] : Module.Finite D.R1 C.B₁ :=
  IsIntegralClosure.finite D.R1 K C.L C.B₁

section Component

variable [IsNoetherianRing D.R1] {C} (p : Ideal D.R1) [p.IsPrime]
  [IsDiscreteValuationRing (Localization.AtPrime p)] {P : Ideal D.R1} [P.IsMaximal]
  (hϖP : ϖ1 ∈ P) (hpP : p < P) (Q : Ideal C.B₁) [Q.IsPrime] [Q.LiesOver p]

omit [IsDomain D.R1] [IsFractionRing D.R1 K] [IsIntegrallyClosed D.R1] [IsNoetherianRing D.R1]
  [p.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime p)] in
include hϖP hpP in
/-- **`C.B₁` is unramified at a prime `Q` over `p`** (`p` strictly below a maximal ideal of the
special fibre; `CovData.hunr₁`). -/
theorem isUnramifiedAt_of_lt : Algebra.IsUnramifiedAt D.R1 Q :=
  C.hunr₁ P hϖP Q (by rw [← Ideal.under_def, ← Ideal.over_def Q p]; exact hpP)

include hϖP hpP in
/-- **The inertia group of a component over `p` is trivial.** -/
theorem inertia_eq_bot : Ideal.inertia (C.L ≃ₐ[K] C.L) Q = ⊥ := by
  haveI := isGaloisGroup_B₁ C
  haveI := finite_B₁ C
  haveI := isDomain_B₁ (C := C)
  haveI : FaithfulSMul D.R1 C.B₁ :=
    (faithfulSMul_iff_algebraMap_injective D.R1 C.B₁).2 injective_algebraMap_B₁
  haveI := isUnramifiedAt_of_lt p hϖP hpP Q
  exact GaloisComponent.inertia_eq_bot_of_isUnramifiedAt p Q

include hϖP hpP in
/-- **`|Stab(Q)| = f(Q | p)`** for a component `Q` over `p`. -/
theorem card_stabilizer_eq_inertiaDeg :
    Nat.card (MulAction.stabilizer (C.L ≃ₐ[K] C.L) Q) = Q.inertiaDeg D.R1 := by
  haveI := isGaloisGroup_B₁ C
  haveI := finite_B₁ C
  haveI := isDomain_B₁ (C := C)
  haveI : FaithfulSMul D.R1 C.B₁ :=
    (faithfulSMul_iff_algebraMap_injective D.R1 C.B₁).2 injective_algebraMap_B₁
  haveI := isUnramifiedAt_of_lt p hϖP hpP Q
  exact GaloisComponent.card_stabilizer_eq_inertiaDeg_of_isUnramifiedAt p Q

include hϖP hpP in
/-- **The decomposition group acts faithfully on the component ring**:
`Stab(Q) ≃ Aut_{D.R1/p}(C.B₁/Q)`. -/
theorem stabilizerHom_bijective :
    Function.Bijective (Ideal.Quotient.stabilizerHom Q p (C.L ≃ₐ[K] C.L)) := by
  haveI := isGaloisGroup_B₁ C
  haveI := finite_B₁ C
  haveI := isDomain_B₁ (C := C)
  haveI : FaithfulSMul D.R1 C.B₁ :=
    (faithfulSMul_iff_algebraMap_injective D.R1 C.B₁).2 injective_algebraMap_B₁
  haveI := isUnramifiedAt_of_lt p hϖP hpP Q
  exact GaloisComponent.stabilizerHom_bijective_of_isUnramifiedAt p Q

include hϖP hpP in
/-- **The degree of the component chart is the order of the decomposition group**:
`rank_{(R1/p)[1/ḡ]} (B₁/Q)[1/ḡ] = |Stab(Q)|` (`g ∉ p`). -/
theorem finrank_C1_eq_card {g : D.R1} (hg : g ∉ p) :
    finrank (ComponentChart.R p g) (ComponentChart.C1 p g Q) =
      Nat.card (MulAction.stabilizer (C.L ≃ₐ[K] C.L) Q) := by
  haveI := finite_B₁ C
  rw [ComponentChart.finrank_C1 hg, card_stabilizer_eq_inertiaDeg p hϖP hpP Q]

end Component

section Line

variable [IsNoetherianRing D.R1] {C} (p : Ideal D.R1) (g : D.R1)

/-- **Purity along a component of the special fibre**: if `D.R1` is regular at the closed points
of `V(p) ∩ D(g)` (with `ϖ1 ∈ p`), then `C.B₁/pC.B₁` is étale over `D.R1/p` on `D(ḡ)`
(`PurityLocal.etale_quot_awayMap` with `CovData.hunr₁`). -/
theorem etale_quot [IsJacobsonRing (D.R1 ⧸ p)] (hϖp : ϖ1 ∈ p)
    (hreg : ∀ (P : Ideal D.R1) [P.IsMaximal], p ≤ P → g ∉ P →
      ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        IsLocalRing.maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y}) :
    (Localization.awayMap (algebraMap (D.R1 ⧸ p) (C.B₁ ⧸ p.map (algebraMap D.R1 C.B₁)))
      (Ideal.Quotient.mk p g)).Etale :=
  PurityLocal.etale_quot_awayMap K (L := C.L) p C.B₁ g hreg fun P _ hpP _ Q _ hQ ↦
    C.hunr₁ P (hpP hϖp) Q hQ

end Line

end CovData

end

end TateS6

end SemistableReduction
