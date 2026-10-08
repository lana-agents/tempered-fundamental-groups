/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ChartTwist
import TemperedFundamentalGroups.SemistableReduction.W7Statement

/-!
# Local interfaces of the type-4 argument (S8.5, leaf T4)

Blueprint §9.12, leaf T4 (`S8A.TypeFourGoodFor`). Two self-contained local statements used by the
Kummer-tower proof of `TypeFourGoodFor` (S8.5 agent), stated here as named hypotheses (to be
discharged by a separate helper; nothing here is assumed as an axiom):

* **`SheetSmooth G`** (step (1), the disc-chart analogue of S6): a point `P'` of the normalized
  vertex chart `DRint 0 1 G` over the residue point `x̄ = 0` of **disc degree one** (a *sheet*:
  the component of `G` over the open unit disc maps isomorphically onto it) is smooth. Expected
  proof: `discDegree ν P' = Σ_{branches (v, Q) at P'} ord_Q x̄` (B1 with a separating element and
  the norm reduction `map_lift_eq_prod` of `VertexMatch`, for the disc chart), so there is one
  branch with `ord_Q x̄ = 1`, and `SmoothVertex.exists_eq_of_uniformizer` with `t = x`.
* **`ChartTransfer e`** (step (4), change of coordinate): `e : G₂ ≃+* G₁` is an isomorphism of
  fields over `C` between two finite extensions of `C(x)`, i.e. one field with two coordinates
  `x` (on `G₁`) and `σ = e x` (the coordinate of `G₂`, read in `G₁`). If `σ` is integral over
  `C[x]`, and every branch of the `x`-chart through `P₁` is (via `e`) a branch of the `σ`-chart
  through `P₂`, then smoothness of `P₂` in the `σ`-chart implies smoothness of `P₁` in the
  `x`-chart. Expected proof: the branch at `P₁` is unique (injectivity of the branch
  correspondence; existence of a branch through every point over `x̄ = 0`); for `α ∈ O_Q`, take
  `y, s` from the `σ`-chart, and multiply `e y, e s` (integral over `C[x]`, of value `≤ 1` at the
  branch valuation) by a power of `z ∈ R'₁ ∖ P₁` vanishing on the other components (prime
  avoidance: no other component passes through `P₁`), so that they lie in `R'₁` (maximum
  principle `SmoothVertex.isIntegral_of_le`).
-/

open IsLocalRing
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open GaussFibre GaussTube DiscCount SmoothVertex PlaceNorm

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable (G : Type*) [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]
  [Algebra.IsSeparable (RatFunc C) G]

/-- **(1) A sheet point is smooth.** Every point of `DRint 0 1 G` over the residue point of
disc degree one (at some, equivalently every, disc valuation of the open unit disc) is smooth. -/
def SheetSmooth : Prop :=
  ∀ (ν : DiscVal (0 : C) 1) (P' : Ideal (DRint (0 : C) 1 G)) [P'.IsMaximal],
    P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) = discIdeal (0 : C) 1 →
    discDegree ν P' = 1 → IsDiscSmooth P'

variable {G}

/-- **(4) Transfer of smoothness along a change of coordinate.** For an isomorphism
`e : G₂ ≃+* G₁` over `C` such that `σ = e x` is integral over `C[x]`: if every branch `(v₁, Q₁)`
of the `x`-chart through `P₁` corresponds (`v₁ ∘ e` an extension `v₂` of the Gauss point of the
`σ`-chart, and `Q₁` transported to `κ(v₂)` a zero of `σ̄` whose point is `P₂`) to a branch of the
`σ`-chart through `P₂`, then smoothness of `P₂` implies smoothness of `P₁`. -/
def ChartTransfer {G₁ G₂ : Type*} [Field G₁] [Algebra (RatFunc C) G₁] [Algebra C G₁]
    [IsScalarTower C (RatFunc C) G₁] [FiniteDimensional (RatFunc C) G₁]
    [Algebra.IsSeparable (RatFunc C) G₁]
    [Field G₂] [Algebra (RatFunc C) G₂] [Algebra C G₂]
    [IsScalarTower C (RatFunc C) G₂] [FiniteDimensional (RatFunc C) G₂]
    [Algebra.IsSeparable (RatFunc C) G₂] (e : G₂ ≃+* G₁)
    (he : ∀ c : C, e.symm (algebraMap C G₁ c) = algebraMap C G₂ c) : Prop :=
  IsIntegral (Algebra.adjoin C {xF C G₁}) (e (xF C G₂)) →
  ∀ (P₁ : Ideal (DRint (0 : C) 1 G₁)) (P₂ : Ideal (DRint (0 : C) 1 G₂)),
    P₁.IsMaximal → P₂.IsMaximal →
    P₁.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₁)) = discIdeal (0 : C) 1 →
    P₂.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G₂)) = discIdeal (0 : C) 1 →
    (∀ (v₁ : Ext C G₁) {Q₁ : CurvePlace 𝓀 (ResidueField v₁.1.valuationSubring)}
      (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C G₁) v₁)), placeIdealD v₁ hQ₁ = P₁ →
      ∃ (v₂ : Ext C G₂) (h : ∀ y : G₁, v₂.1 (e.symm y) = v₁.1 y)
        (hQ₂ : Q₁.map (resAlgEquiv e.symm he h) ∈ zeros 𝓀 (red C (xF C G₂) v₂)),
        placeIdealD v₂ hQ₂ = P₂) →
    IsDiscSmooth P₂ → IsDiscSmooth P₁

end TypeFour

end SemistableReduction
