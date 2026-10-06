/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TreeBridge
import TemperedFundamentalGroups.SemistableReduction.Exhausting
import TemperedFundamentalGroups.SemistableReduction.GaussDescent
import TemperedFundamentalGroups.SemistableReduction.DefinedOverDVR

/-!
# The statement of W7 (semistable Gauss trees), as consumed by W10

Blueprint §9.9 (W7), §9.12 (O6, O7). This file contains only **definitions**. It fixes the precise
form of the output of S7 + S8 (+ S9 on the W10 side) that the W10 assembly consumes. Agreed
between the S8.A agent, S7 and the W10 assembler (2026-10).

Setting: `C` algebraically closed, non-archimedean, `char C = 0`, `‖p‖ < 1` for a prime `p`,
**not** assumed complete (§9.11); `F' / C(x)` finite. A *Gauss tree* is a convex reduced finite
nonempty family of discs `D(aᵢ, |cᵢ|)` (the input of `gaussJoinModel`); its *edges* are the
minimal strict inclusions `D j ⊊ D m` (`TreeBridge.IsEdge`).

* `SmoothVertex.discBranches`, `SmoothVertex.IsDiscSmooth`: a point `P'` of the normalized vertex
  chart `DRint 0 1 F'` over `(𝔪_C, x)` is smooth on the special fibre: exactly one branch `(v, Q)`
  (an extension `v` of `w_{0,1}` and a zero `Q` of `x̄` on `κ(v)`) passes through `P'`, and the
  local ring of the reduction at `P'` is all of `O_Q` (`δ = 0`).
* `W7.IsSemistableTree a c F'`: there is no fixed uniformizer. Every point over a node of every
  edge chart `Rint (c j / c m) (Aff (a j) (c m) F')` (`O_C[t, c'/t]`, `t = (x - a j)/c m`,
  `c' = c j / c m ∈ 𝔪_C ∖ 0`) is an ordinary double point (`GaussTube.IsNodeODP`). Every point of
  a vertex chart over a residue point which is not a child direction is smooth (`IsDiscSmooth`
  on `DRint 0 1 (Aff (a i + c i β) (c i) F')`). So is every point over `∞` of the root (the chart
  `DRint 0 1 (Inv 1 (Aff (a ρ) (c ρ) F'))`, coordinate `c ρ / (x - a ρ)`). By `TreeBridge`
  (`map_rint_aff`, `map_drint_aff`) these charts are the normalizations in `F'` of the standard
  charts of `gaussJoinModel a c`.
* `W7.DiscsLE a₀ c₀ a c`: every disc of `(a₀, c₀)` is a disc of `(a, c)`.
* **`W7.Statement`**: for a finite family of fields `F' k / C(x)` and given discs `V₀`, there is a
  Gauss tree `V ⊇ V₀` that is semistable for every `F' k`. If moreover `τ` is an isometric
  automorphism of `C` with `τ V₀ = V₀` that extends to a `τ`-semilinear ring automorphism of
  `Π k, F' k` (which may permute the factors), then `τ V = V`.
-/

universe u v

open IsLocalRing
open scoped NNReal

namespace SemistableReduction

namespace SmoothVertex

open FundamentalInequality GaussStability GaussFibre GaussTube DiscCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

/-- The branches through a point `P'` of the normalized vertex chart `DRint 0 1 G`: the zeros `Q`
of `x̄` on the residue curves of the extensions of `w_{0,1}` whose point is `P'`. -/
def discBranches (P' : Ideal (DRint (0 : C) 1 G)) : Set (OuterBranch C G) :=
  {b | placeIdealD b.1 b.2.2 = P'}

/-- **Smooth point of the special fibre over `C`** at a point `P'` of the normalized vertex chart:
exactly one branch `(v, Q)` passes through `P'`, and the local ring of the reduction at `P'` is
`O_Q`: every `α ∈ O_Q` is `ρ y / ρ s` with `y, s ∈ R'`, `s ∉ P'`. -/
def IsDiscSmooth (P' : Ideal (DRint (0 : C) 1 G)) : Prop :=
  ∃ b : OuterBranch C G, discBranches P' = {b} ∧
    ∀ α ∈ b.2.1.V, ∃ y s : DRint (0 : C) 1 G, s ∉ P' ∧ redD b.1 y = α * redD b.1 s

end SmoothVertex

namespace W7

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

/-- Every disc of `(a₀, c₀)` is a disc of `(a, c)`: `V ⊇ V₀`, disc-wise. -/
def DiscsLE {ι₀ ι : Type*} (a₀ c₀ : ι₀ → C) (a c : ι → C) : Prop :=
  ∀ k, ∃ i, ‖c i‖ = ‖c₀ k‖ ∧ ‖a i - a₀ k‖ ≤ ‖c i‖

/-- **Semistability of a Gauss tree** `(a, c)` for `F' / C(x)`, over `O_C` and without a fixed
uniformizer: ordinary double points over the nodes of the edges, smooth points elsewhere. -/
structure IsSemistableTree {ι : Type*} (a c : ι → C) (hc : ∀ i, c i ≠ 0) (F' : Type*) [Field F']
    [Algebra (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
    [FiniteDimensional (RatFunc C) F'] : Prop where
  /-- Every point over the node of an edge chart is an ordinary double point. -/
  node : ∀ j m, IsEdge a c j m → ∀ (h1 : ‖c j / c m‖ < 1) (h0 : c j / c m ≠ 0)
    (P' : Ideal (Rint (c j / c m) (Aff (a j) (c m) (hc m) F'))), P'.IsMaximal →
    P'.comap (algebraMap (nodeRing (c j / c m)) (Rint (c j / c m) (Aff (a j) (c m) (hc m) F'))) =
      tubeIdeal (c j / c m) → IsNodeODP h1 h0 P'
  /-- Every point of a vertex chart over a residue point `β̄` which is not a child direction is
  smooth. -/
  smooth : ∀ i (β : C), ‖β‖ ≤ 1 → (∀ j, IsEdge a c j i → ‖a i + c i * β - a j‖ = ‖c i‖) →
    ∀ P' : Ideal (DRint (0 : C) 1 (Aff (a i + c i * β) (c i) (hc i) F')), P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1)
        (DRint (0 : C) 1 (Aff (a i + c i * β) (c i) (hc i) F'))) = discIdeal (0 : C) 1 →
      IsDiscSmooth P'
  /-- Every point over `∞` of the root (the vertex without parent) is smooth. -/
  root : ∀ i, (∀ m, ¬ IsEdge a c i m) →
    ∀ P' : Ideal (DRint (0 : C) 1 (GaussTube.Inv (1 : C) one_ne_zero (Aff (a i) (c i) (hc i) F'))),
      P'.IsMaximal →
      P'.comap (algebraMap (discRing (0 : C) 1)
        (DRint (0 : C) 1 (GaussTube.Inv (1 : C) one_ne_zero (Aff (a i) (c i) (hc i) F')))) =
          discIdeal (0 : C) 1 →
      IsDiscSmooth P'

end W7

/-- **W7: semistable Gauss trees** (the form consumed by the W10 assembly, Blueprint §9.12 O7).

For every algebraically closed non-archimedean `C` of characteristic `0` with `‖p‖ < 1` (not
necessarily complete), every finite family of finite extensions `F' k / C(x)`, each defined over a
complete discretely valued subfield of `C` (`DefinedOverDVR`, needed by the node data O1), and
every finite
family of discs `V₀ = (a₀, c₀)`, there is a convex reduced nonempty finite family of discs
`V = (a, c) ⊇ V₀` such that
* `V` is semistable for every `F' k` (`W7.IsSemistableTree`);
* (**equivariance**) for every isometric ring automorphism `τ` of `C` such that `τ V₀ = V₀` and
  `τ` extends to a `τ`-semilinear ring automorphism `σ` of `Π k, F' k` (`σ` commutes with the
  diagonal `C(x)`-structure twisted by `τ` on coefficients, `x ↦ x`; it may permute the factors),
  also `τ V = V`. -/
def W7.Statement : Prop :=
  ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
    (p : ℕ) (_ : p.Prime) (_ : ‖(p : C)‖ < 1)
    (κ : Type) [Fintype κ] (F' : κ → Type v) [∀ k, Field (F' k)]
    [∀ k, Algebra (RatFunc C) (F' k)] [∀ k, Algebra C (F' k)]
    [∀ k, IsScalarTower C (RatFunc C) (F' k)] [∀ k, FiniteDimensional (RatFunc C) (F' k)]
    (_ : ∀ k, DefinedOverDVR C (F' k))
    (ι₀ : Type) [Fintype ι₀] (a₀ c₀ : ι₀ → C) (_ : ∀ k, c₀ k ≠ 0),
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a c : ι → C) (hc : ∀ i, c i ≠ 0),
      GaussTree.IsConvex (NormedField.valuation (K := C)) a c ∧
      GaussTree.IsReduced (NormedField.valuation (K := C)) a c ∧
      W7.DiscsLE a₀ c₀ a c ∧
      (∀ k, W7.IsSemistableTree a c hc (F' k)) ∧
      ∀ τ : C ≃+* C, (∀ z, ‖τ z‖ = ‖z‖) →
        (∃ σ : (Π k, F' k) ≃+* (Π k, F' k), ∀ (φ : RatFunc C) (k : κ),
          σ (fun k' ↦ algebraMap (RatFunc C) (F' k') φ) k =
            algebraMap (RatFunc C) (F' k) (ratFuncMap τ.toRingHom φ)) →
        W7.DiscsLE (fun k ↦ τ (a₀ k)) c₀ a₀ c₀ → W7.DiscsLE (fun i ↦ τ (a i)) c a c

end SemistableReduction
