/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TwoChartGlue

/-!
# The piece over `V₀` as a parameter of the assembly (Blueprint §12.8, M2.3 (f))

The assembly `TwoChartGlue.twoChart` of the two-chart rings of a covering takes, besides the
sections `Y1` over `U₁`, a piece over a basic open `D(b₀)` of `V₀ = toP1⁻¹U₀` and its overlap
with `Q = Y1[1/y]`. This file bundles that piece:

* **`TwoChartGlue.Patch0`**: a piece `P0b` over `D(b₀) ⊆ V₀` (a `B0`-algebra in which `b₀` is a
  unit), an overlap `P0ab` with `ρ0a : Q → P0ab` (a localization away from `b₀`) and
  `ρ0b : P0b → P0ab` (a localization away from `x₀`);
* `TwoChartGlue.Patch0.twoChart`: the two-chart rings of the glued covering.

Instances: the étale lift of the special-fibre covering over `D(1 + h)` (coverings étale outside
the nodes), and a formal patch with cusp factors at the origin `[0:1:0] ∈ V₀ ∖ V₁` (coverings
ramified at the cusp); the assembly and the tower do not depend on which one is used.
-/

universe u

namespace SemistableReduction

namespace TwoChartGlue

variable {A : Type u} [CommRing A] {B0 : Type u} [CommRing B0] [Algebra A B0]
  (Q : Type u) [CommRing Q] [Algebra A Q] [Algebra B0 Q] [IsScalarTower A B0 Q] (x0 : B0)

/-- **A piece over a basic open `D(b₀)` of `V₀` with its overlap with the `U₁` side**
`Q = Y1[1/y]` (glueing data over `V₀ = D(x₀) ∪ D(b₀)`). -/
structure Patch0 where
  /-- the basic open `D(b₀)` -/
  b0 : B0
  /-- the piece over `D(b₀)` -/
  P0b : Type u
  [commRing : CommRing P0b]
  [algebra : Algebra B0 P0b]
  [algebraA : Algebra A P0b]
  [tower : IsScalarTower A B0 P0b]
  /-- the overlap over `D(x₀ b₀)` -/
  P0ab : Type u
  [commRingab : CommRing P0ab]
  [algebraab : Algebra B0 P0ab]
  [algebraAab : Algebra A P0ab]
  [towerab : IsScalarTower A B0 P0ab]
  ρ0a : Q →ₐ[B0] P0ab
  ρ0b : P0b →ₐ[B0] P0ab
  /-- `b₀` is a unit on the piece -/
  hunit : IsUnit (algebraMap B0 P0b b0)
  /-- the overlap is the piece localized away from `x₀` -/
  hb0 : letI := (ρ0b : P0b →+* P0ab).toAlgebra; IsLocalization.Away (algebraMap B0 P0b x0) P0ab
  /-- the overlap is `Q` localized away from `b₀` -/
  ha0 : letI := (ρ0a : Q →+* P0ab).toAlgebra; IsLocalization.Away (algebraMap B0 Q b0) P0ab

attribute [instance] Patch0.commRing Patch0.algebra Patch0.algebraA Patch0.tower Patch0.commRingab
  Patch0.algebraab Patch0.algebraAab Patch0.towerab

variable {Q x0} {Y1 : Type u} [CommRing Y1] [Algebra A Y1] (y : Y1) (ι : Y1 →ₐ[A] Q)
  (hι : letI := (ι : Y1 →+* Q).toAlgebra; IsLocalization.Away y Q)
  (hxy : algebraMap B0 Q x0 * ι y = 1)

/-- **The two-chart rings of the covering glued from `Y1` and a piece over `V₀`.** -/
noncomputable def Patch0.twoChart (V : Patch0 (A := A) Q x0) : ProjectiveLine.TwoChartRings A :=
  TwoChartGlue.twoChart y ι hι x0 hxy V.ρ0a V.ρ0b V.hb0

end TwoChartGlue

end SemistableReduction
