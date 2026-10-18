/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import TemperedFundamentalGroups.SemistableReduction.KummerPatch
import TemperedFundamentalGroups.SemistableReduction.QuadraticEtale

/-!
# The quadratic node chart `A_D[S]/(S² + S − c)` and its completion along the nodes

(Blueprint §12.8, M2.3 (a'), generic.) Near its two nodes the Tate chart `x₀ ≠ 0`, localized at
`D = 1 + b₄w²`, is `A_D[S]/(S² + S − c)` over the node ring `A = O[u,v]/(uv − π^e)`
(`TemperedFundamentalGroups.TateNormal.quadChartEquiv`). For any such *quadratic node chart*
`R = (A[S]/(S² + S − c))[1/D]` (`c, D ∈ A`):

* `R` is flat over `A` (`A[S]/(monic)` is free, localizations are flat);
* `R` is Noetherian if `O` is;
* **`QuadNode.flat_hat`**: the `f`-adic completion `R̂` (`f = u + v`) is flat over `A`
  (Mathlib `AdicCompletion.flat_of_isNoetherian`), and `f ↦ u + v` (`QuadNode.algebraMap_f`).

These are exactly the hypotheses `[Module.Flat (A π e) R̂]` and `hf` of the level-`n` patching
with the Kummer algebra, `KummerPatch.patch_spec` (`QuadNode.patch_spec`).
-/

universe u

namespace SemistableReduction

open KummerEtale

namespace QuadNode

noncomputable section

variable {O : Type u} [CommRing O] (π : O) (e : ℕ) (c D : A π e)

/-- `A[S]/(S² + S − c)`. -/
abbrev Q : Type u := AdjoinRoot (QuadraticEtale.poly c)

/-- The quadratic node chart `R = (A[S]/(S² + S − c))[1/D]`. -/
abbrev R : Type u := Localization.Away (AdjoinRoot.of (QuadraticEtale.poly c) D)

/-- The element `f = u + v` of the chart, cutting out the nodes. -/
abbrev f : R π e c D := algebraMap (A π e) (R π e c D) (fA π)

instance : Module.Free (A π e) (Q π e c) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (QuadraticEtale.monic_poly c)).basis

instance : Module.Flat (A π e) (R π e c D) := by
  haveI : Module.Flat (Q π e c) (R π e c D) :=
    IsLocalization.flat _ (Submonoid.powers (AdjoinRoot.of (QuadraticEtale.poly c) D))
  exact Module.Flat.trans (A π e) (Q π e c) (R π e c D)

instance [IsNoetherianRing O] : IsNoetherianRing (R π e c D) := by
  haveI : IsNoetherianRing (A π e) := inferInstance
  haveI : IsNoetherianRing (Q π e c) := Algebra.FiniteType.isNoetherianRing (A π e) _
  exact IsLocalization.isNoetherianRing
    (Submonoid.powers (AdjoinRoot.of (QuadraticEtale.poly c) D)) (R π e c D) inferInstance

/-- **The completion along the nodes is flat over the node ring.** -/
instance flat_hat [IsNoetherianRing O] :
    Module.Flat (A π e) (FormalPatchLevel.Hat (f π e c D)) := by
  haveI : Module.Flat (R π e c D) (FormalPatchLevel.Hat (f π e c D)) :=
    inferInstance
  exact Module.Flat.trans (A π e) (R π e c D) _

lemma algebraMap_f : algebraMap (R π e c D) (FormalPatchLevel.Hat (f π e c D)) (f π e c D) =
    algebraMap (A π e) (FormalPatchLevel.Hat (f π e c D)) (fA π) :=
  (IsScalarTower.algebraMap_apply (A π e) (R π e c D) _ _).symm

end

end QuadNode

end SemistableReduction
