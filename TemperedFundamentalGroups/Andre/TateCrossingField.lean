/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateSurjective

/-!
# The function field of the Tate curve in a function field over `K` (HarmonicTate glue)

Let `L = TateField π b₄ b₆` (the fraction field of `O[X][Y] / (f)`, `X = x/π`, `Y = y/π`).

* `TateNormal.algK`: its `K`-algebra structure (`K` the fraction field of `O`).
* `TateNormal.toField ψ x y`: for a field `M` with `ψ : K → M` and a point `(x, y)` of
  `y² + xy = x³ + π² b₄ x + π² b₆` with `x` transcendental over `K`, the embedding `L → M`,
  `X ↦ x/π`, `Y ↦ y/π` (from `tateHom_injective`); it is a `K`-algebra map
  (`toField_comp_algK`).
-/

universe u

open Polynomial

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "L" => TateField π b₄ b₆

/-- The `K`-algebra structure of the function field of the Tate curve. -/
abbrev algK : Algebra K L :=
  (IsFractionRing.lift (A := O) (algebraMap_O_injective π b₄ b₆) : K →+* L).toAlgebra

variable {M : Type u} [Field M] (ψ : K →+* M) {x y : M}

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- Transcendence of `x` over `K` gives the hypothesis of `tateHom_injective`. -/
lemma eval₂_div_eq_zero_imp (hπ : ψ (π : K) ≠ 0)
    (hx : letI := ψ.toAlgebra; Transcendental K x)
    (p : O[X]) (hp : p.eval₂ (ψ.comp O.subtype) (x / (ψ.comp O.subtype) π) = 0) : p = 0 := by
  letI := ψ.toAlgebra
  by_contra hp0
  have hmap : (p.map O.subtype) ≠ 0 := (Polynomial.map_ne_zero_iff
    (ValuationSubring.subtype_injective O)).2 hp0
  have halg : IsAlgebraic K (x / ψ (π : K)) := ⟨p.map O.subtype, hmap, by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    exact hp⟩
  have hπalg : IsAlgebraic K (algebraMap K M (π : K)) := isAlgebraic_algebraMap _
  apply hx
  have := halg.mul hπalg
  rwa [show algebraMap K M (π : K) = ψ (π : K) from rfl, div_mul_cancel₀ _ hπ] at this

variable (hπ : ψ (π : K) ≠ 0)
  (heq : y ^ 2 + x * y = x ^ 3 + (ψ.comp O.subtype) (π ^ 2 * b₄) * x +
    (ψ.comp O.subtype) (π ^ 2 * b₆))
  (hx : letI := ψ.toAlgebra; Transcendental K x)

/-- **The embedding of the function field of the Tate curve** sending `X ↦ x/π`, `Y ↦ y/π`. -/
def toField : L →+* M :=
  IsFractionRing.lift (tateHom_injective π b₄ b₆ (ψ.comp O.subtype) heq hπ
    (eval₂_div_eq_zero_imp π ψ hπ hx))

lemma toField_algebraMap (r : TateRing π b₄ b₆) :
    toField π b₄ b₆ ψ hπ heq hx (algebraMap _ L r) =
      tateHom π b₄ b₆ (ψ.comp O.subtype) heq hπ r :=
  IsFractionRing.lift_algebraMap _ _

lemma toField_aL : toField π b₄ b₆ ψ hπ heq hx (aL π b₄ b₆) = x / ψ (π : K) := by
  rw [aL, IsScalarTower.algebraMap_apply O[X] (TateRing π b₄ b₆) L, toField_algebraMap,
    AdjoinRoot.algebraMap_eq, tateHom_of]
  simp

lemma toField_bL : toField π b₄ b₆ ψ hπ heq hx (bL π b₄ b₆) = y / ψ (π : K) := by
  rw [bL, toField_algebraMap, tateHom_root]
  rfl

lemma toField_algebraMap_O (o : O) :
    toField π b₄ b₆ ψ hπ heq hx (algebraMap O L o) = ψ (o : K) := by
  rw [IsScalarTower.algebraMap_apply O O[X] L, IsScalarTower.algebraMap_apply O[X]
    (TateRing π b₄ b₆) L, toField_algebraMap, AdjoinRoot.algebraMap_eq, tateHom_of]
  simp

/-- `toField` is a `K`-algebra map. -/
lemma toField_comp_algK :
    letI := algK π b₄ b₆
    (toField π b₄ b₆ ψ hπ heq hx).comp (algebraMap K L) = ψ := by
  letI := algK π b₄ b₆
  refine IsLocalization.ringHom_ext (nonZeroDivisors O) (RingHom.ext fun o => ?_)
  simp only [RingHom.comp_apply]
  change toField π b₄ b₆ ψ hπ heq hx (IsFractionRing.lift _ (algebraMap O K o)) = _
  rw [IsFractionRing.lift_algebraMap, toField_algebraMap_O]
  rfl

end

end TemperedFundamentalGroups.TateNormal
