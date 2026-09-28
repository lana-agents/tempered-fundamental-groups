/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalModel
import TemperedFundamentalGroups.Models.Specialization
import TemperedFundamentalGroups.Models.Projective

/-!
# The statement of semistable reduction (W10), as consumed by the tempered group

This file only contains **definitions** (no theorem, no hypothesis is assumed anywhere): the
precise form of the semistable reduction theorem for finite étale covers that the W-chain
(Blueprint §9.3) is proving (`SemistableReduction.Statement`), and that the identification of
`temperedPi1` with André's tempered group (Blueprint §4) and the non-degeneracy witness
(§5.1) consume. Downstream developments build against `Statement` as a named `Prop`; once W10
is proved, `Statement` becomes a theorem and all such developments become unconditional.

## Semistable models

Let `O` be a discrete valuation ring with uniformizer `ϖ` and fraction field `K`, and `c` a
projective `O`-model (`ModelCode O`: a closed subscheme of some `ℙ^m_O`). `c` is
**semistable** (`ModelCode.IsSemistable`) if every point of its special fibre has an affine
open neighbourhood `Spec A` (an open `U` with `IsAffineOpen U`, `A = Γ(U)`) such that `A` is
étale-locally at the corresponding prime a node `O[u,v]/(uv − ϖ^n)` or `O[u]`
(`SemistableReduction.IsSemistableAt`, `LocalModel.lean`).

## The statement

For a complete discretely valued field `K` of characteristic `0`, a smooth affine `K`-curve
`Y = Spec R` and a finite étale `R`-algebra `B` (a finite étale cover `T = Spec B → Y`):
there is a finite extension `K'/K` (with its valuation ring `O'`, the integral closure of `O`),
a semistable projective `O'`-model `c` and an open immersion `Spec (K' ⊗_K B) ⟶ c.scheme` over
`O'` with schematically dense image. (Compatibility with a given model of `Y` — domination of
the normalization of a model of `Ȳ` — is the second clause.)
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

namespace ModelCode

variable {O : Type u} [CommRing O]

/-- The `O`-algebra structure on the sections of a model over an open. -/
noncomputable abbrev sectionsAlgebra (c : TemperedFundamentalGroups.ModelCode O)
    (U : c.scheme.Opens) : Algebra O Γ(c.scheme, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ c.toSpec.appTop ≫
    c.scheme.presheaf.map (homOfLE le_top).op).hom.toAlgebra

/-- A projective `O`-model is **semistable** (relative to the uniformizer `ϖ`) if every point
has an affine open neighbourhood whose ring of sections is, étale-locally at that point, a node
`O[u,v]/(uv − ϖ^n)` or the affine line `O[u]`. (Points of the generic fibre are included: there
the local models are smooth.) -/
def IsSemistable (ϖ : O) (c : TemperedFundamentalGroups.ModelCode O) : Prop :=
  ∀ x : c.scheme, ∃ (U : c.scheme.Opens) (hU : IsAffineOpen U) (hx : x ∈ U),
    letI := sectionsAlgebra c U
    _root_.SemistableReduction.IsSemistableAt ϖ (hU.primeIdealOf ⟨x, hx⟩).asIdeal

end ModelCode

/-- **Semistable reduction of finite étale covers of affine curves (W10)** — the statement.

For every complete discretely valued field `K` of characteristic `0` (valuation subring `O`,
uniformizer `ϖ`), every `K`-algebra `R` smooth of relative dimension one (a smooth affine curve)
and every finite étale `R`-algebra `B`, there are
* a finite extension `K'` of `K`, with the valuation subring `O'` extending `O` and a
  uniformizer `ϖ'` of `O'`;
* a projective `O'`-model `c` that is semistable (`ModelCode.IsSemistable ϖ' c`);
* a morphism `j : Spec (K' ⊗[K] B) ⟶ c.scheme` over `Spec O'` which is an open immersion.
Stated with `K`, `R`, `B` in a fixed universe `u`. -/
def Statement : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [HenselianLocalRing O]
    (R : Type u) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (_ : ringKrullDim R = 1)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] [Module.Finite R B],
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (O' : ValuationSubring K') (_ : O'.comap (algebraMap K K') = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c : TemperedFundamentalGroups.ModelCode O')
      (j : Spec (CommRingCat.of (TensorProduct K K' B)) ⟶ c.scheme),
      ModelCode.IsSemistable ϖ' c ∧ IsOpenImmersion j ∧
        j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeLeftRingHom).comp O'.subtype))

end TemperedFundamentalGroups.SemistableReduction
