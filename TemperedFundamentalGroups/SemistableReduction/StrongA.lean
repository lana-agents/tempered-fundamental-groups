/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.StrongComponent
import TemperedFundamentalGroups.Setup.NoetherLine

/-!
# The minimal form of W10 consumed by Theorem A (proposal)

`Statement.StrongA` is `Statement.StrongComponent` without the outputs that only Theorem B (now
parked) used: split, no loops, open immersion of `j`, the fibre clause, the dimension bound, and
the component clause (with W-models and `IsUnfolded`). It adds the hypothesis that `G` also acts
on `R`, with `R → B` equivariant (true for the levels of Theorem A), so that the x-line can be
chosen `G`-invariant (Noether normalization of `R^G`). It also drops the x-line input, which
Noether normalization supplies (`exists_finite_aeval`). Theorem A (`andreEquiv`) consumes exactly
this form.

**Hypotheses added for correctness/scope.**
* `[IsDomain R]`: without equidimensionality the statement is false (e.g. `R = K[t] × K`, `B = R`:
  a semistable model has relative dimension `1` at every point, so no generic point of it can be
  the image of the factor `Spec K'`). The orbicurve rings of Theorem A are domains.
* mixed characteristic `(p : O) ∈ 𝔪_O` for a prime `p`: W7 is proved for residue characteristic
  `p > 0`. Equal characteristic `0` (tame) is an untargeted extension (Blueprint §9.12).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

/-- **W10, minimal form for Theorem A.** -/
def Statement.StrongA : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (p : ℕ) (_ : p.Prime) (_ : (p : O) ∈ IsLocalRing.maximalIdeal O)
    (R : Type u) [CommRing R] [IsDomain R] [Algebra K R] [Algebra.Smooth K R]
    (_ : ringKrullDim R = 1)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] [Module.Finite R B]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G K B]
    [MulSemiringAction G R] [SMulCommClass G K R]
    (_ : ∀ (g : G) (r : R), g • algebraMap R B r = algebraMap R B (g • r))
    (ι : Type u) [Finite ι] (c₀ : ι → TemperedFundamentalGroups.ModelCode O)
    (j₀ : ∀ i, Spec (CommRingCat.of B) ⟶ (c₀ i).scheme)
    (_ : ∀ i, j₀ i ≫ (c₀ i).toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap K B).comp O.subtype))),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : IsGalois K K')
      (O' : ValuationSubring K') (_ : O'.comap (algebraMap K K') = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c' : TemperedFundamentalGroups.ModelCode O') (c : TemperedFundamentalGroups.ModelCode O)
      (e : c.scheme ≅ c'.scheme)
      (j : Spec (CommRingCat.of (TensorProduct K K' B)) ⟶ c.scheme)
      (act : G × (K' ≃ₐ[K] K') →* Aut c.scheme)
      (dom : ∀ i, c.scheme ⟶ (c₀ i).scheme),
      ModelCode.IsSemistable ϖ' c' ∧
      e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K K').restrict O O' (fun x hx => by
          rw [← ‹O'.comap (algebraMap K K') = O›] at hx; exact hx))) = c.toSpec ∧
      IsSchemeTheoreticallyDominant j ∧
      j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeftRingHom).comp ((algebraMap K K').comp O.subtype))) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'), (act gσ).hom ≫ c.toSpec = c.toSpec) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'),
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr (gσ.2⁻¹)
          (MulSemiringAction.toAlgAut G K B gσ.1⁻¹)).toRingHom) ≫ j = j ≫ (act gσ).hom) ∧
      (∀ i, j ≫ dom i = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct K K' B)) ≫ j₀ i) ∧
      (∀ i, dom i ≫ (c₀ i).toSpec = c.toSpec)

/-- `StrongComponent` implies the minimal form `StrongA`. -/
theorem Statement.strongA_of_strongComponent (h : Statement.StrongComponent.{u}) :
    Statement.StrongA.{u} := by
  intro K _ _ O _ _ _ _ _ R _ _ _ _ hR B _ _ _ _ _ _ G _ _ _ _ _ _ _ ι _ c₀ j₀ hj₀
  obtain ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, hss, -, -, he, -, hjd,
    hjS, hact, hactj, hdom, hdomS, -⟩ := h K O R hR (exists_finite_aeval hR).choose
      (exists_finite_aeval hR).choose_spec B G ι c₀ j₀ hj₀
  exact ⟨K', i1, i2, i3, i4, O', hO', i5, ϖ', hϖ', c', c, e, j, act, dom, hss, he, hjd, hjS, hact,
    hactj, hdom, hdomS⟩

end TemperedFundamentalGroups.SemistableReduction
