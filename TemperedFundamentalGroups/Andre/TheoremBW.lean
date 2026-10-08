/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.LengthW
import TemperedFundamentalGroups.Andre.TheoremB

/-!
# Theorem B from x-lengths (Blueprint §10.3.6, items 1–5)

Scheme case. The Galois class is `galClassW O R A Ω (Level.IsW x)` (`x` the x-line of
`exists_finite_aeval`), with (gal), (dom), (rig) from `Statement.StrongComponent`
(`galoisLimitDataW`). Its pointed members carry the length `lenW` (`Andre/LengthW.lean`): the
length in the tree of the universal covering of the special fibre, with the x-lengths of the
nodes as weights. From `Statement.HarmonicX` and `Statement.NodeOfTwoComponents`:

* the base point has length `0` (`lenW_self`);
* finitely many fibre elements have bounded length (`finite_lenW_le`);
* lengths do not increase along pointed morphisms (`lenW_map_le`).

The results below are conditional on the **Tate loop** (`hloop`), and **Theorem B is not proved**.
`hloop` says that every pointed member over the pointed Tate object `(X₀, x₀)` has a fibre
element of length `≤ ℓ₀` over `δ(n) · x₀`, for a fixed finite `ℓ₀`.

**Warning (Blueprint §10.3.7).** For `lenW` this hypothesis is *not satisfiable in general*: as
members are refined around the base point, lengths over `δ(n)·x₀` grow without bound, and the
lifting hypothesis `hlift` is false. The theorems here are formal reductions only. Theorem B is
parked until the length is redesigned (core-anchored lengths, §10.3.7).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold
open scoped ENNReal

namespace TemperedFundamentalGroups

open GaloisLimit

namespace TateObject

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] (D : Data O R)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Theorem B from the x-length function**: given the targeted `StrongComponent` and
`HarmonicX`, `NodeOfTwoComponents`, and the Tate loop for the length `lenW` (a fibre element of
length `≤ ℓ₀ < ⊤` over `δ(d) x₀` in every pointed member over `(X₀, x₀)`), some element of
`temperedPi1` has character `d`. -/
theorem exists_character_eq_of_lenW
    (hW : SemistableReduction.Statement.StrongComponent.{u})
    (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u})
    (hR : ringKrullDim R = 1) (ϖ : O) (hϖ : Irreducible ϖ) (d : Multiplicative ℤ)
    (ℓ₀ : ℝ≥0∞) (hℓ₀ : ℓ₀ ≠ ⊤)
    (hloop : ∀ p : PtGal (tempFibre O R A V hV)
        (galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)),
      ∀ f : p.G ⟶ X₀ (A := A) D, (tempFibre O R A V hV).map f p.g = basePoint D V hV →
      ∃ γ, lenW V hV (exists_finite_aeval (K := K) hR).choose ϖ p γ ≤ ℓ₀ ∧
        (tempFibre O R A V hV).map f γ = FibreAut.deckAct (X₀ D) (deck D) d (basePoint D V hV)) :
    ∃ τ : temperedPi1 O R A V hV, character D V hV τ = d := by
  obtain ⟨hgal, hdom, hrig⟩ := galoisLimitDataW (A := A) V hV hW hR
  obtain ⟨α, hα⟩ := exists_deckCharacter_eq_of_length' hgal hdom hrig (X₀ D) (deck D)
    (basePoint D V hV) (isDeckTorsor D V hV) d (lenW V hV _ ϖ) ℓ₀
    (fun p => (lenW_self V hV ϖ p).trans_le zero_le)
    (fun p => finite_lenW_le V hV hX hN ϖ hϖ p hℓ₀)
    (fun f γ => lenW_map_le V hV hX hN ϖ hϖ f γ) hloop
  exact ⟨α, hα⟩

/-- **Theorem B from x-lengths, with the Tate loop reduced to lifting**: instead of the loop
in every pointed member, it suffices that fibre elements lift along pointed morphisms of members
without increasing `lenW` (`hlift`, path lifting from (X1) of `HarmonicX`), and that one pointed
member over `(X₀, x₀)` has an element over `δ(d) x₀` (`hbase`). -/
theorem exists_character_eq_of_lenW_lift
    (hW : SemistableReduction.Statement.StrongComponent.{u})
    (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u})
    (hR : ringKrullDim R = 1) (ϖ : O) (hϖ : Irreducible ϖ) (d : Multiplicative ℤ)
    (hlift : ∀ {p q : PtGal (tempFibre O R A V hV)
        (galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose))} (f : p ⟶ q)
      (γ' : (tempFibre O R A V hV).obj q.G), ∃ γ, f.1 γ = γ' ∧
        lenW V hV (exists_finite_aeval (K := K) hR).choose ϖ p γ ≤
          lenW V hV (exists_finite_aeval (K := K) hR).choose ϖ q γ')
    (hbase : ∃ (p₀ : PtGal (tempFibre O R A V hV)
        (galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)))
      (f₀ : p₀.G ⟶ X₀ (A := A) D) (γ₀ : (tempFibre O R A V hV).obj p₀.G),
      (tempFibre O R A V hV).map f₀ p₀.g = basePoint D V hV ∧
      (tempFibre O R A V hV).map f₀ γ₀ = FibreAut.deckAct (X₀ D) (deck D) d (basePoint D V hV)) :
    ∃ τ : temperedPi1 O R A V hV, character D V hV τ = d := by
  obtain ⟨-, hdom, hrig⟩ := galoisLimitDataW (A := A) V hV hW hR
  obtain ⟨p₀, f₀, γ₀, hf₀, hγ₀⟩ := hbase
  have hfin : lenW V hV (exists_finite_aeval (K := K) hR).choose ϖ p₀ γ₀ ≠ ⊤ :=
    CurveConfig.tlen_ne_top (fun _ => by
      unfold WData.weight; split_ifs <;> simp) _ _
  exact exists_character_eq_of_lenW D V hV hW hX hN hR ϖ hϖ d _ hfin
    (exists_loop_of_lift hdom hrig (X₀ D) (deck D) (basePoint D V hV) d _
      (fun f γ => lenW_map_le V hV hX hN ϖ hϖ f γ) hlift p₀ f₀ hf₀ γ₀ hγ₀)

end TateObject

namespace TateOrbicurve

open Orbicurve

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {W : WeierstrassCurve K} [DecidableEq K]
  (A : Type u) [Group A] [Finite A] (A' : Type u) [Group A'] [Subsingleton A']
  {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
  [MulSemiringAction A (geomOrbicurveRing W ℓ M)] [SMulCommClass A K (geomOrbicurveRing W ℓ M)]
  [MulSemiringAction A' (geomOrbicurveRing W ℓ M)]
  [Algebra.Smooth K (geomOrbicurveRing W ℓ M)] [IsDomain (geomOrbicurveRing W ℓ M)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra (geomOrbicurveRing W ℓ M) Ω]
  [IsScalarTower K (geomOrbicurveRing W ℓ M) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy of `temperedPi1 [Y/A]` from x-lengths** (Theorem B): for
`Y = E_q ∖ (E[ℓ] + M)`, given `StrongComponent`, `HarmonicX`, `NodeOfTwoComponents` and the Tate
loop of translation `n ≠ 0` for `lenW`, `temperedPi1 [Y/A]` has an open normal subgroup with
infinite quotient. -/
theorem nondegenerate_of_lenW {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O)
    (hSC : SemistableReduction.Statement.StrongComponent.{u})
    (hX : SemistableReduction.Statement.HarmonicX.{u})
    (hN : SemistableReduction.Statement.NodeOfTwoComponents.{u})
    (hR : ringKrullDim (geomOrbicurveRing W ℓ M) = 1) (ϖ : O) (hϖ : Irreducible ϖ)
    (n : ℤ) (hn : n ≠ 0) (ℓ₀ : ℝ≥0∞) (hℓ₀ : ℓ₀ ≠ ⊤)
    (hloop : ∀ p : PtGal (tempFibre O _ A' V hV)
        (galClassW O _ A' Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)),
      ∀ f : p.G ⟶ TateObject.X₀ (A := A') (data hW hπ hπm ℓ M),
      (tempFibre O _ A' V hV).map f p.g = TateObject.basePoint (data hW hπ hπm ℓ M) V hV →
      ∃ γ, lenW V hV (exists_finite_aeval (K := K) hR).choose ϖ p γ ≤ ℓ₀ ∧
        (tempFibre O _ A' V hV).map f γ =
          FibreAut.deckAct (TateObject.X₀ (data hW hπ hπm ℓ M)) (TateObject.deck _)
            (Multiplicative.ofAdd n) (TateObject.basePoint (data hW hπ hπm ℓ M) V hV)) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) := by
  obtain ⟨τ, hτ⟩ := TateObject.exists_character_eq_of_lenW (data hW hπ hπm ℓ M) V hV hSC hX hN
    hR ϖ hϖ (Multiplicative.ofAdd n) ℓ₀ hℓ₀ hloop
  refine nondegenerate_of_character_ne_one A A' V hV hW hπ hπm ⟨τ, ?_⟩
  change TateObject.character _ V hV τ ≠ 1
  rw [hτ]
  exact fun h => hn (Multiplicative.ofAdd.injective (h.trans ofAdd_zero.symm))

end TateOrbicurve

end TemperedFundamentalGroups
