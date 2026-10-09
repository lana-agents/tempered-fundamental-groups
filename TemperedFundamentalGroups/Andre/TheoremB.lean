/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.NonzeroCharacter
import TemperedFundamentalGroups.Andre.GaloisDomW
import TemperedFundamentalGroups.FibreFunctor.LengthLimit

/-!
# Theorem B from a length function (Blueprint §10.3.6, items 3–5, formal part)

Scheme case (`A'` trivial). Let `𝒢` be a class of Galois objects of the tempered category with
(gal), (dom), (rig) — e.g. `galClassW O R A' Ω (Level.IsW x)` (`galoisLimitDataW`, from
`Statement.StrongComponentA`). If the pointed members of `𝒢` carry a length function with

* base points of length `0`,
* finitely many fibre elements of bounded length,
* lengths non-increasing along pointed morphisms,
* the **Tate loop**: every pointed member over `(X₀, x₀)` has a fibre element of length `≤ ℓ₀`
  over `δ(n) · x₀`,

then the character of `X₀` takes the value `n` (`TateObject.exists_character_eq_of_length`), and
for `n ≠ 0` the tempered group of `[Y/A]` is non-degenerate
(`TateOrbicurve.nondegenerate_of_length`). The geometric construction of the length (B5,
items 2–4 of §10.3.6) is what remains; see the module docstrings of `Andre/GaloisDomW.lean` and
`Topology/TreeLength.lean` for the parts already available.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

open GaloisLimit

namespace TateObject

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] [IsReduced R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R] (D : Data O R)
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Theorem B, formal part**: a length function on the pointed members of a class of Galois
objects with (gal), (dom), (rig), satisfying finiteness, monotonicity and the Tate loop for the
translation `d`, gives an element of `temperedPi1` with character `d`. -/
theorem exists_character_eq_of_length {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hdom : IsDominating (tempFibre O R A V hV) 𝒢)
    (hrig : IsRigid (tempFibre O R A V hV) 𝒢) (d : Multiplicative ℤ)
    (len : ∀ p : PtGal (tempFibre O R A V hV) 𝒢, (tempFibre O R A V hV).obj p.G → ℕ)
    (ℓ₀ : ℕ) (hzero : ∀ p, len p p.g = 0) (hfin : ∀ p (L : ℕ), {γ | len p γ ≤ L}.Finite)
    (hmono : ∀ {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q) γ, len q (f.1 γ) ≤ len p γ)
    (hloop : ∀ p : PtGal (tempFibre O R A V hV) 𝒢, ∀ f : p.G ⟶ X₀ (A := A) D,
      (tempFibre O R A V hV).map f p.g = basePoint D V hV →
      ∃ γ, len p γ ≤ ℓ₀ ∧ (tempFibre O R A V hV).map f γ =
        FibreAut.deckAct (X₀ D) (deck D) d (basePoint D V hV)) :
    ∃ τ : temperedPi1 O R A V hV, character D V hV τ = d :=
  exists_deckCharacter_eq_of_length hgal hdom hrig (X₀ D) (deck D) (basePoint D V hV)
    (isDeckTorsor D V hV) d len ℓ₀ hzero hfin hmono hloop

end TateObject

namespace TateOrbicurve

open Orbicurve

variable {K : Type u} [Field K] {O : ValuationSubring K} {W : WeierstrassCurve K} [DecidableEq K]
  (A : Type u) [Group A] [Finite A] (A' : Type u) [Group A'] [Subsingleton A']
  {ℓ : ℕ} {M : AddSubgroup W.toAffine.Point}
  [MulSemiringAction A (geomOrbicurveRing W ℓ M)] [SMulCommClass A K (geomOrbicurveRing W ℓ M)]
  [MulSemiringAction A' (geomOrbicurveRing W ℓ M)]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra (geomOrbicurveRing W ℓ M) Ω]
  [IsScalarTower K (geomOrbicurveRing W ℓ M) Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy of `temperedPi1 [Y/A]` from a length function** (Theorem B, formal part):
for `Y = E_q ∖ (E[ℓ] + M)`, a class of Galois objects of the scheme category with (gal), (dom),
(rig), and a length function on its pointed members satisfying finiteness, monotonicity and the
Tate loop for a translation `n ≠ 0`, `temperedPi1 [Y/A]` has an open normal subgroup with infinite
quotient. -/
theorem nondegenerate_of_length {π b₄ b₆ : O} (hW : IsTate W π b₄ b₆) (hπ : π ≠ 0)
    (hπm : π ∈ IsLocalRing.maximalIdeal O)
    {𝒢 : ObjectProperty (TempObj O (geomOrbicurveRing W ℓ M) A')}
    (hgal : IsGaloisClass (tempFibre O _ A' V hV) 𝒢)
    (hdom : IsDominating (tempFibre O _ A' V hV) 𝒢) (hrig : IsRigid (tempFibre O _ A' V hV) 𝒢)
    (n : ℤ) (hn : n ≠ 0)
    (len : ∀ p : PtGal (tempFibre O _ A' V hV) 𝒢, (tempFibre O _ A' V hV).obj p.G → ℕ)
    (ℓ₀ : ℕ) (hzero : ∀ p, len p p.g = 0) (hfin : ∀ p (L : ℕ), {γ | len p γ ≤ L}.Finite)
    (hmono : ∀ {p q : PtGal (tempFibre O _ A' V hV) 𝒢} (f : p ⟶ q) γ, len q (f.1 γ) ≤ len p γ)
    (hloop : ∀ p : PtGal (tempFibre O _ A' V hV) 𝒢,
      ∀ f : p.G ⟶ TateObject.X₀ (A := A') (data hW hπ hπm ℓ M),
      (tempFibre O _ A' V hV).map f p.g = TateObject.basePoint (data hW hπ hπm ℓ M) V hV →
      ∃ γ, len p γ ≤ ℓ₀ ∧ (tempFibre O _ A' V hV).map f γ =
        FibreAut.deckAct (TateObject.X₀ (data hW hπ hπm ℓ M)) (TateObject.deck _)
          (Multiplicative.ofAdd n) (TateObject.basePoint (data hW hπ hπm ℓ M) V hV)) :
    ∃ N : Subgroup (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV),
      IsOpen (N : Set (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV)) ∧ N.Normal ∧
        Infinite (temperedPi1 O (geomOrbicurveRing W ℓ M) A V hV ⧸ N) := by
  obtain ⟨τ, hτ⟩ := TateObject.exists_character_eq_of_length (data hW hπ hπm ℓ M) V hV hgal hdom
    hrig (Multiplicative.ofAdd n) len ℓ₀ hzero hfin hmono hloop
  refine nondegenerate_of_character_ne_one A A' V hV hW hπ hπm ⟨τ, ?_⟩
  change TateObject.character _ V hV τ ≠ 1
  rw [hτ]
  exact fun h => hn (Multiplicative.ofAdd.injective (h.trans ofAdd_zero.symm))

end TateOrbicurve

end TemperedFundamentalGroups
