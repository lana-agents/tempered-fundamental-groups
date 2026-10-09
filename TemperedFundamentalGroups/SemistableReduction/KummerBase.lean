/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ClassicalGood

/-!
# Kummer base change at a classical point (interface)

Blueprint §9.12 O6.1f(i). For a finite extension `F / C(x)` and `a ∈ C`, a Kummer extension
`L = F(y)`, `y ^ E = x - a`, kills the ramification over `x = a` (Abhyankar's lemma,
`SemistableReduction/Abhyankar`). In the form consumed by S8.2: `L`, seen as an extension of
`C(y)` (`Coord hy`: `L` with the `C(x)`-algebra structure `X ↦ y`), carries an unramified datum
(`ClassicalSmooth.UnramDatum`) at `y = 0`.

* `Coord ht`: the field `L` with `C(X)` acting through `X ↦ t` (`t` transcendental over `C`);
* **`KummerUnramFor`** (open, owner: O1 agent): the statement above.
-/

open Polynomial

namespace SemistableReduction

namespace ClassicalSmooth

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

section Coord

variable {L : Type*} [Field L] [Algebra C L]

/-- `L` with `C(X)` acting through the coordinate `X ↦ t`. -/
@[nolint unusedArguments]
def Coord {t : L} (_ht : Transcendental C t) : Type _ := L

variable {t : L} (ht : Transcendental C t)

instance : Field (Coord ht) := inferInstanceAs (Field L)

noncomputable instance : Algebra (RatFunc C) (Coord ht) :=
  (coordAlgHom ht).toRingHom.toAlgebra

instance : Algebra C (Coord ht) := inferInstanceAs (Algebra C L)

instance : IsScalarTower C (RatFunc C) (Coord ht) :=
  IsScalarTower.of_algebraMap_eq fun c ↦ ((coordAlgHom ht).commutes c).symm

/-- The identity `L → Coord ht`. -/
def toCoord : L ≃+* Coord ht := RingEquiv.refl L

omit [IsUltrametricDist C] in
lemma algebraMap_coord (φ : RatFunc C) :
    algebraMap (RatFunc C) (Coord ht) φ = toCoord ht (coordAlgHom ht φ) := rfl

end Coord

variable (C) in
/-- **Kummer base change kills ramification** (Blueprint §9.12 O6.1f(i), owner: O1 agent). For
every finite extension `F / C(x)` and `a ∈ C` there are `E ≥ 1`, a finite extension `L / F` and
`y ∈ L` with `y ^ E = x - a` and `L = F(y)` such that `L / C(y)` (`Coord`) is finite and carries
an unramified datum at `y = 0`. -/
def KummerUnramFor (F : Type*) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
    [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F] (a : C) : Prop :=
  ∃ (E : ℕ) (L : Type*) (_ : Field L) (_ : Algebra F L) (_ : FiniteDimensional F L)
    (_ : Algebra C L) (_ : IsScalarTower C F L) (y : L) (hy : Transcendental C y),
    0 < E ∧
    y ^ E = algebraMap F L (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) a)) ∧
    IntermediateField.adjoin F {y} = ⊤ ∧
    ∃ (_ : FiniteDimensional (RatFunc C) (Coord hy)) (θ : L) (n : ℕ)
      (γ : Fin n → HenselComplete.integers C), UnramDatum C (Coord hy) 0 (toCoord hy θ) γ

end ClassicalSmooth

end SemistableReduction
