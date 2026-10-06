/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhInter
import TemperedFundamentalGroups.SemistableReduction.TypeOneGerm
import TemperedFundamentalGroups.SemistableReduction.TypeTwoGerm

/-!
# S8.B from the remaining open inputs (O6.1)

Blueprint §9.12 O6.1. `S8A.s8bMinFor_of_open` assembles `S8BMinFor C F` from the inputs that are
still open (each recorded in §9.12 with its owner):

* O6.1a `R4ExFor` (R4 agent);
* O6.1c `L7For` (S8.5 agent);
* (T⇒) `TubeOfExhausting`, (T⇐) `ExhaustingOfTube`, (D⇒) `DiscCondOfSmooth`,
  (D⇐) `SmoothOfDiscCond` (M10/O9 agent; give O11, O11g and O6.1b);
* O6.1f(i) `KummerUnramFor` (R4 agent) and O6.1f(iii) `A6For` (S8.A agent);
* O6.1h `TypeThreeGermFor` (S8.B agent).

The type-2 germ (O6.1g) is proved (`typeTwoGermFor`).
-/

namespace SemistableReduction

namespace S8A

open ExhaustGluing ClassicalSmooth

universe w

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- **S8.B** from the open inputs. -/
theorem s8bMinFor_of_open (hR4 : R4ExFor C F) (hL7 : L7For C F)
    (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F) (hD : DiscCondOfSmooth C F)
    (hD' : SmoothOfDiscCond C F) (hK : ∀ a : C, KummerUnramFor.{_, _, w} C F a)
    (hA6 : ∀ (L : Type w) [Field L] [Algebra (RatFunc C) L] [Algebra F L]
      [IsScalarTower (RatFunc C) F L] [Algebra C L] [IsScalarTower C (RatFunc C) L]
      [FiniteDimensional (RatFunc C) L] [IsGalois F L], A6For C F L)
    (h3 : TypeThreeGermFor C F) : S8BMinFor C F :=
  s8bMinFor_of_inputs
    { r4ex := hR4
      inter := exhInterFor_of hT hD' (goodGluingFor_of hT hD hD')
      l7 := hL7
      o11 := o11For_of hT hT'
      goodGluing := goodGluingFor_of hT hD hD'
      classical := classicalGoodFor_of hp hp1 hK hA6
      typeTwo := typeTwoGermFor hp hp1
      typeThree := h3 }

end S8A

end SemistableReduction
