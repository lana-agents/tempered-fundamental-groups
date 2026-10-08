/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ExhInter
import TemperedFundamentalGroups.SemistableReduction.TypeOneGerm
import TemperedFundamentalGroups.SemistableReduction.TypeTwoGerm
import TemperedFundamentalGroups.SemistableReduction.KummerUnram
import TemperedFundamentalGroups.SemistableReduction.InftyGerm

/-!
# S8.B from the remaining open inputs (O6.1)

Blueprint §9.12 O6.1. `S8A.s8bMinFor_of_open` assembles `S8BMinFor C F` from the inputs that are
still open (each recorded in §9.12 with its owner):

* O6.1c `L7For` (S8.5 agent);
* (T⇒) `TubeOfExhausting`, (T⇐) `ExhaustingOfTube`, (D⇒) `DiscCondOfSmooth`,
  (D⇐) `SmoothOfDiscCond` (M10/O9 agent; give O11, O11g and O6.1b);
* O6.1f(iii) `A6For` (S8.A agent; O6.1f(i) `KummerUnramFor` is proved, `kummerUnramFor`);
* O6.1h `TypeThreeGermFor` (S8.B agent).

The type-2 germ (O6.1g) is proved (`typeTwoGermFor`), and O6.1a `R4ExFor` follows from R4(ii)
(`GaussTube.belowGerm`, proved) and (T⇒), (T⇐) (`r4ExFor_of`).
-/

namespace SemistableReduction

namespace S8A

open ExhaustGluing ClassicalSmooth

universe u v

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type v} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- **S8.B** from the open inputs. -/
theorem s8bMinFor_of_open (hL7 : L7For C F)
    (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F) (hD : DiscCondOfSmooth C F)
    (hD' : SmoothOfDiscCond C F)
    (hA6 : ∀ (L : Type v) [Field L] [Algebra (RatFunc C) L] [Algebra F L]
      [IsScalarTower (RatFunc C) F L] [Algebra C L] [IsScalarTower C (RatFunc C) L]
      [FiniteDimensional (RatFunc C) L] [IsGalois F L], A6For C F L)
    (h3 : TypeThreeGermFor C F) : S8BMinFor C F :=
  s8bMinFor_of_inputs
    { r4ex := r4ExFor_of hp hp1 hT hT'
      inter := exhInterFor_of hT hD' (goodGluingFor_of hT hD hD')
      l7 := hL7
      o11 := o11For_of hT hT'
      goodGluing := goodGluingFor_of hT hD hD'
      classical := classicalGoodFor_of hp hp1 (fun a ↦ kummerUnramFor F a) hA6
      typeTwo := typeTwoGermFor hp hp1
      typeThree := h3 }

include hp hp1 in
/-- **O6.4** from A6 for `Inv 1 F` (Kummer base change is proved). -/
theorem inftyGoodFor_of_A6
    (hA6 : ∀ (L : Type v) [Field L] [Algebra (RatFunc C) L]
      [Algebra (GaussTube.Inv (1 : C) one_ne_zero F) L]
      [IsScalarTower (RatFunc C) (GaussTube.Inv (1 : C) one_ne_zero F) L] [Algebra C L]
      [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
      [IsGalois (GaussTube.Inv (1 : C) one_ne_zero F) L],
      A6For C (GaussTube.Inv (1 : C) one_ne_zero F) L) :
    InftyGoodFor C F :=
  inftyGoodFor_of hp hp1 (fun a ↦ kummerUnramFor _ a) hA6

end S8A

end SemistableReduction
