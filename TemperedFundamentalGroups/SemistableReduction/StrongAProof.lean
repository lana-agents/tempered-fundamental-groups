/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W7Final
import TemperedFundamentalGroups.SemistableReduction.R5Measure

/-!
# Semistable reduction over mixed-characteristic DVRs, unconditionally

Blueprint §9.12, §9.7a. The last open leaf of W7, R5 (`S8A.R5MeasureFor`, O6.2), is
`S8A.r5MeasureFor_of` from the gluing step `ExhaustGlue.exhaustGlueFor`. Hence:

* `W7.openLeaves : W7.OpenLeaves`;
* **`W7.statement : W7.Statement`**;
* **`Statement.strongA : Statement.StrongA`** (W10, via `W10Assembly.strongA_of_W7`).
-/

universe u

namespace SemistableReduction

namespace W7

/-- All local leaves of W7 are proved. -/
theorem openLeaves : OpenLeaves.{u} where
  r5 := by
    intro C _ _ _ _ p hp hp1 F _ _ _ _ _ _ _
    exact S8A.r5MeasureFor_of hp hp1 (ExhaustGlue.exhaustGlueFor hp hp1)

/-- **W7**, unconditionally. -/
theorem statement : W7.Statement.{u, u} :=
  statement_of_openLeaves openLeaves

end W7

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction.Statement

/-- **Semistable reduction (`StrongA`, W10)**, unconditionally. -/
theorem strongA : StrongA.{u} :=
  _root_.SemistableReduction.W10Assembly.strongA_of_openLeaves
    _root_.SemistableReduction.W7.openLeaves

end TemperedFundamentalGroups.SemistableReduction.Statement
