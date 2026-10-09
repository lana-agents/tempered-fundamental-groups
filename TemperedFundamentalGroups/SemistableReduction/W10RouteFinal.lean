/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DVRDescentRoute
import TemperedFundamentalGroups.SemistableReduction.SmoothFinal
import TemperedFundamentalGroups.SemistableReduction.W10RouteTree
import TemperedFundamentalGroups.SemistableReduction.W10Main

/-!
# G4 closed modulo the node descent

Blueprint §9.7a, step 4.

* `W10Route.treeChartsSemistable_of_node`: `NodeDescentStatement → W10.TreeChartsSemistable`
  (`treeChartsSemistable_of` with the proved `smoothDescentStatement`);
* `W10Assembly.strongA_of_W7_of_node`: `W7.Statement → NodeDescentStatement →
  Statement.StrongA` (`strongA_of_W7_of_tree`);
* `W10Route.treeChartsSemistable : W10.TreeChartsSemistable` (G4, unconditional, with the node
  descent `W10Route.nodeDescentStatement` (O1));
* `W10Assembly.strongA_of_W7 : W7.Statement → Statement.StrongA` (W10 closed).
-/

universe u

namespace SemistableReduction

/-- **G4 modulo the node descent.** -/
theorem W10Route.treeChartsSemistable_of_node (hN : W10Route.NodeDescentStatement.{u}) :
    W10.TreeChartsSemistable.{u} :=
  W10Route.treeChartsSemistable_of W10Route.smoothDescentStatement hN

/-- **StrongA from W7 and the node descent.** -/
theorem W10Assembly.strongA_of_W7_of_node (h7 : W7.Statement.{u, u})
    (hN : W10Route.NodeDescentStatement.{u}) :
    TemperedFundamentalGroups.SemistableReduction.Statement.StrongA.{u} :=
  W10Assembly.strongA_of_W7_of_tree h7 (W10Route.treeChartsSemistable_of_node hN)

/-- **G4**: the normalized charts of the tree models are semistable (unconditional). -/
theorem W10Route.treeChartsSemistable : W10.TreeChartsSemistable.{u} :=
  W10Route.treeChartsSemistable_of_node W10Route.nodeDescentStatement

/-- **W10 closed: StrongA from W7.** -/
theorem W10Assembly.strongA_of_W7 (h7 : W7.Statement.{u, u}) :
    TemperedFundamentalGroups.SemistableReduction.Statement.StrongA.{u} :=
  W10Assembly.strongA_of_W7_of_node h7 W10Route.nodeDescentStatement

end SemistableReduction
