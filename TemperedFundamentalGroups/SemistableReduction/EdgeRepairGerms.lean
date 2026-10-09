/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.EdgeRepair
import TemperedFundamentalGroups.SemistableReduction.ExhInter
import TemperedFundamentalGroups.SemistableReduction.TypeTwoGerm

/-!
# The germ inputs of EdgeRepair

Blueprint §9.12, O10. Two of the named germ hypotheses of `EdgeRepair.edgeRepairFor` are
discharged:

* `EdgeRepair.belowGerm_holds`: **R4(ii)** `BelowGerm` is `GaussTube.belowGerm` (unconditional);
* `EdgeRepair.aboveGerm_of`: its **dual** `AboveGerm` follows from the outward germ at a type-2
  point `S8A.typeTwoGermFor` (fixed centre) and representation independence of exhaustion
  `S8A.edgeGood_of_isExhausting` (under (T⇒), (T⇐)).

Hence `EdgeRepair.edgeRepairFor_of`: EdgeRepair from (T⇒), (T⇐) and the type-3 germ.
-/

open Metric

namespace SemistableReduction

namespace EdgeRepair

open GaussTube AffineTwist ExhaustGluing

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- **R4(ii)** in the form consumed by EdgeRepair (unconditional). -/
theorem belowGerm_holds : BelowGerm C F :=
  fun a c hc ↦ GaussTube.belowGerm hp hp1 a c hc

include hp hp1 in
/-- **The dual of R4(ii)** (under (T⇒), (T⇐)): every disc `D(a, |c|)` is exhausting in the residue
class of `w_{a,|c₂|}` containing it, for `|c| < |c₂| ≤ ρ₂`. -/
theorem aboveGerm_of (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F) :
    AboveGerm C F := by
  intro a c hc
  obtain ⟨ρ', hρ', H⟩ := S8A.typeTwoGermFor hp hp1 (F := F) a c hc
  refine ⟨ρ', hρ', fun c₂ hc₂ hc₂ρ ↦ ?_⟩
  have hc₂0 : c₂ ≠ 0 := norm_pos_iff.1 ((norm_nonneg c).trans_lt hc₂)
  have hc₂pos : 0 < ‖c₂‖ := norm_pos_iff.2 hc₂0
  have hq : ‖c / c₂‖ < 1 := by rw [norm_div, div_lt_one hc₂pos]; exact hc₂
  have hq0 : c / c₂ ≠ 0 := div_ne_zero hc hc₂0
  have hnorm : ‖c₂ * (c / c₂)‖ = ‖c‖ := by rw [mul_div_cancel₀ _ hc₂0]
  have hE := H c₂ (c / c₂) hc₂0 hq hq0 hnorm hc₂ρ
  have hgood := S8A.edgeGood_of_isExhausting hT hT' hc₂0 hq hq0 hE
  rw [hnorm] at hgood
  exact hgood

include hp hp1 in
/-- **O10: EdgeRepair** from (T⇒), (T⇐) and the type-3 germ. -/
theorem edgeRepairFor_of (hT : TubeOfExhausting C F) (hT' : ExhaustingOfTube C F)
    (h3 : TypeThreeGerm C F) : EdgeRepairFor C F :=
  edgeRepairFor hT hT' (belowGerm_holds hp hp1) (aboveGerm_of hp hp1 hT hT') h3

end EdgeRepair

end SemistableReduction
