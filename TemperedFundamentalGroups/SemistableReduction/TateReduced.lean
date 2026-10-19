/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueReduced
import TemperedFundamentalGroups.SemistableReduction.TateGlue0CuspTower
import TemperedFundamentalGroups.SemistableReduction.TateChartReduced

/-!
# The level-0 two-chart rings of the Tate coverings are reduced (Blueprint §12.8, M2.5 input)

Input `I2` of the normalised-model statement `TwoChartTower.isIntegralClosure_shift0/1` for the
Tate coverings: the level-`0` two-chart rings of `TateGlue0.overlap` (étale outside the nodes) and
`TateGlue0.overlapCusp` (ramified at the cusp) are reduced, for `(ϖ)` maximal.

* `isReduced_quot_pow_one`: `T/ϖ¹T = T/(ϖ)`;
* **`TateTwoChart.isReduced_T0_quot`, `isReduced_T1_quot`**: the special fibres
  `T0/ϖ`, `T1/ϖ` (the level-`0` charts `TateGlue0.B 0 = EtaleTower.Tn ϖ T0 0`,
  `TateGlue1.B 0 = TateLevel.T1n 0`) are reduced if `(ϖ)` is maximal, `ϖ ∣ π` and
  `κ (t² − b₆) = 1` (`isReduced_quotient_adjoinRoot`: `T/ϖ = (O/ϖ)[X][Y]/(Ḡ)`, and `Ḡ = Y·Q` with
  `Q` squarefree, `TateChartReduced`);
* **`TateGlue0.isReduced_overlap`**, **`TateGlue0.isReduced_overlapCusp`**: `R0` and `R1` of
  `twoChart 0` are reduced (`NodeEtaleGlue.Overlap.isReduced_twoChart`; the piece over `D(1 + h)`
  by `EtaleTower.Lift.isReduced` resp. `PatchInput.isReduced_piece`).
-/

universe u

open Polynomial

namespace SemistableReduction

/-- `T/ϖ¹T = T/(ϖ)`: reducedness transfers. -/
lemma isReduced_quot_pow_one {O T : Type*} [CommRing O] [CommRing T] [Algebra O T] (ϖ : O)
    (h : IsReduced (T ⧸ Ideal.span {algebraMap O T ϖ})) :
    IsReduced (T ⧸ (Ideal.span {ϖ} ^ (0 + 1)).map (algebraMap O T)) := by
  have e : (Ideal.span {ϖ} ^ (0 + 1)).map (algebraMap O T) = Ideal.span {algebraMap O T ϖ} := by
    rw [zero_add, pow_one, Ideal.map_span, Set.image_singleton]
  exact isReduced_of_injective (Ideal.quotEquivOfEq e) (Ideal.quotEquivOfEq e).injective

namespace TateTwoChart

variable {O : Type u} [CommRing O] (π b₄ t κ : O) {b₆ : O}
  (hκ : κ * (t ^ 2 - b₆) = 1) (ϖ : O) [(Ideal.span {ϖ}).IsMaximal] (hπ : ϖ ∣ π)

include hκ hπ

/-- **The special fibre `T0/ϖ` of the chart over `U₀` is reduced.** -/
theorem isReduced_T0_quot : IsReduced (T0 π b₄ t κ ⧸ (Ideal.span {ϖ} ^ (0 + 1)).map
    (algebraMap O (T0 π b₄ t κ))) := by
  refine isReduced_quot_pow_one ϖ ?_
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  have hπ' : Ideal.Quotient.mk (Ideal.span {ϖ}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hπ)
  have hκ' : Ideal.Quotient.mk (Ideal.span {ϖ}) κ ≠ 0 :=
    left_ne_zero_of_mul_eq_one (b := Ideal.Quotient.mk (Ideal.span {ϖ}) (t ^ 2 - b₆))
      (by rw [← map_mul, hκ, map_one])
  refine isReduced_quotient_adjoinRoot ϖ _ ?_
  rw [map_G0_eq π b₄ t κ _ hπ']
  exact isReduced_adjoinRoot_X_mul (monic_Q0 t κ _) (natDegree_Q0 t κ _)
    (squarefree_coeff_Q0 t hκ') (not_isUnit_coeff_Q0 t hκ')

/-- **The special fibre `T1/ϖ` of the chart over `U₁` is reduced.** -/
theorem isReduced_T1_quot : IsReduced (T1 π b₄ t κ ⧸ (Ideal.span {ϖ} ^ (0 + 1)).map
    (algebraMap O (T1 π b₄ t κ))) := by
  refine isReduced_quot_pow_one ϖ ?_
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  have hπ' : Ideal.Quotient.mk (Ideal.span {ϖ}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hπ)
  have hκ' : Ideal.Quotient.mk (Ideal.span {ϖ}) κ ≠ 0 :=
    left_ne_zero_of_mul_eq_one (b := Ideal.Quotient.mk (Ideal.span {ϖ}) (t ^ 2 - b₆))
      (by rw [← map_mul, hκ, map_one])
  refine isReduced_quotient_adjoinRoot ϖ _ ?_
  rw [map_G1_eq π b₄ t κ _ hπ']
  exact isReduced_adjoinRoot_X_mul (monic_Q1 t κ _) (natDegree_Q1 t κ _)
    (squarefree_coeff_Q1 t hκ') (not_isUnit_coeff_Q1 t hκ')

end TateTwoChart

namespace TateGlue0

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
  {hπe : θ (ϖ ^ m) = 0} {τ : TateGlue1.Rb b₄ b₆ ϖ m ε}
  {cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]
  (Sp : TateGlue1.Special1 hκ hπ hπe τ cov₀) (hm : m ≠ 0)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) [(Ideal.span {ϖ}).IsMaximal]

omit [IsNoetherianRing O] in
include hκ hπ hm in
/-- The level-`0` chart over `U₁` is reduced. -/
lemma isReduced_B1 : IsReduced (TateGlue1.B ϖ π b₄ t κ 0) :=
  isReduced_T1_quot π b₄ t κ hκ ϖ (hπ ▸ dvd_mul_of_dvd_right (dvd_pow_self ϖ hm) ε)

omit [IsNoetherianRing O] in
include hκ hπ hm in
/-- The level-`0` chart over `U₀` is reduced. -/
lemma isReduced_B0 : IsReduced (B ϖ π b₄ t κ 0) :=
  isReduced_T0_quot π b₄ t κ hκ ϖ (hπ ▸ dvd_mul_of_dvd_right (dvd_pow_self ϖ hm) ε)

/-- **The level-`0` two-chart rings of the Tate covering étale outside the nodes are reduced.** -/
theorem isReduced_overlap (Sp0 : Special0 θ π b₄ t κ) (ω : Omega hκ hπ Sp Sp0) :
    IsReduced ((overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).twoChart hθ.out hO 0).R0 ∧
      IsReduced ((overlap hκ hπ hε hϖ π' hπ' hker Sp hm Sp0 ω).twoChart hθ.out hO 0).R1 := by
  haveI := isReduced_B0 hκ hπ hm (ϖ := ϖ) (b₄ := b₄)
  have hE : IsReduced (E0 Sp0 hϖ hker 0).E := EtaleTower.Lift.isReduced _
  exact NodeEtaleGlue.Overlap.isReduced_twoChart hθ.out hO 0 _
    (hB := isReduced_B1 hκ hπ hm (b₄ := b₄))
    (hBN := (inferInstance : IsNoetherianRing (TateGlue1.B ϖ π b₄ t κ 0))) (hP := hE)

/-- **The level-`0` two-chart rings of the Tate covering ramified at the cusp are reduced.** -/
theorem isReduced_overlapCusp
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ))
    (ω : OmegaC hκ hπ Sp Sc.C0) :
    IsReduced ((overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).twoChart hθ.out hO 0).R0 ∧
      IsReduced ((overlapCusp hκ hπ hε hϖ π' hπ' hker Sp hm Sc hO ω).twoChart hθ.out hO 0).R1 := by
  haveI := isReduced_B0 hκ hπ hm (ϖ := ϖ) (b₄ := b₄)
  have hP := NodeEtaleGlue.PatchInput.isReduced_piece hθ.out hO 0
    (CuspTower.cuspInput Sc hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ))
  exact NodeEtaleGlue.Overlap.isReduced_twoChart hθ.out hO 0 _
    (hB := isReduced_B1 hκ hπ hm (b₄ := b₄))
    (hBN := (inferInstance : IsNoetherianRing (TateGlue1.B ϖ π b₄ t κ 0))) (hP := hP)

end TateGlue0

end SemistableReduction
