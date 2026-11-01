/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateChartBaseChange
import TemperedFundamentalGroups.SemistableReduction.CuspInput
import TemperedFundamentalGroups.SemistableReduction.TateGlue0

/-!
# The cusp chart of the Tate model commutes with base change (MR12 S5.7)

**`TateTwoChart.baseChangeRc`**: `O' ⊗_O T0[1/(1 + h)] ≃ₐ[O'] T0'[1/(1 + h)]` for an `O`-algebra
`O'`, from `baseChangeT0` (`IsLocalization.Away.tensorProductEquivTMulRight`).
-/

universe u

open Polynomial TensorProduct

namespace SemistableReduction

namespace TateTwoChart

noncomputable section

variable {O : Type u} [CommRing O] (π b₄ t κ : O) (O' : Type u) [CommRing O'] [Algebra O O']

/-- **The cusp chart `Rc = T0[1/(1 + h)]` commutes with base change** `O → O'`. -/
def baseChangeRc : O' ⊗[O] CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) ≃ₐ[O']
    CuspTower.Rc (T0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
      (algebraMap O O' κ))
      (TateGlue0.c0 (algebraMap O O' π) (algebraMap O O' b₄) (algebraMap O O' t)
        (algebraMap O O' κ)) :=
  (IsLocalization.Away.tensorProductEquivTMulRight O O' (TateGlue0.c0 π b₄ t κ)
      (CuspTower.Rc (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ))).trans
    (IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers ((1 : O') ⊗ₜ TateGlue0.c0 π b₄ t κ))
      (T := Submonoid.powers (TateGlue0.c0 (algebraMap O O' π) (algebraMap O O' b₄)
        (algebraMap O O' t) (algebraMap O O' κ))) (Localization.Away _) (CuspTower.Rc _ _)
      (baseChangeT0 π b₄ t κ O')
      (by
        rw [Submonoid.map_powers]
        congr 1
        simp [TateGlue0.c0, h0, TensorProduct.tmul_add, Algebra.TensorProduct.one_def]))

end

end TateTwoChart

end SemistableReduction
