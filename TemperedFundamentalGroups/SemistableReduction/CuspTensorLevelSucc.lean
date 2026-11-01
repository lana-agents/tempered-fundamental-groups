/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspTensorLevel
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevels
import TemperedFundamentalGroups.SemistableReduction.EtaleLevelSucc

/-!
# The patch sides `toTensorC` form a tower (MR12 T2 S6, G5 over `V₀`)

**`CuspTower.toTensorC_succ`**: the maps `toTensorC n : B₀/ϖⁿ⁺¹ → Rc/ϖⁿ⁺¹ ⊗_{Rc} Bc` commute with
the reductions `B₀/ϖⁿ⁺² → B₀/ϖⁿ⁺¹` and the maps `levelMap` of the levels of `Rc` (the hypothesis
`hμt` of `NodeEtaleGlue.Overlap.exists_iso_of_cuspLevels`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace CuspTower

noncomputable section

variable {O : Type u} [CommRing O] (ϖ : O) {T0' : Type u} [CommRing T0'] [Algebra O T0']
  (c0 : T0') (B₀ : Type u) [CommRing B₀] [Algebra T0' B₀] (Bc : Type u) [CommRing Bc]
  [Algebra (Rc T0' c0) Bc] [Algebra B₀ Bc]
  (hB : ∀ x, algebraMap (Rc T0' c0) Bc (algebraMap T0' (Rc T0' c0) x) =
    algebraMap B₀ Bc (algebraMap T0' B₀ x)) (n : ℕ)

/-- **The reduction `B₀/ϖⁿ⁺² → B₀/ϖⁿ⁺¹`.** -/
abbrev XmapC : TateGlue1.Xn ϖ T0' B₀ (n + 1) →+* TateGlue1.Xn ϖ T0' B₀ n :=
  Ideal.Quotient.factor (EtaleTower.In_succ_le (T := T0') (B := B₀) (ϖ := ϖ) n)

lemma toTensorC_succ_mk (b : B₀) :
    toTensorC ϖ c0 B₀ Bc hB n (XmapC ϖ B₀ n (Ideal.Quotient.mk _ b)) =
      FormalLevel.levelMap (fun l ↦ EtaleTower.Tn ϖ (Rc T0' c0) l) n
        (toTensorC ϖ c0 B₀ Bc hB (n + 1) (Ideal.Quotient.mk _ b)) :=
  (FormalLevel.levelMap_one_tmul (Rt := fun l ↦ EtaleTower.Tn ϖ (Rc T0' c0) l) n
    (algebraMap B₀ Bc b)).symm

/-- **The patch sides form a tower**: `toTensorC n ∘ XmapC n = levelMap n ∘ toTensorC (n + 1)`. -/
theorem toTensorC_succ (x : TateGlue1.Xn ϖ T0' B₀ (n + 1)) :
    toTensorC ϖ c0 B₀ Bc hB n (XmapC ϖ B₀ n x) =
      FormalLevel.levelMap (fun l ↦ EtaleTower.Tn ϖ (Rc T0' c0) l) n
        (toTensorC ϖ c0 B₀ Bc hB (n + 1) x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact toTensorC_succ_mk ϖ c0 B₀ Bc hB n b

end

end CuspTower

end SemistableReduction
