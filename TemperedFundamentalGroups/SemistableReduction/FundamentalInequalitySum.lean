/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalGlobal

/-!
# The fundamental inequality for all extensions (O1, step (2))

Blueprint §9.12, O1 (S7.9 (ii)). For a non-archimedean normed field `F` and `F' / F` finite
separable, the real valuations `w` of `F'` extending the norm satisfy
`Σ_w e(w | v) f(w | v) ≤ [F' : F]` (`finsum_ramificationIdx_mul_inertiaDeg_le`): by B2 each term
is `e · f` of the completion `\hat F[X]/(g)` over `\hat F`, which is at most its degree
(`FundamentalInequality.ramificationIdx_mul_inertiaDeg_le`), and the degrees of the factors add up
to `[F' : F]`. No defectlessness is needed (contrast B4).
-/

open Polynomial

namespace SemistableReduction

namespace LocalGlobal

open FundamentalInequality DenseCompletion

/-- **The fundamental inequality for all extensions**: `Σ_{w | v} e(w | v) f(w | v) ≤ [F' : F]`. -/
theorem finsum_ramificationIdx_mul_inertiaDeg_le {F : Type*} {F' : Type*}
    [NontriviallyNormedField F] [IsUltrametricDist F] [Field F'] [Algebra F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] :
    ∑ᶠ w : Extension F F', ramificationIdx F w.1 * inertiaDeg (NormedField.valuation (K := F)) w.1 ≤
      Module.finrank F F' := by
  classical
  let K := UniformSpace.Completion F
  haveI : Fact (DenseRange (algebraMap F K)) := ⟨denseRange_algebraMap_completion F⟩
  rw [← finsum_comp_equiv (extensionEquiv (K := K)) (f := fun w : Extension F F' ↦
      ramificationIdx F w.1 * inertiaDeg (NormedField.valuation (K := F)) w.1),
    finsum_eq_sum_of_fintype,
    ← sum_natDegree_factors (K := K), ← Finset.sum_coe_sort (factors F K F') natDegree]
  refine Finset.sum_le_sum fun g _ ↦ ?_
  change ramificationIdx F (extValuation g) * inertiaDeg _ (extValuation g) ≤ _
  rw [ramificationIdx_extValuation, inertiaDeg_extValuation, ← finrank_local]
  exact ramificationIdx_mul_inertiaDeg_le

end LocalGlobal

end SemistableReduction

namespace SemistableReduction

/-- **Counting `e` and `f` over a smaller base** (S7.9 (ii)): if `Σ eᵢ fᵢ ≤ n = Σ gᵢ` with
`gᵢ ≤ fᵢ` and `eᵢ ≥ 1`, then `eᵢ = 1` and `fᵢ = gᵢ` for all `i`. -/
theorem eq_one_and_eq_of_sum_le {ι : Type*} (s : Finset ι) (e f g : ι → ℕ) {n : ℕ}
    (hle : ∑ i ∈ s, e i * f i ≤ n) (hsum : ∑ i ∈ s, g i = n) (hgf : ∀ i ∈ s, g i ≤ f i)
    (he : ∀ i ∈ s, 1 ≤ e i) (hg : ∀ i ∈ s, 1 ≤ g i) :
    ∀ i ∈ s, e i = 1 ∧ f i = g i := by
  have hterm : ∀ i ∈ s, g i ≤ e i * f i := fun i hi ↦
    (hgf i hi).trans (Nat.le_mul_of_pos_left _ (he i hi))
  have heq : ∀ i ∈ s, e i * f i = g i := by
    have h1 : ∑ i ∈ s, e i * f i = ∑ i ∈ s, g i :=
      le_antisymm (hsum ▸ hle) (Finset.sum_le_sum hterm)
    intro i hi
    exact ((Finset.sum_eq_sum_iff_of_le hterm).mp h1.symm i hi).symm
  intro i hi
  have h1 := heq i hi
  have h2 := hgf i hi
  have h3 := he i hi
  have h4 := hg i hi
  have hf : f i = g i := by
    apply le_antisymm _ h2
    calc f i ≤ e i * f i := Nat.le_mul_of_pos_left _ h3
      _ = g i := h1
  refine ⟨?_, hf⟩
  rw [hf] at h1
  exact (Nat.mul_eq_right (by omega)).mp h1

end SemistableReduction
