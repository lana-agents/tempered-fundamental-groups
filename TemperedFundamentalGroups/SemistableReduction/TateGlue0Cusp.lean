/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspTower
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Patch
import TemperedFundamentalGroups.SemistableReduction.TateGlue0
import TemperedFundamentalGroups.SemistableReduction.TateLevel

/-!
# The coordinate `h` around the cusp of the Tate chart (Blueprint §12.8, M2.3 (f), cusps)

The origin `O = [0:1:0]` of the Tate curve is the point `h = z = 0` of the chart
`V₀ = Spec T0`; the fibre of `toP1` over `h = 0` consists of `O` and the two points
`[0 : ±√b₆ : 1]`, all in `D(1 + h)`. A covering of the special fibre of `E ∖ {O}` tamely ramified
over `O` ([Mzk1] §3.9 (1′A)) is, over `D(1 + h)`, an admissible covering of `T0[1/(1 + h)]/J`
without nodes with cusp factors `X^e = h` over the points of `V(h)` (over `[0 : ±√b₆ : 1]` it is
étale, i.e. its cusp factors there have index `1` in the split form of `Admissible.Covering`,
cf. the [Mzk1] check in the Blueprint). Its piece over `D(1 + h)` is the cusp patch
`CuspTower.cuspPiece` with `c₀ = 1 + h`, `x₀ = h`; the input needed here:

* `BasisIdeal.repr_mem`, `mem_of_repr_mem`: the coordinates of an element of `I T` in a basis of
  `T` over `A` lie in `I`, and conversely;
* **`TateGlue0.isSMulRegular_h0`**: `h` is regular on the levels `T0/ϖⁿ⁺¹` (`T0` is free over
  `O[h]` and `h` is regular on `O[h]/ϖⁿ⁺¹`).
-/

universe u

open Polynomial

namespace SemistableReduction

/-! ### Coordinates of extended ideals in a basis -/

namespace BasisIdeal

variable {A T : Type u} {ι : Type*} [CommRing A] [CommRing T] [Algebra A T] (b : Module.Basis ι A T)
  (I : Ideal A)

/-- The coordinates of an element of `I T` lie in `I`. -/
lemma repr_mem {x : T} (hx : x ∈ I.map (algebraMap A T)) (i : ι) : b.repr x i ∈ I := by
  have hx' : x ∈ I • (⊤ : Submodule A T) := by
    rw [Ideal.smul_top_eq_map]
    exact hx
  refine Submodule.smul_induction_on hx' (p := fun x ↦ b.repr x i ∈ I)
    (fun r hr m _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact I.mul_mem_right _ hr
  · rw [map_add, Finsupp.add_apply]
    exact I.add_mem hx hy

/-- An element whose coordinates lie in `I` lies in `I T`. -/
lemma mem_of_repr_mem [Finite ι] {x : T} (h : ∀ i, b.repr x i ∈ I) :
    x ∈ I.map (algebraMap A T) := by
  haveI := Fintype.ofFinite ι
  rw [← b.sum_repr x]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h i))

end BasisIdeal

namespace TateGlue0

open TateTwoChart TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] (ϖ π b₄ t κ : O)

/-! ### `h` is regular on the levels -/

lemma X_mul_mem {n : ℕ} {c : O[X]}
    (hc : X * c ∈ (EtaleTower.Iv ϖ n).map (algebraMap O O[X])) :
    c ∈ (EtaleTower.Iv ϖ n).map (algebraMap O O[X]) := by
  have e : (EtaleTower.Iv ϖ n).map (algebraMap O O[X]) = Ideal.span {C (ϖ ^ (n + 1))} := by
    rw [EtaleTower.Iv, Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton,
      Polynomial.algebraMap_eq]
  rw [e, Ideal.mem_span_singleton, Polynomial.C_dvd_iff_dvd_coeff] at hc ⊢
  intro i
  have := hc (i + 1)
  rwa [Polynomial.coeff_X_mul] at this

/-- **`h` is regular on the levels `T0/ϖⁿ⁺¹` of the chart over `U₀`.** -/
theorem isSMulRegular_h0 (n : ℕ) :
    IsSMulRegular (Tn ϖ (T0 π b₄ t κ) n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O (T0 π b₄ t κ))) (h0 π b₄ t κ) :
        Tn ϖ (T0 π b₄ t κ) n) := by
  set b := (AdjoinRoot.powerBasis' (monic_G0 π b₄ t κ)).basis
  set I := (EtaleTower.Iv ϖ n).map (algebraMap O O[X])
  have hI : (EtaleTower.Iv ϖ n).map (algebraMap O (T0 π b₄ t κ)) =
      I.map (algebraMap O[X] (T0 π b₄ t κ)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  intro y z hyz
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk _ (h0 π b₄ t κ) * Ideal.Quotient.mk _ y =
    Ideal.Quotient.mk _ (h0 π b₄ t κ) * Ideal.Quotient.mk _ z at hyz
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at hyz
  rw [Ideal.Quotient.eq]
  rw [hI] at hyz ⊢
  refine BasisIdeal.mem_of_repr_mem b I fun i ↦ X_mul_mem ϖ ?_
  have h := BasisIdeal.repr_mem b I hyz i
  rwa [show h0 π b₄ t κ * (y - z) = (X : O[X]) • (y - z) by
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq], map_smul, Finsupp.smul_apply,
    smul_eq_mul] at h

end

end TateGlue0

end SemistableReduction
