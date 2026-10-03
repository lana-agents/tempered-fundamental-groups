/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussClassification

/-!
# Valuations of `K(X)` as limits of Gauss valuations

Blueprint §9.9, S8.0. Let `K` be an algebraically closed field with a valuation `v`, and `w` a
valuation of `K(X)` (with values in the same group) extending `v`. For `a ∈ K` let
`ρ(a) = w(X - a)` (`GaussLimit.radius`). Then:

* `GaussLimit.radius_eq_max`: if `ρ(a) ≤ ρ(b)` then `ρ(b) = max (v(a - b)) ρ(a)`, i.e. `w` and the
  Gauss valuation `w_{a, ρ(a)}` agree on `X - b`;
* `GaussLimit.exists_forall_eq_gaussRat`: **`w` is approximated by Gauss valuations**: for every
  polynomial `p` there is `a` such that `w(p) = w_{a', ρ(a')}(p)` for every `a'` with
  `ρ(a') ≤ ρ(a)`;
* `GaussLimit.eq_gaussRat_of_le`: if `ρ` attains its infimum at `a`, then `w = w_{a, ρ(a)}` (the
  Gauss points of rational or irrational radius, types 2 and 3); otherwise `w` is the limit of the
  nested Gauss points `w_{a, ρ(a)}` (`GaussLimit.valuation_sub_le`: the discs are nested), a point
  of type 4.

No assumption on the value group or the residue field of `w` is made (compare W2,
`eq_gaussRat`). These are the limit points of the compactness argument S8.1.
-/

open Polynomial

namespace SemistableReduction

namespace GaussLimit

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} (w : Valuation (RatFunc K) Γ₀)

/-- The radius `w(X - a)` of `w` around `a`. -/
noncomputable def radius (a : K) : Γ₀ := w (algebraMap K[X] (RatFunc K) (X - C a))

lemma radius_ne_zero (a : K) : radius w a ≠ 0 := by
  rw [radius, Ne, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]
  exact X_sub_C_ne_zero a

/-- The radius `w(X - a)` as a unit. -/
noncomputable def radiusUnit (a : K) : Γ₀ˣ := Units.mk0 (radius w a) (radius_ne_zero w a)

@[simp]
lemma val_radiusUnit (a : K) : (radiusUnit w a : Γ₀) = radius w a := rfl

variable {w}

lemma algebraMap_X_sub_C (a b : K) : algebraMap K[X] (RatFunc K) (X - C b) =
    algebraMap K[X] (RatFunc K) (X - C a) + algebraMap K (RatFunc K) (a - b) := by
  rw [← ratFunc_algebraMap_C, ← map_add, C_sub]
  ring_nf

/-- If `w(X - a) ≤ w(X - b)`, then `w(X - b) = max (v(a - b)) (w(X - a))`. -/
lemma radius_eq_max (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) {a b : K}
    (h : radius w a ≤ radius w b) : radius w b = max (v (a - b)) (radius w a) := by
  have hsplit := algebraMap_X_sub_C (K := K) a b
  rcases lt_trichotomy (v (a - b)) (radius w a) with hlt | heq | hgt
  · rw [max_eq_right hlt.le, radius, hsplit,
      Valuation.map_add_eq_of_lt_left _ (by rwa [hw]), radius]
  · rw [heq, max_self]
    refine le_antisymm ?_ h
    rw [radius, hsplit]
    refine (Valuation.map_add _ _ _).trans (max_le le_rfl ?_)
    rw [hw, heq, radius]
  · rw [max_eq_left hgt.le, radius, hsplit,
      Valuation.map_add_eq_of_lt_right _ (by rwa [hw]), hw]

/-- If `w(X - a') ≤ w(X - a)`, then `v(a - a') ≤ w(X - a)`: the disc of radius `w(X - a')` around
`a'` lies in the disc of radius `w(X - a)` around `a`. -/
lemma valuation_sub_le (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) {a a' : K}
    (h : radius w a' ≤ radius w a) : v (a - a') ≤ radius w a := by
  rw [radius_eq_max hw h]
  exact le_max_left (v (a' - a)) _ |>.trans' (by rw [← Valuation.map_neg, neg_sub])

/-- `w` agrees with the Gauss valuation `w_{a, w(X - a)}` on `X - b` whenever
`w(X - a) ≤ w(X - b)`. -/
lemma radius_eq_gaussRat (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) {a b : K}
    (h : radius w a ≤ radius w b) :
    radius w b = gaussRat v a (radiusUnit w a) (algebraMap K[X] (RatFunc K) (X - C b)) := by
  rw [gaussRat_algebraMap, gauss_X_sub_C, val_radiusUnit, radius_eq_max hw h]

/-- **Gauss approximation**: for every polynomial `p` there is `a` such that `w(p)` is the value
of `p` at the Gauss valuation `w_{a', w(X - a')}` for every `a'` with `w(X - a') ≤ w(X - a)`. -/
theorem exists_forall_eq_gaussRat [IsAlgClosed K]
    (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c) (p : K[X]) :
    ∃ a : K, ∀ a' : K, radius w a' ≤ radius w a →
      w (algebraMap K[X] (RatFunc K) p) =
        gaussRat v a' (radiusUnit w a') (algebraMap K[X] (RatFunc K) p) := by
  -- `a` minimizes the radius over the roots of `p`
  classical
  obtain ⟨a, ha⟩ : ∃ a : K, ∀ α ∈ p.roots, radius w a ≤ radius w α := by
    rcases p.roots.toFinset.eq_empty_or_nonempty with h | h
    · exact ⟨0, fun α hα ↦ by simp_all⟩
    · obtain ⟨a, -, ha⟩ := Finset.exists_min_image _ (radius w) h
      exact ⟨a, fun α hα ↦ ha α (Multiset.mem_toFinset.2 hα)⟩
  refine ⟨a, fun a' ha' ↦ ?_⟩
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := p))]
  simp only [map_mul, map_multiset_prod, Multiset.map_map, ratFunc_algebraMap_C, hw,
    gaussRat_algebraMap_C]
  congr 2
  exact Multiset.map_congr rfl fun α hα ↦ radius_eq_gaussRat hw (ha'.trans (ha α hα))

/-- **Types 2 and 3**: if `w(X - a)` is the minimal radius, `w` is the Gauss valuation
`w_{a, w(X - a)}`. -/
theorem eq_gaussRat_of_le [IsAlgClosed K] (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c)
    {a : K} (ha : ∀ b, radius w a ≤ radius w b) : w = gaussRat v a (radiusUnit w a) :=
  valuation_ratFunc_ext_of_linear (fun c ↦ by rw [hw, gaussRat_algebraMap_C])
    fun b ↦ radius_eq_gaussRat hw (ha b)

/-- **Type 4**: if the radius has no minimum, `w` is not a Gauss valuation, and it is the limit of
the Gauss valuations `w_{a, w(X - a)}` along radii decreasing to the infimum. -/
theorem forall_ne_gaussRat [IsAlgClosed K] (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c)
    (hmin : ∀ a, ∃ b, radius w b < radius w a) (a : K) (r : Γ₀ˣ) : w ≠ gaussRat v a r := by
  rintro rfl
  obtain ⟨b, hb⟩ := hmin a
  have h1 : radius (gaussRat v a r) a = r := by
    rw [radius, gaussRat_algebraMap, gauss_X_sub_C, sub_self, map_zero, max_eq_right zero_le]
  have h2 : r ≤ radius (gaussRat v a r) b := by
    rw [radius, gaussRat_algebraMap, gauss_X_sub_C]
    exact le_max_right _ _
  exact absurd hb (not_lt.2 (h1 ▸ h2))

end GaussLimit

end SemistableReduction
