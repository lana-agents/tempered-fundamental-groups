/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Localizations away from products (Blueprint §12.8, M2.3 (f))

* **`AwayDvd.away_of_dvd`**: a localization away from `x y` is a localization away from `y` as
  soon as `x` divides a power of `y` (e.g. the node function `f = u + v` divides a power of `u`
  on a level of the node chart, so the node patch localized away from `u = w` is its étale part
  localized away from `w`);
* `AwayDvd.dvd_pow_of_mul_eq`: if `u v = p` with `p` nilpotent (`p^N = 0`), then `u + v` divides
  `u^{2N}`.
-/

universe u v

namespace SemistableReduction

namespace AwayDvd

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- **A localization away from `x y` is a localization away from `y` if `x ∣ yᵏ`.** -/
theorem away_of_dvd (x y : R) (k : ℕ) (h : x ∣ y ^ k) [IsLocalization.Away (x * y) S] :
    IsLocalization.Away y S := by
  have hxy : IsUnit (algebraMap R S (x * y)) := IsLocalization.Away.algebraMap_isUnit (x * y)
  rw [map_mul] at hxy
  have hx : IsUnit (algebraMap R S x) := isUnit_of_mul_isUnit_left hxy
  have hy : IsUnit (algebraMap R S y) := isUnit_of_mul_isUnit_right hxy
  set N : Submonoid R := Submonoid.powers x ⊔ Submonoid.powers y
  have hu : ∀ r ∈ N, IsUnit (algebraMap R S r) := fun r hr ↦ by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.mp hr
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    rw [map_mul, map_pow, map_pow]
    exact (hx.pow i).mul (hy.pow j)
  have hle : Submonoid.powers (x * y) ≤ N := by
    rintro _ ⟨i, rfl⟩
    change (x * y) ^ i ∈ N
    rw [mul_pow]
    exact Submonoid.mul_mem _ (Submonoid.mem_sup_left ⟨i, rfl⟩)
      (Submonoid.mem_sup_right ⟨i, rfl⟩)
  have hN : IsLocalization N S := IsLocalization.of_le (Submonoid.powers (x * y)) N hle hu
  refine (IsLocalization.iff_of_le_of_exists_dvd (M := Submonoid.powers y) N le_sup_right
    fun r hr ↦ ?_).mpr hN
  obtain ⟨a, ha, b, hb, rfl⟩ := Submonoid.mem_sup.mp hr
  obtain ⟨i, rfl⟩ := ha
  obtain ⟨j, rfl⟩ := hb
  refine ⟨y ^ (k * i + j), ⟨_, rfl⟩, ?_⟩
  rw [pow_add, pow_mul]
  exact mul_dvd_mul (pow_dvd_pow_of_dvd h i) dvd_rfl

/-- If `u v = p` and `p^N = 0`, then `u + v` divides `u^{2N}`. -/
theorem dvd_pow_of_mul_eq {u v p : R} (h : u * v = p) {N : ℕ} (hN : p ^ N = 0) :
    u + v ∣ u ^ (2 * N) := by
  have h1 : u ^ 2 - (-p) ∣ (u ^ 2) ^ N - (-p) ^ N := sub_dvd_pow_sub_pow _ _ N
  have h2 : u ^ 2 - (-p) = u * (u + v) := by rw [← h]; ring
  have h3 : (-p) ^ N = 0 := by rw [neg_pow, hN, mul_zero]
  rw [h2, h3, sub_zero, ← pow_mul] at h1
  exact (dvd_mul_left _ _).trans h1

end AwayDvd

end SemistableReduction
