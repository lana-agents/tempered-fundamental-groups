/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TwoChartTower

/-!
# Maps of two-chart rings from maps of the charts (MR12 T2 S6, G5)

The overlap ring `R01` of two-chart rings `D` is the localization of the chart `R1` away from `y`
(`ProjectiveLine.TwoChartRings.isLocalization_ρ1`, from `exists1`, `ker1` and `ρ1 y = u⁻¹`). Hence:

* **`TwoChartMap.ofCharts`**: `A`-algebra maps `f0 : D.R0 → D'.R0`, `f1 : D.R1 → D'.R1` with
  `f0 x = x'`, `f1 y = y'`, compatible with the restrictions to the overlaps (in the form `hρ`:
  `ρ0 a · ρ1(y)ᵏ = ρ1 m` implies `ρ0' (f0 a) · ρ1'(y')ᵏ = ρ1' (f1 m)`) define a map of two-chart
  rings (`f01` is the localization of `f1`);
* **`TwoChartMap.ofCharts_comp_f01`**: maps out of `D` whose `f1`-components satisfy
  `e.f1 ∘ β.f1 = β'.f1` satisfy `e.f01 ∘ β.f01 = β'.f01` (the hypothesis `hc01` of
  `TwoChartTower.exists_iso_of_algebraization_shift` from `hc1`).
-/

universe u

noncomputable section

namespace ProjectiveLine.TwoChartRings

variable {A : Type u} [CommRing A]

variable (D : TwoChartRings A)

/-- **The overlap is the localization of the chart `R1` away from `y`.** -/
theorem isLocalization_ρ1 : letI := D.ρ1.toRingHom.toAlgebra
    IsLocalization.Away D.y D.R01 := by
  letI := D.ρ1.toRingHom.toAlgebra
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    change IsUnit (D.ρ1 (D.y ^ k))
    rw [map_pow, D.ρ1_y]
    exact (Units.isUnit _).pow k
  · intro z
    obtain ⟨m, k, h⟩ := D.exists1 z
    refine ⟨(m, ⟨D.y ^ k, k, rfl⟩), ?_⟩
    change z * D.ρ1 (D.y ^ k) = D.ρ1 m
    rw [map_pow, D.ρ1_y, mul_comm, h]
  · intro a b h
    change D.ρ1 a = D.ρ1 b at h
    obtain ⟨k, hk⟩ := D.ker1 (a - b) (by rw [map_sub, h, sub_self])
    exact ⟨⟨D.y ^ k, k, rfl⟩, by
      change D.y ^ k * a = D.y ^ k * b
      rw [← sub_eq_zero, ← mul_sub, hk]⟩

lemma isUnit_ρ1_y : IsUnit (D.ρ1 D.y) := by
  rw [D.ρ1_y]
  exact Units.isUnit _

end ProjectiveLine.TwoChartRings

end

namespace SemistableReduction

open ProjectiveLine

noncomputable section

variable {A : Type u} [CommRing A]


namespace TwoChartMap

variable {D D' : TwoChartRings A} (f0 : D.R0 →ₐ[A] D'.R0) (f1 : D.R1 →ₐ[A] D'.R1)
  (hx : f0 D.x = D'.x) (hy : f1 D.y = D'.y)

include hy in
lemma isUnit_ρ1_f1 : IsUnit (((D'.ρ1 : D'.R1 →+* D'.R01).comp (f1 : D.R1 →+* D'.R1)) D.y) := by
  change IsUnit (D'.ρ1 (f1 D.y))
  rw [hy]
  exact D'.isUnit_ρ1_y

/-- The map of the overlaps: `f1` localized away from `y`. -/
def f01Of : D.R01 →ₐ[A] D'.R01 :=
  letI := D.ρ1.toRingHom.toAlgebra
  haveI := D.isLocalization_ρ1
  { IsLocalization.Away.lift D.y (isUnit_ρ1_f1 f1 hy) with
    commutes' := fun a ↦ by
      change IsLocalization.Away.lift D.y (isUnit_ρ1_f1 f1 hy) (algebraMap A D.R01 a) = _
      rw [← D.ρ1.commutes a]
      change IsLocalization.Away.lift D.y (isUnit_ρ1_f1 f1 hy)
        (algebraMap D.R1 D.R01 (algebraMap A D.R1 a)) = _
      rw [IsLocalization.Away.lift_eq]
      simp only [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes] }

lemma f01Of_ρ1 (r : D.R1) : f01Of f1 hy (D.ρ1 r) = D'.ρ1 (f1 r) := by
  letI := D.ρ1.toRingHom.toAlgebra
  haveI := D.isLocalization_ρ1
  exact IsLocalization.Away.lift_eq D.y (isUnit_ρ1_f1 f1 hy) r

variable (hρ : ∀ a m (k : ℕ), D.ρ0 a * D.ρ1 D.y ^ k = D.ρ1 m →
  D'.ρ0 (f0 a) * D'.ρ1 D'.y ^ k = D'.ρ1 (f1 m))

include hρ in
lemma f01Of_ρ0 (a : D.R0) : f01Of f1 hy (D.ρ0 a) = D'.ρ0 (f0 a) := by
  obtain ⟨m, k, h⟩ := D.exists1 (D.ρ0 a)
  rw [← D.ρ1_y, mul_comm] at h
  have h' := hρ a m k h
  have e : f01Of f1 hy (D.ρ0 a) * D'.ρ1 D'.y ^ k = D'.ρ1 (f1 m) := by
    rw [← hy, ← f01Of_ρ1 f1 hy, ← f01Of_ρ1 f1 hy, ← map_pow, ← map_mul, h]
  exact (D'.isUnit_ρ1_y.pow k).mul_left_injective (e.trans h'.symm)

/-- **A map of two-chart rings from maps of the charts** compatible with the restrictions. -/
def ofCharts : TwoChartMap D D' where
  f0 := f0
  f1 := f1
  f01 := f01Of f1 hy
  hx := hx
  hy := hy
  hu := by
    rw [← D.ρ0_x, f01Of_ρ0 f0 f1 hy hρ, hx, D'.ρ0_x]
  h0 := f01Of_ρ0 f0 f1 hy hρ
  h1 := f01Of_ρ1 f1 hy

lemma ofCharts_f0 : (ofCharts f0 f1 hx hy hρ).f0 = f0 := rfl

lemma ofCharts_f1 : (ofCharts f0 f1 hx hy hρ).f1 = f1 := rfl

/-- **The overlap components are determined by the `R1`-components**: if `e.f1 ∘ β.f1 = β'.f1`,
then `e.f01 ∘ β.f01 = β'.f01`. -/
theorem comp_f01_of_f1 {D'' : TwoChartRings A} (β : TwoChartMap D D') (β' : TwoChartMap D D'')
    (e : TwoChartMap D' D'') (h : e.f1.comp β.f1 = β'.f1) : e.f01.comp β.f01 = β'.f01 := by
  letI := D.ρ1.toRingHom.toAlgebra
  haveI := D.isLocalization_ρ1
  refine AlgHom.coe_ringHom_injective (IsLocalization.ringHom_ext (Submonoid.powers D.y)
    (RingHom.ext fun r ↦ ?_))
  change e.f01 (β.f01 (D.ρ1 r)) = β'.f01 (D.ρ1 r)
  rw [β.h1, e.h1, β'.h1]
  exact congrArg D''.ρ1 (AlgHom.congr_fun h r)

end TwoChartMap

end

end SemistableReduction
