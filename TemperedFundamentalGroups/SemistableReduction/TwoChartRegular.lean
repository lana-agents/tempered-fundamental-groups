/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TwoChartGlue
import TemperedFundamentalGroups.SemistableReduction.FibreFlat

/-!
# Torsion-freeness over `k[X]` of two-chart rings (Blueprint §12.8, M2.4, step 3f)

For an `A`-algebra `R`, an element `x` and an ideal `I ⊆ A`:

* **`PolyRegular I x`**: `p(x)` is a nonzerodivisor of `R` for every `p ∉ I A[X]` (for `R`
  killed by a maximal `I`: `R` is torsion-free over `(A/I)[X]`, `X ↦ x`);
* `PolyRegular.fibreRegular`: then the chart module `R` (`X` acting by `x`) is `FibreRegular`;
* **`TwoChartRings.polyRegular_u`**: on a two-chart ring, `PolyRegular` of the coordinate `y` of
  `R1` gives `PolyRegular` of `T = u` on the overlap `R01 = R1[1/y]` (via the reflected
  polynomials: `p(T) Tᴺ`-multiples are `p̃(y)`, `p̃ = reflect N p`);
* **`TwoChartGlue.polyRegular_x`**: for the two-chart rings of a Zariski glueing
  `R0 = Q ×_{P0ab} P0b` (`TwoChartGlue.twoChart`), `PolyRegular` of `x` on `R0` from `PolyRegular`
  of `y` on `R1` and of `x₀` on the second piece `P0b`.
-/

universe u

open Polynomial

namespace SemistableReduction

section PolyRegular

variable {A : Type u} [CommRing A] (I : Ideal A) {R : Type u} [CommRing R] [Algebra A R]

/-- **`p(x)` is a nonzerodivisor for every polynomial `p ∉ I A[X]`.** -/
def PolyRegular (x : R) : Prop := ∀ p : A[X], p ∉ I.map C → IsSMulRegular R (aeval x p)

variable {I}

lemma isSMulRegular_iff_mul {r : R} : IsSMulRegular R r ↔ ∀ z : R, r * z = 0 → z = 0 :=
  ⟨fun h z hz ↦ h (show r • z = r • 0 by rw [smul_eq_mul, smul_eq_mul, hz, mul_zero]),
    fun h a b hab ↦ sub_eq_zero.mp (h _ (by rw [mul_sub, sub_eq_zero]; exact hab))⟩

/-- `p(x)` acting on the chart module is multiplication by `p(x)`. -/
lemma aeval_mulLeft (x : R) (p : A[X]) (m : R) :
    aeval (LinearMap.mulLeft A x) p m = aeval x p * m := by
  change aeval (Algebra.lmul A R x) p m = _
  rw [Polynomial.aeval_algHom_apply]
  rfl

/-- **`PolyRegular` gives `FibreRegular`** for a ring killed by `I`. -/
theorem PolyRegular.fibreRegular {x : R} (h : PolyRegular I x)
    (hkill : I • (⊤ : Submodule A R) = ⊥) : FibreFlat.FibreRegular I (LinearMap.mulLeft A x) :=
  FibreFlat.FibreRegular.of_killed hkill fun p hp m hm ↦
    isSMulRegular_iff_mul.mp (h p hp) m (by rw [← aeval_mulLeft]; exact hm)

/-- `PolyRegular` along an injective algebra map. -/
theorem PolyRegular.of_injective {S : Type u} [CommRing S] [Algebra A S] {x : R}
    (φ : R →ₐ[A] S) (hφ : Function.Injective φ) (h : PolyRegular I (φ x)) : PolyRegular I x :=
  fun p hp ↦ isSMulRegular_iff_mul.mpr fun z hz ↦ hφ <| by
    rw [map_zero]
    refine isSMulRegular_iff_mul.mp (h p hp) _ ?_
    rw [Polynomial.aeval_algHom_apply, ← map_mul, hz, map_zero]

/-- The reflection of a polynomial outside `I A[X]` is outside `I A[X]`. -/
lemma reflect_not_mem {p : A[X]} (hp : p ∉ I.map C) (N : ℕ) (hN : p.natDegree ≤ N) :
    reflect N p ∉ I.map C := by
  intro h
  refine hp (Ideal.mem_map_C_iff.mpr fun i ↦ ?_)
  by_cases hi : i ≤ N
  · have := Ideal.mem_map_C_iff.mp h (revAt N i)
    rwa [coeff_reflect, revAt_invol] at this
  · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact I.zero_mem

end PolyRegular

namespace TwoChartRegular

open ProjectiveLine

variable {A : Type u} [CommRing A] {I : Ideal A} (D : TwoChartRings A)

/-- **The overlap**: `PolyRegular` of `y` on `R1` gives `PolyRegular` of `T` on `R01 = R1[1/y]`. -/
theorem polyRegular_u (hI : I ≠ ⊤) (h1 : PolyRegular I D.y) :
    PolyRegular I (D.u : D.R01) := by
  intro p hp
  refine isSMulRegular_iff_mul.mpr fun z hz ↦ ?_
  obtain ⟨m, k, hm⟩ := D.exists1 z
  set N := p.natDegree
  have hp' := reflect_not_mem hp N le_rfl
  letI : Invertible (D.u : D.R01) := D.u.invertible
  have hrefl : aeval (↑D.u⁻¹ : D.R01) (reflect N p) * (D.u : D.R01) ^ N =
      aeval (D.u : D.R01) p := by
    rw [aeval_def, aeval_def, ← eval₂_reflect_mul_pow _ _ N p le_rfl]
    rfl
  have h0 : D.ρ1 (aeval D.y (reflect N p) * m) = 0 := by
    rw [map_mul, ← Polynomial.aeval_algHom_apply, D.ρ1_y, ← hm]
    have hinv : (↑D.u⁻¹ : D.R01) ^ N * (D.u : D.R01) ^ N = 1 := by
      rw [← mul_pow, Units.inv_mul, one_pow]
    calc aeval (↑D.u⁻¹ : D.R01) (reflect N p) * ((↑D.u⁻¹ : D.R01) ^ k * z)
        = (↑D.u⁻¹ : D.R01) ^ k * (↑D.u⁻¹ : D.R01) ^ N *
            (aeval (↑D.u⁻¹ : D.R01) (reflect N p) * (D.u : D.R01) ^ N * z) := by
          linear_combination (-(aeval (↑D.u⁻¹ : D.R01) (reflect N p) * (↑D.u⁻¹ : D.R01) ^ k * z))
            * hinv
      _ = 0 := by rw [hrefl, hz, mul_zero]
  obtain ⟨j, hj⟩ := D.ker1 _ h0
  have hy : IsSMulRegular D.R1 (D.y ^ j) := by
    have := h1 X (fun hX ↦ hI ?_)
    · rw [aeval_X] at this
      exact this.pow j
    · have := Ideal.mem_map_C_iff.mp hX 1
      rw [coeff_X_one] at this
      exact (Ideal.eq_top_iff_one I).mpr this
  have hm0 : m = 0 := isSMulRegular_iff_mul.mp (h1 _ hp') m (isSMulRegular_iff_mul.mp hy _ hj)
  rw [hm0, map_zero] at hm
  have hu : IsUnit ((↑D.u⁻¹ : D.R01) ^ k) := (Units.isUnit _).pow k
  exact (hu.mul_right_eq_zero).mp hm

end TwoChartRegular

namespace TwoChartGlue

variable {A : Type u} [CommRing A] {I : Ideal A}
  {B0 : Type u} [CommRing B0] [Algebra A B0]
  {Y1 : Type u} [CommRing Y1] [Algebra A Y1] (y : Y1)
  {Q : Type u} [CommRing Q] [Algebra A Q] [Algebra B0 Q] [IsScalarTower A B0 Q]
  (ι : Y1 →ₐ[A] Q) (hι : letI := (ι : Y1 →+* Q).toAlgebra; IsLocalization.Away y Q)
  (x0 : B0) (hxy : algebraMap B0 Q x0 * ι y = 1)
  {P0b P0ab : Type u} [CommRing P0b] [CommRing P0ab] [Algebra B0 P0b] [Algebra B0 P0ab]
  [Algebra A P0b] [Algebra A P0ab] [IsScalarTower A B0 P0b] [IsScalarTower A B0 P0ab]
  (ρ0a : Q →ₐ[B0] P0ab) (ρ0b : P0b →ₐ[B0] P0ab)
  (hb0 : letI := (ρ0b : P0b →+* P0ab).toAlgebra; IsLocalization.Away (algebraMap B0 P0b x0) P0ab)

omit [Algebra A P0ab] [IsScalarTower A B0 P0ab] in
/-- **The chart `U₀` of a Zariski glueing**: `PolyRegular` of `x` on `R0 = Q ×_{P0ab} P0b` from
`PolyRegular` of `y` on `R1 = Y1` and of `x₀` on the second piece `P0b`. -/
theorem polyRegular_x (hI : I ≠ ⊤) (h1 : PolyRegular I y)
    (hP : PolyRegular I (algebraMap B0 P0b x0)) :
    PolyRegular I (twoChart y ι hι x0 hxy ρ0a ρ0b hb0).x := by
  set D := twoChart y ι hι x0 hxy ρ0a ρ0b hb0 with hD
  have hu := TwoChartRegular.polyRegular_u D hI h1
  let s : D.R0 →ₐ[A] P0b := (ZariskiTwo.snd ρ0a ρ0b).restrictScalars A
  have hx : s D.x = algebraMap B0 P0b x0 := (ZariskiTwo.snd ρ0a ρ0b).commutes x0
  intro p hp
  refine isSMulRegular_iff_mul.mpr fun z hz ↦ ?_
  have hfst : D.ρ0 z = 0 := by
    refine isSMulRegular_iff_mul.mp (hu p hp) _ ?_
    rw [← D.ρ0_x, Polynomial.aeval_algHom_apply, ← map_mul, hz, map_zero]
  have hsnd : s z = 0 := by
    refine isSMulRegular_iff_mul.mp (hP p hp) _ ?_
    rw [← hx, Polynomial.aeval_algHom_apply, ← map_mul, hz, map_zero]
  exact Subtype.ext (Prod.ext hfst hsnd)

end TwoChartGlue

end SemistableReduction
