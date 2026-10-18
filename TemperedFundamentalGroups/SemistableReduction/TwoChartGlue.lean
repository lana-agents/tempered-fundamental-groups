/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraOfRings
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwo

/-!
# Two-chart rings from a Zariski glueing over the chart `U₀` (Blueprint §12.8, M2.3 (f))

A covering `𝒴` of a model `𝒳` finite over `ℙ¹_A` is described by its sections over the preimages
of the two charts and of their overlap (`ProjectiveLine.TwoChartRings`). When the sections `Y1`
over the chart `U₁` are known, the sections over `U₀` are obtained by glueing (`ZariskiTwo`): the
preimage of `U₀` in `𝒳` is covered by `D(x₀)` (contained in the preimage of `U₁`, where the
sections are `Q = Y1[1/y]`) and by a second basic open `D(b₀)`. This file:

* **`TwoChartGlue.twoChart`**: from `Y1` (with the coordinate `y`), its localization
  `ι : Y1 → Q` away from `y`, a `B0`-algebra structure on `Q` with `x₀ · y = 1` in `Q`, and a
  second piece `P0b` over `D(b₀)` with overlap `P0ab = P0b[1/x₀]`, the two-chart rings
  `R0 = Q ×_{P0ab} P0b` (`ZariskiTwo.glued`), `R1 = Y1`, `R01 = Q`;
* `TwoChartGlue.finite_aeval_mulLeft`: a ring finite over `A[X]` (`X ↦ x`) gives a finite chart
  module (the finiteness hypothesis of `TwoChartTower.system`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TwoChartGlue

noncomputable section

variable {A : Type u} [CommRing A]

/-- **Finiteness of a chart module**: if `R` is finite over `A[X]` via `X ↦ x`, the module
`R` with `X` acting by multiplication with `x` is finite over `A[X]`. -/
lemma finite_aeval_mulLeft {R : Type u} [CommRing R] [Algebra A R] (x : R)
    (h : letI := (Polynomial.aeval x : A[X] →ₐ[A] R).toRingHom.toAlgebra; Module.Finite A[X] R) :
    Module.Finite A[X] (Module.AEval' (LinearMap.mulLeft A x)) := by
  letI := (Polynomial.aeval x : A[X] →ₐ[A] R).toRingHom.toAlgebra
  let e : R ≃ₗ[A[X]] Module.AEval' (LinearMap.mulLeft A x) :=
    { Module.AEval'.of (LinearMap.mulLeft A x) with
      map_smul' := fun p m ↦ by
        change Module.AEval'.of (LinearMap.mulLeft A x) (Polynomial.aeval x p * m) = _
        change _ = Module.AEval'.of (LinearMap.mulLeft A x)
          ((Polynomial.aeval (Algebra.lmul A R x) p) m)
        rw [Polynomial.aeval_algHom_apply]
        rfl }
  exact Module.Finite.equiv e

variable {B0 : Type u} [CommRing B0] [Algebra A B0]
  {Y1 : Type u} [CommRing Y1] [Algebra A Y1] (y : Y1)
  {Q : Type u} [CommRing Q] [Algebra A Q] [Algebra B0 Q] [IsScalarTower A B0 Q]
  (ι : Y1 →ₐ[A] Q) (hι : letI := (ι : Y1 →+* Q).toAlgebra; IsLocalization.Away y Q)
  (x0 : B0) (hxy : algebraMap B0 Q x0 * ι y = 1)
  {P0b P0ab : Type u} [CommRing P0b] [CommRing P0ab] [Algebra B0 P0b] [Algebra B0 P0ab]
  [Algebra A P0b] [Algebra A P0ab] [IsScalarTower A B0 P0b] [IsScalarTower A B0 P0ab]
  (ρ0a : Q →ₐ[B0] P0ab) (ρ0b : P0b →ₐ[B0] P0ab)
  (hb0 : letI := (ρ0b : P0b →+* P0ab).toAlgebra; IsLocalization.Away (algebraMap B0 P0b x0) P0ab)

/-- The sections over `U₀`: the glued algebra `Q ×_{P0ab} P0b`. -/
abbrev R0 : Type u := ZariskiTwo.glued ρ0a ρ0b

/-- The unit `T` of the overlap: the image of `x₀`, with inverse `y`. -/
def uT : Qˣ where
  val := algebraMap B0 Q x0
  inv := ι y
  val_inv := hxy
  inv_val := by rw [mul_comm]; exact hxy

omit [Algebra A B0] [IsScalarTower A B0 Q] [Algebra A P0b] [Algebra A P0ab]
  [IsScalarTower A B0 P0b] [IsScalarTower A B0 P0ab] in
include hxy hb0 in
lemma isLocalization_fst :
    letI := ZariskiTwo.algebraFst (ρa := ρ0a) (ρb := ρ0b)
    IsLocalization.Away (algebraMap B0 (R0 ρ0a ρ0b) x0) Q :=
  ZariskiTwo.isLocalization_fst x0 (IsUnit.of_mul_eq_one _ hxy) hb0

/-- **The two-chart rings of the glued covering**: `R0 = Q ×_{P0ab} P0b`, `R1 = Y1`, `R01 = Q`,
`x = x₀`, `y = y`. -/
def twoChart : ProjectiveLine.TwoChartRings A where
  R0 := R0 ρ0a ρ0b
  R1 := Y1
  R01 := Q
  x := algebraMap B0 (R0 ρ0a ρ0b) x0
  y := y
  u := uT y ι x0 hxy
  ρ0 := (ZariskiTwo.fst ρ0a ρ0b).restrictScalars A
  ρ1 := ι
  ρ0_x := (ZariskiTwo.fst ρ0a ρ0b).commutes x0
  ρ1_y := rfl
  exists0 z := by
    letI := ZariskiTwo.algebraFst (ρa := ρ0a) (ρb := ρ0b)
    have := isLocalization_fst (y := y) (ι := ι) (x0 := x0) (hxy := hxy) (ρ0a := ρ0a)
      (ρ0b := ρ0b) hb0
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ :=
      IsLocalization.surj (Submonoid.powers (algebraMap B0 (R0 ρ0a ρ0b) x0)) z
    refine ⟨m, k, ?_⟩
    change z * ZariskiTwo.fst ρ0a ρ0b (algebraMap B0 (R0 ρ0a ρ0b) x0 ^ k) =
      ZariskiTwo.fst ρ0a ρ0b m at hm
    rw [map_pow, AlgHom.commutes, mul_comm] at hm
    exact hm
  ker0 m hm := by
    letI := ZariskiTwo.algebraFst (ρa := ρ0a) (ρb := ρ0b)
    have := isLocalization_fst (y := y) (ι := ι) (x0 := x0) (hxy := hxy) (ρ0a := ρ0a)
      (ρ0b := ρ0b) hb0
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (algebraMap B0 (R0 ρ0a ρ0b) x0)) Q m).1 hm
    exact ⟨k, hk⟩
  exists1 z := by
    letI := (ι : Y1 →+* Q).toAlgebra
    haveI := hι
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers y) z
    refine ⟨m, k, ?_⟩
    change z * ι (y ^ k) = ι m at hm
    rw [map_pow, mul_comm] at hm
    exact hm
  ker1 m hm := by
    letI := (ι : Y1 →+* Q).toAlgebra
    haveI := hι
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers y) Q m).1 hm
    exact ⟨k, hk⟩

end

end TwoChartGlue

end SemistableReduction
