/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateLineComponent
import TemperedFundamentalGroups.SemistableReduction.TateT1Regular

/-!
# Regularity of `T1` along the line `ℓ` away from the nodes

MR13 step 7, D1 (S3, the regularity input of purity). At a closed point `P` of the special fibre of
`T1` with `w ∈ P` (a point of the line `ℓ = {w = 0}`) and `h'(h' + 1) ∉ P` (not a node), the chart
equation `w (s² + s − b₆ w²) = π (1 + b₄ w²)` (`eqn1`) with `s² + s − b₆ w²` a unit at `P` gives
`w ∈ (ϖ)` in `T1_P`, so the special fibre is `k[h']` near `P`: chart data
(`TateNodeRegular.ChartData`) `γ : T1 → k[X][1/(X(X+1))]`, `h' ↦ X`, `w ↦ 0` (the map `lineHom`).

* **`TateTwoChart.exists_regular_pair_T1_line`**: `ϖ` is prime in `T1_P` and `𝔪_P = (ϖ, y)` with
  `y ∉ (ϖ)` (`TateNodeRegular.exists_regular_pair_of_chartData`).
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace TateTwoChart

open TateNodeRegular TateT1Regular TateTwoChartNode

lemma ring_aux {T : Type*} [CommRing T] (h w t b : T) :
    h * (h + 1) = ((h + t * w) ^ 2 + (h + t * w) - b * w ^ 2) -
      w * (2 * t * h + t ^ 2 * w + t - b * w) := by ring

/-- `s² + s − b₆ w² − (h'² + h')` is a multiple of `w`. -/
lemma s1_sq_sub_mem {O : Type u} [CommRing O] {π b₄ t κ : O} (b₆ : O) (P : Ideal (T1 π b₄ t κ))
    (hwP : w1 π b₄ t κ ∈ P)
    (h : s1 π b₄ t κ ^ 2 + s1 π b₄ t κ - algebraMap O _ b₆ * w1 π b₄ t κ ^ 2 ∈ P) :
    h1 π b₄ t κ * (h1 π b₄ t κ + 1) ∈ P := by
  have e : h1 π b₄ t κ * (h1 π b₄ t κ + 1) =
      (s1 π b₄ t κ ^ 2 + s1 π b₄ t κ - algebraMap O _ b₆ * w1 π b₄ t κ ^ 2) -
        w1 π b₄ t κ * (2 * algebraMap O _ t * h1 π b₄ t κ + algebraMap O _ t ^ 2 * w1 π b₄ t κ +
          algebraMap O _ t - algebraMap O _ b₆ * w1 π b₄ t κ) :=
    ring_aux _ _ _ _
  rw [e]
  exact P.sub_mem h (P.mul_mem_right _ hwP)

/-- **`T1` is regular at the closed points of `ℓ` away from the nodes**: if `P` is a maximal
ideal of `T1` containing `ϖ` and `w` but not `h'(h' + 1)`, then `ϖ` is prime in `T1_P` and
`𝔪_P = (ϖ, y)` with `y ∉ (ϖ)`. -/
theorem exists_regular_pair_T1_line {O : Type u} [CommRing O] [IsDomain O] {k : Type u} [Field k]
    {θ : O →+* k} {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} (hϖ : Irreducible ϖ)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hκ : κ * (t ^ 2 - b₆) = 1) [IsDomain (T1 π b₄ t κ)]
    (P : Ideal (T1 π b₄ t κ)) [hP : P.IsMaximal] (hϖP : algebraMap O _ ϖ ∈ P)
    (hwP : w1 π b₄ t κ ∈ P) (hhP : h1 π b₄ t κ * (h1 π b₄ t κ + 1) ∉ P) :
    ∃ y : Localization.AtPrime P, Prime (algebraMap O (Localization.AtPrime P) ϖ) ∧
      y ∉ Ideal.span {algebraMap O (Localization.AtPrime P) ϖ} ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap O (Localization.AtPrime P) ϖ, y} := by
  have hθϖ : θ ϖ = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ
  have hθπ : θ π = 0 := by
    rw [hπ, map_mul, map_pow, hθϖ, zero_pow (by omega), mul_zero]
  set φ : T1 π b₄ t κ →+* Localization.AtPrime P ⧸
      Ideal.span {algebraMap (T1 π b₄ t κ) (Localization.AtPrime P) (algebraMap O _ ϖ)} :=
    (Ideal.Quotient.mk _).comp (algebraMap (T1 π b₄ t κ) (Localization.AtPrime P))
  have hϖ0 : φ (algebraMap O _ ϖ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hunit : ∀ r ∉ P, IsUnit (φ r) := fun r hr ↦
    (IsLocalization.map_units (Localization.AtPrime P) (⟨r, hr⟩ : P.primeCompl)).map
      (Ideal.Quotient.mk _)
  have hπ0 : φ (algebraMap O _ π) = 0 := by
    rw [congrArg (algebraMap O (T1 π b₄ t κ)) hπ, map_mul, map_pow, map_mul, map_pow, hϖ0,
      zero_pow (by omega), mul_zero]
  -- `w ↦ 0` in `T1_P / (ϖ)`
  have hw0 : φ (w1 π b₄ t κ) = 0 := by
    have hu := hunit _ fun h ↦ hhP (s1_sq_sub_mem b₆ P hwP h)
    have h := congrArg φ (eqn1 π b₄ t κ hκ)
    rw [map_mul, map_mul, hπ0, zero_mul] at h
    exact (hu.mul_left_eq_zero).1 h
  set c := residueFieldLift θ (φ.comp (algebraMap O (T1 π b₄ t κ))) hϖ0 hθ hker
  have hc : ∀ o, c (θ o) = φ (algebraMap O _ o) := residueFieldLift_θ _ _ _ _
  obtain ⟨h, hh⟩ : ∃ h : k[X], h = X * (X + 1) := ⟨_, rfl⟩
  have hβh : IsUnit (eval₂RingHom c (φ (h1 π b₄ t κ)) h) := by
    have := hunit _ hhP
    rw [hh]
    simpa only [coe_eval₂RingHom, eval₂_mul, eval₂_add, eval₂_X, eval₂_one, map_mul, map_add,
      map_one] using this
  set γ : T1 π b₄ t κ →+* Localization.Away h :=
    (algebraMap k[X] (Localization.Away h)).comp (lineHom θ π b₄ t κ hθπ)
  have hγO : ∀ o, γ (algebraMap O _ o) = algebraMap k[X] _ (C (θ o)) := fun o ↦ by
    simp only [γ, RingHom.comp_apply, lineHom_algebraMap]
  have hγh : γ (h1 π b₄ t κ) = algebraMap k[X] _ X := by
    simp only [γ, RingHom.comp_apply, h1, lineHom_of, Polynomial.map_X]
  have hγw : γ (w1 π b₄ t κ) = 0 := by
    simp only [γ, RingHom.comp_apply, w1, lineHom_root, map_zero]
  have hcd : ChartData φ (algebraMap O _ ϖ) P c := by
    refine ⟨φ (h1 π b₄ t κ), h, hβh, γ, 0, h1 π b₄ t κ, 1, ?_, fun r ↦ ?_, fun a ↦ ?_,
      fun h ↦ hP.ne_top ((Ideal.eq_top_iff_one _).2 h), by rw [map_one, mul_one, map_zero,
        sub_zero], by rw [map_one, mul_one, map_zero, sub_zero, hγh]⟩
    · rw [hγO, hθϖ, map_zero, map_zero]
    · have : (IsLocalization.Away.lift (S := Localization.Away h) h hβh).comp γ = φ := by
        refine ringHom_ext_T1 (fun o ↦ ?_) ?_ ?_
        · simp only [RingHom.comp_apply, hγO, IsLocalization.Away.lift_eq, coe_eval₂RingHom,
            eval₂_C, hc]
        · simp only [RingHom.comp_apply, hγh, IsLocalization.Away.lift_eq, coe_eval₂RingHom,
            eval₂_X]
        · simp only [RingHom.comp_apply, hγw, map_zero, hw0]
      exact RingHom.congr_fun this r
    · obtain ⟨o, rfl⟩ := hθ a
      exact ⟨algebraMap O _ o, hc o, hγO o⟩
  have := exists_regular_pair_of_chartData (algebraMap_ϖ_T1_ne_zero hϖ.ne_zero) hϖP _ hcd
  rwa [IsScalarTower.algebraMap_apply O (T1 π b₄ t κ) (Localization.AtPrime P)]

end TateTwoChart

end SemistableReduction
