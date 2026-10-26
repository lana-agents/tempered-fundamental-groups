/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeRegular
import TemperedFundamentalGroups.SemistableReduction.TateGenericFibre

/-!
# Regularity of the Tate chart `T1` where `w` is a unit (MR12 S5.2)

Let `O` be a DVR with uniformizer `ϖ` and residue field `k` (`θ : O → k` onto, `ker θ = (ϖ)`),
and `T1 = O[h'][w]/(G₁)` the chart `u ≠ 0` of the Tate model (`TateTwoChart.T1`), with node
coordinate `s = h' + t w` and chart equation `w (s² + s − b₆ w²) = π (1 + b₄ w²)`
(`TateTwoChart.eqn1`), `π = ε ϖᵐ`, `m ≥ 1`.

* **`TateTwoChart.isDomain_T1`**: `T1` is a domain (for `3 ≠ 0`, `π ≠ 0`, `E ≠ 0`): `T1` is free
  over `O[X]`, so `ϖ` is a non-zero-divisor of `T1` (`TateTwoChart.algebraMap_ϖ_mem_T1`) and
  `T1` embeds into the Dedekind domain `T1[1/ϖ]` (`TateTwoChart.isDedekindDomain_away_T1_of_dvr`).
* **`TateTwoChart.exists_regular_pair_T1`**: at a closed point `P` of the special fibre with
  `w ∉ P`, `ϖ` is prime in `T1_P` and `𝔪_P = (ϖ, y)` with `y ∉ (ϖ)`, in every residue
  characteristic.

Method (as in `TateTwoChartNode.exists_regular_pair`, via
`TateNodeRegular.exists_regular_pair_of_chartData`): modulo `ϖ` the chart equation becomes
`w (s² + s − b₆ w²) = 0`, so `s² + s = b₆ w²` at `P`. For the root `s₀ ∈ {0, −1}` of `S² + S` with
`s − s₀ ∉ P`, `τ = 1 + 2 s₀` and `X = (s − s₀)/w`, the special fibre is the localization
`k[X][1/h]`, `h = X (b₆ − X²)³`, with `w ↦ τ X/(b₆ − X²)`, `s ↦ s₀ + τ X²/(b₆ − X²)` (the
identities of the `u`-branch of the node chart with `b₄ = 0`, since `T1` does not invert
`1 + b₄ w²`).
-/

universe u

open Polynomial IsLocalRing

namespace SemistableReduction

namespace TateTwoChart

/-! ### `T1` is a domain -/

section Domain

variable {O : Type u} [CommRing O] {π b₄ t κ : O}

private lemma natDegree_G1' [Nontrivial O] : (G1 π b₄ t κ).natDegree = 3 := by
  unfold G1
  compute_degree!

lemma algebraMap_ϖ_mem_T1 [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0) :
    algebraMap O (T1 π b₄ t κ) ϖ ∈ nonZeroDivisors (T1 π b₄ t κ) := by
  have hreg : IsSMulRegular (T1 π b₄ t κ) (C ϖ : O[X]) :=
    (IsRegular.of_ne_zero (C_ne_zero.2 hϖ)).isSMulRegular
  have he : ∀ x : T1 π b₄ t κ, algebraMap O (T1 π b₄ t κ) ϖ * x = (C ϖ : O[X]) • x := fun x ↦ by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply O O[X] (T1 π b₄ t κ),
      Polynomial.algebraMap_apply]
    rfl
  refine mem_nonZeroDivisors_iff.2 ⟨fun x hx ↦ hreg ?_, fun x hx ↦ hreg ?_⟩
  · dsimp only
    rw [← he, hx, smul_zero]
  · dsimp only
    rw [← he, mul_comm, hx, smul_zero]

lemma algebraMap_ϖ_T1_ne_zero [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0) :
    algebraMap O (T1 π b₄ t κ) ϖ ≠ 0 := by
  haveI : Nontrivial (T1 π b₄ t κ) := (AdjoinRoot.of.injective_of_degree_ne_zero (f :=
    G1 π b₄ t κ) (by
    rw [degree_eq_natDegree (Monic.ne_zero (monic_G1 π b₄ t κ)), natDegree_G1']; decide)).nontrivial
  exact nonZeroDivisors.ne_zero (algebraMap_ϖ_mem_T1 hϖ)

/-- **The chart ring `T1` is a domain** over a discrete valuation ring `O`, for
`κ (t² − b₆) = 1`, `3 ≠ 0`, `π ≠ 0` and `E = tateE π b₄ b₆ ≠ 0`: it embeds into its generic
fibre `T1[1/ϖ]`, a Dedekind domain. -/
theorem isDomain_T1 [IsDomain O] [IsDiscreteValuationRing O] {b₆ ϖ : O} (hϖ : Irreducible ϖ)
    (hκ : κ * (t ^ 2 - b₆) = 1) (h3 : (3 : O) ≠ 0) (hπ0 : π ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0) : IsDomain (T1 π b₄ t κ) := by
  haveI := isDedekindDomain_away_T1_of_dvr (t := t) (κ := κ) hϖ.ne_zero hϖ.not_isUnit hκ h3 hπ0 hE
  have hinj : Function.Injective (algebraMap (T1 π b₄ t κ)
      (Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ))) :=
    IsLocalization.injective _ (Submonoid.powers_le.2 (algebraMap_ϖ_mem_T1 hϖ.ne_zero))
  exact hinj.isDomain _

end Domain

namespace TateT1Regular

open TateNodeRegular TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} {B : Type u} [CommRing B]

local notation "ιT" => algebraMap O (T1 π b₄ t κ)

/-- Ring maps out of `T1` agreeing on `O`, `h'` and `w` are equal. -/
lemma ringHom_ext_T1 {f g : T1 π b₄ t κ →+* B} (hO : ∀ o, f (ιT o) = g (ιT o))
    (hh : f (h1 π b₄ t κ) = g (h1 π b₄ t κ)) (hw : f (w1 π b₄ t κ) = g (w1 π b₄ t κ)) :
    f = g := by
  letI : Algebra O B := (g.comp (algebraMap O (T1 π b₄ t κ))).toAlgebra
  let f' : T1 π b₄ t κ →ₐ[O] B := { f with commutes' := hO }
  let g' : T1 π b₄ t κ →ₐ[O] B := { g with commutes' := fun _ ↦ rfl }
  have : f' = g' := AdjoinRoot.algHom_ext' (Polynomial.algHom_ext hh) hw
  exact RingHom.ext fun r ↦ AlgHom.congr_fun this r

variable {φ : T1 π b₄ t κ →+* B}

private lemma map_eqn1 (hκ : κ * (t ^ 2 - b₆) = 1) :
    φ (w1 π b₄ t κ) * (φ (s1 π b₄ t κ) ^ 2 + φ (s1 π b₄ t κ) - φ (ιT b₆) * φ (w1 π b₄ t κ) ^ 2) =
      φ (ιT π) * (1 + φ (ιT b₄) * φ (w1 π b₄ t κ) ^ 2) := by
  have h := congrArg φ (eqn1 π b₄ t κ hκ)
  simpa only [map_add, map_sub, map_mul, map_pow, map_one] using h

/-- **Chart data at a point of `T1` where `w` is a unit** (`s − s₀` a unit, `s₀² + s₀ = 0`):
the special fibre is `k[X]` localized at `h = X (b₆ − X²)³` (`w ↦ τ X/(b₆ − X²)`,
`s ↦ s₀ + τ X²/(b₆ − X²)`, `τ = 1 + 2 s₀`). -/
lemma chartData_T1 (hκ : κ * (t ^ 2 - b₆) = 1) {c : k →+* B} (hc : ∀ o, c (θ o) = φ (ιT o))
    (hθ : Function.Surjective θ) (hθϖ : θ ϖ = 0) (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m)
    (hϖ0 : φ (ιT ϖ) = 0) {P : Ideal (T1 π b₄ t κ)} {s₀ : O} (hs₀ : s₀ ^ 2 + s₀ = 0)
    (hwP : w1 π b₄ t κ ∉ P) (hu : IsUnit (φ (w1 π b₄ t κ)))
    (hS : IsUnit (φ (s1 π b₄ t κ - ιT s₀))) : ChartData φ (ιT ϖ) P c := by
  rw [map_sub] at hS
  have hπ0 : φ (ιT π) = 0 := by
    rw [congrArg (algebraMap O (T1 π b₄ t κ)) hπ, map_mul, map_pow, map_mul, map_pow, hϖ0,
      zero_pow (by omega), mul_zero]
  have hR : φ (s1 π b₄ t κ) ^ 2 + φ (s1 π b₄ t κ) = φ (ιT b₆) * φ (w1 π b₄ t κ) ^ 2 := by
    have h := map_eqn1 (φ := φ) hκ
    rw [hπ0, zero_mul] at h
    have hui : ↑hu.unit⁻¹ * φ (w1 π b₄ t κ) = 1 := hu.val_inv_mul
    linear_combination ↑hu.unit⁻¹ * h - (φ (s1 π b₄ t κ) ^ 2 + φ (s1 π b₄ t κ) -
      φ (ιT b₆) * φ (w1 π b₄ t κ) ^ 2) * hui
  have hs₀B : φ (ιT s₀) ^ 2 + φ (ιT s₀) = 0 := by
    rw [← map_pow, ← map_pow, ← map_add, ← map_add, hs₀, map_zero, map_zero]
  obtain ⟨z, hzdef⟩ : ∃ z, z = (φ (s1 π b₄ t κ) - φ (ιT s₀)) * ↑hu.unit⁻¹ := ⟨_, rfl⟩
  have hzu : z * φ (w1 π b₄ t κ) = φ (s1 π b₄ t κ) - φ (ιT s₀) := by
    rw [hzdef, mul_assoc, hu.val_inv_mul, mul_one]
  obtain ⟨h, hh⟩ : ∃ h : k[X], h = X * (C (θ b₆) - X ^ 2) ^ 3 := ⟨_, rfl⟩
  have hβh : IsUnit (eval₂RingHom c z h) := by
    have := isUnit_U (b₄ := 0) (b₆ := φ (ιT b₆)) hs₀B hu hS (by simp) hzu hR
    rw [hh]
    simp only [coe_eval₂RingHom, eval₂_mul, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hc]
    convert this using 1
    ring
  letI : Algebra O (Localization.Away h) :=
    ((algebraMap k[X] (Localization.Away h)).comp (C.comp θ)).toAlgebra
  have halg : ∀ o, algebraMap O (Localization.Away h) o = algebraMap k[X] _ (C (θ o)) :=
    fun _ ↦ rfl
  obtain ⟨Xt, hXt⟩ : ∃ Xt, Xt = algebraMap k[X] (Localization.Away h) X := ⟨_, rfl⟩
  obtain ⟨Hi, hHi⟩ : ∃ Hi, Hi = IsLocalization.Away.invSelf (S := Localization.Away h) h :=
    ⟨_, rfl⟩
  have hH : Xt * (algebraMap O _ b₆ - Xt ^ 2) *
      ((algebraMap O _ b₆ - Xt ^ 2) ^ 2 + 0 * Xt ^ 2) * Hi = 1 := by
    have := IsLocalization.Away.mul_invSelf (S := Localization.Away h) h
    have hmap := congrArg (algebraMap k[X] (Localization.Away h)) hh
    simp only [map_mul, map_sub, map_pow, ← halg, ← hXt] at hmap
    rw [← hHi, hmap] at this
    linear_combination this
  have hs₀T : algebraMap O (Localization.Away h) s₀ ^ 2 + algebraMap O _ s₀ = 0 := by
    rw [← map_pow, ← map_add, hs₀, map_zero]
  obtain ⟨w, hw⟩ : ∃ w, w = wU 0 (algebraMap O (Localization.Away h) b₆)
      (algebraMap O (Localization.Away h) s₀) Xt Hi := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = sU 0 (algebraMap O (Localization.Away h) b₆)
      (algebraMap O (Localization.Away h) s₀) Xt Hi := ⟨_, rfl⟩
  have hq : s ^ 2 + s - algebraMap O _ b₆ * w ^ 2 = 0 := by
    rw [hw, hs]; exact sU_sq hs₀T hH
  have hπT : algebraMap O (Localization.Away h) π = 0 := by
    rw [congrArg (algebraMap O (Localization.Away h)) hπ, halg, map_mul, map_pow, hθϖ,
      zero_pow (by omega), mul_zero, map_zero, map_zero]
  have hch : ChartEq π b₄ b₆ s w := by
    unfold ChartEq; rw [hq, hπT, mul_zero, zero_mul]
  obtain ⟨Ψ, hΨ⟩ : ∃ Ψ, Ψ = IsLocalization.Away.lift (S := Localization.Away h) h hβh :=
    ⟨_, rfl⟩
  have hΨO : ∀ o, Ψ (algebraMap O _ o) = φ (ιT o) := fun o ↦ by
    rw [hΨ, halg, IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_C, hc]
  have hΨX : Ψ Xt = z := by
    rw [hΨ, hXt, IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_X]
  have hhi : z * (φ (ιT b₆) - z ^ 2) * ((φ (ιT b₆) - z ^ 2) ^ 2 + 0 * z ^ 2) * Ψ Hi = 1 := by
    have := congrArg Ψ hH
    simpa only [map_mul, map_sub, map_add, map_pow, map_one, map_zero, hΨO, hΨX] using this
  have hΨw : Ψ w = φ (w1 π b₄ t κ) := by
    rw [show Ψ w = wU 0 (φ (ιT b₆)) (φ (ιT s₀)) z (Ψ Hi) by
      simp only [hw, wU, eiU, map_mul, map_add, map_sub, map_pow, map_one, map_zero, map_ofNat,
        hΨO, hΨX]]
    exact wU_eq hs₀B hu hzu hR hhi
  have hΨs : Ψ s = φ (s1 π b₄ t κ) := by
    rw [show Ψ s = sU 0 (φ (ιT b₆)) (φ (ιT s₀)) z (Ψ Hi) by
      simp only [hs, sU, eiU, map_mul, map_add, map_sub, map_pow, map_one, map_zero, map_ofNat,
        hΨO, hΨX]]
    exact sU_eq hs₀B hu hzu hR hhi
  set γ := liftT1 hκ s w hch
  have hγO : ∀ o, γ (ιT o) = algebraMap k[X] _ (C (θ o)) := fun o ↦ by
    rw [AlgHom.commutes, halg]
  subst hΨ
  refine ⟨z, h, hβh, γ.toRingHom, ιT s₀, s1 π b₄ t κ, w1 π b₄ t κ, ?_, ?_, fun a ↦ ?_, hwP,
    hzu, ?_⟩
  · change γ (ιT ϖ) = 0
    rw [hγO, hθϖ, map_zero, map_zero]
  · have : (IsLocalization.Away.lift (S := Localization.Away h) h hβh).comp γ.toRingHom = φ := by
      refine ringHom_ext_T1 (fun o ↦ ?_) ?_ ?_
      · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hγO,
          IsLocalization.Away.lift_eq, coe_eval₂RingHom, eval₂_C, hc]
      · have e : φ (h1 π b₄ t κ) = φ (s1 π b₄ t κ) - φ (ιT t) * φ (w1 π b₄ t κ) := by
          simp only [map_add, map_mul]; ring
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, γ, liftT1_h1,
          map_sub, map_mul, hΨO, hΨs, hΨw, e]
      · simpa [γ, liftT1_w1] using hΨw
    exact fun r ↦ RingHom.congr_fun this r
  · obtain ⟨o, rfl⟩ := hθ a
    exact ⟨ιT o, hc o, hγO o⟩
  · change γ (s1 π b₄ t κ) - γ (ιT s₀) = algebraMap k[X] _ X * γ (w1 π b₄ t κ)
    rw [liftT1_s1, AlgHom.commutes, liftT1_w1, hs, hw, sU, wU, hXt]
    ring

end

end TateT1Regular

open TateNodeRegular TateTwoChartNode TateT1Regular

/-- **The Tate chart `T1` is regular at the closed points of the special fibre where `w` is a
unit** (MR12 S5.2): if `P` is a maximal ideal of `T1` containing `ϖ` but not `w`, then `ϖ` is
prime in `T1_P` and `𝔪_P = (ϖ, y)` with `y ∉ (ϖ)`. Valid in every residue characteristic. -/
theorem exists_regular_pair_T1 {O : Type u} [CommRing O] [IsDomain O] {k : Type u} [Field k]
    {θ : O →+* k} {π b₄ b₆ t κ ϖ ε : O} {m : ℕ} (hϖ : Irreducible ϖ)
    (hθ : Function.Surjective θ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hπ : π = ε * ϖ ^ m) (hm : 1 ≤ m) (hκ : κ * (t ^ 2 - b₆) = 1) [IsDomain (T1 π b₄ t κ)]
    (P : Ideal (T1 π b₄ t κ)) [hP : P.IsMaximal] (hϖP : algebraMap O _ ϖ ∈ P)
    (hwP : w1 π b₄ t κ ∉ P) :
    ∃ y : Localization.AtPrime P, Prime (algebraMap O (Localization.AtPrime P) ϖ) ∧
      y ∉ Ideal.span {algebraMap O (Localization.AtPrime P) ϖ} ∧
      IsLocalRing.maximalIdeal (Localization.AtPrime P) =
        Ideal.span {algebraMap O (Localization.AtPrime P) ϖ, y} := by
  have hθϖ : θ ϖ = 0 := by
    rw [← RingHom.mem_ker, hker]; exact Ideal.mem_span_singleton_self ϖ
  set φ : T1 π b₄ t κ →+* Localization.AtPrime P ⧸
      Ideal.span {algebraMap (T1 π b₄ t κ) (Localization.AtPrime P) (algebraMap O _ ϖ)} :=
    (Ideal.Quotient.mk _).comp (algebraMap (T1 π b₄ t κ) (Localization.AtPrime P))
  have hϖ0 : φ (algebraMap O _ ϖ) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
  have hunit : ∀ r ∉ P, IsUnit (φ r) := fun r hr ↦
    (IsLocalization.map_units (Localization.AtPrime P) (⟨r, hr⟩ : P.primeCompl)).map
      (Ideal.Quotient.mk _)
  have hc : ∀ o, residueFieldLift θ (φ.comp (algebraMap O (T1 π b₄ t κ))) hϖ0 hθ hker (θ o) =
      φ (algebraMap O _ o) := residueFieldLift_θ _ _ _ _
  have hcd : ChartData φ (algebraMap O _ ϖ) P
      (residueFieldLift θ (φ.comp (algebraMap O (T1 π b₄ t κ))) hϖ0 hθ hker) := by
    by_cases hS : s1 π b₄ t κ ∈ P
    · refine chartData_T1 hκ hc hθ hθϖ hπ hm hϖ0 (s₀ := -1) (by ring) hwP (hunit _ hwP)
        (hunit _ fun h1 ↦ hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_))
      have := P.sub_mem h1 hS
      rwa [map_neg, map_one, sub_neg_eq_add, add_sub_cancel_left] at this
    · exact chartData_T1 hκ hc hθ hθϖ hπ hm hϖ0 (s₀ := 0) (by ring) hwP (hunit _ hwP)
        (hunit _ (by rwa [map_zero, sub_zero]))
  have := exists_regular_pair_of_chartData (algebraMap_ϖ_T1_ne_zero hϖ.ne_zero) hϖP _ hcd
  rwa [IsScalarTower.algebraMap_apply O (T1 π b₄ t κ) (Localization.AtPrime P)]

end TateTwoChart

end SemistableReduction
