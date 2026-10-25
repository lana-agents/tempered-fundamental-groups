/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateTwoChart
import TemperedFundamentalGroups.Andre.TateNormalAlgebra

/-!
# The once-punctured Tate curve `E ∖ {0}` and the charts of the Tate model (T1a)

The Tate cubic `F = v² w + u v w − π u³ − π b₄ u w² − b₆ w³` has its origin at `[0 : 1 : 0]`;
the complement `E ∖ {0} = {w ≠ 0}` is the affine curve with coordinate ring
`A = O[x][y]/(y² + x y − (π x³ + π b₄ x + b₆))` (`TateNormal.TateRing`, `x = u/w`, `y = v/w`).
With `ℓ₀ = v − t w` (`κ (t² − b₆) = 1`) the two charts of the Tate model over `ℙ¹`
(`TateTwoChart.T0`, `T1`) restrict to `E ∖ {0}` as follows, on the generic fibre (`ϖ` inverted,
`π ∣ ϖᵐ`):

* **`TateAffine.span_a_x`**: `y − t` and `x` generate the unit ideal of `A` (`x = y − t = 0`
  would give `t² = b₆`), so `E ∖ {0} = D(y − t) ∪ D(x)`;
* **`TateAffine.isLocalization_T1K`**: `T1[1/ϖ]` is `A[1/ϖ][1/x]`, via `x ↦ 1/w`, `y ↦ s/w`
  (`w = w/u` is a unit on the generic fibre of the chart `u ≠ 0`, which misses the origin);
* **`TateAffine.isLocalization_T0K`**: `T0[1/(ϖ z)]` is `A[1/ϖ][1/(y − t)]`, via
  `x ↦ h/z`, `y ↦ t + 1/z` (`z = w/ℓ₀` vanishes on the generic fibre of the chart `ℓ₀ ≠ 0`
  exactly at the origin);
* **`TateAffine.r0K_comp`**: the two identifications agree on the overlap `T01[1/ϖ]`
  (`TateAffine.r0K`, `TateAffine.r1K` are induced by `TateTwoChart.rho0` and `T1 → T01`).

This is the base of the glueing of the generic fibres of a Tate covering
(`TateAffineGlue`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateAffine

open TateTwoChart TemperedFundamentalGroups.TateNormal

noncomputable section

variable {O : Type u} [CommRing O] (π b₄ b₆ t κ ϖ : O)

/-- The coordinate ring `O[x][y]/(y² + x y − (π x³ + π b₄ x + b₆))` of `E ∖ {0}`. -/
abbrev A : Type u := TateRing π b₄ b₆

/-- `x = u/w`. -/
abbrev xA : A π b₄ b₆ := AdjoinRoot.of _ X

/-- `y = v/w`. -/
abbrev yA : A π b₄ b₆ := bA π b₄ b₆

/-- The Weierstrass equation in `A`. -/
lemma eqA : yA π b₄ b₆ ^ 2 + xA π b₄ b₆ * yA π b₄ b₆ =
    algebraMap O _ π * xA π b₄ b₆ ^ 3 + algebraMap O _ (π * b₄) * xA π b₄ b₆ +
      algebraMap O _ b₆ := by
  have h := bA_sq π b₄ b₆
  simp only [cpoly, map_add, map_mul, map_pow, of_C] at h ⊢
  linear_combination h

/-- The generic fibre `A[1/ϖ]` of `E ∖ {0}`. -/
abbrev AK : Type u := Localization.Away (algebraMap O (A π b₄ b₆) ϖ)

/-- `x` in `A[1/ϖ]`. -/
abbrev xK : AK π b₄ b₆ ϖ := algebraMap (A π b₄ b₆) _ (xA π b₄ b₆)

/-- `y` in `A[1/ϖ]`. -/
abbrev yK : AK π b₄ b₆ ϖ := algebraMap (A π b₄ b₆) _ (yA π b₄ b₆)

/-- `y − t` in `A[1/ϖ]`. -/
abbrev aK : AK π b₄ b₆ ϖ := yK π b₄ b₆ ϖ - algebraMap O _ t

lemma eqAK : yK π b₄ b₆ ϖ ^ 2 + xK π b₄ b₆ ϖ * yK π b₄ b₆ ϖ =
    algebraMap O _ π * xK π b₄ b₆ ϖ ^ 3 + algebraMap O _ (π * b₄) * xK π b₄ b₆ ϖ +
      algebraMap O _ b₆ := by
  have h := congrArg (algebraMap (A π b₄ b₆) (AK π b₄ b₆ ϖ)) (eqA π b₄ b₆)
  simpa only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] using h

/-- The generic fibre `T1[1/ϖ]` of the chart `u ≠ 0`. -/
abbrev T1K : Type u := Localization.Away (algebraMap O (T1 π b₄ t κ) ϖ)

/-- `w` in `T1[1/ϖ]`. -/
abbrev wK : T1K π b₄ t κ ϖ := algebraMap (T1 π b₄ t κ) _ (w1 π b₄ t κ)

/-- `h'` in `T1[1/ϖ]`. -/
abbrev hK : T1K π b₄ t κ ϖ := algebraMap (T1 π b₄ t κ) _ (h1 π b₄ t κ)

/-- `s = h' + t w` in `T1[1/ϖ]`. -/
abbrev sK : T1K π b₄ t κ ϖ := algebraMap (T1 π b₄ t κ) _ (s1 π b₄ t κ)

/-- `A[1/ϖ][1/x]`. -/
abbrev AKx : Type u := Localization.Away (xK π b₄ b₆ ϖ)

/-- `1/x`. -/
abbrev xInv : AKx π b₄ b₆ ϖ := IsLocalization.Away.invSelf (xK π b₄ b₆ ϖ)

/-- `y − t` in `A[1/ϖ][1/x]`. -/
abbrev aKx : AKx π b₄ b₆ ϖ := algebraMap (AK π b₄ b₆ ϖ) _ (aK π b₄ b₆ t ϖ)

variable {π b₄ b₆ t κ ϖ}

/-- **`E ∖ {0} = D(y − t) ∪ D(x)`**: `κ (t² − b₆) = 1` gives
`1 = −κ (y + t) (y − t) − κ (y − π x² − π b₄) x`. -/
lemma span_a_x (hκ : κ * (t ^ 2 - b₆) = 1) :
    Ideal.span {aK π b₄ b₆ t ϖ, xK π b₄ b₆ ϖ} = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_pair]
  have hk : algebraMap O (AK π b₄ b₆ ϖ) κ * (algebraMap O _ t ^ 2 - algebraMap O _ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  refine ⟨-(algebraMap O _ κ * (yK π b₄ b₆ ϖ + algebraMap O _ t)),
    -(algebraMap O _ κ * (yK π b₄ b₆ ϖ - algebraMap O _ π * xK π b₄ b₆ ϖ ^ 2 -
      algebraMap O _ (π * b₄))), ?_⟩
  have h := eqAK π b₄ b₆ ϖ
  simp only [map_mul] at h ⊢
  linear_combination (-(algebraMap O (AK π b₄ b₆ ϖ) κ)) * h + hk

/-! ### Units on the generic fibre -/

section Units

variable {S : Type u} [CommRing S] [Algebra O S] {m : ℕ}

lemma isUnit_pi (hπ : π ∣ ϖ ^ m) (hϖ : IsUnit (algebraMap O S ϖ)) :
    IsUnit (algebraMap O S π) := by
  obtain ⟨c, hc⟩ := hπ
  have h : IsUnit (algebraMap O S (ϖ ^ m)) := by rw [map_pow]; exact hϖ.pow m
  rw [hc, map_mul] at h
  exact isUnit_of_mul_isUnit_left h

lemma isUnit_kappa (hκ : κ * (t ^ 2 - b₆) = 1) : IsUnit (algebraMap O S κ) :=
  IsUnit.of_mul_eq_one (algebraMap O S (t ^ 2 - b₆)) (by rw [← map_mul, hκ, map_one])

end Units

variable (b₄) {m : ℕ} (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π ∣ ϖ ^ m)

/-! ### The chart `u ≠ 0`: `T1[1/ϖ] = A[1/ϖ][1/x]` -/

lemma isUnit_varpi_T1K : IsUnit (algebraMap O (T1K π b₄ t κ ϖ) ϖ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := T1K π b₄ t κ ϖ)
    (algebraMap O (T1 π b₄ t κ) ϖ)
  rwa [← IsScalarTower.algebraMap_apply] at h

include hκ hπ in
/-- `w` is a unit on the generic fibre: `w (w² + κ (2 t h' + t − π b₄) w + κ (h'² + h')) = κ π`. -/
lemma isUnit_wK : IsUnit (wK π b₄ t κ ϖ) := by
  have h := congrArg (algebraMap (T1 π b₄ t κ) (T1K π b₄ t κ ϖ)) (eq1 π b₄ t κ)
  simp only [map_add, map_sub, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply] at h
  have hu : IsUnit (algebraMap O (T1K π b₄ t κ ϖ) κ * algebraMap O _ π) :=
    (isUnit_kappa hκ).mul (isUnit_pi hπ (isUnit_varpi_T1K b₄))
  have e : wK π b₄ t κ ϖ * (wK π b₄ t κ ϖ ^ 2 + algebraMap O _ κ * (algebraMap O _ (2 * t) *
      hK π b₄ t κ ϖ + algebraMap O _ (t - π * b₄)) * wK π b₄ t κ ϖ +
      algebraMap O _ κ * (hK π b₄ t κ ϖ ^ 2 + hK π b₄ t κ ϖ)) =
      algebraMap O _ κ * algebraMap O _ π := by
    simp only [map_mul, map_sub, map_ofNat] at h ⊢
    linear_combination h
  rw [← e] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- `1/w` in `T1[1/ϖ]`. -/
abbrev wInv : T1K π b₄ t κ ϖ := ((isUnit_wK b₄ hκ hπ).unit⁻¹ : (T1K π b₄ t κ ϖ)ˣ)

lemma wK_mul_wInv : wK π b₄ t κ ϖ * wInv b₄ hκ hπ = 1 := (isUnit_wK b₄ hκ hπ).mul_val_inv

include hκ in
lemma eqn1K : wK π b₄ t κ ϖ * (sK π b₄ t κ ϖ ^ 2 + sK π b₄ t κ ϖ -
    algebraMap O _ b₆ * wK π b₄ t κ ϖ ^ 2) =
    algebraMap O _ π * (1 + algebraMap O _ b₄ * wK π b₄ t κ ϖ ^ 2) := by
  have h := congrArg (algebraMap (T1 π b₄ t κ) (T1K π b₄ t κ ϖ)) (eqn1 π b₄ t κ hκ)
  simpa only [map_add, map_sub, map_mul, map_pow, map_one,
    ← IsScalarTower.algebraMap_apply] using h

lemma eval_fpoly_f1 : (fpoly π b₄ b₆).eval₂
    ((Polynomial.aeval (wInv b₄ hκ hπ) : O[X] →ₐ[O] T1K π b₄ t κ ϖ) : O[X] →+* T1K π b₄ t κ ϖ)
    (sK π b₄ t κ ϖ * wInv b₄ hκ hπ) = 0 := by
  rw [eval₂_fpoly]
  have h := eqn1K b₄ hκ (π := π) (ϖ := ϖ)
  have hw := wK_mul_wInv b₄ hκ hπ
  set W := wInv b₄ hκ hπ
  set w := wK π b₄ t κ ϖ
  set s := sK π b₄ t κ ϖ
  simp only [cpoly, RingHom.coe_coe, map_add, map_mul, map_pow, Polynomial.aeval_C,
    Polynomial.aeval_X]
  set e := w * W
  linear_combination W ^ 3 * h + (W ^ 3 * ((e + 1) * (s ^ 2 * w + s * w) -
    algebraMap O _ π * (e ^ 2 + e + 1) - algebraMap O _ π * algebraMap O _ b₄ * w ^ 2) -
    (e ^ 2 + e + 1) * ((s * W) ^ 2 + W * (s * W) - (algebraMap O _ π * W ^ 3 +
      algebraMap O _ π * algebraMap O _ b₄ * W + algebraMap O _ b₆))) * hw

/-- `A → T1[1/ϖ]`: `x ↦ 1/w`, `y ↦ s/w`. -/
def f1 : A π b₄ b₆ →ₐ[O] T1K π b₄ t κ ϖ :=
  AdjoinRoot.liftAlgHom (fpoly π b₄ b₆) (Polynomial.aeval (wInv b₄ hκ hπ))
    (sK π b₄ t κ ϖ * wInv b₄ hκ hπ) (eval_fpoly_f1 b₄ hκ hπ)

lemma f1_x : f1 b₄ hκ hπ (xA π b₄ b₆) = wInv b₄ hκ hπ := by simp [f1]

lemma f1_y : f1 b₄ hκ hπ (yA π b₄ b₆) = sK π b₄ t κ ϖ * wInv b₄ hκ hπ := by simp [f1]

lemma isUnit_f1_varpi : IsUnit (f1 b₄ hκ hπ (algebraMap O (A π b₄ b₆) ϖ)) := by
  rw [AlgHom.commutes]
  exact isUnit_varpi_T1K b₄

/-- `A[1/ϖ] → T1[1/ϖ]`. -/
def f1K : AK π b₄ b₆ ϖ →ₐ[O] T1K π b₄ t κ ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_f1_varpi b₄ hκ hπ)

lemma f1K_algebraMap (a : A π b₄ b₆) : f1K b₄ hκ hπ (algebraMap _ _ a) = f1 b₄ hκ hπ a :=
  IsLocalization.Away.lift_eq _ (isUnit_f1_varpi b₄ hκ hπ) a

/-- The `A[1/ϖ]`-algebra structure of `T1[1/ϖ]`. -/
abbrev algT1K : Algebra (AK π b₄ b₆ ϖ) (T1K π b₄ t κ ϖ) := (f1K b₄ hκ hπ).toRingHom.toAlgebra

lemma xKx_mul_xInv : algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (xK π b₄ b₆ ϖ) *
    xInv π b₄ b₆ ϖ = 1 := IsLocalization.Away.mul_invSelf _

lemma eqAKx : algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (yK π b₄ b₆ ϖ) ^ 2 +
    algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (xK π b₄ b₆ ϖ) *
      algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (yK π b₄ b₆ ϖ) =
    algebraMap O _ π * algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (xK π b₄ b₆ ϖ) ^ 3 +
      algebraMap O _ (π * b₄) * algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (xK π b₄ b₆ ϖ) +
      algebraMap O _ b₆ := by
  have h := congrArg (algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ)) (eqAK π b₄ b₆ ϖ)
  simpa only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] using h

variable (π ϖ) in
include hκ in
lemma eval_G1_g1 : (G1 π b₄ t κ).eval₂
    ((Polynomial.aeval (aKx π b₄ b₆ t ϖ * xInv π b₄ b₆ ϖ) : O[X] →ₐ[O] AKx π b₄ b₆ ϖ) :
      O[X] →+* AKx π b₄ b₆ ϖ) (xInv π b₄ b₆ ϖ) = 0 := by
  have h := eqAKx (π := π) (b₆ := b₆) (ϖ := ϖ) b₄
  have hI := xKx_mul_xInv (π := π) (b₆ := b₆) (ϖ := ϖ) b₄
  have hk : algebraMap O (AKx π b₄ b₆ ϖ) κ * (algebraMap O _ t ^ 2 - algebraMap O _ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  simp only [G1, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    RingHom.coe_coe, map_mul, map_add, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    aKx, aK, map_sub, map_ofNat, Polynomial.eval₂_ofNat]
  rw [← IsScalarTower.algebraMap_apply O (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) t]
  set I := xInv π b₄ b₆ ϖ
  set x := algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (xK π b₄ b₆ ϖ)
  set y := algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (yK π b₄ b₆ ϖ)
  set T := algebraMap O (AKx π b₄ b₆ ϖ) t
  set k := algebraMap O (AKx π b₄ b₆ ϖ) κ
  set p := algebraMap O (AKx π b₄ b₆ ϖ) π
  set c := algebraMap O (AKx π b₄ b₆ ϖ) b₄
  set e := x * I
  set u := y - T
  have hpb : algebraMap O (AKx π b₄ b₆ ϖ) (π * b₄) = p * c := map_mul _ _ _
  rw [hpb] at h
  linear_combination I ^ 3 * k * h - I ^ 3 * hk + (I ^ 3 * ((e ^ 2 + e + 1) *
    (1 + k * (2 * T * u + u ^ 2)) + (e + 1) * k * ((T - p * c) * x + u * x)) -
    (e ^ 2 + e + 1) * (I ^ 3 + k * (2 * T * (u * I) + (T - p * c)) * I ^ 2 +
      k * ((u * I) ^ 2 + u * I) * I - k * p)) * hI


variable (π ϖ) in
include hκ in
/-- `T1 → A[1/ϖ][1/x]`: `h' ↦ (y − t)/x`, `w ↦ 1/x`. -/
def g1 : T1 π b₄ t κ →ₐ[O] AKx π b₄ b₆ ϖ :=
  AdjoinRoot.liftAlgHom (G1 π b₄ t κ) (Polynomial.aeval (aKx π b₄ b₆ t ϖ * xInv π b₄ b₆ ϖ))
    (xInv π b₄ b₆ ϖ) (eval_G1_g1 π b₄ ϖ hκ)

variable (π ϖ) in
include hκ in
lemma g1_h : g1 π b₄ ϖ hκ (h1 π b₄ t κ) = aKx π b₄ b₆ t ϖ * xInv π b₄ b₆ ϖ := by simp [g1]

variable (π ϖ) in
include hκ in
lemma g1_w : g1 π b₄ ϖ hκ (w1 π b₄ t κ) = xInv π b₄ b₆ ϖ := by simp [g1]

variable (π b₆ ϖ) in
lemma isUnit_varpi_AK : IsUnit (algebraMap O (AK π b₄ b₆ ϖ) ϖ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := AK π b₄ b₆ ϖ)
    (algebraMap O (A π b₄ b₆) ϖ)
  rwa [← IsScalarTower.algebraMap_apply] at h

variable (π b₆ ϖ) in
lemma isUnit_varpi_AKx : IsUnit (algebraMap O (AKx π b₄ b₆ ϖ) ϖ) := by
  have h := (isUnit_varpi_AK π b₄ b₆ ϖ).map (algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ))
  rwa [← IsScalarTower.algebraMap_apply] at h

variable (π ϖ) in
include hκ in
lemma isUnit_g1_varpi : IsUnit (g1 π b₄ ϖ hκ (algebraMap O (T1 π b₄ t κ) ϖ)) := by
  rw [AlgHom.commutes]
  exact isUnit_varpi_AKx π b₄ b₆ ϖ

variable (π ϖ) in
/-- `T1[1/ϖ] → A[1/ϖ][1/x]`. -/
def g1K : T1K π b₄ t κ ϖ →ₐ[O] AKx π b₄ b₆ ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_g1_varpi π b₄ ϖ hκ)

variable (π ϖ) in
include hκ in
lemma g1K_algebraMap (a : T1 π b₄ t κ) : g1K π b₄ ϖ hκ (algebraMap _ _ a) = g1 π b₄ ϖ hκ a :=
  IsLocalization.Away.lift_eq _ (isUnit_g1_varpi π b₄ ϖ hκ) a

lemma isUnit_f1K_x : IsUnit (f1K b₄ hκ hπ (xK π b₄ b₆ ϖ)) := by
  rw [f1K_algebraMap, f1_x]
  exact Units.isUnit _

/-- `A[1/ϖ][1/x] → T1[1/ϖ]`. -/
def F1 : AKx π b₄ b₆ ϖ →ₐ[O] T1K π b₄ t κ ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_f1K_x b₄ hκ hπ)

lemma F1_algebraMap (a : AK π b₄ b₆ ϖ) : F1 b₄ hκ hπ (algebraMap _ _ a) = f1K b₄ hκ hπ a :=
  IsLocalization.Away.lift_eq _ (isUnit_f1K_x b₄ hκ hπ) a

lemma wInv_mul_wK : wInv b₄ hκ hπ * wK π b₄ t κ ϖ = 1 := by
  rw [mul_comm]; exact wK_mul_wInv b₄ hκ hπ

lemma F1_xInv : F1 b₄ hκ hπ (xInv π b₄ b₆ ϖ) = wK π b₄ t κ ϖ := by
  refine eq_of_mul_eq_one (a := wInv b₄ hκ hπ) ?_ (wInv_mul_wK b₄ hκ hπ)
  have h := congrArg (F1 b₄ hκ hπ) (xKx_mul_xInv (π := π) (b₆ := b₆) (ϖ := ϖ) b₄)
  rwa [map_mul, F1_algebraMap, f1K_algebraMap, f1_x, map_one] at h

lemma g1K_wInv : g1K π b₄ ϖ hκ (wInv b₄ hκ hπ) =
    algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (xK π b₄ b₆ ϖ) := by
  refine eq_of_mul_eq_one (a := xInv π b₄ b₆ ϖ) ?_ ?_
  · have h := congrArg (g1K π b₄ ϖ hκ) (wK_mul_wInv b₄ hκ hπ)
    rwa [map_mul, g1K_algebraMap, g1_w, map_one] at h
  · rw [mul_comm]; exact xKx_mul_xInv (π := π) (b₆ := b₆) (ϖ := ϖ) b₄

lemma sK_eq : sK π b₄ t κ ϖ = hK π b₄ t κ ϖ + algebraMap O _ t * wK π b₄ t κ ϖ := by
  simp only [sK, s1, map_add, map_mul, ← IsScalarTower.algebraMap_apply]

lemma F1_g1K (a : T1K π b₄ t κ ϖ) : F1 b₄ hκ hπ (g1K π b₄ ϖ hκ a) = a := by
  have : (F1 b₄ hκ hπ).comp (g1K π b₄ ϖ hκ) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (algebraMap O (T1 π b₄ t κ) ϖ))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change F1 b₄ hκ hπ (g1K π b₄ ϖ hκ (algebraMap _ _ (h1 π b₄ t κ))) = hK π b₄ t κ ϖ
      rw [g1K_algebraMap, g1_h, map_mul, F1_xInv, F1_algebraMap, aK, map_sub, AlgHom.commutes,
        f1K_algebraMap, f1_y, sub_mul, mul_assoc, wInv_mul_wK, mul_one, sK_eq]
      ring
    · change F1 b₄ hκ hπ (g1K π b₄ ϖ hκ (algebraMap _ _ (w1 π b₄ t κ))) = wK π b₄ t κ ϖ
      rw [g1K_algebraMap, g1_w, F1_xInv]
  exact AlgHom.congr_fun this a

lemma g1K_F1 (a : AKx π b₄ b₆ ϖ) : g1K π b₄ ϖ hκ (F1 b₄ hκ hπ a) = a := by
  have : (g1K π b₄ ϖ hκ).comp (F1 b₄ hκ hπ) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (xK π b₄ b₆ ϖ)) ?_
    refine IsLocalization.algHom_ext (Submonoid.powers (algebraMap O (A π b₄ b₆) ϖ)) ?_
    refine AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_
    · change g1K π b₄ ϖ hκ (F1 b₄ hκ hπ (algebraMap _ _ (xK π b₄ b₆ ϖ))) =
        algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (xK π b₄ b₆ ϖ)
      rw [F1_algebraMap, f1K_algebraMap, f1_x, g1K_wInv]
    · change g1K π b₄ ϖ hκ (F1 b₄ hκ hπ (algebraMap _ _ (yK π b₄ b₆ ϖ))) =
        algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (yK π b₄ b₆ ϖ)
      rw [F1_algebraMap, f1K_algebraMap, f1_y, map_mul, g1K_wInv, sK_eq, map_add, map_mul,
        AlgHom.commutes, g1K_algebraMap, g1K_algebraMap, g1_h, g1_w, aKx, aK, map_sub,
        ← IsScalarTower.algebraMap_apply O (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) t]
      linear_combination (algebraMap (AK π b₄ b₆ ϖ) (AKx π b₄ b₆ ϖ) (yK π b₄ b₆ ϖ) -
        algebraMap O _ t + algebraMap O _ t) *
        xKx_mul_xInv (π := π) (b₆ := b₆) (ϖ := ϖ) b₄
  exact AlgHom.congr_fun this a

/-- **`T1[1/ϖ] = A[1/ϖ][1/x]`**, as `A[1/ϖ]`-algebras. -/
def equiv1 : letI := algT1K b₄ hκ hπ
    AKx π b₄ b₆ ϖ ≃ₐ[AK π b₄ b₆ ϖ] T1K π b₄ t κ ϖ :=
  letI := algT1K b₄ hκ hπ
  { toFun := F1 b₄ hκ hπ
    invFun := g1K π b₄ ϖ hκ
    left_inv := g1K_F1 b₄ hκ hπ
    right_inv := F1_g1K b₄ hκ hπ
    map_mul' := map_mul _
    map_add' := map_add _
    commutes' := F1_algebraMap b₄ hκ hπ }

/-- **The chart `u ≠ 0` on the generic fibre is `D(x) ⊆ E ∖ {0}`**: `T1[1/ϖ]` is the
localization of `A[1/ϖ]` away from `x`. -/
theorem isLocalization_T1K :
    letI := algT1K b₄ hκ hπ
    IsLocalization.Away (xK π b₄ b₆ ϖ) (T1K π b₄ t κ ϖ) :=
  letI := algT1K b₄ hκ hπ
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (xK π b₄ b₆ ϖ)) (equiv1 b₄ hκ hπ)


/-! ### The chart `ℓ₀ ≠ 0`: `T0[1/(ϖ z)] = A[1/ϖ][1/(y − t)]` -/

variable (π t κ ϖ) in
/-- The generic fibre `T0[1/(ϖ z)]` of the chart `ℓ₀ ≠ 0` with the origin `z = 0` removed. -/
abbrev T0K : Type u := Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)

variable (π t κ ϖ) in
/-- `z` in `T0[1/(ϖ z)]`. -/
abbrev zK : T0K π b₄ t κ ϖ := algebraMap (T0 π b₄ t κ) _ (z0 π b₄ t κ)

variable (π t κ ϖ) in
/-- `h` in `T0[1/(ϖ z)]`. -/
abbrev hK0 : T0K π b₄ t κ ϖ := algebraMap (T0 π b₄ t κ) _ (h0 π b₄ t κ)

variable (π t κ ϖ) in
lemma isUnit_varpi_mul_zK : IsUnit (algebraMap O (T0K π b₄ t κ ϖ) ϖ * zK π b₄ t κ ϖ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := T0K π b₄ t κ ϖ)
    (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)
  rwa [map_mul, ← IsScalarTower.algebraMap_apply] at h

variable (π t κ ϖ) in
lemma isUnit_zK : IsUnit (zK π b₄ t κ ϖ) :=
  isUnit_of_mul_isUnit_right (isUnit_varpi_mul_zK π b₄ t κ ϖ)

variable (π t κ ϖ) in
lemma isUnit_varpi_T0K : IsUnit (algebraMap O (T0K π b₄ t κ ϖ) ϖ) :=
  isUnit_of_mul_isUnit_left (isUnit_varpi_mul_zK π b₄ t κ ϖ)

variable (π t κ ϖ) in
/-- `1/z`. -/
abbrev zInv : T0K π b₄ t κ ϖ := ((isUnit_zK π b₄ t κ ϖ).unit⁻¹ : (T0K π b₄ t κ ϖ)ˣ)

variable (π t κ ϖ) in
lemma zK_mul_zInv : zK π b₄ t κ ϖ * zInv π b₄ t κ ϖ = 1 := (isUnit_zK π b₄ t κ ϖ).mul_val_inv

variable (π t κ ϖ) in
lemma eq0K : zK π b₄ t κ ϖ ^ 3 + algebraMap O _ κ * (2 * algebraMap O _ t +
    (algebraMap O _ t - algebraMap O _ π * algebraMap O _ b₄) * hK0 π b₄ t κ ϖ) *
    zK π b₄ t κ ϖ ^ 2 + algebraMap O _ κ * (1 + hK0 π b₄ t κ ϖ) * zK π b₄ t κ ϖ -
    algebraMap O _ κ * algebraMap O _ π * hK0 π b₄ t κ ϖ ^ 3 = 0 := by
  have h := congrArg (algebraMap (T0 π b₄ t κ) (T0K π b₄ t κ ϖ)) (eq0 π b₄ t κ)
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_one, map_ofNat,
    ← IsScalarTower.algebraMap_apply] at h
  linear_combination h

variable (π ϖ) in
include hκ in
lemma eval_fpoly_f0 : (fpoly π b₄ b₆).eval₂
    ((Polynomial.aeval (hK0 π b₄ t κ ϖ * zInv π b₄ t κ ϖ) : O[X] →ₐ[O] T0K π b₄ t κ ϖ) :
      O[X] →+* T0K π b₄ t κ ϖ) (algebraMap O _ t + zInv π b₄ t κ ϖ) = 0 := by
  rw [eval₂_fpoly]
  have h := eq0K π b₄ t κ ϖ
  have hz := zK_mul_zInv π b₄ t κ ϖ
  have hk : algebraMap O (T0K π b₄ t κ ϖ) κ * (algebraMap O _ t ^ 2 - algebraMap O _ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  set Z := zInv π b₄ t κ ϖ
  set z := zK π b₄ t κ ϖ
  set hh := hK0 π b₄ t κ ϖ
  simp only [cpoly, RingHom.coe_coe, map_add, map_mul, map_pow, Polynomial.aeval_C,
    Polynomial.aeval_X]
  set T := algebraMap O (T0K π b₄ t κ ϖ) t
  set p := algebraMap O (T0K π b₄ t κ ϖ) π
  set c := algebraMap O (T0K π b₄ t κ ϖ) b₄
  set d := algebraMap O (T0K π b₄ t κ ϖ) b₆
  set e := z * Z
  linear_combination (T ^ 2 - d) * Z ^ 3 * h - Z ^ 3 * ((2 * T + (T - p * c) * hh) * z ^ 2 +
    (1 + hh) * z - p * hh ^ 3) * hk - ((T ^ 2 - d) * (e ^ 2 + e + 1) +
    (2 * T + (T - p * c) * hh) * Z * (e + 1) + (1 + hh) * Z ^ 2) * hz

variable (π ϖ) in
include hκ in
/-- `A → T0[1/(ϖ z)]`: `x ↦ h/z`, `y ↦ t + 1/z`. -/
def f0 : A π b₄ b₆ →ₐ[O] T0K π b₄ t κ ϖ :=
  AdjoinRoot.liftAlgHom (fpoly π b₄ b₆) (Polynomial.aeval (hK0 π b₄ t κ ϖ * zInv π b₄ t κ ϖ))
    (algebraMap O _ t + zInv π b₄ t κ ϖ) (eval_fpoly_f0 π b₄ ϖ hκ)

variable (π ϖ) in
include hκ in
lemma f0_x : f0 π b₄ ϖ hκ (xA π b₄ b₆) = hK0 π b₄ t κ ϖ * zInv π b₄ t κ ϖ := by simp [f0]

variable (π ϖ) in
include hκ in
lemma f0_y : f0 π b₄ ϖ hκ (yA π b₄ b₆) = algebraMap O _ t + zInv π b₄ t κ ϖ := by simp [f0]

variable (π ϖ) in
include hκ in
lemma isUnit_f0_varpi : IsUnit (f0 π b₄ ϖ hκ (algebraMap O (A π b₄ b₆) ϖ)) := by
  rw [AlgHom.commutes]
  exact isUnit_varpi_T0K π b₄ t κ ϖ

variable (π ϖ) in
/-- `A[1/ϖ] → T0[1/(ϖ z)]`. -/
def f0K : AK π b₄ b₆ ϖ →ₐ[O] T0K π b₄ t κ ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_f0_varpi π b₄ ϖ hκ)

variable (π ϖ) in
include hκ in
lemma f0K_algebraMap (a : A π b₄ b₆) : f0K π b₄ ϖ hκ (algebraMap _ _ a) = f0 π b₄ ϖ hκ a :=
  IsLocalization.Away.lift_eq _ (isUnit_f0_varpi π b₄ ϖ hκ) a

variable (π ϖ) in
/-- The `A[1/ϖ]`-algebra structure of `T0[1/(ϖ z)]`. -/
abbrev algT0K : Algebra (AK π b₄ b₆ ϖ) (T0K π b₄ t κ ϖ) := (f0K π b₄ ϖ hκ).toRingHom.toAlgebra

variable (π b₆ t ϖ) in
/-- `A[1/ϖ][1/(y − t)]`. -/
abbrev AKa : Type u := Localization.Away (aK π b₄ b₆ t ϖ)

variable (π b₆ t ϖ) in
/-- `1/(y − t)`. -/
abbrev aInv : AKa π b₄ b₆ t ϖ := IsLocalization.Away.invSelf (aK π b₄ b₆ t ϖ)

variable (π b₆ t ϖ) in
/-- `x` in `A[1/ϖ][1/(y − t)]`. -/
abbrev xKa : AKa π b₄ b₆ t ϖ := algebraMap (AK π b₄ b₆ ϖ) _ (xK π b₄ b₆ ϖ)

variable (π b₆ t ϖ) in
/-- `y` in `A[1/ϖ][1/(y − t)]`. -/
abbrev yKa : AKa π b₄ b₆ t ϖ := algebraMap (AK π b₄ b₆ ϖ) _ (yK π b₄ b₆ ϖ)

variable (π b₆ t ϖ) in
lemma aKa_mul_aInv : (yKa π b₄ b₆ t ϖ - algebraMap O _ t) * aInv π b₄ b₆ t ϖ = 1 := by
  have h : algebraMap (AK π b₄ b₆ ϖ) (AKa π b₄ b₆ t ϖ) (aK π b₄ b₆ t ϖ) * aInv π b₄ b₆ t ϖ = 1 :=
    IsLocalization.Away.mul_invSelf _
  simp only [aK, map_sub, ← IsScalarTower.algebraMap_apply] at h
  exact h

variable (π b₆ t ϖ) in
lemma eqAKa : yKa π b₄ b₆ t ϖ ^ 2 + xKa π b₄ b₆ t ϖ * yKa π b₄ b₆ t ϖ =
    algebraMap O _ π * xKa π b₄ b₆ t ϖ ^ 3 + algebraMap O _ π * algebraMap O _ b₄ *
      xKa π b₄ b₆ t ϖ + algebraMap O _ b₆ := by
  have h := congrArg (algebraMap (AK π b₄ b₆ ϖ) (AKa π b₄ b₆ t ϖ)) (eqAK π b₄ b₆ ϖ)
  simpa only [map_add, map_mul, map_pow, ← IsScalarTower.algebraMap_apply] using h

variable (π ϖ) in
include hκ in
lemma eval_G0_g0 : (G0 π b₄ t κ).eval₂
    ((Polynomial.aeval (xKa π b₄ b₆ t ϖ * aInv π b₄ b₆ t ϖ) : O[X] →ₐ[O] AKa π b₄ b₆ t ϖ) :
      O[X] →+* AKa π b₄ b₆ t ϖ) (aInv π b₄ b₆ t ϖ) = 0 := by
  have h := eqAKa π b₄ b₆ t ϖ
  have hI := aKa_mul_aInv π b₄ b₆ t ϖ
  have hk : algebraMap O (AKa π b₄ b₆ t ϖ) κ * (algebraMap O _ t ^ 2 - algebraMap O _ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  simp only [G0, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one,
    RingHom.coe_coe, map_mul, map_add, map_pow, map_one, Polynomial.aeval_C, Polynomial.aeval_X,
    map_sub, map_ofNat, Polynomial.eval₂_ofNat]
  set I := aInv π b₄ b₆ t ϖ
  set x := xKa π b₄ b₆ t ϖ
  set y := yKa π b₄ b₆ t ϖ
  set T := algebraMap O (AKa π b₄ b₆ t ϖ) t
  set k := algebraMap O (AKa π b₄ b₆ t ϖ) κ
  set u := y - T
  linear_combination I ^ 3 * k * h - I ^ 3 * hk -
    k * (2 * T * I ^ 2 + I + u * I ^ 2 + x * I ^ 2) * hI

variable (π ϖ) in
include hκ in
/-- `T0 → A[1/ϖ][1/(y − t)]`: `h ↦ x/(y − t)`, `z ↦ 1/(y − t)`. -/
def g0 : T0 π b₄ t κ →ₐ[O] AKa π b₄ b₆ t ϖ :=
  AdjoinRoot.liftAlgHom (G0 π b₄ t κ) (Polynomial.aeval (xKa π b₄ b₆ t ϖ * aInv π b₄ b₆ t ϖ))
    (aInv π b₄ b₆ t ϖ) (eval_G0_g0 π b₄ ϖ hκ)

variable (π ϖ) in
include hκ in
lemma g0_h : g0 π b₄ ϖ hκ (h0 π b₄ t κ) = xKa π b₄ b₆ t ϖ * aInv π b₄ b₆ t ϖ := by simp [g0]

variable (π ϖ) in
include hκ in
lemma g0_z : g0 π b₄ ϖ hκ (z0 π b₄ t κ) = aInv π b₄ b₆ t ϖ := by simp [g0]

variable (π b₆ t ϖ) in
lemma isUnit_varpi_AKa : IsUnit (algebraMap O (AKa π b₄ b₆ t ϖ) ϖ) := by
  have h := (isUnit_varpi_AK π b₄ b₆ ϖ).map (algebraMap (AK π b₄ b₆ ϖ) (AKa π b₄ b₆ t ϖ))
  rwa [← IsScalarTower.algebraMap_apply] at h

variable (π ϖ) in
include hκ in
lemma isUnit_g0_varpi_z :
    IsUnit (g0 π b₄ ϖ hκ (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)) := by
  rw [map_mul, AlgHom.commutes, g0_z]
  exact (isUnit_varpi_AKa π b₄ b₆ t ϖ).mul
    (IsUnit.of_mul_eq_one_right _ (aKa_mul_aInv π b₄ b₆ t ϖ))

variable (π ϖ) in
/-- `T0[1/(ϖ z)] → A[1/ϖ][1/(y − t)]`. -/
def g0K : T0K π b₄ t κ ϖ →ₐ[O] AKa π b₄ b₆ t ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_g0_varpi_z π b₄ ϖ hκ)

variable (π ϖ) in
include hκ in
lemma g0K_algebraMap (a : T0 π b₄ t κ) : g0K π b₄ ϖ hκ (algebraMap _ _ a) = g0 π b₄ ϖ hκ a :=
  IsLocalization.Away.lift_eq _ (isUnit_g0_varpi_z π b₄ ϖ hκ) a

variable (π ϖ) in
include hκ in
lemma f0K_aK : f0K π b₄ ϖ hκ (aK π b₄ b₆ t ϖ) = zInv π b₄ t κ ϖ := by
  rw [aK, map_sub, AlgHom.commutes, f0K_algebraMap, f0_y, add_sub_cancel_left]

variable (π ϖ) in
include hκ in
lemma isUnit_f0K_a : IsUnit (f0K π b₄ ϖ hκ (aK π b₄ b₆ t ϖ)) := by
  rw [f0K_aK]
  exact Units.isUnit _

variable (π ϖ) in
/-- `A[1/ϖ][1/(y − t)] → T0[1/(ϖ z)]`. -/
def F0 : AKa π b₄ b₆ t ϖ →ₐ[O] T0K π b₄ t κ ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_f0K_a π b₄ ϖ hκ)

variable (π ϖ) in
include hκ in
lemma F0_algebraMap (a : AK π b₄ b₆ ϖ) :
    F0 π b₄ ϖ hκ (algebraMap _ _ a) = f0K π b₄ ϖ hκ a :=
  IsLocalization.Away.lift_eq _ (isUnit_f0K_a π b₄ ϖ hκ) a

variable (π t κ ϖ) in
lemma zInv_mul_zK : zInv π b₄ t κ ϖ * zK π b₄ t κ ϖ = 1 := by
  rw [mul_comm]; exact zK_mul_zInv π b₄ t κ ϖ

variable (π ϖ) in
include hκ in
lemma F0_aInv : F0 π b₄ ϖ hκ (aInv π b₄ b₆ t ϖ) = zK π b₄ t κ ϖ := by
  refine eq_of_mul_eq_one (a := zInv π b₄ t κ ϖ) ?_ (zInv_mul_zK π b₄ t κ ϖ)
  have h := congrArg (F0 π b₄ ϖ hκ) (aKa_mul_aInv π b₄ b₆ t ϖ)
  rwa [map_mul, map_sub, AlgHom.commutes, yKa, F0_algebraMap, f0K_algebraMap, f0_y,
    add_sub_cancel_left, map_one] at h

variable (π ϖ) in
include hκ in
lemma g0K_zInv : g0K π b₄ ϖ hκ (zInv π b₄ t κ ϖ) = yKa π b₄ b₆ t ϖ - algebraMap O _ t := by
  refine eq_of_mul_eq_one (a := aInv π b₄ b₆ t ϖ) ?_ ?_
  · have h := congrArg (g0K π b₄ ϖ hκ) (zK_mul_zInv π b₄ t κ ϖ)
    rwa [map_mul, g0K_algebraMap, g0_z, map_one] at h
  · rw [mul_comm]; exact aKa_mul_aInv π b₄ b₆ t ϖ

variable (π ϖ) in
include hκ in
lemma F0_g0K (a : T0K π b₄ t κ ϖ) : F0 π b₄ ϖ hκ (g0K π b₄ ϖ hκ a) = a := by
  have : (F0 π b₄ ϖ hκ).comp (g0K π b₄ ϖ hκ) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext
      (Submonoid.powers (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change F0 π b₄ ϖ hκ (g0K π b₄ ϖ hκ (algebraMap _ _ (h0 π b₄ t κ))) = hK0 π b₄ t κ ϖ
      rw [g0K_algebraMap, g0_h, map_mul, F0_aInv, xKa, F0_algebraMap, f0K_algebraMap, f0_x,
        mul_assoc, zInv_mul_zK, mul_one]
    · change F0 π b₄ ϖ hκ (g0K π b₄ ϖ hκ (algebraMap _ _ (z0 π b₄ t κ))) = zK π b₄ t κ ϖ
      rw [g0K_algebraMap, g0_z, F0_aInv]
  exact AlgHom.congr_fun this a

variable (π ϖ) in
include hκ in
lemma g0K_F0 (a : AKa π b₄ b₆ t ϖ) : g0K π b₄ ϖ hκ (F0 π b₄ ϖ hκ a) = a := by
  have : (g0K π b₄ ϖ hκ).comp (F0 π b₄ ϖ hκ) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (aK π b₄ b₆ t ϖ)) ?_
    refine IsLocalization.algHom_ext (Submonoid.powers (algebraMap O (A π b₄ b₆) ϖ)) ?_
    refine AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_
    · change g0K π b₄ ϖ hκ (F0 π b₄ ϖ hκ (algebraMap _ _ (xK π b₄ b₆ ϖ))) = xKa π b₄ b₆ t ϖ
      rw [F0_algebraMap, f0K_algebraMap, f0_x, map_mul, g0K_zInv, g0K_algebraMap, g0_h,
        mul_assoc, mul_comm (aInv π b₄ b₆ t ϖ), aKa_mul_aInv, mul_one]
    · change g0K π b₄ ϖ hκ (F0 π b₄ ϖ hκ (algebraMap _ _ (yK π b₄ b₆ ϖ))) = yKa π b₄ b₆ t ϖ
      rw [F0_algebraMap, f0K_algebraMap, f0_y, map_add, g0K_zInv, AlgHom.commutes,
        add_sub_cancel]
  exact AlgHom.congr_fun this a

variable (π ϖ) in
/-- **`T0[1/(ϖ z)] = A[1/ϖ][1/(y − t)]`**, as `A[1/ϖ]`-algebras. -/
def equiv0 : letI := algT0K π b₄ ϖ hκ
    AKa π b₄ b₆ t ϖ ≃ₐ[AK π b₄ b₆ ϖ] T0K π b₄ t κ ϖ :=
  letI := algT0K π b₄ ϖ hκ
  { toFun := F0 π b₄ ϖ hκ
    invFun := g0K π b₄ ϖ hκ
    left_inv := g0K_F0 π b₄ ϖ hκ
    right_inv := F0_g0K π b₄ ϖ hκ
    map_mul' := map_mul _
    map_add' := map_add _
    commutes' := F0_algebraMap π b₄ ϖ hκ }

variable (π ϖ) in
/-- **The chart `ℓ₀ ≠ 0` on the generic fibre, without the origin, is `D(y − t) ⊆ E ∖ {0}`**:
`T0[1/(ϖ z)]` is the localization of `A[1/ϖ]` away from `y − t`. -/
theorem isLocalization_T0K :
    letI := algT0K π b₄ ϖ hκ
    IsLocalization.Away (aK π b₄ b₆ t ϖ) (T0K π b₄ t κ ϖ) :=
  letI := algT0K π b₄ ϖ hκ
  IsLocalization.isLocalization_of_algEquiv (Submonoid.powers (aK π b₄ b₆ t ϖ))
    (equiv0 π b₄ ϖ hκ)

/-! ### The overlap: both identifications agree on `T01[1/ϖ]` -/

variable (π t κ ϖ) in
/-- The generic fibre `T01[1/ϖ]` of the overlap. -/
abbrev T01K : Type u := Localization.Away (algebraMap O (T01 π b₄ t κ) ϖ)

variable (π t κ ϖ) in
lemma isUnit_varpi_T01K : IsUnit (algebraMap O (T01K π b₄ t κ ϖ) ϖ) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := T01K π b₄ t κ ϖ)
    (algebraMap O (T01 π b₄ t κ) ϖ)
  rwa [← IsScalarTower.algebraMap_apply] at h

variable (π t κ ϖ) in
/-- `T1 → T01[1/ϖ]`. -/
abbrev res1 : T1 π b₄ t κ →ₐ[O] T01K π b₄ t κ ϖ :=
  (IsScalarTower.toAlgHom O (T01 π b₄ t κ) (T01K π b₄ t κ ϖ)).comp
    (IsScalarTower.toAlgHom O (T1 π b₄ t κ) (T01 π b₄ t κ))

variable (π t κ ϖ) in
lemma isUnit_res1_varpi : IsUnit (res1 π b₄ t κ ϖ (algebraMap O (T1 π b₄ t κ) ϖ)) := by
  rw [AlgHom.commutes]
  exact isUnit_varpi_T01K π b₄ t κ ϖ

variable (π t κ ϖ) in
/-- `T1[1/ϖ] → T01[1/ϖ]`. -/
def r1K : T1K π b₄ t κ ϖ →ₐ[O] T01K π b₄ t κ ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_res1_varpi π b₄ t κ ϖ)

variable (π t κ ϖ) in
lemma r1K_algebraMap (a : T1 π b₄ t κ) : r1K π b₄ t κ ϖ (algebraMap _ _ a) =
    algebraMap (T01 π b₄ t κ) (T01K π b₄ t κ ϖ) (algebraMap _ _ a) :=
  IsLocalization.Away.lift_eq _ (isUnit_res1_varpi π b₄ t κ ϖ) a

variable (π t κ ϖ) in
/-- `1/h'` in `T01[1/ϖ]`. -/
abbrev Hinv : T01K π b₄ t κ ϖ := algebraMap (T01 π b₄ t κ) _ (hinv π b₄ t κ)

variable (π t κ ϖ) in
/-- `h'` in `T01[1/ϖ]`. -/
abbrev Hh : T01K π b₄ t κ ϖ :=
  algebraMap (T01 π b₄ t κ) _ (algebraMap (T1 π b₄ t κ) _ (h1 π b₄ t κ))

variable (π t κ ϖ) in
lemma Hh_mul_Hinv : Hh π b₄ t κ ϖ * Hinv π b₄ t κ ϖ = 1 := by
  rw [← map_mul, h1_mul_hinv, map_one]

/-- `T0 → T01[1/ϖ]` (through `ρ₀`). -/
abbrev res0 : T0 π b₄ t κ →ₐ[O] T01K π b₄ t κ ϖ :=
  (IsScalarTower.toAlgHom O (T01 π b₄ t κ) (T01K π b₄ t κ ϖ)).comp (rho0 π b₄ t κ)

include hκ hπ in
lemma isUnit_res0_varpi_z :
    IsUnit (res0 b₄ (π := π) (t := t) (κ := κ) (ϖ := ϖ)
      (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)) := by
  rw [map_mul, AlgHom.commutes]
  refine (isUnit_varpi_T01K π b₄ t κ ϖ).mul ?_
  change IsUnit (algebraMap (T01 π b₄ t κ) (T01K π b₄ t κ ϖ) (rho0 π b₄ t κ (z0 π b₄ t κ)))
  rw [rho0_z0, map_mul]
  refine IsUnit.mul ?_ (IsUnit.of_mul_eq_one_right _ (Hh_mul_Hinv π b₄ t κ ϖ))
  have h := (isUnit_wK b₄ hκ hπ).map (r1K π b₄ t κ ϖ)
  rwa [r1K_algebraMap] at h

/-- `T0[1/(ϖ z)] → T01[1/ϖ]`, induced by `ρ₀`. -/
def r0K : T0K π b₄ t κ ϖ →ₐ[O] T01K π b₄ t κ ϖ :=
  IsLocalization.Away.liftAlgHom _ (isUnit_res0_varpi_z b₄ hκ hπ)

lemma r0K_algebraMap (a : T0 π b₄ t κ) : r0K b₄ hκ hπ (algebraMap _ _ a) =
    algebraMap (T01 π b₄ t κ) (T01K π b₄ t κ ϖ) (rho0 π b₄ t κ a) :=
  IsLocalization.Away.lift_eq _ (isUnit_res0_varpi_z b₄ hκ hπ) a

lemma r1K_wK_mul_wInv : r1K π b₄ t κ ϖ (wK π b₄ t κ ϖ) * r1K π b₄ t κ ϖ (wInv b₄ hκ hπ) = 1 := by
  rw [← map_mul, wK_mul_wInv, map_one]

lemma r0K_zInv : r0K b₄ hκ hπ (zInv π b₄ t κ ϖ) =
    r1K π b₄ t κ ϖ (wInv b₄ hκ hπ) * Hh π b₄ t κ ϖ := by
  refine eq_of_mul_eq_one (a := r0K b₄ hκ hπ (zK π b₄ t κ ϖ)) ?_ ?_
  · rw [← map_mul, zK_mul_zInv, map_one]
  · have hw := r1K_wK_mul_wInv b₄ hκ hπ
    have hH := Hh_mul_Hinv π b₄ t κ ϖ
    rw [zK, r0K_algebraMap, rho0_z0, map_mul]
    rw [wK, r1K_algebraMap] at hw
    linear_combination (Hinv π b₄ t κ ϖ * Hh π b₄ t κ ϖ) * hw + hH

/-- **The two charts agree on the overlap**: the identifications `A[1/ϖ] → T0[1/(ϖ z)]` and
`A[1/ϖ] → T1[1/ϖ]` become equal in `T01[1/ϖ]`. -/
theorem r0K_comp : (r0K b₄ hκ hπ).comp (f0K π b₄ ϖ hκ) = (r1K π b₄ t κ ϖ).comp (f1K b₄ hκ hπ) := by
  have hw := r1K_wK_mul_wInv b₄ hκ hπ
  have hH := Hh_mul_Hinv π b₄ t κ ϖ
  have hs : r1K π b₄ t κ ϖ (sK π b₄ t κ ϖ) =
      Hh π b₄ t κ ϖ + algebraMap O _ t * r1K π b₄ t κ ϖ (wK π b₄ t κ ϖ) := by
    rw [sK_eq, map_add, map_mul, AlgHom.commutes, hK, r1K_algebraMap]
  refine IsLocalization.algHom_ext (Submonoid.powers (algebraMap O (A π b₄ b₆) ϖ))
    (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
  · change r0K b₄ hκ hπ (f0K π b₄ ϖ hκ (algebraMap _ _ (xA π b₄ b₆))) =
      r1K π b₄ t κ ϖ (f1K b₄ hκ hπ (algebraMap _ _ (xA π b₄ b₆)))
    rw [f0K_algebraMap, f0_x, f1K_algebraMap, f1_x, map_mul, r0K_zInv, hK0, r0K_algebraMap,
      rho0_h0]
    linear_combination r1K π b₄ t κ ϖ (wInv b₄ hκ hπ) * hH
  · change r0K b₄ hκ hπ (f0K π b₄ ϖ hκ (algebraMap _ _ (yA π b₄ b₆))) =
      r1K π b₄ t κ ϖ (f1K b₄ hκ hπ (algebraMap _ _ (yA π b₄ b₆)))
    rw [f0K_algebraMap, f0_y, f1K_algebraMap, f1_y, map_add, map_mul, r0K_zInv, AlgHom.commutes,
      hs]
    linear_combination (-algebraMap O (T01K π b₄ t κ ϖ) t) * hw

end

end TateAffine

end SemistableReduction
