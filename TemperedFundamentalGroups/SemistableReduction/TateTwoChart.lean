/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraOfRings

/-!
# The Tate model over `ℙ¹` as two-chart rings (Blueprint §12.8, M2.3 (f), Tate case)

The projection `[ℓ₀ : ℓ₁] = [v − t w : u]` of the Tate cubic
`F = v² w + u v w − π u³ − π b₄ u w² − b₆ w³` from `[0 : t : 1]` (`ε = t² − b₆` a unit,
`κ ε = 1`; `TemperedFundamentalGroups.TateProjection.toP1`) is finite of degree `3`; its two
charts are monic cubics over the chart rings of `ℙ¹_O` (`TateProjection.cubic₀/cubic₁`). Here
these chart rings are built algebraically:

* `TateTwoChart.T0 = O[h][z]/(G₀)` with `h = u/ℓ₀`, `z = w/ℓ₀` and
  `G₀ = z³ + κ(2t + (t − π b₄) h) z² + κ(1 + h) z − κ π h³` (`F/ℓ₀³ = ε G₀`, `v/ℓ₀ = 1 + t z`);
* `TateTwoChart.T1 = O[h'][w]/(G₁)` with `h' = ℓ₀/u`, `w = w/u` and
  `G₁ = w³ + κ(2t h' + t − π b₄) w² + κ(h'² + h') w − κ π` (`F/u³ = ε G₁`). In the node
  coordinates `s = v/u = h' + t w`, `w` of the chart `u ≠ 0` this is the equation
  `w (s² + s − b₆ w²) = π (1 + b₄ w²)` (**`TateTwoChart.eqn1`**);
* both are free of rank three over `O[X]` (`X ↦ h`, resp. `X ↦ h'`);
* the overlap: `T01 = T1[1/h']`, and **`TateTwoChart.rho0 : T0 → T01`** (`h ↦ 1/h'`,
  `z ↦ w/h'`) exhibits `T01` as `T0[1/h]` (**`TateTwoChart.isLocalization_rho0`**, via the inverse
  `T1[1/h'] → T0[1/h]`, `h' ↦ 1/h`, `w ↦ z/h`);
* **`TateTwoChart.twoChart`**: the Tate model as `ProjectiveLine.TwoChartRings O` (`x = h`,
  `y = h'`), the input format of the chart algebras of `formal-schemes`.

The identification with the sections of the scheme `TateModel.model` over `toP1⁻¹ U_k` is not
made here.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateTwoChart

noncomputable section

variable {O : Type u} [CommRing O] (π b₄ t κ : O)

/-- The monic cubic `G₀ ∈ O[h][z]` of the chart `ℓ₀ ≠ 0`. -/
def G0 : O[X][X] :=
  X ^ 3 + C (C κ * (C (2 * t) + C (t - π * b₄) * X)) * X ^ 2 + C (C κ * (1 + X)) * X -
    C (C (κ * π) * X ^ 3)

/-- The monic cubic `G₁ ∈ O[h'][w]` of the chart `u ≠ 0`. -/
def G1 : O[X][X] :=
  X ^ 3 + C (C κ * (C (2 * t) * X + C (t - π * b₄))) * X ^ 2 + C (C κ * (X ^ 2 + X)) * X -
    C (C (κ * π))

lemma monic_G0 : (G0 π b₄ t κ).Monic := by
  unfold G0
  monicity!

lemma monic_G1 : (G1 π b₄ t κ).Monic := by
  unfold G1
  monicity!

/-- The chart ring over `U₀ = D₊(ℓ₀)`. -/
abbrev T0 : Type u := AdjoinRoot (G0 π b₄ t κ)

/-- The chart ring over `U₁ = D₊(u)`. -/
abbrev T1 : Type u := AdjoinRoot (G1 π b₄ t κ)

instance : Module.Free O[X] (T0 π b₄ t κ) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_G0 π b₄ t κ)).basis

instance : Module.Finite O[X] (T0 π b₄ t κ) :=
  (AdjoinRoot.powerBasis' (monic_G0 π b₄ t κ)).finite

instance : Module.Free O[X] (T1 π b₄ t κ) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_G1 π b₄ t κ)).basis

instance : Module.Finite O[X] (T1 π b₄ t κ) :=
  (AdjoinRoot.powerBasis' (monic_G1 π b₄ t κ)).finite

/-- `h = u/ℓ₀`. -/
abbrev h0 : T0 π b₄ t κ := AdjoinRoot.of _ X

/-- `z = w/ℓ₀`. -/
abbrev z0 : T0 π b₄ t κ := AdjoinRoot.root _

/-- `h' = ℓ₀/u`. -/
abbrev h1 : T1 π b₄ t κ := AdjoinRoot.of _ X

/-- `w = w/u`. -/
abbrev w1 : T1 π b₄ t κ := AdjoinRoot.root _

/-- The node coordinate `s = v/u = h' + t w`. -/
abbrev s1 : T1 π b₄ t κ := h1 π b₄ t κ + algebraMap O _ t * w1 π b₄ t κ

lemma of_C (G : O[X][X]) (o : O) :
    AdjoinRoot.of G (C o) = algebraMap O (AdjoinRoot G) o := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply]
  rfl

/-- The cubic relation in `T0`. -/
lemma eq0 : z0 π b₄ t κ ^ 3 + algebraMap O _ κ * (algebraMap O _ (2 * t) +
    algebraMap O _ (t - π * b₄) * h0 π b₄ t κ) * z0 π b₄ t κ ^ 2 +
    algebraMap O _ κ * (1 + h0 π b₄ t κ) * z0 π b₄ t κ -
    algebraMap O _ (κ * π) * h0 π b₄ t κ ^ 3 = 0 := by
  have h : AdjoinRoot.mk (G0 π b₄ t κ) (X ^ 3 + C (C κ * (C (2 * t) + C (t - π * b₄) * X)) *
      X ^ 2 + C (C κ * (1 + X)) * X - C (C (κ * π) * X ^ 3)) = 0 := AdjoinRoot.mk_self
  simpa only [map_add, map_sub, map_mul, map_pow, map_one, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    of_C] using h

/-- The cubic relation in `T1`. -/
lemma eq1 : w1 π b₄ t κ ^ 3 + algebraMap O _ κ * (algebraMap O _ (2 * t) * h1 π b₄ t κ +
    algebraMap O _ (t - π * b₄)) * w1 π b₄ t κ ^ 2 +
    algebraMap O _ κ * (h1 π b₄ t κ ^ 2 + h1 π b₄ t κ) * w1 π b₄ t κ -
    algebraMap O _ (κ * π) = 0 := by
  have h : AdjoinRoot.mk (G1 π b₄ t κ) (X ^ 3 + C (C κ * (C (2 * t) * X + C (t - π * b₄))) *
      X ^ 2 + C (C κ * (X ^ 2 + X)) * X - C (C (κ * π))) = 0 := AdjoinRoot.mk_self
  simpa only [map_add, map_sub, map_mul, map_pow, map_one, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    of_C] using h

variable {b₆ : O} (hκ : κ * (t ^ 2 - b₆) = 1)

include hκ in
/-- **The equation of the chart `u ≠ 0` in the node coordinates** `s = h' + t w`, `w`:
`w (s² + s − b₆ w²) = π (1 + b₄ w²)`. -/
lemma eqn1 : w1 π b₄ t κ * (s1 π b₄ t κ ^ 2 + s1 π b₄ t κ - algebraMap O _ b₆ * w1 π b₄ t κ ^ 2) =
    algebraMap O _ π * (1 + algebraMap O _ b₄ * w1 π b₄ t κ ^ 2) := by
  have h := eq1 π b₄ t κ
  have hk : algebraMap O (T1 π b₄ t κ) κ * (algebraMap O _ t ^ 2 - algebraMap O _ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  simp only [map_mul, map_sub, map_ofNat] at h ⊢
  linear_combination (algebraMap O (T1 π b₄ t κ) t ^ 2 - algebraMap O _ b₆) * h -
    (w1 π b₄ t κ * ((2 * algebraMap O _ t * h1 π b₄ t κ + algebraMap O _ t -
      algebraMap O _ π * algebraMap O _ b₄) * w1 π b₄ t κ + h1 π b₄ t κ ^ 2 + h1 π b₄ t κ) -
      algebraMap O _ π) * hk

/-! ### The overlap -/

/-- The overlap `T01 = T1[1/h']`. -/
abbrev T01 : Type u := Localization.Away (h1 π b₄ t κ)

/-- `1/h'` in the overlap. -/
abbrev hinv : T01 π b₄ t κ := IsLocalization.Away.invSelf (h1 π b₄ t κ)

/-- `w` in the overlap. -/
abbrev wo : T01 π b₄ t κ := algebraMap (T1 π b₄ t κ) _ (w1 π b₄ t κ)

lemma h1_mul_hinv :
    algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ) * hinv π b₄ t κ = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma eq1_T01 : wo π b₄ t κ ^ 3 + algebraMap O _ κ * (algebraMap O _ (2 * t) *
    algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ) + algebraMap O _ (t - π * b₄)) *
    wo π b₄ t κ ^ 2 + algebraMap O _ κ * (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ)
    (h1 π b₄ t κ) ^ 2 + algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ)) *
    wo π b₄ t κ - algebraMap O _ (κ * π) = 0 := by
  have h := congrArg (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ)) (eq1 π b₄ t κ)
  simpa only [map_add, map_sub, map_mul, map_pow, map_zero,
    ← IsScalarTower.algebraMap_apply] using h

lemma eval_G0_rho : (G0 π b₄ t κ).eval₂
    ((Polynomial.aeval (hinv π b₄ t κ) : O[X] →ₐ[O] T01 π b₄ t κ) : O[X] →+* T01 π b₄ t κ)
    (wo π b₄ t κ * hinv π b₄ t κ) = 0 := by
  have h := eq1_T01 π b₄ t κ
  have hI := h1_mul_hinv π b₄ t κ
  simp only [G0, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, eval₂_one,
    RingHom.coe_coe, map_mul, map_add, map_one, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [map_mul, map_sub, map_ofNat] at h ⊢
  set H := algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ)
  set I := hinv π b₄ t κ
  set w := wo π b₄ t κ
  linear_combination I ^ 3 * h - (2 * algebraMap O _ t * algebraMap O _ κ * w ^ 2 * I ^ 2 +
    algebraMap O _ κ * w * I * (1 + I * H) + algebraMap O _ κ * w * I ^ 2) * hI

/-- **The restriction `ρ₀ : T0 → T01`**: `h ↦ 1/h'`, `z ↦ w/h'`. -/
def rho0 : T0 π b₄ t κ →ₐ[O] T01 π b₄ t κ :=
  AdjoinRoot.liftAlgHom (G0 π b₄ t κ) (Polynomial.aeval (hinv π b₄ t κ))
    (wo π b₄ t κ * hinv π b₄ t κ) (eval_G0_rho π b₄ t κ)

lemma rho0_h0 : rho0 π b₄ t κ (h0 π b₄ t κ) = hinv π b₄ t κ := by
  simp [rho0]

lemma rho0_z0 : rho0 π b₄ t κ (z0 π b₄ t κ) = wo π b₄ t κ * hinv π b₄ t κ := by
  simp [rho0]

/-! ### The inverse map `T1[1/h'] → T0[1/h]` -/

/-- `T0[1/h]`. -/
abbrev T0h : Type u := Localization.Away (h0 π b₄ t κ)

/-- `1/h` in `T0[1/h]`. -/
abbrev jinv : T0h π b₄ t κ := IsLocalization.Away.invSelf (h0 π b₄ t κ)

/-- `z` in `T0[1/h]`. -/
abbrev zo : T0h π b₄ t κ := algebraMap (T0 π b₄ t κ) _ (z0 π b₄ t κ)

lemma h0_mul_jinv :
    algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ) (h0 π b₄ t κ) * jinv π b₄ t κ = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma eq0_T0h : zo π b₄ t κ ^ 3 + algebraMap O _ κ * (algebraMap O _ (2 * t) +
    algebraMap O _ (t - π * b₄) * algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ) (h0 π b₄ t κ)) *
    zo π b₄ t κ ^ 2 + algebraMap O _ κ * (1 + algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ)
    (h0 π b₄ t κ)) * zo π b₄ t κ -
    algebraMap O _ (κ * π) * algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ) (h0 π b₄ t κ) ^ 3 = 0 := by
  have h := congrArg (algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ)) (eq0 π b₄ t κ)
  simpa only [map_add, map_sub, map_mul, map_pow, map_zero, map_one,
    ← IsScalarTower.algebraMap_apply] using h

lemma eval_G1_sigma : (G1 π b₄ t κ).eval₂
    ((Polynomial.aeval (jinv π b₄ t κ) : O[X] →ₐ[O] T0h π b₄ t κ) : O[X] →+* T0h π b₄ t κ)
    (zo π b₄ t κ * jinv π b₄ t κ) = 0 := by
  have h := eq0_T0h π b₄ t κ
  have hJ := h0_mul_jinv π b₄ t κ
  simp only [G1, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    RingHom.coe_coe, map_mul, map_add, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
  simp only [map_mul, map_sub, map_ofNat] at h ⊢
  set H := algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ) (h0 π b₄ t κ)
  set J := jinv π b₄ t κ
  set z := zo π b₄ t κ
  linear_combination J ^ 3 * h - (algebraMap O _ κ * (algebraMap O _ t -
    algebraMap O _ π * algebraMap O _ b₄) * z ^ 2 * J ^ 2 + algebraMap O _ κ * z * J ^ 2 -
    algebraMap O _ κ * algebraMap O _ π * (1 + H * J + H ^ 2 * J ^ 2)) * hJ

/-- `σ : T1 → T0[1/h]`: `h' ↦ 1/h`, `w ↦ z/h`. -/
def sigma1 : T1 π b₄ t κ →ₐ[O] T0h π b₄ t κ :=
  AdjoinRoot.liftAlgHom (G1 π b₄ t κ) (Polynomial.aeval (jinv π b₄ t κ))
    (zo π b₄ t κ * jinv π b₄ t κ) (eval_G1_sigma π b₄ t κ)

lemma sigma1_h1 : sigma1 π b₄ t κ (h1 π b₄ t κ) = jinv π b₄ t κ := by
  simp [sigma1]

lemma sigma1_w1 : sigma1 π b₄ t κ (w1 π b₄ t κ) = zo π b₄ t κ * jinv π b₄ t κ := by
  simp [sigma1]

lemma eq_of_mul_eq_one {S : Type*} [CommRing S] {a x y : S} (hx : a * x = 1) (hy : a * y = 1) :
    x = y := by
  linear_combination y * hx - x * hy

lemma isUnit_rho0_h0 : IsUnit (rho0 π b₄ t κ (h0 π b₄ t κ)) := by
  rw [rho0_h0]
  exact IsUnit.of_mul_eq_one_right _ (h1_mul_hinv π b₄ t κ)

lemma isUnit_sigma1_h1 : IsUnit (sigma1 π b₄ t κ (h1 π b₄ t κ)) := by
  rw [sigma1_h1]
  exact IsUnit.of_mul_eq_one_right _ (h0_mul_jinv π b₄ t κ)

/-- `T0[1/h] → T01` induced by `ρ₀`. -/
def phi : T0h π b₄ t κ →ₐ[O] T01 π b₄ t κ :=
  IsLocalization.Away.liftAlgHom (h0 π b₄ t κ) (isUnit_rho0_h0 π b₄ t κ)

/-- `T01 → T0[1/h]` induced by `σ`. -/
def psi : T01 π b₄ t κ →ₐ[O] T0h π b₄ t κ :=
  IsLocalization.Away.liftAlgHom (h1 π b₄ t κ) (isUnit_sigma1_h1 π b₄ t κ)

lemma phi_algebraMap (a : T0 π b₄ t κ) :
    phi π b₄ t κ (algebraMap _ _ a) = rho0 π b₄ t κ a :=
  IsLocalization.Away.lift_eq _ (isUnit_rho0_h0 π b₄ t κ) a

lemma psi_algebraMap (a : T1 π b₄ t κ) :
    psi π b₄ t κ (algebraMap _ _ a) = sigma1 π b₄ t κ a :=
  IsLocalization.Away.lift_eq _ (isUnit_sigma1_h1 π b₄ t κ) a

lemma phi_jinv : phi π b₄ t κ (jinv π b₄ t κ) =
    algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ) (h1 π b₄ t κ) := by
  refine eq_of_mul_eq_one (a := hinv π b₄ t κ) ?_ ?_
  · have h := congrArg (phi π b₄ t κ) (h0_mul_jinv π b₄ t κ)
    rwa [map_mul, phi_algebraMap, rho0_h0, map_one] at h
  · rw [mul_comm]; exact h1_mul_hinv π b₄ t κ

lemma psi_hinv : psi π b₄ t κ (hinv π b₄ t κ) =
    algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ) (h0 π b₄ t κ) := by
  refine eq_of_mul_eq_one (a := jinv π b₄ t κ) ?_ ?_
  · have h := congrArg (psi π b₄ t κ) (h1_mul_hinv π b₄ t κ)
    rwa [map_mul, psi_algebraMap, sigma1_h1, map_one] at h
  · rw [mul_comm]; exact h0_mul_jinv π b₄ t κ

lemma phi_psi (x : T01 π b₄ t κ) : phi π b₄ t κ (psi π b₄ t κ x) = x := by
  have : (phi π b₄ t κ).comp (psi π b₄ t κ) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (h1 π b₄ t κ))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change phi π b₄ t κ (psi π b₄ t κ (algebraMap _ _ (h1 π b₄ t κ))) =
        algebraMap _ _ (h1 π b₄ t κ)
      rw [psi_algebraMap, sigma1_h1, phi_jinv]
    · change phi π b₄ t κ (psi π b₄ t κ (algebraMap _ _ (w1 π b₄ t κ))) =
        algebraMap _ _ (w1 π b₄ t κ)
      rw [psi_algebraMap, sigma1_w1, map_mul, phi_jinv, phi_algebraMap, rho0_z0, mul_assoc,
        mul_comm (hinv π b₄ t κ), h1_mul_hinv, mul_one]
  exact AlgHom.congr_fun this x

lemma psi_phi (x : T0h π b₄ t κ) : psi π b₄ t κ (phi π b₄ t κ x) = x := by
  have : (psi π b₄ t κ).comp (phi π b₄ t κ) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (h0 π b₄ t κ))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change psi π b₄ t κ (phi π b₄ t κ (algebraMap _ _ (h0 π b₄ t κ))) =
        algebraMap _ _ (h0 π b₄ t κ)
      rw [phi_algebraMap, rho0_h0, psi_hinv]
    · change psi π b₄ t κ (phi π b₄ t κ (algebraMap _ _ (z0 π b₄ t κ))) =
        algebraMap _ _ (z0 π b₄ t κ)
      rw [phi_algebraMap, rho0_z0, map_mul, psi_hinv, psi_algebraMap, sigma1_w1, mul_assoc,
        mul_comm (jinv π b₄ t κ), h0_mul_jinv, mul_one]
  exact AlgHom.congr_fun this x

/-- **The overlap is `T0[1/h]`**: `T0[1/h] ≃ T1[1/h']` (`h ↦ 1/h'`, `z ↦ w/h'`). -/
def overlapEquiv : T0h π b₄ t κ ≃ₐ[O] T01 π b₄ t κ :=
  AlgEquiv.ofAlgHom (phi π b₄ t κ) (psi π b₄ t κ) (AlgHom.ext (phi_psi π b₄ t κ))
    (AlgHom.ext (psi_phi π b₄ t κ))

/-- The unit `T = 1/h'` of the overlap. -/
def uT : (T01 π b₄ t κ)ˣ where
  val := hinv π b₄ t κ
  inv := algebraMap (T1 π b₄ t κ) _ (h1 π b₄ t κ)
  val_inv := by rw [mul_comm]; exact h1_mul_hinv π b₄ t κ
  inv_val := h1_mul_hinv π b₄ t κ

/-- **The Tate model as two-chart rings over `ℙ¹_O`** (`x = h = u/ℓ₀`, `y = h' = ℓ₀/u`). -/
def twoChart : ProjectiveLine.TwoChartRings O where
  R0 := T0 π b₄ t κ
  R1 := T1 π b₄ t κ
  R01 := T01 π b₄ t κ
  x := h0 π b₄ t κ
  y := h1 π b₄ t κ
  u := uT π b₄ t κ
  ρ0 := rho0 π b₄ t κ
  ρ1 := IsScalarTower.toAlgHom O (T1 π b₄ t κ) (T01 π b₄ t κ)
  ρ0_x := rho0_h0 π b₄ t κ
  ρ1_y := rfl
  exists0 z := by
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (h0 π b₄ t κ))
      ((overlapEquiv π b₄ t κ).symm z)
    refine ⟨m, k, ?_⟩
    change (overlapEquiv π b₄ t κ).symm z * algebraMap _ _ (h0 π b₄ t κ ^ k) =
      algebraMap _ _ m at hm
    have h := congrArg (overlapEquiv π b₄ t κ) hm
    simp only [map_mul, map_pow, AlgEquiv.apply_symm_apply] at h
    change z * phi π b₄ t κ (algebraMap _ _ (h0 π b₄ t κ)) ^ k =
      phi π b₄ t κ (algebraMap _ _ m) at h
    rw [phi_algebraMap, phi_algebraMap, rho0_h0] at h
    rw [mul_comm]
    exact h
  ker0 m hm := by
    have h : algebraMap (T0 π b₄ t κ) (T0h π b₄ t κ) m = 0 := by
      apply (overlapEquiv π b₄ t κ).injective
      change phi π b₄ t κ _ = _
      rw [phi_algebraMap, map_zero]
      exact hm
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (h0 π b₄ t κ)) _ m).1 h
    exact ⟨k, hk⟩
  exists1 z := by
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (h1 π b₄ t κ)) z
    refine ⟨m, k, ?_⟩
    change z * algebraMap _ _ (h1 π b₄ t κ ^ k) = algebraMap _ _ m at hm
    change (algebraMap _ _ (h1 π b₄ t κ)) ^ k * z = algebraMap _ _ m
    rw [mul_comm, ← map_pow]
    exact hm
  ker1 m hm := by
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (h1 π b₄ t κ)) _ m).1 hm
    exact ⟨k, hk⟩

end

end TateTwoChart

end SemistableReduction
