/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateNodeGerm

/-!
# The Tate chart near the nodes is quadratic over the node ring: the conjugation argument

(Blueprint §12.8, M2.3 (a').) In the chart `x₀ ≠ 0` of the Tate model (`s = x₁/x₀`, `w = x₂/x₀`,
equation `w (s (s + 1) − b₆ w²) = π (1 + b₄ w²)`, `TateNormal.chart_zero_eq`) the node coordinates
`u = w`, `v = (s (s + 1) − b₆ w²) / ((1 + b₄ w²) ε)` (`TateNormal.nodeGerm_chart_zero`) lie in the
subfield `K(a)` of the function field `L = K(a, b)`, and `s` satisfies the quadratic equation
`s² + s = ε (1 + b₄ w²) v + b₆ w²` over them. The plan (see the M2.3 row of the Blueprint) is to
present the localized chart as `A_D[S]/(S² + S − c)` over the node ring `A = O[u,v]/(uv − ϖⁿ)`,
standard étale where `2s + 1` is invertible, i.e. near both nodes `p` (`s = 0`) and `q` (`s = −1`).

This file provides the injectivity ingredient: the conjugation `b ↦ −a − b` of `L`
(`TateNormal.conjL`, an `O[X]`-algebra map) fixes `w` and `v` (`conjL_wL`, `conjL_vL`) and sends
`s ↦ −1 − s` (`conjL_sL`), and `2s + 1 ≠ 0` (`two_sL_add_one_ne_zero`: `(2b + a)² = d(a) ≠ 0`).
Hence **`TateNormal.eq_zero_of_add_mul_sL_eq_zero`**: if `x + y s = 0` with `x`, `y` fixed by the
conjugation (e.g. in the image of the node ring), then `x = y = 0`. With the node ring mapped to
`L` by `TateNormal.nodeToL` (`u ↦ w`, `v ↦ v`, `uv = ϖⁿ` by `wL_mul_vL`):
`eq_zero_of_nodeToL_add_mul_sL_eq_zero` (`1, s` are independent over the node ring) and
**`TateNormal.sL_sq_add_sL`** (`s² + s = c := ε (1 + b₄ u²) v + b₆ u²` over the node ring), so
`A[S]/(S² + S − c) → L`, `S ↦ s`, is injective; with `QuadraticEtale.etale` its localization at
`2S + 1` is étale over `A`. Not yet done: its image is the chart localized at `1 + b₄ w²`.
-/

universe u

open Polynomial

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "L" => TateField π b₄ b₆

attribute [local instance] algK

lemma conjL_aL : conjL π b₄ b₆ (aL π b₄ b₆) = aL π b₄ b₆ := (conjL π b₄ b₆).commutes X

lemma conjL_bL : conjL π b₄ b₆ (bL π b₄ b₆) = -aL π b₄ b₆ - bL π b₄ b₆ := by
  change conjR π b₄ b₆ (algebraMap _ _ (bA π b₄ b₆)) = _
  rw [conjR_algebraMap, conj_root, map_sub, map_neg, algebraMap_of]

lemma conjL_algebraMap_O (o : O) : conjL π b₄ b₆ (algebraMap O L o) = algebraMap O L o := by
  rw [algebraMap_O_apply]
  exact (conjL π b₄ b₆).commutes _

/-- The conjugation sends `s ↦ −1 − s`. -/
lemma conjL_sL : conjL π b₄ b₆ (sL π b₄ b₆) = -1 - sL π b₄ b₆ := by
  have ha : aL π b₄ b₆ ≠ 0 := aL_ne_zero π b₄ b₆
  change conjL π b₄ b₆ (bL π b₄ b₆ / aL π b₄ b₆) = -1 - bL π b₄ b₆ / aL π b₄ b₆
  rw [map_div₀, conjL_bL, conjL_aL]
  field_simp

/-- The conjugation fixes `w = 1/a`. -/
lemma conjL_wL : conjL π b₄ b₆ (wL π b₄ b₆) = wL π b₄ b₆ := by
  rw [wL_eq, map_inv₀, conjL_aL]

/-- The conjugation fixes `s (s + 1)`. -/
lemma conjL_sL_mul : conjL π b₄ b₆ (sL π b₄ b₆ * (sL π b₄ b₆ + 1)) =
    sL π b₄ b₆ * (sL π b₄ b₆ + 1) := by
  rw [map_mul, map_add, map_one, conjL_sL]
  ring

/-- The conjugation fixes the node coordinate `v`. -/
lemma conjL_vL (ε : O) : conjL π b₄ b₆ (vL (π := π) (b₄ := b₄) (b₆ := b₆) ε) =
    vL (π := π) (b₄ := b₄) (b₆ := b₆) ε := by
  have hs := conjL_sL_mul π b₄ b₆
  have hw := conjL_wL π b₄ b₆
  simp only [vL]
  set S := sL π b₄ b₆ * (sL π b₄ b₆ + 1)
  set w := wL π b₄ b₆
  rw [map_div₀, map_mul, map_sub, hs, map_mul, map_pow, hw, map_add, map_one, map_mul, map_pow, hw,
    conjL_algebraMap_O, conjL_algebraMap_O, conjL_algebraMap_O]

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- `(2b + a)² = d(a)`. -/
lemma two_bL_add_aL_sq : (2 * bL π b₄ b₆ + aL π b₄ b₆) ^ 2 =
    algebraMap O[X] L (dpoly π b₄ b₆) := by
  have h := bL_sq π b₄ b₆
  have hd : algebraMap O[X] L (dpoly π b₄ b₆) =
      aL π b₄ b₆ ^ 2 + 4 * algebraMap O[X] L (cpoly π b₄ b₆) := by
    simp only [dpoly, map_add, map_pow, map_mul, map_ofNat, aL]
  rw [hd]
  linear_combination 4 * h

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma dpoly_ne_zero : dpoly π b₄ b₆ ≠ 0 := fun h ↦ by
  have := dpoly_coeff_two π b₄ b₆
  rw [h, coeff_zero] at this
  exact zero_ne_one this

/-- `2s + 1 ≠ 0`. -/
lemma two_sL_add_one_ne_zero : 2 * sL π b₄ b₆ + 1 ≠ 0 := by
  have ha : aL π b₄ b₆ ≠ 0 := aL_ne_zero π b₄ b₆
  have hd : algebraMap O[X] L (dpoly π b₄ b₆) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap_injective π b₄ b₆)]
    exact dpoly_ne_zero π b₄ b₆
  have h2 : 2 * bL π b₄ b₆ + aL π b₄ b₆ ≠ 0 := fun h ↦ hd (by
    rw [← two_bL_add_aL_sq, h, zero_pow two_ne_zero])
  change 2 * (bL π b₄ b₆ / aL π b₄ b₆) + 1 ≠ 0
  rw [show 2 * (bL π b₄ b₆ / aL π b₄ b₆) + 1 = (2 * bL π b₄ b₆ + aL π b₄ b₆) / aL π b₄ b₆ by
    field_simp]
  exact div_ne_zero h2 ha

/-- **The conjugation argument**: `x + y s = 0` with `x`, `y` fixed by the conjugation forces
`x = y = 0` (`s` has degree two over the fixed field). -/
theorem eq_zero_of_add_mul_sL_eq_zero {x y : L} (hx : conjL π b₄ b₆ x = x)
    (hy : conjL π b₄ b₆ y = y) (h : x + y * sL π b₄ b₆ = 0) : x = 0 ∧ y = 0 := by
  have h' := congrArg (conjL π b₄ b₆) h
  rw [map_add, map_mul, hx, hy, conjL_sL, map_zero] at h'
  have hy0 : y * (2 * sL π b₄ b₆ + 1) = 0 := by linear_combination h - h'
  have hy0' : y = 0 := (mul_eq_zero.mp hy0).resolve_right (two_sL_add_one_ne_zero π b₄ b₆)
  refine ⟨?_, hy0'⟩
  rw [hy0', zero_mul, add_zero] at h
  exact h

/-! ### The node ring in the function field -/

/-- `1 + b₄ w² ≠ 0` (`w` is transcendental over `K`). -/
lemma one_add_b₄_wL_sq_ne_zero : 1 + algebraMap O L b₄ * wL π b₄ b₆ ^ 2 ≠ 0 := by
  intro h
  apply transcendental_wL π b₄ b₆
  refine ⟨1 + Polynomial.C (b₄ : K) * Polynomial.X ^ 2, fun h0 ↦ ?_, ?_⟩
  · have := congrArg (Polynomial.coeff · 0) h0
    simp at this
  · rw [← wL_eq]
    simp only [map_add, map_one, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
      algebraMap_K_coe]
    exact h

variable {π} in
/-- `u v = ϖⁿ` for the node coordinates `u = w`, `v = (s (s + 1) − b₆ w²) / ((1 + b₄ w²) ε)`. -/
lemma wL_mul_vL {ϖ : O} {ε : Oˣ} {n : ℕ} (hπε : π = ε * ϖ ^ n) :
    wL π b₄ b₆ * vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) = algebraMap O L (ϖ ^ n) := by
  have heq := chart_zero_eq π b₄ b₆
  have hD := one_add_b₄_wL_sq_ne_zero π b₄ b₆
  have hε : algebraMap O L (ε : O) ≠ 0 := by
    rw [← algebraMap_K_coe]
    refine (map_ne_zero (algebraMap K L)).mpr fun h ↦ ε.ne_zero (Subtype.ext h)
  have hπ' : algebraMap O L π = algebraMap O L (ε : O) * algebraMap O L ϖ ^ n := by
    rw [← map_pow, ← map_mul]; exact congrArg _ hπε
  rw [vL, mul_div_assoc', heq, hπ', map_pow, div_eq_iff (mul_ne_zero hD hε)]
  ring

variable {π} in
/-- **The node ring `O[u, v]/(uv − ϖⁿ)` in the function field** (`u ↦ w`, `v ↦ v`). -/
def nodeToL {ϖ : O} {ε : Oˣ} {n : ℕ} (hπε : π = ε * ϖ ^ n) :
    SemistableReduction.Node O (ϖ ^ n) →ₐ[O] L :=
  SemistableReduction.Node.lift (wL π b₄ b₆) (vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O))
    (wL_mul_vL b₄ b₆ hπε)

variable {π} in
/-- The conjugation fixes the image of the node ring. -/
lemma conjL_nodeToL {ϖ : O} {ε : Oˣ} {n : ℕ} (hπε : π = ε * ϖ ^ n)
    (x : SemistableReduction.Node O (ϖ ^ n)) :
    conjL π b₄ b₆ (nodeToL b₄ b₆ hπε x) = nodeToL b₄ b₆ hπε x := by
  have : ((conjL π b₄ b₆).restrictScalars O).comp (nodeToL b₄ b₆ hπε) = nodeToL b₄ b₆ hπε := by
    refine SemistableReduction.Node.algHom_ext ?_ ?_
    · simp only [nodeToL, AlgHom.comp_apply, SemistableReduction.Node.lift_u,
        AlgHom.restrictScalars_apply, conjL_wL]
    · simp only [nodeToL, AlgHom.comp_apply, SemistableReduction.Node.lift_v,
        AlgHom.restrictScalars_apply, conjL_vL]
  exact AlgHom.congr_fun this x

variable {π} in
/-- **`1, s` are linearly independent over the node ring** (in the function field): the
injectivity of `A[S]/(S² + S − c) → L`, `S ↦ s`. -/
theorem eq_zero_of_nodeToL_add_mul_sL_eq_zero {ϖ : O} {ε : Oˣ} {n : ℕ} (hπε : π = ε * ϖ ^ n)
    {x y : SemistableReduction.Node O (ϖ ^ n)}
    (h : nodeToL b₄ b₆ hπε x + nodeToL b₄ b₆ hπε y * sL π b₄ b₆ = 0) :
    nodeToL b₄ b₆ hπε x = 0 ∧ nodeToL b₄ b₆ hπε y = 0 :=
  eq_zero_of_add_mul_sL_eq_zero π b₄ b₆ (conjL_nodeToL b₄ b₆ hπε x) (conjL_nodeToL b₄ b₆ hπε y) h

variable {π} in
/-- **`s` is a root of `S² + S − c` over the node ring**, `c = ε (1 + b₄ u²) v + b₆ u²`
(`QuadraticEtale.poly`). -/
theorem sL_sq_add_sL {ϖ : O} {ε : Oˣ} {n : ℕ} (hπε : π = ε * ϖ ^ n) :
    sL π b₄ b₆ ^ 2 + sL π b₄ b₆ = nodeToL b₄ b₆ hπε
      (algebraMap O _ (ε : O) * (1 + algebraMap O _ b₄ * SemistableReduction.Node.u (ϖ ^ n) ^ 2) *
          SemistableReduction.Node.v (ϖ ^ n) +
        algebraMap O _ b₆ * SemistableReduction.Node.u (ϖ ^ n) ^ 2) := by
  have hD := one_add_b₄_wL_sq_ne_zero π b₄ b₆
  have hε : algebraMap O L (ε : O) ≠ 0 := by
    rw [← algebraMap_K_coe]
    refine (map_ne_zero (algebraMap K L)).mpr fun h ↦ ε.ne_zero (Subtype.ext h)
  have hu : nodeToL b₄ b₆ hπε (SemistableReduction.Node.u (ϖ ^ n)) = wL π b₄ b₆ :=
    SemistableReduction.Node.lift_u ..
  have hv : nodeToL b₄ b₆ hπε (SemistableReduction.Node.v (ϖ ^ n)) =
      vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) :=
    SemistableReduction.Node.lift_v ..
  have key : vL (π := π) (b₄ := b₄) (b₆ := b₆) (ε : O) *
      ((1 + algebraMap O L b₄ * wL π b₄ b₆ ^ 2) * algebraMap O L (ε : O)) =
      sL π b₄ b₆ * (sL π b₄ b₆ + 1) - algebraMap O L b₆ * wL π b₄ b₆ ^ 2 :=
    div_mul_cancel₀ _ (mul_ne_zero hD hε)
  simp only [map_add, map_mul, map_one, map_pow, AlgHom.commutes, hu, hv]
  linear_combination -key

end

end TemperedFundamentalGroups.TateNormal
