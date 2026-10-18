/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateLevel
import TemperedFundamentalGroups.SemistableReduction.AwayDvd

/-!
# The overlap of the Tate node patch with the étale piece over `D(w)` (Blueprint §12.8, M2.3 (f))

On the level `QuadNodeTower.Rn n` of the node chart (`uv = ϖᵐ`, `m ≠ 0`, killed by `ϖⁿ⁺¹`) the
node function `f = u + v` divides `u^{2(n+1)}` (**`TateOverlap.fn_dvd`**), and `u` is the image of
the chart coordinate `w ∈ T1` (**`TateOverlap.fn_dvd_w`**). So on `D(w)` the node patch `G n` is
its étale part `P n` localized away from `w` — the divisibility hypothesis of
`EtaleOverlap.isLocalization_ρa` for the glueing of `G n` with the étale piece `E1 n` over `D(w)`.
-/

universe u

namespace SemistableReduction

namespace TateOverlap

open TateTwoChart TateTwoChartNode TateLevel KummerEtale

variable {O : Type u} [CommRing O] {ϖ π b₄ b₆ t κ ε : O} {m : ℕ}

lemma algebraMap_pow_eq_zero (hm : m ≠ 0) (n : ℕ) :
    (algebraMap O (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n) ϖ ^ m) ^ (n + 1) =
      0 := by
  rw [← map_pow, ← map_pow]
  have hmem : (ϖ ^ m) ^ (n + 1) ∈ QuadNodeTower.Iv ϖ n := by
    obtain ⟨m', rfl⟩ := Nat.exists_eq_add_of_le (Nat.one_le_iff_ne_zero.mpr hm)
    rw [show (ϖ ^ (1 + m')) ^ (n + 1) = ϖ ^ (n + 1) * (ϖ ^ m') ^ (n + 1) by ring]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self ϖ) _)
  have h := Ideal.mem_map_of_mem
    (algebraMap O (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n)) hmem
  rwa [QuadNodeTower.kill, Ideal.mem_bot] at h

/-- **On the level-`n` node chart, `f = u + v` divides `u^{2(n+1)}`.** -/
theorem fn_dvd (hm : m ≠ 0) (n : ℕ) :
    QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n ∣
      QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n (uR b₄ b₆ ϖ m ε) ^ (2 * (n + 1)) := by
  have hf : QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n =
      QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n (uR b₄ b₆ ϖ m ε) +
        QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n (vR b₄ b₆ ϖ m ε) := by
    rw [← map_add]
    change QuadNodeTower.mk ϖ ϖ m _ _ n (algebraMap (A ϖ m) _ (fA ϖ)) = _
    rw [fA, map_add]
  rw [hf]
  refine AwayDvd.dvd_pow_of_mul_eq ?_ (algebraMap_pow_eq_zero hm n)
  rw [← map_mul, uR_mul_vR, map_pow]
  rfl

/-- **In terms of the chart coordinate `w ∈ T1`**: `f ∣ w^{2(n+1)}` on the level-`n` node
chart. -/
theorem fn_dvd_w (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hm : m ≠ 0) (n : ℕ) :
    QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n ∣
      toRn b₄ hκ hπ n (Ideal.Quotient.mk _ (w1 π b₄ t κ)) ^ (2 * (n + 1)) := by
  rw [toRn_mk]
  have hw : toNode b₄ hκ hπ (w1 π b₄ t κ) = uR b₄ b₆ ϖ m ε := by
    simp only [toNode, liftT1_w1]
  rw [hw]
  exact fn_dvd hm n

/-- If `f ∣ u^K` and `g = γ u + β f`, then `f ∣ g^K`. -/
lemma dvd_pow_of_eq {R : Type u} [CommRing R] {f u g γ β : R} {K : ℕ} (hu : f ∣ u ^ K)
    (hg : g = γ * u + β * f) : f ∣ g ^ K := by
  have h1 : g - γ * u ∣ g ^ K - (γ * u) ^ K := sub_dvd_pow_sub_pow _ _ K
  have h2 : f ∣ g - γ * u := ⟨β, by rw [hg]; ring⟩
  have h3 : f ∣ (γ * u) ^ K := by rw [mul_pow]; exact dvd_mul_of_dvd_right hu _
  simpa using (dvd_add (h2.trans h1) h3)

/-- **On the level-`n` node chart, `f` divides `(h'(1 + h'))^{2(n+1)}`**, `h' = S − t u` the `ℙ¹`
coordinate: the overlap `D(h(1 + h)) ⊆ V₀` of the second piece over `V₀` with the node chart
misses the nodes. -/
theorem fn_dvd_g (hm : m ≠ 0) (n : ℕ) :
    QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n ∣
      QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n
        ((SR b₄ b₆ ϖ m ε - algebraMap O _ t * uR b₄ b₆ ϖ m ε) *
          (1 + (SR b₄ b₆ ϖ m ε - algebraMap O _ t * uR b₄ b₆ ϖ m ε))) ^ (2 * (n + 1)) := by
  set mk := QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n
  have hf : QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n =
      mk (uR b₄ b₆ ϖ m ε) + mk (vR b₄ b₆ ϖ m ε) := by
    rw [← map_add]
    change mk (algebraMap (A ϖ m) _ (fA ϖ)) = _
    rw [fA, map_add]
  have hS := congrArg mk (SR_sq b₄ b₆ ϖ m ε)
  rw [algebraMap_cN] at hS
  simp only [map_add, map_mul, map_pow, map_one] at hS
  refine dvd_pow_of_eq (fn_dvd hm n)
    (γ := -(mk (algebraMap O _ ε) * (1 + mk (algebraMap O _ b₄) * mk (uR b₄ b₆ ϖ m ε) ^ 2)) +
      mk (algebraMap O _ b₆) * mk (uR b₄ b₆ ϖ m ε) -
      mk (algebraMap O _ t) * (1 + 2 * mk (SR b₄ b₆ ϖ m ε)) +
      mk (algebraMap O _ t) ^ 2 * mk (uR b₄ b₆ ϖ m ε))
    (β := mk (algebraMap O _ ε) * (1 + mk (algebraMap O _ b₄) * mk (uR b₄ b₆ ϖ m ε) ^ 2)) ?_
  rw [hf]
  simp only [map_add, map_mul, map_sub, map_one]
  linear_combination hS

end TateOverlap

end SemistableReduction
