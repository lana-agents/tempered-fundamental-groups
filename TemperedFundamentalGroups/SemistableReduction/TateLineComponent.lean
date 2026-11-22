/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TameChart

/-!
# The line component `ℓ = {w = 0}` of the special fibre of the Tate chart `T1`

MR13 step 7, D1 (S4). The special fibre of `T1 = O[h'][w]/(G₁)` is
`k[h', w]/(w · Q̄₁)` (`TateChartReduced.map_G1_eq`); its component `ℓ = {w = 0}` has coordinate
`h'`. We define

* **`TateTwoChart.lineHom`**: `T1 → k[X]`, `h' ↦ X`, `w ↦ 0` (surjective, `lineHom_surjective`),
  and its kernel **`lineIdeal`** `P_ℓ` (the generic point of `ℓ`; `T1/P_ℓ ≃ k[X]`,
  `quotientLineEquiv`);
* **`lineIdeal_mem_minimalPrimes`**: `P_ℓ` is a minimal prime over `ϖ` (if `w ∉ q ⊆ P_ℓ`, then
  `w · Q₁(w) = κπ ∈ q` forces `Q₁(w) ∈ P_ℓ`, but `Q₁(w) ↦ κ̄ (X² + X) ≠ 0`);
* **`pointIdeal`** (the point `h' = 1`, `w = 0` of `ℓ`): a maximal ideal containing `ϖ` with
  `P_ℓ < pointIdeal` (**`lineIdeal_lt_pointIdeal`**) — the input of `CovData.hunr₁`;
* **`isDiscreteValuationRing_lineIdeal`**: `T1` localised at `P_ℓ` is a discrete valuation ring.
-/

open Polynomial

namespace SemistableReduction

namespace TateTwoChart

noncomputable section

variable {O : Type*} [CommRing O] {k : Type*} [Field k] (θ : O →+* k) (π b₄ t κ : O)

lemma eval₂_G1_zero (hπ : θ π = 0) : (G1 π b₄ t κ).eval₂ (mapRingHom θ) 0 = 0 := by
  simp [G1, hπ]

/-- **The line `ℓ = {w = 0}` of the special fibre**: `T1 → k[X]`, `h' ↦ X`, `w ↦ 0`. -/
def lineHom (hπ : θ π = 0) : T1 π b₄ t κ →+* k[X] :=
  AdjoinRoot.lift (mapRingHom θ) 0 (eval₂_G1_zero θ π b₄ t κ hπ)

variable {θ π b₄ t κ} (hπ : θ π = 0)

lemma lineHom_mk (f : O[X][X]) :
    lineHom θ π b₄ t κ hπ (AdjoinRoot.mk _ f) = (f.coeff 0).map θ := by
  rw [lineHom, AdjoinRoot.lift_mk, eval₂_at_zero, coe_mapRingHom]

lemma lineHom_of (p : O[X]) : lineHom θ π b₄ t κ hπ (AdjoinRoot.of _ p) = p.map θ := by
  rw [lineHom, AdjoinRoot.lift_of, coe_mapRingHom]

lemma lineHom_root : lineHom θ π b₄ t κ hπ (AdjoinRoot.root _) = 0 := by
  rw [lineHom, AdjoinRoot.lift_root]

lemma algebraMap_T1_C (o : O) :
    algebraMap O (T1 π b₄ t κ) o = AdjoinRoot.of (G1 π b₄ t κ) (C o) :=
  (of_C _ o).symm

lemma lineHom_algebraMap (o : O) : lineHom θ π b₄ t κ hπ (algebraMap O (T1 π b₄ t κ) o) =
    C (θ o) := by
  rw [algebraMap_T1_C, lineHom_of, Polynomial.map_C]

lemma lineHom_surjective (hθ : Function.Surjective θ) :
    Function.Surjective (lineHom θ π b₄ t κ hπ) := fun g ↦ by
  obtain ⟨p, rfl⟩ := Polynomial.map_surjective θ hθ g
  exact ⟨_, lineHom_of hπ p⟩

/-- **The generic point `P_ℓ` of the line `ℓ`.** -/
def lineIdeal (b₄ t κ : O) : Ideal (T1 π b₄ t κ) := RingHom.ker (lineHom θ π b₄ t κ hπ)

instance lineIdeal_isPrime : (lineIdeal hπ b₄ t κ).IsPrime := RingHom.ker_isPrime _

/-- `T1 / P_ℓ ≃ k[X]`. -/
def quotientLineEquiv (hθ : Function.Surjective θ) : T1 π b₄ t κ ⧸ lineIdeal hπ b₄ t κ ≃+* k[X] :=
  RingHom.quotientKerEquivOfSurjective (lineHom_surjective hπ hθ)

lemma mem_lineIdeal_iff (x : T1 π b₄ t κ) :
    x ∈ lineIdeal hπ b₄ t κ ↔ lineHom θ π b₄ t κ hπ x = 0 := RingHom.mem_ker

variable {ϖ : O}

lemma algebraMap_mem_lineIdeal (hϖ : θ ϖ = 0) :
    algebraMap O (T1 π b₄ t κ) ϖ ∈ lineIdeal hπ b₄ t κ := by
  rw [mem_lineIdeal_iff, lineHom_algebraMap, hϖ, map_zero]

/-- The quadratic factor `Q₁(w) = w² + κ(2t h' + t − π b₄) w + κ(h'² + h')` in `T1`. -/
def q1 : T1 π b₄ t κ :=
  AdjoinRoot.mk (G1 π b₄ t κ)
    (X ^ 2 + C (C κ * (C (2 * t) * X + C (t - π * b₄))) * X + C (C κ * (X ^ 2 + X)))

lemma root_mul_q1 : AdjoinRoot.root (G1 π b₄ t κ) * q1 (π := π) (b₄ := b₄) (t := t) (κ := κ) =
    algebraMap O (T1 π b₄ t κ) (κ * π) := by
  have h : AdjoinRoot.mk (G1 π b₄ t κ) (G1 π b₄ t κ) = 0 := AdjoinRoot.mk_self
  rw [algebraMap_T1_C, q1, ← AdjoinRoot.mk_X, ← map_mul, ← AdjoinRoot.mk_C, ← sub_eq_zero,
    ← map_sub, ← h]
  congr 1
  simp only [G1, C_mul]
  ring

lemma lineHom_q1 : lineHom θ π b₄ t κ hπ (q1 (π := π) (b₄ := b₄) (t := t) (κ := κ)) =
    C (θ κ) * (X ^ 2 + X) := by
  rw [q1, lineHom_mk, coeff_zero_eq_eval_zero]
  simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, zero_add, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]

include hπ in
/-- **`P_ℓ` is a minimal prime over `ϖ`.** -/
theorem lineIdeal_mem_minimalPrimes (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
    (hπϖ : ϖ ∣ π) (hκ : θ κ ≠ 0) :
    lineIdeal hπ b₄ t κ ∈ (Ideal.span {algebraMap O (T1 π b₄ t κ) ϖ}).minimalPrimes := by
  refine ⟨⟨inferInstance, (Ideal.span_singleton_le_iff_mem _).2 (algebraMap_mem_lineIdeal hπ hϖ)⟩,
    fun q ⟨hq, hϖq⟩ hqle ↦ ?_⟩
  have hϖq' : algebraMap O (T1 π b₄ t κ) ϖ ∈ q := (Ideal.span_singleton_le_iff_mem _).1 hϖq
  by_cases hw : AdjoinRoot.root (G1 π b₄ t κ) ∈ q
  · intro x hx
    obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [mem_lineIdeal_iff, lineHom_mk] at hx
    have hdvd : C ϖ ∣ f.coeff 0 := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 fun i ↦ by
      have h := congrArg (fun p ↦ p.coeff i) hx
      simp only [coeff_map, coeff_zero] at h
      exact Ideal.mem_span_singleton.1 (hker (RingHom.mem_ker.2 h))
    obtain ⟨g, hg⟩ := hdvd
    rw [← divX_mul_X_add f, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, hg, map_mul,
      ← algebraMap_T1_C]
    exact q.add_mem (q.mul_mem_left _ hw) (q.mul_mem_right _ hϖq')
  · exfalso
    have hmem : AdjoinRoot.root (G1 π b₄ t κ) * q1 (π := π) (b₄ := b₄) (t := t) (κ := κ) ∈ q := by
      rw [root_mul_q1]
      obtain ⟨c, rfl⟩ := hπϖ
      rw [mul_left_comm, map_mul]
      exact q.mul_mem_right _ hϖq'
    have hq1 := hqle ((hq.mem_or_mem hmem).resolve_left hw)
    rw [mem_lineIdeal_iff, lineHom_q1] at hq1
    have h1 := congrArg (fun p ↦ p.coeff 1) hq1
    exact hκ (by simpa [coeff_X] using h1)

/-- **The point `h' = 1`, `w = 0` of the line `ℓ`**: `T1 → k`. -/
def pointHom (b₄ t κ : O) : T1 π b₄ t κ →+* k :=
  (Polynomial.evalRingHom 1).comp (lineHom θ π b₄ t κ hπ)

/-- The maximal ideal of the point `h' = 1` of `ℓ`. -/
def pointIdeal (b₄ t κ : O) : Ideal (T1 π b₄ t κ) := RingHom.ker (pointHom hπ b₄ t κ)

theorem pointIdeal_isMaximal (hθ : Function.Surjective θ) : (pointIdeal hπ b₄ t κ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _ fun c ↦ by
    obtain ⟨x, hx⟩ := lineHom_surjective hπ hθ (C c)
    exact ⟨x, by simp [pointHom, hx]⟩

lemma algebraMap_mem_pointIdeal (hϖ : θ ϖ = 0) :
    algebraMap O (T1 π b₄ t κ) ϖ ∈ pointIdeal hπ b₄ t κ := by
  simp [pointIdeal, pointHom, lineHom_algebraMap, hϖ]

/-- **`P_ℓ < 𝔪_{h'=1}`.** -/
theorem lineIdeal_lt_pointIdeal : lineIdeal hπ b₄ t κ < pointIdeal hπ b₄ t κ := by
  refine lt_of_le_of_ne (fun x hx ↦ ?_) fun h ↦ ?_
  · simp only [pointIdeal, pointHom, RingHom.mem_ker, RingHom.comp_apply]
    rw [(mem_lineIdeal_iff hπ x).1 hx, map_zero]
  · have hx : AdjoinRoot.of (G1 π b₄ t κ) (X - 1) ∈ pointIdeal hπ b₄ t κ := by
      simp [pointIdeal, pointHom, lineHom_of]
    rw [← h, mem_lineIdeal_iff, lineHom_of] at hx
    have h1 := congrArg (fun p ↦ p.coeff 1) hx
    simp [coeff_X, coeff_one] at h1

variable [IsDomain O] [IsNoetherianRing O] {b₆ : O} (hκ : κ * (t ^ 2 - b₆) = 1)
  [(Ideal.span {ϖ}).IsMaximal] (hπϖ : ϖ ∣ π) (hϖ0 : ϖ ≠ 0)

omit [IsDomain O] [IsNoetherianRing O] [(Ideal.span {ϖ}).IsMaximal] in
include hκ in
lemma θκ_ne_zero : θ κ ≠ 0 := fun h ↦ by
  have := congrArg θ hκ
  rw [map_mul, h, zero_mul, map_one] at this
  exact zero_ne_one this

include hκ hπϖ hϖ0 in
/-- **`T1` at the generic point of `ℓ` is a discrete valuation ring.** -/
theorem isDiscreteValuationRing_lineIdeal (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) :
    haveI := Localization.AtPrime.isDomain_of_isReduced (isSMulRegular_T1 π b₄ t κ hϖ0)
      (isReduced_T1_quot' π b₄ t κ hκ hπϖ)
      (lineIdeal_mem_minimalPrimes hπ hϖ hker hπϖ (θκ_ne_zero hκ))
    IsDiscreteValuationRing (Localization.AtPrime (lineIdeal hπ b₄ t κ)) :=
  isDiscreteValuationRing_T1_atPrime π b₄ t κ hκ hπϖ hϖ0
    (lineIdeal_mem_minimalPrimes hπ hϖ hker hπϖ (θκ_ne_zero hκ))

end

end TateTwoChart

end SemistableReduction
