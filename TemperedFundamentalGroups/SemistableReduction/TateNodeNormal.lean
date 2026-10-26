/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerTateChartDomain
import TemperedFundamentalGroups.SemistableReduction.KummerEtaleChart
import TemperedFundamentalGroups.SemistableReduction.TateGenericFibre
import Mathlib.RingTheory.Regular.Flat

/-!
# The quadratic node chart of the Tate model is integrally closed (MR12 T2 S4, Tate chart)

Let `O` be a discrete valuation ring with uniformizer `ϖ`, `m ≥ 1`, `ε ∈ Oˣ`, and
`NR = (A[S]/(S² + S − c))[1/D]` the quadratic node chart of the Tate model over the node ring
`A = O[u,v]/(uv − ϖᵐ)` (`c = ε (1 + b₄ u²) v + b₆ u²`, `D = 1 + b₄ u²`). Assume `3 ≠ 0` in `O`
and `E = tateE (ε ϖᵐ) b₄ b₆ ≠ 0` (the generic fibre is smooth).

**`TateTwoChartNode.isIntegrallyClosed_NR`**: `NR` is integrally closed.

## Proof

* **Gluing criterion** (`TateNodeNormal.isIntegrallyClosed_of_away_of_regular`): a domain `R`
  is integrally closed if `R[1/s]` and `R[1/t]` are, `s, t ≠ 0`, and `t` is regular modulo `s`
  (`t r ∈ (s) → r ∈ (s)`): an integral `x` of the fraction field is `r₁/sⁱ = r₂/tʲ`, so
  `tʲ r₁ ∈ (sⁱ)`, hence `r₁ ∈ (sⁱ)` and `x ∈ R`.
* `s = ϖ`, `t = 2S + 1`:
  - `NR[1/(2S+1)] = NE` is étale over the integrally closed node ring `A` and a domain, hence
    integrally closed (`isIntegrallyClosed_of_etale`);
  - `NR[1/ϖ] ≅ T1[1/D][1/ϖ] ≅ T1[1/ϖ][1/D]` (`chartEquiv`, for any `t, κ` with
    `κ (t² − b₆) = 1`, which exist in a local ring) is a localization of the Dedekind domain
    `T1[1/ϖ]` (`TateTwoChart.isDedekindDomain_away_T1_of_dvr`, this needs `3 ≠ 0`, `E ≠ 0`);
  - `(2S + 1)² = Δ = 1 + 4c ∈ A`, and `[ϖ, Δ]` is a weakly regular sequence in `A`: modulo
    `(ϖ, u)` resp. `(ϖ, v)` the element `Δ` becomes `1 + 4 ε̄ v ≠ 0` in `k[v]` resp.
    `1 + 4 b̄₆ u² ≠ 0` in `k[u]`, and `(ϖ) = ker (A → k[v]) ∩ ker (A → k[u])`
    (`mem_span_of_toPoly`, using `uv = ϖᵐ`). By flatness of `NR` over `A`
    (`IsWeaklyRegular.of_flat`), `Δ`, hence `2S + 1`, is regular modulo `ϖ` on `NR`.
-/

universe u

open Polynomial TemperedFundamentalGroups
open scoped nonZeroDivisors Pointwise

namespace SemistableReduction

namespace TateNodeNormal

variable {R : Type*} [CommRing R] [IsDomain R]

/-- If a localization `S = M⁻¹ R` (`M` without zero) is integrally closed, every element of the
fraction field integral over `R` has a multiple by an element of `M` in `R`. -/
lemma exists_mul_eq_of_isLocalization (M : Submonoid R) (hM : M ≤ R⁰) (S : Type*) [CommRing S]
    [Algebra R S] [IsLocalization M S] [IsIntegrallyClosed S] {x : FractionRing R}
    (hx : IsIntegral R x) : ∃ m ∈ M, ∃ r : R, algebraMap R _ m * x = algebraMap R _ r := by
  let K := FractionRing R
  let g : S →+* K := IsLocalization.map _ (T := R⁰) (RingHom.id R) hM
  letI := g.toAlgebra
  have : IsScalarTower R S K := IsScalarTower.of_algebraMap_eq'
    (by rw [RingHom.algebraMap_toAlgebra, IsLocalization.map_comp, RingHomCompTriple.comp_eq])
  have := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M S K
  obtain ⟨y, hy⟩ := (isIntegrallyClosed_iff K).mp ‹_› (hx.tower_top (A := S))
  obtain ⟨⟨r, m⟩, rfl⟩ := IsLocalization.mk'_surjective M y
  refine ⟨m, m.2, r, ?_⟩
  rw [← hy, RingHom.algebraMap_toAlgebra]
  simp only [g, IsLocalization.map_mk', RingHom.id_apply]
  rw [IsLocalization.mul_mk'_eq_mk'_of_mul, IsLocalization.mk'_eq_iff_eq_mul, map_mul]
  exact mul_comm _ _

/-- **A domain is integrally closed if `R[1/s]`, `R[1/t]` are and `t` is regular modulo `s`.** -/
theorem isIntegrallyClosed_of_away_of_regular {s t : R} (hs : s ≠ 0) (ht : t ≠ 0) (R₁ R₂ : Type*)
    [CommRing R₁] [CommRing R₂] [Algebra R R₁] [Algebra R R₂] [IsLocalization.Away s R₁]
    [IsLocalization.Away t R₂] [IsIntegrallyClosed R₁] [IsIntegrallyClosed R₂]
    (hreg : ∀ r : R, t * r ∈ Ideal.span {s} → r ∈ Ideal.span {s}) : IsIntegrallyClosed R := by
  have hreg' : ∀ (j : ℕ) (r : R), t ^ j * r ∈ Ideal.span {s} → r ∈ Ideal.span {s} := by
    intro j
    induction j with
    | zero => intro r h; simpa using h
    | succ j ih => intro r h; exact ih r (hreg _ (by rw [pow_succ', mul_assoc] at h; exact h))
  have hreg'' : ∀ (i j : ℕ) (r : R), t ^ j * r ∈ Ideal.span {s ^ i} →
      r ∈ Ideal.span {s ^ i} := by
    intro i
    induction i with
    | zero => intro j r _; simp
    | succ i ih =>
      intro j r h
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
      have h1 : r ∈ Ideal.span {s} := hreg' j r (Ideal.mem_span_singleton'.mpr
        ⟨y * s ^ i, by rw [← hy, pow_succ]; ring⟩)
      obtain ⟨r', rfl⟩ := Ideal.mem_span_singleton'.mp h1
      have h2 : t ^ j * r' = y * s ^ i := by
        apply mul_right_cancel₀ hs
        rw [pow_succ] at hy
        linear_combination -hy
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp
        (ih j r' (Ideal.mem_span_singleton'.mpr ⟨y, h2.symm⟩))
      exact Ideal.mem_span_singleton'.mpr ⟨z, by rw [← hz, pow_succ]; ring⟩
  rw [isIntegrallyClosed_iff (FractionRing R)]
  intro x hx
  obtain ⟨_, ⟨i, rfl⟩, r₁, h₁⟩ := exists_mul_eq_of_isLocalization (Submonoid.powers s)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hs) R₁ hx
  obtain ⟨_, ⟨j, rfl⟩, r₂, h₂⟩ := exists_mul_eq_of_isLocalization (Submonoid.powers t)
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht) R₂ hx
  have h : t ^ j * r₁ = s ^ i * r₂ := by
    apply IsFractionRing.injective R (FractionRing R)
    simp only [map_mul, map_pow] at h₁ h₂ ⊢
    rw [← h₁, ← h₂]
    ring
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.mp
    (hreg'' i j r₁ (Ideal.mem_span_singleton'.mpr ⟨r₂, by rw [h]; ring⟩))
  refine ⟨z, ?_⟩
  have hs' : algebraMap R (FractionRing R) (s ^ i) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R _)).mpr (pow_ne_zero i hs)
  apply mul_left_cancel₀ hs'
  rw [h₁, ← hz, map_mul]
  ring

end TateNodeNormal

namespace TateTwoChartNode

open KummerEtale TateTwoChart TateNodeNormal

noncomputable section

variable {O : Type u} [CommRing O] {ϖ : O} {m : ℕ}

/-! ### The node ring modulo `ϖ` -/

variable (ϖ m) in
/-- The swap `u ↔ v` of the node ring. -/
def swapN : A ϖ m →ₐ[O] A ϖ m :=
  Node.lift (Node.v (ϖ ^ m)) (Node.u (ϖ ^ m)) (by rw [mul_comm, Node.u_mul_v])

@[simp] lemma swapN_u : swapN ϖ m (Node.u _) = Node.v _ := Node.lift_u ..

@[simp] lemma swapN_v : swapN ϖ m (Node.v _) = Node.u _ := Node.lift_v ..

lemma swapN_swapN (a : A ϖ m) : swapN ϖ m (swapN ϖ m a) = a := by
  have : (swapN ϖ m).comp (swapN ϖ m) = AlgHom.id O _ :=
    Node.algHom_ext (by simp) (by simp)
  exact AlgHom.congr_fun this a

/-- The map `A → (O ⧸ ϖ)[u]`, `v ↦ 0`. -/
def toPolyV (hm : 1 ≤ m) : A ϖ m →ₐ[O] (O ⧸ Ideal.span {ϖ})[X] :=
  (Node.toPolyU ϖ hm).comp (swapN ϖ m)

lemma toPolyV_u (hm : 1 ≤ m) : toPolyV hm (Node.u (ϖ ^ m)) = X := by
  simp [toPolyV, Node.toPolyU_v]

lemma toPolyV_v (hm : 1 ≤ m) : toPolyV hm (Node.v (ϖ ^ m)) = 0 := by
  simp [toPolyV, Node.toPolyU_u]

lemma toPolyU_ϖ (hm : 1 ≤ m) : Node.toPolyU ϖ hm (algebraMap O (A ϖ m) ϖ) = 0 := by
  rw [AlgHom.commutes, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self ϖ), map_zero]

lemma toPolyV_ϖ (hm : 1 ≤ m) : toPolyV hm (algebraMap O (A ϖ m) ϖ) = 0 := by
  rw [AlgHom.commutes, ← AlgHom.commutes (Node.toPolyU ϖ hm), toPolyU_ϖ]

lemma mem_idealU_of_toPolyU (hm : 1 ≤ m) {a : A ϖ m} (h : Node.toPolyU ϖ hm a = 0) :
    a ∈ Node.idealU (n := m) ϖ := by
  have h' : Node.quotUEquiv ϖ hm (Ideal.Quotient.mk _ a) = 0 := h
  rwa [map_eq_zero_iff _ (Node.quotUEquiv ϖ hm).injective, Ideal.Quotient.eq_zero_iff_mem] at h'

lemma algebraMap_pow_eq (hm : 1 ≤ m) : algebraMap O (A ϖ m) (ϖ ^ m) =
    algebraMap O (A ϖ m) ϖ * algebraMap O (A ϖ m) ϖ ^ (m - 1) := by
  simp only [map_pow]
  rw [← pow_succ', Nat.sub_add_cancel hm]

/-- **`(ϖ) = ker (A → k[v]) ∩ ker (A → k[u])`** in the node ring. -/
lemma mem_span_of_toPoly (hϖ : Prime ϖ) (hm : 1 ≤ m) {a : A ϖ m} (hU : Node.toPolyU ϖ hm a = 0)
    (hV : toPolyV hm a = 0) : a ∈ Ideal.span {algebraMap O (A ϖ m) ϖ} := by
  haveI := isDomain_quot hϖ
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.mp (mem_idealU_of_toPolyU hm hU)
  have hq : toPolyV hm q = 0 := by
    rw [map_add, map_mul, map_mul, toPolyV_ϖ, toPolyV_u, mul_zero, zero_add] at hV
    exact (mul_eq_zero.mp hV).resolve_right X_ne_zero
  obtain ⟨p', q', hpq⟩ := Ideal.mem_span_pair.mp (mem_idealU_of_toPolyU hm hq)
  have hpq' : swapN ϖ m q = p' * algebraMap O (A ϖ m) ϖ + q' * Node.u (ϖ ^ m) := hpq.symm
  have hq' : q = swapN ϖ m p' * algebraMap O (A ϖ m) ϖ + swapN ϖ m q' * Node.v (ϖ ^ m) := by
    rw [← swapN_swapN q, hpq', map_add, map_mul, map_mul, AlgHom.commutes, swapN_u]
  have huv := (Node.u_mul_v (ϖ ^ m)).trans (algebraMap_pow_eq hm)
  refine Ideal.mem_span_singleton'.mpr
    ⟨p + swapN ϖ m p' * Node.u _ + swapN ϖ m q' * algebraMap O (A ϖ m) ϖ ^ (m - 1), ?_⟩
  rw [hq']
  linear_combination (-swapN ϖ m q') * huv

lemma toPolyV_cN (b₄ b₆ ε : O) (hm : 1 ≤ m) :
    toPolyV hm (cN b₄ b₆ ϖ m ε) = C (Ideal.Quotient.mk (Ideal.span {ϖ}) b₆) * X ^ 2 := by
  simp only [toPolyV, AlgHom.comp_apply, cN, map_add, map_mul, map_pow, map_one,
    AlgHom.commutes, swapN_u, swapN_v, Node.toPolyU_u, Node.toPolyU_v,
    Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  ring

lemma one_add_four_C_mul_ne_zero {k : Type*} [CommRing k] [Nontrivial k] (a : k) (n : ℕ)
    (hn : n ≠ 0) : (1 + 4 * (C a * X ^ n) : k[X]) ≠ 0 := by
  intro h
  have := congrArg (coeff · 0) h
  simp [coeff_X_pow, Ne.symm hn] at this

variable [IsDomain O]

lemma algebraMap_ϖ_ne_zero (hϖ : Prime ϖ) (hm : 1 ≤ m) : algebraMap O (A ϖ m) ϖ ≠ 0 := by
  haveI := isDomain_quot hϖ
  haveI : IsDomain (A ϖ m) := Node.isDomain (pow_ne_zero m hϖ.ne_zero)
  intro h
  have huv := (Node.u_mul_v (ϖ ^ m)).trans (algebraMap_pow_eq hm)
  rw [h, zero_mul] at huv
  rcases mul_eq_zero.mp huv with hu | hv
  · have := congrArg (toPolyV hm) hu
    rw [toPolyV_u, map_zero] at this
    exact X_ne_zero this
  · have := congrArg (Node.toPolyU ϖ hm) hv
    rw [Node.toPolyU_v, map_zero] at this
    exact X_ne_zero this

omit [IsDomain O] in
/-- **`Δ = 1 + 4c` is regular modulo `ϖ` on the node ring.** -/
lemma mem_span_of_Δ_mul (b₄ b₆ : O) {ε : O} (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε)
    {a : A ϖ m} (h : (1 + 4 * cN b₄ b₆ ϖ m ε) * a ∈ Ideal.span {algebraMap O (A ϖ m) ϖ}) :
    a ∈ Ideal.span {algebraMap O (A ϖ m) ϖ} := by
  haveI := isDomain_quot hϖ
  have hε0 : Ideal.Quotient.mk (Ideal.span {ϖ}) ε ≠ 0 := (hε.map _).ne_zero
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp h
  refine mem_span_of_toPoly hϖ hm ?_ ?_
  · have := congrArg (Node.toPolyU ϖ hm) hy
    rw [map_mul, map_mul, toPolyU_ϖ, mul_zero, map_add, map_one, map_mul, map_ofNat,
      toPolyU_cN] at this
    have h1 := one_add_four_C_mul_ne_zero (Ideal.Quotient.mk (Ideal.span {ϖ}) ε) 1 one_ne_zero
    rw [pow_one] at h1
    exact (mul_eq_zero.mp this.symm).resolve_left h1
  · have := congrArg (toPolyV hm) hy
    rw [map_mul, map_mul, toPolyV_ϖ, mul_zero, map_add, map_one, map_mul, map_ofNat,
      toPolyV_cN] at this
    exact (mul_eq_zero.mp this.symm).resolve_left
      (one_add_four_C_mul_ne_zero _ 2 two_ne_zero)

lemma mem_smul_top_iff_mem_span {R : Type*} [CommRing R] (r x : R) :
    x ∈ r • (⊤ : Submodule R R) ↔ x ∈ Ideal.span {r} := by
  rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton']
  simp [smul_eq_mul, mul_comm]

/-! ### Regularity of `2S + 1` modulo `ϖ` on the node chart -/

/-- `[ϖ, Δ]` is weakly regular on the node ring. -/
lemma isWeaklyRegular_A (b₄ b₆ : O) {ε : O} (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) :
    RingTheory.Sequence.IsWeaklyRegular (A ϖ m)
      [algebraMap O (A ϖ m) ϖ, 1 + 4 * cN b₄ b₆ ϖ m ε] := by
  haveI : IsDomain (A ϖ m) := Node.isDomain (pow_ne_zero m hϖ.ne_zero)
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  refine ⟨IsSMulRegular.of_ne_zero (algebraMap_ϖ_ne_zero hϖ hm), ?_⟩
  rw [isSMulRegular_iff_right_eq_zero_of_smul]
  intro x hx
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
    mem_smul_top_iff_mem_span, smul_eq_mul] at hx
  rw [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_mem_span]
  exact mem_span_of_Δ_mul b₄ b₆ hϖ hm hε hx

set_option maxHeartbeats 1000000 in
-- Many localization structures on the concrete charts.
/-- **`[ϖ, Δ]` is weakly regular on the node chart** (flat over `A`). -/
lemma isSMulRegular_NR (b₄ b₆ : O) {ε : O} (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) :
    IsSMulRegular (NR b₄ b₆ ϖ m ε) (algebraMap O (NR b₄ b₆ ϖ m ε) ϖ) ∧
      IsSMulRegular (QuotSMulTop (algebraMap O (NR b₄ b₆ ϖ m ε) ϖ) (NR b₄ b₆ ϖ m ε))
        (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (1 + 4 * cN b₄ b₆ ϖ m ε)) := by
  have hN := (isWeaklyRegular_A b₄ b₆ hϖ hm hε).of_flat (S := NR b₄ b₆ ϖ m ε)
  have e : algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (algebraMap O (A ϖ m) ϖ) =
      algebraMap O (NR b₄ b₆ ϖ m ε) ϖ :=
    (IsScalarTower.algebraMap_apply O (A ϖ m) (NR b₄ b₆ ϖ m ε) ϖ).symm
  rw [List.map_cons, List.map_cons, List.map_nil, e,
    RingTheory.Sequence.isWeaklyRegular_cons_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hN
  exact hN

variable {b₄ b₆ : O} {ε : O}

lemma algebraMap_ϖ_NR_ne_zero [IsIntegrallyClosed O] (hϖ : Prime ϖ) (hm : 1 ≤ m)
    (hε : IsUnit ε) : algebraMap O (NR b₄ b₆ ϖ m ε) ϖ ≠ 0 := by
  haveI := isDomain_NR b₄ b₆ hϖ hm hε
  intro h0
  have h := (isSMulRegular_NR b₄ b₆ hϖ hm hε).1
  rw [h0] at h
  have := h.right_eq_zero_of_smul (x := (1 : NR b₄ b₆ ϖ m ε)) (by rw [zero_smul])
  exact one_ne_zero this

set_option maxHeartbeats 1000000 in
-- Many localization structures on the concrete charts.
/-- **`2S + 1` is regular modulo `ϖ` on the node chart.** -/
lemma twoS1_regular (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) (r : NR b₄ b₆ ϖ m ε)
    (h : twoS1 b₄ b₆ ϖ m ε * r ∈ Ideal.span {algebraMap O (NR b₄ b₆ ϖ m ε) ϖ}) :
    r ∈ Ideal.span {algebraMap O (NR b₄ b₆ ϖ m ε) ϖ} := by
  have hW := (isSMulRegular_NR b₄ b₆ hϖ hm hε).2
  have hΔ : algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (1 + 4 * cN b₄ b₆ ϖ m ε) =
      twoS1 b₄ b₆ ϖ m ε ^ 2 := by
    rw [twoS1_sq, map_add, map_one, map_mul, map_ofNat]
  have := hW.right_eq_zero_of_smul (x := Submodule.Quotient.mk r) (by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      mem_smul_top_iff_mem_span, smul_eq_mul, hΔ, pow_two, mul_assoc]
    exact Ideal.mul_mem_left _ _ h)
  rwa [Submodule.Quotient.mk_eq_zero, mem_smul_top_iff_mem_span] at this

/-! ### The generic fibre -/

omit [IsDomain O] in
lemma exists_chart_param [IsLocalRing O] (b₆ : O) : ∃ t κ : O, κ * (t ^ 2 - b₆) = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self b₆ with h | h
  · obtain ⟨κ, hκ⟩ := h.neg.exists_left_inv
    exact ⟨0, κ, by simpa using hκ⟩
  · obtain ⟨κ, hκ⟩ := h.exists_left_inv
    exact ⟨1, κ, by simpa using hκ⟩

set_option maxHeartbeats 1000000 in
-- Many localization structures on the concrete charts.
/-- **The generic fibre `NR[1/ϖ]` is integrally closed**: via `chartEquiv` it is the localization
`T1[1/ϖ][1/D]` of the Dedekind domain `T1[1/ϖ]`. -/
theorem isIntegrallyClosed_away_ϖ [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hm : 1 ≤ m)
    (hε : IsUnit ε) (h3 : (3 : O) ≠ 0) (hE : TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) :
    IsIntegrallyClosed (Localization.Away (algebraMap O (NR b₄ b₆ ϖ m ε) ϖ)) := by
  obtain ⟨t, κ, hκ⟩ := exists_chart_param b₆
  obtain ⟨εi, hεi⟩ := hε.exists_left_inv
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  have hπ0 : ε * ϖ ^ m ≠ 0 := mul_ne_zero hε.ne_zero (pow_ne_zero _ hϖ0)
  haveI := TateTwoChart.isDedekindDomain_away_T1_of_dvr (π := ε * ϖ ^ m) (b₄ := b₄) (t := t)
    hϖ0 hϖ.not_isUnit hκ h3 hπ0 hE
  haveI := isDomain_NR b₄ b₆ hϖ.prime hm hε
  set T := T1 (ε * ϖ ^ m) b₄ t κ
  set x : T := algebraMap O T ϖ
  set y : T := DT (ε * ϖ ^ m) b₄ t κ
  let B := Localization.Away x
  let C₁ := Localization.Away (algebraMap T B y)
  let C₂ := Localization.Away (algebraMap T (T1D (ε * ϖ ^ m) b₄ t κ) x)
  let N₁ := Localization.Away (algebraMap O (NR b₄ b₆ ϖ m ε) ϖ)
  haveI : IsLocalization.Away (x * y) C₁ := inferInstance
  haveI : IsLocalization.Away (x * y) C₂ := inferInstance
  let e₁ : C₁ ≃ₐ[T] C₂ := IsLocalization.algEquiv (Submonoid.powers (x * y)) C₁ C₂
  let φ := chartEquiv (b₆ := b₆) b₄ hκ (rfl : ε * ϖ ^ m = ε * ϖ ^ m) hεi
  have hφ : φ (algebraMap T (T1D (ε * ϖ ^ m) b₄ t κ) x) = algebraMap O (NR b₄ b₆ ϖ m ε) ϖ := by
    rw [← IsScalarTower.algebraMap_apply, AlgEquiv.commutes]
  let e₂ : C₂ ≃+* N₁ := IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (algebraMap T (T1D (ε * ϖ ^ m) b₄ t κ) x))
    (T := Submonoid.powers (algebraMap O (NR b₄ b₆ ϖ m ε) ϖ)) C₂ N₁ φ.toRingEquiv (by
      rw [Submonoid.map_powers]
      exact congrArg Submonoid.powers hφ)
  haveI : IsDomain N₁ := IsLocalization.Away.isDomain (S := N₁)
    (algebraMap_ϖ_NR_ne_zero (b₄ := b₄) (b₆ := b₆) hϖ.prime hm hε)
  have hy0 : algebraMap T B y ≠ 0 := by
    intro h0
    have h1 := IsLocalization.Away.algebraMap_isUnit (S := C₁) (algebraMap T B y)
    have h2 : algebraMap B C₁ (algebraMap T B y) = 0 :=
      (congrArg (algebraMap B C₁) h0).trans (map_zero _)
    have h3 : (0 : C₁) = 1 := isUnit_zero_iff.mp (h2 ▸ h1)
    have h4 := congrArg (e₁.toRingEquiv.trans e₂) h3
    rw [map_zero, map_one] at h4
    exact zero_ne_one h4
  haveI : IsIntegrallyClosed C₁ := isIntegrallyClosed_of_isLocalization (R := B) C₁
    (Submonoid.powers (algebraMap T B y)) (powers_le_nonZeroDivisors_of_noZeroDivisors hy0)
  exact IsIntegrallyClosed.of_equiv (e₁.toRingEquiv.trans e₂)

/-! ### The node chart is integrally closed -/

/-- **The quadratic node chart of the Tate model is integrally closed**: `O` a discrete valuation
ring with uniformizer `ϖ`, `m ≥ 1`, `ε` a unit, `3 ≠ 0` and `E = tateE (ε ϖᵐ) b₄ b₆ ≠ 0`. -/
theorem isIntegrallyClosed_NR [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hm : 1 ≤ m)
    (hε : IsUnit ε) (h3 : (3 : O) ≠ 0) (hE : TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) :
    IsIntegrallyClosed (NR b₄ b₆ ϖ m ε) := by
  have hϖp : Prime ϖ := hϖ.prime
  haveI := isDomain_NR b₄ b₆ hϖp hm hε
  haveI := isDomain_NE (b₄ := b₄) (b₆ := b₆) hϖp hm hε
  haveI : IsDomain (A ϖ m) := Node.isDomain (pow_ne_zero m hϖ.ne_zero)
  haveI : IsIntegrallyClosed (A ϖ m) := Node.isIntegrallyClosed (pow_ne_zero m hϖ.ne_zero)
  haveI : IsIntegrallyClosed (NE b₄ b₆ ϖ m ε) := isIntegrallyClosed_of_etale (A ϖ m) _
  haveI := isIntegrallyClosed_away_ϖ hϖ hm hε h3 hE
  have ht : twoS1 b₄ b₆ ϖ m ε ≠ 0 := by
    intro h0
    have h1 := IsLocalization.Away.algebraMap_isUnit (S := NE b₄ b₆ ϖ m ε) (twoS1 b₄ b₆ ϖ m ε)
    rw [h0, map_zero] at h1
    exact not_isUnit_zero h1
  exact isIntegrallyClosed_of_away_of_regular (algebraMap_ϖ_NR_ne_zero hϖp hm hε) ht
    (Localization.Away (algebraMap O (NR b₄ b₆ ϖ m ε) ϖ)) (NE b₄ b₆ ϖ m ε)
    (twoS1_regular hϖp hm hε)

end

end TateTwoChartNode

end SemistableReduction
