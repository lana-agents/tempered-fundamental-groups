/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateTwoChartNode
import TemperedFundamentalGroups.SemistableReduction.NodeNormal
import TemperedFundamentalGroups.SemistableReduction.NodeLocalRing
import TemperedFundamentalGroups.SemistableReduction.NodeCoverLocal

/-!
# The étale chart of the Tate model near its nodes is a domain (MR12 T2 S4, Tate chart)

Near its nodes the Tate chart `T1[1/D]` is the quadratic node chart
`NR = (A[S]/(S² + S − c))[1/D]` over the node ring `A = O[u,v]/(uv − ϖᵐ)`
(`TateTwoChartNode.chartEquiv`), `c = ε (1 + b₄ u²) v + b₆ u²`, `D = 1 + b₄ u²`.

* **`TateTwoChartNode.prime_poly`**: for `ϖ` prime, `m ≥ 1`, `ε` a unit and `O` an integrally
  closed domain, `S² + S − c` is a prime of `A[S]`: it has no root in `A` (reduce along
  `u ↦ 0`, `ϖ ↦ 0` to `(O/ϖ)[v]`, where `S² + S = ε v` has no solution for degree reasons), hence
  is irreducible over `Frac A`, hence (`A` integrally closed) the minimal polynomial of its root.
  So `Q = A[S]/(S² + S − c)` and `NR = Q[1/D]` are domains (`isDomain_Q`, `isDomain_NR`).
* **The étale chart** `NE = Q[1/(2S + 1)][1/D]`: étale over `A` (`QuadraticEtale.etale`), a
  domain (`isDomain_NE`), and the localization `NR[1/(2S + 1)]` of the node chart
  (`isLocalization_NE`).
* `twoS_add_one_sq`: `(2S + 1)² = 1 + 4c`, so `2S + 1` is a unit at the nodes (`c` vanishes
  there, `cN_mem_closedPoint`).
-/

universe u

open Polynomial

namespace SemistableReduction

open KummerEtale

namespace TateTwoChartNode

variable {O : Type u} [CommRing O] {ϖ : O} {m : ℕ} (b₄ b₆ : O) {ε : O}

lemma toPolyU_cN (hm : 1 ≤ m) :
    Node.toPolyU ϖ hm (cN b₄ b₆ ϖ m ε) = C (Ideal.Quotient.mk (Ideal.span {ϖ}) ε) * X := by
  simp only [cN, map_add, map_mul, map_pow, map_one, AlgHom.commutes, Node.toPolyU_u,
    Node.toPolyU_v, Polynomial.algebraMap_apply, Ideal.Quotient.algebraMap_eq]
  ring

lemma toPolyU_DN (hm : 1 ≤ m) : Node.toPolyU ϖ hm (DN b₄ ϖ m) = 1 := by
  simp only [DN, map_add, map_mul, map_pow, map_one, AlgHom.commutes, Node.toPolyU_u]
  ring

lemma isDomain_quot (hϖ : Prime ϖ) : IsDomain (O ⧸ Ideal.span {ϖ}) :=
  (Ideal.Quotient.isDomain_iff_prime _).2 ((Ideal.span_singleton_prime hϖ.ne_zero).2 hϖ)

/-- **`S² + S = c` has no solution in the node ring** (reduce to `S² + S = ε v` in `(O/ϖ)[v]`). -/
lemma sq_add_ne_cN (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) (a : A ϖ m) :
    a ^ 2 + a ≠ cN b₄ b₆ ϖ m ε := by
  intro h
  have hφ := congrArg (Node.toPolyU ϖ hm) h
  rw [map_add, map_pow, toPolyU_cN] at hφ
  haveI := isDomain_quot hϖ
  have hε0 : Ideal.Quotient.mk (Ideal.span {ϖ}) ε ≠ 0 := (hε.map _).ne_zero
  have h1 : (C (Ideal.Quotient.mk (Ideal.span {ϖ}) ε) * X).natDegree = 1 := natDegree_C_mul_X _ hε0
  set p := Node.toPolyU ϖ hm a
  rcases Nat.eq_zero_or_pos p.natDegree with h0 | h0
  · rw [eq_C_of_natDegree_eq_zero h0, ← C_pow, ← C_add] at hφ
    rw [← hφ, natDegree_C] at h1
    exact zero_ne_one h1
  · have h2 : (p ^ 2).natDegree = 2 * p.natDegree := natDegree_pow p 2
    have h3 : (p ^ 2 + p).natDegree = 2 * p.natDegree := by
      rw [natDegree_add_eq_left_of_natDegree_lt (by rw [h2]; omega), h2]
    rw [hφ, h1] at h3
    omega

lemma natDegree_poly {R : Type*} [CommRing R] [Nontrivial R] (c : R) :
    (QuadraticEtale.poly c).natDegree = 2 := by
  unfold QuadraticEtale.poly
  compute_degree!

/-- `2S + 1 ≠ 0` in `R[S]/(S² + S − c)`. -/
lemma mk_two_X_add_one_ne_zero {R : Type*} [CommRing R] [IsDomain R] (c : R) :
    AdjoinRoot.mk (QuadraticEtale.poly c) (2 * X + 1) ≠ 0 := by
  rw [Ne, AdjoinRoot.mk_eq_zero]
  intro hdvd
  have hne : (2 * X + 1 : R[X]) ≠ 0 := fun h ↦ by
    have := congrArg (coeff · 0) h
    simp at this
  have h1 := natDegree_le_of_dvd hdvd hne
  have h2 : (2 * X + 1 : R[X]).natDegree ≤ 1 := by compute_degree
  rw [natDegree_poly] at h1
  omega

lemma DN_ne_zero (hϖ : Prime ϖ) (hm : 1 ≤ m) : DN b₄ ϖ m ≠ 0 := by
  intro h
  haveI := isDomain_quot hϖ
  have := congrArg (Node.toPolyU ϖ hm) h
  rw [toPolyU_DN, map_zero] at this
  exact one_ne_zero this

lemma cN_mem_closedPoint : cN b₄ b₆ ϖ m ε ∈ Node.closedPoint ϖ (ϖ ^ m) :=
  Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Node.v_mem_closedPoint ϖ))
    (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ (Node.u_mem_closedPoint ϖ) 2 two_pos))

variable [IsDomain O] [IsIntegrallyClosed O]

/-- **`S² + S − c` is prime in `A[S]`.** -/
theorem prime_poly (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) :
    Prime (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) := by
  have hϖm : ϖ ^ m ≠ 0 := pow_ne_zero m hϖ.ne_zero
  haveI : IsDomain (A ϖ m) := Node.isDomain hϖm
  haveI : IsIntegrallyClosed (A ϖ m) := Node.isIntegrallyClosed hϖm
  set c := cN b₄ b₆ ϖ m ε
  set K := FractionRing (A ϖ m)
  have hmon := QuadraticEtale.monic_poly c
  have hdeg : (QuadraticEtale.poly c).natDegree = 2 := by
    unfold QuadraticEtale.poly
    compute_degree!
  set pK := (QuadraticEtale.poly c).map (algebraMap (A ϖ m) K)
  have hdegK : pK.natDegree = 2 := by rw [hmon.natDegree_map, hdeg]
  have hirr : Irreducible pK := by
    refine irreducible_of_degree_le_three_of_not_isRoot (by rw [hdegK]; decide) fun x hx ↦ ?_
    have hint : IsIntegral (A ϖ m) x := ⟨_, hmon, by rwa [IsRoot, eval_map] at hx⟩
    obtain ⟨a, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    rw [IsRoot, eval_map, eval₂_at_apply, ← map_zero (algebraMap (A ϖ m) K)] at hx
    have ha := IsFractionRing.injective (A ϖ m) K hx
    simp only [QuadraticEtale.poly, eval_sub, eval_add, eval_pow, eval_X, eval_C] at ha
    exact sq_add_ne_cN b₄ b₆ hϖ hm hε a (sub_eq_zero.mp ha)
  haveI : Fact (Irreducible pK) := ⟨hirr⟩
  have hx0 : aeval (AdjoinRoot.root pK) pK = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have hxA : IsIntegral (A ϖ m) (AdjoinRoot.root pK) :=
    ⟨_, hmon, by rw [← aeval_def, ← aeval_map_algebraMap K]; exact hx0⟩
  have hmin : minpoly (A ϖ m) (AdjoinRoot.root pK) = QuadraticEtale.poly c := by
    refine Polynomial.map_injective (algebraMap (A ϖ m) K) (IsFractionRing.injective _ K) ?_
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' K hxA]
    exact (minpoly.eq_of_irreducible_of_monic hirr hx0 (hmon.map _)).symm
  haveI : Module.IsTorsionFree (A ϖ m) (AdjoinRoot pK) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [IsScalarTower.algebraMap_eq (A ϖ m) K (AdjoinRoot pK)]
      exact (algebraMap K _).injective.comp (IsFractionRing.injective _ K))
  rw [← hmin]
  exact minpoly.prime_of_isIntegrallyClosed hxA

/-- `Q = A[S]/(S² + S − c)` is a domain. -/
theorem isDomain_Q (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) :
    IsDomain (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) :=
  AdjoinRoot.isDomain_of_prime (prime_poly b₄ b₆ hϖ hm hε)

omit [IsIntegrallyClosed O] in
lemma of_DN_ne_zero (hϖ : Prime ϖ) (hm : 1 ≤ m) :
    AdjoinRoot.of (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) (DN b₄ ϖ m) ≠ 0 := by
  haveI : IsDomain (A ϖ m) := Node.isDomain (pow_ne_zero m hϖ.ne_zero)
  have hdeg : (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)).degree ≠ 0 := by
    rw [degree_eq_natDegree (QuadraticEtale.monic_poly _).ne_zero, natDegree_poly]
    norm_num
  rw [Ne, ← map_zero (AdjoinRoot.of _), (AdjoinRoot.of.injective_of_degree_ne_zero hdeg).eq_iff]
  exact DN_ne_zero b₄ hϖ hm

/-- The node chart `NR = Q[1/D]` is a domain. -/
theorem isDomain_NR (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) :
    IsDomain (NR b₄ b₆ ϖ m ε) :=
  haveI := isDomain_Q b₄ b₆ hϖ hm hε
  IsLocalization.Away.isDomain (S := NR b₄ b₆ ϖ m ε) (of_DN_ne_zero b₄ b₆ (ε := ε) hϖ hm)

end TateTwoChartNode

namespace TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] (b₄ b₆ ϖ : O) (m : ℕ) (ε : O)

/-- `Q[1/(2S + 1)]`, étale over the node ring `A` (`QuadraticEtale.etale`). -/
abbrev QE : Type u :=
  Localization.Away (AdjoinRoot.mk (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) (2 * X + 1))

/-- **The étale chart** `NE = Q[1/(2S + 1)][1/D]` of the Tate model near its nodes. -/
abbrev NE : Type u :=
  Localization.Away (algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (QE b₄ b₆ ϖ m ε)
    (AdjoinRoot.of _ (DN b₄ ϖ m)))

/-- `2S + 1` in the node chart. -/
abbrev twoS1 : NR b₄ b₆ ϖ m ε :=
  algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (NR b₄ b₆ ϖ m ε)
    (AdjoinRoot.mk (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) (2 * X + 1))

instance etale_NE : Algebra.Etale (A ϖ m) (NE b₄ b₆ ϖ m ε) :=
  haveI := QuadraticEtale.etale (cN b₄ b₆ ϖ m ε)
  inferInstance

lemma isUnit_DN_NE : IsUnit (algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (NE b₄ b₆ ϖ m ε)
    (AdjoinRoot.of _ (DN b₄ ϖ m))) := by
  rw [IsScalarTower.algebraMap_apply _ (QE b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- The node chart maps to the étale chart. -/
noncomputable instance : Algebra (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) :=
  (IsLocalization.Away.lift (S := NR b₄ b₆ ϖ m ε) (AdjoinRoot.of _ (DN b₄ ϖ m))
    (isUnit_DN_NE b₄ b₆ ϖ m ε)).toAlgebra

/-- Shortcut instance (the search through the localization instances is expensive). -/
instance (priority := high) : SMul (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) := Algebra.toSMul

instance : IsScalarTower (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (NR b₄ b₆ ϖ m ε)
    (NE b₄ b₆ ϖ m ε) :=
  IsScalarTower.of_algebraMap_eq fun a ↦
    (IsLocalization.Away.lift_eq _ (isUnit_DN_NE b₄ b₆ ϖ m ε) a).symm

instance : IsScalarTower (A ϖ m) (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) :=
  IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply (A ϖ m) (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε))
        (NR b₄ b₆ ϖ m ε) a,
      ← IsScalarTower.algebraMap_apply (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (NR b₄ b₆ ϖ m ε)
        (NE b₄ b₆ ϖ m ε),
      IsScalarTower.algebraMap_apply (A ϖ m) (QE b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) a,
      IsScalarTower.algebraMap_apply (A ϖ m) (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (QE b₄ b₆ ϖ m ε) a,
      ← IsScalarTower.algebraMap_apply (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (QE b₄ b₆ ϖ m ε)
        (NE b₄ b₆ ϖ m ε)]

instance : IsScalarTower O (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) :=
  IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply O (A ϖ m) (NR b₄ b₆ ϖ m ε) a,
      ← IsScalarTower.algebraMap_apply (A ϖ m) (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε),
      ← IsScalarTower.algebraMap_apply O (A ϖ m) (NE b₄ b₆ ϖ m ε)]

/-- **The étale chart is the localization `NR[1/(2S + 1)]` of the node chart.** -/
instance isLocalization_NE : IsLocalization.Away (twoS1 b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) :=
  IsLocalization.Away.commutes (NR b₄ b₆ ϖ m ε) (QE b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε)
    (AdjoinRoot.of _ (DN b₄ ϖ m)) (AdjoinRoot.mk (QuadraticEtale.poly (cN b₄ b₆ ϖ m ε)) (2 * X + 1))

variable {b₄ b₆ ϖ m ε} [IsDomain O] [IsIntegrallyClosed O]

/-- **The étale chart is a domain.** -/
theorem isDomain_NE (hϖ : Prime ϖ) (hm : 1 ≤ m) (hε : IsUnit ε) :
    IsDomain (NE b₄ b₆ ϖ m ε) := by
  haveI := isDomain_Q b₄ b₆ hϖ hm hε
  haveI : IsDomain (A ϖ m) := Node.isDomain (pow_ne_zero m hϖ.ne_zero)
  have h2 := mk_two_X_add_one_ne_zero (cN b₄ b₆ ϖ m ε)
  haveI : IsDomain (QE b₄ b₆ ϖ m ε) := IsLocalization.Away.isDomain (S := QE b₄ b₆ ϖ m ε) h2
  refine IsLocalization.Away.isDomain (S := NE b₄ b₆ ϖ m ε)
    (x := algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (QE b₄ b₆ ϖ m ε)
      (AdjoinRoot.of _ (DN b₄ ϖ m))) ?_
  rw [Ne, ← map_zero (algebraMap (QuadNode.Q ϖ m (cN b₄ b₆ ϖ m ε)) (QE b₄ b₆ ϖ m ε)),
    (IsLocalization.injective (QE b₄ b₆ ϖ m ε)
      (powers_le_nonZeroDivisors_of_noZeroDivisors h2)).eq_iff]
  exact of_DN_ne_zero b₄ b₆ hϖ hm

omit [IsDomain O] [IsIntegrallyClosed O] in
lemma twoS1_eq : twoS1 b₄ b₆ ϖ m ε = 2 * SR b₄ b₆ ϖ m ε + 1 := by
  simp only [twoS1, SR, map_add, map_mul, map_one, AdjoinRoot.mk_X, map_ofNat]

omit [IsDomain O] [IsIntegrallyClosed O] in
/-- `(2S + 1)² = 1 + 4c`. -/
lemma twoS1_sq : twoS1 b₄ b₆ ϖ m ε ^ 2 =
    1 + 4 * algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (cN b₄ b₆ ϖ m ε) := by
  rw [twoS1_eq, ← SR_sq]
  ring

end

end TateTwoChartNode

end SemistableReduction
