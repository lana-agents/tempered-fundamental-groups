/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeChart
import TemperedFundamentalGroups.SemistableReduction.TateGenericFibre

/-!
# The generic fibre of `ℙ¹ ∖ {0, 1, a}` is a Dedekind domain (MR13 A1)

The chart `P1Three.R1 = O[Y][s]/(G₁)`, `G₁ = s³ − Y q(s)`, `q(s) = 1 − (1 + a) s + a s²`, of the
model `h = t (t − 1) (t − a) : ℙ¹_t → ℙ¹_X` of `P1ThreeChart` is the affine curve
`ℙ¹_t ∖ {0, 1, a}` (`s = 1/t`). Over a field `K` (any `a ∈ K`):

* **`P1Three.irreducible_G1`**: `G₁` is irreducible over `K[Y]` (a root `r ∈ K[Y]` would satisfy
  `Y ∣ r³`, hence `r = Y r'` and `Y (Y² r'³ − a Y² r'² + (1 + a) Y r' − 1) = 0`, impossible at
  `Y = 0`);
* **`P1Three.formallySmooth_R1`**: `R1` is smooth over `K`, with the certificate
  `(A + Y B) q + B G₁ = 1` (`q A + s³ B = 1`, `A = 1 + c s + (c² − a) s²`,
  `B = c³ − 2 a c − a (c² − a) s`, `c = 1 + a`: the inverse of `q` modulo `s³`), i.e.
  `∂G₁/∂Y = −q` is a unit modulo `G₁`;
* **`P1Three.isDedekindDomain_R1`**; and for a discrete valuation ring `O` with a nonzero nonunit
  `ϖ`, **`P1Three.isDedekindDomain_away_R1_of_dvr`**: `R1[1/ϖ]` (`= R1` over `K = Frac O`,
  **`P1Three.awayEquiv1`**) is a Dedekind domain — the coordinate ring of `U_K = ℙ¹_K ∖ {0, 1, a}`.

The proofs follow `TateGenericFibre` and use its generic `PlaneCurve` lemmas.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace P1Three

noncomputable section

section Eval

variable {O : Type u} [CommRing O] (a : O) {S : Type*} [CommRing S] [Algebra O S]

lemma eval₂_G1 (x y : S) : (G1 O a).eval₂ ((aeval x : O[X] →ₐ[O] S) : O[X] →+* S) y =
    y ^ 3 - algebraMap O S a * x * y ^ 2 + (1 + algebraMap O S a) * x * y - x := by
  simp only [G1, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, RingHom.coe_coe,
    map_mul, map_add, map_one, aeval_C, aeval_X, eval₂_one]

lemma map_G1 {L : Type u} [CommRing L] (φ : O →+* L) :
    (G1 O a).map (mapRingHom φ) = G1 L (φ a) := by
  simp only [G1, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_X, Polynomial.map_C, coe_mapRingHom, map_mul, map_add, map_one,
    Polynomial.map_one]

end Eval

section Field

variable {K : Type u} [Field K] (a : K)

lemma natDegree_G1 : (G1 K a).natDegree = 3 := by
  unfold G1
  compute_degree!

/-- **`G₁` is irreducible over `K[Y]`.** -/
theorem irreducible_G1 : Irreducible (G1 K a) := by
  rw [(monic_G1 K a).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [natDegree_G1]; norm_num) (by rw [natDegree_G1])]
  refine Multiset.eq_zero_of_forall_notMem fun r hr ↦ ?_
  rw [mem_roots (monic_G1 K a).ne_zero, IsRoot] at hr
  simp only [G1, eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hr
  have hd : (X : K[X]) ∣ r ^ 3 :=
    ⟨C a * r ^ 2 - C (1 + a) * r + 1, by linear_combination hr⟩
  obtain ⟨r', rfl⟩ := prime_X.dvd_of_dvd_pow hd
  have h : (X : K[X]) * (X ^ 2 * r' ^ 3 - C a * X ^ 2 * r' ^ 2 + C (1 + a) * X * r' - 1) = 0 := by
    linear_combination hr
  rcases mul_eq_zero.mp h with h | h
  · exact X_ne_zero h
  · have := congrArg (eval 0) h
    simp at this

/-- The first-order lift of the generators of `R1` (in any `K`-algebra with `e² = 0`). -/
theorem eval₂_lift1 {S : Type*} [CommRing S] [Algebra K S] (x y e : S) (he : e ^ 2 = 0)
    (hG : (G1 K a).eval₂ ((aeval x : K[X] →ₐ[K] S) : K[X] →+* S) y = e) :
    (G1 K a).eval₂ ((aeval (x + e * ((1 + (1 + algebraMap K S a) * y +
        ((1 + algebraMap K S a) ^ 2 - algebraMap K S a) * y ^ 2) +
        x * ((1 + algebraMap K S a) ^ 3 - 2 * algebraMap K S a * (1 + algebraMap K S a) -
          algebraMap K S a * ((1 + algebraMap K S a) ^ 2 - algebraMap K S a) * y))) :
        K[X] →ₐ[K] S) : K[X] →+* S) (y + e * 0) = 0 := by
  rw [eval₂_G1] at hG ⊢
  set φa := algebraMap K S a
  linear_combination (1 + e * ((1 + φa) ^ 3 - 2 * φa * (1 + φa) -
    φa * ((1 + φa) ^ 2 - φa) * y)) * hG + ((1 + φa) ^ 3 - 2 * φa * (1 + φa) -
    φa * ((1 + φa) ^ 2 - φa) * y) * he

/-- **`R1` is smooth over `K`.** -/
theorem formallySmooth_R1 : Algebra.FormallySmooth K (R1 K a) :=
  PlaneCurve.formallySmooth_of_lift _ _ _ (eval₂_lift1 a _ _ _ (PlaneCurve.sq_mk_self _)
    (PlaneCurve.mk_eq_eval₂ _ _).symm)

/-- **`R1 = K[s, 1/((1 − s)(1 − a s))]` is a Dedekind domain.** -/
theorem isDedekindDomain_R1 : IsDedekindDomain (R1 K a) := by
  haveI := formallySmooth_R1 a
  exact PlaneCurve.isDedekindDomain_of_irreducible (monic_G1 K a) (irreducible_G1 a)

end Field

/-! ### `R1[1/ϖ]` -/

section Away

variable {O : Type u} [CommRing O] [IsDomain O] {ϖ : O} (hϖ : ϖ ≠ 0)

include hϖ in
/-- **`R1[1/ϖ]` is the chart ring `R1` over `K = O[1/ϖ]`.** -/
def awayEquiv1 (K : Type u) [CommRing K] [IsDomain K] [Algebra O K] [IsLocalization.Away ϖ K]
    (a : O) : Localization.Away (algebraMap O (R1 O a) ϖ) ≃+* R1 K (algebraMap O K a) :=
  letI := (PlaneCurve.baseMap (map_G1 a (algebraMap O K))).toAlgebra
  haveI := PlaneCurve.isLocalization_adjoinRoot_map (map_G1 a (algebraMap O K))
    (Submonoid.powers ϖ) (powers_le_nonZeroDivisors_of_noZeroDivisors hϖ) (monic_G1 O a)
  haveI : IsLocalization (Algebra.algebraMapSubmonoid (R1 O a) (Submonoid.powers ϖ))
      (Localization.Away (algebraMap O (R1 O a) ϖ)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (R1 O a) (Submonoid.powers ϖ))
    _ _).toRingEquiv

include hϖ in
/-- **The generic fibre `R1[1/ϖ]` is a Dedekind domain** (`K = O[1/ϖ]` a field). -/
theorem isDedekindDomain_away_R1 (K : Type u) [Field K] [Algebra O K] [IsLocalization.Away ϖ K]
    (a : O) : IsDedekindDomain (Localization.Away (algebraMap O (R1 O a) ϖ)) := by
  haveI := isDedekindDomain_R1 (algebraMap O K a)
  exact PlaneCurve.isDedekindDomain_of_ringEquiv (awayEquiv1 hϖ K a)

include hϖ in
/-- **The coordinate ring `R1[1/ϖ]` of `U_K = ℙ¹_K ∖ {0, 1, a}` is a Dedekind domain** (`O` a
discrete valuation ring, `ϖ` a nonzero nonunit). -/
theorem isDedekindDomain_away_R1_of_dvr [IsDiscreteValuationRing O] (hu : ¬IsUnit ϖ) (a : O) :
    IsDedekindDomain (Localization.Away (algebraMap O (R1 O a) ϖ)) := by
  haveI := isLocalization_away_fractionRing hϖ hu
  exact isDedekindDomain_away_R1 hϖ (FractionRing O) a

end Away

end

end P1Three

end SemistableReduction
