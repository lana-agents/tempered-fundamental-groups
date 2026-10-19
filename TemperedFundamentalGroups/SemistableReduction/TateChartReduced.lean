/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateChartIdentification

/-!
# Reducedness of the Tate charts and the identification of the two-chart rings

Let `O` be a domain, `ϖ ∈ O` with `(ϖ)` maximal and `⋂ ϖⁿ O = 0` (e.g. a uniformizer of a
discrete valuation ring), `ϖ ∣ π` and `κ (t² − b₆) = 1`.

* `isReduced_of_quotient`: if `ϖ` is a non-zero-divisor on `T`, `⋂ ϖⁿ T = 0` and `T ⧸ ϖ` is
  reduced, then `T` is reduced.
* `isReduced_adjoinRoot`: `O[X][Y]/(G)` (`G` monic) is reduced if its special fibre
  `(O/ϖ)[X][Y]/(Ḡ)` is (`isReduced_quotient_adjoinRoot`: `T/ϖT ≅ (O/ϖ)[X][Y]/(Ḡ)`; regularity and
  separatedness coefficientwise in the power basis over `O[X]`).
* Special fibres: `Ḡ₀ = z (z² + κ t (2 + h) z + κ (1 + h))` and
  `Ḡ₁ = w (w² + κ t (2h' + 1) w + κ h' (h' + 1))` (`TateTwoChart.map_G0_eq/map_G1_eq`) are
  squarefree in `k[X][Y]` in every residue characteristic: a monic quadratic whose constant
  coefficient is squarefree and not a unit is squarefree (`squarefree_of_monic_quadratic`), and
  `κ (1 + h)`, `κ h' (h' + 1)` are separable.
* **`TateTwoChart.isReduced_T0`, `TateTwoChart.isReduced_T1`**.
* **`TateChartIdentification.twoChartMap_bijective`** (and
  `twoChartMap_bijective_of_irreducible` for a discrete valuation ring): the three components of
  `twoChartMap : twoChart → twoChartRingsOfAffine (toP1 ..)` are bijective, i.e.
  `TateTwoChart.twoChart` is the two-chart description of the Tate model over `ℙ¹_O`;
  `chartEquiv0/1/01` are the resulting `O`-algebra isomorphisms.
-/
open Polynomial

namespace SemistableReduction

/-- **Reducedness lifts from the special fibre** for a `ϖ`-torsion free, `ϖ`-adically separated
ring. -/
theorem isReduced_of_quotient {T : Type*} [CommRing T] (ϖ : T) (hreg : IsSMulRegular T ϖ)
    (hsep : ∀ x : T, (∀ n : ℕ, ϖ ^ n ∣ x) → x = 0)
    (hred : IsReduced (T ⧸ Ideal.span {ϖ})) : IsReduced T := by
  refine ⟨fun x ⟨n, hn⟩ ↦ hsep x fun k ↦ ?_⟩
  have key : ∀ k : ℕ, ∃ y : T, x = ϖ ^ k * y ∧ y ^ n = 0 := by
    intro k
    induction k with
    | zero => exact ⟨x, by simp, hn⟩
    | succ k ih =>
      obtain ⟨y, rfl, hy⟩ := ih
      have hy0 : Ideal.Quotient.mk (Ideal.span {ϖ}) y = 0 :=
        (show IsNilpotent (Ideal.Quotient.mk (Ideal.span {ϖ}) y) from
          ⟨n, by rw [← map_pow, hy, map_zero]⟩).eq_zero
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hy0)
      refine ⟨z, by rw [← hz, pow_succ]; ring, ?_⟩
      have h1 : ϖ ^ n * z ^ n = ϖ ^ n * 0 := by
        rw [mul_zero, ← mul_pow, mul_comm, hz, hy]
      exact hreg.pow n (by simpa only [smul_eq_mul] using h1)
  obtain ⟨y, rfl, -⟩ := key k
  exact dvd_mul_right _ _

section Basis

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S] (b : Module.Basis ι R S)

include b in
/-- A non-zero-divisor of `R` stays one on a free `R`-algebra. -/
theorem isSMulRegular_algebraMap_of_basis {r : R} (hr : IsSMulRegular R r) :
    IsSMulRegular S (algebraMap R S r) := by
  intro x y h
  simp only [smul_eq_mul, ← Algebra.smul_def] at h
  apply b.repr.injective
  ext i
  have h' := congrArg (fun z ↦ b.repr z i) h
  simp only [map_smul, Finsupp.smul_apply] at h'
  exact hr h'

include b in
/-- `r`-adic separatedness passes to a free `R`-algebra. -/
theorem eq_zero_of_forall_dvd_of_basis {r : R} (hR : ∀ a : R, (∀ n : ℕ, r ^ n ∣ a) → a = 0)
    (x : S) (hx : ∀ n : ℕ, algebraMap R S r ^ n ∣ x) : x = 0 := by
  apply b.repr.injective
  ext i
  rw [map_zero, Finsupp.zero_apply]
  refine hR _ fun n ↦ ?_
  obtain ⟨y, hy⟩ := hx n
  rw [hy, ← map_pow, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact dvd_mul_right _ _

end Basis

section AdjoinRoot

variable {O : Type*} [CommRing O]

/-- The special fibre of `O[X][Y]/(G)` at `ϖ` is `(O/ϖ)[X][Y]/(Ḡ)`. -/
theorem isReduced_quotient_adjoinRoot (ϖ : O) (G : O[X][X])
    (hred : IsReduced (AdjoinRoot (G.map (mapRingHom (Ideal.Quotient.mk (Ideal.span {ϖ})))))) :
    IsReduced (AdjoinRoot G ⧸ Ideal.span {algebraMap O (AdjoinRoot G) ϖ}) := by
  set I : Ideal O[X] := Ideal.map C (Ideal.span {ϖ})
  have hI : Ideal.span {algebraMap O (AdjoinRoot G) ϖ} = I.map (AdjoinRoot.of G) := by
    simp only [I, Ideal.map_span, Set.image_singleton, TateTwoChart.of_C]
  let E : (O[X] ⧸ I)[X] ≃+* (O ⧸ Ideal.span {ϖ})[X][X] :=
    Polynomial.mapEquiv (Ideal.polynomialQuotientEquivQuotientPolynomial (Ideal.span {ϖ})).symm
  have hE : E (G.map (Ideal.Quotient.mk I)) =
      G.map (mapRingHom (Ideal.Quotient.mk (Ideal.span {ϖ}))) := by
    simp only [E, Polynomial.mapEquiv_apply, Polynomial.map_map]
    congr 1
  let e : AdjoinRoot G ⧸ Ideal.span {algebraMap O (AdjoinRoot G) ϖ} ≃+*
      AdjoinRoot (G.map (mapRingHom (Ideal.Quotient.mk (Ideal.span {ϖ})))) :=
    (Ideal.quotEquivOfEq hI).trans ((AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot I G).trans
      (Ideal.quotientEquiv _ _ E (by rw [Ideal.map_span, Set.image_singleton, ← hE]; rfl)))
  exact isReduced_of_injective e e.injective

/-- **Reducedness of `O[X][Y]/(G)` from the special fibre**: `O` a domain, `ϖ`-adically separated,
`G` monic and `(O/ϖ)[X][Y]/(Ḡ)` reduced. -/
theorem isReduced_adjoinRoot [IsDomain O] (ϖ : O) (hO : ∀ a : O, (∀ n : ℕ, ϖ ^ n ∣ a) → a = 0)
    {G : O[X][X]} (hG : G.Monic)
    (hred : IsReduced (AdjoinRoot (G.map (mapRingHom (Ideal.Quotient.mk (Ideal.span {ϖ})))))) :
    IsReduced (AdjoinRoot G) := by
  have hq := isReduced_quotient_adjoinRoot ϖ G hred
  by_cases hϖ : ϖ = 0
  · subst hϖ
    rw [map_zero, Ideal.span_singleton_eq_bot.2 rfl] at hq
    refine isReduced_of_injective (Ideal.Quotient.mk (⊥ : Ideal (AdjoinRoot G))) fun x y h ↦ ?_
    rwa [Ideal.Quotient.eq, Ideal.mem_bot, sub_eq_zero] at h
  have hC : algebraMap O (AdjoinRoot G) ϖ = algebraMap O[X] (AdjoinRoot G) (C ϖ) := by
    rw [AdjoinRoot.algebraMap_eq, TateTwoChart.of_C]
  let b := (AdjoinRoot.powerBasis' hG).basis
  refine isReduced_of_quotient (algebraMap O _ ϖ) ?_ ?_ hq
  · rw [hC]
    exact isSMulRegular_algebraMap_of_basis b (IsSMulRegular.of_ne_zero (C_ne_zero.2 hϖ))
  · rw [hC]
    refine eq_zero_of_forall_dvd_of_basis b fun a ha ↦ ?_
    ext j
    refine hO _ fun n ↦ ?_
    obtain ⟨c, hc⟩ := ha n
    rw [hc, ← C_pow, coeff_C_mul]
    exact dvd_mul_right _ _

end AdjoinRoot

section SpecialFibre

/-- A monic quadratic over a domain whose constant coefficient is squarefree and not a unit is
squarefree. -/
theorem squarefree_of_monic_quadratic {R : Type*} [CommRing R] [IsDomain R] {Q : R[X]}
    (hm : Q.Monic) (hd : Q.natDegree = 2) (hc : Squarefree (Q.coeff 0))
    (hcu : ¬IsUnit (Q.coeff 0)) : Squarefree Q := by
  rintro p ⟨q, hQ⟩
  have hp : p ≠ 0 := by rintro rfl; exact hm.ne_zero (by simpa using hQ)
  have hq : q ≠ 0 := by rintro rfl; exact hm.ne_zero (by simpa using hQ)
  have hdeg := congrArg natDegree hQ
  rw [natDegree_mul (mul_ne_zero hp hp) hq, natDegree_mul hp hp, hd] at hdeg
  have hlc := congrArg leadingCoeff hQ
  rw [leadingCoeff_mul, leadingCoeff_mul, hm.leadingCoeff] at hlc
  have h0 := congrArg (coeff · 0) hQ
  simp only [mul_coeff_zero] at h0
  have hp0 : IsUnit (p.coeff 0) := hc _ ⟨q.coeff 0, h0⟩
  rcases (by omega : p.natDegree = 0 ∨ p.natDegree = 1) with h | h
  · rw [eq_C_of_natDegree_eq_zero h]
    exact isUnit_C.2 hp0
  · exfalso
    have hq0 : q.natDegree = 0 := by omega
    have hu : IsUnit q.leadingCoeff := IsUnit.of_mul_eq_one_right _ hlc.symm
    rw [leadingCoeff, hq0] at hu
    exact hcu (h0 ▸ (hp0.mul hp0).mul hu)

/-- `K[X][Y]/(Y Q)` is reduced for a monic quadratic `Q` whose constant coefficient is squarefree
and not a unit. -/
theorem isReduced_adjoinRoot_X_mul {K : Type*} [Field K] {Q : K[X][X]} (hm : Q.Monic)
    (hd : Q.natDegree = 2) (hc : Squarefree (Q.coeff 0)) (hcu : ¬IsUnit (Q.coeff 0)) :
    IsReduced (AdjoinRoot (X * Q)) := by
  have hsq : Squarefree (X * Q) :=
    squarefree_mul_iff.2 ⟨irreducible_X.isRelPrime_iff_not_dvd.2
      (by rw [X_dvd_iff]; exact hc.ne_zero), irreducible_X.squarefree,
      squarefree_of_monic_quadratic hm hd hc hcu⟩
  exact (Ideal.isRadical_iff_quotient_reduced _).1 (isRadical_iff_span_singleton.1 hsq.isRadical)

/-! ### The special fibres of the Tate charts -/

namespace TateTwoChart

variable {O K : Type*} [CommRing O] [Field K] (π b₄ t κ : O) (φ : O →+* K)

/-- The quadratic factor of the special fibre of `G₀`. -/
noncomputable def Q0 : K[X][X] :=
  X ^ 2 + C (C (φ κ) * (C (2 * φ t) + C (φ t) * X)) * X + C (C (φ κ) * (1 + X))

/-- The quadratic factor of the special fibre of `G₁`. -/
noncomputable def Q1 : K[X][X] :=
  X ^ 2 + C (C (φ κ) * (C (2 * φ t) * X + C (φ t))) * X + C (C (φ κ) * (X ^ 2 + X))

/-- `Ḡ₀ = z · Q₀` if `φ π = 0`. -/
lemma map_G0_eq (hπ : φ π = 0) : (G0 π b₄ t κ).map (mapRingHom φ) = X * Q0 t κ φ := by
  simp only [G0, Q0, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_one, coe_mapRingHom,
    map_mul, map_sub, map_ofNat, hπ]
  simp
  ring

/-- `Ḡ₁ = w · Q₁` if `φ π = 0`. -/
lemma map_G1_eq (hπ : φ π = 0) : (G1 π b₄ t κ).map (mapRingHom φ) = X * Q1 t κ φ := by
  simp only [G1, Q1, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, coe_mapRingHom,
    map_mul, map_sub, map_ofNat, hπ]
  simp
  ring

lemma monic_Q0 : (Q0 t κ φ).Monic := by
  unfold Q0
  monicity!

lemma monic_Q1 : (Q1 t κ φ).Monic := by
  unfold Q1
  monicity!

lemma natDegree_Q0 : (Q0 t κ φ).natDegree = 2 := by
  unfold Q0
  compute_degree!

lemma natDegree_Q1 : (Q1 t κ φ).natDegree = 2 := by
  unfold Q1
  compute_degree!

lemma coeff_Q0 : (Q0 t κ φ).coeff 0 = C (φ κ) * (1 + X) := by
  simp [Q0]

lemma coeff_Q1 : (Q1 t κ φ).coeff 0 = C (φ κ) * (X ^ 2 + X) := by
  rw [Q1, coeff_add, coeff_add, coeff_C_zero]
  simp

variable {κ φ} (hκ : φ κ ≠ 0)
include hκ

lemma squarefree_coeff_Q0 : Squarefree ((Q0 t κ φ).coeff 0) := by
  rw [coeff_Q0]
  refine Separable.squarefree ((separable_def _).2 ⟨0, C (φ κ)⁻¹, ?_⟩)
  have hd : derivative (C (φ κ) * (1 + X) : K[X]) = C (φ κ) := by simp
  rw [hd, zero_mul, zero_add, ← C_mul, inv_mul_cancel₀ hκ, C_1]

lemma squarefree_coeff_Q1 : Squarefree ((Q1 t κ φ).coeff 0) := by
  rw [coeff_Q1]
  have hd : derivative (C (φ κ) * (X ^ 2 + X) : K[X]) = C (φ κ) * (2 * X + 1) := by
    simp only [derivative_mul, derivative_C, zero_mul, zero_add, derivative_add,
      derivative_X_pow, derivative_X, Nat.cast_ofNat, map_ofNat]
    ring
  have hu : C (φ κ) * C (φ κ)⁻¹ = 1 := by rw [← C_mul, mul_inv_cancel₀ hκ, C_1]
  refine Separable.squarefree
    ((separable_def _).2 ⟨-4 * C (φ κ)⁻¹, C (φ κ)⁻¹ * (2 * X + 1), ?_⟩)
  rw [hd]
  linear_combination hu

lemma not_isUnit_coeff_Q0 : ¬IsUnit ((Q0 t κ φ).coeff 0) := by
  rw [coeff_Q0]
  intro h
  have h1 := natDegree_eq_zero_of_isUnit h
  have h2 : (C (φ κ) * (1 + X) : K[X]).natDegree = 1 := by compute_degree!
  omega

lemma not_isUnit_coeff_Q1 : ¬IsUnit ((Q1 t κ φ).coeff 0) := by
  rw [coeff_Q1]
  intro h
  have h1 := natDegree_eq_zero_of_isUnit h
  have h2 : (C (φ κ) * (X ^ 2 + X) : K[X]).natDegree = 2 := by compute_degree!
  omega

end TateTwoChart

end SpecialFibre

/-! ### The Tate charts are reduced -/

namespace TateTwoChart

variable {O : Type*} [CommRing O] [IsDomain O] (π b₄ t κ : O) {b₆ : O}
  (hκ : κ * (t ^ 2 - b₆) = 1) (ϖ : O) [(Ideal.span {ϖ}).IsMaximal]
  (hO : ∀ a : O, (∀ n : ℕ, ϖ ^ n ∣ a) → a = 0) (hπ : ϖ ∣ π)

include hκ hO hπ

/-- **`T0 = O[h][z]/(G₀)` is reduced** (`O` a `ϖ`-adically separated domain, `(ϖ)` maximal,
`ϖ ∣ π`, `κ (t² − b₆) = 1`). -/
theorem isReduced_T0 : IsReduced (T0 π b₄ t κ) := by
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  have hπ' : Ideal.Quotient.mk (Ideal.span {ϖ}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hπ)
  have hκ' : Ideal.Quotient.mk (Ideal.span {ϖ}) κ ≠ 0 :=
    left_ne_zero_of_mul_eq_one (b := Ideal.Quotient.mk (Ideal.span {ϖ}) (t ^ 2 - b₆))
      (by rw [← map_mul, hκ, map_one])
  refine isReduced_adjoinRoot ϖ hO (monic_G0 π b₄ t κ) ?_
  rw [map_G0_eq π b₄ t κ _ hπ']
  exact isReduced_adjoinRoot_X_mul (monic_Q0 t κ _) (natDegree_Q0 t κ _)
    (squarefree_coeff_Q0 t hκ') (not_isUnit_coeff_Q0 t hκ')

/-- **`T1 = O[h'][w]/(G₁)` is reduced** (same hypotheses as `isReduced_T0`). -/
theorem isReduced_T1 : IsReduced (T1 π b₄ t κ) := by
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  have hπ' : Ideal.Quotient.mk (Ideal.span {ϖ}) π = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 hπ)
  have hκ' : Ideal.Quotient.mk (Ideal.span {ϖ}) κ ≠ 0 :=
    left_ne_zero_of_mul_eq_one (b := Ideal.Quotient.mk (Ideal.span {ϖ}) (t ^ 2 - b₆))
      (by rw [← map_mul, hκ, map_one])
  refine isReduced_adjoinRoot ϖ hO (monic_G1 π b₄ t κ) ?_
  rw [map_G1_eq π b₄ t κ _ hπ']
  exact isReduced_adjoinRoot_X_mul (monic_Q1 t κ _) (natDegree_Q1 t κ _)
    (squarefree_coeff_Q1 t hκ') (not_isUnit_coeff_Q1 t hκ')

end TateTwoChart

end SemistableReduction

namespace TemperedFundamentalGroups

namespace TateChartIdentification

open SemistableReduction SemistableReduction.TateTwoChart

section Reduced

variable {O : Type*} [CommRing O] [IsDomain O] (π b₄ t κ : O) {b₆ : O}
  (hκ : κ * (t ^ 2 - b₆) = 1) (ϖ : O) [(Ideal.span {ϖ}).IsMaximal]
  (hO : ∀ a : O, (∀ n : ℕ, ϖ ^ n ∣ a) → a = 0) (hπ : ϖ ∣ π)

include hO hπ

/-- **The algebraic two-chart description of the Tate model is the scheme's**: all three
components of `twoChartMap : twoChart → twoChartRingsOfAffine (toP1 ..)` are bijective. -/
theorem twoChartMap_bijective :
    Function.Bijective (twoChartMap π b₄ t κ hκ).f0 ∧
      Function.Bijective (twoChartMap π b₄ t κ hκ).f1 ∧
      Function.Bijective (twoChartMap π b₄ t κ hκ).f01 := by
  haveI := isReduced_T0 π b₄ t κ hκ ϖ hO hπ
  haveI := isReduced_T1 π b₄ t κ hκ ϖ hO hπ
  exact ⟨bijective_f0 π b₄ t κ hκ, bijective_f1 π b₄ t κ hκ, bijective_f01 π b₄ t κ hκ⟩

/-- `T0 ≃ Γ(𝒯, p⁻¹ U₀)` (`h ↦ u/ℓ₀`, `z ↦ w/ℓ₀`). -/
noncomputable def chartEquiv0 : T0 π b₄ t κ ≃ₐ[O] (D π b₄ t κ hκ).R0 :=
  AlgEquiv.ofBijective _ (twoChartMap_bijective π b₄ t κ hκ ϖ hO hπ).1

/-- `T1 ≃ Γ(𝒯, p⁻¹ U₁)` (`h' ↦ ℓ₀/u`, `w ↦ w/u`). -/
noncomputable def chartEquiv1 : T1 π b₄ t κ ≃ₐ[O] (D π b₄ t κ hκ).R1 :=
  AlgEquiv.ofBijective _ (twoChartMap_bijective π b₄ t κ hκ ϖ hO hπ).2.1

/-- `T01 = T1[1/h'] ≃ Γ(𝒯, p⁻¹ (U₀ ∩ U₁))`. -/
noncomputable def chartEquiv01 : T01 π b₄ t κ ≃ₐ[O] (D π b₄ t κ hκ).R01 :=
  AlgEquiv.ofBijective _ (twoChartMap_bijective π b₄ t κ hκ ϖ hO hπ).2.2

end Reduced

/-- **Over a discrete valuation ring** with uniformizer `ϖ ∣ π`, the identification
`twoChartMap` is an isomorphism of two-chart rings. -/
theorem twoChartMap_bijective_of_irreducible {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (π b₄ t κ : O) {b₆ : O} (hκ : κ * (t ^ 2 - b₆) = 1) {ϖ : O}
    (hϖ : Irreducible ϖ) (hπ : ϖ ∣ π) :
    Function.Bijective (twoChartMap π b₄ t κ hκ).f0 ∧
      Function.Bijective (twoChartMap π b₄ t κ hκ).f1 ∧
      Function.Bijective (twoChartMap π b₄ t κ hκ).f01 := by
  haveI : (Ideal.span {ϖ}).IsMaximal := hϖ.maximalIdeal_eq ▸ IsLocalRing.maximalIdeal.isMaximal O
  refine twoChartMap_bijective π b₄ t κ hκ ϖ (fun a ha ↦ ?_) hπ
  have h := Ideal.iInf_pow_eq_bot_of_isDomain (Ideal.span {ϖ})
    (Ideal.span_singleton_ne_top hϖ.not_isUnit)
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro n
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact ha n

end TateChartIdentification

end TemperedFundamentalGroups
