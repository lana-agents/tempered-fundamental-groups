/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeChart
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Cusp
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Overlap

/-!
# Levels and special fibres of the model `h = t (t − 1) (t − a) : ℙ¹_t → ℙ¹_X` (MR13 A1)

For the two-chart rings `P1Three.R0 = O[t]`, `P1Three.R1` (the chart `ℙ¹_t ∖ {0, 1, a}`),
`P1Three.R01 = R1[1/Y] = R0[1/X]` of `P1ThreeChart`:

* **`P1Three.isLocalization_rho0`**: `R01 = R0[1/X]` via `ρ₀`;
* the levels `Tn ϖ R n = R/ϖⁿ⁺¹` of the three charts with `ρ₀`, `ρ₁` at level `n`
  (`rho0n`, `rho1n`) and **`isLocalization_rho0n`**, **`isLocalization_rho1n`**;
* **`isSMulRegular_x0`**, **`isSMulRegular_y1`**: the base coordinates `X` and `Y` are regular on
  the levels (`R0`, `R1` are free over `O[X]`);
* `finite_aeval_x0`, `finite_aeval_y1`: the charts are finite over `O[X]` via `X`, `Y`;
* the special fibre `R01s` of the overlap, `alg1s`, `alg0s` with
  `R01s = (R1/J)[1/Ȳ] = (R0/J)[1/X̄]`
  (`isLocalization_alg1s`, `isLocalization_alg0s`) and `algC1x`, `algC0x`
  (`C1[1/Ȳ]`, `C0[1/X̄]` over `R01s`, the type of the overlap datum `ω`).

All proofs follow the Tate case (`TateLevel`, `TateGlue0Overlap`, `TateGlue0Cusp`), whose generic
lemmas (`TateLevel.quotMap`, `TateLevel.isLocalization_quotMap`, `TateGlue0.X_mul_mem`,
`BasisIdeal`, `AwayAlg`) are reused.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] (ϖ : O) (a : O)

variable (O) in
/-- **`R01 = R0[1/X]`** via `ρ₀`. -/
theorem isLocalization_rho0 :
    letI := (rho0 O a : R0 O a →+* R01 O a).toAlgebra
    IsLocalization.Away (x0 O a) (R01 O a) := by
  letI := (rho0 O a : R0 O a →+* R01 O a).toAlgebra
  have hm : ∀ c, algebraMap (R0 O a) (R01 O a) c = rho0 O a c := fun _ ↦ rfl
  refine (isLocalization_iff ..).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [hm, map_pow, rho0_x0]
    exact (IsUnit.of_mul_eq_one_right _ (y1_mul_yinv O a)).pow k
  · intro z
    obtain ⟨c, k, h⟩ := (twoChart O a).exists0 z
    refine ⟨⟨c, ⟨_, k, rfl⟩⟩, ?_⟩
    change z * rho0 O a (x0 O a ^ k) = rho0 O a c
    rw [map_pow, rho0_x0, mul_comm]
    exact h
  · intro c d hab
    obtain ⟨k, hk⟩ := (twoChart O a).ker0 (c - d) (by
      change rho0 O a (c - d) = 0
      rw [map_sub, ← hm, ← hm, hab, sub_self])
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    change x0 O a ^ k * (c - d) = 0 at hk
    change x0 O a ^ k * c = x0 O a ^ k * d
    rwa [mul_sub, sub_eq_zero] at hk

variable (O) in
lemma towerR0R01 : letI := (rho0 O a : R0 O a →+* R01 O a).toAlgebra
    IsScalarTower O (R0 O a) (R01 O a) :=
  letI := (rho0 O a : R0 O a →+* R01 O a).toAlgebra
  IsScalarTower.of_algebraMap_eq fun o ↦ ((rho0 O a).commutes o).symm

/-! ### The levels -/

/-- `ρ₀` at level `n`. -/
abbrev rho0n (n : ℕ) : Tn ϖ (R0 O a) n →+* Tn ϖ (R01 O a) n :=
  quotMap (rho0 O a) (EtaleTower.Iv ϖ n)

/-- `ρ₁` at level `n`. -/
abbrev rho1n (n : ℕ) : Tn ϖ (R1 O a) n →+* Tn ϖ (R01 O a) n :=
  quotMap (IsScalarTower.toAlgHom O (R1 O a) (R01 O a)) (EtaleTower.Iv ϖ n)

/-- **The overlap at level `n` is `R0n[1/X]`.** -/
theorem isLocalization_rho0n (n : ℕ) :
    letI := (rho0n ϖ a n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk _ (x0 O a) : Tn ϖ (R0 O a) n) (Tn ϖ (R01 O a) n) := by
  letI := (rho0 O a : R0 O a →+* R01 O a).toAlgebra
  haveI := towerR0R01 O a
  haveI := isLocalization_rho0 O a
  exact isLocalization_quotMap (x0 O a) (EtaleTower.Iv ϖ n)

/-- **The overlap at level `n` is `R1n[1/Y]`.** -/
theorem isLocalization_rho1n (n : ℕ) :
    letI := (rho1n ϖ a n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk _ (y1 O a) : Tn ϖ (R1 O a) n) (Tn ϖ (R01 O a) n) :=
  isLocalization_quotMap (y1 O a) (EtaleTower.Iv ϖ n)

/-! ### Regularity of the base coordinates on the levels -/

/-- A free `O[X]`-algebra `AdjoinRoot G` (`G` monic): the image of `X` is regular on the levels. -/
theorem isSMulRegular_of {G : O[X][X]} (hG : G.Monic) (n : ℕ) :
    IsSMulRegular (Tn ϖ (AdjoinRoot G) n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O (AdjoinRoot G)))
        (AdjoinRoot.of G X) : Tn ϖ (AdjoinRoot G) n) := by
  set b := (AdjoinRoot.powerBasis' hG).basis
  set I := (EtaleTower.Iv ϖ n).map (algebraMap O O[X])
  have hI : (EtaleTower.Iv ϖ n).map (algebraMap O (AdjoinRoot G)) =
      I.map (algebraMap O[X] (AdjoinRoot G)) := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  intro y z hyz
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  change Ideal.Quotient.mk _ (AdjoinRoot.of G X) * Ideal.Quotient.mk _ y =
    Ideal.Quotient.mk _ (AdjoinRoot.of G X) * Ideal.Quotient.mk _ z at hyz
  rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← mul_sub] at hyz
  rw [Ideal.Quotient.eq]
  rw [hI] at hyz ⊢
  refine BasisIdeal.mem_of_repr_mem b I fun i ↦ TateGlue0.X_mul_mem ϖ ?_
  have h := BasisIdeal.repr_mem b I hyz i
  rwa [show AdjoinRoot.of G X * (y - z) = (X : O[X]) • (y - z) by
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq], map_smul, Finsupp.smul_apply,
    smul_eq_mul] at h

/-- **`X` is regular on the levels of `R0`.** -/
theorem isSMulRegular_x0 (n : ℕ) :
    IsSMulRegular (Tn ϖ (R0 O a) n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O (R0 O a))) (x0 O a) :
        Tn ϖ (R0 O a) n) :=
  isSMulRegular_of ϖ (monic_G0 O a) n

/-- **`Y` is regular on the levels of `R1`.** -/
theorem isSMulRegular_y1 (n : ℕ) :
    IsSMulRegular (Tn ϖ (R1 O a) n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O (R1 O a))) (y1 O a) :
        Tn ϖ (R1 O a) n) :=
  isSMulRegular_of ϖ (monic_G1 O a) n

/-! ### Finiteness over `O[X]` -/

/-- A finite algebra is finite for any equal algebra structure. -/
lemma finite_of_eq {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (f : R →+* S) (hf : f = algebraMap R S) : letI := f.toAlgebra; Module.Finite R S := by
  subst hf
  rw [show (algebraMap R S).toAlgebra = ‹Algebra R S› from Algebra.algebra_ext _ _ fun _ ↦ rfl]
  infer_instance

/-- `AdjoinRoot G` is finite over `O[X]` via `X ↦ of X`. -/
lemma finite_aeval_of {G : O[X][X]} (hG : G.Monic) :
    letI := (Polynomial.aeval (AdjoinRoot.of G X) :
      Polynomial O →ₐ[O] AdjoinRoot G).toRingHom.toAlgebra
    Module.Finite (Polynomial O) (AdjoinRoot G) :=
  haveI : Module.Finite O[X] (AdjoinRoot G) := (AdjoinRoot.powerBasis' hG).finite
  finite_of_eq _ (Polynomial.ringHom_ext (fun o ↦ by
    change Polynomial.aeval (AdjoinRoot.of G X) (Polynomial.C o) = AdjoinRoot.of G (Polynomial.C o)
    rw [Polynomial.aeval_C, TateTwoChart.of_C]) (by
    change Polynomial.aeval (AdjoinRoot.of G X) Polynomial.X = AdjoinRoot.of G Polynomial.X
    rw [Polynomial.aeval_X]))

variable (O) in
/-- `R0` is finite over `O[X]` via `X`. -/
lemma finite_aeval_x0 : letI := (Polynomial.aeval (x0 O a) :
      Polynomial O →ₐ[O] R0 O a).toRingHom.toAlgebra
    Module.Finite (Polynomial O) (R0 O a) :=
  finite_aeval_of (monic_G0 O a)

variable (O) in
/-- `R1` is finite over `O[X]` via `Y`. -/
lemma finite_aeval_y1 : letI := (Polynomial.aeval (y1 O a) :
      Polynomial O →ₐ[O] R1 O a).toRingHom.toAlgebra
    Module.Finite (Polynomial O) (R1 O a) :=
  finite_aeval_of (monic_G1 O a)

/-! ### The special fibres -/

variable {k : Type u} [Field k] (θ : O →+* k)

variable (O) in
/-- **The special fibre of the overlap chart** `R01`. -/
abbrev R01s : Type u := EtaleTower.Ts θ (R01 O a)

variable (O) in
/-- `R1/J → R01/J`. -/
@[reducible] def alg1s : Algebra (EtaleTower.Ts θ (R1 O a)) (R01s O a θ) :=
  (EtaleNil.red (RingHom.ker θ) (IsScalarTower.toAlgHom O (R1 O a) (R01 O a))).toRingHom.toAlgebra

variable (O) in
/-- `R0/J → R01/J` (through `ρ₀`). -/
@[reducible] def alg0s : Algebra (EtaleTower.Ts θ (R0 O a)) (R01s O a θ) :=
  (EtaleNil.red (RingHom.ker θ) (rho0 O a)).toRingHom.toAlgebra

variable (O) in
/-- **`R01/J = (R1/J)[1/Ȳ]`.** -/
theorem isLocalization_alg1s : letI := alg1s O a θ
    IsLocalization.Away (Ideal.Quotient.mk _ (y1 O a) : EtaleTower.Ts θ (R1 O a)) (R01s O a θ) :=
  EtaleNil.isLocalization_red (RingHom.ker θ) (y1 O a)

variable (O) in
/-- **`R01/J = (R0/J)[1/X̄]`.** -/
theorem isLocalization_alg0s : letI := alg0s O a θ
    IsLocalization.Away (Ideal.Quotient.mk _ (x0 O a) : EtaleTower.Ts θ (R0 O a)) (R01s O a θ) := by
  letI := (rho0 O a : R0 O a →+* R01 O a).toAlgebra
  haveI := towerR0R01 O a
  haveI := isLocalization_rho0 O a
  exact EtaleNil.isLocalization_red (RingHom.ker θ) (x0 O a)

variable {θ}

/-- `C1[1/Ȳ]` over `R01/J`. -/
@[reducible] def algC1x (C1 : Type u) [CommRing C1] [Algebra (EtaleTower.Ts θ (R1 O a)) C1] :
    Algebra (R01s O a θ) (Localization.Away (algebraMap (EtaleTower.Ts θ (R1 O a)) C1
      (Ideal.Quotient.mk _ (y1 O a)))) :=
  letI := alg1s O a θ
  haveI := isLocalization_alg1s O a θ
  AwayAlg.alg _

lemma towerC1x (C1 : Type u) [CommRing C1] [Algebra (EtaleTower.Ts θ (R1 O a)) C1] :
    letI := alg1s O a θ; letI := algC1x a C1 (θ := θ)
    IsScalarTower (EtaleTower.Ts θ (R1 O a)) (R01s O a θ)
      (Localization.Away (algebraMap (EtaleTower.Ts θ (R1 O a)) C1
        (Ideal.Quotient.mk _ (y1 O a)))) :=
  letI := alg1s O a θ
  haveI := isLocalization_alg1s O a θ
  AwayAlg.tower _

/-- `C0[1/X̄]` over `R01/J`. -/
@[reducible] def algC0x (C0 : Type u) [CommRing C0] [Algebra (EtaleTower.Ts θ (R0 O a)) C0] :
    Algebra (R01s O a θ) (Localization.Away (algebraMap (EtaleTower.Ts θ (R0 O a)) C0
      (Ideal.Quotient.mk _ (x0 O a)))) :=
  letI := alg0s O a θ
  haveI := isLocalization_alg0s O a θ
  AwayAlg.alg _

lemma towerC0x (C0 : Type u) [CommRing C0] [Algebra (EtaleTower.Ts θ (R0 O a)) C0] :
    letI := alg0s O a θ; letI := algC0x a C0 (θ := θ)
    IsScalarTower (EtaleTower.Ts θ (R0 O a)) (R01s O a θ)
      (Localization.Away (algebraMap (EtaleTower.Ts θ (R0 O a)) C0
        (Ideal.Quotient.mk _ (x0 O a)))) :=
  letI := alg0s O a θ
  haveI := isLocalization_alg0s O a θ
  AwayAlg.tower _

end

end P1Three

end SemistableReduction
