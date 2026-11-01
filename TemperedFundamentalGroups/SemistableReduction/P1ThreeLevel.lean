/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeChart
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Cusp
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Overlap

/-!
# Levels and special fibres of the model `h = t (t − 1) : ℙ¹_t → ℙ¹_X` (MR13 A1)

For the two-chart rings `P1Three.R0 = O[t]`, `P1Three.R1 = O[s][1/(1 − s)]`,
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

variable {O : Type u} [CommRing O] (ϖ : O)

variable (O) in
/-- **`R01 = R0[1/X]`** via `ρ₀`. -/
theorem isLocalization_rho0 :
    letI := (rho0 O : R0 O →+* R01 O).toAlgebra
    IsLocalization.Away (x0 O) (R01 O) := by
  letI := (rho0 O : R0 O →+* R01 O).toAlgebra
  have hm : ∀ a, algebraMap (R0 O) (R01 O) a = rho0 O a := fun _ ↦ rfl
  refine (isLocalization_iff ..).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [hm, map_pow, rho0_x0]
    exact (IsUnit.of_mul_eq_one_right _ (y1_mul_yinv O)).pow k
  · intro z
    obtain ⟨a, k, h⟩ := (twoChart O).exists0 z
    refine ⟨⟨a, ⟨_, k, rfl⟩⟩, ?_⟩
    change z * rho0 O (x0 O ^ k) = rho0 O a
    rw [map_pow, rho0_x0, mul_comm]
    exact h
  · intro a b hab
    obtain ⟨k, hk⟩ := (twoChart O).ker0 (a - b) (by
      change rho0 O (a - b) = 0
      rw [map_sub, ← hm, ← hm, hab, sub_self])
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    change x0 O ^ k * (a - b) = 0 at hk
    change x0 O ^ k * a = x0 O ^ k * b
    rwa [mul_sub, sub_eq_zero] at hk

variable (O) in
lemma towerR0R01 : letI := (rho0 O : R0 O →+* R01 O).toAlgebra
    IsScalarTower O (R0 O) (R01 O) :=
  letI := (rho0 O : R0 O →+* R01 O).toAlgebra
  IsScalarTower.of_algebraMap_eq fun o ↦ ((rho0 O).commutes o).symm

/-! ### The levels -/

/-- `ρ₀` at level `n`. -/
abbrev rho0n (n : ℕ) : Tn ϖ (R0 O) n →+* Tn ϖ (R01 O) n :=
  quotMap (rho0 O) (EtaleTower.Iv ϖ n)

/-- `ρ₁` at level `n`. -/
abbrev rho1n (n : ℕ) : Tn ϖ (R1 O) n →+* Tn ϖ (R01 O) n :=
  quotMap (IsScalarTower.toAlgHom O (R1 O) (R01 O)) (EtaleTower.Iv ϖ n)

/-- **The overlap at level `n` is `R0n[1/X]`.** -/
theorem isLocalization_rho0n (n : ℕ) :
    letI := (rho0n ϖ n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk _ (x0 O) : Tn ϖ (R0 O) n) (Tn ϖ (R01 O) n) := by
  letI := (rho0 O : R0 O →+* R01 O).toAlgebra
  haveI := towerR0R01 O
  haveI := isLocalization_rho0 O
  exact isLocalization_quotMap (x0 O) (EtaleTower.Iv ϖ n)

/-- **The overlap at level `n` is `R1n[1/Y]`.** -/
theorem isLocalization_rho1n (n : ℕ) :
    letI := (rho1n ϖ n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk _ (y1 O) : Tn ϖ (R1 O) n) (Tn ϖ (R01 O) n) :=
  isLocalization_quotMap (y1 O) (EtaleTower.Iv ϖ n)

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
    IsSMulRegular (Tn ϖ (R0 O) n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O (R0 O))) (x0 O) :
        Tn ϖ (R0 O) n) :=
  isSMulRegular_of ϖ (monic_G0 O) n

/-- **`Y` is regular on the levels of `R1`.** -/
theorem isSMulRegular_y1 (n : ℕ) :
    IsSMulRegular (Tn ϖ (R1 O) n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O (R1 O))) (y1 O) :
        Tn ϖ (R1 O) n) :=
  isSMulRegular_of ϖ (monic_G1 O) n

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
lemma finite_aeval_x0 : letI := (Polynomial.aeval (x0 O) :
      Polynomial O →ₐ[O] R0 O).toRingHom.toAlgebra
    Module.Finite (Polynomial O) (R0 O) :=
  finite_aeval_of (monic_G0 O)

variable (O) in
/-- `R1` is finite over `O[X]` via `Y`. -/
lemma finite_aeval_y1 : letI := (Polynomial.aeval (y1 O) :
      Polynomial O →ₐ[O] R1 O).toRingHom.toAlgebra
    Module.Finite (Polynomial O) (R1 O) :=
  finite_aeval_of (monic_G1 O)

/-! ### The special fibres -/

variable {k : Type u} [Field k] (θ : O →+* k)

variable (O) in
/-- **The special fibre of the overlap chart** `R01`. -/
abbrev R01s : Type u := EtaleTower.Ts θ (R01 O)

variable (O) in
/-- `R1/J → R01/J`. -/
@[reducible] def alg1s : Algebra (EtaleTower.Ts θ (R1 O)) (R01s O θ) :=
  (EtaleNil.red (RingHom.ker θ) (IsScalarTower.toAlgHom O (R1 O) (R01 O))).toRingHom.toAlgebra

variable (O) in
/-- `R0/J → R01/J` (through `ρ₀`). -/
@[reducible] def alg0s : Algebra (EtaleTower.Ts θ (R0 O)) (R01s O θ) :=
  (EtaleNil.red (RingHom.ker θ) (rho0 O)).toRingHom.toAlgebra

variable (O) in
/-- **`R01/J = (R1/J)[1/Ȳ]`.** -/
theorem isLocalization_alg1s : letI := alg1s O θ
    IsLocalization.Away (Ideal.Quotient.mk _ (y1 O) : EtaleTower.Ts θ (R1 O)) (R01s O θ) :=
  EtaleNil.isLocalization_red (RingHom.ker θ) (y1 O)

variable (O) in
/-- **`R01/J = (R0/J)[1/X̄]`.** -/
theorem isLocalization_alg0s : letI := alg0s O θ
    IsLocalization.Away (Ideal.Quotient.mk _ (x0 O) : EtaleTower.Ts θ (R0 O)) (R01s O θ) := by
  letI := (rho0 O : R0 O →+* R01 O).toAlgebra
  haveI := towerR0R01 O
  haveI := isLocalization_rho0 O
  exact EtaleNil.isLocalization_red (RingHom.ker θ) (x0 O)

variable {θ}

/-- `C1[1/Ȳ]` over `R01/J`. -/
@[reducible] def algC1x (C1 : Type u) [CommRing C1] [Algebra (EtaleTower.Ts θ (R1 O)) C1] :
    Algebra (R01s O θ) (Localization.Away (algebraMap (EtaleTower.Ts θ (R1 O)) C1
      (Ideal.Quotient.mk _ (y1 O)))) :=
  letI := alg1s O θ
  haveI := isLocalization_alg1s O θ
  AwayAlg.alg _

lemma towerC1x (C1 : Type u) [CommRing C1] [Algebra (EtaleTower.Ts θ (R1 O)) C1] :
    letI := alg1s O θ; letI := algC1x C1 (O := O) (θ := θ)
    IsScalarTower (EtaleTower.Ts θ (R1 O)) (R01s O θ)
      (Localization.Away (algebraMap (EtaleTower.Ts θ (R1 O)) C1
        (Ideal.Quotient.mk _ (y1 O)))) :=
  letI := alg1s O θ
  haveI := isLocalization_alg1s O θ
  AwayAlg.tower _

/-- `C0[1/X̄]` over `R01/J`. -/
@[reducible] def algC0x (C0 : Type u) [CommRing C0] [Algebra (EtaleTower.Ts θ (R0 O)) C0] :
    Algebra (R01s O θ) (Localization.Away (algebraMap (EtaleTower.Ts θ (R0 O)) C0
      (Ideal.Quotient.mk _ (x0 O)))) :=
  letI := alg0s O θ
  haveI := isLocalization_alg0s O θ
  AwayAlg.alg _

lemma towerC0x (C0 : Type u) [CommRing C0] [Algebra (EtaleTower.Ts θ (R0 O)) C0] :
    letI := alg0s O θ; letI := algC0x C0 (O := O) (θ := θ)
    IsScalarTower (EtaleTower.Ts θ (R0 O)) (R01s O θ)
      (Localization.Away (algebraMap (EtaleTower.Ts θ (R0 O)) C0
        (Ideal.Quotient.mk _ (x0 O)))) :=
  letI := alg0s O θ
  haveI := isLocalization_alg0s O θ
  AwayAlg.tower _

end

end P1Three

end SemistableReduction
