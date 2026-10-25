/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.AbhyankarProduct
import TemperedFundamentalGroups.SemistableReduction.TameGalois

/-!
# Abhyankar's lemma for Galois extensions of degree prime to the residue characteristic (T2, S1)

Let `O` be a discrete valuation ring with fraction field `K` and uniformizer `ϖ`, and `L / K` a
finite Galois extension whose group has order `e = |Gal(L/K)|` prime to the residue
characteristic. Then (step S0, `TameGalois`) the integral closure `B` of `O` in `L` is tame over
`O` with ramification indices dividing `e`, and `e` is a unit of `O`; hence Abhyankar's lemma
applies:

* **`Abhyankar.tame_of_isGalois`**: the hypothesis `htame` of `Abhyankar.etale` for
  `B = integralClosure O L` and `e = |Gal(L/K)|`;
* **`Abhyankar.etale_integralClosure_adjoinRoot_of_isGalois`**: after adjoining `ϖ ^ (1/e)`, the
  normalisation is étale: the integral closure of `O' = O[Y]/(Y ^ e - ϖ)` in
  `L[Y]/(Y ^ e - ϖ) = L ⊗_K K'` is étale over `O'`.

This is the generic-point step of the converse "coverings of degree a `Σ`-integer have admissible
reduction" ([Mzk1] §3.13, proof, Abhyankar's lemma at the generic points of the special fibre;
[SemiAnbd] Cor 3.11, proof): applied to the discrete valuation rings `T_𝔭` of the chart rings `T`
of a model at the height-one primes `𝔭` over `ϖ` (the generic points of the special fibre), at
which `ϖ` is a uniformizer when the special fibre is reduced.
-/

open Polynomial IsLocalRing

namespace SemistableReduction

namespace Abhyankar

variable {O K L : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Field K] [Algebra O K] [IsFractionRing O K]
  [Field L] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
  [FiniteDimensional K L] [IsGalois K L]

include K in
/-- **Tameness of a Galois extension of order prime to the residue characteristic**: the
hypothesis `htame` of `Abhyankar.etale` for the integral closure of `O` in `L` and
`e = |Gal(L/K)|`. -/
theorem tame_of_isGalois
    (hq : (Nat.card Gal(L/K)).Coprime (ringExpChar (O ⧸ maximalIdeal O))) :
    ∀ (𝔓 : Ideal (integralClosure O L)) [𝔓.IsPrime] [𝔓.LiesOver (maximalIdeal O)],
      𝔓.ramificationIdx O ∣ Nat.card Gal(L/K) ∧
        Algebra.IsSeparable (O ⧸ maximalIdeal O) (integralClosure O L ⧸ 𝔓) := by
  haveI : IsIntegralClosure (integralClosure O L) O L := integralClosure.isIntegralClosure O L
  haveI : Module.Finite O (integralClosure O L) := IsIntegralClosure.finite O K L _
  haveI : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  haveI : Module.Free O (integralClosure O L) := IsIntegralClosure.module_free O K L _
  haveI : IsFractionRing (integralClosure O L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  haveI : IsGaloisGroup Gal(L/K) O (integralClosure O L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) O (integralClosure O L) K L
  exact Ideal.tame_of_coprime_card (integralClosure O L) Gal(L/K) hq

omit [Algebra O K] [IsFractionRing O K] [Algebra O L] [IsScalarTower O K L] [IsGalois K L] in
/-- `|Gal(L/K)|` is a unit of `O` (the hypothesis `he` of `Abhyankar.etale`). -/
theorem isUnit_card_of_isGalois
    (hq : (Nat.card Gal(L/K)).Coprime (ringExpChar (O ⧸ maximalIdeal O))) :
    IsUnit ((Nat.card Gal(L/K) : ℕ) : O) :=
  Ideal.isUnit_card_of_coprime (G := Gal(L/K)) hq

include K in
/-- **Abhyankar's lemma for a Galois extension of order prime to the residue characteristic**:
with `e = |Gal(L/K)|` and `O' = O[Y]/(Y ^ e - ϖ)`, the integral closure of `O'` in
`L[Y]/(Y ^ e - ϖ)` (`= L ⊗_K K'`, `K' = Frac O'`) is étale over `O'`. -/
theorem etale_integralClosure_adjoinRoot_of_isGalois {ϖ : O} (hϖ : Irreducible ϖ)
    (hq : (Nat.card Gal(L/K)).Coprime (ringExpChar (O ⧸ maximalIdeal O))) :
    letI := rootAlgebra _ (adjoinRoot_root_pow (L := L) ϖ (Nat.card Gal(L/K)))
    Algebra.Etale (RootOfUniformizer.Ring ϖ (Nat.card Gal(L/K)))
      (integralClosure (RootOfUniformizer.Ring ϖ (Nat.card Gal(L/K)))
        (AdjoinRoot (X ^ Nat.card Gal(L/K) - C (algebraMap O L ϖ)))) := by
  haveI : IsIntegralClosure (integralClosure O L) O L := integralClosure.isIntegralClosure O L
  exact etale_integralClosure_adjoinRoot (K := K) (B := integralClosure O L) hϖ
    (isUnit_card_of_isGalois (O := O) (K := K) (L := L) hq) (tame_of_isGalois (K := K) hq)

end Abhyankar

end SemistableReduction
