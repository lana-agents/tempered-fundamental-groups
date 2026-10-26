/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerTateChart

/-!
# Tame covers of the quadratic node chart are tamely Kummer at the nodes (MR12 T2 S5)

The version of `TateTwoChartNode.isTameKummerAt_T1D` for the quadratic node chart
`NR = QuadNode.R ϖ m c D` itself (the chart of `Admissible.Covering` in `TateGlue1`), with the node
coordinates `uR, vR`: **`TateTwoChartNode.isTameKummerAt_NR`** (from
`NodeCover.isTameKummerAt_of_isLocalization_etale` for the étale chart `NE = NR[1/(2S + 1)]`;
`2S + 1` is a unit at the nodes, `twoS1_notMem_NR`).
-/

universe u

open IsLocalRing Module

namespace SemistableReduction

namespace TateTwoChartNode

open KummerEtale TateTwoChart

variable {O : Type u} [CommRing O] {b₄ b₆ ϖ ε : O} {m : ℕ}

/-- **`2S + 1` is a unit at the nodes of `NR`.** -/
lemma twoS1_notMem_NR (𝔫 : Ideal (NR b₄ b₆ ϖ m ε)) [𝔫.IsPrime]
    (h𝔫 : 𝔫.comap (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε)) = Node.closedPoint ϖ (ϖ ^ m)) :
    twoS1 b₄ b₆ ϖ m ε ∉ 𝔫 := by
  intro hx
  have hcP : algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε) (cN b₄ b₆ ϖ m ε) ∈ 𝔫 := by
    rw [← Ideal.mem_comap, h𝔫]
    exact cN_mem_closedPoint b₄ b₆
  have h3 := 𝔫.pow_mem_of_mem hx 2 two_pos
  rw [twoS1_sq] at h3
  have h1P : (1 : NR b₄ b₆ ϖ m ε) ∈ 𝔫 := (𝔫.add_mem_iff_left (𝔫.mul_mem_left _ hcP)).mp h3
  exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h1P)

set_option maxHeartbeats 1000000 in
-- Many localization structures on the concrete charts.
/-- **Tame covers of the quadratic node chart are tamely Kummer at the nodes** (S4 + S5.0 for
`NR`): as `isTameKummerAt_T1D`, for primes `𝔫` of `NR` over the closed point of the node ring and
the node coordinates `uR, vR`. -/
theorem isTameKummerAt_NR [IsDomain O] [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ)
    [NeZero m] (hε : IsUnit ε) {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M')
    (𝔫 : Ideal (NR b₄ b₆ ϖ m ε)) [𝔫.IsPrime]
    (h𝔫 : 𝔫.comap (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε)) = Node.closedPoint ϖ (ϖ ^ m))
    (K : Type u) [Field K] [Algebra (NR b₄ b₆ ϖ m ε) K] [IsFractionRing (NR b₄ b₆ ϖ m ε) K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra (NR b₄ b₆ ϖ m ε) L]
    [IsScalarTower (NR b₄ b₆ ϖ m ε) K L]
    [Algebra (Localization.AtPrime 𝔫) L] [IsScalarTower (NR b₄ b₆ ϖ m ε) (Localization.AtPrime 𝔫) L]
    (B : Type u) [CommRing B] [Algebra (Localization.AtPrime 𝔫) B] [Algebra B L]
    [IsScalarTower (Localization.AtPrime 𝔫) B L] [IsIntegralClosure B (Localization.AtPrime 𝔫) L]
    (hunr : ∀ (Q : Ideal B) [Q.IsPrime],
      Q.comap (algebraMap (Localization.AtPrime 𝔫) B) ≠ maximalIdeal (Localization.AtPrime 𝔫) →
      Algebra.IsUnramifiedAt (Localization.AtPrime 𝔫) Q) :
    IsTameKummerAt ϖ m M' (uR b₄ b₆ ϖ m ε) (vR b₄ b₆ ϖ m ε) L 𝔫 := by
  have hϖp : Prime ϖ := hϖ.prime
  have hm : 1 ≤ m := Nat.pos_of_neZero m
  haveI : (Ideal.span {ϖ}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hϖ
  haveI : (Node.closedPoint ϖ (ϖ ^ m)).IsPrime :=
    (Node.isMaximal_closedPoint ϖ (dvd_pow_self ϖ (NeZero.ne m))).isPrime
  haveI : IsDomain (NR b₄ b₆ ϖ m ε) := isDomain_NR b₄ b₆ hϖp hm hε
  haveI : IsDomain (NE b₄ b₆ ϖ m ε) := isDomain_NE hϖp hm hε
  haveI : Algebra.Etale (NR b₄ b₆ ϖ m ε) (NE b₄ b₆ ϖ m ε) :=
    Algebra.Etale.of_isLocalizationAway (twoS1 b₄ b₆ ϖ m ε)
  have hdisj : Disjoint ((Submonoid.powers (twoS1 b₄ b₆ ϖ m ε) : Submonoid _) :
      Set (NR b₄ b₆ ϖ m ε)) 𝔫 := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hy
    exact twoS1_notMem_NR 𝔫 h𝔫 (Ideal.IsPrime.mem_of_pow_mem ‹_› k hy)
  exact NodeCover.isTameKummerAt_of_isLocalization_etale hϖ hqM hq hM' (NE b₄ b₆ ϖ m ε)
    (Submonoid.powers (twoS1 b₄ b₆ ϖ m ε)) (algebraMap (A ϖ m) (NR b₄ b₆ ϖ m ε))
    (fun a ↦ IsScalarTower.algebraMap_apply _ _ _ a) 𝔫 hdisj h𝔫 K hζ L hL B hunr

end TateTwoChartNode

end SemistableReduction
