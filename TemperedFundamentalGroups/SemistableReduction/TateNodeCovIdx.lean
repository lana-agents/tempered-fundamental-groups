/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeCovering
import TemperedFundamentalGroups.SemistableReduction.KummerFactorPrimes

/-!
# The Kummer factors of `cov₀` are the points of the normalisation over the nodes
(MR12, interface I5(a))

For the admissible covering `covNR` of the Tate node chart `NR` defined by the normalisation `B`
of `NR` in a tame cover, the index set of the Kummer factors over the two nodes is
`Σ j : Fin 2, Fin (kummerDataNR … j).r`; **`TateTwoChartNode.covNRIdx`** identifies it with
`Σ j : Fin 2, {Q : Ideal B // Q.IsPrime ∧ Q ∩ NR = 𝔪ⱼ}` (the node points of the special fibre of
`Spec B`), via `FormalKummer.KummerNormAtData.primesEquiv` (`k` separably closed, so the étale
neighbourhoods of the nodes have trivial residue field extensions).
-/

universe u

open Module

namespace SemistableReduction

open KummerEtale AdmissibleLift KummerPrimes

namespace TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {b₄ b₆ ϖ : O} {m : ℕ} {ε : O}

local notation "𝒩" => NR b₄ b₆ ϖ m ε

/-- The residue field of the node `j` is `k`. -/
def nodeResidue (hθ : Function.Surjective θ) (hϖ : θ ϖ = 0) (hm : 1 ≤ m) (j : Fin 2) :
    k ≃+* 𝒩 ⧸ nodeIdeal b₄ b₆ ϖ m ε hϖ hm j :=
  (RingHom.quotientKerEquivOfSurjective (evNode_surjective hθ hϖ hm j)).symm

/-- **The node points of `B` ↔ the Kummer factors at the node `j`**, for any choice of the
Kummer data `D` at `j` (`k` separably closed). -/
def nodePrimesEquiv [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
    (hker : RingHom.ker θ = Ideal.span {ϖ}) [NeZero m] {M' : ℕ} {B : Type u} [CommRing B]
    [Algebra 𝒩 B] (j : Fin 2)
    (D : FormalKummer.KummerNormAtData ϖ m M' (uR b₄ b₆ ϖ m ε) (vR b₄ b₆ ϖ m ε) B
      (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j)) :
    PrimesOver B (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j) ≃ Fin D.r :=
  haveI := isMaximal_nodeIdeal (b₄ := b₄) (b₆ := b₆) (ε := ε) hθ.out (θ_ϖ hker)
    (Nat.pos_of_neZero m) j
  D.primesEquiv
    (EtaleResidue.surjective_of_isSepClosed' _ D.𝔫 D.comap_eq
      (nodeResidue hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m) j).toRingHom
      (nodeResidue hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m) j).surjective)
    (genIdeal_le_nodeIdeal _ _ j (uR_mem j)) (genIdeal_le_nodeIdeal _ _ j (vR_mem j))
    (ϖ_mem_nodeIdeal hker (Nat.pos_of_neZero m) j) (Nat.pos_of_neZero m)

/-- **I5(a) at the Tate node chart: the Kummer factors of `covNR` are the points of the
normalisation `B` over the two nodes.** -/
def covNRIdx [Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L]
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (hπe : θ (ϖ ^ m) = 0)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩))) :
    (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).ι ≃
      Σ j : Fin 2, PrimesOver B (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j) :=
  Equiv.sigmaCongrRight fun j ↦ (nodePrimesEquiv hker j
    (kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B j)).symm

end

end TateTwoChartNode

end SemistableReduction
