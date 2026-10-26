/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeIdeals
import TemperedFundamentalGroups.SemistableReduction.KummerNRChart
import TemperedFundamentalGroups.SemistableReduction.NormLocalUnramified
import TemperedFundamentalGroups.SemistableReduction.TateNodeNormal

/-!
# The formal Kummer form of a tame cover of the Tate node chart (MR12 T2 S5, `kummer` field)

Let `NR` be the quadratic node chart of the Tate model over a discrete valuation ring `O`
(uniformiser `ϖ`, residue map `θ : O → k` onto a separably closed field, `ker θ = (ϖ)`), with node
coordinates `uR vR = ϖᵐ`, `m = q M'`. Let `L` be a finite Galois extension of `K = Frac NR` of
degree prime to `q`, with `μ_{M'} ⊆ K`, and `B` the normalisation of `NR` in `L`. If the
normalisation is unramified over `NR` at every prime lying over a prime strictly inside one of the
two node ideals (`hunr`: the cover is unramified over the punctured neighbourhoods of the nodes —
étale over the generic fibre there, and unramified at the generic points of the special fibre by
the tame base change of [Mzk1] §3, input A1 of the plan), then
(**`TateTwoChartNode.exists_kummer_NR`**) the special fibre `B/JB` is formally Kummer along
`V(ū + v̄)` with respect to the formal node coordinates `NodeChart.φ`:

  `(NR/J)^∧ ⊗ B/JB ≅ ∏_{(j, i)} KummerPiece φ εⱼ (dⱼᵢ)`,  `dⱼᵢ ∣ M'`,

`εⱼ` the idempotents of the two nodes (`CompletionProd.idem`): the `kummer` field of the
admissible covering `cov₀` of the node chart.

Proof: `isTameKummerAt_NR` at the two nodes `nodeIdeal j` (S5.3), with its local unramifiedness
hypothesis from `hunr` by `NormLocal.isUnramifiedAt`, then `IsTameKummerAt.isKummerNormAt` and
`FormalKummer.exists_kummer`.
-/

universe u

open TensorProduct Module

namespace SemistableReduction

open KummerEtale AdmissibleLift FormalKummer

namespace TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {b₄ b₆ ϖ : O} {m : ℕ} {ε : O}

local notation "𝒩" => NR b₄ b₆ ϖ m ε

lemma θ_ϖ (hker : RingHom.ker θ = Ideal.span {ϖ}) : θ ϖ = 0 := by
  rw [← RingHom.mem_ker, hker]
  exact Ideal.mem_span_singleton_self ϖ

instance isMaximal_sIdeal_nodeIdeal [hθ : Fact (Function.Surjective θ)] (hϖ : θ ϖ = 0)
    (hm : 1 ≤ m) (j : Fin 2) :
    (FormalKummer.sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε hϖ hm j)).IsMaximal :=
  haveI := isMaximal_nodeIdeal (b₄ := b₄) (b₆ := b₆) (ε := ε) hθ.out hϖ hm j
  isMaximal_sIdeal _ (J_le_nodeIdeal hϖ hm j)

/-- **The normalisation of a tame cover of the Tate node chart is tamely Kummer at the nodes**
(`isTameKummerAt_NR` + `IsTameKummerAt.isKummerNormAt`). -/
theorem isKummerNormAt_NR [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M')
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (hunr : ∀ (j : Fin 2) (Q : Ideal (integralClosure 𝒩 L)) [Q.IsPrime],
      Q.comap (algebraMap 𝒩 (integralClosure 𝒩 L)) <
        nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j →
      Algebra.IsUnramifiedAt 𝒩 Q)
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L] (j : Fin 2) :
    IsKummerNormAt ϖ m M' (uR b₄ b₆ ϖ m ε) (vR b₄ b₆ ϖ m ε) B
      (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j) := by
  have hϖ0 : θ ϖ = 0 := θ_ϖ hker
  have hm : 1 ≤ m := Nat.pos_of_neZero m
  haveI : IsDomain 𝒩 := isDomain_NR b₄ b₆ hϖ.prime hm hε
  have hinj : Function.Injective (algebraMap 𝒩 L) := by
    rw [IsScalarTower.algebraMap_eq 𝒩 K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective 𝒩 K)
  set 𝔫 := nodeIdeal b₄ b₆ ϖ m ε hϖ0 hm j
  haveI : 𝔫.IsMaximal := isMaximal_nodeIdeal hθ.out hϖ0 hm j
  letI := NormLocal.algAtPrime 𝔫 hinj
  haveI := NormLocal.isScalarTower_algAtPrime 𝔫 hinj
  have h := isTameKummerAt_NR hϖ hε hqM hq hM' 𝔫 (comap_nodeIdeal hϖ0 hm hker j) K hζ L hL
    (integralClosure (Localization.AtPrime 𝔫) L)
    (NormLocal.isUnramifiedAt hinj (hunr j))
  exact h.isKummerNormAt hϖ.ne_zero

/-- **The special fibre of a tame cover of the Tate node chart is formally Kummer along the
nodes.** -/
theorem exists_kummer_NR [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M')
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (hunr : ∀ (j : Fin 2) (Q : Ideal (integralClosure 𝒩 L)) [Q.IsPrime],
      Q.comap (algebraMap 𝒩 (integralClosure 𝒩 L)) <
        nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j →
      Algebra.IsUnramifiedAt 𝒩 Q)
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L] (hπe : θ (ϖ ^ m) = 0) :
    ∃ (r : Fin 2 → ℕ) (d : ∀ j, Fin (r j) → ℕ) (hd : ∀ j i, 0 < d j i), (∀ j i, d j i ∣ M') ∧
      Nonempty (Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩)) ⊗[Rs θ 𝒩] Cs θ 𝒩 B
        ≃ₐ[Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩))]
        ∀ p : (Σ j, Fin (r j)), Admissible.KummerPiece (NodeChart.φ 𝒩 hπe)
          (CompletionProd.idem (sIdeal_injective (θ := θ) (θ_ϖ hker) (Nat.pos_of_neZero m))
            (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
            (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m)) p.1) (hd p.1 p.2)) := by
  have hϖ0 : θ ϖ = 0 := θ_ϖ hker
  have hm : 1 ≤ m := Nat.pos_of_neZero m
  have hxy : uR b₄ b₆ ϖ m ε * vR b₄ b₆ ϖ m ε = algebraMap O 𝒩 (ϖ ^ m) := by
    rw [uR_mul_vR]; exact (map_pow _ _ _).symm
  haveI : ∀ j, (nodeIdeal b₄ b₆ ϖ m ε hϖ0 hm j).IsMaximal :=
    isMaximal_nodeIdeal hθ.out hϖ0 hm
  exact exists_kummer (B := B) hxy hϖ0 hm (nodeIdeal b₄ b₆ ϖ m ε hϖ0 hm)
    (J_le_nodeIdeal hϖ0 hm) (surjective_mk_comp_algebraMap hθ.out hϖ0 hm)
    (isKummerNormAt_NR hϖ hker hε hqM hq hM' K hζ L hL hunr B)
    (sIdeal_injective hϖ0 hm) (fbar_mem_sIdeal hϖ0 hm) (iInf_sIdeal_le_radical hϖ0 hm)
    (NodeChart.φ 𝒩 hπe) (NodeChart.φ_u hπe) (NodeChart.φ_v hπe)

/-- **The chosen Kummer data at the nodes** of the Tate node chart (refactor R1). -/
def kummerDataNR [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M')
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (hunr : ∀ (j : Fin 2) (Q : Ideal (integralClosure 𝒩 L)) [Q.IsPrime],
      Q.comap (algebraMap 𝒩 (integralClosure 𝒩 L)) <
        nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j →
      Algebra.IsUnramifiedAt 𝒩 Q)
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L] (j : Fin 2) :
    KummerNormAtData ϖ m M' (uR b₄ b₆ ϖ m ε) (vR b₄ b₆ ϖ m ε) B
      (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j) :=
  KummerNormAtData.ofIsKummerNormAt (isKummerNormAt_NR hϖ hker hε hqM hq hM' K hζ L hL hunr B j)

/-- **The formal Kummer form of the special fibre of a tame cover of the Tate node chart along the
nodes**, defined from the chosen data `kummerDataNR` (refactor R1). -/
def kummerEquivNR [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M')
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (hunr : ∀ (j : Fin 2) (Q : Ideal (integralClosure 𝒩 L)) [Q.IsPrime],
      Q.comap (algebraMap 𝒩 (integralClosure 𝒩 L)) <
        nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j →
      Algebra.IsUnramifiedAt 𝒩 Q)
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L] (hπe : θ (ϖ ^ m) = 0) :
    Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩)) ⊗[Rs θ 𝒩] Cs θ 𝒩 B
      ≃ₐ[Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩))]
      ∀ p : (Σ j, Fin (kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL hunr B j).r),
        Admissible.KummerPiece (NodeChart.φ 𝒩 hπe)
          (CompletionProd.idem (sIdeal_injective (θ := θ) (θ_ϖ hker) (Nat.pos_of_neZero m))
            (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
            (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m)) p.1)
          ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL hunr B p.1).hd p.2) :=
  haveI : ∀ j, (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j).IsMaximal :=
    isMaximal_nodeIdeal hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m)
  kummerEquivOf (B := B) (by rw [uR_mul_vR]; exact (map_pow _ _ _).symm) (θ_ϖ hker)
    (Nat.pos_of_neZero m) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m))
    (J_le_nodeIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
    (surjective_mk_comp_algebraMap hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m))
    (kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL hunr B)
    (sIdeal_injective (θ_ϖ hker) (Nat.pos_of_neZero m))
    (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
    (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m))
    (NodeChart.φ 𝒩 hπe) (NodeChart.φ_u hπe) (NodeChart.φ_v hπe)

/-- **The special fibre of the normalisation is finite over the special fibre of the chart** (the
`finite` field of `cov₀`): the normalisation of the integrally closed Noetherian chart in a finite
separable extension is finite (`isIntegrallyClosed_NR`, which needs `3 ≠ 0` and the
non-vanishing of the discriminant `tateE (εϖᵐ) b₄ b₆` of the generic fibre). -/
theorem finite_Cs [IsDomain O] [IsDiscreteValuationRing O] [IsNoetherianRing O]
    (hϖ : Irreducible ϖ) (hm : 1 ≤ m)
    (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    (θ : O →+* k) (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L] : Module.Finite (Rs θ 𝒩) (Cs θ 𝒩 B) := by
  haveI : IsDomain 𝒩 := isDomain_NR b₄ b₆ hϖ.prime hm hε
  haveI := isIntegrallyClosed_NR hϖ hm hε h3 hE
  haveI : Module.Finite 𝒩 B := IsIntegralClosure.finite 𝒩 K L B
  haveI : Module.Finite 𝒩 (Cs θ 𝒩 B) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒩 _).toLinearMap
      Ideal.Quotient.mk_surjective
  exact Module.Finite.of_restrictScalars_finite 𝒩 (Rs θ 𝒩) (Cs θ 𝒩 B)

end

end TateTwoChartNode

end SemistableReduction
