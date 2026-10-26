/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeKummer
import TemperedFundamentalGroups.SemistableReduction.PurityLocal
import TemperedFundamentalGroups.SemistableReduction.EtaleSpecialFibre

/-!
# The special fibre of a tame cover of the Tate node chart is étale off the nodes (MR12 S5.2)

For the quadratic node chart `NR` of the Tate model over a discrete valuation ring `O` and the
normalisation `B = integralClosure NR L` in a finite separable extension `L` of `K = Frac NR`:
if `NR` is regular at the closed points of the special fibre outside `V(u + v)` (with parameters
`(ϖ, y)`, `hreg`) and `B` is unramified over the punctured spectra of all closed points of the
special fibre (`hunr`: unramified at every prime lying over a prime strictly inside a maximal
ideal containing `ϖ`; this is the input A1 + étaleness of the generic fibre), then
(**`TateTwoChartNode.etale_Cs_of_regular`**) the special fibre `B/JB` is étale over `NR/J` away
from `f̄ = ū + v̄`: the `etale` field of `cov₀`.

Proof: purity at the closed points (`PurityLocal.isEtaleAt`), then the special fibre
(`EtaleQuot.etale_quot_of_isEtaleAt_maximal`; `B/JB` is a Jacobson ring, finite over the finite
type `k`-algebra `NR/J`).
-/

universe u

open TensorProduct Module IsLocalRing

namespace SemistableReduction

open AdmissibleLift FormalKummer

namespace TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {b₄ b₆ ϖ : O} {m : ℕ} {ε : O}

local notation "𝒩" => NR b₄ b₆ ϖ m ε

/-- The special fibre `NR/J` is a Jacobson ring (finite type over `k`). -/
lemma isJacobsonRing_Rs [hθ : Fact (Function.Surjective θ)] [IsNoetherianRing O] :
    IsJacobsonRing (Rs θ 𝒩) := by
  haveI : Algebra.FiniteType O (Rs θ 𝒩) :=
    Algebra.FiniteType.trans (S := 𝒩) inferInstance inferInstance
  letI : Algebra O k := θ.toAlgebra
  letI : Algebra k (Rs θ 𝒩) := QuadNodeTower.algK 𝒩
  haveI : @IsScalarTower O k (Rs θ 𝒩) _ Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun o ↦
    (QuadNodeTower.algK_θ (θ := θ) 𝒩 o).symm
  haveI : Algebra.FiniteType k (Rs θ 𝒩) := Algebra.FiniteType.of_restrictScalars_finiteType O k _
  exact isJacobsonRing_of_finiteType (A := k)

/-- **The special fibre of the normalisation is étale over `D(f̄)`** (the `etale` field of
`cov₀`), given the regularity of `NR` at the closed points of the special fibre off the nodes. -/
theorem etale_Cs_of_regular [hθ : Fact (Function.Surjective θ)] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (hreg : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      NodeChart.fR (π := ϖ) (e := m) 𝒩 ∉ P →
      ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L]
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q) :
    (Localization.awayMap (algebraMap (Rs θ 𝒩) (Cs θ 𝒩 B))
      (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩))).Etale := by
  haveI : IsDomain 𝒩 := isDomain_NR b₄ b₆ hϖ.prime hm hε
  haveI := isIntegrallyClosed_NR hϖ hm hε h3 hE
  haveI : IsJacobsonRing (Rs θ 𝒩) := isJacobsonRing_Rs
  have hϖJ : algebraMap O 𝒩 ϖ ∈ J θ (R := 𝒩) := Ideal.mem_map_of_mem _ (by
    rw [hker]; exact Ideal.mem_span_singleton_self ϖ)
  exact PurityLocal.etale_quot_awayMap K (L := L) (J θ (R := 𝒩)) B _
    (fun P _ hJP hg ↦ hreg P (hJP hϖJ) hg) (fun P _ hJP ↦ hunr P (hJP hϖJ))

end

end TateTwoChartNode

end SemistableReduction
