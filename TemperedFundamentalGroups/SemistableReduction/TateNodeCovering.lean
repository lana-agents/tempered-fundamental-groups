/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeEtale
import TemperedFundamentalGroups.SemistableReduction.TateNodeRegular

/-!
# The admissible covering `cov₀` of the Tate node chart from a tame cover (MR12 S5, first milestone)

For the quadratic node chart `NR` of the Tate model over a discrete valuation ring `O` (residue
field `k` separably closed, `ker θ = (ϖ)`, `π = ε ϖᵐ`, `m = q M'`, `M'` invertible in `k`), a
finite Galois extension `L` of `K = Frac NR` of degree prime to `q` with `μ_{M'} ⊆ K`, and the
normalisation `B` of `NR` in `L`: if `B` is unramified over the punctured spectra of the closed
points of the special fibre (`hunr`), then the special fibre `B/JB` is an admissible covering of
the special fibre of the node chart, with the formal node coordinates `NodeChart.φ`:
**`TateTwoChartNode.covNR`** (`C = B/JB`); the regularity of `NR` at the closed points of the
special fibre off the nodes is `exists_regular_pair` (`TateNodeRegular`).

* `finite`: `finite_Cs`; `etale` over `D(ū + v̄)`: `etale_Cs_of_regular` (purity);
* `kummer`: `exists_kummer_NR` (S4 at the two nodes + the formal Kummer form), one Kummer factor
  for each node `j` and each factor `i` of the étale-local splitting, index `dⱼᵢ ∣ M'`
  (tame since `M'` is invertible in `k`); no cusp factors.
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

lemma ϖ_mem_nodeIdeal (hker : RingHom.ker θ = Ideal.span {ϖ}) (hm : 1 ≤ m) (j : Fin 2) :
    algebraMap O 𝒩 ϖ ∈ nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) hm j :=
  J_le_nodeIdeal (θ_ϖ hker) hm j (Ideal.mem_map_of_mem _ (by
    rw [hker]; exact Ideal.mem_span_singleton_self ϖ))

/-- The local unramifiedness hypothesis of `exists_kummer_NR` from the global one. -/
theorem hunrLoc [hθ : Fact (Function.Surjective θ)] {L : Type u} [Field L] [Algebra 𝒩 L]
    (hker : RingHom.ker θ = Ideal.span {ϖ}) [NeZero m]
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L]
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (j : Fin 2) (Q : Ideal (integralClosure 𝒩 L)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap 𝒩 (integralClosure 𝒩 L)) <
      nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j) :
    Algebra.IsUnramifiedAt 𝒩 Q := by
  haveI := isMaximal_nodeIdeal (b₄ := b₄) (b₆ := b₆) (ε := ε) hθ.out (θ_ϖ hker)
    (Nat.pos_of_neZero m) j
  exact PurityLocal.isUnramifiedAt_integralClosure B
    (hunr _ (ϖ_mem_nodeIdeal hker (Nat.pos_of_neZero m) j)) Q hQ

/-- `exists_kummer_NR` for any normalisation `B`, from unramifiedness over the punctured
spectra of the closed points of the special fibre. -/
theorem exists_kummer_NR' [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M')
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ M')
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hL : (finrank K L).Coprime q) [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L]
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (hπe : θ (ϖ ^ m) = 0) :
    ∃ (r : Fin 2 → ℕ) (d : ∀ j, Fin (r j) → ℕ) (hd : ∀ j i, 0 < d j i), (∀ j i, d j i ∣ M') ∧
      Nonempty (Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩)) ⊗[Rs θ 𝒩] Cs θ 𝒩 B
        ≃ₐ[Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩))]
        ∀ p : (Σ j, Fin (r j)), Admissible.KummerPiece (NodeChart.φ 𝒩 hπe)
          (CompletionProd.idem (sIdeal_injective (θ := θ) (θ_ϖ hker) (Nat.pos_of_neZero m))
            (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
            (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m)) p.1) (hd p.1 p.2)) := by
  exact exists_kummer_NR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B hπe

/-- **The admissible covering `cov₀` of the Tate node chart** defined by the special fibre
`B/JB` of the normalisation `B` of the chart in a tame Galois cover (`C = Cs θ NR B`), given the
regularity of the chart at the closed points of the special fibre off the nodes. -/
def covNR_of_regular [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    (hreg : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      NodeChart.fR (π := ϖ) (e := m) 𝒩 ∉ P →
      ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (hπe : θ (ϖ ^ m) = 0)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩))) :
    Admissible.Covering (NodeChart.φ 𝒩 hπe) ψ :=
  let D := kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B
  { C := Cs θ 𝒩 B
    finite := finite_Cs hϖ (Nat.pos_of_neZero m) hε h3 hE θ K L B
    etale := etale_Cs_of_regular hϖ hker (Nat.pos_of_neZero m) hε h3 hE K L hreg B hunr
    ι := Σ j, Fin (D j).r
    idem := fun p ↦ CompletionProd.idem _ _ _ p.1
    isIdempotentElem_idem := fun p ↦ CompletionProd.isIdempotentElem_idem _ _ _ p.1
    e := fun p ↦ (D p.1).d p.2
    e_pos := fun p ↦ (D p.1).hd p.2
    e_ne_zero := fun p h0 ↦ by
      obtain ⟨c, hc⟩ := (D p.1).hdM p.2
      exact hM'k (by rw [hc, Nat.cast_mul, h0, zero_mul])
    κ := Empty
    cidem := Empty.elim
    isIdempotentElem_cidem := fun i ↦ i.elim
    ce := Empty.elim
    ce_pos := fun i ↦ i.elim
    ce_ne_zero := fun i ↦ i.elim
    kummer := (kummerEquivNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B
      hπe).trans AlgEquiv.prodUnique.symm }

/-- The ring of `covNR_of_regular` is the special fibre of the normalisation. -/
lemma covNR_of_regular_C [Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    (hreg : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      NodeChart.fR (π := ϖ) (e := m) 𝒩 ∉ P →
      ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (hπe : θ (ϖ ^ m) = 0)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩))) :
    (covNR_of_regular hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe ψ).C =
      Cs θ 𝒩 B := rfl

/-- **`NR` is regular at the closed points of the special fibre off the nodes**, in the form of
the hypothesis `hreg` of `covNR_of_regular`. -/
theorem hreg_NR [hθ : Fact (Function.Surjective θ)] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hm : 1 ≤ m) (hε : IsUnit ε)
    (P : Ideal 𝒩) [P.IsMaximal] (hϖP : algebraMap O 𝒩 ϖ ∈ P)
    (hf : NodeChart.fR (π := ϖ) (e := m) 𝒩 ∉ P) :
    ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
      maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y} := by
  have hf' : uR b₄ b₆ ϖ m ε + vR b₄ b₆ ϖ m ε ∉ P := by
    rwa [NodeChart.fR, KummerEtale.fA, map_add] at hf
  obtain ⟨y, h1, h2, h3⟩ := exists_regular_pair hϖ hθ.out hker hm hε P hϖP hf'
  exact ⟨_, y, h1, h2, h3⟩

/-- **The admissible covering `cov₀` of the Tate node chart** defined by the special fibre `B/JB`
of the normalisation `B` of the chart in a tame Galois cover `L` (`C = Cs θ NR B`; first
milestone of S5, `k` separably closed). Hypothesis `hunr`: `B` is unramified over the punctured
spectra of the closed points of the special fibre (debt D3/A1: étaleness of the generic fibre
on the chart + tame base change at the generic points of the special fibre). -/
def covNR [Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    Admissible.Covering (NodeChart.φ 𝒩 hπe) ψ :=
  covNR_of_regular hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B
    (fun P _ hϖP hf ↦ hreg_NR hϖ hker (Nat.pos_of_neZero m) hε P hϖP hf) hunr hπe ψ

/-- **The ramification indices of `covNR` divide `M'`.** -/
theorem covNR_e_dvd [Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    (ψ : Polynomial k →ₐ[k] Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩)))
    (j : (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).ι) :
    (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).e j ∣ M' :=
  (kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B j.1).hdM j.2

end

end TateTwoChartNode

end SemistableReduction
