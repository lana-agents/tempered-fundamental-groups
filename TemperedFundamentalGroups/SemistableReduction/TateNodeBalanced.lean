/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeCovering
import TemperedFundamentalGroups.SemistableReduction.TateNodeNF
import TemperedFundamentalGroups.SemistableReduction.KummerHomBalanced
import TemperedFundamentalGroups.SemistableReduction.NodeBalancedTwist

/-!
# Maps of tame covers of the Tate node chart are balanced (MR12 I5(b), node chart)

* `AdmissibleLift.nodePhiK_eq_of_kummer` (generic): `nodePhiK φc` is `κ' ∘ (R̂ ⊗ φc) ∘ κ⁻¹` for
  any formal Kummer forms `κ`, `κ'` giving the `kummer` fields of two coverings without cusp
  factors;
* **`TateTwoChartNode.covNR_balancedK`**: for an `NR`-algebra map `g : B → B'` of the
  normalisations of the Tate node chart in two tame covers, the map of node factors of the
  admissible coverings `covNR` induced by the reduction of `g` is balanced at the special chart
  (`NodeHom.BalancedK`) with the node parameters `ϖ^(m / e)`: `nodePhiK` is the map
  `FormalKummer.kummerHom` of formal Kummer forms (`kummerEquivNR`), balanced on every piece by
  `FormalKummer.exists_kummerHom_twist`; divisibility of the ramification indices from the node
  normal form (`TateGlue1.cov₀_nfHyp_s/t`, `cov₀_hinter`).
-/

universe u

open TensorProduct Module

namespace SemistableReduction

namespace AdmissibleLift

variable {k : Type u} [Field k] {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov : Admissible.Covering φ₀ ψ₀} {cov' : Admissible.Covering φ₀' ψ₀'}

/-- **`nodePhiK` through formal Kummer forms of the node factors.** -/
lemma nodePhiK_eq_of_kummer [IsEmpty cov.κ]
    (κ₁ : Admissible.Hat f₀ ⊗[R₀] cov.C ≃ₐ[Admissible.Hat f₀]
      ∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j))
    (κ₂ : Admissible.Hat f₀ ⊗[R₀] cov'.C ≃ₐ[Admissible.Hat f₀]
      ∀ j', Admissible.KummerPiece φ₀' (cov'.idem j') (cov'.e_pos j'))
    (h₁ : ∀ w, (cov.kummer w).1 = κ₁ w) (h₂ : ∀ w, (cov'.kummer w).1 = κ₂ w)
    (φc : cov.C →ₐ[R₀] cov'.C) (z : ∀ j, Admissible.KummerPiece φ₀ (cov.idem j) (cov.e_pos j)) :
    nodePhiK φc z =
      κ₂ (Algebra.TensorProduct.map (AlgHom.id (Admissible.Hat f₀) (Admissible.Hat f₀)) φc
        (κ₁.symm z)) := by
  have h : nodeInclK (cov := cov) z = cov.kummer (κ₁.symm z) :=
    Prod.ext (by rw [h₁, AlgEquiv.apply_symm_apply]; rfl) (funext fun i ↦ isEmptyElim i)
  change (cov'.kummer (Algebra.TensorProduct.map (AlgHom.id _ _) φc
    (cov.kummer.symm (nodeInclK z)))).1 = _
  rw [h, AlgEquiv.symm_apply_apply, h₂]

end AdmissibleLift

namespace TateTwoChartNode

noncomputable section

open AdmissibleLift FormalKummer

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {b₄ b₆ ϖ : O} {m : ℕ} {ε : O}

local notation "𝒩" => NR b₄ b₆ ϖ m ε

/-- `covNR` has no cusp factors. -/
instance instIsEmptyCovNRκ [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    : IsEmpty (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).κ :=
  inferInstanceAs (IsEmpty Empty)

/-- The index set of `covNR` has decidable equality. -/
instance instDecidableEqCovNRι [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    : DecidableEq (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).ι :=
  inferInstanceAs (DecidableEq (Σ j : Fin 2,
    Fin (kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B j).r))

set_option maxRecDepth 8000 in
/-- **`nodePhiK` of the reduction of `g : B → B'` is `kummerHom g`.** -/
lemma nodePhiK_covNR [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    (L' : Type u) [Field L'] [Algebra K L'] [FiniteDimensional K L'] [IsGalois K L']
    (hL' : (finrank K L').Coprime q) [Algebra 𝒩 L'] [IsScalarTower 𝒩 K L']
    (B' : Type u) [CommRing B'] [Algebra 𝒩 B'] [Algebra B' L'] [IsScalarTower 𝒩 B' L']
    [IsIntegralClosure B' 𝒩 L']
    (hunr' : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B') [Q.IsPrime], Q.comap (algebraMap 𝒩 B') < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (hπe : θ (ϖ ^ m) = 0)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩)))
    (g : B →ₐ[𝒩] B') :
    haveI : ∀ j, (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j).IsMaximal :=
      isMaximal_nodeIdeal hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m)
    nodePhiK (cov := covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ)
        (cov' := covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ)
        (quotHom (J θ (R := 𝒩)) g) =
      kummerHom (by rw [uR_mul_vR]; exact (map_pow _ _ _).symm) (θ_ϖ hker)
        (Nat.pos_of_neZero m) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m))
        (J_le_nodeIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
        (surjective_mk_comp_algebraMap hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m))
        (kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B)
        (kummerDataNR hϖ hker hε hqM hq hM' K hζ L' hL' (hunrLoc hker B' hunr') B')
        (sIdeal_injective (θ_ϖ hker) (Nat.pos_of_neZero m))
        (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
        (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m))
        (NodeChart.φ 𝒩 hπe) (NodeChart.φ_u hπe) (NodeChart.φ_v hπe) g :=
  AlgHom.ext fun z ↦ nodePhiK_eq_of_kummer
    (cov := covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ)
    (cov' := covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ)
    (kummerEquivNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B hπe)
    (kummerEquivNR hϖ hker hε hqM hq hM' K hζ L' hL' (hunrLoc hker B' hunr') B' hπe)
    (fun _ ↦ rfl) (fun _ ↦ rfl) _ z

set_option maxHeartbeats 1000000 in
-- case analysis on the pieces of the target covering
set_option maxRecDepth 8000 in
/-- **Maps of tame covers of the Tate node chart are balanced at the nodes** (I5(b), node chart):
the map of node factors of `covNR` induced by an `NR`-algebra map `g : B → B'` of normalisations
is balanced at the special chart, with node parameters `ϖ^(m / e)`. -/
theorem covNR_balancedK [hθ : Fact (Function.Surjective θ)] [IsSepClosed k] [IsDomain O]
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
    (L' : Type u) [Field L'] [Algebra K L'] [FiniteDimensional K L'] [IsGalois K L']
    (hL' : (finrank K L').Coprime q) [Algebra 𝒩 L'] [IsScalarTower 𝒩 K L']
    (B' : Type u) [CommRing B'] [Algebra 𝒩 B'] [Algebra B' L'] [IsScalarTower 𝒩 B' L']
    [IsIntegralClosure B' 𝒩 L']
    (hunr' : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B') [Q.IsPrime], Q.comap (algebraMap 𝒩 B') < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (hπe : θ (ϖ ^ m) = 0)
    (ψ : Polynomial k →ₐ[k] Admissible.Hat (fbar θ (NodeChart.fR (π := ϖ) (e := m) 𝒩)))
    (g : B →ₐ[𝒩] B') :
    NodeHom.BalancedK θ
      (fun j ↦ ϖ ^ (m / (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).e j))
      (fun j ↦ ϖ ^ (m / (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ).e j))
      (nodePhiK (cov := covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ)
        (cov' := covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ)
        (quotHom (J θ (R := 𝒩)) g)) := by
  haveI : ∀ j, (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j).IsMaximal :=
    isMaximal_nodeIdeal hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m)
  rw [nodePhiK_covNR]
  refine NodeHom.balancedK_of_twist _ θ _ _ (fun j j' h ↦ ?_) (fun j j' h ↦ ?_)
    (fun j j' h ↦ ?_)
  · exact NodeHom.dvd_of_map_single_ne_zero _ rfl
      (fun j' z hz1 hz2 ↦ TateGlue1.cov₀_hinter hπe _ j' z hz1 hz2)
      (fun j' ↦ TateGlue1.cov₀_nfHyp_s hπe _ j') (fun j' ↦ TateGlue1.cov₀_nfHyp_t hπe _ j') j j' h
  · have h1 := covNR_e_dvd hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ j'
    have hm : M' ∣ m := Dvd.intro_left q hqM
    obtain ⟨a, ha⟩ := h
    obtain ⟨b, hb⟩ := h1.trans hm
    have he0 := (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).e_pos j
    have he0' := (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ).e_pos j'
    have hm' : m = a * b * (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).e j :=
      hb.trans (by rw [ha]; ring)
    have e1 : m / (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).e j = a * b :=
        Nat.div_eq_of_eq_mul_left he0 hm'
    have e2 : m / (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ).e j' = b :=
      Nat.div_eq_of_eq_mul_left he0' (hb.trans (mul_comm _ _))
    have e3 : (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L' hL' B' hunr' hπe ψ).e j' /
        (covNR hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hunr hπe ψ).e j = a :=
            Nat.div_eq_of_eq_mul_left he0 (ha.trans (mul_comm _ _))
    rw [e1, e2, e3, ← pow_mul, mul_comm]
  · have hd := NodeHom.dvd_of_map_single_ne_zero _ rfl
      (fun j' z hz1 hz2 ↦ TateGlue1.cov₀_hinter hπe _ j' z hz1 hz2)
      (fun j' ↦ TateGlue1.cov₀_nfHyp_s hπe _ j') (fun j' ↦ TateGlue1.cov₀_nfHyp_t hπe _ j') j j' h
    obtain ⟨j₁, i⟩ := j
    obtain ⟨j₂, i'⟩ := j'
    by_cases hj : j₂ = j₁
    · subst hj
      exact exists_kummerHom_twist _ (θ_ϖ hker) (Nat.pos_of_neZero m) _ _ _ _ _ _ _ _ _ _ _ _
        hϖ.ne_zero j₂ i i' hd
    · exact absurd (kummerHom_single_one_ne _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ j₁ i hj i') h

end

end TateTwoChartNode

end SemistableReduction
