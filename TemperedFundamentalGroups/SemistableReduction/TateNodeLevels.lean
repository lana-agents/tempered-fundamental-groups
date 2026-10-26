/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateNodeLevelPatch
import TemperedFundamentalGroups.SemistableReduction.FormalLevelPatchTr

/-!
# The level data of the M2 lift over the Tate node chart (MR12 T2 S6, step G3)

**`TateTwoChartNode.levelsS6`**: the level data (`FormalLevel.NodeLevels`) of the tower
`towerS6` of the covering `covNR_of_regular …` of the Tate node chart (the data of
`levelPatchEquiv_NR` at all levels). Hence (`FormalLevel.NodeLevels.equiv`,
`FormalLevel.NodeLevels.equiv_tr`) the level patches `NR/ϖˡ⁺¹ ⊗_{NR} B ≃ G l` and their
compatibility with the transition maps of the tower.
-/

universe u

open TensorProduct Module IsLocalRing

namespace SemistableReduction

namespace QuadNodeTower

variable {O : Type u} [CommRing O] (ϖ π : O) (e : ℕ) (c D : KummerEtale.A π e)

instance (n : ℕ) : IsScalarTower (Rb π e c D) (Rn ϖ π e c D (n + 1)) (Rn ϖ π e c D n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

end QuadNodeTower

namespace TateTwoChartNode

open AdmissibleLift FormalKummer

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {b₄ b₆ ϖ : O} {m : ℕ} {ε : O}

local notation "𝒩" => NR b₄ b₆ ϖ m ε

instance isMaximal_nodeIdeal' [hθ : Fact (Function.Surjective θ)] (hϖ : θ ϖ = 0) (hm : 1 ≤ m)
    (j : Fin 2) : (nodeIdeal b₄ b₆ ϖ m ε hϖ hm j).IsMaximal :=
  isMaximal_nodeIdeal hθ.out hϖ hm j

lemma hJnil_Rn [IsNoetherianRing O] (hker : RingHom.ker θ = Ideal.span {ϖ}) (l : ℕ) :
    J θ (R := QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l) ≤ nilradical _ :=
  fun x hx ↦ ⟨l + 1, by
    have h := Ideal.pow_mem_pow hx (l + 1)
    rw [QuadNodeTower.hJ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hker.le l] at h
    exact (Ideal.mem_bot).1 h⟩

set_option maxHeartbeats 4000000 in
-- the level data of `towerS6` (as in `levelPatchEquiv_NR`, at all levels)
/-- **The level data of the M2 lift over the Tate node chart** (`FormalLevel.NodeLevels` for the
tower `towerS6`): level nodes `(sIdeal 𝔪ⱼ).comap red`, residue maps `resMap`, node coordinates
`hχL_S6`, lifted idempotents (uniqueness of idempotents), étaleness `formallyEtale_Rn`. -/
def levelsS6 [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
    [IsDomain O] [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ)
    (hker : RingHom.ker θ = Ideal.span {ϖ})
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
    (τ : QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m))
    : FormalLevel.NodeLevels (uR_mul_vR' (b₄ := b₄) (b₆ := b₆) (ϖ := ϖ) (m := m) (ε := ε))
      (θ_ϖ hker) (Nat.pos_of_neZero m)
      (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m))
      (J_le_nodeIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
      (surjective_mk_comp_algebraMap hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m))
      (kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B)
      (sIdeal_injective (θ_ϖ hker) (Nat.pos_of_neZero m))
      (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
      (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m))
      (NodeChart.φ 𝒩 hπe) (NodeChart.φ_u hπe) (NodeChart.φ_v hπe)
      (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)
      (finite_Cs hϖ (Nat.pos_of_neZero m) hε h3 hE θ K L B)
      (etale_Cs_of_regular hϖ hker (Nat.pos_of_neZero m) hε h3 hE K L hreg B hunr)
      (fun j i h0 ↦ by
        obtain ⟨c, hc⟩ := ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B)
            j).hdM i
        exact hM'k (by rw [hc, Nat.cast_mul, h0, zero_mul]))
      (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m))
      (towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ) := by
  haveI hmax : ∀ l j, ((sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m)
      j)).comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e
          l))).IsMaximal := fun l j ↦
    CompletionProd.isMaximal_comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B
        hreg hunr hπe τ).e l)) (surjective_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L
        hL B hreg hunr hπe τ).e l))
      (fun j ↦ sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j)) j
  have h𝔪 : ∀ l j, nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j ≤
      ((sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j)).comap
        (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e
            l))).comap (algebraMap 𝒩 _) := fun l j a ha ↦ by
    have h1 : ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e l).symm
        (Ideal.Quotient.mk _ (algebraMap 𝒩
        (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l) a)) = Ideal.Quotient.mk _ a :=
      (AlgEquiv.symm_apply_eq _).2
        (QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (θ_ϖ hker) l a).symm
    change ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e l).symm
        (Ideal.Quotient.mk _ (algebraMap 𝒩 _ a)) ∈
      sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j)
    rw [h1]
    exact Ideal.mem_map_of_mem _ ha
  refine
    { 𝔪' := fun l j ↦ (sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m)
          j)).comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe
              τ).e l))
      isMaximal := hmax
      hinj := fun l ↦ CompletionProd.injective_comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM'
          hM'k K hζ L hL B hreg hunr hπe τ).e l))
        (surjective_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe
            τ).e l)) _ (sIdeal_injective (θ_ϖ hker) (Nat.pos_of_neZero m))
      hf := fun l ↦ CompletionProd.mem_comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K
          hζ L hL B hreg hunr hπe τ).e l)) (red_f θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K
          hζ L hL B hreg hunr hπe τ).e l) ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B
          hreg hunr hπe τ).hfe l)) _
        (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
      hrad := fun l ↦ CompletionProd.iInf_comap_le_radical (red θ ((towerS6 hϖ hker hε h3 hE hqM
          hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e l))
        (surjective_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe
            τ).e l)) (red_f θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe
            τ).e l) ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).hfe
            l)) _
        ((ker_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e
            l)).le.trans (hJnil_Rn hker l))
        (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m))
      r := fun l j ↦ FormalLevel.resMap ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL
          (hunrLoc hker B hunr) B) j).comap_eq
        (FormalKummer.hsurj0_of _ (J_le_nodeIdeal (θ_ϖ hker) (Nat.pos_of_neZero m) j)
          (surjective_mk_comp_algebraMap hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m) j)
          ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B) j)) (h𝔪 l j)
      hχL := fun l p a ↦ hχL_S6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ l p a
      hεL := ?_
      hm := fun _ _ ↦ Ideal.map_comap_le
      hr := fun l j _ hz ↦ FormalLevel.resMap_eq_zero ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L
          hL (hunrLoc hker B hunr) B) j).comap_eq _ _ hz
      etale := fun l ↦ formallyEtale_Rn hϖ hker hε h3 hE K L B hreg hunr l }
  intro l p
  refine eq_of_isNilpotent_sub_of_isIdempotentElem
    (CompletionProd.isIdempotentElem_idem _ _ _ _) (((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K
        hζ L hL B hreg hunr hπe τ).level l).hidem p)
    (isNilpotent_of_mem_ker_ψ θ (QuadNodeTower.hJ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hker.le l) ?_)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  exact (ψ_idem_comap θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e
      l) ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).hfe l)
      (sIdeal_injective (θ_ϖ hker) (Nat.pos_of_neZero m))
    (fbar_mem_sIdeal (θ_ϖ hker) (Nat.pos_of_neZero m))
    (iInf_sIdeal_le_radical (θ_ϖ hker) (Nat.pos_of_neZero m)) (hJnil_Rn hker l) p.1).trans
    (((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).level l).L.hε p).symm

end

end TateTwoChartNode

end SemistableReduction
