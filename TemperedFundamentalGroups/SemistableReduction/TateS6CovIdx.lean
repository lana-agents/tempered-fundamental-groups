/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Datum
import TemperedFundamentalGroups.SemistableReduction.TateNodeCovIdx

/-!
# The Kummer factors of the node covering of a tame cover of the Tate curve (MR12, interface I5(a))

For a tame cover `C : TateS6.Cov …`, the node covering `(TateS6.datum C).cov₀` (`TateS5.cov`,
`TateGlue1.covTate`) has one Kummer factor for each point of the normalisation `C.Bn = C.B₁[1/D]`
over each of the two nodes `𝔪ⱼ` of the node chart `NR`:
**`TateS6.covIdx C : (datum C).cov₀.ι ≃ Σ j : Fin 2, {Q : Ideal C.Bn // Q.IsPrime ∧ Q ∩ NR = 𝔪ⱼ}`**
(`TateGlue1.covTateIdx`, from `TateTwoChartNode.covNRIdx`), and **`TateS6.covIdx₁`**: the same
with the points of `C.B₁` over the node points `𝔪ⱼ ∩ T1` of the chart `T1`
(`KummerPrimes.primesOverAway`). The ramification index of the factor of `Q` is
`(datum C).cov₀.e (covIdx.symm ⟨j, Q⟩)`.
-/

universe u

open Module

namespace SemistableReduction

open TateTwoChart TateTwoChartNode KummerPrimes

namespace TateGlue1

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ}
  [IsDomain O] [IsDiscreteValuationRing O] [IsSepClosed k]
  [hθ : Fact (Function.Surjective θ)]
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) [NeZero m]
  (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
  {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
  (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
  [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) =
    algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) K x)
  {ζ : K} (hζ : IsPrimitiveRoot ζ M')
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (hL : (finrank K L).Coprime q) [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L]
  [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (NR b₄ b₆ ϖ m ε) L]
  [IsScalarTower (NR b₄ b₆ ϖ m ε) K L]
  (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L]
  [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L]
  (B : Type u) [CommRing B] [Algebra (NR b₄ b₆ ϖ m ε) B] [Algebra B L]
  [IsScalarTower (NR b₄ b₆ ϖ m ε) B L] [Algebra B₁ B] [IsScalarTower B₁ B L]
  [IsLocalization.Away
    (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ (DT (ε * ϖ ^ m) b₄ t κ)) B]
  (hB : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) B (toNode b₄ hκ rfl x) =
    algebraMap B₁ B (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ x))
  (hunr : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal],
    algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) ϖ ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
      Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁) < P →
        Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄ t κ) Q)
  (hπe : θ (ϖ ^ m) = 0) (τ : Rb b₄ b₆ ϖ m ε)

/-- **I5(a) for `covTate`**: its Kummer factors are the points of `B = B₁[1/D]` over the two
nodes of the node chart. -/
def covTateIdx :
    (covTate hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe τ).ι ≃
      Σ j : Fin 2, PrimesOver B (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j) :=
  haveI := isFractionRing_NR hϖ hκ hε h3 hE K hK
  haveI := isIntegralClosure_B hϖ hκ hε K hK L B₁ B
  covNRIdx hϖ hker (.of_mul_eq_one_right εi hε) h3 hE hqM hq hM' hM'k K hζ L hL B
    (hunr_B hκ hε B₁ B hB hunr) hπe _

end

end TateGlue1

namespace TateS6

open TateGlue0 TateLevel AdmissibleLift

noncomputable section

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsAlgClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m]
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
  {hκ : κ * (t ^ 2 - b₆) = 1} (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) (hb₆ : IsUnit b₆)
  {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  {K : Type u} [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
  [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) =
    algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) K x)
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ M') {ζe : K} (hζe : IsPrimitiveRoot ζe e)
  (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (h0 (ε * ϖ ^ m) b₄ t
        κ))))

set_option hygiene false in
/-- The chart instances of a Tate cover `C` over `T1` and the node chart. -/
local macro "cov_inst1 " C:term : tactic => `(tactic| (
  letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).algT1
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K ($C).L := ($C).towT1
  letI : Algebra (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁ := ($C).algB₁
  haveI : IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁ ($C).L := ($C).towB₁
  haveI : IsIntegralClosure ($C).B₁ (T1 (ε * ϖ ^ m) b₄ t κ) ($C).L := ($C).intB₁
  haveI : IsLocalization.Away (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) ($C).B₁
    (DT (ε * ϖ ^ m) b₄ t κ)) ($C).Bn := ($C).locBn))

/-- **I5(a): the Kummer factors of the node covering of a tame cover `C` are the points of
`C.Bn = C.B₁[1/D]` over the two nodes of the node chart.** -/
def covIdx (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) :
    (datum hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C).cov₀.ι ≃
      Σ j : Fin 2,
        PrimesOver C.Bn (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j) := by
  cov_inst1 C
  exact TateGlue1.covTateIdx hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ C.L C.hL C.B₁ C.Bn
    C.hBn C.hunr₁ (TateS5.θ_pow hker) τ

/-- **I5(a), on `B₁`: the Kummer factors of the node covering of `C` are the points of the
normalisation `C.B₁` of `T1` over the two node points `𝔪ⱼ ∩ T1` of `T1`.** -/
def covIdx₁ (C : Cov ϖ b₄ b₆ t κ ε m hκ q e K) :
    (datum hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C).cov₀.ι ≃
      Σ j : Fin 2, PrimesOver C.B₁
        ((nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j).comap
          (toNode b₄ hκ rfl).toRingHom : Ideal (twoChart (ε * ϖ ^ m) b₄ t κ).R1) := by
  cov_inst1 C
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  haveI := isLocalization_NR (b₄ := b₄) (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t)
    (κ := κ) hκ rfl hε
  exact (covIdx hϖ hker hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe τ φ₀ C).trans
    (Equiv.sigmaCongrRight fun j ↦
      haveI := isMaximal_nodeIdeal (b₄ := b₄) (b₆ := b₆) (ε := ε) hθ.out (θ_ϖ hker)
        (Nat.pos_of_neZero m) j
      primesOverAway (DT (ε * ϖ ^ m) b₄ t κ) C.hBn _)

end

end TateS6

end SemistableReduction
