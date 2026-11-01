/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS5
import TemperedFundamentalGroups.SemistableReduction.TateNodeLevels
import TemperedFundamentalGroups.SemistableReduction.TateV1Level
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevels
import TemperedFundamentalGroups.SemistableReduction.EtaleLevelSucc

/-!
# The levels of the M2 lift over `V₁` are the levels of the normalisation (MR12 T2 S6, G4)

For the tame cover `L` of the Tate curve (data of `TateS5`), the covering `Y n` over the chart
`V₁ = Spec T1` at level `n` of the M2 lift (`NodeEtaleGlue.Input.Y` of `TateGlue1.input`, glued
from the node patches `G n` of the tower `towerS6` and the étale lifts `E1 n`) is the level
`B₁/ϖⁿ⁺¹` of the normalisation `B₁` of `T1` in `L`:

* `TateS6.inpF` (the input `TateGlue1.input …` typed as `NodeLevels.InputOf` of the node level
  data `levelsS5`, so that the generic results apply without re-checking the covering bridge),
  `TateS6.tF` (`B₁/ϖⁿ⁺¹ → NR/ϖⁿ⁺¹ ⊗ Bn`), **`TateS6.φE`** (`B₁/ϖⁿ⁺¹ → (B₁/ϖⁿ⁺¹)[1/w] ≃ E1 n`),
  **`TateS6.ρX`** (`B₁/ϖⁿ⁺¹ → B₁/JB₁`), `TateS6.hρ_lev` (`NodeLevels.hρ_of_mk`);
* **`TateS6.equivY1`**: `B₁/ϖⁿ⁺¹ ≃ₐ[T1] Y n` (`FormalLevel.NodeLevels.levelEquivX`);
* `TateS6.tF_succ`, `TateS6.hμE_lev`: the components commute with the reductions
  `B₁/ϖⁿ⁺² → B₁/ϖⁿ⁺¹` (the hypotheses `hμt`, `hμE` of `levelEquivX_succ`).

Instance arguments of the generic statements whose instances differ syntactically at the Tate
input (`towerORI`, `towerX`) are passed explicitly; `rw`/`obtain … rfl` in goals mixing the levels
`n`, `n + 1` time out at the Tate types and are avoided (`calc` with `congrArg`, ring-hom ext).
-/

universe u
open Module Polynomial
namespace SemistableReduction

namespace TateS6
open TateS5 TateTwoChart TateTwoChartNode TateGlue0 TateLevel
open TensorProduct
open AdmissibleLift (J)
open FormalKummer (Cs)
noncomputable section
section Data

set_option linter.unusedSectionVars false

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {k : Type u} [Field k]
  [IsAlgClosed k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ} [NeZero m]


variable (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
  (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0) (hb₆ : IsUnit b₆)
  {q M' : ℕ} (hqM : q * M' = m) (hq : 0 < q) (hM' : 0 < M') (hM'k : (M' : k) ≠ 0)
  [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
  (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t
      κ) K] [Algebra (NR b₄ b₆ ϖ m ε) K]
  (hK : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) K (toNode b₄ hκ rfl x) = algebraMap (T1 (ε * ϖ ^ m) b₄ t
      κ) K x)
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) K] [IsFractionRing (RcT (ε * ϖ ^ m) b₄ t κ) K]
  {ζ : K} (hζ : IsPrimitiveRoot ζ M') {ζe : K} (hζe : IsPrimitiveRoot ζe e)
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (hL : (finrank K L).Coprime q) (hd : finrank K L ∣ e)
  [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (NR b₄
      b₆ ϖ m ε) L] [IsScalarTower (NR b₄ b₆ ϖ m ε) K L]
  [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (RcT (ε * ϖ ^ m) b₄ t κ) K L] [Algebra (T0 (ε
      * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε * ϖ ^ m) b₄ t κ) L]
  [Algebra (T01 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) (T01 (ε * ϖ ^ m) b₄ t
      κ) L]
  (hρ : ∀ x, algebraMap (T01 (ε * ϖ ^ m) b₄ t κ) L (rho0 (ε * ϖ ^ m) b₄ t κ x) = algebraMap (T0 (ε
      * ϖ ^ m) b₄ t κ) L x)
  (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L] [IsScalarTower
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L]
  (Bn : Type u) [CommRing Bn] [Algebra (NR b₄ b₆ ϖ m ε) Bn] [Algebra Bn L] [IsScalarTower (NR b₄ b₆
      ϖ m ε) Bn L]
  [Algebra B₁ Bn] [IsScalarTower B₁ Bn L]
  [IsLocalization.Away (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ (DT (ε * ϖ ^ m) b₄ t κ)) Bn]
  (hBn : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) Bn (toNode b₄ hκ rfl x) = algebraMap B₁ Bn (algebraMap
      (T1 (ε * ϖ ^ m) b₄ t κ) B₁ x))
  (B₀ : Type u) [CommRing B₀] [Algebra (T0 (ε * ϖ ^ m) b₄ t κ) B₀] [Algebra B₀ L] [IsScalarTower
      (T0 (ε * ϖ ^ m) b₄ t κ) B₀ L]
  [IsIntegralClosure B₀ (T0 (ε * ϖ ^ m) b₄ t κ) L]
  (Bc : Type u) [CommRing Bc] [Algebra (RcT (ε * ϖ ^ m) b₄ t κ) Bc] [Algebra Bc L] [IsScalarTower
      (RcT (ε * ϖ ^ m) b₄ t κ) Bc L]
  [Algebra B₀ Bc] [IsScalarTower B₀ Bc L]
  [IsLocalization.Away (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)) Bc]
  (hBc : ∀ x, algebraMap (RcT (ε * ϖ ^ m) b₄ t κ) Bc (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) (RcT (ε *
      ϖ ^ m) b₄ t κ) x) = algebraMap B₀ Bc (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀ x))
  (hunr₁ : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T1 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
    Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁) < P → Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄
      t κ) Q)
  (hunr₀ : ∀ (P : Ideal (T0 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal], algebraMap O (T0 (ε * ϖ ^ m) b₄ t
      κ) ϖ ∈ P → ∀ (Q : Ideal B₀) [Q.IsPrime],
    Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀) < P →
      Q.comap (algebraMap (T0 (ε * ϖ ^ m) b₄ t κ) B₀) ≠
        Ideal.span {h0 (ε * ϖ ^ m) b₄ t κ, z0 (ε * ϖ ^ m) b₄ t κ} →
      Algebra.IsUnramifiedAt (T0 (ε * ϖ ^ m) b₄ t κ) Q)
  (τ : TateGlue1.Rb b₄ b₆ ϖ m ε)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ
      (CuspTower.sC (T0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) (h0 (ε * ϖ ^ m) b₄ t
        κ))))




variable {K L B₁ Bn B₀ Bc}

local notation "𝒯" => T1 (ε * ϖ ^ m) b₄ t κ

local notation "𝒩" => NR b₄ b₆ ϖ m ε

/-- **The input of the glueing over `V₁`** (`TateGlue1.input` at the data of S5). -/
abbrev inp := TateGlue1.input hκ rfl hε (TateS5.θ_ϖ hker)
  (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
  (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le
  (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (NeZero.ne m)

local notation "𝓘" => inp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

/-- **The level data of the node patches** (`TateTwoChartNode.levelsS6` for `B = Bn`). -/
abbrev levelsS5 :=
  @levelsS6 O _ k _ θ b₄ b₆ ϖ m ε _ _ _ _ hϖ hker _ (.of_mul_eq_one_right εi hε) h3 hE q M' hqM hq
    hM' hM'k K _ _ (TateGlue1.isFractionRing_NR hϖ hκ hε h3 hE K hK) ζ hζ L _ _ _ _ hL _ _ Bn _ _
        _ _
    (TateGlue1.isIntegralClosure_B hϖ hκ hε K hK L B₁ Bn)
    (fun P _ hϖP hf ↦ hreg_NR hϖ hker (Nat.pos_of_neZero m) (.of_mul_eq_one_right εi hε) P hϖP hf)
    (TateGlue1.hunr_B hκ hε B₁ Bn hBn hunr₁) (θ_pow hker) τ

instance instAlgXn (n : ℕ) : Algebra ((𝓘).B n) (TateGlue1.Xn ϖ 𝒯 B₁ n) :=
  inferInstanceAs (Algebra (EtaleTower.Tn ϖ 𝒯 n) (TateGlue1.Xn ϖ 𝒯 B₁ n))

instance instAlg0Xn (n : ℕ) : Algebra (𝓘).B0 (TateGlue1.Xn ϖ 𝒯 B₁ n) :=
  inferInstanceAs (Algebra 𝒯 (TateGlue1.Xn ϖ 𝒯 B₁ n))

instance instTowerXn (n : ℕ) :
    IsScalarTower (𝓘).B0 ((𝓘).B n) (TateGlue1.Xn ϖ 𝒯 B₁ n) :=
  inferInstanceAs (IsScalarTower 𝒯 (EtaleTower.Tn ϖ 𝒯 n) (TateGlue1.Xn ϖ 𝒯 B₁ n))

lemma toTensor_algebraMap (n : ℕ) (r : TateGlue1.B ϖ (ε * ϖ ^ m) b₄ t κ n) :
    TateGlue1.toTensor hκ B₁ Bn hBn n (algebraMap (EtaleTower.Tn ϖ 𝒯 n) (TateGlue1.Xn ϖ 𝒯 B₁ n) r) =
      algebraMap (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n) _
        (toRn b₄ hκ rfl n r) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [Ideal.Quotient.algebraMap_quotient_map_quotient, TateGlue1.toTensor_mk, ← hBn, toRn_mk,
    ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rfl

instance instAlgNRR (l : ℕ) : Algebra 𝒩 ((𝓘).R l) :=
  inferInstanceAs (Algebra 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerONRR (l : ℕ) : IsScalarTower O 𝒩 ((𝓘).R l) :=
  inferInstanceAs (IsScalarTower O 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instAlgRbR (l : ℕ) :
    Algebra (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) ((𝓘).R l) :=
  inferInstanceAs (Algebra 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerORbR (l : ℕ) :
    IsScalarTower O (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) ((𝓘).R l) :=
  inferInstanceAs (IsScalarTower O 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerRbRR (l : ℕ) :
    IsScalarTower (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) ((𝓘).R (l + 1))
      ((𝓘).R l) :=
  inferInstanceAs (IsScalarTower 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (l + 1))
    (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerNRRR (l : ℕ) : IsScalarTower 𝒩 ((𝓘).R (l + 1)) ((𝓘).R l) :=
  inferInstanceAs (IsScalarTower 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (l + 1))
    (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

set_option maxHeartbeats 1000000 in
-- unfolding the projections of the input
/-- **The reduction `B₁/ϖⁿ⁺¹ → B₁/JB₁`** (over the level `T1/ϖⁿ⁺¹`). -/
def ρX (n : ℕ) : letI := NodeEtaleGlue.algC1 (𝓘).B (𝓘).qB (𝓘).C1 n
    TateGlue1.Xn ϖ 𝒯 B₁ n →ₐ[(𝓘).B n]
        (𝓘).C1 :=
  letI := NodeEtaleGlue.algC1 (𝓘).B
      (𝓘).qB (𝓘).C1 n
  { EtaleTower.red (TateS5.θ_ϖ hker) n with
    commutes' := fun r ↦ by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective r
      rfl }

set_option maxHeartbeats 1000000 in
-- unfolding the projections of the input
lemma ρX_mk (n : ℕ) (b : B₁) : ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n
    (Ideal.Quotient.mk _ b) =
    (Ideal.Quotient.mk _ b : Cs θ 𝒯 B₁) := rfl


set_option maxHeartbeats 400000 in
-- unfolding the projections of the input
lemma ι₀_ρX_mk (n : ℕ) (b : B₁) :
    (𝓘).ι₀ (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n (Ideal.Quotient.mk _ b)) =
      (Ideal.Quotient.mk ((J θ (R := 𝒩)).map (algebraMap 𝒩 Bn)) (algebraMap B₁ Bn b) :
        Cs θ 𝒩 Bn) := by
  rw [ρX_mk]
  rfl

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate input (a proof term whose statement is the
-- hypothesis `hρ` of `levelEquivX`, too long to restate)
/-- **The reduction hypothesis `hρ` of `levelEquivX` at level `n`** (`NodeLevels.hρ_of_mk`). -/
def hρ_lev (n : ℕ) :=
  (levelsS5 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).hρ_of_mk (𝓘)
    (fun l a ↦ QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (TateS5.θ_ϖ hker) l a)
    (TateGlue1.toTensor hκ B₁ Bn hBn n) (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁
        τ n)
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (algebraMap B₁ Bn)
    (fun b ↦ TateGlue1.toTensor_mk hκ B₁ Bn hBn n b) (ι₀_ρX_mk hϖ hker hκ hε h3 hE hqM hq hM' hM'k
        hK hζ hL hBn hunr₁ τ n)

set_option maxHeartbeats 1000000 in
-- unfolding the projections of the input
/-- **The étale side of the level `B₁/ϖⁿ⁺¹`**: `B₁/ϖⁿ⁺¹ → (B₁/ϖⁿ⁺¹)[1/w] ≃ E1 n`. -/
def φE (n : ℕ) : TateGlue1.Xn ϖ 𝒯 B₁ n →ₐ[(𝓘).B n] (𝓘).E n :=
  haveI : Module.Finite 𝒯 B₁ := by
    haveI := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
    haveI := TateGlue1.isIntegrallyClosed_T1' hϖ hker hκ hε h3 hE
    exact IsIntegralClosure.finite 𝒯 K L B₁
  haveI := TateGlue1.etale_Pn_T1 hϖ hker hκ hε h3 hE K L B₁ hunr₁ n
  TateGlue1.φE (TateS5.θ_ϖ hker) hker.le B₁ (w1 (ε * ϖ ^ m) b₄ t κ) n
    (TateGlue1.E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
        hL hBn hunr₁ τ) n)

set_option maxHeartbeats 1000000 in
-- unfolding the projections of the input
lemma hE_lev (n : ℕ) (x : TateGlue1.Xn ϖ 𝒯 B₁ n) :
    (𝓘).σE n (Ideal.Quotient.mk _ (φE
        hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n x)) =
      algebraMap (𝓘).C1
          (Localization.Away (algebraMap (𝓘).Bs (𝓘).C1 (𝓘).bbar))
        (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n x) :=
  haveI : Module.Finite 𝒯 B₁ := by
    haveI := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
    haveI := TateGlue1.isIntegrallyClosed_T1' hϖ hker hκ hε h3 hE
    exact IsIntegralClosure.finite 𝒯 K L B₁
  haveI := TateGlue1.etale_Pn_T1 hϖ hker hκ hε h3 hE K L B₁ hunr₁ n
  TateGlue1.σ_φE (TateS5.θ_ϖ hker) hker.le B₁ (w1 (ε * ϖ ^ m) b₄ t κ) n
    (TateGlue1.E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
        hL hBn hunr₁ τ) n) x

set_option maxHeartbeats 1000000 in
-- unfolding the projections of the input
lemma hlocE_lev (n : ℕ) : letI := (φE hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ
    n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap ((𝓘).B n) (TateGlue1.Xn ϖ 𝒯 B₁ n) ((𝓘).b n)) ((𝓘).E n) :=
  haveI : Module.Finite 𝒯 B₁ := by
    haveI := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
    haveI := TateGlue1.isIntegrallyClosed_T1' hϖ hker hκ hε h3 hE
    exact IsIntegralClosure.finite 𝒯 K L B₁
  haveI := TateGlue1.etale_Pn_T1 hϖ hker hκ hε h3 hE K L B₁ hunr₁ n
  TateGlue1.isLocalization_φE (TateS5.θ_ϖ hker) hker.le B₁ (w1 (ε * ϖ ^ m) b₄ t κ) n
    (TateGlue1.E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
        hL hBn hunr₁ τ) n)

/-- **The input over `V₁` with the implicit arguments of the level data `levelsS5`**
(`FormalLevel.NodeLevels.InputOf`; the covering `covTate` is `covOf …` by `rfl`). -/
def inpF : (levelsS5 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).InputOf :=
  inp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝓘F" => inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

instance instAlgXnF (n : ℕ) : Algebra ((𝓘F).B n) (TateGlue1.Xn ϖ 𝒯 B₁ n) :=
  inferInstanceAs (Algebra (EtaleTower.Tn ϖ 𝒯 n) (TateGlue1.Xn ϖ 𝒯 B₁ n))

instance instAlg0XnF (n : ℕ) : Algebra (𝓘F).B0 (TateGlue1.Xn ϖ 𝒯 B₁ n) :=
  inferInstanceAs (Algebra 𝒯 (TateGlue1.Xn ϖ 𝒯 B₁ n))

instance instTowerXnF (n : ℕ) :
    IsScalarTower (𝓘F).B0 ((𝓘F).B n) (TateGlue1.Xn ϖ 𝒯 B₁ n) :=
  inferInstanceAs (IsScalarTower 𝒯 (EtaleTower.Tn ϖ 𝒯 n) (TateGlue1.Xn ϖ 𝒯 B₁ n))

instance instAlgNRRF (l : ℕ) : Algebra 𝒩 ((𝓘F).R l) :=
  inferInstanceAs (Algebra 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerONRRF (l : ℕ) : IsScalarTower O 𝒩 ((𝓘F).R l) :=
  inferInstanceAs (IsScalarTower O 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instAlgRbRF (l : ℕ) :
    Algebra (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) ((𝓘F).R l) :=
  inferInstanceAs (Algebra 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerORbRF (l : ℕ) :
    IsScalarTower O (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) ((𝓘F).R l) :=
  inferInstanceAs (IsScalarTower O 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerRbRRF (l : ℕ) :
    IsScalarTower (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) ((𝓘F).R (l + 1))
      ((𝓘F).R l) :=
  inferInstanceAs (IsScalarTower 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (l + 1))
    (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

instance instTowerNRRRF (l : ℕ) : IsScalarTower 𝒩 ((𝓘F).R (l + 1)) ((𝓘F).R l) :=
  inferInstanceAs (IsScalarTower 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (l + 1))
    (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

set_option maxHeartbeats 1000000 in
-- instantiating the generic glueing at the Tate input
/-- **MR12 S6 G4: the level `n` of the M2 lift over `V₁` is `B₁/ϖⁿ⁺¹`**:
`B₁/ϖⁿ⁺¹ ≃ₐ[T1] Y n` (`FormalLevel.NodeLevels.levelEquivX` for the node level data
`levelsS5`), with components the node level patch and the étale level `φE`. -/
def equivY1 (n : ℕ) : TateGlue1.Xn ϖ 𝒯 B₁ n ≃ₐ[(𝓘F).B0] (𝓘F).Y hθ.out n :=
  (levelsS5 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).levelEquivX (𝓘F)
    (fun l a ↦ QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (TateS5.θ_ϖ hker) l a)
    (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl
    (towerORI := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
    (towerX := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
    (TateGlue1.toTensor hκ B₁ Bn hBn n) (toTensor_algebraMap hκ hBn n)
    (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (hρ_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (TateGlue1.isLocalization_toTensor hκ B₁ Bn hBn n)
    (φE hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (hE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (hlocE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)


/-- **The reduction `B₁/ϖⁿ⁺² → B₁/ϖⁿ⁺¹`.** -/
abbrev Xmap (n : ℕ) : TateGlue1.Xn ϖ 𝒯 B₁ (n + 1) →+* TateGlue1.Xn ϖ 𝒯 B₁ n :=
  Ideal.Quotient.factor (EtaleTower.In_succ_le (T := 𝒯) (B := B₁) (ϖ := ϖ) n)

/-- `B₁/ϖⁿ⁺¹ → NR/ϖⁿ⁺¹ ⊗ Bn` (`TateGlue1.toTensor`) typed into the node level of the input. -/
def tF (n : ℕ) : TateGlue1.Xn ϖ 𝒯 B₁ n →+* (𝓘F).R n ⊗[𝒩] Bn :=
  TateGlue1.toTensor hκ B₁ Bn hBn n

lemma tF_mk (n : ℕ) (b : B₁) : tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n
    (Ideal.Quotient.mk _ b) = (1 : (𝓘F).R n) ⊗ₜ algebraMap B₁ Bn b :=
  TateGlue1.toTensor_mk hκ B₁ Bn hBn n b

/-- The node level patches commute with the reductions (on generators). -/
lemma tF_succ_mk (n : ℕ) (b : B₁) :
    tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n (Ideal.Quotient.mk _ b) =
      FormalLevel.levelMap (𝓘F).R n (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ
          (n + 1) (Ideal.Quotient.mk _ b)) := by
  have h1 := tF_mk hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n b
  have h2 := tF_mk hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ (n + 1) b
  calc tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n (Ideal.Quotient.mk _ b)
        = (1 : (𝓘F).R n) ⊗ₜ algebraMap B₁ Bn b := h1
    _ = FormalLevel.levelMap (𝓘F).R n ((1 : (𝓘F).R (n + 1)) ⊗ₜ algebraMap B₁ Bn b) :=
      (FormalLevel.levelMap_one_tmul (Rt := (𝓘F).R) n (algebraMap B₁ Bn b)).symm
    _ = FormalLevel.levelMap (𝓘F).R n (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ
        (n + 1) (Ideal.Quotient.mk _ b)) :=
      congrArg _ h2.symm

/-- **The node level patches commute with the reductions** `B₁/ϖⁿ⁺² → B₁/ϖⁿ⁺¹`. -/
lemma tF_succ (n : ℕ) : (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n).comp (Xmap
    (ϖ := ϖ) (b₄ := b₄) (t := t) (κ := κ) (ε := ε) (m := m) (B₁ := B₁) n) =
    (FormalLevel.levelMap (𝓘F).R n).toRingHom.comp (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
        hL hBn hunr₁ τ (n + 1)) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun b ↦ tF_succ_mk hϖ hker hκ hε h3 hE hqM hq hM' hM'k
      hK hζ hL hBn hunr₁ τ n b)

set_option maxHeartbeats 1000000 in
-- the transition maps of the étale lifts
lemma hμE_lev (n : ℕ) (y : TateGlue1.Xn ϖ 𝒯 B₁ (n + 1)) :
    (𝓘F).sE n (φE hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ (n + 1) y) =
      φE hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n
        (Xmap (ϖ := ϖ) (b₄ := b₄) (t := t) (κ := κ) (ε := ε) (m := m) (B₁ := B₁) n y) := by
  haveI : Module.Finite 𝒯 B₁ := by
    haveI := TateGlue1.isDomain_T1' hϖ hκ hε h3 hE
    haveI := TateGlue1.isIntegrallyClosed_T1' hϖ hker hκ hε h3 hE
    exact IsIntegralClosure.finite 𝒯 K L B₁
  haveI := TateGlue1.etale_Pn_T1 hϖ hker hκ hε h3 hE K L B₁ hunr₁ n
  haveI := TateGlue1.etale_Pn_T1 hϖ hker hκ hε h3 hE K L B₁ hunr₁ (n + 1)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact (EtaleTower.levelEquiv_levelSucc (TateS5.θ_ϖ hker) hker.le n
    (TateGlue1.E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
        hL hBn hunr₁ τ) (n + 1))
    (TateGlue1.E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
        hL hBn hunr₁ τ) n)
    (algebraMap _ _ (Ideal.Quotient.mk _ b))).symm.trans
    (congrArg (EtaleTower.levelEquiv (TateS5.θ_ϖ hker) (w1 (ε * ϖ ^ m) b₄ t κ) hker.le n
      (TateGlue1.E1 hκ rfl (TateS5.θ_ϖ hker) hker.le (sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ
          hL hBn hunr₁ τ) n))
      (EtaleTower.levelSucc_mk n b))

end Data
end
end TateS6
end SemistableReduction
