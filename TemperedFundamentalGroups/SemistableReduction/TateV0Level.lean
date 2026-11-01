/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateV0Glue
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelEquivP
import TemperedFundamentalGroups.SemistableReduction.TateOmegaNormCWitness

/-!
# Level data over `V₀` at the Tate data (MR12 T2 S6, G4 over `V₀`)

Inputs of `NodeEtaleGlue.Overlap.levelEquiv0P` at the covering `VF` over `V₀` of the tame cover
`L` of the Tate curve (data of `TateS5`):

* **`TateS6.cuspV`**: the cusp patch `cuspF` typed as a patch over the projections of `VF`
  (so that `VF.P0 = cuspV.piece` holds by `rfl`);
* `TateS6.hρV`: the reduction hypothesis of the cusp patch side at level `n`
  (`CuspLevels.hρ_of_mk`);
* **`TateS6.om_witness`**: for `b ∈ B₀` a witness `(y, k)` of the level-`n` overlap
  identification `omegaN n` and of the overlap datum `om` (`omega_witness` and
  `TateGlue0.omegaNormC_mul_pow`);
* `TateS6.hx1F`: the hypothesis `hx1` (`Overlap.hx1_of_algHom`).
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


local notation "𝓢c" => sc hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "𝓢p" => sp hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝒯0" => T0 (ε * ϖ ^ m) b₄ t κ

local notation "𝒲" => T01 (ε * ϖ ^ m) b₄ t κ


local notation "𝓓" => cuspF hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "ℛ" => RcT (ε * ϖ ^ m) b₄ t κ

local notation "𝓘F" => inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "𝓥" => VF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "𝓒" => cuspLevels hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

set_option maxHeartbeats 4000000 in
-- the ascription unfolds the projections of `VF`
/-- **The cusp patch over the projections of `VF`** (`cuspF`). -/
def cuspV : (𝓒).PatchInputOf (πL := πF hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀)
    (𝓥).B' (𝓥).qB' (𝓥).C0 (𝓥).x0 (𝓥).c0 (𝓥).x0s (𝓥).c0s (𝓥).ϖ := 𝓓

local notation "𝓓V" => cuspV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate cusp patch
/-- **The reduction hypothesis of the cusp patch side at level `n`** (`CuspLevels.hρ_of_mk`). -/
def hρV (n : ℕ) :=
  (𝓒).hρ_of_mk (𝓓V) (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerRII := fun l ↦ inferInstanceAs
      (IsScalarTower ℛ (EtaleTower.Tn ϖ ℛ (l + 1)) (EtaleTower.Tn ϖ ℛ l)))
    (tC (B₀ := B₀) hBc n) (ρX0 (B₀ := B₀) hker n) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (algebraMap B₀ Bc)
    (fun b ↦ CuspTower.toTensorC_mk ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n b)
    (fun _ ↦ rfl)

local notation "𝓞" => om hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

set_option maxHeartbeats 1000000 in
-- relating the overlap datum `om = omegaNormC …` to `omegaNorm`
/-- **The witness of the overlap identification for the datum `om`**: for `b ∈ B₀` there are
`y ∈ B₁`, `k` with `ωn(b̄/1)·h'ᵏ = ȳ/1` and `om(b̄/1)·h̄'ᵏ = ȳ/1`. -/
theorem om_witness (n : ℕ) (b : B₀) : ∃ (y : B₁) (k : ℕ),
    (letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ);
      haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ;
      letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯0 B₀ n) (h0 (ε * ϖ ^ m) b₄ t κ);
      letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ);
      omegaN (B₀ := B₀) (B₁ := B₁) hρ n (algebraMap (TateGlue1.Xn ϖ 𝒯0 B₀ n) _ (Ideal.Quotient.mk
          _ b)) *
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) (Localization.Away (algebraMap 𝒯
          (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)))
          (algebraMap 𝒯 (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)) ^ k =
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) _ (Ideal.Quotient.mk _ y)) ∧
    (letI := algC0x (𝓢c).C0 (θ := θ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ);
      letI := algC1x (𝓢p).C1 (θ := θ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ);
      (𝓞) (algebraMap (𝓢c).C0 _ (Ideal.Quotient.mk _ b : Cs θ 𝒯0 B₀)) *
        algebraMap (𝓢p).C1 (Localization.Away (algebraMap (TateGlue1.T1s θ (ε * ϖ ^ m) b₄ t κ)
          (𝓢p).C1 (Ideal.Quotient.mk _ (h1 (ε * ϖ ^ m) b₄ t κ))))
          (algebraMap (TateGlue1.T1s θ (ε * ϖ ^ m) b₄ t κ) (𝓢p).C1
            (Ideal.Quotient.mk _ (h1 (ε * ϖ ^ m) b₄ t κ))) ^ k =
        algebraMap (𝓢p).C1 _ (Ideal.Quotient.mk _ y : Cs θ 𝒯 B₁)) :=
  (omega_witness (B₀ := B₀) (B₁ := B₁) hρ n b).elim fun y hy ↦ hy.elim fun k hk ↦
    ⟨y, k, hk.1, TateGlue0.omegaNormC_mul_pow hκ rfl (𝓢p) AlgEquiv.refl hρ
      (TateS5.h0_ne_zero hρ) TateS5.h1_ne_zero (Ideal.Quotient.mk _ b : Cs θ 𝒯0 B₀)
      (Ideal.Quotient.mk _ y : Cs θ 𝒯 B₁) k hk.2⟩


set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate overlap
/-- The hypothesis `hx1` at level `n`. -/
def hx1F (n : ℕ) :=
  (𝓥).hx1_of_algHom n (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (towerB := instTowerXnF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)


end Data
end
end TateS6
end SemistableReduction
