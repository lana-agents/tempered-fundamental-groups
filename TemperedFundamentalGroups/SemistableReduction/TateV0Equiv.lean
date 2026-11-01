/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateV0Level
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevelsFamPsi

/-!
# The levels over `V₀` at the Tate data (MR12 T2 S6, G4 over `V₀`)

**`TateS6.equiv0`**: the level `n` of the M2 lift of a tame cover of the Tate curve over the
second chart `V₀` is `B₀/ϖⁿ⁺¹` (`NodeEtaleGlue.Overlap.levelEquiv0P` at the covering `VF` with the
cusp patch `cuspV`). Its inputs, all stated over the projections of `VF` and `inpF`:

* `TateS6.ωF`: the level-`n` overlap identification `omegaN n`;
* `TateS6.bridge1`, `TateS6.bridge2`: the two conjuncts of `om_witness` restated over `VF`;
* **`TateS6.hω0`**: the hypothesis `hω` (`Overlap.hω_of_mkC`, the witnesses chosen in the form of
  `om_witness`, so that no existential statement over the projections of `VF` is formed);
* **`TateS6.hψ1F`**: the hypothesis `hψ` for `equivY1` (`NodeLevels.mk_ψ_levelEquivXFam` for the
  family `eqFam`; the earlier `hψ1`, for the components of `eqFam`, is checked against the type
  needed here only by unfolding `eqFam`, which does not finish).

The statements with `letI`/`haveI` binders are `def`s with values in `Prop`: as `theorem`s their
processing for the `.olean` does not finish (they elaborate in about a second each).
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

local notation "𝓞" => om hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "𝓒" => cuspLevels hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "𝓓V" => cuspV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

local notation "𝓘C1" => NodeEtaleGlue.Input.C1 (inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL
  hBn hunr₁ τ)

local notation "𝓘Bs" => NodeEtaleGlue.Input.Bs (inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL
  hBn hunr₁ τ)

local notation "ρXF" => ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

local notation "omW" => om_witness hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ
  hBn hBc
  hunr₁ hunr₀ τ φ₀

set_option maxHeartbeats 1000000 in
-- the ascription unfolds the projections of `VF`
/-- `omegaN` over the projections of `VF`. -/
def ωF (n : ℕ) : haveI := (𝓥).hW0; haveI := (𝓥).hW0'
    letI := NodeEtaleGlue.awayAlg (W := (𝓥).W0) (C := (TateGlue1.Xn ϖ 𝒯0 B₀ n)) (𝓥).x0
    letI := NodeEtaleGlue.awayAlg (W := (𝓥).W0) (C := (TateGlue1.Xn ϖ 𝒯 B₁ n)) (𝓥).x1
    Localization.Away (algebraMap (𝓥).B0' (TateGlue1.Xn ϖ 𝒯0 B₀ n) (𝓥).x0) ≃ₐ[(𝓥).W0]
      Localization.Away (algebraMap (𝓘F).B0 (TateGlue1.Xn ϖ 𝒯 B₁ n) (𝓥).x1) :=
  omegaN (B₀ := B₀) (B₁ := B₁) hρ n

local notation "ωFF" => ωF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

set_option linter.defProp false in
set_option maxHeartbeats 400000 in
-- comparing the S5 form and the form over `VF` of the first conjunct
/-- The first conjunct of `om_witness` over the projections of `VF` (with `ωF`). -/
def bridge1 (n : ℕ) (b : B₀) (y : B₁) (k : ℕ)
    (h : letI := algT0T01 (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
      haveI := isLocalization_rho0 (ε * ϖ ^ m) b₄ t κ
      letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯0 B₀ n) (h0 (ε * ϖ ^ m) b₄ t κ)
      letI := AwayAlg.alg (W := 𝒲) (C := TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)
      omegaN (B₀ := B₀) (B₁ := B₁) hρ n
          (algebraMap (TateGlue1.Xn ϖ 𝒯0 B₀ n) _ (Ideal.Quotient.mk _ b)) *
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) (Localization.Away (algebraMap 𝒯
          (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)))
          (algebraMap 𝒯 (TateGlue1.Xn ϖ 𝒯 B₁ n) (h1 (ε * ϖ ^ m) b₄ t κ)) ^ k =
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) _ (Ideal.Quotient.mk _ y)) :
    haveI := (𝓥).hW0; haveI := (𝓥).hW0'
    letI := NodeEtaleGlue.awayAlg (W := (𝓥).W0) (C := (TateGlue1.Xn ϖ 𝒯0 B₀ n)) (𝓥).x0
    letI := NodeEtaleGlue.awayAlg (W := (𝓥).W0) (C := (TateGlue1.Xn ϖ 𝒯 B₁ n)) (𝓥).x1
    ωFF n (algebraMap (TateGlue1.Xn ϖ 𝒯0 B₀ n) _ (Ideal.Quotient.mk _ b)) *
        algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n)
          (Localization.Away (algebraMap (𝓘F).B0 (TateGlue1.Xn ϖ 𝒯 B₁ n) (𝓥).x1))
          (algebraMap (𝓘F).B0 (TateGlue1.Xn ϖ 𝒯 B₁ n) (𝓥).x1) ^ k =
      algebraMap (TateGlue1.Xn ϖ 𝒯 B₁ n) _ (Ideal.Quotient.mk _ y) := h

set_option linter.defProp false in
set_option maxHeartbeats 400000 in
-- comparing the S5 form and the form over `VF` of the second conjunct
/-- The second conjunct of `om_witness` over the projections of `VF` (with `VF.ω`). -/
def bridge2 (n : ℕ) (b : B₀) (y : B₁) (k : ℕ)
    (h : letI := algC0x (𝓢c).C0 (θ := θ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
      letI := algC1x (𝓢p).C1 (θ := θ) (π := ε * ϖ ^ m) (b₄ := b₄) (t := t) (κ := κ)
      (𝓞) (algebraMap (𝓢c).C0 _ (Ideal.Quotient.mk _ b : Cs θ 𝒯0 B₀)) *
        algebraMap (𝓢p).C1 (Localization.Away (algebraMap (TateGlue1.T1s θ (ε * ϖ ^ m) b₄ t κ)
          (𝓢p).C1 (Ideal.Quotient.mk _ (h1 (ε * ϖ ^ m) b₄ t κ))))
          (algebraMap (TateGlue1.T1s θ (ε * ϖ ^ m) b₄ t κ) (𝓢p).C1
            (Ideal.Quotient.mk _ (h1 (ε * ϖ ^ m) b₄ t κ))) ^ k =
        algebraMap (𝓢p).C1 _ (Ideal.Quotient.mk _ y : Cs θ 𝒯 B₁)) :
    (𝓥).ω (algebraMap (𝓥).C0 _ (ρX0 (B₀ := B₀) hker n (Ideal.Quotient.mk _ b))) *
        algebraMap 𝓘C1 (Localization.Away (algebraMap 𝓘Bs 𝓘C1 (𝓥).x1s))
          (algebraMap 𝓘Bs 𝓘C1 (𝓥).x1s) ^ k =
      algebraMap 𝓘C1 _ (ρXF n (Ideal.Quotient.mk _ y)) := h

local notation "bridge1F" => bridge1 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ
  hBn
    hBc hunr₁ hunr₀ τ φ₀

local notation "bridge2F" => bridge2 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ
  hBn
    hBc hunr₁ hunr₀ τ φ₀

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate overlap
/-- **The hypothesis `hω` at level `n`** (`Overlap.hω_of_mkC`, with the witnesses of
`om_witness`). -/
def hω0 (n : ℕ) :=
  (𝓥).hω_of_mkC n (ωFF n) (ρXF n) (ρX0 (B₀ := B₀) hker n) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _)
    (fun b ↦ (omW n b).choose) (fun b ↦ (omW n b).choose_spec.choose)
    (fun b ↦ bridge1F n b (omW n b).choose (omW n b).choose_spec.choose
      (omW n b).choose_spec.choose_spec.1)
    (fun b ↦ bridge2F n b (omW n b).choose (omW n b).choose_spec.choose
      (omW n b).choose_spec.choose_spec.2)

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate input and overlap
/-- **The hypothesis `hψ` for `equivY1`** (`NodeLevels.mk_ψ_levelEquivXFam` for `eqFam`). -/
def hψ1F (n : ℕ) (y : TateGlue1.Xn ϖ 𝒯 B₁ n) : letI := (𝓥).algBM n
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := (𝓘F).B n)) ((𝓥).M n))
      ((𝓥).ψ hθ.out (isUnit_of_θ_ne_zero hϖ hker) n (equivY1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK
          hζ hL hBn hunr₁ τ n y)) =
      (𝓥).γM n (ρXF n y) :=
  (levelsS5 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).mk_ψ_levelEquivXFam (𝓘F)
    (fun l a ↦ QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (TateS5.θ_ϖ hker) l a)
    (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl
    (towerORI := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
    (towerX := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
    (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (fun n ↦ toTensor_algebraMap hκ
        hBn n) (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (hρ_lev hϖ hker hκ hε
        h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
    (fun n ↦ TateGlue1.isLocalization_toTensor hκ B₁ Bn hBn n) (φE hϖ hker hκ hε h3 hE hqM hq hM'
        hM'k hK hζ hL hBn hunr₁ τ) (hE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ)
    (hlocE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (Xmap (ϖ := ϖ) (b₄ := b₄)
        (t := t) (κ := κ) (ε := ε) (m := m) (B₁ := B₁))
    (fun n y ↦ RingHom.congr_fun (tF_succ hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ
        n) y) (hμE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) (𝓥) n y

set_option maxHeartbeats 2000000 in
-- instantiating the generic glueing at the Tate overlap
/-- **MR12 S6 G4 over `V₀`: the level `n` of the M2 lift over `V₀` is `B₀/ϖⁿ⁺¹`**
(`NodeEtaleGlue.Overlap.levelEquiv0P` with the cusp patch `cuspV`). -/
def equiv0 (n : ℕ) :=
  (𝓥).levelEquiv0P (isUnit_of_θ_ne_zero hϖ hker) (𝓓V) (𝓒)
    (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    rfl HEq.rfl rfl n (equivY1 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n) (ωFF n)
        (tC (B₀ := B₀) hBc n)
    (CuspTower.toTensorC_algebraMap ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (CuspTower.isLocalization_toTensorC ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (ρXF n) (ρX0 (B₀ := B₀) hker n) (hρV hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd
        hρ hBn
    hBc hunr₁ hunr₀ τ φ₀ n) (EtaleTower.hJ hker.le n)
    (hψ1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
    hBc hunr₁ hunr₀ τ φ₀ n) (hx1F hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
    hBc hunr₁ hunr₀ τ φ₀ n) (hω0 hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn
    hBc hunr₁ hunr₀ τ φ₀ n)

end Data
end
end TateS6
end SemistableReduction
