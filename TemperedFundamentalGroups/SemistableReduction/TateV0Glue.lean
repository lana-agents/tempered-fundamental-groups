/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateV0Omega
import TemperedFundamentalGroups.SemistableReduction.TateCuspLevelPatch
import TemperedFundamentalGroups.SemistableReduction.TateGlue0CuspTower
import TemperedFundamentalGroups.SemistableReduction.CuspTensorLevel
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Cusp
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelPsi
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelEquivX
import TemperedFundamentalGroups.SemistableReduction.TateV1GlueFam

/-!
# The cusp patch and the overlap over `V₀` at the Tate data (MR12 T2 S6, G4 over `V₀`)

For the tame cover `L` of the Tate curve (data of `TateS5`) with normalisation `B₀` of the chart
`T0` and its localization `Bc = B₀[1/(1 + h)]` (the normalisation of the cusp chart `Rc`):

* `TateS6.cuspLevels`: the cusp level data `TateCuspCov.cuspLevelsS6` at the data of `sc`;
* **`TateS6.cuspF`**: the cusp patch `CuspTower.cuspInput (sc …)` typed as
  `FormalCuspLevel.CuspLevels.PatchInputOf` of `cuspLevels` (the ascription unfolds `covCusp` to
  `covCuspOf` once), so that the generic results of `NodeEtaleGlueV0Cusp` apply to it;
* `TateS6.tC` (`B₀/ϖⁿ⁺¹ → Rc/ϖⁿ⁺¹ ⊗ Bc`), `TateS6.ρX0` (`B₀/ϖⁿ⁺¹ → B₀/JB₀`), `TateS6.hρ0`;
* **`TateS6.φP0`** (`B₀/ϖⁿ⁺¹ → G n`, the level-`n` cusp patch), `TateS6.hP0` (a localization
  away from `1 + h`), **`TateS6.hPℓ0`** (its special fibre on the overlap is `ℓ0 ∘ ρX0`);
* **`TateS6.VF`**: the covering over `V₀` (`TateGlue0.overlapP` with the piece of `cuspF`,
  definitionally `overlapCusp` at the data of S5) over `inpF`; `TateS6.hψ1` (the hypothesis `hψ`
  of `Overlap.levelEquiv0X` for `equivY1`).

Instance arguments over the levels of `cuspF` are passed by name (`algRI`, `towerORI`,
`towerRII`) as instances of the levels `Rc/ϖˡ⁺¹`: type class inference on `(cuspF …).R l` takes
seconds per query.
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

/-- **The cusp level data** (`TateCuspCov.cuspLevelsS6` at the data of `sc`). -/
abbrev cuspLevels :=
  TateCuspCov.cuspLevelsS6 hϖ hker rfl (Nat.one_le_iff_ne_zero.2 (NeZero.ne m))
    (.of_mul_eq_one_right εi hε) h3 hE hκ hb₆ he K hζe L hd Bc
    (fun P _ hϖP Q _ hQ hz ↦ hunr_Bc hκ hBc hunr₀ P hϖP Q hQ hz) φ₀ B₀ hBc

set_option maxHeartbeats 4000000 in
-- the ascription unfolds `covCusp` to `covCuspOf` (`TateCuspCov.covCusp_eq_covCuspOf`)
/-- **The cusp patch over `D(1 + h)`** (`CuspTower.cuspInput (sc …)`) with the implicit arguments
of the cusp level data (`FormalCuspLevel.CuspLevels.PatchInputOf`). -/
def cuspF : (cuspLevels hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀).PatchInputOf
    (TateGlue0.B ϖ (ε * ϖ ^ m) b₄ t κ) (EtaleTower.q 𝒯0 (TateS5.θ_ϖ hker)) (𝓢c).C0
    (h0 (ε * ϖ ^ m) b₄ t κ) (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)
    (Ideal.Quotient.mk _ (h0 (ε * ϖ ^ m) b₄ t κ))
    (Ideal.Quotient.mk _ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ)) ϖ :=
  CuspTower.cuspInput (𝓢c) (TateS5.θ_ϖ hker) hker.le (isSMulRegular_h0 ϖ (ε * ϖ ^ m) b₄ t κ)

local notation "𝓒" => cuspLevels hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "𝓓" => cuspF hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀

local notation "ℛ" => RcT (ε * ϖ ^ m) b₄ t κ

/-- `B₀/ϖⁿ⁺¹ → Rc/ϖⁿ⁺¹ ⊗_{Rc} Bc` (`CuspTower.toTensorC`). -/
abbrev tC (n : ℕ) : TateGlue1.Xn ϖ 𝒯0 B₀ n →+* EtaleTower.Tn ϖ ℛ n ⊗[ℛ] Bc :=
  CuspTower.toTensorC ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n

/-- **The reduction `B₀/ϖⁿ⁺¹ → B₀/JB₀`.** -/
abbrev ρX0 (n : ℕ) : TateGlue1.Xn ϖ 𝒯0 B₀ n →+* Cs θ 𝒯0 B₀ :=
  EtaleTower.red (T := 𝒯0) (B := B₀) (TateS5.θ_ϖ hker) n

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate cusp patch
/-- **The reduction hypothesis of the cusp patch side at level `n`** (`CuspLevels.hρ_of_mk`). -/
def hρ0 (n : ℕ) :=
  (𝓒).hρ_of_mk (𝓓) (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerRII := fun l ↦ inferInstanceAs
      (IsScalarTower ℛ (EtaleTower.Tn ϖ ℛ (l + 1)) (EtaleTower.Tn ϖ ℛ l)))
    (tC (B₀ := B₀) hBc n) (ρX0 (B₀ := B₀) hker n) (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective (algebraMap B₀ Bc)
    (fun b ↦ CuspTower.toTensorC_mk ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n b)
    (fun _ ↦ rfl)

set_option maxHeartbeats 1000000 in
-- instantiating the generic map at the Tate cusp patch
/-- **The cusp patch side of the level `B₀/ϖⁿ⁺¹`**: `B₀/ϖⁿ⁺¹ → Rc/ϖⁿ⁺¹ ⊗ Bc ≃ G n`. -/
def φP0 (n : ℕ) :=
  (𝓒).φPX (𝓓) (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl (tC (B₀ := B₀) hBc n)
    (CuspTower.toTensorC_algebraMap ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate cusp patch
/-- The cusp patch side is a localization away from `1 + h`. -/
@[reducible] def hP0 (n : ℕ) :=
  (𝓒).isLocalization_φPX (𝓓) (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl (tC (B₀ := B₀) hBc n)
    (CuspTower.toTensorC_algebraMap ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)
    (CuspTower.isLocalization_toTensorC ϖ (TateGlue0.c0 (ε * ϖ ^ m) b₄ t κ) B₀ Bc hBc n)

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate cusp patch
/-- The special fibre of the cusp patch side on the overlap is `ℓ0 ∘ ρX0`. -/
def hPℓ0 (n : ℕ) :=
  (𝓒).mk_Loc_φPX (𝓓) (algRI := fun l ↦ inferInstanceAs (Algebra ℛ (EtaleTower.Tn ϖ ℛ l)))
    (towerORI := fun l ↦ inferInstanceAs (IsScalarTower O ℛ (EtaleTower.Tn ϖ ℛ l)))
    (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl (tC (B₀ := B₀) hBc n) (ρX0 (B₀ := B₀) hker n)
    (hρ0 hϖ hker hκ hε h3 hE hb₆ he hζe hd hBc hunr₀ φ₀ n)

local notation "𝓘F" => inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ

/-- **The covering over `V₀`**: `TateGlue0.overlapP` with the cusp patch `cuspF` over `D(1 + h)`
(definitionally `TateGlue0.overlapCusp` at the data of S5), over `inpF`. -/
def VF : NodeEtaleGlue.Overlap (inpF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) :=
  overlapP hκ rfl hε (TateS5.θ_ϖ hker) (piP hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn
      hunr₁ τ) (piP_pow hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ) hker.le (𝓢p)
    (NeZero.ne m) (𝓢c).C0
    (om hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc hunr₁ hunr₀ τ φ₀)
    ((𝓓).piece hθ.out (isUnit_of_θ_ne_zero hϖ hker))

local notation "𝓥" => VF hϖ hker hκ hε h3 hE hb₆ hqM hq hM' hM'k he hK hζ hζe hL hd hρ hBn hBc
  hunr₁ hunr₀ τ φ₀

instance instAlgVXn (n : ℕ) : Algebra (𝓥).B0' (TateGlue1.Xn ϖ 𝒯0 B₀ n) :=
  inferInstanceAs (Algebra 𝒯0 (TateGlue1.Xn ϖ 𝒯0 B₀ n))

set_option linter.defProp false in
set_option maxHeartbeats 1000000 in
-- instantiating the generic lemma at the Tate input and overlap
/-- **The hypothesis `hψ` at level `n`** (`NodeLevels.mk_ψ_levelEquivX` for `equivY1`). -/
def hψ1 (n : ℕ) :=
  (levelsS5 hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ).mk_ψ_levelEquivX (𝓘F)
    (fun l a ↦ QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (TateS5.θ_ϖ hker) l a)
    (isUnit_of_θ_ne_zero hϖ hker) rfl HEq.rfl
    (towerORI := fun _ ↦ IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
    (tF hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (toTensor_algebraMap hκ hBn n)
    (ρX hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (hρ_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (towerX := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl)
    (TateGlue1.isLocalization_toTensor hκ B₁ Bn hBn n)
    (φE hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (hE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n)
    (hlocE_lev hϖ hker hκ hε h3 hE hqM hq hM' hM'k hK hζ hL hBn hunr₁ τ n) (𝓥)


end Data
end
end TateS6
end SemistableReduction
