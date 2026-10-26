/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspLevelPatchTr
import TemperedFundamentalGroups.SemistableReduction.TateCuspSpecial
import TemperedFundamentalGroups.SemistableReduction.TateNodeLevelPatch

/-!
# The level patches of the M2 lift over the Tate cusp chart (MR12 T2 S6, step G2c/G3)

For the cusp chart `Rc = T0[1/(1 + h)]` of the Tate model and the normalisation `B = B₀[1/(1 + h)]`
of `Rc` in a tame Galois cover (hypotheses of `TateCuspCov.cuspSpecial`):

* `TateCuspCov.covCusp_eq_covCuspOf`: the special-fibre covering `covCusp` is the generic
  `FormalCuspLevel.covCuspOf` of the chosen local forms `pointCuspData` (by `rfl`);
* `TateCuspCov.etale_Pn_Rc`, `formallyEtale_Tn_Rc`: the levels `(B/ϖˡ⁺¹B)[1/g]` are étale over
  `Rc/ϖˡ⁺¹` on `D(g)` for `g = s` (the cusp coordinate) and `g = z` (purity, `hreg_Rc`, `hunr`);
* **`TateCuspCov.cuspLevelsS6`**: the level data (`FormalCuspLevel.CuspLevels`) of the tower
  `towerC = CuspTower.cuspTower cuspSpecial …`: level points `(sIdeal 𝔪ⱼ).comap red`, level forms
  `levelCuspForm` at the cusp (`z ∈ 𝔪ⱼ`) and `levelEtaleForm` at the other points of `h̄ = 0`,
  cusp coordinate `htL` (by `rfl`), lifted idempotents (uniqueness of idempotents);
* **`TateCuspCov.levelPatchEquiv_Rc`**: `Rc/ϖˡ⁺¹ ⊗_{Rc} B ≃ G l` (the level-`l` patched algebra of
  the M2 lift); its compatibility with the transition maps of the tower is
  `(cuspLevelsS6 …).equiv_tr` (`FormalCuspLevel.CuspLevels.equiv_tr`).
-/

universe u

open Polynomial IsLocalRing Module TensorProduct

namespace SemistableReduction

namespace TateCuspCov

open TateTwoChart AdmissibleLift FormalKummer

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {ϖ π b₄ b₆ t κ ε : O} {m : ℕ}

set_option hygiene false in
local notation "ℛ" => RcT π b₄ t κ

set_option hygiene false in
local notation "𝓈" => CuspTower.sC (T0 π b₄ t κ) (TateGlue0.c0 π b₄ t κ) (h0 π b₄ t κ)

set_option hygiene false in
local notation "𝓏" => algebraMap (T0 π b₄ t κ) (RcT π b₄ t κ) (z0 π b₄ t κ)

/-- **`covCusp` is the generic covering `FormalCuspLevel.covCuspOf`** of the chosen local forms
`pointCuspData` (definitional). -/
theorem covCusp_eq_covCuspOf
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    [IsIntegralClosure B ℛ L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    (hk : ∀ j i, ((pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr
      (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j)).d i : k) ≠ 0) :
    covCusp hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ =
      FormalCuspLevel.covCuspOf (mC θ π b₄ t κ) (J_le_mC θ π b₄ t κ)
        (fun j ↦ pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr _
          (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j))
        (injective_mC θ π b₄ t κ) (sbar_mem_mC θ π b₄ t κ) (iInf_mC_le θ π b₄ t κ) φ₀ _
        (Polynomial.aeval_X _) (finite_Cs hϖ hker hπ hm hε h3 hE hκ hb₆ K L B)
        (etale_s hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr) hk :=
  rfl

/-- **The levels `(B/ϖˡ⁺¹B)[1/g]` of the normalisation are étale over `Rc/ϖˡ⁺¹`** if `g ∉ P`
implies `s ∉ P` at the points `P ∋ z` (purity at the closed points of the special fibre off the
cusp divisor). -/
theorem etale_Pn_Rc
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    [IsIntegralClosure B ℛ L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (g : ℛ) (hg : ∀ (P : Ideal ℛ) [P.IsMaximal], g ∉ P → 𝓏 ∈ P → 𝓈 ∉ P) (l : ℕ) :
    Algebra.Etale (EtaleTower.Tn ϖ ℛ l) (EtaleTower.Pn ϖ ℛ B g l) := by
  haveI := isDomain_Rc' hϖ hπ hε h3 hE hκ
  haveI := isIntegrallyClosed_Rc' hϖ hker hπ hm hε h3 hE hκ hb₆
  haveI : Module.Finite ℛ B := IsIntegralClosure.finite ℛ K L B
  haveI := finiteType_Rc (O := O) (π := π) (b₄ := b₄) (t := t) (κ := κ)
  haveI : Module.Finite (Rs θ ℛ) (Cs θ ℛ B) := finite_Cs hϖ hker hπ hm hε h3 hE hκ hb₆ K L B
  haveI : IsJacobsonRing (Rs θ ℛ) := TateGlue1.isJacobsonRing_quot (θ := θ) ℛ
  haveI : IsJacobsonRing (EtaleTower.CB θ ℛ B) := isJacobsonRing_of_isIntegral (R := Rs θ ℛ)
  have hϖJ := ϖ_mem_J (π := π) (b₄ := b₄) (t := t) (κ := κ) hker
  refine EtaleTower.etale_Pn_of_isEtaleAt_maximal (TateTwoChartNode.θ_ϖ hker) _ hker.le
    (fun Q _ hJQ hgQ ↦ ?_) l
  haveI : (Q.comap (algebraMap ℛ B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have hJP : J θ (R := ℛ) ≤ Q.comap (algebraMap ℛ B) := Ideal.map_le_iff_le_comap.1 hJQ
  have hgP : g ∉ Q.comap (algebraMap ℛ B) := hgQ
  obtain ⟨x, y, hx, hy, hxy⟩ := hreg_Rc hϖ hθ.out hker hπ hm hε h3 hE hκ hb₆ _ (hJP hϖJ)
  exact PurityLocal.isEtaleAt' K (L := L) _ hx hy hxy B
    (fun Q' _ hQ' ↦ hunr _ (hJP hϖJ) Q' hQ' fun hz ↦ map_ne_span _ hQ'.le (hg _ hgP hz)) Q rfl

/-- **`(Rc/ϖˡ⁺¹ ⊗ B)[1/g]` is formally étale over `Rc/ϖˡ⁺¹`** (hypotheses of `etale_Pn_Rc`). -/
theorem formallyEtale_Tn_Rc
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    [IsIntegralClosure B ℛ L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (g : ℛ) (hg : ∀ (P : Ideal ℛ) [P.IsMaximal], g ∉ P → 𝓏 ∈ P → 𝓈 ∉ P) (l : ℕ) :
    Algebra.FormallyEtale (EtaleTower.Tn ϖ ℛ l)
      (Localization.Away (algebraMap (EtaleTower.Tn ϖ ℛ l) (EtaleTower.Tn ϖ ℛ l ⊗[ℛ] B)
        (Ideal.Quotient.mk ((EtaleTower.Iv ϖ l).map (algebraMap O ℛ)) g))) := by
  haveI := etale_Pn_Rc hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr g hg l
  exact TateS6.formallyEtale_away_tensor (A := ℛ) (B := B)
    ((EtaleTower.Iv ϖ l).map (algebraMap O ℛ)) g

/-- `formallyEtale_Tn_Rc` with `algebraMap` (the form of `FormalCuspLevel.levelEtaleForm`). -/
theorem formallyEtale_Tn_Rc'
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    [IsIntegralClosure B ℛ L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (g : ℛ) (hg : ∀ (P : Ideal ℛ) [P.IsMaximal], g ∉ P → 𝓏 ∈ P → 𝓈 ∉ P) (l : ℕ) :
    Algebra.FormallyEtale (EtaleTower.Tn ϖ ℛ l)
      (Localization.Away (algebraMap (EtaleTower.Tn ϖ ℛ l) (EtaleTower.Tn ϖ ℛ l ⊗[ℛ] B)
        (algebraMap ℛ (EtaleTower.Tn ϖ ℛ l) g))) := by
  rw [Ideal.Quotient.algebraMap_eq]
  exact formallyEtale_Tn_Rc hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr g hg l

/-- At a point `𝔪 ∋ z` (the cusp) the chosen local form `pointCuspData` is the one of the chosen
étale-local Kummer data `isCuspNormAt_cusp`. -/
lemma pointCuspData_of_mem
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e]
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    [IsIntegralClosure B ℛ L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (𝔪 : Ideal ℛ) [𝔪.IsMaximal] (hJ : J θ (R := ℛ) ≤ 𝔪) (hs : 𝓈 ∈ 𝔪) (hz : 𝓏 ∈ 𝔪) :
    haveI := finiteType_Rc (O := O) (π := π) (b₄ := b₄) (t := t) (κ := κ)
    (pointCuspFormDataOf 𝔪 hJ (FormalKummer.surjective_mk_comp_of_isAlgClosed (θ := θ) 𝔪 hJ)
      (CuspNormAtData.ofIsCuspNormAt (isCuspNormAt_cusp hϖ hker hπ hε h3 hE hκ K hζ L hd B
        hunr 𝔪 hJ hs hz))).mono (dvd_of_eq (eP_of_mem hz).symm) =
      pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr 𝔪 hJ hs := by
  rw [pointCuspData, dif_pos hz]

/-- The cusp indices are invertible in `k` (they divide `e`). -/
lemma hk_C
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    [IsIntegralClosure B ℛ L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (j : Fin (nC θ π b₄ t κ)) (i : Fin (pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr
      (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j)).r) :
    ((pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr
      (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j)).d i : k) ≠ 0 := by
  intro h0
  obtain ⟨c, hc⟩ := ((pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr
    (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j)).hde i).trans
      (eP_dvd e _)
  exact he (by rw [hc, Nat.cast_mul, h0, zero_mul])

/-- **The tower of patched algebras of the cusp chart** (`CuspTower.cuspTower` of
`cuspSpecial …`). -/
abbrev towerC
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x)) :=
  CuspTower.cuspTower (cuspSpecial hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB)
    (TateTwoChartNode.θ_ϖ hker) hker.le (TateGlue0.isSMulRegular_h0 ϖ π b₄ t κ)

set_option hygiene false in
local notation "𝒯" => towerC hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB

set_option hygiene false in
local notation "𝒟" => fun j ↦ pointCuspData hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr
  (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j)

/-- **The cusp coordinate of the levels of `towerC` is the chart coordinate `s`** (the
hypothesis `htL` of `FormalCuspLevel.levelPatchEquiv`). -/
lemma htL_C
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))
    (l : ℕ) : ((𝒯).level l).M.t = algebraMap ℛ (FormalPatchLevel.Hat ((𝒯).f l)) 𝓈 := by
  change algebraMap (EtaleTower.Tn ϖ ℛ l) (FormalPatchLevel.Hat ((𝒯).f l))
    (Ideal.Quotient.mk _ 𝓈) = _
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Ideal.Quotient.algebraMap_eq]

/-- `J` is nilpotent on the levels `T/ϖˡ⁺¹`. -/
lemma hJnil_Tn {T : Type u} [CommRing T] [Algebra O T] (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
    (l : ℕ) : J θ (R := EtaleTower.Tn ϖ T l) ≤ nilradical _ := fun x hx ↦ ⟨l + 1, by
  have h := Ideal.pow_mem_pow hx (l + 1)
  rw [EtaleTower.hJ hker l] at h
  exact (Ideal.mem_bot).1 h⟩

/-- The level points `red⁻¹(𝔪ⱼ)` of `towerC` are maximal. -/
lemma isMaximal_mL
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))
    (l : ℕ) (j : Fin (nC θ π b₄ t κ)) :
    ((sIdeal (θ := θ) (mC θ π b₄ t κ j)).comap (red θ ((𝒯).e l))).IsMaximal :=
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j)
    (J_le_mC θ π b₄ t κ j)
  CompletionProd.isMaximal_comap (red θ ((𝒯).e l)) (surjective_red θ ((𝒯).e l))
    (fun j ↦ sIdeal (θ := θ) (mC θ π b₄ t κ j)) j

/-- The points `𝔪ⱼ` of `Rc` map into the level points. -/
lemma le_comap_mL
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))
    (l : ℕ) (j : Fin (nC θ π b₄ t κ)) : mC θ π b₄ t κ j ≤
      ((sIdeal (θ := θ) (mC θ π b₄ t κ j)).comap (red θ ((𝒯).e l))).comap
        (algebraMap ℛ (EtaleTower.Tn ϖ ℛ l)) := fun a ha ↦ by
  have h1 : ((𝒯).e l).symm (Ideal.Quotient.mk _ (algebraMap ℛ (EtaleTower.Tn ϖ ℛ l) a)) =
      Ideal.Quotient.mk _ a :=
    (AlgEquiv.symm_apply_eq _).2 (CuspTower.eqv_mk _ (TateTwoChartNode.θ_ϖ hker) l a).symm
  change ((𝒯).e l).symm (Ideal.Quotient.mk _ (algebraMap ℛ _ a)) ∈
    sIdeal (θ := θ) (mC θ π b₄ t κ j)
  rw [h1]
  exact Ideal.mem_map_of_mem _ ha

set_option maxHeartbeats 1000000 in
-- unfolding the chosen local forms at the cusp
/-- **The level forms of `towerC`**: at the cusp (`z ∈ 𝔪ⱼ`) `levelCuspForm` (base change of the
chosen splitting along `hatLift` of the residue map), elsewhere `levelEtaleForm` (étale lift). -/
def ΨC
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))
    (l : ℕ) (j : Fin (nC θ π b₄ t κ)) :
    haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
    haveI := fun j ↦ isMaximal_mL hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB l j
    FormalCuspLevel.LevelPointForm (FormalLevel.redHat (mC θ π b₄ t κ) ((𝒯).e l)
      (fun x ↦ CuspTower.eqv_mk _ (TateTwoChartNode.θ_ϖ hker) l x)
      (fun _ ↦ Ideal.map_comap_le) j) ((𝒟) j) := by
  haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j)
    (J_le_mC θ π b₄ t κ j)
  haveI := fun j ↦ isMaximal_mL hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB l j
  by_cases hz : 𝓏 ∈ mC θ π b₄ t κ j
  · haveI := finiteType_Rc (O := O) (π := π) (b₄ := b₄) (t := t) (κ := κ)
    have hres := FormalKummer.surjective_mk_comp_of_isAlgClosed (θ := θ) _ (J_le_mC θ π b₄ t κ j)
    let CN := CuspNormAtData.ofIsCuspNormAt (isCuspNormAt_cusp hϖ hker hπ hε h3 hE hκ K hζ L hd
      B hunr _ (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j) hz)
    let r : CN.N₁ →ₐ[ℛ] EtaleTower.Tn ϖ ℛ l ⧸
        (sIdeal (θ := θ) (mC θ π b₄ t κ j)).comap (red θ ((𝒯).e l)) :=
      FormalLevel.resMap CN.comap_eq
        (FormalCuspLevel.cHsurj0 _ (J_le_mC θ π b₄ t κ j) hres CN)
        (le_comap_mL hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB l j)
    have hr : ∀ w ∈ CN.𝔫, r w = 0 := fun w hw ↦ FormalLevel.resMap_eq_zero _ _ _ hw
    exact FormalCuspLevel.LevelPointForm.cast
      (pointCuspData_of_mem hϖ hker hπ hm hε h3 hE hκ hb₆ K hζ L hd B hunr
        (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j) (sC_mem_mC θ π b₄ t κ j) hz)
      ((FormalCuspLevel.levelCuspForm (mC θ π b₄ t κ j) (J_le_mC θ π b₄ t κ j) hres CN
        (FormalLevel.hatLift r)
        (FormalLevel.redHat (mC θ π b₄ t κ) ((𝒯).e l)
          (fun x ↦ CuspTower.eqv_mk _ (TateTwoChartNode.θ_ϖ hker) l x)
          (fun _ ↦ Ideal.map_comap_le) j)
        (FormalCuspLevel.redHat_hatLift_cusp (mC θ π b₄ t κ) (J_le_mC θ π b₄ t κ) ((𝒯).e l)
          (fun x ↦ CuspTower.eqv_mk _ (TateTwoChartNode.θ_ϖ hker) l x)
          (fun _ ↦ Ideal.map_comap_le) j CN hres r hr)).mono
        (dvd_of_eq (eP_of_mem hz).symm))
  · haveI := formallyEtale_Tn_Rc' hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr 𝓏
      (fun _ _ hzP hz' ↦ absurd hz' hzP) l
    exact FormalCuspLevel.levelEtaleForm (mC θ π b₄ t κ) (J_le_mC θ π b₄ t κ) 𝒟
      (injective_mC θ π b₄ t κ) (sbar_mem_mC θ π b₄ t κ) (iInf_mC_le θ π b₄ t κ) ((𝒯).e l)
      (fun x ↦ CuspTower.eqv_mk _ (TateTwoChartNode.θ_ϖ hker) l x) ((𝒯).hfe l)
      (CompletionProd.injective_comap (red θ ((𝒯).e l)) (surjective_red θ ((𝒯).e l)) _
        (injective_mC θ π b₄ t κ))
      (CompletionProd.mem_comap (red θ ((𝒯).e l)) (red_f θ ((𝒯).e l) ((𝒯).hfe l)) _
        (sbar_mem_mC θ π b₄ t κ))
      (CompletionProd.iInf_comap_le_radical (red θ ((𝒯).e l)) (surjective_red θ ((𝒯).e l))
        (red_f θ ((𝒯).e l) ((𝒯).hfe l)) _ ((ker_red θ ((𝒯).e l)).le.trans (hJnil_Tn hker.le l))
        (iInf_mC_le θ π b₄ t κ))
      (fun _ ↦ Ideal.map_comap_le) j
      (ψ_idem_comap θ ((𝒯).e l) ((𝒯).hfe l) (injective_mC θ π b₄ t κ)
        (sbar_mem_mC θ π b₄ t κ) (iInf_mC_le θ π b₄ t κ) (hJnil_Tn hker.le l) j)
      (fun i ↦ Nat.dvd_one.mp (((𝒟) j).hde i |>.trans (dvd_of_eq (eP_of_notMem hz))))
      hz (EtaleTower.hJ (T := ℛ) hker.le l)

set_option maxHeartbeats 1000000 in
-- unfolding the transported covering
/-- **The lifted idempotents of `towerC` are the Lemma F idempotents of the level points**
(uniqueness of idempotents lifting `Ê εⱼ`). -/
lemma hδL_C
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))
    (l : ℕ) (p : haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
      Σ j, Fin ((𝒟) j).r) :
    haveI := fun j ↦ isMaximal_mL hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB l j
    ((𝒯).level l).M.δ p = CompletionProd.idem
      (CompletionProd.injective_comap (red θ ((𝒯).e l)) (surjective_red θ ((𝒯).e l)) _
        (injective_mC θ π b₄ t κ))
      (CompletionProd.mem_comap (red θ ((𝒯).e l)) (red_f θ ((𝒯).e l) ((𝒯).hfe l)) _
        (sbar_mem_mC θ π b₄ t κ))
      (CompletionProd.iInf_comap_le_radical (red θ ((𝒯).e l)) (surjective_red θ ((𝒯).e l))
        (red_f θ ((𝒯).e l) ((𝒯).hfe l)) _ ((ker_red θ ((𝒯).e l)).le.trans (hJnil_Tn hker.le l))
        (iInf_mC_le θ π b₄ t κ)) p.1 := by
  haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j)
    (J_le_mC θ π b₄ t κ j)
  haveI := fun j ↦ isMaximal_mL hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB l j
  symm
  refine eq_of_isNilpotent_sub_of_isIdempotentElem
    (CompletionProd.isIdempotentElem_idem _ _ _ _) (((𝒯).level l).hcidem p)
    (isNilpotent_of_mem_ker_ψ θ (EtaleTower.hJ (T := ℛ) hker.le l) ?_)
  rw [RingHom.mem_ker, map_sub, sub_eq_zero]
  exact (ψ_idem_comap θ ((𝒯).e l) ((𝒯).hfe l) (injective_mC θ π b₄ t κ)
    (sbar_mem_mC θ π b₄ t κ) (iInf_mC_le θ π b₄ t κ) (hJnil_Tn hker.le l) p.1).trans
    (((𝒯).level l).M.hδ p).symm

set_option maxHeartbeats 1000000 in
-- the level data of `towerC` (unfolding `cuspSpecial`, `covCusp`)
/-- **The level data of the M2 lift over the Tate cusp chart** (`FormalCuspLevel.CuspLevels` for
the tower `towerC`): level points `(sIdeal 𝔪ⱼ).comap red`, level forms `ΨC`, cusp coordinate
`htL_C`, lifted idempotents `hδL_C`, étaleness `formallyEtale_Tn_Rc`. -/
def cuspLevelsS6
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x)) :
    haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
    haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j)
      (J_le_mC θ π b₄ t κ j)
    FormalCuspLevel.CuspLevels (mC θ π b₄ t κ) (J_le_mC θ π b₄ t κ) 𝒟 (injective_mC θ π b₄ t κ)
      (sbar_mem_mC θ π b₄ t κ) (iInf_mC_le θ π b₄ t κ) φ₀ (CuspTower.ψb (θ := θ) ℛ 𝓈 𝓈)
      (Polynomial.aeval_X _) (finite_Cs hϖ hker hπ hm hε h3 hE hκ hb₆ K L B)
      (etale_s hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr)
      (hk_C hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr)
      (EtaleTower.Tn ϖ ℛ) 𝒯 (fun l r ↦ CuspTower.eqv_mk _ (TateTwoChartNode.θ_ϖ hker) l r) :=
  haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j)
    (J_le_mC θ π b₄ t κ j)
  { 𝔪' := fun l j ↦ (sIdeal (θ := θ) (mC θ π b₄ t κ j)).comap (red θ ((𝒯).e l))
    isMaximal := isMaximal_mL hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB
    hinj := fun l ↦ CompletionProd.injective_comap (red θ ((𝒯).e l)) (surjective_red θ ((𝒯).e l))
      _ (injective_mC θ π b₄ t κ)
    hf := fun l ↦ CompletionProd.mem_comap (red θ ((𝒯).e l)) (red_f θ ((𝒯).e l) ((𝒯).hfe l)) _
      (sbar_mem_mC θ π b₄ t κ)
    hrad := fun l ↦ CompletionProd.iInf_comap_le_radical (red θ ((𝒯).e l))
      (surjective_red θ ((𝒯).e l)) (red_f θ ((𝒯).e l) ((𝒯).hfe l)) _
      ((ker_red θ ((𝒯).e l)).le.trans (hJnil_Tn hker.le l)) (iInf_mC_le θ π b₄ t κ)
    hm := fun _ _ ↦ Ideal.map_comap_le
    Ψ := ΨC hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB
    htL := htL_C hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB
    hδL := hδL_C hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB
    etale := fun l ↦ formallyEtale_Tn_Rc hϖ hker hπ hm hε h3 hE hκ hb₆ K L B hunr 𝓈
      (fun _ _ hs _ ↦ hs) l }

/-- **MR12 S6 G2c/G3 for the Tate cusp chart: the level-`l` patch of the M2 lift is
`Rc/ϖˡ⁺¹ ⊗_{Rc} B`.** For the normalisation `B = B₀[1/(1 + h)]` of the cusp chart `Rc` in a tame
Galois cover `L` (hypotheses of `cuspSpecial`), the level-`l` patched algebra of the tower
`towerC = CuspTower.cuspTower (cuspSpecial …)` is `(Rc/ϖˡ⁺¹) ⊗_{Rc} B`:
`Tn ϖ Rc l ⊗[Rc] B ≃ₐ[Tn ϖ Rc l] (towerC …).G hθ.out l` (`FormalCuspLevel.levelPatchEquiv` at
the level data `cuspLevelsS6`). -/
def levelPatchEquiv_Rc
    [IsDomain O] [IsDiscreteValuationRing O] [IsAlgClosed k] [hθ : Fact (Function.Surjective θ)]
    (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) (hπ : π = ε * ϖ ^ m)
    (hm : 1 ≤ m) (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE π b₄ b₆ ≠ 0)
    (hκ : κ * (t ^ 2 - b₆) = 1) (hb₆ : IsUnit b₆)
    [CharZero O] {e : ℕ} [NeZero e] (he : (e : k) ≠ 0)
    (K : Type u) [Field K] [Algebra ℛ K] [IsFractionRing ℛ K]
    {ζ : K} (hζ : IsPrimitiveRoot ζ e)
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (hd : finrank K L ∣ e) [Algebra ℛ L] [IsScalarTower ℛ K L]
    (B : Type u) [CommRing B] [Algebra ℛ B] [Algebra B L] [IsScalarTower ℛ B L]
    (hunr : ∀ (P : Ideal ℛ) [P.IsMaximal], algebraMap O ℛ ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap ℛ B) < P →
        (𝓏 ∈ P → (Q.comap (algebraMap ℛ B)).map (algebraMap ℛ (Localization.AtPrime P)) ≠
          Ideal.span {algebraMap ℛ (Localization.AtPrime P) 𝓈}) →
        Algebra.IsUnramifiedAt ℛ Q)
    (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (AdmissibleLift.fbar θ 𝓈))
    [Algebra (T0 π b₄ t κ) L] [IsScalarTower (T0 π b₄ t κ) ℛ L]
    (B₀ : Type u) [CommRing B₀] [Algebra (T0 π b₄ t κ) B₀] [Algebra B₀ L]
    [IsScalarTower (T0 π b₄ t κ) B₀ L] [IsIntegralClosure B₀ (T0 π b₄ t κ) L]
    [Algebra B₀ B] [IsScalarTower B₀ B L]
    [IsLocalization.Away (algebraMap (T0 π b₄ t κ) B₀ (TateGlue0.c0 π b₄ t κ)) B]
    (hB : ∀ x, algebraMap ℛ B (algebraMap (T0 π b₄ t κ) ℛ x) =
      algebraMap B₀ B (algebraMap (T0 π b₄ t κ) B₀ x))
    (l : ℕ) :=
  haveI := isIntegralClosure_B (π := π) (b₄ := b₄) (t := t) (κ := κ) L B B₀
  haveI := fun j ↦ FormalKummer.isMaximal_sIdeal (θ := θ) (mC θ π b₄ t κ j)
    (J_le_mC θ π b₄ t κ j)
  (cuspLevelsS6 hϖ hker hπ hm hε h3 hE hκ hb₆ he K hζ L hd B hunr φ₀ B₀ hB).equiv
    (TateTwoChartNode.isUnit_of_θ_ne_zero' hϖ hker) l

end

end TateCuspCov

end SemistableReduction
