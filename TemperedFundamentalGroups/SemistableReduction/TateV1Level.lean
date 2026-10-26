/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateSpecial1
import TemperedFundamentalGroups.SemistableReduction.EtaleLevelLift

/-!
# The levels of the normalisation over the Tate chart `V₁` (MR12 T2 S6, step G4, pieces)

For the normalisation `B₁` of the Tate chart `T1` in a tame cover `L` (setting of
`TateGlue1.special1`) and its localization `B = B₁[1/D]` (the normalisation of the node chart
`NR`), the levels `Xn n = B₁/ϖⁿ⁺¹B₁`:

* **`TateGlue1.etale_Pn_T1`**: `(B₁/ϖⁿ⁺¹)[1/w]` is étale over `T1/ϖⁿ⁺¹` (purity at the closed
  points of the special fibre off the nodes, `exists_regular_pair_T1`, `PurityLocal.isEtaleAt'`);
* **`TateGlue1.φE`**: `Xn n → L.E` for any étale lift `L` of `B₁/JB₁` over `D(w)` (the localization
  `Xn n → (Xn n)[1/w]` followed by `EtaleTower.levelEquiv`), a localization away from `w`
  (`isLocalization_φE`), compatible with the reductions (`σ_φE`);
* **`TateGlue1.toTensor`**: `Xn n → NR/ϖⁿ⁺¹ ⊗_{NR} B`, `b̄ ↦ 1 ⊗ b`, a localization away from `D`
  (`isLocalization_toTensor`; `NormAway.isLocalization_quotMap`).
-/

universe u

open Module TensorProduct

namespace SemistableReduction

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift
open FormalKummer (Cs)

namespace TateGlue1

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ}

local notation "𝒯" => T1 (ε * ϖ ^ m) b₄ t κ

local notation "𝒩" => NR b₄ b₆ ϖ m ε

/-- **The levels of the normalisation**: `Xn n = B₁/ϖⁿ⁺¹B₁`. -/
abbrev Xn (ϖ : O) (T B₁ : Type u) [CommRing T] [Algebra O T] [CommRing B₁] [Algebra T B₁]
    (n : ℕ) : Type u :=
  B₁ ⧸ (EtaleTower.In ϖ T n).map (algebraMap T B₁)

section Etale

variable [IsDomain O] [IsDiscreteValuationRing O] [hθ : Fact (Function.Surjective θ)]
  (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ}) [NeZero m]
  (hκ : κ * (t ^ 2 - b₆) = 1) (hε : εi * ε = 1) (h3 : (3 : O) ≠ 0)
  (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
  (K : Type u) [Field K] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) K]
  [IsFractionRing (T1 (ε * ϖ ^ m) b₄ t κ) K]
  (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
  [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) L] [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) K L]
  (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁] [Algebra B₁ L]
  [IsScalarTower (T1 (ε * ϖ ^ m) b₄ t κ) B₁ L]
  [IsIntegralClosure B₁ (T1 (ε * ϖ ^ m) b₄ t κ) L]
  (hunr : ∀ (P : Ideal (T1 (ε * ϖ ^ m) b₄ t κ)) [P.IsMaximal],
    algebraMap O (T1 (ε * ϖ ^ m) b₄ t κ) ϖ ∈ P → ∀ (Q : Ideal B₁) [Q.IsPrime],
      Q.comap (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁) < P →
        Algebra.IsUnramifiedAt (T1 (ε * ϖ ^ m) b₄ t κ) Q)

include hϖ hker hκ hε h3 hE K L hunr in
/-- **The levels `(B₁/ϖⁿ⁺¹)[1/w]` are étale over `T1/ϖⁿ⁺¹`** (purity at the closed points of the
special fibre off the nodes). -/
theorem etale_Pn_T1 (n : ℕ) :
    Algebra.Etale (EtaleTower.Tn ϖ 𝒯 n) (EtaleTower.Pn ϖ 𝒯 B₁ (w1 (ε * ϖ ^ m) b₄ t κ) n) := by
  haveI := isDomain_T1' hϖ hκ hε h3 hE
  haveI := isIntegrallyClosed_T1' hϖ hker hκ hε h3 hE
  haveI : Module.Finite 𝒯 B₁ := IsIntegralClosure.finite 𝒯 K L B₁
  haveI : Algebra.FiniteType O 𝒯 :=
    Algebra.FiniteType.trans (S := Polynomial O) inferInstance inferInstance
  haveI : IsJacobsonRing (𝒯 ⧸ J θ (R := 𝒯)) := isJacobsonRing_quot 𝒯
  haveI : Module.Finite 𝒯 (Cs θ 𝒯 B₁) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒯 _).toLinearMap Ideal.Quotient.mk_surjective
  haveI : Module.Finite (𝒯 ⧸ J θ (R := 𝒯)) (Cs θ 𝒯 B₁) :=
    Module.Finite.of_restrictScalars_finite 𝒯 _ _
  haveI : IsJacobsonRing (EtaleTower.CB θ 𝒯 B₁) :=
    isJacobsonRing_of_isIntegral (R := 𝒯 ⧸ J θ (R := 𝒯))
  have hϖJ : algebraMap O 𝒯 ϖ ∈ J θ (R := 𝒯) := Ideal.mem_map_of_mem _ (by
    rw [hker]; exact Ideal.mem_span_singleton_self ϖ)
  refine EtaleTower.etale_Pn_of_isEtaleAt_maximal
    (RingHom.mem_ker.1 (hker ▸ Ideal.mem_span_singleton_self ϖ)) _ hker.le
    (fun Q _ hJQ hwQ ↦ ?_) n
  haveI : (Q.comap (algebraMap 𝒯 B₁)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have hJP : J θ (R := 𝒯) ≤ Q.comap (algebraMap 𝒯 B₁) := Ideal.map_le_iff_le_comap.1 hJQ
  obtain ⟨y, h1, h2, h3⟩ := exists_regular_pair_T1 hϖ hθ.out hker rfl (Nat.pos_of_neZero m) hκ
    (Q.comap (algebraMap 𝒯 B₁)) (hJP hϖJ) hwQ
  exact PurityLocal.isEtaleAt' K (L := L) _ h1 h2 h3 B₁ (hunr _ (hJP hϖJ)) Q rfl

end Etale

section Levels

variable {T : Type u} [CommRing T] [Algebra O T] (hϖ : θ ϖ = 0)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
  (B₁ : Type u) [CommRing B₁] [Algebra T B₁] [Module.Finite T B₁] (w : T) (n : ℕ)
  [Algebra.FormallyEtale (EtaleTower.Tn ϖ T n) (EtaleTower.Pn ϖ T B₁ w n)]
  (Lf : EtaleTower.Lift T hϖ (EtaleTower.CB θ T B₁) w n)

/-- **The étale piece of the level `B₁/ϖⁿ⁺¹`**: `Xn n → (Xn n)[1/w] ≃ Lf.E`. -/
def φE : Xn ϖ T B₁ n →ₐ[EtaleTower.Tn ϖ T n] Lf.E :=
  (EtaleTower.levelEquiv hϖ w hker n Lf).toAlgHom.comp
    (IsScalarTower.toAlgHom (EtaleTower.Tn ϖ T n) (Xn ϖ T B₁ n) (EtaleTower.Pn ϖ T B₁ w n))

/-- `φE` is compatible with the reductions to `(B₁/JB₁)[1/w̄]`. -/
lemma σ_φE (x : Xn ϖ T B₁ n) :
    letI := EtaleTower.algC T hϖ (EtaleTower.CB θ T B₁) n
    Lf.σ (Ideal.Quotient.mk _ (φE hϖ hker B₁ w n Lf x)) =
      algebraMap (EtaleTower.CB θ T B₁) (EtaleTower.Cb θ T (EtaleTower.CB θ T B₁) w)
        (EtaleTower.red hϖ n x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact EtaleTower.σ_levelEquiv hϖ w hker n Lf b

/-- **`φE` is a localization away from `w`.** -/
theorem isLocalization_φE : letI := (φE hϖ hker B₁ w n Lf).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (EtaleTower.Tn ϖ T n) (Xn ϖ T B₁ n) (Ideal.Quotient.mk _ w))
      Lf.E := by
  letI := (φE hϖ hker B₁ w n Lf).toRingHom.toAlgebra
  have h : IsLocalization.Away (algebraMap (EtaleTower.Tn ϖ T n) (Xn ϖ T B₁ n)
      (Ideal.Quotient.mk _ w)) (EtaleTower.Pn ϖ T B₁ w n) := by
    rw [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact Localization.isLocalization
  exact RingHomAway.equiv (algebraMap (Xn ϖ T B₁ n) (EtaleTower.Pn ϖ T B₁ w n))
    (EtaleTower.levelEquiv hϖ w hker n Lf).toRingEquiv _ (RingHomAway.of_algebra _)

end Levels

section Tensor

variable (hκ : κ * (t ^ 2 - b₆) = 1)
  (B₁ : Type u) [CommRing B₁] [Algebra (T1 (ε * ϖ ^ m) b₄ t κ) B₁]
  (B : Type u) [CommRing B] [Algebra (NR b₄ b₆ ϖ m ε) B] [Algebra B₁ B]
  (hB : ∀ x, algebraMap (NR b₄ b₆ ϖ m ε) B (toNode b₄ hκ rfl x) =
    algebraMap B₁ B (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ x)) (n : ℕ)

include hκ in
omit [Algebra B₁ B] in
/-- The ideal `ϖⁿ⁺¹` of the node chart is the image of the one of `T1`. -/
lemma IRb_eq : letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
    QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n =
      (EtaleTower.In ϖ 𝒯 n).map (algebraMap 𝒯 𝒩) := by
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  haveI := isScalarTower_NR (b₄ := b₄) (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ)
    hκ rfl
  rw [EtaleTower.In, Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **The node side of the level `B₁/ϖⁿ⁺¹`**: `Xn n → NR/ϖⁿ⁺¹ ⊗_{NR} B`, `b̄ ↦ 1 ⊗ b`. -/
def toTensor : Xn ϖ 𝒯 B₁ n →+*
    QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n ⊗[𝒩] B :=
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  letI := TateGlue1.algTB B₁ B (ε := ε) (ϖ := ϖ) (m := m) (b₄ := b₄) (t := t) (κ := κ)
  haveI : IsScalarTower 𝒯 𝒩 B := IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower 𝒯 B₁ B := IsScalarTower.of_algebraMap_eq' rfl
  (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n)).toRingEquiv.toRingHom.comp
    (NormAway.quotMap (B₁ := B₁) (B := B) (EtaleTower.In ϖ 𝒯 n)
      (QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n) (IRb_eq hκ n))

lemma toTensor_mk (b : B₁) :
    toTensor hκ B₁ B hB n (Ideal.Quotient.mk _ b) = 1 ⊗ₜ algebraMap B₁ B b :=
  rfl

variable [IsLocalization.Away
    (algebraMap (T1 (ε * ϖ ^ m) b₄ t κ) B₁ (DT (ε * ϖ ^ m) b₄ t κ)) B]

/-- **`toTensor` is a localization away from `D`.** -/
theorem isLocalization_toTensor : letI := (toTensor hκ B₁ B hB n).toAlgebra
    IsLocalization.Away (algebraMap (EtaleTower.Tn ϖ 𝒯 n) (Xn ϖ 𝒯 B₁ n)
      (Ideal.Quotient.mk _ (DT (ε * ϖ ^ m) b₄ t κ)))
      (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n ⊗[𝒩] B) := by
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  letI := TateGlue1.algTB B₁ B (ε := ε) (ϖ := ϖ) (m := m) (b₄ := b₄) (t := t) (κ := κ)
  haveI : IsScalarTower 𝒯 𝒩 B := IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower 𝒯 B₁ B := IsScalarTower.of_algebraMap_eq' rfl
  exact RingHomAway.equiv _ (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B
      (QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n)).toRingEquiv _
    (NormAway.isLocalization_quotMap (B₁ := B₁) (B := B) (EtaleTower.In ϖ 𝒯 n)
      (QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n) (IRb_eq hκ n)
      (DT (ε * ϖ ^ m) b₄ t κ))

end Tensor

end

end TateGlue1

end SemistableReduction
