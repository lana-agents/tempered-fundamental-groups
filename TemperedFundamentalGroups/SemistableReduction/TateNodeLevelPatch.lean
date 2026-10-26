/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalLevelPatch
import TemperedFundamentalGroups.SemistableReduction.TateNodeCovering
import TemperedFundamentalGroups.SemistableReduction.EtaleLevelLift
import TemperedFundamentalGroups.SemistableReduction.QuadNodeTower

/-!
# The level patches of the M2 lift over the Tate node chart (MR12 T2 S6, step G3)

`TateTwoChartNode.levelPatchEquiv_NR`: the level-`l` patched algebra of the tower `towerS6` of
the covering `covNR_of_regular …` of the Tate node chart is `NR/ϖˡ⁺¹ ⊗_{NR} B`
(instance of `FormalLevel.levelPatchEquiv`); the étaleness input is `formallyEtale_Rn`
(purity, `etale_Pn_NR`). The level node coordinates of the tower are the chart coordinates
(`hχL_S6`), and `hO` follows from the discrete valuation ring (`isUnit_of_θ_ne_zero'`).
-/

universe u

open TensorProduct Module IsLocalRing

namespace SemistableReduction

open AdmissibleLift FormalKummer

namespace TateS6

noncomputable section

/-- `(A/I ⊗_A B)[1/g]` is formally étale over `A/I` if `(B/IB)[1/g]` is. -/
theorem formallyEtale_away_tensor {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) (g : A)
    [Algebra.FormallyEtale (A ⧸ I)
      (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B g)))] :
    Algebra.FormallyEtale (A ⧸ I)
      (Localization.Away (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I g))) := by
  let Φ := Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I
  have hΦ : Φ (Ideal.Quotient.mk _ (algebraMap A B g)) =
      algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I g) := by
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk,
      Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
      Algebra.smul_def, mul_one]
    rfl
  have H : Submonoid.map Φ (Submonoid.powers (Ideal.Quotient.mk _ (algebraMap A B g))) =
      Submonoid.powers (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I g)) := by
    rw [Submonoid.map_powers]
    exact congrArg _ hΦ
  exact Algebra.FormallyEtale.of_equiv (IsLocalization.algEquivOfAlgEquiv
    (M := Submonoid.powers (Ideal.Quotient.mk _ (algebraMap A B g)))
    (Localization.Away (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B g)))
    (Localization.Away (algebraMap (A ⧸ I) ((A ⧸ I) ⊗[A] B) (Ideal.Quotient.mk I g))) Φ H)

end

end TateS6

namespace TateTwoChartNode

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {b₄ b₆ ϖ : O} {m : ℕ} {ε : O}

local notation "𝒩" => NR b₄ b₆ ϖ m ε

/-- **The levels `(B/ϖˡ⁺¹B)[1/f]` of the normalisation are étale over `NR/ϖˡ⁺¹`** (purity at
the closed points of the special fibre off the nodes). -/
theorem etale_Pn_NR [hθ : Fact (Function.Surjective θ)] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L]
    (hreg : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      NodeChart.fR (π := ϖ) (e := m) 𝒩 ∉ P →
      ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (l : ℕ) :
    Algebra.Etale (EtaleTower.Tn ϖ 𝒩 l)
      (EtaleTower.Pn ϖ 𝒩 B (NodeChart.fR (π := ϖ) (e := m) 𝒩) l) := by
  haveI : IsDomain 𝒩 := isDomain_NR b₄ b₆ hϖ.prime (Nat.pos_of_neZero m) hε
  haveI := isIntegrallyClosed_NR hϖ (Nat.pos_of_neZero m) hε h3 hE
  haveI : Module.Finite 𝒩 B := IsIntegralClosure.finite 𝒩 K L B
  haveI : Module.Finite (Rs θ 𝒩) (Cs θ 𝒩 B) :=
    finite_Cs hϖ (Nat.pos_of_neZero m) hε h3 hE θ K L B
  haveI : IsJacobsonRing (Rs θ 𝒩) := isJacobsonRing_Rs
  haveI : IsJacobsonRing (EtaleTower.CB θ 𝒩 B) := isJacobsonRing_of_isIntegral (R := Rs θ 𝒩)
  have hϖJ : algebraMap O 𝒩 ϖ ∈ J θ (R := 𝒩) := Ideal.mem_map_of_mem _ (by
    rw [hker]; exact Ideal.mem_span_singleton_self ϖ)
  refine EtaleTower.etale_Pn_of_isEtaleAt_maximal (θ_ϖ hker) _ hker.le (fun Q _ hJQ hfQ ↦ ?_) l
  haveI : (Q.comap (algebraMap 𝒩 B)).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have hJP : J θ (R := 𝒩) ≤ Q.comap (algebraMap 𝒩 B) := Ideal.map_le_iff_le_comap.1 hJQ
  obtain ⟨x, y, hx, hy, hxy⟩ := hreg _ (hJP hϖJ) hfQ
  exact PurityLocal.isEtaleAt' K (L := L) _ hx hy hxy B (hunr _ (hJP hϖJ)) Q rfl

/-- **`(NR/ϖˡ⁺¹ ⊗ B)[1/f]` is formally étale over `NR/ϖˡ⁺¹`** (the étaleness hypothesis of
`FormalLevel.levelPatchEquiv` for the Tate node chart). -/
theorem formallyEtale_Rn [hθ : Fact (Function.Surjective θ)] [IsDomain O]
    [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ) (hker : RingHom.ker θ = Ideal.span {ϖ})
    [NeZero m] (hε : IsUnit ε) (h3 : (3 : O) ≠ 0)
    (hE : TemperedFundamentalGroups.TateNormal.tateE (ε * ϖ ^ m) b₄ b₆ ≠ 0)
    (K : Type u) [Field K] [Algebra 𝒩 K] [IsFractionRing 𝒩 K]
    (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra 𝒩 L] [IsScalarTower 𝒩 K L]
    (B : Type u) [CommRing B] [Algebra 𝒩 B] [Algebra B L] [IsScalarTower 𝒩 B L]
    [IsIntegralClosure B 𝒩 L]
    (hreg : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      NodeChart.fR (π := ϖ) (e := m) 𝒩 ∉ P →
      ∃ x y : Localization.AtPrime P, Prime x ∧ y ∉ Ideal.span {x} ∧
        maximalIdeal (Localization.AtPrime P) = Ideal.span {x, y})
    (hunr : ∀ (P : Ideal 𝒩) [P.IsMaximal], algebraMap O 𝒩 ϖ ∈ P →
      ∀ (Q : Ideal B) [Q.IsPrime], Q.comap (algebraMap 𝒩 B) < P → Algebra.IsUnramifiedAt 𝒩 Q)
    (l : ℕ) :
    Algebra.FormallyEtale (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l)
      (Localization.Away (algebraMap (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l)
        (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l ⊗[𝒩] B)
        (QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))) := by
  haveI := etale_Pn_NR hϖ hker hε h3 hE K L B hreg hunr l
  exact TateS6.formallyEtale_away_tensor (A := 𝒩) (B := B)
    (QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l) (NodeChart.fR (π := ϖ) (e := m) 𝒩)
/-- The covering `cov₀ = covNR_of_regular …` of the special fibre of the node chart (with the
coordinate `ψb τ` at the marked points). -/
abbrev covS6 [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
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
    (τ : QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) :
    Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ) :=
  covNR_of_regular hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe _

/-- The deformation parameters `ϖ^(m / e j)` of the Kummer factors (`FormalLevel.πK`). -/
abbrev piS6 [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
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
    (p : (covS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).ι) : O :=
  ϖ ^ (m / (covS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e p)

lemma piS6_pow [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
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
    (p : (covS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).ι) :
    piS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ p ^
      (covS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e p = ϖ ^ m := by
  rw [← pow_mul]
  exact congrArg (ϖ ^ ·)
    ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B p.1).hmd p.2)

/-- **The tower of patched algebras of the Tate node chart** (`QuadNodeTower.tower` for
`cov₀ = covNR_of_regular …`, deformation parameters `piS6`). -/
abbrev towerS6 [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
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
    (τ : QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) :=
  QuadNodeTower.tower ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (θ_ϖ hker) hπe τ
    (covS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ)
    (piS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ)
    (piS6_pow hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ) hker.le

instance isScalarTower_Rn (l : ℕ) :
    IsScalarTower O 𝒩 (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l) :=
  inferInstanceAs (IsScalarTower O 𝒩 (𝒩 ⧸ QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))

lemma isUnit_of_θ_ne_zero' [IsDomain O] [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ)
    (hker : RingHom.ker θ = Ideal.span {ϖ}) (x : O) (hx : θ x ≠ 0) : IsUnit x := by
  by_contra h
  have hm : x ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal x).2 h
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, ← hker] at hm
  exact hx hm

lemma uR_mul_vR' : uR b₄ b₆ ϖ m ε * vR b₄ b₆ ϖ m ε = algebraMap O 𝒩 (ϖ ^ m) := by
  rw [uR_mul_vR]; exact (map_pow _ _ _).symm

/-- The node coordinates `NodeChart.χ` of the level `NR/ϖˡ⁺¹` are the chart coordinates
`u, v ↦ uR, vR`. -/
lemma χ_eq_lift [IsNoetherianRing O] (l : ℕ) {π' : O} {e' : ℕ} (h : π' ^ e' = ϖ ^ m)
    (hxy : uR b₄ b₆ ϖ m ε * vR b₄ b₆ ϖ m ε = algebraMap O 𝒩 (π' ^ e')) (a : KummerEtale.A π' e') :
    NodeChart.χ (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l) h a = algebraMap 𝒩
      (FormalPatchLevel.Hat (QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))
      (Node.lift (uR b₄ b₆ ϖ m ε) (vR b₄ b₆ ϖ m ε) hxy a) := by
  have hext := Node.algHom_ext (f := NodeChart.χ (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ
      m) l) h)
    (g := (IsScalarTower.toAlgHom O 𝒩 (FormalPatchLevel.Hat
      (QuadNodeTower.fn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l))).comp
      (Node.lift (uR b₄ b₆ ϖ m ε) (vR b₄ b₆ ϖ m ε) hxy)) ?_ ?_
  · exact DFunLike.congr_fun hext a
  · rw [NodeChart.χ_apply, Node.congrEq_u, AlgHom.comp_apply, Node.lift_u]
    rfl
  · rw [NodeChart.χ_apply, Node.congrEq_v, AlgHom.comp_apply, Node.lift_v]
    rfl

set_option maxHeartbeats 1000000 in
-- unfolding the level datum of the tower
/-- **The node coordinates of the level data of `towerS6` are the chart coordinates** (the
hypothesis `hχL` of `FormalLevel.levelPatchEquiv`). -/
lemma hχL_S6 [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
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
    (l : ℕ) (p : Σ j, Fin ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B)
        j).r)
    (a : KummerEtale.A (ϖ ^ ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr)
        B) p.1).m p.2) (((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B)
        p.1).d p.2)) :
    ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).level l).L.χ p a =
        algebraMap 𝒩 (FormalPatchLevel.Hat ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B
        hreg hunr hπe τ).f l))
      (FormalLevel.chart uR_mul_vR' ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B
          hunr) B) p.1) p.2 a) :=
  χ_eq_lift l (piS6_pow hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ p) _ a

set_option maxHeartbeats 1000000 in
-- the level datum of the tower is compared with the generic one (unfolding `covNR_of_regular`)
/-- **MR12 S6 G3 for the Tate node chart: the level-`l` patch of the M2 lift is
`NR/ϖˡ⁺¹ ⊗_{NR} B`.** For the normalisation `B` of the Tate node chart `NR` in a tame Galois
cover `L` (hypotheses of `covNR_of_regular`), the level-`l` patched algebra of the tower
`towerS6` of `cov₀ = covNR_of_regular …` is `(NR/ϖˡ⁺¹) ⊗_{NR} B`
(`FormalLevel.levelPatchEquiv`). -/
def levelPatchEquiv_NR [hθ : Fact (Function.Surjective θ)] [IsSepClosed k]
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
    (l : ℕ) :
    QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l ⊗[𝒩] B ≃ₐ[QuadNodeTower.Rn ϖ ϖ m
      (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l]
      (towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).G hθ.out l := by
  haveI : ∀ j, (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) (Nat.pos_of_neZero m) j).IsMaximal :=
    isMaximal_nodeIdeal hθ.out (θ_ϖ hker) (Nat.pos_of_neZero m)
  haveI : Algebra.FormallyEtale (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l)
      (Localization.Away (algebraMap (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l)
        (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l ⊗[𝒩] B) ((towerS6 hϖ hker hε h3 hE
            hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).f l))) :=
    formallyEtale_Rn hϖ hker hε h3 hE K L B hreg hunr l
  have hm1 : 1 ≤ m := Nat.pos_of_neZero m
  have hxy : uR b₄ b₆ ϖ m ε * vR b₄ b₆ ϖ m ε = algebraMap O 𝒩 (ϖ ^ m) := by
    rw [uR_mul_vR]; exact (map_pow _ _ _).symm
  have hJnil : J θ (R := QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l) ≤
      nilradical _ := fun x hx ↦ ⟨l + 1, by
    have h := Ideal.pow_mem_pow hx (l + 1)
    rw [QuadNodeTower.hJ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hker.le l] at h
    exact (Ideal.mem_bot).1 h⟩
  haveI hmax : ∀ j, ((sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) hm1 j)).comap
      (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e
          l))).IsMaximal := fun j ↦
    CompletionProd.isMaximal_comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B
        hreg hunr hπe τ).e l)) (surjective_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L
        hL B hreg hunr hπe τ).e l))
      (fun j ↦ sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) hm1 j)) j
  have h𝔪 : ∀ j, nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) hm1 j ≤
      ((sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) hm1 j)).comap
        (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e
            l))).comap (algebraMap 𝒩 _) := fun j a ha ↦ by
    have h1 : ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e l).symm
        (Ideal.Quotient.mk _ (algebraMap 𝒩
        (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) l) a)) = Ideal.Quotient.mk _ a :=
      (AlgEquiv.symm_apply_eq _).2
        (QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (θ_ϖ hker) l a).symm
    change ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e l).symm
        (Ideal.Quotient.mk _ (algebraMap 𝒩 _ a)) ∈
      sIdeal (θ := θ) (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) hm1 j)
    rw [h1]
    exact Ideal.mem_map_of_mem _ ha
  refine FormalLevel.levelPatchEquiv hxy (θ_ϖ hker) hm1
    (nodeIdeal b₄ b₆ ϖ m ε (θ_ϖ hker) hm1) (J_le_nodeIdeal (θ_ϖ hker) hm1)
    (surjective_mk_comp_algebraMap hθ.out (θ_ϖ hker) hm1) (kummerDataNR hϖ hker hε hqM hq hM' K hζ
        L hL (hunrLoc hker B hunr) B)
    (sIdeal_injective (θ_ϖ hker) hm1) (fbar_mem_sIdeal (θ_ϖ hker) hm1)
    (iInf_sIdeal_le_radical (θ_ϖ hker) hm1)
    (NodeChart.φ 𝒩 hπe) (NodeChart.φ_u hπe) (NodeChart.φ_v hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)
    (finite_Cs hϖ hm1 hε h3 hE θ K L B)
    (etale_Cs_of_regular hϖ hker hm1 hε h3 hE K L hreg B hunr)
    (fun j i h0 ↦ by
      obtain ⟨c, hc⟩ := ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B hunr) B)
          j).hdM i
      exact hM'k (by rw [hc, Nat.cast_mul, h0, zero_mul]))
    (QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) (towerS6 hϖ hker hε h3 hE hqM hq hM'
        hM'k K hζ L hL B hreg hunr hπe τ).hfe
    (fun l a ↦ QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) (θ_ϖ hker) l a) ((towerS6 hϖ
        hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).level l)
    (CompletionProd.injective_comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B
        hreg hunr hπe τ).e l)) (surjective_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L
        hL B hreg hunr hπe τ).e l)) _
      (sIdeal_injective (θ_ϖ hker) hm1))
    (CompletionProd.mem_comap (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg
        hunr hπe τ).e l)) (red_f θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg
        hunr hπe τ).e l) ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe
        τ).hfe l)) _
      (fbar_mem_sIdeal (θ_ϖ hker) hm1))
    (CompletionProd.iInf_comap_le_radical (red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L
        hL B hreg hunr hπe τ).e l)) (surjective_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K
        hζ L hL B hreg hunr hπe τ).e l))
      (red_f θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e l)
          ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).hfe l)) _
          ((ker_red θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).e
          l)).le.trans hJnil)
      (iInf_sIdeal_le_radical (θ_ϖ hker) hm1))
    (fun j ↦ FormalLevel.resMap ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL (hunrLoc hker B
        hunr) B) j).comap_eq
      (FormalKummer.hsurj0_of _ (J_le_nodeIdeal (θ_ϖ hker) hm1 j)
        (surjective_mk_comp_algebraMap hθ.out (θ_ϖ hker) hm1 j) ((kummerDataNR hϖ hker hε hqM hq
            hM' K hζ L hL (hunrLoc hker B hunr) B) j)) (h𝔪 j))
    ?hχL ?hεL (fun _ ↦ Ideal.map_comap_le)
    (fun j _ hz ↦ FormalLevel.resMap_eq_zero ((kummerDataNR hϖ hker hε hqM hq hM' K hζ L hL
        (hunrLoc hker B hunr) B) j).comap_eq _ _ hz)
    (isUnit_of_θ_ne_zero' hϖ hker)
  case hεL =>
    intro p
    refine eq_of_isNilpotent_sub_of_isIdempotentElem
      (CompletionProd.isIdempotentElem_idem _ _ _ _) (((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K
          hζ L hL B hreg hunr hπe τ).level l).hidem p)
      (isNilpotent_of_mem_ker_ψ θ (QuadNodeTower.hJ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hker.le l) ?_)
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    exact (ψ_idem_comap θ ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe
        τ).e l) ((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).hfe l)
        (sIdeal_injective (θ_ϖ hker) hm1)
      (fbar_mem_sIdeal (θ_ϖ hker) hm1) (iInf_sIdeal_le_radical (θ_ϖ hker) hm1) hJnil p.1).trans
      (((towerS6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ).level l).L.hε p).symm
  case hχL =>
    exact fun p a ↦ hχL_S6 hϖ hker hε h3 hE hqM hq hM' hM'k K hζ L hL B hreg hunr hπe τ l p a

end

end TateTwoChartNode

end SemistableReduction
