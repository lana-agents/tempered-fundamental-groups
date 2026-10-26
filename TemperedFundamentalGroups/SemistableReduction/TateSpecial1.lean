/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NormAway
import TemperedFundamentalGroups.SemistableReduction.TateT1Regular
import TemperedFundamentalGroups.SemistableReduction.TateT1Normal
import TemperedFundamentalGroups.SemistableReduction.TateNodeCovering
import TemperedFundamentalGroups.SemistableReduction.TateGlue1

/-!
# The special-fibre covering over `V₁` from a tame cover (MR12 S5.6, `TateGlue1.Special1`)

Let `O` be a discrete valuation ring (uniformizer `ϖ`, residue field `k` separably closed,
`ker θ = (ϖ)`), `π = ε ϖᵐ` (`ε` a unit, `m = q M' ≥ 1`, `M'` invertible in `k`), `T1` the
chart `u ≠ 0` of the Tate model with fraction field `K`, `L / K` finite Galois of degree prime to
`q`
with `μ_{M'} ⊆ K`, and `B₁` the normalisation of `T1` in `L`. Assume (`hunr`, debt D3/A1) that
`B₁` is unramified over `T1` at every prime lying over a prime strictly inside a maximal ideal
containing `ϖ`. Then:

* **`TateGlue1.covTate`**: the admissible covering `cov₀` of the node chart `NR = T1[1/D]`
  (`TateTwoChartNode.covNR` for the normalisation `B₁[1/D]` of `NR`, `NormAway`);
* **`TateGlue1.special1 : Special1 hκ rfl hπe τ (covTate ..)`**: `C1 = B₁/JB₁`, finite over
  `T1/J`, étale over `D(w̄)` (purity at the regular closed points of the special fibre with
  `w ∉ P`, `TateTwoChart.exists_regular_pair_T1`, `T1` normal: `isIntegrallyClosed_T1`), with
  `ι₀ : B₁/JB₁ → B₁[1/D]/J`, a localization away from `D̄`
  (`NormAway.isLocalization_quotMap`).
-/

universe u

open Module IsLocalRing

namespace SemistableReduction

open TateTwoChart TateTwoChartNode
open AdmissibleLift (J)
open FormalKummer (Cs)

namespace TateGlue1

noncomputable section

/-- The special fibre of a finite type `O`-algebra is a Jacobson ring. -/
lemma isJacobsonRing_quot {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
    [Fact (Function.Surjective θ)] [IsNoetherianRing O] (S : Type u) [CommRing S] [Algebra O S]
    [Algebra.FiniteType O S] : IsJacobsonRing (S ⧸ J θ (R := S)) := by
  haveI : Algebra.FiniteType O (S ⧸ J θ (R := S)) :=
    Algebra.FiniteType.trans (S := S) inferInstance inferInstance
  letI : Algebra O k := θ.toAlgebra
  letI : Algebra k (S ⧸ J θ (R := S)) := QuadNodeTower.algK S
  haveI : @IsScalarTower O k (S ⧸ J θ (R := S)) _ Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq fun o ↦ (QuadNodeTower.algK_θ (θ := θ) S o).symm
  haveI : Algebra.FiniteType k (S ⧸ J θ (R := S)) :=
    Algebra.FiniteType.of_restrictScalars_finiteType O k _
  exact isJacobsonRing_of_finiteType (A := k)

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {ϖ b₄ b₆ t κ ε εi : O} {m : ℕ}

local notation "𝒯" => T1 (ε * ϖ ^ m) b₄ t κ

local notation "𝒩" => NR b₄ b₆ ϖ m ε

variable [IsDomain O] [IsDiscreteValuationRing O] [IsSepClosed k]
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

include hκ in
/-- The `T1`-algebra structure on the node chart (`toNode`). -/
abbrev algTN : Algebra 𝒯 𝒩 :=
  algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl

omit [NeZero m] in
include hϖ hκ hε h3 hE in
/-- `T1` is a domain. -/
lemma isDomain_T1' : IsDomain 𝒯 := by
  have hεu : IsUnit ε := .of_mul_eq_one_right εi hε
  exact isDomain_T1 hϖ hκ h3 (mul_ne_zero hεu.ne_zero (pow_ne_zero _ hϖ.ne_zero)) hE

omit [IsSepClosed k] in
include hϖ hker hκ hε h3 hE in
/-- `T1` is integrally closed. -/
lemma isIntegrallyClosed_T1' : IsIntegrallyClosed 𝒯 := by
  haveI := isDomain_T1' hϖ hκ hε h3 hE
  have hθs : Function.Surjective θ := hθ.out
  exact isIntegrallyClosed_T1 hϖ (Nat.pos_of_neZero m) hε h3 hE hκ fun P _ hϖP hw ↦
    (exists_regular_pair_T1 hϖ hθs hker rfl (Nat.pos_of_neZero m) hκ P hϖP hw).choose_spec.1

include hϖ hκ hε h3 hE hK in
/-- `K` is also the fraction field of the node chart. -/
lemma isFractionRing_NR : IsFractionRing 𝒩 K := by
  haveI := isDomain_T1' hϖ hκ hε h3 hE
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  haveI := isLocalization_NR (b₄ := b₄) (b₆ := b₆) (ε := ε)
      (ϖ := ϖ) (m := m) (t := t) (κ := κ) hκ rfl hε
  haveI : IsScalarTower 𝒯 𝒩 K := IsScalarTower.of_algebraMap_eq fun x ↦ (hK x).symm
  have hD : DT (ε * ϖ ^ m) b₄ t κ ∈ nonZeroDivisors 𝒯 := by
    refine mem_nonZeroDivisors_of_ne_zero fun h0 ↦ ?_
    have h1 := IsLocalization.Away.algebraMap_isUnit (S := 𝒩) (DT (ε * ϖ ^ m) b₄ t κ)
    rw [h0, map_zero] at h1
    haveI := isDomain_NR b₄ b₆ hϖ.prime (Nat.pos_of_neZero m) (.of_mul_eq_one_right εi hε)
    exact not_isUnit_zero h1
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (DT (ε * ϖ ^ m) b₄ t κ)) 𝒩 K

include hϖ hκ hε in
lemma DT_ne_zero : DT (ε * ϖ ^ m) b₄ t κ ≠ 0 := by
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  haveI := isLocalization_NR (b₄ := b₄) (b₆ := b₆) (ε := ε)
      (ϖ := ϖ) (m := m) (t := t) (κ := κ) hκ rfl hε
  haveI := isDomain_NR b₄ b₆ hϖ.prime (Nat.pos_of_neZero m) (.of_mul_eq_one_right εi hε)
  intro h0
  have h1 := IsLocalization.Away.algebraMap_isUnit (S := 𝒩) (DT (ε * ϖ ^ m) b₄ t κ)
  rw [h0, map_zero] at h1
  exact not_isUnit_zero h1

omit [FiniteDimensional K L] [IsGalois K L] [Algebra 𝒩 B] [IsScalarTower 𝒩 B L] in
include hϖ hκ hε hK B₁ in
/-- `B = B₁[1/D]` is the normalisation of the node chart in `L`. -/
lemma isIntegralClosure_B : IsIntegralClosure B 𝒩 L := by
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  haveI := isLocalization_NR (b₄ := b₄) (b₆ := b₆) (ε := ε)
      (ϖ := ϖ) (m := m) (t := t) (κ := κ) hκ rfl hε
  haveI : IsScalarTower 𝒯 𝒩 L := IsScalarTower.of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply 𝒯 K L, ← hK x, ← IsScalarTower.algebraMap_apply]
    rfl
  refine NormAway.isIntegralClosure (B₁ := B₁) (DT (ε * ϖ ^ m) b₄ t κ) ?_
  rw [IsScalarTower.algebraMap_apply 𝒯 K L]
  exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective 𝒯 K)).2
    (DT_ne_zero hϖ hκ hε))

omit [IsDomain O] [IsDiscreteValuationRing O] [NeZero m] in
include hκ hε hB hunr in
/-- The hypothesis `hunr` of `covNR` for `B`, from that for `B₁`. -/
lemma hunr_B (P : Ideal 𝒩) [P.IsMaximal] (hP : algebraMap O 𝒩 ϖ ∈ P) (Q : Ideal B)
    [Q.IsPrime]
    (hQ : Q.comap (algebraMap 𝒩 B) < P) : Algebra.IsUnramifiedAt 𝒩 Q := by
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  haveI := isLocalization_NR (b₄ := b₄) (b₆ := b₆) (ε := ε)
      (ϖ := ϖ) (m := m) (t := t) (κ := κ) hκ rfl hε
  haveI := isScalarTower_NR (b₄ := b₄) (b₆ := b₆) (ε := ε)
      (ϖ := ϖ) (m := m) (t := t) (κ := κ) hκ rfl
  letI : Algebra 𝒯 B := ((algebraMap B₁ B).comp (algebraMap 𝒯 B₁)).toAlgebra
  haveI : IsScalarTower 𝒯 𝒩 B := IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower 𝒯 B₁ B := IsScalarTower.of_algebraMap_eq' rfl
  exact NormAway.hunr (B₁ := B₁) (DT (ε * ϖ ^ m) b₄ t κ) (algebraMap O 𝒯 ϖ) hunr P
    (by rwa [← IsScalarTower.algebraMap_apply]) Q hQ

/-- **The admissible covering `cov₀` of the node chart** defined by the special fibre of the
normalisation `B = B₁[1/D]` (`covNR`). -/
def covTate : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ) :=
  haveI := isFractionRing_NR hϖ hκ hε h3 hE K hK
  haveI := isIntegralClosure_B hϖ hκ hε K hK L B₁ B
  covNR hϖ hker (.of_mul_eq_one_right εi hε) h3 hE hqM hq hM' hM'k K hζ L hL B
    (hunr_B hκ hε B₁ B hB hunr) hπe _

lemma covTate_C :
    (covTate hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe τ).C =
      Cs θ 𝒩 B := rfl

/-- The `T1`-algebra structure on `B` (through `B₁`). -/
abbrev algTB : Algebra 𝒯 B := ((algebraMap B₁ B).comp (algebraMap 𝒯 B₁)).toAlgebra

omit [IsDomain O] [IsDiscreteValuationRing O] [IsSepClosed k] hθ [NeZero m] in
lemma J_NR_eq : letI := algTN (b₄ := b₄) (ε := ε) (ϖ := ϖ) (m := m) hκ
    J θ (R := 𝒩) = (J θ (R := 𝒯)).map (algebraMap 𝒯 𝒩) := by
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  haveI := isScalarTower_NR (b₄ := b₄) (b₆ := b₆) (ε := ε)
      (ϖ := ϖ) (m := m) (t := t) (κ := κ) hκ rfl
  change (RingHom.ker θ).map _ = ((RingHom.ker θ).map _).map _
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]

/-- **The special-fibre covering over `V₁`** (`TateGlue1.Special1`) of a tame cover:
`C1 = B₁/JB₁`
with its restriction `covTate` to the node chart. -/
def special1 : Special1 hκ rfl hπe τ
    (covTate hϖ hker hκ hε h3 hE hqM hq hM' hM'k K hK hζ L hL B₁ B hB hunr hπe τ) :=
  haveI := isDomain_T1' hϖ hκ hε h3 hE
  haveI := isIntegrallyClosed_T1' hϖ hker hκ hε h3 hE
  letI := algT1NR (b₆ := b₆) (ε := ε) (ϖ := ϖ) (m := m) (t := t) (κ := κ) b₄ hκ rfl
  letI := algTB B₁ B (ε := ε) (ϖ := ϖ) (m := m) (b₄ := b₄) (t := t) (κ := κ)
  haveI : IsScalarTower 𝒯 𝒩 B := IsScalarTower.of_algebraMap_eq fun x ↦ (hB x).symm
  haveI : IsScalarTower 𝒯 B₁ B := IsScalarTower.of_algebraMap_eq' rfl
  { C1 := Cs θ 𝒯 B₁
    finite := by
      haveI : Module.Finite 𝒯 B₁ := IsIntegralClosure.finite 𝒯 K L B₁
      haveI : Module.Finite 𝒯 (Cs θ 𝒯 B₁) :=
        Module.Finite.of_surjective (Ideal.Quotient.mkₐ 𝒯 _).toLinearMap
          Ideal.Quotient.mk_surjective
      exact Module.Finite.of_restrictScalars_finite 𝒯 (T1s θ (ε * ϖ ^ m) b₄ t κ)
        (Cs θ 𝒯 B₁)
    etale := by
      haveI : Algebra.FiniteType O 𝒯 :=
        Algebra.FiniteType.trans (S := Polynomial O) inferInstance inferInstance
      haveI : IsJacobsonRing (𝒯 ⧸ J θ (R := 𝒯)) := isJacobsonRing_quot 𝒯
      have hϖJ : algebraMap O 𝒯 ϖ ∈ J θ (R := 𝒯) := Ideal.mem_map_of_mem _ (by
        rw [hker]; exact Ideal.mem_span_singleton_self ϖ)
      exact PurityLocal.etale_quot_awayMap K (L := L) (J θ (R := 𝒯)) B₁ _
        (fun P _ hJP hw ↦ by
          obtain ⟨y, h1, h2, h3⟩ := exists_regular_pair_T1 hϖ hθ.out hker rfl
            (Nat.pos_of_neZero m) hκ P (hJP hϖJ) hw
          exact ⟨_, y, h1, h2, h3⟩)
        (fun P _ hJP _ ↦ hunr P (hJP hϖJ))
    ι₀ := NormAway.quotMap (B₁ := B₁) (B := B) (J θ (R := 𝒯)) (J θ (R := 𝒩))
      (J_NR_eq hκ)
    hι₀ := fun x ↦ NormAway.quotMap_algebraMap (B₁ := B₁) (B := B) (J θ (R := 𝒯))
      (J θ (R := 𝒩)) (J_NR_eq hκ) x
    hι := NormAway.isLocalization_quotMap (B₁ := B₁) (B := B) (J θ (R := 𝒯))
      (J θ (R := 𝒩))
      (J_NR_eq hκ) (DT (ε * ϖ ^ m) b₄ t κ) }

end

end TateGlue1

end SemistableReduction
