/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateTwoChartNode
import TemperedFundamentalGroups.SemistableReduction.QuadNodeTower

/-!
# The levels of the Tate charts over `ℙ¹` (Blueprint §12.8, M2.3 (f))

For the two charts `T0`, `T1` of the Tate model over `ℙ¹_O` (`TateTwoChart`) and `ϖ ∈ O`:

* `TateLevel.T1n n = T1/ϖⁿ⁺¹T1`, `TateLevel.T0n n = T0/ϖⁿ⁺¹T0`, the charts of the level `𝒯_n`;
* **`TateLevel.isLocalization_Rn`**: the level-`n` node chart `QuadNodeTower.Rn n` (the chart on
  which the tower of patched algebras `QuadNodeTower.G n` lives) is the localization of `T1n n`
  away from `D = 1 + b₄ w²`, via `toRn` (`TateTwoChartNode.toNode` modulo `ϖⁿ⁺¹`). So the patched
  algebras are algebras over the level charts `T1n n` and live on `D(D) ⊆ toP1⁻¹ U₁`.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateLevel

open TateTwoChart TateTwoChartNode KummerEtale

noncomputable section

variable {O : Type u} [CommRing O] (ϖ : O) (π b₄ t κ : O)

/-- The ideal `ϖⁿ⁺¹` of `O`. -/
abbrev Iv (n : ℕ) : Ideal O := QuadNodeTower.Iv ϖ n

/-- **The level-`n` chart over `U₁`**: `T1/ϖⁿ⁺¹`. -/
abbrev T1n (n : ℕ) : Type u :=
  T1 π b₄ t κ ⧸ (Iv ϖ n).map (algebraMap O (T1 π b₄ t κ))

/-- **The level-`n` chart over `U₀`**: `T0/ϖⁿ⁺¹`. -/
abbrev T0n (n : ℕ) : Type u :=
  T0 π b₄ t κ ⧸ (Iv ϖ n).map (algebraMap O (T0 π b₄ t κ))

/-! ### Quotients of localizations -/

section QuotLoc

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]

/-- The map `R/IR → S/IS` induced by an `O`-algebra map. -/
def quotMap (φ : R →ₐ[O] S) (I : Ideal O) :
    R ⧸ I.map (algebraMap O R) →+* S ⧸ I.map (algebraMap O S) :=
  Ideal.quotientMap _ (φ : R →+* S) (by
    rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap, AlgHom.comp_algebraMap]
    exact Ideal.le_comap_map)

lemma quotMap_mk (φ : R →ₐ[O] S) (I : Ideal O) (x : R) :
    quotMap φ I (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ (φ x) :=
  Ideal.quotientMap_mk

/-- **A localization stays a localization modulo an ideal of the base**: if `S = R[1/r]`, then
`S/IS = (R/IR)[1/r̄]`. -/
theorem isLocalization_quotMap [Algebra R S] [IsScalarTower O R S] (r : R)
    [IsLocalization.Away r S] (I : Ideal O) :
    letI := (quotMap (IsScalarTower.toAlgHom O R S) I).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (I.map (algebraMap O R)) r)
      (S ⧸ I.map (algebraMap O S)) := by
  letI := (quotMap (IsScalarTower.toAlgHom O R S) I).toAlgebra
  have h := IsLocalization.of_surjective (M := Submonoid.powers r) (S := S)
    (R' := R ⧸ I.map (algebraMap O R)) (S' := S ⧸ I.map (algebraMap O S))
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk _)
    Ideal.Quotient.mk_surjective
    (RingHom.ext fun x ↦ (quotMap_mk (IsScalarTower.toAlgHom O R S) I x).symm) (by
      rw [Ideal.mk_ker, Ideal.mk_ker, Ideal.map_map, ← IsScalarTower.algebraMap_eq])
  rwa [Submonoid.map_powers] at h

end QuotLoc

/-! ### The overlap at level `n` -/

/-- `T01 = T1[1/h']` is the localization of `T0` away from `h` (via `ρ₀`). -/
theorem isLocalization_rho0 :
    letI := (rho0 π b₄ t κ : T0 π b₄ t κ →+* T01 π b₄ t κ).toAlgebra
    IsLocalization.Away (h0 π b₄ t κ) (T01 π b₄ t κ) := by
  letI := (rho0 π b₄ t κ : T0 π b₄ t κ →+* T01 π b₄ t κ).toAlgebra
  have hm : ∀ a, algebraMap (T0 π b₄ t κ) (T01 π b₄ t κ) a = rho0 π b₄ t κ a := fun _ ↦ rfl
  refine (isLocalization_iff ..).mpr ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [hm, map_pow, rho0_h0]
    exact (IsUnit.of_mul_eq_one_right _ (h1_mul_hinv π b₄ t κ)).pow k
  · intro z
    obtain ⟨a, k, h⟩ := (twoChart π b₄ t κ).exists0 z
    refine ⟨⟨a, ⟨_, k, rfl⟩⟩, ?_⟩
    change z * rho0 π b₄ t κ (h0 π b₄ t κ ^ k) = rho0 π b₄ t κ a
    rw [map_pow, rho0_h0, mul_comm]
    exact h
  · intro a b hab
    obtain ⟨k, hk⟩ := (twoChart π b₄ t κ).ker0 (a - b) (by
      change rho0 π b₄ t κ (a - b) = 0
      rw [map_sub, ← hm, ← hm, hab, sub_self])
    refine ⟨⟨_, k, rfl⟩, ?_⟩
    change h0 π b₄ t κ ^ k * (a - b) = 0 at hk
    change h0 π b₄ t κ ^ k * a = h0 π b₄ t κ ^ k * b
    rwa [mul_sub, sub_eq_zero] at hk

/-- The overlap at level `n`: `T01/ϖⁿ⁺¹`. -/
abbrev T01n (n : ℕ) : Type u :=
  T01 π b₄ t κ ⧸ (Iv ϖ n).map (algebraMap O (T01 π b₄ t κ))

/-- `ρ₀` at level `n`. -/
abbrev rho0n (n : ℕ) : T0n ϖ π b₄ t κ n →+* T01n ϖ π b₄ t κ n :=
  quotMap (rho0 π b₄ t κ) (Iv ϖ n)

/-- `ρ₁` at level `n`. -/
abbrev rho1n (n : ℕ) : T1n ϖ π b₄ t κ n →+* T01n ϖ π b₄ t κ n :=
  quotMap (IsScalarTower.toAlgHom O (T1 π b₄ t κ) (T01 π b₄ t κ)) (Iv ϖ n)

/-- **The overlap at level `n` is `T0n[1/h]`.** -/
theorem isLocalization_rho0n (n : ℕ) :
    letI := (rho0n ϖ π b₄ t κ n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk _ (h0 π b₄ t κ) : T0n ϖ π b₄ t κ n)
      (T01n ϖ π b₄ t κ n) := by
  letI := (rho0 π b₄ t κ : T0 π b₄ t κ →+* T01 π b₄ t κ).toAlgebra
  haveI : IsScalarTower O (T0 π b₄ t κ) (T01 π b₄ t κ) :=
    IsScalarTower.of_algebraMap_eq fun o ↦ ((rho0 π b₄ t κ).commutes o).symm
  haveI := isLocalization_rho0 π b₄ t κ
  exact isLocalization_quotMap (h0 π b₄ t κ) (Iv ϖ n)

/-- **The overlap at level `n` is `T1n[1/h']`.** -/
theorem isLocalization_rho1n (n : ℕ) :
    letI := (rho1n ϖ π b₄ t κ n).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk _ (h1 π b₄ t κ) : T1n ϖ π b₄ t κ n)
      (T01n ϖ π b₄ t κ n) :=
  isLocalization_quotMap (h1 π b₄ t κ) (Iv ϖ n)

variable {ϖ π b₄ t κ} {b₆ ε εi : O} {m : ℕ}

/-- The level-`n` node chart of the Tate tower. -/
abbrev Rn (b₄ b₆ ϖ : O) (m : ℕ) (ε : O) (n : ℕ) : Type u :=
  QuadNodeTower.Rn ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n

lemma map_le_comap_toNode (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (n : ℕ) :
    (Iv ϖ n).map (algebraMap O (T1 π b₄ t κ)) ≤
      ((QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n).comap
        (toNode b₄ hκ hπ : T1 π b₄ t κ →+* NR b₄ b₆ ϖ m ε)) := by
  rw [Ideal.map_le_iff_le_comap, Ideal.comap_comap]
  intro x hx
  rw [Ideal.mem_comap]
  change toNode b₄ hκ hπ (algebraMap O _ x) ∈ _
  rw [AlgHom.commutes]
  exact Ideal.mem_map_of_mem _ hx

/-- `T1n n → Rn n` (`toNode` modulo `ϖⁿ⁺¹`). -/
def toRn (b₄ : O) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (n : ℕ) :
    T1n ϖ π b₄ t κ n →+* Rn b₄ b₆ ϖ m ε n :=
  Ideal.Quotient.lift _ ((QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n).comp
    (toNode b₄ hκ hπ : T1 π b₄ t κ →+* NR b₄ b₆ ϖ m ε)) fun _ ha ↦
      Ideal.Quotient.eq_zero_iff_mem.mpr (map_le_comap_toNode hκ hπ n ha)

/-- The algebra structure of the node chart over the level chart (via `toRn`). -/
@[reducible] def algRn (b₄ : O) (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (n : ℕ) :
    Algebra (T1n ϖ π b₄ t κ n) (Rn b₄ b₆ ϖ m ε n) :=
  (toRn b₄ hκ hπ n).toAlgebra

lemma toRn_mk (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (n : ℕ) (x : T1 π b₄ t κ) :
    toRn b₄ hκ hπ n (Ideal.Quotient.mk _ x) =
      QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n (toNode b₄ hκ hπ x) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The kernel of `T1[1/D] → Rn n` is `ϖⁿ⁺¹ T1[1/D]`. -/
lemma ker_le (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1) (n : ℕ) :
    RingHom.ker ((QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n).comp
      (chartEquiv b₄ hκ hπ hε : T1D π b₄ t κ →+* NR b₄ b₆ ϖ m ε)) ≤
      (RingHom.ker (Ideal.Quotient.mk ((Iv ϖ n).map (algebraMap O (T1 π b₄ t κ))))).map
        (algebraMap (T1 π b₄ t κ) (T1D π b₄ t κ)) := by
  intro x hx
  replace hx : chartEquiv b₄ hκ hπ hε x ∈ QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n :=
    Ideal.Quotient.eq_zero_iff_mem.mp hx
  rw [Ideal.mk_ker, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  have key : (Iv ϖ n).map (algebraMap O (T1D π b₄ t κ)) =
      (QuadNodeTower.IRb ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n).map
        (chartEquiv b₄ hκ hπ hε).symm.toAlgHom.toRingHom := by
    rw [Ideal.map_map]
    congr 1
    exact RingHom.ext fun o ↦ ((chartEquiv b₄ hκ hπ hε).symm.commutes o).symm
  rw [key]
  have h := Ideal.mem_map_of_mem (chartEquiv b₄ hκ hπ hε).symm.toAlgHom.toRingHom hx
  have hx' : x = (chartEquiv b₄ hκ hπ hε).symm.toAlgHom.toRingHom (chartEquiv b₄ hκ hπ hε x) :=
    ((chartEquiv b₄ hκ hπ hε).symm_apply_apply x).symm
  rw [hx']
  exact h

lemma mk_chartEquiv_algebraMap (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
    (hε : εi * ε = 1) (n : ℕ) (x : T1 π b₄ t κ) :
    QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n
      (chartEquiv b₄ hκ hπ hε (algebraMap _ _ x)) = toRn b₄ hκ hπ n (Ideal.Quotient.mk _ x) := by
  rw [chartEquiv_algebraMap, toRn_mk]

lemma comp_chartEquiv_algebraMap (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m)
    (hε : εi * ε = 1) (n : ℕ) :
    ((QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n).comp
      (chartEquiv b₄ hκ hπ hε : T1D π b₄ t κ →+* NR b₄ b₆ ϖ m ε)).comp
        (algebraMap (T1 π b₄ t κ) (T1D π b₄ t κ)) =
      (toRn b₄ hκ hπ n).comp (Ideal.Quotient.mk _) :=
  RingHom.ext fun x ↦ by
    simp only [RingHom.comp_apply, RingHom.coe_coe]
    exact mk_chartEquiv_algebraMap hκ hπ hε n x

lemma surjective_comp (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    (n : ℕ) : Function.Surjective ((QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n).comp
      (chartEquiv b₄ hκ hπ hε : T1D π b₄ t κ →+* NR b₄ b₆ ϖ m ε)) := fun y ↦ by
  obtain ⟨z, rfl⟩ := QuadNodeTower.mk_surjective ϖ ϖ m _ _ n y
  refine ⟨(chartEquiv b₄ hκ hπ hε).symm z, ?_⟩
  simp only [RingHom.comp_apply, RingHom.coe_coe, AlgEquiv.apply_symm_apply]

/-- **The level-`n` node chart is `T1n n` localized away from `D`.** -/
theorem isLocalization_Rn (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)
    (n : ℕ) :
    letI := algRn b₄ hκ hπ n
    IsLocalization.Away (Ideal.Quotient.mk _ (DT π b₄ t κ) : T1n ϖ π b₄ t κ n)
      (Rn b₄ b₆ ϖ m ε n) := by
  letI := algRn b₄ hκ hπ n
  have h := IsLocalization.of_surjective (M := Submonoid.powers (DT π b₄ t κ))
    (S := T1D π b₄ t κ) (R' := T1n ϖ π b₄ t κ n) (S' := Rn b₄ b₆ ϖ m ε n)
    (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    ((QuadNodeTower.mk ϖ ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) n).comp
      (chartEquiv b₄ hκ hπ hε : T1D π b₄ t κ →+* NR b₄ b₆ ϖ m ε))
    (surjective_comp hκ hπ hε n)
    (by rw [RingHom.algebraMap_toAlgebra]; exact comp_chartEquiv_algebraMap hκ hπ hε n)
    (ker_le hκ hπ hε n)
  rwa [Submonoid.map_powers] at h

end

end TateLevel

end SemistableReduction
