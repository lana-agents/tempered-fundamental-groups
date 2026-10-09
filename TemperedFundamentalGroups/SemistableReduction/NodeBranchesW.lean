/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.WModelCentre
import TemperedFundamentalGroups.SemistableReduction.CrossingZero
import TemperedFundamentalGroups.SemistableReduction.XLengthChain
import TemperedFundamentalGroups.SemistableReduction.ResidueZero

/-!
# Nodes of W-models with their branches (Blueprint §9.7, XL1 (c)/(d))

`exists_nodeBranches`: at a node `z` of a split W-model without loops, the germs form a node core
`a b = ϖ ^ m` whose branch valuations are the centre valuations `Wc` of the two components
through `z` (`NodeBranches`): the monomial points at the ends (`u` resp. `v` has a zero at `z`
on its branch, so transcendental residue, `isResidueTranscendental_of_lt_one`), and the only ones
(same contraction by `NodeCore.valuation_lt_one_of_branch`, same centre, and the centre determines
the valuation at generic points of components, `centreDetermines_gp`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode _root_.SemistableReduction

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
  (hW : IsWModel O L x c j) {ϖ : O} (hϖ : Irreducible ϖ) (hsplit : HasSplitNodes ϖ c)
  (hloops : NoLoops c)

include hW hϖ in
/-- The branch valuation of a component through a point at which `a` vanishes: `a` has
transcendental residue there. -/
lemma residue_of_vanishing {v : Set c.scheme} (hv : v ∈ components c) {z : c.scheme}
    (hzv : z ∈ v) {g : L} (hgW : g ∈ Wc hW hv) (hg1 : (Wc hW hv).valuation g = 1)
    (hgz : ∀ R : ValuationSubring L, IsCentre j R z → R.valuation g < 1) :
    IsResidueTranscendental O (Wc hW hv) g := by
  have hWc := Wc_spec hW hv
  obtain ⟨R, hRW, hRz⟩ := exists_le_centre hW (gp_specializes hv hzv) hWc
  have hcomap : (Wc hW hv).comap (algebraMap K L) = O := by
    refine comap_eq_of_lt_one hϖ (fun o ↦ ?_) ?_
    · rw [show algebraMap K L (o : K) = algebraMap O L o from
        (IsScalarTower.algebraMap_apply O K L o).symm]
      exact germs_le hW hWc (gp_specializes hv hzv) _ (algebraMap_mem_germs hW z o)
    · rw [show algebraMap K L (ϖ : K) = algebraMap O L ϖ from
        (IsScalarTower.algebraMap_apply O K L ϖ).symm]
      exact valuation_ϖ_lt_one hW hϖ (hv.2.1 (gp_mem hv)) hWc
  refine isResidueTranscendental_of_lt_one hcomap hgW hg1 hRW (fun o ↦ ?_) (hgz R hRz)
  rw [show algebraMap K L (o : K) = algebraMap O L o from
    (IsScalarTower.algebraMap_apply O K L o).symm]
  exact ((isCentre_iff_dominates c j (specializes_of_isWModel hW z) R).1 hRz).1
    (algebraMap_mem_germs hW z o)

omit [IsDiscreteValuationRing O] in
lemma algebraMap_O_K (o : O) : algebraMap K L (o : K) = algebraMap O L o :=
  (IsScalarTower.algebraMap_apply O K L o).symm

include hW hϖ in
/-- Uniqueness of the branch valuation with a given unit coordinate. -/
lemma eq_Wc_of_branch {z : c.scheme} {P : Subring L} {a b : L} {m : ℕ}
    (hPg : (P : Set L) = germs c j z)
    (hcore : NodeCore P (algebraMap O L) (algebraMap O L ϖ) a b m) [IsLocalRing P]
    [IsNoetherianRing P] {v : Set c.scheme} (hv : v ∈ components c) (hzv : z ∈ v)
    (ha : (Wc hW hv).valuation a = 1) (hb : (Wc hW hv).valuation b < 1)
    {U : ValuationSubring L} (hPU : (P : Set L) ⊆ U)
    (hϖU : U.valuation (algebraMap O L ϖ) < 1) (haU : U.valuation a = 1) : U = Wc hW hv := by
  have hWc := Wc_spec hW hv
  have hbU : U.valuation b < 1 := by
    have h := hcore.mul_eq
    have : U.valuation a * U.valuation b = U.valuation (algebraMap O L ϖ) ^ m := by
      rw [← map_mul, h, map_pow]
    rw [haU, one_mul] at this
    rw [this]; exact pow_lt_one₀ zero_le hϖU (by have := hcore.one_le; omega)
  obtain ⟨y₁, hy₁⟩ := exists_centre hW (fun o ↦ hPU (hcore.base_mem o))
  have hPW : P ≤ (Wc hW hv).toSubring := fun f hf ↦
    germs_le hW hWc (gp_specializes hv hzv) f (hPg ▸ hf)
  have hcen := CrossingTarget.centre_eq_of_branch (specializes_of_isWModel hW z) hPg hcore
    (fun f hf ↦ hPU hf) hPW hϖU hbU haU (valuation_ϖ_lt_one hW hϖ (hv.2.1 (gp_mem hv)) hWc) hb
    ha hy₁ hWc
  subst hcen
  exact centreDetermines_gp hW hϖ hv U (Wc hW hv) hy₁ hWc

include hW hϖ in
/-- **Branches at a node**, given the components on which `a` resp. `b` is a unit. -/
theorem nodeBranches_of {z : c.scheme} {P : Subring L} {a b : L} {m : ℕ}
    (hPg : (P : Set L) = germs c j z)
    (hcore : NodeCore P (algebraMap O L) (algebraMap O L ϖ) a b m) [IsLocalRing P]
    [IsNoetherianRing P] {v₁ v₂ : Set c.scheme} (hv₁ : v₁ ∈ components c)
    (hv₂ : v₂ ∈ components c) (hz₁ : z ∈ v₁) (hz₂ : z ∈ v₂)
    (ha₁ : (Wc hW hv₁).valuation a = 1) (hb₁ : (Wc hW hv₁).valuation b < 1)
    (hb₂ : (Wc hW hv₂).valuation b = 1) (ha₂ : (Wc hW hv₂).valuation a < 1) :
    NodeBranches O ϖ P (algebraMap O L) a b m (Wc hW hv₁) (Wc hW hv₂) := by
  have hy := specializes_of_isWModel hW z
  have hϖL : algebraMap K L (ϖ : K) = algebraMap O L ϖ := algebraMap_O_K ϖ
  have hPW : ∀ {v} (hv : v ∈ components c), z ∈ v → (P : Set L) ⊆ Wc hW hv :=
    fun hv hzv f hf ↦ germs_le hW (Wc_spec hW hv) (gp_specializes hv hzv) f (hPg ▸ hf)
  have hϖW : ∀ {v} (hv : v ∈ components c), (Wc hW hv).valuation (algebraMap O L ϖ) < 1 :=
    fun hv ↦ valuation_ϖ_lt_one hW hϖ (hv.2.1 (gp_mem hv)) (Wc_spec hW hv)
  have hdom : ∀ R : ValuationSubring L, IsCentre j R z → ∀ f ∈ P, (∀ w ∈ P, f * w ≠ 1) →
      R.valuation f < 1 := fun R hR f hf hfu ↦
    ((isCentre_iff_dominates c j hy R).1 hR).2 f (hPg ▸ hf)
      (fun w hw ↦ hfu w (by rw [← SetLike.mem_coe, hPg]; exact hw))
  have hmem : ∀ {v} (hv : v ∈ components c), z ∈ v → ∀ f ∈ P, f ∈ Wc hW hv :=
    fun hv hzv f hf ↦ hPW hv hzv hf
  have hcomap : ∀ {v} (hv : v ∈ components c), z ∈ v →
      (Wc hW hv).comap (algebraMap K L) = O := by
    intro v hv hzv
    have hO : ∀ o : O, algebraMap K L (o : K) ∈ Wc hW hv := by
      intro o
      rw [algebraMap_O_K]
      exact hmem hv hzv _ (hcore.base_mem o)
    exact comap_eq_of_lt_one hϖ hO (by rw [hϖL]; exact hϖW hv)
  have hm := hcore.one_le
  have hb0 : b ≠ 0 := fun h ↦ by rw [h, map_zero] at hb₂; exact zero_ne_one hb₂
  refine
    { core := hϖL ▸ hcore
      base := fun o ↦ (algebraMap_O_K o).symm
      irred := hϖ
      mono₁ := ⟨hPW hv₁ hz₁, hϖL ▸ hϖW hv₁, by unfold IsLogValue; simpa using ha₁, ?_⟩
      mono₂ := ⟨hPW hv₂ hz₂, hϖL ▸ hϖW hv₂, ?_, ?_⟩
      uniq₁ := fun U hPU hϖU haU ↦ eq_Wc_of_branch hW hϖ hPg hcore hv₁ hz₁ ha₁ hb₁ hPU
        (hϖL ▸ hϖU) haU
      uniq₂ := fun U hPU hϖU hbU ↦ eq_Wc_of_branch hW hϖ hPg hcore.swap hv₂ hz₂ hb₂ ha₂ hPU
        (hϖL ▸ hϖU) hbU }
  · simp only [Rat.den_zero, pow_one, Rat.num_zero, zpow_zero, div_one]
    exact residue_of_vanishing hW hϖ hv₁ hz₁ (hmem hv₁ hz₁ a hcore.u_mem) ha₁
      fun R hR ↦ hdom R hR a hcore.u_mem hcore.u_nonunit
  · unfold IsLogValue
    simp only [Rat.den_natCast, pow_one, Rat.num_natCast, zpow_natCast]
    have : (Wc hW hv₂).valuation a * (Wc hW hv₂).valuation b =
        (Wc hW hv₂).valuation (algebraMap O L ϖ) ^ m := by
      rw [← map_mul, hcore.mul_eq, map_pow]
    rw [hb₂, mul_one] at this
    rw [this, hϖL]
  · simp only [Rat.den_natCast, pow_one, Rat.num_natCast, zpow_natCast]
    have e : a / algebraMap K L (ϖ : K) ^ m = b⁻¹ := by
      have ha0 : a ≠ 0 := fun h ↦ by rw [h, map_zero] at ha₁; exact zero_ne_one ha₁
      rw [hϖL, ← hcore.mul_eq]
      field_simp
    rw [e]
    have hbt := residue_of_vanishing hW hϖ hv₂ hz₂ (hmem hv₂ hz₂ b hcore.v_mem) hb₂
      fun R hR ↦ hdom R hR b hcore.v_mem hcore.v_nonunit
    refine hbt.inv (hcomap hv₂ hz₂) ?_
    rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, hb₂, inv_one]

include hW hϖ hloops in
/-- **The branches at a node**, given the node core of its germs. -/
theorem exists_nodeBranches_of_core {z : c.scheme} (hz : IsNodePt c z) {P : Subring L}
    {a b : L} {m : ℕ} (hPg : (P : Set L) = germs c j z)
    (hcore : NodeCore P (algebraMap O L) (algebraMap O L ϖ) a b m) [IsLocalRing P]
    [IsNoetherianRing P] :
    ∃ (v₁ v₂ : Set c.scheme) (hv₁ : v₁ ∈ components c) (hv₂ : v₂ ∈ components c),
      z ∈ v₁ ∧ z ∈ v₂ ∧ NodeBranches O ϖ P (algebraMap O L) a b m (Wc hW hv₁) (Wc hW hv₂) := by
  obtain ⟨w₁, hw₁, w₂, hw₂, hne, h₁, h₂⟩ := hloops z hz
  have hb := fun {w} (hw : w ∈ components c) (hzw : z ∈ w) ↦
    branch hW hϖ hloops hz hPg hcore hw hzw (Wc_spec hW hw)
  rcases hb hw₁ h₁ with ⟨ha₁, hb₁⟩ | ⟨hb₁, ha₁⟩ <;> rcases hb hw₂ h₂ with ⟨ha₂, hb₂⟩ | ⟨hb₂, ha₂⟩
  · exact absurd (branch_ne hW hϖ hPg hcore hw₁ hw₂ h₁ h₂ (Wc_spec hW hw₁) (Wc_spec hW hw₂)
      ha₁ hb₁ ha₂ hb₂) hne
  · exact ⟨w₁, w₂, hw₁, hw₂, h₁, h₂,
      nodeBranches_of hW hϖ hPg hcore hw₁ hw₂ h₁ h₂ ha₁ hb₁ hb₂ ha₂⟩
  · exact ⟨w₂, w₁, hw₂, hw₁, h₂, h₁,
      nodeBranches_of hW hϖ hPg hcore hw₂ hw₁ h₂ h₁ ha₂ hb₂ hb₁ ha₁⟩
  · exact absurd (branch_ne hW hϖ hPg hcore.swap hw₁ hw₂ h₁ h₂ (Wc_spec hW hw₁)
      (Wc_spec hW hw₂) hb₁ ha₁ hb₂ ha₂) hne

include hW hϖ hsplit hloops in
/-- **The germs at a node with their branches.** -/
theorem exists_nodeBranches {z : c.scheme} (hz : IsNodePt c z) :
    ∃ (P : Subring L) (a b : L) (m : ℕ), (P : Set L) = germs c j z ∧
      NodeCore P (algebraMap O L) (algebraMap O L ϖ) a b m ∧ IsLocalRing P ∧
      IsNoetherianRing P ∧ (∀ t ∈ P, ∀ M : ℕ, (∃ r ∈ P, t * r = algebraMap O L ϖ ^ M) →
        ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap O L ϖ ^ α * a ^ e ∨
          t = ε * algebraMap O L ϖ ^ α * b ^ e) ∧
      ∃ (v₁ v₂ : Set c.scheme) (hv₁ : v₁ ∈ components c) (hv₂ : v₂ ∈ components c),
        z ∈ v₁ ∧ z ∈ v₂ ∧ NodeBranches O ϖ P (algebraMap O L) a b m (Wc hW hv₁) (Wc hW hv₂) := by
  obtain ⟨P, a, b, m, hPg, hcore, hloc, hnoeth, hdiv⟩ := node_data hW hϖ hsplit hloops hz
  haveI := hloc
  haveI := hnoeth
  exact ⟨P, a, b, m, hPg, hcore, hloc, hnoeth, hdiv,
    exists_nodeBranches_of_core hW hϖ hloops hz hPg hcore⟩

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
