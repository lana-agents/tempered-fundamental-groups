/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeFibreProduct
import TemperedFundamentalGroups.SemistableReduction.NodeLemma

/-!
# Exact node coordinates from branch data on a ring (O1, the abstract local assembly)

Blueprint §9.12, O1. Let `B` be a noetherian normal domain over a DVR `O`, `𝔭` a prime of `B`,
and `φᵢ : B → Vᵢ` maps to local domains (the reductions to the local rings of the two branches),
with residue maps `rᵢ` agreeing on `B` and `𝔭 = ker(r₁ ∘ φ₁)`. Suppose:

* (kernel) an element reducing to `0` on both branches is divisible by `ϖ` up to a unit at `𝔭`;
* (fibre product) every matching pair `(a, b)` is `(φ₁ y / φ₁ s, φ₂ y / φ₂ s)` with `s ∉ 𝔭`;
* (residues) the residues of the `Vᵢ` come from `O`;
* `u', v' ∈ B` reduce to `(t₁, 0)`, `(0, t₂)` with `tᵢ` generating the maximal ideals;
* `x, y ∈ B`, `x y = c₀ ∈ O ∖ 0`, `φ₁ x = η t₁^d` with `η` a unit, `φ₂ x = 0`, `φ₂ y ≠ 0`.

Then in `D = B_𝔭` there are exact node coordinates `u v = ϖⁿ` with `u ≡ u'` modulo `ϖ` and
`x = ε u^d` (`exists_node_of_branches`): `D` is an ordinary double point
(`isOrdinaryDoublePoint_of_fibreProduct`), and the node deformation
`IsOrdinaryDoublePoint.exists_node` applies.
-/

open IsLocalRing

namespace SemistableReduction

/-- **Branch data at `𝔭`**: the hypotheses of `exists_node_of_branches` and
`isAnnulusAt_of_branches_alg`, bundled. -/
structure BranchData {O B V₁ V₂ k : Type*} [CommRing O] [CommRing B] [Algebra O B]
    [CommRing V₁] [IsLocalRing V₁] [CommRing V₂] [IsLocalRing V₂] [Field k] (𝔭 : Ideal B)
    (φ₁ : B →+* V₁) (φ₂ : B →+* V₂) (r₁ : V₁ →+* k) (r₂ : V₂ →+* k) (ϖ : O) (u' v' x y : B)
    (c₀ : O) (d : ℕ) : Prop where
  hr₁ : ∀ a, r₁ a = 0 ↔ a ∈ maximalIdeal V₁
  hr₂ : ∀ b, r₂ b = 0 ↔ b ∈ maximalIdeal V₂
  hcomp : ∀ b, r₁ (φ₁ b) = r₂ (φ₂ b)
  h𝔭 : ∀ b, b ∈ 𝔭 ↔ r₁ (φ₁ b) = 0
  hϖ : Irreducible ϖ
  hϖ0 : algebraMap O B ϖ ≠ 0
  hϖ₁ : φ₁ (algebraMap O B ϖ) = 0
  hϖ₂ : φ₂ (algebraMap O B ϖ) = 0
  hker : ∀ b, φ₁ b = 0 → φ₂ b = 0 → ∃ t ∉ 𝔭, ∃ z, t * b = algebraMap O B ϖ * z
  hfp : ∀ a b, r₁ a = r₂ b → ∃ y s, s ∉ 𝔭 ∧ φ₁ y = a * φ₁ s ∧ φ₂ y = b * φ₂ s
  hO₁ : ∀ a : V₁, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₁ a
  hO₂ : ∀ b : V₂, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₂ b
  hu₁ : maximalIdeal V₁ = Ideal.span {φ₁ u'}
  hu₂ : φ₂ u' = 0
  hv₂ : maximalIdeal V₂ = Ideal.span {φ₂ v'}
  hv₁ : φ₁ v' = 0
  hu0 : φ₁ u' ≠ 0
  hv0 : φ₂ v' ≠ 0
  hc₀ : c₀ ≠ 0
  hxy : x * y = algebraMap O B c₀
  hd : 1 ≤ d
  hx₁ : ∃ η : V₁, r₁ η ≠ 0 ∧ φ₁ x = η * φ₁ u' ^ d
  hx₂ : φ₂ x = 0
  hy : φ₂ y ≠ 0

variable {O B V₁ V₂ k : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [Algebra O B]
  [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂]
  [Field k]

/-- **Exact node coordinates from branch data on a ring.** -/
theorem exists_node_of_branches (𝔭 : Ideal B) [𝔭.IsPrime] (φ₁ : B →+* V₁) (φ₂ : B →+* V₂)
    (r₁ : V₁ →+* k) (r₂ : V₂ →+* k) (hr₁ : ∀ a, r₁ a = 0 ↔ a ∈ maximalIdeal V₁)
    (hr₂ : ∀ b, r₂ b = 0 ↔ b ∈ maximalIdeal V₂) (hcomp : ∀ b, r₁ (φ₁ b) = r₂ (φ₂ b))
    (h𝔭 : ∀ b, b ∈ 𝔭 ↔ r₁ (φ₁ b) = 0) {ϖ : O} (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap O B ϖ ≠ 0) (hϖ₁ : φ₁ (algebraMap O B ϖ) = 0)
    (hϖ₂ : φ₂ (algebraMap O B ϖ) = 0)
    (hker : ∀ b, φ₁ b = 0 → φ₂ b = 0 → ∃ t ∉ 𝔭, ∃ z, t * b = algebraMap O B ϖ * z)
    (hfp : ∀ a b, r₁ a = r₂ b → ∃ y s, s ∉ 𝔭 ∧ φ₁ y = a * φ₁ s ∧ φ₂ y = b * φ₂ s)
    (hO₁ : ∀ a : V₁, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₁ a)
    (hO₂ : ∀ b : V₂, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₂ b)
    {u' v' : B} (hu₁ : maximalIdeal V₁ = Ideal.span {φ₁ u'}) (hu₂ : φ₂ u' = 0)
    (hv₂ : maximalIdeal V₂ = Ideal.span {φ₂ v'}) (hv₁ : φ₁ v' = 0) (hu0 : φ₁ u' ≠ 0)
    (hv0 : φ₂ v' ≠ 0) {x y : B} {c₀ : O} (hc₀ : c₀ ≠ 0) (hxy : x * y = algebraMap O B c₀)
    {d : ℕ} (hd : 1 ≤ d) {η : V₁} (hη : r₁ η ≠ 0) (hx₁ : φ₁ x = η * φ₁ u' ^ d) (hx₂ : φ₂ x = 0)
    (hy : φ₂ y ≠ 0) :
    ∃ (n : ℕ) (u v : Localization.AtPrime 𝔭), 1 ≤ n ∧
      u * v = algebraMap O (Localization.AtPrime 𝔭) ϖ ^ n ∧
      u - algebraMap B _ u' ∈ Ideal.span {algebraMap O (Localization.AtPrime 𝔭) ϖ} ∧
      (∀ (a : B) (s : 𝔭.primeCompl), IsLocalization.mk' (Localization.AtPrime 𝔭) a s = u →
        φ₁ a = φ₁ s * φ₁ u') ∧
      ∃ ε : (Localization.AtPrime 𝔭)ˣ, algebraMap B _ x = ε * u ^ d := by
  classical
  set D := Localization.AtPrime 𝔭
  haveI : IsNoetherianRing D := IsLocalization.isNoetherianRing 𝔭.primeCompl D inferInstance
  haveI : IsIntegrallyClosed D :=
    isIntegrallyClosed_of_isLocalization D 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  have hinj : Function.Injective (algebraMap B D) :=
    IsLocalization.injective D 𝔭.primeCompl_le_nonZeroDivisors
  -- units at `𝔭`
  have hu₁' : ∀ s : 𝔭.primeCompl, IsUnit (φ₁ s) := by
    intro s
    by_contra h
    exact s.2 ((h𝔭 _).mpr ((hr₁ _).mpr ((mem_maximalIdeal _).mpr h)))
  have hu₂' : ∀ s : 𝔭.primeCompl, IsUnit (φ₂ s) := by
    intro s
    by_contra h
    exact s.2 ((h𝔭 _).mpr (by rw [hcomp]; exact (hr₂ _).mpr ((mem_maximalIdeal _).mpr h)))
  set ψ₁ : D →+* V₁ := IsLocalization.lift hu₁'
  set ψ₂ : D →+* V₂ := IsLocalization.lift hu₂'
  have hψ₁ : ∀ b, ψ₁ (algebraMap B D b) = φ₁ b := IsLocalization.lift_eq hu₁'
  have hψ₂ : ∀ b, ψ₂ (algebraMap B D b) = φ₂ b := IsLocalization.lift_eq hu₂'
  have hspec₁ : ∀ (b : B) (s : 𝔭.primeCompl), ψ₁ (IsLocalization.mk' D b s) * φ₁ s = φ₁ b :=
    fun b s ↦ by
      rw [mul_comm]; exact ((IsLocalization.lift_mk'_spec (hg := hu₁') b _ s).mp rfl).symm
  have hspec₂ : ∀ (b : B) (s : 𝔭.primeCompl), ψ₂ (IsLocalization.mk' D b s) * φ₂ s = φ₂ b :=
    fun b s ↦ by
      rw [mul_comm]; exact ((IsLocalization.lift_mk'_spec (hg := hu₂') b _ s).mp rfl).symm
  have hcompD : ∀ z, r₁ (ψ₁ z) = r₂ (ψ₂ z) := by
    intro z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
    have e₁ := congrArg r₁ (hspec₁ b s)
    have e₂ := congrArg r₂ (hspec₂ b s)
    rw [map_mul] at e₁ e₂
    have hs0 : r₂ (φ₂ s) ≠ 0 := by
      rw [← hcomp]; exact fun h ↦ s.2 ((h𝔭 _).mpr h)
    rw [hcomp, hcomp] at e₁
    exact mul_right_cancel₀ hs0 (e₁.trans e₂.symm)
  -- the algebra map from `O`
  have hOD : ∀ o, algebraMap O D o = algebraMap B D (algebraMap O B o) :=
    IsScalarTower.algebraMap_apply O B D
  -- the kernel
  have hkerD : ∀ z, ψ₁ z = 0 → ψ₂ z = 0 → z ∈ Ideal.span {algebraMap O D ϖ} := by
      intro z hz₁ hz₂
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
      have hb₁ : φ₁ b = 0 := by rw [← hspec₁ b s, hz₁, zero_mul]
      have hb₂ : φ₂ b = 0 := by rw [← hspec₂ b s, hz₂, zero_mul]
      obtain ⟨t, ht, w, hw⟩ := hker b hb₁ hb₂
      rw [Ideal.mem_span_singleton']
      refine ⟨IsLocalization.mk' D w (⟨t, ht⟩ * s), ?_⟩
      rw [hOD, mul_comm, ← IsLocalization.mk'_one (M := 𝔭.primeCompl) D, ← IsLocalization.mk'_mul,
        one_mul, IsLocalization.mk'_eq_iff_eq]
      simp only [Submonoid.coe_mul]
      congr 1
      linear_combination (-(s : B)) * hw
  -- the fibre product
  have hfpD : ∀ a b, r₁ a = r₂ b → ∃ z, ψ₁ z = a ∧ ψ₂ z = b := by
      intro a b hab
      obtain ⟨y', s, hs, h₁, h₂⟩ := hfp a b hab
      let s' : 𝔭.primeCompl := ⟨s, hs⟩
      refine ⟨IsLocalization.mk' D y' s', ?_, ?_⟩
      · have := hspec₁ y' s'
        rw [h₁] at this
        exact mul_right_cancel₀ (hu₁' s').ne_zero this
      · have := hspec₂ y' s'
        rw [h₂] at this
        exact mul_right_cancel₀ (hu₂' s').ne_zero this
  -- the ordinary double point
  have H : IsOrdinaryDoublePoint ϖ (algebraMap B D u') (algebraMap B D v') (RingHom.ker ψ₁)
      (RingHom.ker ψ₂) := by
    refine isOrdinaryDoublePoint_of_fibreProduct ψ₁ ψ₂ r₁ r₂ hr₁ hr₂ hcompD hkerD
      (by rw [hOD, hψ₁]; exact hϖ₁) (by rw [hOD, hψ₂]; exact hϖ₂) hfpD ?_ ?_
      (by rw [hψ₁]; exact hu₁) (by rw [hψ₂]; exact hu₂) (by rw [hψ₂]; exact hv₂)
      (by rw [hψ₁]; exact hv₁) (by rw [hψ₁]; exact hu0) (by rw [hψ₂]; exact hv0)
    · intro a
      obtain ⟨o, ho⟩ := hO₁ a
      exact ⟨o, by rw [hOD, hψ₁]; exact ho⟩
    · intro b
      obtain ⟨o, ho⟩ := hO₂ b
      exact ⟨o, by rw [hOD, hψ₁]; exact ho⟩
  -- the unit `η` lifted to `D`
  obtain ⟨o, ho⟩ := hO₁ η
  obtain ⟨ηD, hηD₁, -⟩ := hfpD η (φ₂ (algebraMap O B o)) (by rw [← hcomp, ho])
  have hmax : maximalIdeal D ≤ RingHom.ker (r₁.comp ψ₁) := by
    rw [H.maximalIdeal_eq, Ideal.span_le]
    rintro w (rfl | rfl | rfl)
    · change r₁ (ψ₁ _) = 0
      rw [hOD, hψ₁, hϖ₁, map_zero]
    · change r₁ (ψ₁ _) = 0
      rw [hψ₁, hr₁, hu₁]
      exact Ideal.subset_span rfl
    · change r₁ (ψ₁ _) = 0
      rw [hψ₁, hv₁, map_zero]
  have hηD : ηD ∉ maximalIdeal D := fun h ↦ hη (by
    have := hmax h
    rw [RingHom.mem_ker, RingHom.comp_apply, hηD₁] at this
    exact this)
  have h1 : (1 : D) ∉ maximalIdeal D := fun h ↦ (maximalIdeal.isMaximal D).ne_top
    ((Ideal.eq_top_iff_one _).mpr h)
  have hxD : 1 * algebraMap B D x - ηD * algebraMap B D u' ^ d ∈
      Ideal.span {algebraMap O D ϖ, algebraMap B D v'} := by
    refine Ideal.span_mono (by simp) (hkerD _ ?_ ?_)
    · rw [one_mul, map_sub, map_mul, map_pow, hψ₁, hψ₁, hηD₁, hx₁, sub_self]
    · rw [one_mul, map_sub, map_mul, map_pow, hψ₂, hψ₂, hx₂, hu₂, zero_pow (by omega), mul_zero,
        sub_self]
  have hyD : algebraMap B D y ∉ RingHom.ker ψ₂ := by
    rw [RingHom.mem_ker, hψ₂]; exact hy
  have hϖ0D : algebraMap O D ϖ ≠ 0 := by
    rw [hOD]; exact fun h ↦ hϖ0 (hinj (by rw [h, map_zero]))
  have hc₀D : algebraMap B D x * algebraMap B D y = algebraMap O D c₀ := by
    rw [← map_mul, hxy, hOD]
  obtain ⟨n, u, v, hn, huv, -, -, -, hu, ⟨ε, hε⟩, -⟩ :=
    H.exists_node hϖ hϖ0D hc₀ hc₀D hd h1 hηD hxD hyD
  refine ⟨n, u, v, hn, huv, hu, fun a s has ↦ ?_, ε, hε⟩
  have h1 : ψ₁ u = φ₁ u' := by
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp hu
    have : u = algebraMap B D u' + w * algebraMap O D ϖ := by rw [hw]; ring
    rw [this, map_add, map_mul, hψ₁, hOD, hψ₁, hϖ₁, mul_zero, add_zero]
  rw [← hspec₁ a s, has, h1, mul_comm]

/-- `exists_node_of_branches` for bundled branch data. -/
theorem BranchData.exists_node {𝔭 : Ideal B} [𝔭.IsPrime] {φ₁ : B →+* V₁} {φ₂ : B →+* V₂}
    {r₁ : V₁ →+* k} {r₂ : V₂ →+* k} {ϖ : O} {u' v' x y : B} {c₀ : O} {d : ℕ}
    (h : BranchData 𝔭 φ₁ φ₂ r₁ r₂ ϖ u' v' x y c₀ d) :
    ∃ (n : ℕ) (u v : Localization.AtPrime 𝔭), 1 ≤ n ∧
      u * v = algebraMap O (Localization.AtPrime 𝔭) ϖ ^ n ∧
      u - algebraMap B _ u' ∈ Ideal.span {algebraMap O (Localization.AtPrime 𝔭) ϖ} ∧
      (∀ (a : B) (s : 𝔭.primeCompl), IsLocalization.mk' (Localization.AtPrime 𝔭) a s = u →
        φ₁ a = φ₁ s * φ₁ u') ∧
      ∃ ε : (Localization.AtPrime 𝔭)ˣ, algebraMap B _ x = ε * u ^ d := by
  obtain ⟨η, hη, hx₁⟩ := h.hx₁
  exact exists_node_of_branches 𝔭 φ₁ φ₂ r₁ r₂ h.hr₁ h.hr₂ h.hcomp h.h𝔭 h.hϖ h.hϖ0 h.hϖ₁ h.hϖ₂
    h.hker h.hfp h.hO₁ h.hO₂ h.hu₁ h.hu₂ h.hv₂ h.hv₁ h.hu0 h.hv0 h.hc₀ h.hxy h.hd hη hx₁ h.hx₂
    h.hy

section Annulus

universe u

variable {O B : Type u} {V₁ V₂ k : Type*} [CommRing O] [IsDomain O]
  [IsDiscreteValuationRing O] [CommRing B] [IsDomain B]
  [IsIntegrallyClosed B] [Algebra O B] [Algebra.FiniteType O B] [FaithfulSMul O B]
  [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂]
  [Field k]

/-- **The node lemma from branch data on a ring, with split node**: under the hypotheses of
`exists_node_of_branches`, `B` is étale-locally the node at `𝔭` (`IsAnnulusAt`), and
the node is split (`IsSplitNodePt`). -/
theorem isAnnulusAt_and_isSplitNodePt_of_branches_alg (𝔭 : Ideal B) [𝔭.IsPrime] (φ₁ : B →+* V₁)
    (φ₂ : B →+* V₂)
    (r₁ : V₁ →+* k) (r₂ : V₂ →+* k) (hr₁ : ∀ a, r₁ a = 0 ↔ a ∈ maximalIdeal V₁)
    (hr₂ : ∀ b, r₂ b = 0 ↔ b ∈ maximalIdeal V₂) (hcomp : ∀ b, r₁ (φ₁ b) = r₂ (φ₂ b))
    (h𝔭 : ∀ b, b ∈ 𝔭 ↔ r₁ (φ₁ b) = 0) {ϖ : O} (hϖ : Irreducible ϖ)
    (_hϖ0 : algebraMap O B ϖ ≠ 0) (hϖ₁ : φ₁ (algebraMap O B ϖ) = 0)
    (hϖ₂ : φ₂ (algebraMap O B ϖ) = 0)
    (hker : ∀ b, φ₁ b = 0 → φ₂ b = 0 → ∃ t ∉ 𝔭, ∃ z, t * b = algebraMap O B ϖ * z)
    (hfp : ∀ a b, r₁ a = r₂ b → ∃ y s, s ∉ 𝔭 ∧ φ₁ y = a * φ₁ s ∧ φ₂ y = b * φ₂ s)
    (hO₁ : ∀ a : V₁, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₁ a)
    (hO₂ : ∀ b : V₂, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₂ b)
    {u' v' : B} (hu₁ : maximalIdeal V₁ = Ideal.span {φ₁ u'}) (hu₂ : φ₂ u' = 0)
    (hv₂ : maximalIdeal V₂ = Ideal.span {φ₂ v'}) (hv₁ : φ₁ v' = 0) (hu0 : φ₁ u' ≠ 0)
    (hv0 : φ₂ v' ≠ 0) {x y : B} {c₀ : O} (hc₀ : c₀ ≠ 0) (hxy : x * y = algebraMap O B c₀)
    {d : ℕ} (hd : 1 ≤ d) {η : V₁} (hη : r₁ η ≠ 0) (hx₁ : φ₁ x = η * φ₁ u' ^ d) (hx₂ : φ₂ x = 0)
    (hy : φ₂ y ≠ 0) :
    IsAnnulusAt ϖ x y d 𝔭 ∧ IsSplitNodePt ϖ 𝔭 := by
  classical
  set D := Localization.AtPrime 𝔭
  have hinj : Function.Injective (algebraMap B D) :=
    IsLocalization.injective D 𝔭.primeCompl_le_nonZeroDivisors
  -- units at `𝔭`
  have hu₁' : ∀ s : 𝔭.primeCompl, IsUnit (φ₁ s) := by
    intro s
    by_contra h
    exact s.2 ((h𝔭 _).mpr ((hr₁ _).mpr ((mem_maximalIdeal _).mpr h)))
  have hu₂' : ∀ s : 𝔭.primeCompl, IsUnit (φ₂ s) := by
    intro s
    by_contra h
    exact s.2 ((h𝔭 _).mpr (by rw [hcomp]; exact (hr₂ _).mpr ((mem_maximalIdeal _).mpr h)))
  set ψ₁ : D →+* V₁ := IsLocalization.lift hu₁'
  set ψ₂ : D →+* V₂ := IsLocalization.lift hu₂'
  have hψ₁ : ∀ b, ψ₁ (algebraMap B D b) = φ₁ b := IsLocalization.lift_eq hu₁'
  have hψ₂ : ∀ b, ψ₂ (algebraMap B D b) = φ₂ b := IsLocalization.lift_eq hu₂'
  have hspec₁ : ∀ (b : B) (s : 𝔭.primeCompl), ψ₁ (IsLocalization.mk' D b s) * φ₁ s = φ₁ b :=
    fun b s ↦ by
      rw [mul_comm]; exact ((IsLocalization.lift_mk'_spec (hg := hu₁') b _ s).mp rfl).symm
  have hspec₂ : ∀ (b : B) (s : 𝔭.primeCompl), ψ₂ (IsLocalization.mk' D b s) * φ₂ s = φ₂ b :=
    fun b s ↦ by
      rw [mul_comm]; exact ((IsLocalization.lift_mk'_spec (hg := hu₂') b _ s).mp rfl).symm
  have hcompD : ∀ z, r₁ (ψ₁ z) = r₂ (ψ₂ z) := by
    intro z
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
    have e₁ := congrArg r₁ (hspec₁ b s)
    have e₂ := congrArg r₂ (hspec₂ b s)
    rw [map_mul] at e₁ e₂
    have hs0 : r₂ (φ₂ s) ≠ 0 := by
      rw [← hcomp]; exact fun h ↦ s.2 ((h𝔭 _).mpr h)
    rw [hcomp, hcomp] at e₁
    exact mul_right_cancel₀ hs0 (e₁.trans e₂.symm)
  -- the algebra map from `O`
  have hOD : ∀ o, algebraMap O D o = algebraMap B D (algebraMap O B o) :=
    IsScalarTower.algebraMap_apply O B D
  -- the kernel
  have hkerD : ∀ z, ψ₁ z = 0 → ψ₂ z = 0 → z ∈ Ideal.span {algebraMap O D ϖ} := by
      intro z hz₁ hz₂
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl z
      have hb₁ : φ₁ b = 0 := by rw [← hspec₁ b s, hz₁, zero_mul]
      have hb₂ : φ₂ b = 0 := by rw [← hspec₂ b s, hz₂, zero_mul]
      obtain ⟨t, ht, w, hw⟩ := hker b hb₁ hb₂
      rw [Ideal.mem_span_singleton']
      refine ⟨IsLocalization.mk' D w (⟨t, ht⟩ * s), ?_⟩
      rw [hOD, mul_comm, ← IsLocalization.mk'_one (M := 𝔭.primeCompl) D, ← IsLocalization.mk'_mul,
        one_mul, IsLocalization.mk'_eq_iff_eq]
      simp only [Submonoid.coe_mul]
      congr 1
      linear_combination (-(s : B)) * hw
  -- the fibre product
  have hfpD : ∀ a b, r₁ a = r₂ b → ∃ z, ψ₁ z = a ∧ ψ₂ z = b := by
      intro a b hab
      obtain ⟨y', s, hs, h₁, h₂⟩ := hfp a b hab
      let s' : 𝔭.primeCompl := ⟨s, hs⟩
      refine ⟨IsLocalization.mk' D y' s', ?_, ?_⟩
      · have := hspec₁ y' s'
        rw [h₁] at this
        exact mul_right_cancel₀ (hu₁' s').ne_zero this
      · have := hspec₂ y' s'
        rw [h₂] at this
        exact mul_right_cancel₀ (hu₂' s').ne_zero this
  -- the ordinary double point
  have H : IsOrdinaryDoublePoint ϖ (algebraMap B D u') (algebraMap B D v') (RingHom.ker ψ₁)
      (RingHom.ker ψ₂) := by
    refine isOrdinaryDoublePoint_of_fibreProduct ψ₁ ψ₂ r₁ r₂ hr₁ hr₂ hcompD hkerD
      (by rw [hOD, hψ₁]; exact hϖ₁) (by rw [hOD, hψ₂]; exact hϖ₂) hfpD ?_ ?_
      (by rw [hψ₁]; exact hu₁) (by rw [hψ₂]; exact hu₂) (by rw [hψ₂]; exact hv₂)
      (by rw [hψ₁]; exact hv₁) (by rw [hψ₁]; exact hu0) (by rw [hψ₂]; exact hv0)
    · intro a
      obtain ⟨o, ho⟩ := hO₁ a
      exact ⟨o, by rw [hOD, hψ₁]; exact ho⟩
    · intro b
      obtain ⟨o, ho⟩ := hO₂ b
      exact ⟨o, by rw [hOD, hψ₁]; exact ho⟩
  -- `s x - η u'^d ∈ (ϖ)` with `s, η ∈ B ∖ 𝔭`
  obtain ⟨o, ho⟩ := hO₁ η
  obtain ⟨η', s', hs', hη₁, -⟩ := hfp η (φ₂ (algebraMap O B o)) (by rw [← hcomp, ho])
  have hzero₁ : φ₁ (s' * x - η' * u' ^ d) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, hx₁, hη₁]; ring
  have hzero₂ : φ₂ (s' * x - η' * u' ^ d) = 0 := by
    rw [map_sub, map_mul, map_mul, map_pow, hx₂, hu₂, zero_pow (by omega)]; ring
  obtain ⟨t, ht, z, hz⟩ := hker _ hzero₁ hzero₂
  have hs'' : t * s' ∉ 𝔭 := Ideal.IsPrime.mul_notMem ‹_› ht hs'
  have hη' : t * η' ∉ 𝔭 := by
    refine Ideal.IsPrime.mul_notMem ‹_› ht ?_
    rw [h𝔭, hη₁, map_mul]
    exact mul_ne_zero hη fun h ↦ hs' ((h𝔭 _).mpr h)
  refine isAnnulusAt_and_isSplitNodePt_of_isOrdinaryDoublePoint hϖ 𝔭 H hc₀ hxy hd hs'' hη' ?_ ?_
  · have : t * s' * x - t * η' * u' ^ d = algebraMap O B ϖ * z := by
      rw [← hz]; ring
    rw [this]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · rw [RingHom.mem_ker, hψ₂]; exact hy

/-- **The node lemma from branch data on a ring**: under the hypotheses of
`exists_node_of_branches`, `B` is étale-locally the node at `𝔭` (`IsAnnulusAt`). -/
theorem isAnnulusAt_of_branches_alg (𝔭 : Ideal B) [𝔭.IsPrime] (φ₁ : B →+* V₁) (φ₂ : B →+* V₂)
    (r₁ : V₁ →+* k) (r₂ : V₂ →+* k) (hr₁ : ∀ a, r₁ a = 0 ↔ a ∈ maximalIdeal V₁)
    (hr₂ : ∀ b, r₂ b = 0 ↔ b ∈ maximalIdeal V₂) (hcomp : ∀ b, r₁ (φ₁ b) = r₂ (φ₂ b))
    (h𝔭 : ∀ b, b ∈ 𝔭 ↔ r₁ (φ₁ b) = 0) {ϖ : O} (hϖ : Irreducible ϖ)
    (hϖ0 : algebraMap O B ϖ ≠ 0) (hϖ₁ : φ₁ (algebraMap O B ϖ) = 0)
    (hϖ₂ : φ₂ (algebraMap O B ϖ) = 0)
    (hker : ∀ b, φ₁ b = 0 → φ₂ b = 0 → ∃ t ∉ 𝔭, ∃ z, t * b = algebraMap O B ϖ * z)
    (hfp : ∀ a b, r₁ a = r₂ b → ∃ y s, s ∉ 𝔭 ∧ φ₁ y = a * φ₁ s ∧ φ₂ y = b * φ₂ s)
    (hO₁ : ∀ a : V₁, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₁ a)
    (hO₂ : ∀ b : V₂, ∃ o : O, r₁ (φ₁ (algebraMap O B o)) = r₂ b)
    {u' v' : B} (hu₁ : maximalIdeal V₁ = Ideal.span {φ₁ u'}) (hu₂ : φ₂ u' = 0)
    (hv₂ : maximalIdeal V₂ = Ideal.span {φ₂ v'}) (hv₁ : φ₁ v' = 0) (hu0 : φ₁ u' ≠ 0)
    (hv0 : φ₂ v' ≠ 0) {x y : B} {c₀ : O} (hc₀ : c₀ ≠ 0) (hxy : x * y = algebraMap O B c₀)
    {d : ℕ} (hd : 1 ≤ d) {η : V₁} (hη : r₁ η ≠ 0) (hx₁ : φ₁ x = η * φ₁ u' ^ d) (hx₂ : φ₂ x = 0)
    (hy : φ₂ y ≠ 0) :
    IsAnnulusAt ϖ x y d 𝔭 :=
  (isAnnulusAt_and_isSplitNodePt_of_branches_alg 𝔭 φ₁ φ₂ r₁ r₂ hr₁ hr₂ hcomp h𝔭 hϖ hϖ0 hϖ₁ hϖ₂
    hker hfp hO₁ hO₂ hu₁ hu₂ hv₂ hv₁ hu0 hv0 hc₀ hxy hd hη hx₁ hx₂ hy).1

/-- `isAnnulusAt_and_isSplitNodePt_of_branches_alg` for bundled branch data: split node. -/
theorem BranchData.isSplitNodePt {𝔭 : Ideal B} [𝔭.IsPrime] {φ₁ : B →+* V₁} {φ₂ : B →+* V₂}
    {r₁ : V₁ →+* k} {r₂ : V₂ →+* k} {ϖ : O} {u' v' x y : B} {c₀ : O} {d : ℕ}
    (h : BranchData 𝔭 φ₁ φ₂ r₁ r₂ ϖ u' v' x y c₀ d) : IsSplitNodePt ϖ 𝔭 := by
  obtain ⟨η, hη, hx₁⟩ := h.hx₁
  exact (isAnnulusAt_and_isSplitNodePt_of_branches_alg 𝔭 φ₁ φ₂ r₁ r₂ h.hr₁ h.hr₂ h.hcomp h.h𝔭
    h.hϖ h.hϖ0 h.hϖ₁ h.hϖ₂ h.hker h.hfp h.hO₁ h.hO₂ h.hu₁ h.hu₂ h.hv₂ h.hv₁ h.hu0 h.hv0 h.hc₀
    h.hxy h.hd hη hx₁ h.hx₂ h.hy).2

/-- `isAnnulusAt_of_branches_alg` for bundled branch data. -/
theorem BranchData.isAnnulusAt {𝔭 : Ideal B} [𝔭.IsPrime] {φ₁ : B →+* V₁} {φ₂ : B →+* V₂}
    {r₁ : V₁ →+* k} {r₂ : V₂ →+* k} {ϖ : O} {u' v' x y : B} {c₀ : O} {d : ℕ}
    (h : BranchData 𝔭 φ₁ φ₂ r₁ r₂ ϖ u' v' x y c₀ d) : IsAnnulusAt ϖ x y d 𝔭 := by
  obtain ⟨η, hη, hx₁⟩ := h.hx₁
  exact isAnnulusAt_of_branches_alg 𝔭 φ₁ φ₂ r₁ r₂ h.hr₁ h.hr₂ h.hcomp h.h𝔭 h.hϖ h.hϖ0 h.hϖ₁ h.hϖ₂
    h.hker h.hfp h.hO₁ h.hO₂ h.hu₁ h.hu₂ h.hv₂ h.hv₁ h.hu0 h.hv0 h.hc₀ h.hxy h.hd hη hx₁ h.hx₂
    h.hy

end Annulus

end SemistableReduction
