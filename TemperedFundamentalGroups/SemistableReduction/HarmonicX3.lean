/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothPrime
import TemperedFundamentalGroups.SemistableReduction.NoLoopsPrimes

/-!
# (X3): nodes not over nodes map to points on exactly one component (Blueprint §9.7, XL10)

* `exists_mem_components`: every point of the special fibre lies on a component;
* `smooth_unique_component`: a smooth point lies on at most one component (`ϖ` is prime in its
  local ring, `isPrime_span_of_etale_polynomial`, so the minimal primes over `ϖ` below it
  coincide);
* `mem_Z_of_over`: points over the special fibre of the base lie in the special fibre.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction

section

variable {O : Type u} [CommRing O] [IsLocalRing O] {c : TemperedFundamentalGroups.ModelCode O}

/-- **Every point of the special fibre lies on a component.** -/
theorem exists_mem_components {p : c.scheme} (hp : p ∈ Z c) : ∃ v ∈ components c, p ∈ v := by
  obtain ⟨t, ht, hst, hmax⟩ := exists_preirreducible ({⟨p, hp⟩} : Set (Z c))
    isPreirreducible_singleton
  have hpt : (⟨p, hp⟩ : Z c) ∈ t := hst rfl
  have hirr : IsIrreducible t := ⟨⟨_, hpt⟩, ht⟩
  refine ⟨Subtype.val '' t, ⟨hirr.image _ continuous_subtype_val.continuousOn,
    fun _ ⟨q, _, hq⟩ ↦ hq ▸ q.2, fun w hw hwZ hsub ↦ ?_⟩, ⟨_, hpt, rfl⟩⟩
  have hpre : IsPreirreducible (Subtype.val ⁻¹' w : Set (Z c)) := by
    intro U₁ U₂ hU₁ hU₂ h₁ h₂
    obtain ⟨O₁, hO₁, rfl⟩ := isOpen_induced_iff.1 hU₁
    obtain ⟨O₂, hO₂, rfl⟩ := isOpen_induced_iff.1 hU₂
    obtain ⟨a, ha, ha₁⟩ := h₁
    obtain ⟨b, hb, hb₂⟩ := h₂
    obtain ⟨z, hzw, hz₁, hz₂⟩ := hw.2 O₁ O₂ hO₁ hO₂ ⟨a, ha, ha₁⟩ ⟨b, hb, hb₂⟩
    exact ⟨⟨z, hwZ hzw⟩, hzw, hz₁, hz₂⟩
  have hsub' : t ⊆ Subtype.val ⁻¹' w := fun q hq ↦ hsub ⟨q, hq, rfl⟩
  have := hmax _ hpre hsub'
  rw [← this]
  ext z
  exact ⟨fun hz ↦ ⟨⟨z, hwZ hz⟩, hz, rfl⟩, fun ⟨q, hq, hqz⟩ ↦ hqz ▸ hq⟩

end

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {c : TemperedFundamentalGroups.ModelCode O}

/-- **A smooth point lies on at most one component.** -/
theorem smooth_unique_component {ϖ : O} (hϖ : Irreducible ϖ) {p : c.scheme} (hpZ : p ∈ Z c)
    (hs : IsSmoothPt c p) {v w : Set c.scheme} (hv : v ∈ components c) (hw : w ∈ components c)
    (hpv : p ∈ v) (hpw : p ∈ w) : v = w := by
  by_contra hne
  obtain ⟨U, hU, hpU, hsm⟩ := hs
  letI := sectionsAlgebra c U
  obtain ⟨P₁, P₂, hp₁, hp₂, hϖ₁, hϖ₂, hle₁, hle₂, hmin₁, hmin₂, hP⟩ :=
    exists_minimal_primes_of_mem hϖ hv hw hne hpv hpw hU hpU
  set 𝔭 := (hU.primeIdealOf ⟨p, hpU⟩).asIdeal
  have hϖ𝔭 : algebraMap O Γ(c.scheme, U) ϖ ∈ 𝔭 := (mem_Z_iff hϖ hU hpU).1 hpZ
  have hprime := isPrime_span_of_etale_polynomial hϖ 𝔭 hϖ𝔭 hsm
  set D := Localization.AtPrime 𝔭
  set Q := (Ideal.span {algebraMap O D ϖ}).comap (algebraMap Γ(c.scheme, U) D)
  haveI : Q.IsPrime := Ideal.comap_isPrime _ _
  have hϖQ : algebraMap O Γ(c.scheme, U) ϖ ∈ Q := by
    rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact Ideal.mem_span_singleton_self _
  have hQle : ∀ P : Ideal Γ(c.scheme, U), P.IsPrime → P ≤ 𝔭 →
      algebraMap O Γ(c.scheme, U) ϖ ∈ P → Q ≤ P := by
    intro P hP hP𝔭 hϖP f hf
    have hdisj : Disjoint (𝔭.primeCompl : Set Γ(c.scheme, U)) P := by
      rw [Set.disjoint_left]; intro z hz hzP; exact hz (hP𝔭 hzP)
    rw [← IsLocalization.under_map_of_isPrime_disjoint 𝔭.primeCompl D hP hdisj]
    rw [Ideal.mem_comap] at hf ⊢
    refine Ideal.span_le.2 ?_ hf
    rintro _ rfl
    rw [IsScalarTower.algebraMap_apply O Γ(c.scheme, U) D]
    exact Ideal.mem_map_of_mem _ hϖP
  have h₁ := hmin₁ Q inferInstance hϖQ (hQle P₁ hp₁ hle₁ hϖ₁)
  have h₂ := hmin₂ Q inferInstance hϖQ (hQle P₂ hp₂ hle₂ hϖ₂)
  exact hP (h₁.symm.trans h₂)

/-- Restriction of a valuation subring to a base is a local homomorphism. -/
lemma isLocalHom_restrict {K K' : Type u} [Field K] [Field K'] [Algebra K K']
    {O₀ : ValuationSubring K} {O' : ValuationSubring K'} (h : O'.comap (algebraMap K K') = O₀) :
    IsLocalHom ((algebraMap K K').restrict O₀ O' (fun y hy ↦ by rw [← h] at hy; exact hy)) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨w, hw⟩ := ha.exists_right_inv
  have ha0 : (a : K) ≠ 0 := fun h0 ↦ by
    have := congrArg Subtype.val hw
    simp [RingHom.restrict, h0] at this
  have hinv : (a : K)⁻¹ ∈ O₀ := by
    have hmem : (a : K)⁻¹ ∈ O'.comap (algebraMap K K') := by
      rw [ValuationSubring.mem_comap, map_inv₀]
      have : algebraMap K K' (a : K) * (w : K') = 1 := congrArg Subtype.val hw
      rw [← eq_inv_of_mul_eq_one_right this]; exact w.2
    exact h ▸ hmem
  exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

/-- **Points over the special fibre of the base lie in the special fibre.** -/
theorem mem_Z_of_over {K K₁ K₂ : Type u} [Field K] [Field K₁] [Field K₂] [Algebra K K₁]
    [Algebra K K₂] {O₀ : ValuationSubring K} [IsDiscreteValuationRing O₀]
    {O₁ : ValuationSubring K₁} {O₂ : ValuationSubring K₂} [IsDiscreteValuationRing O₂]
    (h₁ : O₁.comap (algebraMap K K₁) = O₀) (h₂ : O₂.comap (algebraMap K K₂) = O₀)
    {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}
    {ψ : c.scheme ⟶ c'.scheme}
    (hψO : ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O₀ O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O₀ O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy)))) {y : c.scheme} (hy : y ∈ Z c) :
    ψ y ∈ Z c' := by
  haveI := isLocalHom_restrict h₁
  have e := congrArg (fun f ↦ f y) hψO
  simp only [Scheme.Hom.comp_apply] at e
  change c.toSpec y = closedPoint O₁ at hy
  rw [hy, Spec_closedPoint] at e
  change c'.toSpec (ψ y) = closedPoint O₂
  set q := c'.toSpec (ψ y)
  by_contra hq
  have hqb : q.asIdeal = ⊥ := by
    by_contra hne
    apply hq
    apply PrimeSpectrum.ext
    exact ((q.isPrime.isMaximal hne).eq_of_le (maximalIdeal.isMaximal O₂).ne_top
      (le_maximalIdeal q.isPrime.ne_top)).symm.symm ▸ rfl
  have e' := congrArg PrimeSpectrum.asIdeal e
  change Ideal.comap _ q.asIdeal = maximalIdeal O₀ at e'
  rw [hqb] at e'
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O₀
  have hm : ϖ₀ ∈ maximalIdeal O₀ := hϖ₀.not_isUnit
  rw [← e', Ideal.mem_comap, Ideal.mem_bot] at hm
  apply hϖ₀.ne_zero
  apply Subtype.ext
  have := congrArg Subtype.val hm
  simpa [RingHom.restrict] using this

/-- **(X3)**: a node not over a node maps to a point on exactly one component. -/
theorem x3 {K K₁ K₂ : Type u} [Field K] [Field K₁] [Field K₂] [Algebra K K₁]
    [Algebra K K₂] {O₀ : ValuationSubring K} [IsDiscreteValuationRing O₀]
    {O₁ : ValuationSubring K₁} {O₂ : ValuationSubring K₂} [IsDiscreteValuationRing O₂]
    (h₁ : O₁.comap (algebraMap K K₁) = O₀) (h₂ : O₂.comap (algebraMap K K₂) = O₀) {ϖ₂ : O₂}
    (hϖ₂ : Irreducible ϖ₂)
    {c : TemperedFundamentalGroups.ModelCode O₁} {c' : TemperedFundamentalGroups.ModelCode O₂}
    {ψ : c.scheme ⟶ c'.scheme}
    (hψO : ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O₀ O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O₀ O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy)))) :
    ∀ y : c.scheme, IsNodePt c y → ¬ IsNodePt c' (ψ y) →
      ∃! w', w' ∈ components c' ∧ ψ y ∈ w' := by
  intro y hy hny
  have hZ := mem_Z_of_over h₁ h₂ hψO hy.1
  have hs : IsSmoothPt c' (ψ y) := by
    by_contra h; exact hny ⟨hZ, h⟩
  obtain ⟨v, hv, hpv⟩ := exists_mem_components hZ
  exact ⟨v, ⟨hv, hpv⟩, fun w ⟨hw, hpw⟩ ↦
    (smooth_unique_component hϖ₂ hZ hs hv hw hpv hpw).symm⟩

end TemperedFundamentalGroups.SemistableReduction.ModelCode
