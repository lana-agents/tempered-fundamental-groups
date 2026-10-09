/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeScheme

/-!
# Split node charts and their transfer between affine opens (W8′, XL1, H6 glue)

Blueprint §9.7 (XL1). `IsSplitNodeAt ϖ n 𝔭`: the `O`-algebra `A` is, at `𝔭`, étale-locally the
singular point of the node `O[u, v] ⧸ (u v - ϖ ^ n)`, through a chart point `𝔮` whose residue
field is that of `O` (the data of `ModelCode.HasSplitNodes`, at the singular point). It descends
along étale maps (`IsSplitNodeAt.of_comap`) and ascends to localizations away from elements
outside `𝔭` (`IsSplitNodeAt.away`), hence moves between affine neighbourhoods of a point.
-/

universe u

open IsLocalRing

namespace SemistableReduction

variable {O : Type u} [CommRing O]

/-- **A split node chart at `𝔭`.** -/
def IsSplitNodeAt (ϖ : O) (n : ℕ) {A : Type u} [CommRing A] [Algebra O A] (𝔭 : Ideal A) :
    Prop :=
  ∃ (C : Type u) (_ : CommRing C) (g : A →+* C) (f : Node O (ϖ ^ n) →+* C) (𝔮 : Ideal C),
    g.Etale ∧ f.Etale ∧ 𝔮.IsPrime ∧ 𝔮.comap g = 𝔭 ∧
      f.comp (algebraMap O _) = g.comp (algebraMap O A) ∧
      f (Node.u _) ∈ 𝔮 ∧ f (Node.v _) ∈ 𝔮 ∧
      Function.Surjective ((Ideal.Quotient.mk 𝔮).comp (g.comp (algebraMap O A)))

variable {ϖ : O} {n : ℕ} {A A' : Type u} [CommRing A] [Algebra O A] [CommRing A'] [Algebra O A']

/-- Split node charts descend along étale maps. -/
theorem IsSplitNodeAt.of_comap (φ : A →ₐ[O] A') (hφ : φ.toRingHom.Etale) {𝔭' : Ideal A'}
    (h : IsSplitNodeAt ϖ n 𝔭') : IsSplitNodeAt ϖ n (𝔭'.comap φ.toRingHom) := by
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp, hu, hv, hres⟩ := h
  have hφO : φ.toRingHom.comp (algebraMap O A) = algebraMap O A' := φ.comp_algebraMap
  refine ⟨C, inferInstance, g.comp φ.toRingHom, f, 𝔮,
    RingHom.Etale.stableUnderComposition _ _ hφ hg, hf, h𝔮, by rw [← Ideal.comap_comap, hcomap],
    ?_, hu, hv, ?_⟩
  · rw [hcomp, RingHom.comp_assoc, hφO]
  · rwa [RingHom.comp_assoc, hφO]

/-- Split node charts ascend to localizations away from elements outside the point. -/
theorem IsSplitNodeAt.away [IsDomain O] [IsDiscreteValuationRing O] (hϖ : Irreducible ϖ)
    [Algebra A A'] [IsScalarTower O A A'] (t : A) [IsLocalization.Away t A'] {𝔭 : Ideal A}
    [𝔭.IsPrime] (ht : t ∉ 𝔭) (h : IsSplitNodeAt ϖ n 𝔭) :
    IsSplitNodeAt ϖ n (𝔭.map (algebraMap A A')) := by
  classical
  obtain ⟨C, _, g, f, 𝔮, hg, hf, h𝔮, hcomap, hcomp, hu, hv, hres⟩ := h
  letI : Algebra A C := g.toAlgebra
  haveI : Algebra.Etale A C := RingHom.etale_algebraMap.mp hg
  let gt := g t
  let C' := Localization.Away gt
  have hgt : IsUnit (algebraMap A C' t) := by
    rw [IsScalarTower.algebraMap_apply A C C']
    exact IsLocalization.Away.algebraMap_isUnit gt
  let g' : A' →+* C' := IsLocalization.Away.lift t hgt
  have hg' : ∀ a, g' (algebraMap A A' a) = algebraMap A C' a := fun a ↦ IsLocalization.lift_eq _ a
  letI : Algebra A' C' := g'.toAlgebra
  haveI : IsScalarTower A A' C' := IsScalarTower.of_algebraMap_eq fun a ↦ (hg' a).symm
  haveI : Algebra.Etale A A' := Algebra.Etale.of_isLocalizationAway t
  haveI : Algebra.Etale C C' := Algebra.Etale.of_isLocalizationAway gt
  haveI : Algebra.Etale A C' := Algebra.Etale.comp A C C'
  haveI : Algebra.Etale A' C' := Algebra.Etale.of_restrictScalars A A' C'
  -- the chart point
  have hgt𝔮 : gt ∉ 𝔮 := fun hm ↦ ht (by rw [← hcomap]; exact hm)
  have hdisj : Disjoint (Submonoid.powers gt : Set C) 𝔮 := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ hk
    exact hgt𝔮 (h𝔮.mem_of_pow_mem k hk)
  let 𝔮' : Ideal C' := 𝔮.map (algebraMap C C')
  have h𝔮' : 𝔮'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers gt) C' 𝔮 h𝔮 hdisj
  have h𝔮'c : 𝔮'.comap (algebraMap C C') = 𝔮 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers gt) C' h𝔮 hdisj
  have hϖ𝔮 : g (algebraMap O A ϖ) ∈ 𝔮 := by
    have h1 : f (Node.u (ϖ ^ n) * Node.v (ϖ ^ n)) ∈ 𝔮 := by
      rw [map_mul]; exact Ideal.mul_mem_right _ _ hu
    rw [Node.u_mul_v, ← RingHom.comp_apply f, hcomp, RingHom.comp_apply, map_pow,
      map_pow] at h1
    exact h𝔮.mem_of_pow_mem _ h1
  refine ⟨C', inferInstance, g', (algebraMap C C').comp f, 𝔮', RingHom.etale_algebraMap.mpr
    inferInstance, RingHom.Etale.stableUnderComposition _ _ hf
      (RingHom.etale_algebraMap.mpr inferInstance), h𝔮', ?_, ?_,
    Ideal.mem_map_of_mem _ hu, Ideal.mem_map_of_mem _ hv, ?_⟩
  · -- contraction
    haveI : (𝔮'.comap g').IsPrime := Ideal.comap_isPrime _ _
    have hc : (𝔮'.comap g').comap (algebraMap A A') = 𝔭 := by
      rw [Ideal.comap_comap]
      change 𝔮'.comap (algebraMap A' C' |>.comp (algebraMap A A')) = 𝔭
      rw [← IsScalarTower.algebraMap_eq A A' C', IsScalarTower.algebraMap_eq A C C',
        ← Ideal.comap_comap, h𝔮'c]
      exact hcomap
    rw [← hc]
    exact (IsLocalization.map_under (Submonoid.powers t) A' _).symm
  · ext o
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [← RingHom.comp_apply f, hcomp, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply O A A', hg']
    rfl
  · -- residue field
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers gt) z
    simp only at hz
    obtain ⟨o₁, ho₁⟩ := hres (Ideal.Quotient.mk 𝔮 c)
    obtain ⟨o₂, ho₂⟩ := hres (Ideal.Quotient.mk 𝔮 gt)
    simp only [RingHom.coe_comp, Function.comp_apply] at ho₁ ho₂
    rw [Ideal.Quotient.eq] at ho₁ ho₂
    have ho₂u : IsUnit o₂ := by
      by_contra hnu
      have hm : o₂ ∈ maximalIdeal O := (mem_maximalIdeal o₂).mpr hnu
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ] at hm
      obtain ⟨o', rfl⟩ := Ideal.mem_span_singleton'.mp hm
      have h1 : g (algebraMap O A (o' * ϖ)) ∈ 𝔮 := by
        rw [map_mul, map_mul]; exact Ideal.mul_mem_left _ _ hϖ𝔮
      exact hgt𝔮 (by have := sub_mem h1 ho₂; simpa using this)
    set q := o₁ * ↑ho₂u.unit⁻¹ ^ k
    have hqo : q * o₂ ^ k = o₁ := by
      simp only [q]
      rw [mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one]
    refine ⟨q, ?_⟩
    simp only [RingHom.coe_comp, Function.comp_apply]
    rw [Ideal.Quotient.eq]
    have hq : g' (algebraMap O A' q) = algebraMap C C' (g (algebraMap O A q)) := by
      rw [IsScalarTower.algebraMap_apply O A A', hg', IsScalarTower.algebraMap_apply A C C']
      rfl
    rw [hq]
    have hdiff : c - g (algebraMap O A q) * gt ^ k ∈ 𝔮 := by
      have e : g (algebraMap O A q) * g (algebraMap O A o₂) ^ k = g (algebraMap O A o₁) := by
        rw [← map_pow, ← map_mul, ← map_pow, ← map_mul, hqo]
      have h3 : g (algebraMap O A o₂) ^ k - gt ^ k ∈ 𝔮 := by
        obtain ⟨w, hw⟩ := sub_dvd_pow_sub_pow (g (algebraMap O A o₂)) gt k
        rw [hw]; exact Ideal.mul_mem_right _ _ ho₂
      have : c - g (algebraMap O A q) * gt ^ k =
          -(g (algebraMap O A o₁) - c) + g (algebraMap O A q) *
            (g (algebraMap O A o₂) ^ k - gt ^ k) := by
        linear_combination -e
      rw [this]
      exact add_mem (neg_mem ho₁) (Ideal.mul_mem_left _ _ h3)
    have hunitk : IsUnit (algebraMap C C' gt ^ k) :=
      (IsLocalization.Away.algebraMap_isUnit gt).pow k
    have key : (z - algebraMap C C' (g (algebraMap O A q))) * algebraMap C C' gt ^ k ∈ 𝔮' := by
      have := Ideal.mem_map_of_mem (algebraMap C C') hdiff
      convert this using 1
      rw [map_sub, map_mul, map_pow, sub_mul, ← hz]
      simp
    have := Ideal.mul_mem_right (↑hunitk.unit⁻¹) _ key
    rw [mul_assoc, IsUnit.mul_val_inv, mul_one] at this
    rw [← neg_sub]; exact neg_mem this

end SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction CategoryTheory AlgebraicGeometry

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {c : TemperedFundamentalGroups.ModelCode O}

omit [IsDomain O] [IsDiscreteValuationRing O] in
/-- Membership in the prime of a point of an affine open is non-membership of the point in the
basic open. -/
lemma mem_primeIdealOf_iff {U : c.scheme.Opens} (hU : IsAffineOpen U) {y : c.scheme} (hy : y ∈ U)
    (b : Γ(c.scheme, U)) :
    b ∈ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ↔ y ∉ c.scheme.basicOpen b := by
  have h1 := hU.fromSpec_primeIdealOf ⟨y, hy⟩
  have h2 : hU.primeIdealOf ⟨y, hy⟩ ∈ PrimeSpectrum.basicOpen b ↔
      y ∈ c.scheme.basicOpen b := by
    rw [← hU.fromSpec_preimage_basicOpen]
    exact Iff.of_eq (congrArg (· ∈ c.scheme.basicOpen b) h1)
  exact ⟨fun hb hm ↦ (PrimeSpectrum.mem_basicOpen _ _).mp (h2.mpr hm) hb,
    fun hn ↦ by_contra fun hb ↦ hn (h2.mp ((PrimeSpectrum.mem_basicOpen _ _).mpr hb))⟩

/-- **Split node charts do not depend on the affine neighbourhood.** -/
theorem isSplitNodeAt_transfer {ϖ : O} (hϖ : Irreducible ϖ) {n : ℕ} {x : c.scheme}
    {U U' : c.scheme.Opens} (hU : IsAffineOpen U) (hU' : IsAffineOpen U') (hx : x ∈ U)
    (hx' : x ∈ U')
    (h : letI := sectionsAlgebra c U'
      IsSplitNodeAt ϖ n (hU'.primeIdealOf ⟨x, hx'⟩).asIdeal) :
    letI := sectionsAlgebra c U
    IsSplitNodeAt ϖ n (hU.primeIdealOf ⟨x, hx⟩).asIdeal := by
  obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter hU hU' x ⟨hx, hx'⟩
  set V := c.scheme.basicOpen g
  have hV : IsAffineOpen V := hU'.basicOpen g
  have hxV : x ∈ V := e ▸ hxf
  have hVU : V ≤ U := e ▸ c.scheme.basicOpen_le f
  have hVU' : V ≤ U' := c.scheme.basicOpen_le g
  letI := sectionsAlgebra c U
  letI := sectionsAlgebra c U'
  letI := sectionsAlgebra c V
  -- ascend from `Γ(U')` to `Γ(V) = Γ(U')[1/g]`
  letI : Algebra Γ(c.scheme, U') Γ(c.scheme, V) := (restrictAlgHom c hVU').toRingHom.toAlgebra
  haveI : IsScalarTower O Γ(c.scheme, U') Γ(c.scheme, V) :=
    IsScalarTower.of_algebraMap_eq fun o ↦ ((restrictAlgHom c hVU').commutes o).symm
  haveI : IsLocalization.Away g Γ(c.scheme, V) := hU'.isLocalization_basicOpen g
  have hg : g ∉ (hU'.primeIdealOf ⟨x, hx'⟩).asIdeal := by
    rw [mem_primeIdealOf_iff]; exact not_not.mpr hxV
  have h₁ := h.away (A' := Γ(c.scheme, V)) hϖ g hg
  have hmap : (hU'.primeIdealOf ⟨x, hx'⟩).asIdeal.map
      (algebraMap Γ(c.scheme, U') Γ(c.scheme, V)) = (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    rw [← comap_primeIdealOf_restrict hU' hV hVU' hxV]
    exact IsLocalization.map_under (Submonoid.powers g) _ _
  rw [hmap] at h₁
  -- descend from `Γ(V)` to `Γ(U)`
  have h₂ := h₁.of_comap (restrictAlgHom c hVU) (restrict_etale hU f e.symm hVU)
  rwa [restrictAlgHom_toRingHom, comap_primeIdealOf_restrict hU hV hVU hxV] at h₂

end TemperedFundamentalGroups.SemistableReduction.ModelCode
