/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ModelBase
import TemperedFundamentalGroups.SemistableReduction.SmoothPrime
import TemperedFundamentalGroups.SemistableReduction.NoLoopsPrimes

/-!
# Points of W-models (Blueprint §10.3.8, CrossingX1, CX4)

For a W-model `c` of `L` with generic point `j`:

* `specializes_of_isWModel`: every point is a specialization of the generic point;
* `stalkTo_injective`: the stalk maps to `L` are injective;
* `baseHom_eq_of_isWModel`: the base map is the algebra map `O' → L`;
* `exists_eq_unit_mul_pow_of_smooth`: at a smooth point of the special fibre every divisor of a
  power of `ϖ` among the germs is a unit times a power of `ϖ` (`ϖ` is prime there).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CentreGerms

open ModelCode

variable {K' L : Type u} [Field K'] [Field L] [Algebra K' L] {O' : ValuationSubring K'}
  [Algebra O' L] [IsScalarTower O' K' L] {x : L} {c : TemperedFundamentalGroups.ModelCode O'}
  {j : Spec (CommRingCat.of L) ⟶ c.scheme}

/-- **W-models are dominated by their generic point.** -/
theorem specializes_of_isWModel (hW : IsWModel O' L x c j) (z : c.scheme) :
    j (closedPoint L) ⤳ z := by
  obtain ⟨U, hU, hzU, h, hinj, -⟩ := exists_wChart hW z
  rw [specializes_iff_forall_open]
  intro V hV hzV
  obtain ⟨f, hfV, hzf⟩ := hU.exists_basicOpen_le ⟨z, (show z ∈ (⟨V, hV⟩ : c.scheme.Opens) from hzV)⟩
    hzU
  have hf0 : toL j h f ≠ 0 := by
    intro h0
    have : f = 0 := hinj (by rw [h0, ← toLHom_apply, map_zero])
    rw [this, Scheme.basicOpen_zero] at hzf
    exact hzf
  have := top_le_preimage_basicOpen j h f hf0 (Set.mem_univ (closedPoint L))
  exact hfV this

/-- **The stalk maps of a W-model are injective.** -/
theorem stalkTo_injective (hW : IsWModel O' L x c j) (z : c.scheme) :
    Function.Injective (stalkTo j (specializes_of_isWModel hW z)).hom := by
  obtain ⟨U, hU, hzU, h, hinj, -⟩ := exists_wChart hW z
  letI := c.scheme.presheaf.algebra_section_stalk ⟨z, hzU⟩
  haveI := hU.isLocalization_stalk ⟨z, hzU⟩
  refine (IsLocalization.injective_of_map_algebraMap_zero
    (M := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal.primeCompl) (S := c.scheme.presheaf.stalk z)
    (stalkTo j (specializes_of_isWModel hW z)).hom ?_)
  intro a ha
  change (stalkTo j _).hom (c.scheme.presheaf.germ U z hzU a) = 0 at ha
  rw [stalkTo_germ] at ha
  have : a = 0 := hinj (by rw [toL, ha, ← toLHom_apply, map_zero])
  rw [this, map_zero]

/-- **The base map of a W-model is the algebra map.** -/
theorem baseHom_eq_of_isWModel (hW : IsWModel O' L x c j) (o : O') :
    baseHom c j o = algebraMap O' L o := by
  obtain ⟨U, -, -, h, -, -, hO, -⟩ := exists_wChart hW (j (closedPoint L))
  letI := sectionsAlgebra c U
  rw [baseHom_eq_toL c j h, hO]

variable [IsDiscreteValuationRing O']

/-- **Divisors at smooth points.** -/
theorem exists_eq_unit_mul_pow_of_smooth (hW : IsWModel O' L x c j) {ϖ : O'}
    (hϖ : Irreducible ϖ) {z : c.scheme} (hz : z ∈ Z c) (hs : IsSmoothPt c z) {t : L}
    (ht : t ∈ germs c j z) {m : ℕ} (hr : ∃ r ∈ germs c j z, t * r = algebraMap O' L ϖ ^ m) :
    ∃ ε ∈ germs c j z, ε⁻¹ ∈ germs c j z ∧ ∃ α : ℕ, t = ε * algebraMap O' L ϖ ^ α := by
  have h := specializes_of_isWModel hW z
  set f₀ := (stalkTo j h).hom
  have hinj : Function.Injective f₀ := stalkTo_injective hW z
  haveI : IsDomain (c.scheme.presheaf.stalk z) := hinj.isDomain f₀
  -- the smooth chart
  obtain ⟨U, hU, hzU, hsm⟩ := hs
  letI := sectionsAlgebra c U
  letI := c.scheme.presheaf.algebra_section_stalk ⟨z, hzU⟩
  haveI := hU.isLocalization_stalk ⟨z, hzU⟩
  set 𝔭 := (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
  have hϖ𝔭 : algebraMap O' Γ(c.scheme, U) ϖ ∈ 𝔭 := (mem_Z_iff hϖ hU hzU).1 hz
  have hprime := _root_.SemistableReduction.isPrime_span_of_etale_polynomial hϖ 𝔭 hϖ𝔭 hsm
  -- transfer to the stalk
  let e : Localization.AtPrime 𝔭 ≃ₐ[Γ(c.scheme, U)] c.scheme.presheaf.stalk z :=
    IsLocalization.algEquiv 𝔭.primeCompl _ _
  set ϖS : c.scheme.presheaf.stalk z := algebraMap Γ(c.scheme, U) _ (algebraMap O' _ ϖ)
  have heϖ : e (algebraMap O' (Localization.AtPrime 𝔭) ϖ) = ϖS := by
    rw [IsScalarTower.algebraMap_apply O' Γ(c.scheme, U) (Localization.AtPrime 𝔭),
      AlgEquiv.commutes]
  have hprimeS : (Ideal.span {ϖS}).IsPrime := by
    have := Ideal.map_isPrime_of_equiv (f := e.toRingEquiv) (I := Ideal.span {algebraMap O' _ ϖ})
    rw [Ideal.map_span, Set.image_singleton] at this
    change (Ideal.span {e _}).IsPrime at this
    rwa [heϖ] at this
  have hf₀ϖ : f₀ ϖS = algebraMap O' L ϖ := by
    change (stalkTo j h).hom (c.scheme.presheaf.germ U z hzU _) = _
    rw [stalkTo_germ, ← toL, ← baseHom_eq_toL c j, baseHom_eq_of_isWModel hW]
  have hϖ0 : ϖS ≠ 0 := fun h0 ↦ by
    have := congrArg f₀ h0
    rw [hf₀ϖ, map_zero, IsScalarTower.algebraMap_apply O' K' L,
      map_eq_zero_iff _ (algebraMap K' L).injective] at this
    exact hϖ.ne_zero (Subtype.ext this)
  have hpS : Prime ϖS := (Ideal.span_singleton_prime hϖ0).1 hprimeS
  -- the divisor
  rw [germs_eq_range c j h] at ht hr ⊢
  obtain ⟨s, rfl⟩ := ht
  obtain ⟨_, ⟨s', rfl⟩, hss'⟩ := hr
  have hss : s * s' = ϖS ^ m := hinj (by rw [map_mul, hss', map_pow, hf₀ϖ])
  obtain ⟨ε, α, rfl⟩ := _root_.SemistableReduction.eq_unit_mul_pow_of_prime hpS hss
  refine ⟨f₀ ε, ⟨_, rfl⟩, ⟨↑ε⁻¹, ?_⟩, α, by rw [map_mul, map_pow, hf₀ϖ]⟩
  have h1 : f₀ ↑ε⁻¹ * f₀ ↑ε = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  first
  | exact (eq_inv_of_mul_eq_one_left h1).symm
  | exact eq_inv_of_mul_eq_one_left h1

end TemperedFundamentalGroups.SemistableReduction.CentreGerms
