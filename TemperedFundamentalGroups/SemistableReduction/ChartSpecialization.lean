/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Models.Specialization
import TemperedFundamentalGroups.SemistableReduction.ZariskiModel

/-!
# Specialization through an affine chart

Blueprint §9.6 (W5), layer M3: compatibility of the valuation-theoretic specialization of Zariski
models (`ZariskiModel.center`) with the scheme-theoretic one (`Models/Specialization.lean`).

* `sp_eq_of_chart`: let `f : X ⟶ Spec O` be universally closed and separated, and
  `ι : Spec A ⟶ X` a morphism over `Spec O` (e.g. an affine open chart). If an `Ω`-point of `X`
  factors through `ι` via `φ : A → V ⊆ Ω`, its specialization is `ι` of the point
  `φ⁻¹(𝔪_V)` of `Spec A`.
* `asIdeal_comap_closedPoint`: for a chart `A ⊆ F` of a Zariski model and a field embedding
  `j : F → Ω` with `A ⊆ W := j⁻¹(V)`, the point `φ⁻¹(𝔪_V)` is the center `𝔪_W ∩ A` of `W`,
  whose local ring is `localAt A W` (`localAt_eq_localSubringOfPrime`). So on a scheme glued from
  the charts of a Zariski model, the specialization of the `Ω`-point `F → Ω` is the point with
  local ring `ZariskiModel.center W`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace SemistableReduction

open TemperedFundamentalGroups

section Scheme

variable {K : Type u} [Field K] {O : ValuationSubring K}
variable {Ω : Type u} [Field Ω] [Algebra K Ω] {V : ValuationSubring Ω}
  {hV : V.comap (algebraMap K Ω) = O} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of O)}

lemma chart_point_comp {A : Type u} [CommRing A] (ψ : O →+* A)
    (ι : Spec (CommRingCat.of A) ⟶ X) (hι : ι ≫ f = Spec.map (CommRingCat.ofHom ψ))
    (φ : A →+* V) (hφ : φ.comp ψ = valToVal O V hV) :
    (Spec.map (CommRingCat.ofHom ((algebraMap V Ω).comp φ)) ≫ ι) ≫ f =
      Spec.map (CommRingCat.ofHom (valToField O)) := by
  rw [Category.assoc, hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.comp_assoc, hφ,
    valToVal_comp_algebraMap]

/-- **Specialization through a chart.** If an `Ω`-point of `X` factors through `ι : Spec A ⟶ X`
(over `Spec O`) via `φ : A → V`, its specialization is `ι (φ⁻¹ 𝔪_V)`. -/
theorem sp_eq_of_chart [UniversallyClosed f] [IsSeparated f] {A : Type u} [CommRing A]
    (ψ : O →+* A) (ι : Spec (CommRingCat.of A) ⟶ X)
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom ψ)) (φ : A →+* V)
    (hφ : φ.comp ψ = valToVal O V hV) :
    (sp f V hV (Spec.map (CommRingCat.ofHom ((algebraMap V Ω).comp φ)) ≫ ι)
      (chart_point_comp ψ ι hι φ hφ) : X) = ι (PrimeSpectrum.comap φ (closedPoint V)) := by
  rw [sp_eq_of_lift _ _ (Spec.map (CommRingCat.ofHom φ) ≫ ι)]
  · rfl
  · rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  · rw [Category.assoc, hι, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ]

end Scheme

section Chart

variable {F Ω : Type*} [Field F] [Field Ω] (j : F →+* Ω) (V : ValuationSubring Ω)

/-- The map `A → V` induced by `j : F → Ω`, for a chart `A ⊆ j⁻¹(V)`. -/
def chartToVal (A : Subring F) (h : A ≤ (V.comap j).toSubring) : A →+* V :=
  (j.comp A.subtype).codRestrict V.toSubring fun a ↦ h a.2

lemma mem_maximalIdeal_comap_iff {x : F} (hx : x ∈ V.comap j) :
    (⟨x, hx⟩ : V.comap j) ∈ maximalIdeal (V.comap j) ↔
      (⟨j x, hx⟩ : V) ∈ maximalIdeal V := by
  rw [← ValuationSubring.coe_mem_nonunits_iff, ← ValuationSubring.coe_mem_nonunits_iff,
    ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  simp [ValuationSubring.mem_comap]

/-- The point `φ⁻¹(𝔪_V)` of a chart `A ⊆ W = j⁻¹(V)` is the center `𝔪_W ∩ A` of `W`. -/
theorem asIdeal_comap_closedPoint (A : Subring F) (h : A ≤ (V.comap j).toSubring) :
    (PrimeSpectrum.comap (chartToVal j V A h) (closedPoint V)).asIdeal =
      centerIdeal A (V.comap j) h := by
  ext a
  change chartToVal j V A h a ∈ maximalIdeal V ↔
    Subring.inclusion h a ∈ maximalIdeal (V.comap j)
  exact (mem_maximalIdeal_comap_iff j V (h a.2)).symm

end Chart

end SemistableReduction
