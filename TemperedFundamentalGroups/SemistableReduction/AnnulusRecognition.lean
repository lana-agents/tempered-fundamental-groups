/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.BranchRecognition
import TemperedFundamentalGroups.SemistableReduction.NodeLemma

/-!
# Annuli from the branches of the special fibre over a DVR

Blueprint §9.10, L3 (a2) (input of R4 and S10). Let `O` be a DVR with uniformizer `ϖ`, `B` a
normal domain of finite type over `O` (a chart of the normalization of a base node chart
`x y = c₀`) and `𝔭` a prime of `B`. If the special fibre at `𝔭` has two reduced branches `𝔔₁, 𝔔₂`
with finite normalizations in which `u'`, `v'` are uniformizers (R2,
`BranchRecognition.isOrdinaryDoublePoint_of_branches`), `u' v' ∈ (ϖ)`, the residue field at `𝔭`
is that of `O`, and the base coordinate has order `d` on the outer branch, then `B` is an annulus
over the base node at `𝔭` (`IsAnnulusAt`, the node lemma S9,
`isAnnulusAt_of_isOrdinaryDoublePoint`): `isAnnulusAt_of_branches`.
-/

open IsLocalRing

namespace SemistableReduction

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {B : Type u} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra O B]
  [Algebra.FiniteType O B] [FaithfulSMul O B]

/-- **Annulus recognition over a DVR** (R2 + S9): two reduced branches at `𝔭` with finite
normalizations in which `u'`, `v'` are uniformizers, `u' v' ∈ (ϖ)`, residue field that of `O`,
and the base coordinate `x` of order `d` on the outer branch (`s x ≡ η u'^d` modulo `(ϖ, v')`),
`y = c₀ / x` a unit on the inner branch ⇒ `B` is an annulus over the base node at `𝔭`. -/
theorem isAnnulusAt_of_branches {ϖ : O} (hϖ : Irreducible ϖ) (𝔭 : Ideal B) [𝔭.IsPrime]
    {𝔔₁ 𝔔₂ : Ideal (Localization.AtPrime 𝔭)} [𝔔₁.IsPrime] [𝔔₂.IsPrime]
    (hmem₁ : algebraMap O (Localization.AtPrime 𝔭) ϖ ∈ 𝔔₁)
    (hmem₂ : algebraMap O (Localization.AtPrime 𝔭) ϖ ∈ 𝔔₂)
    (hred₁ : ∀ z ∈ 𝔔₁, ∃ s ∉ 𝔔₁,
      s * z ∈ Ideal.span {algebraMap O (Localization.AtPrime 𝔭) ϖ})
    (hred₂ : ∀ z ∈ 𝔔₂, ∃ s ∉ 𝔔₂,
      s * z ∈ Ideal.span {algebraMap O (Localization.AtPrime 𝔭) ϖ})
    (hbr : ∀ 𝔮 : Ideal (Localization.AtPrime 𝔭), 𝔮.IsPrime →
      algebraMap O (Localization.AtPrime 𝔭) ϖ ∈ 𝔮 → 𝔔₁ ≤ 𝔮 ∨ 𝔔₂ ≤ 𝔮)
    (hresO : ∀ z : Localization.AtPrime 𝔭, ∃ o : O,
      z - algebraMap O (Localization.AtPrime 𝔭) o ∈ maximalIdeal (Localization.AtPrime 𝔭))
    {u' v' : B}
    (huv : algebraMap B (Localization.AtPrime 𝔭) u' * algebraMap B (Localization.AtPrime 𝔭) v' ∈
      Ideal.span {algebraMap O (Localization.AtPrime 𝔭) ϖ})
    (hu₁ : algebraMap B (Localization.AtPrime 𝔭) u' ∉ 𝔔₁)
    (hv₂ : algebraMap B (Localization.AtPrime 𝔭) v' ∉ 𝔔₂)
    {V₁ : Type*} [CommRing V₁] [Algebra (Localization.AtPrime 𝔭) V₁]
    [Module.Finite (Localization.AtPrime 𝔭) V₁]
    (hker₁ : RingHom.ker (algebraMap (Localization.AtPrime 𝔭) V₁) = 𝔔₁)
    (hres₁ : ∀ w : V₁, ∃ d : Localization.AtPrime 𝔭, w - algebraMap _ V₁ d ∈
      Ideal.span {algebraMap _ V₁ (algebraMap B (Localization.AtPrime 𝔭) u')})
    (hloc₁ : ∀ z ∈ maximalIdeal (Localization.AtPrime 𝔭), algebraMap _ V₁ z ∈
      Ideal.span {algebraMap _ V₁ (algebraMap B (Localization.AtPrime 𝔭) u')})
    {V₂ : Type*} [CommRing V₂] [Algebra (Localization.AtPrime 𝔭) V₂]
    [Module.Finite (Localization.AtPrime 𝔭) V₂]
    (hker₂ : RingHom.ker (algebraMap (Localization.AtPrime 𝔭) V₂) = 𝔔₂)
    (hres₂ : ∀ w : V₂, ∃ d : Localization.AtPrime 𝔭, w - algebraMap _ V₂ d ∈
      Ideal.span {algebraMap _ V₂ (algebraMap B (Localization.AtPrime 𝔭) v')})
    (hloc₂ : ∀ z ∈ maximalIdeal (Localization.AtPrime 𝔭), algebraMap _ V₂ z ∈
      Ideal.span {algebraMap _ V₂ (algebraMap B (Localization.AtPrime 𝔭) v')})
    {x y : B} {c₀ : O} (hc₀ : c₀ ≠ 0) (hxy : x * y = algebraMap O B c₀) {d : ℕ} (hd : 1 ≤ d)
    {s η : B} (hs : s ∉ 𝔭) (hη : η ∉ 𝔭)
    (hx : s * x - η * u' ^ d ∈ Ideal.span {algebraMap O B ϖ, v'})
    (hy : algebraMap B (Localization.AtPrime 𝔭) y ∉ 𝔔₂) :
    IsAnnulusAt ϖ x y d 𝔭 := by
  let D := Localization.AtPrime 𝔭
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  haveI : IsNoetherianRing D := IsLocalization.isNoetherianRing 𝔭.primeCompl D inferInstance
  haveI : IsIntegrallyClosed D :=
    isIntegrallyClosed_of_isLocalization D 𝔭.primeCompl 𝔭.primeCompl_le_nonZeroDivisors
  have hιD : Function.Injective (algebraMap B D) :=
    IsLocalization.injective D 𝔭.primeCompl_le_nonZeroDivisors
  have hOB : Function.Injective (algebraMap O B) := FaithfulSMul.algebraMap_injective O B
  have hϖ0 : algebraMap O D ϖ ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply O B D]
    exact fun h ↦ hϖ.ne_zero (hOB (hιD (by rw [h, map_zero, map_zero])))
  exact isAnnulusAt_of_isOrdinaryDoublePoint hϖ 𝔭
    (BranchRecognition.isOrdinaryDoublePoint_of_branches hϖ0 hmem₁ hmem₂ hred₁ hred₂ hbr hresO
      huv hu₁ hv₂ hker₁ hres₁ hloc₁ hker₂ hres₂ hloc₂) hc₀ hxy hd hs hη hx hy

end SemistableReduction
