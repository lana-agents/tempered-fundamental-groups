/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleNil
import TemperedFundamentalGroups.SemistableReduction.AwayDvd

/-!
# The overlap of a node patch with an étale piece (Blueprint §12.8, M2.3 (f))

Setting (one level): a ring `R` with a nilpotent ideal `J`, elements `a, b ∈ R`; the node chart
`A = R[1/a]`; a patched algebra `G` over `A` whose localization away from the node function
`f ∈ A` is a formally étale `A`-algebra `P` (`fst : G → P`); a formally étale `R`-algebra `E` in
which `b` is a unit (the étale piece over `D(b)`), and `Bab = E[1/a]`. If `f` divides a power of
`b` in `A` (the overlap `D(a b)` misses the nodes) and a map of special fibres
`χ̄ : P/JP → Bab/J` is a localization away from `b`, then:

* `EtaleOverlap.κ : P → Bab`, the lift of `χ̄` (`EtaleNil.lift`), is a localization away from `b`
  (`EtaleNil.isLocalization_of_red`);
* **`EtaleOverlap.ρa = κ ∘ fst : G → Bab` is a localization away from `b`**
  (`isLocalization_ρa`; `AwayDvd.away_of_dvd`),

so `G` (on `D(a)`) and `E` (on `D(b)`) are glueing data along `Bab` (`ZariskiTwo.glued`).
-/

universe u

namespace SemistableReduction

namespace EtaleOverlap

noncomputable section

variable {R : Type u} [CommRing R] (J : Ideal R) {m : ℕ} (hJ : J ^ m = ⊥) (a b : R)
  {A : Type u} [CommRing A] [Algebra R A] [IsLocalization.Away a A]
  {P : Type u} [CommRing P] [Algebra A P] [Algebra R P] [IsScalarTower R A P]
  [Algebra.FormallyEtale A P]
  {E : Type u} [CommRing E] [Algebra R E]

/-- The overlap `Bab = E[1/a]`. -/
abbrev Bab (E : Type u) [CommRing E] [Algebra R E] : Type u := Localization.Away (algebraMap R E a)

variable (A) in
include a A in
lemma formallyEtale_P : Algebra.FormallyEtale R P := by
  haveI : Algebra.FormallyEtale R A := Algebra.FormallyEtale.of_isLocalization
    (Submonoid.powers a)
  exact Algebra.FormallyEtale.comp R A P

variable (χ : P ⧸ EtaleNil.JB J P →ₐ[R] Bab a E ⧸ EtaleNil.JB J (Bab a E))

variable (A) in
/-- **The lift `κ : P → Bab` of the special-fibre map `χ̄`.** -/
def κ : P →ₐ[R] Bab a E :=
  haveI := formallyEtale_P a A (P := P)
  EtaleNil.lift J hJ (χ.comp (Ideal.Quotient.mkₐ R _))

variable (A) in
lemma red_κ : EtaleNil.red J (κ J hJ a A χ) = χ := by
  haveI := formallyEtale_P a A (P := P)
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [EtaleNil.red_mk]
  exact EtaleNil.mk_lift J hJ _ x

variable [Algebra.FormallyEtale R E] (hb : IsUnit (algebraMap R E b))
  (hχ : letI := χ.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R (P ⧸ EtaleNil.JB J P) b) (Bab a E ⧸ EtaleNil.JB J (Bab a E)))

omit [Algebra.FormallyEtale R E] in
include hb in
lemma isUnit_b : IsUnit (algebraMap R (Bab a E) b) := by
  rw [IsScalarTower.algebraMap_apply R E (Bab a E)]
  exact hb.map _

variable (A) in
include hb hχ in
/-- **`κ` is a localization away from `b`.** -/
theorem isLocalization_κ :
    letI := (κ J hJ a A χ).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R P b) (Bab a E) := by
  haveI := formallyEtale_P a A (P := P)
  haveI : Algebra.FormallyEtale R (Bab a E) := Algebra.FormallyEtale.comp R E (Bab a E)
  refine EtaleNil.isLocalization_of_red J hJ b (κ J hJ a A χ) (isUnit_b a b hb) ?_
  rw [red_κ]
  exact hχ

variable {G : Type u} [CommRing G] [Algebra A G] [Algebra R G] [IsScalarTower R A G]
  (fst : G →ₐ[A] P) (f : A)
  (hfst : letI := fst.toRingHom.toAlgebra; IsLocalization.Away (algebraMap A G f) P)
  {k : ℕ} (hdiv : f ∣ algebraMap R A b ^ k)

/-- **The overlap map** `ρa = κ ∘ fst : G → Bab`. -/
def ρa : G →ₐ[R] Bab a E := (κ J hJ a A χ).comp (fst.restrictScalars R)

include hb hχ hfst hdiv in
/-- **`ρa : G → Bab` is a localization away from `b`.** -/
theorem isLocalization_ρa :
    letI := (ρa J hJ a χ fst).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap R G b) (Bab a E) := by
  letI : Algebra G P := fst.toRingHom.toAlgebra
  letI : Algebra P (Bab a E) := (κ J hJ a A χ).toRingHom.toAlgebra
  letI : Algebra G (Bab a E) := (ρa J hJ a χ fst).toRingHom.toAlgebra
  haveI : IsScalarTower G P (Bab a E) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsLocalization.Away (algebraMap A G f) P := hfst
  have hy : algebraMap G P (algebraMap R G b) = algebraMap R P b := by
    change fst (algebraMap R G b) = _
    rw [IsScalarTower.algebraMap_apply R A G, AlgHom.commutes,
      ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization.Away (algebraMap G P (algebraMap R G b)) (Bab a E) := by
    rw [hy]
    exact isLocalization_κ J hJ a b A χ hb hχ
  haveI := IsLocalization.Away.mul' P (Bab a E) (algebraMap A G f) (algebraMap R G b)
  refine AwayDvd.away_of_dvd (algebraMap A G f) (algebraMap R G b) k ?_
  rw [IsScalarTower.algebraMap_apply R A G, ← map_pow]
  exact map_dvd _ hdiv

end

end EtaleOverlap

end SemistableReduction
