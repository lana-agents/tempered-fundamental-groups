/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Models.Projective
import FormalSchemes.ChartRingsOfAffineIso
import FormalSchemes.ChartAlgebraStructureMapAffine
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# From finite covers of models to chart algebras on `ℙ¹` (Blueprint §12.8, M2 step 4, bridge)

The algebraization step of M2 (Grothendieck existence, M2.4) is available in `formal-schemes`
only on the projective line: coherent chart modules/algebras on `ℙ¹_A`
(`ProjectiveLine.ChartModule.AdicChartAlgSystem.exists_algebraization`), their relative `Spec`
(`AlgStr.scheme`, `AlgStr.toP1`) and the converse construction for affine morphisms
`Y ⟶ ℙ¹_A` (`ProjectiveLine.algStrOfAffine`, `ProjectiveLine.relSpecIso`). This file connects the
projective models of this repository (`ModelCode`, closed subschemes of `ℙᵐ_R`) to it:

* `projSpace_one_eq`: the repository's `ℙ¹_R = projSpace R 1` *is* `ProjectiveLine.scheme R`
  (both are `Proj` of `R[x₀, x₁]` with the standard grading);
* `isProper_of_over`: any morphism `π : c.scheme ⟶ ℙ¹_R` over `Spec R` is proper (the model is
  proper and `ℙ¹_R` is separated over `R`);
* **`isFinite_of_locallyQuasiFinite`**: such a `π` is finite as soon as it is locally
  quasi-finite (Zariski's main theorem in Mathlib, `IsFinite.of_isProper_of_locallyQuasiFinite`;
  Stacks, Tag 02LS, as tagged in Mathlib's `IsFinite.iff_isProper_and_locallyQuasiFinite`);
* **`chartAlgebraOfFinite`**: along a finite `π : c.scheme ⟶ ℙ¹_R`, every finite morphism
  `g : 𝒴 ⟶ c.scheme` (a finite cover of the model) is the relative `Spec` of a chart algebra on
  `ℙ¹_R` (`relSpecIsoOfFinite`, lying over `ℙ¹_R`: `relSpecIsoOfFinite_hom_comp`).

So, for a model admitting a finite morphism to `ℙ¹` over the base, finite covers of the model are
exactly the objects the `formal-schemes` algebraization produces. What is still open for M2 step 4
is the existence of such a quasi-finite `π` for the models that occur (W-models: the composite of
the finite normalization map with a map from the Gauss-join model, which must be non-constant on
every component of the special fibre; the coordinate `x` itself contracts components).
-/

open AlgebraicGeometry CategoryTheory

universe u

namespace SemistableReduction

namespace ModelChartAlgebra

open TemperedFundamentalGroups

variable (R : Type u) [CommRing R]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The repository's `ℙ¹_R` is the projective line of `formal-schemes`.** -/
lemma projSpace_one_eq : projSpace R 1 = ProjectiveLine.scheme R := rfl

variable {R}

/-- **A morphism from a model to `ℙ¹` over the base is proper.** -/
lemma isProper_of_over (c : ModelCode R) (π : c.scheme ⟶ projSpace R 1)
    (hπ : π ≫ projSpace.toSpec R 1 = c.toSpec) : IsProper π := by
  have : IsProper (π ≫ projSpace.toSpec R 1) := hπ ▸ inferInstance
  exact IsProper.of_comp π (projSpace.toSpec R 1)

/-- **A locally quasi-finite morphism from a model to `ℙ¹` over the base is finite.** -/
lemma isFinite_of_locallyQuasiFinite (c : ModelCode R) (π : c.scheme ⟶ projSpace R 1)
    (hπ : π ≫ projSpace.toSpec R 1 = c.toSpec) [LocallyQuasiFinite π] : IsFinite π := by
  have := isProper_of_over c π hπ
  exact IsFinite.of_isProper_of_locallyQuasiFinite π

variable {c : ModelCode R} (π : c.scheme ⟶ ProjectiveLine.scheme R) [IsFinite π]
  {Y : Scheme.{u}} (g : Y ⟶ c.scheme) [IsFinite g]

instance : IsAffineHom (g ≫ π) := inferInstance

/-- **The chart algebra on `ℙ¹_R` of a finite cover `g : 𝒴 ⟶ c.scheme` along a finite
`π : c.scheme ⟶ ℙ¹_R`.** -/
noncomputable abbrev chartAlgebraOfFinite :=
  ProjectiveLine.algStrOfAffine (g ≫ π)

/-- The relative `Spec` of `chartAlgebraOfFinite π g` is `𝒴`. -/
noncomputable def relSpecIsoOfFinite : (chartAlgebraOfFinite π g).scheme ≅ Y :=
  ProjectiveLine.relSpecIso (g ≫ π)

/-- The identification lies over `ℙ¹_R`. -/
lemma relSpecIsoOfFinite_hom_comp :
    (relSpecIsoOfFinite π g).hom ≫ g ≫ π = (chartAlgebraOfFinite π g).toP1 :=
  ProjectiveLine.relSpecIso_hom_comp (g ≫ π)

end ModelChartAlgebra

end SemistableReduction
