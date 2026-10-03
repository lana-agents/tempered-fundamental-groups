/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.LocalModel
import TemperedFundamentalGroups.Models.Specialization
import TemperedFundamentalGroups.Models.Projective

/-!
# Dual graphs of semistable models (W8′, definitions)

For a projective model `c` over a local ring `O` with uniformizer `ϖ` (`ModelCode O`), the
**metrized dual graph** of its special fibre `Z = specialFibre c.toSpec` is read off directly on
`Z` (Blueprint §9.7, §10.3):

* **vertices** are the irreducible components of `Z` (`ModelCode.components`): maximal irreducible
  subsets of `Z`;
* **edges** are the **node points** (`ModelCode.IsNodePt`): points of `Z` at which `c` is not
  étale-locally the affine line `O[u]`; in a semistable model these are exactly the points that
  are étale-locally the singular point of a node `O[u, v] ⧸ (u v - ϖ ^ n)`, `n ≥ 1`
  (`ModelCode.IsNodeOfThickness`);
* **lengths**: a node point of thickness `n` has length `n / e(O/O₀)` over a base `O₀`; we only
  use the integer thickness `n`;
* **incidence**: a node point `x` lies on the component `v` iff `x ∈ v` (self-loops allowed).

The Zariski-model version (for W5's `ZariskiModel`, where the proofs live) is in
`SemistableReduction/ZariskiDualGraph.lean`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

variable {O : Type u} [CommRing O]

/-- The `O`-algebra structure on the sections of a model over an open. -/
noncomputable abbrev sectionsAlgebra (c : TemperedFundamentalGroups.ModelCode O)
    (U : c.scheme.Opens) : Algebra O Γ(c.scheme, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ c.toSpec.appTop ≫
    c.scheme.presheaf.map (homOfLE le_top).op).hom.toAlgebra

/-- `c` is **étale-locally `M` at the point `x`**: some affine open neighbourhood `U` of `x` has
sections étale-locally isomorphic to the `O`-algebra `M` at the prime of `x`. -/
def IsEtaleLocallyAtPt (M : Type u) [CommRing M] [Algebra O M]
    (c : TemperedFundamentalGroups.ModelCode O) (x : c.scheme) : Prop :=
  ∃ (U : c.scheme.Opens) (hU : IsAffineOpen U) (hx : x ∈ U),
    letI := sectionsAlgebra c U
    _root_.SemistableReduction.IsEtaleLocallyAt O M (hU.primeIdealOf ⟨x, hx⟩).asIdeal

/-- `x` is a **smooth point** of `c` over `O`: étale-locally the affine line `O[u]`. -/
def IsSmoothPt (c : TemperedFundamentalGroups.ModelCode O) (x : c.scheme) : Prop :=
  IsEtaleLocallyAtPt (Polynomial O) c x

variable [IsLocalRing O]

/-- The special fibre of a model. -/
abbrev Z (c : TemperedFundamentalGroups.ModelCode O) : Set c.scheme :=
  specialFibre c.toSpec

/-- The **vertices** of the dual graph: the irreducible components of the special fibre. -/
def components (c : TemperedFundamentalGroups.ModelCode O) : Set (Set c.scheme) :=
  {v | IsIrreducible v ∧ v ⊆ Z c ∧ ∀ w, IsIrreducible w → w ⊆ Z c → v ⊆ w → w = v}

/-- The **edges** of the dual graph: points of the special fibre which are not smooth. -/
def IsNodePt (c : TemperedFundamentalGroups.ModelCode O) (x : c.scheme) : Prop :=
  x ∈ Z c ∧ ¬ IsSmoothPt c x

/-- A **node point of thickness `n`**: a node point which is étale-locally the node
`O[u, v] ⧸ (u v - ϖ ^ n)`. -/
def IsNodeOfThickness (ϖ : O) (c : TemperedFundamentalGroups.ModelCode O) (x : c.scheme)
    (n : ℕ) : Prop :=
  IsNodePt c x ∧ IsEtaleLocallyAtPt (_root_.SemistableReduction.Node O (ϖ ^ n)) c x

end TemperedFundamentalGroups.SemistableReduction.ModelCode
