/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussDescent

/-!
# Function fields defined over a complete discretely valued subfield

Blueprint §9.10, R4 (setting of the descent (a1)). For a non-archimedean field `C` and a finite
extension `F' / C(x)`, `DefinedOverDVR C F'` says that `F'` comes from a function field over a
complete discretely valued subfield `K ⊆ C` over which `C` is algebraic, and that every finite
subset of `C` lies in a finitely generated (hence finite) complete discretely valued extension
`E ⊇ K` inside `C` (the W9 setting: `C` an algebraic closure of a complete discretely valued
field of characteristic `0`):

* there are `K`, and a primitive element `θ` of `F' / C(x)` whose minimal polynomial has
  coefficients in `K(x)` (`ratFuncMap K → C`), so that `F' = K(x)(θ) ⊗_{K(x)} C(x)`;
* for every finite `S ⊆ C` there is `E = K(T)` (`T` finite) containing `S`, complete with
  discrete valuation ring of integers.

The descent of the C-level ordinary double points (`GaussTube.IsNodeODP`) to such `E` and the
exact node data (`GaussTube.NodeData`) are §9.10 L3 (a1) (in progress elsewhere).
-/

namespace SemistableReduction

universe u

/-- The integers of a subfield `E ⊆ C` (for the restriction of the norm of `C`) form a complete
discrete valuation ring. -/
def IsCompleteDVRSubfield {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C]
    (E : Subfield C) : Prop :=
  IsDiscreteValuationRing ((NormedField.valuation (K := C)).comap E.subtype).valuationSubring ∧
    IsComplete (E : Set C)

/-- **`F'` is defined over a complete discretely valued subfield of `C`**, and `C` is exhausted
by finitely generated complete discretely valued extensions of it. -/
def DefinedOverDVR (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] (F' : Type*)
    [Field F'] [Algebra (RatFunc C) F'] : Prop :=
  ∃ K : Subfield C, IsCompleteDVRSubfield K ∧ Algebra.IsAlgebraic K C ∧
    (∀ S : Finset C, ∃ T : Finset C, (∀ s ∈ S, s ∈ Subfield.closure ((K : Set C) ∪ T)) ∧
      IsCompleteDVRSubfield (Subfield.closure ((K : Set C) ∪ T))) ∧
    ∃ θ : F', Algebra.adjoin (RatFunc C) {θ} = ⊤ ∧
      ∀ i, (minpoly (RatFunc C) θ).coeff i ∈ (ratFuncMap K.subtype).range

end SemistableReduction
