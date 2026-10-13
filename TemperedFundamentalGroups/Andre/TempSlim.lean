/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.CurveTower
import TemperedFundamentalGroups.Andre.TateObjectDouble
import TemperedFundamentalGroups.Andre.TheoremAFinal
import TemperedFundamentalGroups.SemiAnbd.TempSlim

/-!
# Temp-slimness of the tempered fundamental group of a curve (Blueprint §12.9)

Scheme case (`A` trivial), under the hypotheses of Theorem A. [Mzk14], Example 3.10 proves that
the tempered fundamental group `Π^tp_X` of a hyperbolic curve over a `p`-adic field is temp-slim
(`TempSlim`: every open subgroup has trivial centralizer) by the following argument, which is
formalized here for André's tree tower `andreTower` on `andreGroup ≅ temperedPi1`:

1. a verticial subgroup `Π_v = stab s` (the decomposition group of a compatible system of
   components) is compact (`isCompact_stab_andreTower`);
2. it is commensurably terminal when edge-like subgroups have infinite index in it (`HI s`,
   `TreeTower.commensurator_stab`);
3. it is slim (as a profinite group: every open subgroup has trivial centralizer);
4. hence (`TempSlim.of_commensurator_eq`) `Π^tp_X` is temp-slim: an element centralizing an open
   `H` commensurates `Π_v` (as `H ⊓ Π_v` has finite index in the compact `Π_v`), so lies in
   `Π_v`, and centralizes the open subgroup `H ⊓ Π_v` of the slim `Π_v`.

Steps 1, 2 (given `HI s`) and 4 are proved. The remaining input is isolated as
`VerticialTempSlim`: **some compatible system `s` of the tree tower satisfies `HI s` and has a
temp-slim stabilizer**. Neither half is proved for any curve here:

* `HI s` for the system of a hyperbolic component is the specialization of admissible coverings
  (missing theorem M2, Blueprint §12.5 C10, §12.8);
* slimness of `Π_v` is the slimness of the arithmetic étale fundamental group of a hyperbolic
  curve over a `p`-adic field (the component, via the comparison of verticial subgroups with
  fundamental groups of components, not available without log geometry), which in turn rests on
  the slimness of `G_K` and of the geometric profinite fundamental group of a hyperbolic curve
  (`TempSlim.of_extension` is the extension step).

## Main results

* `tempSlim_andreGroup`, `tempSlim_temperedPi1`: `VerticialTempSlim → TempSlim Π^tp_X`.
* `tempSlim_of_isOpen`: hence every open subgroup of `Π^tp_X` is temp-slim, in particular
  `tempSlim_ker_character` (`Π^tp_Y = ker(Π^tp_X → ℤ)` of the Tate curve, `iut`'s
  `Iut.EtaleTheta.TateObject.piY`) and `tempSlim_piYddot` (`Π^tp_Ÿ`). These are the hypotheses
  `TempSlim P` of [EtTh], Prop. 2.11(ii) / Cor. 2.19(i) (first step) for `P = Π^tp_Y`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] [Finite A] [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-- **The remaining input for temp-slimness of `Π^tp_X`** ([Mzk14], Example 3.10): some
compatible system `s` of (vertices of the trees of the dual graphs of) André's tower satisfies
`HI s` (edge-like subgroups have infinite index in `stab s`; missing theorem M2) and its
verticial subgroup `stab s` is temp-slim (slimness of the profinite decomposition group of a
component). -/
def VerticialTempSlim : Prop :=
  ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys,
    (andreTower (R := R) (A := A) V hV hp hR).HI s ∧ TempSlim (TreeTower.stab s)

/-- **André's group is temp-slim**, given `VerticialTempSlim`. -/
theorem tempSlim_andreGroup (h : VerticialTempSlim (R := R) (A := A) V hV hp hR) :
    TempSlim (andreGroup O R A V hV) := by
  obtain ⟨s, hs, hslim⟩ := h
  exact TreeTower.tempSlim_of_HI hs (isCompact_stab_andreTower V hV hp hR s) hslim

/-- **The tempered fundamental group `Π^tp_X` is temp-slim** ([Mzk14], Example 3.10), given
`VerticialTempSlim`, via Theorem A. -/
theorem tempSlim_temperedPi1 (h : VerticialTempSlim (R := R) (A := A) V hV hp hR) :
    TempSlim (temperedPi1 O R A V hV) :=
  (tempSlim_andreGroup V hV hp hR h).of_continuousMulEquiv (andreEquiv' V hV hp hR).symm

/-- **Open subgroups of `Π^tp_X` are temp-slim** (tempered fundamental groups of finite étale
and tempered coverings, e.g. `Π^tp_Y`), given `VerticialTempSlim`. -/
theorem tempSlim_of_isOpen (h : VerticialTempSlim (R := R) (A := A) V hV hp hR)
    {U : Subgroup (temperedPi1 O R A V hV)} (hU : IsOpen (U : Set (temperedPi1 O R A V hV))) :
    TempSlim U :=
  (tempSlim_temperedPi1 V hV hp hR h).of_isOpen hU

/-- **`Π^tp_Y` is temp-slim** for the `ℤ`-covering `Y → X` of the Tate curve
(`Π^tp_Y = ker(TateObject.character)`, `iut`'s `TateObject.piY`), given `VerticialTempSlim`. -/
theorem tempSlim_ker_character (D : TateObject.Data O R)
    (h : VerticialTempSlim (R := R) (A := A) V hV hp hR) :
    TempSlim (TateObject.character (A := A) D V hV).ker :=
  (tempSlim_temperedPi1 V hV hp hR h).ker _ (TateObject.continuous_character D V hV)

/-- **`Π^tp_Ÿ` is temp-slim** (the double covering `Ÿ → Y`), given `VerticialTempSlim`. -/
theorem tempSlim_piYddot (D : TateObject.DoubleData O R) (s : Ω)
    (hs : s ^ 2 = algebraMap R Ω D.c) (h : VerticialTempSlim (R := R) (A := A) V hV hp hR) :
    TempSlim (TateObject.piYddot (A := A) D V hV s hs) :=
  tempSlim_of_isOpen V hV hp hR h (TateObject.isOpen_piYddot D V hV s hs)

end

end TemperedFundamentalGroups
