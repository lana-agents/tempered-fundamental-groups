/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ProjNormalizationCode
import TemperedFundamentalGroups.SemistableReduction.Statement

/-!
# W-models and the targeted harmonicity statement (W8′, H5)

Only **definitions**. A *W-model* (`ModelCode.IsWModel`) of a function field `L` of a curve over
`K'`, on the *x-line* given by a transcendental `x ∈ L` (`L` finite over `K'(x)`), is the
projective model code (M9c, `exists_projModelCode_normalization`) of the normalization in `L` of
a Gauss-tree model `gaussJoinModel` of `K'(x)` (M5), up to isomorphism over `O'`: these are the
models the W-chain produces (Blueprint §9.7, §9.9). `Statement.HarmonicW` is the targeted form of
W8′: every morphism between W-models over the same x-line, compatible with a finite extension of
function fields, is harmonic on dual graphs (`ModelCode.IsHarmonicGeneral`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

open _root_.SemistableReduction

variable {K' : Type u} [Field K']

/-- The `K'(x)`-algebra structure on `L` given by a transcendental element `x`. -/
noncomputable abbrev xLineAlgebra (L : Type u) [Field L] [Algebra K' L] {x : L}
    (hx : Transcendental K' x) : Algebra (RatFunc K') L :=
  (RatFunc.liftAlgHom (Polynomial.aeval x) (fun p hp ↦ by
    simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq] at hp ⊢
    exact fun h ↦ hp ((injective_iff_map_eq_zero _).mp
      (transcendental_iff_injective.mp hx) p h))).toRingHom.toAlgebra

/-- **`c` is a W-model of `L` on the x-line `x`** (over `O'`): there are Gauss data `(a i, b i)`
on `K'(x)` and homogeneous coordinates `g` on `L` such that the projective model of `g` has the
points of the normalization in `L` of `gaussJoinModel` (M9c), and `c` is isomorphic over `O'` to
`ProjScheme.projModelCode O' g`, with `j : Spec L ⟶ c` corresponding to the generic point
(`ProjScheme.toProj`). -/
def ModelCode.IsWModel (O' : ValuationSubring K') (L : Type u) [Field L] [Algebra K' L]
    [Algebra O' L] [IsScalarTower O' K' L] (x : L) (c : TemperedFundamentalGroups.ModelCode O')
    (j : Spec (CommRingCat.of L) ⟶ c.scheme) : Prop :=
  ∃ (hx : Transcendental K' x) (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a b : ι → K')
    (n : ℕ) (g : Fin (n + 1) → L) (hg : ∀ l, g l ≠ 0),
    letI := xLineAlgebra L hx
    haveI : IsScalarTower K' (RatFunc K') L := IsScalarTower.of_algebraMap_eq fun k ↦ by
      change algebraMap K' L k = RatFunc.liftAlgHom _ _ (algebraMap K' (RatFunc K') k)
      rw [AlgHom.commutes]
    (∀ i, b i ≠ 0) ∧
    (ZariskiModel.projModel (baseRing L O'.valuation.valuationSubring) g).points =
      ((gaussJoinModel O'.valuation a b).normalization L).points ∧
    ∃ e : c.scheme ≅ (ProjScheme.projModelCode O' hg).scheme,
      e.hom ≫ (ProjScheme.projModelCode O' hg).toSpec = c.toSpec ∧
      j ≫ e.hom = (ProjScheme.toProj O' hg).toImage

/-- **W8′, targeted form: maps of W-models are harmonic.** Let `O'` be a discrete valuation ring
with uniformizer `ϖ` and fraction field `K'`, `L ⊆ L'` function fields of curves over `K'` with
`L'/L` finite, `x ∈ L` (the x-line), `c` a W-model of `L'` on `x` and `c'` a W-model of `L` on `x`
(with generic points `j`, `j'`), both split, semistable and without loops, and `ψ : c ⟶ c'` a
morphism over `O'` inducing `L ⊆ L'` on generic points. Then `ψ` is harmonic on dual graphs
(`ModelCode.IsHarmonicGeneral`: monotone walks over each node with `∑ dᵢ nᵢ = n'`, lengths do not
decrease, nodes map to nodes or to points on a single component). -/
def Statement.HarmonicW : Prop :=
  ∀ (K' : Type u) [Field K'] (O' : ValuationSubring K') [IsDiscreteValuationRing O'] (ϖ : O')
    (_ : Irreducible ϖ) (L L' : Type u) [Field L] [Field L'] [Algebra K' L] [Algebra K' L']
    [Algebra L L'] [IsScalarTower K' L L'] [FiniteDimensional L L'] [Algebra O' L]
    [IsScalarTower O' K' L] [Algebra O' L'] [IsScalarTower O' K' L'] (x : L)
    (c c' : TemperedFundamentalGroups.ModelCode O') (ψ : c.scheme ⟶ c'.scheme)
    (j : Spec (CommRingCat.of L') ⟶ c.scheme) (j' : Spec (CommRingCat.of L) ⟶ c'.scheme),
    ModelCode.IsWModel O' L' (algebraMap L L' x) c j → ModelCode.IsWModel O' L x c' j' →
    j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫ j' → ψ ≫ c'.toSpec = c.toSpec →
    ModelCode.IsSemistable ϖ c → ModelCode.IsSemistable ϖ c' →
    ModelCode.IsSplit ϖ c → ModelCode.IsSplit ϖ c' → ModelCode.NoLoops c → ModelCode.NoLoops c' →
      ModelCode.IsHarmonicGeneral ϖ ψ

end TemperedFundamentalGroups.SemistableReduction
