/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.WModel
import TemperedFundamentalGroups.SemistableReduction.XLength
import TemperedFundamentalGroups.SemistableReduction.GaussTree

/-!
# Intrinsic x-lengths of nodes of models and the targeted statement `Statement.HarmonicX`

Blueprint §9.7 (W8′, consumer: Theorem B, B5). Only **definitions** (and the transport of germs
along isomorphisms). For a projective model `c` over `O'` of a function field `L` with generic
point `j : Spec L ⟶ c` and a point `y`:

* `ModelCode.germs c j y ⊆ L`: the functions regular at `y` (images in `L` of sections over
  opens containing `y` and the generic point) — the Zariski point of `y` (W5 dictionary);
* `ModelCode.IsXLength ϖ₀ O' ϖ' c j x y λ`: `λ` is the **x-length** of the node `y` on the
  x-line `x ∈ L`: there are sections `u, v` near `y`, vanishing at `y`, with `u v = ϖ' ^ n`, and
  `λ` is the x-length of the node (`SemistableReduction.IsXLength`, `XLength.lean`): the total
  variation of the log radius (normalised to `v(ϖ₀) = 1`, `ϖ₀` the uniformizer of the base
  `O`) of the restrictions to the x-line of the interpolating monomial valuations of the node —
  the sum of `|Δ log radius|` over the monotone pieces, folds included. It is purely
  valuation-theoretic and does not depend on `O'` (only on the normalisation `ϖ₀`).
* `ModelCode.IsHarmonicX`: (X0)–(X3) for `ψ : c ⟶ c'`;
* `Statement.HarmonicX` (**targeted**; supersedes `Statement.HarmonicW` for B5): for W-models
  `c`, `c'` on the same x-line over **arbitrary** finite extensions `K₁`, `K₂` of `K`, and
  `ψ : c ⟶ c'` over `O` compatible with the generic points, `ψ` is x-harmonic.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

variable {K' L : Type u} [Field K'] [Field L]

/-- The **germs at `y`**: the elements of `L` which are images, along the generic point
`j : Spec L ⟶ c`, of sections of `c` over an open `U ∋ y` (with `j` landing in `U`). For a
W-model this is the local ring of the Zariski point of `y` (W5). -/
def germs {O : Type u} [CommRing O] (c : TemperedFundamentalGroups.ModelCode O)
    (j : Spec (CommRingCat.of L) ⟶ c.scheme) (y : c.scheme) : Set L :=
  {f | ∃ (U : c.scheme.Opens) (_ : y ∈ U) (h : ⊤ ≤ j ⁻¹ᵁ U) (s : Γ(c.scheme, U)),
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom ((j.appLE U ⊤ h).hom s) = f}

/-- The image in `L` of a section over an open containing the generic point. -/
noncomputable def toL {O : Type u} [CommRing O] {c : TemperedFundamentalGroups.ModelCode O}
    (j : Spec (CommRingCat.of L) ⟶ c.scheme) {U : c.scheme.Opens} (h : ⊤ ≤ j ⁻¹ᵁ U)
    (s : Γ(c.scheme, U)) : L :=
  (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom ((j.appLE U ⊤ h).hom s)

lemma toL_mem_germs {O : Type u} [CommRing O] {c : TemperedFundamentalGroups.ModelCode O}
    (j : Spec (CommRingCat.of L) ⟶ c.scheme) {U : c.scheme.Opens} (h : ⊤ ≤ j ⁻¹ᵁ U)
    {y : c.scheme} (hy : y ∈ U) (s : Γ(c.scheme, U)) : toL j h s ∈ germs c j y :=
  ⟨U, hy, h, s, rfl⟩

/-- Germs are transported along isomorphisms of models compatible with the generic points
(one inclusion; equality is `germs_iso`). -/
lemma germs_iso_subset {O : Type u} [CommRing O] {c c' : TemperedFundamentalGroups.ModelCode O}
    (e : c.scheme ≅ c'.scheme) (j : Spec (CommRingCat.of L) ⟶ c.scheme) (y : c.scheme) :
    germs c' (j ≫ e.hom) (e.hom y) ⊆ germs c j y := by
  rintro f ⟨U', hy, h, s, rfl⟩
  refine ⟨e.hom ⁻¹ᵁ U', hy, h, e.hom.appLE U' (e.hom ⁻¹ᵁ U') le_rfl s, ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE]
  rfl

/-- **Germs are invariant under isomorphisms** of models compatible with the generic points.
(The remaining data of `IsXLength`, the sections `u, v`, transport along `e.hom.appLE`, with
`toL` unchanged by the same computation; Blueprint §9.7, X-iso.) -/
theorem germs_iso {O : Type u} [CommRing O] {c c' : TemperedFundamentalGroups.ModelCode O}
    (e : c.scheme ≅ c'.scheme) (j : Spec (CommRingCat.of L) ⟶ c.scheme) (y : c.scheme) :
    germs c' (j ≫ e.hom) (e.hom y) = germs c j y := by
  refine (germs_iso_subset e j y).antisymm ?_
  have h := germs_iso_subset (c := c') (c' := c) e.symm (j ≫ e.hom) (e.hom y)
  have hy : e.symm.hom (e.hom y) = y := by
    change (e.hom ≫ e.inv) y = y
    rw [e.hom_inv_id]
    rfl
  have hj : (j ≫ e.hom) ≫ e.symm.hom = j := by simp
  rwa [hy, hj] at h

variable [Algebra K' L]

/-- **`c` is an unfolded W-model** of `L` on the x-line `x` (over `O'`): `c` is the W-model of
**convex reduced** Gauss data `(a, b)` (`ModelCode.IsWModelOf`, `GaussTree.IsConvex`,
`GaussTree.IsReduced`), and **every node of `c` lies over a node of its Gauss tree**: the
functions of `K'(x)` regular at a node point `y` of `c` (germs at `y` lying in `K'(x)`) lie in two
distinct vertices of `gaussJoinModel O' a b`. Equivalently (W7 (c)) the points of `c` over smooth
points of the Gauss tree are smooth; with convexity the two branches of every node then restrict
to the two ends of an edge of the tree and the x-path of every node is monotone. Convexity is
needed: for the non-convex data `D(0, |ϖ|), D(1, |ϖ|)` on `K(x)` the join model has a node of
thickness 2 at which both conditions hold, but its x-path turns at `D(0, 1)` (`λ = 2`, position
difference `0`). The models produced by the W-chain are unfolded (W7 (c); W7's trees are convex
and reduced). -/
def IsUnfolded (O' : ValuationSubring K') [Algebra O' L] [IsScalarTower O' K' L] (x : L)
    (c : TemperedFundamentalGroups.ModelCode O') (j : Spec (CommRingCat.of L) ⟶ c.scheme) :
    Prop :=
  ∃ (hx : Transcendental K' x) (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (a b : ι → K'),
    ModelCode.IsWModelOf O' L x hx a b c j ∧
    _root_.SemistableReduction.GaussTree.IsConvex O'.valuation a b ∧
    _root_.SemistableReduction.GaussTree.IsReduced O'.valuation a b ∧
    letI := xLineAlgebra L hx
    ∀ y : c.scheme, IsNodePt c y →
      ∃ W₁ ∈ (_root_.SemistableReduction.gaussJoinModel O'.valuation a b).vertexSet,
      ∃ W₂ ∈ (_root_.SemistableReduction.gaussJoinModel O'.valuation a b).vertexSet, W₁ ≠ W₂ ∧
        ∀ f : RatFunc K', algebraMap (RatFunc K') L f ∈ germs c j y → f ∈ W₁ ∧ f ∈ W₂

/-- An unfolded W-model is a W-model. -/
lemma IsUnfolded.isWModel {O' : ValuationSubring K'} [Algebra O' L] [IsScalarTower O' K' L]
    {x : L} {c : TemperedFundamentalGroups.ModelCode O'}
    {j : Spec (CommRingCat.of L) ⟶ c.scheme} (h : IsUnfolded O' x c j) : IsWModel O' L x c j := by
  obtain ⟨hx, ι, _, _, a, b, h, -⟩ := h
  exact ⟨hx, ι, inferInstance, inferInstance, a, b, h⟩

/-- **The x-length of a node of a model** (Blueprint §9.7): `λ` is the x-length of the point
`y` of `c` (a projective `O'`-model of `L`, generic point `j`, `ϖ'` a uniformizer of `O'`) on the
x-line `x ∈ L`, normalised by the image `ϖ₀ ∈ L` of the uniformizer of the base: there are an
open `U ∋ y` containing the generic point and sections `u, v` over `U` vanishing at `y` with
`u v = ϖ' ^ n`, such that `λ` is the x-length (`SemistableReduction.IsXLength`) of the node at
the germs of `y` with coordinate `u`: the total variation of the normalised log radius of the
path on the x-line obtained by restricting the interpolating monomial valuations (from the
branch `u = unit` to the branch `v = unit`) to `K'(x)`, i.e. the sum of `|Δ log radius|`
over its finitely many monotone pieces, **including the folded case** (a node over a smooth
point of the base, e.g. `x = z + ϖ / z`, has positive x-length although both branches restrict
to the same Gauss point). Valuation-theoretic, no Berkovich spaces; independent of `O'`. -/
def IsXLength (ϖ₀ : L) (O' : ValuationSubring K') [Algebra O' L] (ϖ' : O')
    (c : TemperedFundamentalGroups.ModelCode O') (j : Spec (CommRingCat.of L) ⟶ c.scheme)
    (x : L) (y : c.scheme) (l : ℚ) : Prop :=
  ∃ (U : c.scheme.Opens) (hy : y ∈ U) (h : ⊤ ≤ j ⁻¹ᵁ U) (n : ℕ) (u v : Γ(c.scheme, U)),
    letI := sectionsAlgebra c U
    u * v = algebraMap O' Γ(c.scheme, U) (ϖ' ^ n) ∧
    ¬ IsUnit ((c.scheme.presheaf.germ U y hy).hom u) ∧
    ¬ IsUnit ((c.scheme.presheaf.germ U y hy).hom v) ∧
    _root_.SemistableReduction.IsXLength O' (germs c j y) ϖ₀ (algebraMap O' L ϖ') (toL j h u)
      x n l

/-- **x-harmonicity** of `ψ : c ⟶ c'` (`c` over `O₁ ⊆ K₁`, function field `L₁`, generic point
`j₁`; `c'` over `O₂ ⊆ K₂`, function field `L₂`, generic point `j₂`; x-lines `x₁ ∈ L₁`,
`x₂ ∈ L₂`; base uniformizer images `ϖ₁₀ ∈ L₁`, `ϖ₂₀ ∈ L₂`):
* (X0) every node of `c` has an x-length, and it is positive;
* (X1) for every node `y'` of `c'` on two components `w₁' ≠ w₂'` and every component `v` of `c`
  over `w₁'` there is a walk from `v` crossing `y'` (`Walk.Crosses`) to a component over `w₂'`
  whose x-lengths sum to the x-length of `y'`;
* (X2) every walk crossing `y'` from a component over `w₁'` to one over `w₂'` has total
  x-length at least that of `y'`;
* (X3) a node of `c` not over a node maps to a point on exactly one component. -/
def IsHarmonicX {K₁ K₂ L₁ L₂ : Type u} [Field K₁] [Field K₂] [Field L₁] [Field L₂]
    [Algebra K₁ L₁] [Algebra K₂ L₂] (O₁ : ValuationSubring K₁) (O₂ : ValuationSubring K₂)
    [Algebra O₁ L₁] [Algebra O₂ L₂] (ϖ₁ : O₁) (ϖ₂ : O₂) (ϖ₁₀ : L₁) (ϖ₂₀ : L₂) (x₁ : L₁)
    (x₂ : L₂) {c : TemperedFundamentalGroups.ModelCode O₁}
    {c' : TemperedFundamentalGroups.ModelCode O₂} (j₁ : Spec (CommRingCat.of L₁) ⟶ c.scheme)
    (j₂ : Spec (CommRingCat.of L₂) ⟶ c'.scheme) (ψ : c.scheme ⟶ c'.scheme) : Prop :=
  (∀ y : c.scheme, IsNodePt c y →
    (∃ l, IsXLength ϖ₁₀ O₁ ϖ₁ c j₁ x₁ y l) ∧ ∀ l, IsXLength ϖ₁₀ O₁ ϖ₁ c j₁ x₁ y l → 0 < l) ∧
  (∀ y' : c'.scheme, IsNodePt c' y' →
    ∀ w₁' ∈ components c', ∀ w₂' ∈ components c', w₁' ≠ w₂' → y' ∈ w₁' → y' ∈ w₂' →
    ∀ v ∈ components c, ψ '' v = w₁' → ∀ l', IsXLength ϖ₂₀ O₂ ϖ₂ c' j₂ x₂ y' l' →
      ∃ w : Walk c, w.v 0 = v ∧ w.Crosses ψ y' ∧ ψ '' w.v (Fin.last w.k) = w₂' ∧
        ∃ l : Fin w.k → ℚ, (∀ i, IsXLength ϖ₁₀ O₁ ϖ₁ c j₁ x₁ (w.x i) (l i)) ∧ ∑ i, l i = l') ∧
  (∀ y' : c'.scheme, IsNodePt c' y' →
    ∀ w₁' ∈ components c', ∀ w₂' ∈ components c', w₁' ≠ w₂' → y' ∈ w₁' → y' ∈ w₂' →
    ∀ w : Walk c, w.Crosses ψ y' → ψ '' w.v 0 = w₁' → ψ '' w.v (Fin.last w.k) = w₂' →
      ∀ l : Fin w.k → ℚ, (∀ i, IsXLength ϖ₁₀ O₁ ϖ₁ c j₁ x₁ (w.x i) (l i)) →
      ∀ l', IsXLength ϖ₂₀ O₂ ϖ₂ c' j₂ x₂ y' l' → l' ≤ ∑ i, l i) ∧
  (∀ y : c.scheme, IsNodePt c y → ¬ IsNodePt c' (ψ y) →
    ∃! w', w' ∈ components c' ∧ ψ y ∈ w')

end TemperedFundamentalGroups.SemistableReduction.ModelCode

namespace TemperedFundamentalGroups.SemistableReduction

/-- **W8′, targeted form for B5: maps of W-models are x-harmonic** (Blueprint §9.7). Let `K` be
a complete discretely valued field of characteristic `0` (valuation subring `O`, uniformizer
`ϖ`), `K₁`, `K₂` **arbitrary** finite extensions (no inclusion between them) with valuation
subrings `O₁`, `O₂` over `O` and uniformizers `ϖ₁`, `ϖ₂`, `L₂ ⊆ L₁` function fields of curves
over `K₂` resp. `K₁` (compatibly over `K`, `L₁ / L₂` finite), `x ∈ L₂` (the x-line), `c` a
W-model of `L₁` over `O₁` and `c'` a W-model of `L₂` over `O₂` on `x` (generic points `j`,
`j'`), both **unfolded** (`ModelCode.IsUnfolded`: every node lies over a node of the Gauss tree,
W7 (c)), split, semistable and without loops, and `ψ : c ⟶ c'` a morphism over `Spec O`
inducing `L₂ ⊆ L₁` on generic points. Then `ψ` is x-harmonic (`ModelCode.IsHarmonicX`, lengths
normalised to `v(ϖ) = 1`): positive x-lengths (X0), monotone crossing walks of the same total
x-length (X1), crossing walks do not shorten (X2), nodes not over nodes map to points on a single
component (X3). Supersedes `Statement.HarmonicW` for B5. -/
def Statement.HarmonicX : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (ϖ : O) (_ : Irreducible ϖ)
    (K₁ K₂ : Type u) [Field K₁] [Field K₂] [Algebra K K₁] [Algebra K K₂]
    [FiniteDimensional K K₁] [FiniteDimensional K K₂]
    (O₁ : ValuationSubring K₁) (O₂ : ValuationSubring K₂)
    (h₁ : O₁.comap (algebraMap K K₁) = O) (h₂ : O₂.comap (algebraMap K K₂) = O)
    [IsDiscreteValuationRing O₁] [IsDiscreteValuationRing O₂] (ϖ₁ : O₁) (ϖ₂ : O₂)
    (_ : Irreducible ϖ₁) (_ : Irreducible ϖ₂)
    (L₁ L₂ : Type u) [Field L₁] [Field L₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
    [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
    [IsScalarTower K L₂ L₁] [FiniteDimensional L₂ L₁]
    [Algebra O₁ L₁] [IsScalarTower O₁ K₁ L₁] [Algebra O₂ L₂] [IsScalarTower O₂ K₂ L₂] (x : L₂)
    (c : TemperedFundamentalGroups.ModelCode O₁) (c' : TemperedFundamentalGroups.ModelCode O₂)
    (ψ : c.scheme ⟶ c'.scheme)
    (j : Spec (CommRingCat.of L₁) ⟶ c.scheme) (j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme),
    ModelCode.IsUnfolded O₁ (algebraMap L₂ L₁ x) c j → ModelCode.IsUnfolded O₂ x c' j' →
    j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j' →
    ψ ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₂).restrict O O₂
      (fun y hy ↦ by rw [← h₂] at hy; exact hy))) =
      c.toSpec ≫ Spec.map (CommRingCat.ofHom ((algebraMap K K₁).restrict O O₁
        (fun y hy ↦ by rw [← h₁] at hy; exact hy))) →
    ModelCode.IsSemistable ϖ₁ c → ModelCode.IsSemistable ϖ₂ c' →
    ModelCode.IsSplit ϖ₁ c → ModelCode.IsSplit ϖ₂ c' →
    ModelCode.NoLoops c → ModelCode.NoLoops c' →
      ModelCode.IsHarmonicX O₁ O₂ ϖ₁ ϖ₂ (algebraMap K L₁ ϖ) (algebraMap K L₂ ϖ)
        (algebraMap L₂ L₁ x) x j j' ψ

end TemperedFundamentalGroups.SemistableReduction
