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

theorem isClosed_Z (c : TemperedFundamentalGroups.ModelCode O) : IsClosed (Z c) :=
  (IsLocalRing.isClosed_singleton_closedPoint O).preimage c.toSpec.continuous

/-- The generic fibre: the complement of the special fibre, as an open subscheme. -/
def genericOpen (c : TemperedFundamentalGroups.ModelCode O) : c.scheme.Opens :=
  ⟨(Z c)ᶜ, (isClosed_Z c).isOpen_compl⟩

/-- The node point `x` **joins** the components `v` and `w` (an edge of the dual graph between
`v` and `w`): `x ∈ v ∩ w`, and if `v = w` then `x` lies on no other component (a self-loop). -/
def Joins (c : TemperedFundamentalGroups.ModelCode O) (x : c.scheme) (v w : Set c.scheme) :
    Prop :=
  IsNodePt c x ∧ x ∈ v ∧ x ∈ w ∧ (v ≠ w ∨ ∀ v' ∈ components c, x ∈ v' → v' = v)

/-- A **walk** in the dual graph: components `v 0, …, v k` and node points `x 0, …, x (k-1)`,
`x i` joining `v i` and `v (i+1)`. -/
structure Walk (c : TemperedFundamentalGroups.ModelCode O) where
  /-- The number of edges. -/
  k : ℕ
  /-- The components. -/
  v : Fin (k + 1) → Set c.scheme
  /-- The edges (node points). -/
  x : Fin k → c.scheme
  mem_components : ∀ i, v i ∈ components c
  joins : ∀ i : Fin k, Joins c (x i) (v i.castSucc) (v i.succ)

/-- A walk is a **cycle** if it is closed, nonempty and uses each node at most once. -/
def Walk.IsCycle {c : TemperedFundamentalGroups.ModelCode O} (w : Walk c) : Prop :=
  1 ≤ w.k ∧ w.v 0 = w.v (Fin.last w.k) ∧ Function.Injective w.x

/-- `c` has **split nodes**: every node point `x` has an étale neighbourhood `Spec C → U` which is
also étale over a node `O[u, v] ⧸ (u v - ϖ ^ n)`, at a point `𝔮` of `C` over `x` with residue
field the residue field of `O` (`O → C ⧸ 𝔮` surjective). Then `κ(x) = κ(O)` and the two branches
of `Z c` at `x` are defined over `κ(O)` (the henselizations of `c` at `x` and of the node at its
singular point agree). -/
def HasSplitNodes (ϖ : O) (c : TemperedFundamentalGroups.ModelCode O) : Prop :=
  ∀ x : c.scheme, IsNodePt c x → ∃ (U : c.scheme.Opens) (hU : IsAffineOpen U) (hx : x ∈ U),
    letI := sectionsAlgebra c U
    ∃ (n : ℕ) (C : Type u) (_ : CommRing C) (g : Γ(c.scheme, U) →+* C)
      (f : _root_.SemistableReduction.Node O (ϖ ^ n) →+* C) (𝔮 : Ideal C),
      g.Etale ∧ f.Etale ∧ 𝔮.IsPrime ∧ 𝔮.comap g = (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      f.comp (algebraMap O _) = g.comp (algebraMap O Γ(c.scheme, U)) ∧
      Function.Surjective ((Ideal.Quotient.mk 𝔮).comp (g.comp (algebraMap O Γ(c.scheme, U))))

/-- The ring map from `O` to the residue field of a point of a model. -/
noncomputable def residueMap (c : TemperedFundamentalGroups.ModelCode O) (x : c.scheme) :
    O →+* c.scheme.residueField x :=
  ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ c.toSpec.appTop ≫
    c.scheme.presheaf.germ ⊤ x trivial ≫ c.scheme.residue x).hom

/-- The components of `Z c` are **geometrically irreducible**: at the generic point `η` of a
component, the residue field `κ(O)` is separably closed in `κ(η)` (every element of `κ(η)` which
is a simple root of a monic polynomial over `O` comes from `O`). -/
def HasGeomIrreducibleComponents (c : TemperedFundamentalGroups.ModelCode O) : Prop :=
  ∀ v ∈ components c, ∀ η ∈ v, closure {η} = v → ∀ a : c.scheme.residueField η,
    (∃ P : Polynomial O, P.Monic ∧ P.eval₂ (residueMap c η) a = 0 ∧
      (Polynomial.derivative P).eval₂ (residueMap c η) a ≠ 0) →
    ∃ o : O, residueMap c η o = a

/-- `c` is **split**: its nodes are split and its components geometrically irreducible, so that
the dual graph read off on `Z c` is the geometric one. -/
def IsSplit (ϖ : O) (c : TemperedFundamentalGroups.ModelCode O) : Prop :=
  HasSplitNodes ϖ c ∧ HasGeomIrreducibleComponents c

/-- **Harmonicity of a morphism of models** (W8′(a), Blueprint §9.7, §10.3) for
`ψ : c' ⟶ c` over `O`:
* thicknesses of nodes of `c` and `c'` are well defined, and every node point has a thickness
  `≥ 1`;
* every node `x'` of `c'` of thickness `n'` maps either to a node of `c` of thickness `n = d·n'`,
  `d ≥ 1` (the local degree; lengths are scaled by it), or to a smooth point of `c` lying on
  exactly one component;
* every component of `c'` maps onto a component of `c`;
* points over nodes are nodes (edge lifting at the images of components). -/
def IsHarmonic (ϖ : O) {c c' : TemperedFundamentalGroups.ModelCode O}
    (ψ : c'.scheme ⟶ c.scheme) : Prop :=
  (∀ (x : c.scheme) (n m : ℕ), IsNodeOfThickness ϖ c x n → IsNodeOfThickness ϖ c x m → n = m) ∧
  (∀ (x' : c'.scheme) (n m : ℕ), IsNodeOfThickness ϖ c' x' n →
    IsNodeOfThickness ϖ c' x' m → n = m) ∧
  (∀ x : c.scheme, IsNodePt c x → ∃ n, 1 ≤ n ∧ IsNodeOfThickness ϖ c x n) ∧
  (∀ x' : c'.scheme, IsNodePt c' x' → ∃ n', 1 ≤ n' ∧ IsNodeOfThickness ϖ c' x' n') ∧
  (∀ (x' : c'.scheme) (n' : ℕ), IsNodeOfThickness ϖ c' x' n' →
    (∃ n d : ℕ, 1 ≤ d ∧ n = d * n' ∧ IsNodeOfThickness ϖ c (ψ x') n) ∨
    (IsSmoothPt c (ψ x') ∧ ∃! v, v ∈ components c ∧ ψ x' ∈ v)) ∧
  (∀ v' ∈ components c', ψ '' v' ∈ components c) ∧
  (∀ x' : c'.scheme, IsNodePt c (ψ x') → IsNodePt c' x')

/-- The morphism `ψ : c ⟶ c'` has **local degree `d` at the node `x`** of `c` (lying over a node
of `c'`): there are affine opens `U ∋ x` and `U' ⊇ ψ U`, étale node charts
`Node O (ϖ ^ n) → C` at `x` (at its singular point) and `Node O (ϖ ^ n') → C'` of `U'`, and a
compatible map `C' → C`, such that the pulled back coordinates of `c'` are
`u' = ε ϖ ^ a u ^ d`, `v' = ε' ϖ ^ b v ^ d` with units `ε, ε'` (for a finite `ψ` near `x`,
`a = b = 0`; inner nodes of chains contracted by a modification have `a` or `b` positive). -/
def HasLocalDegree (ϖ : O) {c c' : TemperedFundamentalGroups.ModelCode O}
    (ψ : c.scheme ⟶ c'.scheme) (x : c.scheme) (d : ℕ) : Prop :=
  ∃ (U : c.scheme.Opens) (hU : IsAffineOpen U) (hx : x ∈ U) (U' : c'.scheme.Opens)
    (hle : U ≤ ψ ⁻¹ᵁ U'),
    letI := sectionsAlgebra c U
    letI := sectionsAlgebra c' U'
    ∃ (n n' a b : ℕ) (C : Type u) (_ : CommRing C) (g : Γ(c.scheme, U) →+* C)
      (f : _root_.SemistableReduction.Node O (ϖ ^ n) →+* C) (𝔮 : Ideal C)
      (C' : Type u) (_ : CommRing C') (g' : Γ(c'.scheme, U') →+* C')
      (f' : _root_.SemistableReduction.Node O (ϖ ^ n') →+* C') (k : C' →+* C) (ε ε' : Cˣ),
      g.Etale ∧ f.Etale ∧ g'.Etale ∧ f'.Etale ∧ 𝔮.IsPrime ∧
      𝔮.comap g = (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧
      f.comp (algebraMap O _) = g.comp (algebraMap O _) ∧
      f'.comp (algebraMap O _) = g'.comp (algebraMap O _) ∧
      f (_root_.SemistableReduction.Node.u _) ∈ 𝔮 ∧ f (_root_.SemistableReduction.Node.v _) ∈ 𝔮 ∧
      k.comp g' = g.comp (ψ.appLE U' U hle).hom ∧
      k (f' (_root_.SemistableReduction.Node.u _)) =
        ε * f (algebraMap O _ (ϖ ^ a)) * f (_root_.SemistableReduction.Node.u _) ^ d ∧
      k (f' (_root_.SemistableReduction.Node.v _)) =
        ε' * f (algebraMap O _ (ϖ ^ b)) * f (_root_.SemistableReduction.Node.v _) ^ d

end TemperedFundamentalGroups.SemistableReduction.ModelCode
