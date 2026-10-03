/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.DualGraph
import TemperedFundamentalGroups.Models.Specialization
import TemperedFundamentalGroups.Models.Projective

/-!
# The statement of semistable reduction (W10), as consumed by the tempered group

This file only contains **definitions** (no theorem, no hypothesis is assumed anywhere): the
precise form of the semistable reduction theorem for finite étale covers that the W-chain
(Blueprint §9.3) is proving (`SemistableReduction.Statement`), and that the identification of
`temperedPi1` with André's tempered group (Blueprint §4) and the non-degeneracy witness
(§5.1) consume. Downstream developments build against `Statement` as a named `Prop`; once W10
is proved, `Statement` becomes a theorem and all such developments become unconditional.

## Semistable models

Let `O` be a discrete valuation ring with uniformizer `ϖ` and fraction field `K`, and `c` a
projective `O`-model (`ModelCode O`: a closed subscheme of some `ℙ^m_O`). `c` is
**semistable** (`ModelCode.IsSemistable`) if every point of its special fibre has an affine
open neighbourhood `Spec A` (an open `U` with `IsAffineOpen U`, `A = Γ(U)`) such that `A` is
étale-locally at the corresponding prime a node `O[u,v]/(uv − ϖ^n)` or `O[u]`
(`SemistableReduction.IsSemistableAt`, `LocalModel.lean`).

## The statement

For a complete discretely valued field `K` of characteristic `0`, a smooth affine `K`-curve
`Y = Spec R` and a finite étale `R`-algebra `B` (a finite étale cover `T = Spec B → Y`):
there is a finite extension `K'/K` (with its valuation ring `O'`, the integral closure of `O`),
a semistable projective `O'`-model `c` and an open immersion `Spec (K' ⊗_K B) ⟶ c.scheme` over
`O'` with schematically dense image. (Compatibility with a given model of `Y` — domination of
the normalization of a model of `Ȳ` — is the second clause.)
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction

namespace ModelCode

variable {O : Type u} [CommRing O]

/-- A projective `O`-model is **semistable** (relative to the uniformizer `ϖ`) if every point
has an affine open neighbourhood whose ring of sections is, étale-locally at that point, a node
`O[u,v]/(uv − ϖ^n)` or the affine line `O[u]`. (Points of the generic fibre are included: there
the local models are smooth.) -/
def IsSemistable (ϖ : O) (c : TemperedFundamentalGroups.ModelCode O) : Prop :=
  ∀ x : c.scheme, ∃ (U : c.scheme.Opens) (hU : IsAffineOpen U) (hx : x ∈ U),
    letI := sectionsAlgebra c U
    _root_.SemistableReduction.IsSemistableAt ϖ (hU.primeIdealOf ⟨x, hx⟩).asIdeal

end ModelCode

/-- **Semistable reduction of finite étale covers of affine curves (W10)** — the statement.

For every complete discretely valued field `K` of characteristic `0` (valuation subring `O`, `O` adically complete,
uniformizer `ϖ`), every `K`-algebra `R` smooth of relative dimension one (a smooth affine curve)
and every finite étale `R`-algebra `B`, there are
* a finite extension `K'` of `K`, with the valuation subring `O'` extending `O` and a
  uniformizer `ϖ'` of `O'`;
* a projective `O'`-model `c` that is semistable (`ModelCode.IsSemistable ϖ' c`);
* a morphism `j : Spec (K' ⊗[K] B) ⟶ c.scheme` over `Spec O'` which is an open immersion.
Stated with `K`, `R`, `B` in a fixed universe `u`. -/
def Statement : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (R : Type u) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (_ : ringKrullDim R = 1)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] [Module.Finite R B],
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (O' : ValuationSubring K') (_ : O'.comap (algebraMap K K') = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c : TemperedFundamentalGroups.ModelCode O')
      (j : Spec (CommRingCat.of (TensorProduct K K' B)) ⟶ c.scheme),
      ModelCode.IsSemistable ϖ' c ∧ IsOpenImmersion j ∧
        j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
          ((Algebra.TensorProduct.includeLeftRingHom).comp O'.subtype))

end TemperedFundamentalGroups.SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction

/-- **The strong form of W10** (clauses requested by the André identification, Blueprint §10):
in addition to `Statement`, for a finite group `G` acting on `B` by `K`-algebra automorphisms
and finitely many given projective `O`-models `c₀ i` of `Spec B` (with `j₀ i` over `O`):
* `K'/K` is Galois;
* the semistable model is also a projective `O`-model `c` (isomorphic, over `O`, to the
  semistable `O'`-model `c'`), and `c'` is split (`ModelCode.IsSplit`: split nodes, geometrically
  irreducible components);
* `j : Spec (K' ⊗_K B) ⟶ c` is an open immersion over `O` which is scheme-theoretically dominant;
* `G × Gal(K'/K)` acts on `c` over `O` with `j` equivariant (`g` acts on `K' ⊗ B` by `id ⊗ g`,
  `σ` by `σ ⊗ id`);
* `c` dominates every `c₀ i` compatibly with the `j`s;
* the special fibre of `c` has dimension `≤ 1`. -/
def Statement.Strong : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (R : Type u) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (_ : ringKrullDim R = 1)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] [Module.Finite R B]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G B] [SMulCommClass G K B]
    (ι : Type u) [Finite ι] (c₀ : ι → TemperedFundamentalGroups.ModelCode O)
    (j₀ : ∀ i, Spec (CommRingCat.of B) ⟶ (c₀ i).scheme)
    (_ : ∀ i, j₀ i ≫ (c₀ i).toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap K B).comp O.subtype))),
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : IsGalois K K')
      (O' : ValuationSubring K') (_ : O'.comap (algebraMap K K') = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c' : TemperedFundamentalGroups.ModelCode O') (c : TemperedFundamentalGroups.ModelCode O)
      (e : c.scheme ≅ c'.scheme)
      (j : Spec (CommRingCat.of (TensorProduct K K' B)) ⟶ c.scheme)
      (act : G × (K' ≃ₐ[K] K') →* Aut c.scheme)
      (dom : ∀ i, c.scheme ⟶ (c₀ i).scheme),
      ModelCode.IsSemistable ϖ' c' ∧ ModelCode.IsSplit ϖ' c' ∧
      e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
        ((algebraMap K K').restrict O O' (fun x hx => by
          rw [← ‹O'.comap (algebraMap K K') = O›] at hx; exact hx))) = c.toSpec ∧
      IsOpenImmersion j ∧ IsSchemeTheoreticallyDominant j ∧
      j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeftRingHom).comp ((algebraMap K K').comp O.subtype))) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'), (act gσ).hom ≫ c.toSpec = c.toSpec) ∧
      (∀ gσ : G × (K' ≃ₐ[K] K'),
        Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.congr (gσ.2⁻¹)
          (MulSemiringAction.toAlgAut G K B gσ.1⁻¹)).toRingHom) ≫ j = j ≫ (act gσ).hom) ∧
      (∀ i, j ≫ dom i = Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom : B →+* TensorProduct K K' B)) ≫ j₀ i) ∧
      (∀ i, dom i ≫ (c₀ i).toSpec = c.toSpec) ∧
      topologicalKrullDim (specialFibre c.toSpec) ≤ 1

end TemperedFundamentalGroups.SemistableReduction

namespace TemperedFundamentalGroups.SemistableReduction

/-- **Simultaneous semistable reduction** (requested for W8′ / Theorem B of the André
identification): for a tower of finite étale covers `Spec B' → Spec B → Spec R` of a smooth
affine `K`-curve, after a finite extension `K'/K` there are semistable projective `O'`-models
`c` of `Spec (K' ⊗ B)` and `c'` of `Spec (K' ⊗ B')`, both split (`ModelCode.IsSplit`), with
open immersions `j, j'` over `O'` and a
**finite** morphism `ψ : c' ⟶ c` over `O'` compatible with `j, j'` (e.g. `c'` the normalization of
`c` in `K' ⊗ B'`), which is harmonic on dual graphs (`ModelCode.IsHarmonic`, W8′). -/
def Statement.Simultaneous : Prop :=
  ∀ (K : Type u) [Field K] [CharZero K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (R : Type u) [CommRing R] [Algebra K R] [Algebra.Smooth K R] (_ : ringKrullDim R = 1)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
    [Algebra.Etale R B] [Module.Finite R B]
    (B' : Type u) [CommRing B'] [Algebra B B'] [Algebra K B'] [IsScalarTower K B B']
    [Algebra.Etale B B'] [Module.Finite B B'],
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (O' : ValuationSubring K') (_ : O'.comap (algebraMap K K') = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c c' : TemperedFundamentalGroups.ModelCode O')
      (j : Spec (CommRingCat.of (TensorProduct K K' B)) ⟶ c.scheme)
      (j' : Spec (CommRingCat.of (TensorProduct K K' B')) ⟶ c'.scheme)
      (ψ : c'.scheme ⟶ c.scheme),
      ModelCode.IsSemistable ϖ' c ∧ ModelCode.IsSemistable ϖ' c' ∧
      ModelCode.IsSplit ϖ' c ∧ ModelCode.IsSplit ϖ' c' ∧
      IsOpenImmersion j ∧ IsOpenImmersion j' ∧ IsFinite ψ ∧
      ψ ≫ c.toSpec = c'.toSpec ∧ ModelCode.IsHarmonic ϖ' ψ ∧
      j ≫ c.toSpec = Spec.map (CommRingCat.ofHom
        ((Algebra.TensorProduct.includeLeftRingHom).comp O'.subtype)) ∧
      j' ≫ ψ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id K K')
        (IsScalarTower.toAlgHom K B B')).toRingHom) ≫ j

/-- **W8′(a): finite maps of semistable models are harmonic on dual graphs** (Blueprint §9.7,
§10.3; consumed by Theorem B). Let `O` be a discrete valuation ring with uniformizer `ϖ`, `c`, `c'`
semistable projective `O`-models and `ψ : c' ⟶ c` a finite morphism over `O` (as produced by
`Statement.Simultaneous`). Dual graphs are read off on the special fibres
(`SemistableReduction/DualGraph.lean`). Then:
* the thickness of a node is well defined, and every node point has a thickness `n ≥ 1`;
* every node `x'` of `c'` of thickness `n'` maps either to a node of `c` of thickness `n = d·n'`
  for some `d ≥ 1` (the local degree; lengths are scaled by it), or to a smooth point of `c`
  lying on exactly one component;
* every component of `c'` maps onto a component of `c`;
* points over nodes are nodes; in particular every node of `c` on the image of a component `v'`
  of `c'` is the image of a node on `v'` (edge lifting).

Superseded by `Statement.HarmonicGeneral`; not targeted (the W-chain proves harmonicity for the
models it produces, as a clause of `Statement.Simultaneous`). -/
def Statement.Harmonic : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (_ : Irreducible ϖ) (c c' : TemperedFundamentalGroups.ModelCode O) (ψ : c'.scheme ⟶ c.scheme),
    IsFinite ψ → ψ ≫ c.toSpec = c'.toSpec →
    ModelCode.IsSemistable ϖ c → ModelCode.IsSemistable ϖ c' → ModelCode.IsHarmonic ϖ ψ

/-- A component `v` of a model `c'` is **contracted** by `ψ : c' ⟶ c` if it maps to a point. -/
def ModelCode.IsContracted {O : Type u} [CommRing O] {c c' : TemperedFundamentalGroups.ModelCode O}
    (ψ : c'.scheme ⟶ c.scheme) (v : Set c'.scheme) : Prop :=
  ∃ y, ψ '' v = {y}

/-- A walk in the dual graph of `c'` **crosses** the point `x` of `c` along `ψ : c' ⟶ c`: it
starts and ends on non-contracted components, its inner components are contracted to `x`, its
nodes lie over `x`, and it uses each node at most once. -/
def ModelCode.Walk.IsCrossing {O : Type u} [CommRing O] [IsLocalRing O]
    {c c' : TemperedFundamentalGroups.ModelCode O} (ψ : c'.scheme ⟶ c.scheme) (x : c.scheme)
    (w : ModelCode.Walk c') : Prop :=
  1 ≤ w.k ∧ Function.Injective w.x ∧ ¬ ModelCode.IsContracted ψ (w.v 0) ∧
    ¬ ModelCode.IsContracted ψ (w.v (Fin.last w.k)) ∧
    (∀ i : Fin (w.k + 1), i ≠ 0 → i ≠ Fin.last w.k → ψ '' w.v i = {x}) ∧
    (∀ i, ψ (w.x i) = x)

/-- **W8′(b′): modifications of semistable models** (Blueprint §9.7, §10.3; consumed by
Theorem B). Let `O` be a discrete valuation ring with uniformizer `ϖ`, `c`, `c'` split
(`ModelCode.IsSplit`) semistable projective `O`-models and `ψ : c' ⟶ c` a morphism over `O` which
is an isomorphism over the generic fibre. Then:
* (forest) the components of `c'` contracted to a point `x` contain no cycle of the dual graph;
* (node chains) over a node `x` of thickness `n`, `ψ⁻¹(x)` is connected, some walk crosses `x`,
  and the thicknesses of the nodes of every walk crossing `x` sum to `n`;
* every non-contracted component maps onto a component, and a node all of whose components are
  non-contracted maps to a node of the same thickness.

(Without splitness the dual graph read off on the special fibre is not the geometric one: a
non-split node is a self-loop, and the chain clause fails.) Superseded by
`Statement.HarmonicGeneral`; not targeted. -/
def Statement.Modification : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (ϖ : O) (_ : Irreducible ϖ)
    (c c' : TemperedFundamentalGroups.ModelCode O) (ψ : c'.scheme ⟶ c.scheme),
    ψ ≫ c.toSpec = c'.toSpec → IsIso (ψ ∣_ ModelCode.genericOpen c) →
    ModelCode.IsSemistable ϖ c → ModelCode.IsSemistable ϖ c' →
    ModelCode.IsSplit ϖ c → ModelCode.IsSplit ϖ c' →
      (∀ (x : c.scheme) (w : ModelCode.Walk c'), w.IsCycle →
        ¬ ∀ i, ψ '' w.v i = {x}) ∧
      (∀ (x : c.scheme) (n : ℕ), ModelCode.IsNodeOfThickness ϖ c x n →
        _root_.IsConnected (ψ ⁻¹' {x}) ∧ (∃ w : ModelCode.Walk c', w.IsCrossing ψ x) ∧
        ∀ w : ModelCode.Walk c', w.IsCrossing ψ x → ∀ t : Fin w.k → ℕ,
          (∀ i, ModelCode.IsNodeOfThickness ϖ c' (w.x i) (t i)) → ∑ i, t i = n) ∧
      (∀ v' ∈ ModelCode.components c',
        ModelCode.IsContracted ψ v' ∨ ψ '' v' ∈ ModelCode.components c) ∧
      (∀ (x' : c'.scheme) (n' : ℕ), ModelCode.IsNodeOfThickness ϖ c' x' n' →
        (∀ v' ∈ ModelCode.components c', x' ∈ v' → ¬ ModelCode.IsContracted ψ v') →
          ModelCode.IsNodeOfThickness ϖ c (ψ x') n')

/-- **W8′ (general form): harmonicity of maps of split semistable models which are finite on
generic fibres** (targeted; consumed by Theorem B, B5; Blueprint §9.7). Let `O` be a discrete
valuation ring with uniformizer `ϖ`, `c`, `c'` split semistable projective `O`-models and
`ψ : c ⟶ c'` a morphism over `O`, finite over the generic fibre of `c'` (a finite map composed
with a modification). For every node `x'` of `c'` of thickness `n'`:
* (H1) for every component `v` of `c` mapping onto a component through `x'`, some walk crosses
  `x'` (inner components contracted to `x'`, nodes over `x'`) starting on `v`, ending on a
  component mapping onto a component through `x'` (onto the other branch if `x'` lies on two
  components), with `∑ dᵢ nᵢ = n'` (`nᵢ` the thicknesses, `dᵢ` the local degrees,
  `ModelCode.HasLocalDegree`);
* (H2) every walk crossing `x'` has `∑ dᵢ nᵢ ≤ n'`;
* (H3) a node of `c` which does not map to a node maps to a point lying on exactly one component.
Supersedes `Statement.Harmonic` (finite `ψ`) and `Statement.Modification` (birational `ψ`). -/
def Statement.HarmonicGeneral : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (_ : Irreducible ϖ) (c c' : TemperedFundamentalGroups.ModelCode O) (ψ : c.scheme ⟶ c'.scheme),
    ψ ≫ c'.toSpec = c.toSpec → IsFinite (ψ ∣_ ModelCode.genericOpen c') →
    ModelCode.IsSemistable ϖ c → ModelCode.IsSemistable ϖ c' →
    ModelCode.IsSplit ϖ c → ModelCode.IsSplit ϖ c' →
      (∀ (x' : c'.scheme) (n' : ℕ), ModelCode.IsNodeOfThickness ϖ c' x' n' →
        ∀ v ∈ ModelCode.components c, (∃ w' ∈ ModelCode.components c', x' ∈ w' ∧ ψ '' v = w') →
          ∃ w : ModelCode.Walk c, w.v 0 = v ∧ w.IsCrossing ψ x' ∧
            (∃ w' ∈ ModelCode.components c', x' ∈ w' ∧ ψ '' w.v (Fin.last w.k) = w' ∧
              ((∃ w'' ∈ ModelCode.components c', x' ∈ w'' ∧ w'' ≠ ψ '' v) → w' ≠ ψ '' v)) ∧
            ∃ t dd : Fin w.k → ℕ, (∀ i, ModelCode.IsNodeOfThickness ϖ c (w.x i) (t i)) ∧
              (∀ i, ModelCode.HasLocalDegree ϖ ψ (w.x i) (dd i)) ∧ ∑ i, dd i * t i = n') ∧
      (∀ (x' : c'.scheme) (n' : ℕ), ModelCode.IsNodeOfThickness ϖ c' x' n' →
        ∀ w : ModelCode.Walk c, w.IsCrossing ψ x' → ∀ t dd : Fin w.k → ℕ,
          (∀ i, ModelCode.IsNodeOfThickness ϖ c (w.x i) (t i)) →
          (∀ i, ModelCode.HasLocalDegree ϖ ψ (w.x i) (dd i)) → ∑ i, dd i * t i ≤ n') ∧
      (∀ x : c.scheme, ModelCode.IsNodePt c x → ¬ ModelCode.IsNodePt c' (ψ x) →
        ∃! w', w' ∈ ModelCode.components c' ∧ ψ x ∈ w')

end TemperedFundamentalGroups.SemistableReduction
