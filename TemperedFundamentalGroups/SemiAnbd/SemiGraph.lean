/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
# Semi-graphs (Blueprint §12.1, S1–S3)

Mochizuki's semi-graphs ([SemiAnbd] §1): a set of vertices `V`, a set of edges `E`, each edge
`e` having two branches `(e, true)` and `(e, false)`, each branch abutting to a vertex or to
nothing (`ζ : E × Bool → Option V`). An edge is *closed* if both branches abut, *open* (a cusp)
if exactly one does. Loops (both branches abutting to the same vertex) are allowed.

* `SemiGraph`, `SemiGraph.IsClosedEdge`, `SemiGraph.IsOpenEdge`, `SemiGraph.Abuts`.
* `SemiGraph.incGraph`: the incidence (barycentric) graph on `V ⊕ E`, bipartite by construction
  (`SemiGraph.kind`, `SemiGraph.kind_ne_of_adj`); `SemiGraph.Connected`.
* `SemiGraph.Hom`: morphisms (vertices to vertices, edges to edges, branches to branches,
  compatible with `ζ`), `SemiGraph.Hom.incHom` the induced map of incidence graphs,
  `SemiGraph.Hom.id`, `SemiGraph.Hom.comp`.
-/

universe u

namespace TemperedFundamentalGroups

/-- A **semi-graph**: vertices, edges with two branches each, and for each branch the vertex it
abuts to (or `none`). -/
structure SemiGraph where
  /-- The vertices. -/
  V : Type u
  /-- The edges. -/
  E : Type u
  /-- The vertex a branch abuts to, if any. -/
  ζ : E × Bool → Option V

namespace SemiGraph

variable (𝔾 : SemiGraph.{u})

/-- The edge `e` abuts to the vertex `v` (through some branch). -/
def Abuts (v : 𝔾.V) (e : 𝔾.E) : Prop := ∃ b, 𝔾.ζ (e, b) = some v

/-- A closed edge: both branches abut to vertices. -/
def IsClosedEdge (e : 𝔾.E) : Prop := (𝔾.ζ (e, true)).isSome ∧ (𝔾.ζ (e, false)).isSome

/-- An open edge (a cusp): exactly one branch abuts to a vertex. -/
def IsOpenEdge (e : 𝔾.E) : Prop := (𝔾.ζ (e, true)).isSome ≠ (𝔾.ζ (e, false)).isSome

/-- The **incidence graph** (barycentric subdivision): `v ~ e` iff `e` abuts to `v`. -/
def incGraph : SimpleGraph (𝔾.V ⊕ 𝔾.E) where
  Adj
    | .inl v, .inr e => 𝔾.Abuts v e
    | .inr e, .inl v => 𝔾.Abuts v e
    | _, _ => False
  symm := ⟨by rintro (v | e) (w | f) h <;> simp_all⟩
  loopless := ⟨by rintro (v | e) h <;> simp_all⟩

@[simp]
lemma incGraph_adj_inl_inr (v : 𝔾.V) (e : 𝔾.E) : 𝔾.incGraph.Adj (.inl v) (.inr e) ↔ 𝔾.Abuts v e :=
  Iff.rfl

@[simp]
lemma incGraph_adj_inr_inl (v : 𝔾.V) (e : 𝔾.E) : 𝔾.incGraph.Adj (.inr e) (.inl v) ↔ 𝔾.Abuts v e :=
  Iff.rfl

@[simp]
lemma not_incGraph_adj_inl_inl (v w : 𝔾.V) : ¬ 𝔾.incGraph.Adj (.inl v) (.inl w) := id

@[simp]
lemma not_incGraph_adj_inr_inr (e f : 𝔾.E) : ¬ 𝔾.incGraph.Adj (.inr e) (.inr f) := id

/-- The 2-colouring of the incidence graph: `true` on vertices, `false` on edges. -/
def kind : 𝔾.V ⊕ 𝔾.E → Bool := Sum.isLeft

lemma kind_ne_of_adj {x y : 𝔾.V ⊕ 𝔾.E} (h : 𝔾.incGraph.Adj x y) : 𝔾.kind x ≠ 𝔾.kind y := by
  rcases x with v | e <;> rcases y with w | f <;> simp_all [kind]

/-- A semi-graph is **connected** if its incidence graph is. -/
def Connected : Prop := 𝔾.incGraph.Connected

/-- A closed edge abuts to the vertices of both its branches. -/
lemma abuts_of_ζ {e : 𝔾.E} {b : Bool} {v : 𝔾.V} (h : 𝔾.ζ (e, b) = some v) : 𝔾.Abuts v e :=
  ⟨b, h⟩

variable {𝔾} {ℍ 𝕂 : SemiGraph.{u}}

/-- A **morphism of semi-graphs**: maps of vertices and edges and a map of branches over the map
of edges, compatible with `ζ` on abutting branches. -/
structure Hom (𝔾 ℍ : SemiGraph.{u}) where
  /-- The map of vertices. -/
  fV : 𝔾.V → ℍ.V
  /-- The map of edges. -/
  fE : 𝔾.E → ℍ.E
  /-- The map of branches of `e` to branches of `fE e`. -/
  fB : 𝔾.E → Bool → Bool
  map_ζ : ∀ e b v, 𝔾.ζ (e, b) = some v → ℍ.ζ (fE e, fB e b) = some (fV v)

namespace Hom

/-- The identity morphism. -/
def id (𝔾 : SemiGraph.{u}) : Hom 𝔾 𝔾 := ⟨fun v ↦ v, fun e ↦ e, fun _ b ↦ b, fun _ _ _ h ↦ h⟩

/-- The composition of morphisms. -/
def comp (φ : Hom 𝔾 ℍ) (ψ : Hom ℍ 𝕂) : Hom 𝔾 𝕂 where
  fV := ψ.fV ∘ φ.fV
  fE := ψ.fE ∘ φ.fE
  fB e b := ψ.fB (φ.fE e) (φ.fB e b)
  map_ζ e b v h := ψ.map_ζ _ _ _ (φ.map_ζ e b v h)

/-- **S3**: a morphism of semi-graphs is a morphism of incidence graphs. -/
def incHom (φ : Hom 𝔾 ℍ) : 𝔾.incGraph →g ℍ.incGraph where
  toFun := Sum.map φ.fV φ.fE
  map_rel' := by
    rintro (v | e) (w | f) h
    · exact h.elim
    · obtain ⟨b, hb⟩ := h
      exact ⟨φ.fB f b, φ.map_ζ f b v hb⟩
    · obtain ⟨b, hb⟩ := h
      exact ⟨φ.fB e b, φ.map_ζ e b w hb⟩
    · exact h.elim

@[simp]
lemma incHom_inl (φ : Hom 𝔾 ℍ) (v : 𝔾.V) : φ.incHom (.inl v) = .inl (φ.fV v) := rfl

@[simp]
lemma incHom_inr (φ : Hom 𝔾 ℍ) (e : 𝔾.E) : φ.incHom (.inr e) = .inr (φ.fE e) := rfl

lemma incHom_comp (φ : Hom 𝔾 ℍ) (ψ : Hom ℍ 𝕂) :
    (φ.comp ψ).incHom = ψ.incHom.comp φ.incHom := by
  ext (v | e) <;> rfl

/-- Morphisms preserve the colouring of incidence graphs. -/
lemma kind_incHom (φ : Hom 𝔾 ℍ) (x : 𝔾.V ⊕ 𝔾.E) : ℍ.kind (φ.incHom x) = 𝔾.kind x := by
  rcases x with v | e <;> rfl

end Hom

end SemiGraph

end TemperedFundamentalGroups
