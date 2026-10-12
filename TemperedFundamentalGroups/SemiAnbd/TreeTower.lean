/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.GroupTheory.Commensurable
import TemperedFundamentalGroups.SemiAnbd.TreeFixedPoint

/-!
# Tree towers: verticial subgroups of tempered groups (Blueprint §12.4, W1–W8)

The tempered fundamental group of a semi-graph of anabelioids (or of a curve, §11.3, G6) is an
inverse limit `lim_j Γ_j` of discrete groups `Γ_j`, each acting on a tree `T_j` (the universal
combinatorial covering of the dual semi-graph of a finite Galois covering, barycentrically
subdivided). A **tree tower** over a group `Γ` records this structure: a category `J` of levels,
homomorphisms `ρ j : Γ →* G j`, trees `T j` with a 2-colouring (`kind`: vertices and edges of the
dual graph) preserved by the actions, and equivariant, non-expanding maps of trees along the
morphisms of `J` (non-expanding rather than graph morphisms, and not required to be functorial,
since for curves components of a covering may be contracted to points; functoriality,
`TreeTower.IsFunctorial`, is only used for W5).

A **system** is a compatible family of vertices `s j ∈ T j`; `Γ` acts on systems and
`stab s` is the stabilizer. Verticial subgroups are the `stab s` for systems of vertex kind.

## Main results

* `TreeTower.exists_adj_fixed_inf` (**W2**): `stab s ⊓ stab s'` fixes the neighbour of `s k`
  towards `s' k` (the geodesics of `T k` are fixed pointwise, T4).
* `TreeTower.HI s` (edge groups have infinite index in the verticial subgroup of `s`).
* `TreeTower.commensurator_stab` (**W3**): under `HI s`, `stab s` is commensurably terminal.
* `TreeTower.eq_of_stab_le` (**W4**): under `HI s`, `stab s ≤ stab s'` implies `s = s'`.
* `TreeTower.exists_le_stab_of_bounded` (**W5**): a subgroup moving a system by a bounded
  amount at every level fixes a system (T3 levelwise, König's lemma).
* `TreeTower.VertexCorrespondence` (**W7**) and `TreeTower.adjacency_iff` (**W8**): an
  isomorphism of tower groups that maps verticial subgroups (of systems satisfying `HI`) onto
  verticial subgroups induces a unique equivariant bijection of these systems; under the stated
  PSC-type adjacency hypothesis it preserves the adjacency of the limit tree.
-/

universe u v w x

open CategoryTheory TemperedFundamentalGroups.TreeGeom
open scoped Pointwise

namespace TemperedFundamentalGroups

/-- A **tree tower** over a group `Γ`, indexed by a category `J`. -/
structure TreeTower (Γ : Type x) [Group Γ] (J : Type u) [Category.{v} J] where
  /-- The group at level `j`. -/
  G : J → Type w
  [grp : ∀ j, Group (G j)]
  /-- The projection to level `j`. -/
  ρ : ∀ j, Γ →* G j
  /-- The vertices of the tree at level `j`. -/
  V : J → Type w
  /-- The tree at level `j`. -/
  graph : ∀ j, SimpleGraph (V j)
  isTree : ∀ j, (graph j).IsTree
  [act : ∀ j, MulAction (G j) (V j)]
  adj_smul : ∀ j (g : G j) (x y : V j), (graph j).Adj (g • x) (g • y) ↔ (graph j).Adj x y
  /-- The 2-colouring: `true` for vertices, `false` for edges of the dual semi-graph. -/
  kind : ∀ j, V j → Bool
  kind_smul : ∀ j (g : G j) (x : V j), kind j (g • x) = kind j x
  kind_adj : ∀ j (x y : V j), (graph j).Adj x y → kind j x ≠ kind j y
  /-- The map of trees along a morphism of levels. -/
  map : ∀ {j k : J}, (j ⟶ k) → V j → V k
  map_smul : ∀ {j k : J} (f : j ⟶ k) (g : Γ) (x : V j), map f (ρ j g • x) = ρ k g • map f x
  map_adj : ∀ {j k : J} (f : j ⟶ k) (x y : V j), (graph j).Adj x y →
    (graph k).Adj (map f x) (map f y) ∨ map f x = map f y

namespace TreeTower

attribute [instance] grp act

variable {Γ : Type x} [Group Γ] {J : Type u} [Category.{v} J] (T : TreeTower.{u, v, w} Γ J)

lemma not_adj_smul (j : J) (g : T.G j) (x : T.V j) : ¬ (T.graph j).Adj x (g • x) :=
  fun h ↦ T.kind_adj j _ _ h (T.kind_smul j g x).symm

lemma dist_map_le {j k : J} (f : j ⟶ k) (x y : T.V j) :
    (T.graph k).dist (T.map f x) (T.map f y) ≤ (T.graph j).dist x y :=
  TreeGeom.dist_map_le (T.isTree j).connected (T.map f) (T.map_adj f) x y

/-- A **system**: a compatible family of vertices of the trees. -/
def Sys : Type _ := {s : ∀ j, T.V j // ∀ {j k : J} (f : j ⟶ k), T.map f (s j) = s k}

variable {T}

@[ext]
lemma Sys.ext {s s' : T.Sys} (h : ∀ j, s.1 j = s'.1 j) : s = s' := Subtype.ext (funext h)

instance : MulAction Γ T.Sys where
  smul g s := ⟨fun j ↦ T.ρ j g • s.1 j, fun f ↦ by rw [T.map_smul, s.2]⟩
  one_smul s := Sys.ext fun j ↦ by
    change T.ρ j 1 • s.1 j = s.1 j
    rw [map_one, one_smul]
  mul_smul g h s := Sys.ext fun j ↦ by
    change T.ρ j (g * h) • s.1 j = T.ρ j g • T.ρ j h • s.1 j
    rw [map_mul, mul_smul]

@[simp]
lemma smul_apply (g : Γ) (s : T.Sys) (j : J) : (g • s).1 j = T.ρ j g • s.1 j := rfl

variable (T) in
/-- The subgroup of `Γ` fixing a vertex `w` of the tree at level `k`. -/
def fixAt (k : J) (w : T.V k) : Subgroup Γ := (MulAction.stabilizer (T.G k) w).comap (T.ρ k)

lemma mem_fixAt {k : J} {w : T.V k} {g : Γ} : g ∈ T.fixAt k w ↔ T.ρ k g • w = w := Iff.rfl

/-- The stabilizer of a system: for a system of vertex kind a **verticial subgroup**, for a
system of edge kind an **edge-like subgroup**. -/
def stab (s : T.Sys) : Subgroup Γ := MulAction.stabilizer Γ s

lemma mem_stab {s : T.Sys} {g : Γ} : g ∈ stab s ↔ ∀ j, T.ρ j g • s.1 j = s.1 j := by
  rw [stab, MulAction.mem_stabilizer_iff]
  exact ⟨fun h j ↦ congrArg (fun s : T.Sys ↦ s.1 j) h, fun h ↦ Sys.ext h⟩

lemma stab_le_fixAt (s : T.Sys) (j : J) : stab s ≤ T.fixAt j (s.1 j) :=
  fun _ hg ↦ mem_stab.1 hg j

/-- Verticial systems: of vertex kind at every level. -/
def IsVert (s : T.Sys) : Prop := ∀ j, T.kind j (s.1 j) = true

lemma IsVert.smul {s : T.Sys} (hs : IsVert s) (g : Γ) : IsVert (g • s) := fun j ↦ by
  rw [smul_apply, T.kind_smul]; exact hs j

/-! ### W1 -/

/-- **W1**: the stabilizer of a translate is the conjugate. -/
lemma stab_smul (g : Γ) (s : T.Sys) : stab (g • s) = ConjAct.toConjAct g • stab s := by
  ext h
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    ConjAct.toConjAct_smul, stab, stab, MulAction.mem_stabilizer_iff,
    MulAction.mem_stabilizer_iff, inv_inv, mul_smul, mul_smul, inv_smul_eq_iff]

/-- Systems that differ at a level differ at every deeper level. -/
lemma ne_of_ne {s s' : T.Sys} {j k : J} (f : k ⟶ j) (h : s.1 j ≠ s'.1 j) : s.1 k ≠ s'.1 k :=
  fun hk ↦ h (by rw [← s.2 f, ← s'.2 f, hk])

/-! ### W2 -/

/-- **W2**: for systems differing at level `k`, `stab s ⊓ stab s'` fixes the neighbour of
`s k` towards `s' k`. -/
theorem exists_adj_fixed_inf {s s' : T.Sys} {k : J} (h : s.1 k ≠ s'.1 k) :
    ∃ w, (T.graph k).Adj (s.1 k) w ∧ stab s ⊓ stab s' ≤ T.fixAt k w := by
  obtain ⟨w, hw, hwd⟩ := exists_adj_geodesic (T.isTree k).connected h
  refine ⟨w, hw, fun g hg ↦ ?_⟩
  exact smul_eq_of_mem_geodesic (T.isTree k) (T.adj_smul k) (mem_stab.1 hg.1 k)
    (mem_stab.1 hg.2 k) hwd

/-! ### The hypothesis (HI) -/

variable (T) in
/-- **(HI s)**: at arbitrarily deep levels, the stabilizers in `stab s` of the neighbours of
`s k` have index `> n` (or infinite index) in `stab s`, for every `n`. ("Edge-like subgroups
have infinite index in verticial subgroups".) -/
def HI (s : T.Sys) : Prop :=
  ∀ (n : ℕ) (j : J), ∃ (k : J) (_ : k ⟶ j), ∀ w, (T.graph k).Adj (s.1 k) w →
    (T.fixAt k w).relIndex (stab s) = 0 ∨ n < (T.fixAt k w).relIndex (stab s)

/-- A subgroup of `stab s` of finite index `m` fixes no neighbour of `s k` at the levels given
by `(HI s)` for `m`. -/
lemma not_le_fixAt {s : T.Sys} {H : Subgroup Γ} {k : J} {w : T.V k}
    (hk : (T.fixAt k w).relIndex (stab s) = 0 ∨ H.relIndex (stab s) <
      (T.fixAt k w).relIndex (stab s))
    (hH : H.relIndex (stab s) ≠ 0) (hle : H ⊓ stab s ≤ T.fixAt k w) : False := by
  have hdvd : (T.fixAt k w).relIndex (stab s) ∣ H.relIndex (stab s) := by
    rw [← Subgroup.inf_relIndex_right H]
    exact Subgroup.relIndex_dvd_of_le_left _ hle
  have hpos := Nat.pos_of_ne_zero hH
  rcases hk with hk | hk
  · rw [hk, zero_dvd_iff] at hdvd; exact hH hdvd
  · exact absurd (Nat.le_of_dvd hpos hdvd) (not_le.2 hk)

/-! ### W3 and W4 -/

/-- **W4**: under `(HI s)`, a verticial subgroup is contained in no other one:
`stab s ≤ stab s'` implies `s = s'`. -/
theorem eq_of_stab_le {s s' : T.Sys} (hs : T.HI s) (hle : stab s ≤ stab s') : s = s' := by
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, s.1 j ≠ s'.1 j := by
    by_contra! h; exact hne (Sys.ext h)
  obtain ⟨k, f, hk⟩ := hs 1 j
  obtain ⟨w, hw, hfix⟩ := exists_adj_fixed_inf (ne_of_ne f hj)
  refine not_le_fixAt (s := s) (H := stab s) (k := k) (w := w) ?_
    (by rw [Subgroup.relIndex_self]; exact one_ne_zero) (le_trans (by simp [hle]) hfix)
  rw [Subgroup.relIndex_self]
  exact hk w hw

/-- Under `(HI s)` the system is determined by its stabilizer. -/
theorem eq_of_stab_eq {s s' : T.Sys} (hs : T.HI s) (h : stab s = stab s') : s = s' :=
  eq_of_stab_le hs h.le

/-- **W3, commensurable terminality** ([SemiAnbd] 3.7(i)-type): under `(HI s)` the
commensurator of `stab s` is `stab s`. -/
theorem commensurator_stab {s : T.Sys} (hs : T.HI s) :
    Subgroup.Commensurable.commensurator (stab s) = stab s := by
  refine le_antisymm (fun g hg ↦ ?_) (fun g hg ↦ ?_)
  · rw [Subgroup.Commensurable.commensurator_mem_iff, ← stab_smul] at hg
    by_contra hgs
    have hne : g • s ≠ s := fun h ↦ hgs (by rw [stab, MulAction.mem_stabilizer_iff]; exact h)
    obtain ⟨j, hj⟩ : ∃ j, s.1 j ≠ (g • s).1 j := by
      by_contra! h; exact hne (Sys.ext fun j ↦ (h j).symm)
    obtain ⟨k, f, hk⟩ := hs ((stab (g • s)).relIndex (stab s)) j
    obtain ⟨w, hw, hfix⟩ := exists_adj_fixed_inf (ne_of_ne f hj)
    exact not_le_fixAt (hk w hw) hg.1 (by rw [inf_comm]; exact hfix)
  · rw [Subgroup.Commensurable.commensurator_mem_iff, ← stab_smul]
    have : g • s = s := by rwa [stab, MulAction.mem_stabilizer_iff] at hg
    rw [this]

/-- Verticial subgroups satisfying `(HI)` are self-normalising. -/
theorem normalizer_stab {s : T.Sys} (hs : T.HI s) :
    Subgroup.normalizer (stab s : Set Γ) = stab s := by
  refine le_antisymm (fun g hg ↦ ?_) Subgroup.le_normalizer
  rw [← commensurator_stab hs, Subgroup.Commensurable.commensurator_mem_iff]
  have : ConjAct.toConjAct g • stab s = stab s := by
    ext h
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
      ConjAct.toConjAct_smul, inv_inv, Subgroup.mem_normalizer_iff.1 hg]
    simp [mul_assoc]
  rw [this]

/-! ### W5: subgroups with bounded displacement fix a system -/

section Bounded

variable [IsCofilteredOrEmpty J]

variable (T) in
/-- The maps of trees are functorial. (Not part of the definition: for curves, components can be
contracted by transition maps, and the induced maps of vertices need not compose.) -/
structure IsFunctorial : Prop where
  map_id : ∀ j (x : T.V j), T.map (𝟙 j) x = x
  map_comp : ∀ {j k l : J} (f : j ⟶ k) (g : k ⟶ l) (x : T.V j),
    T.map (f ≫ g) x = T.map g (T.map f x)

/-- **W5**: in a functorial tower of locally finite trees, a subgroup `H` moving a system `x` by
at most `D` at every level fixes a system `s` with `d(x j, s j) ≤ D` at every level (T3 at each
level; the fixed vertices in the `D`-balls form an inverse system of finite nonempty sets,
König). -/
theorem exists_le_stab_of_bounded (hT : T.IsFunctorial)
    (hlf : ∀ j (v : T.V j), ((T.graph j).neighborSet v).Finite)
    (H : Subgroup Γ) (x : T.Sys) (D : ℕ)
    (hD : ∀ j, ∀ g ∈ H, (T.graph j).dist (x.1 j) (T.ρ j g • x.1 j) ≤ D) :
    ∃ s : T.Sys, H ≤ stab s ∧ ∀ j, (T.graph j).dist (x.1 j) (s.1 j) ≤ D := by
  let S : ∀ j, Set (T.V j) := fun j ↦
    {v | (T.graph j).dist (x.1 j) v ≤ D ∧ ∀ g ∈ H, T.ρ j g • v = v}
  have hS : ∀ {j k : J} (f : j ⟶ k) (v : T.V j), v ∈ S j → T.map f v ∈ S k := by
    intro j k f v ⟨hv, hfix⟩
    refine ⟨?_, fun g hg ↦ ?_⟩
    · rw [← x.2 f]; exact (T.dist_map_le f _ _).trans hv
    · rw [← T.map_smul, hfix g hg]
  let F : J ⥤ Type w :=
    { obj j := S j
      map f := TypeCat.ofHom fun v ↦ ⟨T.map f v.1, hS f v.1 v.2⟩
      map_id j := by ext v; exact hT.map_id j v.1
      map_comp f g := by ext v; exact hT.map_comp f g v.1 }
  have hfin : ∀ j, Finite (F.obj j) := fun j ↦
    ((finite_ball (T.isTree j).connected (hlf j) (x.1 j) D).subset fun v hv ↦ hv.1).to_subtype
  have hne : ∀ j, Nonempty (F.obj j) := by
    intro j
    let Λ := H.map (T.ρ j)
    obtain ⟨c, hc, hcD⟩ := exists_fixed_of_bounded (Γ := Λ) (T.isTree j) (hlf j)
      (fun g a b ↦ T.adj_smul j g a b) (fun g a ↦ T.not_adj_smul j g a) (x.1 j) D
      (by
        rintro ⟨_, g, hg, rfl⟩
        exact hD j g hg)
    exact ⟨⟨c, hcD, fun g hg ↦ hc ⟨T.ρ j g, g, hg, rfl⟩⟩⟩
  obtain ⟨u, hu⟩ := nonempty_sections_of_finite_cofiltered_system F
  refine ⟨⟨fun j ↦ (u j).1, fun f ↦ congrArg Subtype.val (hu f)⟩, fun g hg ↦ ?_,
    fun j ↦ (u j).2.1⟩
  exact mem_stab.2 fun j ↦ (u j).2.2 g hg

end Bounded

/-! ### W7, W8: verticial isomorphisms -/

lemma mem_stab_smul {g x : Γ} {s : T.Sys} : x ∈ stab (g • s) ↔ g⁻¹ * x * g ∈ stab s := by
  rw [stab_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    ConjAct.toConjAct_smul, inv_inv]

lemma fixAt_smul (k : J) (g : Γ) (w : T.V k) :
    T.fixAt k (T.ρ k g • w) = ConjAct.toConjAct g • T.fixAt k w := by
  ext h
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, ConjAct.toConjAct_smul,
    mem_fixAt, mem_fixAt, inv_inv, map_mul, map_mul, mul_smul, mul_smul, map_inv,
    inv_smul_eq_iff]

/-- `(HI)` is invariant under translation. -/
lemma HI.smul {s : T.Sys} (hs : T.HI s) (g : Γ) : T.HI (g • s) := by
  intro n j
  obtain ⟨k, f, hk⟩ := hs n j
  refine ⟨k, f, fun w' hw' ↦ ?_⟩
  obtain ⟨w, rfl⟩ : ∃ w, w' = T.ρ k g • w := ⟨(T.ρ k g)⁻¹ • w', (smul_inv_smul _ _).symm⟩
  rw [smul_apply, T.adj_smul] at hw'
  rw [fixAt_smul, stab_smul, Subgroup.relIndex_pointwise_smul]
  exact hk w hw'

variable (T) in
/-- Verticial systems satisfying `(HI)`. -/
abbrev VSys : Type _ := {s : T.Sys // IsVert s ∧ T.HI s}

instance : MulAction Γ T.VSys where
  smul g s := ⟨g • s.1, s.2.1.smul g, s.2.2.smul g⟩
  one_smul s := Subtype.ext (one_smul Γ s.1)
  mul_smul g h s := Subtype.ext (mul_smul g h s.1)

@[simp]
lemma VSys.smul_val (g : Γ) (s : T.VSys) : (g • s).1 = g • s.1 := rfl

lemma VSys.ext_stab {s s' : T.VSys} (h : stab s.1 = stab s'.1) : s = s' :=
  Subtype.ext (eq_of_stab_eq s.2.2 h)

/-- Group-theoretic adjacency of systems: different, with nontrivial intersection of
stabilizers. -/
def AdjG (s s' : T.Sys) : Prop := s ≠ s' ∧ stab s ⊓ stab s' ≠ ⊥

/-- Adjacency in the limit tree: different, at distance at most `2` at every level (distances
can only grow along deeper levels). -/
def LimAdj (s s' : T.Sys) : Prop := s ≠ s' ∧ ∀ k, (T.graph k).dist (s.1 k) (s'.1 k) ≤ 2

variable (T) in
/-- **PSC-type adjacency hypothesis**: two different verticial systems have intersecting
stabilizers exactly when they are adjacent in the limit tree. -/
def PSCAdj : Prop := ∀ s s' : T.VSys, AdjG s.1 s'.1 ↔ LimAdj s.1 s'.1

variable {Γ' : Type*} [Group Γ'] {J' : Type*} [Category J'] {T' : TreeTower.{_, _, w} Γ' J'}

/-- A **vertex correspondence** for an isomorphism `α : Γ ≃* Γ'`: a bijection of verticial
systems (with `(HI)`) compatible with the stabilizers. -/
structure VertexCorrespondence (α : Γ ≃* Γ') where
  /-- The bijection of systems. -/
  e : T.VSys ≃ T'.VSys
  map_stab : ∀ s, (stab s.1).map α.toMonoidHom = stab (e s).1

namespace VertexCorrespondence

variable {α : Γ ≃* Γ'}

lemma map_stab_inj {H K : Subgroup Γ} (h : H.map α.toMonoidHom = K.map α.toMonoidHom) : H = K :=
  Subgroup.map_injective α.injective h

/-- **W7, uniqueness**: a vertex correspondence is determined by `α`. -/
lemma ext' (E E' : VertexCorrespondence (T := T) (T' := T') α) (s : T.VSys) : E.e s = E'.e s :=
  VSys.ext_stab (by rw [← E.map_stab, ← E'.map_stab])

/-- **W7, equivariance**: `e (g • s) = α g • e s`. -/
theorem e_smul (E : VertexCorrespondence (T := T) (T' := T') α) (g : Γ) (s : T.VSys) :
    E.e (g • s) = α g • E.e s := by
  refine VSys.ext_stab ?_
  ext x
  rw [← E.map_stab, VSys.smul_val, VSys.smul_val, mem_stab_smul, ← E.map_stab,
    Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, mem_stab_smul]
  simp [mul_assoc]

/-- **W7, adjacency**: `e` preserves group-theoretic adjacency. -/
theorem adjG_iff (E : VertexCorrespondence (T := T) (T' := T') α) (s s' : T.VSys) :
    AdjG s.1 s'.1 ↔ AdjG (E.e s).1 (E.e s').1 := by
  have hinf : (stab s.1 ⊓ stab s'.1).map α.toMonoidHom = stab (E.e s).1 ⊓ stab (E.e s').1 := by
    rw [Subgroup.map_inf_eq _ _ α.toMonoidHom α.injective, E.map_stab, E.map_stab]
  have hne : s.1 ≠ s'.1 ↔ (E.e s).1 ≠ (E.e s').1 := by
    rw [ne_eq, ne_eq, ← Subtype.ext_iff, ← Subtype.ext_iff, E.e.injective.eq_iff]
  rw [AdjG, AdjG, hne, ← hinf]
  exact and_congr_right' (not_congr (Subgroup.map_eq_bot_iff_of_injective _ α.injective).symm)

/-- **W8**: under the PSC-type adjacency hypothesis on both towers, `e` preserves adjacency of
the limit trees: `α` is graphic on vertices and edges between them. -/
theorem limAdj_iff (E : VertexCorrespondence (T := T) (T' := T') α) (hT : T.PSCAdj)
    (hT' : T'.PSCAdj) (s s' : T.VSys) : LimAdj s.1 s'.1 ↔ LimAdj (E.e s).1 (E.e s').1 := by
  rw [← hT, ← hT', E.adjG_iff]

end VertexCorrespondence

/-- **W7, existence**: an isomorphism mapping the verticial subgroups (of systems with `(HI)`) of
`T` onto those of `T'` has a vertex correspondence. -/
theorem nonempty_vertexCorrespondence (α : Γ ≃* Γ')
    (hα : ∀ s : T.VSys, ∃ s' : T'.VSys, (stab s.1).map α.toMonoidHom = stab s'.1)
    (hα' : ∀ s' : T'.VSys, ∃ s : T.VSys, (stab s.1).map α.toMonoidHom = stab s'.1) :
    Nonempty (VertexCorrespondence (T := T) (T' := T') α) := by
  choose e he using hα
  choose e' he' using hα'
  refine ⟨⟨⟨e, e', fun s ↦ ?_, fun s' ↦ ?_⟩, he⟩⟩
  · exact VSys.ext_stab (VertexCorrespondence.map_stab_inj (by rw [he', he]))
  · exact VSys.ext_stab (by rw [← he, he'])

/-! ### Pulling back towers along group homomorphisms -/

/-- The tower pulled back along a homomorphism `φ : Γ' →* Γ`. -/
def comap {Γ' : Type*} [Group Γ'] (φ : Γ' →* Γ) : TreeTower Γ' J :=
  { T with
    ρ := fun j ↦ (T.ρ j).comp φ
    map_smul := fun f g x ↦ T.map_smul f (φ g) x }

/-- Systems of the pulled back tower are the systems of `T`. -/
def comapSys {Γ' : Type*} [Group Γ'] (φ : Γ' →* Γ) : T.Sys ≃ (T.comap φ).Sys := Equiv.refl _

lemma stab_comap {Γ' : Type*} [Group Γ'] (φ : Γ' →* Γ) (s : T.Sys) :
    stab (T.comapSys φ s) = (stab s).comap φ := by
  ext g
  rw [mem_stab, Subgroup.mem_comap, mem_stab]
  rfl

end TreeTower

end TemperedFundamentalGroups
