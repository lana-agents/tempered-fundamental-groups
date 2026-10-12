/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemiAnbd.TreeTower

/-!
# Compact subgroups of tree towers (Blueprint §12.4, W6, W9–W12)

We follow the proof of [SemiAnbd] Thm. 3.7(iii) ("every compact subgroup of the tempered
fundamental group is contained in a verticial subgroup"). A compact subgroup `H` of the tempered
group has finite image at every level, so it fixes a vertex of every tree (T3). Mochizuki's
hypothesis that the semi-graph of anabelioids is *totally estranged* ([SemiAnbd] Def. 2.4(iv))
implies that a nontrivial `H` fixes at most two vertices (joined by an edge) at cofinally many
levels; the fixed vertices then form an inverse system of finite nonempty sets, whose sections
(König's lemma) are compatible systems fixed by `H`.

* `TreeTower.fixSet`, `TreeTower.nonempty_fixSet`: the vertices fixed by `H` at a level.
* **`TreeTower.exists_sys_of_finite_fixSet`** (**W6**, conditional form): in a functorial tower,
  a subgroup with finite images whose fixed sets (inside a map-stable colour class) are finite at
  cofinally many levels fixes a compatible system.
* `TreeTower.Estranged` (**W9**, [SemiAnbd] Def. 2.4(iv)-type): every nontrivial element fixes,
  at cofinally many levels, only a set of diameter `≤ 2`.
  **`TreeTower.exists_le_stab_of_estranged`**, **`TreeTower.exists_isVert_le_stab_of_estranged`**:
  under estrangement every nontrivial subgroup with finite images lies in a (verticial, if the
  maps preserve colours and edges are not inverted) subgroup `stab s` ([SemiAnbd] Thm. 3.7(iii)).
* `TreeTower.Elevated` (**W10**, [SemiAnbd] Def. 2.4(i)-type) and **`TreeTower.HI_of_elevated`**:
  the hypothesis `(HI)` follows from elevatedness (the argument of [SemiAnbd] Prop. 2.6).
* **`TreeTower.limAdj_of_adjG`**, **`TreeTower.adjG_of_limAdj`**,
  **`TreeTower.pscAdj_of_estranged`** (**W11**): the PSC-type adjacency hypothesis `PSCAdj` of
  CG3 follows from estrangement, the absence of branch inversions and nontrivial edge-like
  subgroups.
* `TreeTower.restrict` (**W12**): the tower restricted along a functor `J' ⥤ J` (a subsystem of
  levels), `TreeTower.isFunctorial_restrict`, `TreeTower.stab_le_stab_restrict`.
-/

universe u v w x

open CategoryTheory TemperedFundamentalGroups.TreeGeom

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type x} [Group Γ] {J : Type u} [Category.{v} J] (T : TreeTower.{u, v, w} Γ J)

/-! ### Fixed sets -/

/-- The vertices of the tree at level `j` fixed by `H`. -/
def fixSet (j : J) (H : Subgroup Γ) : Set (T.V j) := {v | ∀ g ∈ H, T.ρ j g • v = v}

variable {T}

lemma map_mem_fixSet {j k : J} (f : j ⟶ k) {H : Subgroup Γ} {v : T.V j}
    (hv : v ∈ T.fixSet j H) : T.map f v ∈ T.fixSet k H := fun g hg ↦ by
  rw [← T.map_smul, hv g hg]

/-- A subgroup with finite image at level `j` fixes a vertex of the tree (T3). -/
lemma nonempty_fixSet {j : J} {H : Subgroup Γ} (hH : Finite (H.map (T.ρ j))) :
    (T.fixSet j H).Nonempty := by
  obtain ⟨c, hc⟩ := exists_fixed_of_finite (Γ := H.map (T.ρ j)) (T.isTree j)
    (fun g a b ↦ T.adj_smul j g a b) (fun g a ↦ T.not_adj_smul j g a)
  exact ⟨c, fun g hg ↦ hc ⟨T.ρ j g, g, hg, rfl⟩⟩

lemma stab_le_iff {H : Subgroup Γ} {s : T.Sys} : H ≤ stab s ↔ ∀ j, s.1 j ∈ T.fixSet j H :=
  ⟨fun h j _ hg ↦ mem_stab.1 (h hg) j, fun h g hg ↦ mem_stab.2 fun j ↦ h j g hg⟩

/-! ### W6: König's lemma for fixed sets -/

section Konig

variable [IsCofilteredOrEmpty J]

/-- A common lower bound of two levels, with equal composites to a third level. -/
lemma exists_cone_eq {j k k' : J} (f : k ⟶ j) (f' : k' ⟶ j) :
    ∃ (l : J) (a : l ⟶ k) (b : l ⟶ k'), a ≫ f = b ≫ f' := by
  obtain ⟨W, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs k k'
  obtain ⟨W', c, hc⟩ := IsCofilteredOrEmpty.cone_maps (a ≫ f) (b ≫ f')
  exact ⟨W', c ≫ a, c ≫ b, by simpa using hc⟩

/-- **W6, conditional form** ([SemiAnbd] Thm. 3.7(iii), proof): in a functorial tower, let `P` be
a family of sets of vertices stable under the maps (e.g. a colour class), and `H` a subgroup
fixing a vertex of `P j` at every level, such that at cofinally many levels only finitely many
vertices of `P` are fixed. Then `H` fixes a compatible system with values in `P`. -/
theorem exists_sys_of_finite_fixSet (hT : T.IsFunctorial) (P : ∀ j, Set (T.V j))
    (hP : ∀ {j k : J} (f : j ⟶ k) (v : T.V j), v ∈ P j → T.map f v ∈ P k) (H : Subgroup Γ)
    (hne : ∀ j, (T.fixSet j H ∩ P j).Nonempty)
    (hfin : ∀ j, ∃ (k : J) (_ : k ⟶ j), (T.fixSet k H ∩ P k).Finite) :
    ∃ s : T.Sys, H ≤ stab s ∧ ∀ j, s.1 j ∈ P j := by
  classical
  -- the fixed vertices of `P`
  let A : ∀ j, Set (T.V j) := fun j ↦ T.fixSet j H ∩ P j
  have hA : ∀ {j k : J} (f : j ⟶ k) (v : T.V j), v ∈ A j → T.map f v ∈ A k :=
    fun f v hv ↦ ⟨map_mem_fixSet f hv.1, hP f v hv.2⟩
  -- the images of the finite fixed sets of deeper levels
  let img : ∀ {j k : J}, (k ⟶ j) → Set (T.V j) := fun f ↦ T.map f '' A _
  have img_comp : ∀ {j k l : J} (a : l ⟶ k) (f : k ⟶ j), img (a ≫ f) ⊆ img f := by
    rintro j k l a f _ ⟨u, hu, rfl⟩
    exact ⟨T.map a u, hA a u hu, (hT.map_comp a f u).symm⟩
  let S : ∀ j, Set (T.V j) := fun j ↦
    {v | v ∈ A j ∧ ∀ (k : J) (f : k ⟶ j), (A k).Finite → v ∈ img f}
  have hS : ∀ {j j' : J} (f' : j ⟶ j') (v : T.V j), v ∈ S j → T.map f' v ∈ S j' := by
    intro j j' f' v ⟨hv, hvS⟩
    refine ⟨hA f' v hv, fun k h hk ↦ ?_⟩
    obtain ⟨W, a, b, hab⟩ := exists_cone_eq h f'
    obtain ⟨l, d, hl⟩ := hfin W
    obtain ⟨u, hu, rfl⟩ := hvS l (d ≫ b) hl
    refine ⟨T.map (d ≫ a) u, hA _ u hu, ?_⟩
    rw [← hT.map_comp, ← hT.map_comp, Category.assoc, hab, Category.assoc]
  have hSfin : ∀ j, (S j).Finite := fun j ↦ by
    obtain ⟨k, f, hk⟩ := hfin j
    exact (hk.image (T.map f)).subset fun v hv ↦ hv.2 k f hk
  have hSne : ∀ j, (S j).Nonempty := by
    intro j
    -- a deeper level whose image has minimal cardinality
    have hex : ∃ n, ∃ (k : J) (f : k ⟶ j), (A k).Finite ∧ (img f).ncard = n := by
      obtain ⟨k, f, hk⟩ := hfin j
      exact ⟨_, k, f, hk, rfl⟩
    obtain ⟨k, f, hk, hmin⟩ := Nat.find_spec hex
    have hle : ∀ (k' : J) (f' : k' ⟶ j), (A k').Finite → Nat.find hex ≤ (img f').ncard :=
      fun k' f' hk' ↦ Nat.find_min' hex ⟨k', f', hk', rfl⟩
    obtain ⟨u, hu⟩ := hne k
    refine ⟨T.map f u, ⟨hA f u hu, fun k' f' hk' ↦ ?_⟩⟩
    obtain ⟨W, a, b, hab⟩ := exists_cone_eq f f'
    obtain ⟨l, d, hl⟩ := hfin W
    -- the image from `l` is contained in both images and has the minimal cardinality
    have h₁ : img ((d ≫ a) ≫ f) ⊆ img f := img_comp _ _
    have h₂ : img ((d ≫ a) ≫ f) ⊆ img f' := by
      rw [Category.assoc, hab, ← Category.assoc]; exact img_comp _ _
    have hfinf : (img f).Finite := hk.image _
    have heq : img ((d ≫ a) ≫ f) = img f :=
      Set.eq_of_subset_of_ncard_le h₁ (by rw [hmin]; exact hle l _ hl) hfinf
    exact h₂ (heq ▸ ⟨u, hu, rfl⟩)
  let F : J ⥤ Type w :=
    { obj j := S j
      map f := TypeCat.ofHom fun v ↦ ⟨T.map f v.1, hS f v.1 v.2⟩
      map_id j := by ext v; exact hT.map_id j v.1
      map_comp f g := by ext v; exact hT.map_comp f g v.1 }
  have : ∀ j, Finite (F.obj j) := fun j ↦ (hSfin j).to_subtype
  have : ∀ j, Nonempty (F.obj j) := fun j ↦ (hSne j).to_subtype
  obtain ⟨σ, hσ⟩ := nonempty_sections_of_finite_cofiltered_system F
  exact ⟨⟨fun j ↦ (σ j).1, fun f ↦ congrArg Subtype.val (hσ f)⟩,
    stab_le_iff.2 fun j ↦ (σ j).2.1.1, fun j ↦ (σ j).2.1.2⟩

/-- **W6, conditional form**: a subgroup with finite images whose fixed sets are finite at
cofinally many levels fixes a compatible system. -/
theorem exists_le_stab_of_finite_fixSet (hT : T.IsFunctorial) (H : Subgroup Γ)
    (hH : ∀ j, Finite (H.map (T.ρ j)))
    (hfin : ∀ j, ∃ (k : J) (_ : k ⟶ j), (T.fixSet k H).Finite) :
    ∃ s : T.Sys, H ≤ stab s := by
  obtain ⟨s, hs, -⟩ := exists_sys_of_finite_fixSet hT (fun _ ↦ Set.univ)
    (fun _ _ _ ↦ Set.mem_univ _) H
    (fun j ↦ by rw [Set.inter_univ]; exact nonempty_fixSet (hH j))
    (fun j ↦ by simp only [Set.inter_univ]; exact hfin j)
  exact ⟨s, hs⟩

end Konig

/-! ### Colours: preserved colours and branch inversions -/

variable (T) in
/-- The maps of trees preserve the colours (no component is contracted to a node). -/
def PreservesKind : Prop :=
  ∀ {j k : J} (f : j ⟶ k) (v : T.V j), T.kind k (T.map f v) = T.kind j v

variable (T) in
/-- **No branch inversions**: an element fixing a vertex of edge kind fixes its neighbours (in
[SemiAnbd], the action on the universal combinatorial coverings is over `𝒢`, so it does not
switch the branches of an edge). -/
def NoBranchSwap : Prop :=
  ∀ j (g : T.G j) (e w : T.V j), T.kind j e = false → (T.graph j).Adj e w → g • e = e → g • w = w

lemma exists_adj_of_nontrivial (j : J) [Nontrivial (T.V j)] (v : T.V j) :
    ∃ w, (T.graph j).Adj v w := by
  obtain ⟨u, hu⟩ := exists_ne v
  obtain ⟨w, hw, -⟩ := exists_adj_geodesic (T.isTree j).connected hu.symm
  exact ⟨w, hw⟩

/-- Without branch inversions, a subgroup with finite image fixes a vertex of vertex kind. -/
lemma nonempty_fixSet_inter_kind (hB : T.NoBranchSwap) {j : J} [Nontrivial (T.V j)]
    {H : Subgroup Γ} (hH : Finite (H.map (T.ρ j))) :
    (T.fixSet j H ∩ {v | T.kind j v = true}).Nonempty := by
  obtain ⟨c, hc⟩ := nonempty_fixSet hH
  cases hk : T.kind j c
  · obtain ⟨w, hw⟩ := exists_adj_of_nontrivial j c
    refine ⟨w, fun g hg ↦ hB j _ c w hk hw (hc g hg), ?_⟩
    have := T.kind_adj j c w hw
    rw [hk] at this
    cases hw' : T.kind j w <;> simp_all
  · exact ⟨c, hc, hk⟩

/-! ### W9: estrangement -/

variable (T) in
/-- **Estrangement** ([SemiAnbd] Def. 2.4(iv), in the form used in the proof of Thm. 3.7(iii)):
at cofinally many levels, a nontrivial element of `Γ` fixes only a set of diameter `≤ 2` (at
most two vertices of vertex kind, joined by an edge). -/
def Estranged : Prop :=
  ∀ g : Γ, g ≠ 1 → ∀ j, ∃ (k : J) (_ : k ⟶ j), ∀ x y : T.V k,
    T.ρ k g • x = x → T.ρ k g • y = y → (T.graph k).dist x y ≤ 2

/-- Under estrangement, nontrivial subgroups have finite fixed sets at cofinally many levels. -/
lemma finite_fixSet_of_estranged (hE : T.Estranged)
    (hlf : ∀ j (v : T.V j), ((T.graph j).neighborSet v).Finite) {H : Subgroup Γ} (hH : H ≠ ⊥)
    (j : J) : ∃ (k : J) (_ : k ⟶ j), (T.fixSet k H).Finite := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hH
  replace hg1 : g ≠ 1 := fun h ↦ hg1 (Subtype.ext h)
  obtain ⟨k, f, hk⟩ := hE g hg1 j
  refine ⟨k, f, ?_⟩
  rcases (T.fixSet k H).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]; exact Set.finite_empty
  · exact (finite_ball (T.isTree k).connected (hlf k) x 2).subset fun y hy ↦
      hk x y (hx g hg) (hy g hg)

section Konig

variable [IsCofilteredOrEmpty J]

/-- **W9, [SemiAnbd] Thm. 3.7(iii) for estranged functorial towers**: a nontrivial subgroup with
finite images at every level (e.g. a compact subgroup of the limit of discrete groups) is
contained in `stab s` for a compatible system `s`. -/
theorem exists_le_stab_of_estranged (hT : T.IsFunctorial) (hE : T.Estranged)
    (hlf : ∀ j (v : T.V j), ((T.graph j).neighborSet v).Finite) (H : Subgroup Γ) (hH1 : H ≠ ⊥)
    (hH : ∀ j, Finite (H.map (T.ρ j))) : ∃ s : T.Sys, H ≤ stab s :=
  exists_le_stab_of_finite_fixSet hT H hH (finite_fixSet_of_estranged hE hlf hH1)

/-- **W9, verticial form**: if moreover the maps preserve colours and edges are not inverted,
`s` can be taken verticial: every nontrivial subgroup with finite images lies in a verticial
subgroup. -/
theorem exists_isVert_le_stab_of_estranged (hT : T.IsFunctorial) (hK : T.PreservesKind)
    (hB : T.NoBranchSwap) (hE : T.Estranged)
    (hlf : ∀ j (v : T.V j), ((T.graph j).neighborSet v).Finite) [∀ j, Nontrivial (T.V j)]
    (H : Subgroup Γ) (hH1 : H ≠ ⊥) (hH : ∀ j, Finite (H.map (T.ρ j))) :
    ∃ s : T.Sys, IsVert s ∧ H ≤ stab s := by
  obtain ⟨s, hs, hv⟩ := exists_sys_of_finite_fixSet hT (fun j ↦ {v | T.kind j v = true})
    (fun f v (hv : T.kind _ v = true) ↦ (hK f v).trans hv) H
    (fun j ↦ nonempty_fixSet_inter_kind hB (hH j))
    (fun j ↦ (finite_fixSet_of_estranged hE hlf hH1 j).imp fun _ ⟨f, hf⟩ ↦
      ⟨f, hf.subset Set.inter_subset_left⟩)
  exact ⟨s, hv, hs⟩

end Konig

/-! ### W10: elevated systems satisfy `(HI)` -/

variable (T) in
/-- **Elevated systems** ([SemiAnbd] Def. 2.4(i)-type): for every `n`, at arbitrarily deep levels
`k` the verticial subgroup contains a subgroup of order `> n` meeting the stabilizers of all
neighbours of `s k` trivially. -/
def Elevated (s : T.Sys) : Prop :=
  ∀ (n : ℕ) (j : J), ∃ (k : J) (_ : k ⟶ j) (N : Subgroup Γ), N ≤ stab s ∧ n < Nat.card N ∧
    ∀ w, (T.graph k).Adj (s.1 k) w → N ⊓ T.fixAt k w = ⊥

/-- **W10** (the argument of [SemiAnbd] Prop. 2.6): elevated systems satisfy `(HI)`. -/
theorem HI_of_elevated {s : T.Sys} (hs : T.Elevated s) : T.HI s := by
  intro n j
  obtain ⟨k, f, N, hN, hn, hw⟩ := hs n j
  refine ⟨k, f, fun w hadj ↦ ?_⟩
  by_cases h0 : (T.fixAt k w).relIndex (stab s) = 0
  · exact .inl h0
  refine .inr (lt_of_lt_of_le hn ?_)
  have h1 : (T.fixAt k w).relIndex N = Nat.card N := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hw w hadj, Subgroup.relIndex_bot_left]
  rw [← h1]
  exact Subgroup.relIndex_le_of_le_right hN h0

/-! ### W11: the adjacency hypothesis `PSCAdj` -/

/-- Under estrangement, group-theoretically adjacent systems are adjacent in the limit tree. -/
theorem limAdj_of_adjG (hE : T.Estranged) {s s' : T.Sys} (h : AdjG s s') : LimAdj s s' := by
  refine ⟨h.1, fun j ↦ ?_⟩
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.2
  have hg1' : g ≠ 1 := fun h ↦ hg1 (Subtype.ext h)
  obtain ⟨k, f, hk⟩ := hE g hg1' j
  rw [← s.2 f, ← s'.2 f]
  exact (T.dist_map_le f _ _).trans (hk _ _ (mem_stab.1 hg.1 k) (mem_stab.1 hg.2 k))

/-- Two different vertices of vertex kind at distance `≤ 2` are at distance exactly `2`. -/
lemma dist_eq_two {k : J} {x y : T.V k} (hx : T.kind k x = true) (hy : T.kind k y = true)
    (hne : x ≠ y) (hd : (T.graph k).dist x y ≤ 2) : (T.graph k).dist x y = 2 := by
  have hpos := (T.isTree k).connected.pos_dist_of_ne hne
  have h1 : (T.graph k).dist x y ≠ 1 := fun h ↦
    T.kind_adj k x y (SimpleGraph.dist_eq_one_iff_adj.1 h) (hx.trans hy.symm)
  omega

/-- The midpoint of two vertices at distance `2`. -/
lemma exists_midpoint {k : J} {x y : T.V k} (hd : (T.graph k).dist x y = 2) :
    ∃ m, (T.graph k).dist x m = 1 ∧ (T.graph k).dist m y = 1 := by
  have hne : x ≠ y := fun h ↦ by rw [h, SimpleGraph.dist_self] at hd; omega
  obtain ⟨m, hm, hmd⟩ := exists_adj_geodesic (T.isTree k).connected hne
  rw [SimpleGraph.dist_eq_one_iff_adj.2 hm] at hmd
  exact ⟨m, SimpleGraph.dist_eq_one_iff_adj.2 hm, by omega⟩

/-- Midpoints are unique. -/
lemma eq_of_midpoint {k : J} {x y m m' : T.V k} (hd : (T.graph k).dist x y = 2)
    (hm : (T.graph k).dist x m = 1 ∧ (T.graph k).dist m y = 1)
    (hm' : (T.graph k).dist x m' ≤ 1 ∧ (T.graph k).dist m' y ≤ 1) : m' = m := by
  have hconn := (T.isTree k).connected
  have htri := hconn.dist_triangle (u := x) (v := m') (w := y)
  have h1 : (T.graph k).dist x m' = 1 := by omega
  refine eq_of_mem_geodesic (T.isTree k) (x := x) (y := y) ?_ ?_ ?_
  · omega
  · omega
  · omega

section Midpoint

variable [IsCofilteredOrEmpty J] (hT : T.IsFunctorial)
include hT

/-- **W11**: in a functorial tower without branch inversions, two verticial systems adjacent in
the limit tree are group-theoretically adjacent as soon as the edge-like subgroups (stabilizers
of systems that are eventually of edge kind) are nontrivial: the midpoints form an edge-like
system whose stabilizer fixes both systems. -/
theorem adjG_of_limAdj (hB : T.NoBranchSwap)
    (hedge : ∀ e : T.Sys, (∀ j, ∃ (k : J) (_ : k ⟶ j), T.kind k (e.1 k) = false) → stab e ≠ ⊥)
    {s s' : T.Sys} (hs : IsVert s) (hs' : IsVert s') (h : LimAdj s s') : AdjG s s' := by
  classical
  refine ⟨h.1, ?_⟩
  obtain ⟨j₀, hj₀⟩ : ∃ j, s.1 j ≠ s'.1 j := by
    by_contra! hc; exact h.1 (Sys.ext hc)
  -- the levels at which the systems differ, where they are at distance `2`
  let D : J → Prop := fun k ↦ s.1 k ≠ s'.1 k
  have hD2 : ∀ k, D k → (T.graph k).dist (s.1 k) (s'.1 k) = 2 := fun k hk ↦
    dist_eq_two (hs k) (hs' k) hk (h.2 k)
  have hDdeep : ∀ j, ∃ (k : J) (_ : k ⟶ j), D k := fun j ↦ by
    obtain ⟨W, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j j₀
    exact ⟨W, a, ne_of_ne b hj₀⟩
  have hDmap : ∀ {k l : J} (_ : l ⟶ k), D k → D l := fun f hk ↦ ne_of_ne f hk
  let mid : ∀ k, D k → T.V k := fun k hk ↦ (exists_midpoint (hD2 k hk)).choose
  have hmid : ∀ k (hk : D k), (T.graph k).dist (s.1 k) (mid k hk) = 1 ∧
      (T.graph k).dist (mid k hk) (s'.1 k) = 1 := fun k hk ↦
    (exists_midpoint (hD2 k hk)).choose_spec
  -- midpoints are mapped to midpoints
  have hmap : ∀ {k l : J} (f : l ⟶ k) (hl : D l) (hk : D k), T.map f (mid l hl) = mid k hk := by
    intro k l f hl hk
    refine eq_of_midpoint (hD2 k hk) (hmid k hk) ⟨?_, ?_⟩
    · rw [← s.2 f]; exact (T.dist_map_le f _ _).trans (hmid l hl).1.le
    · rw [← s'.2 f]; exact (T.dist_map_le f _ _).trans (hmid l hl).2.le
  -- the edge-like system of midpoints
  let lev : ∀ j, Σ' (k : J) (_ : k ⟶ j), D k := fun j ↦
    ⟨(hDdeep j).choose, (hDdeep j).choose_spec.choose, (hDdeep j).choose_spec.choose_spec⟩
  let e : T.Sys := ⟨fun j ↦ T.map (lev j).2.1 (mid _ (lev j).2.2), fun {j j'} h ↦ by
    obtain ⟨W, a, b, hab⟩ := exists_cone_eq ((lev j).2.1 ≫ h) (lev j').2.1
    have hW : D W := hDmap a (lev j).2.2
    change T.map h (T.map (lev j).2.1 (mid _ (lev j).2.2)) =
      T.map (lev j').2.1 (mid _ (lev j').2.2)
    rw [← hmap a hW (lev j).2.2, ← hmap b hW (lev j').2.2]
    simp only [← hT.map_comp, Category.assoc, hab]⟩
  have he : ∀ k (hk : D k), e.1 k = mid k hk := fun k hk ↦
    hmap (lev k).2.1 (lev k).2.2 hk
  refine fun hbot ↦ hedge e (fun j ↦ ?_) (le_bot_iff.1 (le_trans ?_ hbot.le))
  · obtain ⟨k, f, hk⟩ := hDdeep j
    refine ⟨k, f, ?_⟩
    rw [he k hk]
    have hadj := SimpleGraph.dist_eq_one_iff_adj.1 (hmid k hk).1
    have := T.kind_adj k _ _ hadj
    rw [hs k] at this
    cases hm' : T.kind k (mid k hk) <;> simp_all
  · intro g hg
    have hfix : ∀ k, D k → T.ρ k g • s.1 k = s.1 k ∧ T.ρ k g • s'.1 k = s'.1 k := by
      intro k hk
      have hadj := SimpleGraph.dist_eq_one_iff_adj.1 (hmid k hk).1
      have hadj' := SimpleGraph.dist_eq_one_iff_adj.1 (hmid k hk).2
      have hkind : T.kind k (mid k hk) = false := by
        have := T.kind_adj k _ _ hadj
        rw [hs k] at this
        cases hm' : T.kind k (mid k hk) <;> simp_all
      have hgm : T.ρ k g • mid k hk = mid k hk := by rw [← he k hk]; exact mem_stab.1 hg k
      exact ⟨hB k _ _ _ hkind hadj.symm hgm, hB k _ _ _ hkind hadj' hgm⟩
    refine ⟨mem_stab.2 fun j ↦ ?_, mem_stab.2 fun j ↦ ?_⟩ <;>
    obtain ⟨k, f, hk⟩ := hDdeep j
    · rw [← s.2 f, ← T.map_smul, (hfix k hk).1]
    · rw [← s'.2 f, ← T.map_smul, (hfix k hk).2]

/-- **W11**: `PSCAdj` (the adjacency hypothesis of CG3) holds for estranged functorial towers
without branch inversions whose edge-like subgroups are nontrivial. -/
theorem pscAdj_of_estranged (hE : T.Estranged) (hB : T.NoBranchSwap)
    (hedge : ∀ e : T.Sys, (∀ j, ∃ (k : J) (_ : k ⟶ j), T.kind k (e.1 k) = false) → stab e ≠ ⊥) :
    T.PSCAdj := fun s s' ↦
  ⟨limAdj_of_adjG hE, adjG_of_limAdj hT hB hedge s.2.1 s'.2.1⟩

end Midpoint

/-! ### W12: restriction to a subsystem of levels -/

section Restrict

variable {J' : Type*} [Category J']

variable (T) in
/-- The tower restricted along a functor `F : J' ⥤ J` (e.g. a subcategory of levels). -/
def restrict (F : J' ⥤ J) : TreeTower Γ J' where
  G j := T.G (F.obj j)
  ρ j := T.ρ (F.obj j)
  V j := T.V (F.obj j)
  graph j := T.graph (F.obj j)
  isTree j := T.isTree (F.obj j)
  act j := T.act (F.obj j)
  adj_smul j := T.adj_smul (F.obj j)
  kind j := T.kind (F.obj j)
  kind_smul j := T.kind_smul (F.obj j)
  kind_adj j := T.kind_adj (F.obj j)
  map f := T.map (F.map f)
  map_smul f := T.map_smul (F.map f)
  map_adj f := T.map_adj (F.map f)

/-- **W12**: the restricted tower is functorial as soon as the maps of `T` are functorial along
the morphisms in the image of `F`. -/
theorem isFunctorial_restrict (F : J' ⥤ J) (hid : ∀ j (x : T.V (F.obj j)), T.map (𝟙 _) x = x)
    (hcomp : ∀ {j k l : J'} (f : j ⟶ k) (g : k ⟶ l) (x : T.V (F.obj j)),
      T.map (F.map f ≫ F.map g) x = T.map (F.map g) (T.map (F.map f) x)) :
    (T.restrict F).IsFunctorial where
  map_id j x := by
    change T.map (F.map (𝟙 j)) x = x
    rw [F.map_id]; exact hid j x
  map_comp f g x := by
    change T.map (F.map (f ≫ g)) x = T.map (F.map g) (T.map (F.map f) x)
    rw [F.map_comp]; exact hcomp f g x

/-- Systems of `T` restrict to systems of the restricted tower. -/
def restrictSys (F : J' ⥤ J) (s : T.Sys) : (T.restrict F).Sys :=
  ⟨fun j ↦ s.1 (F.obj j), fun f ↦ s.2 (F.map f)⟩

lemma stab_le_stab_restrict (F : J' ⥤ J) (s : T.Sys) : stab s ≤ stab (restrictSys F s) :=
  fun _ hg ↦ mem_stab.2 fun j ↦ mem_stab.1 hg (F.obj j)

end Restrict

end TreeTower

end TemperedFundamentalGroups
