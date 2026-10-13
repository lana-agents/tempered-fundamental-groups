/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.TreeTowerCompact

/-!
# Estrangement element by element: tame and wild parts (Blueprint §12.10, M4)

`TreeTower.Estranged` (W9) asks, for every nontrivial `g`, that at cofinally many levels the
fixed set of `g` have diameter `≤ 2`. This file splits that condition along a set `P` of levels
(intended: the *tame* levels, coverings of degree prime to `p`):

* `TreeTower.SmallFixAt k g`, `TreeTower.EstrangedElt g` (the condition for one element),
  `TreeTower.EstrangedOn S` (for the nontrivial elements of a set `S`), with
  `estranged_iff_estrangedOn_univ` and `estranged_comap_iff` (pulling back along an injective
  homomorphism, e.g. `Δ.subtype`);
* `TreeTower.actKer P`: the elements acting trivially on the trees of all levels in `P`;
* **`TreeTower.WildEstranged Δ P`** (the shape of missing theorem **M4**): the nontrivial
  elements of `Δ ⊓ actKer P` are estranged; `TreeTower.TameEstranged Δ P`: the elements of `Δ`
  acting nontrivially on some `P`-level are estranged; **`estrangedOn_iff_tame_wild`**;
  monotonicity `WildEstranged.mono` and `wildEstranged_bot_iff` (with no tame levels, M4 is all
  of the estrangement of `Δ`);
* **necessary conditions** (`exists_moved_of_estrangedElt`, `WildEstranged.exists_not_mem`): if
  all trees contain two vertices at distance `> 2`, an estranged element moves a vertex at
  cofinally many levels; so M4 forces every nontrivial element of the wild kernel to act
  nontrivially on trees of non-`P` levels below every level (wild estrangement cannot be checked
  on tame levels);
* **line levels** (the single loop / `n`-gon case, e.g. the dual graph of the Tate curve and of
  its topological coverings, whose universal covering tree is a line): `LineAt k` (every vertex
  has at most two neighbours); `smul_eq_of_lineAt` (an automorphism of such a tree fixing two
  distinct vertices is trivial); `smallFixAt_of_lineAt`, `estrangedElt_of_lineAt`;
  **`estranged_iff_of_lineAt`**: for a tower of line trees with vertices at distance `> 2`,
  estrangement is equivalent to faithfulness at cofinally many finite levels;
* reduction to sub-towers `estrangedElt_of_restrict` (estrangement along a subsystem of levels
  which is cofinal in the sense that every level receives a map from one of its levels).
-/

universe u v w x

open CategoryTheory SimpleGraph TemperedFundamentalGroups.TreeGeom

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type x} [Group Γ] {J : Type u} [Category.{v} J] (T : TreeTower.{u, v, w} Γ J)

/-! ### Estrangement of single elements -/

/-- At level `k`, the fixed set of `g` has diameter `≤ 2`. -/
def SmallFixAt (k : J) (g : Γ) : Prop :=
  ∀ x y : T.V k, T.ρ k g • x = x → T.ρ k g • y = y → (T.graph k).dist x y ≤ 2

/-- `g` is **estranged**: at cofinally many levels its fixed set has diameter `≤ 2`. -/
def EstrangedElt (g : Γ) : Prop := ∀ j, ∃ (k : J) (_ : k ⟶ j), T.SmallFixAt k g

/-- All nontrivial elements of `S` are estranged. -/
def EstrangedOn (S : Set Γ) : Prop := ∀ g ∈ S, g ≠ 1 → T.EstrangedElt g

lemma estranged_iff_estrangedOn_univ : T.Estranged ↔ T.EstrangedOn Set.univ :=
  ⟨fun h g _ hg ↦ h g hg, fun h g hg ↦ h g trivial hg⟩

variable {T}

lemma EstrangedOn.mono {S S' : Set Γ} (h : T.EstrangedOn S') (hS : S ⊆ S') : T.EstrangedOn S :=
  fun g hg ↦ h g (hS hg)

lemma estrangedOn_union {S S' : Set Γ} :
    T.EstrangedOn (S ∪ S') ↔ T.EstrangedOn S ∧ T.EstrangedOn S' :=
  ⟨fun h ↦ ⟨h.mono Set.subset_union_left, h.mono Set.subset_union_right⟩,
    fun h g hg ↦ hg.elim (h.1 g) (h.2 g)⟩

/-- Estrangement of a pulled back tower along an injective homomorphism `φ` is the estrangement
of the elements of the image of `φ`. -/
lemma estranged_comap_iff {Γ' : Type*} [Group Γ'] (φ : Γ' →* Γ) (hφ : Function.Injective φ) :
    (T.comap φ).Estranged ↔ T.EstrangedOn (Set.range φ) := by
  constructor
  · rintro h _ ⟨g, rfl⟩ hg
    exact h g fun h1 ↦ hg (by rw [h1, map_one])
  · intro h g hg
    exact h (φ g) ⟨g, rfl⟩ fun h1 ↦ hg (hφ (by rw [h1, map_one]))

/-- For a subgroup `Δ`: `T.comap Δ.subtype` is estranged iff the nontrivial elements of `Δ`
are. -/
lemma estranged_comap_subtype_iff (Δ : Subgroup Γ) :
    (T.comap Δ.subtype).Estranged ↔ T.EstrangedOn Δ := by
  rw [estranged_comap_iff _ Δ.subtype_injective, Subgroup.coe_subtype, Subtype.range_coe]

/-! ### The kernel of the action on a set of levels -/

variable (T) in
/-- The elements acting trivially on the trees of all levels in `P` (for `P` the tame levels:
the elements invisible to the tame part of the tower). -/
def actKer (P : J → Prop) : Subgroup Γ := ⨅ (j : J) (_ : P j) (v : T.V j), T.fixAt j v

lemma mem_actKer {P : J → Prop} {g : Γ} :
    g ∈ T.actKer P ↔ ∀ j, P j → ∀ v : T.V j, T.ρ j g • v = v := by
  simp only [actKer, Subgroup.mem_iInf, mem_fixAt]

lemma actKer_anti {P P' : J → Prop} (h : ∀ j, P j → P' j) : T.actKer P' ≤ T.actKer P :=
  fun _ hg ↦ mem_actKer.2 fun j hj v ↦ mem_actKer.1 hg j (h j hj) v

lemma actKer_bot : T.actKer (fun _ ↦ False) = ⊤ :=
  eq_top_iff.2 fun _ _ ↦ mem_actKer.2 fun _ h ↦ h.elim

/-! ### Tame and wild estrangement -/

variable (T) in
/-- **The shape of missing theorem M4 (wild estrangement)**: every nontrivial element of `Δ`
acting trivially on the trees of all `P`-levels is estranged. -/
def WildEstranged (Δ : Subgroup Γ) (P : J → Prop) : Prop :=
  T.EstrangedOn ((Δ ⊓ T.actKer P : Subgroup Γ) : Set Γ)

variable (T) in
/-- **Tame estrangement**: every element of `Δ` acting nontrivially on the tree of some
`P`-level is estranged (at cofinally many levels of the whole tower). -/
def TameEstranged (Δ : Subgroup Γ) (P : J → Prop) : Prop :=
  T.EstrangedOn {g | g ∈ Δ ∧ g ∉ T.actKer P}

/-- **Estrangement of `Δ` = tame estrangement + wild estrangement (M4).** -/
theorem estrangedOn_iff_tame_wild (Δ : Subgroup Γ) (P : J → Prop) :
    T.EstrangedOn Δ ↔ T.TameEstranged Δ P ∧ T.WildEstranged Δ P := by
  rw [TameEstranged, WildEstranged, ← estrangedOn_union]
  constructor
  · intro h
    refine h.mono ?_
    rintro g (hg | hg)
    exacts [hg.1, (Subgroup.mem_inf.1 hg).1]
  · intro h
    refine h.mono fun g hg ↦ ?_
    by_cases hk : g ∈ T.actKer P
    · exact Or.inr (Subgroup.mem_inf.2 ⟨hg, hk⟩)
    · exact Or.inl ⟨hg, hk⟩

/-- Tame and wild estrangement give estrangement of the tower pulled back to `Δ`. -/
theorem estranged_comap_of_tame_wild {Δ : Subgroup Γ} {P : J → Prop}
    (hT : T.TameEstranged Δ P) (hW : T.WildEstranged Δ P) : (T.comap Δ.subtype).Estranged :=
  (estranged_comap_subtype_iff Δ).2 ((estrangedOn_iff_tame_wild Δ P).2 ⟨hT, hW⟩)

/-- Wild estrangement gets weaker as the set of tame levels grows. -/
lemma WildEstranged.mono {Δ : Subgroup Γ} {P P' : J → Prop} (h : T.WildEstranged Δ P)
    (hP : ∀ j, P j → P' j) : T.WildEstranged Δ P' :=
  EstrangedOn.mono h fun _ hg ↦ Subgroup.mem_inf.2
    ⟨(Subgroup.mem_inf.1 hg).1, actKer_anti hP (Subgroup.mem_inf.1 hg).2⟩

/-- Without tame levels, wild estrangement is the whole estrangement of `Δ`. -/
lemma wildEstranged_bot_iff (Δ : Subgroup Γ) :
    T.WildEstranged Δ (fun _ ↦ False) ↔ T.EstrangedOn Δ := by
  rw [WildEstranged, actKer_bot, inf_top_eq]

/-! ### Necessary conditions: estranged elements move vertices -/

/-- If the tree at level `k` has two vertices at distance `> 2`, an element with small fixed set
at `k` moves some vertex at `k`. -/
lemma SmallFixAt.exists_moved {k : J} {g : Γ} (h : T.SmallFixAt k g)
    (hbig : ∃ x y : T.V k, 2 < (T.graph k).dist x y) : ∃ v : T.V k, T.ρ k g • v ≠ v := by
  by_contra hc
  simp only [not_exists, not_not] at hc
  obtain ⟨x, y, hxy⟩ := hbig
  exact absurd (h x y (hc x) (hc y)) (not_le.2 hxy)

/-- **Estranged elements act nontrivially at cofinally many levels** (when all trees have
vertices at distance `> 2`). -/
theorem exists_moved_of_estrangedElt (hbig : ∀ k, ∃ x y : T.V k, 2 < (T.graph k).dist x y)
    {g : Γ} (h : T.EstrangedElt g) (j : J) :
    ∃ (k : J) (_ : k ⟶ j), ∃ v : T.V k, T.ρ k g • v ≠ v := by
  obtain ⟨k, f, hk⟩ := h j
  exact ⟨k, f, hk.exists_moved (hbig k)⟩

/-- **M4 cannot be checked on tame levels**: under wild estrangement, every nontrivial element of
the wild kernel `Δ ⊓ actKer P` acts nontrivially on the tree of a non-`P` level below every
level. -/
theorem WildEstranged.exists_not_mem {Δ : Subgroup Γ} {P : J → Prop} (hW : T.WildEstranged Δ P)
    (hbig : ∀ k, ∃ x y : T.V k, 2 < (T.graph k).dist x y) {g : Γ} (hgΔ : g ∈ Δ)
    (hgK : g ∈ T.actKer P) (hg1 : g ≠ 1) (j : J) :
    ∃ (k : J) (_ : k ⟶ j), ¬ P k ∧ ∃ v : T.V k, T.ρ k g • v ≠ v := by
  obtain ⟨k, f, v, hv⟩ :=
    exists_moved_of_estrangedElt hbig (hW g (Subgroup.mem_inf.2 ⟨hgΔ, hgK⟩) hg1) j
  exact ⟨k, f, fun hk ↦ hv (mem_actKer.1 hgK k hk v), v, hv⟩

/-! ### Line levels (a single loop / an `n`-gon as dual graph) -/

variable (T) in
/-- The tree at level `k` is a **line**: every vertex has at most two neighbours (the universal
covering of a dual graph which is a cycle, e.g. the `2`-gon of the Tate curve). -/
def LineAt (k : J) : Prop :=
  ∀ v a b c : T.V k, (T.graph k).Adj v a → (T.graph k).Adj v b → (T.graph k).Adj v c →
    a = b ∨ a = c ∨ b = c

/-- On a line, an automorphism fixing a vertex `v` and a neighbour `u` fixes every neighbour of
`v`. -/
lemma smul_eq_of_lineAt_adj {k : J} (hk : T.LineAt k) {h : T.G k} {v u w : T.V k}
    (hv : h • v = v) (hu : h • u = u) (hvu : (T.graph k).Adj v u) (hvw : (T.graph k).Adj v w) :
    h • w = w := by
  have hhw : (T.graph k).Adj v (h • w) := by
    have := (T.adj_smul k h v w).2 hvw
    rwa [hv] at this
  rcases hk v (h • w) u w hhw hvu hvw with h1 | h1 | h1
  · rw [← hu] at h1
    rw [MulAction.injective h h1, hu]
  · exact h1
  · rw [← h1]; exact hu

/-- Propagation along walks: if `h` fixes adjacent `a, b`, it fixes the end of every walk
starting at `b`. -/
lemma smul_eq_of_walk {k : J} (hk : T.LineAt k) {h : T.G k} :
    ∀ {b z : T.V k} (_ : (T.graph k).Walk b z) {a : T.V k}, h • a = a → h • b = b →
      (T.graph k).Adj b a → h • z = z
  | _, _, .nil, _, _, hb, _ => hb
  | _, _, .cons hbc q, _, ha, hb, hba =>
    smul_eq_of_walk hk q hb (smul_eq_of_lineAt_adj hk hb ha hba hbc) hbc.symm

/-- **On a line, an automorphism fixing two distinct vertices is trivial.** -/
theorem smul_eq_of_lineAt {k : J} (hk : T.LineAt k) {h : T.G k} {x y : T.V k} (hx : h • x = x)
    (hy : h • y = y) (hxy : x ≠ y) (z : T.V k) : h • z = z := by
  obtain ⟨w, hw, hwd⟩ := exists_adj_geodesic (T.isTree k).connected hxy
  have hwf : h • w = w := smul_eq_of_mem_geodesic (T.isTree k) (T.adj_smul k) hx hy hwd
  obtain ⟨q⟩ := (T.isTree k).connected.preconnected x z
  exact smul_eq_of_walk hk q hwf hx hw

/-- At a line level, an element acting nontrivially fixes at most one vertex. -/
theorem smallFixAt_of_lineAt {k : J} (hk : T.LineAt k) {g : Γ}
    (hmov : ∃ v : T.V k, T.ρ k g • v ≠ v) : T.SmallFixAt k g := by
  intro x y hx hy
  by_cases hxy : x = y
  · subst hxy; simp
  · obtain ⟨v, hv⟩ := hmov
    exact absurd (smul_eq_of_lineAt hk hx hy hxy v) hv

/-- An element acting nontrivially at cofinally many line levels is estranged. -/
theorem estrangedElt_of_lineAt {L : J → Prop} (hL : ∀ k, L k → T.LineAt k) {g : Γ}
    (h : ∀ j, ∃ (k : J) (_ : k ⟶ j), L k ∧ ∃ v : T.V k, T.ρ k g • v ≠ v) :
    T.EstrangedElt g := by
  intro j
  obtain ⟨k, f, hk, hmov⟩ := h j
  exact ⟨k, f, smallFixAt_of_lineAt (hL k hk) hmov⟩

/-- **Towers of lines: estrangement = faithfulness at cofinal finite levels.** If every tree is a
line with two vertices at distance `> 2` (e.g. the universal coverings of the cycles of the
topological coverings of the dual graph of a Tate curve), the tower is estranged iff every
nontrivial element acts nontrivially on the trees of cofinally many levels. -/
theorem estranged_iff_of_lineAt (hL : ∀ k, T.LineAt k)
    (hbig : ∀ k, ∃ x y : T.V k, 2 < (T.graph k).dist x y) :
    T.Estranged ↔
      ∀ g : Γ, g ≠ 1 → ∀ j, ∃ (k : J) (_ : k ⟶ j), ∃ v : T.V k, T.ρ k g • v ≠ v := by
  constructor
  · intro h g hg j
    exact exists_moved_of_estrangedElt hbig (h g hg) j
  · intro h g hg
    exact estrangedElt_of_lineAt (L := fun _ ↦ True) (fun k _ ↦ hL k) fun j ↦
      (h g hg j).imp fun k ⟨f, hf⟩ ↦ ⟨f, trivial, hf⟩

/-! ### Reduction to sub-towers -/

/-- Estrangement along a subsystem of levels `F` which maps to every level gives estrangement
of `T`. -/
theorem estrangedElt_of_restrict {J' : Type*} [Category J'] (F : J' ⥤ J)
    (hF : ∀ j, ∃ j' : J', Nonempty (F.obj j' ⟶ j)) {g : Γ}
    (h : (T.restrict F).EstrangedElt g) : T.EstrangedElt g := by
  intro j
  obtain ⟨j', ⟨f⟩⟩ := hF j
  obtain ⟨k', f', hk'⟩ := h j'
  exact ⟨F.obj k', F.map f' ≫ f, hk'⟩

end TreeTower

end TemperedFundamentalGroups
