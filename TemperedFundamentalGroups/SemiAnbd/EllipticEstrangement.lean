/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.Estrangement

/-!
# Hyperbolic elements are estranged; only elliptic elements matter (Blueprint §12.10)

In a tree tower over a cofiltered category of levels, call `g` **hyperbolic at `j`**
(`HyperbolicAt j g`) if it fixes no vertex of the tree at level `j`, and **elliptic**
(`Elliptic g`) if it fixes a vertex at every level. Fixed vertices map to fixed vertices along
the equivariant maps of trees, so:

* **`estrangedElt_of_hyperbolicAt`**: an element hyperbolic at one level fixes no vertex at any
  level mapping to it, so it is estranged (with empty fixed sets) — at *all* deeper levels,
  including wild ones;
* **`estrangedOn_iff_elliptic`**, **`estranged_iff_estrangedOn_elliptic`**: estrangement only has
  to be checked on elliptic elements;
* `tameEstranged_iff_elliptic`, `wildEstranged_iff_elliptic`: the same for the tame and wild
  halves of M4 (`SemiAnbd/Estrangement.lean`);
* **`tameEstranged_of_hyperbolicAt`**: if every element of `Δ` acting nontrivially on the tree
  of a `P`-level acts there without fixed vertices (e.g. by deck transformations of the tree
  covering of the dual graph), the tame half `TameEstranged Δ P` holds;
* `elliptic_of_mem`: elements of subgroups with finite images at every level (compact subgroups
  of a limit of discrete groups) are elliptic; hence (`not_hyperbolicAt_of_mem`) **hyperbolic
  elements play no role in [SemiAnbd] Thm. 3.7(iii)**:
  `exists_le_stab_of_estrangedOn` needs the estrangement of the elements of `H` only;
* **line towers** (`estrangedElt_of_lineAt_of_moved`): if all trees are lines and the maps of
  trees are non-constant, every element acting nontrivially on the tree of some level is
  estranged (the fixed set of a nontrivially acting automorphism of a line is at most a vertex,
  and a nontrivial action on a deeper line forces a nontrivial action on the image).
-/

universe u v w x

open CategoryTheory SimpleGraph TemperedFundamentalGroups.TreeGeom

namespace TemperedFundamentalGroups

namespace TreeTower

variable {Γ : Type x} [Group Γ] {J : Type u} [Category.{v} J] (T : TreeTower.{u, v, w} Γ J)

/-! ### Hyperbolic and elliptic elements -/

/-- `g` is **hyperbolic at `j`**: it fixes no vertex of the tree at level `j`. -/
def HyperbolicAt (j : J) (g : Γ) : Prop := ∀ v : T.V j, T.ρ j g • v ≠ v

/-- `g` is **elliptic**: it fixes a vertex of the tree at every level. -/
def Elliptic (g : Γ) : Prop := ∀ j, ∃ v : T.V j, T.ρ j g • v = v

variable {T}

lemma not_elliptic_iff {g : Γ} : ¬ T.Elliptic g ↔ ∃ j, T.HyperbolicAt j g := by
  simp only [Elliptic, HyperbolicAt, not_forall, not_exists]

/-- Fixed vertices map to fixed vertices: an element hyperbolic at `j` is hyperbolic at every
level mapping to `j`. -/
lemma HyperbolicAt.of_hom {j k : J} (f : k ⟶ j) {g : Γ} (h : T.HyperbolicAt j g) :
    T.HyperbolicAt k g := fun v hv ↦ h (T.map f v) (by rw [← T.map_smul, hv])

/-- At a level where `g` is hyperbolic, its fixed set is empty, in particular small. -/
lemma HyperbolicAt.smallFixAt {k : J} {g : Γ} (h : T.HyperbolicAt k g) : T.SmallFixAt k g :=
  fun x _ hx _ ↦ absurd hx (h x)

/-- Elements of a subgroup with finite images fix vertices at every level (T3). -/
lemma elliptic_of_mem {H : Subgroup Γ} (hH : ∀ j, Finite (H.map (T.ρ j))) {g : Γ} (hg : g ∈ H) :
    T.Elliptic g := fun j ↦ by
  obtain ⟨v, hv⟩ := nonempty_fixSet (hH j)
  exact ⟨v, hv g hg⟩

/-- **Hyperbolic elements lie in no subgroup with finite images** (e.g. no compact subgroup of
a limit of discrete groups). -/
lemma not_hyperbolicAt_of_mem {H : Subgroup Γ} (hH : ∀ j, Finite (H.map (T.ρ j))) {g : Γ}
    (hg : g ∈ H) (j : J) : ¬ T.HyperbolicAt j g := fun h ↦ by
  obtain ⟨v, hv⟩ := elliptic_of_mem hH hg j
  exact h v hv

section Cofiltered

variable [IsCofilteredOrEmpty J]

/-- **Hyperbolic elements are estranged**: below every level there is a level mapping to the
level where `g` is hyperbolic, and there `g` fixes no vertex at all. -/
theorem estrangedElt_of_hyperbolicAt {j₀ : J} {g : Γ} (h : T.HyperbolicAt j₀ g) :
    T.EstrangedElt g := by
  intro j
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j j₀
  exact ⟨k, a, (h.of_hom b).smallFixAt⟩

/-- Non-elliptic elements are estranged. -/
theorem estrangedElt_of_not_elliptic {g : Γ} (h : ¬ T.Elliptic g) : T.EstrangedElt g := by
  obtain ⟨j₀, hj₀⟩ := not_elliptic_iff.1 h
  exact estrangedElt_of_hyperbolicAt hj₀

/-- **Estrangement only has to be checked on elliptic elements.** -/
theorem estrangedOn_iff_elliptic (S : Set Γ) :
    T.EstrangedOn S ↔ T.EstrangedOn (S ∩ {g | T.Elliptic g}) := by
  refine ⟨fun h ↦ h.mono Set.inter_subset_left, fun h g hg hg1 ↦ ?_⟩
  by_cases he : T.Elliptic g
  · exact h g ⟨hg, he⟩ hg1
  · exact estrangedElt_of_not_elliptic he

/-- **The tower is estranged iff its nontrivial elliptic elements are.** -/
theorem estranged_iff_estrangedOn_elliptic :
    T.Estranged ↔ T.EstrangedOn {g | T.Elliptic g} := by
  rw [estranged_iff_estrangedOn_univ, estrangedOn_iff_elliptic, Set.univ_inter]

/-- The tame half of M4 only concerns elliptic elements. -/
theorem tameEstranged_iff_elliptic (Δ : Subgroup Γ) (P : J → Prop) :
    T.TameEstranged Δ P ↔
      T.EstrangedOn {g | g ∈ Δ ∧ g ∉ T.actKer P ∧ T.Elliptic g} := by
  rw [TameEstranged, estrangedOn_iff_elliptic]
  constructor
  · exact fun h ↦ h.mono fun g hg ↦ ⟨⟨hg.1, hg.2.1⟩, hg.2.2⟩
  · exact fun h ↦ h.mono fun g hg ↦ ⟨hg.1.1, hg.1.2, hg.2⟩

/-- The wild half (M4) only concerns elliptic elements. -/
theorem wildEstranged_iff_elliptic (Δ : Subgroup Γ) (P : J → Prop) :
    T.WildEstranged Δ P ↔
      T.EstrangedOn {g | g ∈ Δ ∧ g ∈ T.actKer P ∧ T.Elliptic g} := by
  rw [WildEstranged, estrangedOn_iff_elliptic]
  constructor
  · exact fun h ↦ h.mono fun g hg ↦ ⟨Subgroup.mem_inf.2 ⟨hg.1, hg.2.1⟩, hg.2.2⟩
  · exact fun h ↦ h.mono fun g hg ↦
      ⟨(Subgroup.mem_inf.1 hg.1).1, (Subgroup.mem_inf.1 hg.1).2, hg.2⟩

/-- **Tame estrangement from hyperbolicity on the tame levels**: if every element of `Δ` acting
nontrivially on the tree of a `P`-level acts there without fixed vertices, then every element of
`Δ` acting nontrivially on some `P`-level is estranged. -/
theorem tameEstranged_of_hyperbolicAt {Δ : Subgroup Γ} {P : J → Prop}
    (h : ∀ g ∈ Δ, ∀ j, P j → (∃ v : T.V j, T.ρ j g • v ≠ v) → T.HyperbolicAt j g) :
    T.TameEstranged Δ P := by
  rintro g ⟨hgΔ, hgK⟩ -
  obtain ⟨j, hj, v, hv⟩ : ∃ j, P j ∧ ∃ v : T.V j, T.ρ j g • v ≠ v := by
    by_contra hc
    push Not at hc
    exact hgK (mem_actKer.2 hc)
  exact estrangedElt_of_hyperbolicAt (h g hgΔ j hj ⟨v, hv⟩)

end Cofiltered

/-! ### [SemiAnbd] Thm. 3.7(iii) from the estrangement of the elements of `H` -/

/-- Under the estrangement of the elements of `H`, a nontrivial `H` has finite fixed sets at
cofinally many levels. -/
lemma finite_fixSet_of_estrangedOn {H : Subgroup Γ} (hE : T.EstrangedOn H)
    (hlf : ∀ j (v : T.V j), ((T.graph j).neighborSet v).Finite) (hH : H ≠ ⊥) (j : J) :
    ∃ (k : J) (_ : k ⟶ j), (T.fixSet k H).Finite := by
  obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hH
  replace hg1 : g ≠ 1 := fun h ↦ hg1 (Subtype.ext h)
  obtain ⟨k, f, hk⟩ := hE g hg hg1 j
  refine ⟨k, f, ?_⟩
  rcases (T.fixSet k H).eq_empty_or_nonempty with h | ⟨x, hx⟩
  · rw [h]; exact Set.finite_empty
  · exact (finite_ball (T.isTree k).connected (hlf k) x 2).subset fun y hy ↦
      hk x y (hx g hg) (hy g hg)

/-- **[SemiAnbd] Thm. 3.7(iii) from the estrangement of `H` alone**: a nontrivial subgroup with
finite images whose nontrivial elements are estranged fixes a compatible system. Its elements
are elliptic (`elliptic_of_mem`), so only elliptic estrangement is used. -/
theorem exists_le_stab_of_estrangedOn [IsCofilteredOrEmpty J] (hT : T.IsFunctorial)
    (hlf : ∀ j (v : T.V j), ((T.graph j).neighborSet v).Finite) (H : Subgroup Γ) (hH1 : H ≠ ⊥)
    (hH : ∀ j, Finite (H.map (T.ρ j))) (hE : T.EstrangedOn H) : ∃ s : T.Sys, H ≤ stab s :=
  exists_le_stab_of_finite_fixSet hT H hH (finite_fixSet_of_estrangedOn hE hlf hH1)

/-! ### Towers of lines -/

/-- If the tree at `j` is a line, an automorphism fixing two distinct vertices of the image of a
map of trees acts trivially there; so a nontrivial action at `j` is nontrivial at `k`. -/
lemma moved_of_moved_lineAt {j k : J} (f : k ⟶ j) (hj : T.LineAt j)
    (hf : ∃ x y : T.V k, T.map f x ≠ T.map f y) {g : Γ} (hmov : ∃ v : T.V j, T.ρ j g • v ≠ v) :
    ∃ v : T.V k, T.ρ k g • v ≠ v := by
  by_contra hc
  push Not at hc
  obtain ⟨x, y, hxy⟩ := hf
  obtain ⟨v, hv⟩ := hmov
  have hx : T.ρ j g • T.map f x = T.map f x := by rw [← T.map_smul, hc x]
  have hy : T.ρ j g • T.map f y = T.map f y := by rw [← T.map_smul, hc y]
  exact hv (smul_eq_of_lineAt hj hx hy hxy v)

/-- **Towers of lines with non-constant maps**: every element acting nontrivially on the tree of
some level is estranged (it acts nontrivially, hence with at most one fixed vertex, at every
deeper level). -/
theorem estrangedElt_of_lineAt_of_moved [IsCofilteredOrEmpty J] (hL : ∀ k, T.LineAt k)
    (hf : ∀ {j k : J} (f : k ⟶ j), ∃ x y : T.V k, T.map f x ≠ T.map f y) {g : Γ} {j₀ : J}
    (hmov : ∃ v : T.V j₀, T.ρ j₀ g • v ≠ v) : T.EstrangedElt g := by
  intro j
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j j₀
  exact ⟨k, a, smallFixAt_of_lineAt (hL k) (moved_of_moved_lineAt b (hL j₀) (hf b) hmov)⟩

/-- In a tower of lines with non-constant maps, the tame half of M4 holds for every `Δ` and
every set `P` of levels. -/
theorem tameEstranged_of_lineAt [IsCofilteredOrEmpty J] (hL : ∀ k, T.LineAt k)
    (hf : ∀ {j k : J} (f : k ⟶ j), ∃ x y : T.V k, T.map f x ≠ T.map f y) (Δ : Subgroup Γ)
    (P : J → Prop) : T.TameEstranged Δ P := by
  rintro g ⟨-, hgK⟩ -
  obtain ⟨j, -, v, hv⟩ : ∃ j, P j ∧ ∃ v : T.V j, T.ρ j g • v ≠ v := by
    by_contra hc
    push Not at hc
    exact hgK (mem_actKer.2 hc)
  exact estrangedElt_of_lineAt_of_moved hL hf ⟨v, hv⟩

end TreeTower

end TemperedFundamentalGroups
