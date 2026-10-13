/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import TemperedFundamentalGroups.SemiAnbd.EllipticEstrangement

/-!
# The line tower of the Tate curve: `D_∞` acting on the `ℤ`-chain (Blueprint §12.10)

An explicit tree tower modelling the graph part of the tame tower of a Tate curve and of its
`±1`-quotient. The special fibre of the `ℤ`-covering `Y` of the Tate curve `X = G_m / q^ℤ` is a
chain of rational curves (`TateObject.X₀`, the copies of `C ∪ E'` glued alternately at `p`, `q`);
its barycentrically subdivided dual graph is the line `ℤ`, with the nodes at the even and the
components at the odd integers (`kind x = true` iff `x` is odd). The deck group `ℤ` of `Y → X`
acts by translations `x ↦ x + 2i` (`r i`), the involution `x ↦ q^i / x` of `G_m` by the
reflections `x ↦ -2i - x` (`sr i`); together this is the infinite dihedral group
`DihedralGroup 0`. The topological coverings of the dual graph (the cyclic `n`-gon coverings)
have the same universal covering line, so the tower is constant: `DihedralLine.tower J` has
the line at every level of any category of levels `J`, with identity transition maps.

* `DihedralLine.lineGraph`, **`DihedralLine.isTree_lineGraph`**: the line is a tree;
  `DihedralLine.lineAt` (every vertex has at most two neighbours);
* the action (`r_smul`, `sr_smul`): translations by `i ≠ 0` fix no vertex
  (**`hyperbolicAt_r`**), the reflection `sr i` fixes exactly the vertex `-i`
  (`sr_smul_eq_iff`); the action is faithful (`eq_one_of_forall_smul_eq`);
* **`DihedralLine.estranged`**: the tower is estranged (every nontrivial element fixes at most one
  vertex); its elliptic elements are exactly `1` and the reflections (`elliptic_iff`);
* **[SemiAnbd] Thm. 3.7(iii)/(iv) for the model**: every compatible system is constant
  (`eq_vsys`); the stabilizer of the system at `x` is `{1, sr (-x)}` (`mem_stab_vsys`); every
  nontrivial finite subgroup fixes a system (**`exists_le_stab_vsys`**); the maximal finite
  subgroups are exactly the stabilizers of systems (**`exists_eq_stab_of_maximal`**,
  **`maximal_stab_vsys`**).

For the Tate curve `X` itself (André's tower requires the group `A` of the orbifold to be
trivial) only the translations occur: they are hyperbolic, so their estrangement is automatic
(`TreeTower.estrangedElt_of_hyperbolicAt`) and they lie in no finite subgroup; the elliptic
elements, which are what [SemiAnbd] Thm. 3.7(iii) is about, come from the reflections of the
`±1`-quotient. The comparison with André's tower is `TateLineLevel` (`Andre/TameEstrangement.lean`).
-/

universe u v

open CategoryTheory SimpleGraph DihedralGroup TemperedFundamentalGroups.TreeGeom

namespace TemperedFundamentalGroups

namespace DihedralLine

/-! ### `ZMod 0 = ℤ` -/

/-- `ZMod 0` is `ℤ`. -/
def z (i : ZMod 0) : ℤ := i

/-- `ℤ` is `ZMod 0`. -/
def ofZ (x : ℤ) : ZMod 0 := x

lemma z_add (i j : ZMod 0) : z (i + j) = z i + z j := rfl

lemma z_sub (i j : ZMod 0) : z (i - j) = z i - z j := rfl

lemma z_zero : z 0 = 0 := rfl

@[simp] lemma z_ofZ (x : ℤ) : z (ofZ x) = x := rfl

lemma z_inj {i j : ZMod 0} (h : z i = z j) : i = j := h

/-! ### The line -/

/-- The line: `x` and `y` are adjacent iff they differ by one. -/
def lineGraph : SimpleGraph ℤ where
  Adj x y := x + 1 = y ∨ y + 1 = x
  symm := ⟨fun _ _ h ↦ Or.symm h⟩
  loopless := ⟨fun x (h : x + 1 = x ∨ x + 1 = x) ↦ by omega⟩

lemma lineGraph_adj {x y : ℤ} : lineGraph.Adj x y ↔ x + 1 = y ∨ y + 1 = x := Iff.rfl

lemma reachable_zero (n : ℤ) : lineGraph.Reachable 0 n := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ n ih => exact ih.trans (Adj.reachable (Or.inl rfl))
  | pred n ih => exact ih.trans (Adj.reachable (Or.inr (by ring)))

/-- **The line is a tree.** -/
theorem isTree_lineGraph : lineGraph.IsTree :=
  ⟨⟨fun x y ↦ (reachable_zero x).symm.trans (reachable_zero y)⟩,
    isAcyclic_of_rank Int.natAbs (fun x y h ↦ by rw [lineGraph_adj] at h; omega)
      (fun x y w hy hw hyx hwx ↦ by rw [lineGraph_adj] at hy hw; omega)⟩

lemma finite_neighborSet (x : ℤ) : (lineGraph.neighborSet x).Finite :=
  (Set.toFinite {x - 1, x + 1}).subset fun y (hy : lineGraph.Adj x y) ↦ by
    rw [lineGraph_adj] at hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    omega

/-! ### The action of `D_∞` -/

/-- The action of `D_∞`: `r i` translates by `2i`, `sr i` is the reflection `x ↦ -2i - x`. -/
def act : DihedralGroup 0 → ℤ → ℤ
  | r i, x => x + 2 * z i
  | sr i, x => -2 * z i - x

instance : MulAction (DihedralGroup 0) ℤ where
  smul := act
  one_smul x := by change act (r 0) x = x; simp [act, z_zero]
  mul_smul g h x := by
    cases g <;> cases h <;> simp only [r_mul_r, r_mul_sr, sr_mul_r, sr_mul_sr] <;>
      change act _ x = act _ (act _ x) <;> simp only [act, z_add, z_sub] <;> ring

lemma r_smul (i : ZMod 0) (x : ℤ) : (r i : DihedralGroup 0) • x = x + 2 * z i := rfl

lemma sr_smul (i : ZMod 0) (x : ℤ) : (sr i : DihedralGroup 0) • x = -2 * z i - x := rfl

lemma adj_smul (g : DihedralGroup 0) (x y : ℤ) :
    lineGraph.Adj (g • x) (g • y) ↔ lineGraph.Adj x y := by
  cases g <;> simp only [lineGraph_adj, r_smul, sr_smul] <;> omega

/-- The colour: components at the odd, nodes at the even integers. -/
def kind (x : ℤ) : Bool := decide (Odd x)

lemma kind_smul (g : DihedralGroup 0) (x : ℤ) : kind (g • x) = kind x := by
  cases g <;> simp only [kind, r_smul, sr_smul, decide_eq_decide, Int.odd_iff] <;> omega

lemma kind_adj (x y : ℤ) (h : lineGraph.Adj x y) : kind x ≠ kind y := by
  rw [lineGraph_adj] at h
  simp only [kind, ne_eq, decide_eq_decide, Int.odd_iff]
  omega

/-- Translations by `i ≠ 0` fix no vertex. -/
lemma r_smul_ne {i : ZMod 0} (hi : i ≠ 0) (x : ℤ) : (r i : DihedralGroup 0) • x ≠ x := by
  rw [r_smul]
  intro h
  exact hi (z_inj (by rw [z_zero]; omega))

/-- **The reflection `sr i` fixes exactly the vertex `-i`.** -/
lemma sr_smul_eq_iff {i : ZMod 0} {x : ℤ} : (sr i : DihedralGroup 0) • x = x ↔ x = -z i := by
  rw [sr_smul]
  omega

/-- The action is faithful. -/
lemma eq_one_of_forall_smul_eq {g : DihedralGroup 0} (h : ∀ x : ℤ, g • x = x) : g = 1 := by
  cases g with
  | r i =>
    by_contra hi
    refine r_smul_ne (i := i) (fun h0 ↦ hi ?_) 0 (h 0)
    rw [h0, one_def]
  | sr i =>
    have h0 := sr_smul_eq_iff.1 (h 0)
    have h1 := sr_smul_eq_iff.1 (h 1)
    omega

/-! ### The tower -/

/-- **The line tower** over a category of levels `J`: the line with the action of `D_∞` at every
level, identity transition maps. -/
abbrev tower (J : Type u) [Category.{v} J] : TreeTower.{u, v, 0} (DihedralGroup 0) J where
  G _ := DihedralGroup 0
  ρ _ := MonoidHom.id _
  V _ := ℤ
  graph _ := lineGraph
  isTree _ := isTree_lineGraph
  act _ := inferInstance
  adj_smul _ := adj_smul
  kind _ := kind
  kind_smul _ := kind_smul
  kind_adj _ := kind_adj
  map _ := id
  map_smul _ _ _ := rfl
  map_adj _ _ _ h := Or.inl h

variable {J : Type u} [Category.{v} J]

lemma tower_smul (j : J) (g : DihedralGroup 0) (x : ℤ) : (tower J).ρ j g • x = g • x := rfl

lemma isFunctorial : (tower J).IsFunctorial := ⟨fun _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩

lemma locallyFinite (j : J) (x : (tower J).V j) : (((tower J).graph j).neighborSet x).Finite :=
  finite_neighborSet x

/-- Every level of the tower is a line. -/
lemma lineAt (j : J) : (tower J).LineAt j := by
  intro (x : ℤ) (a : ℤ) (b : ℤ) (c : ℤ) ha hb hc
  change lineGraph.Adj x a at ha
  change lineGraph.Adj x b at hb
  change lineGraph.Adj x c at hc
  rw [lineGraph_adj] at ha hb hc
  change @Eq ℤ a b ∨ @Eq ℤ a c ∨ @Eq ℤ b c
  omega

/-- Nontrivial translations are hyperbolic at every level. -/
lemma hyperbolicAt_r {i : ZMod 0} (hi : i ≠ 0) (j : J) : (tower J).HyperbolicAt j (r i) :=
  r_smul_ne hi

/-- **The line tower is estranged**: a nontrivial element fixes at most one vertex. -/
theorem estranged : (tower J).Estranged := by
  intro g hg j
  refine ⟨j, 𝟙 j, TreeTower.smallFixAt_of_lineAt (lineAt j) ?_⟩
  by_contra hc
  push Not at hc
  exact hg (eq_one_of_forall_smul_eq hc)

/-- Both halves of M4 hold for the line tower, for every `Δ` and every set of levels `P`. -/
theorem tame_wild (Δ : Subgroup (DihedralGroup 0)) (P : J → Prop) :
    (tower J).TameEstranged Δ P ∧ (tower J).WildEstranged Δ P :=
  (TreeTower.estrangedOn_iff_tame_wild Δ P).1 fun g _ hg ↦ estranged g hg

/-- **The elliptic elements of the line tower are `1` and the reflections.** -/
theorem elliptic_iff [Nonempty J] {g : DihedralGroup 0} :
    (tower J).Elliptic g ↔ g = 1 ∨ ∃ i, g = sr i := by
  constructor
  · intro h
    cases g with
    | r i =>
      left
      by_contra hi
      obtain ⟨x, hx⟩ := h (Classical.arbitrary J)
      exact r_smul_ne (i := i) (fun h0 ↦ hi (by rw [h0, one_def])) x hx
    | sr i => exact Or.inr ⟨i, rfl⟩
  · rintro (rfl | ⟨i, rfl⟩) j
    · exact ⟨0, one_smul _ _⟩
    · exact ⟨-z i, sr_smul_eq_iff.2 rfl⟩

/-! ### Systems and [SemiAnbd] Thm. 3.7(iii)/(iv) -/

/-- The constant system at the vertex `x`. -/
def vsys (x : ℤ) : (tower J).Sys := ⟨fun _ ↦ x, fun _ ↦ rfl⟩

/-- Over a cofiltered category of levels, every compatible system is constant. -/
lemma eq_vsys [IsCofiltered J] (s : (tower J).Sys) : ∃ x, s = vsys x := by
  haveI : Nonempty J := IsCofiltered.nonempty
  let j₀ : J := Classical.arbitrary J
  refine ⟨s.1 j₀, TreeTower.Sys.ext fun j ↦ ?_⟩
  obtain ⟨k, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j j₀
  change s.1 j = s.1 j₀
  rw [← s.2 a, ← s.2 b]

/-- **The stabilizer of the system at `x` is `{1, sr (-x)}`.** -/
lemma mem_stab_vsys [Nonempty J] {x : ℤ} {g : DihedralGroup 0} :
    g ∈ TreeTower.stab (vsys (J := J) x) ↔ g = 1 ∨ g = sr (ofZ (-x)) := by
  rw [TreeTower.mem_stab]
  constructor
  · intro h
    have hx : g • x = x := h (Classical.arbitrary J)
    cases g with
    | r i =>
      left
      by_contra hi
      exact r_smul_ne (i := i) (fun h0 ↦ hi (by rw [h0, one_def])) x hx
    | sr i =>
      right
      have := sr_smul_eq_iff.1 hx
      exact congrArg sr (z_inj (by rw [z_ofZ]; omega))
  · rintro (rfl | rfl) j
    · change (1 : DihedralGroup 0) • x = x
      exact one_smul _ _
    · change (sr (ofZ (-x)) : DihedralGroup 0) • x = x
      exact sr_smul_eq_iff.2 (by rw [z_ofZ, neg_neg])

lemma finite_stab_vsys [Nonempty J] (x : ℤ) :
    (TreeTower.stab (vsys (J := J) x) : Set (DihedralGroup 0)).Finite :=
  (Set.toFinite {1, sr (ofZ (-x))}).subset fun _ hg ↦ by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using mem_stab_vsys.1 hg

lemma sr_mem_stab_vsys [Nonempty J] (x : ℤ) :
    sr (ofZ (-x)) ∈ TreeTower.stab (vsys (J := J) x) :=
  mem_stab_vsys.2 (Or.inr rfl)

/-- **[SemiAnbd] Thm. 3.7(iii) for the line tower**: every nontrivial finite subgroup of `D_∞`
fixes a vertex of the line, i.e. lies in the stabilizer of a (constant) compatible system. -/
theorem exists_le_stab_vsys [IsCofiltered J] (H : Subgroup (DihedralGroup 0)) [Finite H]
    (hH1 : H ≠ ⊥) : ∃ x : ℤ, H ≤ TreeTower.stab (vsys (J := J) x) := by
  have hfin : ∀ j : J, Finite (H.map ((tower J).ρ j)) := fun j ↦ by
    change Finite (H.map (MonoidHom.id _))
    rw [Subgroup.map_id]
    infer_instance
  obtain ⟨s, hs⟩ := TreeTower.exists_le_stab_of_estranged isFunctorial estranged locallyFinite H
    hH1 hfin
  obtain ⟨x, rfl⟩ := eq_vsys s
  exact ⟨x, hs⟩

/-- **[SemiAnbd] Thm. 3.7(iv) for the line tower**: a nontrivial maximal finite subgroup of `D_∞`
is the stabilizer of a compatible system. -/
theorem exists_eq_stab_of_maximal [IsCofiltered J] (H : Subgroup (DihedralGroup 0)) [Finite H]
    (hH1 : H ≠ ⊥)
    (hmax : ∀ H' : Subgroup (DihedralGroup 0), Finite H' → H ≤ H' → H' = H) :
    ∃ x : ℤ, H = TreeTower.stab (vsys (J := J) x) := by
  haveI : Nonempty J := IsCofiltered.nonempty
  obtain ⟨x, hx⟩ := exists_le_stab_vsys (J := J) H hH1
  exact ⟨x, (hmax _ (finite_stab_vsys x).to_subtype hx).symm⟩

/-- **Conversely, the stabilizers of systems are maximal finite subgroups.** -/
theorem maximal_stab_vsys [IsCofiltered J] (x : ℤ) (H' : Subgroup (DihedralGroup 0)) [Finite H']
    (hle : TreeTower.stab (vsys (J := J) x) ≤ H') : H' = TreeTower.stab (vsys (J := J) x) := by
  haveI : Nonempty J := IsCofiltered.nonempty
  have hne : H' ≠ ⊥ := fun h ↦ by
    have := hle (sr_mem_stab_vsys (J := J) x)
    rw [h, Subgroup.mem_bot, one_def] at this
    cases this
  obtain ⟨y, hy⟩ := exists_le_stab_vsys (J := J) H' hne
  have hxy : x = y := by
    rcases mem_stab_vsys.1 (hy (hle (sr_mem_stab_vsys (J := J) x))) with h | h
    · rw [one_def] at h
      cases h
    · have := congrArg z (sr.inj h)
      rw [z_ofZ, z_ofZ] at this
      omega
  subst hxy
  exact le_antisymm hy hle

end DihedralLine

end TemperedFundamentalGroups
