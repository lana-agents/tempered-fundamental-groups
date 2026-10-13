/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.CoverVertex
import TemperedFundamentalGroups.SemiAnbd.Estrangement

/-!
# Fixed arcs: estrangement at one level, and its finite-level shadow (Blueprint §12.10, E17)

**Exact tree criterion.** In a 2-coloured tree (adjacent vertices of different colours, as in a
`TreeTower`), the fixed set of an automorphism has diameter `≤ 2` iff it contains no **arc**
`x₀ – x₁ – x₂ – x₃` (consecutive vertices adjacent, `x₀ ≠ x₂`, `x₁ ≠ x₃`):

* `TreeTower.FixedArcAt k g`, **`TreeTower.smallFixAt_iff_not_fixedArcAt`**, and
  **`TreeTower.estrangedElt_iff_not_fixedArcAt`**: `g` is estranged iff below every level there is
  a level at which `g` fixes no arc; `TreeTower.not_estrangedElt_of_forall_fixedArcAt` (a fixed
  arc at all levels below one level obstructs estrangement).

**Finite-level shadow.** For the tree `K.Tree r` of reduced walks in the incidence graph of a
curve configuration `K` (components and special points of a special fibre `Z`), the last vertex
of a walk is a local isomorphism of graphs to the finite incidence graph. If a map of tree
coverings over `ψ : Z → Z` (e.g. the action of a stage group element, over the homeomorphism of
the special fibre) fixes an arc of the tree, then `ψ` fixes the canonical points (generic points of
components, special points) of a reduced walk of length `3` in the finite incidence graph
(`CurveConfig.FixedArc ψ`, **`CurveConfig.fixedArc_of_tree`**). Hence: if `ψ` fixes no such walk
in the special fibre, the element has fixed set of diameter `≤ 2` in the tree.
-/

universe u v w x

open CategoryTheory SimpleGraph TemperedFundamentalGroups.TreeGeom

namespace TemperedFundamentalGroups

lemma bool_eq_of_ne_of_ne {a b c : Bool} (h₁ : a ≠ b) (h₂ : b ≠ c) : a = c := by
  cases a <;> cases b <;> cases c <;> simp_all

namespace TreeTower

variable {Γ : Type x} [Group Γ] {J : Type u} [Category.{v} J] (T : TreeTower.{u, v, w} Γ J)

/-! ### Arcs -/

/-- `g` **fixes an arc** at level `k`: four vertices `x₀ – x₁ – x₂ – x₃` of the tree, consecutive
ones adjacent, `x₀ ≠ x₂`, `x₁ ≠ x₃`, all fixed by `g`. -/
def FixedArcAt (k : J) (g : Γ) : Prop :=
  ∃ x₀ x₁ x₂ x₃ : T.V k, (T.graph k).Adj x₀ x₁ ∧ (T.graph k).Adj x₁ x₂ ∧ (T.graph k).Adj x₂ x₃ ∧
    x₀ ≠ x₂ ∧ x₁ ≠ x₃ ∧ T.ρ k g • x₀ = x₀ ∧ T.ρ k g • x₁ = x₁ ∧ T.ρ k g • x₂ = x₂ ∧
      T.ρ k g • x₃ = x₃

variable {T}

/-- The ends of an arc are at distance `> 2`. -/
lemma two_lt_dist_of_arc {k : J} {x₀ x₁ x₂ x₃ : T.V k} (h₀₁ : (T.graph k).Adj x₀ x₁)
    (h₁₂ : (T.graph k).Adj x₁ x₂) (h₂₃ : (T.graph k).Adj x₂ x₃) (h₀₂ : x₀ ≠ x₂)
    (h₁₃ : x₁ ≠ x₃) : 2 < (T.graph k).dist x₀ x₃ := by
  have hG := T.isTree k
  have k₀₁ := T.kind_adj k _ _ h₀₁
  have k₁₂ := T.kind_adj k _ _ h₁₂
  have k₂₃ := T.kind_adj k _ _ h₂₃
  have e₀₂ : T.kind k x₀ = T.kind k x₂ := bool_eq_of_ne_of_ne k₀₁ k₁₂
  have n₀₃ : T.kind k x₀ ≠ T.kind k x₃ := by rw [e₀₂]; exact k₂₃
  by_contra hle
  replace hle := not_lt.1 hle
  -- the distance is `1`
  have h1 : (T.graph k).dist x₀ x₃ = 1 := by
    rcases Nat.lt_or_ge ((T.graph k).dist x₀ x₃) 1 with h | h
    · have h0 : (T.graph k).dist x₀ x₃ = 0 := by omega
      rcases (hG.connected.dist_eq_zero_iff).1 h0 with he
      exact absurd (congrArg (T.kind k) he) n₀₃
    · rcases Nat.lt_or_ge ((T.graph k).dist x₀ x₃) 2 with h' | h'
      · omega
      · obtain ⟨w, hw, hdw⟩ := exists_adj_dist_eq hG.connected (u := x₀) (v := x₃) (n := 1)
          (by omega)
        have hw' : (T.graph k).Adj x₀ w := dist_eq_one_iff_adj.1 hdw
        exact absurd (bool_eq_of_ne_of_ne (T.kind_adj k _ _ hw')
          (T.kind_adj k _ _ hw.symm)) n₀₃
  have h₀₃ : (T.graph k).Adj x₀ x₃ := dist_eq_one_iff_adj.1 h1
  -- `x₂` is at distance `2` from `x₀`, with two neighbours at distance `1`
  have hd₂ : (T.graph k).dist x₂ x₀ = 2 := by
    have hne : (T.graph k).dist x₂ x₀ ≠ 0 := fun h0 ↦
      h₀₂ ((hG.connected.dist_eq_zero_iff).1 h0).symm
    have hna : (T.graph k).dist x₂ x₀ ≠ 1 := fun h1' ↦
      T.kind_adj k _ _ (dist_eq_one_iff_adj.1 h1') e₀₂.symm
    have hle2 : (T.graph k).dist x₂ x₀ ≤ 2 := by
      have := hG.connected.dist_triangle (u := x₂) (v := x₁) (w := x₀)
      rw [dist_eq_one_iff_adj.2 h₁₂.symm, dist_eq_one_iff_adj.2 h₀₁.symm] at this
      exact this
    omega
  have hd₁ : (T.graph k).dist x₁ x₀ = 1 := dist_eq_one_iff_adj.2 h₀₁.symm
  have hd₃ : (T.graph k).dist x₃ x₀ = 1 := dist_eq_one_iff_adj.2 h₀₃.symm
  exact h₁₃ (eq_of_adj_of_dist_lt (s := x₀) hG h₁₂.symm h₂₃ (by omega) (by omega))

/-- If `g` fixes two vertices at distance `> 2`, it fixes an arc (the first four vertices of the
geodesic between them). -/
lemma fixedArcAt_of_two_lt_dist {k : J} {g : Γ} {x y : T.V k} (hx : T.ρ k g • x = x)
    (hy : T.ρ k g • y = y) (hd : 2 < (T.graph k).dist x y) : T.FixedArcAt k g := by
  have hG := T.isTree k
  have hc := hG.connected
  have hadj := T.adj_smul k
  have hne : ∀ {a b : T.V k}, 0 < (T.graph k).dist a b → a ≠ b := by
    rintro a b h rfl; simp at h
  obtain ⟨w₁, a₁, d₁⟩ := exists_adj_geodesic hc (hne (by omega : 0 < (T.graph k).dist x y))
  have e₁ : (T.graph k).dist x w₁ = 1 := dist_eq_one_iff_adj.2 a₁
  obtain ⟨w₂, a₂, d₂⟩ := exists_adj_geodesic hc
    (hne (by omega : 0 < (T.graph k).dist w₁ y))
  have e₂ : (T.graph k).dist w₁ w₂ = 1 := dist_eq_one_iff_adj.2 a₂
  have t₂ := hc.dist_triangle (u := x) (v := w₂) (w := y)
  have t₂' := hc.dist_triangle (u := x) (v := w₁) (w := w₂)
  have f₂ : (T.graph k).dist x w₂ = 2 := by omega
  obtain ⟨w₃, a₃, d₃⟩ := exists_adj_geodesic hc
    (hne (by omega : 0 < (T.graph k).dist w₂ y))
  have e₃ : (T.graph k).dist w₂ w₃ = 1 := dist_eq_one_iff_adj.2 a₃
  have t₃ := hc.dist_triangle (u := x) (v := w₃) (w := y)
  have t₃' := hc.dist_triangle (u := x) (v := w₂) (w := w₃)
  have f₃ : (T.graph k).dist x w₃ = 3 := by omega
  have fix : ∀ w, (T.graph k).dist x w + (T.graph k).dist w y = (T.graph k).dist x y →
      T.ρ k g • w = w := fun w hw ↦ smul_eq_of_mem_geodesic hG hadj hx hy hw
  refine ⟨x, w₁, w₂, w₃, a₁, a₂, a₃, fun h ↦ ?_, fun h ↦ ?_, hx, fix w₁ (by omega),
    fix w₂ (by omega), fix w₃ (by omega)⟩
  · rw [← h] at f₂; simp at f₂
  · rw [h] at e₁; omega

/-- **Exact tree criterion**: the fixed set of `g` at level `k` has diameter `≤ 2` iff `g` fixes
no arc at `k`. -/
theorem smallFixAt_iff_not_fixedArcAt (k : J) (g : Γ) :
    T.SmallFixAt k g ↔ ¬ T.FixedArcAt k g := by
  constructor
  · rintro hS ⟨x₀, x₁, x₂, x₃, h₀₁, h₁₂, h₂₃, h₀₂, h₁₃, f₀, -, -, f₃⟩
    exact absurd (hS x₀ x₃ f₀ f₃) (not_le.2 (two_lt_dist_of_arc h₀₁ h₁₂ h₂₃ h₀₂ h₁₃))
  · intro hn x y hx hy
    by_contra hd
    exact hn (fixedArcAt_of_two_lt_dist hx hy (not_le.1 hd))

/-- **Estrangement of one element by arcs**: `g` is estranged iff below every level there is a
level at which `g` fixes no arc. -/
theorem estrangedElt_iff_not_fixedArcAt (g : Γ) :
    T.EstrangedElt g ↔ ∀ j, ∃ (k : J) (_ : k ⟶ j), ¬ T.FixedArcAt k g := by
  simp only [EstrangedElt, smallFixAt_iff_not_fixedArcAt]

/-- **A fixed arc at all levels below one level obstructs estrangement.** -/
theorem not_estrangedElt_of_forall_fixedArcAt {g : Γ} {j : J}
    (h : ∀ (k : J) (_ : k ⟶ j), T.FixedArcAt k g) : ¬ T.EstrangedElt g := by
  rw [estrangedElt_iff_not_fixedArcAt]
  intro hE
  obtain ⟨k, f, hk⟩ := hE j
  exact hk (h k f)

end TreeTower

/-! ### The finite-level shadow in the incidence graph of a special fibre -/

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

variable (K) in
/-- The canonical point of a vertex of the incidence graph: the generic point of a component, or
the special point itself. -/
def pt : ι ⊕ Z → Z := Sum.elim K.η id

variable (K) in
/-- **`ψ : Z → Z` fixes an arc of the incidence graph**: a reduced walk `v₀ – v₁ – v₂ – v₃`
(consecutive vertices incident, `v₀ ≠ v₂`, `v₁ ≠ v₃`) whose canonical points are fixed by `ψ`;
for a homeomorphism `ψ` of the special fibre: two distinct components meeting in a special point,
each fixed, with one further fixed special point on one of them (or the same with the roles of
components and points exchanged). A condition on the finite special fibre. -/
def FixedArc (ψ : Z → Z) : Prop :=
  ∃ v₀ v₁ v₂ v₃ : ι ⊕ Z, K.Adj v₀ v₁ ∧ K.Adj v₁ v₂ ∧ K.Adj v₂ v₃ ∧ v₀ ≠ v₂ ∧ v₁ ≠ v₃ ∧
    ψ (K.pt v₀) = K.pt v₀ ∧ ψ (K.pt v₁) = K.pt v₁ ∧ ψ (K.pt v₂) = K.pt v₂ ∧
      ψ (K.pt v₃) = K.pt v₃

/-- **Local injectivity of the last vertex**: two neighbours of a vertex of the tree with the
same last vertex coincide. -/
lemma Tree.eq_of_adj_of_head_eq {t a b : K.Tree r} (ha : t.Adj a) (hb : t.Adj b)
    {v : ι ⊕ Z} (hav : a.1.head? = some v) (hbv : b.1.head? = some v) : a = b := by
  obtain ⟨h, hh⟩ := Tree.exists_head t
  have hv : K.Adj h v := adj_head t.2 a.2 ha hh hav
  rw [Tree.eq_nbr ha hh hv hav, Tree.eq_nbr hb hh hv hbv]

section Over

variable (hη : ∀ i, K.η i ∉ K.S) {f : K.Cover r → K.Cover r} {ψ : Z → Z}
  (hfψ : ∀ x, (f x).1.1 = ψ x.1.1) (hgen : ∀ i, ∃ j, ψ (K.η i) = K.η j)
  (hS : ∀ z, ψ z ∈ K.S ↔ z ∈ K.S)

include hfψ hgen hS in
/-- A vertex of the tree fixed by the map of vertices of `f` lies over a point fixed by `ψ`. -/
lemma pt_fixed_of_vmap_eq {t : K.Tree r} (ht : vmap hη f t = t) {v : ι ⊕ Z}
    (hv : t.1.head? = some v) : ψ (K.pt v) = K.pt v := by
  have hc := hfψ (canon hη t)
  change (f (canon hη t)).1.1 = ψ (canonPt t) at hc
  rcases v with i | s
  · obtain ⟨j, hj, hpt⟩ := vmap_inl_of_over hη hη hfψ hgen hv
    rw [ht, hv] at hj
    simp only [Option.some.injEq, Sum.inl.injEq] at hj
    subst hj
    rw [hpt, canonPt_of_inl hv] at hc
    exact hc.symm
  · obtain ⟨s', hs', hpt⟩ := vmap_inr_of_over hη hfψ hS hv
    rw [ht, hv] at hs'
    simp only [Option.some.injEq, Sum.inr.injEq] at hs'
    subst hs'
    rw [hpt, canonPt_of_inr hv] at hc
    exact hc.symm

include hfψ hgen hS in
/-- **An arc of the tree fixed by the map of vertices of `f` gives an arc of the incidence graph
fixed by `ψ`.** -/
theorem fixedArc_of_tree {t₀ t₁ t₂ t₃ : K.Tree r} (h₀₁ : t₀.Adj t₁) (h₁₂ : t₁.Adj t₂)
    (h₂₃ : t₂.Adj t₃) (h₀₂ : t₀ ≠ t₂) (h₁₃ : t₁ ≠ t₃) (f₀ : vmap hη f t₀ = t₀)
    (f₁ : vmap hη f t₁ = t₁) (f₂ : vmap hη f t₂ = t₂) (f₃ : vmap hη f t₃ = t₃) :
    K.FixedArc ψ := by
  obtain ⟨v₀, e₀⟩ := Tree.exists_head t₀
  obtain ⟨v₁, e₁⟩ := Tree.exists_head t₁
  obtain ⟨v₂, e₂⟩ := Tree.exists_head t₂
  obtain ⟨v₃, e₃⟩ := Tree.exists_head t₃
  refine ⟨v₀, v₁, v₂, v₃, adj_head t₀.2 t₁.2 h₀₁ e₀ e₁, adj_head t₁.2 t₂.2 h₁₂ e₁ e₂,
    adj_head t₂.2 t₃.2 h₂₃ e₂ e₃, fun h ↦ ?_, fun h ↦ ?_,
    pt_fixed_of_vmap_eq hη hfψ hgen hS f₀ e₀, pt_fixed_of_vmap_eq hη hfψ hgen hS f₁ e₁,
    pt_fixed_of_vmap_eq hη hfψ hgen hS f₂ e₂, pt_fixed_of_vmap_eq hη hfψ hgen hS f₃ e₃⟩
  · subst h
    exact h₀₂ (Tree.eq_of_adj_of_head_eq (Tree.adj_comm.1 h₀₁) h₁₂ e₀ e₂)
  · subst h
    exact h₁₃ (Tree.eq_of_adj_of_head_eq (Tree.adj_comm.1 h₁₂) h₂₃ e₁ e₃)

end Over

end CurveConfig

end TemperedFundamentalGroups
