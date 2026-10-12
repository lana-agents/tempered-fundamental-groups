/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Set.Finite.Lattice

/-!
# Fixed points of groups acting on trees (Blueprint §12.3, T1–T5)

Let `G` be a tree (`SimpleGraph.IsTree`).

* `TreeGeom.eq_of_adj_of_dist_lt`: a vertex has at most one neighbour closer to a given vertex.
* `TreeGeom.dist_eq_gate` (**T1**, gate lemma): for adjacent `x ~ z`, a vertex `y` on the side of
  `z` and a vertex `s` on the side of `x`, `d(y, s) = d(y, z) + 1 + d(x, s)`.
* `TreeGeom.adj_of_mem_centre` (**T2**): two different vertices minimising the eccentricity
  `x ↦ max_{s ∈ S} d(x, s)` of a finite nonempty set `S` are adjacent.
* `TreeGeom.exists_fixed` (**T3**): a group acting by graph automorphisms that never moves a
  vertex to a neighbour (an action *without inversions*, e.g. preserving a 2-colouring) and has a
  finite nonempty invariant set fixes a vertex, within the eccentricity of each point of the set;
  `TreeGeom.exists_fixed_of_finite` for finite groups.
* `TreeGeom.smul_eq_of_mem_geodesic` (**T4**): an automorphism fixing `x` and `y` fixes every
  vertex on the geodesic between them, and `TreeGeom.exists_adj_fixed` the neighbour of `x`
  towards `y`.
* `TreeGeom.dist_map_le` (**T5**): non-expanding maps do not increase distances;
  `TreeGeom.finite_ball`: balls in locally finite connected graphs are finite.
* `TreeGeom.isAcyclic_of_rank`: graphs in which every vertex has at most one neighbour of smaller
  rank, adjacent ranks differing by one, are acyclic (used for the tree covering of an incidence
  graph, `SemiAnbd/IncidenceTree.lean`).
-/

namespace TemperedFundamentalGroups.TreeGeom

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

section Basic

/-- A vertex at distance `n + 1` from `u` has a neighbour at distance `n` from `u`. -/
lemma exists_adj_dist_eq (hG : G.Connected) {u v : V} {n : ℕ} (h : G.dist u v = n + 1) :
    ∃ w, G.Adj v w ∧ G.dist u w = n := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist v u
  rw [dist_comm, h] at hp
  cases p with
  | nil => simp at hp
  | @cons _ w _ hadj q =>
    refine ⟨w, hadj, le_antisymm ?_ ?_⟩
    · rw [dist_comm]
      exact (dist_le q).trans (by simp at hp; omega)
    · have h1 := hG.dist_triangle (u := u) (v := w) (w := v)
      rw [dist_comm (u := w), dist_eq_one_iff_adj.2 hadj] at h1
      omega

/-- Distances to the ends of an edge differ by one. -/
lemma dist_adj_le (hG : G.Connected) {u v w : V} (hadj : G.Adj v w) :
    G.dist u w ≤ G.dist u v + 1 := by
  have := hG.dist_triangle (u := u) (v := v) (w := w)
  rwa [dist_eq_one_iff_adj.2 hadj] at this

/-- **Uniqueness of the closer neighbour**: in a tree a vertex has at most one neighbour closer
to a given vertex. -/
lemma eq_of_adj_of_dist_lt (hG : G.IsTree) {a b c s : V} (hab : G.Adj a b) (hac : G.Adj a c)
    (hb : G.dist b s < G.dist a s) (hc : G.dist c s < G.dist a s) : b = c := by
  have e1 : G.dist s a = G.dist a s := dist_comm
  have e2 : G.dist s b = G.dist b s := dist_comm
  have e3 : G.dist s c = G.dist c s := dist_comm
  have hb' : G.dist a s = G.dist b s + 1 := by
    rcases hG.dist_eq_dist_add_one_of_adj s hab with h | h <;> omega
  have hc' : G.dist a s = G.dist c s + 1 := by
    rcases hG.dist_eq_dist_add_one_of_adj s hac with h | h <;> omega
  obtain ⟨pb, hpb⟩ := hG.connected.exists_walk_length_eq_dist b s
  obtain ⟨pc, hpc⟩ := hG.connected.exists_walk_length_eq_dist c s
  have h1 : (Walk.cons hab pb).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by simp [hpb, hb'])
  have h2 : (Walk.cons hac pc).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by simp [hpc, hc'])
  have := congrArg Subtype.val (hG.isAcyclic.path_unique ⟨_, h1⟩ ⟨_, h2⟩)
  have h3 := congrArg (fun p : G.Walk a s ↦ p.getVert 1) this
  simpa using h3

end Basic

section Gate

/-- **T1, the gate lemma.** For adjacent `x ~ z`, if `s` is closer to `x` than to `z` and `y` is
closer to `z` than to `x`, then the geodesic from `y` to `s` passes through `z` and `x`. -/
theorem dist_eq_gate (hG : G.IsTree) {x z s : V} (hxz : G.Adj x z)
    (hs : G.dist x s < G.dist z s) :
    ∀ (n : ℕ) (y : V), G.dist z y = n → G.dist z y < G.dist x y →
      G.dist y s = n + 1 + G.dist x s := by
  have hconn := hG.connected
  have hzs : G.dist z s = G.dist x s + 1 := by
    rcases hG.dist_eq_dist_add_one_of_adj s hxz with h | h
    · rw [dist_comm (u := x), h, dist_comm] at hs; omega
    · rw [dist_comm, h, dist_comm]
  -- for `y` on the side of `z`, `d(x, y) = d(z, y) + 1`
  have hside : ∀ y, G.dist z y < G.dist x y → G.dist x y = G.dist z y + 1 := by
    intro y hy
    rcases hG.dist_eq_dist_add_one_of_adj y hxz with h | h
    · rw [dist_comm (u := x), h, dist_comm]
    · rw [dist_comm (u := z), dist_comm (u := x)] at hy; omega
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro y hn hy
  rcases n with _ | n
  · rw [← hconn.dist_eq_zero_iff.1 hn]; omega
  · obtain ⟨y', hyy', hy'⟩ := exists_adj_dist_eq hconn hn
    have hxy := hside y hy
    have hxy' : G.dist x y ≤ G.dist x y' + 1 := dist_adj_le (u := x) hconn hyy'.symm
    have IH := ih n (by omega) y' hy' (by omega)
    rcases hG.dist_eq_dist_add_one_of_adj s hyy' with h | h
    · rw [dist_comm (u := s), dist_comm (u := s)] at h; omega
    · exfalso
      rw [dist_comm (u := s), dist_comm (u := s)] at h
      -- the neighbour `w` of `y'` towards `z` is also closer to `s`
      obtain ⟨w, hy'w, hw, hwy⟩ : ∃ w, G.Adj y' w ∧ G.dist w s + 1 = G.dist y' s ∧ w ≠ y := by
        rcases n with _ | m
        · have hz : z = y' := hconn.dist_eq_zero_iff.1 hy'
          subst hz
          refine ⟨x, hxz.symm, by omega, ?_⟩
          rintro rfl
          simp at hy
        · obtain ⟨w, hy'w, hw⟩ := exists_adj_dist_eq hconn hy'
          have hxw : G.dist x y' ≤ G.dist x w + 1 := dist_adj_le (u := x) hconn hy'w.symm
          have IHw := ih m (by omega) w hw (by omega)
          refine ⟨w, hy'w, by omega, ?_⟩
          rintro rfl
          omega
      exact hwy (eq_of_adj_of_dist_lt (s := s) hG hy'w hyy'.symm (by omega) (by omega))

/-- The gate lemma without the auxiliary distance. -/
theorem dist_eq_gate' (hG : G.IsTree) {x z s y : V} (hxz : G.Adj x z)
    (hs : G.dist x s < G.dist z s) (hy : G.dist z y < G.dist x y) :
    G.dist y s = G.dist z y + 1 + G.dist x s :=
  dist_eq_gate hG hxz hs _ y rfl hy

end Gate

section Centre

variable (G) in
/-- The eccentricity of `x` with respect to a finite set `S`: `max_{s ∈ S} d(x, s)`. -/
noncomputable def ecc (S : Finset V) (x : V) : ℕ := S.sup fun s ↦ G.dist x s

lemma dist_le_ecc {S : Finset V} {s : V} (hs : s ∈ S) (x : V) : G.dist x s ≤ ecc G S x :=
  Finset.le_sup (f := fun s ↦ G.dist x s) hs

/-- **T2**: two different vertices of minimal eccentricity are adjacent. -/
theorem adj_of_mem_centre (hG : G.IsTree) {S : Finset V} (hS : S.Nonempty) {x y : V}
    (hx : ∀ w, ecc G S x ≤ ecc G S w) (hy : ∀ w, ecc G S y ≤ ecc G S w) (hxy : x ≠ y) :
    G.Adj x y := by
  have hconn := hG.connected
  by_contra hadj
  have h2 : 2 ≤ G.dist x y := by
    have h0 := hconn.pos_dist_of_ne hxy
    have h1 : G.dist x y ≠ 1 := fun h ↦ hadj (dist_eq_one_iff_adj.1 h)
    omega
  obtain ⟨z, hxz, hz⟩ : ∃ z, G.Adj x z ∧ G.dist y z + 1 = G.dist y x := by
    obtain ⟨z, hz, hzd⟩ := exists_adj_dist_eq hconn (u := y) (v := x) (n := G.dist y x - 1)
      (by rw [dist_comm]; omega)
    exact ⟨z, hz, by rw [dist_comm (u := y) (v := x)] at hzd ⊢; omega⟩
  have hzy : G.dist z y < G.dist x y := by rw [dist_comm, dist_comm (u := x)]; omega
  have hlt : ecc G S z < ecc G S x := by
    obtain ⟨s₀, hs₀⟩ := hS
    have hpos : ⊥ < ecc G S x := by
      have := dist_le_ecc (G := G) hs₀ y
      have := hy x
      have := dist_le_ecc (G := G) hs₀ x
      -- `ecc x ≥ d(x, s₀)` and `ecc x ≥ ... `; positivity from `d(x, y) ≥ 2`
      have hxs : 0 < G.dist x s₀ ∨ 0 < G.dist y s₀ := by
        by_contra! h
        have hx0 : x = s₀ := hconn.dist_eq_zero_iff.1 (by omega)
        have hy0 : y = s₀ := hconn.dist_eq_zero_iff.1 (by omega)
        exact hxy (hx0.trans hy0.symm)
      change 0 < _
      omega
    rw [ecc, Finset.sup_lt_iff hpos]
    intro s hs
    rcases hG.dist_eq_dist_add_one_of_adj s hxz with h | h
    · rw [dist_comm (u := s), dist_comm (u := s)] at h
      exact lt_of_lt_of_le (by omega) (dist_le_ecc hs x)
    · rw [dist_comm (u := s), dist_comm (u := s)] at h
      have hg := dist_eq_gate' (s := s) hG hxz (by omega) hzy
      have hzy0 : 0 < G.dist z y := by
        refine hconn.pos_dist_of_ne fun hzy' ↦ hadj ?_
        rw [← hzy']
        exact hxz
      have := dist_le_ecc (G := G) hs y
      have := hy x
      omega
  exact absurd (hx z) (not_le.2 hlt)

/-- The centre of a finite nonempty set is nonempty. -/
lemma exists_centre (S : Finset V) [Nonempty V] : ∃ x, ∀ w, ecc G S x ≤ ecc G S w := by
  obtain ⟨x, hx⟩ := Nat.sInf_mem (Set.range_nonempty (ecc G S))
  exact ⟨x, fun w ↦ hx ▸ Nat.sInf_le ⟨w, rfl⟩⟩

end Centre


section Maps

variable {V' : Type*} {G' : SimpleGraph V'}

/-- Non-expanding maps send walks to walks that are not longer. -/
lemma exists_walk_map_le (f : V → V') (hf : ∀ x y, G.Adj x y → G'.Adj (f x) (f y) ∨ f x = f y)
    {x y : V} (p : G.Walk x y) : ∃ q : G'.Walk (f x) (f y), q.length ≤ p.length := by
  induction p with
  | nil => exact ⟨Walk.nil, le_rfl⟩
  | @cons u v w h p ih =>
    obtain ⟨q, hq⟩ := ih
    rcases hf u v h with h' | h'
    · exact ⟨Walk.cons h' q, by simp [hq]⟩
    · exact ⟨q.copy h'.symm rfl, by simp only [Walk.length_cons, Walk.length_copy]; omega⟩

/-- **T5**: non-expanding maps (adjacent vertices go to adjacent or equal vertices) do not
increase distances. -/
theorem dist_map_le (hG : G.Connected) (f : V → V')
    (hf : ∀ x y, G.Adj x y → G'.Adj (f x) (f y) ∨ f x = f y) (x y : V) :
    G'.dist (f x) (f y) ≤ G.dist x y := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist x y
  obtain ⟨q, hq⟩ := exists_walk_map_le f hf p
  exact (dist_le q).trans (hp ▸ hq)

/-- **T5**: balls of a connected locally finite graph are finite. -/
theorem finite_ball (hG : G.Connected) (hlf : ∀ v, (G.neighborSet v).Finite) (x : V) (n : ℕ) :
    {y | G.dist x y ≤ n}.Finite := by
  induction n with
  | zero =>
    refine (Set.finite_singleton x).subset fun y hy ↦ ?_
    exact (hG.dist_eq_zero_iff.1 (Nat.le_zero.1 hy)).symm
  | succ n ih =>
    refine (ih.union (ih.biUnion fun w _ ↦ hlf w)).subset fun y hy ↦ ?_
    rcases Nat.lt_or_ge (G.dist x y) (n + 1) with h | h
    · exact .inl (Nat.lt_succ_iff.1 h)
    · obtain ⟨w, hyw, hw⟩ := exists_adj_dist_eq hG (le_antisymm hy h)
      exact .inr (Set.mem_biUnion (x := w) (le_of_eq hw) hyw.symm)

end Maps

section Action

variable {Γ : Type*} [Group Γ] [MulAction Γ V]

/-- Graph automorphisms preserve distances. -/
lemma dist_smul (hG : G.Connected) (hadj : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (g : Γ) (x y : V) : G.dist (g • x) (g • y) = G.dist x y := by
  refine le_antisymm (dist_map_le hG (g • ·) (fun a b h ↦ .inl ((hadj g a b).2 h)) x y) ?_
  have := dist_map_le hG (g⁻¹ • ·) (fun a b h ↦ .inl ((hadj g⁻¹ a b).2 h)) (g • x) (g • y)
  simpa using this

lemma ecc_smul (hG : G.Connected) (hadj : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    {S : Finset V} (hS : ∀ (g : Γ), ∀ s ∈ S, g • s ∈ S) (g : Γ) (x : V) :
    ecc G S (g • x) = ecc G S x := by
  have key : ∀ (g : Γ) x, ecc G S (g • x) ≤ ecc G S x := by
    intro g x
    refine Finset.sup_le fun s hs ↦ ?_
    have h := dist_smul hG hadj g x (g⁻¹ • s)
    rw [smul_inv_smul] at h
    exact h ▸ dist_le_ecc (hS g⁻¹ s hs) x
  refine le_antisymm (key g x) ?_
  have := key g⁻¹ (g • x)
  rwa [inv_smul_smul] at this

/-- **T3, fixed point theorem.** A group acting on a tree by graph automorphisms without
inversions (no vertex is moved to a neighbour) with a finite nonempty invariant set `S` fixes a
vertex `c`, at distance at most the eccentricity `max_{s ∈ S} d(x, s)` from every `x ∈ S`. -/
theorem exists_fixed (hG : G.IsTree) (hadj : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (hinv : ∀ (g : Γ) x, ¬ G.Adj x (g • x)) {S : Finset V} (hS : S.Nonempty)
    (hSinv : ∀ (g : Γ), ∀ s ∈ S, g • s ∈ S) :
    ∃ c, (∀ g : Γ, g • c = c) ∧ ∀ x ∈ S, G.dist x c ≤ ecc G S x := by
  have : Nonempty V := ⟨hS.choose⟩
  obtain ⟨c, hc⟩ := exists_centre (G := G) S
  refine ⟨c, fun g ↦ ?_, fun x hx ↦ ?_⟩
  · by_contra hne
    have hgc : ∀ w, ecc G S (g • c) ≤ ecc G S w := fun w ↦
      (ecc_smul hG.connected hadj hSinv g c).symm ▸ hc w
    exact hinv g c (adj_of_mem_centre hG hS hc hgc (Ne.symm hne))
  · rw [dist_comm]
    exact (dist_le_ecc hx c).trans (hc x)

/-- **T3 for bounded orbits**: in a locally finite tree, a group acting without inversions that
moves `x` by at most `D` fixes a vertex at distance at most `D` from `x`. -/
theorem exists_fixed_of_bounded (hG : G.IsTree) (hlf : ∀ v, (G.neighborSet v).Finite)
    (hadj : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (hinv : ∀ (g : Γ) x, ¬ G.Adj x (g • x)) (x : V) (D : ℕ)
    (hD : ∀ g : Γ, G.dist x (g • x) ≤ D) :
    ∃ c, (∀ g : Γ, g • c = c) ∧ G.dist x c ≤ D := by
  have hfin : (Set.range fun g : Γ ↦ g • x).Finite :=
    (finite_ball hG.connected hlf x D).subset (Set.range_subset_iff.2 hD)
  set S := hfin.toFinset
  have hxS : x ∈ S := by simpa [S] using ⟨1, one_smul Γ x⟩
  have hSinv : ∀ (g : Γ), ∀ s ∈ S, g • s ∈ S := by
    intro g s hs
    obtain ⟨h, rfl⟩ : s ∈ Set.range fun g : Γ ↦ g • x := by simpa [S] using hs
    simp [S, smul_smul]
  obtain ⟨c, hc, hcS⟩ := exists_fixed hG hadj hinv ⟨x, hxS⟩ hSinv
  refine ⟨c, hc, (hcS x hxS).trans (Finset.sup_le fun s hs ↦ ?_)⟩
  obtain ⟨h, rfl⟩ : s ∈ Set.range fun g : Γ ↦ g • x := by simpa [S] using hs
  exact hD h

/-- **T3 for finite groups**: a finite group acting on a tree without inversions fixes a
vertex. -/
theorem exists_fixed_of_finite [Finite Γ] (hG : G.IsTree)
    (hadj : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y)
    (hinv : ∀ (g : Γ) x, ¬ G.Adj x (g • x)) : ∃ c : V, ∀ g : Γ, g • c = c := by
  obtain ⟨x⟩ := hG.connected.nonempty
  have hfin : (Set.range fun g : Γ ↦ g • x).Finite := Set.finite_range _
  set S := hfin.toFinset
  have hxS : x ∈ S := by simpa [S] using ⟨1, one_smul Γ x⟩
  have hSinv : ∀ (g : Γ), ∀ s ∈ S, g • s ∈ S := by
    intro g s hs
    obtain ⟨h, rfl⟩ : s ∈ Set.range fun g : Γ ↦ g • x := by simpa [S] using hs
    simp [S, smul_smul]
  obtain ⟨c, hc, -⟩ := exists_fixed hG hadj hinv ⟨x, hxS⟩ hSinv
  exact ⟨c, hc⟩

end Action

section Geodesic

/-- In a tree, a vertex on a geodesic from `x` to `y` is determined by its distance to `x`. -/
theorem eq_of_mem_geodesic (hG : G.IsTree) {x y w w' : V}
    (hw : G.dist x w + G.dist w y = G.dist x y) (hw' : G.dist x w' + G.dist w' y = G.dist x y)
    (h : G.dist x w = G.dist x w') : w = w' := by
  obtain ⟨p, hp⟩ := hG.connected.exists_walk_length_eq_dist x w
  obtain ⟨q, hq⟩ := hG.connected.exists_walk_length_eq_dist w y
  obtain ⟨p', hp'⟩ := hG.connected.exists_walk_length_eq_dist x w'
  obtain ⟨q', hq'⟩ := hG.connected.exists_walk_length_eq_dist w' y
  have h1 : (p.append q).IsPath := Walk.isPath_of_length_eq_dist _ (by simp [hp, hq, hw])
  have h2 : (p'.append q').IsPath := Walk.isPath_of_length_eq_dist _ (by simp [hp', hq', hw'])
  have := congrArg Subtype.val (hG.isAcyclic.path_unique ⟨_, h1⟩ ⟨_, h2⟩)
  have h3 := congrArg (fun r : G.Walk x y ↦ r.getVert (G.dist x w)) this
  have hl : p.length = p'.length := by rw [hp, hp', h]
  simp only [Walk.getVert_append, ← hp, lt_irrefl, if_false, Nat.sub_self, Walk.getVert_zero,
    hl] at h3
  exact h3

/-- **T4**: an automorphism of a tree fixing `x` and `y` fixes every vertex on the geodesic
from `x` to `y`. -/
theorem smul_eq_of_mem_geodesic {Γ : Type*} [Group Γ] [MulAction Γ V] (hG : G.IsTree)
    (hadj : ∀ (g : Γ) x y, G.Adj (g • x) (g • y) ↔ G.Adj x y) {g : Γ} {x y w : V}
    (hx : g • x = x) (hy : g • y = y) (hw : G.dist x w + G.dist w y = G.dist x y) :
    g • w = w := by
  have h1 := dist_smul hG.connected hadj g x w
  have h2 := dist_smul hG.connected hadj g w y
  rw [hx] at h1
  rw [hy] at h2
  exact eq_of_mem_geodesic hG (by rw [h1, h2, hw]) hw h1

/-- The neighbour of `x` towards `y ≠ x`. -/
lemma exists_adj_geodesic (hG : G.Connected) {x y : V} (hxy : x ≠ y) :
    ∃ w, G.Adj x w ∧ G.dist x w + G.dist w y = G.dist x y := by
  have hpos := hG.pos_dist_of_ne hxy
  obtain ⟨w, hw, hwd⟩ := exists_adj_dist_eq hG (u := y) (v := x) (n := G.dist y x - 1)
    (by rw [dist_comm]; omega)
  refine ⟨w, hw, ?_⟩
  rw [dist_eq_one_iff_adj.2 hw, dist_comm (u := w), hwd, dist_comm (u := y)]
  omega

end Geodesic

section Rank

/-- A graph with a rank function such that adjacent vertices have ranks differing by one and
every vertex has at most one neighbour of smaller rank (a "parent") is acyclic. -/
theorem isAcyclic_of_rank (rk : V → ℕ) (hadj : ∀ x y, G.Adj x y → rk x = rk y + 1 ∨ rk y = rk x + 1)
    (huniq : ∀ x y z, G.Adj x y → G.Adj x z → rk y < rk x → rk z < rk x → y = z) :
    G.IsAcyclic := by
  classical
  intro v c hc
  obtain ⟨m, hm, hmax⟩ := c.support.toFinset.exists_max_image rk ⟨v, by simp⟩
  have hm' : m ∈ c.support := by simpa using hm
  have hc' : (c.rotate m hm').IsCycle := hc.rotate hm'
  have hsub : ∀ x ∈ (c.rotate m hm').support, rk x ≤ rk m := by
    intro x hx
    refine hmax x (List.mem_toFinset.2 ?_)
    rw [Walk.rotate, Walk.mem_support_append_iff] at hx
    rcases hx with hx | hx
    · exact Walk.support_dropUntil_subset_support _ _ hx
    · exact Walk.support_takeUntil_subset_support _ _ hx
  have hnil := hc'.not_nil
  have h1 := (c.rotate m hm').adj_snd hnil
  have h2 := (c.rotate m hm').adj_penultimate hnil
  have r1 : rk (c.rotate m hm').snd ≤ rk m := hsub _ ((c.rotate m hm').getVert_mem_support 1)
  have r2 : rk (c.rotate m hm').penultimate ≤ rk m :=
    hsub _ ((c.rotate m hm').getVert_mem_support ((c.rotate m hm').length - 1))
  have e1 := hadj _ _ h1
  have e2 := hadj _ _ h2
  exact hc'.snd_ne_penultimate (huniq m _ _ h1 h2.symm (by omega) (by omega))

end Rank

end TemperedFundamentalGroups.TreeGeom
