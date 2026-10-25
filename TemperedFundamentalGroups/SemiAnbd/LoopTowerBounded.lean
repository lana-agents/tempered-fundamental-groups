/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Tactic.Group
import TemperedFundamentalGroups.SemiAnbd.LoopTowerSys
import TemperedFundamentalGroups.SemiAnbd.SysEstranged

/-!
# Estrangement of systems in the loop tower: the bounded case

Let `Π` be a compact vertex group with closed branch images `Π_A = b₀(E)`, `Π_B = b₁(E)` that are
**estranged** in the sense of [SemiAnbd] Def 2.4(iv) (`Π_X ∩ q Π_Y q⁻¹ = 1` whenever `X ≠ Y`, or
`X = Y` and `q ∉ Π_X`). We show that a nontrivial element `g` of the loop group fixing two
compatible systems `s`, `s'` whose distances `d_N(s_N, s'_N)` are **bounded** keeps them at
distance `≤ 2` at every level.

Proof: the distances are eventually constant `= D`; if `D ≥ 3`, the geodesics from `s_N` to `s'_N`
map isometrically to each other along the transition maps, so their points form compatible systems,
all fixed by `g`. Among the points at distance `1, 2` from `s` there is one of vertex kind with two
distinct neighbouring edge systems on the geodesic. Translating it to the base system
(`exists_smul_baseSys`), `g` becomes the image of some `σ ≠ 1` in `Π` fixing two distinct edge
systems at the base vertex; by compactness of `Π × Π` there are `q, q' ∈ Π` with
`σ ∈ q Π_X q⁻¹ ∩ q' Π_Y q'⁻¹` and `(X, q⁻¹ q')` a rival of `X` — contradicting estrangement.

* `TreeGeom.exists_mem_geodesic`, `TreeGeom.geoPt` (points on geodesics), `TreeTower.map_geoPt`;
* `LoopTower.ebase`: the edges at the base vertex, `LoopTower.exists_ebase`;
* **`LoopTower.false_of_fix_two_edges`**: no `σ ≠ 1` fixes two distinct edge systems at the base;
* **`LoopTower.dist_le_two_of_bounded`**: the bounded case of `TreeTower.SysEstranged`.
-/

open CategoryTheory HNNExtension QuotientGroup TemperedFundamentalGroups.TreeGeom
open scoped Pointwise

namespace TemperedFundamentalGroups

namespace TreeGeom

variable {V : Type*} {G : SimpleGraph V}

/-- Every distance `i ≤ d(x, y)` is realised by a point on a geodesic from `x` to `y`. -/
lemma exists_mem_geodesic (hG : G.Connected) (x y : V) {i : ℕ} (hi : i ≤ G.dist x y) :
    ∃ w, G.dist x w = i ∧ G.dist w y = G.dist x y - i := by
  induction i with
  | zero => exact ⟨x, by simp, by simp⟩
  | succ i ih =>
    obtain ⟨w, hw1, hw2⟩ := ih (by omega)
    have hne : w ≠ y := by
      rintro rfl
      rw [SimpleGraph.dist_self] at hw2
      omega
    obtain ⟨w', hadj, hw'⟩ := exists_adj_geodesic hG hne
    rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at hw'
    refine ⟨w', le_antisymm ?_ ?_, by omega⟩
    · have := dist_adj_le hG (u := x) hadj
      omega
    · have := hG.dist_triangle (u := x) (v := w') (w := y)
      omega

open Classical in
/-- The point at distance `i` from `x` on the geodesic from `x` to `y` (for `i ≤ d(x, y)`). -/
noncomputable def geoPt (G : SimpleGraph V) (x y : V) (i : ℕ) : V :=
  haveI : Nonempty V := ⟨x⟩
  Classical.epsilon fun w ↦ G.dist x w = i ∧ G.dist w y = G.dist x y - i

lemma geoPt_spec (hG : G.Connected) {x y : V} {i : ℕ} (hi : i ≤ G.dist x y) :
    G.dist x (geoPt G x y i) = i ∧ G.dist (geoPt G x y i) y = G.dist x y - i :=
  haveI : Nonempty V := ⟨x⟩
  Classical.epsilon_spec (exists_mem_geodesic hG x y hi)

lemma eq_geoPt (hG : G.IsTree) {x y w : V} {i : ℕ} (hi : i ≤ G.dist x y) (hw1 : G.dist x w = i)
    (hw2 : G.dist w y = G.dist x y - i) : w = geoPt G x y i := by
  have h := geoPt_spec hG.connected hi
  exact eq_of_mem_geodesic (x := x) (y := y) hG (by omega) (by omega) (by rw [hw1, h.1])

lemma adj_geoPt (hG : G.IsTree) {x y : V} {i : ℕ} (hi : i + 1 ≤ G.dist x y) :
    G.Adj (geoPt G x y i) (geoPt G x y (i + 1)) := by
  have h := geoPt_spec hG.connected (x := x) (y := y) (i := i) (by omega)
  have hne : geoPt G x y i ≠ y := by
    intro he
    rw [he, SimpleGraph.dist_self] at h
    omega
  obtain ⟨w', hadj, hw'⟩ := exists_adj_geodesic hG.connected hne
  rw [SimpleGraph.dist_eq_one_iff_adj.2 hadj] at hw'
  have h1 : G.dist x w' = i + 1 := by
    refine le_antisymm ?_ ?_
    · have := dist_adj_le hG.connected (u := x) hadj
      omega
    · have := hG.connected.dist_triangle (u := x) (v := w') (w := y)
      omega
  rwa [← eq_geoPt hG hi h1 (by omega)]

lemma geoPt_ne (hG : G.Connected) {x y : V} {i j : ℕ} (hi : i ≤ G.dist x y)
    (hj : j ≤ G.dist x y) (hij : i ≠ j) : geoPt G x y i ≠ geoPt G x y j := by
  intro h
  have h1 := (geoPt_spec hG hi).1
  rw [h, (geoPt_spec hG hj).1] at h1
  exact hij h1.symm

end TreeGeom

namespace TreeTower

variable {Γ : Type*} [Group Γ] {J : Type*} [Category J] (T : TreeTower Γ J)

/-- A transition map preserving the distance of two points maps the geodesic between them onto the
geodesic between their images. -/
lemma map_geoPt {j k : J} (f : j ⟶ k) {x y : T.V j}
    (hd : (T.graph k).dist (T.map f x) (T.map f y) = (T.graph j).dist x y) {i : ℕ}
    (hi : i ≤ (T.graph j).dist x y) :
    T.map f (geoPt (T.graph j) x y i) = geoPt (T.graph k) (T.map f x) (T.map f y) i := by
  have h := geoPt_spec (T.isTree j).connected hi
  have h1 := T.dist_map_le f x (geoPt (T.graph j) x y i)
  have h2 := T.dist_map_le f (geoPt (T.graph j) x y i) y
  have h3 := (T.isTree k).connected.dist_triangle (u := T.map f x)
    (v := T.map f (geoPt (T.graph j) x y i)) (w := T.map f y)
  exact eq_geoPt (T.isTree k) (by omega) (by omega) (by omega)

end TreeTower

namespace LoopTower

noncomputable section

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [Group E] {b₀ b₁ : E →* Pv}

variable (b₀ b₁) in
/-- The two branches: `false ↦ b₀` (image `A`), `true ↦ b₁` (image `B`). -/
def br : Bool → (E →* Pv)
  | false => b₀
  | true => b₁

/-- The image of the branch `X` in `Q_N`. -/
def branchX (N : Level b₀ b₁) (X : Bool) : Subgroup (levelQuot N) :=
  ((QuotientGroup.mk' N.1).comp (br b₀ b₁ X)).range

/-- The edges at the base vertex `G` of the tree at level `N`: `q B` (type `true`, from `G` to
`q t G`) and `q t⁻¹ B` (type `false`, from `q t⁻¹ G` to `G`). -/
def ebase (N : Level b₀ b₁) : Bool → levelQuot N → BSVertex (levelEquiv N)
  | true, q => .inr ((of q : levelGroup N) : _ ⧸ edgeSubgroup (levelEquiv N))
  | false, q => .inr ((of q * t⁻¹ : levelGroup N) : _ ⧸ edgeSubgroup (levelEquiv N))

/-- Every neighbour of the base vertex is an edge `ebase N X q`. -/
lemma exists_ebase (N : Level b₀ b₁) (w : BSVertex (levelEquiv N))
    (hw : (bassSerreGraph (levelEquiv N)).Adj ((baseSys b₀ b₁).1 N) w) :
    ∃ X q, w = ebase N X q := by
  rcases w with w | w
  · exact absurd hw (not_adj_inl_inl _ _)
  induction w using QuotientGroup.induction_on with
  | H k =>
  rw [SimpleGraph.adj_comm, adj_inr_iff] at hw
  rcases hw with hw | hw
  · obtain ⟨y, hy⟩ := mk_vertex_eq_iff.1 (Sum.inl_injective hw)
    rw [one_mul] at hy
    exact ⟨true, y, by rw [hy]; rfl⟩
  · obtain ⟨y, hy⟩ := mk_vertex_eq_iff.1 (Sum.inl_injective hw)
    rw [one_mul] at hy
    refine ⟨false, y, ?_⟩
    rw [show k = of y * t⁻¹ by rw [← hy, mul_inv_cancel_right]]
    rfl

lemma vertexMap_ebase {N N' : Level b₀ b₁} (h : N ≤ N') (X : Bool) (q : levelQuot N) :
    vertexMap h (ebase N X q) = ebase N' X (quotMap h q) := by
  cases X <;> simp [ebase, levelMap_of]

lemma t_inv_notMem_range (N : Level b₀ b₁) :
    (t⁻¹ : levelGroup N) ∉ (of : levelQuot N →* levelGroup N).range := by
  intro h
  have h1 := (tLength_eq_zero_iff _).2 h
  have h2 := tLength_of_mul_t_pow (φ := levelEquiv N) (1 : levelQuot N) (-1)
  rw [map_one, one_mul, Units.val_neg, Units.val_one, zpow_neg, zpow_one] at h2
  omega

lemma ebase_true_ne_false (N : Level b₀ b₁) (q q' : levelQuot N) :
    ebase N true q ≠ ebase N false q' := by
  intro h
  obtain ⟨b, hb⟩ := mk_edge_eq_iff.1 (Sum.inr_injective h)
  refine t_inv_notMem_range N ⟨q'⁻¹ * (q * b), ?_⟩
  rw [map_mul, map_mul, map_inv, ← hb, inv_mul_cancel_left]

lemma ebase_ne {N : Level b₀ b₁} {X Y : Bool} (hXY : X ≠ Y) (q q' : levelQuot N) :
    ebase N X q ≠ ebase N Y q' := by
  cases X <;> cases Y
  · exact absurd rfl hXY
  · exact (ebase_true_ne_false N q' q).symm
  · exact ebase_true_ne_false N q q'
  · exact absurd rfl hXY

lemma ebase_eq_of_mem {N : Level b₀ b₁} {X : Bool} {q q' : levelQuot N}
    (h : q⁻¹ * q' ∈ branchX N X) : ebase N X q = ebase N X q' := by
  cases X
  · refine congrArg Sum.inr (mk_edge_eq_iff.2 ⟨levelEquiv N ⟨_, h⟩, ?_⟩)
    rw [equiv_eq_conj]
    simp [mul_assoc]
  · refine congrArg Sum.inr (mk_edge_eq_iff.2 ⟨⟨_, h⟩, ?_⟩)
    simp

lemma mem_branchX_of_smul_ebase {N : Level b₀ b₁} {X : Bool} {q σ : levelQuot N}
    (h : (of σ : levelGroup N) • ebase N X q = ebase N X q) : q⁻¹ * σ * q ∈ branchX N X := by
  cases X
  · have h' := (stabilizer_inr N (of q * t⁻¹) (of σ)).1 h
    obtain ⟨b, hb, hbe⟩ := h'
    have h1 : (of (q⁻¹ * σ * q) : levelGroup N) = t⁻¹ * of b * t := by
      rw [hbe]; simp [mul_assoc]
    rw [← equiv_symm_eq_conj (b := ⟨b, hb⟩), (of_injective _).eq_iff] at h1
    rw [h1]
    exact ((levelEquiv N).symm ⟨b, hb⟩).2
  · have h' := (stabilizer_inr N (of q) (of σ)).1 h
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem (of_injective _)] at h'
    exact h'

/-- The edge type of a system of edges at the base vertex is constant. -/
lemma exists_type [IsTopologicalGroup Pv] (e : (tower b₀ b₁).Sys)
    (he : ∀ N, (bassSerreGraph (levelEquiv N)).Adj ((baseSys b₀ b₁).1 N) (e.1 N)) :
    ∃ X, ∀ N, ∃ q : Pv, e.1 N = ebase N X (q : levelQuot N) := by
  choose X q hq using fun N ↦ exists_ebase N (e.1 N) (he N)
  refine ⟨X Level.top, fun N ↦ ?_⟩
  obtain ⟨q₀, hq₀⟩ := QuotientGroup.mk_surjective (q N)
  refine ⟨q₀, ?_⟩
  rw [hq, ← hq₀]
  by_contra hne
  have hle : N ≤ Level.top := fun _ _ ↦ trivial
  have h1 := e.2 (homOfLE hle)
  change vertexMap hle (e.1 N) = e.1 Level.top at h1
  rw [hq N, vertexMap_ebase, hq Level.top] at h1
  exact ebase_ne (fun h ↦ hne (by rw [h])) _ _ h1

lemma ebase_sys {e : (tower b₀ b₁).Sys} {N N' : Level b₀ b₁} (h : N ≤ N') {X : Bool} {q : Pv}
    (hq : e.1 N = ebase N X (q : levelQuot N)) : e.1 N' = ebase N' X (q : levelQuot N') := by
  rw [← e.2 (homOfLE h)]
  change vertexMap h (e.1 N) = _
  rw [hq, vertexMap_ebase, quotMap_mk]

/-- A closed subset `K` of compact `Π` is the intersection of the `K N` over the levels, if the
levels separate the points of `Π`. -/
lemma mem_of_forall_level [CompactSpace Pv] [IsTopologicalGroup Pv]
    (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1) {K : Set Pv} (hK : IsClosed K)
    {x : Pv} (hx : ∀ N : Level b₀ b₁, ∃ k ∈ K, k⁻¹ * x ∈ N.1) : x ∈ K := by
  let F : Level b₀ b₁ → Set Pv := fun N ↦ K ∩ (fun k ↦ k⁻¹ * x) ⁻¹' (N.1 : Set Pv)
  have hFcl : ∀ N, IsClosed (F N) := fun N ↦
    hK.inter ((N.1.isClosed_of_isOpen N.2.2.1).preimage (continuous_inv.mul continuous_const))
  obtain ⟨k, hk⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F
    (fun N N' ↦ ⟨Level.inf N N', fun _ h ↦ ⟨h.1, Level.inf_le_left N N' h.2⟩,
      fun _ h ↦ ⟨h.1, Level.inf_le_right N N' h.2⟩⟩)
    (fun N ↦ hx N) (fun N ↦ (hFcl N).isCompact) hFcl
  rw [Set.mem_iInter] at hk
  have h1 : k⁻¹ * x = 1 := by
    by_contra hne
    obtain ⟨N, hN⟩ := hsep _ hne
    exact hN (hk N).2
  exact (inv_mul_eq_one.1 h1) ▸ (hk Level.top).1

/-- **No nontrivial element of `Π` fixes two distinct edge systems at the base vertex**, if the
branch images are closed and estranged ([SemiAnbd] Def 2.4(iv)). -/
theorem false_of_fix_two_edges [CompactSpace Pv] [IsTopologicalGroup Pv]
    (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1)
    (hcl : ∀ X, IsClosed ((br b₀ b₁ X).range : Set Pv))
    (hEst : ∀ (X Y : Bool) (q : Pv), (X ≠ Y ∨ q ∉ (br b₀ b₁ X).range) →
      (br b₀ b₁ X).range ⊓ (ConjAct.toConjAct q • (br b₀ b₁ Y).range) = ⊥)
    {σ : Pv} (hσ : σ ≠ 1) (e e' : (tower b₀ b₁).Sys)
    (he : ∀ N, (bassSerreGraph (levelEquiv N)).Adj ((baseSys b₀ b₁).1 N) (e.1 N))
    (he' : ∀ N, (bassSerreGraph (levelEquiv N)).Adj ((baseSys b₀ b₁).1 N) (e'.1 N))
    (hne : e ≠ e') (hf : vertexIncl b₀ b₁ σ ∈ TreeTower.stab e)
    (hf' : vertexIncl b₀ b₁ σ ∈ TreeTower.stab e') : False := by
  obtain ⟨X, hX⟩ := exists_type e he
  obtain ⟨Y, hY⟩ := exists_type e' he'
  -- compactness: representatives `q, q'` in `Π` compatible at all levels
  let F : Level b₀ b₁ → Set (Pv × Pv) := fun N ↦
    (fun p : Pv × Pv ↦ ((p.1 : levelQuot N), (p.2 : levelQuot N))) ⁻¹'
      {c | e.1 N = ebase N X c.1 ∧ e'.1 N = ebase N Y c.2}
  have hFcl : ∀ N, IsClosed (F N) := fun N ↦ by
    haveI : DiscreteTopology (levelQuot N) := QuotientGroup.discreteTopology N.2.2.1
    exact (isClosed_discrete _).preimage
      ((QuotientGroup.continuous_mk.comp continuous_fst).prodMk
        (QuotientGroup.continuous_mk.comp continuous_snd))
  obtain ⟨⟨q, q'⟩, hqq⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F
    (fun N N' ↦ ⟨Level.inf N N',
      fun p hp ↦ ⟨ebase_sys (Level.inf_le_left N N') hp.1,
        ebase_sys (Level.inf_le_left N N') hp.2⟩,
      fun p hp ↦ ⟨ebase_sys (Level.inf_le_right N N') hp.1,
        ebase_sys (Level.inf_le_right N N') hp.2⟩⟩)
    (fun N ↦ by
      obtain ⟨a, ha⟩ := hX N
      obtain ⟨a', ha'⟩ := hY N
      exact ⟨(a, a'), ha, ha'⟩)
    (fun N ↦ (hFcl N).isCompact) hFcl
  rw [Set.mem_iInter] at hqq
  -- `q⁻¹ σ q ∈ Π_X`, `q'⁻¹ σ q' ∈ Π_Y`
  have hmem : ∀ (Z : Bool) (r : Pv) (c : (tower b₀ b₁).Sys),
      vertexIncl b₀ b₁ σ ∈ TreeTower.stab c →
      (∀ N, c.1 N = ebase N Z (r : levelQuot N)) → r⁻¹ * σ * r ∈ (br b₀ b₁ Z).range := by
    intro Z r c hc hcr
    refine mem_of_forall_level hsep (hcl Z) fun N ↦ ?_
    have h1 := TreeTower.mem_stab.1 hc N
    rw [hcr N] at h1
    obtain ⟨ε, hε⟩ := mem_branchX_of_smul_ebase (σ := (σ : levelQuot N)) h1
    refine ⟨br b₀ b₁ Z ε, ⟨ε, rfl⟩, ?_⟩
    rw [← QuotientGroup.eq]
    exact hε
  have h1 := hmem X q e hf fun N ↦ (hqq N).1
  have h2 := hmem Y q' e' hf' fun N ↦ (hqq N).2
  -- `(X, q⁻¹ q')` is a rival of `X`
  have hrival : X ≠ Y ∨ q⁻¹ * q' ∉ (br b₀ b₁ X).range := by
    by_contra! hc
    obtain ⟨rfl, ε, hε⟩ := hc
    refine hne (TreeTower.Sys.ext fun N ↦ ?_)
    rw [(hqq N).1, (hqq N).2]
    refine ebase_eq_of_mem ⟨ε, ?_⟩
    rw [MonoidHom.comp_apply, hε]
    rfl
  have hbot := hEst X Y (q⁻¹ * q') hrival
  have hin : q⁻¹ * σ * q ∈ (br b₀ b₁ X).range ⊓
      (ConjAct.toConjAct (q⁻¹ * q') • (br b₀ b₁ Y).range) := by
    refine ⟨h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_⟩
    rw [← map_inv, ConjAct.toConjAct_smul]
    convert h2 using 1
    group
  rw [hbot, Subgroup.mem_bot] at hin
  apply hσ
  have h3 := congrArg (fun z ↦ q * z * q⁻¹) hin
  simpa [mul_assoc] using h3

/-! ### Systems from the levels below a fixed level -/

/-- The system extending a compatible family given below the level `N₀`. -/
def extSys (N₀ : Level b₀ b₁) (f : ∀ N : Level b₀ b₁, BSVertex (levelEquiv N))
    (hf : ∀ N N' (h : N ≤ N'), N' ≤ N₀ → vertexMap h (f N) = f N') : (tower b₀ b₁).Sys :=
  ⟨fun M ↦ vertexMap (Level.inf_le_left M N₀) (f (Level.inf M N₀)), fun {M M'} g ↦ by
    have hle : Level.inf M N₀ ≤ Level.inf M' N₀ :=
      fun x hx ↦ ⟨g.le hx.1, hx.2⟩
    change vertexMap g.le (vertexMap (Level.inf_le_left M N₀) (f (Level.inf M N₀))) =
      vertexMap (Level.inf_le_left M' N₀) (f (Level.inf M' N₀))
    rw [vertexMap_comp, ← hf _ _ hle (Level.inf_le_right M' N₀), vertexMap_comp]⟩

lemma extSys_apply {N₀ : Level b₀ b₁} {f : ∀ N : Level b₀ b₁, BSVertex (levelEquiv N)}
    {hf : ∀ N N' (h : N ≤ N'), N' ≤ N₀ → vertexMap h (f N) = f N'} {N : Level b₀ b₁}
    (hN : N ≤ N₀) : (extSys N₀ f hf).1 N = f N :=
  hf _ _ (Level.inf_le_left N N₀) hN

lemma extSys_adj {N₀ : Level b₀ b₁} {f f' : ∀ N : Level b₀ b₁, BSVertex (levelEquiv N)}
    {hf : ∀ N N' (h : N ≤ N'), N' ≤ N₀ → vertexMap h (f N) = f N'}
    {hf' : ∀ N N' (h : N ≤ N'), N' ≤ N₀ → vertexMap h (f' N) = f' N'}
    (hadj : ∀ N, N ≤ N₀ → (bassSerreGraph (levelEquiv N)).Adj (f N) (f' N)) (M : Level b₀ b₁) :
    (bassSerreGraph (levelEquiv M)).Adj ((extSys N₀ f hf).1 M) ((extSys N₀ f' hf').1 M) :=
  vertexMap_adj _ _ _ (hadj _ (Level.inf_le_right M N₀))

lemma extSys_mem_stab {N₀ : Level b₀ b₁} {f : ∀ N : Level b₀ b₁, BSVertex (levelEquiv N)}
    {hf : ∀ N N' (h : N ≤ N'), N' ≤ N₀ → vertexMap h (f N) = f N'} {g : loopGroup b₀ b₁}
    (hg : ∀ N, N ≤ N₀ → proj N g • f N = f N) : g ∈ TreeTower.stab (extSys N₀ f hf) := by
  refine TreeTower.mem_stab.2 fun M ↦ ?_
  have := vertexMap_smul (Level.inf_le_left M N₀) (proj (Level.inf M N₀) g) (f (Level.inf M N₀))
  rw [hg _ (Level.inf_le_right M N₀), levelMap_proj] at this
  exact this.symm

/-- The kind of a system of the loop tower is the same at all levels. -/
lemma kind_sys [IsTopologicalGroup Pv] (s : (tower b₀ b₁).Sys) (M M' : Level b₀ b₁) :
    (tower b₀ b₁).kind M (s.1 M) = (tower b₀ b₁).kind M' (s.1 M') := by
  rw [← s.2 (homOfLE (Level.inf_le_left M M')), ← s.2 (homOfLE (Level.inf_le_right M M')),
    preservesKind_tower, preservesKind_tower]

/-! ### The bounded case -/

/-- **The bounded case of estrangement of systems** for the loop tower: if the branch images are
closed and estranged ([SemiAnbd] Def 2.4(iv)), a nontrivial element fixing two systems at bounded
distance keeps them at distance `≤ 2` at every level. -/
theorem dist_le_two_of_bounded [CompactSpace Pv] [IsTopologicalGroup Pv]
    (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1)
    (hcl : ∀ X, IsClosed ((br b₀ b₁ X).range : Set Pv))
    (hEst : ∀ (X Y : Bool) (q : Pv), (X ≠ Y ∨ q ∉ (br b₀ b₁ X).range) →
      (br b₀ b₁ X).range ⊓ (ConjAct.toConjAct q • (br b₀ b₁ Y).range) = ⊥)
    {g : loopGroup b₀ b₁} (hg : g ≠ 1) {s s' : (tower b₀ b₁).Sys}
    (hs : g ∈ TreeTower.stab s) (hs' : g ∈ TreeTower.stab s')
    (hbdd : ∃ C, ∀ N, (bassSerreGraph (levelEquiv N)).dist (s.1 N) (s'.1 N) ≤ C) (N : Level b₀ b₁) :
    (bassSerreGraph (levelEquiv N)).dist (s.1 N) (s'.1 N) ≤ 2 := by
  classical
  obtain ⟨C, hC⟩ := hbdd
  obtain ⟨d, hd⟩ : ∃ d : Level b₀ b₁ → ℕ,
      ∀ N, d N = (bassSerreGraph (levelEquiv N)).dist (s.1 N) (s'.1 N) := ⟨_, fun _ ↦ rfl⟩
  have hmono : ∀ N N' (_ : N ≤ N'), d N' ≤ d N := fun N N' h ↦ by
    rw [hd, hd, ← s.2 (homOfLE h), ← s'.2 (homOfLE h)]
    exact (tower b₀ b₁).dist_map_le (homOfLE h) _ _
  -- the maximal distance `D`, attained at `N₀`
  have hC' : ∀ N, d N ≤ C := fun N ↦ (hd N).symm ▸ hC N
  obtain ⟨D, hD, N₀, hN₀⟩ : ∃ D, (∀ N, d N ≤ D) ∧ ∃ N₀, d N₀ = D :=
    ⟨Nat.findGreatest (fun m ↦ ∃ N, d N = m) C, fun N ↦ Nat.le_findGreatest (hC' N) ⟨N, rfl⟩,
      Nat.findGreatest_spec (P := fun m ↦ ∃ N, d N = m) (hC' Level.top) ⟨Level.top, rfl⟩⟩
  have hconst : ∀ N, N ≤ N₀ → d N = D := fun N h ↦ le_antisymm (hD N) (hN₀ ▸ hmono N N₀ h)
  by_contra hN
  have hD3 : 3 ≤ D := by have := hD N; rw [hd] at this; omega
  -- the geodesic points, compatible below `N₀`
  let pt : ℕ → ∀ N : Level b₀ b₁, BSVertex (levelEquiv N) := fun i N ↦
    geoPt (bassSerreGraph (levelEquiv N)) (s.1 N) (s'.1 N) i
  have hdist : ∀ N, N ≤ N₀ → (bassSerreGraph (levelEquiv N)).dist (s.1 N) (s'.1 N) = D :=
    fun N hN ↦ (hd N).symm.trans (hconst N hN)
  have hpt : ∀ i, i ≤ D → ∀ N N' (h : N ≤ N'), N' ≤ N₀ → vertexMap h (pt i N) = pt i N' := by
    intro i hi N N' h hN'
    have e1 : vertexMap h (s.1 N) = s.1 N' := s.2 (homOfLE h)
    have e2 : vertexMap h (s'.1 N) = s'.1 N' := s'.2 (homOfLE h)
    have hmap := (tower b₀ b₁).map_geoPt (homOfLE h) (x := s.1 N) (y := s'.1 N) (i := i)
      (by
        change (bassSerreGraph (levelEquiv N')).dist (vertexMap h (s.1 N))
          (vertexMap h (s'.1 N)) = (bassSerreGraph (levelEquiv N)).dist (s.1 N) (s'.1 N)
        rw [e1, e2, hdist N' hN', hdist N (le_trans h hN')])
      (by
        change i ≤ (bassSerreGraph (levelEquiv N)).dist (s.1 N) (s'.1 N)
        rw [hdist N (le_trans h hN')]; exact hi)
    change vertexMap h _ = geoPt _ (vertexMap h (s.1 N)) (vertexMap h (s'.1 N)) i at hmap
    rw [e1, e2] at hmap
    exact hmap
  have hfix : ∀ i, i ≤ D → ∀ N, N ≤ N₀ → proj N g • pt i N = pt i N := fun i hi N hN ↦ by
    have h := geoPt_spec isTree_bassSerreGraph.connected (G := bassSerreGraph (levelEquiv N))
      (x := s.1 N) (y := s'.1 N) (i := i) (by rw [hdist N hN]; exact hi)
    have h' := hdist N hN
    exact smul_eq_of_mem_geodesic isTree_bassSerreGraph bassSerreGraph_adj_smul
      (TreeTower.mem_stab.1 hs N) (TreeTower.mem_stab.1 hs' N) (by simp only [pt]; omega)
  have hadj : ∀ i, i + 1 ≤ D → ∀ N, N ≤ N₀ →
      (bassSerreGraph (levelEquiv N)).Adj (pt i N) (pt (i + 1) N) := fun i hi N hN ↦
    adj_geoPt isTree_bassSerreGraph (by rw [hdist N hN]; exact hi)
  -- a vertex point with two distinct fixed edge points on the geodesic gives a contradiction
  have key : ∀ j, j + 2 ≤ D → (tower b₀ b₁).kind N₀ (pt (j + 1) N₀) = true → False := by
    intro j hj hk
    let P := extSys N₀ (pt (j + 1)) (hpt (j + 1) (by omega))
    let E1 := extSys N₀ (pt j) (hpt j (by omega))
    let E2 := extSys N₀ (pt (j + 2)) (hpt (j + 2) hj)
    have hP : TreeTower.IsVert P := fun M ↦ by
      rw [kind_sys P M N₀, show P.1 N₀ = pt (j + 1) N₀ from extSys_apply le_rfl]
      exact hk
    have hadj1 : ∀ M, (bassSerreGraph (levelEquiv M)).Adj (P.1 M) (E1.1 M) :=
      extSys_adj fun N hN ↦ (hadj j (by omega) N hN).symm
    have hadj2 : ∀ M, (bassSerreGraph (levelEquiv M)).Adj (P.1 M) (E2.1 M) :=
      extSys_adj fun N hN ↦ hadj (j + 1) hj N hN
    have hne : E1 ≠ E2 := fun h ↦ by
      have h1 := congrArg (fun c : (tower b₀ b₁).Sys ↦ c.1 N₀) h
      simp only [E1, E2] at h1
      rw [extSys_apply le_rfl, extSys_apply le_rfl] at h1
      exact geoPt_ne isTree_bassSerreGraph.connected (by rw [hdist N₀ le_rfl]; omega)
        (by rw [hdist N₀ le_rfl]; omega) (by omega : j ≠ j + 2) h1
    have hgP : g ∈ TreeTower.stab P := extSys_mem_stab fun N hN ↦ hfix _ (by omega) N hN
    have hg1 : g ∈ TreeTower.stab E1 := extSys_mem_stab fun N hN ↦ hfix _ (by omega) N hN
    have hg2 : g ∈ TreeTower.stab E2 := extSys_mem_stab fun N hN ↦ hfix _ hj N hN
    obtain ⟨y, hy⟩ := exists_smul_baseSys P hP
    have hbase : baseSys b₀ b₁ = y⁻¹ • P := by rw [← hy, inv_smul_smul]
    have hg' : y⁻¹ * g * y ∈ TreeTower.stab (baseSys b₀ b₁) := by
      rw [← hy, TreeTower.mem_stab_smul] at hgP
      exact hgP
    have hmemE : ∀ c : (tower b₀ b₁).Sys, g ∈ TreeTower.stab c →
        y⁻¹ * g * y ∈ TreeTower.stab (y⁻¹ • c) := fun c hc ↦ by
      rw [TreeTower.mem_stab_smul]
      simpa [mul_assoc] using hc
    have hadjE : ∀ c : (tower b₀ b₁).Sys,
        (∀ M, (bassSerreGraph (levelEquiv M)).Adj (P.1 M) (c.1 M)) →
        ∀ M, (bassSerreGraph (levelEquiv M)).Adj ((baseSys b₀ b₁).1 M) ((y⁻¹ • c).1 M) :=
      fun c hc M ↦ by
        rw [hbase, TreeTower.smul_apply, TreeTower.smul_apply]
        exact (bassSerreGraph_adj_smul _ _ _).2 (hc M)
    rw [stab_baseSys_eq_range] at hg'
    obtain ⟨σ, hσ⟩ := hg'
    have hσ1 : σ ≠ 1 := by
      rintro rfl
      rw [map_one] at hσ
      apply hg
      have := congrArg (fun z ↦ y * z * y⁻¹) hσ
      simpa [mul_assoc] using this.symm
    refine false_of_fix_two_edges hsep hcl hEst hσ1 (y⁻¹ • E1) (y⁻¹ • E2) (hadjE E1 hadj1)
      (hadjE E2 hadj2) (fun h ↦ hne (MulAction.injective y⁻¹ h)) (hσ ▸ hmemE E1 hg1)
      (hσ ▸ hmemE E2 hg2)
  by_cases hk1 : (tower b₀ b₁).kind N₀ (pt 1 N₀) = true
  · exact key 0 (by omega) hk1
  · refine key 1 (by omega) ?_
    have := (tower b₀ b₁).kind_adj N₀ _ _ (hadj 1 (by omega) N₀ le_rfl)
    revert hk1 this
    cases (tower b₀ b₁).kind N₀ (pt 1 N₀) <;> cases (tower b₀ b₁).kind N₀ (pt (1 + 1) N₀) <;> simp

end

end LoopTower

end TemperedFundamentalGroups
