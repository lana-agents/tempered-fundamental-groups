/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import TemperedFundamentalGroups.SemiAnbd.LoopTower
import TemperedFundamentalGroups.SemiAnbd.TempSlim
import TemperedFundamentalGroups.SemiAnbd.TreeTowerCompact

/-!
# The verticial subgroup of the loop tower

For the tree tower of a loop of groups (`SemiAnbd/LoopTower.lean`) with vertex group `Π`:

* `LoopTower.vertexIncl`: `Π →* loopGroup b₀ b₁`, `π ↦ (of (π mod N))_N`;
* `LoopTower.baseSys`: the system of base vertices `G ∈ H_N ⧸ G`; its stabilizer contains the
  image of `Π` (`vertexIncl_mem_stab`), with equality when `Π` is compact
  (`stab_baseSys_eq_range`);
* the **topology** of `loopGroup b₀ b₁` (inverse limit of the discrete level groups), a
  topological group (`instIsTopologicalGroup`), Hausdorff;
* **`LoopTower.HI_baseSys`** (bridge B2b, [SemiAnbd] Prop 2.6): if the vertex group is elevated
  relative to the loop at cofinally many levels ([SemiAnbd] Def 2.4(i)), the base system
  satisfies `HI`;
* **`LoopTower.tempSlim_loopGroup`** (bridge B4 + [SemiAnbd] Prop 3.6(iv)/Ex 3.10 argument): for
  compact Hausdorff `Π` whose open normal subgroups separate points through the levels, the loop
  group is temp-slim as soon as `Π` is temp-slim (i.e. slim) and `HI` holds.
-/

open CategoryTheory HNNExtension QuotientGroup Topology
open scoped Pointwise

namespace TemperedFundamentalGroups

namespace LoopTower

noncomputable section

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [Group E] {b₀ b₁ : E →* Pv}

/-! ### The vertex group inside the loop group -/

variable (b₀ b₁) in
/-- The vertex group `Π` maps to the loop group. -/
def vertexIncl : Pv →* loopGroup b₀ b₁ where
  toFun π := ⟨fun N ↦ (of ((π : levelQuot N)) : levelGroup N), fun N N' h ↦ by simp⟩
  map_one' := by ext N; simp
  map_mul' x y := by ext N; simp

@[simp] lemma proj_vertexIncl (N : Level b₀ b₁) (π : Pv) :
    proj N (vertexIncl b₀ b₁ π) = of (π : levelQuot N) := rfl

variable (b₀ b₁) in
/-- The base vertex system: the coset `G` at every level. -/
def baseSys : (tower b₀ b₁).Sys :=
  ⟨fun N ↦ .inl ((1 : levelGroup N) : _ ⧸ vertexSubgroup (levelEquiv N)), fun {N N'} f ↦ by
    change vertexMap f.le (Sum.inl (QuotientGroup.mk 1)) = Sum.inl (QuotientGroup.mk 1)
    rw [vertexMap_inl, map_one]⟩

lemma mem_stab_baseSys {x : loopGroup b₀ b₁} :
    x ∈ TreeTower.stab (baseSys b₀ b₁) ↔ ∀ N, proj N x ∈ vertexSubgroup (levelEquiv N) := by
  rw [TreeTower.mem_stab]
  refine forall_congr' fun N ↦ ?_
  change proj N x • (Sum.inl ((1 : levelGroup N) : _ ⧸ vertexSubgroup (levelEquiv N)) :
    BSVertex (levelEquiv N)) = Sum.inl _ ↔ _
  rw [Sum.smul_inl, Sum.inl.injEq, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  simp

lemma vertexIncl_mem_stab (π : Pv) : vertexIncl b₀ b₁ π ∈ TreeTower.stab (baseSys b₀ b₁) :=
  mem_stab_baseSys.2 fun _ ↦ ⟨_, rfl⟩

/-! ### Topology -/

variable (b₀ b₁) in
/-- The inverse limit topology on the loop group (each level group discrete). -/
instance instTopologicalSpace : TopologicalSpace (loopGroup b₀ b₁) :=
  ⨅ N : Level b₀ b₁, TopologicalSpace.induced (proj N) ⊥

lemma isOpen_proj_fiber (N : Level b₀ b₁) (g : levelGroup N) :
    IsOpen {x : loopGroup b₀ b₁ | proj N x = g} := by
  have h : IsOpen[TopologicalSpace.induced (proj N) ⊥] {x : loopGroup b₀ b₁ | proj N x = g} :=
    ⟨{g}, trivial, rfl⟩
  exact (TopologicalSpace.le_def.1 (iInf_le (fun N : Level b₀ b₁ ↦
    TopologicalSpace.induced (proj N) (⊥ : TopologicalSpace (levelGroup N))) N)) _ h

lemma continuous_of_proj {X : Type*} [TopologicalSpace X] (f : X → loopGroup b₀ b₁)
    (hf : ∀ N g, IsOpen {x | proj N (f x) = g}) : Continuous f := by
  refine continuous_iInf_rng.2 fun N ↦ continuous_induced_rng.2 ?_
  letI : TopologicalSpace (levelGroup N) := ⊥
  haveI : DiscreteTopology (levelGroup N) := ⟨rfl⟩
  exact continuous_discrete_rng.2 fun g ↦ hf N g

instance instIsTopologicalGroup : IsTopologicalGroup (loopGroup b₀ b₁) where
  continuous_mul := continuous_of_proj _ fun N g ↦ by
    have : {p : loopGroup b₀ b₁ × loopGroup b₀ b₁ | proj N (p.1 * p.2) = g} =
        ⋃ a : levelGroup N, ({p | proj N p.1 = a} ∩ {p | proj N p.2 = a⁻¹ * g}) := by
      ext p
      simp only [map_mul, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      exact ⟨fun h ↦ ⟨proj N p.1, rfl, by rw [← h, inv_mul_cancel_left]⟩,
        fun ⟨a, h1, h2⟩ ↦ by rw [h1, h2, mul_inv_cancel_left]⟩
    rw [this]
    exact isOpen_iUnion fun a ↦ ((isOpen_proj_fiber N a).preimage continuous_fst).inter
      ((isOpen_proj_fiber N _).preimage continuous_snd)
  continuous_inv := continuous_of_proj _ fun N g ↦ by
    have : {x : loopGroup b₀ b₁ | proj N x⁻¹ = g} = {x | proj N x = g⁻¹} := by
      ext x; simp [inv_eq_iff_eq_inv]
    rw [this]
    exact isOpen_proj_fiber N _

instance instT2Space : T2Space (loopGroup b₀ b₁) := by
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, proj N x ≠ proj N y := by
    by_contra! h
    exact hxy (Subtype.ext (funext h))
  exact ⟨_, _, isOpen_proj_fiber N (proj N x), isOpen_proj_fiber N (proj N y), rfl, rfl,
    Set.disjoint_left.2 fun z hz hz' ↦ hN (hz.symm.trans hz')⟩

lemma continuous_vertexIncl [IsTopologicalGroup Pv] : Continuous (vertexIncl b₀ b₁) :=
  continuous_of_proj _ fun N g ↦ by
    by_cases hg : ∃ q : levelQuot N, of q = g
    · obtain ⟨q, rfl⟩ := hg
      induction q using QuotientGroup.induction_on with
      | H π =>
      have : {x : Pv | proj N (vertexIncl b₀ b₁ x) = of (π : levelQuot N)} =
          (π • (N.1 : Set Pv)) := by
        ext x
        simp only [proj_vertexIncl, Set.mem_setOf_eq, (of_injective _).eq_iff, QuotientGroup.eq,
          mem_leftCoset_iff]
        exact ⟨fun h ↦ by simpa using inv_mem h, fun h ↦ by simpa using inv_mem h⟩
      rw [this]
      exact N.2.2.1.smul π
    · convert isOpen_empty
      ext x
      simp only [proj_vertexIncl, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h ↦ hg ⟨_, h⟩

/-! ### The stabilizer of the base system -/

/-- For compact `Π`, the stabilizer of the base system is the image of `Π` (Cantor's
intersection theorem over the directed set of levels). -/
theorem stab_baseSys_eq_range [CompactSpace Pv] [IsTopologicalGroup Pv] :
    TreeTower.stab (baseSys b₀ b₁) = (vertexIncl b₀ b₁).range := by
  refine le_antisymm (fun x hx ↦ ?_) (by rintro _ ⟨π, rfl⟩; exact vertexIncl_mem_stab π)
  rw [mem_stab_baseSys] at hx
  choose q hq using hx
  let F : Level b₀ b₁ → Set Pv := fun N ↦ {π | (π : levelQuot N) = q N}
  have hFcl : ∀ N, IsClosed (F N) := fun N ↦ by
    induction hqN : q N using QuotientGroup.induction_on with
    | H π₀ =>
    have : F N = π₀ • (N.1 : Set Pv) := by
      ext π
      simp only [F, Set.mem_setOf_eq, hqN, mem_leftCoset_iff, QuotientGroup.eq]
      exact ⟨fun h ↦ by simpa using inv_mem h, fun h ↦ by simpa using inv_mem h⟩
    rw [this]
    exact (N.1.isClosed_of_isOpen N.2.2.1).smul π₀
  haveI : Nonempty (Level b₀ b₁) := ⟨Level.top⟩
  obtain ⟨π, hπ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed F
    (fun N N' ↦ ⟨Level.inf N N', fun π hπ ↦ by
        simp only [F, Set.mem_setOf_eq] at hπ ⊢
        have h1 := congrArg (quotMap (Level.inf_le_left N N')) hπ
        rw [quotMap_mk] at h1
        rw [h1]
        apply of_injective
        rw [← levelMap_of, hq, hq, levelMap_proj],
      fun π hπ ↦ by
        simp only [F, Set.mem_setOf_eq] at hπ ⊢
        have h1 := congrArg (quotMap (Level.inf_le_right N N')) hπ
        rw [quotMap_mk] at h1
        rw [h1]
        apply of_injective
        rw [← levelMap_of, hq, hq, levelMap_proj]⟩)
    (fun N ↦ QuotientGroup.mk_surjective (q N)) (fun N ↦ (hFcl N).isCompact) hFcl
  refine ⟨π, Subtype.ext (funext fun N ↦ ?_)⟩
  have := Set.mem_iInter.1 hπ N
  simp only [F, Set.mem_setOf_eq] at this
  change of (π : levelQuot N) = proj N x
  rw [this, hq]

/-- If the levels separate the points of `Π`, the vertex inclusion is injective. -/
lemma vertexIncl_injective (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1) :
    Function.Injective (vertexIncl b₀ b₁) := by
  rw [injective_iff_map_eq_one]
  intro π hπ
  by_contra hne
  obtain ⟨N, hN⟩ := hsep π hne
  have := congrArg (proj N) hπ
  rw [proj_vertexIncl, map_one, ← of.map_one, (of_injective _).eq_iff,
    QuotientGroup.eq_one_iff] at this
  exact hN this

/-- For compact Hausdorff `Π` whose points are separated by the levels, `Π` is isomorphic, as a
topological group, to the verticial subgroup of the base system. -/
def vertexEquiv [CompactSpace Pv] [IsTopologicalGroup Pv]
    (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1) :
    Pv ≃ₜ* TreeTower.stab (baseSys b₀ b₁) := by
  let f : Pv →* TreeTower.stab (baseSys b₀ b₁) :=
    (vertexIncl b₀ b₁).codRestrict _ vertexIncl_mem_stab
  have hbij : Function.Bijective f := by
    refine ⟨fun x y h ↦ vertexIncl_injective hsep (congrArg Subtype.val h), fun x ↦ ?_⟩
    have hx : (x : loopGroup b₀ b₁) ∈ (vertexIncl b₀ b₁).range := by
      rw [← stab_baseSys_eq_range]; exact x.2
    obtain ⟨π, hπ⟩ := hx
    exact ⟨π, Subtype.ext hπ⟩
  have hf : Continuous f := continuous_vertexIncl.subtype_mk _
  exact
    { toMulEquiv := MulEquiv.ofBijective f hbij
      continuous_toFun := hf
      continuous_invFun :=
        (hf.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f hbij)).symm.continuous }

lemma isCompact_stab_baseSys [CompactSpace Pv] [IsTopologicalGroup Pv] :
    IsCompact (TreeTower.stab (baseSys b₀ b₁) : Set (loopGroup b₀ b₁)) := by
  rw [stab_baseSys_eq_range, MonoidHom.coe_range]
  exact isCompact_range continuous_vertexIncl

/-! ### `HI` from elevatedness (bridge B2b) -/

lemma stabilizer_inr (N : Level b₀ b₁) (k : levelGroup N) (g : levelGroup N) :
    g ∈ MulAction.stabilizer (levelGroup N)
        (Sum.inr (k : _ ⧸ edgeSubgroup (levelEquiv N)) : BSVertex (levelEquiv N)) ↔
      k⁻¹ * g * k ∈ edgeSubgroup (levelEquiv N) := by
  rw [MulAction.mem_stabilizer_iff, Sum.smul_inr, Sum.inr.injEq, MulAction.Quotient.smul_mk,
    QuotientGroup.eq, ← inv_mem_iff]
  simp [mul_assoc]

/-- The level form of [SemiAnbd] Def 2.4(i) at a level `N`, for the loop: a subgroup `H ⊆ Q_N`
meeting all conjugates of both branch images trivially. -/
def ElevatedAt (N : Level b₀ b₁) (H : Subgroup (levelQuot N)) : Prop :=
  ∀ q : levelQuot N, H ⊓ (ConjAct.toConjAct q • (branch₀ N).range) = ⊥ ∧
    H ⊓ (ConjAct.toConjAct q • (branch₁ N).range) = ⊥

/-- At a level where `H` is elevated, the stabilizers of the neighbours of the base vertex have
index at least `|H|` in the verticial subgroup. -/
lemma card_le_relIndex (N : Level b₀ b₁) (H : Subgroup (levelQuot N)) (hH : ElevatedAt N H)
    (w : BSVertex (levelEquiv N))
    (hw : (bassSerreGraph (levelEquiv N)).Adj ((baseSys b₀ b₁).1 N) w)
    (h0 : ((tower b₀ b₁).fixAt N w).relIndex (TreeTower.stab (baseSys b₀ b₁)) ≠ 0) :
    Nat.card H ≤ ((tower b₀ b₁).fixAt N w).relIndex (TreeTower.stab (baseSys b₀ b₁)) := by
  change ((MulAction.stabilizer (levelGroup N) w).comap (proj N)).relIndex _ ≠ 0 at h0
  change _ ≤ ((MulAction.stabilizer (levelGroup N) w).comap (proj N)).relIndex _
  rw [Subgroup.relIndex_comap] at h0 ⊢
  -- `of(H)` lies in the image of the verticial subgroup and meets the stabilizer of `w` trivially
  have hle : H.map (of : levelQuot N →* levelGroup N) ≤
      (TreeTower.stab (baseSys b₀ b₁)).map (proj N) := by
    rintro _ ⟨q, -, rfl⟩
    induction q using QuotientGroup.induction_on with
    | H π => exact ⟨vertexIncl b₀ b₁ π, vertexIncl_mem_stab π, rfl⟩
  have hinf : H.map (of : levelQuot N →* levelGroup N) ⊓
      MulAction.stabilizer (levelGroup N) w = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨⟨h, hhH, rfl⟩, hst⟩
    rw [Subgroup.mem_bot, ← of.map_one, (of_injective _).eq_iff]
    rcases w with w | w
    · exact absurd hw (not_adj_inl_inl _ _)
    induction w using QuotientGroup.induction_on with
    | H k =>
    rw [SimpleGraph.adj_comm, adj_inr_iff] at hw
    replace hst := (stabilizer_inr N k (of h)).1 hst
    rcases hw with hw | hw
    · obtain ⟨y, hy⟩ := mk_vertex_eq_iff.1 (Sum.inl_injective hw)
      rw [one_mul] at hy
      subst hy
      rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem (of_injective _)] at hst
      have hmem : h ∈ H ⊓ (ConjAct.toConjAct y • (branch₁ N).range) := by
        refine ⟨hhH, Subgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_⟩
        simpa [ConjAct.smul_def, mul_assoc] using hst
      rwa [(hH y).2, Subgroup.mem_bot] at hmem
    · obtain ⟨y, hy⟩ := mk_vertex_eq_iff.1 (Sum.inl_injective hw)
      rw [one_mul] at hy
      have hk : k = of y * t⁻¹ := by rw [← hy, mul_inv_cancel_right]
      subst hk
      obtain ⟨b, hb, hbe⟩ := hst
      have hA : y⁻¹ * h * y ∈ (branch₀ N).range := by
        have h1 : (of (y⁻¹ * h * y) : levelGroup N) = t⁻¹ * of b * t := by
          rw [hbe]; simp [mul_assoc]
        rw [← equiv_symm_eq_conj (b := ⟨b, hb⟩), (of_injective _).eq_iff] at h1
        rw [h1]
        exact (levelEquiv N).symm ⟨b, hb⟩ |>.2
      have hmem : h ∈ H ⊓ (ConjAct.toConjAct y • (branch₀ N).range) := by
        refine ⟨hhH, Subgroup.mem_pointwise_smul_iff_inv_smul_mem.2 ?_⟩
        simpa [ConjAct.smul_def, mul_assoc] using hA
      rwa [(hH y).1, Subgroup.mem_bot] at hmem
  have h1 : (MulAction.stabilizer (levelGroup N) w).relIndex
      (H.map (of : levelQuot N →* levelGroup N)) = Nat.card H := by
    rw [← Subgroup.inf_relIndex_right, inf_comm, hinf, Subgroup.relIndex_bot_left,
      Subgroup.card_map_of_injective (of_injective _)]
  rw [← h1]
  exact Subgroup.relIndex_le_of_le_right hle h0

/-- **Bridge B2b**: if every `n` is exceeded by the order of an elevated subgroup at some
level, the base system satisfies `HI`. -/
theorem HI_baseSys (hel : ∀ n : ℕ, ∃ (N : Level b₀ b₁) (H : Subgroup (levelQuot N)),
    n < Nat.card H ∧ ElevatedAt N H) :
    (tower b₀ b₁).HI (baseSys b₀ b₁) := by
  intro n j
  obtain ⟨a, H, hn, hH⟩ := hel n
  refine ⟨Level.inf a j, homOfLE (Level.inf_le_right a j), fun w hw ↦ ?_⟩
  have hka : Level.inf a j ≤ a := Level.inf_le_left a j
  set w' := vertexMap hka w
  have hw' : (bassSerreGraph (levelEquiv a)).Adj ((baseSys b₀ b₁).1 a) w' := by
    have := vertexMap_adj hka _ _ hw
    rwa [show vertexMap hka ((baseSys b₀ b₁).1 (Level.inf a j)) = (baseSys b₀ b₁).1 a from
      (baseSys b₀ b₁).2 (homOfLE hka)] at this
  have hle : (tower b₀ b₁).fixAt (Level.inf a j) w ≤ (tower b₀ b₁).fixAt a w' := by
    intro g hg
    rw [TreeTower.mem_fixAt] at hg ⊢
    change proj a g • vertexMap hka w = vertexMap hka w
    rw [← levelMap_proj hka, ← vertexMap_smul]
    exact congrArg _ hg
  by_cases h0 : ((tower b₀ b₁).fixAt (Level.inf a j) w).relIndex
      (TreeTower.stab (baseSys b₀ b₁)) = 0
  · exact .inl h0
  refine .inr (lt_of_lt_of_le hn ((card_le_relIndex a H hH w' hw'
    (fun h ↦ h0 (Subgroup.relIndex_eq_zero_of_le_left hle h))).trans
    (Subgroup.relIndex_le_of_le_left hle h0)))

/-- **Temp-slimness of the loop group** ([SemiAnbd] Prop 3.6(iv), the argument of Ex 3.10, for a
loop of groups): for compact `Π` separated by the levels, temp-slim (= slim) `Π` and `HI` of the
base system give a temp-slim loop group. -/
theorem tempSlim_loopGroup [CompactSpace Pv] [IsTopologicalGroup Pv]
    (hsep : ∀ π : Pv, π ≠ 1 → ∃ N : Level b₀ b₁, π ∉ N.1)
    (hHI : (tower b₀ b₁).HI (baseSys b₀ b₁)) (hslim : TempSlim Pv) :
    TempSlim (loopGroup b₀ b₁) :=
  TreeTower.tempSlim_of_HI hHI isCompact_stab_baseSys
    (hslim.of_continuousMulEquiv (vertexEquiv hsep))

end

end LoopTower

end TemperedFundamentalGroups
