/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Topology.Algebra.Group.Basic
import TemperedFundamentalGroups.SemiAnbd.HNNTree
import TemperedFundamentalGroups.SemiAnbd.TreeTower

/-!
# The tree tower of a semi-graph of groups with one vertex and one loop

Let `Π` be a topological group (the vertex group) and `b₀ b₁ : E →* Π` the two branch
homomorphisms of a loop with edge group `E` (for the stable `1`-gon `G^Σ`: `Π = Π^Σ_{0,3}`,
`E = ℤ^Σ`, `b₀`, `b₁` the inertia maps of `c₀` and `c₁⁻¹`, `SemiAnbd/OneGonSigma.lean`).
A **level** is an open normal subgroup `N ⊴ Π` with `b₀⁻¹ N = b₁⁻¹ N`; levels are closed under
intersection. At a level `N` the branch images `A_N = b₀(E) N / N` and `B_N = b₁(E) N / N` of the
finite (if `Π` is compact) group `Q_N = Π ⧸ N` are identified by `φ_N : b₀(x) ↦ b₁(x)`, and the
**level group** is the HNN extension `H_N = Q_N *_{φ_N}` (the Galois group of the universal
combinatorial covering of the finite covering of the loop of groups determined by `N`,
[SemiAnbd] §3; decision (c) of `MR12-tfg-plan.md`). The level groups form an inverse system,
whose limit `loopGroup b₀ b₁` is the **tempered fundamental group of the loop of groups**; it acts
on the Bass–Serre trees of the `H_N` (`SemiAnbd/HNNTree.lean`), which form a `TreeTower`.

## Main definitions and results

* `LoopTower.Level b₀ b₁`: the levels, a directed (downwards) set; `Level.inf`.
* `LoopTower.levelGroup N`: the HNN extension `H_N`; `LoopTower.levelMap`: the transition maps,
  functorial (`levelMap_comp`, `levelMap_id`).
* `LoopTower.loopGroup b₀ b₁`: the inverse limit, as a subgroup of `∀ N, H_N`.
* **`LoopTower.tower b₀ b₁`**: the tree tower, functorial (`isFunctorial_tower`).
-/

open CategoryTheory HNNExtension QuotientGroup

namespace TemperedFundamentalGroups

namespace LoopTower

noncomputable section

universe u

/-- The map of left coset spaces induced by a homomorphism. -/
def cosetMap {H H' : Type*} [Group H] [Group H'] (f : H →* H') {S : Subgroup H}
    {S' : Subgroup H'} (hS : S ≤ S'.comap f) : H ⧸ S → H' ⧸ S' :=
  Quotient.map' f fun a b hab ↦ by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [← map_inv, ← map_mul]
    exact hS hab

@[simp] lemma cosetMap_mk {H H' : Type*} [Group H] [Group H'] (f : H →* H') {S : Subgroup H}
    {S' : Subgroup H'} (hS : S ≤ S'.comap f) (k : H) :
    cosetMap f hS (k : H ⧸ S) = (f k : H' ⧸ S') := rfl

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [Group E] (b₀ b₁ : E →* Pv)

/-- A **level**: an open normal subgroup on which the two branches have the same preimage. -/
def Level : Type u :=
  {N : Subgroup Pv // N.Normal ∧ IsOpen (N : Set Pv) ∧ N.comap b₀ = N.comap b₁}

variable {b₀ b₁}

instance : PartialOrder (Level b₀ b₁) := Subtype.partialOrder _

namespace Level

instance (N : Level b₀ b₁) : N.1.Normal := N.2.1

lemma comap_eq (N : Level b₀ b₁) : N.1.comap b₀ = N.1.comap b₁ := N.2.2.2

/-- The intersection of two levels is a level. -/
def inf (N N' : Level b₀ b₁) : Level b₀ b₁ :=
  ⟨N.1 ⊓ N'.1, Subgroup.normal_inf_normal _ _, N.2.2.1.inter N'.2.2.1, by
    rw [Subgroup.comap_inf, Subgroup.comap_inf, N.comap_eq, N'.comap_eq]⟩

lemma inf_le_left (N N' : Level b₀ b₁) : inf N N' ≤ N := fun _ h ↦ h.1

lemma inf_le_right (N N' : Level b₀ b₁) : inf N N' ≤ N' := fun _ h ↦ h.2

variable [IsTopologicalGroup Pv] in
/-- The whole group is a level. -/
def top : Level b₀ b₁ := ⟨⊤, Subgroup.normal_top, isOpen_univ, by simp⟩

end Level

/-- The quotient `Q_N = Π ⧸ N`. -/
abbrev levelQuot (N : Level b₀ b₁) : Type u := Pv ⧸ N.1

/-- The branch maps to the quotient. -/
def branch₀ (N : Level b₀ b₁) : E →* levelQuot N := (QuotientGroup.mk' N.1).comp b₀

/-- The branch maps to the quotient. -/
def branch₁ (N : Level b₀ b₁) : E →* levelQuot N := (QuotientGroup.mk' N.1).comp b₁

lemma ker_branch₀ (N : Level b₀ b₁) : (branch₀ N).ker = N.1.comap b₀ := by
  rw [branch₀, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

lemma ker_branch₁ (N : Level b₀ b₁) : (branch₁ N).ker = N.1.comap b₁ := by
  rw [branch₁, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

/-- The identification `φ_N : A_N ≃* B_N`, `b₀(x) ↦ b₁(x)`. -/
def levelEquiv (N : Level b₀ b₁) : (branch₀ N).range ≃* (branch₁ N).range :=
  (QuotientGroup.quotientKerEquivRange (branch₀ N)).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (by rw [ker_branch₀, ker_branch₁, N.comap_eq])).trans
      (QuotientGroup.quotientKerEquivRange (branch₁ N)))

lemma levelEquiv_apply (N : Level b₀ b₁) (x : E) :
    ((levelEquiv N ⟨branch₀ N x, x, rfl⟩ : (branch₁ N).range) : levelQuot N) = branch₁ N x := by
  have h : (QuotientGroup.quotientKerEquivRange (branch₀ N)).symm ⟨branch₀ N x, x, rfl⟩ =
      (x : E ⧸ (branch₀ N).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [levelEquiv, MulEquiv.trans_apply, h, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- **The level group** `H_N`: the HNN extension of `Q_N` along `φ_N`. -/
abbrev levelGroup (N : Level b₀ b₁) : Type u :=
  HNNExtension (levelQuot N) (branch₀ N).range (branch₁ N).range (levelEquiv N)

/-- The transition map of quotients for `N ≤ N'`. -/
def quotMap {N N' : Level b₀ b₁} (h : N ≤ N') : levelQuot N →* levelQuot N' :=
  QuotientGroup.map _ _ (MonoidHom.id Pv) h

@[simp] lemma quotMap_mk {N N' : Level b₀ b₁} (h : N ≤ N') (x : Pv) :
    quotMap h (x : levelQuot N) = (x : levelQuot N') := rfl

lemma quotMap_branch₀ {N N' : Level b₀ b₁} (h : N ≤ N') (x : E) :
    quotMap h (branch₀ N x) = branch₀ N' x := rfl

lemma quotMap_branch₁ {N N' : Level b₀ b₁} (h : N ≤ N') (x : E) :
    quotMap h (branch₁ N x) = branch₁ N' x := rfl

/-- The transition map of level groups for `N ≤ N'`. -/
def levelMap {N N' : Level b₀ b₁} (h : N ≤ N') : levelGroup N →* levelGroup N' :=
  HNNExtension.lift ((HNNExtension.of : levelQuot N' →* levelGroup N').comp (quotMap h)) t
    (by
      rintro ⟨_, x, rfl⟩
      simp only [MonoidHom.comp_apply, quotMap_branch₀]
      rw [show (branch₀ N' x) = ((⟨branch₀ N' x, x, rfl⟩ : (branch₀ N').range) : levelQuot N')
        from rfl, t_mul_of, levelEquiv_apply, levelEquiv_apply, quotMap_branch₁])

@[simp] lemma levelMap_of {N N' : Level b₀ b₁} (h : N ≤ N') (q : levelQuot N) :
    levelMap h (of q) = of (quotMap h q) := by
  simp [levelMap]

@[simp] lemma levelMap_t {N N' : Level b₀ b₁} (h : N ≤ N') :
    levelMap h (t : levelGroup N) = t := by
  simp [levelMap]

lemma levelMap_comp {N N' N'' : Level b₀ b₁} (h : N ≤ N') (h' : N' ≤ N'') :
    (levelMap h').comp (levelMap h) = levelMap (h.trans h') := by
  refine HNNExtension.hom_ext ?_ (by simp)
  ext x
  simp

lemma levelMap_apply_apply {N N' N'' : Level b₀ b₁} (h : N ≤ N') (h' : N' ≤ N'')
    (x : levelGroup N) : levelMap h' (levelMap h x) = levelMap (h.trans h') x :=
  DFunLike.congr_fun (levelMap_comp h h') x

lemma levelMap_id (N : Level b₀ b₁) : levelMap (le_refl N) = MonoidHom.id _ := by
  refine HNNExtension.hom_ext ?_ (by simp)
  ext x
  simp

variable (b₀ b₁) in
/-- **The tempered fundamental group of the loop of groups**: the inverse limit of the level
groups, as the subgroup of compatible families. -/
def loopGroup : Subgroup (∀ N : Level b₀ b₁, levelGroup N) where
  carrier := {x | ∀ N N' (h : N ≤ N'), levelMap h (x N) = x N'}
  mul_mem' hx hy N N' h := by simp [hx N N' h, hy N N' h]
  one_mem' N N' h := by simp
  inv_mem' hx N N' h := by simp [hx N N' h]

/-- The projection of the loop group to a level. -/
def proj (N : Level b₀ b₁) : loopGroup b₀ b₁ →* levelGroup N :=
  (Pi.evalMonoidHom (fun N ↦ levelGroup N) N).comp (loopGroup b₀ b₁).subtype

@[simp] lemma levelMap_proj {N N' : Level b₀ b₁} (h : N ≤ N') (x : loopGroup b₀ b₁) :
    levelMap h (proj N x) = proj N' x :=
  x.2 N N' h

/-! ### The tree tower -/

/-- The map of Bass–Serre vertices induced by a transition map. -/
def vertexMap {N N' : Level b₀ b₁} (h : N ≤ N') :
    BSVertex (levelEquiv N) → BSVertex (levelEquiv N') :=
  Sum.map
    (cosetMap (levelMap h) (by
      rintro _ ⟨q, rfl⟩
      exact ⟨quotMap h q, (levelMap_of h q).symm⟩))
    (cosetMap (levelMap h) (by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨branch₁ N' x, ⟨x, rfl⟩, by simp [quotMap_branch₁]⟩))

@[simp] lemma vertexMap_inl {N N' : Level b₀ b₁} (h : N ≤ N') (k : levelGroup N) :
    vertexMap h (.inl (k : levelGroup N ⧸ vertexSubgroup (levelEquiv N))) =
      .inl ((levelMap h k : levelGroup N') : _ ⧸ vertexSubgroup (levelEquiv N')) := rfl

@[simp] lemma vertexMap_inr {N N' : Level b₀ b₁} (h : N ≤ N') (k : levelGroup N) :
    vertexMap h (.inr (k : levelGroup N ⧸ edgeSubgroup (levelEquiv N))) =
      .inr ((levelMap h k : levelGroup N') : _ ⧸ edgeSubgroup (levelEquiv N')) := rfl

lemma vertexMap_smul {N N' : Level b₀ b₁} (h : N ≤ N') (g : levelGroup N)
    (x : BSVertex (levelEquiv N)) : vertexMap h (g • x) = levelMap h g • vertexMap h x := by
  rcases x with x | x <;> induction x using QuotientGroup.induction_on with
  | H k => simp [Sum.smul_inl, Sum.smul_inr, MulAction.Quotient.smul_mk]

lemma vertexMap_adj {N N' : Level b₀ b₁} (h : N ≤ N') (x y : BSVertex (levelEquiv N))
    (hxy : (bassSerreGraph (levelEquiv N)).Adj x y) :
    (bassSerreGraph (levelEquiv N')).Adj (vertexMap h x) (vertexMap h y) := by
  wlog hx : x.isRight generalizing x y
  · rcases x with x | x
    · rcases y with y | y
      · exact absurd hxy (not_adj_inl_inl _ _)
      · exact (this _ _ hxy.symm rfl).symm
    · exact absurd rfl hx
  rcases x with x | x
  · exact absurd hx (by simp)
  induction x using QuotientGroup.induction_on with
  | H k =>
  rw [adj_inr_iff] at hxy
  rw [vertexMap_inr, adj_inr_iff]
  rcases hxy with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by simp)

lemma vertexMap_comp {N N' N'' : Level b₀ b₁} (h : N ≤ N') (h' : N' ≤ N'')
    (x : BSVertex (levelEquiv N)) : vertexMap h' (vertexMap h x) = vertexMap (h.trans h') x := by
  rcases x with x | x <;> induction x using QuotientGroup.induction_on with
  | H k => simp [levelMap_apply_apply]

lemma vertexMap_id (N : Level b₀ b₁) (x : BSVertex (levelEquiv N)) :
    vertexMap (le_refl N) x = x := by
  rcases x with x | x <;> induction x using QuotientGroup.induction_on with
  | H k => simp [levelMap_id]

variable (b₀ b₁) in
/-- **The tree tower of the loop of groups** on its tempered fundamental group `loopGroup b₀ b₁`:
level groups `H_N`, Bass–Serre trees, kinds `true` on vertex cosets. -/
def tower : TreeTower (loopGroup b₀ b₁) (Level b₀ b₁) where
  G N := levelGroup N
  ρ N := proj N
  V N := BSVertex (levelEquiv N)
  graph N := bassSerreGraph (levelEquiv N)
  isTree N := isTree_bassSerreGraph
  adj_smul N g x y := bassSerreGraph_adj_smul g x y
  kind N x := x.isLeft
  kind_smul N g x := by rcases x with x | x <;> rfl
  kind_adj N x y hxy := by
    rcases x with x | x <;> rcases y with y | y
    · exact absurd hxy (not_adj_inl_inl _ _)
    · simp
    · simp
    · exact absurd hxy (not_adj_inr_inr _ _)
  map f := vertexMap f.le
  map_smul f g x := by
    rw [vertexMap_smul, levelMap_proj]
  map_adj f x y hxy := Or.inl (vertexMap_adj f.le x y hxy)

theorem isFunctorial_tower : (tower b₀ b₁).IsFunctorial where
  map_id N x := vertexMap_id N x
  map_comp f g x := (vertexMap_comp f.le g.le x).symm

end

end LoopTower

end TemperedFundamentalGroups
