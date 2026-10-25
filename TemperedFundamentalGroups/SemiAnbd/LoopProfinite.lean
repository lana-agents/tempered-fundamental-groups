/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import TemperedFundamentalGroups.SemiAnbd.HNNResFinite
import TemperedFundamentalGroups.SemiAnbd.LoopTowerSys

/-!
# The tempered fundamental group of a loop injects into the profinite one

For a loop of groups with compact vertex group `Π` (`SemiAnbd/LoopTower.lean`), the level groups
`H_N = Q_N *_{φ_N}` are HNN extensions of the finite groups `Q_N = Π / N`. The **profinite
fundamental group** of the loop is
`π̂₁ = lim_N Ĥ_N` (`LoopTower.loopHat`, a profinite group): a finite quotient of the profinite
HNN extension of `Π` whose restriction to `Π` is continuous has an open normal kernel `N` on `Π`
with `b₀⁻¹ N = b₁⁻¹ N`, hence factors through `H_N`.

* `LoopTower.exists_isOpen_finiteIndex_not_mem`: the open normal subgroups of finite index of
  `loopGroup b₀ b₁ = π^temp` separate points (`H_N` is residually finite,
  `HNNExtension.residuallyFinite`);
* **`LoopTower.toHat`**, **`LoopTower.toHat_injective`**: the comparison
  `π^temp ↪ π̂₁` ([SemiAnbd] Prop 3.6(iii), `semianbd.txt` l.1808, proof l.1880), continuous
  (`LoopTower.continuous_toHat`);
* `LoopTower.exists_finite_quotient_vertex_injective`: for every level `N` there is a finite
  quotient of `H_N` in which `Q_N` embeds ([SemiAnbd] Prop 2.5(ii), l.1186).
-/

open CategoryTheory HNNExtension

namespace TemperedFundamentalGroups

namespace LoopTower

noncomputable section

universe u

variable {Pv E : Type u} [Group Pv] [TopologicalSpace Pv] [IsTopologicalGroup Pv] [CompactSpace Pv]
  [Group E] {b₀ b₁ : E →* Pv}

instance (N : Level b₀ b₁) : Group.ResiduallyFinite (levelGroup N) :=
  HNNExtension.residuallyFinite _

/-- **[SemiAnbd] Prop 2.5(ii) for the loop**: at every level there is a finite quotient of the
level group in which the vertex group `Q_N` embeds. -/
theorem exists_finite_quotient_vertex_injective (N : Level b₀ b₁) :
    ∃ (Q : Type u) (_ : Group Q) (_ : Finite Q) (f : levelGroup N →* Q),
      Function.Injective (f.comp of) :=
  HNNExtension.exists_finite_quotient_injective_of _

/-- **The open normal subgroups of finite index of `π^temp` separate points.** -/
theorem exists_isOpen_finiteIndex_not_mem (g : loopGroup b₀ b₁) (hg : g ≠ 1) :
    ∃ U : Subgroup (loopGroup b₀ b₁), U.Normal ∧ U.FiniteIndex ∧
      IsOpen (U : Set (loopGroup b₀ b₁)) ∧ g ∉ U := by
  obtain ⟨N, hN⟩ : ∃ N, proj N g ≠ 1 := by
    by_contra! h
    exact hg (Subtype.ext (funext h))
  obtain ⟨H, hH⟩ := Group.exists_finiteIndexNormalSubgroup_notMem (proj N g) hN
  refine ⟨(H.comap (proj N)).toSubgroup, (H.comap (proj N)).isNormal',
    (H.comap (proj N)).isFiniteIndex',
    Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_, hH⟩
  refine Filter.mem_of_superset ((isOpen_proj_fiber N 1).mem_nhds (map_one _)) fun x hx ↦ ?_
  change proj N x ∈ H.toSubgroup
  rw [show proj N x = 1 from hx]
  exact one_mem _

variable (b₀ b₁) in
/-- The diagram of level groups. -/
def levelDiagram : Level b₀ b₁ ⥤ GrpCat.{u} where
  obj N := GrpCat.of (levelGroup N)
  map f := GrpCat.ofHom (levelMap (leOfHom f))
  map_id N := GrpCat.hom_ext (levelMap_id N)
  map_comp f g := GrpCat.hom_ext (levelMap_comp (leOfHom f) (leOfHom g)).symm

variable (b₀ b₁) in
/-- **The profinite fundamental group `π̂₁` of the loop**: the limit of the profinite completions
of the level groups. -/
abbrev loopHat : ProfiniteGrp.{u} :=
  ProfiniteGrp.limit (levelDiagram b₀ b₁ ⋙ ProfiniteGrp.profiniteCompletion)

lemma completion_map_etaFn {G H : GrpCat.{u}} (f : G ⟶ H) (x : G) :
    ProfiniteGrp.profiniteCompletion.map f (ProfiniteGrp.ProfiniteCompletion.etaFn G x) =
      ProfiniteGrp.ProfiniteCompletion.etaFn H (f x) :=
  ConcreteCategory.congr_hom (ProfiniteGrp.ProfiniteCompletion.lift_eta
    (f ≫ ProfiniteGrp.ProfiniteCompletion.eta H)) x

/-- The underlying map of `toHat`. -/
def toHatFun (x : loopGroup b₀ b₁) : loopHat b₀ b₁ :=
  ⟨fun N ↦ ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (levelGroup N)) (proj N x),
    fun N N' f ↦ by
      exact (completion_map_etaFn ((levelDiagram b₀ b₁).map f) (proj N x)).trans
        (congrArg _ (levelMap_proj (leOfHom f) x))⟩

/-- **The comparison `π^temp ↪ π̂₁`** ([SemiAnbd] Prop 3.6(iii)). -/
def toHat : loopGroup b₀ b₁ →* loopHat b₀ b₁ where
  toFun := toHatFun
  map_one' := Subtype.ext (funext fun N ↦ by simp [toHatFun]; rfl)
  map_mul' x y := Subtype.ext (funext fun N ↦ by simp [toHatFun]; rfl)

omit [IsTopologicalGroup Pv] [CompactSpace Pv] in
/-- A map factoring through a projection to a (discrete) level group is continuous. -/
lemma continuous_comp_proj {Y : Type*} [TopologicalSpace Y] (N : Level b₀ b₁)
    (h : levelGroup N → Y) : Continuous fun x : loopGroup b₀ b₁ ↦ h (proj N x) := by
  refine continuous_def.2 fun S _ ↦ ?_
  have : (fun x : loopGroup b₀ b₁ ↦ h (proj N x)) ⁻¹' S =
      ⋃ y ∈ h ⁻¹' S, {x | proj N x = y} := by
    ext x; simp
  rw [this]
  exact isOpen_biUnion fun y _ ↦ isOpen_proj_fiber N y

omit [IsTopologicalGroup Pv] [CompactSpace Pv] in
/-- The comparison `π^temp → π̂₁` is continuous. -/
theorem continuous_toHat : Continuous (toHat (b₀ := b₀) (b₁ := b₁)) :=
  Continuous.subtype_mk (continuous_pi fun N ↦ continuous_comp_proj N _) _

/-- **`π^temp(G) ↪ π̂₁(G)` is injective** ([SemiAnbd] Prop 3.6(iii): the level groups, HNN
extensions of finite groups, are residually finite). -/
theorem toHat_injective : Function.Injective (toHat (b₀ := b₀) (b₁ := b₁)) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  refine Subtype.ext (funext fun N ↦ ?_)
  have h1 := congrArg (fun y : loopHat b₀ b₁ ↦ y.1 N) hx
  have hinj := (ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (GrpCat.of (levelGroup N))).2 inferInstance
  exact hinj (h1.trans (map_one (ProfiniteGrp.ProfiniteCompletion.eta
    (GrpCat.of (levelGroup N))).hom).symm)

end

end LoopTower

end TemperedFundamentalGroups
