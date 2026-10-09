/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.CountableFibres
import TemperedFundamentalGroups.Topology.CurveCovering

/-!
# Universal coverings of noetherian spaces of dimension at most one

Let `Z` be a noetherian, quasi-sober `T₀` space of topological Krull dimension `≤ 1` (for
instance the special fibre of a proper curve over a discrete valuation ring). Its irreducible
components form a curve configuration (`TemperedFundamentalGroups.curveConfig`): two different
components meet in finitely many closed points. The tree covering of this configuration
(`TemperedFundamentalGroups.CurveConfig.Cover`) is a universal covering of `Z`.

## Main definitions and results

* `TemperedFundamentalGroups.IsUniversalCovering p`: `p` is a covering map with connected
  total space, and every continuous map from the total space lifts along every covering map,
  through every point of the fibre.
* `TemperedFundamentalGroups.universalCovering Z hdim z₀`, with projection
  `universalCovering.proj` and base point `universalCovering.base` over `z₀`.
* `TemperedFundamentalGroups.universalCovering.isUniversalCovering`.
* `TemperedFundamentalGroups.IsUniversalCovering.existsUnique_lift`: for a covering `q : P → Z`
  and `x₀` over `p e₀`, there is a unique continuous `f` with `q ∘ f = p` and `f e₀ = x₀`.
* `TemperedFundamentalGroups.IsUniversalCovering.exists_section`: every covering of the total
  space has a continuous section through every point.
* `TemperedFundamentalGroups.IsUniversalCovering.countable_fibre`: the fibres are countable.
* `TemperedFundamentalGroups.exists_universalCovering`.
-/

universe u v

open Set Topology TopologicalSpace

namespace TemperedFundamentalGroups

/-- `p : E → Z` is a universal covering: a covering map with connected total space such that
every continuous map from `E` lifts along every covering map, through every point of the
fibre. -/
structure IsUniversalCovering.{u₁, v₁, w₁, w₂} {E : Type u₁} {Z : Type v₁} [TopologicalSpace E]
    [TopologicalSpace Z] (p : E → Z) : Prop where
  isCoveringMap : IsCoveringMap p
  connectedSpace : ConnectedSpace E
  exists_lift : ∀ (Y : Type w₁) (P : Type w₂) [TopologicalSpace Y] [TopologicalSpace P]
    (q : P → Y), IsCoveringMap q → ∀ g : E → Y, Continuous g → ∀ (b : E) (y : P), q y = g b →
    ∃ f : E → P, Continuous f ∧ q ∘ f = g ∧ f b = y

namespace IsUniversalCovering

universe w₁ w₂

variable {E : Type u} {Z : Type v} [TopologicalSpace E] [TopologicalSpace Z] {p : E → Z}

/-- Every covering of the total space of a universal covering has a continuous section through
every point. -/
theorem exists_section (hp : IsUniversalCovering.{u, v, u, w₂} p) {P : Type w₂}
    [TopologicalSpace P] {q : P → E} (hq : IsCoveringMap q) (x : P) :
    ∃ s : E → P, Continuous s ∧ q ∘ s = id ∧ s (q x) = x :=
  hp.exists_lift E P q hq id continuous_id (q x) x rfl

/-- The lifting property of a universal covering: maps of coverings from the universal covering
to any covering exist and are unique once the image of a point is fixed. -/
theorem existsUnique_lift (hp : IsUniversalCovering.{u, v, v, w₂} p) {P : Type w₂}
    [TopologicalSpace P] {q : P → Z} (hq : IsCoveringMap q) (e₀ : E) (x₀ : P)
    (hx₀ : q x₀ = p e₀) : ∃! f : E → P, Continuous f ∧ q ∘ f = p ∧ f e₀ = x₀ := by
  have := hp.connectedSpace
  obtain ⟨f, hf, hqf, hfx⟩ :=
    hp.exists_lift Z P q hq p hp.isCoveringMap.continuous e₀ x₀ hx₀
  refine ⟨f, ⟨hf, hqf, hfx⟩, fun f' ⟨hf', hqf', hfx'⟩ ↦ ?_⟩
  exact hq.eq_of_comp_eq hf' hf (hqf'.trans hqf.symm) e₀ (hfx'.trans hfx.symm)

/-- The fibres of a universal covering of a noetherian space are countable. -/
theorem countable_fibre (hp : IsUniversalCovering.{u, v, w₁, w₂} p) [NoetherianSpace Z]
    (z : Z) : (p ⁻¹' {z}).Countable :=
  have := hp.connectedSpace
  hp.isCoveringMap.countable_fibre z

end IsUniversalCovering

section Dimension

variable {Z : Type u} [TopologicalSpace Z]

/-- In a space of dimension `≤ 1` there are no chains of three irreducible closed sets. -/
lemma not_lt_lt_of_topologicalKrullDim_le_one (hdim : topologicalKrullDim Z ≤ 1)
    {A B C : IrreducibleCloseds Z} (hAB : A < B) (hBC : B < C) : False := by
  rcases Order.krullDim_le_one_iff.1 hdim B with h | h
  · exact h.not_lt hAB
  · exact h.not_lt hBC

/-- A point on two different irreducible components of a `T₀` space of dimension `≤ 1` is
closed. -/
lemma isClosed_singleton_of_mem_inter [T0Space Z] (hdim : topologicalKrullDim Z ≤ 1)
    {C D : Set Z} (hC : C ∈ irreducibleComponents Z) (hD : D ∈ irreducibleComponents Z)
    (hCD : C ≠ D) {z : Z} (hzC : z ∈ C) (hzD : z ∈ D) : IsClosed ({z} : Set Z) := by
  have hCc := isClosed_of_mem_irreducibleComponents C hC
  have hDc := isClosed_of_mem_irreducibleComponents D hD
  let B : IrreducibleCloseds Z := ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
  let C' : IrreducibleCloseds Z := ⟨C, hC.1, hCc⟩
  have hBC : B < C' := by
    refine lt_of_le_of_ne (show closure {z} ⊆ C from
      hCc.closure_subset_iff.2 (singleton_subset_iff.2 hzC)) fun h ↦ hCD ?_
    have h' : C = closure {z} := congrArg SetLike.coe h.symm
    have hCD' : C ⊆ D := h' ▸ hDc.closure_subset_iff.2 (singleton_subset_iff.2 hzD)
    exact le_antisymm hCD' (hC.2 hD.1 hCD')
  suffices h : closure ({z} : Set Z) ⊆ {z} by
    rw [← closure_subset_iff_isClosed]; exact h
  intro y hy
  by_contra hyz
  let A : IrreducibleCloseds Z := ⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩
  have hAB : A < B := by
    refine lt_of_le_of_ne (show closure {y} ⊆ closure {z} from
      isClosed_closure.closure_subset_iff.2 (singleton_subset_iff.2 hy)) fun h ↦ hyz ?_
    exact (inseparable_iff_closure_eq.2 (congrArg SetLike.coe h)).eq
  exact not_lt_lt_of_topologicalKrullDim_le_one hdim hAB hBC

/-- Two different irreducible components of a noetherian quasi-sober `T₀` space of dimension
`≤ 1` meet in a finite set. -/
lemma finite_inter_of_mem_irreducibleComponents [NoetherianSpace Z] [QuasiSober Z] [T0Space Z]
    (hdim : topologicalKrullDim Z ≤ 1) {C D : Set Z} (hC : C ∈ irreducibleComponents Z)
    (hD : D ∈ irreducibleComponents Z) (hCD : C ≠ D) : (C ∩ D).Finite := by
  obtain ⟨S, hSf, hSc, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    ((isClosed_of_mem_irreducibleComponents C hC).inter
      (isClosed_of_mem_irreducibleComponents D hD))
  rw [hS]
  refine hSf.sUnion fun T hT ↦ Set.Subsingleton.finite ?_
  obtain ⟨x, hx⟩ := QuasiSober.sober (hSi T hT) (hSc T hT)
  have hmem : x ∈ C ∩ D := hS ▸ subset_sUnion_of_mem hT hx.mem
  have hcl := isClosed_singleton_of_mem_inter hdim hC hD hCD hmem.1 hmem.2
  have hx' : closure ({x} : Set Z) = T := hx
  rw [← hx', hcl.closure_eq]
  exact subsingleton_singleton

end Dimension

section Config

variable (Z : Type u) [TopologicalSpace Z] [NoetherianSpace Z] [T0Space Z] [QuasiSober Z]

instance : Finite (irreducibleComponents Z) :=
  NoetherianSpace.finite_irreducibleComponents.to_subtype

/-- The irreducible components of a noetherian quasi-sober `T₀` space of dimension `≤ 1` form a
curve configuration. -/
noncomputable def curveConfig (hdim : topologicalKrullDim Z ≤ 1) :
    CurveConfig Z (irreducibleComponents Z) where
  C i := i.1
  isClosed_C i := isClosed_of_mem_irreducibleComponents i.1 i.2
  η i := i.2.1.genericPoint
  η_mem i := (i.2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents i.1 i.2)).mem
  η_generic i U hU hne := by
    rw [(i.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents i.1 i.2)).mem_open_set_iff hU, inter_comm]
    exact hne
  S := {z | ∃ i j : irreducibleComponents Z, i ≠ j ∧ z ∈ i.1 ∧ z ∈ j.1}
  finite_S := by
    refine (finite_iUnion fun p : {p : irreducibleComponents Z × irreducibleComponents Z //
      p.1 ≠ p.2} ↦ finite_inter_of_mem_irreducibleComponents hdim p.1.1.2 p.1.2.2
        (fun h ↦ p.2 (Subtype.ext h))).subset ?_
    rintro z ⟨i, j, hij, hi, hj⟩
    exact mem_iUnion.2 ⟨⟨(i, j), hij⟩, hi, hj⟩
  isClosed_singleton := by
    rintro z ⟨i, j, hij, hi, hj⟩
    exact isClosed_singleton_of_mem_inter hdim i.2 j.2 (fun h ↦ hij (Subtype.ext h)) hi hj
  cover z := by
    obtain ⟨C, hC, hzC⟩ :=
      exists_mem_irreducibleComponents_subset_of_isIrreducible {z} isIrreducible_singleton
    exact ⟨⟨C, hC⟩, hzC rfl⟩
  mem_S z i j hi hj hij := ⟨i, j, hij, hi, hj⟩

variable {Z}

/-- The root component of the universal covering: a component containing `z₀`. -/
noncomputable def universalCovering.root (hdim : topologicalKrullDim Z ≤ 1) (z₀ : Z) :
    irreducibleComponents Z :=
  (curveConfig Z hdim).comp z₀

variable (Z) in
/-- The universal covering of a noetherian quasi-sober `T₀` space of dimension `≤ 1`, based at a
point `z₀`. -/
abbrev universalCovering (hdim : topologicalKrullDim Z ≤ 1) (z₀ : Z) : Type u :=
  (curveConfig Z hdim).Cover (universalCovering.root hdim z₀)

namespace universalCovering

variable (hdim : topologicalKrullDim Z ≤ 1) (z₀ : Z)

/-- The projection of the universal covering. -/
noncomputable def proj : universalCovering Z hdim z₀ → Z :=
  (curveConfig Z hdim).proj (root hdim z₀)

/-- The base point of the universal covering. -/
noncomputable def base : universalCovering Z hdim z₀ :=
  CurveConfig.base _ _ ((curveConfig Z hdim).mem_comp z₀)

lemma proj_base : proj hdim z₀ (base hdim z₀) = z₀ := rfl

theorem isUniversalCovering : IsUniversalCovering.{u, u, w₁, w₂} (proj hdim z₀) where
  isCoveringMap := CurveConfig.isCoveringMap_proj
  connectedSpace := CurveConfig.connectedSpace_cover ((curveConfig Z hdim).mem_comp z₀)
  exists_lift _ _ _ _ _ hq _ hg b y hy :=
    CurveConfig.exists_lift hq hg ((curveConfig Z hdim).mem_comp z₀) b y hy

end universalCovering

end Config

/-- **Universal coverings of curves.** A connected noetherian quasi-sober `T₀` space of
topological Krull dimension `≤ 1` has a universal covering: a connected covering space on which
every covering has a continuous section through every point. -/
theorem exists_universalCovering (Z : Type u) [TopologicalSpace Z] [NoetherianSpace Z]
    [T0Space Z] [QuasiSober Z] [ConnectedSpace Z] (hdim : topologicalKrullDim Z ≤ 1) (z₀ : Z) :
    ∃ (E : Type u) (_ : TopologicalSpace E) (p : E → Z) (e₀ : E), p e₀ = z₀ ∧
      IsCoveringMap p ∧ ConnectedSpace E ∧
      ∀ (P : Type u) [TopologicalSpace P] (q : P → E), IsCoveringMap q → ∀ x : P,
        ∃ s : E → P, Continuous s ∧ q ∘ s = id ∧ s (q x) = x := by
  have h := universalCovering.isUniversalCovering.{u, u, u} hdim z₀
  exact ⟨_, inferInstance, _, universalCovering.base hdim z₀, rfl, h.isCoveringMap,
    h.connectedSpace, fun P _ q hq x ↦ h.exists_section hq x⟩

end TemperedFundamentalGroups
