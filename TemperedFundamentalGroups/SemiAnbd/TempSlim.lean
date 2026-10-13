/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Topology.Algebra.OpenSubgroup
import TemperedFundamentalGroups.SemiAnbd.TreeTower

/-!
# Temp-slim topological groups (Blueprint §12.9)

A topological group `P` is **temp-slim** (`TempSlim P`) if the centralizer of every open subgroup
is trivial ([Mzk14] (Semi-graphs of anabelioids), Example 3.10; [EtTh], proof of Prop. 2.11).
This is the hypothesis of [EtTh], Prop. 2.11(ii) and hence of the first step of cyclotomic
rigidity ([EtTh], Cor. 2.19(i)): it lets one recover the kernel `μ_N` of `Π[μ_N] ↠ Π` as the
union of the centralizers of the open subgroups of `Π[μ_N]`.

## Main results

* `TempSlim.of_continuousMulEquiv`: temp-slimness is invariant under `≃ₜ*`.
* `TempSlim.of_isOpen`, `TempSlim.ker`: open subgroups (e.g. kernels of continuous characters
  to discrete groups, such as `Π^tp_Y ⊆ Π^tp_X`) of temp-slim groups are temp-slim.
* `TempSlim.of_extension`: if `f : P →* Q` is an open map, `ker f` is temp-slim and `Q` is
  temp-slim (e.g. `Q = G_K` slim, `ker f = Δ`), then `P` is temp-slim.
* `TempSlim.of_commensurator_eq` (**the argument of [Mzk14], Example 3.10**): if `P` has one
  compact subgroup `S` which is **commensurably terminal** (`commensurator S = S`) and
  temp-slim, then `P` is temp-slim. Indeed, if `x` centralizes an open `H`, then `H ⊓ S` has
  finite index in the compact `S` and is fixed by conjugation by `x`, so `x` commensurates `S`,
  hence `x ∈ S`, and `x` centralizes the open subgroup `H ⊓ S` of `S`.
* `TreeTower.tempSlim_of_HI`: the tree-tower form: a compact verticial subgroup `stab s` with
  `HI s` (commensurably terminal by `TreeTower.commensurator_stab`) which is temp-slim (for a
  compact group: slim in the profinite sense) makes the tower group temp-slim.
-/

open scoped Pointwise

namespace TemperedFundamentalGroups

/-- **Temp-slim topological groups** ([Mzk14], Example 3.10; [EtTh], proof of Prop. 2.11): the
centralizer of every open subgroup is trivial. (The same definition as `Iut.EtaleTheta.TempSlim`
in `iut`.) -/
def TempSlim (P : Type*) [Group P] [TopologicalSpace P] : Prop :=
  ∀ H : Subgroup P, IsOpen (H : Set P) → Subgroup.centralizer (H : Set P) = ⊥

namespace TempSlim

variable {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]

lemma eq_one (h : TempSlim P) {H : Subgroup P} (hH : IsOpen (H : Set P)) {x : P}
    (hx : ∀ y ∈ H, y * x = x * y) : x = 1 := by
  have : x ∈ Subgroup.centralizer (H : Set P) := Subgroup.mem_centralizer_iff.2 hx
  rwa [h H hH, Subgroup.mem_bot] at this

lemma center_eq_bot (h : TempSlim P) : Subgroup.center P = ⊥ := by
  rw [← Subgroup.centralizer_univ]
  exact h ⊤ isOpen_univ

/-- Temp-slimness is invariant under isomorphisms of topological groups. -/
theorem of_continuousMulEquiv (e : P ≃ₜ* Q) (h : TempSlim P) : TempSlim Q := by
  intro H hH
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' : e.symm x = 1 := by
    refine h.eq_one (H := H.comap e.toMulEquiv.toMonoidHom) (hH.preimage e.continuous) ?_
    intro y hy
    apply e.injective
    have := Subgroup.mem_centralizer_iff.1 hx (e y) hy
    simpa using this
  simpa using congrArg e hx'

theorem congr (e : P ≃ₜ* Q) : TempSlim P ↔ TempSlim Q :=
  ⟨of_continuousMulEquiv e, of_continuousMulEquiv e.symm⟩

/-- **Open subgroups of temp-slim groups are temp-slim** (with the subspace topology). -/
theorem of_isOpen (h : TempSlim P) {U : Subgroup P} (hU : IsOpen (U : Set P)) : TempSlim U := by
  intro H hH
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hH' : IsOpen ((H.map U.subtype : Subgroup P) : Set P) := by
    rw [Subgroup.coe_map]
    exact hU.isOpenMap_subtype_val _ hH
  apply Subtype.ext
  refine h.eq_one hH' ?_
  rintro _ ⟨y, hy, rfl⟩
  exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hx y hy)

/-- The kernel of a continuous homomorphism to a discrete group (e.g. `Π^tp_Y = ker(Π^tp_X → ℤ)`)
of a temp-slim group is temp-slim. -/
theorem ker [DiscreteTopology Q] (h : TempSlim P) (f : P →* Q) (hf : Continuous f) :
    TempSlim f.ker :=
  h.of_isOpen (isOpen_ker_of_continuous _ hf)
where
  isOpen_ker_of_continuous (f : P →* Q) (hf : Continuous f) : IsOpen (f.ker : Set P) := by
    have : (f.ker : Set P) = f ⁻¹' {1} := rfl
    rw [this]
    exact (isOpen_discrete _).preimage hf

/-- **Extensions** ([Mzk14], Example 3.10; the arithmetic tempered group as an extension of the
slim `G_K` by the geometric tempered group): if `f : P →* Q` is an open map, `ker f` (with the
subspace topology) is temp-slim and `Q` is temp-slim, then `P` is temp-slim. -/
theorem of_extension (f : P →* Q) (hf : IsOpenMap f) (hQ : TempSlim Q) (hK : TempSlim f.ker) :
    TempSlim P := by
  intro H hH
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' := Subgroup.mem_centralizer_iff.1 hx
  have hfx : f x = 1 := by
    refine hQ.eq_one (H := H.map f) (by rw [Subgroup.coe_map]; exact hf _ hH) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hx' y hy]
  have := hK.eq_one (x := ⟨x, hfx⟩) (H := H.comap f.ker.subtype)
    (hH.preimage continuous_subtype_val) (fun y hy => Subtype.ext (hx' y hy))
  exact congrArg Subtype.val this

/-- For `S` compact and `H` open, `H ⊓ S` has finite index in `S`. -/
lemma relIndex_ne_zero_of_isCompact [IsTopologicalGroup P] {S H : Subgroup P}
    (hS : IsCompact (S : Set P)) (hH : IsOpen (H : Set P)) : H.relIndex S ≠ 0 := by
  have : CompactSpace S := isCompact_iff_compactSpace.1 hS
  have hW : IsOpen ((H.subgroupOf S : Subgroup S) : Set S) := hH.preimage continuous_subtype_val
  have := Subgroup.quotient_finite_of_isOpen _ hW
  have : (H.subgroupOf S).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  exact Subgroup.FiniteIndex.index_ne_zero

omit [TopologicalSpace P] in
/-- If `x` centralizes `W ≤ S` and `W` has finite index in `S`, then `x` commensurates `S`. -/
lemma mem_commensurator_of_centralizes {S W : Subgroup P} (hWS : W ≤ S)
    (hW : W.relIndex S ≠ 0) {x : P} (hx : ∀ y ∈ W, y * x = x * y) :
    x ∈ Subgroup.Commensurable.commensurator S := by
  rw [Subgroup.Commensurable.commensurator_mem_iff]
  have hSW : Subgroup.Commensurable S W := ⟨by rw [Subgroup.relIndex_eq_one.2 hWS]; simp, hW⟩
  have hxW : ConjAct.toConjAct x • W = W := by
    ext y
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def, map_inv,
      ConjAct.ofConjAct_toConjAct]
    simp only [inv_inv]
    constructor
    · intro hy
      have h := hx _ hy
      have h' : x⁻¹ * y * x = y :=
        mul_right_cancel (h.trans (by simp [mul_assoc]))
      rwa [h'] at hy
    · intro hy
      rw [mul_assoc, hx y hy, inv_mul_cancel_left]
      exact hy
  have h := hSW.conj (ConjAct.toConjAct x)
  rw [hxW] at h
  exact h.trans hSW.symm

/-- **[Mzk14], Example 3.10 (the argument)**: a group with a compact, commensurably terminal,
temp-slim subgroup `S` is temp-slim. -/
theorem of_commensurator_eq [IsTopologicalGroup P] {S : Subgroup P}
    (hS : IsCompact (S : Set P)) (hcomm : Subgroup.Commensurable.commensurator S = S)
    (hSslim : TempSlim S) : TempSlim P := by
  intro H hH
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hx' := Subgroup.mem_centralizer_iff.1 hx
  have hxS : x ∈ S := by
    rw [← hcomm]
    refine mem_commensurator_of_centralizes (W := H ⊓ S) inf_le_right ?_
      (fun y hy => hx' y hy.1)
    have h := relIndex_ne_zero_of_isCompact hS hH
    rwa [Subgroup.inf_relIndex_right]
  have := hSslim.eq_one (x := ⟨x, hxS⟩) (H := H.subgroupOf S)
    (hH.preimage continuous_subtype_val) (fun y hy => Subtype.ext (hx' y hy))
  exact congrArg Subtype.val this

end TempSlim

namespace TreeTower

universe u v w x

variable {Γ : Type x} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {J : Type u} [CategoryTheory.Category.{v} J] {T : TreeTower.{u, v, w} Γ J}

/-- **Temp-slimness of a tree-tower group from one verticial subgroup** ([Mzk14], Example 3.10):
if the stabilizer of a system `s` with `HI s` (edge-like subgroups of infinite index, so `stab s`
is commensurably terminal, `commensurator_stab`) is compact and temp-slim, then `Γ` is
temp-slim. -/
theorem tempSlim_of_HI {s : T.Sys} (hs : T.HI s) (hc : IsCompact (stab s : Set Γ))
    (hslim : TempSlim (stab s)) : TempSlim Γ :=
  TempSlim.of_commensurator_eq hc (commensurator_stab hs) hslim

end TreeTower

end TemperedFundamentalGroups
