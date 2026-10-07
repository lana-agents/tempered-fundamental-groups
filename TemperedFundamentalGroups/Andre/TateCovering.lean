/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.CoveringCode

/-!
# The `ℤ`-covering of a space made of two pieces meeting in two places

Let `Z` be a topological space with closed subsets `C, E` such that `Z = C ∪ E` and
`C ∩ E = Cp ⊔ Cq` for disjoint closed sets `Cp, Cq` (`TateCovering.Decomp`). This is the shape of
the special fibre of the model of a Tate curve in `Andre/TateModel.lean`: a line `C` and a conic
`E` meeting in two points `p, q`. Gluing `ℤ` copies `Cₙ` of `C` and `Eₙ` of `E` by
`Cₙ ∩ Eₙ = Cp` and `Cₙ ∩ Eₙ₊₁ = Cq` gives a covering space `D.Space → Z` with deck group `ℤ`
acting by translation, simply transitively on every fibre. It is connected when `C` and `E` are
connected and `Cp, Cq` are nonempty.

Concretely `D.Space = Z × ℤ` as a set. Over `U₁ = Z ∖ Cq` the second coordinate is the sheet;
over `U₂ = Z ∖ Cp` the sheet is `n - shift z` with `shift = 0` on `C` and `1` off `C`. The topology
is the coarsest one for which the projection is continuous and the sheets over `U₁` and `U₂` are
open (`Decomp.continuous_iff`).

## Main results

* `Decomp.isCoveringMap`: the projection `D.Space → Z` is a covering map.
* `Decomp.deck`: the deck action `Multiplicative ℤ →* (D.Space ≃ₜ D.Space)`, simply transitive
  on fibres (`Decomp.existsUnique_deck`).
* `Decomp.connectedSpace`: `D.Space` is connected if `C, E` are and `Cp, Cq ≠ ∅`.
* `Decomp.toCode`: the covering coded as a `CoveringCode` for a trivial group action, with the
  deck action `Decomp.deckCode`.
-/

universe u

open Topology Set

namespace TemperedFundamentalGroups

namespace TateCovering

/-- A space `Z = C ∪ E` with `C ∩ E = Cp ⊔ Cq`, all four sets closed. -/
structure Decomp (Z : Type u) [TopologicalSpace Z] where
  /-- The first piece. -/
  C : Set Z
  /-- The second piece. -/
  E : Set Z
  /-- The first part of the intersection. -/
  Cp : Set Z
  /-- The second part of the intersection. -/
  Cq : Set Z
  isClosed_C : IsClosed C
  isClosed_E : IsClosed E
  isClosed_Cp : IsClosed Cp
  isClosed_Cq : IsClosed Cq
  union : C ∪ E = univ
  inter : C ∩ E = Cp ∪ Cq
  disjoint : Disjoint Cp Cq

namespace Decomp

variable {Z : Type u} [TopologicalSpace Z] (D : Decomp Z)

lemma mem_C_of_notMem_E {z : Z} (hz : z ∉ D.E) : z ∈ D.C := by
  have : z ∈ D.C ∪ D.E := D.union ▸ mem_univ z
  exact this.resolve_right hz

lemma Cp_subset_inter : D.Cp ⊆ D.C ∩ D.E := D.inter ▸ subset_union_left

lemma Cq_subset_inter : D.Cq ⊆ D.C ∩ D.E := D.inter ▸ subset_union_right

lemma mem_C_of_mem_Cp {z : Z} (hz : z ∈ D.Cp) : z ∈ D.C := (D.Cp_subset_inter hz).1

lemma mem_C_of_mem_Cq {z : Z} (hz : z ∈ D.Cq) : z ∈ D.C := (D.Cq_subset_inter hz).1

lemma mem_E_of_mem_Cp {z : Z} (hz : z ∈ D.Cp) : z ∈ D.E := (D.Cp_subset_inter hz).2

lemma mem_E_of_mem_Cq {z : Z} (hz : z ∈ D.Cq) : z ∈ D.E := (D.Cq_subset_inter hz).2

lemma notMem_Cq_of_mem_Cp {z : Z} (hz : z ∈ D.Cp) : z ∉ D.Cq :=
  fun h => D.disjoint.notMem_of_mem_left hz h

lemma mem_Cp_or_mem_Cq {z : Z} (hC : z ∈ D.C) (hE : z ∈ D.E) : z ∈ D.Cp ∨ z ∈ D.Cq := by
  have : z ∈ D.C ∩ D.E := ⟨hC, hE⟩
  rwa [D.inter] at this

open Classical in
/-- The sheet shift between the two charts: `0` on `C`, `1` off `C`. -/
noncomputable def shift (z : Z) : ℤ := if z ∈ D.C then 0 else 1

lemma shift_of_mem {z : Z} (hz : z ∈ D.C) : D.shift z = 0 := if_pos hz

lemma shift_of_notMem {z : Z} (hz : z ∉ D.C) : D.shift z = 1 := if_neg hz

/-- The points of the covering space: a point of `Z` and an integer (the sheet over `Z ∖ Cq`,
resp. the sheet over `Z ∖ Cp` for points of `Cq`). -/
@[ext]
structure Space (D : Decomp Z) : Type u where
  /-- The image in `Z`. -/
  pt : Z
  /-- The label. -/
  n : ℤ

/-- The map defining the topology of `D.Space`. -/
def embed (x : D.Space) : Z × (ℤ → Prop) × (ℤ → Prop) :=
  (x.pt, fun k => x.pt ∉ D.Cq ∧ x.n = k, fun k => x.pt ∉ D.Cp ∧ x.n - D.shift x.pt = k)

instance : TopologicalSpace D.Space := TopologicalSpace.induced D.embed inferInstance

variable {D}

/-- A map into `D.Space` is continuous iff its projection is continuous and the preimages of
the sheets over `Z ∖ Cq` and over `Z ∖ Cp` are open. -/
lemma continuous_iff {Y : Type*} [TopologicalSpace Y] {g : Y → D.Space} :
    Continuous g ↔ Continuous (fun y => (g y).pt) ∧
      (∀ k, IsOpen {y | (g y).pt ∉ D.Cq ∧ (g y).n = k}) ∧
      ∀ k, IsOpen {y | (g y).pt ∉ D.Cp ∧ (g y).n - D.shift (g y).pt = k} := by
  rw [continuous_induced_rng, continuous_prodMk, continuous_prodMk, continuous_pi_iff,
    continuous_pi_iff]
  simp only [Function.comp_def, embed, continuous_Prop]

variable (D)

lemma continuous_pt : Continuous (fun x : D.Space => x.pt) :=
  (continuous_iff.1 continuous_id).1

lemma isOpen_sheet₁ (k : ℤ) : IsOpen {x : D.Space | x.pt ∉ D.Cq ∧ x.n = k} :=
  (continuous_iff.1 continuous_id).2.1 k

lemma isOpen_sheet₂ (k : ℤ) :
    IsOpen {x : D.Space | x.pt ∉ D.Cp ∧ x.n - D.shift x.pt = k} :=
  (continuous_iff.1 continuous_id).2.2 k

/-! ### Local triviality -/

lemma sheet₂_iff {z : Z} (hz : z ∉ D.Cq) (n k : ℤ) :
    (z ∉ D.Cp ∧ n - D.shift z = k) ↔ (z ∉ D.E ∧ n = k) ∨ (z ∉ D.C ∧ n = k + 1) := by
  by_cases hC : z ∈ D.C
  · rw [D.shift_of_mem hC, sub_zero]
    have : z ∈ D.Cp ↔ z ∈ D.E := ⟨D.mem_E_of_mem_Cp, fun hE =>
      (D.mem_Cp_or_mem_Cq hC hE).resolve_right hz⟩
    rw [this]
    tauto
  · rw [D.shift_of_notMem hC]
    have hp : z ∉ D.Cp := fun h => hC (D.mem_C_of_mem_Cp h)
    have hE : z ∈ D.E := by_contra fun h => hC (D.mem_C_of_notMem_E h)
    constructor
    · rintro ⟨-, h⟩
      exact Or.inr ⟨hC, by omega⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd hE h
      · exact ⟨hp, by omega⟩

lemma sheet₁_iff {z : Z} (hz : z ∉ D.Cp) (m k : ℤ) :
    (z ∉ D.Cq ∧ m + D.shift z = k) ↔ (z ∉ D.E ∧ m = k) ∨ (z ∉ D.C ∧ m = k - 1) := by
  by_cases hC : z ∈ D.C
  · rw [D.shift_of_mem hC, add_zero]
    have : z ∈ D.Cq ↔ z ∈ D.E := ⟨D.mem_E_of_mem_Cq, fun hE =>
      (D.mem_Cp_or_mem_Cq hC hE).resolve_left hz⟩
    rw [this]
    tauto
  · rw [D.shift_of_notMem hC]
    have hq : z ∉ D.Cq := fun h => hC (D.mem_C_of_mem_Cq h)
    have hE : z ∈ D.E := by_contra fun h => hC (D.mem_C_of_notMem_E h)
    constructor
    · rintro ⟨-, h⟩
      exact Or.inr ⟨hC, by omega⟩
    · rintro (⟨h, -⟩ | ⟨-, h⟩)
      · exact absurd hE h
      · exact ⟨hq, by omega⟩

lemma isOpen_snd_eq {X : Type*} [TopologicalSpace X] (k : ℤ) :
    IsOpen {x : X × ℤ | x.2 = k} :=
  (isOpen_discrete {k}).preimage continuous_snd

/-- The section over `Z ∖ Cq` of sheet `n`. -/
def sec₁ (x : (D.Cqᶜ : Set Z) × ℤ) : D.Space := ⟨x.1, x.2⟩

lemma continuous_sec₁ : Continuous D.sec₁ := by
  refine continuous_iff.2 ⟨continuous_subtype_val.comp continuous_fst, fun k => ?_, fun k => ?_⟩
  · convert isOpen_snd_eq (X := (D.Cqᶜ : Set Z)) k using 1
    ext x
    exact and_iff_right x.1.2
  · have : {x : (D.Cqᶜ : Set Z) × ℤ | (D.sec₁ x).pt ∉ D.Cp ∧ (D.sec₁ x).n -
        D.shift (D.sec₁ x).pt = k} =
        ((fun x : (D.Cqᶜ : Set Z) × ℤ => (x.1 : Z)) ⁻¹' D.Eᶜ ∩ {x | x.2 = k}) ∪
        ((fun x : (D.Cqᶜ : Set Z) × ℤ => (x.1 : Z)) ⁻¹' D.Cᶜ ∩ {x | x.2 = k + 1}) := by
      ext x
      exact D.sheet₂_iff x.1.2 x.2 k
    rw [this]
    have hc : Continuous fun x : (D.Cqᶜ : Set Z) × ℤ => (x.1 : Z) :=
      continuous_subtype_val.comp continuous_fst
    exact ((D.isClosed_E.isOpen_compl.preimage hc).inter (isOpen_snd_eq k)).union
      ((D.isClosed_C.isOpen_compl.preimage hc).inter (isOpen_snd_eq _))

/-- The section over `Z ∖ Cp` of sheet `m`. -/
noncomputable def sec₂ (x : (D.Cpᶜ : Set Z) × ℤ) : D.Space := ⟨x.1, x.2 + D.shift x.1⟩

lemma continuous_sec₂ : Continuous D.sec₂ := by
  refine continuous_iff.2 ⟨continuous_subtype_val.comp continuous_fst, fun k => ?_, fun k => ?_⟩
  · have : {x : (D.Cpᶜ : Set Z) × ℤ | (D.sec₂ x).pt ∉ D.Cq ∧ (D.sec₂ x).n = k} =
        ((fun x : (D.Cpᶜ : Set Z) × ℤ => (x.1 : Z)) ⁻¹' D.Eᶜ ∩ {x | x.2 = k}) ∪
        ((fun x : (D.Cpᶜ : Set Z) × ℤ => (x.1 : Z)) ⁻¹' D.Cᶜ ∩ {x | x.2 = k - 1}) := by
      ext x
      have := D.sheet₁_iff x.1.2 x.2 k
      simp only [sec₂, mem_setOf_eq, mem_union, mem_inter_iff, mem_preimage, mem_compl_iff]
      rw [this]
    rw [this]
    have hc : Continuous fun x : (D.Cpᶜ : Set Z) × ℤ => (x.1 : Z) :=
      continuous_subtype_val.comp continuous_fst
    exact ((D.isClosed_E.isOpen_compl.preimage hc).inter (isOpen_snd_eq k)).union
      ((D.isClosed_C.isOpen_compl.preimage hc).inter (isOpen_snd_eq _))
  · convert isOpen_snd_eq (X := (D.Cpᶜ : Set Z)) k using 1
    ext x
    simp only [sec₂, mem_setOf_eq, add_sub_cancel_right]
    exact and_iff_right x.1.2

/-- The trivialization over `Z ∖ Cq`. -/
def triv₁ : (fun x : D.Space => x.pt) ⁻¹' D.Cqᶜ ≃ₜ (D.Cqᶜ : Set Z) × ℤ where
  toFun x := (⟨x.1.pt, x.2⟩, x.1.n)
  invFun y := ⟨D.sec₁ y, y.1.2⟩
  left_inv x := rfl
  right_inv y := rfl
  continuous_toFun := by
    refine Continuous.prodMk ((D.continuous_pt.comp continuous_subtype_val).subtype_mk _) ?_
    refine continuous_discrete_rng.2 fun k => ?_
    convert (D.isOpen_sheet₁ k).preimage continuous_subtype_val using 1
    ext x
    exact (and_iff_right x.2).symm
  continuous_invFun := D.continuous_sec₁.subtype_mk _

/-- The trivialization over `Z ∖ Cp`. -/
noncomputable def triv₂ : (fun x : D.Space => x.pt) ⁻¹' D.Cpᶜ ≃ₜ (D.Cpᶜ : Set Z) × ℤ where
  toFun x := (⟨x.1.pt, x.2⟩, x.1.n - D.shift x.1.pt)
  invFun y := ⟨D.sec₂ y, y.1.2⟩
  left_inv x := by
    ext
    · rfl
    · simp [sec₂]
  right_inv y := by
    ext
    · rfl
    · simp [sec₂]
  continuous_toFun := by
    refine Continuous.prodMk ((D.continuous_pt.comp continuous_subtype_val).subtype_mk _) ?_
    refine continuous_discrete_rng.2 fun k => ?_
    convert (D.isOpen_sheet₂ k).preimage continuous_subtype_val using 1
    ext x
    exact (and_iff_right x.2).symm
  continuous_invFun := D.continuous_sec₂.subtype_mk _

/-- **The projection `D.Space → Z` is a covering map.** -/
theorem isCoveringMap : IsCoveringMap (fun x : D.Space => x.pt) := fun z => by
  by_cases hz : z ∈ D.Cq
  · have hp : z ∉ D.Cp := fun h => D.notMem_Cq_of_mem_Cp h hz
    exact IsEvenlyCovered.to_isEvenlyCovered_preimage (I := ℤ) ⟨inferInstance, D.Cpᶜ, hp,
      D.isClosed_Cp.isOpen_compl, D.isClosed_Cp.isOpen_compl.preimage D.continuous_pt,
      D.triv₂, fun _ => rfl⟩
  · exact IsEvenlyCovered.to_isEvenlyCovered_preimage (I := ℤ) ⟨inferInstance, D.Cqᶜ, hz,
      D.isClosed_Cq.isOpen_compl, D.isClosed_Cq.isOpen_compl.preimage D.continuous_pt,
      D.triv₁, fun _ => rfl⟩

/-! ### Deck transformations -/

/-- Translation of the labels by `d`. -/
def translate (d : ℤ) : D.Space ≃ₜ D.Space where
  toFun x := ⟨x.pt, x.n + d⟩
  invFun x := ⟨x.pt, x.n - d⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := by
    refine continuous_iff.2 ⟨D.continuous_pt, fun k => ?_, fun k => ?_⟩
    · convert D.isOpen_sheet₁ (k - d) using 1
      ext x
      change (x.pt ∉ D.Cq ∧ x.n + d = k) ↔ (x.pt ∉ D.Cq ∧ x.n = k - d)
      exact and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩
    · convert D.isOpen_sheet₂ (k - d) using 1
      ext x
      change (x.pt ∉ D.Cp ∧ x.n + d - D.shift x.pt = k) ↔
        (x.pt ∉ D.Cp ∧ x.n - D.shift x.pt = k - d)
      exact and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩
  continuous_invFun := by
    refine continuous_iff.2 ⟨D.continuous_pt, fun k => ?_, fun k => ?_⟩
    · convert D.isOpen_sheet₁ (k + d) using 1
      ext x
      change (x.pt ∉ D.Cq ∧ x.n - d = k) ↔ (x.pt ∉ D.Cq ∧ x.n = k + d)
      exact and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩
    · convert D.isOpen_sheet₂ (k + d) using 1
      ext x
      change (x.pt ∉ D.Cp ∧ x.n - d - D.shift x.pt = k) ↔
        (x.pt ∉ D.Cp ∧ x.n - D.shift x.pt = k + d)
      exact and_congr_right fun _ => ⟨fun h => by omega, fun h => by omega⟩

@[simp] lemma translate_pt (d : ℤ) (x : D.Space) : (D.translate d x).pt = x.pt := rfl

@[simp] lemma translate_n (d : ℤ) (x : D.Space) : (D.translate d x).n = x.n + d := rfl

/-- **The deck action** of `ℤ` (written multiplicatively) by translation. -/
def deck : Multiplicative ℤ →* (D.Space ≃ₜ D.Space) where
  toFun d := D.translate d.toAdd
  map_one' := by
    ext x
    · rfl
    · simp
  map_mul' d e := by
    ext x
    · rfl
    · simp only [translate_n, toAdd_mul, Homeomorph.mul_apply]
      ring

@[simp] lemma deck_pt (d : Multiplicative ℤ) (x : D.Space) : (D.deck d x).pt = x.pt := rfl

@[simp] lemma deck_n (d : Multiplicative ℤ) (x : D.Space) : (D.deck d x).n = x.n + d.toAdd :=
  rfl

/-- The deck group acts simply transitively on every fibre. -/
lemma existsUnique_deck {x y : D.Space} (h : x.pt = y.pt) :
    ∃! d : Multiplicative ℤ, D.deck d x = y := by
  refine ⟨Multiplicative.ofAdd (y.n - x.n), ?_, fun d hd => ?_⟩
  · ext
    · exact h
    · rw [deck_n, toAdd_ofAdd]
      ring
  · have := congrArg Space.n hd
    simp only [deck_n] at this
    apply Multiplicative.toAdd.injective
    simp only [toAdd_ofAdd]
    omega

/-! ### Connectedness -/

/-- The copy `Cₙ` of `C`. -/
def sheetC (n : ℤ) (z : D.C) : D.Space := ⟨z, n⟩

open Classical in
/-- The copy `Eₙ` of `E`: it meets `Cₙ` over `Cp` and `Cₙ₋₁` over `Cq`. -/
noncomputable def sheetE (n : ℤ) (z : D.E) : D.Space := ⟨z, if (z : Z) ∈ D.Cq then n - 1 else n⟩

lemma continuous_sheetC (n : ℤ) : Continuous (D.sheetC n) := by
  refine continuous_iff.2 ⟨continuous_subtype_val, fun k => ?_, fun k => ?_⟩
  · exact (D.isClosed_Cq.isOpen_compl.preimage continuous_subtype_val).inter
      (isOpen_const (p := n = k))
  · convert (D.isClosed_Cp.isOpen_compl.preimage continuous_subtype_val).inter
      (isOpen_const (p := n = k)) using 1
    ext z
    simp [sheetC, D.shift_of_mem z.2]

lemma continuous_sheetE (n : ℤ) : Continuous (D.sheetE n) := by
  refine continuous_iff.2 ⟨continuous_subtype_val, fun k => ?_, fun k => ?_⟩
  · convert (D.isClosed_Cq.isOpen_compl.preimage continuous_subtype_val).inter
      (isOpen_const (p := n = k)) using 1
    ext z
    simp only [sheetE, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    constructor
    · rintro ⟨h, h'⟩
      rw [if_neg h] at h'
      exact ⟨h, h'⟩
    · rintro ⟨h, h'⟩
      rw [if_neg h]
      exact ⟨h, h'⟩
  · convert (D.isClosed_Cp.isOpen_compl.preimage continuous_subtype_val).inter
      (isOpen_const (p := n - 1 = k)) using 1
    ext z
    simp only [sheetE, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_compl_iff]
    refine and_congr_right fun hp => ?_
    by_cases hq : (z : Z) ∈ D.Cq
    · rw [if_pos hq, D.shift_of_mem (D.mem_C_of_mem_Cq hq), sub_zero]
    · rw [if_neg hq]
      have hC : (z : Z) ∉ D.C := fun hC => (D.mem_Cp_or_mem_Cq hC z.2).elim hp hq
      rw [D.shift_of_notMem hC]

/-- **The covering space is connected** if `C` and `E` are connected and `Cp`, `Cq` are
nonempty. -/
theorem connectedSpace (hC : IsPreconnected D.C) (hE : IsPreconnected D.E)
    (hp : D.Cp.Nonempty) (hq : D.Cq.Nonempty) : ConnectedSpace D.Space := by
  obtain ⟨p, hp⟩ := hp
  obtain ⟨q, hq⟩ := hq
  have : PreconnectedSpace D.C := isPreconnected_iff_preconnectedSpace.1 hC
  have : PreconnectedSpace D.E := isPreconnected_iff_preconnectedSpace.1 hE
  let A : ℤ → Set D.Space := fun n => range (D.sheetC n) ∪ range (D.sheetE n)
  have hA : ∀ n, IsPreconnected (A n) := fun n => by
    refine (isPreconnected_range (D.continuous_sheetC n)).union ⟨p, n⟩
      ⟨⟨p, D.mem_C_of_mem_Cp hp⟩, rfl⟩ ⟨⟨p, D.mem_E_of_mem_Cp hp⟩, ?_⟩
      (isPreconnected_range (D.continuous_sheetE n))
    simp [sheetE, D.notMem_Cq_of_mem_Cp hp]
  have hK : ∀ n, (A n ∩ A (Order.succ n)).Nonempty := fun n => by
    refine ⟨⟨q, n⟩, Or.inl ⟨⟨q, D.mem_C_of_mem_Cq hq⟩, rfl⟩,
      Or.inr ⟨⟨q, D.mem_E_of_mem_Cq hq⟩, ?_⟩⟩
    simp [sheetE, hq, Order.succ_eq_add_one]
  have hU : (⋃ n, A n) = univ := by
    refine eq_univ_of_forall fun x => mem_iUnion.2 ⟨x.n, ?_⟩
    by_cases hx : x.pt ∈ D.C
    · exact Or.inl ⟨⟨x.pt, hx⟩, rfl⟩
    · have hE : x.pt ∈ D.E := by_contra fun h => hx (D.mem_C_of_notMem_E h)
      refine Or.inr ⟨⟨x.pt, hE⟩, ?_⟩
      have : x.pt ∉ D.Cq := fun h => hx (D.mem_C_of_mem_Cq h)
      simp [sheetE, this]
  have := IsPreconnected.iUnion_of_chain hA hK
  rw [hU] at this
  exact { isPreconnected_univ := this, toNonempty := ⟨⟨p, 0⟩⟩ }

/-! ### The covering as a `CoveringCode` -/

/-- The bijection of `Z × ℕ` with `D.Space` (labels coded by `Equiv.intEquivNat`). -/
def codeEquiv : (univ : Set (Z × ℕ)) ≃ D.Space where
  toFun x := ⟨x.1.1, Equiv.intEquivNat.symm x.1.2⟩
  invFun x := ⟨(x.pt, Equiv.intEquivNat x.n), mem_univ _⟩
  left_inv x := by simp
  right_inv x := by simp

/-- The topology of the coded covering: transported from `D.Space`. -/
@[reducible] def codeTop : TopologicalSpace (univ : Set (Z × ℕ)) :=
  TopologicalSpace.induced D.codeEquiv inferInstance

/-- The coded covering is homeomorphic to `D.Space`. -/
def codeHomeomorph : @Homeomorph (univ : Set (Z × ℕ)) D.Space D.codeTop _ :=
  @Equiv.toHomeomorphOfIsInducing _ _ D.codeTop _ D.codeEquiv
    (@IsInducing.induced _ _ _ D.codeEquiv)

variable {G : Type u} [Group G]

/-- **The `ℤ`-covering as a covering code** for a trivial action `ρ`. -/
def toCode (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, ρ g = 1) : CoveringCode ρ where
  carrier := univ
  top := D.codeTop
  isCoveringMap := by
    letI := D.codeTop
    exact D.isCoveringMap.comp_homeomorph D.codeHomeomorph
  act := 1
  act_fst g x := by
    rw [hρ g]
    rfl

/-- The deck action on the coded covering. -/
def deckCode (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, ρ g = 1) :
    Multiplicative ℤ →* ((D.toCode ρ hρ).carrier ≃ₜ (D.toCode ρ hρ).carrier) where
  toFun d := letI := D.codeTop
    (D.codeHomeomorph.trans (D.deck d)).trans D.codeHomeomorph.symm
  map_one' := by
    letI := D.codeTop
    ext x : 1
    simp only [map_one, Homeomorph.trans_apply]
    exact D.codeHomeomorph.symm_apply_apply x
  map_mul' d e := by
    letI := D.codeTop
    ext x : 1
    change D.codeHomeomorph.symm (D.deck (d * e) (D.codeHomeomorph x)) =
      D.codeHomeomorph.symm (D.deck d (D.codeHomeomorph
        (D.codeHomeomorph.symm (D.deck e (D.codeHomeomorph x)))))
    rw [Homeomorph.apply_symm_apply, map_mul, Homeomorph.mul_apply]

lemma deckCode_fst (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, ρ g = 1) (d : Multiplicative ℤ)
    (x : (D.toCode ρ hρ).carrier) : (D.deckCode ρ hρ d x).1.1 = x.1.1 :=
  rfl

/-- The deck group acts simply transitively on the fibres of the coded covering. -/
lemma existsUnique_deckCode (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, ρ g = 1)
    {x y : (D.toCode ρ hρ).carrier} (h : x.1.1 = y.1.1) :
    ∃! d : Multiplicative ℤ, D.deckCode ρ hρ d x = y := by
  letI := D.codeTop
  obtain ⟨d, hd, hu⟩ := D.existsUnique_deck (x := D.codeHomeomorph x) (y := D.codeHomeomorph y) h
  refine ⟨d, ?_, fun e he => hu e ?_⟩
  · change D.codeHomeomorph.symm (D.deck d (D.codeHomeomorph x)) = y
    rw [hd]
    exact D.codeHomeomorph.symm_apply_apply y
  · rw [← he]
    change _ = D.codeHomeomorph (D.codeHomeomorph.symm _)
    rw [Homeomorph.apply_symm_apply]
    rfl

/-- The coded covering is connected under the hypotheses of `connectedSpace`. -/
lemma connectedSpace_toCode (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, ρ g = 1)
    (hC : IsPreconnected D.C) (hE : IsPreconnected D.E) (hp : D.Cp.Nonempty)
    (hq : D.Cq.Nonempty) : ConnectedSpace (D.toCode ρ hρ).carrier := by
  letI := D.codeTop
  have := D.connectedSpace hC hE hp hq
  exact D.codeHomeomorph.symm.surjective.connectedSpace D.codeHomeomorph.symm.continuous

end Decomp

end TateCovering

end TemperedFundamentalGroups
