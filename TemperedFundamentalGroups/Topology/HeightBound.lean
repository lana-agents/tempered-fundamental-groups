/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Topology.HeightLength

/-!
# Heights are bounded (Blueprint §10.3.8, I7)

The height `dN w ν b` of a component vertex `b` of the tree covering only depends on the
label of `b`: walks of the tree project to walks of the incidence graph with the same weight
(`sum_labW`), and walks of the incidence graph lift to the tree from every vertex with the
right label (`exists_pWalk_labW`). Hence, for finitely many components, finite weights and some
component vertex labelled in `ν`, the heights are bounded by a finite constant
(`CurveConfig.exists_dN_le`), and the height-corrected length condition `HC … ℓ` bounds the tree
length by `ℓ + 2M` (`CurveConfig.tlen_le_of_hc_of_le`).
-/

universe u v

open Set
open scoped ENNReal

namespace TemperedFundamentalGroups

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- Every component vertex has a walk to every other component vertex. -/
lemma exists_pWalk_of_isComp {a b : K.Tree r} (ha : IsComp a) (hb : IsComp b) :
    ∃ L, PWalk a L ∧ pend a L = b := by
  obtain ⟨⟨L₁, h₁, e₁, -⟩, -⟩ := exists_pWalk_root _ a le_rfl ha
  obtain ⟨-, ⟨L₂, h₂, e₂, -⟩⟩ := exists_pWalk_root _ b le_rfl hb
  exact ⟨L₁ ++ L₂, pWalk_append.2 ⟨h₁, e₁ ▸ h₂⟩, by rw [pend_append, e₁, e₂]⟩

/-- **The height only depends on the label**: a walk from a component vertex `b₀` to a vertex
labelled in `ν` bounds the height of every component vertex with the label of `b₀`. -/
lemma dN_le_of_lab (w : Z → ℝ≥0∞) (ν : ι → Prop) {b b₀ : K.Tree r} (hb : IsComp b)
    (hb₀ : IsComp b₀) (hlab : lab b = lab b₀) {L : List (K.Tree r × K.Tree r)}
    (hL : PWalk b₀ L) (hν : ν (lab (pend b₀ L))) : dN w ν b ≤ cost w L := by
  obtain ⟨T, hT, hTL⟩ := exists_pWalk_labW (labW L) hb (hlab ▸ incWalk_labW hb₀ hL)
  have hlast : lab (pend b T) = lab (pend b₀ L) := by
    rw [← lastLab_labW, ← lastLab_labW, hTL, hlab]
  refine (dN_le w ν hT (hT.isComp_pend hb) (hlast ▸ hν)).trans_eq ?_
  rw [← sum_labW w hb hT, ← sum_labW w hb₀ hL, hTL]

/-- **Heights are bounded** (finitely many components, finite weights, and some component vertex
labelled in `ν`). -/
lemma exists_dN_le [Finite ι] {w : Z → ℝ≥0∞} (hw : ∀ z, w z ≠ ⊤) (ν : ι → Prop) {t₁ : K.Tree r}
    (ht₁ : IsComp t₁) (hν₁ : ν (lab t₁)) :
    ∃ M : ℝ≥0∞, M ≠ ⊤ ∧ ∀ b : K.Tree r, IsComp b → dN w ν b ≤ M := by
  classical
  haveI := Fintype.ofFinite ι
  have hwalk : ∀ i, ∃ c : ℝ≥0∞, c ≠ ⊤ ∧
      ∀ b : K.Tree r, IsComp b → lab b = i → dN w ν b ≤ c := by
    intro i
    by_cases h : ∃ b₀ : K.Tree r, IsComp b₀ ∧ lab b₀ = i
    · obtain ⟨b₀, hb₀, hi⟩ := h
      obtain ⟨L, hL, hLe⟩ := exists_pWalk_of_isComp hb₀ ht₁
      refine ⟨cost w L, cost_ne_top hw L, fun b hb hbi => ?_⟩
      exact dN_le_of_lab w ν hb hb₀ (hbi.trans hi.symm) hL (hLe ▸ hν₁)
    · exact ⟨0, ENNReal.zero_ne_top, fun b hb hbi => absurd ⟨b, hb, hbi⟩ h⟩
  choose c hc hcb using hwalk
  refine ⟨Finset.univ.sup c, ?_, fun b hb => (hcb _ b hb rfl).trans
    (Finset.le_sup (f := c) (Finset.mem_univ _))⟩
  exact ((Finset.sup_lt_iff ENNReal.zero_lt_top).2 fun i _ => (hc i).lt_top).ne

/-- `HC … ℓ` bounds the tree length by `ℓ + 2M` for heights bounded by `M`. -/
lemma tlen_le_of_hc_of_le {w : Z → ℝ≥0∞} {ν : ι → Prop} {a c : K.Tree r} {ℓ M : ℝ≥0∞}
    (h : HC w ν a c ℓ) (hM : ∀ b : K.Tree r, IsComp b → dN w ν b ≤ M) :
    tlen w a c ≤ ℓ + (M + M) :=
  tlen_le_of_hc h fun _ _ hb hb' => add_le_add (hM _ hb.isComp) (hM _ hb'.isComp)

end CurveConfig

end TemperedFundamentalGroups
