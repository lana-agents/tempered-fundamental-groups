/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TreePoints
import TemperedFundamentalGroups.SemistableReduction.GaussTreeFinite
import TemperedFundamentalGroups.SemistableReduction.AffineTwist

/-!
# Convex Gauss trees as tree data (O8, combinatorial part)

Blueprint §9.12, O8. A convex reduced nonempty finite family of discs `D(aᵢ, |cᵢ|)` of an
algebraically closed non-archimedean field `C` (the input of `gaussJoinModel`, with
`v = NormedField.valuation`) carries the tree structure used by S7's δ-count
(`TreeCount.TreeData`):

* `GaussTree.IsEdge v a c j m`: `D j ⊊ D m` with no disc of the family strictly in between (the
  node charts of `gaussJoinModel` at its node points, `center_lines_eq`);
* `exists_edge_of_lt`: below every vertex `m` and above every smaller disc `D j ⊊ D m` there is an
  edge `(k, m)` with `D j ⊆ D k`;
* `TreeBridge.treeData`: the tree data with the same vertices `(aᵢ, cᵢ)`, the edges `IsEdge`, and
  points `bᵢ` in free residue directions (the residue field of `C` is infinite).

The charts agree (`x = xF C F'` the coordinate of `F' / C(x)`, all identities as subrings of `F'`):

* `edgeChart_eq`: S7's normalized node chart `R'_e` of an edge (integral closure of
  `O_C[x_e, c_e/x_e]` along `X ↦ x_e`) is `normChart F' (nodeChart (coord X a_{χe} c_{πe}) c_e)`,
  the normalization of the `gaussJoinModel` node chart (`IsStandardChart`);
* `map_rint_aff`, `map_drint_aff`: the twisted charts `Rint c' (Aff a c F')` (W7, `IsExhausting`)
  and `DRint 0 1 (Aff a c F')` are the normalizations of `nodeChart (coord X a c) c'` and
  `polyChart (coord X a c)`; `drint_eq`: likewise `DRint a c F'`;
* `isOver_vcoord_iff`, `mem_S_iff`: the vertex set `S` of tree data consists of the type-2
  valuations extending some `w_{aᵢ,|cᵢ|}`; `valuationSubring_mem_vertexSet`: their valuation
  subrings are vertices of `(gaussJoinModel a c).normalization F'`.
-/

open Polynomial IsLocalRing
open scoped NNReal

namespace SemistableReduction

namespace TreeBridge

open GaussTree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

section Norm

lemma norm_sub_le_max (x y z : C) : ‖x - z‖ ≤ max ‖x - y‖ ‖y - z‖ := by
  have := IsUltrametricDist.norm_add_le_max (x - y) (y - z)
  rwa [sub_add_sub_cancel] at this


end Norm

section Free

/-- **Free residue directions**: finitely many points of the closed unit disc leave a point of the
closed unit disc at distance `1` from all of them (the residue field is infinite). -/
lemma exists_far [IsAlgClosed C] (s : Finset C) (hs : ∀ γ ∈ s, ‖γ‖ ≤ 1) :
    ∃ β : C, ‖β‖ ≤ 1 ∧ ∀ γ ∈ s, 1 ≤ ‖β - γ‖ := by
  classical
  haveI := DiscreteCoefficients.isAlgClosed_residueField (F := C)
  let r : C → ResidueField (HenselComplete.integers C) := fun γ ↦
    if h : ‖γ‖ ≤ 1 then residue _ ⟨γ, (HenselComplete.mem_integers_iff γ).2 h⟩ else 0
  obtain ⟨κ, hκ⟩ := Infinite.exists_notMem_finset (s.image r)
  obtain ⟨β, rfl⟩ := residue_surjective κ
  refine ⟨β, HenselComplete.norm_le_one β, fun γ hγ ↦ ?_⟩
  by_contra hlt
  push Not at hlt
  have hγ1 := hs γ hγ
  have : residue _ β = r γ := by
    simp only [r, dif_pos hγ1]
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff,
      HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
    exact hlt
  exact hκ (Finset.mem_image.2 ⟨γ, hγ, this.symm⟩)

end Free

variable {ι : Type*} {a c : ι → C}

/-- Disc inclusion in real norms. -/
lemma discLE_iff {i j : ι} : DiscLE ν a c i j ↔ ‖c i‖ ≤ ‖c j‖ ∧ ‖a i - a j‖ ≤ ‖c j‖ := by
  simp only [DiscLE, NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm]

lemma dle_c {i j : ι} (h : DiscLE ν a c i j) : ‖c i‖ ≤ ‖c j‖ := (discLE_iff.1 h).1

lemma dle_a {i j : ι} (h : DiscLE ν a c i j) : ‖a i - a j‖ ≤ ‖c j‖ := (discLE_iff.1 h).2

/-- A point of `D i` lies in every disc containing `D i`. -/
lemma dle_mem {i j : ι} (h : DiscLE ν a c i j) {z : C} (hz : ‖z - a i‖ ≤ ‖c i‖) :
    ‖z - a j‖ ≤ ‖c j‖ :=
  (norm_sub_le_max z (a i) (a j)).trans (max_le (hz.trans (dle_c h)) (dle_a h))

/-- **Discs are nested or disjoint.** -/
lemma discLE_or_discLE {i j : ι} {z : C} (hi : ‖z - a i‖ ≤ ‖c i‖) (hj : ‖z - a j‖ ≤ ‖c j‖) :
    DiscLE ν a c i j ∨ DiscLE ν a c j i := by
  rcases le_total ‖c i‖ ‖c j‖ with h | h
  · refine .inl (discLE_iff.2 ⟨h, ?_⟩)
    rw [norm_sub_rev] at hi
    exact (norm_sub_le_max (a i) z (a j)).trans (max_le (hi.trans h) hj)
  · refine .inr (discLE_iff.2 ⟨h, ?_⟩)
    rw [norm_sub_rev] at hj
    exact (norm_sub_le_max (a j) z (a i)).trans (max_le (hj.trans h) hi)

omit [IsUltrametricDist C] in
lemma self_mem (i : ι) : ‖a i - a i‖ ≤ ‖c i‖ := by simp

variable (hred : GaussTree.IsReduced ν a c)
include hred

lemma eq_of_discLE_of_norm_eq {i j : ι} (h : DiscLE ν a c i j) (he : ‖c i‖ = ‖c j‖) : i = j :=
  hred i j h (discLE_symm_of_eq h (by
    rw [NormedField.valuation_apply, NormedField.valuation_apply]; exact NNReal.eq he))

/-- A strict inclusion has strictly smaller radius. -/
lemma dle_lt {i j : ι} (h : DiscLE ν a c i j) (hne : i ≠ j) : ‖c i‖ < ‖c j‖ :=
  lt_of_le_of_ne (dle_c h) fun he ↦ hne (eq_of_discLE_of_norm_eq hred h he)

omit hred in
variable (a c) in
/-- An **edge** `(j, m)`: `D j ⊊ D m` with no disc of the family strictly in between. -/
def IsEdge (j m : ι) : Prop :=
  DiscLE ν a c j m ∧ j ≠ m ∧ ∀ k, DiscLE ν a c j k → DiscLE ν a c k m → k = j ∨ k = m

variable [Finite ι]

/-- **Edges below a vertex**: if `D j ⊊ D m`, there is an edge `(k, m)` with `D j ⊆ D k`. -/
lemma exists_edge_of_lt {j m : ι} (h : DiscLE ν a c j m) (hne : j ≠ m) :
    ∃ k, IsEdge a c k m ∧ DiscLE ν a c j k := by
  have hfin : {k | DiscLE ν a c j k ∧ DiscLE ν a c k m ∧ k ≠ m}.Finite := Set.toFinite _
  obtain ⟨k, ⟨hjk, hkm, hkne⟩, hmax⟩ := Set.exists_max_image _ (fun k ↦ ‖c k‖) hfin
    ⟨j, DiscLE.refl j, h, hne⟩
  refine ⟨k, ⟨hkm, hkne, fun l hkl hlm ↦ ?_⟩, hjk⟩
  by_cases hlm' : l = m
  · exact .inr hlm'
  · exact .inl (eq_of_discLE_of_norm_eq hred hkl
      (le_antisymm (dle_c hkl) (hmax l ⟨DiscLE.trans hjk hkl, hlm, hlm'⟩))).symm

/-- **Parents**: a vertex strictly contained in another one is the child of an edge. -/
lemma exists_edge_of_lt' {j m : ι} (h : DiscLE ν a c j m) (hne : j ≠ m) :
    ∃ k, IsEdge a c j k ∧ DiscLE ν a c k m := by
  have hfin : {k | DiscLE ν a c j k ∧ DiscLE ν a c k m ∧ k ≠ j}.Finite := Set.toFinite _
  obtain ⟨k, ⟨hjk, hkm, hkne⟩, hmin⟩ := Set.exists_min_image _ (fun k ↦ ‖c k‖) hfin
    ⟨m, h, DiscLE.refl m, hne.symm⟩
  refine ⟨k, ⟨hjk, hkne.symm, fun l hjl hlk ↦ ?_⟩, hkm⟩
  by_cases hlj : l = j
  · exact .inl hlj
  · exact .inr (eq_of_discLE_of_norm_eq hred hlk
      (le_antisymm (dle_c hlk) (hmin l ⟨hjl, DiscLE.trans hlk hkm, hlj⟩)))

omit hred [Finite ι] in
/-- An edge has a unique parent. -/
lemma IsEdge.eq_par {j m m' : ι} (h : IsEdge a c j m) (h' : IsEdge a c j m') : m = m' := by
  rcases discLE_or_discLE (dle_mem h.1 (self_mem j)) (dle_mem h'.1 (self_mem j)) with hmm | hmm
  · rcases h'.2.2 m h.1 hmm with h1 | h1
    · exact absurd h1.symm h.2.1
    · exact h1
  · rcases h.2.2 m' h'.1 hmm with h1 | h1
    · exact absurd h1.symm h'.2.1
    · exact h1.symm

section Tree

variable (hconv : GaussTree.IsConvex ν a c)
include hconv

omit [Finite ι] in
/-- **Children of a vertex lie in distinct residue directions.** -/
lemma IsEdge.norm_sub_eq {j j' m : ι} (h : IsEdge a c j m) (h' : IsEdge a c j' m)
    (hne : j ≠ j') : ‖a j - a j'‖ = ‖c m‖ := by
  have hle : ‖a j - a j'‖ ≤ ‖c m‖ := by
    rw [norm_sub_rev] at *
    have := norm_sub_le_max (a j') (a m) (a j)
    rw [norm_sub_rev (a m) (a j)] at this
    exact this.trans (max_le (dle_a h'.1) (dle_a h.1))
  refine le_antisymm hle (not_lt.1 fun hlt ↦ ?_)
  obtain ⟨k, hjk, hj'k, hk⟩ := hconv j j'
  have hk' : ‖c k‖ < ‖c m‖ := by
    have : ‖c k‖ ≤ max (max ‖c j‖ ‖c j'‖) ‖a j - a j'‖ := by
      have hk2 : ((ν (c k) : ℝ≥0) : ℝ) ≤ ((max (max (ν (c j)) (ν (c j'))) (ν (a j - a j')) :
          ℝ≥0) : ℝ) := by exact_mod_cast hk
      simpa [NormedField.valuation_apply] using hk2
    exact this.trans_lt (max_lt (max_lt (dle_lt hred h.1 h.2.1) (dle_lt hred h'.1 h'.2.1)) hlt)
  have hkm : DiscLE ν a c k m := by
    rcases discLE_or_discLE (dle_mem hjk (self_mem j)) (dle_mem h.1 (self_mem j)) with h1 | h1
    · exact h1
    · exact absurd (dle_c h1) (not_le.2 hk')
  rcases h.2.2 k hjk hkm with rfl | rfl
  · rcases h'.2.2 _ hj'k h.1 with h2 | h2
    · exact hne h2
    · exact h.2.1 h2
  · exact lt_irrefl _ hk'

end Tree


end TreeBridge

end SemistableReduction

namespace SemistableReduction

namespace TreeBridge

open GaussTree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {a c : ι → C} (hc : ∀ i, c i ≠ 0)

section Free

include hc in
omit [IsAlgClosed C] [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma norm_dir_le {j i : ι} (h : DiscLE ν a c j i) : ‖(a j - a i) / c i‖ ≤ 1 := by
  rw [norm_div, div_le_one (norm_pos_iff.2 (hc i))]
  exact dle_a h

include hc in
omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
lemma exists_freeDir [Finite ι] (i : ι) : ∃ β : C, ‖β‖ ≤ 1 ∧
    ∀ j, IsEdge a c j i → 1 ≤ ‖β - (a j - a i) / c i‖ := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨β, hβ, h⟩ := exists_far ((Finset.univ.filter fun j ↦ IsEdge a c j i).image
    fun j ↦ (a j - a i) / c i) (by
      intro γ hγ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hγ
      exact norm_dir_le hc (Finset.mem_filter.1 hj).2.1)
  exact ⟨β, hβ, fun j hj ↦ h _ (Finset.mem_image.2 ⟨j, Finset.mem_filter.2
    ⟨Finset.mem_univ _, hj⟩, rfl⟩)⟩

variable (a c) in
/-- The free residue direction of a vertex: a point `β` of the unit disc in a residue class of the
coordinate `(x - aᵢ)/cᵢ` containing no child. -/
noncomputable def freeDir (i : ι) : C := Classical.choose (exists_freeDir (a := a) hc i)

omit [DecidableEq ι] [Nonempty ι] in
lemma freeDir_spec (i : ι) : ‖freeDir a c hc i‖ ≤ 1 ∧
    ∀ j, IsEdge a c j i → 1 ≤ ‖freeDir a c hc i - (a j - a i) / c i‖ :=
  Classical.choose_spec (exists_freeDir (a := a) hc i)

variable (a c) in
/-- The point `bᵢ = aᵢ + cᵢ β` in the free direction of the vertex `i`. -/
noncomputable def freePt (i : ι) : C := a i + c i * freeDir a c hc i

omit [DecidableEq ι] [Nonempty ι] in
lemma norm_freePt_sub (i : ι) : ‖freePt a c hc i - a i‖ ≤ ‖c i‖ := by
  rw [freePt, add_sub_cancel_left, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (freeDir_spec hc i).1

omit [DecidableEq ι] [Nonempty ι] in
lemma norm_freePt_sub_child {j i : ι} (h : IsEdge a c j i) :
    ‖freePt a c hc i - a j‖ = ‖c i‖ := by
  have hci : c i ≠ 0 := hc i
  have heq : freePt a c hc i - a j = c i * (freeDir a c hc i - (a j - a i) / c i) := by
    rw [freePt, mul_sub, mul_div_cancel₀ _ hci]
    ring
  rw [heq, norm_mul]
  have h1 := (freeDir_spec hc i).2 j h
  have h2 : ‖freeDir a c hc i - (a j - a i) / c i‖ ≤ 1 := by
    have := norm_sub_le_max (freeDir a c hc i) 0 ((a j - a i) / c i)
    rw [sub_zero, zero_sub, norm_neg] at this
    exact this.trans (max_le (freeDir_spec hc i).1 (norm_dir_le hc h.1))
  rw [le_antisymm h2 h1, mul_one]

end Free

section Data

variable (hconv : GaussTree.IsConvex ν a c) (hred : GaussTree.IsReduced ν a c)

include hred in
omit [DecidableEq ι] [Nonempty ι] in
/-- Every point of the free direction of a vertex `j` lying in a disc `D i`, `i ≠ j`, lies in the
residue class of a child of `i`. -/
lemma freePt_dir {i j : ι} (hji : j ≠ i) (h : ‖freePt a c hc j - a i‖ ≤ ‖c i‖) :
    ∃ k, IsEdge a c k i ∧ ‖freePt a c hc j - a k‖ < ‖c i‖ := by
  rcases discLE_or_discLE (norm_freePt_sub hc j) h with hle | hle
  · obtain ⟨k, hk, hjk⟩ := exists_edge_of_lt hred hle hji
    exact ⟨k, hk, (dle_mem hjk (norm_freePt_sub hc j)).trans_lt (dle_lt hred hk.1 hk.2.1)⟩
  · obtain ⟨k, hk, hik⟩ := exists_edge_of_lt hred hle (Ne.symm hji)
    have h1 := dle_mem hik h
    have h2 := norm_freePt_sub_child hc hk
    exact absurd (h2 ▸ h1) (not_le.2 (dle_lt hred hk.1 hk.2.1))

include hconv hred in
omit [DecidableEq ι] in
/-- The root (the vertex without parent) contains all points `bⱼ`. -/
lemma freePt_root {i : ι} (hi : ∀ m, ¬ IsEdge a c i m) (j : ι) :
    ‖freePt a c hc j - a i‖ ≤ ‖c i‖ := by
  obtain ⟨ρ, hρ⟩ := exists_root hconv hred
  have hiρ : i = ρ := by
    by_contra hne
    obtain ⟨k, hk, -⟩ := exists_edge_of_lt' hred (hρ i) hne
    exact hi k hk
  subst hiρ
  exact dle_mem (hρ j) (norm_freePt_sub hc j)

include hconv hred in
omit [DecidableEq ι] [Nonempty ι] in
/-- No point `bₗ` lies in the open annulus of an edge. -/
lemma freePt_edge {j m : ι} (he : IsEdge a c j m) (l : ι) :
    ‖freePt a c hc l - a j‖ ≤ ‖c j‖ ∨ ‖c m‖ ≤ ‖freePt a c hc l - a j‖ := by
  set z := freePt a c hc l
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have hzl : ‖z - a l‖ ≤ ‖c l‖ := norm_freePt_sub hc l
  have hzm : ‖z - a m‖ ≤ ‖c m‖ :=
    (norm_sub_le_max z (a j) (a m)).trans (max_le h2.le (dle_a he.1))
  rcases discLE_or_discLE hzl hzm with hlm | hml
  · by_cases hlm' : l = m
    · subst hlm'
      exact absurd (norm_freePt_sub_child hc he) h2.ne
    · -- the join of `l` and `j` lies strictly between `j` and `m`
      have hcl := dle_lt hred hlm hlm'
      obtain ⟨k, hlk, hjk, hk⟩ := hconv l j
      have hlj : ‖a l - a j‖ < ‖c m‖ := by
        have := norm_sub_le_max (a l) z (a j)
        rw [norm_sub_rev (a l) z] at this
        exact this.trans_lt (max_lt (hzl.trans_lt hcl) h2)
      have hk' : ‖c k‖ < ‖c m‖ := by
        have : ‖c k‖ ≤ max (max ‖c l‖ ‖c j‖) ‖a l - a j‖ := by
          have hk2 : ((ν (c k) : ℝ≥0) : ℝ) ≤ ((max (max (ν (c l)) (ν (c j))) (ν (a l - a j)) :
              ℝ≥0) : ℝ) := by exact_mod_cast hk
          simpa [NormedField.valuation_apply] using hk2
        exact this.trans_lt (max_lt (max_lt hcl (dle_lt hred he.1 he.2.1)) hlj)
      have hkm : DiscLE ν a c k m := by
        rcases discLE_or_discLE (dle_mem hjk (self_mem j)) (dle_mem he.1 (self_mem j)) with
          h3 | h3
        · exact h3
        · exact absurd (dle_c h3) (not_le.2 hk')
      rcases he.2.2 k hjk hkm with rfl | rfl
      · exact absurd (dle_mem hlk hzl) (not_le.2 h1)
      · exact lt_irrefl _ hk'
  · by_cases hml' : m = l
    · subst hml'
      exact absurd (norm_freePt_sub_child hc he) h2.ne
    · obtain ⟨k, hk, hmk⟩ := exists_edge_of_lt hred hml hml'
      have h3 : ‖z - a k‖ ≤ ‖c k‖ := by
        have hjk := dle_a (DiscLE.trans he.1 hmk)
        exact (norm_sub_le_max z (a j) (a k)).trans
          (max_le (h2.le.trans (dle_c hmk)) hjk)
      have h4 := norm_freePt_sub_child hc hk
      exact absurd (h4 ▸ h3) (not_le.2 (dle_lt hred hk.1 hk.2.1))

open Classical in
variable (a c) in
/-- **O8: the tree data of a convex reduced Gauss tree.** The vertices are the discs
`D(aᵢ, |cᵢ|)` of the family, the edges the minimal strict inclusions `D j ⊊ D m` (`IsEdge`), and
the free points `bᵢ = aᵢ + cᵢ βᵢ` (`freePt`). -/
noncomputable def treeData : TreeCount.TreeData C where
  ι := ι
  E := {p : ι × ι // IsEdge a c p.1 p.2}
  a := a
  c := c
  b := freePt a c hc
  par e := e.1.2
  chi e := e.1.1
  hc := hc
  hred i j h1 h2 := eq_of_discLE_of_norm_eq hred (discLE_iff.2 ⟨h1.le, h1 ▸ h2⟩) h1
  hedge_c e := dle_lt hred e.2.1 e.2.2.1
  hedge_a e := dle_a e.2.1
  hchi e e' h := by
    have hp := IsEdge.eq_par e.2 (h ▸ e'.2)
    exact Subtype.ext (Prod.ext h hp)
  hdir e e' h hne := by
    refine IsEdge.norm_sub_eq hred hconv e.2 (h ▸ e'.2) fun hc' ↦ hne ?_
    exact Subtype.ext (Prod.ext hc' h)
  hb_mem := norm_freePt_sub hc
  hb_free e := norm_freePt_sub_child hc e.2
  hb_dir i j hji h := by
    obtain ⟨k, hk, hlt⟩ := freePt_dir hc hred hji h
    exact ⟨⟨(k, i), hk⟩, rfl, hlt⟩
  hroot i hi j := freePt_root hc hconv hred (fun m hm ↦ hi ⟨(i, m), hm⟩ rfl) j
  hb_edge e l := freePt_edge hc hconv hred e.2 l

@[simp] lemma treeData_ι : (treeData a c hc hconv hred).ι = ι := rfl

@[simp] lemma treeData_a : (treeData a c hc hconv hred).a = a := rfl

@[simp] lemma treeData_c : (treeData a c hc hconv hred).c = c := rfl

lemma treeData_isEdge (e : (treeData a c hc hconv hred).E) :
    IsEdge a c ((treeData a c hc hconv hred).chi e) ((treeData a c hc hconv hred).par e) :=
  e.2

/-- Every edge of the family is an edge of the tree data. -/
lemma exists_edge_treeData {j m : ι} (h : IsEdge a c j m) :
    ∃ e : (treeData a c hc hconv hred).E,
      (treeData a c hc hconv hred).chi e = j ∧ (treeData a c hc hconv hred).par e = m :=
  ⟨⟨(j, m), h⟩, rfl, rfl⟩

end Data

end TreeBridge

end SemistableReduction

/-! ### The charts -/

namespace SemistableReduction

namespace TreeBridge

open ZariskiModel GaussTree GaussTube GaussFibre AffineTwist TreeCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

set_option hygiene false in
local notation "ν" => NormedField.valuation (K := C)

section Map

variable {a c : C} (hc0 : c ≠ 0)

include hc0 in
/-- The twist `x ↦ (x - a)/c` maps the node chart `O_C[x, c'/x]` onto the node chart
`O_C[t, c'/t]`, `t = (x - a)/c`. -/
lemma map_nodeRing_affHom (c' : C) :
    (nodeRing c').map (affHom a c hc0).toRingHom =
      nodeChart ν (coord (RatFunc.X : RatFunc C) a c) c' := by
  rw [nodeRing, nodeChart, nodeChart, RingHom.map_closure, Set.image_union]
  congr 2
  · ext f
    simp only [baseRing, Subring.coe_map, Set.mem_image]
    constructor
    · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
      exact ⟨o, ho, ((affHom a c hc0).commutes o).symm⟩
    · rintro ⟨o, ho, rfl⟩
      exact ⟨_, ⟨o, ho, rfl⟩, (affHom a c hc0).commutes o⟩
  · rw [Set.image_insert_eq, Set.image_singleton]
    have hX : (affHom a c hc0).toRingHom RatFunc.X = coord (RatFunc.X : RatFunc C) a c := by
      change affHom a c hc0 RatFunc.X = _
      rw [affHom_X, gaussCoord_eq_coord hc0]
    rw [hX]
    congr 2
    change affHom a c hc0 (algebraMap C (RatFunc C) c' / RatFunc.X) = _
    rw [map_div₀, AlgHom.commutes, affHom_X, gaussCoord_eq_coord hc0]

end Map

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F']

/-- The coordinate algebra map of `(x - a)/c` is the twist followed by the structure map. -/
lemma coordAlgHom_vcoord {a c : C} (hc0 : c ≠ 0)
    (h : Transcendental C (vcoord (xF C F') a c)) :
    coordAlgHom h = (IsScalarTower.toAlgHom C (RatFunc C) F').comp (affHom a c hc0) := by
  refine ratFunc_algHom_ext ?_
  rw [coordAlgHom_X, AlgHom.comp_apply, affHom_X, gaussCoord_eq_coord hc0,
    IsScalarTower.coe_toAlgHom', coord, vcoord, map_div₀, map_sub, xF,
    IsScalarTower.algebraMap_apply C (RatFunc C) F',
    IsScalarTower.algebraMap_apply C (RatFunc C) F']

/-- The structure map composed with the twist, on subrings. -/
lemma map_nodeRing_coordAlgHom {a c : C} (hc0 : c ≠ 0)
    (h : Transcendental C (vcoord (xF C F') a c)) (c' : C) :
    (nodeRing c').map (coordAlgHom h).toRingHom =
      (nodeChart ν (coord (RatFunc.X : RatFunc C) a c) c').map (algebraMap (RatFunc C) F') := by
  rw [coordAlgHom_vcoord hc0 h, ← map_nodeRing_affHom hc0, Subring.map_map]
  rfl

variable (T : TreeData C)

/-- **O8, node charts.** The normalized node chart `R'_e` of an edge `e` of tree data over the
coordinate `x` of `F'` (S7: integral closure of `O_C[x_e, c_e/x_e]`, `x_e = (x - a_{χe})/c_{πe}`)
is the normalization in `F'` of the node chart `O_C[u, c_e/u]`, `u = (x - a_{χe})/c_{πe}`, of
`gaussJoinModel` (`IsStandardChart`). -/
theorem edgeChart_eq (e : T.E) :
    (letI := T.edgeAlg (transcendental_xF (C := C) (F := F')) e
     (Rint (T.ce e) F').toSubring) =
      normChart F' (nodeChart ν (coord (RatFunc.X : RatFunc C) (T.a (T.chi e)) (T.c (T.par e)))
        (T.ce e)) := by
  have key := map_nodeRing_coordAlgHom (F' := F') (T.hc (T.par e))
    (T.hec transcendental_xF e) (T.ce e)
  letI := T.edgeAlg (transcendental_xF (C := C) (F := F')) e
  refine (integralClosure_toSubring_eq (F' := F') (nodeRing (T.ce e))).trans ?_
  exact congrArg (fun S : Subring F' ↦ (integralClosure S F').toSubring) key

section Twist

variable {a c : C} (hc0 : c ≠ 0)

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- The integral closure of a subring `A ⊆ C(x)` in the twist `Aff a c F'` (where `x` acts as
`(x - a)/c`) is, as a subring of `F'`, the integral closure of the twisted subring. -/
lemma map_integralClosure_aff (A : Subring (RatFunc C)) :
    (integralClosure A (Aff a c hc0 F')).toSubring.map (toAff hc0).symm.toRingHom =
      (integralClosure ((A.map (affHom a c hc0).toRingHom).map (algebraMap (RatFunc C) F'))
        F').toSubring := by
  set φ : RatFunc C →+* F' := (algebraMap (RatFunc C) F').comp (affHom a c hc0).toRingHom
  have hφ : Function.Injective φ :=
    (algebraMap (RatFunc C) F').injective.comp (affHom a c hc0).toRingHom.injective
  have hB : (A.map (affHom a c hc0).toRingHom).map (algebraMap (RatFunc C) F') = A.map φ :=
    Subring.map_map _ _ _
  rw [hB]
  set e : A ≃+* A.map φ := A.equivMapOfInjective φ hφ
  ext y
  simp only [Subring.mem_map, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact IsIntegral.map_of_comp_eq e.toRingHom (toAff hc0).symm.toRingHom
      (RingHom.ext fun _ ↦ rfl) hz
  · intro hy
    refine ⟨toAff hc0 y, ?_, rfl⟩
    refine IsIntegral.map_of_comp_eq e.symm.toRingHom (toAff hc0).toRingHom
      (RingHom.ext fun b ↦ ?_) hy
    change toAff hc0 (φ (e.symm b : RatFunc C)) = toAff hc0 (b : F')
    congr 1
    have := Subring.coe_equivMapOfInjective_apply A φ hφ (e.symm b)
    rw [← this]
    exact congrArg Subtype.val (e.apply_symm_apply b)

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- **O8, node charts in the twisted form** (`AffineTwist.IsExhausting`, W7): the normalized node
chart `Rint c' (Aff a c F')` of `O_C[t, c'/t]`, `t = (x - a)/c`, is, as a subring of `F'`, the
normalization of the `gaussJoinModel` node chart `nodeChart (coord x a c) c'`. -/
theorem map_rint_aff (c' : C) :
    (Rint c' (Aff a c hc0 F')).toSubring.map (toAff hc0).symm.toRingHom =
      normChart F' (nodeChart ν (coord (RatFunc.X : RatFunc C) a c) c') := by
  rw [map_integralClosure_aff, map_nodeRing_affHom]
  rfl

lemma map_discRing_affHom :
    (DiscCount.discRing (0 : C) 1).map (affHom a c hc0).toRingHom =
      polyChart ν (coord (RatFunc.X : RatFunc C) a c) := by
  rw [← gaussCoord_eq_coord hc0]
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact (aff_mem_discRing_iff (a := a) hc0).2 hg
  · intro hf
    refine ⟨(aff a c hc0).symm f, (aff_mem_discRing_iff (a := a) hc0).1 ?_, ?_⟩
    · rwa [AlgEquiv.apply_symm_apply]
    · exact (aff a c hc0).apply_symm_apply f

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- **O8, vertex charts in the twisted form**: the normalized vertex chart `DRint 0 1 (Aff a c F')`
is the normalization of the `gaussJoinModel` line chart `O[(x - a)/c]`. -/
theorem map_drint_aff :
    (DiscCount.DRint (0 : C) 1 (Aff a c hc0 F')).toSubring.map (toAff hc0).symm.toRingHom =
      normChart F' (polyChart ν (coord (RatFunc.X : RatFunc C) a c)) := by
  rw [map_integralClosure_aff, map_discRing_affHom]
  rfl

include hc0 in
omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- **O8, vertex charts**: `DRint a c F'` is the normalization of `O[(x - a)/c]`. -/
theorem drint_eq :
    (DiscCount.DRint a c F').toSubring =
      normChart F' (polyChart ν (coord (RatFunc.X : RatFunc C) a c)) := by
  rw [← gaussCoord_eq_coord hc0]
  exact integralClosure_toSubring_eq _

/-- `C`-algebra endomorphisms of `C(x)` map line charts to line charts. -/
lemma map_polyChart_algHom (f : RatFunc C →ₐ[C] RatFunc C) (y : RatFunc C) :
    (polyChart ν y).map f.toRingHom = polyChart ν (f y) := by
  rw [polyChart, polyChart, RingHom.map_closure, Set.image_union, Set.image_singleton]
  congr 2
  ext g
  simp only [baseRing, Subring.coe_map, Set.mem_image]
  constructor
  · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
    exact ⟨o, ho, (f.commutes o).symm⟩
  · rintro ⟨o, ho, rfl⟩
    exact ⟨_, ⟨o, ho, rfl⟩, f.commutes o⟩

omit [IsUltrametricDist C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- **Integral closures in twisted fields.** If `e : G ≃+* F'` turns the `C(x)`-structure of `G`
into that of `F'` precomposed with `ψ`, then `e` maps the integral closure of `A` in `G` onto the
integral closure of the twisted subring `ψ(A)` in `F'`. -/
lemma map_integralClosure_twist {G : Type*} [Field G] [Algebra (RatFunc C) G] (e : G ≃+* F')
    (ψ : RatFunc C →+* RatFunc C)
    (he : ∀ φ, e (algebraMap (RatFunc C) G φ) = algebraMap (RatFunc C) F' (ψ φ))
    (A : Subring (RatFunc C)) :
    (integralClosure A G).toSubring.map e.toRingHom =
      (integralClosure ((A.map ψ).map (algebraMap (RatFunc C) F')) F').toSubring := by
  set φ : RatFunc C →+* F' := (algebraMap (RatFunc C) F').comp ψ
  have hφ : Function.Injective φ := (algebraMap (RatFunc C) F').injective.comp ψ.injective
  rw [Subring.map_map]
  set eA : A ≃+* A.map φ := A.equivMapOfInjective φ hφ
  ext y
  simp only [Subring.mem_map, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact IsIntegral.map_of_comp_eq eA.toRingHom e.toRingHom
      (RingHom.ext fun b ↦ (he b).symm) hz
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    refine IsIntegral.map_of_comp_eq eA.symm.toRingHom e.symm.toRingHom
      (RingHom.ext fun b ↦ ?_) hy
    change algebraMap (RatFunc C) G (eA.symm b : RatFunc C) = e.symm (b : F')
    rw [← e.symm_apply_apply (algebraMap (RatFunc C) G _), he]
    congr 1
    have := Subring.coe_equivMapOfInjective_apply A φ hφ (eA.symm b)
    rw [show algebraMap (RatFunc C) F' (ψ (eA.symm b : RatFunc C)) = φ (eA.symm b) from rfl,
      ← this]
    exact congrArg Subtype.val (eA.apply_symm_apply b)

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- **O8, the chart at `∞` of a vertex**: the normalized vertex chart of the inversion of the
twist, `DRint 0 1 (Inv 1 (Aff a c F'))` (coordinate `c/(x - a)`), is the normalization of the
`gaussJoinModel` line chart `O[((x - a)/c)⁻¹]`. -/
theorem map_drint_inv_aff :
    (DiscCount.DRint (0 : C) 1 (GaussTube.Inv (1 : C) one_ne_zero (Aff a c hc0 F'))).toSubring.map
        ((GaussTube.toInv (c := (1 : C)) one_ne_zero (F' := Aff a c hc0 F')).symm.trans
          (toAff hc0).symm).toRingHom =
      normChart F' (polyChart ν (coord (RatFunc.X : RatFunc C) a c)⁻¹) := by
  rw [map_integralClosure_twist _ ((affHom a c hc0).toRingHom.comp
    (GaussTube.invHom (c := (1 : C)) one_ne_zero).toRingHom) (fun φ ↦ rfl),
    ← Subring.map_map, map_polyChart_algHom, map_polyChart_algHom]
  have hy : affHom a c hc0 (GaussTube.invHom (c := (1 : C)) one_ne_zero (gaussCoord (0 : C) 1)) =
      (coord (RatFunc.X : RatFunc C) a c)⁻¹ := by
    rw [SmoothVertex.gaussCoord_zero_one, GaussTube.invHom_X, map_one, map_div₀, map_one,
      affHom_X, gaussCoord_eq_coord hc0, one_div]
  rw [hy]
  rfl
end Twist

section Vertices

variable [IsAlgClosed C]

/-- **O8, vertices**: a type-2 valuation lies over the Gauss point of the vertex coordinate
`(x - aᵢ)/cᵢ` iff it extends the Gauss valuation `w_{aᵢ,|cᵢ|}` of `C(x)`. -/
theorem isOver_vcoord_iff {a c : C} (hc0 : c ≠ 0) (h : Transcendental C (vcoord (xF C F') a c))
    (W : TypeTwo C F') :
    IsOver h W ↔ W.val.comap (algebraMap (RatFunc C) F') =
      gaussRat ν a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0)) := by
  have hW : W.val.comap (coordAlgHom h).toRingHom =
      (W.val.comap (algebraMap (RatFunc C) F')).comap (aff a c hc0).toRingEquiv.toRingHom := by
    rw [coordAlgHom_vcoord hc0 h]
    exact Valuation.ext fun φ ↦ rfl
  rw [IsOver, hW]
  constructor
  · intro h1
    ext φ
    have := congrArg (fun w : Valuation (RatFunc C) ℝ≥0 ↦ w ((aff a c hc0).symm φ)) h1
    simp only [Valuation.comap_apply] at this
    rw [← gauss1_aff_symm hc0, ← this]
    simp
  · intro h1
    ext φ
    rw [Valuation.comap_apply, h1,
      show (aff a c hc0).toRingEquiv.toRingHom φ = aff a c hc0 φ from rfl, gaussRat_aff]

variable [CharZero C] [IsCurveFunctionField C F'] [FiniteDimensional (RatFunc C) F']
  {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

omit [FiniteDimensional (RatFunc C) F'] in
/-- **O8, vertex sets**: the vertex set `S` of tree data over the coordinate `x` of `F'` consists of
the type-2 valuations extending one of the Gauss valuations `w_{aᵢ,|cᵢ|}`. -/
theorem mem_S_iff (W : TypeTwo C F') :
    W ∈ T.S transcendental_xF hp hp1 ↔ ∃ i, W.val.comap (algebraMap (RatFunc C) F') =
      gaussRat ν (T.a i) (Units.mk0 ‖T.c i‖₊ (nnnorm_ne_zero_iff.2 (T.hc i))) := by
  rw [T.mem_S]
  exact exists_congr fun i ↦ isOver_vcoord_iff (T.hc i) _ W

/-- **O8, vertex sets**: the valuation subrings of the vertex set `S` of tree data are vertices
of the normalization of `gaussJoinModel` in `F'`. -/
theorem valuationSubring_mem_vertexSet {W : TypeTwo C F'} (hW : W ∈ T.S transcendental_xF hp hp1) :
    W.val.valuationSubring ∈
      ((gaussJoinModel ν T.a T.c).normalization F').vertexSet := by
  haveI : Algebra.IsAlgebraic (RatFunc C) F' := Algebra.IsAlgebraic.of_finite _ _
  rw [gaussJoinModel_normalization_vertexSet (r := fun i ↦ Units.mk0 ‖T.c i‖₊
    (nnnorm_ne_zero_iff.2 (T.hc i))) fun i ↦ rfl]
  obtain ⟨i, hi⟩ := (mem_S_iff T hp hp1 W).1 hW
  refine ⟨i, ?_⟩
  rw [← hi]
  ext x
  simp

end Vertices

end TreeBridge

end SemistableReduction
