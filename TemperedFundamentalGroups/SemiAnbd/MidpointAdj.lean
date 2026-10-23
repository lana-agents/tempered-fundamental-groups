/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemiAnbd.TreeTowerCompact

/-!
# The restricted edge hypothesis for `PSCAdj` (Blueprint M2.6)

`TreeTower.pscAdj_of_estranged` consumes `hedge` (all eventually-edge-kind systems have
nontrivial stabilizers) only through `adjG_of_limAdj`, i.e. only for the midpoint systems of two
verticial systems adjacent in the limit tree. The hypothesis that M2.6 has to discharge is
therefore exactly the reverse half of `PSCAdj`:

`LimAdjInf T : ∀ s s', IsVert s → IsVert s' → LimAdj s s' → stab s ⊓ stab s' ≠ ⊥`.

`limAdjInf_of_mid`: it suffices that every midpoint system of two such systems (adjacent to both
wherever they differ) has a nontrivial stabilizer.
-/

open CategoryTheory

namespace TemperedFundamentalGroups.TreeTower

variable {Γ : Type*} [Group Γ] {J : Type*} [Category J] {T : TreeTower Γ J}

variable (T) in
/-- **The restricted edge hypothesis**: two verticial systems adjacent in the limit tree have
stabilizers with nontrivial intersection (equivalently, by W2 and `NoBranchSwap`, the midpoint
system has a nontrivial stabilizer). -/
def LimAdjInf : Prop :=
  ∀ s s' : T.Sys, IsVert s → IsVert s' → LimAdj s s' → stab s ⊓ stab s' ≠ ⊥

/-- `hedge` implies the restricted form (W11). -/
theorem limAdjInf_of_hedge [IsCofilteredOrEmpty J] (hT : T.IsFunctorial) (hB : T.NoBranchSwap)
    (hedge : ∀ e : T.Sys, (∀ j, ∃ (k : J) (_ : k ⟶ j), T.kind k (e.1 k) = false) → stab e ≠ ⊥) :
    T.LimAdjInf :=
  fun _ _ hs hs' h ↦ (adjG_of_limAdj hT hB hedge hs hs' h).2

/-- **`PSCAdj` from estrangement and the restricted edge hypothesis** (no functoriality and no
`NoBranchSwap` needed at this point). -/
theorem pscAdj_of_estranged_of_limAdjInf (hE : T.Estranged) (hL : T.LimAdjInf) : T.PSCAdj :=
  fun s s' ↦ ⟨limAdj_of_adjG hE, fun h ↦ ⟨h.1, hL s.1 s'.1 s.2.1 s'.2.1 h⟩⟩

/-- `LimAdjInf` from nontrivial stabilizers of the midpoint systems. -/
theorem limAdjInf_of_mid [IsCofilteredOrEmpty J] (hT : T.IsFunctorial) (hB : T.NoBranchSwap)
    (hmid' : ∀ s s' e : T.Sys, IsVert s → IsVert s' → LimAdj s s' →
      (∀ k, s.1 k ≠ s'.1 k → (T.graph k).Adj (s.1 k) (e.1 k) ∧
        (T.graph k).Adj (e.1 k) (s'.1 k)) → stab e ≠ ⊥) :
    T.LimAdjInf := by
  classical
  intro s s' hs hs' h
  obtain ⟨j₀, hj₀⟩ : ∃ j, s.1 j ≠ s'.1 j := by
    by_contra! hc; exact h.1 (Sys.ext hc)
  let D : J → Prop := fun k ↦ s.1 k ≠ s'.1 k
  have hD2 : ∀ k, D k → (T.graph k).dist (s.1 k) (s'.1 k) = 2 := fun k hk ↦
    dist_eq_two (hs k) (hs' k) hk (h.2 k)
  have hDdeep : ∀ j, ∃ (k : J) (_ : k ⟶ j), D k := fun j ↦ by
    obtain ⟨W, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs j j₀
    exact ⟨W, a, ne_of_ne b hj₀⟩
  have hDmap : ∀ {k l : J} (_ : l ⟶ k), D k → D l := fun f hk ↦ ne_of_ne f hk
  let mid : ∀ k, D k → T.V k := fun k hk ↦ (exists_midpoint (hD2 k hk)).choose
  have hmid : ∀ k (hk : D k), (T.graph k).dist (s.1 k) (mid k hk) = 1 ∧
      (T.graph k).dist (mid k hk) (s'.1 k) = 1 := fun k hk ↦
    (exists_midpoint (hD2 k hk)).choose_spec
  have hmap : ∀ {k l : J} (f : l ⟶ k) (hl : D l) (hk : D k), T.map f (mid l hl) = mid k hk := by
    intro k l f hl hk
    refine eq_of_midpoint (hD2 k hk) (hmid k hk) ⟨?_, ?_⟩
    · rw [← s.2 f]; exact (T.dist_map_le f _ _).trans (hmid l hl).1.le
    · rw [← s'.2 f]; exact (T.dist_map_le f _ _).trans (hmid l hl).2.le
  let lev : ∀ j, Σ' (k : J) (_ : k ⟶ j), D k := fun j ↦
    ⟨(hDdeep j).choose, (hDdeep j).choose_spec.choose, (hDdeep j).choose_spec.choose_spec⟩
  let e : T.Sys := ⟨fun j ↦ T.map (lev j).2.1 (mid _ (lev j).2.2), fun {j j'} h ↦ by
    obtain ⟨W, a, b, hab⟩ := exists_cone_eq ((lev j).2.1 ≫ h) (lev j').2.1
    have hW : D W := hDmap a (lev j).2.2
    change T.map h (T.map (lev j).2.1 (mid _ (lev j).2.2)) =
      T.map (lev j').2.1 (mid _ (lev j').2.2)
    rw [← hmap a hW (lev j).2.2, ← hmap b hW (lev j').2.2]
    simp only [← hT.map_comp, Category.assoc, hab]⟩
  have he : ∀ k (hk : D k), e.1 k = mid k hk := fun k hk ↦
    hmap (lev k).2.1 (lev k).2.2 hk
  refine fun hbot ↦ hmid' s s' e hs hs' h (fun k hk ↦ ?_) (le_bot_iff.1 (le_trans ?_ hbot.le))
  · rw [he k hk]
    exact ⟨SimpleGraph.dist_eq_one_iff_adj.1 (hmid k hk).1,
      SimpleGraph.dist_eq_one_iff_adj.1 (hmid k hk).2⟩
  · intro g hg
    have hfix : ∀ k, D k → T.ρ k g • s.1 k = s.1 k ∧ T.ρ k g • s'.1 k = s'.1 k := by
      intro k hk
      have hadj := SimpleGraph.dist_eq_one_iff_adj.1 (hmid k hk).1
      have hadj' := SimpleGraph.dist_eq_one_iff_adj.1 (hmid k hk).2
      have hkind : T.kind k (mid k hk) = false := by
        have := T.kind_adj k _ _ hadj
        rw [hs k] at this
        cases hm' : T.kind k (mid k hk) <;> simp_all
      have hgm : T.ρ k g • mid k hk = mid k hk := by rw [← he k hk]; exact mem_stab.1 hg k
      exact ⟨hB k _ _ _ hkind hadj.symm hgm, hB k _ _ _ hkind hadj' hgm⟩
    refine ⟨mem_stab.2 fun j ↦ ?_, mem_stab.2 fun j ↦ ?_⟩ <;>
    obtain ⟨k, f, hk⟩ := hDdeep j
    · rw [← s.2 f, ← T.map_smul, (hfix k hk).1]
    · rw [← s'.2 f, ← T.map_smul, (hfix k hk).2]

end TemperedFundamentalGroups.TreeTower
