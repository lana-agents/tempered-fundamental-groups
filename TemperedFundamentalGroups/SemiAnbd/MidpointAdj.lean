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

end TemperedFundamentalGroups.TreeTower
