/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.CurveTowerBranches
import TemperedFundamentalGroups.SemiAnbd.Estrangement

/-!
# Missing theorem M4 (wild estrangement) for André's tower (Blueprint §12.10)

Scheme case, under the hypotheses of Theorem A. The estrangement hypothesis of the P13
consumers (`exists_le_stab_andreTower_of_le_estranged`, `exists_eq_stab_of_maximal_of_estranged`,
`pscAdj_andreTower_of_estranged'`, `isGraphic_iff_andreTower_of_estranged'`,
`isGraphic_iff_andreTower_andreTower`) is split along a set `P` of levels of André's tower
(intended: the tame levels, whose geometric Galois groups have order prime to `p`; the
repository has no such predicate, so `P` is a parameter):

* **`TameEstrangement Δ P`**: every element of `Δ` acting nontrivially on the tree of some
  `P`-level is estranged (for the pro-`Σ` quotient this is [SemiAnbd] Ex. 2.10 given M2,
  Blueprint §12.8; for the full tower it also needs that the fixed sets stay small at the deeper,
  wild, levels);
* **`WildEstrangement Δ P`** (**M4**): every nontrivial element of `Δ` acting trivially on the
  trees of all `P`-levels is estranged.

`estranged_comap_andreTower_iff` shows that the two together are exactly the estrangement of the
tower pulled back to `Δ`; the consumers follow (`exists_le_stab_andreTower_of_tame_wild`,
`exists_eq_stab_of_maximal_of_tame_wild`, `pscAdj_andreTower_of_tame_wild`,
`isGraphic_iff_andreTower_of_tame_wild`). `WildEstrangement` is not proved for any curve;
`TameEstrangement Δ RigidLevel` (levels whose ring has no nontrivial `R`-endomorphism) is proved
in `Andre/TameEstrangement.lean` (`tameEstrangement_rigid`), together with the reduction of M4
relative to these levels to elliptic estrangement. Necessary conditions and the line case are in
`SemiAnbd/Estrangement.lean` (`TreeTower.WildEstranged.exists_not_mem`,
`TreeTower.estranged_iff_of_lineAt`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open GaloisLimit

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A] [Finite A] [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-- **Missing theorem M4 (wild estrangement) for André's tower**: for a subgroup `Δ` of André's
group (e.g. the geometric subgroup) and a set `P` of levels (the tame levels), every nontrivial
element of `Δ` acting trivially on the trees of the dual graphs of all `P`-levels has, at
cofinally many levels, a fixed set of diameter `≤ 2`. -/
def WildEstrangement (Δ : Subgroup (andreGroup O R A V hV))
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop) : Prop :=
  (andreTower (R := R) (A := A) V hV hp hR).WildEstranged Δ P

/-- **Tame estrangement for André's tower**: every element of `Δ` acting nontrivially on the
tree of some `P`-level has, at cofinally many levels, a fixed set of diameter `≤ 2`. -/
def TameEstrangement (Δ : Subgroup (andreGroup O R A V hV))
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop) : Prop :=
  (andreTower (R := R) (A := A) V hV hp hR).TameEstranged Δ P

/-- **Estrangement of André's tower over `Δ` = tame estrangement + M4.** -/
theorem estranged_comap_andreTower_iff (Δ : Subgroup (andreGroup O R A V hV))
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop) :
    ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged ↔
      TameEstrangement V hV hp hR Δ P ∧ WildEstrangement V hV hp hR Δ P := by
  rw [TreeTower.estranged_comap_subtype_iff]
  exact TreeTower.estrangedOn_iff_tame_wild Δ P

/-- For `Δ = ⊤`: estrangement of André's tower = tame estrangement + M4. -/
theorem estranged_andreTower_iff (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop) :
    (andreTower (R := R) (A := A) V hV hp hR).Estranged ↔
      TameEstrangement V hV hp hR ⊤ P ∧ WildEstrangement V hV hp hR ⊤ P := by
  rw [TreeTower.estranged_iff_estrangedOn_univ, ← Subgroup.coe_top]
  exact TreeTower.estrangedOn_iff_tame_wild ⊤ P

/-- **[SemiAnbd] Thm. 3.7(iii) for `Δ` (system form) from tame estrangement and M4**: every
nontrivial compact subgroup of `Δ` fixes a compatible system of vertices of all levels. -/
theorem exists_le_stab_andreTower_of_tame_wild (Δ : Subgroup (andreGroup O R A V hV))
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop)
    (hT : TameEstrangement V hV hp hR Δ P) (hW : WildEstrangement V hV hp hR Δ P)
    (H : Subgroup (andreGroup O R A V hV)) (hHΔ : H ≤ Δ) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s :=
  exists_le_stab_andreTower_of_le_estranged V hV hp hR Δ
    ((estranged_comap_andreTower_iff V hV hp hR Δ P).2 ⟨hT, hW⟩) H hHΔ hH1 hH

/-- **[SemiAnbd] Thm. 3.7(iv) for André's group (system form) from tame estrangement and M4.** -/
theorem exists_eq_stab_of_maximal_of_tame_wild
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop)
    (hT : TameEstrangement V hV hp hR ⊤ P) (hW : WildEstrangement V hV hp hR ⊤ P)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV)))
    (hmax : ∀ H' : Subgroup (andreGroup O R A V hV), IsCompact (H' : Set (andreGroup O R A V hV)) →
      H ≤ H' → H' = H) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H = TreeTower.stab s :=
  exists_eq_stab_of_maximal_of_estranged V hV hp hR
    ((estranged_andreTower_iff V hV hp hR P).2 ⟨hT, hW⟩) H hH1 hH hmax

/-- **`PSCAdj` for André's group from tame estrangement, M4 and nontrivial edge-like
subgroups.** -/
theorem pscAdj_andreTower_of_tame_wild
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop)
    (hT : TameEstrangement V hV hp hR ⊤ P) (hW : WildEstrangement V hV hp hR ⊤ P)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj :=
  pscAdj_andreTower_of_estranged' V hV hp hR
    ((estranged_andreTower_iff V hV hp hR P).2 ⟨hT, hW⟩) hedge

/-- **CG3' for André's group from tame estrangement, M4 and nontrivial edge-like subgroups**,
against a functorial estranged tree tower without branch inversions. -/
theorem isGraphic_iff_andreTower_of_tame_wild {Γ' : Type*} [Group Γ'] {J' : Type*}
    [Category J'] [IsCofilteredOrEmpty J'] {T' : TreeTower Γ' J'}
    {α : andreGroup O R A V hV ≃* Γ'}
    (P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop)
    (hT : TameEstrangement V hV hp hR ⊤ P) (hW : WildEstrangement V hV hp hR ⊤ P)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥)
    (hT' : T'.IsFunctorial) (hE' : T'.Estranged) (hB' : T'.NoBranchSwap)
    (hedge' : ∀ e : T'.Sys, (∀ j, ∃ (k : J') (_ : k ⟶ j), T'.kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR) T' α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α :=
  isGraphic_iff_andreTower_of_estranged' V hV hp hR
    ((estranged_andreTower_iff V hV hp hR P).2 ⟨hT, hW⟩) hedge hT' hE' hB' hedge'

/-- **M4 is not visible on tame levels**: if M4 holds and all trees of André's tower contain
two vertices at distance `> 2`, every nontrivial element of `Δ` acting trivially on the trees
of all `P`-levels acts nontrivially on the tree of a non-`P` level below every level. -/
theorem WildEstrangement.exists_not_mem {Δ : Subgroup (andreGroup O R A V hV)}
    {P : PtGal (tempFibre O R A V hV) (galW O R A Ω hR) → Prop}
    (hW : WildEstrangement V hV hp hR Δ P)
    (hbig : ∀ k, ∃ x y : (andreTower (R := R) (A := A) V hV hp hR).V k,
      2 < ((andreTower (R := R) (A := A) V hV hp hR).graph k).dist x y)
    {g : andreGroup O R A V hV} (hgΔ : g ∈ Δ)
    (hgK : g ∈ (andreTower (R := R) (A := A) V hV hp hR).actKer P) (hg1 : g ≠ 1)
    (j : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :
    ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j), ¬ P k ∧
      ∃ v : (andreTower (R := R) (A := A) V hV hp hR).V k,
        (andreTower (R := R) (A := A) V hV hp hR).ρ k g • v ≠ v :=
  TreeTower.WildEstranged.exists_not_mem hW hbig hgΔ hgK hg1 j

end

end TemperedFundamentalGroups
