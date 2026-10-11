/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.StageGroup
import TemperedFundamentalGroups.Topology.DualGraphPi1

/-!
# The deck group of the tree covering is the combinatorial `π₁` of the dual graph
(Blueprint §11.3, G6.3)

For a curve configuration `Γ` on the special fibre `Lv.Z` of a level with root component `r`, the
reduced closed walks at `r` form a group `Γ.Loop r` under concatenation and reduction
(`Topology/DualGraphPi1.lean`), acting on the tree covering `Γ.Cover r` by deck transformations
(`loopDeck`). We show:

* `isUniversalCovering_proj`: the tree covering is a universal covering;
* **`deckLoopEquiv : deckGroup Lv (Γ.proj r) ≃* Γ.Loop r`**, upgrading the torsor bijection
  `deckFibreEquiv` (at a base point `(z, root)`, `z` on the root component and not special) to a
  group isomorphism (`deckLoopEquiv_eq`: `deckLoopEquiv τ` is the tree coordinate of
  `deckFibreEquiv τ`);
* `universalCovering.deckLoopEquiv`: for the universal covering of N1 (`universalObj`), the deck
  group is the combinatorial fundamental group of the dual graph (irreducible components and
  their intersection points) at the root component (`curveConfig.genericPoint_notMem_S`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology

namespace TemperedFundamentalGroups

noncomputable section

open GaloisObject CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

section Config

variable {Lv : Level O R A} {ι : Type u} [Finite ι] (Γ : CurveConfig Lv.Z ι) (r : ι)

/-- The tree covering of a curve configuration is a universal covering. -/
theorem isUniversalCovering_proj {z₀ : Lv.Z} (hz₀ : z₀ ∈ Γ.C r) :
    IsUniversalCovering.{u, u, u, u} (Γ.proj r) where
  isCoveringMap := isCoveringMap_proj
  connectedSpace := connectedSpace_cover hz₀
  exists_lift _ _ _ _ _ hq _ hg b y hy := CurveConfig.exists_lift hq hg hz₀ b y hy

/-- Closed walks at the root act on the tree covering by deck transformations. -/
def loopDeck : Γ.Loop r →* deckGroup Lv (Γ.proj r) :=
  coverHom.codRestrict _ fun _ _ ↦ rfl

omit [Finite ι] in
lemma loopDeck_apply (a : Γ.Loop r) (x : Γ.Cover r) :
    ((loopDeck Γ r a).1 x).1 = (x.1.1, Tree.translate a x.1.2) := rfl

variable {Γ r} {z : Lv.Z} (hz : z ∈ Γ.C r) (hzS : z ∉ Γ.S)

/-- The base point `(z, root)` of the tree covering, for `z` a non-special point of the root
component. -/
def rootPt : Γ.Cover r := ⟨(z, root Γ r), show z ∈ Γ.C r \ Γ.S from ⟨hz, hzS⟩⟩

include hz hzS

omit [Finite ι] in
/-- Points of the fibre through `(z, root)` lie over closed walks at the root. -/
lemma head_eq_of_fst_eq {x : Γ.Cover r} (hx : x.1.1 = z) : x.1.2.1.head? = some (.inl r) := by
  rcases x.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, hs, hsh⟩
  · have hmem := Cover.mem_piece_inl hi
    rw [hx] at hmem
    rw [hi, Γ.eq_of_notMem_S hmem.1 hz hzS]
  · rw [← Cover.eq_of_inr hsh, hx] at hs
    exact absurd hs hzS

omit [Finite ι] in
lemma loopDeck_injective : Function.Injective (loopDeck Γ r) := by
  intro a b h
  have := congrArg (fun τ : deckGroup Lv (Γ.proj r) ↦ (τ.1 (rootPt hz hzS)).1.2) h
  exact Subtype.ext this

lemma loopDeck_surjective : Function.Surjective (loopDeck Γ r) := by
  intro τ
  have hp := isUniversalCovering_proj Γ r hz
  have hfst : (τ.1 (rootPt hz hzS)).1.1 = z := τ.2 _
  refine ⟨⟨_, head_eq_of_fst_eq hz hzS hfst⟩, (deckFibreEquiv hp (rootPt hz hzS)).injective ?_⟩
  refine Subtype.ext (Cover.ext hfst.symm rfl)

/-- **The deck group of the tree covering is the combinatorial fundamental group of the incidence
graph**: `deckGroup ≃* Γ.Loop r`, inverse to `loopDeck`. -/
def deckLoopEquiv : deckGroup Lv (Γ.proj r) ≃* Γ.Loop r :=
  (MulEquiv.ofBijective (loopDeck Γ r)
    ⟨loopDeck_injective hz hzS, loopDeck_surjective hz hzS⟩).symm

lemma loopDeck_deckLoopEquiv (τ : deckGroup Lv (Γ.proj r)) :
    loopDeck Γ r (deckLoopEquiv hz hzS τ) = τ :=
  (MulEquiv.ofBijective (loopDeck Γ r)
    ⟨loopDeck_injective hz hzS, loopDeck_surjective hz hzS⟩).apply_symm_apply τ

/-- `deckLoopEquiv` upgrades the torsor bijection `deckFibreEquiv` at `(z, root)`: the closed walk
of `τ` is the tree coordinate of `τ (z, root)`. -/
lemma deckLoopEquiv_eq (τ : deckGroup Lv (Γ.proj r)) :
    (deckLoopEquiv hz hzS τ).1 =
      (deckFibreEquiv (isUniversalCovering_proj Γ r hz) (rootPt hz hzS) τ).1.1.2 := by
  conv_rhs => rw [← loopDeck_deckLoopEquiv hz hzS τ]
  rfl

end Config

section Universal

open TopologicalSpace

/-- The generic point of an irreducible component is not a special point of the configuration
of irreducible components. -/
lemma curveConfig_η_notMem_S {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [T0Space X]
    [QuasiSober X] (hdim : topologicalKrullDim X ≤ 1) (i : irreducibleComponents X) :
    (curveConfig X hdim).η i ∉ (curveConfig X hdim).S := by
  rintro ⟨j, k, hjk, hj, hk⟩
  have hgen := i.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents i.1 i.2)
  have hsub : ∀ l : irreducibleComponents X, i.2.1.genericPoint ∈ l.1 → i = l := fun l hl ↦
    Subtype.ext (i.2.eq_of_subset l.2.1 (by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.2 hl)
        (isClosed_of_mem_irreducibleComponents l.1 l.2)))
  exact hjk ((hsub j hj).symm.trans (hsub k hk))

variable {Lv : Level O R A} [NoetherianSpace Lv.Z] [T0Space Lv.Z] [QuasiSober Lv.Z]
  (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z)

/-- **The deck group of the universal covering of N1 (`universalObj`) is the combinatorial
fundamental group of the dual graph** (components and their intersection points) at the root
component, based at `(η, root)` with `η` the generic point of the root component. -/
def universalCovering.deckLoopEquiv :
    deckGroup Lv (universalCovering.proj hdim z₀) ≃*
      (curveConfig Lv.Z hdim).Loop (universalCovering.root hdim z₀) :=
  TemperedFundamentalGroups.deckLoopEquiv ((curveConfig Lv.Z hdim).η_mem _)
    (curveConfig_η_notMem_S hdim _)

end Universal

end

end TemperedFundamentalGroups
