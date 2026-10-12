/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.DualGraphPi1
import TemperedFundamentalGroups.Andre.StageGroup
import TemperedFundamentalGroups.SemiAnbd.IncidenceTree

/-!
# Finite subgroups of the stage groups (Blueprint §12.5, C3–C4)

The stage group `Π_Lv` of the Galois object `U_Lv` is an extension
`1 → deck(Z̃) → Π_Lv → Aut_R(B)ᵒᵖ → 1` (`stageGroup_extension`, §11.3, G6.3), where the deck
group of the tree covering `Z̃` of the dual graph is its combinatorial fundamental group
(`deckLoopEquiv`). That group acts freely on the tree without inversions, so it has no torsion
(`CurveConfig.eq_one_of_isOfFinOrder`, T3). Hence:

* `deck_eq_one_of_isOfFinOrder` (**C3**): the deck group of the tree covering has no torsion;
  `universalCovering.deck_eq_one_of_isOfFinOrder` for the universal covering of N1.
* `eq_one_of_isOfFinOrder_of_stageLevel` (**C4**): an element of finite order of a stage group
  acting trivially on level coordinates is trivial, provided the deck group has no torsion;
  `injective_stageLevel_comp_subtype`: **every finite subgroup of `Π_Lv` embeds into the
  permutations of `F_L` (into `Aut_R(B)ᵒᵖ`)**, and `universalObj_injective_stageLevel` for
  `U_Lv = universalObj`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

section Deck

variable {Lv : Level O R A} {ι : Type u} [Finite ι] {Γ : CurveConfig Lv.Z ι} {r : ι}
  {z : Lv.Z} (hz : z ∈ Γ.C r) (hzS : z ∉ Γ.S)

include hz hzS in
/-- **C3**: the deck group of the tree covering of a curve configuration has no torsion. -/
theorem deck_eq_one_of_isOfFinOrder {τ : deckGroup Lv (Γ.proj r)} (h : IsOfFinOrder τ) :
    τ = 1 := by
  have h' : IsOfFinOrder (deckLoopEquiv hz hzS τ) :=
    (deckLoopEquiv hz hzS).toMonoidHom.isOfFinOrder h
  exact (deckLoopEquiv hz hzS).injective (by
    rw [map_one]; exact eq_one_of_isOfFinOrder h')

end Deck

section Universal

variable {Lv : Level O R A} [TopologicalSpace.NoetherianSpace Lv.Z] [T0Space Lv.Z]
  [QuasiSober Lv.Z] (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z)

instance universalCovering.instNonempty : Nonempty (universalCovering Lv.Z hdim z₀) :=
  ⟨universalCovering.base hdim z₀⟩

/-- **C3** for the universal covering of N1. -/
theorem universalCovering.deck_eq_one_of_isOfFinOrder
    {τ : deckGroup Lv (universalCovering.proj hdim z₀)} (h : IsOfFinOrder τ) : τ = 1 :=
  TemperedFundamentalGroups.deck_eq_one_of_isOfFinOrder ((curveConfig Lv.Z hdim).η_mem _)
    (curveConfig_η_notMem_S hdim _) h

end Universal

section Stage

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  [Subsingleton A] {Lv : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H]
  {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}
  [ConnectedSpace Lv.Z] [Nonempty E] [Nonempty (Lv.L.B →ₐ[R] Ω)]
  {𝒢 : ObjectProperty (TempObj O R A)}

/-- **C4**: if the deck group of `Z̃` has no torsion, an element of finite order of the stage
group of `U_Lv` acting trivially on level coordinates is trivial. -/
theorem eq_one_of_isOfFinOrder_of_stageLevel
    (htor : ∀ τ : deckGroup Lv p, IsOfFinOrder τ → τ = 1)
    (hrig : IsRigid (tempFibre O R A V hV) 𝒢) (hU : 𝒢 (obj Lv hp hc))
    {σ : stageGroup (tempFibre O R A V hV) (obj Lv hp hc)} (hσ : IsOfFinOrder σ)
    (h1 : stageLevel V hV (levelPt_surjective V hV (hp := hp) (hc := hc)) σ = 1) : σ = 1 := by
  have hmem : σ ∈ (stageLevel V hV (levelPt_surjective V hV (hp := hp) (hc := hc))).ker := h1
  rw [ker_stageLevel V hV hrig hU] at hmem
  obtain ⟨τ, rfl⟩ := hmem
  have hτ : IsOfFinOrder τ := (deckStage_injective V hV).isOfFinOrder_iff.1 hσ
  rw [htor τ hτ, map_one]

/-- **C4**: if the deck group of `Z̃` has no torsion, every finite subgroup of the stage group
of `U_Lv` embeds into the permutations of the level coordinates `F_L = Hom_R(B, Ω)` (whose
image is `Aut_R(B)ᵒᵖ`, `stageGroup_extension`). -/
theorem injective_stageLevel_comp_subtype
    (htor : ∀ τ : deckGroup Lv p, IsOfFinOrder τ → τ = 1)
    (hrig : IsRigid (tempFibre O R A V hV) 𝒢) (hU : 𝒢 (obj Lv hp hc))
    (H : Subgroup (stageGroup (tempFibre O R A V hV) (obj Lv hp hc))) (hH : Finite H) :
    Function.Injective
      ((stageLevel V hV (levelPt_surjective V hV (hp := hp) (hc := hc))).comp H.subtype) := by
  refine (injective_iff_map_eq_one _).2 fun x hx ↦ Subtype.ext ?_
  exact eq_one_of_isOfFinOrder_of_stageLevel V hV htor hrig hU
    (H.subtype.isOfFinOrder (isOfFinOrder_of_finite x)) hx

end Stage

section UniversalStage

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  [Subsingleton A] {Lv : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H]
  [TopologicalSpace.NoetherianSpace Lv.Z] [T0Space Lv.Z] [QuasiSober Lv.Z]
  (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z)
  [ConnectedSpace Lv.Z] [Nonempty (Lv.L.B →ₐ[R] Ω)]
  {𝒢 : ObjectProperty (TempObj O R A)}

/-- **C4** for `U_Lv = universalObj`: every finite subgroup of its stage group embeds into the
permutations of `F_L`. -/
theorem universalObj_injective_stageLevel
    (hrig : IsRigid (tempFibre O R A V hV) 𝒢) (hU : 𝒢 (universalObj Lv hdim z₀))
    (H : Subgroup (stageGroup (tempFibre O R A V hV) (universalObj Lv hdim z₀))) [Finite H] :
    Function.Injective
      ((stageLevel V hV (levelPt_surjective V hV
        (hp := universalCovering.isUniversalCovering.{u, u, u} hdim z₀)
        (hc := (universalCovering.isUniversalCovering.{u, u, u} hdim z₀).countable_fibre))).comp
        H.subtype) := by
  exact injective_stageLevel_comp_subtype V hV
    (hp := universalCovering.isUniversalCovering.{u, u, u} hdim z₀)
    (hc := (universalCovering.isUniversalCovering.{u, u, u} hdim z₀).countable_fibre)
    (fun _ h ↦ universalCovering.deck_eq_one_of_isOfFinOrder hdim z₀ h) hrig hU H ‹_›

end UniversalStage

end

end TemperedFundamentalGroups
