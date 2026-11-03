/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0CuspTower
import TemperedFundamentalGroups.SemistableReduction.TateCuspNF
import TemperedFundamentalGroups.SemistableReduction.TateT1Normal
import TemperedFundamentalGroups.SemistableReduction.NodeLevelHom
import TemperedFundamentalGroups.SemistableReduction.EtaleTowerHom
import TemperedFundamentalGroups.SemistableReduction.OverlapHom
import TemperedFundamentalGroups.SemistableReduction.CuspPieceOverlap
import TemperedFundamentalGroups.SemistableReduction.AdicSystemHom
import TemperedFundamentalGroups.SemistableReduction.OmegaPairHom
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueEnd

/-!
# Maps of the node patches and étale lifts of Tate coverings (MR12 I3, Tate instance, part 1)

The first pieces of the map of adic systems `systemCusp … Sp … → systemCusp … Sp' …` induced by
a morphism `f₁ : Sp.C1 → Sp'.C1` of special-fibre coverings over `V₁`:

* `NodeEtaleGlue.Special.covMap` (generic): the map `cov₀.C = C1[1/ā] → cov₀'.C` of the node
  coverings induced by `f₁` (`covMap_ι₀`);
* `QuadNodeTower.lev`: the levels of `QuadNodeTower.tower` with the base data spelled through
  the chart's constants `fn`, `eqv`, `hfe` (not through projections of the tower), so that levels
  of towers of *different* coverings live over syntactically equal bases; `QuadNodeTower.nodeCoord`,
  `nodeCoordL` (the lifted node coordinates are the chart's `u`, `v`);
  **`QuadNodeTower.gMap`**: the map of the node patches of two node-only coverings induced by a
  balanced map of the coverings (`LevelTower.nodeLevelMap`);
* Tate: `TateGlue1.isLocalization_toNodeJ`, **`TateGlue1.covMap`** (`covMap_ι₀`),
  **`TateGlue1.eMap`** (the maps of the étale lifts `E1`, `EtaleTower.homLift`), `sE_eMap`, and
  **`TateGlue1.Balanced`** (the node balance condition for `f₁` at every level).

Implementation note (MR12 c48). Statements mixing the patched levels of `TateGlue1.input` for two
coverings `cov₀ ≠ cov₀'` with maps built from `nodeLevelMap` do not elaborate (no heartbeat
timeout; the unifier unfolds the chain of `abbrev`s `Data.G → Level.G → LevelStep.patchOf → …`
on both sides, since `tryHeuristic` does not compare arguments of abbreviations, and then
compares differently spelled instance terms over the concrete Tate charts). Hence the levels
over constant base data (`lev`) and, for the remaining wiring, a generic heterogeneous
`nodeLevelMap` (see `MR12-tfg-plan.md`, continuation 48).
-/

universe u

namespace SemistableReduction

open AdmissibleLift

noncomputable section

/-! ### Generic: the map of node coverings induced by a map of special-fibre coverings -/

namespace NodeEtaleGlue.Special

variable {k : Type u} [Field k] {Bs : Type u} [CommRing Bs] {R₀ : Type u} [CommRing R₀]
  [Algebra k R₀] {f₀ : R₀} {φ₀ φ₀' : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ ψ₀' : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {cov₀' : Admissible.Covering φ₀' ψ₀'}
  {φs : Bs →+* R₀} {abar bbar : Bs}
  (Sp : Special Bs cov₀ φs abar bbar) (Sp' : Special Bs cov₀' φs abar bbar)

lemma isUnit_covMap (f : Sp.C1 →ₐ[Bs] Sp'.C1) :
    IsUnit ((Sp'.ι₀.comp (f : Sp.C1 →+* Sp'.C1)) (algebraMap Bs Sp.C1 abar)) := by
  rw [RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
  letI := Sp'.ι₀.toAlgebra
  haveI := Sp'.hι
  exact IsLocalization.Away.algebraMap_isUnit (algebraMap Bs Sp'.C1 abar)

/-- The ring map `cov₀.C = C1[1/ā] → cov₀'.C = C1'[1/ā]` induced by `f : C1 → C1'`. -/
def covMapR (f : Sp.C1 →ₐ[Bs] Sp'.C1) : cov₀.C →+* cov₀'.C :=
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  IsLocalization.Away.lift (algebraMap Bs Sp.C1 abar) (Sp.isUnit_covMap Sp' f)

lemma covMapR_ι₀ (f : Sp.C1 →ₐ[Bs] Sp'.C1) (c : Sp.C1) :
    Sp.covMapR Sp' f (Sp.ι₀ c) = Sp'.ι₀ (f c) :=
  letI := Sp.ι₀.toAlgebra
  haveI := Sp.hι
  IsLocalization.Away.lift_eq _ (Sp.isUnit_covMap Sp' f) c

variable (hloc : letI := φs.toAlgebra; IsLocalization.Away abar R₀)

/-- **The map of the node coverings `cov₀.C → cov₀'.C`** over `R₀ = Bs[1/ā]` induced by a map
`f : C1 → C1'` of the special-fibre coverings of the base chart. -/
def covMap (f : Sp.C1 →ₐ[Bs] Sp'.C1) : cov₀.C →ₐ[R₀] cov₀'.C :=
  { Sp.covMapR Sp' f with
    commutes' := fun r ↦ by
      letI := φs.toAlgebra
      haveI := hloc
      have h := IsLocalization.ringHom_ext (Submonoid.powers abar) (S := R₀)
        (j := (Sp.covMapR Sp' f).comp (algebraMap R₀ cov₀.C)) (k := algebraMap R₀ cov₀'.C)
        (RingHom.ext fun x ↦ by
          change Sp.covMapR Sp' f (algebraMap R₀ cov₀.C (φs x)) = algebraMap R₀ cov₀'.C (φs x)
          rw [← Sp.hι₀, covMapR_ι₀, AlgHom.commutes, Sp'.hι₀])
      exact RingHom.congr_fun h r }

lemma covMap_ι₀ (f : Sp.C1 →ₐ[Bs] Sp'.C1) (c : Sp.C1) :
    Sp.covMap Sp' hloc f (Sp.ι₀ c) = Sp'.ι₀ (f c) :=
  Sp.covMapR_ι₀ Sp' f c

end NodeEtaleGlue.Special

/-! ### Generic over the quadratic node chart: maps of the node patches -/

namespace QuadNodeTower

open KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ π : O} {e : ℕ} {c D : A π e}
  (hϖ : θ ϖ = 0) {hπe : θ (π ^ e) = 0} {τ : Rb π e c D}
  {cov₀ cov₀' : Admissible.Covering (NodeChart.φ (Rb π e c D) hπe) (ψb (θ := θ) π e c D τ)}
  (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = π ^ e)
  (π'' : cov₀'.ι → O) (hπ'' : ∀ j, π'' j ^ cov₀'.e j = π ^ e)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

/-- **The lifted node coordinates of the levels are the chart's `u`, `v`** (`χ_j` is
`NodeChart.χ`). -/
lemma nodeCoord (n : ℕ) :
    LevelTower.NodeCoord ((tower π e c D hϖ hπe τ cov₀ π' hπ' hker).level n)
      (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)) (Node.u (π ^ e)))
      (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)) (Node.v (π ^ e))) :=
  ⟨fun j ↦ congrArg (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)))
      (Node.congrEq_u (hπ' j)),
    fun j ↦ congrArg (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)))
      (Node.congrEq_v (hπ' j))⟩

variable {π' π''} in
/-- **The levels of the tower with the base data spelled by the chart's constants** (`fn`, `eqv`,
`hfe`), so that levels of towers of different coverings live over syntactically equal bases. -/
abbrev lev (hπ' : ∀ j, π' j ^ cov₀.e j = π ^ e) (n : ℕ) :
    LevelTower.Level (Rn ϖ π e c D) cov₀ π' (hfe π e c D hϖ) n :=
  (tower π e c D hϖ hπe τ cov₀ π' hπ' hker).level n

lemma nodeCoordL (n : ℕ) :
    LevelTower.NodeCoord (lev hϖ hker hπ' n)
      (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)) (Node.u (π ^ e)))
      (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)) (Node.v (π ^ e))) :=
  ⟨fun j ↦ congrArg (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)))
      (Node.congrEq_u (hπ' j)),
    fun j ↦ congrArg (algebraMap (A π e) (FormalPatchLevel.Hat (fn ϖ π e c D n)))
      (Node.congrEq_v (hπ' j))⟩

variable [IsEmpty cov₀.κ] [IsEmpty cov₀'.κ]
  (φ : cov₀.C →ₐ[Rb π e c D ⧸ J θ (R := Rb π e c D)] cov₀'.C)
  (hbal : ∀ n, LevelTower.NodeBalanced (hfe π e c D hϖ) π' π'' φ n)

/-- **The map of the node patches at level `n`** induced by a balanced map `φ` of node-only
coverings (`LevelTower.nodeLevelMap`), between the levels `lev`. -/
noncomputable def gMap (n : ℕ) : (lev hϖ hker hπ' n).G hθ.out →ₐ[Rn ϖ π e c D n]
    (lev hϖ hker hπ'' n).G hθ.out :=
  LevelTower.nodeLevelMap hθ.out (lev hϖ hker hπ' n) (lev hϖ hker hπ'' n) φ
    (nodeCoordL hϖ π' hπ' hker n) (nodeCoordL hϖ π'' hπ'' hker n) (hbal n)


end QuadNodeTower

/-! ### The Tate instance -/

namespace TateGlue1

open TateTwoChart TateTwoChartNode TateLevel KummerEtale

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)

omit hθ in
include hε in
/-- **The special fibre of the node chart is `T1/J[1/D̄]`** (through `toNodeJ`). -/
lemma isLocalization_toNodeJ :
    letI := (toNodeJ (θ := θ) (b₄ := b₄) (b₆ := b₆) (ϖ := ϖ) (m := m) (ε := ε) hκ hπ).toAlgebra
    IsLocalization.Away (Ideal.Quotient.mk (J θ (R := T1 π b₄ t κ)) (DT π b₄ t κ))
      (Rb b₄ b₆ ϖ m ε ⧸ J θ (R := Rb b₄ b₆ ϖ m ε)) :=
  letI := algT1NR (b₆ := b₆) (ϖ := ϖ) (m := m) (ε := ε) b₄ hκ hπ
  haveI := isScalarTower_NR (b₄ := b₄) hκ hπ
  haveI := isLocalization_NR (b₄ := b₄) hκ hπ hε
  TateLevel.isLocalization_quotMap (DT π b₄ t κ) (RingHom.ker θ)

variable {hπe : θ (ϖ ^ m) = 0} {τ : Rb b₄ b₆ ϖ m ε}
  {cov₀ cov₀' : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ)}
  (Sp : Special1 hκ hπ hπe τ cov₀) (Sp' : Special1 hκ hπ hπe τ cov₀')

/-- **The map of the node coverings** `cov₀.C → cov₀'.C` induced by a map `f₁ : C1 → C1'` of
the special-fibre coverings over `V₁`. -/
abbrev covMap (f₁ : Sp.C1 →ₐ[T1s θ π b₄ t κ] Sp'.C1) :
    cov₀.C →ₐ[Rb b₄ b₆ ϖ m ε ⧸ J θ (R := Rb b₄ b₆ ϖ m ε)] cov₀'.C :=
  NodeEtaleGlue.Special.covMap Sp Sp' (isLocalization_toNodeJ hκ hπ hε) f₁

lemma covMap_ι₀ (f₁ : Sp.C1 →ₐ[T1s θ π b₄ t κ] Sp'.C1) (c : Sp.C1) :
    covMap hκ hπ hε Sp Sp' f₁ (Sp.ι₀ c) = Sp'.ι₀ (f₁ c) :=
  NodeEtaleGlue.Special.covMap_ι₀ Sp Sp' _ f₁ c

variable (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (π'' : cov₀'.ι → O) (hπ'' : ∀ j, π'' j ^ cov₀'.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

/-! #### The étale lifts -/

/-- **The map of the étale lifts over `D(w)`** at level `n` induced by `f₁`
(`EtaleTower.homLift`). -/
def eMap (f₁ : Sp.C1 →ₐ[T1s θ π b₄ t κ] Sp'.C1) (n : ℕ) :
    (E1 hκ hπ hϖ hker Sp n).E →ₐ[EtaleTower.Tn ϖ (T1 π b₄ t κ) n] (E1 hκ hπ hϖ hker Sp' n).E :=
  EtaleTower.homLift (T1 π b₄ t κ) hϖ (w1 π b₄ t κ) hker f₁ (E1 hκ hπ hϖ hker Sp n)
    (E1 hκ hπ hϖ hker Sp' n)

lemma sE_eMap (f₁ : Sp.C1 →ₐ[T1s θ π b₄ t κ] Sp'.C1) (n : ℕ) (x : (E1 hκ hπ hϖ hker Sp (n + 1)).E) :
    sE hκ hπ hϖ hker Sp' n (eMap hκ hπ Sp Sp' hϖ hker f₁ (n + 1) x) =
      eMap hκ hπ Sp Sp' hϖ hker f₁ n (sE hκ hπ hϖ hker Sp n x) :=
  EtaleTower.succ_comp_homLift (T1 π b₄ t κ) hϖ (w1 π b₄ t κ) hker f₁ _ _ _ _ x

/-! #### The node patches -/

/-- **The balance condition** for `f₁` at all levels: the induced map `covMap f₁` of the node
coverings has a balanced Kummer normal form (`LevelTower.NodeBalanced`). -/
def Balanced [IsEmpty cov₀.κ] (f₁ : Sp.C1 →ₐ[T1s θ π b₄ t κ] Sp'.C1) : Prop :=
  ∀ n, LevelTower.NodeBalanced (QuadNodeTower.hfe ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hϖ) π' π''
    (covMap hκ hπ hε Sp Sp' f₁) n


end TateGlue1

end

end SemistableReduction
