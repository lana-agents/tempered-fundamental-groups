/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlue
import TemperedFundamentalGroups.SemistableReduction.EtaleTower
import TemperedFundamentalGroups.SemistableReduction.TateOverlap

/-!
# The Tate covering over the chart `V₁` (Blueprint §12.8, M2.3 (f))

The level charts `T1n n = T1/ϖⁿ⁺¹` over `U₁` of the Tate model are covered by `D(D)` (the node
chart `Rn n = T1n n[1/D]`, `TateLevel.isLocalization_Rn`) and `D(w)` (`1 = D − b₄w · w`). For a
covering of the special fibre given over `V₁`:

* **`TateGlue1.Special1`**: the special-fibre covering over `V₁` — a finite `T1/J`-algebra `C1`,
  étale over `D(w̄)`, together with its restriction to the node chart: an admissible covering `cov₀`
  of `NR/J` (Kummer at the nodes) and `ι₀ : C1 → cov₀.C`, a localization away from `D̄`;
  (**scope: coverings étale outside the nodes** on `V₁`, i.e. the marked points, if any, lie in
  `V₀ ∖ V₁`; the cusp at the origin `[0:1:0]` is handled by the piece over `V₀`);
* `TateGlue1.E1 n`: the étale lifts of `C1` over `D(w)` (`EtaleTower.lift`);
* the data of `NodeEtaleGlue` for the Tate charts (`instBR`, `towerOBR`, `isLocalization_BR`,
  `hφs`); the covering over `V₁` and its tower are in `TateGlue1Tower`.
-/

universe u

namespace SemistableReduction

namespace TateGlue1

open TateTwoChart TateTwoChartNode TateLevel KummerEtale AdmissibleLift

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {ϖ b₄ b₆ t κ ε εi π : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π = ε * ϖ ^ m) (hε : εi * ε = 1)

/-- The node chart. -/
abbrev Rb (b₄ b₆ ϖ : O) (m : ℕ) (ε : O) : Type u :=
  QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)

/-- The special fibre `T1/J` of the chart over `U₁`. -/
abbrev T1s (θ : O →+* k) (π b₄ t κ : O) : Type u := EtaleTower.Ts θ (T1 π b₄ t κ)

/-- `T1/J → NR/J` (`toNode` modulo `J`). -/
def toNodeJ : T1s θ π b₄ t κ →+* (Rb b₄ b₆ ϖ m ε ⧸ J θ (R := Rb b₄ b₆ ϖ m ε)) :=
  Ideal.quotientMap _ (toNode b₄ hκ hπ : T1 π b₄ t κ →+* NR b₄ b₆ ϖ m ε) (by
    rw [J, Ideal.map_le_iff_le_comap, Ideal.comap_comap, J]
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply, RingHom.coe_coe, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hx)

omit hθ in
lemma toNodeJ_mk (x : T1 π b₄ t κ) : toNodeJ (θ := θ) hκ hπ (Ideal.Quotient.mk _ x) =
    Ideal.Quotient.mk _ (toNode b₄ hκ hπ x) := Ideal.quotientMap_mk

variable (hπe : θ (ϖ ^ m) = 0) (τ : Rb b₄ b₆ ϖ m ε)

variable (cov₀ : Admissible.Covering
    (NodeChart.φ (QuadNodeTower.Rb ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m)) hπe)
    (QuadNodeTower.ψb (θ := θ) ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) τ))

/-- **The special-fibre covering over `V₁`** with its restriction `cov₀` to the node chart
(`NodeEtaleGlue.Special`): a finite `T1/J`-algebra `C1`, étale over `D(w̄)`, with
`ι₀ : C1 → cov₀.C` exhibiting `cov₀.C` as `C1[1/D̄]`. -/
abbrev Special1 : Type (u + 1) :=
  NodeEtaleGlue.Special (T1s θ π b₄ t κ) cov₀ (toNodeJ hκ hπ)
    (Ideal.Quotient.mk _ (DT π b₄ t κ)) (Ideal.Quotient.mk _ (w1 π b₄ t κ))

/-! ### The families of charts -/

/-- The level charts over `U₁`. -/
abbrev B (ϖ π b₄ t κ : O) (n : ℕ) : Type u := T1n ϖ π b₄ t κ n

/-- The level node charts. -/
abbrev R (b₄ b₆ ϖ : O) (m : ℕ) (ε : O) (n : ℕ) : Type u := Rn b₄ b₆ ϖ m ε n

variable (ϖ b₄) in
/-- The node charts as algebras over the level charts (`algRn`). -/
@[reducible] def instBR : ∀ n, Algebra (B ϖ π b₄ t κ n) (R b₄ b₆ ϖ m ε n) :=
  fun n ↦ algRn b₄ hκ hπ n

lemma toRn_algebraMap (n : ℕ) (o : O) :
    toRn b₄ hκ hπ n (algebraMap O (T1n ϖ π b₄ t κ n) o) =
      algebraMap O (Rn b₄ b₆ ϖ m ε n) o := by
  change toRn b₄ hκ hπ n (Ideal.Quotient.mk _ (algebraMap O _ o)) = _
  rw [toRn_mk, AlgHom.commutes]
  rfl

lemma towerOBR (n : ℕ) : letI := instBR ϖ b₄ hκ hπ
    IsScalarTower O (B ϖ π b₄ t κ n) (R b₄ b₆ ϖ m ε n) :=
  letI := instBR ϖ b₄ hκ hπ
  IsScalarTower.of_algebraMap_eq fun o ↦ (toRn_algebraMap hκ hπ n o).symm

include hε in
lemma isLocalization_BR (n : ℕ) : letI := instBR ϖ b₄ hκ hπ
    IsLocalization.Away (Ideal.Quotient.mk _ (DT π b₄ t κ) : B ϖ π b₄ t κ n)
      (R b₄ b₆ ϖ m ε n) :=
  isLocalization_Rn hκ hπ hε n

/-! ### The tower of node patches and the special-fibre comparison -/

variable (hϖ : θ ϖ = 0) (π' : cov₀.ι → O) (hπ' : ∀ j, π' j ^ cov₀.e j = ϖ ^ m)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing O]

/-- The tower of node patches of `cov₀` (`QuadNodeTower.tower`). -/
abbrev tower := QuadNodeTower.tower ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hϖ hπe τ cov₀ π' hπ' hker

/-- The reductions `T1n n → T1/J`. -/
abbrev qB (n : ℕ) : B ϖ π b₄ t κ n →+* T1s θ π b₄ t κ := EtaleTower.q (T1 π b₄ t κ) hϖ n

/-- **The special fibres of the level charts and of the node charts agree**
(`QuadNodeTower.eqv`). -/
lemma hφs (n : ℕ) (x : B ϖ π b₄ t κ n) :
    (tower hπe τ cov₀ hϖ π' hπ' hker).e n (toNodeJ hκ hπ (qB hϖ n x)) =
      Ideal.Quotient.mk _ (letI := instBR ϖ b₄ hκ hπ
        algebraMap (B ϖ π b₄ t κ n) (R b₄ b₆ ϖ m ε n) x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  change QuadNodeTower.eqv ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hϖ n
    (toNodeJ hκ hπ (Ideal.Quotient.mk _ y)) =
      Ideal.Quotient.mk _ (toRn b₄ hκ hπ n (Ideal.Quotient.mk _ y))
  rw [toNodeJ_mk, toRn_mk]
  exact QuadNodeTower.eqv_mk ϖ m (cN b₄ b₆ ϖ m ε) (DN b₄ ϖ m) hϖ n _

variable {hπe τ cov₀} (Sp : Special1 hκ hπ hπe τ cov₀)

instance isNoetherianRing_T1 : IsNoetherianRing (T1 π b₄ t κ) :=
  Ideal.Quotient.isNoetherianRing _

/-- **The étale lifts of `C1` over `D(w)`** at level `n` (`EtaleTower.lift`). -/
def E1 (n : ℕ) : EtaleTower.Lift (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) n :=
  haveI := Sp.finite
  EtaleTower.lift (T1 π b₄ t κ) hϖ Sp.C1 (w1 π b₄ t κ) hker Sp.etale n

end

end TateGlue1

end SemistableReduction
