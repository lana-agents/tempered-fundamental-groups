/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueOverlap
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapPiece
import TemperedFundamentalGroups.SemistableReduction.TwoChartPatch

/-!
# The second chart of a covering glued with the covering over the first (Blueprint §12.8, M2.3 (f))

An input `I : NodeEtaleGlue.Input` describes a covering over the chart `V₁ = Spec B0` of a model
of `ℙ¹` (levels `B n`). **`NodeEtaleGlue.Overlap I`** adds the second chart `V₀ = Spec B0'`
(levels `B' n`), the overlaps `W0 = B0[1/x₁] = B0'[1/x₀]` (levels `W n`), and the covering over
`V₀` away from the nodes: a special-fibre covering `C0` over `Bs'` with its étale lifts `E0 n`
over `D(c₀) ⊆ V₀`, together with the **overlap datum**
`ω : C0[1/x̄₀] ≃ₐ[Ws] C1[1/x̄₁]` over the special fibre `Ws` of the overlap.

`ω` is part of the given covering: `C0`, `C1`, `ω` are the **chart description (glueing data) of
one covering of the special fibre**. (When the charts are identified with the sections of the
model over the preimages of the charts of `ℙ¹` (Blueprint §12.8 (g)), this description has to be
shown equivalent to giving the covering as a scheme over the special fibre.)

* `Overlap.M n = E0 n[1/x₀]`, **`Overlap.γM`**, `isLocalization_γM`: its special fibre is
  `C1[1/ḡ]` (`OverlapPiece`);
* **`Overlap.ψ n : Y n → M n`**, `isLocalization_ψ`: a localization away from `g`
  (`Input.glueM`);
* `Overlap.Q n = Y n[1/x₁]`, **`Overlap.ρ0a : Q n → M n`** (`isLocalization_ρ0a`: away from `c₀`),
  `ρ0b : E0 n → M n` (away from `x₀`), **`Overlap.patch0 n`** (`TwoChartGlue.Patch0`) and
  **`Overlap.twoChart n`**: the two-chart rings of the covering at level `n`.
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}

/-- **The second chart and the overlap datum** of a covering given over the first chart by `I`
(scope: étale outside the nodes over `D(c₀)`). -/
structure Overlap (I : Input θ cov₀ πL) where
  /-- the second chart `V₀ = Spec B0'` and its levels -/
  B0' : Type u
  [commRingB0' : CommRing B0']
  [algOB0' : Algebra O B0']
  B' : ℕ → Type u
  [commRingB' : ∀ n, CommRing (B' n)]
  [algOB' : ∀ n, Algebra O (B' n)]
  [algB0'B' : ∀ n, Algebra B0' (B' n)]
  [towerOB' : ∀ n, IsScalarTower O B0' (B' n)]
  /-- the overlap `W0 = B0[1/x₁] = B0'[1/x₀]` and its levels -/
  W0 : Type u
  [commRingW0 : CommRing W0]
  [algB0W0 : Algebra I.B0 W0]
  [algB0'W0 : Algebra B0' W0]
  [algOB0 : Algebra O I.B0]
  [algOW0 : Algebra O W0]
  [towerOB0W0 : IsScalarTower O I.B0 W0]
  [towerOB0'W0 : IsScalarTower O B0' W0]
  W : ℕ → Type u
  [commRingW : ∀ n, CommRing (W n)]
  [algOW : ∀ n, Algebra O (W n)]
  [algBW : ∀ n, Algebra (I.B n) (W n)]
  [algB'W : ∀ n, Algebra (B' n) (W n)]
  [towerOBW : ∀ n, IsScalarTower O (I.B n) (W n)]
  [towerOB'W : ∀ n, IsScalarTower O (B' n) (W n)]
  [algW0W : ∀ n, Algebra W0 (W n)]
  x0 : B0'
  c0 : B0'
  x1 : I.B0
  g : I.B0
  hW0 : IsLocalization.Away x1 W0
  hxW0 : algebraMap B0' W0 x0 * algebraMap I.B0 W0 x1 = 1
  hcW0 : algebraMap B0' W0 c0 * algebraMap I.B0 W0 x1 ^ 2 = algebraMap I.B0 W0 g
  hx1g : x1 ∣ g
  hWn0 : ∀ n, IsLocalization.Away (algebraMap B0' (B' n) x0) (W n)
  hWn1 : ∀ n, IsLocalization.Away (algebraMap I.B0 (I.B n) x1) (W n)
  hWB : ∀ n b, algebraMap W0 (W n) (algebraMap I.B0 W0 b) =
    algebraMap (I.B n) (W n) (algebraMap I.B0 (I.B n) b)
  hWB' : ∀ n y, algebraMap W0 (W n) (algebraMap B0' W0 y) =
    algebraMap (B' n) (W n) (algebraMap B0' (B' n) y)
  /-- `D(g)` misses the nodes -/
  kg : ℕ → ℕ
  hfg : ∀ n, I.T.f n ∣ algebraMap (I.B n) (I.R n) (algebraMap I.B0 (I.B n) g) ^ kg n
  /-- the special fibres -/
  Bs' : Type u
  [commRingBs' : CommRing Bs']
  qB' : ∀ n, B' n →+* Bs'
  Ws : Type u
  [commRingWs : CommRing Ws]
  [algBsWs : Algebra I.Bs Ws]
  [algBs'Ws : Algebra Bs' Ws]
  qW : ∀ n, W n →+* Ws
  hq1 : ∀ n r, qW n (algebraMap (I.B n) (W n) r) = algebraMap I.Bs Ws (I.qB n r)
  hq0 : ∀ n y, qW n (algebraMap (B' n) (W n) y) = algebraMap Bs' Ws (qB' n y)
  x0s : Bs'
  c0s : Bs'
  x1s : I.Bs
  gs : I.Bs
  hx0 : ∀ n, qB' n (algebraMap B0' (B' n) x0) = x0s
  hc0 : ∀ n, qB' n (algebraMap B0' (B' n) c0) = c0s
  hx1 : ∀ n, I.qB n (algebraMap I.B0 (I.B n) x1) = x1s
  hg : ∀ n, I.qB n (algebraMap I.B0 (I.B n) g) = gs
  hcg : algebraMap Bs' Ws c0s * algebraMap I.Bs Ws x1s ^ 2 = algebraMap I.Bs Ws gs
  /-- the special-fibre covering over `V₀` and the overlap datum `ω` -/
  C0 : Type u
  [commRingC0 : CommRing C0]
  [algC0 : Algebra Bs' C0]
  [algWs1 : Algebra Ws (Localization.Away (algebraMap I.Bs I.C1 x1s))]
  [towerWs1 : IsScalarTower I.Bs Ws (Localization.Away (algebraMap I.Bs I.C1 x1s))]
  [algWs0 : Algebra Ws (Localization.Away (algebraMap Bs' C0 x0s))]
  [towerWs0 : IsScalarTower Bs' Ws (Localization.Away (algebraMap Bs' C0 x0s))]
  ω : Localization.Away (algebraMap Bs' C0 x0s) ≃ₐ[Ws] Localization.Away (algebraMap I.Bs I.C1 x1s)
  /-- the étale lifts of `C0` over `D(c₀)` -/
  E0 : ℕ → Type u
  [commRingE0 : ∀ n, CommRing (E0 n)]
  [algB'E0 : ∀ n, Algebra (B' n) (E0 n)]
  [algOE0 : ∀ n, Algebra O (E0 n)]
  [towerOE0 : ∀ n, IsScalarTower O (B' n) (E0 n)]
  [etaleE0 : ∀ n, Algebra.FormallyEtale (B' n) (E0 n)]
  σE0 : ∀ n, letI := ((algebraMap Bs' C0).comp (qB' n)).toAlgebra
    (E0 n ⧸ EtaleNil.JB (J θ (R := B' n)) (E0 n)) ≃ₐ[B' n] Localization.Away (algebraMap Bs' C0 c0s)
  hcE0 : ∀ n, IsUnit (algebraMap (B' n) (E0 n) (algebraMap B0' (B' n) c0))
  /-- `V₀ = D(x₀) ∪ D(c₀)` -/
  hxc : Ideal.span {x0, c0} = ⊤
  /-- finiteness: the charts are finite over `O[X]` (via `x₁`, `x₀`), the levels are quotients,
  the étale pieces are finite over `D(b₀)`, `D(c₀)`, `W0 = B0'[1/x₀]` -/
  hW0' : IsLocalization.Away x0 W0
  finB0 : letI := (Polynomial.aeval x1 : Polynomial O →ₐ[O] I.B0).toRingHom.toAlgebra
    Module.Finite (Polynomial O) I.B0
  finB0' : letI := (Polynomial.aeval x0 : Polynomial O →ₐ[O] B0').toRingHom.toAlgebra
    Module.Finite (Polynomial O) B0'
  surjB : ∀ n, Function.Surjective (algebraMap I.B0 (I.B n))
  surjB' : ∀ n, Function.Surjective (algebraMap B0' (B' n))
  hfinE : ∀ n, ∃ s : Finset (I.E n), ∀ p : I.E n, ∃ k : ℕ,
    algebraMap I.B0 (I.B n) I.b0 ^ k • p ∈ Submodule.span (I.B n) (s : Set (I.E n))
  hfinE0 : ∀ n, ∃ s : Finset (E0 n), ∀ p : E0 n, ∃ k : ℕ,
    algebraMap B0' (B' n) c0 ^ k • p ∈ Submodule.span (B' n) (s : Set (E0 n))
  /-- the successor maps over `V₀` -/
  [algSuccB' : ∀ n, Algebra (B' (n + 1)) (B' n)]
  [towerOSuccB' : ∀ n, IsScalarTower O (B' (n + 1)) (B' n)]
  [towerB0'SuccB' : ∀ n, IsScalarTower B0' (B' (n + 1)) (B' n)]
  sE0 : ∀ n, E0 (n + 1) →+* E0 n
  hsE0 : ∀ n (x : B' (n + 1)), sE0 n (algebraMap (B' (n + 1)) (E0 (n + 1)) x) =
    algebraMap (B' n) (E0 n) (algebraMap (B' (n + 1)) (B' n) x)
  hσE0 : ∀ n (x : E0 (n + 1)), σE0 n (Ideal.Quotient.mk _ (sE0 n x)) =
    σE0 (n + 1) (Ideal.Quotient.mk _ x)
  hsE0s : ∀ n, Function.Surjective (sE0 n)
  [algSuccW : ∀ n, Algebra (W (n + 1)) (W n)]
  hWs1 : ∀ n (x : I.B (n + 1)),
    algebraMap (W (n + 1)) (W n) (algebraMap (I.B (n + 1)) (W (n + 1)) x) =
    algebraMap (I.B n) (W n) (algebraMap (I.B (n + 1)) (I.B n) x)
  hWs0 : ∀ n (x : B' (n + 1)),
    algebraMap (W (n + 1)) (W n) (algebraMap (B' (n + 1)) (W (n + 1)) x) =
    algebraMap (B' n) (W n) (algebraMap (B' (n + 1)) (B' n) x)
  /-- the levels: killed by `ϖⁿ⁺¹`, the kernels of the successor maps are `ϖⁿ⁺¹` -/
  ϖ : O
  hOB0B : ∀ n (o : O), algebraMap I.B0 (I.B n) (algebraMap O I.B0 o) = algebraMap O (I.B n) o
  hK : ∀ n, I.K n = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O I.B0)
  hkE0 : ∀ n, RingHom.ker (sE0 n) = (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (E0 (n + 1)))
  killB : ∀ n, (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (I.B n)) = ⊥
  killB' : ∀ n, (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap O (B' n)) = ⊥

namespace Overlap

attribute [instance] commRingB0' algOB0' commRingB' algOB' algB0'B' towerOB' commRingW0 algB0W0
  algB0'W0 algOW0 towerOB0W0 towerOB0'W0 commRingW algOW algBW algB'W towerOBW towerOB'W algW0W
  commRingBs' commRingWs algBsWs
  algBs'Ws commRingC0 algC0 algWs1 towerWs1 algWs0 towerWs0 commRingE0 algB'E0 algOE0 towerOE0
  etaleE0 algSuccB' towerOSuccB' towerB0'SuccB' algSuccW

variable {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)

/-- **The étale piece over `D(c₀)` restricted to the overlap**: `E0 n[1/x₀]`. -/
abbrev M : Type u := OverlapPiece.M (algebraMap V.B0' (V.B' n) V.x0) (V.E0 n)

/-- `M n` over the level `B n` of the first chart (through the overlap). -/
@[reducible] def algBM : Algebra (I.B n) (V.M n) :=
  OverlapPiece.algBM (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.E0 n)

/-- `M n` over the first chart `B0`. -/
@[reducible] def alg0M : Algebra I.B0 (V.M n) :=
  letI := V.algBM n
  ((algebraMap (I.B n) (V.M n)).comp (algebraMap I.B0 (I.B n))).toAlgebra

/-- **The special fibre of `M n`**: `γM : C1 → M n/J`. -/
def γM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := V.algBM n
    I.C1 →ₐ[I.B n] V.M n ⧸ EtaleNil.JB (J θ (R := I.B n)) (V.M n) :=
  OverlapPiece.γM (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.E0 n) (I.qB n)
    (V.qB' n) (V.qW n) V.x1s V.x0s V.c0s V.ω (V.σE0 n) (V.hx0 n) (V.hq1 n) (V.hq0 n)

/-- **`M n/J = C1[1/ḡ]`.** -/
theorem isLocalization_γM : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    letI := V.algBM n
    letI := (V.γM n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) I.C1 (algebraMap I.B0 (I.B n) V.g))
      (V.M n ⧸ EtaleNil.JB (J θ (R := I.B n)) (V.M n)) := by
  letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
  letI := V.algBM n
  have h := OverlapPiece.isLocalization_γM (RingHom.ker θ) (algebraMap V.B0' (V.B' n) V.x0)
    (V.hWn0 n) (V.E0 n) (I.qB n) (V.qB' n) (V.qW n) V.x1s V.x0s V.c0s V.gs V.ω (V.σE0 n) (V.hx0 n)
    V.hcg (by rw [← V.hx1 n, ← V.hg n]; exact map_dvd _ (map_dvd _ V.hx1g)) (V.hq1 n) (V.hq0 n)
  have e : algebraMap I.Bs I.C1 V.gs = algebraMap (I.B n) I.C1 (algebraMap I.B0 (I.B n) V.g) := by
    rw [← V.hg n]
    rfl
  exact RingHomAway.congr _ e h

lemma formallyEtale_M : letI := V.algBM n; Algebra.FormallyEtale (I.B n) (V.M n) :=
  OverlapPiece.formallyEtale_M (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.E0 n) (V.hWn1 n)

lemma tower0M : letI := V.algBM n; letI := V.alg0M n; IsScalarTower I.B0 (I.B n) (V.M n) :=
  letI := V.algBM n
  letI := V.alg0M n
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

include hO in
/-- **The covering over `V₁` restricted to the overlap with the étale piece**:
`ψ : Y n → M n = E0 n[1/x₀]`, a localization away from `g` (`Input.ψ`). -/
def ψ : letI := V.alg0M n; I.Y hθ n →ₐ[I.B0] V.M n :=
  letI := V.algBM n
  letI := V.alg0M n
  haveI := V.formallyEtale_M n
  haveI := V.tower0M n
  I.ψ hθ hO n V.g (V.hfg n) (V.γM n) (V.isLocalization_γM n)

/-- **`M n = Y n[1/g]`.** -/
theorem isLocalization_ψ : letI := V.alg0M n
    letI := (V.ψ hθ hO n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap I.B0 (I.Y hθ n) V.g) (V.M n) :=
  letI := V.algBM n
  letI := V.alg0M n
  haveI := V.formallyEtale_M n
  haveI := V.tower0M n
  I.isLocalization_ψ hθ hO n V.g (V.hfg n) (V.γM n) (V.isLocalization_γM n)

/-! ### The piece over `V₀` as a `TwoChartGlue.Patch0` -/

/-- The sections over `D(x₁) ⊆ V₁`: `Q n = Y n[1/x₁]`. -/
abbrev Q : Type u := Localization.Away (algebraMap I.B0 (I.Y hθ n) V.x1)

lemma isUnit_x1_Q : IsUnit (algebraMap I.B0 (V.Q hθ n) V.x1) := by
  rw [IsScalarTower.algebraMap_apply I.B0 (I.Y hθ n) (V.Q hθ n)]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `Q n` over the overlap `W0 = B0[1/x₁]`. -/
@[reducible] def algW0Q : Algebra V.W0 (V.Q hθ n) :=
  haveI := V.hW0
  (IsLocalization.Away.lift V.x1 (S := V.W0) (g := algebraMap I.B0 (V.Q hθ n))
    (V.isUnit_x1_Q hθ n)).toAlgebra

lemma algW0Q_algebraMap (b : I.B0) :
    (letI := V.algW0Q hθ n; algebraMap V.W0 (V.Q hθ n) (algebraMap I.B0 V.W0 b)) =
      algebraMap I.B0 (V.Q hθ n) b :=
  haveI := V.hW0
  IsLocalization.Away.lift_eq V.x1 (V.isUnit_x1_Q hθ n) b

/-- `Q n` over the second chart `B0'` (through the overlap). -/
@[reducible] def alg0'Q : Algebra V.B0' (V.Q hθ n) :=
  letI := V.algW0Q hθ n
  ((algebraMap V.W0 (V.Q hθ n)).comp (algebraMap V.B0' V.W0)).toAlgebra

/-- `Q n` over `O` (through `B0'`). -/
@[reducible] def algOQ : Algebra O (V.Q hθ n) :=
  letI := V.alg0'Q hθ n
  ((algebraMap V.B0' (V.Q hθ n)).comp (algebraMap O V.B0')).toAlgebra

lemma towerOQ : letI := V.alg0'Q hθ n; letI := V.algOQ hθ n
    IsScalarTower O V.B0' (V.Q hθ n) :=
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `E0 n` over `B0'`. -/
@[reducible] def alg0'E : Algebra V.B0' (V.E0 n) :=
  ((algebraMap (V.B' n) (V.E0 n)).comp (algebraMap V.B0' (V.B' n))).toAlgebra

/-- `M n` over `B0'`. -/
@[reducible] def alg0'M : Algebra V.B0' (V.M n) :=
  ((algebraMap (V.B' n) (V.M n)).comp (algebraMap V.B0' (V.B' n))).toAlgebra

lemma towerOE : letI := V.alg0'E n; IsScalarTower O V.B0' (V.E0 n) := by
  letI := V.alg0'E n
  refine IsScalarTower.of_algebraMap_eq fun o ↦ ?_
  change _ = algebraMap (V.B' n) (V.E0 n) (algebraMap V.B0' (V.B' n) (algebraMap O V.B0' o))
  rw [← IsScalarTower.algebraMap_apply O V.B0' (V.B' n),
    ← IsScalarTower.algebraMap_apply O (V.B' n) (V.E0 n)]

lemma towerOM : letI := V.alg0'M n; IsScalarTower O V.B0' (V.M n) := by
  letI := V.alg0'M n
  refine IsScalarTower.of_algebraMap_eq fun o ↦ ?_
  change _ = algebraMap (V.B' n) (V.M n) (algebraMap V.B0' (V.B' n) (algebraMap O V.B0' o))
  rw [IsScalarTower.algebraMap_apply O (V.B' n) (V.M n),
    IsScalarTower.algebraMap_apply O V.B0' (V.B' n)]

/-- `M n` over the overlap `W n`. -/
@[reducible] def algWM : Algebra (V.W n) (V.M n) :=
  OverlapPiece.algWM (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.E0 n)

include hθ hO in
lemma isUnit_x1_M : letI := V.alg0M n; IsUnit (algebraMap I.B0 (V.M n) V.x1) := by
  letI := V.alg0M n
  letI := (V.ψ hθ hO n).toRingHom.toAlgebra
  haveI := V.isLocalization_ψ hθ hO n
  have h := IsLocalization.Away.algebraMap_isUnit (S := V.M n) (algebraMap I.B0 (I.Y hθ n) V.g)
  change IsUnit (V.ψ hθ hO n (algebraMap I.B0 (I.Y hθ n) V.g)) at h
  rw [AlgHom.commutes] at h
  exact isUnit_of_dvd_unit (map_dvd _ V.hx1g) h

/-- The restriction map `Q n → M n` (as a ring map). -/
def ρ0aR : V.Q hθ n →+* V.M n :=
  letI := V.alg0M n
  IsLocalization.Away.lift (algebraMap I.B0 (I.Y hθ n) V.x1)
    (g := (V.ψ hθ hO n : I.Y hθ n →+* V.M n)) (by
      rw [RingHom.coe_coe, AlgHom.commutes]
      exact V.isUnit_x1_M hθ hO n)

lemma ρ0aR_algebraMap (y : I.Y hθ n) :
    V.ρ0aR hθ hO n (algebraMap (I.Y hθ n) (V.Q hθ n) y) = V.ψ hθ hO n y :=
  letI := V.alg0M n
  IsLocalization.Away.lift_eq _ _ y

/-- `Q n → M n` is `W0`-linear. -/
lemma ρ0aR_W0 (w : V.W0) : V.ρ0aR hθ hO n (letI := V.algW0Q hθ n; algebraMap V.W0 (V.Q hθ n) w) =
    (letI := V.algWM n; algebraMap (V.W n) (V.M n) (algebraMap V.W0 (V.W n) w)) := by
  letI := V.algW0Q hθ n
  letI := V.algWM n
  letI := V.alg0M n
  haveI := V.hW0
  have : (V.ρ0aR hθ hO n).comp (algebraMap V.W0 (V.Q hθ n)) =
      (algebraMap (V.W n) (V.M n)).comp (algebraMap V.W0 (V.W n)) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers V.x1) (RingHom.ext fun b ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [V.algW0Q_algebraMap hθ n, IsScalarTower.algebraMap_apply I.B0 (I.Y hθ n) (V.Q hθ n),
      ρ0aR_algebraMap, AlgHom.commutes, V.hWB n]
    rfl
  exact RingHom.congr_fun this w

/-- **The restriction map `ρ0a : Q n → M n`** over `B0'`. -/
def ρ0a : letI := V.alg0'Q hθ n; letI := V.alg0'M n; V.Q hθ n →ₐ[V.B0'] V.M n :=
  letI := V.alg0'Q hθ n
  letI := V.alg0'M n
  { V.ρ0aR hθ hO n with
    commutes' := fun y ↦ by
      letI := V.algW0Q hθ n
      letI := V.algWM n
      change V.ρ0aR hθ hO n (algebraMap V.W0 (V.Q hθ n) (algebraMap V.B0' V.W0 y)) = _
      rw [ρ0aR_W0, V.hWB' n]
      exact OverlapPiece.algWM_algebraMap (algebraMap V.B0' (V.B' n) V.x0) (V.hWn0 n) (V.E0 n) _ }

/-- **`M n = Q n[1/c₀]`.** -/
theorem isLocalization_ρ0a : letI := V.alg0'Q hθ n
    letI := (V.ρ0aR hθ hO n).toAlgebra
    IsLocalization.Away (algebraMap V.B0' (V.Q hθ n) V.c0) (V.M n) := by
  letI := V.alg0M n
  letI := V.algW0Q hθ n
  letI := V.alg0'Q hθ n
  set Y := I.Y hθ n
  set x1Y := algebraMap I.B0 Y V.x1
  set gY := algebraMap I.B0 Y V.g
  have hψ := V.isLocalization_ψ hθ hO n
  have hu : IsUnit ((V.ψ hθ hO n : Y →+* V.M n) x1Y) := by
    rw [RingHom.coe_coe, AlgHom.commutes]
    exact V.isUnit_x1_M hθ hO n
  have h1 : letI := (V.ψ hθ hO n : Y →+* V.M n).toAlgebra
      IsLocalization.Away (x1Y * gY) (V.M n) := by
    letI := (V.ψ hθ hO n : Y →+* V.M n).toAlgebra
    haveI : IsLocalization.Away gY (V.M n) := hψ
    exact OverlapFibre.away_mul_of_isUnit x1Y gY hu
  have hc : (V.ρ0aR hθ hO n).comp (algebraMap Y (V.Q hθ n)) = (V.ψ hθ hO n : Y →+* V.M n) :=
    IsLocalization.Away.lift_comp _ _
  rw [← hc] at h1
  have h2 := RingHomAway.of_comp (algebraMap Y (V.Q hθ n)) (V.ρ0aR hθ hO n) _ _
    (RingHomAway.of_algebra x1Y) h1
  have e : algebraMap Y (V.Q hθ n) gY =
      algebraMap I.B0 (V.Q hθ n) V.x1 ^ 2 * algebraMap V.B0' (V.Q hθ n) V.c0 := by
    rw [← IsScalarTower.algebraMap_apply, ← V.algW0Q_algebraMap hθ n, ← V.hcW0,
      ← V.algW0Q_algebraMap hθ n, map_mul, map_pow, mul_comm]
    rfl
  rw [e] at h2
  exact RingHomAway.of_dvd _ _ _ 0 (by rw [pow_zero]; exact ((V.isUnit_x1_Q hθ n).pow 2).dvd) h2

/-- `ρ0a` as a map of `B0'`-algebras is a localization away from `c₀`. -/
theorem isLocalization_ρ0a' : letI := V.alg0'Q hθ n; letI := V.alg0'M n
    letI := (V.ρ0a hθ hO n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' (V.Q hθ n) V.c0) (V.M n) :=
  V.isLocalization_ρ0a hθ hO n

/-- **The localization map `ρ0b : E0 n → M n = E0 n[1/x₀]`** over `B0'`. -/
def ρ0b : letI := V.alg0'E n; letI := V.alg0'M n; V.E0 n →ₐ[V.B0'] V.M n :=
  letI := V.alg0'E n
  letI := V.alg0'M n
  { algebraMap (V.E0 n) (V.M n) with
    commutes' := fun _ ↦ (IsScalarTower.algebraMap_apply (V.B' n) (V.E0 n) (V.M n) _).symm }

/-- `M n = E0 n[1/x₀]`. -/
theorem isLocalization_ρ0b : letI := V.alg0'E n; letI := V.alg0'M n
    letI := (V.ρ0b n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' (V.E0 n) V.x0) (V.M n) := by
  letI := V.alg0'E n
  exact RingHomAway.of_algebra (algebraMap (V.B' n) (V.E0 n) (algebraMap V.B0' (V.B' n) V.x0))

/-- **The piece over `V₀` at level `n`** (`TwoChartGlue.Patch0`): `E0 n` over `D(c₀)`, glued with
`Q n = Y n[1/x₁]` along `M n`. -/
def patch0 : letI := V.alg0'Q hθ n; letI := V.algOQ hθ n; haveI := V.towerOQ hθ n
    TwoChartGlue.Patch0 (A := O) (V.Q hθ n) V.x0 :=
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  letI := V.alg0'E n
  haveI := V.towerOE n
  letI := V.alg0'M n
  haveI := V.towerOM n
  { b0 := V.c0
    P0b := V.E0 n
    P0ab := V.M n
    ρ0a := V.ρ0a hθ hO n
    ρ0b := V.ρ0b n
    hunit := V.hcE0 n
    hb0 := V.isLocalization_ρ0b n
    ha0 := V.isLocalization_ρ0a' hθ hO n }

/-! ### The two-chart rings at level `n` -/

/-- `Y n` over `O` (through `B0`). -/
@[reducible] def algOY : Algebra O (I.Y hθ n) :=
  letI := V.algOB0
  ((algebraMap I.B0 (I.Y hθ n)).comp (algebraMap O I.B0)).toAlgebra

/-- The localization `Y n → Q n` over `O`. -/
def ιQ : letI := V.algOY hθ n; letI := V.algOQ hθ n; I.Y hθ n →ₐ[O] V.Q hθ n :=
  letI := V.algOY hθ n
  letI := V.algOQ hθ n
  { algebraMap (I.Y hθ n) (V.Q hθ n) with
    commutes' := fun o ↦ by
      letI := V.algOB0
      letI := V.algW0Q hθ n
      change algebraMap (I.Y hθ n) (V.Q hθ n) (algebraMap I.B0 (I.Y hθ n) (algebraMap O I.B0 o)) =
        algebraMap V.W0 (V.Q hθ n) (algebraMap V.B0' V.W0 (algebraMap O V.B0' o))
      rw [← IsScalarTower.algebraMap_apply I.B0 (I.Y hθ n) (V.Q hθ n), ← V.algW0Q_algebraMap hθ n,
        ← IsScalarTower.algebraMap_apply O I.B0 V.W0,
        ← IsScalarTower.algebraMap_apply O V.B0' V.W0] }

lemma hxy : letI := V.alg0'Q hθ n
    algebraMap V.B0' (V.Q hθ n) V.x0 * V.ιQ hθ n (algebraMap I.B0 (I.Y hθ n) V.x1) = 1 := by
  letI := V.algW0Q hθ n
  letI := V.alg0'Q hθ n
  change algebraMap V.W0 (V.Q hθ n) (algebraMap V.B0' V.W0 V.x0) *
    algebraMap (I.Y hθ n) (V.Q hθ n) (algebraMap I.B0 (I.Y hθ n) V.x1) = 1
  rw [← IsScalarTower.algebraMap_apply I.B0 (I.Y hθ n) (V.Q hθ n), ← V.algW0Q_algebraMap hθ n,
    ← map_mul, V.hxW0, map_one]

/-- **The two-chart rings of the covering at level `n`** (`TwoChartGlue.Patch0.twoChart`):
`R1 = Y n`, `R01 = Q n`, `R0 = Q n ×_{M n} E0 n`. -/
def twoChart : ProjectiveLine.TwoChartRings O :=
  letI := V.alg0'Q hθ n
  letI := V.algOQ hθ n
  haveI := V.towerOQ hθ n
  letI := V.algOY hθ n
  TwoChartGlue.Patch0.twoChart (algebraMap I.B0 (I.Y hθ n) V.x1) (V.ιQ hθ n)
    (RingHomAway.of_algebra _) (V.hxy hθ n) (V.patch0 hθ hO n)

end Overlap

end NodeEtaleGlue

end

end SemistableReduction
