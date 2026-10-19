/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueTower

/-!
# The bundled input of the glueing of node patches with étale pieces (Blueprint §12.8, M2.3 (f))

All data of `NodeEtaleGlue` and `NodeEtaleGlueTower` in one structure **`NodeEtaleGlue.Input`**:
the tower of node patches `T` on node charts `R n`, the base charts `B n` (algebras over one base
`B0`, with `R n = B n[1/a0]`, `span {a0, b0} = B0`), the special-fibre covering `C1` with its
restriction to the node chart, the étale pieces `E n` over `D(b0)` with their successor maps, and
the kernels `K n` of the successor maps. Concrete coverings (the Tate curve over `V₁`) are single
definitions of type `Input`, so the generic statements apply to them without re-elaborating the
glued algebras:

* `Input.Y I n`: the covering over `Spec B n` (`NodeEtaleGlue.Y0`);
* `Input.hkG`: the kernels of the transition maps of the node patches;
* **`Input.Ymap I n : Y (n+1) → Y n`**, **`Input.surjective_Ymap`**, **`Input.ker_Ymap`**
  (kernel `K n · Y (n+1)`).
-/

universe u

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  (cov₀ : Admissible.Covering φ₀ ψ₀) (πL : cov₀.ι → O) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The input of the glueing**: a tower of node patches, base charts, the special-fibre
covering with its restriction to the node chart, étale pieces with successor maps, and the
kernels of the successor maps (of the node charts for the node patches, `hkR`: the input never
mentions the patched algebras `G n`, whose instances are expensive to synthesize for concrete
charts). -/
structure Input where
  R : ℕ → Type u
  [commRingR : ∀ n, CommRing (R n)]
  [algOR : ∀ n, Algebra O (R n)]
  [noethR : ∀ n, IsNoetherianRing (R n)]
  [algkR : ∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  [algSuccR : ∀ n, Algebra (R (n + 1)) (R n)]
  [towerOR : ∀ n, IsScalarTower O (R (n + 1)) (R n)]
  T : Data (θ := θ) R cov₀ πL
  B : ℕ → Type u
  [commRingB : ∀ n, CommRing (B n)]
  [algBR : ∀ n, Algebra (B n) (R n)]
  [algOB : ∀ n, Algebra O (B n)]
  [towerOBR : ∀ n, IsScalarTower O (B n) (R n)]
  [algSuccB : ∀ n, Algebra (B (n + 1)) (B n)]
  [towerOB : ∀ n, IsScalarTower O (B (n + 1)) (B n)]
  B0 : Type u
  [commRingB0 : CommRing B0]
  [algB0B : ∀ n, Algebra B0 (B n)]
  [towerB0 : ∀ n, IsScalarTower B0 (B (n + 1)) (B n)]
  a0 : B0
  b0 : B0
  hab : Ideal.span {a0, b0} = ⊤
  [away : ∀ n, IsLocalization.Away (algebraMap B0 (B n) a0) (R n)]
  Bs : Type u
  [commRingBs : CommRing Bs]
  qB : ∀ n, B n →+* Bs
  φs : Bs →+* R₀
  hφs : ∀ n (x : B n), T.e n (φs (qB n x)) = Ideal.Quotient.mk _ (algebraMap (B n) (R n) x)
  C1 : Type u
  [commRingC1 : CommRing C1]
  [algC1 : Algebra Bs C1]
  ι₀ : C1 →+* cov₀.C
  hι₀ : ∀ x : Bs, ι₀ (algebraMap Bs C1 x) = algebraMap R₀ cov₀.C (φs x)
  abar : Bs
  bbar : Bs
  ha : ∀ n, qB n (algebraMap B0 (B n) a0) = abar
  hι : letI := ι₀.toAlgebra; IsLocalization.Away (algebraMap Bs C1 abar) cov₀.C
  hbb : ∀ n, qB n (algebraMap B0 (B n) b0) = bbar
  E : ℕ → Type u
  [commRingE : ∀ n, CommRing (E n)]
  [algBE : ∀ n, Algebra (B n) (E n)]
  [etaleE : ∀ n, Algebra.FormallyEtale (B n) (E n)]
  σE : ∀ n, letI := NodeEtaleGlue.algC1 B qB C1 n
    (E n ⧸ EtaleNil.JB (J θ (R := B n)) (E n)) ≃ₐ[B n] Localization.Away (algebraMap Bs C1 bbar)
  hbE : ∀ n, IsUnit (algebraMap (B n) (E n) (algebraMap B0 (B n) b0))
  kdiv : ℕ → ℕ
  hdiv : ∀ n, T.f n ∣ algebraMap (B n) (R n) (algebraMap B0 (B n) b0) ^ kdiv n
  mB : ℕ → ℕ
  hJB : ∀ n, J θ (R := B n) ^ mB n = ⊥
  hBR : ∀ n (x : B (n + 1)), algebraMap (R (n + 1)) (R n) (algebraMap (B (n + 1)) (R (n + 1)) x) =
    algebraMap (B n) (R n) (algebraMap (B (n + 1)) (B n) x)
  sE : ∀ n, E (n + 1) →+* E n
  hsE : ∀ n (x : B (n + 1)), sE n (algebraMap (B (n + 1)) (E (n + 1)) x) =
    algebraMap (B n) (E n) (algebraMap (B (n + 1)) (B n) x)
  hσE : ∀ n (x : E (n + 1)), σE n (Ideal.Quotient.mk _ (sE n x)) =
    σE (n + 1) (Ideal.Quotient.mk _ x)
  hsEs : ∀ n, Function.Surjective (sE n)
  K : ℕ → Ideal B0
  hkR : ∀ n, RingHom.ker (algebraMap (R (n + 1)) (R n)) =
    (K n).map ((algebraMap (B (n + 1)) (R (n + 1))).comp (algebraMap B0 (B (n + 1))))
  hkE : ∀ n, RingHom.ker (sE n) =
    (K n).map (letI := alg0 B B0 (n + 1) (E (n + 1)); algebraMap B0 (E (n + 1)))

namespace Input

attribute [instance] commRingR algOR noethR algkR algSuccR towerOR commRingB algBR algOB towerOBR
  algSuccB towerOB commRingB0 algB0B towerB0 away commRingBs commRingC1 algC1 commRingE algBE etaleE

variable {θ cov₀ πL} (I : Input θ cov₀ πL)

/-- The family `a n`. -/
abbrev a (n : ℕ) : I.B n := algebraMap I.B0 (I.B n) I.a0

/-- The family `b n`. -/
abbrev b (n : ℕ) : I.B n := algebraMap I.B0 (I.B n) I.b0

lemma haS (n : ℕ) : algebraMap (I.B (n + 1)) (I.B n) (I.a (n + 1)) = I.a n :=
  (IsScalarTower.algebraMap_apply I.B0 (I.B (n + 1)) (I.B n) I.a0).symm

/-- The kernels of the transition maps of the node patches (`LevelTower.Data.ker_tr`). -/
theorem hkG (n : ℕ) : RingHom.ker (I.T.tr hθ hO n) =
    (I.K n).map (letI := alg0G I.T hθ I.B I.B0 (n + 1); algebraMap I.B0 (I.T.G hθ (n + 1))) := by
  rw [I.T.ker_tr hθ hO n, I.hkR n, Ideal.map_map]
  rfl

/-- **The covering over `Spec B n`** (`NodeEtaleGlue.Y0`). -/
abbrev Y (n : ℕ) : Type u :=
  Y0 I.T hθ I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE I.hdiv I.hJB I.B0 n

/-- **The successor maps** `Y (n+1) → Y n` (`NodeEtaleGlue.Ymap`). -/
def Ymap (n : ℕ) : I.Y hθ (n + 1) →ₐ[I.B0] I.Y hθ n :=
  NodeEtaleGlue.Ymap I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E I.σE I.hbE
    I.hdiv I.hJB I.hBR I.haS I.sE I.hsE I.hσE I.B0 n

/-- **The successor maps are surjective.** -/
theorem surjective_Ymap (n : ℕ) : Function.Surjective (I.Ymap hθ hO n) :=
  NodeEtaleGlue.surjective_Ymap I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E
    I.σE I.hbE I.hdiv I.hbb I.hJB I.hBR I.haS I.sE I.hsE I.hσE I.B0 (fun _ ↦ rfl) (fun _ ↦ rfl)
    I.hab I.K I.hsEs (I.hkG hθ hO) I.hkE n

/-- **The kernel of the successor map is `K n · Y (n+1)`.** -/
theorem ker_Ymap (n : ℕ) :
    RingHom.ker (I.Ymap hθ hO n) = (I.K n).map (algebraMap I.B0 (I.Y hθ (n + 1))) :=
  NodeEtaleGlue.ker_Ymap I.T hθ I.B hO I.qB I.φs I.hφs I.ι₀ I.hι₀ I.a I.b I.ha I.hι I.E
    I.σE I.hbE I.hdiv I.hbb I.hJB I.hBR I.haS I.sE I.hsE I.hσE I.B0 (fun _ ↦ rfl) (fun _ ↦ rfl)
    I.hab I.K I.hsEs (I.hkG hθ hO) I.hkE n

end Input

end NodeEtaleGlue

end

end SemistableReduction
