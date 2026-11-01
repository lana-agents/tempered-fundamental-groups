/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Cusp
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelSucc

/-!
# The levels over `V₀` with the patch side from cusp level data (MR12 T2 S6, G4 over `V₀`)

Let `V : NodeEtaleGlue.Overlap I` be a covering over the second chart whose piece over `D(c₀)` is
the piece of a patch `Dp` (`hP0 : V.P0 = Dp.piece`), and `Vc` cusp level data whose tower is the
tower of `Dp` (as in `NodeEtaleGlueV0Cusp`). For a `B0'`-algebra `X` with a localization
`t : X → Dp.R l ⊗_R B` away from `c₀` and a reduction `ρX : X → C0`:

* **`NodeEtaleGlue.Overlap.φPof`**: the patch side `X → V.P0.P l` (`CuspLevels.φPX`, transported
  along `hP0`), **`hPof`** (a localization away from `c₀`), **`hPℓof`** (its special fibre on
  `D(x₀)` is `ℓ0 ∘ ρX`), **`sP_φPof`** (compatibility with the successor maps of `V.P0`);
* **`NodeEtaleGlue.Overlap.levelEquiv0P`**: `levelEquiv0X` with this patch side, i.e.
  `X0 ≃ₐ[B0'] Q n ×_{M n} P0 n` built from `e1`, `ωn` and the cusp data only;
* **`NodeEtaleGlue.Overlap.f0_levelEquiv0P`**: these identifications commute with the successor
  maps `f0 n` of the covering.

The equation `hP0` is used only through `subst` on a general piece, so at concrete data (the Tate
curve) the patch side is never elaborated through the projections of `V.P0`: there `hP0` is `rfl`.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace NodeEtaleGlue

namespace Overlap

noncomputable section

open FormalKummer AdmissibleLift FormalLevel FormalCuspLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]
  {R₁ : Type u} [CommRing R₁] [Algebra k R₁] {f₁ : R₁}
  {φ₁ : Node k (0 : k) →ₐ[k] Admissible.Hat f₁} {ψ₁ : Polynomial k →ₐ[k] Admissible.Hat f₁}
  {cov₁ : Admissible.Covering φ₁ ψ₁} {πL₁ : cov₁.ι → O}
  {I : Input θ cov₁ πL₁} (V : Overlap I) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  {hJ : ∀ j, J θ (R := R) ≤ 𝔪 j} {s : R} {E : ι → ℕ}
  {D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (E j) (𝔪 j)} {g : R}
  {hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j)}
  {hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j)}
  {hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g)}
  {ψk : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g)}
  {hψ : ψk Polynomial.X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s)}
  {hfin : Module.Finite (Rs θ R) (Cs θ R B)}
  {het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale}
  {hk : ∀ j i, ((D j).d i : k) ≠ 0}
  {πL : (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).ι → O}
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
  (Dp : PatchInput θ V.B' V.qB' V.C0 V.x0 V.c0 V.x0s V.c0s V.ϖ
    (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL)
  [algRI : ∀ l, Algebra R (Dp.R l)] [towerORI : ∀ l, IsScalarTower O R (Dp.R l)]
  [towerRII : ∀ l, IsScalarTower R (Dp.R (l + 1)) (Dp.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    LevelTower.Data (θ := θ) Dp.R (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL}
  {he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Dp.R l) r)}
  (Vc : CuspLevels 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T' he)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)) = Dp.algkR) (hT : HEq T' Dp.T)

section Patch

variable (P : Piece0 θ V.B' V.qB' V.C0 V.x0 V.c0 V.x0s V.c0s V.ϖ) (hP : P = Dp.piece hθ.out hO)
  {l : ℕ} {X : Type u} [CommRing X] [Algebra V.B0' X]
  (t : X →+* Dp.R l ⊗[R] B)
  (ht : ∀ r, t (algebraMap V.B0' X r) = algebraMap (Dp.R l) (Dp.R l ⊗[R] B)
    (algebraMap (V.B' l) (Dp.R l) (algebraMap V.B0' (V.B' l) r)))

/-- **The patch side `X → P l`** for a piece `P` equal to the piece of `Dp`
(`CuspLevels.φPX`). -/
def φPof : letI := ((algebraMap (V.B' l) (P.P l)).comp (algebraMap V.B0' (V.B' l))).toAlgebra
    X →ₐ[V.B0'] P.P l := by
  subst hP
  exact Vc.φPX Dp hO hkI hT t ht

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
/-- The patch side is a localization away from `c₀`. -/
theorem hPof (htloc : letI := t.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X V.c0) (Dp.R l ⊗[R] B)) :
    letI := ((algebraMap (V.B' l) (P.P l)).comp (algebraMap V.B0' (V.B' l))).toAlgebra
    letI := (V.φPof hO Dp Vc hkI hT P hP t ht).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X V.c0) (P.P l) := by
  subst hP
  exact Vc.isLocalization_φPX Dp hO hkI hT t ht htloc

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
/-- **The special fibre of the patch side on `D(x₀)` is `ℓ0 ∘ ρX`.** -/
theorem hPℓof (ρX : X →+* V.C0)
    (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
      ∀ x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he l (t x) = Dp.ι₀ (ρX x))
    (x : X) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := V.B' l)) (Loc0 (V.B' l) (P.P l) V.x0))
      (algebraMap (P.P l) (Loc0 (V.B' l) (P.P l) V.x0) (V.φPof hO Dp Vc hkI hT P hP t ht x)) =
      P.ℓ0 l (ρX x) := by
  subst hP
  exact Vc.mk_Loc_φPX Dp hO hkI hT t ρX hρ x

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **The patch sides commute with the successor maps of the piece.** -/
theorem sP_φPof {X' : Type u} [CommRing X'] [Algebra V.B0' X']
    (t' : X' →+* Dp.R (l + 1) ⊗[R] B)
    (ht' : ∀ r, t' (algebraMap V.B0' X' r) = algebraMap (Dp.R (l + 1)) (Dp.R (l + 1) ⊗[R] B)
      (algebraMap (V.B' (l + 1)) (Dp.R (l + 1)) (algebraMap V.B0' (V.B' (l + 1)) r)))
    (μ : X' →+* X) (hμt : ∀ x, t (μ x) = levelMap Dp.R l (t' x)) (x : X') :
    P.sP l (V.φPof hO Dp Vc hkI hT P hP t' ht' x) = V.φPof hO Dp Vc hkI hT P hP t ht (μ x) := by
  subst hP
  exact Vc.φPX_succ Dp hO hkI hT t ht t' ht' μ hμt x

end Patch

variable (hP0 : V.P0 = Dp.piece hθ.out hO) (n : ℕ)
  {X1 : Type u} [CommRing X1] [Algebra I.B0 X1] [Algebra (I.B n) X1]
  (e1 : X1 ≃ₐ[I.B0] I.Y hθ.out n)
  {X0 : Type u} [CommRing X0] [Algebra V.B0' X0]
  (ωn : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0) V.x0
    letI := awayAlg (W := V.W0) (C := X1) V.x1
    Localization.Away (algebraMap V.B0' X0 V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1 V.x1))
  (t : X0 →+* Dp.R n ⊗[R] B)
  (ht : ∀ r, t (algebraMap V.B0' X0 r) = algebraMap (Dp.R n) (Dp.R n ⊗[R] B)
    (algebraMap (V.B' n) (Dp.R n) (algebraMap V.B0' (V.B' n) r)))
  (htloc : letI := t.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X0 V.c0) (Dp.R n ⊗[R] B))
  (ρX1 : letI := algC1 I.B I.qB I.C1 n; X1 →ₐ[I.B n] I.C1) (ρX0 : X0 →+* V.C0)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he n (t x) = Dp.ι₀ (ρX0 x))
  {m : ℕ} (hJm : J θ (R := V.B' n) ^ m = ⊥)
  (hψ1 : ∀ y, (letI := V.algBM n; Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (V.M n))
    (V.ψ hθ.out hO n (e1 y))) = V.γM n (ρX1 y))
  (hx1 : ρX1 (algebraMap I.B0 X1 V.x1) = algebraMap I.Bs I.C1 V.x1s)
  (hω : ∀ x : X0, ∃ (y : X1) (k : ℕ),
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0) V.x0
      letI := awayAlg (W := V.W0) (C := X1) V.x1
      ωn (algebraMap X0 _ x) *
        algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1)) (algebraMap I.B0 X1 V.x1) ^ k =
        algebraMap X1 _ y) ∧
    V.ω (algebraMap V.C0 _ (ρX0 x)) *
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
          (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 y))

omit hθ [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **The hypothesis `hx1`** for a reduction `ρX1` over `I.B n` (`x₁` comes from `I.B n`). -/
theorem hx1_of_algHom [towerB : IsScalarTower I.B0 (I.B n) X1] :
    ρX1 (algebraMap I.B0 X1 V.x1) = algebraMap I.Bs I.C1 V.x1s := by
  letI := algC1 I.B I.qB I.C1 n
  rw [IsScalarTower.algebraMap_apply I.B0 (I.B n) X1, AlgHom.commutes]
  exact congrArg (algebraMap I.Bs I.C1) (V.hx1 n)

omit hθ [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **The hypothesis `hω` from generators** (`hω_of_mk` with `ω' = V.ω` and the reduction `ρX1`
over `I.B n`). -/
theorem hω_of_mkA {Z Z1 : Type u} (q0 : Z → X0) (hq0 : Function.Surjective q0) (q1 : Z1 → X1)
    (H : ∀ b : Z, ∃ (y : Z1) (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ (q0 b)) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k =
          algebraMap X1 _ (q1 y)) ∧
      V.ω (algebraMap V.C0 _ (ρX0 (q0 b))) *
          algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
            (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 (q1 y))) :
    ∀ x : X0, ∃ (y : X1) (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ x) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k =
          algebraMap X1 _ y) ∧
      V.ω (algebraMap V.C0 _ (ρX0 x)) *
          algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
            (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 y) := by
  intro x
  obtain ⟨b, rfl⟩ := hq0 x
  obtain ⟨y, k, h⟩ := H b
  exact ⟨q1 y, k, h⟩

/-- **G4 over `V₀` from cusp level data: the level `n` of the covering over the second chart is
`X0`**, `X0 ≃ₐ[B0'] Q n ×_{M n} P0 n` (`levelEquiv0X` with the patch side `φPof` of the cusp
level data `Vc` along `hP0 : V.P0 = Dp.piece`). -/
def levelEquiv0P : letI := V.alg0'Q hθ.out n; letI := V.alg0'E n; letI := V.alg0'M n
    X0 ≃ₐ[V.B0'] ZariskiTwo.glued (V.ρ0a hθ.out hO n) (V.ρ0b n) :=
  letI := algC1 I.B I.qB I.C1 n
  V.levelEquiv0X hθ.out hO n e1 ωn (V.φPof hO Dp Vc hkI hT V.P0 hP0 t ht) ρX1.toRingHom ρX0
    (V.hPof hO Dp Vc hkI hT V.P0 hP0 t ht htloc) hJm hψ1 hx1 hω
    (V.hPℓof hO Dp Vc hkI hT V.P0 hP0 t ht ρX0 hρ)

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
lemma levelEquiv0P_fst (x : X0) :
    (V.levelEquiv0P hO Dp Vc hkI hT hP0 n e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω x).1.1 =
      V.φQn hθ.out n e1 ωn x := rfl

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
lemma levelEquiv0P_snd (x : X0) :
    (V.levelEquiv0P hO Dp Vc hkI hT hP0 n e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω x).1.2 =
      V.φPof hO Dp Vc hkI hT V.P0 hP0 t ht x := rfl

variable {X1' : Type u} [CommRing X1'] [Algebra I.B0 X1'] [Algebra (I.B (n + 1)) X1']
  (e1' : X1' ≃ₐ[I.B0] I.Y hθ.out (n + 1))
  {X0' : Type u} [CommRing X0'] [Algebra V.B0' X0']
  (ωn' : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0') V.x0
    letI := awayAlg (W := V.W0) (C := X1') V.x1
    Localization.Away (algebraMap V.B0' X0' V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1' V.x1))
  (t' : X0' →+* Dp.R (n + 1) ⊗[R] B)
  (ht' : ∀ r, t' (algebraMap V.B0' X0' r) = algebraMap (Dp.R (n + 1)) (Dp.R (n + 1) ⊗[R] B)
    (algebraMap (V.B' (n + 1)) (Dp.R (n + 1)) (algebraMap V.B0' (V.B' (n + 1)) r)))
  (htloc' : letI := t'.toAlgebra
    IsLocalization.Away (algebraMap V.B0' X0' V.c0) (Dp.R (n + 1) ⊗[R] B))
  (ρX1' : letI := algC1 I.B I.qB I.C1 (n + 1); X1' →ₐ[I.B (n + 1)] I.C1) (ρX0' : X0' →+* V.C0)
  (hρ' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he (n + 1) (t' x) =
      Dp.ι₀ (ρX0' x))
  {m' : ℕ} (hJm' : J θ (R := V.B' (n + 1)) ^ m' = ⊥)
  (hψ1' : ∀ y, (letI := V.algBM (n + 1)
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B (n + 1))) (V.M (n + 1)))
      (V.ψ hθ.out hO (n + 1) (e1' y))) = V.γM (n + 1) (ρX1' y))
  (hx1' : ρX1' (algebraMap I.B0 X1' V.x1) = algebraMap I.Bs I.C1 V.x1s)
  (hω' : ∀ x : X0', ∃ (y : X1') (k : ℕ),
    (haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0') V.x0
      letI := awayAlg (W := V.W0) (C := X1') V.x1
      ωn' (algebraMap X0' _ x) *
        algebraMap X1' (Localization.Away (algebraMap I.B0 X1' V.x1))
          (algebraMap I.B0 X1' V.x1) ^ k = algebraMap X1' _ y) ∧
    V.ω (algebraMap V.C0 _ (ρX0' x)) *
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
          (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1' y))
  (μ1 : X1' →+* X1) (μ0 : X0' →+* X0)
  (he1 : ∀ y, I.Ymap hθ.out hO n (e1' y) = e1 (μ1 y))
  (hμt : ∀ x, t (μ0 x) = levelMap Dp.R n (t' x))

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
include he1 hμt in
/-- **The levels over `V₀` form a tower** (`f0_levelEquiv0X`, with the patch sides compatible by
`sP_φPof`). -/
theorem f0_levelEquiv0P
    (hω2 : ∀ x : X0', ∃ (y : X1') (k : ℕ),
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0') V.x0
        letI := awayAlg (W := V.W0) (C := X1') V.x1
        ωn' (algebraMap X0' _ x) *
          algebraMap X1' (Localization.Away (algebraMap I.B0 X1' V.x1))
            (algebraMap I.B0 X1' V.x1) ^ k = algebraMap X1' _ y) ∧
      (haveI := V.hW0; haveI := V.hW0'
        letI := awayAlg (W := V.W0) (C := X0) V.x0
        letI := awayAlg (W := V.W0) (C := X1) V.x1
        ωn (algebraMap X0 _ (μ0 x)) *
          algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1))
            (algebraMap I.B0 X1 V.x1) ^ k = algebraMap X1 _ (μ1 y)))
    (x : X0') :
    V.f0 hθ.out hO n (V.levelEquiv0P hO Dp Vc hkI hT hP0 (n + 1) e1' ωn' t' ht' htloc' ρX1' ρX0'
      hρ' hJm' hψ1' hx1' hω' x) =
      V.levelEquiv0P hO Dp Vc hkI hT hP0 n e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω (μ0 x) :=
  letI := algC1 I.B I.qB I.C1 n
  letI := algC1 I.B I.qB I.C1 (n + 1)
  V.f0_levelEquiv0X hθ.out hO n e1 ωn e1' ωn' μ1 μ0 he1 _ ρX1.toRingHom ρX0
    (V.hPof hO Dp Vc hkI hT V.P0 hP0 t ht htloc) hJm hψ1 hx1 hω
    (V.hPℓof hO Dp Vc hkI hT V.P0 hP0 t ht ρX0 hρ) _ ρX1'.toRingHom ρX0'
    (V.hPof hO Dp Vc hkI hT V.P0 hP0 t' ht' htloc') hJm' hψ1' hx1' hω'
    (V.hPℓof hO Dp Vc hkI hT V.P0 hP0 t' ht' ρX0' hρ') hω2
    (V.sP_φPof hO Dp Vc hkI hT V.P0 hP0 t ht t' ht' μ0 hμt) x

end

end Overlap

end NodeEtaleGlue

end SemistableReduction
