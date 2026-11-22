/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevels
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevelsFam
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueSpecial
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0LevelEquivP
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0PatchSpecial

/-!
# At a level with `J = 0` the level identifications are the special-fibre ones (MR12, I3)

At a level where `J = 0` on the base charts (the bottom level of a tower `B/ϖⁿ⁺¹`), the level
identifications of G4 (from level data of the node and cusp patches) are the canonical
identifications of the special fibre:

* **`FormalPatchLevel.patch_ext_of_fst`**: an element of the patched algebra `G = P ×_{N_f} N` is
  determined by its first component when `f` is a non-zero-divisor on `N`;
* **`LevelTower.Level.eq_cEquiv`** (L1): at a level with `J = 0`, an element of the level patch
  whose first component reduces (under `σP`) to the class of `c` is `cEquiv c`;
* **`NodeEtaleGlue.Input.levelEquiv_eq_yEquiv`**: the identification `levelEquiv : X ≃ Y n` is
  `yEquiv ∘ ρX`;
* **`FormalLevel.NodeLevels.levelEquivX_eq_yEquiv`**, **`yEquiv_symm_levelEquivX`** (L2): the
  same for `levelEquivX` (node level data over `V₁`);
* **`FormalCuspLevel.CuspLevels.φPX_eq_toG`**: the patch side of cusp level data is `toG ∘ ρX`;
* **`NodeEtaleGlue.Overlap.φQn_eq_φQ`**, **`NodeEtaleGlue.Overlap.φPof_eq_bottom`**: the two
  components over `V₀`;
* **`NodeEtaleGlue.Overlap.levelEquiv0P_eq_r0Equiv`**, **`r0Equiv'_symm_levelEquiv0P`** (L3):
  `levelEquiv0P` is `r0Equiv ∘ ρX0` for the bottom identification `bot` of the cusp patch, given
  as any `bot : V.P0.Bottom n` with `HEq bot (Dp.bottom …)` (at concrete data with
  `hP0 = rfl`: `bot = Dp.bottom …`, `HEq.rfl`; in general `bottomOf hP0`, `bottomOf_heq`).
-/
universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace FormalPatchLevel

variable {R : Type u} [CommRing R] (f : R) (J : Ideal R) {n : ℕ} (hJ : J ^ n = ⊥)
  {P : Type u} [CommRing P] [Algebra R P] [Algebra.FormallyEtale R P]
  {N : Type u} [CommRing N] [Algebra R N]

/-- **The first projection of the patched algebra is injective** when `f` is a non-zero-divisor
on `N`. -/
theorem patch_ext_of_fst (α₀ : P →ₐ[R] Nf f N ⧸ JNf f J N)
    (hN : ∀ x : N, algebraMap R N f * x = 0 → x = 0) {x y : patch f J hJ α₀}
    (h : (x : P × N).1 = (y : P × N).1) : x = y := by
  have hx := (FormalGlueing.mem_glued N _).mp x.2
  have hy := (FormalGlueing.mem_glued N _).mp y.2
  have h2 : algebraMap N (Nf f N) (x : P × N).2 = algebraMap N (Nf f N) (y : P × N).2 := by
    rw [← hx, ← hy, h]
  obtain ⟨⟨_, k, rfl⟩, hc⟩ := (IsLocalization.eq_iff_exists
    (Submonoid.powers (algebraMap R N f)) (Nf f N)).mp h2
  have hpow : ∀ (k : ℕ) (z : N), algebraMap R N f ^ k * z = 0 → z = 0 := by
    intro k
    induction k with
    | zero => intro z hz; simpa using hz
    | succ k ih =>
      intro z hz
      refine ih z (hN _ ?_)
      rw [← mul_assoc, ← pow_succ']
      exact hz
  have h3 : (x : P × N).2 = (y : P × N).2 :=
    sub_eq_zero.mp (hpow k _ (by rw [mul_sub, sub_eq_zero]; exact hc))
  exact Subtype.ext (Prod.ext h h3)

end FormalPatchLevel

namespace LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} {hfe : ∀ n, e n f₀ = fbar θ (f n)}
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **L1: at a level with `J = 0`, an element of the level patch is `cEquiv c`** as soon as its
first component reduces (under `σP`) to the class of `c`. -/
theorem Level.eq_cEquiv {n : ℕ} (D : Level R cov₀ πL hfe n) (hJ0 : J θ (R := R n) = ⊥)
    (g : D.G hθ) (c : (cov₀.transport (h := hfe n)).C)
    (hg : D.σP (Ideal.Quotient.mk _ (g : D.P × NFall D.L D.M).1) =
      algebraMap _ (Localization.Away (algebraMap (R n) _ (f n))) c) :
    g = D.cEquiv hθ hO hJ0 c := by
  have h1 : Ideal.Quotient.mk ((J θ (R := R n)).map (algebraMap (R n) D.P))
      (g : D.P × NFall D.L D.M).1 =
      Ideal.Quotient.mk _ (FormalPatchLevel.toP hJ0 (f n) D.σP c) :=
    D.σP.injective (hg.trans (FormalPatchLevel.mk_toP hJ0 (f n) D.σP c).symm)
  exact FormalPatchLevel.patch_ext_of_fst (f n) (J θ) D.hJ _
    (noTorsion_NFall D.L D.M D.hflat D.hidem D.hfχ D.hcidem D.hreg)
    ((congrArg (FormalPatchLevel.quotEquivOfEqBot hJ0 (R n) D.P) h1).trans
      (D.cEquiv_fst hθ hO hJ0 c).symm)

end LevelTower

namespace NodeEtaleGlue.Input

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O} (I : Input θ cov₀ πL)
  (hθ : Function.Surjective θ) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) (n : ℕ)
  {X : Type u} [CommRing X] [Algebra (I.B n) X]
  (φG : letI := algBG I.T hθ I.B n; X →ₐ[I.B n] I.T.G hθ n) (φE : X →ₐ[I.B n] I.E n)
  (ρX : letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n; X →ₐ[I.B n] I.C1)
  (hG : ∀ x, (letI := algBP I.T I.B n; σPn I.T I.B n (Ideal.Quotient.mk _ (fstP I.T hθ n (φG x)))) =
    algebraMap (Cc I.T n) _ (ιn I.T I.B I.qB I.φs I.hφs I.ι₀ I.hι₀ n (ρX x)))
  (hE : ∀ x, I.σE n (Ideal.Quotient.mk _ (φE x)) =
    algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX x))
  (hlocE : letI := φE.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) X (I.b n)) (I.E n))
  [Algebra I.B0 X] [IsScalarTower I.B0 (I.B n) X]
  (hlocG : letI := algBG I.T hθ I.B n; letI := φG.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B n) X (I.a n)) (I.T.G hθ n))
  (hJ0 : J θ (R := I.B n) = ⊥)

/-- **L2 (generic form): at a level with `J = 0` the identification `levelEquiv` of G4 is the
special-fibre identification**: `levelEquiv x = yEquiv (ρX x)`. -/
theorem levelEquiv_eq_yEquiv (x : X) :
    I.levelEquiv hθ hO n φG φE ρX hG hE hlocE hlocG x = I.yEquiv hθ hO hJ0 (ρX x) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact (I.T.level n).eq_cEquiv hθ hO _ (φG x) (I.ι₀ (ρX x)) (hG x)
  · change φE x = I.φE hJ0 (ρX x)
    letI := NodeEtaleGlue.algC1 I.B I.qB I.C1 n
    have h1 : Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (I.E n)) (φE x) =
        Ideal.Quotient.mk (EtaleNil.JB (J θ (R := I.B n)) (I.E n)) (I.φE hJ0 (ρX x)) := by
      rw [mk_φE]
      exact (I.σE n).injective ((hE x).trans (AlgEquiv.apply_symm_apply _ _).symm)
    exact congrArg (FormalPatchLevel.quotEquivOfEqBot hJ0 (I.B n) (I.E n)) h1

end NodeEtaleGlue.Input

namespace FormalLevel

open KummerEtale FormalKummer AdmissibleLift NodeEtaleGlue

attribute [local instance] KummerNormAtData.algO

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing R]
  {ϖ : O} {n M' : ℕ} {x y : R}
  {hxy : x * y = algebraMap O R (ϖ ^ n)} {hϖ : θ ϖ = 0} {hn0 : 0 < n}
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  {hJ : ∀ j, J θ (R := R) ≤ 𝔪 j}
  {hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R))}
  {D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)} {g : R}
  {hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j)}
  {hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j)}
  {hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical}
  {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g)}
  {hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x)}
  {hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g)}
  {hfin : Module.Finite (Rs θ R) (Cs θ R B)}
  {het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale}
  {hk : ∀ j i, ((D j).d i : k) ≠ 0}
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]

variable
  (I : Input θ (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk) (πK 𝔪 D))
  [algRI : ∀ l, Algebra R (I.R l)] [towerORI : ∀ l, IsScalarTower O R (I.R l)]
  [towerRII : ∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    LevelTower.Data (θ := θ) I.R (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
      het hk) (πK 𝔪 D)}
  (V : NodeLevels hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T')
  (he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (I.R l) r))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)) = I.algkR) (hT : HEq T' I.T)

namespace NodeLevels

variable {l : ℕ} {X : Type u} [CommRing X] [Algebra (I.B l) X]
  (t : X →+* I.R l ⊗[R] B)
  (ht : ∀ r, t (algebraMap (I.B l) X r) =
    algebraMap (I.R l) (I.R l ⊗[R] B) (algebraMap (I.B l) (I.R l) r))

variable (ρX : letI := algC1 I.B I.qB I.C1 l; X →ₐ[I.B l] I.C1)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ x, ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T'.hfe he l
      (t x) = I.ι₀ (ρX x))

variable [Algebra I.B0 X] [towerX : IsScalarTower I.B0 (I.B l) X]
  (htloc : letI := t.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.a l)) (I.R l ⊗[R] B))
  (φE : X →ₐ[I.B l] I.E l)
  (hE : ∀ x, I.σE l (Ideal.Quotient.mk _ (φE x)) =
    algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX x))
  (hlocE : letI := φE.toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) X (I.b l)) (I.E l))

omit [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)] in
/-- **L2: at a level with `J = 0` the identification `levelEquivX` is the special-fibre
identification** `yEquiv ∘ ρX`. -/
theorem levelEquivX_eq_yEquiv (hJ0 : J θ (R := I.B l) = ⊥) (x : X) :
    V.levelEquivX I he hO hkI hT t ht ρX hρ htloc φE hE hlocE x =
      I.yEquiv hθ.out hO hJ0 (ρX x) :=
  I.levelEquiv_eq_yEquiv hθ.out hO l _ φE ρX _ hE hlocE _ hJ0 x

omit [∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)] in
/-- **L2, inverse form**: `yEquiv⁻¹ (levelEquivX x) = ρX x` at a level with `J = 0`. -/
theorem yEquiv_symm_levelEquivX (hJ0 : J θ (R := I.B l) = ⊥) (x : X) :
    (letI := I.algC10 l;
      (I.yEquiv hθ.out hO hJ0).symm
        (V.levelEquivX I he hO hkI hT t ht ρX hρ htloc φE hE hlocE x)) = ρX x :=
  letI := I.algC10 l
  (AlgEquiv.symm_apply_eq _).mpr (V.levelEquivX_eq_yEquiv I he hO hkI hT t ht ρX hρ htloc φE hE
    hlocE hJ0 x)

end NodeLevels

end FormalLevel

namespace FormalCuspLevel

open FormalKummer AdmissibleLift FormalLevel NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing R]
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
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}


variable
  (Dp : PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk)
    πL)
  [algRI : ∀ l, Algebra R (Dp.R l)] [towerORI : ∀ l, IsScalarTower O R (Dp.R l)]
  [towerRII : ∀ l, IsScalarTower R (Dp.R (l + 1)) (Dp.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    LevelTower.Data (θ := θ) Dp.R (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL}
  {he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Dp.R l) r)}
  (V : CuspLevels 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T' he)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)) = Dp.algkR) (hT : HEq T' Dp.T)


namespace CuspLevels

variable {l : ℕ} {X : Type u} [CommRing X] [Algebra B0' X]
  (t : X →+* Dp.R l ⊗[R] B)
  (ht : ∀ r, t (algebraMap B0' X r) = algebraMap (Dp.R l) (Dp.R l ⊗[R] B)
    (algebraMap (B' l) (Dp.R l) (algebraMap B0' (B' l) r)))
variable (ρX : X →+* C0)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he l (t x) = Dp.ι₀ (ρX x))


omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
set_option maxRecDepth 20000 in
include hρ in
/-- **At a level with `J = 0` the patch side of `X` is `toG ∘ ρX`** (`LevelTower.Level.eq_cEquiv`
with the `σP`-reduction of the level patch). -/
theorem φPX_eq_toG (hJ0 : J θ (R := Dp.R l) = ⊥) (x : X) :
    V.φPX Dp hO hkI hT t ht x = Dp.toG hθ.out hO hJ0 (ρX x) := by
  have h := V.σP_φ₁ l (t x)
  rw [hρ] at h
  exact (Dp.T.level l).eq_cEquiv hθ.out hO hJ0 _ (Dp.ι₀ (ρX x))
    (LevelTower.Data.GEquivOfInst_σP _ Dp.algkR hkI T' Dp.T hT hθ.out l
      (V.equiv hO l (t x)) (Dp.ι₀ (ρX x)) h)

end CuspLevels

end FormalCuspLevel

namespace NodeEtaleGlue.Overlap

section Q

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  {I : Input θ cov₀ πL} (V : Overlap I) (hθ : Function.Surjective θ)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ} (hJ0 : J θ (R := I.B n) = ⊥)
  {X1 : Type u} [CommRing X1] [Algebra I.B0 X1] (e1 : X1 ≃ₐ[I.B0] I.Y hθ n)
  {X0 : Type u} [CommRing X0] [Algebra V.B0' X0]
  (ωn : haveI := V.hW0; haveI := V.hW0'
    letI := awayAlg (W := V.W0) (C := X0) V.x0
    letI := awayAlg (W := V.W0) (C := X1) V.x1
    Localization.Away (algebraMap V.B0' X0 V.x0) ≃ₐ[V.W0]
      Localization.Away (algebraMap I.B0 X1 V.x1))
  (ρX1 : X1 →+* I.C1) (ρX0 : X0 →+* V.C0)

/-- `yEquiv (x̄₁) = x₁` in `Q n`. -/
lemma algebraMap_yEquiv_x1s :
    algebraMap (I.Y hθ n) (V.Q hθ n) (I.yEquiv hθ hO hJ0 (algebraMap I.Bs I.C1 V.x1s)) =
      algebraMap I.B0 (V.Q hθ n) V.x1 := by
  letI := I.algC10 n
  rw [← V.hx1 n]
  have h : I.yEquiv hθ hO hJ0 (algebraMap I.Bs I.C1 (I.qB n (algebraMap I.B0 (I.B n) V.x1))) =
      algebraMap I.B0 (I.Y hθ n) V.x1 := (I.yEquiv hθ hO hJ0).commutes V.x1
  rw [h, ← IsScalarTower.algebraMap_apply]

/-- **The `Q`-components at a level with `J = 0`**: if `e1 = yEquiv ∘ ρX1`, then on an element
`x` with a common witness `(y, k)` of `ωn` and `ω`, `φQn x = φQ (ρX0 x)`. -/
theorem φQn_eq_φQ (he1 : ∀ y, e1 y = I.yEquiv hθ hO hJ0 (ρX1 y)) (x : X0) (y : X1) (k : ℕ)
    (h1 : haveI := V.hW0; haveI := V.hW0'
      letI := awayAlg (W := V.W0) (C := X0) V.x0
      letI := awayAlg (W := V.W0) (C := X1) V.x1
      ωn (algebraMap X0 _ x) *
        algebraMap X1 (Localization.Away (algebraMap I.B0 X1 V.x1)) (algebraMap I.B0 X1 V.x1) ^ k =
        algebraMap X1 _ y)
    (h2 : V.ω (algebraMap V.C0 _ (ρX0 x)) *
        algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 V.x1s))
          (algebraMap I.Bs I.C1 V.x1s) ^ k = algebraMap I.C1 _ (ρX1 y)) :
    V.φQn hθ n e1 ωn x = V.φQ hθ hO hJ0 (ρX0 x) := by
  have a := V.φQn_mul_pow hθ n e1 ωn x y k h1
  rw [he1] at a
  have b : V.φQ hθ hO hJ0 (ρX0 x) * algebraMap I.B0 (V.Q hθ n) V.x1 ^ k =
      algebraMap (I.Y hθ n) (V.Q hθ n) (I.yEquiv hθ hO hJ0 (ρX1 y)) := by
    have b0 := congrArg (V.eQ hθ hO hJ0) h2
    rw [map_mul, map_pow, eQ_algebraMap, eQ_algebraMap, algebraMap_yEquiv_x1s] at b0
    exact b0
  exact ((V.isUnit_x1_Q hθ n).pow k).mul_left_injective (a.trans b.symm)

end Q

section Patch

open FormalKummer AdmissibleLift FormalLevel FormalCuspLevel

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)]
  {R₁ : Type u} [CommRing R₁] [Algebra k R₁] {f₁ : R₁}
  {φ₁ : Node k (0 : k) →ₐ[k] Admissible.Hat f₁} {ψ₁ : Polynomial k →ₐ[k] Admissible.Hat f₁}
  {cov₁ : Admissible.Covering φ₁ ψ₁} {πL₁ : cov₁.ι → O}
  {I : Input θ cov₁ πL₁} (V : Overlap I) (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing R]
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


/-- **The bottom identification of the cusp patch as one of `V.P0`** (transported along
`hP0 : V.P0 = Dp.piece`; at concrete data with `hP0 = rfl` use `Dp.bottom` directly). -/
def bottomOf (hP0 : V.P0 = Dp.piece hθ.out hO) {n : ℕ} (hJ0' : J θ (R := Dp.R n) = ⊥) :
    V.P0.Bottom n :=
  cast (congrArg (fun P ↦ Piece0.Bottom P n) hP0.symm) (Dp.bottom hθ.out hO hJ0')

omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] algRI towerORI towerRII in
lemma bottomOf_heq (hP0 : V.P0 = Dp.piece hθ.out hO) {n : ℕ} (hJ0' : J θ (R := Dp.R n) = ⊥) :
    HEq (V.bottomOf hO Dp hP0 hJ0') (Dp.bottom hθ.out hO hJ0') :=
  cast_heq _ _

omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
/-- **At a level with `J = 0` the patch side `φPof` is the bottom identification** `bot.toP ∘ ρX`,
for any bottom identification `bot` of `P` equal (heterogeneously, along `hP`) to `Dp.bottom`. -/
theorem φPof_eq_bottom (P : Piece0 θ V.B' V.qB' V.C0 V.x0 V.c0 V.x0s V.c0s V.ϖ)
    (hP : P = Dp.piece hθ.out hO) {l : ℕ} {X : Type u} [CommRing X] [Algebra V.B0' X]
    (t : X →+* Dp.R l ⊗[R] B)
    (ht : ∀ r, t (algebraMap V.B0' X r) = algebraMap (Dp.R l) (Dp.R l ⊗[R] B)
      (algebraMap (V.B' l) (Dp.R l) (algebraMap V.B0' (V.B' l) r)))
    (ρX : X →+* V.C0)
    (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
      ∀ x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he l (t x) = Dp.ι₀ (ρX x))
    (hJ0' : J θ (R := Dp.R l) = ⊥) (bot : P.Bottom l) (hbot : HEq bot (Dp.bottom hθ.out hO hJ0'))
    (x : X) :
    V.φPof hO Dp Vc hkI hT P hP t ht x = bot.toP (ρX x) := by
  subst hP
  obtain rfl := eq_of_heq hbot
  exact Vc.φPX_eq_toG Dp hO hkI hT t ht ρX hρ hJ0' x

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


omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
/-- **L3: at a level with `J = 0` the identification `levelEquiv0P` over `V₀` is the
special-fibre identification** `r0Equiv ∘ ρX0`, if the identification `e1` over `V₁` is canonical
(`e1 = yEquiv ∘ ρX1`, L2) and `bot` is the bottom identification of the cusp patch. -/
theorem levelEquiv0P_eq_r0Equiv (hJ0 : J θ (R := I.B n) = ⊥) (hJ0' : J θ (R := Dp.R n) = ⊥)
    (bot : V.P0.Bottom n) (hbot : HEq bot (Dp.bottom hθ.out hO hJ0'))
    (he1 : letI := algC1 I.B I.qB I.C1 n; ∀ y, e1 y = I.yEquiv hθ.out hO hJ0 (ρX1 y))
    (x : X0) :
    V.levelEquiv0P hO Dp Vc hkI hT hP0 n e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω x =
      V.r0Equiv hθ.out hO hJ0 bot (ρX0 x) := by
  letI := algC1 I.B I.qB I.C1 n
  obtain ⟨y, k, h1, h2⟩ := hω x
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact V.φQn_eq_φQ hθ.out hO hJ0 e1 ωn ρX1.toRingHom ρX0 he1 x y k h1 h2
  · exact V.φPof_eq_bottom hO Dp Vc hkI hT V.P0 hP0 t ht ρX0 hρ hJ0' bot hbot x

omit [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
/-- **L3, the form of `r0Equiv'_symm_map`**: `r0Equiv'⁻¹ (levelEquiv0P x) = ρX0 x`. -/
theorem r0Equiv'_symm_levelEquiv0P (hJ0 : J θ (R := I.B n) = ⊥)
    (hJ0' : J θ (R := Dp.R n) = ⊥) (bot : V.P0.Bottom n)
    (hbot : HEq bot (Dp.bottom hθ.out hO hJ0'))
    (he1 : letI := algC1 I.B I.qB I.C1 n; ∀ y, e1 y = I.yEquiv hθ.out hO hJ0 (ρX1 y))
    (x : X0) :
    (V.r0Equiv' hθ.out hO hJ0 bot).symm
        (V.levelEquiv0P hO Dp Vc hkI hT hP0 n e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω x) =
      ρX0 x :=
  (RingEquiv.symm_apply_eq _).mpr
    (V.levelEquiv0P_eq_r0Equiv hO Dp Vc hkI hT hP0 n e1 ωn t ht htloc ρX1 ρX0 hρ hJm hψ1 hx1 hω
      hJ0 hJ0' bot hbot he1 x)

end Patch

end NodeEtaleGlue.Overlap

namespace FormalLevel

open KummerEtale FormalKummer NodeEtaleGlue

attribute [local instance] KummerNormAtData.algO

section Fam

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsNoetherianRing R]
  {ϖ : O} {n M' : ℕ} {x y : R}
  {hxy : x * y = algebraMap O R (ϖ ^ n)} {hϖ : θ ϖ = 0} {hn0 : 0 < n}
  {ι : Type} [Fintype ι] [DecidableEq ι] {𝔪 : ι → Ideal R} [∀ j, (𝔪 j).IsMaximal]
  {hJ : ∀ j, J θ (R := R) ≤ 𝔪 j}
  {hres : ∀ j, Function.Surjective ((Ideal.Quotient.mk (𝔪 j)).comp (algebraMap O R))}
  {D : ∀ j, KummerNormAtData ϖ n M' x y B (𝔪 j)} {g : R}
  {hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j)}
  {hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j)}
  {hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical}
  {φ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g)}
  {hφu : φ (Node.u _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ x)}
  {hφv : φ (Node.v _) = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ y)}
  {ψc : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g)}
  {hfin : Module.Finite (Rs θ R) (Cs θ R B)}
  {het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale}
  {hk : ∀ j i, ((D j).d i : k) ≠ 0}
  [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]
variable
  (I : Input θ (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk) (πK 𝔪 D))
  [algRI : ∀ l, Algebra R (I.R l)] [towerORI : ∀ l, IsScalarTower O R (I.R l)]
  [towerRII : ∀ l, IsScalarTower R (I.R (l + 1)) (I.R l)]
  {T' : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    LevelTower.Data (θ := θ) I.R (cov₀ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin
      het hk) (πK 𝔪 D)}
  (V : NodeLevels hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T')
  (he : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ l (r : R), T'.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (I.R l) r))
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hkI : (fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)) = I.algkR) (hT : HEq T' I.T)


namespace NodeLevels

variable {X : ℕ → Type u} [∀ l, CommRing (X l)] [∀ l, Algebra (I.B l) (X l)]
  [∀ l, Algebra I.B0 (X l)] [towerX : ∀ l, IsScalarTower I.B0 (I.B l) (X l)]
  (t : ∀ l, X l →+* I.R l ⊗[R] B)
  (ht : ∀ l r, t l (algebraMap (I.B l) (X l) r) =
    algebraMap (I.R l) (I.R l ⊗[R] B) (algebraMap (I.B l) (I.R l) r))
  (ρX : ∀ l, letI := algC1 I.B I.qB I.C1 l; X l →ₐ[I.B l] I.C1)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (I.R l)
    ∀ l x, ρ hxy hϖ hn0 𝔪 hJ hres D hinjk hfk hradk φ hφu hφv ψc hfin het hk I.R T'.hfe he l
      (t l x) = I.ι₀ (ρX l x))
  (htloc : ∀ l, letI := (t l).toAlgebra
    IsLocalization.Away (algebraMap (I.B l) (X l) (I.a l)) (I.R l ⊗[R] B))
  (φE : ∀ l, X l →ₐ[I.B l] I.E l)
  (hE : ∀ l x, I.σE l (Ideal.Quotient.mk _ (φE l x)) =
    algebraMap I.C1 (Localization.Away (algebraMap I.Bs I.C1 I.bbar)) (ρX l x))
  (hlocE : ∀ l, letI := (φE l).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (I.B l) (X l) (I.b l)) (I.E l))
  (μ : ∀ l, X (l + 1) →+* X l) (hμt : ∀ l x, t l (μ l x) = levelMap I.R l (t (l + 1) x))
  (hμE : ∀ l x, I.sE l (φE (l + 1) x) = φE l (μ l x))

/-- **L2 for families**: at the bottom level (`J = 0`) the identification of `levelEquivXFam` is
`yEquiv ∘ ρX 0`. -/
theorem levelEquivXFam_equiv_zero (hJ0 : J θ (R := I.B 0) = ⊥) (x : X 0) :
    (V.levelEquivXFam I he hO hkI hT t ht ρX hρ htloc φE hE hlocE μ hμt hμE).equiv 0 x =
      I.yEquiv hθ.out hO hJ0 (ρX 0 x) :=
  V.levelEquivX_eq_yEquiv I he hO hkI hT (t 0) (ht 0) (ρX 0) (hρ 0) (htloc 0) (φE 0) (hE 0)
    (hlocE 0) hJ0 x

end NodeLevels

end Fam

end FormalLevel

end

end SemistableReduction
