/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.LevelTower

/-!
# The tower of patched algebras (Blueprint §12.8, M2.3 (e'), tower)

Setting: charts `R n` (`n : ℕ`, Noetherian `O`-algebras) with surjections `q_n : R (n+1) → R n`,
elements `f n` with `q_n (f (n+1)) = f n`, one admissible covering `cov₀` of a fixed special fibre
`R₀` and `k`-algebra isomorphisms `e n : R₀ ≃ R n/J` with `e n f₀ = f̄ n`, compatible with the
`q_n`. Every level carries the transported covering `cov₀.transport (e n)`.

* `LevelTower.Level n`: the patching data at level `n` (lift data `L`, `M` of the Kummer and cusp
  factors with deformation parameters `πL` shared by all levels, the nilpotence exponent, flatness
  of the node coordinates modulo an ideal `I` of `O`, a formally étale lift `P` of `C_f` with
  `σP : P/JP ≃ C_f`); `Level.G` the patched algebra and **`Level.spec`** (finite over `R n`,
  equal to `P` on `D(f n)`, to the lifted formal model along `V(f n)`; `patch_specF`);
* **`LevelTower.tr`**: given levels whose lift data are compatible under the completion maps
  `ψ₂` (`hχχ`, `hεε`, `hδδ`, `htt`), the transition maps `G (n+1) → G n`, surjective
  (`surjective_tr`) with kernel `(ker q_n) G (n+1)` (`ker_tr`), semilinear over `q_n`
  (`tr_algebraMap`);
* `LevelStep.eq_idem₂`: lifted idempotents at consecutive levels are compatible, so the
  idempotent part of `hεε`, `hδδ` holds for any choices (Stacks 00J9).
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift

noncomputable section

namespace LevelStep

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : Type u} [CommRing R] [Algebra O R] {R' : Type u} [CommRing R'] [Algebra O R']
  [Algebra R R'] (f : R) (f₂ : R') (hf : f' (R' := R') f = f₂)
  [Algebra k (R ⧸ J θ (R := R))] [Algebra k (R' ⧸ J θ (R := R'))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {e₁ : R₀ ≃ₐ[k] (R ⧸ J θ (R := R))} {e₂ : R₀ ≃ₐ[k] (R' ⧸ J θ (R := R'))}
  (h₁ : e₁ f₀ = fbar θ f) (h₂ : e₂ f₀ = fbar θ f₂)
  (he : ∀ r : R, e₂ (e₁.symm (Ideal.Quotient.mk _ r)) = Ideal.Quotient.mk _ (algebraMap R R' r))

include hf he in
/-- **Lifted idempotents of consecutive levels are compatible** (free target element). -/
theorem eq_idem₂ [IsNoetherianRing R'] {m : ℕ} (hJ : J θ (R := R') ^ m = ⊥)
    {ε : FormalPatchLevel.Hat f} (hεi : IsIdempotentElem ε) {ε₀ : Admissible.Hat f₀}
    (hε : ψ θ f ε = Admissible.hatEquiv e₁ h₁ ε₀) {ε' : FormalPatchLevel.Hat f₂}
    (hεi' : IsIdempotentElem ε') (hε' : ψ θ f₂ ε' = Admissible.hatEquiv e₂ h₂ ε₀) :
    ψ₂ f f₂ hf ε = ε' := by
  subst hf
  exact eq_idem_base f h₁ he hJ hεi hε hεi' hε'

end LevelStep

namespace LevelTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  (R : ℕ → Type u) [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  (cov₀ : Admissible.Covering φ₀ ψ₀) (πL : cov₀.ι → O)
  {f : ∀ n, R n} {e : ∀ n, R₀ ≃ₐ[k] (R n ⧸ J θ (R := R n))} (hfe : ∀ n, e n f₀ = fbar θ (f n))

/-- **The patching data at level `n`** of the transported covering `cov₀.transport (e n)`. -/
structure Level (n : ℕ) where
  /-- Lift data of the Kummer factors (deformation parameters `πL`). -/
  L : KummerLift (cov₀.transport (h := hfe n)) πL
  /-- Lift data of the cusp factors. -/
  M : CuspLift (cov₀.transport (h := hfe n))
  /-- A nilpotence exponent of `J`. -/
  m : ℕ
  hJ : J θ (R := R n) ^ m = ⊥
  /-- The node coordinates are flat modulo `I`. -/
  I : Ideal O
  hflat : ∀ j, KummerFactorQuot.KFlat I (L.χ j).toRingHom
  hidem : ∀ j, IsIdempotentElem (L.ε j)
  hfχ : ∀ j, L.χ j (fA (πL j)) = algebraMap (R n) (FormalPatchLevel.Hat (f n)) (f n)
  hcidem : ∀ i, IsIdempotentElem (M.δ i)
  hreg : ∀ y : FormalPatchLevel.Hat (f n), algebraMap (R n) _ (f n) * y = 0 → y = 0
  /-- The étale lift over `D(f n)`. -/
  P : Type u
  [commRing : CommRing P]
  [algebra : Algebra (R n) P]
  [etale : Algebra.FormallyEtale (R n) P]
  σP : (P ⧸ (J θ).map (algebraMap (R n) P)) ≃ₐ[R n]
    Localization.Away (algebraMap (R n) (cov₀.transport (h := hfe n)).C (f n))
  hfP : IsUnit (algebraMap (R n) P (f n))
  hP : ∃ s : Finset P, ∀ p : P, ∃ k : ℕ, f n ^ k • p ∈ Submodule.span (R n) (s : Set P)

attribute [instance] Level.commRing Level.algebra Level.etale

variable {R cov₀ πL hfe}
variable (hθ : Function.Surjective θ)

/-- The patched algebra at level `n`. -/
abbrev Level.G {n : ℕ} (D : Level R cov₀ πL hfe n) : Type u :=
  LevelStep.patchOf hθ cov₀ (f n) (hfe n) D.L D.M D.hJ D.σP

/-- **Level-`n` patching**: the patched algebra is finite over `R n`, equal to the étale lift `P`
on `D(f n)`, and to the lifted formal model `NF` along `V(f n)`. -/
theorem Level.spec (hO : ∀ x : O, θ x ≠ 0 → IsUnit x) {n : ℕ} (D : Level R cov₀ πL hfe n) :
    Module.Finite (R n) (D.G hθ) ∧
      (letI := FormalGlueing.algebraFst (NFall D.L D.M) (FormalPatchLevel.lift (f n) (J θ) D.hJ
        (FormalPatchLevel.alphaOfEquiv (f n) (J θ)
          (FormalPatchLevel.specialFibreEquiv (f n) (J θ) D.σP (kappaF D.L D.M hθ))));
        IsLocalization.Away (algebraMap (R n) (D.G hθ) (f n)) D.P) ∧
      IsBaseChange (FormalPatchLevel.Hat (f n))
        (FormalGlueing.snd (NFall D.L D.M) (FormalPatchLevel.lift (f n) (J θ) D.hJ
          (FormalPatchLevel.alphaOfEquiv (f n) (J θ)
            (FormalPatchLevel.specialFibreEquiv (f n) (J θ) D.σP
              (kappaF D.L D.M hθ))))).toLinearMap :=
  patch_specF D.L D.M hθ hO D.hJ D.hflat D.hidem D.hfχ D.hcidem D.hreg D.σP D.hfP D.hP

/-! ### The transition maps -/

variable [∀ n, Algebra (R (n + 1)) (R n)] [∀ n, IsScalarTower O (R (n + 1)) (R n)]
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)
  (hq : ∀ n, Function.Surjective (algebraMap (R (n + 1)) (R n)))
  (hf : ∀ n, LevelStep.f' (R' := R n) (f (n + 1)) = f n)
  (he : ∀ n (r : R (n + 1)), e n ((e (n + 1)).symm (Ideal.Quotient.mk _ r)) =
    Ideal.Quotient.mk _ (algebraMap (R (n + 1)) (R n) r))
  (D : ∀ n, Level R cov₀ πL hfe n)
  (hχχ : ∀ n j a, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.χ j a) = (D n).L.χ j a)
  (hεε : ∀ n j, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).L.ε j) = (D n).L.ε j)
  (hδδ : ∀ n i, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) ((D (n + 1)).M.δ i) = (D n).M.δ i)
  (htt : ∀ n, LevelStep.ψ₂ (f (n + 1)) (f n) (hf n) (D (n + 1)).M.t = (D n).M.t)

/-- `R (n+1) → R n → P n`. -/
abbrev algP (n : ℕ) : Algebra (R (n + 1)) (D n).P :=
  ((algebraMap (R n) (D n).P).comp (algebraMap (R (n + 1)) (R n))).toAlgebra

/-- **The transition map** `G (n+1) → G n` of the tower. -/
def tr (n : ℕ) : (D (n + 1)).G hθ →+* (D n).G hθ :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.trans₂ (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) (hq n) hθ hO cov₀
    (D (n + 1)).L (D (n + 1)).M (D n).L (D n).M (hχχ n) (hεε n) (hδδ n) (htt n)
    (D (n + 1)).hJ (D n).hJ (D (n + 1)).hflat (D (n + 1)).hidem (D (n + 1)).hfχ
    (D (n + 1)).hcidem (D (n + 1)).hreg (D n).hflat (D n).hidem (D n).hfχ (D n).hcidem
    (D n).hreg (D (n + 1)).σP (D n).σP (D (n + 1)).hfP (D n).hfP

/-- The transition maps are surjective. -/
theorem surjective_tr (n : ℕ) : Function.Surjective (tr hθ hO hq hf he D hχχ hεε hδδ htt n) :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.surjective_trans₂ (f (n + 1)) (f n) (hf n) (hfe (n + 1)) (hfe n) (he n) (hq n) hθ hO
    cov₀ (D (n + 1)).L (D (n + 1)).M (D n).L (D n).M (hχχ n) (hεε n) (hδδ n) (htt n)
    (D (n + 1)).hJ (D n).hJ (D (n + 1)).hflat (D (n + 1)).hidem (D (n + 1)).hfχ
    (D (n + 1)).hcidem (D (n + 1)).hreg (D n).hflat (D n).hidem (D n).hfχ (D n).hcidem
    (D n).hreg (D (n + 1)).σP (D n).σP (D (n + 1)).hfP (D n).hfP

/-- **The kernel of the transition map** `G (n+1) → G n` is `(ker q_n) G (n+1)`. -/
theorem ker_tr (n : ℕ) : RingHom.ker (tr hθ hO hq hf he D hχχ hεε hδδ htt n) =
    (RingHom.ker (algebraMap (R (n + 1)) (R n))).map (algebraMap (R (n + 1)) ((D (n + 1)).G hθ)) :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.ker_trans₂ ..

/-- The transition maps are semilinear over `q_n`. -/
theorem tr_algebraMap (n : ℕ) (r : R (n + 1)) :
    tr hθ hO hq hf he D hχχ hεε hδδ htt n (algebraMap (R (n + 1)) _ r) =
      algebraMap (R n) _ (algebraMap (R (n + 1)) (R n) r) :=
  letI := algP D n
  haveI : IsScalarTower (R (n + 1)) (R n) (D n).P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  LevelStep.trans₂_algebraMap ..

end LevelTower

end

end SemistableReduction
