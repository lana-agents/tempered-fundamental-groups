/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.EtaleOverlapFibre
import TemperedFundamentalGroups.SemistableReduction.LevelTowerSystem
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoMap

/-!
# Glueing a tower of node patches with étale pieces (Blueprint §12.8, M2.3 (f))

Setting (generic, at every level `n`): a tower of patched algebras `G n` on node charts `R n`
(`T : LevelTower.Data R cov₀ πL`), base charts `B n` (Tate case: the levels `T1n n` of the
`ℙ¹`-chart over `U₁`) with `R n = B n[1/a n]`, and étale pieces `E n` over `D(b n) ⊆ Spec B n`:
formally étale `B n`-algebras with `σE n : E n/J ≃ C1[1/b̄]` (`b̄ = qB n (b n)`) for
one special-fibre covering `C1` over `Bs` (the special fibre of the base chart). The special
fibres are compared by `ι₀ : C1 → cov₀.C`, a localization away from `ā` over `φs : Bs → R₀`
(the covering on the node chart is the covering on the base chart restricted to `D(ā)`).

At level `n`:

* `NodeEtaleGlue.ιn`, `σPn` (the étale part of the node patch with the ideal `J` of the base),
  `χn` (`OverlapFibre.χ`);
* **`NodeEtaleGlue.ρa n : G n → E n[1/a n]`** (`EtaleOverlap.ρa`), and **`isLocalization_ρa`**:
  it is a localization away from `b n`, given `f n ∣ (b n)ᵏ` in `R n`;
* the glued coverings `G n ×_{E n[1/a]} E n` and their tower: `NodeEtaleGlueTower`.
-/

universe u

open TensorProduct

namespace SemistableReduction

open KummerEtale AdmissibleLift LevelTower

noncomputable section

namespace NodeEtaleGlue

section Special

variable {k : Type u} [Field k] (Bs : Type u) [CommRing Bs] {R₀ : Type u} [CommRing R₀]
  [Algebra k R₀] {f₀ : R₀} {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀}
  {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}

/-- **A special-fibre covering of a base chart with its restriction to the node chart**: a finite
`Bs`-algebra `C1`, étale over `D(b̄)`, and `ι₀ : C1 → cov₀.C` over `φs : Bs → R₀`, exhibiting the
admissible covering `cov₀` of the node chart as `C1[1/ā]`. -/
structure Special (cov₀ : Admissible.Covering φ₀ ψ₀) (φs : Bs →+* R₀) (abar bbar : Bs) where
  C1 : Type u
  [commRing : CommRing C1]
  [algebra : Algebra Bs C1]
  finite : Module.Finite Bs C1
  etale : (Localization.awayMap (algebraMap Bs C1) bbar).Etale
  ι₀ : C1 →+* cov₀.C
  hι₀ : ∀ x, ι₀ (algebraMap Bs C1 x) = algebraMap R₀ cov₀.C (φs x)
  hι : letI := ι₀.toAlgebra; IsLocalization.Away (algebraMap Bs C1 abar) cov₀.C

attribute [instance] Special.commRing Special.algebra

end Special

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  {R : ℕ → Type u} [∀ n, CommRing (R n)] [∀ n, Algebra O (R n)]
  [∀ n, IsNoetherianRing (R n)] [∀ n, Algebra k (R n ⧸ J θ (R := R n))]
  {R₀ : Type u} [CommRing R₀] [Algebra k R₀] {f₀ : R₀}
  {φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat f₀} {ψ₀ : Polynomial k →ₐ[k] Admissible.Hat f₀}
  {cov₀ : Admissible.Covering φ₀ ψ₀} {πL : cov₀.ι → O}
  [∀ n, Algebra (R (n + 1)) (R n)]
  (T : Data (θ := θ) R cov₀ πL) (hθ : Function.Surjective θ)
  (B : ℕ → Type u) [∀ n, CommRing (B n)]
  [∀ n, Algebra (B n) (R n)]

/-! ### Algebra structures over the base charts -/

/-- The covering of the node chart at level `n` (`cov₀` transported). -/
abbrev Cc (n : ℕ) : Type u := (cov₀.transport (h := T.hfe n)).C

/-- `P n` over `B n`. -/
@[reducible] def algBP (n : ℕ) : Algebra (B n) (T.level n).P :=
  ((algebraMap (R n) (T.level n).P).comp (algebraMap (B n) (R n))).toAlgebra

/-- `Cc n` over `B n`. -/
@[reducible] def algBC (n : ℕ) : Algebra (B n) (Cc T n) :=
  ((algebraMap (R n) (Cc T n)).comp (algebraMap (B n) (R n))).toAlgebra

/-- `G n` over `B n`. -/
@[reducible] def algBG (n : ℕ) : Algebra (B n) (T.G hθ n) :=
  ((algebraMap (R n) (T.G hθ n)).comp (algebraMap (B n) (R n))).toAlgebra

lemma towerBP (n : ℕ) : letI := algBP T B n; IsScalarTower (B n) (R n) (T.level n).P :=
  letI := algBP T B n; IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

omit [∀ n, IsNoetherianRing (R n)] in
lemma towerBC (n : ℕ) : letI := algBC T B n; IsScalarTower (B n) (R n) (Cc T n) :=
  letI := algBC T B n; IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

lemma towerBG (n : ℕ) : letI := algBG T hθ B n; IsScalarTower (B n) (R n) (T.G hθ n) :=
  letI := algBG T hθ B n; IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The projection `G n → P n` (`G n` on `D(f n)`). -/
def fstP (n : ℕ) : T.G hθ n →ₐ[R n] (T.level n).P := FormalGlueing.fst _ _

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

include hO in
lemma isLocalization_fstP (n : ℕ) :
    letI := (fstP T hθ n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (R n) (T.G hθ n) (T.f n)) (T.level n).P :=
  (Level.spec hθ hO (T.level n)).2.1

/-! ### The étale part of the node patch with the ideal `J` of the base -/

variable [∀ n, Algebra O (B n)] [∀ n, IsScalarTower O (B n) (R n)]

lemma JB_eq (n : ℕ) : letI := algBP T B n
    EtaleNil.JB (J θ (R := B n)) (T.level n).P =
      (J θ (R := R n)).map (algebraMap (R n) (T.level n).P) := by
  letI := algBP T B n
  haveI := towerBP T B n
  rw [EtaleNil.JB, J, J, Ideal.map_map, Ideal.map_map]
  congr 1
  ext o
  change algebraMap (R n) _ (algebraMap (B n) (R n) (algebraMap O (B n) o)) =
    algebraMap (R n) _ (algebraMap O (R n) o)
  rw [← IsScalarTower.algebraMap_apply O (B n) (R n) o]

/-- **The étale part of the node patch over the base**: `P n/J ≃ Cc n[1/f n]` over `B n`. -/
def σPn (n : ℕ) : letI := algBP T B n; letI := algBC T B n
    ((T.level n).P ⧸ EtaleNil.JB (J θ (R := B n)) (T.level n).P) ≃ₐ[B n]
      Localization.Away (algebraMap (R n) (Cc T n) (T.f n)) :=
  letI := algBP T B n
  letI := algBC T B n
  haveI : IsScalarTower (B n) (R n)
      ((T.level n).P ⧸ (J θ (R := R n)).map (algebraMap (R n) (T.level n).P)) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (B n) (R n) (Localization.Away (algebraMap (R n) (Cc T n) (T.f n))) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [IsScalarTower.algebraMap_apply (B n) (Cc T n),
        IsScalarTower.algebraMap_apply (R n) (Cc T n)]
      rfl
  (Ideal.quotientEquivAlgOfEq (B n) (JB_eq T B n)).trans ((T.level n).σP.restrictScalars (B n))

/-! ### The special-fibre data -/

variable {Bs : Type u} [CommRing Bs] (qB : ∀ n, B n →+* Bs) (φs : Bs →+* R₀)
  (hφs : ∀ n (x : B n), T.e n (φs (qB n x)) = Ideal.Quotient.mk _ (algebraMap (B n) (R n) x))
  {C1 : Type u} [CommRing C1] [Algebra Bs C1] (ι₀ : C1 →+* cov₀.C)
  (hι₀ : ∀ x : Bs, ι₀ (algebraMap Bs C1 x) = algebraMap R₀ cov₀.C (φs x))

variable (C1) in
/-- `C1` over `B n` (through `qB n`). -/
@[reducible] def algC1 (n : ℕ) : Algebra (B n) C1 := ((algebraMap Bs C1).comp (qB n)).toAlgebra

omit [∀ n, IsNoetherianRing (R n)] [∀ n, IsScalarTower O (B n) (R n)] [∀ n, Algebra O (B n)] in
include hφs hι₀ in
lemma ι₀_algebraMap (n : ℕ) (x : B n) :
    ι₀ (algebraMap Bs C1 (qB n x)) = (letI := algBC T B n; algebraMap (B n) (Cc T n) x) := by
  rw [hι₀]
  change _ = algebraMap R₀ cov₀.C ((T.e n).symm (Ideal.Quotient.mk _ (algebraMap (B n) (R n) x)))
  rw [← hφs, AlgEquiv.symm_apply_apply]

/-- **The comparison of the special fibres at level `n`**: `ι₀` as a `B n`-algebra map. -/
def ιn (n : ℕ) : letI := algC1 B qB C1 n; letI := algBC T B n; C1 →ₐ[B n] Cc T n :=
  letI := algC1 B qB C1 n
  letI := algBC T B n
  { (ι₀ : C1 →+* Cc T n) with commutes' := ι₀_algebraMap T B qB φs hφs ι₀ hι₀ n }

/-! ### The overlap with the étale pieces -/

variable (a b : ∀ n, B n) [∀ n, IsLocalization.Away (a n) (R n)] {abar : Bs}
  (ha : ∀ n, qB n (a n) = abar)
  (hι : letI := ι₀.toAlgebra; IsLocalization.Away (algebraMap Bs C1 abar) cov₀.C)

omit [∀ n, IsNoetherianRing (R n)] [∀ n, IsScalarTower O (B n) (R n)] [∀ n, Algebra O (B n)]
  [∀ n, IsLocalization.Away (a n) (R n)] in
include ha hι in
lemma isLocalization_ιn (n : ℕ) :
    letI := algC1 B qB C1 n
    letI := (ιn T B qB φs hφs ι₀ hι₀ n : C1 →+* Cc T n).toAlgebra
    IsLocalization.Away (algebraMap (B n) C1 (a n)) (Cc T n) := by
  change letI := ι₀.toAlgebra; IsLocalization.Away (algebraMap Bs C1 (qB n (a n))) cov₀.C
  rw [ha n]
  exact hι

variable (E : ℕ → Type u) [∀ n, CommRing (E n)] [∀ n, Algebra (B n) (E n)]
  [∀ n, Algebra.FormallyEtale (B n) (E n)]
  {bbar : Bs} (σE : ∀ n, letI := algC1 B qB C1 n
    (E n ⧸ EtaleNil.JB (J θ (R := B n)) (E n)) ≃ₐ[B n] Localization.Away (algebraMap Bs C1 bbar))
  (hbE : ∀ n, IsUnit (algebraMap (B n) (E n) (b n)))
  {kdiv : ℕ → ℕ} (hdiv : ∀ n, T.f n ∣ algebraMap (B n) (R n) (b n) ^ kdiv n)

/-- **The special-fibre map** `χ̄ n : P n/J → (E n[1/a])/J` (`OverlapFibre.χ`). -/
def χn (n : ℕ) : letI := algBP T B n
    ((T.level n).P ⧸ EtaleNil.JB (J θ (R := B n)) (T.level n).P) →ₐ[B n]
      OverlapFibre.Z (J θ (R := B n)) (a n) (E n) :=
  letI := algBP T B n
  letI := algBC T B n
  haveI := towerBC T B n
  letI := algC1 B qB C1 n
  OverlapFibre.χ (J θ (R := B n)) (a n) (b n) (ιn T B qB φs hφs ι₀ hι₀ n) (T.f n) (σPn T B n)
    (σE n) (isLocalization_ιn T B qB φs hφs ι₀ hι₀ a ha hι n) (hbE n) (hdiv n)

variable (hbb : ∀ n, qB n (b n) = bbar)

variable (C1) in
include hbb in
lemma isLocalization_C1 (n : ℕ) : letI := algC1 B qB C1 n
    IsLocalization.Away (algebraMap (B n) C1 (b n))
      (Localization.Away (algebraMap Bs C1 bbar)) := by
  change IsLocalization.Away (algebraMap Bs C1 (qB n (b n))) _
  rw [hbb n]
  infer_instance

omit [∀ n, Algebra.FormallyEtale (B n) (E n)] [∀ n, IsLocalization.Away (a n) (R n)] in
include ha hι hbE hdiv hbb in
lemma isLocalization_χn (n : ℕ) :
    letI := algBP T B n
    letI := (χn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (B n) ((T.level n).P ⧸ EtaleNil.JB (J θ (R := B n))
      (T.level n).P) (b n)) (OverlapFibre.Z (J θ (R := B n)) (a n) (E n)) :=
  letI := algBP T B n
  letI := algBC T B n
  haveI := towerBC T B n
  letI := algC1 B qB C1 n
  haveI := isLocalization_C1 B qB C1 b hbb n
  OverlapFibre.isLocalization_χ (J θ (R := B n)) (a n) (b n) (ιn T B qB φs hφs ι₀ hι₀ n) (T.f n)
    (σPn T B n) (σE n) (isLocalization_ιn T B qB φs hφs ι₀ hι₀ a ha hι n) (hbE n) (hdiv n)

variable {mB : ℕ → ℕ} (hJB : ∀ n, J θ (R := B n) ^ mB n = ⊥)

/-- **The overlap map** `ρa n : G n → E n[1/a n]` (`EtaleOverlap.ρa`). -/
def ρa (n : ℕ) : letI := algBG T hθ B n
    T.G hθ n →ₐ[B n] EtaleOverlap.Bab (a n) (E n) :=
  letI := algBP T B n
  haveI := towerBP T B n
  letI := algBG T hθ B n
  haveI := towerBG T hθ B n
  EtaleOverlap.ρa (J θ (R := B n)) (hJB n) (a n) (A := R n)
    (χn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n) (fstP T hθ n)

include hO hJB hbb in
/-- **The overlap map is a localization away from `b n`.** -/
theorem isLocalization_ρa (n : ℕ) :
    letI := algBG T hθ B n
    letI := (ρa T hθ B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hJB n).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (B n) (T.G hθ n) (b n)) (EtaleOverlap.Bab (a n) (E n)) :=
  letI := algBP T B n
  haveI := towerBP T B n
  letI := algBG T hθ B n
  haveI := towerBG T hθ B n
  EtaleOverlap.isLocalization_ρa (J θ (R := B n)) (hJB n) (a n) (b n) (A := R n)
    (χn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv n) (hbE n)
    (isLocalization_χn T B qB φs hφs ι₀ hι₀ a b ha hι E σE hbE hdiv hbb n) (fstP T hθ n) (T.f n)
    (isLocalization_fstP T hθ hO n) (hdiv n)

end NodeEtaleGlue

end

end SemistableReduction
