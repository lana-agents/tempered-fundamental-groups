/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspLevelPatch
import TemperedFundamentalGroups.SemistableReduction.FormalLevelPatchTr

/-!
# The level data of the M2 lift over a chart without nodes (MR12 T2 S6, step G2c/G3, cusps)

**`FormalCuspLevel.CuspLevels`**: the per-level hypotheses of `FormalCuspLevel.levelPatchEquiv`
along a tower `T : LevelTower.Data Rt (covCuspOf …) πL` (level points `𝔪' l j` reducing into the
special-fibre points, level forms `Ψ l j` of the local formal cusp forms, the cusp coordinate
`htL`, the lifted idempotents `hδL`, and the étaleness of `(Rt l ⊗_R B)[1/f l]`), bundled for all
levels `l` (as `FormalLevel.NodeLevels` on the node side). Results:

* **`CuspLevels.equiv`**: the level-`l` patched algebra is `Rt l ⊗_R B`;
* **`CuspLevels.equiv_tr`**: these identifications commute with the transition maps `tr` of the
  tower and the maps `Rt (l+1) ⊗_R B → Rt l ⊗_R B` (`FormalLevel.levelMap`), via
  `LevelTower.Data.tr_eq_of_etale`.
-/

universe u

open TensorProduct Polynomial

namespace SemistableReduction

namespace FormalCuspLevel

noncomputable section

open FormalKummer AdmissibleLift FormalLevel

/-- Transport of a level form along an equality of local formal cusp forms. -/
def LevelPointForm.cast {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
    {R : Type u} [CommRing R] [Algebra O R] {B : Type u} [CommRing B] [Algebra R B]
    {𝔪 : Ideal R} {T' : Type u} [CommRing T'] [Algebra R T'] {red : T' →ₐ[R] Tn θ 𝔪} {s : R}
    {E : ℕ} {D D' : PointCuspFormData (θ := θ) (B := B) s E 𝔪} (h : D = D')
    (L : LevelPointForm red D) : LevelPointForm red D' :=
  h ▸ L

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
  {B : Type u} [CommRing B] [Algebra R B] [IsSepClosed k] [IsNoetherianRing R]
  {ι : Type} [Fintype ι] [DecidableEq ι] (𝔪 : ι → Ideal R) [∀ j, (𝔪 j).IsMaximal]
  (hJ : ∀ j, J θ (R := R) ≤ 𝔪 j) {s : R} {E : ι → ℕ}
  (D : ∀ j, PointCuspFormData (θ := θ) (B := B) s (E j) (𝔪 j)) {g : R}
  (hinjk : Function.Injective fun j ↦ sIdeal (θ := θ) (𝔪 j))
  (hfk : ∀ j, fbar θ g ∈ sIdeal (θ := θ) (𝔪 j))
  (hradk : ⨅ j, sIdeal (θ := θ) (𝔪 j) ≤ (Ideal.span {fbar θ g}).radical)
  (φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ g))
  (ψk : Polynomial k →ₐ[k] Admissible.Hat (fbar θ g))
  (hψ : ψk X = algebraMap (Rs θ R) _ (Ideal.Quotient.mk _ s))
  (hfin : Module.Finite (Rs θ R) (Cs θ R B))
  (het : (Localization.awayMap (algebraMap (Rs θ R) (Cs θ R B)) (fbar θ g)).Etale)
  (hk : ∀ j i, ((D j).d i : k) ≠ 0)
  (Rt : ℕ → Type u) [∀ l, CommRing (Rt l)] [∀ l, Algebra O (Rt l)]
  [∀ l, IsNoetherianRing (Rt l)] [∀ l, Algebra R (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  [∀ l, Algebra (Rt (l + 1)) (Rt l)] [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)]
  [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)]
  {πL : (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).ι → O}
  (T : LevelTower.Data (θ := θ) Rt (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL)
  (he : ∀ l (r : R), T.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Rt l) r))

omit [IsSepClosed k] [∀ l, IsNoetherianRing (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
  [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)] in
/-- The reductions `ρ` of consecutive levels are compatible with `levelMap`. -/
lemma ρ_levelMap (l : ℕ) (z : Rt (l + 1) ⊗[R] B) :
    ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he l (levelMap Rt l z) =
      LevelStep.idC (T.f (l + 1)) (T.f l) (T.hfe (l + 1)) (T.hfe l)
        (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk)
        (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he (l + 1) z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; rfl
  | add z w hz hw => rw [map_add, map_add, hz, hw, map_add]; rfl
  | tmul c b =>
    rw [levelMap, Algebra.TensorProduct.map_tmul, ρ_tmul, ρ_tmul]
    simp only [LevelStep.idC]
    congr 1
    change algebraMap (Rs θ R) (Cs θ R B) ((T.e l).symm (Ideal.Quotient.mk _
        (algebraMap (Rt (l + 1)) (Rt l) c))) =
      algebraMap (Rs θ R) (Cs θ R B) ((T.e (l + 1)).symm (Ideal.Quotient.mk _ c))
    rw [← T.he l c, AlgEquiv.symm_apply_apply]

section TrCompat

variable {O' : Type u} [CommRing O'] {k' : Type u} [Field k'] {θ' : O' →+* k'}
  [Fact (Function.Surjective θ')] {R' : Type u} [CommRing R'] {B' : Type u} [CommRing B']
  [Algebra R' B'] {Rt' : ℕ → Type u} [∀ l, CommRing (Rt' l)] [∀ l, Algebra O' (Rt' l)]
  [∀ l, IsNoetherianRing (Rt' l)] [∀ l, Algebra R' (Rt' l)] [∀ l, Algebra (Rt' (l + 1)) (Rt' l)]
  [∀ l, IsScalarTower O' (Rt' (l + 1)) (Rt' l)] [∀ l, IsScalarTower R' (Rt' (l + 1)) (Rt' l)]
  {R₀ : Type u} [CommRing R₀] [Algebra k' R₀] {f₀ : R₀}
  {φ₀' : Node k' (0 : k') →ₐ[k'] Admissible.Hat f₀}
  {ψ₀ : Polynomial k' →ₐ[k'] Admissible.Hat f₀} {cov : Admissible.Covering φ₀' ψ₀}
  {π' : cov.ι → O'}

/-- **Compatibility of identifications of the level patches with the transition maps**: a family
`Φ l : Rt l ⊗_R B ≃ G l` of identifications of the level patches of a tower `T` commutes with the
transition maps `tr` of `T` and the maps `Rt (l+1) ⊗_R B → Rt l ⊗_R B` (`FormalLevel.levelMap`).
-/
def TrCompat (T : LevelTower.Data (θ := θ') Rt' cov π') (hO : ∀ x : O', θ' x ≠ 0 → IsUnit x)
    (Φ : ∀ l, Rt' l ⊗[R'] B' ≃ₐ[Rt' l] T.G (Fact.out (p := Function.Surjective θ')) l) :
    Prop :=
  ∀ l (z : Rt' (l + 1) ⊗[R'] B'),
    T.tr (Fact.out (p := Function.Surjective θ')) hO l (Φ (l + 1) z) = Φ l (levelMap Rt' l z)

end TrCompat

variable [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal]

/-- **The level data of the M2 lift of `covCuspOf …` along a tower `T`** (the per-level
hypotheses of `FormalCuspLevel.levelPatchEquiv`): level points `𝔪' l` reducing into the
special-fibre points (`hm`), level forms `Ψ l j` of the local formal cusp forms `D j`, the cusp
coordinate of the levels of `T` (`htL`), the lifted idempotents (`hδL`), and the étaleness of
`(Rt l ⊗_R B)[1/f l]`. -/
structure CuspLevels where
  𝔪' : ∀ l, ι → Ideal (Rt l)
  isMaximal : ∀ l j, (𝔪' l j).IsMaximal
  hinj : ∀ l, Function.Injective (𝔪' l)
  hf : ∀ l j, T.f l ∈ 𝔪' l j
  hrad : ∀ l, ⨅ j, 𝔪' l j ≤ (Ideal.span {T.f l}).radical
  hm : ∀ l j, (𝔪' l j).map (red θ (T.e l)) ≤ sIdeal (θ := θ) (𝔪 j)
  Ψ : ∀ l j, (haveI := isMaximal l;
    LevelPointForm (redHat 𝔪 (T.e l) (he l) (hm l) j) (D j))
  htL : ∀ l, (T.level l).M.t = algebraMap R (FormalPatchLevel.Hat (T.f l)) s
  hδL : ∀ l p, (T.level l).M.δ p =
    (haveI := isMaximal l; CompletionProd.idem (hinj l) (hf l) (hrad l) p.1)
  etale : ∀ l, Algebra.FormallyEtale (Rt l)
    (Localization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (T.f l)))

namespace CuspLevels

variable {𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T he}
variable (V : CuspLevels 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T he)
  (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- The étale component `φ₁ : Rt l ⊗_R B → P l` of the level patch (`exists_φ₁`). -/
def φ₁ (l : ℕ) : Rt l ⊗[R] B →ₐ[Rt l] (T.level l).P :=
  haveI := V.etale l
  (exists_φ₁ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he πL (T.level l)).choose

omit [IsSepClosed k] [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)]
  [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma isLocalization_φ₁ (l : ℕ) : letI := (V.φ₁ l).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (Rt l) (Rt l ⊗[R] B) (T.f l)) (T.level l).P :=
  haveI := V.etale l
  (exists_φ₁ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he πL
    (T.level l)).choose_spec.1

omit [IsSepClosed k] [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)]
  [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma σP_φ₁ (l : ℕ) (z : Rt l ⊗[R] B) :
    (T.level l).σP (Ideal.Quotient.mk _ (V.φ₁ l z)) = algebraMap _ _
      (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he l z) :=
  haveI := V.etale l
  (exists_φ₁ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he πL
    (T.level l)).choose_spec.2 z

set_option maxRecDepth 20000 in
/-- **The level-`l` patch of the M2 lift is `Rt l ⊗_R B`** (`FormalCuspLevel.levelPatchEquiv`
at the level data `V`). -/
def equiv (l : ℕ) : Rt l ⊗[R] B ≃ₐ[Rt l] T.G hθ.out l :=
  haveI := V.isMaximal l
  haveI := V.etale l
  levelPatchEquiv 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he πL (T.level l)
    (V.hinj l) (V.hf l) (V.hrad l) (V.hm l) (V.Ψ l) (V.htL l) (V.hδL l) hO

omit [IsSepClosed k] [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)]
  [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
lemma equiv_fst (l : ℕ) (z : Rt l ⊗[R] B) : (V.equiv hO l z).1.1 = V.φ₁ l z := rfl

set_option maxRecDepth 20000 in
omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- **The level patches of the M2 lift form a tower**: `equiv` commutes with the transition maps
`tr` of the tower and the maps `Rt (l+1) ⊗_R B → Rt l ⊗_R B`. -/
theorem equiv_tr (l : ℕ) (z : Rt (l + 1) ⊗[R] B) :
    T.tr hθ.out hO l (V.equiv hO (l + 1) z) = V.equiv hO l (levelMap Rt l z) :=
  haveI := V.etale (l + 1)
  T.tr_eq_of_etale hθ.out hO l (V.φ₁ (l + 1)) (V.φ₁ l) (levelMap Rt l).toRingHom
    (fun c ↦ by
      change Algebra.TensorProduct.map _ _ (c ⊗ₜ (1 : B)) = _
      rw [Algebra.TensorProduct.map_tmul, map_one]
      rfl)
    (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he (l + 1))
    (ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T.hfe he l)
    (V.σP_φ₁ (l + 1)) (V.σP_φ₁ l)
    (ρ_levelMap 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T he l) z
    _ _ rfl rfl

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
/-- `equiv_tr` in the form `FormalCuspLevel.TrCompat` (a predicate on the family of level
identifications). -/
theorem trCompat : TrCompat T hO (V.equiv hO) :=
  fun l z ↦ V.equiv_tr hO l z

end CuspLevels

end

end FormalCuspLevel

end SemistableReduction
