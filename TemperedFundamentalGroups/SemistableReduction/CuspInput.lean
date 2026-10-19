/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspTower
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Patch
import TemperedFundamentalGroups.SemistableReduction.TateLevel

/-!
# A cusp patch on a basic open of a chart (Blueprint §12.8, M2.3 (f), cusps)

For a Noetherian chart `T0'` (an `O`-algebra, levels `Tn n = T0'/ϖⁿ⁺¹`, special fibre `Ts`),
elements `c₀, x₀ ∈ T0'` and the chart `Rc = T0'[1/c₀]` with the coordinate `s = x₀`, whose zero
locus in `D(c̄₀)` on the special fibre consists of marked points (no nodes in `D(c₀)`):

* `CuspTower.algBR`, `isLocalization_BR`: the levels of `Rc` are `Tn n[1/c₀]`;
  `isSMulRegular_s`: `s` is regular on them if `x₀` is regular on the levels of `T0'`;
* **`CuspTower.CuspSpecial`**: the special-fibre data — a covering `C0` of `Ts`, an admissible
  covering `cov` of `Rc/J` without nodes and with cusp factors along `s`, and `ι₀ : C0 → cov.C`
  exhibiting `cov.C` as `C0[1/c̄₀]`;
* **`CuspTower.cuspInput`** (a `NodeEtaleGlue.PatchInput`) and **`CuspTower.cuspPiece`** (a
  `NodeEtaleGlue.Piece0`): the piece of the covering over `D(c₀)`.
-/

universe u

namespace SemistableReduction

namespace CuspTower

open TateLevel AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] (ϖ : O) (T0' : Type u) [CommRing T0'] [Algebra O T0']
  (c0 x0 : T0')

/-- **The chart `D(c₀)`.** -/
abbrev Rc : Type u := Localization.Away c0

/-- The coordinate `x₀` on `Rc`. -/
abbrev sC : Rc T0' c0 := algebraMap T0' (Rc T0' c0) x0

instance [IsNoetherianRing T0'] : IsNoetherianRing (Rc T0' c0) :=
  IsLocalization.isNoetherianRing (Submonoid.powers c0) _ inferInstance

instance towerSucc (n : ℕ) : IsScalarTower T0' (Tn ϖ T0' (n + 1)) (Tn ϖ T0' n) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The levels of `Rc` over the levels of `T0'`. -/
@[reducible] def algBR (n : ℕ) : Algebra (Tn ϖ T0' n) (Tn ϖ (Rc T0' c0) n) :=
  (quotMap (IsScalarTower.toAlgHom O T0' (Rc T0' c0)) (EtaleTower.Iv ϖ n)).toAlgebra

lemma towerBR (n : ℕ) : letI := algBR ϖ T0' c0 n
    IsScalarTower O (Tn ϖ T0' n) (Tn ϖ (Rc T0' c0) n) :=
  letI := algBR ϖ T0' c0 n
  IsScalarTower.of_algebraMap_eq fun o ↦ by
    change _ = quotMap _ _ (Ideal.Quotient.mk _ (algebraMap O T0' o))
    rw [quotMap_mk, AlgHom.commutes]
    rfl

lemma isLocalization_BR (n : ℕ) : letI := algBR ϖ T0' c0 n
    IsLocalization.Away (algebraMap T0' (Tn ϖ T0' n) c0) (Tn ϖ (Rc T0' c0) n) :=
  isLocalization_quotMap c0 (EtaleTower.Iv ϖ n)

/-- **`s` is regular on the levels of `Rc`** if `x₀` is regular on the levels of `T0'`. -/
theorem isSMulRegular_s (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))
    (n : ℕ) : IsSMulRegular (Tn ϖ (Rc T0' c0) n) (fn (ϖ := ϖ) _ (sC T0' c0 x0) n) := by
  letI := algBR ϖ T0' c0 n
  haveI := isLocalization_BR ϖ T0' c0 n
  haveI : Module.Flat (Tn ϖ T0' n) (Tn ϖ (Rc T0' c0) n) :=
    IsLocalization.flat _ (Submonoid.powers (algebraMap T0' (Tn ϖ T0' n) c0))
  exact (hx n).of_flat (S := Tn ϖ (Rc T0' c0) n)

/-! ### The special-fibre data -/

variable {k : Type u} [Field k] (θ : O →+* k)

lemma J_le_comap : J θ (R := T0') ≤
    (J θ (R := Rc T0' c0)).comap (algebraMap T0' (Rc T0' c0)) := by
  rw [J, J, Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
  exact Ideal.le_comap_map

/-- The special fibre of `T0'` to the special fibre of `Rc`. -/
def φsC : Ts θ T0' →+* Ts θ (Rc T0' c0) :=
  Ideal.quotientMap _ (algebraMap T0' (Rc T0' c0)) (J_le_comap T0' c0 θ)

variable [hθ : Fact (Function.Surjective θ)] {θ}

/-- **The special-fibre data of a covering around marked points in `D(c₀)`**: a covering `C0` of
the special fibre `Ts` of the chart and an admissible covering `cov` of the special fibre of
`Rc = T0'[1/c₀]` **without nodes**, with cusp factors along `s`, which is `C0[1/c̄₀]` (`ι₀`). -/
structure CuspSpecial where
  C0 : Type u
  [commRing : CommRing C0]
  [algebra : Algebra (Ts θ T0') C0]
  φ₀ : Node k (0 : k) →ₐ[k] Admissible.Hat (fbar θ (sC T0' c0 x0))
  cov : Admissible.Covering φ₀ (ψb (θ := θ) _ (sC T0' c0 x0) (sC T0' c0 x0))
  [noNodes : IsEmpty cov.ι]
  ι₀ : C0 →+* cov.C
  hι₀ : ∀ x, ι₀ (algebraMap (Ts θ T0') C0 x) =
    algebraMap (Ts θ (Rc T0' c0)) cov.C (φsC T0' c0 θ x)
  hι : letI := ι₀.toAlgebra
    IsLocalization.Away (algebraMap (Ts θ T0') C0 (Ideal.Quotient.mk _ c0)) cov.C

attribute [instance] CuspSpecial.commRing CuspSpecial.algebra CuspSpecial.noNodes

variable {T0' c0 x0} (Sc : CuspSpecial T0' c0 x0 (θ := θ)) {ϖ} (hϖ : θ ϖ = 0)
  (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) [IsNoetherianRing T0']
  (hx : ∀ n, IsSMulRegular (Tn ϖ T0' n)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ n).map (algebraMap O T0')) x0 : Tn ϖ T0' n))

/-- The (empty) deformation parameters of the Kummer factors. -/
def πc : Sc.cov.ι → O := fun j ↦ isEmptyElim j

/-- **The tower of patched algebras on `D(c₀)`.** -/
abbrev cuspTower : LevelTower.Data (θ := θ) (Tn ϖ (Rc T0' c0)) Sc.cov (πc Sc) :=
  tower _ hϖ (sC T0' c0 x0) (sC T0' c0 x0) Sc.cov (πc Sc) hker (isSMulRegular_s ϖ T0' c0 x0 hx)

lemma hφsC (n : ℕ) (x : Tn ϖ T0' n) :
    (cuspTower Sc hϖ hker hx).e n (φsC T0' c0 θ (EtaleTower.q T0' hϖ n x)) =
      Ideal.Quotient.mk _ (letI := algBR ϖ T0' c0 n
        algebraMap (Tn ϖ T0' n) (Tn ϖ (Rc T0' c0) n) x) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact eqv_mk _ hϖ n _

/-- **The cusp patch as a `NodeEtaleGlue.PatchInput`** over `D(c₀)`. -/
def cuspInput : NodeEtaleGlue.PatchInput θ (Tn ϖ T0') (EtaleTower.q T0' hϖ) Sc.C0
    x0 c0 (Ideal.Quotient.mk _ x0) (Ideal.Quotient.mk _ c0) ϖ Sc.cov (πc Sc) where
  R := Tn ϖ (Rc T0' c0)
  T := cuspTower Sc hϖ hker hx
  algBR := algBR ϖ T0' c0
  towerOBR := towerBR ϖ T0' c0
  away := isLocalization_BR ϖ T0' c0
  φs := φsC T0' c0 θ
  hφs := hφsC Sc hϖ hker hx
  ι₀ := Sc.ι₀
  hι₀ := Sc.hι₀
  hc0 := fun _ ↦ rfl
  hx0 := fun _ ↦ rfl
  hι := Sc.hι
  kdiv := fun _ ↦ 1
  hdiv := fun _ ↦ by rw [pow_one]; exact dvd_refl _
  hBR := fun _ x ↦ by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  hkR := fun n ↦ ker_succ_T _ n

variable (hO : ∀ x : O, θ x ≠ 0 → IsUnit x)

/-- **The piece of a covering, tamely ramified over marked points in `D(c₀) ∖ D(x₀)`, over
`D(c₀)`** (a `NodeEtaleGlue.Piece0`). -/
abbrev cuspPiece : NodeEtaleGlue.Piece0 θ (Tn ϖ T0') (EtaleTower.q T0' hϖ) Sc.C0
    x0 c0 (Ideal.Quotient.mk _ x0) (Ideal.Quotient.mk _ c0) ϖ :=
  (cuspInput Sc hϖ hker hx).piece hθ.out hO

end

end CuspTower

end SemistableReduction
