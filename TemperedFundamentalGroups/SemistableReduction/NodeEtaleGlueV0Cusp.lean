/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalCuspLevelPatchTr
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueV0Levels
import TemperedFundamentalGroups.SemistableReduction.NodeEtaleGlueLevels

/-!
# The cusp patch from the level data of a chart without nodes (MR12 T2 S6, G4 over `V₀`)

Let `Dp : NodeEtaleGlue.PatchInput …` be a patch over `D(c₀)` of the second chart whose tower is
(up to the `k`-algebra structures on the special fibres) the tower of the cusp level data
`V : FormalCuspLevel.CuspLevels …` over the levels `Dp.R l` of the chart `D(c₀)`. Let `X` be a
`B0'`-algebra with a localization `t : X → Dp.R l ⊗_R B` away from `c₀` and a reduction
`ρX : X → C0` compatible with the reduction `ρ` of `V`. Then (the cusp analogues of
`FormalLevel.NodeLevels.inputEquiv`, `φGX`, `hGX`, `hlocGX`, `hρ_of_mk`):

* **`FormalCuspLevel.CuspLevels.PatchInputOf`**: the type of such patches with the implicit
  arguments of `V`;
* **`CuspLevels.inputEquivP`**: `Dp.R l ⊗_R B ≃ Dp.G l`, with `inputEquivP_tr`;
* **`CuspLevels.φPX`**: `X → Dp.R l ⊗_R B ≃ Dp.G l` over `B0'`, **`isLocalization_φPX`** (away
  from `c₀`), **`mk_Loc_φPX`** (its special fibre on `D(x₀)` is `ℓ0 ∘ ρX`: the hypothesis `hPℓ`
  of `NodeEtaleGlue.Overlap.φQn_compat`, via `PatchInput.mk_Loc`);
* **`CuspLevels.φPX_succ`**: compatibility with the transition maps `trG` of the patch;
* **`CuspLevels.hρ_of_mk`**: the compatibility of `ρX` with `ρ` from generators.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalCuspLevel

noncomputable section

open FormalKummer AdmissibleLift FormalLevel NodeEtaleGlue

variable {O : Type u} [CommRing O] {k : Type u} [Field k] {θ : O →+* k}
  [hθ : Fact (Function.Surjective θ)] {R : Type u} [CommRing R] [Algebra O R]
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
  {B0' : Type u} [CommRing B0'] {B' : ℕ → Type u} [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
  [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
  {Bs' : Type u} [CommRing Bs'] {qB' : ∀ n, B' n →+* Bs'} {C0 : Type u} [CommRing C0]
  [Algebra Bs' C0] {x0 c0 : B0'} {x0s c0s : Bs'} {ϖ : O}

/-- **The type of patches over `D(c₀)` of the covering `cov₀ …` of the cusp level data `V`**,
with the implicit arguments of `V` (a patch of another syntactic type, e.g. at the Tate curve, is
converted to this type once, by a type ascription). -/
abbrev CuspLevels.PatchInputOf {Rt : ℕ → Type u} [∀ l, CommRing (Rt l)] [∀ l, Algebra O (Rt l)]
    [∀ l, IsNoetherianRing (Rt l)] [∀ l, Algebra R (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
    [∀ l, Algebra (Rt (l + 1)) (Rt l)] [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)]
    [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)]
    {T : LevelTower.Data (θ := θ) Rt (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL}
    {he : ∀ l (r : R), T.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Rt l) r)}
    (_V : CuspLevels 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T he)
    (B' : ℕ → Type u) [∀ n, CommRing (B' n)] [∀ n, Algebra O (B' n)]
    [∀ n, Algebra B0' (B' n)] [∀ n, Algebra (B' (n + 1)) (B' n)]
    (qB' : ∀ n, B' n →+* Bs') (C0 : Type u) [CommRing C0] [Algebra Bs' C0] (x0 c0 : B0')
    (x0s c0s : Bs') (ϖ : O) :=
  PatchInput θ B' qB' C0 x0 c0 x0s c0s ϖ (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL

/-- **The type of the Kummer data `πL` of the covering `cov₀ …` of the cusp level data `V`**,
spelled with the implicit arguments of `V`. A patch of another syntactic type (e.g. at the Tate
curve, where `πL` is typed over the covering of the cusp input) should be typed with a `πL` of
this type: unifying the two spellings of the covering unfolds it, which costs seconds per type
class query on the levels of the patch. -/
abbrev CuspLevels.PiOf {Rt : ℕ → Type u} [∀ l, CommRing (Rt l)] [∀ l, Algebra O (Rt l)]
    [∀ l, IsNoetherianRing (Rt l)] [∀ l, Algebra R (Rt l)] [∀ l, IsScalarTower O R (Rt l)]
    [∀ l, Algebra (Rt (l + 1)) (Rt l)] [∀ l, IsScalarTower O (Rt (l + 1)) (Rt l)]
    [∀ l, IsScalarTower R (Rt (l + 1)) (Rt l)]
    {T : LevelTower.Data (θ := θ) Rt (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk) πL}
    {he : ∀ l (r : R), T.e l (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (algebraMap R (Rt l) r)}
    (_V : CuspLevels 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Rt T he) :=
  (cov₀ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk).ι → O

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

/-- **The level patches of `V` as the patches of `Dp`**: `Dp.R l ⊗_R B ≃ Dp.G l`. -/
def inputEquivP (l : ℕ) : Dp.R l ⊗[R] B ≃ₐ[Dp.R l] Dp.G hθ.out l :=
  (V.equiv hO l).trans (LevelTower.Data.GEquivOfInst _ Dp.algkR hkI T' Dp.T hT hθ.out l)

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
set_option maxRecDepth 20000 in
/-- **The level patches of `V` as the patches of `Dp` form a tower.** -/
theorem inputEquivP_tr (l : ℕ) (z : Dp.R (l + 1) ⊗[R] B) :
    Dp.T.tr hθ.out hO l (V.inputEquivP Dp hO hkI hT (l + 1) z) =
      V.inputEquivP Dp hO hkI hT l (levelMap Dp.R l z) :=
  (LevelTower.Data.GEquivOfInst_tr _ Dp.algkR hkI T' Dp.T hT hθ.out hO l
    (V.equiv hO (l + 1) z)).trans
    (congrArg (LevelTower.Data.GEquivOfInst _ Dp.algkR hkI T' Dp.T hT hθ.out l)
      (V.equiv_tr hO l z))

variable {l : ℕ} {X : Type u} [CommRing X] [Algebra B0' X]
  (t : X →+* Dp.R l ⊗[R] B)
  (ht : ∀ r, t (algebraMap B0' X r) = algebraMap (Dp.R l) (Dp.R l ⊗[R] B)
    (algebraMap (B' l) (Dp.R l) (algebraMap B0' (B' l) r)))

/-- **The patch side of `X`**: `X → Dp.R l ⊗_R B ≃ Dp.G l`, over `B0'` (through `B' l`). -/
def φPX : letI := ((algebraMap (B' l) (Dp.G hθ.out l)).comp (algebraMap B0' (B' l))).toAlgebra
    X →ₐ[B0'] Dp.G hθ.out l :=
  letI := ((algebraMap (B' l) (Dp.G hθ.out l)).comp (algebraMap B0' (B' l))).toAlgebra
  { (V.inputEquivP Dp hO hkI hT l).toRingEquiv.toRingHom.comp t with
    commutes' := fun r ↦ by
      change V.inputEquivP Dp hO hkI hT l (t (algebraMap B0' X r)) = _
      rw [ht, AlgEquiv.commutes]
      rfl }

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
lemma φPX_apply (x : X) : V.φPX Dp hO hkI hT t ht x = V.inputEquivP Dp hO hkI hT l (t x) := rfl

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII in
include ht in
/-- The patch side of `X` is a localization away from `c₀`. -/
theorem isLocalization_φPX (htloc : letI := t.toAlgebra
    IsLocalization.Away (algebraMap B0' X c0) (Dp.R l ⊗[R] B)) :
    letI := ((algebraMap (B' l) (Dp.G hθ.out l)).comp (algebraMap B0' (B' l))).toAlgebra
    letI := (V.φPX Dp hO hkI hT t ht).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap B0' X c0) (Dp.G hθ.out l) :=
  RingHomAway.equiv _ (V.inputEquivP Dp hO hkI hT l).toRingEquiv _ htloc

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
set_option maxRecDepth 20000 in
/-- **The patch sides form a tower**: for `μ : X' → X` (levels `l + 1`, `l`) compatible with the
maps `t` and `levelMap`, `φPX` commutes with the transition maps `trG` of the patch. -/
theorem φPX_succ {X' : Type u} [CommRing X'] [Algebra B0' X'] (t' : X' →+* Dp.R (l + 1) ⊗[R] B)
    (ht' : ∀ r, t' (algebraMap B0' X' r) = algebraMap (Dp.R (l + 1)) (Dp.R (l + 1) ⊗[R] B)
      (algebraMap (B' (l + 1)) (Dp.R (l + 1)) (algebraMap B0' (B' (l + 1)) r)))
    (μ : X' →+* X) (hμt : ∀ x, t (μ x) = levelMap Dp.R l (t' x)) (x : X') :
    Dp.trG hθ.out hO l (V.φPX Dp hO hkI hT t' ht' x) = V.φPX Dp hO hkI hT t ht (μ x) :=
  (V.inputEquivP_tr Dp hO hkI hT l (t' x)).trans
    (congrArg (V.inputEquivP Dp hO hkI hT l) (hμt x).symm)

variable (ρX : X →+* C0)
  (hρ : letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he l (t x) = Dp.ι₀ (ρX x))

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] towerRII [Algebra B0' X] in
set_option maxRecDepth 20000 in
include hρ in
/-- **The special fibre of the patch side on `D(x₀)` is `ℓ0 ∘ ρX`** (the hypothesis `hPℓ` of
`NodeEtaleGlue.Overlap.φQn_compat`, by `PatchInput.mk_Loc`). -/
theorem mk_Loc_φPX (x : X) :
    Ideal.Quotient.mk (EtaleNil.JB (J θ (R := B' l)) (Dp.Loc hθ.out l))
      (algebraMap (Dp.G hθ.out l) (Dp.Loc hθ.out l) (V.inputEquivP Dp hO hkI hT l (t x))) =
      Dp.ℓ0 hθ.out hO l (ρX x) := by
  refine Dp.mk_Loc hθ.out hO l _ (ρX x) ?_
  have h := V.σP_φ₁ l (t x)
  rw [hρ] at h
  exact LevelTower.Data.GEquivOfInst_σP _ Dp.algkR hkI T' Dp.T hT hθ.out l
    (V.equiv hO l (t x)) (Dp.ι₀ (ρX x)) h

omit [IsSepClosed k] [∀ j, (sIdeal (θ := θ) (𝔪 j)).IsMaximal] in
set_option linter.unusedSectionVars false in
-- `V` is included for field notation at the instances
include V in
/-- **The compatibility of `ρX` with `ρ` from generators**: if `t` maps generators `q z` of `X` to
`1 ⊗ u z` and `ι₀ (ρX (q z))` is the class of `u z` in `C = B/JB`, then `ρ ∘ t = ι₀ ∘ ρX`. -/
theorem hρ_of_mk {Z : Type u} (q : Z → X) (hq : Function.Surjective q) (u : Z → B)
    (htu : ∀ z, t (q z) = (1 : Dp.R l) ⊗ₜ u z)
    (hι : ∀ z, Dp.ι₀ (ρX (q z)) =
      (Ideal.Quotient.mk ((J θ (R := R)).map (algebraMap R B)) (u z) : Cs θ R B)) :
    letI := fun l ↦ QuadNodeTower.algK (θ := θ) (Dp.R l)
    ∀ x, ρ 𝔪 hJ D hinjk hfk hradk φ₀ ψk hψ hfin het hk Dp.R T'.hfe he l (t x) =
      Dp.ι₀ (ρX x) := by
  intro x
  obtain ⟨z, rfl⟩ := hq x
  rw [htu, ρ_one_tmul, hι]
  rfl

end CuspLevels

end

end FormalCuspLevel

end SemistableReduction
