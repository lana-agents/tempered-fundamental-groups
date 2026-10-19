/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0
import TemperedFundamentalGroups.SemistableReduction.TateLevel
import TemperedFundamentalGroups.SemistableReduction.EtaleNil

/-!
# The special fibre of the Tate overlap chart (Blueprint §12.8, M2.3 (f))

The overlap datum `ω` of `NodeEtaleGlue.Overlap` is an isomorphism `C0[1/x̄₀] ≃ₐ[Ws] C1[1/x̄₁]`
over the special fibre `Ws` of the overlap chart. This file provides the algebra structures needed
to state it:

* `AwayAlg.alg`, `AwayAlg.tower` (generic): for `W = S[1/s]` and an `S`-algebra `C`,
  `C[1/s]` is a `W`-algebra (`IsLocalization.Away.map`);
* `TateGlue0.T01s`: the special fibre `T01/J` of the overlap chart `T01 = T1[1/h'] = T0[1/h]`;
  `TateGlue0.alg1s`, `alg0s` (`T1/J → T01/J`, `T0/J → T01/J`), **`isLocalization_alg1s`**,
  **`isLocalization_alg0s`** (`T01/J = (T1/J)[1/h̄'] = (T0/J)[1/h̄]`, `isLocalization_red`);
* `TateGlue0.algC1x`, `algC0x` (+ `towerC1x`, `towerC0x`): `C1[1/h̄']` and `C0[1/h̄]` over
  `T01/J`, for special-fibre coverings `C1` of `T1/J` and `C0` of `T0/J` (the type of `ω`).
-/

universe u

namespace SemistableReduction

namespace AwayAlg

variable {S W C : Type u} [CommRing S] [CommRing W] [CommRing C] [Algebra S W] [Algebra S C]
  (s : S) [IsLocalization.Away s W]

/-- **`C[1/s]` as an algebra over `W = S[1/s]`.** -/
@[reducible] noncomputable def alg : Algebra W (Localization.Away (algebraMap S C s)) :=
  (IsLocalization.Away.map W (Localization.Away (algebraMap S C s)) (algebraMap S C) s).toAlgebra

lemma tower : letI := alg (C := C) (W := W) s
    IsScalarTower S W (Localization.Away (algebraMap S C s)) :=
  letI := alg (C := C) (W := W) s
  IsScalarTower.of_algebraMap_eq fun x ↦ by
    change _ = IsLocalization.Away.map W _ (algebraMap S C) s (algebraMap S W x)
    rw [IsLocalization.Away.map, IsLocalization.map_eq, ← IsScalarTower.algebraMap_apply]

end AwayAlg

namespace TateGlue0

open TateTwoChart

noncomputable section

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k) (π b₄ t κ : O)

/-- **The special fibre of the overlap chart** `T01 = T1[1/h']`. -/
abbrev T01s : Type u := EtaleTower.Ts θ (T01 π b₄ t κ)

/-- `T1/J → T01/J`. -/
@[reducible] def alg1s : Algebra (EtaleTower.Ts θ (T1 π b₄ t κ)) (T01s θ π b₄ t κ) :=
  (EtaleNil.red (RingHom.ker θ)
    (IsScalarTower.toAlgHom O (T1 π b₄ t κ) (T01 π b₄ t κ))).toRingHom.toAlgebra

/-- `T0/J → T01/J` (through `ρ₀`). -/
@[reducible] def alg0s : Algebra (EtaleTower.Ts θ (T0 π b₄ t κ)) (T01s θ π b₄ t κ) :=
  (EtaleNil.red (RingHom.ker θ) (rho0 π b₄ t κ)).toRingHom.toAlgebra

/-- **`T01/J = (T1/J)[1/h̄']`.** -/
theorem isLocalization_alg1s : letI := alg1s θ π b₄ t κ
    IsLocalization.Away (Ideal.Quotient.mk _ (h1 π b₄ t κ) : EtaleTower.Ts θ (T1 π b₄ t κ))
      (T01s θ π b₄ t κ) :=
  EtaleNil.isLocalization_red (RingHom.ker θ) (h1 π b₄ t κ)

/-- **`T01/J = (T0/J)[1/h̄]`.** -/
theorem isLocalization_alg0s : letI := alg0s θ π b₄ t κ
    IsLocalization.Away (Ideal.Quotient.mk _ (h0 π b₄ t κ) : EtaleTower.Ts θ (T0 π b₄ t κ))
      (T01s θ π b₄ t κ) := by
  letI := (rho0 π b₄ t κ : T0 π b₄ t κ →+* T01 π b₄ t κ).toAlgebra
  haveI : IsScalarTower O (T0 π b₄ t κ) (T01 π b₄ t κ) :=
    IsScalarTower.of_algebraMap_eq fun o ↦ ((rho0 π b₄ t κ).commutes o).symm
  haveI := TateLevel.isLocalization_rho0 π b₄ t κ
  exact EtaleNil.isLocalization_red (RingHom.ker θ) (h0 π b₄ t κ)

variable {θ π b₄ t κ}

/-- `C1[1/h̄']` over `T01/J`. -/
@[reducible] def algC1x (C1 : Type u) [CommRing C1] [Algebra (EtaleTower.Ts θ (T1 π b₄ t κ)) C1] :
    Algebra (T01s θ π b₄ t κ) (Localization.Away (algebraMap (EtaleTower.Ts θ (T1 π b₄ t κ)) C1
      (Ideal.Quotient.mk _ (h1 π b₄ t κ)))) :=
  letI := alg1s θ π b₄ t κ
  haveI := isLocalization_alg1s θ π b₄ t κ
  AwayAlg.alg _

lemma towerC1x (C1 : Type u) [CommRing C1] [Algebra (EtaleTower.Ts θ (T1 π b₄ t κ)) C1] :
    letI := alg1s θ π b₄ t κ; letI := algC1x C1 (θ := θ) (π := π) (b₄ := b₄) (t := t) (κ := κ)
    IsScalarTower (EtaleTower.Ts θ (T1 π b₄ t κ)) (T01s θ π b₄ t κ)
      (Localization.Away (algebraMap (EtaleTower.Ts θ (T1 π b₄ t κ)) C1
        (Ideal.Quotient.mk _ (h1 π b₄ t κ)))) :=
  letI := alg1s θ π b₄ t κ
  haveI := isLocalization_alg1s θ π b₄ t κ
  AwayAlg.tower _

/-- `C0[1/h̄]` over `T01/J`. -/
@[reducible] def algC0x (C0 : Type u) [CommRing C0] [Algebra (EtaleTower.Ts θ (T0 π b₄ t κ)) C0] :
    Algebra (T01s θ π b₄ t κ) (Localization.Away (algebraMap (EtaleTower.Ts θ (T0 π b₄ t κ)) C0
      (Ideal.Quotient.mk _ (h0 π b₄ t κ)))) :=
  letI := alg0s θ π b₄ t κ
  haveI := isLocalization_alg0s θ π b₄ t κ
  AwayAlg.alg _

lemma towerC0x (C0 : Type u) [CommRing C0] [Algebra (EtaleTower.Ts θ (T0 π b₄ t κ)) C0] :
    letI := alg0s θ π b₄ t κ; letI := algC0x C0 (θ := θ) (π := π) (b₄ := b₄) (t := t) (κ := κ)
    IsScalarTower (EtaleTower.Ts θ (T0 π b₄ t κ)) (T01s θ π b₄ t κ)
      (Localization.Away (algebraMap (EtaleTower.Ts θ (T0 π b₄ t κ)) C0
        (Ideal.Quotient.mk _ (h0 π b₄ t κ)))) :=
  letI := alg0s θ π b₄ t κ
  haveI := isLocalization_alg0s θ π b₄ t κ
  AwayAlg.tower _

end

end TateGlue0

end SemistableReduction
