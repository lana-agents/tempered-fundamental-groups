/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateAffine
import TemperedFundamentalGroups.SemistableReduction.ZariskiTwoEtale

/-!
# Glueing the generic fibre of a Tate covering over `E ∖ {0}` (T1a, generic part)

Let `ι₀ : T0 → B₀`, `ι₁ : T1 → B₁`, `ι₀₁ : T01 → B₀₁` be ring maps from the chart rings of the
Tate model (`TateTwoChart.twoChart`) to the rings of a covering over the two charts and their
overlap, compatible with the restrictions `r₀ : B₀ → B₀₁`, `r₁ : B₁ → B₀₁`, which are the
localizations away from `h` and `h'` (for a chart algebra `B` over the Tate model these are
`B.Ring0`, `B.Ring1`, `B.Ring01`, `B.r0Hom`, `B.r1Hom`; `TateAffineGlueChart`).

The generic fibres of the pieces over `E ∖ {0} = D(y − t) ∪ D(x)` (`TateAffine.span_a_x`) are
`Ba = B₀[1/(ϖ z)]` over `T0[1/(ϖ z)] = A[1/ϖ][1/(y − t)]` and `Bb = B₁[1/ϖ]` over
`T1[1/ϖ] = A[1/ϖ][1/x]`, glued along `Bab = B₀₁[1/ϖ]` (**`TateAffine.rhoA`**, **`rhoB`**, the
`A[1/ϖ]`-algebra structures `algA`, `algB`, `algAB`). The glued algebra
**`TateAffine.gluedK`** over the coordinate ring `A[1/ϖ]` of `E ∖ {0}` satisfies:

* **`TateAffine.isLocalization_gluedK_fst`** / **`_snd`**: `Ba = gluedK[1/(y − t)]`,
  `Bb = gluedK[1/x]`;
* **`TateAffine.etale_gluedK`**: it is étale over `A[1/ϖ]` if `Ba` is étale over `T0[1/ϖ]` and
  `Bb` over `T1[1/ϖ]` (the conclusions of `TateGlue0.etale_overlapCusp_z` and
  `TateGlue0.etale_overlapCusp`);
* **`TateAffine.finite_gluedK`**: it is finite over `A[1/ϖ]` if `B₀`, `B₁` are finite over `T0`,
  `T1`.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace TateAffine

open TateTwoChart TemperedFundamentalGroups.TateNormal

noncomputable section

variable {O : Type u} [CommRing O] (b₄ : O) {π b₆ t κ ϖ : O} {m : ℕ}
  (hκ : κ * (t ^ 2 - b₆) = 1) (hπ : π ∣ ϖ ^ m)
  {B0 B1 B01 : Type u} [CommRing B0] [CommRing B1] [CommRing B01]
  (ι0 : T0 π b₄ t κ →+* B0) (ι1 : T1 π b₄ t κ →+* B1) (ι01 : T01 π b₄ t κ →+* B01)
  (r0 : B0 →+* B01) (r1 : B1 →+* B01)

variable (ϖ) in
/-- `Ba = B₀[1/(ϖ z)]`. -/
abbrev Ba : Type u := Localization.Away (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ))

variable (ϖ) in
/-- `Bb = B₁[1/ϖ]`. -/
abbrev Bb : Type u := Localization.Away (ι1 (algebraMap O (T1 π b₄ t κ) ϖ))

variable (ϖ) in
/-- `Bab = B₀₁[1/ϖ]`. -/
abbrev Bab : Type u := Localization.Away (ι01 (algebraMap O (T01 π b₄ t κ) ϖ))

variable (ϖ) in
/-- `T0[1/(ϖ z)] → B₀[1/(ϖ z)]`. -/
abbrev iotaA : T0K π b₄ t κ ϖ →+* Ba b₄ ϖ ι0 :=
  IsLocalization.map (Ba b₄ ϖ ι0) ι0
    (Submonoid.le_comap_map (Submonoid.powers (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)))

variable (ϖ) in
/-- `T1[1/ϖ] → B₁[1/ϖ]`. -/
abbrev iotaB : T1K π b₄ t κ ϖ →+* Bb b₄ ϖ ι1 :=
  IsLocalization.map (Bb b₄ ϖ ι1) ι1
    (Submonoid.le_comap_map (Submonoid.powers (algebraMap O (T1 π b₄ t κ) ϖ)))

variable (ϖ) in
/-- `T01[1/ϖ] → B₀₁[1/ϖ]`. -/
abbrev iotaAB : T01K π b₄ t κ ϖ →+* Bab b₄ ϖ ι01 :=
  IsLocalization.map (Bab b₄ ϖ ι01) ι01
    (Submonoid.le_comap_map (Submonoid.powers (algebraMap O (T01 π b₄ t κ) ϖ)))

variable (ϖ) in
lemma iotaA_algebraMap (a : T0 π b₄ t κ) :
    iotaA b₄ ϖ ι0 (algebraMap _ _ a) = algebraMap B0 (Ba b₄ ϖ ι0) (ι0 a) :=
  IsLocalization.map_eq _ a

variable (ϖ) in
lemma iotaB_algebraMap (a : T1 π b₄ t κ) :
    iotaB b₄ ϖ ι1 (algebraMap _ _ a) = algebraMap B1 (Bb b₄ ϖ ι1) (ι1 a) :=
  IsLocalization.map_eq _ a

variable (ϖ) in
lemma iotaAB_algebraMap (a : T01 π b₄ t κ) :
    iotaAB b₄ ϖ ι01 (algebraMap _ _ a) = algebraMap B01 (Bab b₄ ϖ ι01) (ι01 a) :=
  IsLocalization.map_eq _ a

section Restrictions

variable {ι0 ι1 ι01 r0 r1}
  (hc0 : r0.comp ι0 = ι01.comp (rho0 π b₄ t κ).toRingHom)
  (hc1 : r1.comp ι1 = ι01.comp (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ)))

include hc0 in
lemma r0_iota0 (a : T0 π b₄ t κ) : r0 (ι0 a) = ι01 (rho0 π b₄ t κ a) :=
  RingHom.congr_fun hc0 a

include hc1 in
lemma r1_iota1 (a : T1 π b₄ t κ) : r1 (ι1 a) = ι01 (algebraMap _ _ a) :=
  RingHom.congr_fun hc1 a

include hc0 hκ hπ in
lemma isUnit_rhoA :
    IsUnit (((algebraMap B01 (Bab b₄ ϖ ι01)).comp r0)
      (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ))) := by
  rw [RingHom.comp_apply, r0_iota0 b₄ hc0, ← iotaAB_algebraMap, ← r0K_algebraMap b₄ hκ hπ]
  exact ((IsLocalization.Away.algebraMap_isUnit _).map (r0K b₄ hκ hπ)).map _

include hc1 in
lemma isUnit_rhoB :
    IsUnit (((algebraMap B01 (Bab b₄ ϖ ι01)).comp r1) (ι1 (algebraMap O (T1 π b₄ t κ) ϖ))) := by
  rw [RingHom.comp_apply, r1_iota1 b₄ hc1, ← IsScalarTower.algebraMap_apply]
  exact IsLocalization.Away.algebraMap_isUnit _

/-- `Ba → Bab`, induced by `r₀`. -/
def rhoA : Ba b₄ ϖ ι0 →+* Bab b₄ ϖ ι01 :=
  IsLocalization.Away.lift _ (isUnit_rhoA b₄ hκ hπ hc0)

/-- `Bb → Bab`, induced by `r₁`. -/
def rhoB : Bb b₄ ϖ ι1 →+* Bab b₄ ϖ ι01 :=
  IsLocalization.Away.lift _ (isUnit_rhoB b₄ hc1)

lemma rhoA_algebraMap (a : B0) :
    rhoA b₄ hκ hπ hc0 (algebraMap _ _ a) = algebraMap B01 (Bab b₄ ϖ ι01) (r0 a) :=
  IsLocalization.Away.lift_eq _ (isUnit_rhoA b₄ hκ hπ hc0) a

lemma rhoB_algebraMap (a : B1) :
    rhoB b₄ hc1 (algebraMap _ _ a) = algebraMap B01 (Bab b₄ ϖ ι01) (r1 a) :=
  IsLocalization.Away.lift_eq _ (isUnit_rhoB b₄ hc1) a

lemma rhoA_iotaA : (rhoA b₄ hκ hπ hc0).comp (iotaA b₄ ϖ ι0) =
    (iotaAB b₄ ϖ ι01).comp (r0K b₄ hκ hπ : T0K π b₄ t κ ϖ →+* T01K π b₄ t κ ϖ) := by
  refine IsLocalization.ringHom_ext
    (Submonoid.powers (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)) (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.comp_apply, iotaA_algebraMap, rhoA_algebraMap, RingHom.coe_coe,
    r0K_algebraMap, iotaAB_algebraMap, r0_iota0 b₄ hc0]

lemma rhoB_iotaB : (rhoB b₄ hc1).comp (iotaB b₄ ϖ ι1) =
    (iotaAB b₄ ϖ ι01).comp (r1K π b₄ t κ ϖ : T1K π b₄ t κ ϖ →+* T01K π b₄ t κ ϖ) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap O (T1 π b₄ t κ) ϖ))
    (RingHom.ext fun a ↦ ?_)
  simp only [RingHom.comp_apply, iotaB_algebraMap, rhoB_algebraMap, RingHom.coe_coe,
    r1K_algebraMap, iotaAB_algebraMap, r1_iota1 b₄ hc1]

/-! ### The `A[1/ϖ]`-algebra structures -/

variable (ϖ ι0) in
/-- The `A[1/ϖ]`-algebra structure of `Ba` (through `T0[1/(ϖ z)]`). -/
abbrev algA : Algebra (AK π b₄ b₆ ϖ) (Ba b₄ ϖ ι0) :=
  ((iotaA b₄ ϖ ι0).comp (f0K π b₄ ϖ hκ : AK π b₄ b₆ ϖ →+* T0K π b₄ t κ ϖ)).toAlgebra

variable (ι1) in
/-- The `A[1/ϖ]`-algebra structure of `Bb` (through `T1[1/ϖ]`). -/
abbrev algB : Algebra (AK π b₄ b₆ ϖ) (Bb b₄ ϖ ι1) :=
  ((iotaB b₄ ϖ ι1).comp (f1K b₄ hκ hπ : AK π b₄ b₆ ϖ →+* T1K π b₄ t κ ϖ)).toAlgebra

/-- The `A[1/ϖ]`-algebra structure of `Bab` (through `Bb`). -/
abbrev algAB : Algebra (AK π b₄ b₆ ϖ) (Bab b₄ ϖ ι01) :=
  ((rhoB b₄ hc1).comp ((iotaB b₄ ϖ ι1).comp
    (f1K b₄ hκ hπ : AK π b₄ b₆ ϖ →+* T1K π b₄ t κ ϖ))).toAlgebra

/-- `Ba → Bab` as an `A[1/ϖ]`-algebra map (the two charts agree on the overlap,
`TateAffine.r0K_comp`). -/
def rhoAA : letI := algA b₄ ϖ hκ ι0; letI := algAB b₄ hκ hπ hc1
    Ba b₄ ϖ ι0 →ₐ[AK π b₄ b₆ ϖ] Bab b₄ ϖ ι01 :=
  letI := algA b₄ ϖ hκ ι0
  letI := algAB b₄ hκ hπ hc1
  { rhoA b₄ hκ hπ hc0 with
    commutes' := fun x ↦ by
      change (rhoA b₄ hκ hπ hc0) (iotaA b₄ ϖ ι0 (f0K π b₄ ϖ hκ x)) =
        rhoB b₄ hc1 (iotaB b₄ ϖ ι1 (f1K b₄ hκ hπ x))
      rw [← RingHom.comp_apply (rhoA b₄ hκ hπ hc0), rhoA_iotaA,
        ← RingHom.comp_apply (rhoB b₄ hc1), rhoB_iotaB, RingHom.comp_apply, RingHom.comp_apply]
      congr 1
      exact AlgHom.congr_fun (r0K_comp b₄ hκ hπ) x }

/-- `Bb → Bab` as an `A[1/ϖ]`-algebra map. -/
def rhoBA : letI := algB b₄ hκ hπ ι1; letI := algAB b₄ hκ hπ hc1
    Bb b₄ ϖ ι1 →ₐ[AK π b₄ b₆ ϖ] Bab b₄ ϖ ι01 :=
  letI := algB b₄ hκ hπ ι1
  letI := algAB b₄ hκ hπ hc1
  { rhoB b₄ hc1 with commutes' := fun _ ↦ rfl }

/-- **The generic fibre of the covering over `E ∖ {0}`**: the glueing of `Ba` and `Bb` along
`Bab`, an `A[1/ϖ]`-algebra. -/
abbrev gluedK : letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    Subalgebra (AK π b₄ b₆ ϖ) (Ba b₄ ϖ ι0 × Bb b₄ ϖ ι1) :=
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  letI := algAB b₄ hκ hπ hc1
  ZariskiTwo.glued (rhoAA b₄ hκ hπ hc0 hc1) (rhoBA b₄ hκ hπ hc1)

end Restrictions


section Theorems

variable {ι0 ι1 ι01 r0 r1}
  (hc0 : r0.comp ι0 = ι01.comp (rho0 π b₄ t κ).toRingHom)
  (hc1 : r1.comp ι1 = ι01.comp (algebraMap (T1 π b₄ t κ) (T01 π b₄ t κ)))
  (hloc0 : letI := r0.toAlgebra; IsLocalization.Away (ι0 (h0 π b₄ t κ)) B01)
  (hloc1 : letI := r1.toAlgebra; IsLocalization.Away (ι1 (h1 π b₄ t κ)) B01)

lemma f1K_aK : f1K b₄ hκ hπ (aK π b₄ b₆ t ϖ) = hK π b₄ t κ ϖ * wInv b₄ hκ hπ := by
  rw [aK, map_sub, AlgHom.commutes, f1K_algebraMap, f1_y, sK_eq]
  linear_combination (algebraMap O _ t) * wK_mul_wInv b₄ hκ hπ

variable (ι0) in
lemma isUnit_a : letI := algA b₄ ϖ hκ ι0
    IsUnit (algebraMap (AK π b₄ b₆ ϖ) (Ba b₄ ϖ ι0) (aK π b₄ b₆ t ϖ)) := by
  letI := algA b₄ ϖ hκ ι0
  change IsUnit (iotaA b₄ ϖ ι0 (f0K π b₄ ϖ hκ (aK π b₄ b₆ t ϖ)))
  rw [f0K_aK]
  exact (Units.isUnit _).map _

variable (ι1) in
lemma isUnit_x : letI := algB b₄ hκ hπ ι1
    IsUnit (algebraMap (AK π b₄ b₆ ϖ) (Bb b₄ ϖ ι1) (xK π b₄ b₆ ϖ)) := by
  letI := algB b₄ hκ hπ ι1
  change IsUnit (iotaB b₄ ϖ ι1 (f1K b₄ hκ hπ (xK π b₄ b₆ ϖ)))
  rw [f1K_algebraMap, f1_x]
  exact (Units.isUnit _).map _

include hloc1 in
/-- `Bab = Bb[1/(y − t)]`. -/
lemma isLocalization_Bab_b : letI := algB b₄ hκ hπ ι1; letI := algAB b₄ hκ hπ hc1
    letI := (rhoBA b₄ hκ hπ hc1).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (AK π b₄ b₆ ϖ) (Bb b₄ ϖ ι1) (aK π b₄ b₆ t ϖ))
      (Bab b₄ ϖ ι01) := by
  letI := algB b₄ hκ hπ ι1
  letI : Algebra B1 B01 := r1.toAlgebra
  letI := algAB b₄ hκ hπ hc1
  letI : Algebra (Bb b₄ ϖ ι1) (Bab b₄ ϖ ι01) := (rhoBA b₄ hκ hπ hc1).toRingHom.toAlgebra
  haveI : IsScalarTower B1 (Bb b₄ ϖ ι1) (Bab b₄ ϖ ι01) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply B1 B01 (Bab b₄ ϖ ι01)]
      exact (rhoB_algebraMap b₄ hc1 a).symm
  have e : algebraMap B1 B01 (ι1 (algebraMap O (T1 π b₄ t κ) ϖ)) =
      ι01 (algebraMap O (T01 π b₄ t κ) ϖ) := by
    change r1 _ = _
    rw [r1_iota1 b₄ hc1, ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization.Away (algebraMap B1 B01 (ι1 (algebraMap O (T1 π b₄ t κ) ϖ)))
      (Bab b₄ ϖ ι01) := by
    rw [e]; infer_instance
  haveI := hloc1
  haveI := IsLocalization.Away.commutes (R := B1) (Bb b₄ ϖ ι1) B01 (Bab b₄ ϖ ι01)
    (ι1 (algebraMap O (T1 π b₄ t κ) ϖ)) (ι1 (h1 π b₄ t κ))
  have ha : algebraMap (AK π b₄ b₆ ϖ) (Bb b₄ ϖ ι1) (aK π b₄ b₆ t ϖ) =
      algebraMap B1 (Bb b₄ ϖ ι1) (ι1 (h1 π b₄ t κ)) * iotaB b₄ ϖ ι1 (wInv b₄ hκ hπ) := by
    change iotaB b₄ ϖ ι1 (f1K b₄ hκ hπ _) = _
    rw [f1K_aK, map_mul, hK, iotaB_algebraMap]
  rw [ha]
  exact IsLocalization.Away.of_associated
    (associated_mul_unit_right _ _ ((Units.isUnit _).map _))

include hloc0 in
/-- `Bab = Ba[1/x]`. -/
lemma isLocalization_Bab_a : letI := algA b₄ ϖ hκ ι0; letI := algAB b₄ hκ hπ hc1
    letI := (rhoAA b₄ hκ hπ hc0 hc1).toRingHom.toAlgebra
    IsLocalization.Away (algebraMap (AK π b₄ b₆ ϖ) (Ba b₄ ϖ ι0) (xK π b₄ b₆ ϖ))
      (Bab b₄ ϖ ι01) := by
  letI := algA b₄ ϖ hκ ι0
  letI : Algebra B0 B01 := r0.toAlgebra
  letI := algAB b₄ hκ hπ hc1
  letI : Algebra (Ba b₄ ϖ ι0) (Bab b₄ ϖ ι01) := (rhoAA b₄ hκ hπ hc0 hc1).toRingHom.toAlgebra
  haveI : IsScalarTower B0 (Ba b₄ ϖ ι0) (Bab b₄ ϖ ι01) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [IsScalarTower.algebraMap_apply B0 B01 (Bab b₄ ϖ ι01)]
      exact (rhoA_algebraMap b₄ hκ hπ hc0 a).symm
  have e : algebraMap B0 B01 (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)) =
      ι01 (algebraMap O (T01 π b₄ t κ) ϖ) * ι01 (rho0 π b₄ t κ (z0 π b₄ t κ)) := by
    change r0 _ = _
    rw [r0_iota0 b₄ hc0, map_mul, map_mul, AlgHom.commutes]
  have hu : IsUnit (algebraMap B01 (Bab b₄ ϖ ι01) (ι01 (rho0 π b₄ t κ (z0 π b₄ t κ)))) := by
    rw [← iotaAB_algebraMap, ← r0K_algebraMap b₄ hκ hπ]
    exact ((isUnit_zK π b₄ t κ ϖ).map (r0K b₄ hκ hπ)).map _
  haveI : IsLocalization.Away
      (algebraMap B0 B01 (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ))) (Bab b₄ ϖ ι01) := by
    rw [e]
    exact IsLocalization.Away.mul_of_isUnit _ _ hu
  haveI := hloc0
  haveI := IsLocalization.Away.commutes (R := B0) (Ba b₄ ϖ ι0) B01 (Bab b₄ ϖ ι01)
    (ι0 (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)) (ι0 (h0 π b₄ t κ))
  have hx : algebraMap (AK π b₄ b₆ ϖ) (Ba b₄ ϖ ι0) (xK π b₄ b₆ ϖ) =
      algebraMap B0 (Ba b₄ ϖ ι0) (ι0 (h0 π b₄ t κ)) * iotaA b₄ ϖ ι0 (zInv π b₄ t κ ϖ) := by
    change iotaA b₄ ϖ ι0 (f0K π b₄ ϖ hκ _) = _
    rw [f0K_algebraMap, f0_x, map_mul, hK0, iotaA_algebraMap]
  rw [hx]
  exact IsLocalization.Away.of_associated
    (associated_mul_unit_right _ _ ((Units.isUnit _).map _))

include hloc1 in
/-- **`Ba = gluedK[1/(y − t)]`**: the glued algebra restricts to `Ba` over `D(y − t)`. -/
theorem isLocalization_gluedK_fst : letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    letI := algAB b₄ hκ hπ hc1
    letI := ZariskiTwo.algebraFst (ρa := rhoAA b₄ hκ hπ hc0 hc1) (ρb := rhoBA b₄ hκ hπ hc1)
    IsLocalization.Away (algebraMap (AK π b₄ b₆ ϖ) (gluedK b₄ hκ hπ hc0 hc1)
      (aK π b₄ b₆ t ϖ)) (Ba b₄ ϖ ι0) :=
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  letI := algAB b₄ hκ hπ hc1
  ZariskiTwo.isLocalization_fst _ (isUnit_a b₄ hκ ι0) (isLocalization_Bab_b b₄ hκ hπ hc1 hloc1)

include hloc0 in
/-- **`Bb = gluedK[1/x]`**: the glued algebra restricts to `Bb` over `D(x)`. -/
theorem isLocalization_gluedK_snd : letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    letI := algAB b₄ hκ hπ hc1
    letI := ZariskiTwo.algebraSnd (ρa := rhoAA b₄ hκ hπ hc0 hc1) (ρb := rhoBA b₄ hκ hπ hc1)
    IsLocalization.Away (algebraMap (AK π b₄ b₆ ϖ) (gluedK b₄ hκ hπ hc0 hc1)
      (xK π b₄ b₆ ϖ)) (Bb b₄ ϖ ι1) :=
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  letI := algAB b₄ hκ hπ hc1
  ZariskiTwo.isLocalization_snd (isUnit_x b₄ hκ hπ ι1)
    (isLocalization_Bab_a b₄ hκ hπ hc0 hc1 hloc0)

variable (ι0) in
/-- `T0[1/(ϖ z)] → B₀[1/(ϖ z)]` is étale if `B₀[1/(ϖ z)]` is étale over `T0[1/ϖ]`. -/
lemma etale_iotaA
    (hBa : letI : Algebra (T0 π b₄ t κ) (Ba b₄ ϖ ι0) :=
        ((algebraMap B0 (Ba b₄ ϖ ι0)).comp ι0).toAlgebra
      ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (Ba b₄ ϖ ι0)]
        [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
          (Ba b₄ ϖ ι0) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (Ba b₄ ϖ ι0)) :
    (iotaA b₄ ϖ ι0).Etale := by
  have hu : IsUnit (algebraMap (T0 π b₄ t κ) (T0K π b₄ t κ ϖ) (algebraMap O _ ϖ)) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact isUnit_varpi_T0K π b₄ t κ ϖ
  let φ : Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ) →+* T0K π b₄ t κ ϖ :=
    IsLocalization.Away.lift _ hu
  letI : Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (T0K π b₄ t κ ϖ) :=
    φ.toAlgebra
  haveI : IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
      (T0K π b₄ t κ ϖ) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq _ hu a).symm
  haveI : Algebra.Etale (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) :=
    Algebra.Etale.of_isLocalizationAway (algebraMap O _ ϖ)
  haveI : Algebra.Etale (T0 π b₄ t κ) (T0K π b₄ t κ ϖ) :=
    Algebra.Etale.of_isLocalizationAway (algebraMap O _ ϖ * z0 π b₄ t κ)
  haveI : Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (T0K π b₄ t κ ϖ) :=
    Algebra.Etale.of_restrictScalars (T0 π b₄ t κ) _ _
  letI : Algebra (T0 π b₄ t κ) (Ba b₄ ϖ ι0) := ((algebraMap B0 (Ba b₄ ϖ ι0)).comp ι0).toAlgebra
  letI : Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (Ba b₄ ϖ ι0) :=
    ((iotaA b₄ ϖ ι0).comp φ).toAlgebra
  haveI : IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
      (Ba b₄ ϖ ι0) := IsScalarTower.of_algebraMap_eq fun a ↦ by
    change _ = iotaA b₄ ϖ ι0 (φ (algebraMap _ _ a))
    rw [IsLocalization.Away.lift_eq, iotaA_algebraMap]
    rfl
  haveI := hBa
  letI : Algebra (T0K π b₄ t κ ϖ) (Ba b₄ ϖ ι0) := (iotaA b₄ ϖ ι0).toAlgebra
  haveI : IsScalarTower (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (T0K π b₄ t κ ϖ)
      (Ba b₄ ϖ ι0) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Algebra.Etale (T0K π b₄ t κ ϖ) (Ba b₄ ϖ ι0) :=
    Algebra.Etale.of_restrictScalars (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) _ _
  exact RingHom.etale_algebraMap.2 this

variable (ι1) in
/-- `T1[1/ϖ] → B₁[1/ϖ]` is étale if `B₁[1/ϖ]` is étale over `T1[1/ϖ]`. -/
lemma etale_iotaB
    (hBb : letI : Algebra (T1 π b₄ t κ) (Bb b₄ ϖ ι1) :=
        ((algebraMap B1 (Bb b₄ ϖ ι1)).comp ι1).toAlgebra
      ∀ [Algebra (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1)]
        [@IsScalarTower (T1 π b₄ t κ) (T1K π b₄ t κ ϖ)
          (Bb b₄ ϖ ι1) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1)) :
    (iotaB b₄ ϖ ι1).Etale := by
  letI : Algebra (T1 π b₄ t κ) (Bb b₄ ϖ ι1) := ((algebraMap B1 (Bb b₄ ϖ ι1)).comp ι1).toAlgebra
  letI : Algebra (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1) := (iotaB b₄ ϖ ι1).toAlgebra
  haveI : IsScalarTower (T1 π b₄ t κ) (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change _ = iotaB b₄ ϖ ι1 (algebraMap _ _ a)
      rw [iotaB_algebraMap]
      rfl
  haveI := hBb
  exact RingHom.etale_algebraMap.2 this

include hloc0 hloc1 in
/-- **T1a: the generic fibre of the covering over `E ∖ {0}` is étale**, given that `Ba` is
étale over `T0[1/ϖ]` and `Bb` over `T1[1/ϖ]`. -/
theorem etale_gluedK
    (hBa : letI : Algebra (T0 π b₄ t κ) (Ba b₄ ϖ ι0) :=
        ((algebraMap B0 (Ba b₄ ϖ ι0)).comp ι0).toAlgebra
      ∀ [Algebra (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (Ba b₄ ϖ ι0)]
        [@IsScalarTower (T0 π b₄ t κ) (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ))
          (Ba b₄ ϖ ι0) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (Localization.Away (algebraMap O (T0 π b₄ t κ) ϖ)) (Ba b₄ ϖ ι0))
    (hBb : letI : Algebra (T1 π b₄ t κ) (Bb b₄ ϖ ι1) :=
        ((algebraMap B1 (Bb b₄ ϖ ι1)).comp ι1).toAlgebra
      ∀ [Algebra (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1)]
        [@IsScalarTower (T1 π b₄ t κ) (T1K π b₄ t κ ϖ)
          (Bb b₄ ϖ ι1) Algebra.toSMul Algebra.toSMul Algebra.toSMul],
        Algebra.Etale (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1)) :
    letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    Algebra.Etale (AK π b₄ b₆ ϖ) (gluedK b₄ hκ hπ hc0 hc1) := by
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  letI := algAB b₄ hκ hπ hc1
  have h0 : (f0K π b₄ ϖ hκ : AK π b₄ b₆ ϖ →+* T0K π b₄ t κ ϖ).Etale := by
    letI := algT0K π b₄ ϖ hκ
    haveI := isLocalization_T0K π b₄ ϖ hκ
    exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway (aK π b₄ b₆ t ϖ))
  have h1 : (f1K b₄ hκ hπ : AK π b₄ b₆ ϖ →+* T1K π b₄ t κ ϖ).Etale := by
    letI := algT1K b₄ hκ hπ
    haveI := isLocalization_T1K b₄ hκ hπ
    exact RingHom.etale_algebraMap.2 (Algebra.Etale.of_isLocalizationAway (xK π b₄ b₆ ϖ))
  exact ZariskiTwo.etale_glued (span_a_x hκ) (isUnit_a b₄ hκ ι0)
    (isLocalization_Bab_b b₄ hκ hπ hc1 hloc1) (isUnit_x b₄ hκ hπ ι1)
    (isLocalization_Bab_a b₄ hκ hπ hc0 hc1 hloc0)
    (RingHom.Etale.stableUnderComposition _ _ h0 (etale_iotaA b₄ ι0 hBa))
    (RingHom.Etale.stableUnderComposition _ _ h1 (etale_iotaB b₄ ι1 hBb))

include hloc0 hloc1 in
/-- **T1a: the generic fibre of the covering over `E ∖ {0}` is finite** if `B₀`, `B₁` are finite
over `T0`, `T1`. -/
theorem finite_gluedK (hf0 : ι0.Finite) (hf1 : ι1.Finite) :
    letI := algA b₄ ϖ hκ ι0; letI := algB b₄ hκ hπ ι1
    Module.Finite (AK π b₄ b₆ ϖ) (gluedK b₄ hκ hπ hc0 hc1) := by
  letI := algA b₄ ϖ hκ ι0
  letI := algB b₄ hκ hπ ι1
  letI := algAB b₄ hκ hπ hc1
  letI := algT0K π b₄ ϖ hκ
  letI := algT1K b₄ hκ hπ
  haveI := isLocalization_T0K π b₄ ϖ hκ
  haveI := isLocalization_T1K b₄ hκ hπ
  letI : Algebra (T0K π b₄ t κ ϖ) (Ba b₄ ϖ ι0) := (iotaA b₄ ϖ ι0).toAlgebra
  letI : Algebra (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1) := (iotaB b₄ ϖ ι1).toAlgebra
  haveI : IsScalarTower (AK π b₄ b₆ ϖ) (T0K π b₄ t κ ϖ) (Ba b₄ ϖ ι0) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower (AK π b₄ b₆ ϖ) (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : Module.Finite (T0K π b₄ t κ ϖ) (Ba b₄ ϖ ι0) := RingHom.finite_algebraMap.1
    (RingHom.finite_localizationPreserves ι0
      (Submonoid.powers (algebraMap O (T0 π b₄ t κ) ϖ * z0 π b₄ t κ)) _ _ hf0)
  haveI : Module.Finite (T1K π b₄ t κ ϖ) (Bb b₄ ϖ ι1) := RingHom.finite_algebraMap.1
    (RingHom.finite_localizationPreserves ι1
      (Submonoid.powers (algebraMap O (T1 π b₄ t κ) ϖ)) _ _ hf1)
  exact ZariskiTwo.finite_glued' (span_a_x hκ) (isUnit_a b₄ hκ ι0)
    (isLocalization_Bab_b b₄ hκ hπ hc1 hloc1) (isUnit_x b₄ hκ hπ ι1)
    (isLocalization_Bab_a b₄ hκ hπ hc0 hc1 hloc0) (T0K π b₄ t κ ϖ) (T1K π b₄ t κ ϖ)

end Theorems

end

end TateAffine

end SemistableReduction
