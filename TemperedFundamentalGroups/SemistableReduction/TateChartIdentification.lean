/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartRingsOfAffine
import TemperedFundamentalGroups.SemistableReduction.TwoChartTower
import TemperedFundamentalGroups.SemistableReduction.TateChartSections
import TemperedFundamentalGroups.SemistableReduction.LinearProjectionSections

/-!
# The two-chart rings of the Tate model over `ℙ¹` (Blueprint §12.8, M2.3 (g))

**`TateChartIdentification.twoChartMap`**: a morphism of two-chart rings (`TwoChartMap`) from the
algebraic description `TateTwoChart.twoChart` (`T0 = O[h][z]/(G₀)`, `T1 = O[h'][w]/(G₁)`,
`T01 = T1[1/h']`) to the two-chart rings `ProjectiveLine.twoChartRingsOfAffine (toP1 ..)` of the
projection `TateProjection.toP1 : 𝒯 ⟶ ℙ¹_O` (sections of the Tate model over the preimages of
the charts of `ℙ¹_O` and of their overlap). If `T0`, `T1` are reduced, all three components are
bijective (**`TateChartIdentification.bijective_f0/f1/f01`**), i.e. `TateTwoChart.twoChart` *is*
the two-chart description of the scheme `TateModel.model` over `ℙ¹_O`.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace TemperedFundamentalGroups

namespace TateChartIdentification

open SemistableReduction SemistableReduction.LinearProjection SemistableReduction.TateTwoChart
  TateProjection TateChartSections

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] (π b₄ t κ : O) {b₆ : O} (hκ : κ * (t ^ 2 - b₆) = 1)

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

/-- The projection `𝒯 ⟶ ℙ¹_O` from `[0 : t : 1]`. -/
abbrev P : (TateModel.modelIdeal π b₄ b₆).subscheme ⟶ ProjectiveLine.scheme O :=
  toP1 π b₄ b₆ (isUnit_ε t κ hκ)

instance isAffineHom_P : IsAffineHom (P π b₄ t κ hκ) :=
  (isFinite_toP1 π b₄ (isUnit_ε t κ hκ)).toIsAffineHom

/-- The two-chart rings of the scheme: sections over the preimages of the charts of `ℙ¹_O`. -/
abbrev D : ProjectiveLine.TwoChartRings O :=
  ProjectiveLine.twoChartRingsOfAffine (P π b₄ t κ hκ)

/-- `T0 → Γ(𝒯, p⁻¹ U₀)`. -/
def F0 : T0 π b₄ t κ →+* (D π b₄ t κ hκ).R0 :=
  (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 0).toRingHom.comp (f0 π b₄ t κ hκ)

/-- `T1 → Γ(𝒯, p⁻¹ U₁)`. -/
def F1 : T1 π b₄ t κ →+* (D π b₄ t κ hκ).R1 :=
  (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 1).toRingHom.comp (f1 π b₄ t κ hκ)

lemma F0_of (q : Polynomial O) :
    F0 π b₄ t κ hκ (AdjoinRoot.of _ q) = ProjectiveLine.chartPullback (P π b₄ t κ hκ) 0 q := by
  exact (congrArg (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 0) (f0_of π b₄ t κ hκ q)).trans
    (sectionsEquiv_baseRes (hcov π b₄ (isUnit_ε t κ hκ)) 0 (ProjectiveLine.polyToChart 0 q))

lemma F1_of (q : Polynomial O) :
    F1 π b₄ t κ hκ (AdjoinRoot.of _ q) = ProjectiveLine.chartPullback (P π b₄ t κ hκ) 1 q := by
  exact (congrArg (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 1) (f1_of π b₄ t κ hκ q)).trans
    (sectionsEquiv_baseRes (hcov π b₄ (isUnit_ε t κ hκ)) 1 (ProjectiveLine.polyToChart 1 q))

lemma F0_algebraMap (o : O) :
    F0 π b₄ t κ hκ (algebraMap O _ o) = algebraMap O (D π b₄ t κ hκ).R0 o := by
  rw [← of_C, F0_of]
  rfl

lemma F1_algebraMap (o : O) :
    F1 π b₄ t κ hκ (algebraMap O _ o) = algebraMap O (D π b₄ t κ hκ).R1 o := by
  rw [← of_C, F1_of]
  rfl

lemma F0_h0 : F0 π b₄ t κ hκ (h0 π b₄ t κ) = (D π b₄ t κ hκ).x :=
  F0_of π b₄ t κ hκ Polynomial.X

lemma F1_h1 : F1 π b₄ t κ hκ (h1 π b₄ t κ) = (D π b₄ t κ hκ).y :=
  F1_of π b₄ t κ hκ Polynomial.X

/-- `T0 → Γ(𝒯, p⁻¹ U₀)` as an `O`-algebra map. -/
def A0 : T0 π b₄ t κ →ₐ[O] (D π b₄ t κ hκ).R0 :=
  { F0 π b₄ t κ hκ with commutes' := F0_algebraMap π b₄ t κ hκ }

/-- `T1 → Γ(𝒯, p⁻¹ U₁)` as an `O`-algebra map. -/
def A1 : T1 π b₄ t κ →ₐ[O] (D π b₄ t κ hκ).R1 :=
  { F1 π b₄ t κ hκ with commutes' := F1_algebraMap π b₄ t κ hκ }

lemma isUnit_F1_h1 :
    IsUnit ((D π b₄ t κ hκ).ρ1 (F1 π b₄ t κ hκ (h1 π b₄ t κ))) := by
  rw [F1_h1, (D π b₄ t κ hκ).ρ1_y]
  exact Units.isUnit _

/-- The overlap `T01 = T1[1/h'] → Γ(𝒯, p⁻¹ (U₀ ∩ U₁))`. -/
def F01 : T01 π b₄ t κ →+* (D π b₄ t κ hκ).R01 :=
  IsLocalization.Away.lift (h1 π b₄ t κ)
    (g := (D π b₄ t κ hκ).ρ1.toRingHom.comp (F1 π b₄ t κ hκ)) (isUnit_F1_h1 π b₄ t κ hκ)

lemma F01_algebraMap (a : T1 π b₄ t κ) :
    F01 π b₄ t κ hκ (algebraMap _ _ a) = (D π b₄ t κ hκ).ρ1 (F1 π b₄ t κ hκ a) :=
  IsLocalization.Away.lift_eq _ _ a

/-- `T01 → Γ(𝒯, p⁻¹ (U₀ ∩ U₁))` as an `O`-algebra map. -/
def A01 : T01 π b₄ t κ →ₐ[O] (D π b₄ t κ hκ).R01 :=
  { F01 π b₄ t κ hκ with
    commutes' := fun o ↦ by
      change F01 π b₄ t κ hκ (algebraMap O (T01 π b₄ t κ) o) = _
      rw [IsScalarTower.algebraMap_apply O (T1 π b₄ t κ) (T01 π b₄ t κ), F01_algebraMap,
        F1_algebraMap]
      exact (D π b₄ t κ hκ).ρ1.commutes o }

lemma A01_hinv :
    A01 π b₄ t κ hκ (hinv π b₄ t κ) = ((D π b₄ t κ hκ).u : (D π b₄ t κ hκ).R01) := by
  refine eq_of_mul_eq_one (a := (D π b₄ t κ hκ).ρ1 (F1 π b₄ t κ hκ (h1 π b₄ t κ))) ?_ ?_
  · change _ * F01 π b₄ t κ hκ (hinv π b₄ t κ) = 1
    rw [← F01_algebraMap, ← map_mul, h1_mul_hinv, map_one]
  · rw [F1_h1, (D π b₄ t κ hκ).ρ1_y, Units.inv_mul]

/-! ### The overlap identity `w/ℓ₀ = (w/u) (u/ℓ₀)` -/

/-- `ℓ₀ ℓ₁`. -/
abbrev x01 : MvPolynomial (Fin (2 + 1)) O := linHom (lin t) (lin_mem t) (X 0 * X 1)

lemma hx0 : x01 t = linHom (lin t) (lin_mem t) (X 0) * linHom (lin t) (lin_mem t) (X 1) :=
  map_mul _ _ _

lemma hx1 : x01 t = linHom (lin t) (lin_mem t) (X 1) * linHom (lin t) (lin_mem t) (X 0) := by
  rw [x01, map_mul, mul_comm]

lemma W_le : P π b₄ t κ hκ ⁻¹ᵁ (ProjectiveLine.U O 0 ⊓ ProjectiveLine.U O 1) ≤
    TateModel.ι π b₄ b₆ ⁻¹ᵁ Proj.basicOpen (𝒜 2) (x01 t) := by
  intro z hz
  have h0 : z ∈ V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 := by
    rw [← preimage_proj_U (hcov π b₄ (isUnit_ε t κ hκ)) 0]
    exact hz.1
  have h1 : z ∈ V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 := by
    rw [← preimage_proj_U (hcov π b₄ (isUnit_ε t κ hκ)) 1]
    exact hz.2
  change TateModel.ι π b₄ b₆ z ∈ Proj.basicOpen _ (linHom (lin t) (lin_mem t) (X 0 * X 1))
  rw [map_mul, Proj.basicOpen_mul]
  exact ⟨h0, h1⟩

/-- Sections over `ι⁻¹ D₊(ℓ₀ ℓ₁)`, restricted to `p⁻¹ (U₀ ∩ U₁)`. -/
def Ψ : Away (𝒜 2) (x01 t) →+* (D π b₄ t κ hκ).R01 :=
  ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map
    (homOfLE (W_le π b₄ t κ hκ)).op).hom.comp
    (((TateModel.ι π b₄ b₆).app (Proj.basicOpen (𝒜 2) (x01 t))).hom.comp
      (Proj.awayToSection (𝒜 2) (x01 t)).hom)

lemma ρ0_sec (a : Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 0))) :
    (D π b₄ t κ hκ).ρ0 (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 0
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a)) =
      Ψ π b₄ t κ hκ
        (awayMap (𝒜 2) ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 1)) (hx0 t) a) := by
  have hB : TateModel.ι π b₄ b₆ ⁻¹ᵁ Proj.basicOpen (𝒜 2) (x01 t) ≤
      V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 :=
    (TateModel.ι π b₄ b₆).preimage_mono (D_mul_le_left (lin t) (lin_mem t) 0 1)
  have h := sectionsEquiv_secRes (hcov π b₄ (isUnit_ε t κ hκ)) 0 a
  have h2 := res_secZ (ι := TateModel.ι π b₄ b₆) 0
    ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 1)) (hx0 t) hB a
  calc (D π b₄ t κ hκ).ρ0 (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 0
        (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a))
      = (D π b₄ t κ hκ).ρ0 ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map
          (homOfLE (preimage_proj_U (hcov π b₄ (isUnit_ε t κ hκ)) 0).le).op
          (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a)) := congrArg _ h
    _ = (TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map (homOfLE (W_le π b₄ t κ hκ)).op
          ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map (homOfLE hB).op
            (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a)) := by
      change ProjectiveLine.preimageRes _ 0 _ = _
      have e1 := ConcreteCategory.congr_hom
        ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map_comp
          (homOfLE (preimage_proj_U (hcov π b₄ (isUnit_ε t κ hκ)) 0).le).op
          (homOfLE (ProjectiveLine.preimage_inf_le (P π b₄ t κ hκ) 0)).op)
        (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a)
      have e2 := ConcreteCategory.congr_hom
        ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map_comp (homOfLE hB).op
          (homOfLE (W_le π b₄ t κ hκ)).op)
        (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a)
      exact e1.symm.trans ((congrArg (fun f ↦
        (TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map f
          (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a)) (Subsingleton.elim _ _)).trans e2)
    _ = _ := congrArg _ h2

lemma ρ1_sec (a : Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 1))) :
    (D π b₄ t κ hκ).ρ1 (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 1
      (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a)) =
      Ψ π b₄ t κ hκ
        (awayMap (𝒜 2) ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 0)) (hx1 t) a) := by
  have hB : TateModel.ι π b₄ b₆ ⁻¹ᵁ Proj.basicOpen (𝒜 2) (x01 t) ≤
      V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 :=
    (TateModel.ι π b₄ b₆).preimage_mono (D_mul_le_right (lin t) (lin_mem t) 0 1)
  have h := sectionsEquiv_secRes (hcov π b₄ (isUnit_ε t κ hκ)) 1 a
  have h2 := res_secZ (ι := TateModel.ι π b₄ b₆) 1
    ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 0)) (hx1 t) hB a
  calc (D π b₄ t κ hκ).ρ1 (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 1
        (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a))
      = (D π b₄ t κ hκ).ρ1 ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map
          (homOfLE (preimage_proj_U (hcov π b₄ (isUnit_ε t κ hκ)) 1).le).op
          (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a)) := congrArg _ h
    _ = (TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map (homOfLE (W_le π b₄ t κ hκ)).op
          ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map (homOfLE hB).op
            (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a)) := by
      change ProjectiveLine.preimageRes _ 1 _ = _
      have e1 := ConcreteCategory.congr_hom
        ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map_comp
          (homOfLE (preimage_proj_U (hcov π b₄ (isUnit_ε t κ hκ)) 1).le).op
          (homOfLE (ProjectiveLine.preimage_inf_le (P π b₄ t κ hκ) 1)).op)
        (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a)
      have e2 := ConcreteCategory.congr_hom
        ((TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map_comp (homOfLE hB).op
          (homOfLE (W_le π b₄ t κ hκ)).op)
        (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a)
      exact e1.symm.trans ((congrArg (fun f ↦
        (TateModel.modelIdeal π b₄ b₆).subscheme.presheaf.map f
          (secZ (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a)) (Subsingleton.elim _ _)).trans e2)
    _ = _ := congrArg _ h2

/-- `w/ℓ₀ = (w/u) · (u/ℓ₀)` in `(O[u,v,w]_{(ℓ₀ u)})₀`. -/
lemma awayMap_identity :
    awayMap (𝒜 2) ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 1)) (hx0 t)
        (coordFrac (lin t) (lin_mem t) 0 2) =
      awayMap (𝒜 2) ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 0)) (hx1 t)
        (coordFrac (lin t) (lin_mem t) 1 2) *
      awayMap (𝒜 2) ((linHom (lin t) (lin_mem t)).map_mem (X_mem' 1)) (hx0 t)
        (coordFrac (lin t) (lin_mem t) 0 0) := by
  simp only [coordFrac, awayMap_mk]
  apply val_injective
  simp only [val_mul, Away.val_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [x01, map_mul, linHom_X, lin_zero, lin_one, Submonoid.coe_mul, OneMemClass.coe_one,
    one_mul]
  simp [lin_zero, lin_one]
  ring

lemma F0_sec (x : T0 π b₄ t κ) : F0 π b₄ t κ hκ x =
    sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 0 (f0 π b₄ t κ hκ x) := rfl

lemma F1_sec (x : T1 π b₄ t κ) : F1 π b₄ t κ hκ x =
    sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 1 (f1 π b₄ t κ hκ x) := rfl

/-- **The overlap compatibility** `ρ₀ ∘ F₀ = F₀₁ ∘ rho0`. -/
lemma h0_comm (a : T0 π b₄ t κ) :
    A01 π b₄ t κ hκ (rho0 π b₄ t κ a) = (D π b₄ t κ hκ).ρ0 (A0 π b₄ t κ hκ a) := by
  have key : (A01 π b₄ t κ hκ).toRingHom.comp (rho0 π b₄ t κ).toRingHom =
      (D π b₄ t κ hκ).ρ0.toRingHom.comp (F0 π b₄ t κ hκ) := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro o
        change A01 π b₄ t κ hκ (rho0 π b₄ t κ (AdjoinRoot.of _ (Polynomial.C o))) =
          (D π b₄ t κ hκ).ρ0 (F0 π b₄ t κ hκ (AdjoinRoot.of _ (Polynomial.C o)))
        rw [of_C, AlgHom.commutes, AlgHom.commutes, F0_algebraMap, AlgHom.commutes]
      · change A01 π b₄ t κ hκ (rho0 π b₄ t κ (h0 π b₄ t κ)) =
          (D π b₄ t κ hκ).ρ0 (F0 π b₄ t κ hκ (h0 π b₄ t κ))
        rw [rho0_h0, A01_hinv, F0_h0, (D π b₄ t κ hκ).ρ0_x]
    · change A01 π b₄ t κ hκ (rho0 π b₄ t κ (z0 π b₄ t κ)) =
        (D π b₄ t κ hκ).ρ0 (F0 π b₄ t κ hκ (z0 π b₄ t κ))
      have hu : ((D π b₄ t κ hκ).u : (D π b₄ t κ hκ).R01) =
          (D π b₄ t κ hκ).ρ0 (F0 π b₄ t κ hκ (h0 π b₄ t κ)) := by
        rw [F0_h0, (D π b₄ t κ hκ).ρ0_x]
      rw [rho0_z0, map_mul, A01_hinv, hu]
      change F01 π b₄ t κ hκ (algebraMap _ _ (w1 π b₄ t κ)) * _ = _
      rw [F01_algebraMap, F1_sec, f1_w1, F0_sec, F0_sec, f0_h0, f0_z0, ρ0_sec, ρ0_sec, ρ1_sec,
        ← map_mul, awayMap_identity]
  exact RingHom.congr_fun key a

/-- **The algebraic charts of the Tate model map to its sections over `ℙ¹_O`**: a morphism of
two-chart rings `TateTwoChart.twoChart → twoChartRingsOfAffine (toP1 ..)` (`h ↦ u/ℓ₀`,
`z ↦ w/ℓ₀`, `h' ↦ ℓ₀/u`, `w ↦ w/u`). -/
def twoChartMap : TwoChartMap (twoChart π b₄ t κ) (D π b₄ t κ hκ) where
  f0 := A0 π b₄ t κ hκ
  f1 := A1 π b₄ t κ hκ
  f01 := A01 π b₄ t κ hκ
  hx := F0_h0 π b₄ t κ hκ
  hy := F1_h1 π b₄ t κ hκ
  hu := A01_hinv π b₄ t κ hκ
  h0 := h0_comm π b₄ t κ hκ
  h1 := F01_algebraMap π b₄ t κ hκ

lemma bijective_f0 [IsReduced (T0 π b₄ t κ)] :
    Function.Bijective (twoChartMap π b₄ t κ hκ).f0 :=
  ((equiv0 π b₄ t κ hκ).trans (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 0)).bijective

lemma bijective_f1 [IsReduced (T1 π b₄ t κ)] :
    Function.Bijective (twoChartMap π b₄ t κ hκ).f1 :=
  ((equiv1 π b₄ t κ hκ).trans (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 1)).bijective

lemma bijective_f01 [IsReduced (T1 π b₄ t κ)] :
    Function.Bijective (twoChartMap π b₄ t κ hκ).f01 := by
  letI : Algebra (D π b₄ t κ hκ).R1 (D π b₄ t κ hκ).R01 :=
    (ProjectiveLine.preimageRes (P π b₄ t κ hκ) 1).toAlgebra
  haveI : IsLocalization.Away (D π b₄ t κ hκ).y (D π b₄ t κ hκ).R01 :=
    ProjectiveLine.isLocalization_preimageRes (P π b₄ t κ hκ) 1
  let E1 : T1 π b₄ t κ ≃+* (D π b₄ t κ hκ).R1 :=
    (equiv1 π b₄ t κ hκ).trans (sectionsEquiv (hcov π b₄ (isUnit_ε t κ hκ)) 1)
  have hE : (Submonoid.powers (h1 π b₄ t κ)).map E1.toMonoidHom =
      Submonoid.powers (D π b₄ t κ hκ).y := by
    rw [Submonoid.map_powers]
    exact congrArg _ (F1_h1 π b₄ t κ hκ)
  let e := IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (h1 π b₄ t κ))
    (S := T01 π b₄ t κ) (Q := (D π b₄ t κ hκ).R01) E1 hE
  have he : F01 π b₄ t κ hκ = e.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (h1 π b₄ t κ)) (RingHom.ext fun a ↦ ?_)
    rw [RingHom.comp_apply, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, IsLocalization.ringEquivOfRingEquiv_eq]
    exact F01_algebraMap π b₄ t κ hκ a
  have hf : ⇑(twoChartMap π b₄ t κ hκ).f01 = ⇑e := funext fun x ↦ RingHom.congr_fun he x
  rw [hf]
  exact e.bijective

end

end TateChartIdentification

end TemperedFundamentalGroups
