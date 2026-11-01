/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TwoChartNormalisation

/-!
# Functoriality of the normalisation of two-chart rings in a field (MR12, interface I1 of MR13)

Let `D` be two-chart rings over `A` and `L`, `L'` fields receiving `D` compatibly, with
normalisations `P_L = (B₀, B₁)` and `P_L' = (B₀', B₁')` (`TwoChartNorm.twoChart`). A ring map
`f : L → L'` compatible with the maps from the overlap `D.R01` (hence from `D.R0`, `D.R1`)
induces a morphism of two-chart rings `P_L → P_L'` (**`TwoChartNorm.normMap`**): on the charts
`b ↦ f b` (integral closure is functorial), on the overlap `z ↦ f z`. It is compatible with the
generic fibres (**`normMap_f0_algebraMap`**, **`normMap_f1_algebraMap`**, **`normMap_f01_val`**),
with the structure maps from `D` (**`normMap_comp_toNorm`**), with identities and composition
(**`normMap_id`**, **`normMap_comp`**), hence a morphism of chart algebras
(`TwoChartMap.isHom`).

Also: `TwoChartMap.id`, `TwoChartMap.comp`, `TwoChartMap.ext`, `toHom_id`, `toHom_comp`, and the
endomorphism monoid `TwoChartMap D D`.
-/

universe u

open Polynomial

namespace SemistableReduction

open ProjectiveLine ProjectiveLine.ChartModule

namespace TwoChartMap

variable {A : Type u} [CommRing A]

/-- **Extensionality of morphisms of two-chart rings.** -/
lemma ext {D D' : TwoChartRings A} {φ ψ : TwoChartMap D D'} (h0 : φ.f0 = ψ.f0)
    (h1 : φ.f1 = ψ.f1) (h01 : φ.f01 = ψ.f01) : φ = ψ := by
  cases φ
  cases ψ
  cases h0
  cases h1
  cases h01
  rfl

/-- **Morphisms of two-chart rings are determined by their chart components** (the overlap
component is determined by the first chart, `ChartModule.Hom.f01_eq_of_f0_eq`). -/
lemma ext_of_f0_f1 {D D' : TwoChartRings A} {φ ψ : TwoChartMap D D'} (h0 : φ.f0 = ψ.f0)
    (h1 : φ.f1 = ψ.f1) : φ = ψ := by
  have h01 : φ.toHom.f01 = ψ.toHom.f01 :=
    ChartModule.Hom.f01_eq_of_f0_eq (φ := φ.toHom) (ψ := ψ.toHom)
      (LinearMap.ext fun a ↦ by change φ.f0 a = ψ.f0 a; rw [h0])
  exact ext h0 h1 (AlgHom.ext fun z ↦ LinearMap.congr_fun h01 z)

/-- The identity morphism of two-chart rings. -/
def id (D : TwoChartRings A) : TwoChartMap D D where
  f0 := AlgHom.id A D.R0
  f1 := AlgHom.id A D.R1
  f01 := AlgHom.id A D.R01
  hx := rfl
  hy := rfl
  hu := rfl
  h0 _ := rfl
  h1 _ := rfl

/-- Composition of morphisms of two-chart rings. -/
def comp {D D' D'' : TwoChartRings A} (ψ : TwoChartMap D' D'') (φ : TwoChartMap D D') :
    TwoChartMap D D'' where
  f0 := ψ.f0.comp φ.f0
  f1 := ψ.f1.comp φ.f1
  f01 := ψ.f01.comp φ.f01
  hx := by rw [AlgHom.comp_apply, φ.hx, ψ.hx]
  hy := by rw [AlgHom.comp_apply, φ.hy, ψ.hy]
  hu := by rw [AlgHom.comp_apply, φ.hu, ψ.hu]
  h0 a := by rw [AlgHom.comp_apply, φ.h0, ψ.h0]; rfl
  h1 a := by rw [AlgHom.comp_apply, φ.h1, ψ.h1]; rfl

@[simp] lemma id_f0 (D : TwoChartRings A) (a : D.R0) : (id D).f0 a = a := rfl
@[simp] lemma id_f1 (D : TwoChartRings A) (a : D.R1) : (id D).f1 a = a := rfl
@[simp] lemma id_f01 (D : TwoChartRings A) (a : D.R01) : (id D).f01 a = a := rfl

section

variable {D D' D'' : TwoChartRings A} (ψ : TwoChartMap D' D'') (φ : TwoChartMap D D')

@[simp] lemma comp_f0 (a : D.R0) : (ψ.comp φ).f0 a = ψ.f0 (φ.f0 a) := rfl
@[simp] lemma comp_f1 (a : D.R1) : (ψ.comp φ).f1 a = ψ.f1 (φ.f1 a) := rfl
@[simp] lemma comp_f01 (a : D.R01) : (ψ.comp φ).f01 a = ψ.f01 (φ.f01 a) := rfl

lemma comp_id : φ.comp (id D) = φ := ext rfl rfl rfl

lemma id_comp : (id D').comp φ = φ := ext rfl rfl rfl

lemma comp_assoc {D''' : TwoChartRings A} (χ : TwoChartMap D'' D''') :
    (χ.comp ψ).comp φ = χ.comp (ψ.comp φ) := ext rfl rfl rfl

/-- `toHom` of the identity. -/
lemma toHom_id : (id D).toHom = ChartModule.Hom.id D.chartModule := Hom.ext' rfl rfl rfl

/-- `toHom` of a composition. -/
lemma toHom_comp : (ψ.comp φ).toHom = ψ.toHom.comp φ.toHom := Hom.ext' rfl rfl rfl

end

/-- The endomorphisms of two-chart rings form a monoid under composition. -/
instance (D : TwoChartRings A) : Monoid (TwoChartMap D D) where
  mul ψ φ := ψ.comp φ
  one := id D
  mul_assoc χ ψ φ := comp_assoc ψ φ χ
  one_mul φ := id_comp φ
  mul_one φ := comp_id φ

lemma mul_def {D : TwoChartRings A} (ψ φ : TwoChartMap D D) : ψ * φ = ψ.comp φ := rfl

lemma one_def (D : TwoChartRings A) : (1 : TwoChartMap D D) = id D := rfl

end TwoChartMap

namespace TwoChartNorm

noncomputable section

variable {A : Type u} [CommRing A] {D : TwoChartRings A}

section Map

variable {L L' : Type u} [Field L] [Field L'] [Algebra D.R01 L] [Algebra D.R01 L']
  [Algebra D.R0 L] [Algebra D.R1 L] [Algebra D.R0 L'] [Algebra D.R1 L']
  (h0L : ∀ a, algebraMap D.R01 L (D.ρ0 a) = algebraMap D.R0 L a)
  (h1L : ∀ a, algebraMap D.R01 L (D.ρ1 a) = algebraMap D.R1 L a)
  (h0L' : ∀ a, algebraMap D.R01 L' (D.ρ0 a) = algebraMap D.R0 L' a)
  (h1L' : ∀ a, algebraMap D.R01 L' (D.ρ1 a) = algebraMap D.R1 L' a)
  (f : L →+* L') (hf : ∀ a, f (algebraMap D.R01 L a) = algebraMap D.R01 L' a)

omit [Algebra D.R1 L] [Algebra D.R1 L'] in
include h0L h0L' hf in
lemma hf0 (a : D.R0) : f (algebraMap D.R0 L a) = algebraMap D.R0 L' a := by
  rw [← h0L, hf, h0L']

omit [Algebra D.R0 L] [Algebra D.R0 L'] in
include h1L h1L' hf in
lemma hf1 (a : D.R1) : f (algebraMap D.R1 L a) = algebraMap D.R1 L' a := by
  rw [← h1L, hf, h1L']

variable (B₀ B₁ B₀' B₁' : Type u) [CommRing B₀] [CommRing B₁] [CommRing B₀'] [CommRing B₁']
  [Algebra D.R0 B₀] [Algebra B₀ L] [IsScalarTower D.R0 B₀ L] [IsIntegralClosure B₀ D.R0 L]
  [Algebra D.R1 B₁] [Algebra B₁ L] [IsScalarTower D.R1 B₁ L] [IsIntegralClosure B₁ D.R1 L]
  [Algebra D.R0 B₀'] [Algebra B₀' L'] [IsScalarTower D.R0 B₀' L'] [IsIntegralClosure B₀' D.R0 L']
  [Algebra D.R1 B₁'] [Algebra B₁' L'] [IsScalarTower D.R1 B₁' L'] [IsIntegralClosure B₁' D.R1 L']

omit [Algebra D.R1 L] [Algebra D.R1 L'] [Algebra D.R0 B₀] [IsScalarTower D.R0 B₀ L]
  [IsScalarTower D.R0 B₀' L'] [IsIntegralClosure B₀' D.R0 L'] in
include h0L h0L' hf in
lemma isIntegral_f0 (b : B₀) : IsIntegral D.R0 (f (algebraMap B₀ L b)) :=
  IsIntegral.map_of_comp_eq (RingHom.id D.R0) f
    (RingHom.ext fun a ↦ (hf0 h0L h0L' f hf a).symm)
    ((IsIntegralClosure.isIntegral_iff (A := B₀)).2 ⟨b, rfl⟩)

omit [Algebra D.R0 L] [Algebra D.R0 L'] [Algebra D.R1 B₁] [IsScalarTower D.R1 B₁ L]
  [IsScalarTower D.R1 B₁' L'] [IsIntegralClosure B₁' D.R1 L'] in
include h1L h1L' hf in
lemma isIntegral_f1 (b : B₁) : IsIntegral D.R1 (f (algebraMap B₁ L b)) :=
  IsIntegral.map_of_comp_eq (RingHom.id D.R1) f
    (RingHom.ext fun a ↦ (hf1 h1L h1L' f hf a).symm)
    ((IsIntegralClosure.isIntegral_iff (A := B₁)).2 ⟨b, rfl⟩)

/-- The map `B₀ → B₀'` of normalisations induced by `f`. -/
def map0 : B₀ →+* B₀' where
  toFun b := IsIntegralClosure.mk' B₀' (f (algebraMap B₀ L b)) (isIntegral_f0 h0L h0L' f hf B₀ b)
  map_one' := IsIntegralClosure.algebraMap_injective B₀' D.R0 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_one, map_one, map_one])
  map_mul' x y := IsIntegralClosure.algebraMap_injective B₀' D.R0 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_mul, map_mul, map_mul,
      IsIntegralClosure.algebraMap_mk', IsIntegralClosure.algebraMap_mk'])
  map_zero' := IsIntegralClosure.algebraMap_injective B₀' D.R0 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_zero, map_zero, map_zero])
  map_add' x y := IsIntegralClosure.algebraMap_injective B₀' D.R0 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_add, map_add, map_add,
      IsIntegralClosure.algebraMap_mk', IsIntegralClosure.algebraMap_mk'])

/-- The map `B₁ → B₁'` of normalisations induced by `f`. -/
def map1 : B₁ →+* B₁' where
  toFun b := IsIntegralClosure.mk' B₁' (f (algebraMap B₁ L b)) (isIntegral_f1 h1L h1L' f hf B₁ b)
  map_one' := IsIntegralClosure.algebraMap_injective B₁' D.R1 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_one, map_one, map_one])
  map_mul' x y := IsIntegralClosure.algebraMap_injective B₁' D.R1 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_mul, map_mul, map_mul,
      IsIntegralClosure.algebraMap_mk', IsIntegralClosure.algebraMap_mk'])
  map_zero' := IsIntegralClosure.algebraMap_injective B₁' D.R1 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_zero, map_zero, map_zero])
  map_add' x y := IsIntegralClosure.algebraMap_injective B₁' D.R1 L' (by
    rw [IsIntegralClosure.algebraMap_mk', map_add, map_add, map_add,
      IsIntegralClosure.algebraMap_mk', IsIntegralClosure.algebraMap_mk'])

omit [Algebra D.R1 L] [Algebra D.R1 L'] [Algebra D.R0 B₀] [IsScalarTower D.R0 B₀ L]
  [Algebra D.R0 B₀'] [IsScalarTower D.R0 B₀' L'] in
lemma algebraMap_map0 (b : B₀) :
    algebraMap B₀' L' (map0 h0L h0L' f hf B₀ B₀' b) = f (algebraMap B₀ L b) :=
  IsIntegralClosure.algebraMap_mk' (R := D.R0) B₀' _ (isIntegral_f0 h0L h0L' f hf B₀ b)

omit [Algebra D.R0 L] [Algebra D.R0 L'] [Algebra D.R1 B₁] [IsScalarTower D.R1 B₁ L]
  [Algebra D.R1 B₁'] [IsScalarTower D.R1 B₁' L'] in
lemma algebraMap_map1 (b : B₁) :
    algebraMap B₁' L' (map1 h1L h1L' f hf B₁ B₁' b) = f (algebraMap B₁ L b) :=
  IsIntegralClosure.algebraMap_mk' (R := D.R1) B₁' _ (isIntegral_f1 h1L h1L' f hf B₁ b)

omit [Algebra D.R1 L] [Algebra D.R1 L'] in
lemma map0_algebraMap (a : D.R0) :
    map0 h0L h0L' f hf B₀ B₀' (algebraMap D.R0 B₀ a) = algebraMap D.R0 B₀' a :=
  IsIntegralClosure.algebraMap_injective B₀' D.R0 L' (by
    rw [algebraMap_map0, ← IsScalarTower.algebraMap_apply, hf0 h0L h0L' f hf,
      ← IsScalarTower.algebraMap_apply])

omit [Algebra D.R0 L] [Algebra D.R0 L'] in
lemma map1_algebraMap (a : D.R1) :
    map1 h1L h1L' f hf B₁ B₁' (algebraMap D.R1 B₁ a) = algebraMap D.R1 B₁' a :=
  IsIntegralClosure.algebraMap_injective B₁' D.R1 L' (by
    rw [algebraMap_map1, ← IsScalarTower.algebraMap_apply, hf1 h1L h1L' f hf,
      ← IsScalarTower.algebraMap_apply])

omit [Algebra D.R0 L] [Algebra D.R1 L] [Algebra D.R0 L'] [Algebra D.R1 L'] in
include hf in
lemma isIntegral_f01 (z : integralClosure D.R01 L) : IsIntegral D.R01 (f (z : L)) :=
  IsIntegral.map_of_comp_eq (RingHom.id D.R01) f (RingHom.ext fun a ↦ (hf a).symm) z.2

/-- The map of the overlaps `∫(D.R01, L) → ∫(D.R01, L')` induced by `f`. -/
def map01 : integralClosure D.R01 L →+* integralClosure D.R01 L' :=
  (f.comp (integralClosure D.R01 L).val.toRingHom).codRestrict (integralClosure D.R01 L')
    fun z ↦ isIntegral_f01 f hf z

/-- **The morphism of normalisations `P_L → P_L'` induced by `f : L → L'`.** -/
def normMap :
    TwoChartMap (twoChart B₀ B₁ h0L h1L) (twoChart B₀' B₁' h0L' h1L') where
  f0 := letI := alg0 D B₀; letI := alg0 D B₀'
    { map0 h0L h0L' f hf B₀ B₀' with
      commutes' := fun a ↦ map0_algebraMap h0L h0L' f hf B₀ B₀' (algebraMap A D.R0 a) }
  f1 := letI := alg1 D B₁; letI := alg1 D B₁'
    { map1 h1L h1L' f hf B₁ B₁' with
      commutes' := fun a ↦ map1_algebraMap h1L h1L' f hf B₁ B₁' (algebraMap A D.R1 a) }
  f01 := letI := alg01 D L; letI := alg01 D L'
    { map01 f hf with
      commutes' := fun a ↦ Subtype.ext (hf (algebraMap A D.R01 a)) }
  hx := by exact map0_algebraMap h0L h0L' f hf B₀ B₀' D.x
  hy := by exact map1_algebraMap h1L h1L' f hf B₁ B₁' D.y
  hu := Subtype.ext (hf (D.u : D.R01))
  h0 b := Subtype.ext (algebraMap_map0 h0L h0L' f hf B₀ B₀' b).symm
  h1 b := Subtype.ext (algebraMap_map1 h1L h1L' f hf B₁ B₁' b).symm

/-- **Generic-fibre compatibility on the first chart.** -/
lemma normMap_f0_algebraMap (b : B₀) :
    algebraMap B₀' L' ((normMap h0L h1L h0L' h1L' f hf B₀ B₁ B₀' B₁').f0 b) =
      f (algebraMap B₀ L b) :=
  algebraMap_map0 h0L h0L' f hf B₀ B₀' b

/-- **Generic-fibre compatibility on the second chart.** -/
lemma normMap_f1_algebraMap (b : B₁) :
    algebraMap B₁' L' ((normMap h0L h1L h0L' h1L' f hf B₀ B₁ B₀' B₁').f1 b) =
      f (algebraMap B₁ L b) :=
  algebraMap_map1 h1L h1L' f hf B₁ B₁' b

/-- **Generic-fibre compatibility on the overlap.** -/
lemma normMap_f01_val (z : integralClosure D.R01 L) :
    Subtype.val (p := (· ∈ integralClosure D.R01 L'))
        ((normMap h0L h1L h0L' h1L' f hf B₀ B₁ B₀' B₁').f01 z) = f z :=
  rfl

/-- **`normMap` is compatible with the structure maps from `D`.** -/
lemma normMap_comp_toNorm :
    (normMap h0L h1L h0L' h1L' f hf B₀ B₁ B₀' B₁').comp (toNorm B₀ B₁ h0L h1L) =
      toNorm B₀' B₁' h0L' h1L' := by
  refine TwoChartMap.ext (AlgHom.ext fun a ↦ ?_) (AlgHom.ext fun a ↦ ?_)
    (AlgHom.ext fun a ↦ Subtype.ext ?_)
  · exact map0_algebraMap h0L h0L' f hf B₀ B₀' a
  · exact map1_algebraMap h1L h1L' f hf B₁ B₁' a
  · exact hf a

/-- **`normMap` is a morphism of chart algebras.** -/
theorem normMap_isHom :
    (twoChart B₀ B₁ h0L h1L).algStr.IsHom (twoChart B₀' B₁' h0L' h1L').algStr
      (normMap h0L h1L h0L' h1L' f hf B₀ B₁ B₀' B₁').toHom :=
  TwoChartMap.isHom _

end Map

section Functor

variable {L L' L'' : Type u} [Field L] [Field L'] [Field L''] [Algebra D.R01 L] [Algebra D.R01 L']
  [Algebra D.R01 L''] [Algebra D.R0 L] [Algebra D.R1 L] [Algebra D.R0 L'] [Algebra D.R1 L']
  [Algebra D.R0 L''] [Algebra D.R1 L'']
  (h0L : ∀ a, algebraMap D.R01 L (D.ρ0 a) = algebraMap D.R0 L a)
  (h1L : ∀ a, algebraMap D.R01 L (D.ρ1 a) = algebraMap D.R1 L a)
  (h0L' : ∀ a, algebraMap D.R01 L' (D.ρ0 a) = algebraMap D.R0 L' a)
  (h1L' : ∀ a, algebraMap D.R01 L' (D.ρ1 a) = algebraMap D.R1 L' a)
  (h0L'' : ∀ a, algebraMap D.R01 L'' (D.ρ0 a) = algebraMap D.R0 L'' a)
  (h1L'' : ∀ a, algebraMap D.R01 L'' (D.ρ1 a) = algebraMap D.R1 L'' a)
  (B₀ B₁ B₀' B₁' B₀'' B₁'' : Type u) [CommRing B₀] [CommRing B₁] [CommRing B₀'] [CommRing B₁']
  [CommRing B₀''] [CommRing B₁'']
  [Algebra D.R0 B₀] [Algebra B₀ L] [IsScalarTower D.R0 B₀ L] [IsIntegralClosure B₀ D.R0 L]
  [Algebra D.R1 B₁] [Algebra B₁ L] [IsScalarTower D.R1 B₁ L] [IsIntegralClosure B₁ D.R1 L]
  [Algebra D.R0 B₀'] [Algebra B₀' L'] [IsScalarTower D.R0 B₀' L'] [IsIntegralClosure B₀' D.R0 L']
  [Algebra D.R1 B₁'] [Algebra B₁' L'] [IsScalarTower D.R1 B₁' L'] [IsIntegralClosure B₁' D.R1 L']
  [Algebra D.R0 B₀''] [Algebra B₀'' L''] [IsScalarTower D.R0 B₀'' L'']
  [IsIntegralClosure B₀'' D.R0 L'']
  [Algebra D.R1 B₁''] [Algebra B₁'' L''] [IsScalarTower D.R1 B₁'' L'']
  [IsIntegralClosure B₁'' D.R1 L'']

/-- **`normMap` of the identity.** -/
lemma normMap_id :
    normMap h0L h1L h0L h1L (RingHom.id L) (fun _ ↦ rfl) B₀ B₁ B₀ B₁ =
      TwoChartMap.id (twoChart B₀ B₁ h0L h1L) := by
  refine TwoChartMap.ext (AlgHom.ext fun b ↦ ?_) (AlgHom.ext fun b ↦ ?_)
    (AlgHom.ext fun z ↦ Subtype.ext rfl)
  · exact IsIntegralClosure.algebraMap_injective B₀ D.R0 L
      (normMap_f0_algebraMap h0L h1L h0L h1L (RingHom.id L) (fun _ ↦ rfl) B₀ B₁ B₀ B₁ b)
  · exact IsIntegralClosure.algebraMap_injective B₁ D.R1 L
      (normMap_f1_algebraMap h0L h1L h0L h1L (RingHom.id L) (fun _ ↦ rfl) B₀ B₁ B₀ B₁ b)

/-- **`normMap` of a composition.** -/
lemma normMap_comp (f : L →+* L') (hf : ∀ a, f (algebraMap D.R01 L a) = algebraMap D.R01 L' a)
    (g : L' →+* L'') (hg : ∀ a, g (algebraMap D.R01 L' a) = algebraMap D.R01 L'' a) :
    normMap h0L h1L h0L'' h1L'' (g.comp f) (fun a ↦ by rw [RingHom.comp_apply, hf, hg])
        B₀ B₁ B₀'' B₁'' =
      (normMap h0L' h1L' h0L'' h1L'' g hg B₀' B₁' B₀'' B₁'').comp
        (normMap h0L h1L h0L' h1L' f hf B₀ B₁ B₀' B₁') := by
  refine TwoChartMap.ext (AlgHom.ext fun b ↦ ?_) (AlgHom.ext fun b ↦ ?_)
    (AlgHom.ext fun z ↦ Subtype.ext rfl)
  · refine IsIntegralClosure.algebraMap_injective B₀'' D.R0 L'' ?_
    rw [normMap_f0_algebraMap, TwoChartMap.comp_f0, normMap_f0_algebraMap,
      normMap_f0_algebraMap, RingHom.comp_apply]
  · refine IsIntegralClosure.algebraMap_injective B₁'' D.R1 L'' ?_
    rw [normMap_f1_algebraMap, TwoChartMap.comp_f1, normMap_f1_algebraMap,
      normMap_f1_algebraMap, RingHom.comp_apply]

end Functor

end

end TwoChartNorm

end SemistableReduction
