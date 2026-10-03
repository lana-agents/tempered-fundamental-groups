/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.FracMap
import TemperedFundamentalGroups.Andre.GaloisDomW
import TemperedFundamentalGroups.SemistableReduction.XHarmonic

/-!
# W-model data on levels and x-harmonicity of morphisms (Blueprint §10.3.6, item 4)

`Level.IsW x Lv` (`Andre/GaloisDomW.lean`) is an existential statement; `WData x Lv` bundles its
witnesses: a split semistable W-model `c'` without loops over the valuation ring `O'` of a
finite extension `K'/K`, an isomorphism `e : Lv.c ≅ c'`, a fraction field `L₁` of the ring of
the level, and the generic point `j₁ : Spec L₁ ⟶ c'`.

For a morphism `m : X ⟶ Y` of the tempered category between objects whose levels carry W-model
data `D`, `D'`, the model map `D.e⁻¹ ≫ m.ψ ≫ D'.e : D.c' ⟶ D'.c'` satisfies the hypotheses of
`SemistableReduction.Statement.HarmonicX` (`L₂ = D'.L₁ ⊆ L₁ = D.L₁` through the map of
fraction fields induced by the level map, `fracMap`), hence is **x-harmonic**
(`WData.isHarmonicX`), with x-lengths normalised by a uniformizer `ϖ` of `O` and taken on the
x-line `x ∈ R`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- **W-model data on a level** (the witnesses of `Level.IsW x Lv`). -/
structure WData (x : R) (Lv : Level O R A) where
  /-- The finite extension of `K`. -/
  K' : Type u
  [fieldK' : Field K']
  [algK : Algebra K K']
  [fd : FiniteDimensional K K']
  /-- Its valuation ring over `O`. -/
  O' : ValuationSubring K'
  hO' : O'.comap (algebraMap K K') = O
  [dvr : IsDiscreteValuationRing O']
  /-- A uniformizer. -/
  ϖ' : O'
  hϖ' : Irreducible ϖ'
  /-- The W-model. -/
  c' : ModelCode O'
  /-- The identification of the model of the level with the W-model. -/
  e : Lv.c.scheme ≅ c'.scheme
  semistable : SemistableReduction.ModelCode.IsSemistable ϖ' c'
  split : SemistableReduction.ModelCode.IsSplit ϖ' c'
  noLoops : SemistableReduction.ModelCode.NoLoops c'
  toSpec_eq : e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap K K').restrict O O' (fun y hy => by rw [← hO'] at hy; exact hy))) =
    Lv.c.toSpec
  /-- A fraction field of the ring of the level. -/
  L₁ : Type u
  [fieldL : Field L₁]
  [algB : Algebra Lv.L.B L₁]
  [frac : IsFractionRing Lv.L.B L₁]
  [algK' : Algebra K' L₁]
  [algO' : Algebra O' L₁]
  [tower : IsScalarTower O' K' L₁]
  /-- The `K'`-structure of the ring of the level. -/
  κ : K' →+* Lv.L.B
  /-- The generic point of the W-model. -/
  j₁ : Spec (CommRingCat.of L₁) ⟶ c'.scheme
  hκL : algebraMap K' L₁ = (algebraMap Lv.L.B L₁).comp κ
  hκ : κ.comp (algebraMap K K') = (algebraMap R Lv.L.B).comp (algebraMap K R)
  wmodel : SemistableReduction.ModelCode.IsUnfolded O'
    (algebraMap Lv.L.B L₁ (algebraMap R Lv.L.B x)) c' j₁
  hj : j₁ = Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B L₁)) ≫ Lv.j ≫ e.hom

attribute [instance] WData.fieldK' WData.algK WData.fd WData.dvr WData.fieldL WData.algB
  WData.frac WData.algK' WData.algO' WData.tower

namespace WData

variable {x : R} {Lv : Level O R A}

lemma nonempty_of_isW (h : Level.IsW x Lv) : Nonempty (WData x Lv) := by
  obtain ⟨K', _, _, _, O', hO', _, ϖ', hϖ', c', e, hss, hsp, hnl, hto, L₁, _, _, _, _, _, _, κ,
    j₁, hκL, hκ, hW, hj⟩ := h
  exact ⟨⟨K', O', hO', ϖ', hϖ', c', e, hss, hsp, hnl, hto, L₁, κ, j₁, hκL, hκ, hW, hj⟩⟩

/-- The x-line in the function field. -/
def xL (D : WData x Lv) : D.L₁ := algebraMap Lv.L.B D.L₁ (algebraMap R Lv.L.B x)

/-- The `K`-algebra structure of the function field (through the ring of the level). -/
@[reducible] def algKL (D : WData x Lv) : Algebra K D.L₁ :=
  ((algebraMap Lv.L.B D.L₁).comp ((algebraMap R Lv.L.B).comp (algebraMap K R))).toAlgebra

/-- The image of the uniformizer of the base in the function field. -/
def ϖL (D : WData x Lv) (ϖ : O) : D.L₁ :=
  algebraMap Lv.L.B D.L₁ (algebraMap R Lv.L.B (algebraMap K R (ϖ : K)))

lemma isDomain (D : WData x Lv) : IsDomain Lv.L.B :=
  Function.Injective.isDomain (algebraMap Lv.L.B D.L₁) (IsFractionRing.injective _ _)

lemma isScalarTower_K (D : WData x Lv) :
    letI := D.algKL
    IsScalarTower K D.K' D.L₁ := by
  letI := D.algKL
  refine IsScalarTower.of_algebraMap_eq fun k => ?_
  rw [D.hκL, RingHom.comp_apply, ← RingHom.comp_apply D.κ, D.hκ]
  rfl

/-- The point of the special fibre of the W-model of a point of the special fibre of the model
of the level. -/
lemma toSpec_e_inv (D : WData x Lv) :
    D.e.inv ≫ Lv.c.toSpec = D.c'.toSpec ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap K D.K').restrict O D.O' (fun y hy => by rw [← D.hO'] at hy; exact hy))) := by
  rw [← D.toSpec_eq, Iso.inv_hom_id_assoc]

end WData

section Harmonic

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {x : R}

/-- **Morphisms between objects over levels with W-model data are x-harmonic** (from the
targeted `Statement.HarmonicX`). -/
theorem WData.isHarmonicX (hX : SemistableReduction.Statement.HarmonicX.{u}) (ϖ : O)
    (hϖ : Irreducible ϖ) {X Y : TempObj O R A} (m : X ⟶ Y) (D : WData x X.Lv)
    (D' : WData x Y.Lv) :
    SemistableReduction.ModelCode.IsHarmonicX D.O' D'.O' D.ϖ' D'.ϖ' (D.ϖL ϖ) (D'.ϖL ϖ) D.xL
      D'.xL D.j₁ D'.j₁ (D.e.inv ≫ m.ψ ≫ D'.e.hom) := by
  haveI := D.isDomain
  haveI := D'.isDomain
  haveI := X.Lv.L.etale
  haveI := X.Lv.L.finite
  haveI := Y.Lv.L.etale
  haveI := Y.Lv.L.finite
  letI := D.algKL
  letI := D'.algKL
  haveI := D.isScalarTower_K
  haveI := D'.isScalarTower_K
  letI : Algebra D'.L₁ D.L₁ := (fracMap D'.L₁ D.L₁ m.φ.f).toAlgebra
  haveI : FiniteDimensional D'.L₁ D.L₁ := finiteDimensional_fracMap D'.L₁ D.L₁ m.φ.f
  have hfrac : ∀ b, algebraMap D'.L₁ D.L₁ (algebraMap Y.Lv.L.B D'.L₁ b) =
      algebraMap X.Lv.L.B D.L₁ (m.φ.f b) := fracMap_algebraMap m.φ.f
  haveI : IsScalarTower K D'.L₁ D.L₁ := IsScalarTower.of_algebraMap_eq fun k => by
    change _ = algebraMap D'.L₁ D.L₁ (algebraMap Y.Lv.L.B D'.L₁ _)
    rw [hfrac, RingHom.comp_apply, AlgHom.commutes]
    rfl
  have hxL : algebraMap D'.L₁ D.L₁ D'.xL = D.xL := by
    rw [WData.xL, hfrac, AlgHom.commutes]
    rfl
  have h := hX K O ϖ hϖ D.K' D'.K' D.O' D'.O' D.hO' D'.hO' D.ϖ' D'.ϖ' D.hϖ' D'.hϖ' D.L₁ D'.L₁
    D'.xL D.c' D'.c' (D.e.inv ≫ m.ψ ≫ D'.e.hom) D.j₁ D'.j₁ (by rw [hxL]; exact D.wmodel)
    D'.wmodel ?_ ?_ D.semistable D'.semistable D.split D'.split D.noLoops D'.noLoops
  · rw [hxL] at h
    exact h
  · rw [D.hj, D'.hj]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc X.Lv.j m.ψ, m.j_ψ]
    simp only [Category.assoc]
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    exact RingHom.ext fun b => (hfrac b).symm
  · rw [Category.assoc, Category.assoc, D'.toSpec_eq, m.ψ_toSpec, ← D.toSpec_e_inv]

end Harmonic

end

end TemperedFundamentalGroups
