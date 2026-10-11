/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGaloisGal

/-!
# Rigidity of the orbifold Galois objects (Blueprint §11.3, G6, orbifold case)

Two morphisms `f, g : OrbGal.obj ⟶ Y` which agree on the base pair `(t₀ ∘ ev₁, (1, e₀))`
induce the same map of fibres (`fibreMap_eq_of_preMap_eq`):

* their level maps agree after `ev₁` (`B` is connected, `algHom_eq_of_comp_eq`), hence their
  model maps agree on the copy `1` (dominance of `j₁`), hence their covering maps agree on the
  sheet `(1, Z̃)` (uniqueness of lifts);
* on the copy `x` the level maps are determined by `ev₁` through the equivariance along
  `r(x)` (`ev_comp_eq`), and the two maps differ by `r_g(x) r_f(x)⁻¹ ∈ H⁰` of `Y`, which also
  relates the covering maps on the sheet `(x, Z̃)`.

With `exists_iso_preMap` and `conjHom` this gives rigidity on fibres for any fibre element
(`fibreMap_eq_of_eq`, **rig**).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A₁ : Type u} [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

namespace OrbGal

variable {X₁ : TempObj O R A₁} (D : IndData (μ₁ A A₁) X₁) [Subsingleton X₁.Lv.L.H]
  (hX : IndFaithful X₁) {E : Type u} [TopologicalSpace E] {p : E → X₁.Lv.Z}
  (hp : IsUniversalCovering.{u, u, u, u} p) (hc : ∀ z, (p ⁻¹' {z}).Countable)
  {Y : TempObj O R A}

/-- The evaluation at the copy `x` of a level map out of the induced level is determined by
the evaluation at the copy `1`, through the equivariance along `r (x, 1)`. -/
lemma ev_comp_eq (m : (D.lv hX).L ⟶ Y.Lv.L) (x : D.S) (y : Y.Lv.L.B) :
    D.ev x (m.f y) = D.ev 1 (m.f ((m.r (gS D hX x) : SemilinearAut R A Y.Lv.L.B).σ.symm y)) := by
  have h1 : D.ev x (m.f y) = D.ev 1 (((gS D hX x : (D.lv hX).L.H) :
      SemilinearAut R A (D.lv hX).L.B).σ.symm (m.f y)) := by
    change _ = D.ev 1 (((D.equivT hX (x, 1) : D.level.H) :
      SemilinearAut R A D.level.B).σ.symm (m.f y))
    rw [IndData.ev_equivT_symm]
    simp
  rw [h1]
  congr 1
  have := m.f_σ (gS D hX x) (((m.r (gS D hX x)) : SemilinearAut R A Y.Lv.L.B).σ.symm y)
  rw [RingEquiv.apply_symm_apply] at this
  exact (RingEquiv.symm_apply_eq _).mpr this

variable [IsSchemeTheoreticallyDominant X₁.Lv.j]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

section Nose

variable (hidem : ∀ e : X₁.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
  (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (e₀ : E) (he₀ : p e₀ = X₁.Lv.sp V hV t₀)
  (f g : obj D hX hp hc ⟶ Y)

include hidem in
lemma ev₁_comp_eq_of_preMap_eq
    (h : preMap V hV f (basePre D hX hp hc V hV t₀ e₀ he₀) =
      preMap V hV g (basePre D hX hp hc V hV t₀ e₀ he₀)) :
    D.ev₁.comp f.φ.f = D.ev₁.comp g.φ.f := by
  haveI := Y.Lv.L.etale
  haveI := Y.Lv.L.finite
  have h1 := congrArg (fun q => q.1.1) h
  exact algHom_eq_of_comp_eq hidem _ _ t₀ h1

lemma inc_ψ_eq (hf : D.ev₁.comp f.φ.f = D.ev₁.comp g.φ.f) :
    D.inc 1 ≫ f.ψ = D.inc 1 ≫ g.ψ := by
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated Y.Lv.c.toSpec
    (by
      rw [Category.assoc, Category.assoc]
      erw [f.ψ_toSpec, g.ψ_toSpec]) X₁.Lv.j ?_
  have hj : ∀ m : obj D hX hp hc ⟶ Y, X₁.Lv.j ≫ D.inc 1 ≫ m.ψ =
      Spec.map (CommRingCat.ofHom ((D.ev₁.comp m.φ.f : Y.Lv.L.B →ₐ[R] X₁.Lv.L.B) :
        Y.Lv.L.B →+* X₁.Lv.L.B)) ≫ Y.Lv.j := fun m => by
    rw [← Category.assoc, ← IndData.specMap_ev_j, Category.assoc]
    refine (congrArg (fun φ => Spec.map (CommRingCat.ofHom (D.ev 1)) ≫ φ) m.j_ψ).trans ?_
    refine (Category.assoc _ _ _).symm.trans ?_
    congr 1
    exact (Spec.map_comp _ _).symm
  rw [hj, hj, hf]

lemma coe_Θo_one (e : E) : ((Θo D hX hp hc ⟨1, e⟩).1.1).1 = D.inc 1 (p e).1 :=
  (congrArg Subtype.val (Θ_fst (Lv := D.lv hX) (hp := isUniversalCovering_proj D hX hp)
    (hc := countable_proj D hX hc) _)).trans
    ((congrArg Subtype.val (indProj_one (proj D hX p) e)).trans (IndData.inc₁S_coe D hX (p e)))

lemma h_eq_of_inc_ψ_eq (hψ : D.inc 1 ≫ f.ψ = D.inc 1 ≫ g.ψ)
    (h₀ : f.h (Θo D hX hp hc ⟨1, e₀⟩) = g.h (Θo D hX hp hc ⟨1, e₀⟩)) (e : E) :
    f.h (Θo D hX hp hc ⟨1, e⟩) = g.h (Θo D hX hp hc ⟨1, e⟩) := by
  haveI := hp.connectedSpace
  have hc₁ : Continuous fun e : E => Θo D hX hp hc ⟨1, e⟩ :=
    (Θo D hX hp hc).continuous.comp (continuous_sigmaMk (σ := fun _ : (D.lv hX).L.H => E))
  have key := Y.P.isCoveringMap.eq_of_comp_eq (f.continuous_h.comp hc₁)
    (g.continuous_h.comp hc₁) (funext fun e => Subtype.ext ?_) e₀ h₀
  · exact congrFun key e
  · change ((f.h _).1.1 : Y.Lv.c.scheme) = (g.h _).1.1
    rw [f.fst_h, g.fst_h, coe_Θo_one]
    have := congrArg (fun φ => φ (p e).1) hψ
    simp only [Scheme.Hom.comp_apply] at this
    exact this

end Nose

end OrbGal

end

end TemperedFundamentalGroups
