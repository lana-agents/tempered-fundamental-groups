/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.InducedLevel

/-!
# Morphisms of induced tempered coverings (Blueprint §11, F7′)

A morphism `m : X₁ ⟶ X₂` of tempered coverings of `[Spec R / A']` together with a homomorphism
`θ : S₁ →* S₂` of index groups compatible with the induction data (`α₂ ∘ θ = α₁`,
`θ ∘ β₁ = β₂ ∘ m.r`) induces a morphism `D₁.obj ⟶ D₂.obj` of induced tempered coverings
(`IndData.hom`): `φ ↦ (x ↦ m.f (φ (θ x)))` on algebras, `(s, k) ↦ (θ s, m.r k)` on groups, the
copy `x` of `𝒯₁` to the copy `θ x` of `𝒯₂` through `m.ψ`, and `m.h` on covering spaces.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A' : Type u} [Group A'] [MulSemiringAction A' R] {μ : OrbMap R A R A'}

namespace IndData

variable {X' : TempObj O R A'} (D : IndData μ X')

lemma ext_ev {y y' : D.level.B} (h : ∀ x, D.ev x y = D.ev x y') : y = y' :=
  D.E.injective (funext h)

lemma ev_injective_equivT (hX : IndFaithful X') {g g' : D.level.H}
    (h : (D.equivT hX).symm g = (D.equivT hX).symm g') : g = g' :=
  (D.equivT hX).symm.injective h

variable {X₁ X₂ : TempObj O R A'} (D₁ : IndData μ X₁) (D₂ : IndData μ X₂)
  (hX₁ : IndFaithful X₁) (hX₂ : IndFaithful X₂) (m : X₁ ⟶ X₂) (θ : D₁.S →* D₂.S)
  (hθα : ∀ x, D₂.α (θ x) = D₁.α x) (hθβ : ∀ k, θ (D₁.β k) = D₂.β (m.φ.r k))

/-- The map of induced algebras. -/
def homF : D₂.level.B →ₐ[R] D₁.level.B :=
  D₁.E.symm.toAlgHom.comp ((indMap θ hθα m.φ.f).comp D₂.E.toAlgHom)

lemma ev_homF (x : D₁.S) (y : D₂.level.B) :
    D₁.ev x (homF D₁ D₂ m θ hθα y) = m.φ.f (D₂.ev (θ x) y) := by
  change ((D₁.E (D₁.E.symm _) : D₁.Alg) x : X₁.Lv.L.B) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

/-- The map of level groups `(s, k) ↦ (θ s, m.r k)`. -/
def homR : D₁.level.H →* D₂.level.H :=
  (D₂.equivT hX₂).toMonoidHom.comp ((θ.prodMap m.φ.r).comp (D₁.equivT hX₁).symm.toMonoidHom)

lemma homR_equivT (t : D₁.T) :
    homR D₁ D₂ hX₁ hX₂ m θ (D₁.equivT hX₁ t) = D₂.equivT hX₂ (θ t.1, m.φ.r t.2) := by
  simp [homR]
  rfl

include hθβ in
/-- **The morphism of induced levels.** -/
def homφ : D₁.level ⟶ D₂.level where
  f := homF D₁ D₂ m θ hθα
  r := homR D₁ D₂ hX₁ hX₂ m θ
  r_a g := by
    obtain ⟨t, rfl⟩ := (D₁.equivT hX₁).surjective g
    rw [homR_equivT]
    exact hθα t.1
  f_σ g y := by
    obtain ⟨t, rfl⟩ := (D₁.equivT hX₁).surjective g
    rw [homR_equivT]
    refine D₁.ext_ev fun x => ?_
    rw [ev_homF, ev_equivT, ev_equivT, ev_homF, m.φ.f_σ]
    congr 2
    rw [map_mul, map_mul, map_inv, hθβ]

/-- The model map: the copy `x` of `𝒯₁` to the copy `θ x` of `𝒯₂` through `m.ψ`. -/
def homψ : D₁.c.scheme ⟶ D₂.c.scheme :=
  (SemistableReduction.ModelCode.sigmaIso (fun _ : D₁.S => X₁.Lv.c)).inv ≫
    Sigma.desc fun x => m.ψ ≫ D₂.inc (θ x)

@[reassoc]
lemma inc_homψ (x : D₁.S) : D₁.inc x ≫ homψ D₁ D₂ m θ = m.ψ ≫ D₂.inc (θ x) := by
  simp only [homψ, SemistableReduction.ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ _

lemma homψ_toSpec : homψ D₁ D₂ m θ ≫ D₂.c.toSpec = D₁.c.toSpec :=
  D₁.c_hom_ext fun x => by rw [inc_homψ_assoc, inc_toSpec, m.ψ_toSpec, inc_toSpec]

lemma homψ_fold : homψ D₁ D₂ m θ ≫ D₂.fold = D₁.fold ≫ m.ψ :=
  D₁.c_hom_ext fun x => by
    rw [inc_homψ_assoc, inc_fold, Category.comp_id, inc_fold_assoc]

lemma j_homψ : D₁.j ≫ homψ D₁ D₂ m θ =
    Spec.map (CommRingCat.ofHom (homF D₁ D₂ m θ hθα : D₂.level.B →+* D₁.level.B)) ≫ D₂.j := by
  refine D₁.hom_ext fun x => ?_
  have hring : (D₁.ev x).comp (homF D₁ D₂ m θ hθα : D₂.level.B →+* D₁.level.B) =
      (m.φ.f : X₂.Lv.L.B →+* X₁.Lv.L.B).comp (D₂.ev (θ x)) :=
    RingHom.ext fun y => ev_homF D₁ D₂ m θ hθα x y
  rw [specMap_ev_j_assoc, inc_homψ, ← Category.assoc, m.j_ψ, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, Category.assoc, specMap_ev_j]

lemma exists_inc (z : D.c.scheme) : ∃ x z₀, D.inc x z₀ = z := by
  set e := SemistableReduction.ModelCode.sigmaIso (fun _ : D.S => X'.Lv.c)
  obtain ⟨⟨x, z₀⟩, hz⟩ := (sigmaMk (fun _ : D.S => X'.Lv.c.scheme)).surjective (e.inv z)
  refine ⟨x, z₀, ?_⟩
  have h1 : D.inc x z₀ = e.hom (Sigma.ι (fun _ : D.S => X'.Lv.c.scheme) x z₀) :=
    Scheme.Hom.comp_apply _ _ _
  rw [h1, ← sigmaMk_mk, hz, ← Scheme.Hom.comp_apply, e.inv_hom_id]
  rfl

/-- A morphism of tempered coverings is equivariant on the model at points under the covering
space. -/
lemma _root_.TemperedFundamentalGroups.TempObj.Hom.ψ_ρ {Y₁ Y₂ : TempObj O R A'} (n : Y₁ ⟶ Y₂)
    (k : Y₁.Lv.L.H) (p : Y₁.P.carrier) :
    n.ψ ((Y₁.Lv.ρ k).hom (p.1.1 : Y₁.Lv.c.scheme)) =
      (Y₂.Lv.ρ (n.φ.r k)).hom (n.ψ (p.1.1 : Y₁.Lv.c.scheme)) := by
  have h := congrArg (fun q : Y₂.P.carrier => (q.1.1 : Y₂.Lv.c.scheme)) (n.h_act k p)
  rw [n.fst_h, Y₁.P.act_fst, Level.ρs_apply, Y₂.P.act_fst, Level.ρs_apply, n.fst_h] at h
  exact h

lemma toH'_equivT {X' : TempObj O R A'} (D : IndData μ X') (hX : IndFaithful X') (t : D.T) :
    D.toH' hX (D.equivT hX t) = t.2 := by
  simp [toH']

/-- The map of special fibres induced by the model map. -/
def homψS : (D₁.lv hX₁).Z → (D₂.lv hX₂).Z :=
  specialFibreMap (homψ D₁ D₂ m θ) (homψ_toSpec D₁ D₂ m θ)

lemma homψS_coe (z : (D₁.lv hX₁).Z) :
    (homψS D₁ D₂ hX₁ hX₂ m θ z).1 = homψ D₁ D₂ m θ z.1 :=
  coe_specialFibreMap _ _ _

lemma homH_aux (q : (D₁.obj hX₁).P.carrier) :
    (m.h (CoveringCode.pullbackPt X₁.P (D₁.foldS hX₁) q)).1.1 =
      D₂.foldS hX₂ (homψS D₁ D₂ hX₁ hX₂ m θ q.1.1) := by
  apply Subtype.ext
  rw [m.fst_h, coe_foldS, homψS_coe, ← Scheme.Hom.comp_apply, homψ_fold,
    Scheme.Hom.comp_apply]
  rfl

/-- The map of covering spaces. -/
def homH : (D₁.obj hX₁).P.carrier → (D₂.obj hX₂).P.carrier :=
  CoveringCode.pullbackLiftFun X₂.P (fun q => homψS D₁ D₂ hX₁ hX₂ m θ q.1.1)
    (fun q => m.h (CoveringCode.pullbackPt X₁.P (D₁.foldS hX₁) q)) (homH_aux D₁ D₂ hX₁ hX₂ m θ)

lemma pullbackPt_homH (q : (D₁.obj hX₁).P.carrier) :
    CoveringCode.pullbackPt X₂.P (D₂.foldS hX₂) (homH D₁ D₂ hX₁ hX₂ m θ q) =
      m.h (CoveringCode.pullbackPt X₁.P (D₁.foldS hX₁) q) :=
  CoveringCode.pullbackPt_liftFun _ _ _ _ _

include hθβ in
/-- **The morphism of induced tempered coverings.** -/
def hom : D₁.obj hX₁ ⟶ D₂.obj hX₂ where
  φ := homφ D₁ D₂ hX₁ hX₂ m θ hθα hθβ
  ψ := homψ D₁ D₂ m θ
  ψ_toSpec := homψ_toSpec D₁ D₂ m θ
  j_ψ := j_homψ D₁ D₂ m θ hθα
  h := homH D₁ D₂ hX₁ hX₂ m θ
  continuous_h := CoveringCode.continuous_pullbackLiftFun X₂.P (homH_aux D₁ D₂ hX₁ hX₂ m θ)
    ((continuous_specialFibreMap _ _).comp (D₁.obj hX₁).P.continuous_proj)
    (m.continuous_h.comp (CoveringCode.continuous_pullbackPt X₁.P))
  fst_h x := homψS_coe D₁ D₂ hX₁ hX₂ m θ x.1.1
  h_act g x := by
    obtain ⟨t, rfl⟩ := (D₁.equivT hX₁).surjective g
    refine CoveringCode.pullback_ext X₂.P (D₂.foldS hX₂) ?_ ?_
    · apply Subtype.ext
      change homψ D₁ D₂ m θ (D₁.actHom ((D₁.equivT hX₁).symm (D₁.equivT hX₁ t)) x.1.1.1) =
        D₂.actHom ((D₂.equivT hX₂).symm (homR D₁ D₂ hX₁ hX₂ m θ (D₁.equivT hX₁ t)))
          (homψ D₁ D₂ m θ x.1.1.1)
      rw [MulEquiv.symm_apply_apply, homR_equivT, MulEquiv.symm_apply_apply]
      obtain ⟨y, z₀, hz⟩ := D₁.exists_inc x.1.1.1
      have hp : ((CoveringCode.pullbackPt X₁.P (D₁.foldS hX₁) x).1.1 : X₁.Lv.c.scheme) = z₀ := by
        change D₁.fold x.1.1.1 = z₀
        rw [← hz, ← Scheme.Hom.comp_apply, inc_fold]
        rfl
      have hψρ := m.ψ_ρ t.2 (CoveringCode.pullbackPt X₁.P (D₁.foldS hX₁) x)
      rw [hp] at hψρ
      have hidx : θ (t.1 * y * (D₁.β t.2)⁻¹) = θ t.1 * θ y * (D₂.β (m.φ.r t.2))⁻¹ := by
        rw [map_mul, map_mul, map_inv, hθβ]
      have key : (D₁.inc y ≫ D₁.actHom t ≫ homψ D₁ D₂ m θ) z₀ =
          (D₁.inc y ≫ homψ D₁ D₂ m θ ≫ D₂.actHom (θ t.1, m.φ.r t.2)) z₀ := by
        rw [inc_actHom_assoc, inc_homψ, inc_homψ_assoc, inc_actHom, Scheme.Hom.comp_apply,
          Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hψρ, hidx]
      simpa only [Scheme.Hom.comp_apply, hz] using key
    · change (m.h (CoveringCode.pullbackPt X₁.P (D₁.foldS hX₁)
          (CoveringCode.pullbackActFun X₁.P (D₁.toH' hX₁) (D₁.foldS_ρs hX₁)
            (D₁.equivT hX₁ t) x))).1.2 =
        (X₂.P.act (D₂.toH' hX₂ (homR D₁ D₂ hX₁ hX₂ m θ (D₁.equivT hX₁ t)))
          (CoveringCode.pullbackPt X₂.P (D₂.foldS hX₂) (homH D₁ D₂ hX₁ hX₂ m θ x))).1.2
      rw [CoveringCode.pullbackPt_actFun, pullbackPt_homH, m.h_act, toH'_equivT, homR_equivT,
        toH'_equivT]

end IndData

end

end TemperedFundamentalGroups
