/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGalois

/-!
# Twisted automorphisms of the orbifold Galois objects (Blueprint §11.3, G6, orbifold case)

Let `Lv₁ = X₁.Lv` be a scheme level with `B = Lv₁.L.B` and `D = OrbGal.data X₁ S α hα` the
induction data. For `c ∈ S` and a semilinear automorphism `γ` of `B` over `α c ∈ A` (with a
model automorphism `ψ_γ` of `𝒯₁` compatible with `j₁`), the **twisted automorphism**

* of the induced algebra: `φ ↦ (x ↦ γ (φ (x c)))` (`twAlg`, `R`-linear since `γ` lies over
  `α c`), with the identity on `S`: a level automorphism `twφ`;
* of the model `∐_S 𝒯₁`: the copy `x` goes to the copy `x c` through `ψ_γ` (`twψ`);
* of the covering space `Ind_1^S Z̃`: `(1, e) ↦ (c, τ e)` for a lift `τ` of `ψ_γ` to `Z̃`
  (`twHom`, via `GaloisObject.liftHom`).

These move points between copies of different type `α x ∈ A`; together with the deck
transformations they act transitively on the fibre of `OrbGal.obj` (`exists_iso_preMap`).
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

variable {X₁ : TempObj O R A₁} (D : IndData (μ₁ A A₁) X₁)

section Twist

variable (c : D.S) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α c)

/-- The twisted automorphism `φ ↦ (x ↦ γ (φ (x c)))` of the induced algebra. -/
def twAlg : D.Alg ≃ₐ[R] D.Alg :=
  { indRingEquiv (α := D.α) 1 c γ.σ with
    commutes' := fun r => by
      funext x
      change γ.σ (algebraMap R X₁.Lv.L.B ((D.α (1⁻¹ * x * c))⁻¹ • r)) =
        algebraMap R X₁.Lv.L.B ((D.α x)⁻¹ • r)
      rw [γ.map_algebraMap, smul_smul, hγ]
      congr 2
      simp only [inv_one, one_mul, map_mul, mul_inv_rev]
      group }

lemma twAlg_apply (φ : D.Alg) (x : D.S) :
    (twAlg D c γ hγ φ x : X₁.Lv.L.B) = γ.σ (φ (x * c)) := by
  change γ.σ (φ (1⁻¹ * x * c)) = _
  rw [inv_one, one_mul]

/-- The twisted automorphism of the coded induced algebra. -/
def twF : D.level.B →ₐ[R] D.level.B :=
  D.E.symm.toAlgHom.comp
    ((twAlg D c γ hγ).toAlgHom.comp D.E.toAlgHom)

lemma ev_twF (x : D.S) (y : D.level.B) :
    D.ev x (twF D c γ hγ y) = γ.σ (D.ev (x * c) y) := by
  change ((D.E (D.E.symm _) : D.Alg) x :
    X₁.Lv.L.B) = _
  rw [AlgEquiv.apply_symm_apply]
  exact twAlg_apply D c γ hγ _ x

variable [Subsingleton X₁.Lv.L.H] (hX : IndFaithful X₁)

/-- **The twisted level automorphism** (the identity on `S`). -/
def twφ : D.level ⟶ D.level where
  f := twF D c γ hγ
  r := MonoidHom.id _
  r_a _ := rfl
  f_σ g y := by
    obtain ⟨t, rfl⟩ := (D.equivT hX).surjective g
    refine D.ext_ev fun (x : D.S) => ?_
    have ht : t.2 = 1 := Subsingleton.elim _ _
    rw [ev_twF, MonoidHom.id_apply, IndData.ev_equivT, IndData.ev_equivT, ev_twF, ht]
    rw [map_one]
    change γ.σ (D.ev (t.1⁻¹ * (x * c) * 1) y) = γ.σ (D.ev (t.1⁻¹ * x * 1 * c) y)
    congr 3
    group

variable (ψγ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme)

/-- The twisted model map: the copy `x` goes to the copy `x c` through `ψ_γ`. -/
def twψ : D.c.scheme ⟶ D.c.scheme :=
  (SemistableReduction.ModelCode.sigmaIso (fun _ : D.S => X₁.Lv.c)).inv ≫
    Sigma.desc fun (x : D.S) => ψγ ≫ D.inc (x * c)

@[reassoc]
lemma inc_twψ (x : D.S) :
    D.inc x ≫ twψ D c ψγ = ψγ ≫ D.inc (x * c) := by
  simp only [twψ, SemistableReduction.ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ _

variable {ψγ} (hψγ : ψγ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec)
  (hjγ : X₁.Lv.j ≫ ψγ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)

include hψγ in
lemma twψ_toSpec : twψ D c ψγ ≫ D.c.toSpec =
    D.c.toSpec :=
  D.c_hom_ext fun (x : D.S) => by
    rw [inc_twψ_assoc, IndData.inc_toSpec, hψγ, IndData.inc_toSpec]

include hjγ in
lemma j_twψ : D.j ≫ twψ D c ψγ =
    Spec.map (CommRingCat.ofHom (twF D c γ hγ : D.level.B →+*
      D.level.B)) ≫ D.j := by
  refine D.hom_ext fun (x : D.S) => ?_
  have hring : (D.ev x).comp (twF D c γ hγ : D.level.B →+*
      D.level.B) =
      (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B).comp (D.ev (x * c)) :=
    RingHom.ext fun y => ev_twF D c γ hγ x y
  rw [IndData.specMap_ev_j_assoc, inc_twψ, ← Category.assoc, hjγ, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, Category.assoc, IndData.specMap_ev_j]

/-- **The twisted automorphism of the induced level with its model.** -/
def twℓ : LevelHom O R A (D.lv hX) (D.lv hX) where
  φ := twφ D c γ hγ hX
  ψ := twψ D c ψγ
  ψ_toSpec := twψ_toSpec D c hψγ
  j_ψ := j_twψ D c γ hγ hjγ

lemma twℓ_isEquivariant : (twℓ D c γ hγ hX hψγ hjγ).IsEquivariant := by
  intro g
  obtain ⟨t, rfl⟩ := (D.equivT hX).surjective g
  have ht : t.2 = 1 := Subsingleton.elim _ _
  change D.actHom ((D.equivT hX).symm
      (D.equivT hX t)) ≫ twψ D c ψγ =
    twψ D c ψγ ≫ D.actHom ((D.equivT hX).symm
      (D.equivT hX t))
  rw [MulEquiv.symm_apply_apply]
  refine D.c_hom_ext fun (x : D.S) => ?_
  have hρ : (X₁.Lv.ρ t.2).hom = 𝟙 _ := by
    rw [ht, map_one]
    rfl
  rw [IndData.inc_actHom_assoc, inc_twψ_assoc, inc_twψ, IndData.inc_actHom, hρ,
    Category.id_comp, Category.id_comp]
  congr 2
  rw [ht, map_one]
  group

end Twist


/-! ### Lifting homeomorphisms of `Z₁` to `Z̃` -/

section LiftHomeo

variable {Z E : Type u} [TopologicalSpace Z] [TopologicalSpace E] {p : E → Z}

/-- **Lifting homeomorphisms** of the base to a universal covering, through prescribed points. -/
lemma exists_lift_homeo (hp : IsUniversalCovering.{u, u, u, u} p) (h : Z ≃ₜ Z) {e₁ e₂ : E}
    (he : p e₂ = h (p e₁)) : ∃ τ : E ≃ₜ E, (∀ e, p (τ e) = h (p e)) ∧ τ e₁ = e₂ := by
  have hpc := hp.isCoveringMap.continuous
  obtain ⟨f, hf, hpf, hfe⟩ := hp.exists_lift Z E p hp.isCoveringMap (h ∘ p)
    (h.continuous.comp hpc) e₁ e₂ he
  obtain ⟨f', hf', hpf', hfe'⟩ := hp.exists_lift Z E p hp.isCoveringMap (h.symm ∘ p)
    (h.symm.continuous.comp hpc) e₂ e₁
    (by rw [Function.comp_apply, he, Homeomorph.symm_apply_apply])
  have := hp.connectedSpace
  have h₁ : f' ∘ f = id := hp.isCoveringMap.eq_of_comp_eq (hf'.comp hf) continuous_id
    (by
      funext e
      have h₁ := congrFun hpf' (f e)
      have h₂ := congrFun hpf e
      simp only [Function.comp_apply] at h₁ h₂ ⊢
      rw [h₁, h₂, Homeomorph.symm_apply_apply]
      rfl) e₁ (by simp [hfe, hfe'])
  have h₂ : f ∘ f' = id := hp.isCoveringMap.eq_of_comp_eq (hf.comp hf') continuous_id
    (by
      funext e
      have h₁ := congrFun hpf (f' e)
      have h₂ := congrFun hpf' e
      simp only [Function.comp_apply] at h₁ h₂ ⊢
      rw [h₁, h₂, Homeomorph.apply_symm_apply]
      rfl) e₂ (by simp [hfe, hfe'])
  exact ⟨{ toFun := f, invFun := f', left_inv := congrFun h₁, right_inv := congrFun h₂
           continuous_toFun := hf, continuous_invFun := hf' }, fun e => congrFun hpf e, hfe⟩

end LiftHomeo

/-! ### The twisted automorphisms of `OrbGal.obj` -/

section Lift

variable [Subsingleton X₁.Lv.L.H] (hX : IndFaithful X₁)
  {E : Type u} [TopologicalSpace E] {p : E → X₁.Lv.Z}
  (hp : IsUniversalCovering.{u, u, u, u} p) (hc : ∀ z, (p ⁻¹' {z}).Countable)

/-- The element `(s, 1)` of the level group `S × 1` of the induced level. -/
def gS (s : D.S) : (D.lv hX).L.H := D.equivT hX (s, 1)

lemma gS_one : gS D hX (1 : D.S) = 1 := (D.equivT hX).map_one

lemma gS_mul (s s' : D.S) : gS D hX s * gS D hX s' = gS D hX (s * s') :=
  ((D.equivT hX).map_mul (s, 1) (s', 1)).symm.trans
    (congrArg _ (Prod.ext rfl (mul_one 1)))

/-- The coded covering space of `OrbGal.obj` is `Ind_1^S Z̃`. -/
abbrev Θo : IndSpace (D.lv hX) E ≃ₜ (obj D hX hp hc).P.carrier :=
  Θ (D.lv hX) (isUniversalCovering_proj D hX hp) (countable_proj D hX hc)

lemma coe_indProj (s : D.S) (e : E) :
    (indProj (proj D hX p) (⟨gS D hX s, e⟩ : IndSpace (D.lv hX) E)).1 =
      D.inc s (p e : X₁.Lv.c.scheme) := by
  change D.actHom ((D.equivT hX).symm (D.equivT hX (s, 1))) (D.inc 1 (p e : X₁.Lv.c.scheme)) = _
  rw [MulEquiv.symm_apply_apply, ← Scheme.Hom.comp_apply, IndData.inc_actHom]
  have h1 : ((s, 1) : D.T).2 = 1 := rfl
  rw [h1, map_one, map_one, inv_one, mul_one, mul_one]
  change (𝟙 _ ≫ D.inc s) _ = _
  rw [Category.id_comp]

variable (c : D.S) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α c)
  {ψγ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme} (hψγ : ψγ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec)
  (hjγ : X₁.Lv.j ≫ ψγ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
  {τ : E → E} (hτc : Continuous τ) (hτ : ∀ e, p (τ e) = specialFibreMap ψγ hψγ (p e))

/-- The lift `e ↦ (c, τ e)` of `ψ ∘ p` to the covering space of `OrbGal.obj`. -/
def twS (τ : E → E) (e : E) : (obj D hX hp hc).P.carrier := Θo D hX hp hc ⟨gS D hX c, τ e⟩

include hτc in
lemma continuous_twS : Continuous (twS D hX hp hc c τ) :=
  (Θo D hX hp hc).continuous.comp
    ((continuous_sigmaMk (σ := fun _ : (D.lv hX).L.H => E) (i := gS D hX c)).comp hτc)

include hτ in
lemma twS_fst (e : E) : (twS D hX hp hc c τ e).1.1 =
    (twℓ D c γ hγ hX hψγ hjγ).ψs (proj D hX p e) := by
  apply Subtype.ext
  change (indProj (proj D hX p) (⟨gS D hX c, τ e⟩ : IndSpace (D.lv hX) E)).1 = _
  rw [coe_indProj, LevelHom.coe_ψs, hτ, coe_specialFibreMap]
  change _ = twψ D c ψγ (D.inc 1 (p e : X₁.Lv.c.scheme))
  rw [← Scheme.Hom.comp_apply (D.inc 1), inc_twψ, one_mul, Scheme.Hom.comp_apply]

/-- **The twisted automorphism** of `OrbGal.obj`: `(c, γ)` on the level, `ψ_γ` on the model,
`(1, e) ↦ (c, τ e)` on the covering space. -/
def twHom : obj D hX hp hc ⟶ obj D hX hp hc :=
  liftHom (isUniversalCovering_proj D hX hp) (countable_proj D hX hc)
    (twℓ D c γ hγ hX hψγ hjγ) (twℓ_isEquivariant D c γ hγ hX hψγ hjγ)
    (continuous_twS D hX hp hc c hτc) (twS_fst D hX hp hc c γ hγ hψγ hjγ hτ)

lemma twHom_φ : (twHom D hX hp hc c γ hγ hψγ hjγ hτc hτ).φ = twφ D c γ hγ hX := rfl

lemma twHom_ψ : (twHom D hX hp hc c γ hγ hψγ hjγ hτc hτ).ψ = twψ D c ψγ := rfl

lemma twHom_h (g : (D.lv hX).L.H) (e : E) :
    (twHom D hX hp hc c γ hγ hψγ hjγ hτc hτ).h (Θo D hX hp hc ⟨g, e⟩) =
      Θo D hX hp hc ⟨g * gS D hX c, τ e⟩ := by
  change liftInd (twℓ D c γ hγ hX hψγ hjγ) (twS D hX hp hc c τ)
    ((Θo D hX hp hc).symm (Θo D hX hp hc ⟨g, e⟩)) = _
  rw [Homeomorph.symm_apply_apply]
  change (obj D hX hp hc).P.act g (Θo D hX hp hc ⟨gS D hX c, τ e⟩) = _
  exact act_Θ g _

lemma twHom_h_one (e : E) :
    (twHom D hX hp hc c γ hγ hψγ hjγ hτc hτ).h (Θo D hX hp hc ⟨1, e⟩) =
      Θo D hX hp hc ⟨gS D hX c, τ e⟩ := by
  rw [twHom_h, one_mul]

end Lift

end OrbGal

end

end TemperedFundamentalGroups
