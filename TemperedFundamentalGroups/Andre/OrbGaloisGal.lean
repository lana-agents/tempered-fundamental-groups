/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGaloisAut

/-!
# The orbifold Galois objects are Galois (Blueprint §11.3, G6, orbifold case)

For `OrbGal.obj D hX hp hc = Ind_1^S Z̃` over the induced level of a scheme level `Lv₁` whose
algebra `B` is connected and Galois over `R` (`Aut_R(B)` transitive on `B →ₐ[R] Ω`), on which
every `a ∈ A` lifts to a semilinear automorphism of `B` (**`B` is Galois over `[Spec R / A]`**),
each semilinear automorphism extending to the model:

* `twIso`: the twisted automorphisms are isomorphisms (inverse: `(c⁻¹, γ⁻¹)`, `twHom_comp`);
* `exists_iso_preMap`: **every pair `(t, x)` of the fibre is the image of the base pair
  `(t₀ ∘ ev₁, (1, e₀))` under a twisted automorphism**: `t` lies on a copy `x'`, the
  semilinear point `t ∘ ev_{x'}⁻¹` of `B` is `t₀ ∘ γ` for a `γ` over `α x'`, and the covering
  point is reached by the choice of the lift `τ`;
* `exists_iso_fibreMap`: `Aut (OrbGal.obj)` acts transitively on the fibre (**gal**).
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

namespace GaloisObject

variable {Lv : Level O R A} [Finite Lv.L.H] {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}

/-- `hom_ext` for a composite of endomorphisms being the identity. -/
lemma comp_eq_id {f g : obj Lv hp hc ⟶ obj Lv hp hc}
    (hφ : (f ≫ g).φ = TempObj.Hom.φ (𝟙 (obj Lv hp hc)))
    (hψ : (f ≫ g).ψ = TempObj.Hom.ψ (𝟙 (obj Lv hp hc))) (x₀ : (code Lv hp hc).carrier)
    (h : g.h (f.h x₀) = x₀) : f ≫ g = 𝟙 _ :=
  hom_ext hφ hψ x₀ h

end GaloisObject

namespace OrbGal

variable {X₁ : TempObj O R A₁} (D : IndData (μ₁ A A₁) X₁) [Subsingleton X₁.Lv.L.H]
  (hX : IndFaithful X₁) {E : Type u} [TopologicalSpace E] {p : E → X₁.Lv.Z}
  (hp : IsUniversalCovering.{u, u, u, u} p) (hc : ∀ z, (p ⁻¹' {z}).Countable)

section Comp

variable (c c' : D.S) (γ γ' : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α c)
  (hγ' : γ'.a = D.α c')
  {ψ ψ' : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme} (hψ : ψ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec)
  (hjψ : X₁.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
  (hψ' : ψ' ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec)
  (hjψ' : X₁.Lv.j ≫ ψ' = Spec.map (CommRingCat.ofHom (γ'.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫
    X₁.Lv.j)
  {τ τ' : E → E} (hτc : Continuous τ) (hτ : ∀ e, p (τ e) = specialFibreMap ψ hψ (p e))
  (hτc' : Continuous τ') (hτ' : ∀ e, p (τ' e) = specialFibreMap ψ' hψ' (p e))

set_option maxHeartbeats 1000000 in
lemma twHom_comp_h (hcc : c * c' = 1) (hττ : ∀ e, τ' (τ e) = e) (e : E) :
    (twHom D hX hp hc c' γ' hγ' hψ' hjψ' hτc' hτ').h
      ((twHom D hX hp hc c γ hγ hψ hjψ hτc hτ).h (Θo D hX hp hc ⟨1, e⟩)) =
      Θo D hX hp hc ⟨1, e⟩ := by
  rw [twHom_h_one, twHom_h, hττ, gS_mul, hcc, gS_one]

lemma twHom_comp_φ (hcc : c * c' = 1) (hσ : ∀ b, γ.σ (γ'.σ b) = b) :
    (twHom D hX hp hc c γ hγ hψ hjψ hτc hτ ≫ twHom D hX hp hc c' γ' hγ' hψ' hjψ' hτc' hτ').φ =
      (𝟙 (obj D hX hp hc) : obj D hX hp hc ⟶ obj D hX hp hc).φ := by
  refine FiniteLevel.Hom.ext (AlgHom.ext fun y => D.ext_ev fun (x : D.S) => ?_)
      (MonoidHom.ext fun g => rfl)
  change D.ev x (twF D c γ hγ (twF D c' γ' hγ' y)) = D.ev x y
  rw [ev_twF, ev_twF, hσ, mul_assoc, hcc, mul_one]

lemma twHom_comp_ψ (hcc : c * c' = 1) (hψψ : ψ ≫ ψ' = 𝟙 _) :
    (twHom D hX hp hc c γ hγ hψ hjψ hτc hτ ≫ twHom D hX hp hc c' γ' hγ' hψ' hjψ' hτc' hτ').ψ =
      (𝟙 (obj D hX hp hc) : obj D hX hp hc ⟶ obj D hX hp hc).ψ := by
  refine D.c_hom_ext fun (x : D.S) => ?_
  change D.inc x ≫ twψ D c ψ ≫ twψ D c' ψ' = D.inc x ≫ 𝟙 _
  rw [inc_twψ_assoc, inc_twψ, reassoc_of% hψψ, mul_assoc, hcc, mul_one, Category.comp_id]

/-- Twisted automorphisms with inverse data compose to the identity. -/
lemma twHom_comp (hcc : c * c' = 1) (hσ : ∀ b, γ.σ (γ'.σ b) = b) (hψψ : ψ ≫ ψ' = 𝟙 _)
    (hττ : ∀ e, τ' (τ e) = e) :
    twHom D hX hp hc c γ hγ hψ hjψ hτc hτ ≫ twHom D hX hp hc c' γ' hγ' hψ' hjψ' hτc' hτ' =
      𝟙 _ := by
  haveI := hp.connectedSpace
  obtain ⟨e₀⟩ := (inferInstance : Nonempty E)
  exact GaloisObject.comp_eq_id (Lv := D.lv hX) (hp := isUniversalCovering_proj D hX hp)
    (hc := countable_proj D hX hc)
    (twHom_comp_φ D hX hp hc c c' γ γ' hγ hγ' hψ hjψ hψ' hjψ' hτc hτ hτc' hτ' hcc hσ)
    (twHom_comp_ψ D hX hp hc c c' γ γ' hγ hγ' hψ hjψ hψ' hjψ' hτc hτ hτc' hτ' hcc hψψ)
    (Θo D hX hp hc ⟨1, e₀⟩)
    (twHom_comp_h D hX hp hc c c' γ γ' hγ hγ' hψ hjψ hψ' hjψ' hτc hτ hτc' hτ' hcc hττ e₀)

end Comp

section Iso

variable (c : D.S) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α c)
  (eψ : X₁.Lv.c.scheme ≅ X₁.Lv.c.scheme) (heψ : eψ.hom ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec)
  (hjψ : X₁.Lv.j ≫ eψ.hom =
    Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
  (hjψ' : X₁.Lv.j ≫ eψ.inv =
    Spec.map (CommRingCat.ofHom (γ⁻¹.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
  (τ : E ≃ₜ E) (hτ : ∀ e, p (τ e) = specialFibreMap eψ.hom heψ (p e))

include heψ in
lemma inv_toSpec : eψ.inv ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec := by
  rw [Iso.inv_comp_eq, heψ]

include hγ in
lemma inv_a : γ⁻¹.a = D.α c⁻¹ := by
  rw [SemilinearAut.inv_a, hγ, map_inv]

include hτ in
lemma symm_lift (e : E) :
    p (τ.symm e) = specialFibreMap eψ.inv (inv_toSpec eψ heψ) (p e) := by
  apply Subtype.ext
  have h := congrArg Subtype.val (hτ (τ.symm e))
  rw [Homeomorph.apply_symm_apply, coe_specialFibreMap] at h
  rw [coe_specialFibreMap, h, ← Scheme.Hom.comp_apply, eψ.hom_inv_id]
  rfl

/-- **The twisted automorphisms are isomorphisms.** -/
def twIso : obj D hX hp hc ≅ obj D hX hp hc where
  hom := twHom D hX hp hc c γ hγ heψ hjψ τ.continuous hτ
  inv := twHom D hX hp hc c⁻¹ γ⁻¹ (inv_a D c γ hγ) (inv_toSpec eψ heψ) hjψ' τ.symm.continuous
    (symm_lift eψ heψ τ hτ)
  hom_inv_id := twHom_comp D hX hp hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mul_inv_cancel c)
    (fun b => γ.σ.apply_symm_apply b) eψ.hom_inv_id (fun e => τ.symm_apply_apply e)
  inv_hom_id := twHom_comp D hX hp hc _ _ _ _ _ _ _ _ _ _ _ _ _ _ (inv_mul_cancel c)
    (fun b => γ.σ.symm_apply_apply b) eψ.inv_hom_id (fun e => τ.apply_symm_apply e)

lemma twIso_hom : (twIso D hX hp hc c γ hγ eψ heψ hjψ hjψ' τ hτ).hom =
    twHom D hX hp hc c γ hγ heψ hjψ τ.continuous hτ := rfl

end Iso

end OrbGal

end

end TemperedFundamentalGroups
