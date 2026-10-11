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


section Main

variable [IsSchemeTheoreticallyDominant X₁.Lv.j]

lemma specMap_σ_inv (γ : SemilinearAut R A X₁.Lv.L.B) :
    Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫
      Spec.map (CommRingCat.ofHom (γ⁻¹.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B).comp (γ⁻¹.σ : X₁.Lv.L.B →+* X₁.Lv.L.B) =
      RingHom.id _ := RingHom.ext fun b => γ.σ.apply_symm_apply b
  rw [h]
  exact Spec.map_id _

/-- **Model isomorphisms**: if every semilinear automorphism of `B` extends to the model, the
extensions of `γ` and `γ⁻¹` are inverse (by dominance of `j`). -/
lemma exists_modelIso
    (hact : ∀ γ : SemilinearAut R A X₁.Lv.L.B, ∃ ψ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme,
      ψ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec ∧
      X₁.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
    (γ : SemilinearAut R A X₁.Lv.L.B) :
    ∃ (eψ : X₁.Lv.c.scheme ≅ X₁.Lv.c.scheme) (_ : eψ.hom ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec),
      X₁.Lv.j ≫ eψ.hom =
        Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j ∧
      X₁.Lv.j ≫ eψ.inv =
        Spec.map (CommRingCat.ofHom (γ⁻¹.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j := by
  obtain ⟨ψ, hψ, hj⟩ := hact γ
  obtain ⟨ψ', hψ', hj'⟩ := hact γ⁻¹
  have h₁ : ψ ≫ ψ' = 𝟙 _ :=
    ext_of_isSchemeTheoreticallyDominant_of_isSeparated X₁.Lv.c.toSpec
      (by rw [Category.assoc, hψ', hψ, Category.id_comp]) X₁.Lv.j
      (by rw [reassoc_of% hj, hj', ← Category.assoc, specMap_σ_inv, Category.id_comp,
        Category.comp_id])
  have h₂ : ψ' ≫ ψ = 𝟙 _ :=
    ext_of_isSchemeTheoreticallyDominant_of_isSeparated X₁.Lv.c.toSpec
      (by rw [Category.assoc, hψ, hψ', Category.id_comp]) X₁.Lv.j
      (by
        rw [reassoc_of% hj', hj, ← Category.assoc, Category.comp_id]
        have := specMap_σ_inv γ⁻¹
        rw [inv_inv] at this
        rw [this, Category.id_comp])
  exact ⟨⟨ψ, ψ', h₁, h₂⟩, hψ, hj, hj'⟩

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The base pair** `(t₀ ∘ ev₁, (1, e₀))` of `OrbGal.obj`, for `e₀ ∈ Z̃` over the
specialization of a geometric point `t₀` of `B`. -/
def basePre (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (e₀ : E) (he₀ : p e₀ = X₁.Lv.sp V hV t₀) :
    PreFibre Ω V hV (obj D hX hp hc) :=
  ⟨(t₀.comp D.ev₁, Θo D hX hp hc ⟨1, e₀⟩), by
    refine (congrArg Subtype.val (Θ_fst (Lv := D.lv hX) (hp := isUniversalCovering_proj D hX hp)
      (hc := countable_proj D hX hc) _)).trans ?_
    refine (congrArg Subtype.val (indProj_one (proj D hX p) e₀)).trans ?_
    refine (IndData.inc₁S_coe D hX (p e₀)).trans ?_
    rw [he₀, ← IndData.sp_comp_ev₁]
    rfl⟩

lemma ev_algebraMap (x : D.S) (r : R) :
    D.ev x (algebraMap R D.level.B r) = algebraMap R X₁.Lv.L.B ((D.α x)⁻¹ • r) := by
  rw [IndData.ev_apply, AlgEquiv.commutes]
  rfl

/-- A geometric point on the copy `x` of the induced algebra is a semilinear point of `B` over
`α x`. -/
lemma onCopy_algebraMap (t : D.level.B →ₐ[R] Ω) (x : D.S)
    (hx : ((t : D.level.B →ₐ[R] Ω) : D.level.B →+* Ω) (D.idem x) = 1) (r : R) :
    D.onCopy ((t : D.level.B →ₐ[R] Ω) : D.level.B →+* Ω) x hx (algebraMap R X₁.Lv.L.B r) =
      algebraMap R Ω (D.α x • r) := by
  have h1 : D.ev x (algebraMap R D.level.B (D.α x • r)) = algebraMap R X₁.Lv.L.B r := by
    rw [ev_algebraMap, inv_smul_smul]
  rw [← h1, IndData.onCopy_ev]
  exact t.commutes _

/-- **A semilinear point over `a` is `t₀ ∘ γ`** for a semilinear automorphism `γ` over `a`, if
`B` is Galois over `R` and `a` lifts to a semilinear automorphism of `B`. -/
lemma exists_semilinear_comp
    (hgal : ∀ t t' : X₁.Lv.L.B →ₐ[R] Ω, ∃ σ : X₁.Lv.L.B ≃ₐ[R] X₁.Lv.L.B,
      t.comp (σ : X₁.Lv.L.B →ₐ[R] X₁.Lv.L.B) = t')
    (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (a : A) (γ₀ : SemilinearAut R A X₁.Lv.L.B) (hγ₀ : γ₀.a = a)
    (t' : X₁.Lv.L.B →+* Ω) (ht' : ∀ r, t' (algebraMap R X₁.Lv.L.B r) = algebraMap R Ω (a • r)) :
    ∃ γ : SemilinearAut R A X₁.Lv.L.B, γ.a = a ∧
      (t₀ : X₁.Lv.L.B →+* Ω).comp (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B) = t' := by
  let u : X₁.Lv.L.B →ₐ[R] Ω :=
    { t'.comp (γ₀.σ.symm : X₁.Lv.L.B →+* X₁.Lv.L.B) with
      commutes' := fun r => by
        change t' ((γ₀⁻¹).σ (algebraMap R X₁.Lv.L.B r)) = _
        rw [(γ₀⁻¹).map_algebraMap, ht', SemilinearAut.inv_a, hγ₀, smul_inv_smul] }
  obtain ⟨δ, hδ⟩ := hgal t₀ u
  let δ' : SemilinearAut R A X₁.Lv.L.B :=
    ⟨1, δ.toRingEquiv, fun r => by
      rw [one_smul]
      exact δ.commutes r⟩
  refine ⟨δ' * γ₀, by rw [SemilinearAut.mul_a, hγ₀, one_mul], RingHom.ext fun b => ?_⟩
  change t₀ (δ (γ₀.σ b)) = t' b
  have := DFunLike.congr_fun hδ (γ₀.σ b)
  change t₀ (δ (γ₀.σ b)) = t' (γ₀.σ.symm (γ₀.σ b)) at this
  rw [this, RingEquiv.symm_apply_apply]

set_option maxHeartbeats 1000000 in
/-- **Every pair is a twisted translate of the base pair**: for every pair `q` of the fibre of
`OrbGal.obj` there is an automorphism mapping the base pair `(t₀ ∘ ev₁, (1, e₀))` to `q`. -/
theorem exists_iso_preMap
    (hgal : ∀ t t' : X₁.Lv.L.B →ₐ[R] Ω, ∃ σ : X₁.Lv.L.B ≃ₐ[R] X₁.Lv.L.B,
      t.comp (σ : X₁.Lv.L.B →ₐ[R] X₁.Lv.L.B) = t')
    (hsym : ∀ a : A, ∃ γ : SemilinearAut R A X₁.Lv.L.B, γ.a = a)
    (hact : ∀ γ : SemilinearAut R A X₁.Lv.L.B, ∃ ψ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme,
      ψ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec ∧
      X₁.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
    (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (e₀ : E) (he₀ : p e₀ = X₁.Lv.sp V hV t₀)
    (q : PreFibre Ω V hV (obj D hX hp hc)) :
    ∃ (x : D.S) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α x)
      (eψ : X₁.Lv.c.scheme ≅ X₁.Lv.c.scheme) (heψ : eψ.hom ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec)
      (hj : X₁.Lv.j ≫ eψ.hom =
        Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
      (hj' : X₁.Lv.j ≫ eψ.inv =
        Spec.map (CommRingCat.ofHom (γ⁻¹.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
      (τ : E ≃ₜ E) (hτ : ∀ e, p (τ e) = specialFibreMap eψ.hom heψ (p e)),
      preMap V hV (twIso D hX hp hc x γ hγ eψ heψ hj hj' τ hτ).hom
        (basePre D hX hp hc V hV t₀ e₀ he₀) = q := by
  obtain ⟨⟨t, x⟩, hq⟩ := q
  obtain ⟨⟨g, e⟩, rfl⟩ := (Θo D hX hp hc).surjective x
  obtain ⟨⟨s, k⟩, rfl⟩ := (D.equivT hX).surjective g
  obtain rfl : k = 1 := Subsingleton.elim _ _
  let tt : D.level.B →ₐ[R] Ω := t
  obtain ⟨x', hx'⟩ := D.exists_idem (tt : D.level.B →+* Ω)
  obtain ⟨γ₀, hγ₀⟩ := hsym (D.α x')
  obtain ⟨γ, hγ, hγt⟩ := exists_semilinear_comp hgal t₀ (D.α x') γ₀ hγ₀ _
    (onCopy_algebraMap D tt x' hx')
  obtain ⟨eψ, heψ, hj, hj'⟩ := exists_modelIso hact γ
  -- the level part
  have htF : (t₀.comp D.ev₁).comp (twF D x' γ hγ) = t := by
    refine AlgHom.ext fun y => ?_
    change t₀ (D.ev 1 (twF D x' γ hγ y)) = t y
    rw [ev_twF, one_mul]
    exact (RingHom.congr_fun hγt _).trans (IndData.onCopy_ev _ _ _ _ _)
  -- the specialization of `t`
  have hsp : ((D.lv hX).sp V hV t).1 = D.inc x' (eψ.hom (p e₀).1) := by
    have h := LevelHom.ψ_sp V hV (twℓ D x' γ hγ hX heψ hj) (t₀.comp D.ev₁)
    rw [← htF]
    refine h.symm.trans ?_
    change twψ D x' eψ.hom ((D.lv hX).sp V hV (t₀.comp D.ev₁)).1 = _
    rw [IndData.sp_comp_ev₁, ← he₀, ← Scheme.Hom.comp_apply, inc_twψ, one_mul]
    rfl
  have hq' : D.inc s (p e).1 = D.inc x' (eψ.hom (p e₀).1) := by
    rw [← hsp, ← coe_indProj D hX s e]
    exact hq
  have hs : s = x' := D.inc_eq_inc hq'
  subst hs
  have hpe : p e = specialFibreHomeomorph eψ heψ (p e₀) :=
    Subtype.ext ((D.inc s).isOpenEmbedding.injective hq')
  obtain ⟨τ, hτ, hτe⟩ := exists_lift_homeo hp (specialFibreHomeomorph eψ heψ) hpe
  refine ⟨s, γ, hγ, eψ, heψ, hj, hj', τ, hτ, Subtype.ext (Prod.ext htF ?_)⟩
  refine (twHom_h_one D hX hp hc s γ hγ heψ hj τ.continuous hτ e₀).trans ?_
  rw [hτe]
  rfl

/-- **`OrbGal.obj` is Galois**: its automorphisms act transitively on its fibre. -/
theorem exists_iso_fibreMap
    (hgal : ∀ t t' : X₁.Lv.L.B →ₐ[R] Ω, ∃ σ : X₁.Lv.L.B ≃ₐ[R] X₁.Lv.L.B,
      t.comp (σ : X₁.Lv.L.B →ₐ[R] X₁.Lv.L.B) = t')
    (hsym : ∀ a : A, ∃ γ : SemilinearAut R A X₁.Lv.L.B, γ.a = a)
    (hact : ∀ γ : SemilinearAut R A X₁.Lv.L.B, ∃ ψ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme,
      ψ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec ∧
      X₁.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
    (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (e₀ : E) (he₀ : p e₀ = X₁.Lv.sp V hV t₀)
    (u v : Fibre Ω V hV (obj D hX hp hc)) :
    ∃ σ : obj D hX hp hc ≅ obj D hX hp hc, fibreMap V hV σ.hom u = v := by
  obtain ⟨q₁, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨q₂, rfl⟩ := Quotient.mk_surjective v
  obtain ⟨x₁, γ₁, hγ₁, e₁, he₁, hj₁, hj₁', τ₁, hτ₁, hF₁⟩ :=
    exists_iso_preMap D hX hp hc V hV hgal hsym hact t₀ e₀ he₀ q₁
  obtain ⟨x₂, γ₂, hγ₂, e₂, he₂, hj₂, hj₂', τ₂, hτ₂, hF₂⟩ :=
    exists_iso_preMap D hX hp hc V hV hgal hsym hact t₀ e₀ he₀ q₂
  refine ⟨(twIso D hX hp hc x₁ γ₁ hγ₁ e₁ he₁ hj₁ hj₁' τ₁ hτ₁).symm ≪≫
    twIso D hX hp hc x₂ γ₂ hγ₂ e₂ he₂ hj₂ hj₂' τ₂ hτ₂, congrArg (Quotient.mk _) ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, preMap_comp, ← hF₁, ← preMap_comp V hV
    (twIso D hX hp hc x₁ γ₁ hγ₁ e₁ he₁ hj₁ hj₁' τ₁ hτ₁).hom, Iso.hom_inv_id, preMap_id, hF₂]

end Main

end OrbGal

end

end TemperedFundamentalGroups
