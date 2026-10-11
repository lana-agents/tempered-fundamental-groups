/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGaloisClass

/-!
# Level maps out of induced levels (Blueprint §11.3, G6, orbifold case)

Let `D` be induction data `(S, α)` over a scheme level `Lv₁` (trivial `H`, algebra `B₁`). A
level `Y.Lv = (B_Y, H_Y)` of `[Spec R / A]` receives an equivariant morphism of levels with
models from the induced level `(Π_{x : S} B₁^{(α x)}, S)` (`OrbGal.indℓ`) given

* an `R`-algebra map `m : B_Y → B₁`,
* a homomorphism `θ : S →* H_Y` over `A` (`(θ s).a = α s`),
* a model map `dom : 𝒯₁ → 𝒯_Y` over `O` with `j₁ ≫ dom = Spec m ≫ j_Y`:

on algebras `b ↦ (x ↦ m (σ_{θ x}⁻¹ b))`, on groups `(s, 1) ↦ θ s`, on models the copy `x` goes
to `𝒯_Y` through `ρ(θ x) ∘ dom`. At the copy `1` it is `m` (`ev₁_indF`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A₁ : Type u} [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

namespace OrbGal

variable {X₁ : TempObj O R A₁} (D : IndData (μ₁ A A₁) X₁) [Subsingleton X₁.Lv.L.H]
  (hX : IndFaithful X₁) {Y : TempObj O R A}
  (m : Y.Lv.L.B →ₐ[R] X₁.Lv.L.B) (θ : D.S →* Y.Lv.L.H)
  (hθ : ∀ s, ((θ s : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B).a = D.α s)

/-- The component at the copy `x`: `b ↦ m (σ_{θ x}⁻¹ b)`, `R`-linear into `B₁^{(α x)}`. -/
def indComp (x : D.S) : Y.Lv.L.B →ₐ[R] TwAlg X₁.Lv.L.B (D.α x) :=
  { (m : Y.Lv.L.B →+* X₁.Lv.L.B).comp
      (((θ x : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B).σ.symm : Y.Lv.L.B →+* Y.Lv.L.B) with
    commutes' := fun r => by
      change m (((θ x : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B)⁻¹.σ (algebraMap R _ r)) =
        algebraMap R X₁.Lv.L.B ((D.α x)⁻¹ • r)
      rw [SemilinearAut.map_algebraMap, SemilinearAut.inv_a, hθ, AlgHom.commutes] }

/-- **The algebra map of the induced level morphism.** -/
def indF : Y.Lv.L.B →ₐ[R] D.level.B :=
  D.E.symm.toAlgHom.comp (AlgHom.pi (indComp D m θ hθ))

lemma ev_indF (x : D.S) (b : Y.Lv.L.B) :
    D.ev x (indF D m θ hθ b) =
      m (((θ x : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B).σ.symm b) := by
  change ((D.E (D.E.symm _) : D.Alg) x : X₁.Lv.L.B) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

lemma ev₁_indF (b : Y.Lv.L.B) : D.ev 1 (indF D m θ hθ b) = m b := by
  rw [ev_indF, map_one]
  rfl

/-- The group homomorphism `(s, 1) ↦ θ s`. -/
def indR : D.level.H →* Y.Lv.L.H :=
  θ.comp ((MonoidHom.fst _ _).comp (D.equivT hX).symm.toMonoidHom)

lemma indR_equivT (t : D.T) : indR D hX θ (D.equivT hX t) = θ t.1 := by
  simp [indR]

/-- **The morphism of levels.** -/
def indφ : D.level ⟶ Y.Lv.L where
  f := indF D m θ hθ
  r := indR D hX θ
  r_a g := by
    obtain ⟨t, rfl⟩ := (D.equivT hX).surjective g
    rw [indR_equivT, hθ]
    rfl
  f_σ g b := by
    obtain ⟨t, rfl⟩ := (D.equivT hX).surjective g
    refine D.ext_ev fun (x : D.S) => ?_
    have ht : t.2 = 1 := Subsingleton.elim _ _
    rw [indR_equivT, IndData.ev_equivT, ht, ev_indF, ev_indF, map_one, mul_one]
    change m _ = m _
    congr 1
    simp [SemilinearAut.mul_σ, SemilinearAut.inv_σ]

variable {dom : X₁.Lv.c.scheme ⟶ Y.Lv.c.scheme}

/-- The model map: the copy `x` goes to `𝒯_Y` through `ρ(θ x) ∘ dom`. -/
def indψ (dom : X₁.Lv.c.scheme ⟶ Y.Lv.c.scheme) : D.c.scheme ⟶ Y.Lv.c.scheme :=
  (SemistableReduction.ModelCode.sigmaIso (fun _ : D.S => X₁.Lv.c)).inv ≫
    Sigma.desc fun (x : D.S) => dom ≫ (Y.Lv.ρ (θ x)).hom

@[reassoc]
lemma inc_indψ (x : D.S) : D.inc x ≫ indψ D θ dom = dom ≫ (Y.Lv.ρ (θ x)).hom := by
  simp only [indψ, SemistableReduction.ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ _

variable (hdS : dom ≫ Y.Lv.c.toSpec = X₁.Lv.c.toSpec)
  (hdj : X₁.Lv.j ≫ dom = Spec.map (CommRingCat.ofHom (m : Y.Lv.L.B →+* X₁.Lv.L.B)) ≫ Y.Lv.j)

include hdS in
lemma indψ_toSpec : indψ D θ dom ≫ Y.Lv.c.toSpec = D.c.toSpec :=
  D.c_hom_ext fun (x : D.S) => by
    rw [inc_indψ_assoc, Y.Lv.ρ_toSpec, hdS, IndData.inc_toSpec]

include hdj in
lemma j_indψ : D.j ≫ indψ D θ dom =
    Spec.map (CommRingCat.ofHom (indF D m θ hθ : Y.Lv.L.B →+* D.level.B)) ≫ Y.Lv.j := by
  refine D.hom_ext fun (x : D.S) => ?_
  have hring : (D.ev x).comp (indF D m θ hθ : Y.Lv.L.B →+* D.level.B) =
      (m : Y.Lv.L.B →+* X₁.Lv.L.B).comp
        (((θ x : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B).σ.symm : Y.Lv.L.B →+* Y.Lv.L.B) :=
    RingHom.ext fun b => ev_indF D m θ hθ x b
  rw [IndData.specMap_ev_j_assoc, inc_indψ, ← Category.assoc, hdj, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, Category.assoc, Y.Lv.ρ_j]

/-- **The equivariant morphism of levels with models out of the induced level.** -/
def indℓ : LevelHom O R A (D.lv hX) Y.Lv where
  φ := indφ D hX m θ hθ
  ψ := indψ D θ dom
  ψ_toSpec := indψ_toSpec D θ hdS
  j_ψ := j_indψ D m θ hθ hdj

lemma indℓ_isEquivariant : (indℓ D hX m θ hθ hdS hdj).IsEquivariant := by
  intro g
  obtain ⟨t, rfl⟩ := (D.equivT hX).surjective g
  have ht : t.2 = 1 := Subsingleton.elim _ _
  change D.actHom ((D.equivT hX).symm (D.equivT hX t)) ≫ indψ D θ dom =
    indψ D θ dom ≫ (Y.Lv.ρ (indR D hX θ (D.equivT hX t))).hom
  rw [MulEquiv.symm_apply_apply, indR_equivT]
  refine D.c_hom_ext fun (x : D.S) => ?_
  have hρ : (X₁.Lv.ρ t.2).hom = 𝟙 _ := by
    rw [ht, map_one]
    rfl
  rw [IndData.inc_actHom_assoc, inc_indψ, inc_indψ_assoc, hρ, Category.id_comp, ht,
    β_eq_one D (1 : X₁.Lv.L.H), inv_one, mul_one, map_mul, map_mul, Aut.Aut_mul_def,
    Iso.trans_hom]

end OrbGal

end

end TemperedFundamentalGroups
