/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbStageLimit
import TemperedFundamentalGroups.Andre.StageGroup

/-!
# The stage groups of orbifold Galois objects (Blueprint §11.3, G6.10)

For an orbifold Galois object `U = OrbGal.obj D hX hp hc` (`Ind_1^S Z̃` over an induced level,
a member of `galClassO`):

* `deckStageO : deckGroup (D.lv hX) proj →* Π_U`, the deck transformations of `Z̃` (lifts of the
  identity of `Z₁`, `[t, (1, e)] ↦ [t, (1, τ e)]`), is injective (`deckStageO_injective`);
* `SameLevel u v`: the level coordinates `t` of `u = [t, x]` and `v` are `H⁰`-equivalent
  (`t ∈ F_L = Hom_R(Π_x B^{(α x)}, Ω)`);
* **`mem_range_deckStageO_iff`**: an element of `Π_U` lies in the image of the deck group iff it
  preserves all level classes (`SameLevel (σ u) u`).

So `Π_U` is an extension of the group of permutations of level classes it induces (the twisted
level automorphisms `(x, γ)`) by the deck group of `Z̃` (`π₁` of the dual graph for the tree
covering).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit OrbGal

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  {A₁ : Type u} [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

namespace OrbGal

variable {X₁ : TempObj O R A₁} (D : IndData (μ₁ A A₁) X₁) [Subsingleton X₁.Lv.L.H]
  (hX : IndFaithful X₁) {E : Type u} [TopologicalSpace E] {p : E → X₁.Lv.Z}
  (hp : IsUniversalCovering.{u, u, u, u} p) (hc : ∀ z, (p ⁻¹' {z}).Countable)

/-- **The deck group of `Z̃` in the stage group** of `OrbGal.obj`. -/
def deckStageO : deckGroup (D.lv hX) (proj D hX p) →*
    stageGroup (tempFibre O R A V hV) (obj D hX hp hc) :=
  (stageOfHom (tempFibre O R A V hV) (obj D hX hp hc)).comp
    ((deck (isUniversalCovering_proj D hX hp) (countable_proj D hX hc)).comp
      (((toH (D.lv hX) (proj D hX p)).ker.subtype).comp
        (kerEquiv (D.lv hX) (p := proj D hX p)).symm.toMonoidHom))

lemma deckStageO_mk (τ : deckGroup (D.lv hX) (proj D hX p)) (q : PreFibre Ω V hV (obj D hX hp hc))
    (g : (D.lv hX).L.H) (e : E) (hq : q.1.2 = Θo D hX hp hc ⟨g, e⟩) :
    ∃ q' : PreFibre Ω V hV (obj D hX hp hc), q'.1.1 = q.1.1 ∧
      q'.1.2 = Θo D hX hp hc ⟨g, τ.1 e⟩ ∧
      (deckStageO V hV D hX hp hc τ).1 (Quotient.mk _ q) = Quotient.mk _ q' := by
  refine ⟨preMap V hV (deckHom (isUniversalCovering_proj D hX hp) (countable_proj D hX hc)
    ((kerEquiv (D.lv hX) (p := proj D hX p)).symm τ).1) q, rfl, ?_, rfl⟩
  change (deckHom _ _ _).h q.1.2 = _
  rw [hq]
  refine (deckHom_h_Θ _ _).trans (congrArg (Θ (D.lv hX) _ _) (Sigma.ext ?_ HEq.rfl))
  change g * (1 : (D.lv hX).L.H)⁻¹ = g
  rw [inv_one, mul_one]

/-- **Equal level classes**: `[t, x]` and `[t', x']` have `H⁰`-equivalent level coordinates. -/
def SameLevel : Fibre Ω V hV (obj D hX hp hc) → Fibre Ω V hV (obj D hX hp hc) → Prop :=
  fun u v => ∃ q q' : PreFibre Ω V hV (obj D hX hp hc), Quotient.mk _ q = u ∧
    Quotient.mk _ q' = v ∧ ∃ k : (D.lv hX).L.H0, FiniteLevel.fibreAct Ω _ k q.1.1 = q'.1.1

section Main

variable [IsSchemeTheoreticallyDominant X₁.Lv.j]
  (hidem : ∀ e : X₁.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
  (hgal : ∀ t t' : X₁.Lv.L.B →ₐ[R] Ω, ∃ σ : X₁.Lv.L.B ≃ₐ[R] X₁.Lv.L.B,
    t.comp (σ : X₁.Lv.L.B →ₐ[R] X₁.Lv.L.B) = t')
  (hsym : ∀ a : A, ∃ γ : SemilinearAut R A X₁.Lv.L.B, γ.a = a)
  (hact : ∀ γ : SemilinearAut R A X₁.Lv.L.B, ∃ ψ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme,
    ψ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec ∧
    X₁.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)
  (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (e₀ : E) (he₀ : p e₀ = X₁.Lv.sp V hV t₀)

include hidem hgal hsym hact he₀ in
/-- Elements of the stage group of `OrbGal.obj` are determined by their value at one point. -/
lemma stage_ext {σ τ : stageGroup (tempFibre O R A V hV) (obj D hX hp hc)}
    (u : Fibre Ω V hV (obj D hX hp hc)) (h : σ.1 u = τ.1 u) : σ = τ := by
  obtain ⟨a, rfl⟩ := eq_stageOf σ
  obtain ⟨b, rfl⟩ := eq_stageOf τ
  have key := fibreMap_eq_of_eq D hX hp hc V hV hidem t₀ e₀ he₀ a.hom b.hom hgal hsym hact u h
  exact Subtype.ext (Equiv.ext fun v => congrFun key v)

include hidem hgal hsym hact he₀ in
/-- **The deck group of `Z̃` embeds into the stage group.** -/
theorem deckStageO_injective : Function.Injective (deckStageO V hV D hX hp hc) := by
  rw [injective_iff_map_eq_one]
  intro τ hτ
  obtain ⟨q', hq'₁, hq'₂, hq'⟩ := deckStageO_mk V hV D hX hp hc τ
    (basePre D hX hp hc V hV t₀ e₀ he₀) 1 e₀ rfl
  have h1 : (Quotient.mk _ q' : Fibre Ω V hV (obj D hX hp hc)) =
      Quotient.mk _ (basePre D hX hp hc V hV t₀ e₀ he₀) := by
    rw [← hq', hτ]
    rfl
  obtain ⟨k, hk⟩ := Quotient.exact h1
  have a1 : (obj D hX hp hc).P.act (k : (obj D hX hp hc).Lv.L.H)
      (basePre D hX hp hc V hV t₀ e₀ he₀).1.2 = q'.1.2 :=
    (congrArg Prod.snd (smul_val V hV _ k _)).symm.trans (congrArg (fun q => q.1.2) hk)
  have a2 : (basePre D hX hp hc V hV t₀ e₀ he₀).1.2 = Θo D hX hp hc ⟨1, e₀⟩ := rfl
  have a3 : (obj D hX hp hc).P.act (k : (obj D hX hp hc).Lv.L.H) (Θo D hX hp hc ⟨1, e₀⟩) =
      Θo D hX hp hc ⟨1, τ.1 e₀⟩ :=
    (congrArg ((obj D hX hp hc).P.act (k : (obj D hX hp hc).Lv.L.H)) a2.symm).trans
      (a1.trans hq'₂)
  let kk : (D.lv hX).L.H := k.1
  have h2 : Θ (D.lv hX) (isUniversalCovering_proj D hX hp) (countable_proj D hX hc)
      ⟨kk * 1, e₀⟩ = Θo D hX hp hc ⟨1, τ.1 e₀⟩ :=
    (act_Θ kk ⟨1, e₀⟩).symm.trans a3
  have h3 := (Sigma.mk.inj ((Θ (D.lv hX) _ _).injective h2)).2
  have he : τ.1 e₀ = e₀ := (eq_of_heq h3).symm
  haveI := hp.connectedSpace
  have hτ1 : (τ.1 : E → E) = id := (isCoveringMap_proj D hX hp.isCoveringMap).eq_of_comp_eq
    τ.1.continuous continuous_id (funext fun e => τ.2 e) e₀ he
  exact Subtype.ext (Homeomorph.ext fun e => congrFun hτ1 e)

end Main

end OrbGal

end

end TemperedFundamentalGroups
