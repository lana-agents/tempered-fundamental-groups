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

lemma act_gS_Θo (x : D.S) (e : E) :
    (obj D hX hp hc).P.act (gS D hX x) (Θo D hX hp hc ⟨1, e⟩) = Θo D hX hp hc ⟨gS D hX x, e⟩ := by
  refine (act_Θ (gS D hX x) _).trans ?_
  rw [indAct_apply, mul_one]
  rfl

lemma ev_gS_symm (x : D.S) (y : D.level.B) :
    D.ev 1 (((gS D hX x : (D.lv hX).L.H) : SemilinearAut R A (D.lv hX).L.B).σ.symm y) =
      D.ev x y := by
  have h := IndData.ev_equivT_symm D hX (x, 1) 1 y
  rw [map_one, inv_one, mul_one, mul_one] at h
  exact h

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

set_option maxHeartbeats 1600000 in
-- unifying the algebra instances of `D.level.B` and `(obj D hX hp hc).Lv.L.B` is slow
/-- Untwisted pairs on a copy `x ∈ ker α` are `H⁰`-equivalent to pairs on the copy `1`. -/
lemma tw_quot (x : D.S) (hx : D.α x = 1) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α x)
    (hγ1 : ∀ b, γ.σ b = b) (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (q' q : PreFibre Ω V hV (obj D hX hp hc))
    (hq'₁ : (q'.1.1 : D.level.B →ₐ[R] Ω) = t₀.comp D.ev₁)
    (hq₁ : (q.1.1 : D.level.B →ₐ[R] Ω) = (t₀.comp D.ev₁).comp (twF D x γ hγ)) (e : E)
    (hq'₂ : q'.1.2 = Θo D hX hp hc ⟨1, e⟩) (hq₂ : q.1.2 = Θo D hX hp hc ⟨gS D hX x, e⟩) :
    (Quotient.mk _ q : Fibre Ω V hV (obj D hX hp hc)) = Quotient.mk _ q' := by
  have hmem : gS D hX x ∈ (D.lv hX).L.H0 := by
    rw [FiniteLevel.mem_H0]
    exact hx
  refine Quotient.sound ⟨⟨gS D hX x, hmem⟩, Subtype.ext (Prod.ext ?_ ?_)⟩
  · refine (congrArg Prod.fst (smul_val V hV _ _ q')).trans ?_
    refine AlgHom.ext fun y => ?_
    rw [FiniteLevel.fibreAct_apply, hq'₁, hq₁]
    exact (congrArg t₀ (ev_gS_symm D hX x y)).trans
      ((tw_apply D x γ hγ t₀ y).trans (congrArg t₀ (hγ1 _))).symm
  · refine (congrArg Prod.snd (smul_val V hV _ _ q')).trans ?_
    rw [hq'₂, hq₂]
    exact act_gS_Θo D hX hp hc x e

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

include hidem in
/-- A twisted level coordinate `H⁰`-equivalent to `t₀ ∘ ev₁` is untwisted: the copy is in
`ker α` and `γ` fixes `t₀`. -/
lemma tw_level_eq (x : D.S) (γ : SemilinearAut R A X₁.Lv.L.B) (hγ : γ.a = D.α x)
    (k : (D.lv hX).L.H0)
    (hk : FiniteLevel.fibreAct Ω _ k ((t₀.comp D.ev₁).comp (twF D x γ hγ)) = t₀.comp D.ev₁) :
    D.α x = 1 ∧ ∀ b, γ.σ b = b := by
  obtain ⟨⟨s, h⟩, hsh⟩ := (D.equivT hX).surjective k.1
  have hh : h = 1 := Subsingleton.elim _ _
  subst hh
  have hk0 := FiniteLevel.mem_H0.1 k.2
  rw [← hsh] at hk0
  have hαs : D.α s = 1 := hk0
  have hy : ∀ y, t₀ (γ.σ (D.ev (s * x) y)) = t₀ (D.ev 1 y) := fun y => by
    have := DFunLike.congr_fun hk y
    change t₀ (D.ev 1 (twF D x γ hγ ((((k : (D.lv hX).L.H) : SemilinearAut R A
      (D.lv hX).L.B)).σ.symm y))) = t₀ (D.ev 1 y) at this
    rw [← hsh] at this
    rw [ev_twF, one_mul] at this
    erw [IndData.ev_equivT_symm] at this
    rw [map_one, inv_one, mul_one] at this
    exact this
  have hsx : s * x = 1 := D.eq_of_comp_ev (t₀ := ((t₀ : X₁.Lv.L.B →+* Ω).comp
    (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B))) (t₁ := (t₀ : X₁.Lv.L.B →+* Ω))
    (RingHom.ext fun y => hy y)
  have hx : D.α x = 1 := by
    have := congrArg D.α hsx
    rw [map_mul, hαs, one_mul, map_one] at this
    exact this
  refine ⟨hx, fun b => ?_⟩
  have h1 : ∀ b, t₀ (γ.σ b) = t₀ b := fun b => by
    have := hy (D.single 1 b)
    rwa [hsx, IndData.ev_single_self] at this
  haveI := X₁.Lv.L.etale
  have h2 := algHom_eq_of_comp_eq hidem (algEquivOfA γ (hγ.trans hx) :
    X₁.Lv.L.B →ₐ[R] X₁.Lv.L.B) (AlgHom.id R _) t₀ (AlgHom.ext fun b => h1 b)
  exact DFunLike.congr_fun h2 b

lemma fibreAct_inv_mul (k : (D.lv hX).L.H0) (t : (D.lv hX).L.B →ₐ[R] Ω) :
    FiniteLevel.fibreAct Ω _ k⁻¹ (FiniteLevel.fibreAct Ω _ k t) = t := by
  rw [← FiniteLevel.fibreAct_mul, inv_mul_cancel, FiniteLevel.fibreAct_one]

set_option maxHeartbeats 1600000 in
-- unifying the algebra instances of `D.level.B` and `(obj D hX hp hc).Lv.L.B` is slow
include hidem hgal hsym hact he₀ in
/-- **An element of the stage group preserving the level class of the base point is a deck
transformation of `Z̃`.** -/
theorem mem_range_deckStageO_of_base (σ : stageGroup (tempFibre O R A V hV) (obj D hX hp hc))
    (hσ : SameLevel V hV D hX hp hc (σ.1 (Quotient.mk _ (basePre D hX hp hc V hV t₀ e₀ he₀)))
      (Quotient.mk _ (basePre D hX hp hc V hV t₀ e₀ he₀))) :
    σ ∈ (deckStageO V hV D hX hp hc).range := by
  let q₀ := basePre D hX hp hc V hV t₀ e₀ he₀
  obtain ⟨x, γ, hγ, eψ, heψ, hj, hj', τ, hτ, hq⟩ :=
    exists_iso_preMap D hX hp hc V hV hgal hsym hact t₀ e₀ he₀
      (Quotient.out (σ.1 (Quotient.mk _ q₀)))
  have hσu : σ.1 (Quotient.mk _ q₀) = Quotient.mk _ (preMap V hV
      (twIso D hX hp hc x γ hγ eψ heψ hj hj' τ hτ).hom q₀) :=
    (Quotient.out_eq _).symm.trans (congrArg (Quotient.mk _) hq.symm)
  obtain ⟨q₁, q₂, h₁, h₂, k, hk⟩ := hσ
  obtain ⟨g₁, hg₁⟩ := Quotient.exact (h₁.trans hσu)
  obtain ⟨g₂, hg₂⟩ := Quotient.exact h₂
  let g₁' : (D.lv hX).L.H0 := g₁
  let g₂' : (D.lv hX).L.H0 := g₂
  have e₁ : q₁.1.1 = FiniteLevel.fibreAct Ω _ g₁' ((t₀.comp D.ev₁).comp (twF D x γ hγ)) :=
    (congrArg (fun q => q.1.1) hg₁).symm
  have e₂ : q₂.1.1 = FiniteLevel.fibreAct Ω _ g₂' (t₀.comp D.ev₁) :=
    (congrArg (fun q => q.1.1) hg₂).symm
  rw [e₁, e₂] at hk
  have hk' : FiniteLevel.fibreAct Ω _ (g₂'⁻¹ * k * g₁')
      ((t₀.comp D.ev₁).comp (twF D x γ hγ)) = t₀.comp D.ev₁ := by
    rw [FiniteLevel.fibreAct_mul, FiniteLevel.fibreAct_mul, hk, fibreAct_inv_mul]
    rfl
  obtain ⟨hx, hγ1⟩ := tw_level_eq D hX hidem t₀ x γ hγ _ hk'
  -- the model automorphism is the identity
  have hψ1 : eψ.hom = 𝟙 _ := by
    refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated X₁.Lv.c.toSpec
      (by rw [heψ, Category.id_comp]) X₁.Lv.j ?_
    have hring : (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B) = RingHom.id _ := RingHom.ext hγ1
    rw [hj, hring, Category.comp_id]
    exact (congrArg (· ≫ X₁.Lv.j) (Spec.map_id _)).trans (Category.id_comp _)
  have hτd : ∀ e, proj D hX p (τ e) = proj D hX p e := fun e => by
    change D.inc₁S hX (p (τ e)) = D.inc₁S hX (p e)
    rw [hτ]
    congr 1
    apply Subtype.ext
    rw [coe_specialFibreMap, hψ1]
    rfl
  obtain ⟨τd, hτd'⟩ : ∃ τd : deckGroup (D.lv hX) (proj D hX p), τd.1 = τ := ⟨⟨τ, hτd⟩, rfl⟩
  subst hτd'
  refine ⟨τd, stage_ext V hV D hX hp hc hidem hgal hsym hact t₀ e₀ he₀
    (Quotient.mk _ q₀) ?_⟩
  have hq₀ : (basePre D hX hp hc V hV t₀ e₀ he₀).1.2 = Θo D hX hp hc ⟨1, e₀⟩ := rfl
  have hmk := deckStageO_mk V hV D hX hp hc τd (basePre D hX hp hc V hV t₀ e₀ he₀) 1 e₀ hq₀
  have hq₀def : q₀ = basePre D hX hp hc V hV t₀ e₀ he₀ := rfl
  clear_value q₀
  subst hq₀def
  obtain ⟨q', hq'₁, hq'₂, hq'⟩ := hmk
  refine hq'.trans (Eq.trans ?_ hσu.symm)
  exact (tw_quot V hV D hX hp hc x hx γ hγ hγ1 t₀ _ _ hq'₁ rfl (τd.1 e₀) hq'₂
    (twHom_h_one D hX hp hc x γ hγ heψ hj τd.1.continuous hτ e₀)).symm

set_option maxHeartbeats 1600000 in
-- see `mem_range_deckStageO_of_base`
include hidem hgal hsym hact he₀ in
/-- **The kernel of the action on level classes is the deck group**: an element of the stage
group of `OrbGal.obj` comes from a deck transformation of `Z̃` iff it preserves all level
classes. -/
theorem mem_range_deckStageO_iff (σ : stageGroup (tempFibre O R A V hV) (obj D hX hp hc)) :
    σ ∈ (deckStageO V hV D hX hp hc).range ↔ ∀ u, SameLevel V hV D hX hp hc (σ.1 u) u := by
  constructor
  · rintro ⟨τ, rfl⟩ u
    obtain ⟨q, rfl⟩ := Quotient.mk_surjective u
    obtain ⟨⟨g, e⟩, hge⟩ := (Θo D hX hp hc).surjective q.1.2
    obtain ⟨q', hq'₁, -, hq'⟩ := deckStageO_mk V hV D hX hp hc τ q g e hge.symm
    exact ⟨q', q, hq'.symm, rfl, 1, by rw [FiniteLevel.fibreAct_one]; exact hq'₁⟩
  · intro hσ
    exact mem_range_deckStageO_of_base V hV D hX hp hc hidem hgal hsym hact t₀ e₀ he₀ σ
      (hσ _)

end Main

end OrbGal

end

end TemperedFundamentalGroups
