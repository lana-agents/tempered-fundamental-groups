/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.StageGroup

/-!
# Functoriality of the stage groups (Blueprint §11.3, G6.4)

Scheme case, levels with trivial `H`.

* `stageLevel_transition`: the transition map of a pointed morphism `f` (with underlying morphism
  `F`) is compatible with the actions on level coordinates along `F_L → F_{L'}`, `t ↦ t ∘ φ.f`;
* `stageLevel_eq_one_of_apply_eq`: over a connected `B`, a stage group element fixing one level
  coordinate fixes all of them; hence `transition_mem_ker`: **transition maps send the deck
  subgroups (`ker stageLevel`) into the deck subgroups**;
* `treeMap F : Z̃ → Z̃'`: the map of universal coverings (of trees of the dual graphs) induced by a
  morphism `F : U_Lv ⟶ U_Lv'` (`p' ∘ treeMap F = ψ ∘ p`, `treeMap_spec`, `continuous_treeMap`);
* **`exists_deck_transition`**: for `U_Lv`, `U_Lv'` in a Galois class, a morphism `F` and a deck
  transformation `τ` of `Z̃`, the transition of `deckStage τ` along `F` is `deckStage τ'` for the
  unique deck transformation `τ'` of `Z̃'` with `τ' ∘ treeMap F = treeMap F ∘ τ`: the map of
  fundamental groups of dual graphs induced by the map of trees.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

section General

variable {X Y : TempObj O R A} [Subsingleton X.Lv.L.H] [Subsingleton Y.Lv.L.H]
  (hX : Function.Surjective (levelPt V hV X)) (hY : Function.Surjective (levelPt V hV Y))

/-- **Transition maps are compatible with level coordinates**: if `τ ∘ F = F ∘ σ` on fibres, then
`τ` acts on `t ∘ φ.f` as `σ` acts on `t`, composed with `φ.f`. -/
lemma stageLevel_comm (F : X ⟶ Y) (σ : stageGroup (tempFibre O R A V hV) X)
    (τ : stageGroup (tempFibre O R A V hV) Y)
    (h : ∀ x, τ.1 (fibreMap V hV F x) = fibreMap V hV F (σ.1 x)) (t : X.Lv.L.B →ₐ[R] Ω) :
    stageLevel V hV hY τ (t.comp F.φ.f) = (stageLevel V hV hX σ t).comp F.φ.f := by
  obtain ⟨x, rfl⟩ := hX t
  rw [← levelPt_fibreMap, stageLevel_levelPt, h, levelPt_fibreMap, stageLevel_levelPt]

/-- The transition map of a pointed morphism with underlying morphism `F`. -/
lemma stageLevel_transition {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
    {p q : PtGal (tempFibre O R A V hV) 𝒢} [Subsingleton p.G.Lv.L.H] [Subsingleton q.G.Lv.L.H]
    (hp : Function.Surjective (levelPt V hV p.G)) (hq : Function.Surjective (levelPt V hV q.G))
    (f : p ⟶ q) (F : p.G ⟶ q.G) (hF : fibreMap V hV F = f.1)
    (σ : stageGroup (tempFibre O R A V hV) p.G) (t : p.G.Lv.L.B →ₐ[R] Ω) :
    stageLevel V hV hq (transition hgal hrig f σ) (t.comp F.φ.f) =
      (stageLevel V hV hp σ t).comp F.φ.f :=
  stageLevel_comm V hV hp hq F σ _ (fun x ↦ by
    have := transition_comm hgal hrig f σ x
    rw [← hF] at this
    exact this) t

/-- Over a connected `B`, **a stage group element fixing one level coordinate fixes all**. -/
lemma stageLevel_eq_one_of_apply_eq
    (hidem : ∀ e : Y.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (τ : stageGroup (tempFibre O R A V hV) Y) {t : Y.Lv.L.B →ₐ[R] Ω}
    (ht : stageLevel V hV hY τ t = t) : stageLevel V hV hY τ = 1 := by
  haveI : Algebra.Etale R Y.Lv.L.B := Y.Lv.L.etale
  haveI : Module.Finite R Y.Lv.L.B := Y.Lv.L.finite
  obtain ⟨a, rfl⟩ := eq_stageOf τ
  have hconn : ∀ f₀ f₁ : Y.Lv.L.B →ₐ[R] Y.Lv.L.B, t.comp f₀ = t.comp f₁ → f₀ = f₁ :=
    fun f₀ f₁ h ↦ algHom_eq_of_comp_eq hidem f₀ f₁ t h
  have hf : (a.hom.φ.f : Y.Lv.L.B →ₐ[R] Y.Lv.L.B) = AlgHom.id R Y.Lv.L.B :=
    hconn _ _ ((stageLevel_stageOf V hV hY a t).symm.trans ht)
  refine Equiv.ext fun t' ↦ ?_
  rw [stageLevel_stageOf, hf]
  rfl

/-- **Transition maps preserve the deck subgroups** `ker stageLevel`. -/
theorem transition_mem_ker {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
    {p q : PtGal (tempFibre O R A V hV) 𝒢} [Subsingleton p.G.Lv.L.H] [Subsingleton q.G.Lv.L.H]
    (hp : Function.Surjective (levelPt V hV p.G)) (hq : Function.Surjective (levelPt V hV q.G))
    (hidem : ∀ e : q.G.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    [Nonempty (p.G.Lv.L.B →ₐ[R] Ω)] (f : p ⟶ q) {σ : stageGroup (tempFibre O R A V hV) p.G}
    (hσ : σ ∈ (stageLevel V hV hp).ker) :
    transition hgal hrig f σ ∈ (stageLevel V hV hq).ker := by
  obtain ⟨⟨F, hF⟩, -⟩ := f.2
  obtain ⟨t⟩ := ‹Nonempty (p.G.Lv.L.B →ₐ[R] Ω)›
  refine stageLevel_eq_one_of_apply_eq V hV hq hidem _ (t := t.comp F.φ.f) ?_
  rw [stageLevel_transition V hV hgal hrig hp hq f F hF, MonoidHom.mem_ker.1 hσ]
  rfl

end General

section Tree

variable {Lv Lv' : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H] [Finite Lv'.L.H]
  [Subsingleton Lv'.L.H]
  {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}
  {E' : Type u} [TopologicalSpace E'] {p' : E' → Lv'.Z}
  {hp' : IsUniversalCovering.{u, u, u, u} p'} {hc' : ∀ z, (p' ⁻¹' {z}).Countable}

/-- **The map of universal coverings** (trees of the dual graphs) induced by a morphism of Galois
objects: `e ↦` the `Z̃'`-coordinate of `F (1, e)`. -/
def treeMap (F : obj Lv hp hc ⟶ obj Lv' hp' hc') (e : E) : E' :=
  ((Θ Lv' hp' hc').symm (F.h (Θ Lv hp hc ⟨1, e⟩))).2

omit [Subsingleton Lv.L.H] in
lemma h_Θ_one (F : obj Lv hp hc ⟶ obj Lv' hp' hc') (e : E) :
    F.h (Θ Lv hp hc ⟨1, e⟩) = Θ Lv' hp' hc' ⟨1, treeMap F e⟩ := by
  rw [← (Θ Lv' hp' hc').apply_symm_apply (F.h _)]
  congr 1
  exact Sigma.ext (Subsingleton.elim _ _) HEq.rfl

omit [Subsingleton Lv.L.H] [Subsingleton Lv'.L.H] in
lemma continuous_treeMap (F : obj Lv hp hc ⟶ obj Lv' hp' hc') : Continuous (treeMap F) := by
  have h₁ : Continuous fun e : E ↦ Θ Lv hp hc ⟨1, e⟩ :=
    (Θ Lv hp hc).continuous.comp (continuous_sigmaMk (σ := fun _ : Lv.L.H ↦ E))
  have h₂ : Continuous fun x : GaloisObject.IndSpace Lv' E' ↦ x.2 :=
    continuous_sigma fun _ ↦ continuous_id
  exact h₂.comp ((Θ Lv' hp' hc').symm.continuous.comp (F.continuous_h.comp h₁))

omit [Subsingleton Lv.L.H] in
/-- `treeMap F` lies over the model map: `p' (treeMap F e) = ψ (p e)`. -/
lemma treeMap_spec (F : obj Lv hp hc ⟶ obj Lv' hp' hc') (e : E) :
    ((p' (treeMap F e) : Lv'.Z) : Lv'.c.scheme) = F.ψ ((p e : Lv.Z) : Lv.c.scheme) := by
  have h := F.fst_h (Θ Lv hp hc ⟨1, e⟩)
  rw [h_Θ_one] at h
  have h₁ := congrArg Subtype.val (Θ_fst (Lv := Lv') (hp := hp') (hc := hc') ⟨1, treeMap F e⟩)
  have h₂ := congrArg Subtype.val (Θ_fst (Lv := Lv) (hp := hp) (hc := hc) ⟨1, e⟩)
  rw [indProj_one] at h₁ h₂
  change ((Θ Lv' hp' hc' ⟨1, treeMap F e⟩).1.1 : Lv'.c.scheme) = _ at h
  rw [h₁] at h
  rw [h, ← h₂]

omit [Subsingleton Lv.L.H] in
/-- The image of `[t, (1, e)]` under a morphism of Galois objects. -/
lemma fibreMap_prePt (F : obj Lv hp hc ⟶ obj Lv' hp' hc') (t : Lv.L.B →ₐ[R] Ω) (e : E)
    (he : p e = Lv.sp V hV t) :
    ∃ he' : p' (treeMap F e) = Lv'.sp V hV (t.comp F.φ.f),
      fibreMap V hV F (Quotient.mk _ (prePt V hV t e he)) =
        Quotient.mk _ (prePt V hV (t.comp F.φ.f) (treeMap F e) he') := by
  have he' : p' (treeMap F e) = Lv'.sp V hV (t.comp F.φ.f) := by
    apply Subtype.ext
    rw [treeMap_spec, he]
    exact ψ_sp V hV F t
  refine ⟨he', ?_⟩
  change Quotient.mk _ (preMap V hV F _) = _
  congr 1
  exact Subtype.ext (Prod.ext rfl (h_Θ_one F e))

variable [Subsingleton A] [ConnectedSpace Lv.Z] [Nonempty E] [ConnectedSpace Lv'.Z] [Nonempty E']

omit [Subsingleton Lv.L.H] [Subsingleton A] [ConnectedSpace Lv'.Z] [Nonempty E'] in
/-- **The induced map of deck groups is the map of trees**: if `deckStage τ'` and `deckStage τ`
are intertwined by `F` (on fibres), then `τ' ∘ treeMap F = treeMap F ∘ τ`. -/
theorem treeMap_comp_deck [Nonempty (Lv.L.B →ₐ[R] Ω)] (F : obj Lv hp hc ⟶ obj Lv' hp' hc')
    (τ : deckGroup Lv p) (τ' : deckGroup Lv' p')
    (h : ∀ x, (deckStage V hV hp' hc' τ').1 (fibreMap V hV F x) =
      fibreMap V hV F ((deckStage V hV hp hc τ).1 x)) :
    τ'.1 ∘ treeMap F = treeMap F ∘ τ.1 := by
  obtain ⟨t⟩ := ‹Nonempty (Lv.L.B →ₐ[R] Ω)›
  obtain ⟨e₀, he₀⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
  have hx := h (Quotient.mk _ (prePt V hV t e₀ he₀))
  obtain ⟨he₁, h₁⟩ := fibreMap_prePt V hV F t e₀ he₀
  obtain ⟨he₂, h₂⟩ := fibreMap_prePt V hV F t (τ.1 e₀) ((τ.2 e₀).trans he₀)
  have A' := deckStage_apply V hV (hp := hp') (hc := hc') τ' (t.comp F.φ.f) (treeMap F e₀) he₁
  have A := deckStage_apply V hV (hp := hp) (hc := hc) τ t e₀ he₀
  have hx' := A'.symm.trans ((congrArg (deckStage V hV hp' hc' τ').1 h₁).symm.trans
    (hx.trans ((congrArg (fibreMap V hV F) A).trans h₂)))
  have hpt := ((mk_prePt_eq_iff V hV _ _).1 hx').2
  -- both maps are lifts of `ψ ∘ p` through `p'`
  refine lift_ext hp hp'.isCoveringMap (τ'.1.continuous.comp (continuous_treeMap F))
    ((continuous_treeMap F).comp τ.1.continuous) (funext fun e ↦ Subtype.ext ?_) e₀ hpt
  simp only [Function.comp_apply]
  rw [τ'.2, treeMap_spec, treeMap_spec, τ.2]

/-- **Functoriality of the deck subgroups** (G6.4): for a morphism `F : U_Lv ⟶ U_Lv'` between
Galois objects of a Galois class (connected `B'`) and a deck transformation `τ` of `Z̃`, the stage
group element of `U_Lv'` intertwined with `deckStage τ` by `F` (the transition of `deckStage τ`
along the pointed morphism `F`, `transition_eq_iff`) is `deckStage τ'` for a deck transformation
`τ'` of `Z̃'` with `τ' ∘ treeMap F = treeMap F ∘ τ`. -/
theorem exists_deck_transition {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
    (hU : 𝒢 (obj Lv hp hc)) (hU' : 𝒢 (obj Lv' hp' hc'))
    (hidem' : ∀ e : Lv'.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    [Nonempty (Lv.L.B →ₐ[R] Ω)] [Nonempty (Lv'.L.B →ₐ[R] Ω)]
    (F : obj Lv hp hc ⟶ obj Lv' hp' hc') (τ : deckGroup Lv p) :
    ∃ τ' : deckGroup Lv' p',
      (∀ x, (deckStage V hV hp' hc' τ').1 (fibreMap V hV F x) =
        fibreMap V hV F ((deckStage V hV hp hc τ).1 x)) ∧
      τ'.1 ∘ treeMap F = treeMap F ∘ τ.1 := by
  obtain ⟨x₀⟩ : Nonempty (Fibre Ω V hV (obj Lv hp hc)) := by
    obtain ⟨t⟩ := ‹Nonempty (Lv.L.B →ₐ[R] Ω)›
    obtain ⟨x, -⟩ := levelPt_surjective V hV (hp := hp) (hc := hc) t
    exact ⟨x⟩
  let P : PtGal (tempFibre O R A V hV) 𝒢 := ⟨_, hU, x₀⟩
  let Q : PtGal (tempFibre O R A V hV) 𝒢 := ⟨_, hU', fibreMap V hV F x₀⟩
  let f : P ⟶ Q := ptHom F rfl
  haveI : Subsingleton P.G.Lv.L.H := ‹Subsingleton Lv.L.H›
  haveI : Subsingleton Q.G.Lv.L.H := ‹Subsingleton Lv'.L.H›
  haveI : Nonempty (P.G.Lv.L.B →ₐ[R] Ω) := ‹Nonempty (Lv.L.B →ₐ[R] Ω)›
  have hker := transition_mem_ker V hV hgal hrig (p := P) (q := Q)
    (levelPt_surjective V hV (hp := hp) (hc := hc))
    (levelPt_surjective V hV (hp := hp') (hc := hc')) hidem' f
    (σ := deckStage V hV hp hc τ) (stageLevel_deckStage V hV (hp := hp) (hc := hc) τ)
  rw [ker_stageLevel V hV hrig hU'] at hker
  obtain ⟨τ', hτ'⟩ := hker
  have hcomm : ∀ x, (deckStage V hV hp' hc' τ').1 (fibreMap V hV F x) =
      fibreMap V hV F ((deckStage V hV hp hc τ).1 x) := fun x ↦ by
    rw [hτ']
    exact transition_comm hgal hrig f _ x
  exact ⟨τ', hcomm, treeMap_comp_deck V hV F τ τ' hcomm⟩

end Tree

end

end TemperedFundamentalGroups
