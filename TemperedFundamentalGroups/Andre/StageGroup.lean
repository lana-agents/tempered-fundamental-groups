/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.GaloisGroupLimit
import TemperedFundamentalGroups.Andre.GaloisClass

/-!
# The stage group of a Galois object as an extension (Blueprint §11.3, G6.3)

Scheme case with trivial `H` (the levels of `galClassW`). For a tempered covering `X` over a level
with trivial `H`, a point of the fibre `Φ X` is a pair `[t, p]` of a geometric point
`t ∈ F_L = Hom_R(B, Ω)` and a point `p` of the covering over its specialization;
`levelPt [t, p] = t` (`levelPt_fibreMap`: `t ↦ t ∘ φ.f` along morphisms).

For `U = U_Lv` (`GaloisObject.obj Lv hp hc`, `p : Z̃ → Z` a universal covering, e.g. the tree
covering of the dual graph):

* `stageLevel : stageGroup Φ U →* Perm F_L`: the action of the stage group on level coordinates
  (`stageLevel_levelPt`);
* `deckStage : deckGroup Lv p →* stageGroup Φ U`, `τ ↦` the deck transformation `[t, (1, e)] ↦
  [t, (1, τ e)]` (`deckStage_injective`);
* **`ker_stageLevel`: `ker stageLevel = range deckStage`**;
* **`range_stageLevel`**: for a Galois connected level the image of `stageLevel` consists exactly
  of the permutations `t ↦ t ∘ σ`, `σ ∈ Aut_R(B)` (`autPerm`).

So `1 → π₁(Z) → Π_Lv → Aut_R(B)ᵒᵖ → 1`, `π₁(Z)` the deck group of the tree covering of the
dual graph.
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

namespace TempObj

/-- **The level coordinate** `[t, p] ↦ t` of the fibre of a covering over a level with trivial
`H`. -/
def levelPt (X : TempObj O R A) [Subsingleton X.Lv.L.H] :
    Fibre Ω V hV X → (X.Lv.L.B →ₐ[R] Ω) :=
  Quotient.lift (fun q ↦ q.1.1) fun q q' ⟨g, hg⟩ ↦ by
    have hg1 : g = 1 := Subtype.ext (Subsingleton.elim _ _)
    subst hg1
    change (1 : X.Lv.L.H0) • q' = q at hg
    rw [one_smul] at hg
    rw [hg]

lemma levelPt_mk (X : TempObj O R A) [Subsingleton X.Lv.L.H] (q : PreFibre Ω V hV X) :
    levelPt V hV X (Quotient.mk _ q) = q.1.1 := rfl

/-- The level coordinate is natural: `levelPt (m x) = levelPt x ∘ φ.f`. -/
lemma levelPt_fibreMap {X Y : TempObj O R A} [Subsingleton X.Lv.L.H] [Subsingleton Y.Lv.L.H]
    (m : X ⟶ Y) (x : Fibre Ω V hV X) :
    levelPt V hV Y (fibreMap V hV m x) = (levelPt V hV X x).comp m.φ.f := by
  induction x using Quotient.inductionOn
  rfl

end TempObj

section Stage

variable {X : TempObj O R A} [Subsingleton X.Lv.L.H]

/-- Stage group elements act on level coordinates. -/
lemma levelPt_stage_eq (σ : stageGroup (tempFibre O R A V hV) X) {x y : Fibre Ω V hV X}
    (h : levelPt V hV X x = levelPt V hV X y) :
    levelPt V hV X (σ.1 x) = levelPt V hV X (σ.1 y) := by
  obtain ⟨σ, a, ha⟩ := σ
  change levelPt V hV X (σ x) = levelPt V hV X (σ y)
  rw [ha]
  change levelPt V hV X (fibreMap V hV a.hom x) = levelPt V hV X (fibreMap V hV a.hom y)
  rw [levelPt_fibreMap, levelPt_fibreMap, h]

variable (hsurj : Function.Surjective (levelPt V hV X))

/-- The action of a stage group element on level coordinates (as a function). -/
def stageLevelFun (σ : stageGroup (tempFibre O R A V hV) X) (t : X.Lv.L.B →ₐ[R] Ω) :
    X.Lv.L.B →ₐ[R] Ω :=
  levelPt V hV X (σ.1 (hsurj t).choose)

lemma stageLevelFun_levelPt (σ : stageGroup (tempFibre O R A V hV) X) (x : Fibre Ω V hV X) :
    stageLevelFun V hV hsurj σ (levelPt V hV X x) = levelPt V hV X (σ.1 x) :=
  levelPt_stage_eq V hV σ (hsurj _).choose_spec

/-- **The action of the stage group on the level coordinates** `F_L`. -/
def stageLevel : stageGroup (tempFibre O R A V hV) X →* Equiv.Perm (X.Lv.L.B →ₐ[R] Ω) where
  toFun σ :=
    { toFun := stageLevelFun V hV hsurj σ
      invFun := stageLevelFun V hV hsurj σ⁻¹
      left_inv := fun t ↦ by
        obtain ⟨x, rfl⟩ := hsurj t
        rw [stageLevelFun_levelPt, stageLevelFun_levelPt, ← Equiv.Perm.mul_apply,
          ← Subgroup.coe_mul, inv_mul_cancel]
        rfl
      right_inv := fun t ↦ by
        obtain ⟨x, rfl⟩ := hsurj t
        rw [stageLevelFun_levelPt, stageLevelFun_levelPt, ← Equiv.Perm.mul_apply,
          ← Subgroup.coe_mul, mul_inv_cancel]
        rfl }
  map_one' := by
    refine Equiv.ext fun t ↦ ?_
    obtain ⟨x, rfl⟩ := hsurj t
    exact stageLevelFun_levelPt V hV hsurj 1 x
  map_mul' σ τ := by
    refine Equiv.ext fun t ↦ ?_
    obtain ⟨x, rfl⟩ := hsurj t
    change stageLevelFun V hV hsurj (σ * τ) _ =
      stageLevelFun V hV hsurj σ (stageLevelFun V hV hsurj τ _)
    rw [stageLevelFun_levelPt, stageLevelFun_levelPt, stageLevelFun_levelPt]
    rfl

lemma stageLevel_levelPt (σ : stageGroup (tempFibre O R A V hV) X) (x : Fibre Ω V hV X) :
    stageLevel V hV hsurj σ (levelPt V hV X x) = levelPt V hV X (σ.1 x) :=
  stageLevelFun_levelPt V hV hsurj σ x

/-- The stage group element of an automorphism acts on level coordinates by `t ↦ t ∘ φ.f`. -/
lemma stageLevel_stageOf (a : X ≅ X) (t : X.Lv.L.B →ₐ[R] Ω) :
    stageLevel V hV hsurj (stageOf a) t = t.comp a.hom.φ.f := by
  obtain ⟨x, rfl⟩ := hsurj t
  rw [stageLevel_levelPt]
  exact levelPt_fibreMap V hV a.hom x

end Stage

/-- `stageOf` as a homomorphism `Aut G →* stageGroup Φ G`. -/
def GaloisLimit.stageOfHom {C : Type*} [Category C] (Φ : C ⥤ Type*) (G : C) :
    Aut G →* stageGroup Φ G where
  toFun a := stageOf a
  map_one' := Subtype.ext (Equiv.ext fun x ↦ by
    change Φ.map (𝟙 G) x = x
    rw [Φ.map_id]
    rfl)
  map_mul' a b := Subtype.ext (Equiv.ext fun x ↦ by
    change Φ.map (b.hom ≫ a.hom) x = Φ.map a.hom (Φ.map b.hom x)
    rw [Functor.map_comp_apply])

lemma GaloisLimit.eq_stageOf {C : Type*} [Category C] {Φ : C ⥤ Type*} {G : C}
    (σ : stageGroup Φ G) : ∃ a : G ≅ G, σ = stageOf a := by
  obtain ⟨σ, a, ha⟩ := σ
  exact ⟨a, Subtype.ext (Equiv.ext fun x ↦ congrFun ha x)⟩

section Universal

variable [Subsingleton A] {Lv : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H]
  {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}

instance : Subsingleton (obj Lv hp hc).Lv.L.H := ‹Subsingleton Lv.L.H›

omit [Subsingleton A] in
/-- The level coordinate of `[t, (1, e)]` is `t`. -/
lemma levelPt_prePt (t : Lv.L.B →ₐ[R] Ω) (e : E) (he : p e = Lv.sp V hV t) :
    levelPt V hV (obj Lv hp hc) (Quotient.mk _ (prePt V hV t e he)) = t := rfl

omit [Subsingleton A] in
/-- **The level coordinate of `U_Lv` is surjective** (`Z` connected, `Z̃` nonempty). -/
lemma levelPt_surjective [ConnectedSpace Lv.Z] [Nonempty E] :
    Function.Surjective (levelPt V hV (obj Lv hp hc)) := fun t ↦ by
  obtain ⟨e, he⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
  exact ⟨Quotient.mk _ (prePt V hV t e he), rfl⟩

variable (hp hc) in
/-- **The deck group of `Z̃` in the stage group** of `U_Lv`: `τ ↦ [t, (1, e)] ↦ [t, (1, τ e)]`. -/
def deckStage : deckGroup Lv p →* stageGroup (tempFibre O R A V hV) (obj Lv hp hc) :=
  (stageOfHom (tempFibre O R A V hV) (obj Lv hp hc)).comp ((deck hp hc).comp
    (((toH Lv p).ker.subtype).comp (kerEquiv Lv (p := p)).symm.toMonoidHom))

omit [Subsingleton A] [Subsingleton Lv.L.H] in
lemma deckStage_eq (τ : deckGroup Lv p) :
    deckStage V hV hp hc τ = stageOf (deck hp hc ((kerEquiv Lv (p := p)).symm τ).1) := rfl

omit [Subsingleton A] [Subsingleton Lv.L.H] in
/-- The deck transformation of `τ` on the points `[t, (1, e)]`. -/
lemma deckStage_apply (τ : deckGroup Lv p) (t : Lv.L.B →ₐ[R] Ω) (e : E)
    (he : p e = Lv.sp V hV t) :
    (deckStage V hV hp hc τ).1 (Quotient.mk _ (prePt V hV t e he)) =
      Quotient.mk _ (prePt V hV t (τ.1 e) ((τ.2 e).trans he)) := by
  rw [deckStage_eq, stageOf_apply, deck_hom]
  change Quotient.mk _ (preMap V hV _ _) = _
  congr 1
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change (deckHom hp hc _).h (Θ Lv hp hc ⟨1, e⟩) = Θ Lv hp hc ⟨1, τ.1 e⟩
  rw [deckHom_h_Θ]
  exact congrArg (Θ Lv hp hc) (Sigma.ext (by simp; rfl) HEq.rfl)

omit [Subsingleton A] in
/-- Two points `[t, (1, e)]`, `[t', (1, e')]` are equal iff `t = t'` and `e = e'`. -/
lemma mk_prePt_eq_iff {t t' : Lv.L.B →ₐ[R] Ω} {e e' : E} (he : p e = Lv.sp V hV t)
    (he' : p e' = Lv.sp V hV t') :
    (Quotient.mk _ (prePt V hV t e he) : Fibre Ω V hV (obj Lv hp hc)) =
      Quotient.mk _ (prePt V hV t' e' he') ↔ t = t' ∧ e = e' := by
  constructor
  · intro h
    obtain ⟨g, hg⟩ := Quotient.exact h
    have hg1 : g = 1 := Subtype.ext (Subsingleton.elim _ _)
    subst hg1
    change (1 : (obj Lv hp hc).Lv.L.H0) • prePt V hV t' e' he' = prePt V hV t e he at hg
    rw [one_smul] at hg
    have h₁ := congrArg (fun q ↦ q.1.1) hg
    have h₂ := congrArg (fun q ↦ q.1.2) hg
    simp only [prePt] at h₁ h₂
    obtain ⟨-, h₃⟩ := Sigma.mk.inj ((Θ Lv hp hc).injective h₂)
    exact ⟨h₁.symm, (eq_of_heq h₃).symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

omit [Subsingleton A] in
/-- **The deck group embeds into the stage group** (if `F_L` is nonempty). -/
lemma deckStage_injective [ConnectedSpace Lv.Z] [Nonempty E] [Nonempty (Lv.L.B →ₐ[R] Ω)] :
    Function.Injective (deckStage V hV hp hc) := by
  refine (injective_iff_map_eq_one _).2 fun τ hτ ↦ ?_
  obtain ⟨t⟩ := ‹Nonempty (Lv.L.B →ₐ[R] Ω)›
  obtain ⟨e, he⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
  have h := deckStage_apply V hV (hp := hp) (hc := hc) τ t e he
  rw [hτ] at h
  have he' := ((mk_prePt_eq_iff V hV (hp := hp) (hc := hc) he ((τ.2 e).trans he)).1 h).2
  apply Subtype.ext
  have hπ : ((kerEquiv Lv (p := p)).symm τ).1 = 1 :=
    Pi.ext_of_apply hp rfl e (by exact he'.symm)
  have := congrArg (kerEquiv Lv (p := p)) (Subtype.ext hπ : (kerEquiv Lv (p := p)).symm τ = 1)
  rw [MulEquiv.apply_symm_apply, map_one] at this
  exact congrArg Subtype.val this

variable [ConnectedSpace Lv.Z] [Nonempty E]

omit [Subsingleton A] in
/-- Deck transformations act trivially on level coordinates. -/
lemma stageLevel_deckStage (τ : deckGroup Lv p) :
    stageLevel V hV (levelPt_surjective V hV) (deckStage V hV hp hc τ) = 1 := by
  refine Equiv.ext fun t ↦ ?_
  rw [deckStage_eq, stageLevel_stageOf]
  rfl

/-- **`ker stageLevel = range deckStage`**: a stage group element fixing the level coordinates is
a deck transformation of the tree covering (rigidity of `U_Lv`). -/
theorem ker_stageLevel {𝒢 : ObjectProperty (TempObj O R A)}
    (hrig : IsRigid (tempFibre O R A V hV) 𝒢) (hU : 𝒢 (obj Lv hp hc))
    [Nonempty (Lv.L.B →ₐ[R] Ω)] :
    (stageLevel V hV (levelPt_surjective V hV (hp := hp) (hc := hc))).ker =
      (deckStage V hV hp hc).range := by
  ext σ
  refine ⟨fun hσ ↦ ?_, ?_⟩
  · obtain ⟨t⟩ := ‹Nonempty (Lv.L.B →ₐ[R] Ω)›
    obtain ⟨e₁, he₁⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
    set x₀ : Fibre Ω V hV (obj Lv hp hc) := Quotient.mk _ (prePt V hV t e₁ he₁)
    obtain ⟨q₂, e₂, hq₂, hσx⟩ := exists_rep V hV (σ.1 x₀)
    have ht : q₂.1.1 = t := by
      have h := stageLevel_levelPt V hV (levelPt_surjective V hV) σ x₀
      rw [MonoidHom.mem_ker.1 hσ, hσx] at h
      exact h.symm
    have hp₂ : p e₂ = Lv.sp V hV t := ht ▸ proj_eq_sp V hV q₂ hq₂
    obtain ⟨τ', hτ', hτe⟩ := exists_lift Lv hp 1 (e₁ := e₁) (e₂ := e₂)
      (by rw [hp₂, map_one, Homeomorph.one_apply, he₁])
    let τ : deckGroup Lv p := ⟨τ', fun e ↦ by rw [hτ', map_one, Homeomorph.one_apply]⟩
    refine ⟨τ, stageGroup_eq_of_apply_eq hrig hU (x := x₀) ?_⟩
    rw [deckStage_apply V hV (hp := hp) (hc := hc), hσx]
    have hq : q₂ = prePt V hV t e₂ hp₂ := by
      apply Subtype.ext
      exact Prod.ext ht hq₂
    subst hq
    change Quotient.mk _ (prePt V hV t (τ' e₁) _) = Quotient.mk _ (prePt V hV t e₂ hp₂)
    exact (mk_prePt_eq_iff V hV (hp := hp) (hc := hc) _ _).2 ⟨rfl, hτe⟩
  · rintro ⟨τ, rfl⟩
    exact stageLevel_deckStage V hV (hp := hp) (hc := hc) τ

/-- The permutation `t ↦ t ∘ σ` of `F_L` of an automorphism `σ` of `B`. -/
def autPerm (σ : Lv.L.B ≃ₐ[R] Lv.L.B) : Equiv.Perm (Lv.L.B →ₐ[R] Ω) where
  toFun t := t.comp (σ : Lv.L.B →ₐ[R] Lv.L.B)
  invFun t := t.comp (σ.symm : Lv.L.B →ₐ[R] Lv.L.B)
  left_inv t := by ext; simp
  right_inv t := by ext; simp

omit [Subsingleton A] in
/-- **Every stage group element acts on `F_L` through an automorphism of `B`**: the level part of
an automorphism of `U_Lv`. -/
theorem exists_autPerm (σ : stageGroup (tempFibre O R A V hV) (obj Lv hp hc)) :
    ∃ s : Lv.L.B ≃ₐ[R] Lv.L.B,
      stageLevel V hV (levelPt_surjective V hV) σ = autPerm s := by
  obtain ⟨a, rfl⟩ := eq_stageOf σ
  have h₁ : (a.inv.φ ≫ a.hom.φ).f = AlgHom.id R Lv.L.B := congrArg (fun m ↦ m.φ.f) a.inv_hom_id
  have h₂ : (a.hom.φ ≫ a.inv.φ).f = AlgHom.id R Lv.L.B := congrArg (fun m ↦ m.φ.f) a.hom_inv_id
  refine ⟨AlgEquiv.ofAlgHom a.hom.φ.f a.inv.φ.f h₂ h₁, Equiv.ext fun t ↦ ?_⟩
  rw [stageLevel_stageOf]
  rfl

omit [Subsingleton A] in
/-- **Every automorphism of a Galois connected level is realised in the stage group** (by (gal)
and rigidity of maps into the connected `B`). -/
theorem exists_stageLevel_eq {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hU : 𝒢 (obj Lv hp hc))
    (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    [Nonempty (Lv.L.B →ₐ[R] Ω)] (s : Lv.L.B ≃ₐ[R] Lv.L.B) :
    ∃ σ : stageGroup (tempFibre O R A V hV) (obj Lv hp hc),
      stageLevel V hV (levelPt_surjective V hV) σ = autPerm s := by
  haveI : Algebra.Etale R Lv.L.B := Lv.L.etale
  haveI : Module.Finite R Lv.L.B := Lv.L.finite
  obtain ⟨t⟩ := ‹Nonempty (Lv.L.B →ₐ[R] Ω)›
  obtain ⟨x₀, hx₀⟩ := levelPt_surjective V hV (hp := hp) (hc := hc) t
  obtain ⟨x₁, hx₁⟩ := levelPt_surjective V hV (hp := hp) (hc := hc) (autPerm s t)
  obtain ⟨σ, hσ⟩ := exists_stageGroup_apply_eq hgal hU x₀ x₁
  refine ⟨σ, ?_⟩
  obtain ⟨a, rfl⟩ := eq_stageOf σ
  have h₁ := stageLevel_stageOf V hV (levelPt_surjective V hV (hp := hp) (hc := hc)) a t
  have h₂ : stageLevel V hV (levelPt_surjective V hV (hp := hp) (hc := hc)) (stageOf a) t =
      autPerm s t := by
    have h := stageLevel_levelPt V hV (levelPt_surjective V hV (hp := hp) (hc := hc))
      (stageOf a) x₀
    rw [hx₀, hσ, hx₁] at h
    exact h
  have key : t.comp (a.hom.φ.f : Lv.L.B →ₐ[R] Lv.L.B) = t.comp (s : Lv.L.B →ₐ[R] Lv.L.B) :=
    h₁.symm.trans h₂
  have hconn : ∀ f₀ f₁ : Lv.L.B →ₐ[R] Lv.L.B, t.comp f₀ = t.comp f₁ → f₀ = f₁ :=
    fun f₀ f₁ h ↦ algHom_eq_of_comp_eq hidem f₀ f₁ t h
  have hf : (a.hom.φ.f : Lv.L.B →ₐ[R] Lv.L.B) = (s : Lv.L.B →ₐ[R] Lv.L.B) := hconn _ _ key
  refine Equiv.ext fun t' ↦ ?_
  rw [stageLevel_stageOf, hf]
  rfl

/-- **G6.3: the stage group `Π_Lv` of `U_Lv` is an extension** of the automorphism group of the
level by the deck group of `Z̃` (for the tree covering: the fundamental group of the dual graph):
`deckStage` is injective, its image is the kernel of the action `stageLevel` on `F_L`, and the
image of `stageLevel` is `{t ↦ t ∘ σ | σ ∈ Aut_R(B)}`. -/
theorem stageGroup_extension {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
    (hU : 𝒢 (obj Lv hp hc)) (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    [Nonempty (Lv.L.B →ₐ[R] Ω)] :
    Function.Injective (deckStage V hV hp hc) ∧
      (stageLevel V hV (levelPt_surjective V hV (hp := hp) (hc := hc))).ker =
        (deckStage V hV hp hc).range ∧
      Set.range (stageLevel V hV (levelPt_surjective V hV (hp := hp) (hc := hc))) =
        Set.range (autPerm (Ω := Ω) (Lv := Lv)) := by
  refine ⟨deckStage_injective V hV, ker_stageLevel V hV hrig hU, ?_⟩
  ext π
  constructor
  · rintro ⟨σ, rfl⟩
    obtain ⟨s, hs⟩ := exists_autPerm V hV σ
    exact ⟨s, hs.symm⟩
  · rintro ⟨s, rfl⟩
    exact exists_stageLevel_eq V hV hgal hU hidem s

end Universal

end

end TemperedFundamentalGroups
