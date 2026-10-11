/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbStageLevel

/-!
# Functoriality of the orbifold stage groups (Blueprint §11.3, G6.4 / G6.10)

Orbifold Galois objects `U = OrbGal.obj D hX hp hc`, `U' = OrbGal.obj D' hX' hp' hc'` (possibly
different induction data `(S, α)`, `(S', α')` and scheme levels).

* `stageLevelO_eq_one_of_apply_eq`: a stage group element of `U` fixing one level class fixes all
  of them (conjugate it to the base point, `mem_range_deckStageO_of_base`);
* the compatibility of the actions on level classes with transition maps along
  `[t] ↦ [t ∘ φ.f]` is `stageCls_transition` (`Andre/LevelClass.lean`);
* **`transition_mem_range_deckStageO`: transition maps of pointed morphisms `U ⟶ U'` send the
  deck group of `Z̃` into the deck group of `Z̃'`**; `exists_deck_transitionO`: for a morphism
  `F : U ⟶ U'` and a deck transformation `τ` of `Z̃` there is a deck transformation `τ'` of `Z̃'`
  intertwined with `τ` by `F` on fibres;
* `treeMapO F : Z̃ → Z̃'`: the `Z̃'`-coordinate of `F (1, e)` (`F (1, e) = (copyO F e,
  treeMapO F e)`), continuous, lying over the model map;
  **`treeMapO_comp_deck`**: `τ' ∘ treeMapO F = treeMapO F ∘ τ` — the induced map of deck groups
  (fundamental groups of the dual graphs, for the tree coverings) is the map of trees.
  Uses that `H⁰ = ker α` acts freely on the geometric points `F_L` (`eq_one_of_fibreAct_eq`).
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

set_option maxHeartbeats 1600000 in
-- unifying the algebra instances of `D.level.B` and `(obj D hX hp hc).Lv.L.B` is slow
/-- **`H⁰` acts freely on the geometric points of the induced level**: `(s, 1)` moves a point on
the copy `y` to the copy `s y`. -/
lemma eq_one_of_fibreAct_eq (k : (obj D hX hp hc).Lv.L.H0)
    (t : (obj D hX hp hc).Lv.L.B →ₐ[R] Ω) (h : FiniteLevel.fibreAct Ω _ k t = t) : k = 1 := by
  let tt : D.level.B →ₐ[R] Ω := t
  obtain ⟨y, hy⟩ := D.exists_idem (tt : D.level.B →+* Ω)
  obtain ⟨⟨s, k₁⟩, hsk⟩ := (D.equivT hX).surjective k.1
  obtain rfl : k₁ = 1 := Subsingleton.elim _ _
  have key : (D.onCopy (tt : D.level.B →+* Ω) y hy).comp (D.ev (s * y)) =
      (D.onCopy (tt : D.level.B →+* Ω) y hy).comp (D.ev y) := RingHom.ext fun z => by
    have h1 := IndData.ev_equivT_symm D hX (s, 1) y z
    rw [map_one, inv_one, mul_one] at h1
    rw [RingHom.comp_apply, RingHom.comp_apply, D.onCopy_ev]
    refine (congrArg (D.onCopy (tt : D.level.B →+* Ω) y hy) h1.symm).trans ?_
    rw [D.onCopy_ev]
    have h2 := DFunLike.congr_fun h z
    rw [hsk]
    exact h2
  have hs : s * y = y := D.eq_of_comp_ev key
  have hs1 : s = 1 := mul_eq_right.1 hs
  subst hs1
  refine Subtype.ext ?_
  rw [← hsk]
  exact (D.equivT hX).map_one

/-- Two points `(g₁, e₁)`, `(g₂, e₂)` of `Ind_1^S Z̃` over the same point of `Z` have
`p e₁ = p e₂`. -/
lemma p_eq_of_indProj_eq (g₁ g₂ : (D.lv hX).L.H) (e₁ e₂ : E)
    (h : (indProj (proj D hX p) (⟨g₁, e₁⟩ : IndSpace (D.lv hX) E)).1 =
      (indProj (proj D hX p) (⟨g₂, e₂⟩ : IndSpace (D.lv hX) E)).1) : p e₁ = p e₂ := by
  obtain ⟨⟨s₁, k₁⟩, rfl⟩ := (D.equivT hX).surjective g₁
  obtain ⟨⟨s₂, k₂⟩, rfl⟩ := (D.equivT hX).surjective g₂
  obtain rfl : k₁ = 1 := Subsingleton.elim _ _
  obtain rfl : k₂ = 1 := Subsingleton.elim _ _
  have h' : D.inc s₁ (p e₁ : X₁.Lv.c.scheme) = D.inc s₂ (p e₂ : X₁.Lv.c.scheme) :=
    (coe_indProj D hX s₁ e₁).symm.trans (h.trans (coe_indProj D hX s₂ e₂))
  obtain rfl : s₁ = s₂ := D.inc_eq_inc h'
  exact Subtype.ext ((D.inc s₁).isOpenEmbedding.injective h')

variable [IsSchemeTheoreticallyDominant X₁.Lv.j] [ConnectedSpace X₁.Lv.Z]
  (hidem : ∀ e : X₁.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
  (hbase : ∃ (t₀ : X₁.Lv.L.B →ₐ[R] Ω) (e₀ : E), p e₀ = X₁.Lv.sp V hV t₀)
  (hgal : ∀ t t' : X₁.Lv.L.B →ₐ[R] Ω, ∃ σ : X₁.Lv.L.B ≃ₐ[R] X₁.Lv.L.B,
    t.comp (σ : X₁.Lv.L.B →ₐ[R] X₁.Lv.L.B) = t')
  (hsym : ∀ a : A, ∃ γ : SemilinearAut R A X₁.Lv.L.B, γ.a = a)
  (hact : ∀ γ : SemilinearAut R A X₁.Lv.L.B, ∃ ψ : X₁.Lv.c.scheme ⟶ X₁.Lv.c.scheme,
    ψ ≫ X₁.Lv.c.toSpec = X₁.Lv.c.toSpec ∧
    X₁.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁.Lv.L.B →+* X₁.Lv.L.B)) ≫ X₁.Lv.j)

include hidem hbase hgal hsym hact in
/-- **A stage group element of `OrbGal.obj` fixing one level class fixes all of them** (it is
then a deck transformation of `Z̃`). -/
theorem stageLevelO_eq_one_of_apply_eq
    (hsurj : Function.Surjective (levelCls V hV (obj D hX hp hc)))
    (τ : stageGroup (tempFibre O R A V hV) (obj D hX hp hc)) {c : LevelCls Ω (obj D hX hp hc)}
    (hfix : stageLevelO V hV D hX hp hc hsurj τ c = c) :
    stageLevelO V hV D hX hp hc hsurj τ = 1 := by
  obtain ⟨t₀, e₀, he₀⟩ := id hbase
  let u₀ : Fibre Ω V hV (obj D hX hp hc) := Quotient.mk _ (basePre D hX hp hc V hV t₀ e₀ he₀)
  obtain ⟨u, rfl⟩ := hsurj c
  obtain ⟨a, ha⟩ := exists_iso_fibreMap D hX hp hc V hV hgal hsym hact t₀ e₀ he₀ u₀ u
  let π : stageGroup (tempFibre O R A V hV) (obj D hX hp hc) := stageOf a
  have hπ : π.1 u₀ = u := ha
  have h1 : stageLevelO V hV D hX hp hc hsurj π (levelCls V hV _ u₀) = levelCls V hV _ u := by
    rw [stageCls_levelCls, hπ]
  have h2 : stageLevelO V hV D hX hp hc hsurj (π⁻¹ * τ * π) (levelCls V hV _ u₀) =
      levelCls V hV _ u₀ := by
    rw [map_mul, map_mul, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, hfix, ← h1, map_inv,
      Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have hρ : π⁻¹ * τ * π ∈ (deckStageO V hV D hX hp hc).range :=
    mem_range_deckStageO_of_base V hV D hX hp hc hidem hgal hsym hact t₀ e₀ he₀ _
      ((sameLevel_iff V hV D hX hp hc _ _).2 ((stageCls_levelCls V hV hsurj _ _).symm.trans h2))
  rw [← ker_stageLevelO V hV D hX hp hc hidem hbase hgal hsym hact hsurj] at hρ
  have := (MonoidHom.normal_ker _).conj_mem _ hρ π
  rw [mul_assoc, mul_assoc, mul_inv_cancel, mul_one, ← mul_assoc, mul_inv_cancel,
    one_mul] at this
  exact this

section Two

variable {X₁' : TempObj O R A₁} (D' : IndData (μ₁ A A₁) X₁') [Subsingleton X₁'.Lv.L.H]
  (hX' : IndFaithful X₁') {E' : Type u} [TopologicalSpace E'] {p' : E' → X₁'.Lv.Z}
  (hp' : IsUniversalCovering.{u, u, u, u} p') (hc' : ∀ z, (p' ⁻¹' {z}).Countable)
  [IsSchemeTheoreticallyDominant X₁'.Lv.j] [ConnectedSpace X₁'.Lv.Z]
  (hidem' : ∀ e : X₁'.Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
  (hbase' : ∃ (t₀ : X₁'.Lv.L.B →ₐ[R] Ω) (e₀ : E'), p' e₀ = X₁'.Lv.sp V hV t₀)
  (hgal' : ∀ t t' : X₁'.Lv.L.B →ₐ[R] Ω, ∃ σ : X₁'.Lv.L.B ≃ₐ[R] X₁'.Lv.L.B,
    t.comp (σ : X₁'.Lv.L.B →ₐ[R] X₁'.Lv.L.B) = t')
  (hsym' : ∀ a : A, ∃ γ : SemilinearAut R A X₁'.Lv.L.B, γ.a = a)
  (hact' : ∀ γ : SemilinearAut R A X₁'.Lv.L.B, ∃ ψ : X₁'.Lv.c.scheme ⟶ X₁'.Lv.c.scheme,
    ψ ≫ X₁'.Lv.c.toSpec = X₁'.Lv.c.toSpec ∧
    X₁'.Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : X₁'.Lv.L.B →+* X₁'.Lv.L.B)) ≫ X₁'.Lv.j)
  {𝒢 : ObjectProperty (TempObj O R A)} (hgalC : IsGaloisClass (tempFibre O R A V hV) 𝒢)
  (hrigC : IsRigid (tempFibre O R A V hV) 𝒢)
  (hU : 𝒢 (obj D hX hp hc)) (hU' : 𝒢 (obj D' hX' hp' hc'))

include hidem hbase hgal hsym hact hidem' hbase' hgal' hsym' hact' in
/-- **Transition maps preserve the deck groups**: for a pointed morphism `f` between orbifold
Galois objects `U = OrbGal.obj D …`, `U' = OrbGal.obj D' …` of a Galois class, the transition
map `Π_U → Π_{U'}` sends the deck group of `Z̃` into the deck group of `Z̃'`. -/
theorem transition_mem_range_deckStageO (x₀ : Fibre Ω V hV (obj D hX hp hc))
    (y₀ : Fibre Ω V hV (obj D' hX' hp' hc'))
    (f : (⟨_, hU, x₀⟩ : PtGal (tempFibre O R A V hV) 𝒢) ⟶ ⟨_, hU', y₀⟩)
    {σ : stageGroup (tempFibre O R A V hV) (obj D hX hp hc)}
    (hσ : σ ∈ (deckStageO V hV D hX hp hc).range) :
    transition hgalC hrigC f σ ∈ (deckStageO V hV D' hX' hp' hc').range := by
  obtain ⟨⟨F, hF⟩, -⟩ := f.2
  have hs := levelCls_surjective_obj V hV D hX hp hc hbase hgal hsym hact
  have hs' := levelCls_surjective_obj V hV D' hX' hp' hc' hbase' hgal' hsym' hact'
  rw [← ker_stageLevelO V hV D hX hp hc hidem hbase hgal hsym hact hs] at hσ
  rw [← ker_stageLevelO V hV D' hX' hp' hc' hidem' hbase' hgal' hsym' hact' hs']
  refine MonoidHom.mem_ker.2 (stageLevelO_eq_one_of_apply_eq V hV D' hX' hp' hc' hidem' hbase'
    hgal' hsym' hact' hs' _ (c := levelMap F (levelCls V hV _ x₀)) ?_)
  refine (stageCls_transition V hV hgalC hrigC (p := ⟨_, hU, x₀⟩) (q := ⟨_, hU', y₀⟩) hs hs' f F
    hF σ _).trans ?_
  rw [MonoidHom.mem_ker.1 hσ]
  rfl

include hidem hbase hgal hsym hact hidem' hbase' hgal' hsym' hact' hgalC hrigC hU hU' in
/-- **Functoriality of the deck groups**: for a morphism `F : U ⟶ U'` of orbifold Galois objects
of a Galois class and a deck transformation `τ` of `Z̃` there is a deck transformation `τ'` of
`Z̃'` with `deckStageO τ' ∘ F = F ∘ deckStageO τ` on fibres (`τ'` is the transition of `τ`
along `F`). -/
theorem exists_deck_transitionO (F : obj D hX hp hc ⟶ obj D' hX' hp' hc')
    (τ : deckGroup (D.lv hX) (proj D hX p)) :
    ∃ τ' : deckGroup (D'.lv hX') (proj D' hX' p'),
      ∀ x, (deckStageO V hV D' hX' hp' hc' τ').1 (fibreMap V hV F x) =
        fibreMap V hV F ((deckStageO V hV D hX hp hc τ).1 x) := by
  obtain ⟨t₀, e₀, he₀⟩ := id hbase
  let x₀ : Fibre Ω V hV (obj D hX hp hc) := Quotient.mk _ (basePre D hX hp hc V hV t₀ e₀ he₀)
  let P : PtGal (tempFibre O R A V hV) 𝒢 := ⟨_, hU, x₀⟩
  let Q : PtGal (tempFibre O R A V hV) 𝒢 := ⟨_, hU', fibreMap V hV F x₀⟩
  let f : P ⟶ Q := ptHom F rfl
  obtain ⟨τ', hτ'⟩ := transition_mem_range_deckStageO V hV D hX hp hc hidem hbase hgal hsym hact
    D' hX' hp' hc' hidem' hbase' hgal' hsym' hact' hgalC hrigC hU hU' x₀ _ f
    (σ := deckStageO V hV D hX hp hc τ) ⟨τ, rfl⟩
  refine ⟨τ', fun x => ?_⟩
  rw [hτ']
  exact transition_comm hgalC hrigC f _ x

/-! ### The map of trees -/

variable {D hX hp hc D' hX' hp' hc'}

/-- **The map of universal coverings** induced by a morphism `F : U ⟶ U'` of orbifold Galois
objects: `e ↦` the `Z̃'`-coordinate of `F (1, e)`. -/
def treeMapO (F : obj D hX hp hc ⟶ obj D' hX' hp' hc') (e : E) : E' :=
  ((Θo D' hX' hp' hc').symm (F.h (Θo D hX hp hc ⟨1, e⟩))).2

/-- The copy (element of `S' × 1`) of `F (1, e)`. -/
def copyO (F : obj D hX hp hc ⟶ obj D' hX' hp' hc') (e : E) : (D'.lv hX').L.H :=
  ((Θo D' hX' hp' hc').symm (F.h (Θo D hX hp hc ⟨1, e⟩))).1

lemma h_Θo_one (F : obj D hX hp hc ⟶ obj D' hX' hp' hc') (e : E) :
    F.h (Θo D hX hp hc ⟨1, e⟩) = Θo D' hX' hp' hc' ⟨copyO F e, treeMapO F e⟩ :=
  ((Θo D' hX' hp' hc').apply_symm_apply _).symm

lemma continuous_treeMapO (F : obj D hX hp hc ⟶ obj D' hX' hp' hc') :
    Continuous (treeMapO F) := by
  have h₁ : Continuous fun e : E => Θo D hX hp hc ⟨1, e⟩ :=
    (Θo D hX hp hc).continuous.comp (continuous_sigmaMk (σ := fun _ : (D.lv hX).L.H => E))
  have h₂ : Continuous fun x : GaloisObject.IndSpace (D'.lv hX') E' => x.2 :=
    continuous_sigma fun _ => continuous_id
  exact h₂.comp ((Θo D' hX' hp' hc').symm.continuous.comp (F.continuous_h.comp h₁))

/-- `treeMapO F` lies over the model map: points of `Z̃` over the same point of `Z` go to points
of `Z̃'` over the same point of `Z'`. -/
lemma proj_treeMapO_eq (F : obj D hX hp hc ⟶ obj D' hX' hp' hc') {e₁ e₂ : E}
    (h : proj D hX p e₁ = proj D hX p e₂) :
    proj D' hX' p' (treeMapO F e₁) = proj D' hX' p' (treeMapO F e₂) := by
  have h₁ := F.fst_h (Θo D hX hp hc ⟨1, e₁⟩)
  have h₂ := F.fst_h (Θo D hX hp hc ⟨1, e₂⟩)
  have h₀ : (Θo D hX hp hc ⟨1, e₁⟩).1.1 = (Θo D hX hp hc ⟨1, e₂⟩).1.1 := by
    change (D.lv hX).ρs 1 (proj D hX p e₁) = (D.lv hX).ρs 1 (proj D hX p e₂)
    rw [h]
  rw [h₀] at h₁
  rw [h_Θo_one] at h₁ h₂
  have key : (indProj (proj D' hX' p')
      (⟨copyO F e₁, treeMapO F e₁⟩ : IndSpace (D'.lv hX') E')).1 =
      (indProj (proj D' hX' p') (⟨copyO F e₂, treeMapO F e₂⟩ : IndSpace (D'.lv hX') E')).1 :=
    h₁.trans h₂.symm
  change D'.inc₁S hX' (p' _) = D'.inc₁S hX' (p' _)
  rw [p_eq_of_indProj_eq D' hX' _ _ _ _ key]

set_option maxHeartbeats 1600000 in
-- unifying the algebra instances of `D.level.B` and `(obj D hX hp hc).Lv.L.B` is slow
include hbase in
/-- **The induced map of deck groups is the map of trees**: if `deckStageO τ'` and
`deckStageO τ` are intertwined by `F` on fibres, then `τ' ∘ treeMapO F = treeMapO F ∘ τ`. -/
theorem treeMapO_comp_deck (F : obj D hX hp hc ⟶ obj D' hX' hp' hc')
    (τ : deckGroup (D.lv hX) (proj D hX p)) (τ' : deckGroup (D'.lv hX') (proj D' hX' p'))
    (h : ∀ x, (deckStageO V hV D' hX' hp' hc' τ').1 (fibreMap V hV F x) =
      fibreMap V hV F ((deckStageO V hV D hX hp hc τ).1 x)) :
    τ'.1 ∘ treeMapO F = treeMapO F ∘ τ.1 := by
  obtain ⟨t₀, e₀, he₀⟩ := id hbase
  let q₀ := basePre D hX hp hc V hV t₀ e₀ he₀
  obtain ⟨q', hq'₁, hq'₂, hq'⟩ := deckStageO_mk V hV D hX hp hc τ q₀ 1 e₀ rfl
  obtain ⟨q'', hq''₁, hq''₂, hq''⟩ := deckStageO_mk V hV D' hX' hp' hc' τ' (preMap V hV F q₀)
    (copyO F e₀) (treeMapO F e₀) (h_Θo_one F e₀)
  have hx := h (Quotient.mk _ q₀)
  rw [hq'] at hx
  change (deckStageO V hV D' hX' hp' hc' τ').1 (Quotient.mk _ (preMap V hV F q₀)) =
    Quotient.mk _ (preMap V hV F q') at hx
  rw [hq''] at hx
  obtain ⟨k, hk⟩ := Quotient.exact hx
  have hk₁ : (k • preMap V hV F q').1.1 = q''.1.1 := congrArg (fun q => q.1.1) hk
  have hlev : (preMap V hV F q').1.1 = q''.1.1 := by
    rw [hq''₁]
    change q'.1.1.comp F.φ.f = q₀.1.1.comp F.φ.f
    rw [hq'₁]
  rw [smul_val, ← hlev] at hk₁
  obtain rfl := eq_one_of_fibreAct_eq D' hX' hp' hc' k _ hk₁
  replace hk : preMap V hV F q' = q'' := (one_smul _ _).symm.trans hk
  have hpt : Θo D' hX' hp' hc' ⟨copyO F (τ.1 e₀), treeMapO F (τ.1 e₀)⟩ =
      Θo D' hX' hp' hc' ⟨copyO F e₀, τ'.1 (treeMapO F e₀)⟩ := by
    rw [← h_Θo_one, ← hq'₂, ← hq''₂, ← hk]
    rfl
  have he := (Sigma.mk.inj ((Θo D' hX' hp' hc').injective hpt)).2
  refine lift_ext hp (isCoveringMap_proj D' hX' hp'.isCoveringMap)
    (τ'.1.continuous.comp (continuous_treeMapO F))
    ((continuous_treeMapO F).comp τ.1.continuous) (funext fun e => ?_) e₀ (eq_of_heq he).symm
  simp only [Function.comp_apply]
  rw [τ'.2, proj_treeMapO_eq F (τ.2 e)]

end Two

end OrbGal

end

end TemperedFundamentalGroups
