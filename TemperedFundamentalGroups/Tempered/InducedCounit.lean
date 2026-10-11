/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.InducedRange
import TemperedFundamentalGroups.Tempered.InducedUnit

/-!
# The counit of induction, as a span (Blueprint §11, F7′)

For a tempered covering `Y` of `[Spec R / A]` with finite level group `H`, the base change
`bc Y` to `[Spec R / A']` has the induction data `counitData Y` with index group `S = H`
(`α = (h ↦ h.a)`, `β = bcPr`). The induced covering `W = Ind_H (bc Y)` maps

* to `Y` (`counitHom`): `b ↦ (x ↦ 1 ⊗ σ_x⁻¹ b)` on algebras, `(h, k) ↦ h` on groups, the copy `x`
  of the model through `ρ x`, and `(z, p) ↦ x • p` on covering spaces (`x` the copy of `z`);
* to the push `Ind_A (bc Y)` (`IndData.hom` along `H → A`).

On fibres, `counitHom` sends `ι_W z` to the fibre element `z` of `Y` (`counitHom_ι`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits TensorProduct

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A' : Type u} [Group A'] [MulSemiringAction A' R] {μ : OrbMap R A R A'}

namespace IndData

variable {X' : TempObj O R A'} (D : IndData μ X')

/-! ### Copies of points of `∐ 𝒯'` -/

lemma inc_eq_inc {x y : D.S} {w w' : X'.Lv.c.scheme} (h : D.inc x w = D.inc y w') : x = y := by
  have h' : Sigma.ι (fun _ : D.S => X'.Lv.c.scheme) x w =
      Sigma.ι (fun _ : D.S => X'.Lv.c.scheme) y w' := by
    apply (SemistableReduction.ModelCode.sigmaIso (fun _ : D.S => X'.Lv.c)).hom.homeomorph.injective
    exact h
  exact congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).1 h')

/-- The copy of a point of `∐ 𝒯'`. -/
def copy (z : D.c.scheme) : D.S := (D.exists_inc z).choose

lemma exists_inc_copy (z : D.c.scheme) : ∃ w, D.inc (D.copy z) w = z :=
  (D.exists_inc z).choose_spec

lemma copy_inc (x : D.S) (w : X'.Lv.c.scheme) : D.copy (D.inc x w) = x :=
  let ⟨_, hw⟩ := D.exists_inc_copy (D.inc x w)
  D.inc_eq_inc hw

lemma copy_eq_iff (z : D.c.scheme) (x : D.S) : D.copy z = x ↔ z ∈ Set.range (D.inc x) := by
  constructor
  · rintro rfl
    obtain ⟨w, hw⟩ := D.exists_inc_copy z
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    exact D.copy_inc x w

lemma isOpen_copy (x : D.S) : IsOpen {z | D.copy z = x} := by
  have : {z | D.copy z = x} = Set.range (D.inc x) := Set.ext fun z => D.copy_eq_iff z x
  rw [this]
  exact (D.inc x).isOpenEmbedding.isOpen_range

section Push

variable [Finite A]

variable (μ) in
/-- **The induction data of the push** along the orbifold cover: `S = A`, `β k = μ.α k.a`. -/
abbrev pushData (X' : TempObj O R A') : IndData μ X' where
  S := A
  fintype := Fintype.ofFinite A
  decEq := Classical.decEq A
  α := MonoidHom.id A
  α_surj := Function.surjective_id
  β := μ.α.comp (SemilinearAut.toA.comp X'.Lv.L.H.subtype)
  hβ _ := rfl

end Push

section Counit

variable (μ) (Y : TempObj O R A) [Fintype Y.Lv.L.H] [DecidableEq Y.Lv.L.H]

/-- The induction data of `bc Y` with index group `H` (`α = (h ↦ h.a)`, `β = bcPr`). -/
abbrev counitData : IndData μ (Y.baseChange μ) where
  S := Y.Lv.L.H
  α := SemilinearAut.toA.comp Y.Lv.L.H.subtype
  α_surj a := let ⟨g, hg, ha⟩ := Y.Lv.L.surjective a; ⟨⟨g, hg⟩, ha⟩
  β := Y.Lv.L.bcPr μ
  hβ k := Y.Lv.L.bcPr_a μ k

variable {μ Y}

lemma σ_symm_algebraMap (g : SemilinearAut R A Y.Lv.L.B) (r : R) :
    g.σ.symm (algebraMap R Y.Lv.L.B r) = algebraMap R Y.Lv.L.B (g.a⁻¹ • r) :=
  (g⁻¹).map_algebraMap r

/-- The algebra map of the counit: `b ↦ (x ↦ 1 ⊗ σ_x⁻¹ b)`. -/
def counitAlg : Y.Lv.L.B →ₐ[R] (counitData μ Y).Alg where
  toFun b x := (Y.Lv.L.bcι μ (((x : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B).σ.symm b) :
    (Y.Lv.L.baseChange μ).B)
  map_one' := funext fun x => by
    change Y.Lv.L.bcι μ _ = 1
    rw [map_one, map_one]
  map_mul' a b := funext fun x => by
    change Y.Lv.L.bcι μ _ = Y.Lv.L.bcι μ _ * Y.Lv.L.bcι μ _
    rw [map_mul, map_mul]
  map_zero' := funext fun x => by
    change Y.Lv.L.bcι μ _ = 0
    rw [map_zero, map_zero]
  map_add' a b := funext fun x => by
    change Y.Lv.L.bcι μ _ = Y.Lv.L.bcι μ _ + Y.Lv.L.bcι μ _
    rw [map_add, map_add]
  commutes' r := funext fun x => by
    change Y.Lv.L.bcι μ _ = algebraMap R (Y.Lv.L.baseChange μ).B
      (((x : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B).a⁻¹ • r)
    rw [σ_symm_algebraMap, FiniteLevel.bcι_algebraMap]
    rfl

lemma ev_E_symm {X' : TempObj O R A'} (D : IndData μ X') (x : D.S) (φ : D.Alg) :
    D.ev x (D.E.symm φ) = φ x := by
  rw [ev_apply, AlgEquiv.apply_symm_apply]

variable (hY : IndFaithful (Y.baseChange μ))

/-- The level map of the counit. -/
def counitF : Y.Lv.L.B →ₐ[R] (counitData μ Y).level.B :=
  (counitData μ Y).E.symm.toAlgHom.comp counitAlg

lemma ev_counitF (x : Y.Lv.L.H) (b : Y.Lv.L.B) :
    (counitData μ Y).ev x (counitF b) =
      Y.Lv.L.bcι μ ((x : SemilinearAut R A Y.Lv.L.B).σ.symm b) :=
  ev_E_symm (counitData μ Y) x (counitAlg b)

lemma σ_mul_apply (u v : SemilinearAut R A Y.Lv.L.B) (b : Y.Lv.L.B) :
    (u * v).σ b = u.σ (v.σ b) := rfl

/-- The group map of the counit, `(h, k) ↦ h`. -/
def counitR : (counitData μ Y).level.H →* Y.Lv.L.H :=
  (MonoidHom.fst _ _).comp ((counitData μ Y).equivT hY).symm.toMonoidHom

lemma counitR_equivT (t : (counitData μ Y).T) :
    counitR hY ((counitData μ Y).equivT hY t) = t.1 := by
  simp [counitR]

/-- **The morphism of levels of the counit.** -/
def counitφ : (counitData μ Y).level ⟶ Y.Lv.L where
  f := counitF
  r := counitR hY
  r_a g := by
    obtain ⟨t, rfl⟩ := ((counitData μ Y).equivT hY).surjective g
    rw [counitR_equivT]
    rfl
  f_σ g b := by
    obtain ⟨t, rfl⟩ := ((counitData μ Y).equivT hY).surjective g
    rw [counitR_equivT]
    refine (counitData μ Y).ext_ev fun x => ?_
    rw [ev_equivT, ev_counitF, ev_counitF]
    erw [FiniteLevel.bcσ_bcι]
    congr 1
    change ((x : SemilinearAut R A Y.Lv.L.B)⁻¹ * (t.1 : SemilinearAut R A Y.Lv.L.B)).σ b =
      ((Y.Lv.L.bcPr μ t.2 : SemilinearAut R A Y.Lv.L.B) *
        ((t.1⁻¹ * x * Y.Lv.L.bcPr μ t.2 : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B)⁻¹).σ b
    have h : (x : SemilinearAut R A Y.Lv.L.B)⁻¹ * (t.1 : SemilinearAut R A Y.Lv.L.B) =
        (Y.Lv.L.bcPr μ t.2 : SemilinearAut R A Y.Lv.L.B) *
          ((t.1⁻¹ * x * Y.Lv.L.bcPr μ t.2 : Y.Lv.L.H) : SemilinearAut R A Y.Lv.L.B)⁻¹ := by
      rw [← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_inv, ← Subgroup.coe_mul]
      congr 1
      group
    rw [h]

/-- The model map of the counit: the copy `x` through `ρ x`. -/
def counitψ : (counitData μ Y).c.scheme ⟶ Y.Lv.c.scheme :=
  (SemistableReduction.ModelCode.sigmaIso
    (fun _ : (counitData μ Y).S => (Y.baseChange μ).Lv.c)).inv ≫
    Sigma.desc fun x => (Y.Lv.ρ x).hom

@[reassoc]
lemma inc_counitψ (x : Y.Lv.L.H) :
    (counitData μ Y).inc x ≫ counitψ = (Y.Lv.ρ x).hom := by
  simp only [counitψ, SemistableReduction.ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ _

lemma counitψ_toSpec : counitψ ≫ Y.Lv.c.toSpec = (counitData μ Y).c.toSpec :=
  (counitData μ Y).c_hom_ext fun (x : Y.Lv.L.H) => by
    rw [inc_counitψ_assoc]
    exact (Y.Lv.ρ_toSpec x).trans ((counitData μ Y).inc_toSpec x).symm

lemma counit_j_ψ : (counitData μ Y).j ≫ counitψ =
    Spec.map (CommRingCat.ofHom ((counitF (μ := μ) (Y := Y)) :
      Y.Lv.L.B →+* (counitData μ Y).level.B)) ≫ Y.Lv.j := by
  refine (counitData μ Y).hom_ext fun (x : Y.Lv.L.H) => ?_
  have hring : ((counitData μ Y).ev x).comp
      ((counitF (μ := μ) (Y := Y)) : Y.Lv.L.B →+* (counitData μ Y).level.B) =
      (Y.Lv.L.bcι μ).comp ((x : SemilinearAut R A Y.Lv.L.B).σ.symm : Y.Lv.L.B →+* Y.Lv.L.B) :=
    RingHom.ext fun b => ev_counitF x b
  rw [specMap_ev_j_assoc, inc_counitψ, ← Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, hring]
  change (Spec.map (CommRingCat.ofHom (Y.Lv.L.bcι μ)) ≫ Y.Lv.j) ≫ (Y.Lv.ρ x).hom = _
  simp only [Category.assoc]
  refine (congrArg (Spec.map (CommRingCat.ofHom (Y.Lv.L.bcι μ)) ≫ ·) (Y.Lv.ρ_j x).symm).trans ?_
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

/-- The covering map of the counit: `(z, p) ↦ x • p` for `z` on the copy `x`. -/
def counitH (q : ((counitData μ Y).obj hY).P.carrier) : Y.P.carrier :=
  Y.P.act ((counitData μ Y).copy q.1.1.1)
    (CoveringCode.pullbackPt (Y.baseChange μ).P ((counitData μ Y).foldS hY) q)

lemma continuous_counitH : Continuous (counitH hY) := by
  rw [continuous_iff_continuousAt]
  intro q
  set x := (counitData μ Y).copy q.1.1.1
  have hc : Continuous fun q' : ((counitData μ Y).obj hY).P.carrier =>
      Y.P.act x (CoveringCode.pullbackPt (Y.baseChange μ).P ((counitData μ Y).foldS hY) q') :=
    (Y.P.act x).continuous.comp (CoveringCode.continuous_pullbackPt _)
  refine hc.continuousAt.congr ?_
  have hU : IsOpen {q' : ((counitData μ Y).obj hY).P.carrier |
      (counitData μ Y).copy q'.1.1.1 = x} :=
    ((counitData μ Y).isOpen_copy x).preimage
      (continuous_subtype_val.comp ((counitData μ Y).obj hY).P.continuous_proj)
  filter_upwards [hU.mem_nhds rfl] with q' hq'
  simp only [counitH]
  rw [hq']


lemma copy_act (g : ((counitData μ Y).obj hY).Lv.L.H) (q : ((counitData μ Y).obj hY).P.carrier) :
    (counitData μ Y).copy (((counitData μ Y).obj hY).P.act g q).1.1.1 =
      (((counitData μ Y).equivT hY).symm g).1 * (counitData μ Y).copy q.1.1.1 *
        (Y.Lv.L.bcPr μ (((counitData μ Y).equivT hY).symm g).2)⁻¹ := by
  obtain ⟨w, hw⟩ := (counitData μ Y).exists_inc_copy q.1.1.1
  have h : (((counitData μ Y).obj hY).P.act g q).1.1.1 =
      (counitData μ Y).actHom (((counitData μ Y).equivT hY).symm g) q.1.1.1 := rfl
  rw [h]
  conv_lhs => rw [← hw, ← Scheme.Hom.comp_apply, inc_actHom, Scheme.Hom.comp_apply, copy_inc]
  rfl

/-- **The counit** `Ind_H (bc Y) ⟶ Y`. -/
def counitHom : (counitData μ Y).obj hY ⟶ Y where
  φ := counitφ hY
  ψ := counitψ
  ψ_toSpec := counitψ_toSpec
  j_ψ := counit_j_ψ
  h := counitH hY
  continuous_h := continuous_counitH hY
  fst_h q := by
    obtain ⟨w, hw⟩ := (counitData μ Y).exists_inc_copy q.1.1.1
    rw [counitH, Y.P.act_fst, Level.ρs_apply]
    change (Y.Lv.ρ ((counitData μ Y).copy q.1.1.1)).hom ((counitData μ Y).fold q.1.1.1) =
      counitψ q.1.1.1
    rw [← hw, ← Scheme.Hom.comp_apply, inc_fold, ← Scheme.Hom.comp_apply, inc_counitψ, copy_inc]
    rfl
  h_act g q := by
    change Y.P.act _ (CoveringCode.pullbackPt (Y.baseChange μ).P ((counitData μ Y).foldS hY)
      (CoveringCode.pullbackActFun (Y.baseChange μ).P ((counitData μ Y).toH' hY)
        ((counitData μ Y).foldS_ρs hY) g q)) = Y.P.act (counitR hY g) (counitH hY q)
    rw [CoveringCode.pullbackPt_actFun, copy_act]
    change Y.P.act _ (Y.P.act (Y.Lv.L.bcPr μ ((counitData μ Y).toH' hY g)) _) =
      Y.P.act (counitR hY g) (Y.P.act _ _)
    rw [← Homeomorph.mul_apply, ← map_mul, ← Homeomorph.mul_apply, ← map_mul]
    congr 2
    obtain ⟨t, rfl⟩ := ((counitData μ Y).equivT hY).surjective g
    rw [toH'_equivT, counitR_equivT, MulEquiv.symm_apply_apply]
    group

end Counit


section CounitFibre

variable [Finite A] (Y : TempObj O R A) [Fintype Y.Lv.L.H] [DecidableEq Y.Lv.L.H]
  (hY : IndFaithful (Y.baseChange μ))
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The group map `H → A` of the counit span. -/
abbrev counitθ : (counitData μ Y).S →* (pushData μ (Y.baseChange μ)).S :=
  SemilinearAut.toA.comp Y.Lv.L.H.subtype

lemma counitθα (x : (counitData μ Y).S) :
    (pushData μ (Y.baseChange μ)).α (counitθ Y x) = (counitData μ Y).α x := rfl

lemma counitθβ (k : (Y.baseChange μ).Lv.L.H) :
    counitθ Y ((counitData μ Y).β k) =
      (pushData μ (Y.baseChange μ)).β ((𝟙 (Y.baseChange μ) : _ ⟶ _).φ.r k) :=
  Y.Lv.L.bcPr_a μ k

/-- **The span leg** `Ind_H (bc Y) ⟶ Ind_A (bc Y)`. -/
def counitπ₁ : (counitData μ Y).obj hY ⟶ (pushData μ (Y.baseChange μ)).obj hY :=
  hom (counitData μ Y) (pushData μ (Y.baseChange μ)) hY hY (𝟙 _) (counitθ Y) (counitθα Y)
    (counitθβ Y)

lemma counitHom_ι (z : TempObj.Fibre Ω V hV (Y.baseChange μ)) :
    TempObj.fibreMap V hV (counitHom hY) ((counitData μ Y).ι hY V hV z) =
      TempObj.bcFibreEquiv μ V hV Y z := by
  induction z using Quotient.inductionOn with
  | h q =>
    refine congrArg Quotient.mk'' (Subtype.ext (Prod.ext ?_ ?_))
    · ext b
      change q.1.1 ((counitData μ Y).ev 1 (counitF b)) = q.1.1 (Y.Lv.L.bcι μ b)
      rw [ev_counitF]
      rfl
    · change Y.P.act ((counitData μ Y).copy ((counitData μ Y).inc₁S hY q.1.2.1.1).1)
        (CoveringCode.pullbackPt (Y.baseChange μ).P ((counitData μ Y).foldS hY)
          ((counitData μ Y).incP hY q.1.2)) = q.1.2
      rw [pullbackPt_incP, inc₁S_coe, copy_inc]
      change Y.P.act 1 q.1.2 = q.1.2
      rw [map_one]
      rfl


lemma fibreMap_id {X : TempObj O R A'} (x : TempObj.Fibre Ω V hV X) :
    TempObj.fibreMap V hV (𝟙 X) x = x := by
  induction x using Quotient.inductionOn with
  | h q => rfl

/-- **The counit span on fibres**: a fibre element of `Ind_H (bc Y)` over `ι z` in `Ind_A (bc Y)`
maps to `z` in `Y`. -/
lemma counit_fibre (hα : Function.Injective μ.α)
    (w : TempObj.Fibre Ω V hV ((counitData μ Y).obj hY))
    (z : TempObj.Fibre Ω V hV (Y.baseChange μ))
    (h : TempObj.fibreMap V hV (counitπ₁ Y hY) w = (pushData μ (Y.baseChange μ)).ι hY V hV z) :
    TempObj.fibreMap V hV (counitHom hY) w = TempObj.bcFibreEquiv μ V hV Y z := by
  induction w using Quotient.inductionOn with
  | h q =>
  obtain ⟨x, t₀, ht⟩ := (counitData μ Y).exists_comp_ev
    (q.1.1 : ((counitData μ Y).obj hY).Lv.L.B →+* Ω)
  have hz := h
  induction z using Quotient.inductionOn with
  | h z =>
  set D₂ := pushData μ (Y.baseChange μ)
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact hz.symm)
  obtain ⟨⟨s, k⟩, htg⟩ := (D₂.equivT hY).surjective g.1
  have hs : s = 1 := by
    have := D₂.equivT_symm_mem_H0 hY g.2
    rwa [← htg, MulEquiv.symm_apply_apply] at this
  have hpre : ((TempObj.preMap V hV (counitπ₁ Y hY) q).1.1 : (D₂.obj hY).Lv.L.B →+* Ω) =
      t₀.comp (D₂.ev (counitθ Y x)) := by
    refine RingHom.ext fun y => ?_
    exact (RingHom.congr_fun ht _).trans
      (congrArg t₀ (ev_homF (counitData μ Y) D₂ (𝟙 _) (counitθ Y) (counitθα Y) x y))
  have h1 := D₂.comp_σ_symm hY hpre s k
  have h2 : ((z.1.1 : (Y.baseChange μ).Lv.L.B →+* Ω)).comp (D₂.ev 1) =
      ((TempObj.preMap V hV (counitπ₁ Y hY) q).1.1 : (D₂.obj hY).Lv.L.B →+* Ω).comp
        (((D₂.equivT hY (s, k) : D₂.level.H) : SemilinearAut R A D₂.level.B).σ.symm :
          D₂.level.B →+* D₂.level.B) := by
    refine RingHom.ext fun y => ?_
    have := congrArg (fun q' : TempObj.PreFibre Ω V hV (D₂.obj hY) => q'.1.1 y) hg
    refine this.symm.trans ?_
    change (TempObj.preMap V hV (counitπ₁ Y hY) q).1.1 (g.1.1.σ.symm y) = _
    rw [← htg]
    rfl
  have hcomp := D₂.eq_of_comp_ev (h2.trans h1)
  rw [hs, one_mul, eq_comm, mul_inv_eq_one] at hcomp
  have hxa : (x : SemilinearAut R A Y.Lv.L.B).a = μ.α k.1.a := hcomp
  let k₂ : (Y.baseChange μ).Lv.L.H := Y.Lv.L.bcEquiv μ ⟨(x, k.1.a), hxa⟩
  have hk₂ : (counitData μ Y).β k₂ = x := FiniteLevel.bcPr_bcEquiv μ _ _
  obtain ⟨z', hz'⟩ := (counitData μ Y).mem_range_ι hY V hV q k₂ t₀ (by rw [hk₂]; exact ht)
  change TempObj.fibreMap V hV (counitHom hY) (Quotient.mk'' q) =
    TempObj.bcFibreEquiv μ V hV Y (Quotient.mk'' z)
  rw [← hz', counitHom_ι]
  congr 1
  apply D₂.ι_injective hY V hV hα
  rw [← fibreMap_id V hV z', ι_natural (D₁ := counitData μ Y) (D₂ := D₂) (hX₁ := hY) (hX₂ := hY)
    (m := 𝟙 _) (θ := counitθ Y) (hθα := counitθα Y) (hθβ := counitθβ Y), hz']
  exact hz

end CounitFibre

end IndData
