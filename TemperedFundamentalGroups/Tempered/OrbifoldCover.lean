/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.FibreFunctor.SpanPushRestrict
import TemperedFundamentalGroups.Tempered.Comparison
import TemperedFundamentalGroups.Tempered.InducedCounit
import TemperedFundamentalGroups.Andre.Refinement

/-!
# Orbifold covers: `temperedPi1Map` is injective with open image of finite index
(Blueprint §11, F7′)

Let `μ : OrbMap R A R A'` be an orbifold cover `[Spec R / A'] → [Spec R / A]` (`R = R'`,
`μ.α : A' →* A`), with `A` finite, `R` a noetherian domain, `A'` acting faithfully on `R` and
`A` acting `K`-linearly. Then `temperedPi1Map μ` is injective, an open embedding, with image the
stabilizer of the base point of the cover `[Spec R / A'] → [Spec R / A]`, of finite index
(`temperedPi1Map_injective_orbifold`, `range_temperedPi1Map_orbifold`,
`isOpenEmbedding_temperedPi1Map_orbifold`, `finiteIndex_range_temperedPi1Map_orbifold`).

Proof: the criterion `SpanPushData` (`FibreFunctor/SpanPushRestrict.lean`) with

* good objects: tempered coverings whose algebra `B'` is faithful over `R` (all others have empty
  fibres, since `R` is a domain and `B'` is flat);
* the push `X' ↦ Ind_A X'` (`IndData.pushData`, `Tempered/InducedLevel.lean`), the fibre injection
  `ι` (the copy `1`), the unit `X' ⟶ bc (Ind_A X')` (`IndData.unit`);
* the cover `E = Ind_A 1'` of the trivial covering `1'` of `[Spec R / A']` with its base point,
  `τ = Ind_A (X' ⟶ 1')`;
* the counit span `Ind_A (bc Y) ⟵ Ind_H (bc Y) ⟶ Y` (`IndData.counitπ₁`, `IndData.counitHom`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A' : Type u} [Group A'] [MulSemiringAction A' R] [SMulCommClass A' K R]
  (μ : OrbMap R A R A')

namespace OrbifoldCover

/-! ### Good objects -/

/-- A tempered covering is *good* if its algebra is faithful over `R`. -/
def Good (X' : TempObj O R A') : Prop := Function.Injective (algebraMap R X'.Lv.L.B)

lemma subsingleton_of_not_injective [IsDomain R] {A₀ : Type u} [Group A₀]
    [MulSemiringAction A₀ R] (L : FiniteLevel R A₀) (h : ¬ Function.Injective (algebraMap R L.B)) :
    Subsingleton L.B := by
  haveI := L.etale
  rw [injective_iff_map_eq_zero] at h
  push Not at h
  obtain ⟨r, hr, hr0⟩ := h
  have h1 : r • (1 : L.B) = 0 := (Algebra.algebraMap_eq_smul_one r).symm.trans hr
  rcases smul_eq_zero.1 h1 with h2 | h2
  · exact absurd h2 hr0
  · exact subsingleton_of_zero_eq_one h2.symm

lemma isEmpty_fibre [IsDomain R] {A₀ : Type u} [Group A₀] [MulSemiringAction A₀ R]
    {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
    (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O) (X : TempObj O R A₀)
    (h : ¬ Function.Injective (algebraMap R X.Lv.L.B)) : IsEmpty (TempObj.Fibre Ω V hV X) := by
  haveI := subsingleton_of_not_injective X.Lv.L h
  refine ⟨fun x => ?_⟩
  induction x using Quotient.inductionOn with
  | h q =>
    have := q.1.1.map_one
    rw [Subsingleton.elim (1 : X.Lv.L.B) 0, map_zero] at this
    exact zero_ne_one this

variable {μ}

lemma indFaithful [IsDomain R] [FaithfulSMul A' R] {X' : TempObj O R A'} (hX : Good X') :
    IndFaithful X' where
  nontrivial := hX.nontrivial
  faithful k hk := by
    have ha : (k : SemilinearAut R A' X'.Lv.L.B).a = 1 := by
      refine eq_of_smul_eq_smul (α := R) fun r => ?_
      apply hX
      rw [← (k : SemilinearAut R A' X'.Lv.L.B).map_algebraMap, hk, one_smul]
    exact Subtype.ext (SemilinearAut.ext ha (RingEquiv.ext hk))

lemma good_baseChange (Y : TempObj O R A) (hY : Function.Injective (algebraMap R Y.Lv.L.B)) :
    Good (Y.baseChange μ) := by
  intro r s h
  apply hY
  apply Y.Lv.L.bcι_injective μ
  rw [FiniteLevel.bcι_algebraMap, FiniteLevel.bcι_algebraMap]
  exact h

lemma α_injective [FaithfulSMul A' R] : Function.Injective μ.α := by
  intro a b h
  refine eq_of_smul_eq_smul (α := R) fun r => ?_
  rw [← OrbMap.smul_eq μ, ← OrbMap.smul_eq μ, h]

/-! ### The trivial covering of `[Spec R / A']` -/

variable (A') in
/-- The action of `A'` on `R` as semilinear automorphisms. -/
def unitAct : A' →* SemilinearAut R A' R where
  toFun a := ⟨a, MulSemiringAction.toRingEquiv A' R a, fun r => by simp⟩
  map_one' := SemilinearAut.ext rfl (RingEquiv.ext fun r => one_smul A' r)
  map_mul' a b := SemilinearAut.ext rfl (RingEquiv.ext fun r => mul_smul a b r)

variable (R A') in
/-- The trivial finite étale cover `R` of `[Spec R / A']`. -/
def unitEt : EquivEtale R A' := EquivEtale.ofAlgebra (unitAct A') fun _ => rfl

variable (O R A') in
/-- **The trivial tempered covering** `1'` of `[Spec R / A']`. -/
abbrev one : TempObj O R A' := (etaleToTemp O R A').obj (unitEt R A')

/-- The coded trivial cover is `R`. -/
def unitE : (unitEt R A').B ≃ₐ[R] R := EquivEtale.ofAlgebraEquiv _ _

lemma unitE_act (a : A') (y : (unitEt R A').B) :
    unitE (((unitEt R A').act a).σ y) = a • unitE y :=
  EquivEtale.ofAlgebraEquiv_act _ _ a y

/-- The structure map `R → B'`, from the coded trivial cover. -/
def toOneF (L : FiniteLevel R A') : (unitEt R A').B →ₐ[R] L.B :=
  (Algebra.ofId R L.B).comp unitE.toAlgHom

lemma toOneF_apply (L : FiniteLevel R A') (y : (unitEt R A').B) :
    toOneF L y = algebraMap R L.B (unitE y) := rfl

/-- The structure morphism of levels `L ⟶ 1'`. -/
def toOneφ (L : FiniteLevel R A') : L ⟶ (unitEt R A').level where
  f := toOneF L
  r := { toFun := fun k => ⟨(unitEt R A').act (k : SemilinearAut R A' L.B).a, ⟨_, rfl⟩⟩
         map_one' := by ext1; simp
         map_mul' := fun k k' => by ext1; simp }
  r_a k := (unitEt R A').act_a _
  f_σ k y := by
    change toOneF L (((unitEt R A').act (k : SemilinearAut R A' L.B).a).σ y) = _
    rw [toOneF_apply, toOneF_apply, unitE_act, (k : SemilinearAut R A' L.B).map_algebraMap]

/-- The model map to the trivial model. -/
abbrev toOneψ (X : TempObj O R A') : X.Lv.c.scheme ⟶ (ModelCode.trivial O).scheme :=
  X.Lv.c.toSpec ≫ inv (ModelCode.trivial O).toSpec

lemma toOneψ_toSpec (X : TempObj O R A') :
    toOneψ X ≫ (ModelCode.trivial O).toSpec = X.Lv.c.toSpec := by
  simp

lemma toOneψ_ρ (X : TempObj O R A') (g : X.Lv.L.H) (z : X.Lv.c.scheme) :
    toOneψ X ((X.Lv.ρ g).hom z) = toOneψ X z := by
  rw [← Scheme.Hom.comp_apply, ← Category.assoc, X.Lv.ρ_toSpec]

/-- The covering map to the one-sheeted covering. -/
def toOneH (X : TempObj O R A') : X.P.carrier → (one O R A').P.carrier := fun x =>
  ⟨(specialFibreMap (toOneψ X) (toOneψ_toSpec X) x.1.1, 0), Set.mem_univ _, Nat.zero_lt_one⟩

lemma continuous_toOneH (X : TempObj O R A') : Continuous (toOneH X) := by
  apply Continuous.subtype_mk
  refine Continuous.prodMk ?_ continuous_const
  exact (continuous_specialFibreMap _ _).comp X.P.continuous_proj

/-- **The structure morphism** `X' ⟶ 1'`. -/
def toOne (X : TempObj O R A') : X ⟶ one O R A' where
  φ := toOneφ X.Lv.L
  ψ := toOneψ X
  ψ_toSpec := toOneψ_toSpec X
  j_ψ := by
    change X.Lv.j ≫ X.Lv.c.toSpec ≫ _ = _ ≫ Spec.map (CommRingCat.ofHom
      (levelStructureMap O R A' (unitEt R A').level)) ≫ inv (ModelCode.trivial O).toSpec
    rw [← Category.assoc, X.Lv.j_toSpec, spec_levelStructureMap O R A' (toOneφ X.Lv.L),
      Category.assoc]
    rfl
  h := toOneH X
  continuous_h := continuous_toOneH X
  fst_h _ := rfl
  h_act g x := by
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) rfl
    change toOneψ X ((X.P.act g x).1.1 : X.Lv.c.scheme) = toOneψ X (x.1.1 : X.Lv.c.scheme)
    rw [X.P.act_fst, Level.ρs_apply, toOneψ_ρ]

lemma comp_toOne {X Y : TempObj O R A'} (m : X ⟶ Y) : m ≫ toOne Y = toOne X := by
  refine TempObj.Hom.ext (FiniteLevel.Hom.ext (AlgHom.ext fun z => ?_) (MonoidHom.ext fun g => ?_))
    ?_ (funext fun x => ?_)
  · change m.φ.f (toOneF Y.Lv.L z) = toOneF X.Lv.L z
    rw [toOneF_apply, toOneF_apply, AlgHom.commutes]
  · apply Subtype.ext
    change (unitEt R A').act ((m.φ.r g : Y.Lv.L.H) : SemilinearAut R A' Y.Lv.L.B).a =
      (unitEt R A').act (g : SemilinearAut R A' X.Lv.L.B).a
    rw [m.φ.r_a]
  · change m.ψ ≫ Y.Lv.c.toSpec ≫ _ = X.Lv.c.toSpec ≫ _
    rw [← Category.assoc, m.ψ_toSpec]
  · apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) rfl
    change toOneψ Y (m.h x).1.1.1 = toOneψ X x.1.1.1
    rw [m.fst_h, ← Scheme.Hom.comp_apply, ← Category.assoc, m.ψ_toSpec]

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma unitE_symm (r : R) : (unitE (A' := A')).symm r = algebraMap R (unitEt R A').B r := by
  rw [← AlgEquiv.commutes unitE.symm r]
  rfl

lemma algHom_unit_ext (t t' : (unitEt R A').B →ₐ[R] Ω) : t = t' := by
  ext y
  rw [← unitE.symm_apply_apply y, unitE_symm, t.commutes, t'.commutes]

variable (A') in
/-- The base point of the trivial covering. -/
def onePt : TempObj.Fibre Ω V hV (one O R A') :=
  (etaleToTempFibreEquiv O R A' V hV (unitEt R A')).symm ((Algebra.ofId R Ω).comp unitE.toAlgHom)

lemma eq_onePt (x : TempObj.Fibre Ω V hV (one O R A')) : x = onePt A' V hV :=
  (etaleToTempFibreEquiv O R A' V hV (unitEt R A')).injective (algHom_unit_ext _ _)

end Fibre

section Push

variable [Finite A] [IsDomain R] [IsNoetherianRing R] [FaithfulSMul A' R]

/-- The level groups are finite. -/
local instance (Y : TempObj O R A) : Fintype Y.Lv.L.H :=
  @Fintype.ofFinite _ Y.Lv.L.finite_H

local instance (Y : TempObj O R A) : DecidableEq Y.Lv.L.H := Classical.decEq _

variable (μ)

/-- The push of a good covering. -/
abbrev P (X' : TempObj O R A') (hX : Good X') : TempObj O R A :=
  (IndData.pushData μ X').obj (indFaithful hX)

lemma pushθβ {X' Y' : TempObj O R A'} (m : X' ⟶ Y') (k : X'.Lv.L.H) :
    MonoidHom.id A ((IndData.pushData μ X').β k) = (IndData.pushData μ Y').β (m.φ.r k) := by
  change μ.α (k : SemilinearAut R A' X'.Lv.L.B).a =
    μ.α ((m.φ.r k : Y'.Lv.L.H) : SemilinearAut R A' Y'.Lv.L.B).a
  rw [m.φ.r_a]

/-- The push of a morphism of good coverings. -/
abbrev Pmap {X' Y' : TempObj O R A'} (hX : Good X') (hY : Good Y') (m : X' ⟶ Y') :
    P μ X' hX ⟶ P μ Y' hY :=
  IndData.hom (IndData.pushData μ X') (IndData.pushData μ Y') (indFaithful hX) (indFaithful hY) m
    (MonoidHom.id A) (fun _ => rfl) (pushθβ μ m)

lemma Pmap_congr {X' Y' : TempObj O R A'} (hX : Good X') (hY : Good Y') {m m' : X' ⟶ Y'}
    (h : m = m') : Pmap μ hX hY m = Pmap μ hX hY m' := by
  subst h
  rfl

lemma Pmap_comp {X' Y' Z' : TempObj O R A'} (hX : Good X') (hY : Good Y') (hZ : Good Z')
    (m : X' ⟶ Y') (m' : Y' ⟶ Z') :
    Pmap μ hX hY m ≫ Pmap μ hY hZ m' = Pmap μ hX hZ (m ≫ m') :=
  IndData.hom_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _

variable {μ}

lemma good_one : Good (one O R A') := by
  intro r s h
  have h' : (unitE (A' := A')).symm r = unitE.symm s := by
    rw [unitE_symm, unitE_symm]
    exact h
  exact unitE.symm.injective h'

end Push

section Range

variable [Finite A] [IsDomain R] [IsNoetherianRing R] [FaithfulSMul A' R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The image of `ι`** is the fibre over the base point of the cover. -/
lemma range_ι (X' : TempObj O R A') (hX : Good X') (y : TempObj.Fibre Ω V hV (P μ X' hX)) :
    (∃ x, (IndData.pushData μ X').ι (indFaithful hX) V hV x = y) ↔
      TempObj.fibreMap V hV (Pmap μ hX good_one (toOne X')) y =
        (IndData.pushData μ (one O R A')).ι (indFaithful good_one) V hV (onePt A' V hV) := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [← IndData.ι_natural, eq_onePt V hV (TempObj.fibreMap V hV (toOne X') x)]
  · intro h
    induction y using Quotient.inductionOn with
    | h q =>
    set D₁ := IndData.pushData μ (one O R A')
    set D := IndData.pushData μ X'
    obtain ⟨x, t₀, ht⟩ := D.exists_comp_ev (q.1.1 : (P μ X' hX).Lv.L.B →+* Ω)
    obtain ⟨q₀, hq₀⟩ := Quotient.exists_rep (onePt (O := O) (R := R) A' V hV)
    rw [← hq₀] at h
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 (Quotient.exact h.symm)
    obtain ⟨⟨s, k⟩, htg⟩ := (D₁.equivT (indFaithful good_one)).surjective g.1
    have hs : s = 1 := by
      have := D₁.equivT_symm_mem_H0 (indFaithful good_one) g.2
      rwa [← htg, MulEquiv.symm_apply_apply] at this
    have hpre : ((TempObj.preMap V hV (Pmap μ hX good_one (toOne X')) q).1.1 :
        (D₁.obj (indFaithful good_one)).Lv.L.B →+* Ω) =
        (t₀.comp ((toOneF X'.Lv.L : (unitEt R A').B →ₐ[R] X'.Lv.L.B) :
          (unitEt R A').B →+* X'.Lv.L.B)).comp (D₁.ev x) := by
      refine RingHom.ext fun y => ?_
      exact (RingHom.congr_fun ht _).trans
        (congrArg t₀ (IndData.ev_homF D D₁ (toOne X') (MonoidHom.id A) (fun _ => rfl) x y))
    have h1 := D₁.comp_σ_symm (indFaithful good_one) hpre s k
    have h2 : ((q₀.1.1 : (one O R A').Lv.L.B →+* Ω)).comp (D₁.ev 1) =
        ((TempObj.preMap V hV (Pmap μ hX good_one (toOne X')) q).1.1 :
          (D₁.obj (indFaithful good_one)).Lv.L.B →+* Ω).comp
          (((D₁.equivT (indFaithful good_one) (s, k) : D₁.level.H) :
            SemilinearAut R A D₁.level.B).σ.symm : D₁.level.B →+* D₁.level.B) := by
      refine RingHom.ext fun y => ?_
      have := congrArg (fun q' : TempObj.PreFibre Ω V hV (D₁.obj (indFaithful good_one)) =>
        q'.1.1 y) hg
      refine this.symm.trans ?_
      change (TempObj.preMap V hV (Pmap μ hX good_one (toOne X')) q).1.1 (g.1.1.σ.symm y) = _
      rw [← htg]
      rfl
    have hcomp := D₁.eq_of_comp_ev (h2.trans h1)
    rw [hs, one_mul, eq_comm, mul_inv_eq_one] at hcomp
    obtain ⟨k', hk'mem, hk'a⟩ := X'.Lv.L.surjective k.1.a
    have hβ : D.β ⟨k', hk'mem⟩ = x := by
      change μ.α k'.a = x
      rw [hk'a]
      exact hcomp.symm
    obtain ⟨z, hz⟩ := D.mem_range_ι (indFaithful hX) V hV q ⟨k', hk'mem⟩ t₀ (by rw [hβ]; exact ht)
    exact ⟨z, hz⟩

end Range

section Data

variable [Finite A] [IsDomain R] [IsNoetherianRing R] [FaithfulSMul A' R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

local instance (Y : TempObj O R A) : Fintype Y.Lv.L.H :=
  @Fintype.ofFinite _ Y.Lv.L.finite_H

local instance (Y : TempObj O R A) : DecidableEq Y.Lv.L.H := Classical.decEq _

variable (μ) in
/-- **The span push data of an orbifold cover.** -/
def spanPushData : SpanPushData (TempObj.bcFunctor (O := O) μ) (TempObj.bcFibreIso μ V hV) where
  good := Good
  empty X' h := isEmpty_fibre V hV X' h
  P := P μ
  Pmap hX hY m := Pmap μ hX hY m
  ι X' hX := (IndData.pushData μ X').ι (indFaithful hX) V hV
  ι_injective X' hX := (IndData.pushData μ X').ι_injective (indFaithful hX) V hV α_injective
  ι_natural hX hY m x := IndData.ι_natural (V := V) (hV := hV) _ _ _ _ m _ _ _ x
  E := P μ (one O R A') good_one
  x₀ := (IndData.pushData μ (one O R A')).ι (indFaithful good_one) V hV (onePt A' V hV)
  τ X' hX := Pmap μ hX good_one (toOne X')
  τ_natural hX hY m := by
    rw [Pmap_comp]
    exact Pmap_congr μ hX good_one (comp_toOne m)
  range_ι X' hX y := range_ι V hV X' hX y
  u X' hX := (IndData.pushData μ X').unit (indFaithful hX)
  u_ι X' hX x := (IndData.pushData μ X').bcFibreEquiv_unit (indFaithful hX) V hV x
  W Y hY := (IndData.counitData μ Y).obj (indFaithful hY)
  π₁ Y hY := IndData.counitπ₁ Y (indFaithful hY)
  π₂ Y hY := IndData.counitHom (indFaithful hY)
  π_surj Y hY z := ⟨(IndData.counitData μ Y).ι (indFaithful hY) V hV z, by
    have := IndData.ι_natural (V := V) (hV := hV) (IndData.counitData μ Y)
      (IndData.pushData μ (Y.baseChange μ)) (indFaithful hY) (indFaithful hY) (𝟙 _)
      (IndData.counitθ Y) (IndData.counitθα Y) (IndData.counitθβ Y) z
    rw [IndData.fibreMap_id] at this
    exact this.symm⟩
  π_ι Y hY z w h := IndData.counit_fibre Y (indFaithful hY) V hV α_injective w z h

end Data

end OrbifoldCover

section Main

variable [Finite A] [IsDomain R] [IsNoetherianRing R] [FaithfulSMul A' R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **F7′: along an orbifold cover, `temperedPi1Map` is injective.** -/
theorem temperedPi1Map_injective_orbifold :
    Function.Injective (temperedPi1Map (O := O) μ V hV) :=
  (OrbifoldCover.spanPushData μ V hV).injective_restrict

/-- **F7′: the image of `temperedPi1Map`** is the stabilizer of the base point of the cover. -/
theorem range_temperedPi1Map_orbifold :
    (temperedPi1Map (O := O) μ V hV).range = (OrbifoldCover.spanPushData μ V hV).stab :=
  (OrbifoldCover.spanPushData μ V hV).range_restrict

/-- **F7′: `temperedPi1Map` is an open embedding.** -/
theorem isOpenEmbedding_temperedPi1Map_orbifold :
    Topology.IsOpenEmbedding (temperedPi1Map (O := O) μ V hV) :=
  (OrbifoldCover.spanPushData μ V hV).isOpenEmbedding_restrict

theorem isOpen_range_temperedPi1Map_orbifold :
    IsOpen (Set.range (temperedPi1Map (O := O) μ V hV)) :=
  (isOpenEmbedding_temperedPi1Map_orbifold μ V hV).isOpen_range

end Main


namespace OrbifoldCover

section FiniteE

variable [Finite A] [IsDomain R] [IsNoetherianRing R] [FaithfulSMul A' R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma unit_eq_algebraMap (y : (unitEt R A').B) : y = algebraMap R _ (unitE y) := by
  rw [← unitE_symm, AlgEquiv.symm_apply_apply]

lemma onCopy_unit (x : A)
    (s : ((IndData.pushData μ (one O R A')).obj (indFaithful good_one)).Lv.L.B →ₐ[R] Ω)
    (s₀ : (unitEt R A').B →+* Ω)
    (hs : (s : ((IndData.pushData μ (one O R A')).obj (indFaithful good_one)).Lv.L.B →+* Ω) =
      s₀.comp ((IndData.pushData μ (one O R A')).ev x))
    (y : (unitEt R A').B) : s₀ y = algebraMap R Ω (x • unitE y) := by
  have h1 := s.commutes (x • unitE y)
  have h2 := RingHom.congr_fun hs
    (algebraMap R (IndData.pushData μ (one O R A')).level.B (x • unitE y))
  rw [← h1]
  refine Eq.trans ?_ h2.symm
  change s₀ y = s₀ (((IndData.pushData μ (one O R A')).E (algebraMap R
    (IndData.pushData μ (one O R A')).level.B (x • unitE y)) :
      (IndData.pushData μ (one O R A')).Alg) x)
  rw [AlgEquiv.commutes]
  change s₀ y = s₀ (algebraMap R (unitEt R A').B ((MonoidHom.id A x)⁻¹ • x • unitE y))
  rw [MonoidHom.id_apply, inv_smul_smul, ← unit_eq_algebraMap]

/-- The fibre of the cover `Ind_A 1'` is finite. -/
lemma finite_fibre_E : Finite (TempObj.Fibre Ω V hV (P μ (one O R A') good_one)) := by
  set D := IndData.pushData μ (one O R A')
  set hD := indFaithful (good_one (O := O) (R := R) (A' := A'))
  haveI hpts : Finite ((D.obj hD).Lv.L.B →ₐ[R] Ω) := by
    refine Finite.of_injective
      (fun t => (D.exists_comp_ev (t : (D.obj hD).Lv.L.B →+* Ω)).choose) fun t t' h => ?_
    obtain ⟨t₀, ht⟩ := (D.exists_comp_ev (t : (D.obj hD).Lv.L.B →+* Ω)).choose_spec
    obtain ⟨t₀', ht'⟩ := (D.exists_comp_ev (t' : (D.obj hD).Lv.L.B →+* Ω)).choose_spec
    simp only at h
    rw [← h] at ht'
    have h0 : t₀ = t₀' := RingHom.ext fun y => by
      exact (onCopy_unit μ _ t t₀ ht y).trans (onCopy_unit μ _ t' t₀' ht' y).symm
    refine AlgHom.ext fun y => ?_
    have e1 := RingHom.congr_fun ht y
    have e2 := RingHom.congr_fun ht' y
    rw [h0] at e1
    exact e1.trans e2.symm
  haveI : Finite (TempObj.PreFibre Ω V hV (D.obj hD)) := by
    refine Finite.of_injective (fun q => q.1.1) fun q q' h => ?_
    simp only at h
    refine Subtype.ext (Prod.ext h ?_)
    refine CoveringCode.pullback_ext (one O R A').P (D.foldS hD) (Subtype.ext ?_) ?_
    · rw [q.2, q'.2, h]
    · have h1 := (q.1.2).2.2
      have h2 := (q'.1.2).2.2
      simp only [Set.mem_setOf_eq, Nat.lt_one_iff] at h1 h2
      rw [h1, h2]
  exact Quotient.finite _

end FiniteE

end OrbifoldCover

section Main'

variable [Finite A] [IsDomain R] [IsNoetherianRing R] [FaithfulSMul A' R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **F7′: the image of `temperedPi1Map` has finite index.** -/
theorem finiteIndex_range_temperedPi1Map_orbifold :
    (temperedPi1Map (O := O) μ V hV).range.FiniteIndex :=
  haveI : Finite ((tempFibre O R A V hV).obj (OrbifoldCover.spanPushData μ V hV).E) :=
    OrbifoldCover.finite_fibre_E (μ := μ) V hV
  (OrbifoldCover.spanPushData μ V hV).finiteIndex_range_restrict

end Main'

end

end TemperedFundamentalGroups
