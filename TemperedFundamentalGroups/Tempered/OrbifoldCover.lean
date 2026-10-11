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

end OrbifoldCover

end

end TemperedFundamentalGroups
