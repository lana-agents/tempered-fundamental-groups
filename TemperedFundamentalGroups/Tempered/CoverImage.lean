/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.FibreFunctor.PushRestrict
import TemperedFundamentalGroups.Tempered.Comparison
import TemperedFundamentalGroups.Tempered.PushLevel

/-!
# Finite étale covers: `temperedPi1Map` is injective with open image of finite index
(Blueprint §11, F7)

Scheme case: `A`, `A'` trivial, `R'` finite étale over `R`, `μ : OrbMap R A R' A'`. The push
functor (`TempObj.pushFunctor`, restriction of scalars along `Spec R' → Spec R`) provides the
data of `PushData` for the base change functor:

* `ι`: a fibre element `(t', p)` of `X'` (with `t'` over `R'`) gives the fibre element
  `(t'|_R, p)` of `push X'`;
* `E`: the cover `Spec R' → Spec R` itself (`coverObj`, with trivial model and one sheet), with
  the base point `x₀ = (R' → Ω)`; `τ : push X' ⟶ E` is the structure map; the image of `ι` is
  the set of fibre elements over `x₀` (those `t` which are `R'`-linear);
* `π : push (bc Y) ⟶ Y` (`b ↦ 1 ⊗ b`) and `u : X' ⟶ bc (push X')` (`r' ⊗ b ↦ r' b`).

Hence (`temperedPi1Map_injective`, `range_temperedPi1Map`, `isOpen_range_temperedPi1Map`,
`finiteIndex_range_temperedPi1Map`): `temperedPi1 O R' A' V hV` is an open subgroup of finite
index of `temperedPi1 O R A V hV`, the stabilizer of the base point of the cover.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R']
  {A' : Type u} [Group A'] [Subsingleton A'] [MulSemiringAction A' R']
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

variable (R A R') in
/-- **The cover** `Spec R' → Spec R` as a (coded) finite étale `R`-algebra with trivial action. -/
def coverEt : EquivEtale R A where
  toEtaleCode := FiniteLevel.codeOf (R' := R) R'
  act := 1
  act_a _ := Subsingleton.elim _ _

variable (R A R') in
/-- The coded cover is `R'`. -/
def coverE : (coverEt R A R').B ≃ₐ[R] R' := EquivEtale.presEquiv R R'

namespace FiniteLevel

variable (R A) in
/-- A geometric point of `B'` over `R'`, as a geometric point of the pushed level over `R`. -/
def pushRes (L' : FiniteLevel R' A') (t : L'.B →ₐ[R'] Ω) : (L'.push R A).B →ₐ[R] Ω :=
  (t.restrictScalars R).comp (L'.pushE R A).toAlgHom

lemma pushRes_apply (L' : FiniteLevel R' A') (t : L'.B →ₐ[R'] Ω) (x : (L'.push R A).B) :
    L'.pushRes R A t x = t (L'.pushE R A x) := rfl

lemma pushRes_injective (L' : FiniteLevel R' A') :
    Function.Injective (L'.pushRes (Ω := Ω) R A) := by
  intro t₁ t₂ h
  ext y
  have := congrArg (fun t => t ((L'.pushE R A).symm y)) h
  simpa [pushRes_apply] using this

lemma pushRes_fibreAct (L' : FiniteLevel R' A') (g : L'.H0) (t : L'.B →ₐ[R'] Ω) :
    L'.pushRes R A (fibreAct Ω L' g t) =
      fibreAct Ω (L'.push R A) ⟨L'.pushEquiv R A g, mem_H0.2 (Subsingleton.elim _ _)⟩
        (L'.pushRes R A t) := by
  ext x
  simp only [pushRes_apply, fibreAct_apply]
  congr 1
  apply ((g : L'.H) : SemilinearAut R' A' L'.B).σ.injective
  rw [RingEquiv.apply_symm_apply]
  have := pushEquiv_symm_σ L' (L'.pushEquiv R A g) (L'.pushE R A
    ((((L'.pushEquiv R A g : (L'.push R A).H) : SemilinearAut R A (L'.push R A).B).σ.symm x)))
  rw [MulEquiv.symm_apply_apply] at this
  rw [this, AlgEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]

lemma pushRes_pushMap {L' M' : FiniteLevel R' A'} (φ : L' ⟶ M') (t : L'.B →ₐ[R'] Ω) :
    M'.pushRes R A (t.comp φ.f) = (L'.pushRes R A t).comp (pushMap R A φ).f := by
  ext x
  simp [pushRes_apply, pushMap_f]

end FiniteLevel

namespace TempObj

lemma push_sp (X : TempObj O R' A') (t : X.Lv.L.B →ₐ[R'] Ω) :
    (X.push R A).Lv.sp V hV (X.Lv.L.pushRes R A t) = X.Lv.sp V hV t := by
  unfold Level.sp
  congr 1
  change Spec.map _ ≫ Spec.map _ ≫ X.Lv.j = Spec.map _ ≫ X.Lv.j
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  refine congrArg CommRingCat.ofHom (RingHom.ext fun y => ?_)
  change X.Lv.L.pushRes R A t ((X.Lv.L.pushE R A).symm y) = t y
  rw [FiniteLevel.pushRes_apply, AlgEquiv.apply_symm_apply]

variable (R A) in
/-- `ι` on pairs. -/
def pushPre (X : TempObj O R' A') (q : PreFibre Ω V hV X) : PreFibre Ω V hV (X.push R A) :=
  ⟨(X.Lv.L.pushRes R A q.1.1, q.1.2), by rw [push_sp]; exact q.2⟩

lemma pushPre_smul (X : TempObj O R' A') (g : X.Lv.L.H0) (q : PreFibre Ω V hV X) :
    pushPre R A V hV X (g • q) =
      (⟨X.Lv.L.pushEquiv R A g, FiniteLevel.mem_H0.2 (Subsingleton.elim _ _)⟩ :
        (X.push R A).Lv.L.H0) • pushPre R A V hV X q := by
  apply Subtype.ext
  simp only [pushPre, smul_val]
  refine Prod.ext (FiniteLevel.pushRes_fibreAct X.Lv.L g q.1.1) ?_
  change X.P.act (g : X.Lv.L.H) q.1.2 =
    X.P.act ((X.Lv.L.pushEquiv R A).symm (X.Lv.L.pushEquiv R A g)) q.1.2
  rw [MulEquiv.symm_apply_apply]

variable (R A) in
/-- **`ι`**: the fibre of `X'` injects into the fibre of `push X'`. -/
def pushι (X : TempObj O R' A') : Fibre Ω V hV X → Fibre Ω V hV (X.push R A) :=
  Quotient.map (pushPre R A V hV X) fun q q' ⟨g, hg⟩ => by
    rw [← hg, pushPre_smul]
    exact ⟨_, rfl⟩

lemma pushι_mk (X : TempObj O R' A') (q : PreFibre Ω V hV X) :
    pushι R A V hV X (Quotient.mk'' q) = Quotient.mk'' (pushPre R A V hV X q) := rfl

lemma pushι_injective (X : TempObj O R' A') : Function.Injective (pushι R A V hV X) := by
  intro x y h
  induction x using Quotient.inductionOn with | h q => ?_
  induction y using Quotient.inductionOn with | h q' => ?_
  obtain ⟨g, hg⟩ := Quotient.exact h
  let g' : X.Lv.L.H0 := ⟨(X.Lv.L.pushEquiv R A).symm g.1, FiniteLevel.mem_H0.2
    (Subsingleton.elim _ _)⟩
  have h1 : pushPre R A V hV X (g' • q') = pushPre R A V hV X q := by
    rw [pushPre_smul, ← hg]
    congr 1
    apply Subtype.ext
    exact (X.Lv.L.pushEquiv R A).apply_symm_apply g.1
  apply Quotient.sound
  refine ⟨g', ?_⟩
  apply Subtype.ext
  have h2 := congrArg Subtype.val h1
  simp only [pushPre] at h2
  exact Prod.ext (FiniteLevel.pushRes_injective X.Lv.L (Prod.ext_iff.1 h2).1)
    (Prod.ext_iff.1 h2).2

lemma pushι_natural {X Y : TempObj O R' A'} (m : X ⟶ Y) (x : Fibre Ω V hV X) :
    pushι R A V hV Y (fibreMap V hV m x) =
      fibreMap V hV (pushHom R A m) (pushι R A V hV X x) := by
  induction x using Quotient.inductionOn with | h q => ?_
  apply congrArg Quotient.mk''
  apply Subtype.ext
  exact Prod.ext (FiniteLevel.pushRes_pushMap m.φ q.1.1) rfl

end TempObj

section Cover

variable [SMulCommClass A K R]

variable (O R A R') in
/-- **The cover** `Spec R' → Spec R` as a tempered covering (trivial model, one sheet). -/
abbrev coverObj : TempObj O R A := (etaleToTemp O R A).obj (coverEt R A R')

variable (R A R' Ω) in
/-- The base point `R' → Ω` of the cover. -/
def coverPt : (coverEt R A R').B →ₐ[R] Ω :=
  ((Algebra.ofId R' Ω).restrictScalars R).comp (coverE R A R').toAlgHom

/-- The base point of the cover, as a fibre element. -/
def coverFibrePt : TempObj.Fibre Ω V hV (coverObj O R A R') :=
  (etaleToTempFibreEquiv O R A V hV (coverEt R A R')).symm (coverPt R A R' Ω)

namespace FiniteLevel

/-- The structure map `R' → B'`, as a map from the coded cover to the pushed level. -/
def coverMapF (L' : FiniteLevel R' A') : (coverEt R A R').B →ₐ[R] (L'.push R A).B :=
  (L'.pushE R A).symm.toAlgHom.comp
    ((IsScalarTower.toAlgHom R R' L'.B).comp (coverE R A R').toAlgHom)

lemma coverMapF_apply (L' : FiniteLevel R' A') (y : (coverEt R A R').B) :
    L'.coverMapF y = (L'.pushE R A).symm (algebraMap R' L'.B (coverE R A R' y)) := rfl

/-- The structure morphism of levels `push L' ⟶ cover`. -/
def coverMap (L' : FiniteLevel R' A') : L'.push R A ⟶ (coverEt R A R').level where
  f := L'.coverMapF
  r := 1
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    change L'.coverMapF y = _
    rw [coverMapF_apply]
    apply (L'.pushE R A).injective
    rw [AlgEquiv.apply_symm_apply, ← pushEquiv_symm_σ, SemilinearAut.σ_algebraMap_of_a_eq_one
      (Subsingleton.elim _ _)]

end FiniteLevel

namespace TempObj

/-- The model map to the trivial model. -/
abbrev coverψ (X : TempObj O R' A') : X.Lv.c.scheme ⟶ (ModelCode.trivial O).scheme :=
  X.Lv.c.toSpec ≫ inv (ModelCode.trivial O).toSpec

lemma coverψ_toSpec (X : TempObj O R' A') :
    X.coverψ ≫ (ModelCode.trivial O).toSpec = X.Lv.c.toSpec := by
  simp

lemma coverψ_ρ (X : TempObj O R' A') (g : X.Lv.L.H) (z : X.Lv.c.scheme) :
    X.coverψ ((X.Lv.ρ g).hom z) = X.coverψ z := by
  rw [← Scheme.Hom.comp_apply, ← Category.assoc, X.Lv.ρ_toSpec]

/-- The covering map to the one-sheeted covering. -/
def coverH (X : TempObj O R' A') : X.P.carrier → (coverObj O R A R').P.carrier := fun x =>
  ⟨(specialFibreMap X.coverψ X.coverψ_toSpec x.1.1, 0), Set.mem_univ _, Nat.zero_lt_one⟩

lemma continuous_coverH (X : TempObj O R' A') : Continuous (X.coverH (R := R) (A := A)) := by
  apply Continuous.subtype_mk
  refine Continuous.prodMk ?_ continuous_const
  exact (continuous_specialFibreMap _ _).comp X.P.continuous_proj

lemma coverH_act (X : TempObj O R' A') (g : X.Lv.L.H) (x : X.P.carrier) :
    X.coverH (R := R) (A := A) (X.P.act g x) = X.coverH x := by
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) rfl
  change X.coverψ ((X.P.act g x).1.1 : X.Lv.c.scheme) = X.coverψ (x.1.1 : X.Lv.c.scheme)
  rw [X.P.act_fst, Level.ρs_apply, coverψ_ρ]

lemma coverObj_act_one (y : (coverObj O R A R').P.carrier) :
    (coverObj O R A R').P.act 1 y = y := by
  rw [map_one]
  rfl

lemma coverObj_j : (coverObj O R A R').Lv.j =
    Spec.map (CommRingCat.ofHom (levelStructureMap O R A (coverEt R A R').level)) ≫
      inv (ModelCode.trivial O).toSpec := rfl

lemma push_j_toSpec (X : TempObj O R' A') :
    (Spec.map (CommRingCat.ofHom
      ((X.Lv.L.pushE R A).symm : X.Lv.L.B →+* (X.Lv.L.push R A).B)) ≫ X.Lv.j) ≫
        X.Lv.c.toSpec =
      Spec.map (CommRingCat.ofHom (levelStructureMap O R A (X.Lv.L.push R A))) :=
  (X.push R A).Lv.j_toSpec

lemma cover_j_ψ (X : TempObj O R' A') :
    (Spec.map (CommRingCat.ofHom
      ((X.Lv.L.pushE R A).symm : X.Lv.L.B →+* (X.Lv.L.push R A).B)) ≫ X.Lv.j) ≫
        X.Lv.c.toSpec ≫ inv (ModelCode.trivial O).toSpec =
      Spec.map (CommRingCat.ofHom ((FiniteLevel.coverMap (R := R) (A := A) X.Lv.L).f :
        (coverEt R A R').B →+* (X.Lv.L.push R A).B)) ≫
        Spec.map (CommRingCat.ofHom (levelStructureMap O R A (coverEt R A R').level)) ≫
          inv (ModelCode.trivial O).toSpec := by
  rw [← Category.assoc, push_j_toSpec, spec_levelStructureMap O R A X.Lv.L.coverMap,
    Category.assoc]

variable (R A) in
/-- **The structure morphism** `push X' ⟶ cover`. -/
def coverHom (X : TempObj O R' A') : X.push R A ⟶ coverObj O R A R' where
  φ := X.Lv.L.coverMap
  ψ := X.coverψ
  ψ_toSpec := X.coverψ_toSpec
  j_ψ := X.cover_j_ψ (R := R) (A := A)
  h := X.coverH
  continuous_h := X.continuous_coverH
  fst_h _ := rfl
  h_act g x := by
    have h1 : (coverObj O R A R').P.act (X.Lv.L.coverMap.r g) (X.coverH x) = X.coverH x :=
      coverObj_act_one _
    exact (X.coverH_act _ x).trans h1.symm

lemma coverHom_natural {X Y : TempObj O R' A'} (m : X ⟶ Y) :
    pushHom R A m ≫ coverHom R A Y = coverHom R A X := by
  refine Hom.ext (FiniteLevel.Hom.ext (AlgHom.ext fun z => ?_) (MonoidHom.ext fun g => ?_))
    ?_ (funext fun x => ?_)
  · change (FiniteLevel.pushMap R A m.φ).f (Y.Lv.L.coverMapF z) = X.Lv.L.coverMapF z
    rw [FiniteLevel.pushMap_f, FiniteLevel.coverMapF_apply, FiniteLevel.coverMapF_apply,
      AlgEquiv.apply_symm_apply, AlgHom.commutes]
  · apply Subtype.ext
    rw [(coverEt R A R').eq_act_of_mem ((_ : (coverEt R A R').level.H)).2,
      (coverEt R A R').eq_act_of_mem ((_ : (coverEt R A R').level.H)).2]
    rfl
  · change m.ψ ≫ Y.Lv.c.toSpec ≫ _ = X.Lv.c.toSpec ≫ _
    rw [← Category.assoc, m.ψ_toSpec]
  · apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) rfl
    change Y.coverψ (m.h x).1.1.1 = X.coverψ x.1.1.1
    rw [m.fst_h, ← Scheme.Hom.comp_apply, ← Category.assoc, m.ψ_toSpec]

variable (Ω) in
lemma coverFib_coverHom (X : TempObj O R' A') (q : PreFibre Ω V hV (X.push R A)) :
    etaleToTempFibreEquiv O R A V hV (coverEt R A R')
      (fibreMap V hV (coverHom R A X) (Quotient.mk'' q)) = q.1.1.comp X.Lv.L.coverMapF := rfl

lemma coverFibrePt_eq_iff (X : TempObj O R' A') (y : Fibre Ω V hV (X.push R A)) :
    fibreMap V hV (coverHom R A X) y = coverFibrePt V hV ↔
      etaleToTempFibreEquiv O R A V hV (coverEt R A R') (fibreMap V hV (coverHom R A X) y) =
        coverPt R A R' Ω :=
  Equiv.eq_symm_apply _

lemma pushRes_comp_coverMapF (X : TempObj O R' A') (t : X.Lv.L.B →ₐ[R'] Ω) :
    (X.Lv.L.pushRes R A t).comp X.Lv.L.coverMapF = coverPt R A R' Ω := by
  ext z
  simp only [AlgHom.comp_apply, FiniteLevel.pushRes_apply, FiniteLevel.coverMapF_apply,
    AlgEquiv.apply_symm_apply, AlgHom.commutes]
  rfl

/-- The `R'`-linear geometric point attached to a geometric point over the base point. -/
def pushUnres (X : TempObj O R' A') (t : (X.Lv.L.push R A).B →ₐ[R] Ω)
    (h : t.comp X.Lv.L.coverMapF = coverPt R A R' Ω) : X.Lv.L.B →ₐ[R'] Ω :=
  { (t : (X.Lv.L.push R A).B →+* Ω).comp ((X.Lv.L.pushE R A).symm : X.Lv.L.B →+* _) with
    commutes' := fun r => by
      have := AlgHom.congr_fun h ((coverE R A R').symm r)
      simp only [AlgHom.comp_apply, FiniteLevel.coverMapF_apply, AlgEquiv.apply_symm_apply,
        coverPt, AlgHom.coe_restrictScalars', AlgEquiv.coe_toAlgHom, Algebra.ofId_apply] at this
      exact this }

lemma pushRes_pushUnres (X : TempObj O R' A') (t : (X.Lv.L.push R A).B →ₐ[R] Ω)
    (h : t.comp X.Lv.L.coverMapF = coverPt R A R' Ω) :
    X.Lv.L.pushRes R A (X.pushUnres t h) = t := by
  ext x
  change t ((X.Lv.L.pushE R A).symm (X.Lv.L.pushE R A x)) = t x
  rw [AlgEquiv.symm_apply_apply]

lemma range_pushι (X : TempObj O R' A') (y : Fibre Ω V hV (X.push R A)) :
    (∃ x, pushι R A V hV X x = y) ↔ fibreMap V hV (coverHom R A X) y = coverFibrePt V hV := by
  rw [coverFibrePt_eq_iff]
  constructor
  · rintro ⟨x, rfl⟩
    induction x using Quotient.inductionOn with | h q' => ?_
    rw [pushι_mk, coverFib_coverHom]
    exact X.pushRes_comp_coverMapF q'.1.1
  · induction y using Quotient.inductionOn with | h q => ?_
    rw [coverFib_coverHom]
    intro h
    refine ⟨Quotient.mk'' ⟨(X.pushUnres q.1.1 h, q.1.2), ?_⟩, ?_⟩
    · change q.1.2.1.1.1 = (X.Lv.sp V hV (X.pushUnres q.1.1 h)).1
      rw [← push_sp V hV (R := R) (A := A), pushRes_pushUnres]
      exact q.2
    · rw [pushι_mk]
      apply congrArg Quotient.mk''
      apply Subtype.ext
      exact Prod.ext (X.pushRes_pushUnres q.1.1 h) rfl

end TempObj

section Counit

variable (μ : OrbMap R A R' A')

namespace FiniteLevel

/-- `bcι` as an `R`-algebra map into the pushed base change. -/
def bcιR (L : FiniteLevel R A) : L.B →ₐ[R] ((L.baseChange μ).push R A).B :=
  ((L.baseChange μ).pushE R A).symm.toAlgHom.comp
    { (L.bcι μ) with
      commutes' := fun r => by
        change L.bcι μ (algebraMap R L.B r) = _
        rw [bcι_algebraMap, ← IsScalarTower.algebraMap_apply] }

lemma bcιR_apply (L : FiniteLevel R A) (y : L.B) :
    L.bcιR μ y = ((L.baseChange μ).pushE R A).symm (L.bcι μ y) := rfl

/-- The counit `push (bc L) ⟶ L` on levels. -/
def counitMap (L : FiniteLevel R A) : (L.baseChange μ).push R A ⟶ L where
  f := L.bcιR μ
  r := (L.bcPr μ).comp ((L.baseChange μ).pushEquiv R A).symm.toMonoidHom
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    rw [bcιR_apply, bcιR_apply]
    apply ((L.baseChange μ).pushE R A).injective
    rw [AlgEquiv.apply_symm_apply, ← pushEquiv_symm_σ, bcσ_bcι]
    rfl

/-- The multiplication `R' ⊗_R B' → B'`, on the coded base change of the pushed level. -/
def unitF (L' : FiniteLevel R' A') : ((L'.push R A).baseChange μ).B →ₐ[R'] L'.B :=
  (Algebra.TensorProduct.lift (Algebra.ofId R' L'.B) (L'.pushE R A).toAlgHom
    fun _ _ => Commute.all _ _).comp ((L'.push R A).bcE' μ).toAlgHom

lemma unitF_bcι (L' : FiniteLevel R' A') (y : (L'.push R A).B) :
    L'.unitF μ ((L'.push R A).bcι μ y) = L'.pushE R A y := by
  simp [unitF, bcE_bcι]

lemma unitF_σ (L' : FiniteLevel R' A') (g : L'.H) (z : R' ⊗[R] (L'.push R A).B)
    (p : (L'.push R A).Hfp μ) (hp : p.1.1 = L'.pushEquiv R A g) :
    Algebra.TensorProduct.lift (Algebra.ofId R' L'.B) (L'.pushE R A).toAlgHom
        (fun _ _ => Commute.all _ _) ((bcAut μ (L'.push R A) p).σ z) =
      (g : SemilinearAut R' A' L'.B).σ (Algebra.TensorProduct.lift (Algebra.ofId R' L'.B)
        (L'.pushE R A).toAlgHom (fun _ _ => Commute.all _ _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [bcAut_σ_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      map_mul, hp, Subsingleton.elim p.1.2 1, one_smul]
    simp only [Algebra.ofId_apply, AlgEquiv.coe_toAlgHom]
    rw [SemilinearAut.σ_algebraMap_of_a_eq_one (Subsingleton.elim _ _), pushEquiv_σ,
      AlgEquiv.apply_symm_apply]
  | add x y hx hy => rw [RingEquiv.map_add, map_add, hx, hy, map_add, RingEquiv.map_add]

/-- The group homomorphism `H' → H(push) ×_A A'`. -/
def unitK (L' : FiniteLevel R' A') : L'.H →* (L'.push R A).Hfp μ where
  toFun g := ⟨(L'.pushEquiv R A g, 1), Subsingleton.elim _ _⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

/-- The unit `L' ⟶ bc (push L')` on levels. -/
def unitMap (L' : FiniteLevel R' A') : L' ⟶ (L'.push R A).baseChange μ where
  f := L'.unitF μ
  r := ((L'.push R A).bcEquiv μ).toMonoidHom.comp (L'.unitK μ)
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    have h := L'.unitF_σ μ g ((L'.push R A).bcE' μ y) (L'.unitK μ g) rfl
    change L'.unitF μ ((((L'.push R A).bcEquiv μ (L'.unitK μ g) : ((L'.push R A).baseChange μ).H) :
      SemilinearAut R' A' ((L'.push R A).baseChange μ).B).σ y) = _
    rw [bcEquiv_σ]
    simp only [unitF, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact h

end FiniteLevel

namespace TempObj

lemma counit_j_ψ (Y : TempObj O R A) :
    (Spec.map (CommRingCat.ofHom (((Y.Lv.L.baseChange μ).pushE R A).symm :
        (Y.Lv.L.baseChange μ).B →+* ((Y.Lv.L.baseChange μ).push R A).B)) ≫
      Spec.map (CommRingCat.ofHom (Y.Lv.L.bcι μ)) ≫ Y.Lv.j) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom ((Y.Lv.L.counitMap μ).f :
        Y.Lv.L.B →+* ((Y.Lv.L.baseChange μ).push R A).B)) ≫ Y.Lv.j := by
  rw [Category.comp_id, ← Category.assoc, ← Spec.map_comp]
  rfl

/-- **The counit** `push (bc Y) ⟶ Y`. -/
def counit (Y : TempObj O R A) : (Y.baseChange μ).push R A ⟶ Y where
  φ := Y.Lv.L.counitMap μ
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := Y.counit_j_ψ μ
  h := id
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act _ _ := rfl

lemma unit_j_ψ (X : TempObj O R' A') :
    X.Lv.j ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom (X.Lv.L.unitF μ :
          ((X.Lv.L.push R A).baseChange μ).B →+* X.Lv.L.B)) ≫
        Spec.map (CommRingCat.ofHom ((X.Lv.L.push R A).bcι μ)) ≫
          Spec.map (CommRingCat.ofHom ((X.Lv.L.pushE R A).symm :
            X.Lv.L.B →+* (X.Lv.L.push R A).B)) ≫ X.Lv.j := by
  have h : CommRingCat.ofHom ((X.Lv.L.pushE R A).symm : X.Lv.L.B →+* (X.Lv.L.push R A).B) ≫
      CommRingCat.ofHom ((X.Lv.L.push R A).bcι μ) ≫
        CommRingCat.ofHom (X.Lv.L.unitF μ :
          ((X.Lv.L.push R A).baseChange μ).B →+* X.Lv.L.B) = 𝟙 _ := by
    refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
    change X.Lv.L.unitF μ ((X.Lv.L.push R A).bcι μ ((X.Lv.L.pushE R A).symm b)) = b
    rw [FiniteLevel.unitF_bcι, AlgEquiv.apply_symm_apply]
  rw [Category.comp_id, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, h,
    Spec.map_id, Category.id_comp]

/-- **The unit** `X' ⟶ bc (push X')`. -/
def unit (X : TempObj O R' A') : X ⟶ (X.push R A).baseChange μ where
  φ := X.Lv.L.unitMap μ
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := X.unit_j_ψ μ
  h := id
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act g x := by
    change X.P.act g x = X.P.act ((X.Lv.L.pushEquiv R A).symm ((X.Lv.L.push R A).bcPr μ
      ((X.Lv.L.push R A).bcEquiv μ (X.Lv.L.unitK μ g)))) x
    rw [FiniteLevel.bcPr_bcEquiv]
    change _ = X.P.act ((X.Lv.L.pushEquiv R A).symm (X.Lv.L.pushEquiv R A g)) x
    rw [MulEquiv.symm_apply_apply]

lemma counit_pushι (Y : TempObj O R A) (z : Fibre Ω V hV (Y.baseChange μ)) :
    fibreMap V hV (Y.counit μ) (pushι R A V hV (Y.baseChange μ) z) = bcFibreEquiv μ V hV Y z := by
  induction z using Quotient.inductionOn with | h q => ?_
  apply congrArg Quotient.mk''
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  ext y
  change q.1.1 ((Y.Lv.L.baseChange μ).pushE R A (((Y.Lv.L.baseChange μ).pushE R A).symm
    (Y.Lv.L.bcι μ y))) = q.1.1 (Y.Lv.L.bcι μ y)
  rw [AlgEquiv.apply_symm_apply]

lemma unit_pushι (X : TempObj O R' A') (x : Fibre Ω V hV X) :
    bcFibreEquiv μ V hV (X.push R A) (fibreMap V hV (X.unit μ) x) = pushι R A V hV X x := by
  induction x using Quotient.inductionOn with | h q => ?_
  apply congrArg Quotient.mk''
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  ext y
  change q.1.1 (X.Lv.L.unitF μ ((X.Lv.L.push R A).bcι μ y)) = q.1.1 (X.Lv.L.pushE R A y)
  rw [FiniteLevel.unitF_bcι]

end TempObj

end Counit

end Cover

section Image

variable [SMulCommClass A K R] (μ : OrbMap R A R' A')

/-- **The push data** of a finite étale cover (scheme case). -/
def coverPushData : PushData (TempObj.bcFunctor (O := O) μ) (TempObj.bcFibreIso μ V hV) where
  P := TempObj.pushFunctor O R A
  ι X' := TempObj.pushι R A V hV X'
  ι_injective X' := TempObj.pushι_injective V hV X'
  ι_natural m x := TempObj.pushι_natural V hV m x
  E := coverObj O R A R'
  x₀ := coverFibrePt V hV
  τ X' := TempObj.coverHom R A X'
  τ_natural m := TempObj.coverHom_natural m
  range_ι X' y := TempObj.range_pushι V hV X' y
  π Y := TempObj.counit μ Y
  π_ι Y z := TempObj.counit_pushι V hV μ Y z
  u X' := TempObj.unit μ X'
  u_ι X' x := TempObj.unit_pushι V hV μ X' x

/-- **A finite étale cover induces an injection of tempered fundamental groups.** -/
theorem temperedPi1Map_injective : Function.Injective (temperedPi1Map (O := O) μ V hV) :=
  (coverPushData V hV μ).injective_restrict

/-- **The image is the stabilizer of the base point of the cover** `Spec R' → Spec R`. -/
theorem mem_range_temperedPi1Map (γ : temperedPi1 O R A V hV) :
    γ ∈ (temperedPi1Map (O := O) μ V hV).range ↔
      γ.app (coverObj O R A R') (coverFibrePt V hV) = coverFibrePt V hV := by
  rw [show (temperedPi1Map (O := O) μ V hV).range = (coverPushData V hV μ).stab from
    (coverPushData V hV μ).range_restrict]
  rfl

/-- **`temperedPi1 O R' A' V hV` is an open subgroup of `temperedPi1 O R A V hV`**: the map is an
open embedding. -/
theorem isOpenEmbedding_temperedPi1Map :
    Topology.IsOpenEmbedding (temperedPi1Map (O := O) μ V hV) :=
  (coverPushData V hV μ).isOpenEmbedding_restrict

theorem isOpen_range_temperedPi1Map :
    IsOpen ((temperedPi1Map (O := O) μ V hV).range : Set (temperedPi1 O R A V hV)) := by
  rw [show (temperedPi1Map (O := O) μ V hV).range = (coverPushData V hV μ).stab from
    (coverPushData V hV μ).range_restrict]
  exact (coverPushData V hV μ).isOpen_stab

theorem finiteIndex_range_temperedPi1Map :
    (temperedPi1Map (O := O) μ V hV).range.FiniteIndex := by
  haveI : Finite ((coverEt R A R').B →ₐ[R] Ω) := by
    haveI := (coverEt R A R').finite
    infer_instance
  haveI : Finite ((tempFibre O R A V hV).obj (coverPushData V hV μ).E) :=
    Finite.of_equiv ((coverEt R A R').B →ₐ[R] Ω)
      (etaleToTempFibreEquiv O R A V hV (coverEt R A R')).symm
  exact (coverPushData V hV μ).finiteIndex_range_restrict

/-- `γ'` fixes a fibre element of `X'` iff its image fixes the corresponding fibre element of
`push X'` (`temperedPi1Map` is compatible with the basic open subgroups). -/
theorem temperedPi1Map_app_pushι (γ : temperedPi1 O R' A' V hV) (X : TempObj O R' A')
    (x : TempObj.Fibre Ω V hV X) :
    (temperedPi1Map μ V hV γ).app (X.push R A) (TempObj.pushι R A V hV X x) =
      TempObj.pushι R A V hV X (γ.app X x) :=
  (coverPushData V hV μ).restrict_app_ι γ X x

/-- The endomorphism of the cover induced by an `R`-algebra endomorphism `τ` of `R'`. -/
def coverEndEt (τ : R' →ₐ[R] R') : coverEt R A R' ⟶ coverEt R A R' where
  f := (coverE R A R').symm.toAlgHom.comp (τ.comp (coverE R A R').toAlgHom)
  f_act _ _ := rfl

lemma etaleToTempFibreEquiv_map {X Y : EquivEtale R A} (m : X ⟶ Y)
    (z : TempObj.Fibre Ω V hV ((etaleToTemp O R A).obj X)) :
    etaleToTempFibreEquiv O R A V hV Y (TempObj.fibreMap V hV ((etaleToTemp O R A).map m) z) =
      (etaleToTempFibreEquiv O R A V hV X z).comp m.f := by
  induction z using Quotient.inductionOn
  rfl

/-- **For a Galois cover the image is normal**: if every geometric point `R' → Ω` over `R` is the
base point composed with an `R`-algebra endomorphism of `R'`, then `temperedPi1 O R' A' V hV` is a
normal subgroup of `temperedPi1 O R A V hV`. -/
theorem normal_range_temperedPi1Map
    (hGal : ∀ t : R' →ₐ[R] Ω, ∃ τ : R' →ₐ[R] R',
      t = ((Algebra.ofId R' Ω).restrictScalars R).comp τ) :
    (temperedPi1Map (O := O) μ V hV).range.Normal := by
  rw [show (temperedPi1Map (O := O) μ V hV).range = (coverPushData V hV μ).stab from
    (coverPushData V hV μ).range_restrict]
  refine ⟨fun γ hγ δ => ?_⟩
  rw [PushData.mem_stab] at hγ ⊢
  change γ.app (coverObj O R A R') (coverFibrePt V hV) = coverFibrePt V hV at hγ
  change (δ * γ * δ⁻¹).app (coverObj O R A R') (coverFibrePt V hV) = coverFibrePt V hV
  set e := etaleToTempFibreEquiv O R A V hV (coverEt R A R')
  obtain ⟨τ, hτ⟩ := hGal ((e (δ⁻¹.app _ (coverFibrePt V hV))).comp
    (coverE R A R').symm.toAlgHom)
  set m := (etaleToTemp O R A).map (coverEndEt τ)
  have hclaim : δ⁻¹.app _ (coverFibrePt V hV) =
      TempObj.fibreMap V hV m (coverFibrePt V hV) := by
    apply e.injective
    rw [etaleToTempFibreEquiv_map, show e (coverFibrePt V hV) = coverPt R A R' Ω from
      Equiv.apply_symm_apply _ _]
    refine AlgHom.ext fun y => ?_
    have := AlgHom.congr_fun hτ (coverE R A R' y)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this
    exact this.trans (by simp [coverEndEt, coverPt])
  rw [FibreAut.mul_app, FibreAut.mul_app, hclaim,
    show γ.app _ (TempObj.fibreMap V hV m (coverFibrePt V hV)) =
      TempObj.fibreMap V hV m (γ.app _ (coverFibrePt V hV)) from
      FibreAut.app_naturality γ m (coverFibrePt V hV),
    hγ, ← hclaim, FibreAut.app_inv_app]

end Image

end

end TemperedFundamentalGroups
