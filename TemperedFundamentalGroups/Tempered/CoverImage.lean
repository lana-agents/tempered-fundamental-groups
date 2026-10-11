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

end TempObj

end Cover

end

end TemperedFundamentalGroups
