/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChange

/-!
# Pushing tempered coverings along a finite étale cover (Blueprint §11, F7)

Scheme case: `A` and `A'` are trivial groups (`Subsingleton`) and `R'` is finite étale over `R`.
A level `(B', H')` of `Spec R'` is a level of `Spec R`: `B'` is finite étale over `R` and the
`R'`-linear automorphisms in `H'` are `R`-linear (`FiniteLevel.push`). Keeping the model and the
covering space gives the **push functor** `TempObj O R' A' ⥤ TempObj O R A`
(`TempObj.pushFunctor`). It is the restriction of scalars along the finite étale cover
`Spec R' → Spec R`, and is used to identify the image of `temperedPi1Map`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [Subsingleton A]
  [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  [Algebra.Etale R R'] [Module.Finite R R']
  {A' : Type u} [Group A'] [Subsingleton A'] [MulSemiringAction A' R']

namespace FiniteLevel

section

variable (L' : FiniteLevel R' A')

instance : Algebra.Etale R L'.B := by
  haveI := L'.etale
  exact Algebra.Etale.comp R R' L'.B

instance : Module.Finite R L'.B := by
  haveI := L'.finite
  exact Module.Finite.trans R' L'.B

end

variable (R A) in
/-- The elements of `H'` (which are `R'`-linear) as `R`-linear automorphisms. -/
def pushAut (L' : FiniteLevel R' A') : L'.H →* SemilinearAut R A L'.B where
  toFun g := ⟨1, (g : SemilinearAut R' A' L'.B).σ, fun r => by
    rw [one_smul, IsScalarTower.algebraMap_apply R R' L'.B,
      SemilinearAut.σ_algebraMap_of_a_eq_one (Subsingleton.elim _ _)]⟩
  map_one' := rfl
  map_mul' _ _ := SemilinearAut.ext (mul_one 1).symm rfl

variable (R) in
/-- The code of `B'` as a finite étale `R`-algebra. -/
def pushCode (L' : FiniteLevel R' A') : EtaleCode R := codeOf (R' := R) L'.B

variable (R A) in
/-- The pushed level `(B', H')` of `Spec R`. -/
def push (L' : FiniteLevel R' A') : FiniteLevel R A where
  toEtaleCode := pushCode R L'
  H := ((SemilinearAut.congr (EquivEtale.presEquiv R L'.B).symm).comp (pushAut R A L')).range
  surjective _ := ⟨1, Subgroup.one_mem _, Subsingleton.elim _ _⟩

variable (R A) in
/-- The coded pushed level is `B'`. -/
def pushE (L' : FiniteLevel R' A') : (L'.push R A).B ≃ₐ[R] L'.B := EquivEtale.presEquiv R L'.B

variable (R A) in
/-- The group homomorphism `H' → H(push)`. -/
def pushHom (L' : FiniteLevel R' A') : L'.H →* SemilinearAut R A (L'.push R A).B :=
  (SemilinearAut.congr (L'.pushE R A).symm).comp (pushAut R A L')

lemma pushHom_σ (L' : FiniteLevel R' A') (g : L'.H) (x : (L'.push R A).B) :
    (L'.pushHom R A g).σ x = (L'.pushE R A).symm ((g : SemilinearAut R' A' L'.B).σ (L'.pushE R A x)) :=
  rfl

lemma pushHom_injective (L' : FiniteLevel R' A') : Function.Injective (L'.pushHom R A) := by
  intro g h hgh
  refine Subtype.ext (SemilinearAut.ext (Subsingleton.elim _ _) (RingEquiv.ext fun y => ?_))
  have := congrArg (fun k : SemilinearAut R A (L'.push R A).B => L'.pushE R A (k.σ
    ((L'.pushE R A).symm y))) hgh
  simpa [pushHom_σ] using this

variable (R A) in
/-- `H' ≃* H(push)`. -/
def pushEquiv (L' : FiniteLevel R' A') : L'.H ≃* (L'.push R A).H :=
  MonoidHom.ofInjective (pushHom_injective L')

lemma pushEquiv_σ (L' : FiniteLevel R' A') (g : L'.H) (x : (L'.push R A).B) :
    ((L'.pushEquiv R A g : (L'.push R A).H) : SemilinearAut R A (L'.push R A).B).σ x =
      (L'.pushE R A).symm ((g : SemilinearAut R' A' L'.B).σ (L'.pushE R A x)) := rfl

lemma pushEquiv_symm_σ (L' : FiniteLevel R' A') (g : (L'.push R A).H) (y : L'.B) :
    (((L'.pushEquiv R A).symm g : L'.H) : SemilinearAut R' A' L'.B).σ y =
      L'.pushE R A ((g : SemilinearAut R A (L'.push R A).B).σ ((L'.pushE R A).symm y)) := by
  conv_rhs => rw [← (L'.pushEquiv R A).apply_symm_apply g]
  rw [pushEquiv_σ, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

variable (R A) in
/-- The pushed morphism of levels. -/
def pushMap {L' M' : FiniteLevel R' A'} (φ : L' ⟶ M') : L'.push R A ⟶ M'.push R A where
  f := (L'.pushE R A).symm.toAlgHom.comp ((φ.f.restrictScalars R).comp (M'.pushE R A).toAlgHom)
  r := (M'.pushEquiv R A).toMonoidHom.comp (φ.r.comp (L'.pushEquiv R A).symm.toMonoidHom)
  r_a _ := Subsingleton.elim _ _
  f_σ g y := by
    conv_rhs => rw [← (L'.pushEquiv R A).apply_symm_apply g]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, pushEquiv_σ, AlgEquiv.apply_symm_apply,
      AlgHom.coe_restrictScalars']
    rw [φ.f_σ]

variable (R A) in
/-- **The push functor on levels.** -/
def pushFunctor : FiniteLevel R' A' ⥤ FiniteLevel R A where
  obj L' := L'.push R A
  map φ := pushMap R A φ
  map_id L' := by
    refine Hom.ext (AlgHom.ext fun x => ?_) (MonoidHom.ext fun g => ?_)
    · change (L'.pushE R A).symm (L'.pushE R A x) = x
      rw [AlgEquiv.symm_apply_apply]
    · change (L'.pushEquiv R A) ((L'.pushEquiv R A).symm g) = g
      rw [MulEquiv.apply_symm_apply]
  map_comp φ ψ := by
    refine Hom.ext (AlgHom.ext fun x => ?_) (MonoidHom.ext fun g => ?_)
    · simp [pushMap]
    · simp [pushMap]

lemma pushMap_f {L' M' : FiniteLevel R' A'} (φ : L' ⟶ M') (x : (M'.push R A).B) :
    (pushMap R A φ).f x = (L'.pushE R A).symm (φ.f (M'.pushE R A x)) := rfl

end FiniteLevel

namespace FiniteLevel

lemma pushE_symm_levelStructureMap (L' : FiniteLevel R' A') (o : O) :
    (L'.pushE R A).symm (levelStructureMap O R' A' L' o) =
      levelStructureMap O R A (L'.push R A) o := by
  change (L'.pushE R A).symm (algebraMap R' L'.B (algebraMap K R' o)) =
    algebraMap R _ (algebraMap K R o)
  rw [IsScalarTower.algebraMap_apply K R R', ← IsScalarTower.algebraMap_apply R R' L'.B,
    AlgEquiv.commutes]

lemma pushEquiv_symm_σ_symm (L' : FiniteLevel R' A') (g : (L'.push R A).H) (y : L'.B) :
    (g : SemilinearAut R A (L'.push R A).B).σ.symm ((L'.pushE R A).symm y) =
      (L'.pushE R A).symm
        ((((L'.pushEquiv R A).symm g : L'.H) : SemilinearAut R' A' L'.B).σ.symm y) := by
  apply (g : SemilinearAut R A (L'.push R A).B).σ.injective
  rw [RingEquiv.apply_symm_apply]
  apply (L'.pushE R A).injective
  rw [AlgEquiv.apply_symm_apply, ← pushEquiv_symm_σ, RingEquiv.apply_symm_apply]

end FiniteLevel

namespace Level

variable (R A) in
/-- **The pushed level with model**: the same model, `j` composed with `Spec B' ≅ Spec B'`. -/
def push (Lv : Level O R' A') : Level O R A where
  L := Lv.L.push R A
  c := Lv.c
  j := Spec.map (CommRingCat.ofHom ((Lv.L.pushE R A).symm : Lv.L.B →+* (Lv.L.push R A).B)) ≫ Lv.j
  j_toSpec := by
    rw [Category.assoc, Lv.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun o => Lv.L.pushE_symm_levelStructureMap o
  ρ := Lv.ρ.comp (Lv.L.pushEquiv R A).symm.toMonoidHom
  ρ_toSpec g := Lv.ρ_toSpec _
  ρ_j g := by
    rw [MonoidHom.comp_apply, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Category.assoc, ← Lv.ρ_j, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine congrArg CommRingCat.ofHom (RingHom.ext fun y => ?_)
    exact Lv.L.pushEquiv_symm_σ_symm g y

end Level

namespace TempObj

variable (R A) in
/-- **The pushed tempered covering** of `Spec R`. -/
def push (X : TempObj O R' A') : TempObj O R A where
  Lv := X.Lv.push R A
  P := X.P.comapGroup (X.Lv.L.pushEquiv R A).symm.toMonoidHom (fun _ _ => rfl)

variable (R A) in
/-- The pushed morphism. -/
def pushHom {X Y : TempObj O R' A'} (m : X ⟶ Y) : X.push R A ⟶ Y.push R A where
  φ := FiniteLevel.pushMap R A m.φ
  ψ := m.ψ
  ψ_toSpec := m.ψ_toSpec
  j_ψ := by
    have h : Spec.map (CommRingCat.ofHom
          ((X.Lv.L.pushE R A).symm : X.Lv.L.B →+* (X.Lv.L.push R A).B)) ≫
        Spec.map (CommRingCat.ofHom (m.φ.f : Y.Lv.L.B →+* X.Lv.L.B)) =
        Spec.map (CommRingCat.ofHom ((FiniteLevel.pushMap R A m.φ).f :
          (Y.Lv.L.push R A).B →+* (X.Lv.L.push R A).B)) ≫
        Spec.map (CommRingCat.ofHom
          ((Y.Lv.L.pushE R A).symm : Y.Lv.L.B →+* (Y.Lv.L.push R A).B)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      refine RingHom.ext fun y => ?_
      change _ = (FiniteLevel.pushMap R A m.φ).f ((Y.Lv.L.pushE R A).symm y)
      rw [FiniteLevel.pushMap_f, AlgEquiv.apply_symm_apply]
      rfl
    change (Spec.map (CommRingCat.ofHom
          ((X.Lv.L.pushE R A).symm : X.Lv.L.B →+* (X.Lv.L.push R A).B)) ≫ X.Lv.j) ≫ m.ψ =
      Spec.map (CommRingCat.ofHom ((FiniteLevel.pushMap R A m.φ).f :
          (Y.Lv.L.push R A).B →+* (X.Lv.L.push R A).B)) ≫
        Spec.map (CommRingCat.ofHom
          ((Y.Lv.L.pushE R A).symm : Y.Lv.L.B →+* (Y.Lv.L.push R A).B)) ≫ Y.Lv.j
    rw [Category.assoc, m.j_ψ, ← Category.assoc, h, Category.assoc]
  h := m.h
  continuous_h := m.continuous_h
  fst_h := m.fst_h
  h_act g x := by
    change m.h (X.P.act ((X.Lv.L.pushEquiv R A).symm g) x) =
      Y.P.act ((Y.Lv.L.pushEquiv R A).symm ((FiniteLevel.pushMap R A m.φ).r g)) (m.h x)
    rw [m.h_act]
    simp [FiniteLevel.pushMap]

variable (O R A) in
/-- **The push functor** `TempObj O R' A' ⥤ TempObj O R A`. -/
def pushFunctor : TempObj O R' A' ⥤ TempObj O R A where
  obj X := X.push R A
  map m := pushHom R A m
  map_id X := Hom.ext ((FiniteLevel.pushFunctor R A).map_id X.Lv.L) rfl rfl
  map_comp m n := Hom.ext ((FiniteLevel.pushFunctor R A).map_comp m.φ n.φ) rfl rfl

end TempObj

end

end TemperedFundamentalGroups
