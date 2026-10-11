/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChange
import TemperedFundamentalGroups.Tempered.Comparison

/-!
# Functoriality of the étale fundamental group, compatibly with the comparison map
(Blueprint §11, F5)

For a map of orbifolds `μ : OrbMap R A R' A'`, an `A`-equivariant finite étale `R`-algebra `B`
base-changes to the `A'`-equivariant finite étale `R'`-algebra `R' ⊗_R B`, `a'` acting by
`a' ⊗ act (α a')` (`bcEt`). Its geometric fibre is that of `B` (`bcEtFibreIso`), which gives
`etalePi1Map μ : etalePi1 R' A' Ω →* etalePi1 R A Ω`, and the comparison maps
`temperedToEtale` intertwine `temperedPi1Map μ` and `etalePi1Map μ`
(`temperedToEtale_temperedPi1Map`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] (μ : OrbMap R A R' A')

namespace EquivEtaleBC

/-- The element `(act (α a'), a')` of `H ×_A A'` for the level of an equivariant algebra. -/
def actHom (X : EquivEtale R A) : A' →* X.level.Hfp μ where
  toFun a' := ⟨(⟨X.act (μ.α a'), ⟨_, rfl⟩⟩, a'), X.act_a _⟩
  map_one' := by ext <;> simp
  map_mul' _ _ := by ext <;> simp

/-- **Base change of an equivariant finite étale algebra**: `R' ⊗_R B`, coded, with `a'` acting
by `a' ⊗ act (α a')`. -/
def bcEt (X : EquivEtale R A) : EquivEtale R' A' where
  toEtaleCode := FiniteLevel.bcCode X.level
  act := (FiniteLevel.bcHomH μ X.level).comp (actHom μ X)
  act_a _ := rfl

lemma bcRfp_actHom {X Y : EquivEtale R A} (m : X ⟶ Y) (a' : A') :
    FiniteLevel.bcRfp (EquivEtale.levelMap m) (actHom μ X a') = actHom μ Y a' := by
  apply Subtype.ext
  refine Prod.ext (Subtype.ext ?_) rfl
  change Y.act ((X.act (μ.α a')).a) = Y.act (μ.α a')
  rw [X.act_a]

/-- Base change of a morphism. -/
def bcEtMap {X Y : EquivEtale R A} (m : X ⟶ Y) : bcEt μ X ⟶ bcEt μ Y where
  f := (FiniteLevel.bcMap μ (EquivEtale.levelMap m)).f
  f_act a' y := by
    change (X.level.bcE' μ).symm (Algebra.TensorProduct.map (AlgHom.id R' R') m.f
      (Y.level.bcE' μ ((Y.level.bcE' μ).symm ((FiniteLevel.bcAut μ Y.level (actHom μ Y a')).σ
        (Y.level.bcE' μ y))))) = (X.level.bcE' μ).symm ((FiniteLevel.bcAut μ X.level
          (actHom μ X a')).σ (X.level.bcE' μ ((X.level.bcE' μ).symm
            (Algebra.TensorProduct.map (AlgHom.id R' R') m.f (Y.level.bcE' μ y)))))
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, ← bcRfp_actHom μ m a']
    exact congrArg _ (FiniteLevel.bcAut_map (EquivEtale.levelMap m) _ _)

/-- **The base change functor** on equivariant finite étale algebras. -/
def bcEtFunctor : EquivEtale R A ⥤ EquivEtale R' A' where
  obj X := bcEt μ X
  map m := bcEtMap μ m
  map_id X := EquivEtale.Hom.ext (congrArg FiniteLevel.Hom.f
    ((FiniteLevel.bcFunctor μ).map_id X.level))
  map_comp m n := EquivEtale.Hom.ext (congrArg FiniteLevel.Hom.f
    ((FiniteLevel.bcFunctor μ).map_comp (EquivEtale.levelMap m) (EquivEtale.levelMap n)))

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]

/-- The geometric fibre of the base change is the geometric fibre. -/
def bcEtFibreEquiv (X : EquivEtale R A) :
    (etaleFibre R' A' Ω).obj (bcEt μ X) ≃ (etaleFibre R A Ω).obj X where
  toFun t := X.level.bcRes μ t
  invFun t := X.level.bcExt μ t
  left_inv t := X.level.bcExt_bcRes μ t
  right_inv t := X.level.bcRes_bcExt μ t

variable (Ω) in
/-- **The base change functor commutes with the geometric fibre functors.** -/
def bcEtFibreIso : bcEtFunctor μ ⋙ etaleFibre R' A' Ω ≅ etaleFibre R A Ω :=
  NatIso.ofComponents (fun X => (bcEtFibreEquiv μ X).toIso) fun {X Y} m => by
    ext t
    exact FiniteLevel.bcRes_bcMap μ (EquivEtale.levelMap m) t

end EquivEtaleBC

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]

/-- **Functoriality of the étale fundamental group** along a map of orbifolds. -/
def etalePi1Map : etalePi1 R' A' Ω →* etalePi1 R A Ω :=
  FibreAut.restrict (EquivEtaleBC.bcEtFunctor μ) (EquivEtaleBC.bcEtFibreIso μ Ω)

lemma continuous_etalePi1Map : Continuous (etalePi1Map μ Ω) :=
  FibreAut.continuous_restrict _ _

section Comparison

variable [SMulCommClass A K R] [SMulCommClass A' K R']
  {Ω} (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace EquivEtaleBC

lemma range_act_le (X : EquivEtale R A) :
    (bcEt μ X).act.range ≤ (X.level.baseChange μ).H := by
  rintro _ ⟨a', rfl⟩
  exact ⟨_, rfl⟩

/-- The comparison morphism `etaleToTemp (bcEt X) ⟶ bc (etaleToTemp X)` (identity on algebras,
models and coverings). -/
def cmpLevel (X : EquivEtale R A) : (bcEt μ X).level ⟶ X.level.baseChange μ where
  f := AlgHom.id R' _
  r := (Subgroup.inclusion (range_act_le μ X)).comp (MonoidHom.id _)
  r_a _ := rfl
  f_σ _ _ := rfl

lemma cmp_j (X : EquivEtale R A) :
    ((etaleToTemp O R' A').obj (bcEt μ X)).Lv.j ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom ((cmpLevel μ X).f : _ →+* (bcEt μ X).B)) ≫
        Spec.map (CommRingCat.ofHom (X.level.bcι μ)) ≫
          ((etaleToTemp O R A).obj X).Lv.j := by
  change (Spec.map (CommRingCat.ofHom (levelStructureMap O R' A' (bcEt μ X).level)) ≫
      inv (ModelCode.trivial O).toSpec) ≫ 𝟙 _ =
    Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ Spec.map (CommRingCat.ofHom (X.level.bcι μ)) ≫
      Spec.map (CommRingCat.ofHom (levelStructureMap O R A X.level)) ≫
        inv (ModelCode.trivial O).toSpec
  rw [Category.comp_id, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, ← Category.assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 3
  exact RingHom.ext fun o => (X.level.bcι_levelStructureMap μ o).symm

/-- The comparison morphism of tempered coverings. -/
def cmp (X : EquivEtale R A) :
    (etaleToTemp O R' A').obj (bcEt μ X) ⟶ ((etaleToTemp O R A).obj X).baseChange μ where
  φ := cmpLevel μ X
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := cmp_j μ X
  h := id
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act _ _ := rfl

lemma cmp_fibre (X : EquivEtale R A)
    (z : TempObj.Fibre Ω V hV ((etaleToTemp O R' A').obj (bcEt μ X))) :
    etaleToTempFibreEquiv O R A V hV X (TempObj.bcFibreEquiv μ V hV _
      (TempObj.fibreMap V hV (cmp μ X) z)) =
      bcEtFibreEquiv μ X (etaleToTempFibreEquiv O R' A' V hV (bcEt μ X) z) := by
  induction z using Quotient.inductionOn
  rfl

end EquivEtaleBC

/-- **The comparison maps are natural** in maps of orbifolds:
`temperedToEtale ∘ temperedPi1Map μ = etalePi1Map μ ∘ temperedToEtale`. -/
theorem temperedToEtale_temperedPi1Map (γ : temperedPi1 O R' A' V hV) :
    temperedToEtale O R A V hV (temperedPi1Map μ V hV γ) =
      etalePi1Map μ Ω (temperedToEtale O R' A' V hV γ) := by
  ext X t
  set y : TempObj.Fibre Ω V hV ((etaleToTemp O R' A').obj (EquivEtaleBC.bcEt μ X)) :=
    (etaleToTempFibreEquiv O R' A' V hV (EquivEtaleBC.bcEt μ X)).symm
      (EquivEtaleBC.bcEtFibreEquiv μ X |>.symm t) with hy_def
  have hy : TempObj.fibreMap V hV (EquivEtaleBC.cmp μ X) y =
      (TempObj.bcFibreEquiv μ V hV _).symm ((etaleToTempFibreEquiv O R A V hV X).symm t) := by
    refine (Equiv.eq_symm_apply _).2 ((Equiv.eq_symm_apply _).2 ?_)
    refine (EquivEtaleBC.cmp_fibre μ V hV X y).trans ?_
    rw [hy_def, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have key := FibreAut.app_naturality γ (EquivEtaleBC.cmp μ X) y
  change etaleToTempFibreEquiv O R A V hV X (TempObj.bcFibreEquiv μ V hV _
      (γ.app _ ((TempObj.bcFibreEquiv μ V hV _).symm
        ((etaleToTempFibreEquiv O R A V hV X).symm t)))) =
    EquivEtaleBC.bcEtFibreEquiv μ X (etaleToTempFibreEquiv O R' A' V hV _ (γ.app _ y))
  rw [← hy]
  rw [show γ.app _ (TempObj.fibreMap V hV (EquivEtaleBC.cmp μ X) y) =
    TempObj.fibreMap V hV (EquivEtaleBC.cmp μ X) (γ.app _ y) from key, EquivEtaleBC.cmp_fibre]

end Comparison

end

end TemperedFundamentalGroups
