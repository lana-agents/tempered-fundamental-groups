/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChangeLevel
import TemperedFundamentalGroups.Tempered.Category

/-!
# Functoriality of the tempered fundamental group (Blueprint §11, F2–F3)

Let `μ : OrbMap R A R' A'` be a map of affine orbifolds `[Spec R' / A'] → [Spec R / A]` over the
valued field `(K, O)`: an injective `K`-algebra map `R → R'` and a group homomorphism
`α : A' →* A` for which it is equivariant. This covers finite étale covers (`R'` finite étale
over `R`), open immersions (`R'` a localization of `R`, i.e. removing points such as cusps) and
orbifold covers (`R = R'`, `A' ≤ A`; for `A'` trivial this is `Y → [Y/A]`).

A tempered covering of `[Spec R / A]` pulls back to `[Spec R' / A']` (`TempObj.baseChange`):
the level is base-changed (`FiniteLevel.baseChange`), the model `𝒯` and the covering space `P`
of its special fibre are kept, `j` is composed with `Spec (R' ⊗_R B) → Spec B`, and
`H' = H ×_A A'` acts on `𝒯` and `P` through `H' → H`. Its fibre at a geometric point
`Spec Ω → Spec R' → Spec R` is the fibre of the given covering (`bcFibreIso`). Restricting
fibre-functor automorphisms along the base change functor gives the continuous homomorphism

`temperedPi1Map μ : temperedPi1 O R' A' V hV →* temperedPi1 O R A V hV`.

## Main definitions

* `Level.baseChange`, `TempObj.baseChange`, `TempObj.bcFunctor`: base change of levels with
  models and of tempered coverings.
* `TempObj.bcFibreIso : bcFunctor μ ⋙ tempFibre O R' A' V hV ≅ tempFibre O R A V hV`.
* `temperedPi1Map`, `continuous_temperedPi1Map`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

namespace TemperedFundamentalGroups

noncomputable section

namespace CoveringCode

variable {Z : Type u} [TopologicalSpace Z] {G G' : Type u} [Group G] [Group G']

/-- A `G`-equivariant covering code is `G'`-equivariant along a homomorphism `k : G' →* G`. -/
def comapGroup {ρ : G →* (Z ≃ₜ Z)} (P : CoveringCode ρ) (k : G' →* G) {ρ' : G' →* (Z ≃ₜ Z)}
    (h : ∀ g x, ρ' g x = ρ (k g) x) : CoveringCode ρ' where
  carrier := P.carrier
  top := P.top
  isCoveringMap := P.isCoveringMap
  act := P.act.comp k
  act_fst g x := by rw [MonoidHom.comp_apply, P.act_fst, h]

end CoveringCode

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] (μ : OrbMap R A R' A')

namespace FiniteLevel

lemma bcσ_symm_bcι (L : FiniteLevel R A) (g : (L.baseChange μ).H) (y : L.B) :
    (g : SemilinearAut R' A' (L.baseChange μ).B).σ.symm (L.bcι μ y) =
      L.bcι μ ((L.bcPr μ g : SemilinearAut R A L.B).σ.symm y) := by
  apply (g : SemilinearAut R' A' (L.baseChange μ).B).σ.injective
  rw [RingEquiv.apply_symm_apply, bcσ_bcι, RingEquiv.apply_symm_apply]

lemma bcι_levelStructureMap (L : FiniteLevel R A) (o : O) :
    L.bcι μ (levelStructureMap O R A L o) = levelStructureMap O R' A' (L.baseChange μ) o := by
  change L.bcι μ (algebraMap R L.B (algebraMap K R o)) = algebraMap R' _ (algebraMap K R' o)
  rw [bcι_algebraMap, ← IsScalarTower.algebraMap_apply K R R']

end FiniteLevel

namespace Level

/-- **Base change of a level with a model**: the model is kept, `j` is composed with
`Spec (R' ⊗_R B) → Spec B`, and `H'` acts through `H' → H`. -/
def baseChange (Lv : Level O R A) : Level O R' A' where
  L := Lv.L.baseChange μ
  c := Lv.c
  j := Spec.map (CommRingCat.ofHom (Lv.L.bcι μ)) ≫ Lv.j
  j_toSpec := by
    rw [Category.assoc, Lv.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    exact Lv.L.bcι_levelStructureMap μ o
  ρ := Lv.ρ.comp (Lv.L.bcPr μ)
  ρ_toSpec g := Lv.ρ_toSpec _
  ρ_j g := by
    rw [MonoidHom.comp_apply, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      Category.assoc, ← Lv.ρ_j, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    congr 1
    exact RingHom.ext fun y => Lv.L.bcσ_symm_bcι μ g y

lemma baseChange_ρs (Lv : Level O R A) (g : (Lv.L.baseChange μ).H) (x : Lv.Z) :
    (Lv.baseChange μ).ρs g x = Lv.ρs (Lv.L.bcPr μ g) x := rfl

end Level

namespace TempObj

/-- **Base change of a tempered covering** along `μ`. -/
def baseChange (X : TempObj O R A) : TempObj O R' A' where
  Lv := X.Lv.baseChange μ
  P := X.P.comapGroup (X.Lv.L.bcPr μ) (fun g x => X.Lv.baseChange_ρs μ g x)

/-- Base change of a morphism of tempered coverings. -/
def bcHom {X Y : TempObj O R A} (m : X ⟶ Y) : X.baseChange μ ⟶ Y.baseChange μ where
  φ := FiniteLevel.bcMap μ m.φ
  ψ := m.ψ
  ψ_toSpec := m.ψ_toSpec
  j_ψ := by
    have h : Spec.map (CommRingCat.ofHom (X.Lv.L.bcι μ)) ≫
        Spec.map (CommRingCat.ofHom (m.φ.f : Y.Lv.L.B →+* X.Lv.L.B)) =
        Spec.map (CommRingCat.ofHom ((FiniteLevel.bcMap μ m.φ).f :
          (Y.Lv.L.baseChange μ).B →+* (X.Lv.L.baseChange μ).B)) ≫
        Spec.map (CommRingCat.ofHom (Y.Lv.L.bcι μ)) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun y => (FiniteLevel.bcMap_f_bcι m.φ y).symm
    change (Spec.map (CommRingCat.ofHom (X.Lv.L.bcι μ)) ≫ X.Lv.j) ≫ m.ψ =
      Spec.map (CommRingCat.ofHom ((FiniteLevel.bcMap μ m.φ).f :
          (Y.Lv.L.baseChange μ).B →+* (X.Lv.L.baseChange μ).B)) ≫
        Spec.map (CommRingCat.ofHom (Y.Lv.L.bcι μ)) ≫ Y.Lv.j
    rw [Category.assoc, m.j_ψ, ← Category.assoc, h, Category.assoc]
  h := m.h
  continuous_h := m.continuous_h
  fst_h := m.fst_h
  h_act g x := by
    change m.h (X.P.act (X.Lv.L.bcPr μ g) x) =
      Y.P.act (Y.Lv.L.bcPr μ ((FiniteLevel.bcMap μ m.φ).r g)) (m.h x)
    rw [m.h_act, FiniteLevel.bcPr_bcMap]

/-- **The base change functor** `TempObj O R A ⥤ TempObj O R' A'`. -/
def bcFunctor : TempObj O R A ⥤ TempObj O R' A' where
  obj X := X.baseChange μ
  map m := bcHom μ m
  map_id X := Hom.ext ((FiniteLevel.bcFunctor μ).map_id X.Lv.L) rfl rfl
  map_comp m n := Hom.ext ((FiniteLevel.bcFunctor μ).map_comp m.φ n.φ) rfl rfl

end TempObj

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace FiniteLevel

/-- A geometric point of `R' ⊗_R B` over `R'` restricts to a geometric point of `B` over `R`. -/
def bcRes (L : FiniteLevel R A) (t : (L.baseChange μ).B →ₐ[R'] Ω) : L.B →ₐ[R] Ω :=
  { (t : (L.baseChange μ).B →+* Ω).comp (L.bcι μ) with
    commutes' := fun r => by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply,
        bcι_algebraMap, AlgHom.commutes]
      rw [← IsScalarTower.algebraMap_apply] }

lemma bcRes_apply (L : FiniteLevel R A) (t : (L.baseChange μ).B →ₐ[R'] Ω) (y : L.B) :
    L.bcRes μ t y = t (L.bcι μ y) := rfl

/-- A geometric point of `B` over `R` extends uniquely to `R' ⊗_R B` over `R'`. -/
def bcExt (L : FiniteLevel R A) (t : L.B →ₐ[R] Ω) : (L.baseChange μ).B →ₐ[R'] Ω :=
  (Algebra.TensorProduct.lift (Algebra.ofId R' Ω) t fun _ _ => Commute.all _ _).comp
    (L.bcE' μ).toAlgHom

lemma bcRes_bcExt (L : FiniteLevel R A) (t : L.B →ₐ[R] Ω) : L.bcRes μ (L.bcExt μ t) = t := by
  ext y
  rw [bcRes_apply, bcExt, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, bcE_bcι,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul]

lemma bcExt_bcRes (L : FiniteLevel R A) (t : (L.baseChange μ).B →ₐ[R'] Ω) :
    L.bcExt μ (L.bcRes μ t) = t := by
  have h : (L.bcExt μ (L.bcRes μ t)).comp (L.bcE' μ).symm.toAlgHom =
      t.comp (L.bcE' μ).symm.toAlgHom := by
    refine Algebra.TensorProduct.ext' fun x y => ?_
    simp only [bcExt, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply,
      Algebra.TensorProduct.lift_tmul, bcRes_apply]
    rw [show (L.bcE' μ).symm (x ⊗ₜ y) = x • L.bcι μ y by
      apply (L.bcE' μ).injective
      rw [AlgEquiv.apply_symm_apply, map_smul, bcE_bcι, smul_tmul', smul_eq_mul, mul_one],
      map_smul, Algebra.ofId_apply, Algebra.smul_def]
  ext z
  simpa using AlgHom.congr_fun h (L.bcE' μ z)

lemma bcRes_fibreAct (L : FiniteLevel R A) (g : (L.baseChange μ).H0)
    (t : (L.baseChange μ).B →ₐ[R'] Ω) :
    L.bcRes μ (fibreAct Ω (L.baseChange μ) g t) =
      fibreAct Ω L ⟨L.bcPr μ g, bcPr_mem_H0 μ L g.2⟩ (L.bcRes μ t) := by
  ext y
  simp only [bcRes_apply, fibreAct_apply]
  rw [bcσ_symm_bcι]

lemma bcRes_bcMap {L M : FiniteLevel R A} (φ : L ⟶ M) (t : (L.baseChange μ).B →ₐ[R'] Ω) :
    M.bcRes μ (t.comp (bcMap μ φ).f) = (L.bcRes μ t).comp φ.f := by
  ext y
  simp only [bcRes_apply, AlgHom.comp_apply, bcMap_f_bcι]

end FiniteLevel

namespace TempObj

lemma bc_sp (X : TempObj O R A) (t : (X.Lv.L.baseChange μ).B →ₐ[R'] Ω) :
    (X.baseChange μ).Lv.sp V hV t = X.Lv.sp V hV (X.Lv.L.bcRes μ t) := by
  unfold Level.sp
  congr 1
  change Spec.map _ ≫ Spec.map _ ≫ X.Lv.j = Spec.map _ ≫ X.Lv.j
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

/-- Restriction of pairs `(t, p)`. -/
def bcPreRes (X : TempObj O R A) (q : PreFibre Ω V hV (X.baseChange μ)) : PreFibre Ω V hV X :=
  ⟨(X.Lv.L.bcRes μ q.1.1, q.1.2), by rw [← bc_sp]; exact q.2⟩

/-- Extension of pairs `(t, p)`. -/
def bcPreExt (X : TempObj O R A) (q : PreFibre Ω V hV X) : PreFibre Ω V hV (X.baseChange μ) :=
  ⟨(X.Lv.L.bcExt μ q.1.1, q.1.2), by rw [bc_sp, FiniteLevel.bcRes_bcExt]; exact q.2⟩

lemma bcPreRes_smul (X : TempObj O R A) (g : (X.baseChange μ).Lv.L.H0)
    (q : PreFibre Ω V hV (X.baseChange μ)) :
    bcPreRes μ V hV X (g • q) =
      (⟨X.Lv.L.bcPr μ g.1, FiniteLevel.bcPr_mem_H0 μ X.Lv.L g.2⟩ :
        X.Lv.L.H0) •
        bcPreRes μ V hV X q := by
  apply Subtype.ext
  simp only [bcPreRes, smul_val]
  exact Prod.ext (FiniteLevel.bcRes_fibreAct μ X.Lv.L g q.1.1) rfl

lemma bcPreExt_smul (X : TempObj O R A) (h : X.Lv.L.H0) (q : PreFibre Ω V hV X) :
    bcPreExt μ V hV X (h • q) =
      (show (X.baseChange μ).Lv.L.H0 from X.Lv.L.bcH0 μ h) • bcPreExt μ V hV X q := by
  have := bcPreRes_smul μ V hV X (X.Lv.L.bcH0 μ h) (bcPreExt μ V hV X q)
  have hres : ∀ q', bcPreExt μ V hV X (bcPreRes μ V hV X q') = q' := fun q' => by
    apply Subtype.ext
    simp [bcPreExt, bcPreRes, FiniteLevel.bcExt_bcRes]
  have hres' : bcPreRes μ V hV X (bcPreExt μ V hV X q) = q := by
    apply Subtype.ext
    simp [bcPreExt, bcPreRes, FiniteLevel.bcRes_bcExt]
  rw [hres'] at this
  have hh : (⟨X.Lv.L.bcPr μ (X.Lv.L.bcH0 μ h : (X.Lv.L.baseChange μ).H),
      FiniteLevel.bcPr_mem_H0 μ X.Lv.L (X.Lv.L.bcH0 μ h).2⟩ : X.Lv.L.H0) = h :=
    Subtype.ext (FiniteLevel.bcPr_bcH0 μ X.Lv.L h)
  rw [hh] at this
  rw [← this, hres]

/-- **The fibre of the base change** is the fibre of the given covering. -/
def bcFibreEquiv (X : TempObj O R A) : Fibre Ω V hV (X.baseChange μ) ≃ Fibre Ω V hV X where
  toFun := Quotient.map (bcPreRes μ V hV X) fun q q' ⟨g, hg⟩ => by
    rw [← hg, bcPreRes_smul]
    exact ⟨_, rfl⟩
  invFun := Quotient.map (bcPreExt μ V hV X) fun q q' ⟨g, hg⟩ => by
    rw [← hg, bcPreExt_smul]
    exact ⟨_, rfl⟩
  left_inv x := by
    induction x using Quotient.inductionOn
    apply congrArg Quotient.mk''
    apply Subtype.ext
    simp [bcPreExt, bcPreRes, FiniteLevel.bcExt_bcRes]
  right_inv x := by
    induction x using Quotient.inductionOn
    apply congrArg Quotient.mk''
    apply Subtype.ext
    simp [bcPreExt, bcPreRes, FiniteLevel.bcRes_bcExt]

lemma bcFibreEquiv_mk (X : TempObj O R A) (q : PreFibre Ω V hV (X.baseChange μ)) :
    bcFibreEquiv μ V hV X (Quotient.mk'' q) = Quotient.mk'' (bcPreRes μ V hV X q) := rfl

/-- **The base change functor commutes with the fibre functors.** -/
def bcFibreIso : bcFunctor μ ⋙ tempFibre O R' A' V hV ≅ tempFibre O R A V hV :=
  NatIso.ofComponents (fun X => (bcFibreEquiv μ V hV X).toIso) fun {X Y} m => by
    ext x
    induction x using Quotient.inductionOn with
    | h q =>
      change bcFibreEquiv μ V hV Y (Quotient.mk'' (preMap V hV (bcHom μ m) q)) =
        fibreMap V hV m (bcFibreEquiv μ V hV X (Quotient.mk'' q))
      rw [bcFibreEquiv_mk, bcFibreEquiv_mk]
      apply congrArg Quotient.mk''
      apply Subtype.ext
      simp only [bcPreRes, preMap]
      exact Prod.ext (FiniteLevel.bcRes_bcMap μ m.φ _) rfl

end TempObj

/-- **Functoriality of the tempered fundamental group**: a map of affine orbifolds
`[Spec R' / A'] → [Spec R / A]` (`μ : OrbMap R A R' A'`) induces a homomorphism
`temperedPi1 O R' A' V hV →* temperedPi1 O R A V hV` (restriction along base change). -/
def temperedPi1Map : temperedPi1 O R' A' V hV →* temperedPi1 O R A V hV :=
  FibreAut.restrict (TempObj.bcFunctor μ) (TempObj.bcFibreIso μ V hV)

lemma continuous_temperedPi1Map : Continuous (temperedPi1Map μ V hV) :=
  FibreAut.continuous_restrict _ _

lemma temperedPi1Map_app (γ : temperedPi1 O R' A' V hV) (X : TempObj O R A)
    (x : TempObj.Fibre Ω V hV X) :
    (temperedPi1Map μ V hV γ).app X x = TempObj.bcFibreEquiv μ V hV X
      (γ.app (X.baseChange μ) ((TempObj.bcFibreEquiv μ V hV X).symm x)) := rfl

end Fibre

end

end TemperedFundamentalGroups
