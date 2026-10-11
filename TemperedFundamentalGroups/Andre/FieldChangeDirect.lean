/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.FieldChange

/-!
# The change of the valued field on André's groups, defined directly (Blueprint §11, F8 (c′))

Let `(K, O) → (K', O')` be an extension of valued fields with `O'` finite over `O`. Restriction of
scalars of tempered coverings (`TempObj.rsObj`: the same level and covering space, the model
`ModelCode.restrictScalars` viewed over `O`) is a functor `TempObj.rsFunctor` with
`rsFibreIso : rsFunctor ⋙ tempFibre O ≅ tempFibre O'`, and it **preserves semistable levels**
for `K'/K` finite (`isSemistableLevel_rs`: a semistable model over a finite extension `K''/K'` is
one over the finite extension `K''/K`). Restricting automorphisms of fibre functors along it
gives, without Theorem A,

* `temperedPi1Rs : temperedPi1 O R' A' →* temperedPi1 O' R' A'`, a left inverse of the pure field
  change (`temperedPi1Rs_temperedPi1FieldMap`), hence its inverse
  (`temperedPi1Rs_eq_symm`);
* **`andreFieldMap : andreGroup O R' A' →* andreGroup O' R' A'`**, the field change on André's
  groups defined directly by restriction along the functor `rsSemistable` of semistable
  coverings, continuous (`continuous_andreFieldMap`) and compatible with the restrictions
  `temperedPi1 → andreGroup` (`andreRestrict_temperedPi1Rs`).

Under the hypotheses of Theorem A over `(K, O)` and `(K', O')`, `andreFieldMap` is the inverse of
`andreFieldEquiv'` (`andreFieldMap_andreFieldEquiv'`, `andreFieldEquiv'_andreFieldMap`,
`andreFieldEquiv'_symm_apply`), so `andreFieldEquiv'` (built from Theorem A) is the inverse of
the direct map; `andreFieldEquivDirect` is the resulting isomorphism with
`andreFieldEquivDirect_apply : andreFieldEquivDirect γ = andreFieldMap γ` (definitionally the
direct map) and `andreFieldEquivDirect_symm : andreFieldEquivDirect.symm = andreFieldEquiv'`.

**Why restriction of scalars and not base change.** The base change `TempObj.fieldChange` (models
the scheme-theoretic image of the generic fibre in `𝒯 ×_O O'`) does not preserve semistable
levels: if `𝒯` is semistable over `O''` (finite over `O`), the image lies in `𝒯 ×_{O''} O₁` for
the order `O₁ = im (O'' ⊗_O O' → L)` of a factor `L` of `K'' ⊗_K K'`, which is in general not
normal (e.g. for two different ramified extensions `K''`, `K'`), while a semistable model over a
discrete valuation ring is normal; making it semistable needs normalization of the model, which
is not available for these coded models. Restriction of scalars goes the other way and keeps the
model scheme, so it preserves semistability; this is why the direct map goes from `O` to `O'`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {K' : Type u} [Field K'] [Algebra K K'] {O' : ValuationSubring K'}
  (hO : O'.comap (algebraMap K K') = O) (hfin : (valMap hO).Finite)
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra K R'] [IsScalarTower K K' R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']

namespace TempObj

/-! ### The restriction of scalars functor -/

lemma rsMap_id (X : TempObj O' R' A') : rsMap hO hfin (𝟙 X) = 𝟙 (rsObj hO hfin X) := by
  refine Hom.ext rfl ?_ (funext fun q => ?_)
  · change (X.Lv.c.rsIso hfin).inv ≫ 𝟙 _ ≫ (X.Lv.c.rsIso hfin).hom = 𝟙 _
    rw [Category.id_comp, Iso.inv_hom_id]
  · refine CoveringCode.pullbackPt_injective X.P (X.Lv.rsZ hO hfin).symm.injective ?_
    rw [rsMap_h, pullbackPt_rsH]
    rfl

lemma rsMap_comp {X Y Z : TempObj O' R' A'} (m : X ⟶ Y) (n : Y ⟶ Z) :
    rsMap hO hfin (m ≫ n) = rsMap hO hfin m ≫ rsMap hO hfin n := by
  refine Hom.ext rfl ?_ (funext fun q => ?_)
  · change (X.Lv.c.rsIso hfin).inv ≫ (m.ψ ≫ n.ψ) ≫ (Z.Lv.c.rsIso hfin).hom =
      ((X.Lv.c.rsIso hfin).inv ≫ m.ψ ≫ (Y.Lv.c.rsIso hfin).hom) ≫
        (Y.Lv.c.rsIso hfin).inv ≫ n.ψ ≫ (Z.Lv.c.rsIso hfin).hom
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  · refine CoveringCode.pullbackPt_injective Z.P (Z.Lv.rsZ hO hfin).symm.injective ?_
    change CoveringCode.pullbackPt Z.P _ (rsH hO hfin (m ≫ n) q) =
      CoveringCode.pullbackPt Z.P _ (rsH hO hfin n (rsH hO hfin m q))
    rw [pullbackPt_rsH, pullbackPt_rsH, pullbackPt_rsH]
    rfl

/-- **Restriction of scalars of tempered coverings** along `O → O'` (`O'` finite over `O`). -/
def rsFunctor : TempObj O' R' A' ⥤ TempObj O R' A' where
  obj := rsObj hO hfin
  map m := rsMap hO hfin m
  map_id X := rsMap_id hO hfin X
  map_comp m n := rsMap_comp hO hfin m n

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

lemma rsFibreEquiv_fibreMap {X Y : TempObj O' R' A'} (m : X ⟶ Y)
    (x : Fibre Ω V (comap_eq hO V hV') (rsObj hO hfin X)) :
    rsFibreEquiv hO hfin V hV' Y (fibreMap V (comap_eq hO V hV') (rsMap hO hfin m) x) =
      fibreMap V hV' m (rsFibreEquiv hO hfin V hV' X x) := by
  induction x using Quotient.inductionOn with
  | h q => exact congrArg Quotient.mk'' (Subtype.ext (Prod.ext rfl (pullbackPt_rsH hO hfin m _)))

/-- **The fibre functors agree along restriction of scalars.** -/
def rsFibreIso : rsFunctor hO hfin ⋙ tempFibre O R' A' V (comap_eq hO V hV') ≅
    tempFibre O' R' A' V hV' :=
  NatIso.ofComponents (fun X => (rsFibreEquiv hO hfin V hV' X).toIso) fun m => by
    ext x
    exact rsFibreEquiv_fibreMap hO hfin V hV' m x

lemma rsFibreIso_hom_app (X : TempObj O' R' A')
    (x : Fibre Ω V (comap_eq hO V hV') (rsObj hO hfin X)) :
    (rsFibreIso hO hfin V hV').hom.app X x = rsFibreEquiv hO hfin V hV' X x := rfl

end Fibre

end TempObj

open TempObj

/-! ### The restriction on tempered groups -/

section Tempered

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

variable (R' A') in
/-- **Restriction along restriction of scalars**: `temperedPi1 O R' A' →* temperedPi1 O' R' A'`
(no Theorem A involved). -/
def temperedPi1Rs : temperedPi1 O R' A' V (comap_eq hO V hV') →* temperedPi1 O' R' A' V hV' :=
  FibreAut.restrict (rsFunctor (R' := R') (A' := A') hO hfin)
    (rsFibreIso (R' := R') (A' := A') hO hfin V hV')

lemma continuous_temperedPi1Rs : Continuous (temperedPi1Rs hO hfin R' A' V hV') :=
  FibreAut.continuous_restrict _ _

/-- `temperedPi1Rs` is a left inverse of the pure field change. -/
theorem temperedPi1Rs_temperedPi1FieldMap (γ : temperedPi1 O' R' A' V hV') :
    temperedPi1Rs hO hfin R' A' V hV' (temperedPi1FieldMap hO (OrbMap.id R' A') V hV' γ) = γ := by
  ext X x
  obtain ⟨z, rfl⟩ := (bijective_fibreMap_rsW hO hfin V hV' X).2 x
  have hw : ∀ z, fibreMap V hV' (rsW hO hfin X) z =
      (rsFibreIso hO hfin V hV').hom.app X
        ((fcFibreIso O O' hO (OrbMap.id R' A') V hV').hom.app (rsObj hO hfin X) z) :=
    fun z => fibreMap_rsW hO hfin V hV' X z
  have h₁ := restrict_app_e (G := rsFunctor (R' := R') (A' := A') hO hfin)
    (e := rsFibreIso hO hfin V hV') (temperedPi1FieldMap hO (OrbMap.id R' A') V hV' γ) X
    ((fcFibreIso O O' hO (OrbMap.id R' A') V hV').hom.app (rsObj hO hfin X) z)
  have h₂ := restrict_app_e (G := fcFunctor O O' hO (OrbMap.id R' A'))
    (e := fcFibreIso O O' hO (OrbMap.id R' A') V hV') γ (rsObj hO hfin X) z
  have h₃ := FibreAut.app_naturality γ (rsW hO hfin X) z
  rw [hw]
  refine h₁.trans ?_
  erw [h₂]
  exact (hw _).symm.trans (h₃.symm.trans (congrArg (γ.app X) (hw z)))

/-- `temperedPi1Rs` is the inverse of the pure field change `temperedPi1FieldEquiv`. -/
theorem temperedPi1Rs_eq_symm (δ : temperedPi1 O R' A' V (comap_eq hO V hV')) :
    temperedPi1Rs hO hfin R' A' V hV' δ = (temperedPi1FieldEquiv hO hfin V hV').symm δ := by
  obtain ⟨γ, rfl⟩ := (temperedPi1FieldEquiv hO hfin V hV').surjective δ
  rw [ContinuousMulEquiv.symm_apply_apply, temperedPi1FieldEquiv_apply,
    temperedPi1Rs_temperedPi1FieldMap]

end Tempered

/-! ### Semistable levels and André's groups -/

section Semistable

variable [FiniteDimensional K K']

include hO in
/-- **Restriction of scalars preserves semistable levels** (`K'/K` finite). -/
theorem isSemistableLevel_rs {Lv : Level O' R' A'} (h : IsSemistableLevel Lv) :
    IsSemistableLevel (Lv.rs hO hfin) := by
  obtain ⟨K'', _, _, _, O'', h'', _, ϖ, hϖ, c'', e, hss, hcomp⟩ := h
  letI : Algebra K K'' := ((algebraMap K' K'').comp (algebraMap K K')).toAlgebra
  haveI : IsScalarTower K K' K'' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : FiniteDimensional K K'' := Module.Finite.trans K' K''
  have hc : O''.comap (algebraMap K K'') = O := by
    rw [← hO, ← h'', IsScalarTower.algebraMap_eq K K' K'']
    rfl
  refine ⟨K'', inferInstance, inferInstance, inferInstance, O'', hc, inferInstance, ϖ, hϖ, c'',
    (Lv.c.rsIso hfin).symm ≪≫ e, hss, ?_⟩
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  have hmap : Spec.map (CommRingCat.ofHom ((algebraMap K K'').restrict O O'' (fun x hx => by
        rw [← hc] at hx; exact hx))) =
      Spec.map (CommRingCat.ofHom ((algebraMap K' K'').restrict O' O'' (fun x hx => by
        rw [← h''] at hx; exact hx))) ≫ Spec.map (CommRingCat.ofHom (valMap hO)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  rw [hmap, ← Category.assoc c''.toSpec, ← Category.assoc e.hom, hcomp]
  exact ModelCode.rsIso_inv_toSpec hfin Lv.c

/-- Restriction of scalars on tempered coverings presented through semistable levels. -/
def rsSemistable :
    (semistableObj O' R' A').FullSubcategory ⥤ (semistableObj O R' A').FullSubcategory :=
  (semistableObj O R' A').lift ((semistableObj O' R' A').ι ⋙ rsFunctor hO hfin)
    fun X => isSemistableLevel_rs hO hfin X.2

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')

/-- The fibre functors agree along `rsSemistable`. -/
def rsSemistableFibreIso :
    rsSemistable hO hfin ⋙ (semistableObj O R' A').ι ⋙
        tempFibre O R' A' V (comap_eq hO V hV') ≅
      (semistableObj O' R' A').ι ⋙ tempFibre O' R' A' V hV' :=
  Functor.isoWhiskerLeft (semistableObj O' R' A').ι (rsFibreIso hO hfin V hV')

variable (R' A') in
/-- **The change of the valued field on André's groups, defined directly**: restriction of
automorphisms of the fibre functor along restriction of scalars of semistable coverings,
`andreGroup O R' A' →* andreGroup O' R' A'` (no Theorem A involved). -/
def andreFieldMap :
    andreGroup O R' A' V (comap_eq hO V hV') →* andreGroup O' R' A' V hV' :=
  FibreAut.restrict (rsSemistable (R' := R') (A' := A') hO hfin)
    (rsSemistableFibreIso (R' := R') (A' := A') hO hfin V hV')

lemma continuous_andreFieldMap : Continuous (andreFieldMap hO hfin R' A' V hV') :=
  FibreAut.continuous_restrict _ _

/-- The direct field change is compatible with the restrictions `temperedPi1 → andreGroup`. -/
theorem andreRestrict_temperedPi1Rs (δ : temperedPi1 O R' A' V (comap_eq hO V hV')) :
    andreRestrict O' R' A' V hV' (temperedPi1Rs hO hfin R' A' V hV' δ) =
      andreFieldMap hO hfin R' A' V hV' (andreRestrict O R' A' V (comap_eq hO V hV') δ) := by
  ext c x
  rfl

end Semistable

/-! ### Comparison with `andreFieldEquiv'` (Theorem A) -/

section TheoremA

variable [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [PerfectField (IsLocalRing.ResidueField O)]
  [CharZero K'] [IsDiscreteValuationRing O'] [IsAdicComplete (IsLocalRing.maximalIdeal O') O']
  [PerfectField (IsLocalRing.ResidueField O')]
  [IsDomain R'] [Algebra.Smooth K R'] [Algebra.Smooth K' R'] [SMulCommClass A' K R'] [Finite A']
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra K' Ω] [IsScalarTower K K' Ω]
  [Algebra R' Ω] [IsScalarTower K' R' Ω] [IsScalarTower K R' Ω] [IsAlgClosed Ω]
  (V : ValuationSubring Ω) (hV' : V.comap (algebraMap K' Ω) = O')
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
  (hp' : ∃ p : ℕ, p.Prime ∧ (p : O') ∈ IsLocalRing.maximalIdeal O')
  (hR : ringKrullDim R' = 1) [FiniteDimensional K K']

/-- **The direct field change inverts `andreFieldEquiv'`.** -/
theorem andreFieldMap_andreFieldEquiv' (γ : andreGroup O' R' A' V hV') :
    andreFieldMap hO (valMap_finite hO) R' A' V hV'
      (andreFieldEquiv' hO V hV' hp hp' hR γ) = γ := by
  obtain ⟨γ', rfl⟩ := (andreEquiv' V hV' hp' hR).surjective γ
  rw [andreEquiv'_apply, andreFieldEquiv'_andreRestrict, ← andreRestrict_temperedPi1Rs,
    temperedPi1Rs_temperedPi1FieldMap]

theorem andreFieldEquiv'_andreFieldMap (δ : andreGroup O R' A' V (comap_eq hO V hV')) :
    andreFieldEquiv' hO V hV' hp hp' hR
      (andreFieldMap hO (valMap_finite hO) R' A' V hV' δ) = δ := by
  obtain ⟨γ, rfl⟩ := (andreFieldEquiv' hO V hV' hp hp' hR).surjective δ
  rw [andreFieldMap_andreFieldEquiv']

/-- **`andreFieldEquiv'` is the inverse of the direct field change.** -/
theorem andreFieldEquiv'_symm_apply (δ : andreGroup O R' A' V (comap_eq hO V hV')) :
    (andreFieldEquiv' hO V hV' hp hp' hR).symm δ =
      andreFieldMap hO (valMap_finite hO) R' A' V hV' δ :=
  (ContinuousMulEquiv.symm_apply_eq _).2 (andreFieldEquiv'_andreFieldMap hO V hV' hp hp' hR δ).symm

include hp hp' hR in
theorem bijective_andreFieldMap :
    Function.Bijective (andreFieldMap hO (valMap_finite hO) R' A' V hV') := by
  rw [← funext (andreFieldEquiv'_symm_apply hO V hV' hp hp' hR)]
  exact (andreFieldEquiv' hO V hV' hp hp' hR).symm.bijective

/-- **The direct field change is an isomorphism of topological groups**
`andreGroup O R' A' ≃ₜ* andreGroup O' R' A'`, with underlying map `andreFieldMap`
(`andreFieldEquivDirect_apply`) and inverse `andreFieldEquiv'` (`andreFieldEquivDirect_symm`). -/
def andreFieldEquivDirect :
    andreGroup O R' A' V (comap_eq hO V hV') ≃ₜ* andreGroup O' R' A' V hV' where
  toFun := andreFieldMap hO (valMap_finite hO) R' A' V hV'
  invFun := andreFieldEquiv' hO V hV' hp hp' hR
  left_inv := andreFieldEquiv'_andreFieldMap hO V hV' hp hp' hR
  right_inv := andreFieldMap_andreFieldEquiv' hO V hV' hp hp' hR
  map_mul' := map_mul _
  continuous_toFun := continuous_andreFieldMap (R' := R') (A' := A') hO _ V hV'
  continuous_invFun := (andreFieldEquiv' hO V hV' hp hp' hR).continuous

lemma andreFieldEquivDirect_apply (δ : andreGroup O R' A' V (comap_eq hO V hV')) :
    andreFieldEquivDirect (R' := R') (A' := A') hO V hV' hp hp' hR δ =
      andreFieldMap hO (valMap_finite hO) R' A' V hV' δ :=
  rfl

/-- **Agreement with Theorem A**: the direct field change is the inverse of `andreFieldEquiv'`. -/
theorem andreFieldEquivDirect_symm :
    (andreFieldEquivDirect (R' := R') (A' := A') hO V hV' hp hp' hR).symm =
      andreFieldEquiv' hO V hV' hp hp' hR :=
  ContinuousMulEquiv.ext fun _ => rfl

end TheoremA

end

end TemperedFundamentalGroups
