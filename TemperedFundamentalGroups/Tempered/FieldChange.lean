/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChange
import TemperedFundamentalGroups.Tempered.Comparison
import TemperedFundamentalGroups.Models.BaseChange
import TemperedFundamentalGroups.Andre.Pullback

/-!
# Change of the valued field (Blueprint §11, F8)

Let `(K, O) → (K', O')` be an extension of valued fields (`O'.comap (algebraMap K K') = O`) and
`μ : OrbMap R A R' A'` a map of orbifolds `[Spec R' / A'] → [Spec R / A]` with `R'` a
`K'`-algebra (e.g. `R' = K' ⊗_K R`). A tempered covering of `[Spec R / A]` over `(K, O)` pulls
back to a tempered covering of `[Spec R' / A']` over `(K', O')` (`TempObj.fieldChange`): the level
is base-changed as in F1, the model is base-changed to `O'` (`ModelCode.baseChange`, the fibre
product `𝒯 ×_O O'`), and the covering space is pulled back along `|𝒯'_s| → |𝒯_s|`. Its fibre at a
geometric point `Spec Ω → Spec R'` (with `V ∩ K' = O'`) is the fibre of the given covering
(`TempObj.fcFibreIso`). Restriction of fibre-functor automorphisms gives the continuous
homomorphism

`temperedPi1FieldMap : temperedPi1 O' R' A' V hV' →* temperedPi1 O R A V hV`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {K' : Type u} [Field K'] [Algebra K K'] {O' : ValuationSubring K'}
  (hO : O'.comap (algebraMap K K') = O)

/-- The inclusion `O → O'` of valuation rings. -/
def valMap : O →+* O' :=
  ((algebraMap K K').comp O.subtype).codRestrict O'.toSubring fun o => by
    have h : (o : K) ∈ O'.comap (algebraMap K K') := by rw [hO]; exact o.2
    exact h

lemma coe_valMap (o : O) : (valMap hO o : K') = algebraMap K K' o := rfl

instance : IsLocalHom (valMap hO) where
  map_nonunit a ha := by
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 ha
    have hb' : (a : K) ≠ 0 := by
      intro h0
      have := congrArg Subtype.val hb
      simp [coe_valMap, h0] at this
    have hinv : ((a : K)⁻¹) ∈ O := by
      suffices h : algebraMap K K' (a : K)⁻¹ ∈ O' by
        have h' : (a : K)⁻¹ ∈ O'.comap (algebraMap K K') := h
        rwa [hO] at h'
      have : (b : K') = (algebraMap K K' a)⁻¹ := by
        have : (valMap hO a : K') * b = 1 := congrArg Subtype.val hb
        rw [coe_valMap] at this
        exact eq_inv_of_mul_eq_one_right this
      rw [map_inv₀, ← this]
      exact b.2
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hb')⟩

variable {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra K' R'] [Algebra R R'] [Algebra K R']
  [IsScalarTower K R R'] [IsScalarTower K K' R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K' R']
  (μ : OrbMap R A R' A')

namespace FiniteLevel

lemma bcι_comp_levelStructureMap (L : FiniteLevel R A) :
    (L.bcι μ).comp (levelStructureMap O R A L) =
      (levelStructureMap O' R' A' (L.baseChange μ)).comp (valMap hO) := by
  ext o
  change L.bcι μ (algebraMap R L.B (algebraMap K R o)) =
    algebraMap R' _ (algebraMap K' R' (algebraMap K K' o))
  rw [FiniteLevel.bcι_algebraMap]
  congr 1
  rw [← IsScalarTower.algebraMap_apply K R R', ← IsScalarTower.algebraMap_apply K K' R']

end FiniteLevel

namespace Level

variable (Lv : Level O R A)

/-- The base-changed model `𝒯 ×_O O'`. -/
abbrev fcC : ModelCode O' := Lv.c.baseChange (valMap hO)

lemma fc_j_w : (Spec.map (CommRingCat.ofHom (Lv.L.bcι μ)) ≫ Lv.j) ≫ Lv.c.toSpec =
    Spec.map (CommRingCat.ofHom (levelStructureMap O' R' A' (Lv.L.baseChange μ))) ≫
      Spec.map (CommRingCat.ofHom (valMap hO)) := by
  rw [Category.assoc, Lv.j_toSpec, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, FiniteLevel.bcι_comp_levelStructureMap hO μ Lv.L]

/-- The map `j' : Spec (R' ⊗_R B) ⟶ 𝒯 ×_O O'`. -/
def fcJ : Spec (CommRingCat.of (Lv.L.baseChange μ).B) ⟶ (Lv.fcC hO).scheme :=
  Lv.c.bcLift (valMap hO) _ _ (Lv.fc_j_w hO μ)

/-- The action of `g ∈ H` on `𝒯 ×_O O'`. -/
def fcEnd (g : Lv.L.H) : (Lv.fcC hO).scheme ⟶ (Lv.fcC hO).scheme :=
  Lv.c.bcLift (valMap hO) (Lv.c.bcFst (valMap hO) ≫ (Lv.ρ g).hom) (Lv.fcC hO).toSpec (by
    rw [Category.assoc, Lv.ρ_toSpec, ModelCode.bcFst_toSpec])

@[reassoc]
lemma fcEnd_fst (g : Lv.L.H) :
    Lv.fcEnd hO g ≫ Lv.c.bcFst (valMap hO) = Lv.c.bcFst (valMap hO) ≫ (Lv.ρ g).hom :=
  ModelCode.bcLift_fst _ _ _ _ _

@[reassoc]
lemma fcEnd_toSpec (g : Lv.L.H) : Lv.fcEnd hO g ≫ (Lv.fcC hO).toSpec = (Lv.fcC hO).toSpec :=
  ModelCode.bcLift_toSpec _ _ _ _ _

lemma fcEnd_comp (g g' : Lv.L.H) : Lv.fcEnd hO g ≫ Lv.fcEnd hO g' = Lv.fcEnd hO (g' * g) := by
  refine Lv.c.bc_hom_ext (valMap hO) ?_ ?_
  · rw [Category.assoc, fcEnd_fst, fcEnd_fst_assoc, fcEnd_fst, map_mul, Aut.Aut_mul_def,
      Iso.trans_hom]
  · rw [Category.assoc, fcEnd_toSpec, fcEnd_toSpec, fcEnd_toSpec]

lemma fcEnd_one : Lv.fcEnd hO 1 = 𝟙 _ := by
  refine Lv.c.bc_hom_ext (valMap hO) ?_ ?_
  · rw [fcEnd_fst, map_one, Category.id_comp]
    exact Category.comp_id _
  · rw [fcEnd_toSpec, Category.id_comp]

/-- **The action of `H` on `𝒯 ×_O O'`.** -/
def fcAct : Lv.L.H →* Aut (Lv.fcC hO).scheme :=
  MonoidHom.mk' (fun g =>
    { hom := Lv.fcEnd hO g
      inv := Lv.fcEnd hO g⁻¹
      hom_inv_id := by rw [fcEnd_comp, inv_mul_cancel, fcEnd_one]
      inv_hom_id := by rw [fcEnd_comp, mul_inv_cancel, fcEnd_one] })
    fun g g' => by
      ext1
      simp only [Aut.Aut_mul_def, Iso.trans_hom]
      exact (Lv.fcEnd_comp hO g' g).symm

lemma fcAct_hom (g : Lv.L.H) : (Lv.fcAct hO g).hom = Lv.fcEnd hO g := rfl

/-- **The level with model over `(K', O')`.** -/
def fieldChange : Level O' R' A' where
  L := Lv.L.baseChange μ
  c := Lv.fcC hO
  j := Lv.fcJ hO μ
  j_toSpec := ModelCode.bcLift_toSpec _ _ _ _ _
  ρ := (Lv.fcAct hO).comp (Lv.L.bcPr μ)
  ρ_toSpec g := Lv.fcEnd_toSpec hO _
  ρ_j g := by
    refine Lv.c.bc_hom_ext (valMap hO) ?_ ?_
    · simp only [MonoidHom.comp_apply, fcAct_hom, Category.assoc]
      have e1 : Lv.fcJ hO μ ≫ Lv.c.bcFst (valMap hO) =
          Spec.map (CommRingCat.ofHom (Lv.L.bcι μ)) ≫ Lv.j :=
        ModelCode.bcLift_fst _ _ _ _ _
      have e2 : Lv.fcEnd hO (Lv.L.bcPr μ g) ≫ Lv.c.bcFst (valMap hO) =
          Lv.c.bcFst (valMap hO) ≫ (Lv.ρ (Lv.L.bcPr μ g)).hom := Lv.fcEnd_fst hO _
      rw [e2, ← Category.assoc (Lv.fcJ hO μ), e1]
      refine Eq.trans ?_ (Category.assoc _ _ _).symm
      refine Eq.trans ?_ (congrArg (Spec.map (CommRingCat.ofHom (Lv.L.bcι μ)) ≫ ·)
        (Lv.ρ_j (Lv.L.bcPr μ g)))
      simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      exact RingHom.ext fun y => FiniteLevel.bcσ_symm_bcι μ Lv.L g y
    · simp only [MonoidHom.comp_apply, fcAct_hom, Category.assoc, fcEnd_toSpec]
      rw [fcJ, ModelCode.bcLift_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      refine congrArg (fun φ => Spec.map (CommRingCat.ofHom φ)) (RingHom.ext fun o => ?_)
      exact levelStructureMap_σ O' R' A' _
        (g : SemilinearAut R' A' (Lv.L.baseChange μ).B)⁻¹ o

end Level

end

end TemperedFundamentalGroups
