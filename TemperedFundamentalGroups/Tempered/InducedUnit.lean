/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.InducedFibre

/-!
# The unit of induction (Blueprint §11, F7′)

For induction data `D` of a tempered covering `X'` of `[Spec R / A']`, the copy `1` gives a
morphism `X' ⟶ bc (Ind X')` of tempered coverings of `[Spec R / A']` (`IndData.unit`): the
evaluation at `1` on algebras, `k ↦ ((β k, k), k.a)` on groups, the inclusion of the copy `1` of
the model and of the covering space. Under the identification of fibres of the base change
(`TempObj.bcFibreEquiv`) it induces `ι` (`IndData.bcFibreEquiv_unit`).
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

variable {X' : TempObj O R A'} (D : IndData μ X') (hX : IndFaithful X')

/-- The map `R ⊗_R (Π x, B'^{(α x)}) → B'`, `r ⊗ φ ↦ r φ(1)`. -/
def unitF : (D.level.baseChange μ).B →ₐ[R] X'.Lv.L.B :=
  (Algebra.TensorProduct.lift (Algebra.ofId R X'.Lv.L.B) D.ev₁ fun _ _ => Commute.all _ _).comp
    (D.level.bcE' μ).toAlgHom

lemma unitF_bcι (y : D.level.B) : D.unitF (D.level.bcι μ y) = D.ev 1 y := by
  rw [unitF, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, FiniteLevel.bcE_bcι,
    Algebra.TensorProduct.lift_tmul, map_one, one_mul, ev₁_apply]

/-- The homomorphism `H' → H ×_A A'`, `k ↦ ((β k, k), k.a)`. -/
def unitP : X'.Lv.L.H →* D.level.Hfp μ where
  toFun k := ⟨(D.equivT hX (D.β k, k), (k : SemilinearAut R A' X'.Lv.L.B).a), by
    rw [FiniteLevel.mem_Hfp, equivT_apply, homT_a, D.hβ]⟩
  map_one' := by
    ext1
    simp only [map_one, Prod.mk_one_one, OneMemClass.coe_one, SemilinearAut.one_a]
  map_mul' k k' := Subtype.ext (Prod.ext (by
    change D.equivT hX (D.β (k * k'), k * k') = D.equivT hX (D.β k, k) * D.equivT hX (D.β k', k')
    rw [← map_mul, Prod.mk_mul_mk, map_mul]) rfl)

/-- The homomorphism of groups of the unit. -/
def unitR : X'.Lv.L.H →* (D.level.baseChange μ).H :=
  (D.level.bcEquiv μ).toMonoidHom.comp (D.unitP hX)

lemma bcPr_unitR (k : X'.Lv.L.H) :
    D.level.bcPr μ (D.unitR hX k) = D.equivT hX (D.β k, k) :=
  FiniteLevel.bcPr_bcEquiv μ _ _

lemma unitF_σ (k : X'.Lv.L.H) (y : (D.level.baseChange μ).B) :
    D.unitF (((D.unitR hX k : (D.level.baseChange μ).H) :
      SemilinearAut R A' (D.level.baseChange μ).B).σ y) =
      (k : SemilinearAut R A' X'.Lv.L.B).σ (D.unitF y) := by
  change D.unitF ((D.level.bcE' μ).symm ((FiniteLevel.bcAut μ D.level (D.unitP hX k)).σ
    (D.level.bcE' μ y))) = _
  simp only [unitF, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  induction D.level.bcE' μ y using TensorProduct.induction_on with
  | zero => simp
  | tmul r b =>
    rw [FiniteLevel.bcAut_σ_tmul, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.lift_tmul, map_mul, Algebra.ofId_apply, Algebra.ofId_apply,
      (k : SemilinearAut R A' X'.Lv.L.B).map_algebraMap, ev₁_apply, ev₁_apply]
    congr 1
    change D.ev 1 (((D.equivT hX (D.β k, k) : D.level.H) : SemilinearAut R A D.level.B).σ b) = _
    rw [ev_equivT]
    congr 2
    group
  | add z z' hz hz' =>
    rw [RingEquiv.map_add, _root_.map_add, _root_.map_add, hz, hz', RingEquiv.map_add]

/-- **The morphism of levels of the unit.** -/
def unitφ : X'.Lv.L ⟶ D.level.baseChange μ where
  f := D.unitF
  r := D.unitR hX
  r_a _ := rfl
  f_σ k y := D.unitF_σ hX k y

lemma unit_j_ψ : X'.Lv.j ≫ D.inc 1 =
    Spec.map (CommRingCat.ofHom ((D.unitφ hX).f : (D.level.baseChange μ).B →+* X'.Lv.L.B)) ≫
      ((D.lv hX).baseChange μ).j := by
  change _ = _ ≫ Spec.map (CommRingCat.ofHom (D.level.bcι μ)) ≫ D.j
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have h : ((D.unitφ hX).f : (D.level.baseChange μ).B →+* X'.Lv.L.B).comp (D.level.bcι μ) =
      D.ev 1 := RingHom.ext fun y => D.unitF_bcι y
  rw [h, specMap_ev_j]

/-- **The unit** `X' ⟶ bc (Ind X')`. -/
def unit : X' ⟶ (D.obj hX).baseChange μ where
  φ := D.unitφ hX
  ψ := D.inc 1
  ψ_toSpec := D.inc_toSpec 1
  j_ψ := D.unit_j_ψ hX
  h := D.incP hX
  continuous_h := D.continuous_incP hX
  fst_h p := D.inc₁S_coe hX p.1.1
  h_act k p := by
    change D.incP hX (X'.P.act k p) = (D.obj hX).P.act (D.level.bcPr μ (D.unitR hX k))
      (D.incP hX p)
    rw [bcPr_unitR, act_incP]

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma bcFibreEquiv_unit (x : TempObj.Fibre Ω V hV X') :
    TempObj.bcFibreEquiv μ V hV (D.obj hX) (TempObj.fibreMap V hV (D.unit hX) x) =
      D.ι hX V hV x := by
  induction x using Quotient.inductionOn with
  | h q =>
    refine congrArg Quotient.mk'' (Subtype.ext (Prod.ext ?_ rfl))
    ext y
    change q.1.1 (D.unitF (D.level.bcι μ y)) = q.1.1 (D.ev₁ y)
    rw [unitF_bcι, ev₁_apply]

end IndData

end

end TemperedFundamentalGroups
