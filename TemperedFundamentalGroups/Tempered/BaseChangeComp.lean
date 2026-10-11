/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChange

/-!
# `temperedPi1Map` is a functor (Blueprint §11, F4)

* `OrbMap.id`, `OrbMap.comp`: identity and composite maps of orbifolds.
* `temperedPi1Map_id`: the identity map induces the identity.
* `temperedPi1Map_comp`: for `[Spec R'' / A''] → [Spec R' / A'] → [Spec R / A]`,
  `temperedPi1Map (μ₁.comp μ₂) = temperedPi1Map μ₁ ∘ temperedPi1Map μ₂`.

Both are proved with comparison morphisms in the tempered category which are compatible with the
fibre isomorphisms: `bc_id Y ⟶ Y` (`b ↦ 1 ⊗ b`) and `bc₂ (bc₁ Y) ⟶ bc₁₂ Y`
(`r'' ⊗ b ↦ r'' ⊗ (1 ⊗ b)`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

/-- The identity map of an orbifold. -/
def OrbMap.id (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R] :
    OrbMap R A R A where
  α := MonoidHom.id A
  map_smul _ _ := rfl
  injective := Function.injective_id

/-- The composite of maps of orbifolds `[Spec R'' / A''] → [Spec R' / A'] → [Spec R / A]`. -/
def OrbMap.comp {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]
    {R' : Type u} [CommRing R'] [Algebra R R'] {A' : Type u} [Group A']
    [MulSemiringAction A' R'] {R'' : Type u} [CommRing R''] [Algebra R' R''] [Algebra R R'']
    [IsScalarTower R R' R''] {A'' : Type u} [Group A''] [MulSemiringAction A'' R'']
    (μ₁ : OrbMap R A R' A') (μ₂ : OrbMap R' A' R'' A'') : OrbMap R A R'' A'' where
  α := μ₁.α.comp μ₂.α
  map_smul a r := by
    rw [IsScalarTower.algebraMap_apply R R' R'', MonoidHom.comp_apply, μ₁.map_smul, μ₂.map_smul,
      ← IsScalarTower.algebraMap_apply]
  injective := by
    rw [IsScalarTower.algebraMap_eq R R' R'', RingHom.coe_comp]
    exact μ₂.injective.comp μ₁.injective

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

section Id

namespace TempObj

/-- The comparison morphism `bc_id Y ⟶ Y`. -/
def bcIdHom (Y : TempObj O R A) : Y.baseChange (OrbMap.id R A) ⟶ Y where
  φ :=
    { f := { Y.Lv.L.bcι (OrbMap.id R A) with
        commutes' := fun r => by
          change Y.Lv.L.bcι (OrbMap.id R A) (algebraMap R Y.Lv.L.B r) = _
          rw [FiniteLevel.bcι_algebraMap]
          rfl }
      r := Y.Lv.L.bcPr (OrbMap.id R A)
      r_a g := Y.Lv.L.bcPr_a (OrbMap.id R A) g
      f_σ g y := (Y.Lv.L.bcσ_bcι (OrbMap.id R A) g y).symm }
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := Category.comp_id _
  h := _root_.id
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act _ _ := rfl

lemma fibreMap_bcIdHom (Y : TempObj O R A) (z : Fibre Ω V hV (Y.baseChange (OrbMap.id R A))) :
    fibreMap V hV Y.bcIdHom z = bcFibreEquiv (OrbMap.id R A) V hV Y z := by
  induction z using Quotient.inductionOn
  rfl

end TempObj

/-- **The identity map induces the identity.** -/
theorem temperedPi1Map_id (γ : temperedPi1 O R A V hV) :
    temperedPi1Map (OrbMap.id R A) V hV γ = γ := by
  ext Y y
  rw [temperedPi1Map_app]
  set z := (TempObj.bcFibreEquiv (OrbMap.id R A) V hV Y).symm y with hz
  have hy : y = TempObj.fibreMap V hV Y.bcIdHom z := by
    rw [TempObj.fibreMap_bcIdHom, hz, Equiv.apply_symm_apply]
  rw [hy, ← TempObj.fibreMap_bcIdHom]
  exact (FibreAut.app_naturality γ Y.bcIdHom z).symm

end Id

section Comp

variable {R' : Type u} [CommRing R'] [Algebra K R'] [Algebra R R'] [IsScalarTower K R R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R']
  {R'' : Type u} [CommRing R''] [Algebra K R''] [Algebra R' R''] [IsScalarTower K R' R'']
  [Algebra R R''] [IsScalarTower R R' R''] [IsScalarTower K R R'']
  {A'' : Type u} [Group A''] [MulSemiringAction A'' R'']
  (μ₁ : OrbMap R A R' A') (μ₂ : OrbMap R' A' R'' A'')

namespace FiniteLevel

/-- `ι₂ ∘ ι₁ : B → R'' ⊗_{R'} (R' ⊗_R B)`, `R`-linear. -/
def bcι₂₁ (L : FiniteLevel R A) : L.B →ₐ[R] ((L.baseChange μ₁).baseChange μ₂).B :=
  { ((L.baseChange μ₁).bcι μ₂).comp (L.bcι μ₁) with
    commutes' := fun r => by
      change (L.baseChange μ₁).bcι μ₂ (L.bcι μ₁ (algebraMap R L.B r)) = _
      rw [bcι_algebraMap, bcι_algebraMap, ← IsScalarTower.algebraMap_apply R R' R'',
        ← IsScalarTower.algebraMap_apply R R'' ((L.baseChange μ₁).baseChange μ₂).B] }

lemma bcι₂₁_apply (L : FiniteLevel R A) (b : L.B) :
    L.bcι₂₁ μ₁ μ₂ b = (L.baseChange μ₁).bcι μ₂ (L.bcι μ₁ b) := rfl

/-- The comparison map `R'' ⊗_R B → R'' ⊗_{R'} (R' ⊗_R B)` on coded levels. -/
def cmpF (L : FiniteLevel R A) :
    (L.baseChange (μ₁.comp μ₂)).B →ₐ[R''] ((L.baseChange μ₁).baseChange μ₂).B :=
  (Algebra.TensorProduct.lift (Algebra.ofId R'' _) (L.bcι₂₁ μ₁ μ₂)
    fun _ _ => Commute.all _ _).comp (L.bcE' (μ₁.comp μ₂)).toAlgHom

lemma cmpF_bcι (L : FiniteLevel R A) (b : L.B) :
    L.cmpF μ₁ μ₂ (L.bcι (μ₁.comp μ₂) b) = (L.baseChange μ₁).bcι μ₂ (L.bcι μ₁ b) := by
  simp [cmpF, bcE_bcι, bcι₂₁_apply]

/-- The comparison homomorphism of groups `H₂ → H₁₂`. -/
def cmpR (L : FiniteLevel R A) :
    ((L.baseChange μ₁).baseChange μ₂).H →* (L.baseChange (μ₁.comp μ₂)).H :=
  (L.bcEquiv (μ₁.comp μ₂)).toMonoidHom.comp
    { toFun := fun g => ⟨(L.bcPr μ₁ ((L.baseChange μ₁).bcPr μ₂ g),
        (g : SemilinearAut R'' A'' _).a), by
          rw [mem_Hfp, bcPr_a, bcPr_a]
          rfl⟩
      map_one' := by ext <;> simp
      map_mul' _ _ := by ext <;> simp }

lemma bcPr_cmpR (L : FiniteLevel R A) (g : ((L.baseChange μ₁).baseChange μ₂).H) :
    L.bcPr (μ₁.comp μ₂) (L.cmpR μ₁ μ₂ g) = L.bcPr μ₁ ((L.baseChange μ₁).bcPr μ₂ g) :=
  bcPr_bcEquiv _ _ _

lemma cmpF_σ (L : FiniteLevel R A) (g : ((L.baseChange μ₁).baseChange μ₂).H)
    (z : R'' ⊗[R] L.B) :
    Algebra.TensorProduct.lift (Algebra.ofId R'' _) (L.bcι₂₁ μ₁ μ₂)
        (fun _ _ => Commute.all _ _)
        ((bcAut (μ₁.comp μ₂) L ((L.bcEquiv (μ₁.comp μ₂)).symm (L.cmpR μ₁ μ₂ g))).σ z) =
      (g : SemilinearAut R'' A'' _).σ (Algebra.TensorProduct.lift (Algebra.ofId R'' _)
        (L.bcι₂₁ μ₁ μ₂) (fun _ _ => Commute.all _ _) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [bcAut_σ_tmul, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul,
      map_mul]
    simp only [cmpR, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulEquiv.symm_apply_apply, MonoidHom.coe_mk, OneHom.coe_mk, Algebra.ofId_apply,
      bcι₂₁_apply]
    rw [show (g.1 : SemilinearAut R'' A'' _).σ (algebraMap R'' _ a) =
      algebraMap R'' _ (g.1.a • a) from g.1.map_algebraMap a, bcσ_bcι, bcσ_bcι]
  | add x y hx hy => rw [RingEquiv.map_add, map_add, hx, hy, map_add, RingEquiv.map_add]

/-- The comparison morphism of levels `bc₂ (bc₁ L) ⟶ bc₁₂ L`. -/
def cmpLevel (L : FiniteLevel R A) :
    (L.baseChange μ₁).baseChange μ₂ ⟶ L.baseChange (μ₁.comp μ₂) where
  f := L.cmpF μ₁ μ₂
  r := L.cmpR μ₁ μ₂
  r_a _ := rfl
  f_σ g y := by
    have h := L.cmpF_σ μ₁ μ₂ g (L.bcE' (μ₁.comp μ₂) y)
    conv_lhs => rw [← (L.bcEquiv (μ₁.comp μ₂)).apply_symm_apply (L.cmpR μ₁ μ₂ g)]
    rw [bcEquiv_σ]
    simp only [cmpF, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
    exact h

end FiniteLevel

namespace TempObj

lemma cmp_j_ψ (Y : TempObj O R A) :
    (Spec.map (CommRingCat.ofHom ((Y.Lv.L.baseChange μ₁).bcι μ₂)) ≫
      Spec.map (CommRingCat.ofHom (Y.Lv.L.bcι μ₁)) ≫ Y.Lv.j) ≫ 𝟙 _ =
      Spec.map (CommRingCat.ofHom ((Y.Lv.L.cmpLevel μ₁ μ₂).f :
        (Y.Lv.L.baseChange (μ₁.comp μ₂)).B →+* ((Y.Lv.L.baseChange μ₁).baseChange μ₂).B)) ≫
        Spec.map (CommRingCat.ofHom (Y.Lv.L.bcι (μ₁.comp μ₂))) ≫ Y.Lv.j := by
  rw [Category.comp_id, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  refine congrArg CommRingCat.ofHom (RingHom.ext fun b => ?_)
  exact (Y.Lv.L.cmpF_bcι μ₁ μ₂ b).symm

/-- The comparison morphism `bc₂ (bc₁ Y) ⟶ bc₁₂ Y`. -/
def cmpHom (Y : TempObj O R A) :
    (Y.baseChange μ₁).baseChange μ₂ ⟶ Y.baseChange (μ₁.comp μ₂) where
  φ := Y.Lv.L.cmpLevel μ₁ μ₂
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := Y.cmp_j_ψ μ₁ μ₂
  h := _root_.id
  continuous_h := continuous_id
  fst_h _ := rfl
  h_act g x := by
    change Y.P.act (Y.Lv.L.bcPr μ₁ ((Y.Lv.L.baseChange μ₁).bcPr μ₂ g)) x =
      Y.P.act (Y.Lv.L.bcPr (μ₁.comp μ₂) (Y.Lv.L.cmpR μ₁ μ₂ g)) x
    rw [FiniteLevel.bcPr_cmpR]

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  [Algebra R'' Ω] [IsScalarTower K R'' Ω] [IsScalarTower R' R'' Ω] [IsScalarTower R R'' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma fibreMap_cmpHom (Y : TempObj O R A)
    (z : Fibre Ω V hV ((Y.baseChange μ₁).baseChange μ₂)) :
    bcFibreEquiv (μ₁.comp μ₂) V hV Y (fibreMap V hV (Y.cmpHom μ₁ μ₂) z) =
      bcFibreEquiv μ₁ V hV Y (bcFibreEquiv μ₂ V hV (Y.baseChange μ₁) z) := by
  induction z using Quotient.inductionOn with | h q => ?_
  apply congrArg Quotient.mk''
  apply Subtype.ext
  refine Prod.ext ?_ rfl
  ext b
  change q.1.1 (Y.Lv.L.cmpF μ₁ μ₂ (Y.Lv.L.bcι (μ₁.comp μ₂) b)) = _
  rw [FiniteLevel.cmpF_bcι]
  rfl

end TempObj

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  [Algebra R' Ω] [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]
  [Algebra R'' Ω] [IsScalarTower K R'' Ω] [IsScalarTower R' R'' Ω] [IsScalarTower R R'' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **`temperedPi1Map` respects composition.** -/
theorem temperedPi1Map_comp (γ : temperedPi1 O R'' A'' V hV) :
    temperedPi1Map (μ₁.comp μ₂) V hV γ = temperedPi1Map μ₁ V hV (temperedPi1Map μ₂ V hV γ) := by
  ext Y y
  rw [temperedPi1Map_app, temperedPi1Map_app, temperedPi1Map_app]
  set z := (TempObj.bcFibreEquiv μ₂ V hV (Y.baseChange μ₁)).symm
    ((TempObj.bcFibreEquiv μ₁ V hV Y).symm y) with hz
  have hy : (TempObj.bcFibreEquiv (μ₁.comp μ₂) V hV Y).symm y =
      TempObj.fibreMap V hV (Y.cmpHom μ₁ μ₂) z := by
    rw [Equiv.symm_apply_eq, TempObj.fibreMap_cmpHom, hz, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  rw [hy, show γ.app _ (TempObj.fibreMap V hV (Y.cmpHom μ₁ μ₂) z) =
    TempObj.fibreMap V hV (Y.cmpHom μ₁ μ₂) (γ.app _ z) from
      FibreAut.app_naturality γ (Y.cmpHom μ₁ μ₂) z, TempObj.fibreMap_cmpHom]

end Comp

end

end TemperedFundamentalGroups
