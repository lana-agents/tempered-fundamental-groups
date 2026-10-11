/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChangeEtale
import TemperedFundamentalGroups.Tempered.FieldChangeOrbifold
import TemperedFundamentalGroups.Andre.GaloisClass

/-!
# Finite étale maps of orbifolds: `temperedPi1Map` is injective (Blueprint §11, F7/F8)

Draft.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

namespace OrbifoldCover

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]

/-- A morphism of levels `X.L ⟶ (B, image of A)` to the level of an equivariant finite étale
algebra gives a morphism of tempered coverings `X ⟶ etaleToTemp B` (to the trivial model and the
one-sheeted covering). -/
def toEt (X : TempObj O R A) (Y : EquivEtale R A) (φ : X.Lv.L ⟶ Y.level) :
    X ⟶ (etaleToTemp O R A).obj Y where
  φ := φ
  ψ := toOneψ X
  ψ_toSpec := toOneψ_toSpec X
  j_ψ := by
    change X.Lv.j ≫ X.Lv.c.toSpec ≫ _ = _ ≫ Spec.map (CommRingCat.ofHom
      (levelStructureMap O R A Y.level)) ≫ inv (ModelCode.trivial O).toSpec
    rw [← Category.assoc, X.Lv.j_toSpec, spec_levelStructureMap O R A φ, Category.assoc]
    rfl
  h x := ⟨(specialFibreMap (toOneψ X) (toOneψ_toSpec X) x.1.1, 0), Set.mem_univ _,
    Nat.zero_lt_one⟩
  continuous_h := by
    apply Continuous.subtype_mk
    refine Continuous.prodMk ?_ continuous_const
    exact (continuous_specialFibreMap _ _).comp X.P.continuous_proj
  fst_h _ := rfl
  h_act g x := by
    apply Subtype.ext
    refine Prod.ext (Subtype.ext ?_) rfl
    change toOneψ X ((X.P.act g x).1.1 : X.Lv.c.scheme) = toOneψ X (x.1.1 : X.Lv.c.scheme)
    rw [X.P.act_fst, Level.ρs_apply, toOneψ_ρ]

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma toEt_fibre (X : TempObj O R A) (Y : EquivEtale R A) (φ : X.Lv.L ⟶ Y.level)
    (q : TempObj.PreFibre Ω V hV X) :
    etaleToTempFibreEquiv O R A V hV Y (TempObj.fibreMap V hV (toEt X Y φ) (Quotient.mk'' q)) =
      q.1.1.comp φ.f := rfl

end OrbifoldCover

namespace EtaleOrbCover

open EtaleOrb OrbifoldCover

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R' : Type u} [CommRing R'] [Algebra K R'] [IsDomain R'] [IsNoetherianRing R']
  {A' : Type u} [Group A'] [MulSemiringAction A' R'] [SMulCommClass A' K R'] [Finite A']

variable (O R' A') in
/-- The induction data of the cover `E' = Ind_{A'} 1` of `[Spec R' / A']`. -/
abbrev D : IndData (cov R' A') (one O R' (⊥ : Subgroup A')) :=
  IndData.pushData (cov R' A') (one O R' (⊥ : Subgroup A'))

variable (O R' A') in
/-- The cover `E' = Ind_{A'} 1` of `[Spec R' / A']` (`Spec R' → [Spec R' / A']`). -/
abbrev E : TempObj O R' A' := P (cov R' A') (one O R' (⊥ : Subgroup A')) good_one

lemma eq_homT (g : (D O R' A').level.H) :
    (g : SemilinearAut R' A' (D O R' A').level.B) =
      (D O R' A').homT ((g : SemilinearAut R' A' (D O R' A').level.B).a, 1) := by
  obtain ⟨⟨s, k⟩, hk⟩ := g.2
  obtain ⟨b, hb⟩ := k.2
  have hk1 : k = 1 := by
    apply Subtype.ext
    rw [← hb, Subsingleton.elim b 1, map_one]
    rfl
  rw [← hk, hk1]
  rfl

variable (O R' A') in
/-- The equivariant finite étale `R'`-algebra underlying `E'` (`Π_{x : A'} R'`, `A'` permuting
the copies). -/
def Eet : EquivEtale R' A' where
  toEtaleCode := (D O R' A').code
  act := (D O R' A').homT.comp (MonoidHom.inl A' _)
  act_a _ := rfl

/-- The level morphism `E' ⟶ E'_et` (the identity on algebras). -/
def φE : (D O R' A').level ⟶ (Eet O R' A').level where
  f := AlgHom.id R' _
  r := { toFun := fun g => ⟨(Eet O R' A').act (g : SemilinearAut R' A' (D O R' A').level.B).a,
           ⟨_, rfl⟩⟩
         map_one' := by
           ext1
           simp only [OneMemClass.coe_one, SemilinearAut.one_a, map_one]
         map_mul' := fun g h => by
           ext1
           simp only [Subgroup.coe_mul, SemilinearAut.mul_a, map_mul] }
  r_a _ := (Eet O R' A').act_a _
  f_σ g y :=
    (congrArg (fun k : SemilinearAut R' A' (D O R' A').level.B => k.σ y) (eq_homT g)).symm

variable (O R' A') in
/-- **The morphism** `E' ⟶ etaleToTemp E'_et`. -/
def m₁ : E O R' A' ⟶ (etaleToTemp O R' A').obj (Eet O R' A') :=
  toEt (E O R' A') (Eet O R' A') φE

section Fibre

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R' Ω] [IsScalarTower K R' Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The fibre map of `E' ⟶ etaleToTemp E'_et` is injective (`E'` is one-sheeted over its
finite étale part). -/
lemma m₁_fibre_injective (y y' : TempObj.Fibre Ω V hV (E O R' A'))
    (h : etaleToTempFibreEquiv O R' A' V hV (Eet O R' A') (TempObj.fibreMap V hV (m₁ O R' A') y) =
      etaleToTempFibreEquiv O R' A' V hV (Eet O R' A') (TempObj.fibreMap V hV (m₁ O R' A') y')) :
    y = y' := by
  induction y using Quotient.inductionOn with
  | h q =>
  induction y' using Quotient.inductionOn with
  | h q' =>
  have h' : q.1.1 = q'.1.1 := h
  congr 1
  refine Subtype.ext (Prod.ext h' ?_)
  refine CoveringCode.pullback_ext (one O R' (⊥ : Subgroup A')).P
    ((D O R' A').foldS (indFaithful good_one)) (Subtype.ext ?_) ?_
  · rw [q.2, q'.2, h']
  · have h1 := (q.1.2).2.2
    have h2 := (q'.1.2).2.2
    simp only [Set.mem_setOf_eq, Nat.lt_one_iff] at h1 h2
    rw [h1, h2]

end Fibre

/-! ### The equivariant algebra `Π_{a : A} R'` over `[Spec R / A]` -/

section Etale

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R] [Finite A]
  [Algebra R R'] [Algebra.Etale R R'] [Module.Finite R R'] (ν : OrbMap R A R' A')

local instance : Fintype A := Fintype.ofFinite A

variable (R' R A) in
/-- The induced algebra `Π_{a : A} R'^{(a)}` of `R'` (an `R`-algebra) along `A`. -/
abbrev YAlg : Type u := IndAlg R' (MonoidHom.id A)

lemma hβY (k : (⊥ : Subgroup (SemilinearAut R A R'))) :
    MonoidHom.id A ((1 : (⊥ : Subgroup (SemilinearAut R A R')) →* A) k) =
      MonoidHom.id A (k : SemilinearAut R A R').a := by
  rw [(Subgroup.mem_bot).1 k.2]
  rfl

variable (R' R A) in
/-- The action of `A` on `Π_{a : A} R'^{(a)}`: `(b • φ) a = φ (b⁻¹ * a)`. -/
def actY : A →* SemilinearAut R A (YAlg R' A) :=
  (indAutHom (A' := A) (μα := MonoidHom.id A) (fun _ _ => rfl) 1 hβY).comp
    (MonoidHom.inl A _)

lemma actY_a (a : A) : (actY R' R A a).a = a := rfl

variable (R' R A) in
/-- **The equivariant finite étale algebra** `Π_{a : A} R'^{(a)}` over `[Spec R / A]`. -/
def Yet : EquivEtale R A := EquivEtale.ofAlgebra (actY R' R A) actY_a

/-- `Yet` is `Π_{a : A} R'^{(a)}`. -/
def eY : (Yet R' R A).B ≃ₐ[R] YAlg R' A := EquivEtale.ofAlgebraEquiv _ _

lemma eY_act (b : A) (y : (Yet R' R A).B) (a : A) :
    (eY (((Yet R' R A).act b).σ y) a : R') = eY y (b⁻¹ * a) := by
  have h := congrFun (EquivEtale.ofAlgebraEquiv_act (actY R' R A) actY_a b y) a
  refine h.trans ?_
  change (eY y (b⁻¹ * a * 1) : R') = _
  rw [mul_one]

variable (O) in
/-- The ring map `Π_{a : A} R'^{(a)} → Π_{x : A'} R'^{(x)}`, `φ ↦ (x ↦ φ (α x))`. -/
def G₀ : YAlg R' A →+* (D O R' A').Alg :=
  RingHom.pi fun x => ((unitE (R := R') (A' := (⊥ : Subgroup A'))).symm.toRingEquiv.toRingHom :
    R' →+* TwAlg (one O R' (⊥ : Subgroup A')).Lv.L.B (MonoidHom.id A' x)).comp
      (Pi.evalRingHom (fun a : A => TwAlg R' (MonoidHom.id A a)) (ν.α x))

lemma G₀_apply (φ : YAlg R' A) (x : A') :
    (G₀ O ν φ x : (one O R' (⊥ : Subgroup A')).Lv.L.B) =
      (unitE (R := R') (A' := (⊥ : Subgroup A'))).symm (φ (ν.α x) : R') := rfl

variable (O) in
/-- The `R`-algebra map `Yet → E'_et`. -/
def G : (Yet R' R A).B →ₐ[R] (Eet O R' A').B where
  toRingHom := ((D O R' A').e.symm.toRingEquiv.toRingHom).comp
    ((G₀ O ν).comp eY.toRingEquiv.toRingHom)
  commutes' r := by
    change (D O R' A').e.symm (G₀ O ν (eY (algebraMap R _ r))) =
      algebraMap R (D O R' A').code.B r
    rw [AlgEquiv.commutes, IsScalarTower.algebraMap_apply R R' (D O R' A').code.B,
      ← (D O R' A').e.symm.commutes]
    congr 1
    funext x
    rw [G₀_apply, indAlg_algebraMap_apply, unitE_symm]
    change _ = algebraMap R' (one O R' (⊥ : Subgroup A')).Lv.L.B
      ((MonoidHom.id A' x)⁻¹ • algebraMap R R' r)
    rw [MonoidHom.id_apply, ← ν.map_smul, map_inv]
    rfl

lemma G_act (a' : A') (y : (Yet R' R A).B) :
    G O ν (((Yet R' R A).act (ν.α a')).σ y) = ((Eet O R' A').act a').σ (G O ν y) := by
  change (D O R' A').e.symm (G₀ O ν (eY (((Yet R' R A).act (ν.α a')).σ y))) =
    ((D O R' A').homT (a', 1)).σ ((D O R' A').e.symm (G₀ O ν (eY y)))
  rw [IndData.homT_σ, AlgEquiv.apply_symm_apply]
  congr 1
  funext x
  change _ = (1 : SemilinearAut R' (⊥ : Subgroup A') (one O R' (⊥ : Subgroup A')).Lv.L.B).σ
    (G₀ O ν (eY y) (a'⁻¹ * x * (D O R' A').β 1))
  rw [map_one, mul_one, G₀_apply, G₀_apply, eY_act, map_mul, map_inv]
  rfl

variable (O) in
/-- The `R'`-algebra map `R' ⊗_R Yet → E'_et`, `r ⊗ φ ↦ r · (x ↦ φ (α x))`. -/
def F : (EquivEtaleBC.bcEt ν (Yet R' R A)).B →ₐ[R'] (Eet O R' A').B :=
  (Algebra.TensorProduct.lift (Algebra.ofId R' _) (G O ν) fun _ _ => Commute.all _ _).comp
    (FiniteLevel.bcE (Yet R' R A).level).toAlgHom

variable (O) in
/-- **The morphism** `E'_et ⟶ bcEt ν Yet` of equivariant finite étale `R'`-algebras. -/
def f : Eet O R' A' ⟶ EquivEtaleBC.bcEt ν (Yet R' R A) where
  f := F O ν
  f_act a' y := by
    change Algebra.TensorProduct.lift (Algebra.ofId R' _) (G O ν) (fun _ _ => Commute.all _ _)
        (FiniteLevel.bcE (Yet R' R A).level ((FiniteLevel.bcE (Yet R' R A).level).symm
          ((FiniteLevel.bcAut ν (Yet R' R A).level (EquivEtaleBC.actHom ν (Yet R' R A) a')).σ
            (FiniteLevel.bcE (Yet R' R A).level y)))) =
      ((Eet O R' A').act a').σ (Algebra.TensorProduct.lift (Algebra.ofId R' _) (G O ν)
        (fun _ _ => Commute.all _ _) (FiniteLevel.bcE (Yet R' R A).level y))
    rw [AlgEquiv.apply_symm_apply]
    generalize FiniteLevel.bcE (Yet R' R A).level y = z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul r y' =>
      rw [FiniteLevel.bcAut_σ_tmul, Algebra.TensorProduct.lift_tmul,
        Algebra.TensorProduct.lift_tmul, map_mul]
      change Algebra.ofId R' _ (a' • r) * G O ν (((Yet R' R A).act (ν.α a')).σ y') = _
      rw [G_act, Algebra.ofId_apply, Algebra.ofId_apply, SemilinearAut.map_algebraMap,
        (Eet O R' A').act_a]
    | add z z' hz hz' =>
      rw [RingEquiv.map_add, _root_.map_add, hz, hz', _root_.map_add, RingEquiv.map_add]

lemma F_tmul (y : (Yet R' R A).B) :
    F O ν ((FiniteLevel.bcE (Yet R' R A).level).symm ((1 : R') ⊗ₜ y)) = G O ν y := by
  change Algebra.TensorProduct.lift (Algebra.ofId R' _) (G O ν) (fun _ _ => Commute.all _ _)
    (FiniteLevel.bcE (Yet R' R A).level ((FiniteLevel.bcE (Yet R' R A).level).symm
      ((1 : R') ⊗ₜ y))) = _
  rw [AlgEquiv.apply_symm_apply, Algebra.TensorProduct.lift_tmul, map_one, one_mul]

lemma ev_G (x : A') (ψ : YAlg R' A) :
    (D O R' A').ev x (G O ν (eY.symm ψ)) =
      (unitE (R := R') (A' := (⊥ : Subgroup A'))).symm (ψ (ν.α x) : R') := by
  change ((D O R' A').e ((D O R' A').e.symm (G₀ O ν (eY (eY.symm ψ)))) x :
    (one O R' (⊥ : Subgroup A')).Lv.L.B) = _
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rfl

section Points

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [Algebra R' Ω]
  [IsScalarTower K R' Ω] [IsScalarTower R R' Ω]

/-- A geometric point of `E'_et = Π_{x : A'} R'^{(x)}` lies on one copy `x`. -/
lemma exists_point_eq (t : (Eet O R' A').B →ₐ[R'] Ω) :
    ∃ x : A', ∀ y, t y = algebraMap R' Ω
      (x • unitE (R := R') (A' := (⊥ : Subgroup A')) ((D O R' A').ev x y)) := by
  obtain ⟨x, t₀, ht⟩ := (D O R' A').exists_comp_ev
    (show (D O R' A').level.B →+* Ω from t.toRingHom)
  refine ⟨x, fun y => ?_⟩
  rw [← onCopy_unit (cov R' A') x t t₀ ht]
  exact RingHom.congr_fun ht y

/-- An element of `ker α` acts on `R'` by an `R`-algebra automorphism. -/
def kerAlgHom (w : A') (hw : ν.α w = 1) : R' →ₐ[R] R' where
  toRingHom := MulSemiringAction.toRingHom A' R' w
  commutes' r := by
    change w • algebraMap R R' r = algebraMap R R' r
    rw [← ν.map_smul, hw, one_smul]

/-- **Rigidity**: an element of `ker α` fixing a geometric point of `Spec R'` acts trivially on
`R'` (`R'` is a domain, finite étale over `R`), hence is trivial if `A'` acts faithfully. -/
lemma eq_one_of_ker [FaithfulSMul A' R'] (w : A') (hw : ν.α w = 1)
    (h : ∀ s : R', algebraMap R' Ω (w • s) = algebraMap R' Ω s) : w = 1 := by
  have hid : kerAlgHom ν w hw = AlgHom.id R R' := by
    refine algHom_eq_of_comp_eq (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) _ _
      (IsScalarTower.toAlgHom R R' Ω) (AlgHom.ext fun s => ?_)
    exact h s
  refine eq_of_smul_eq_smul (α := R') fun s => ?_
  rw [one_smul]
  exact AlgHom.congr_fun hid s

/-- **The geometric points of `E'_et` are separated by `Yet`**: precomposition with
`F : R' ⊗_R Yet → E'_et` is injective on geometric points. -/
lemma comp_F_injective [FaithfulSMul A' R'] (t t' : (Eet O R' A').B →ₐ[R'] Ω)
    (h : t.comp (F O ν) = t'.comp (F O ν)) : t = t' := by
  obtain ⟨x, hx⟩ := exists_point_eq t
  obtain ⟨x', hx'⟩ := exists_point_eq t'
  classical
  have key : ∀ ψ : YAlg R' A, algebraMap R' Ω (x • show R' from ψ (ν.α x)) =
      algebraMap R' Ω (x' • show R' from ψ (ν.α x')) := by
    intro ψ
    have := AlgHom.congr_fun h ((FiniteLevel.bcE (Yet R' R A).level).symm ((1 : R') ⊗ₜ
      eY.symm ψ))
    simp only [AlgHom.comp_apply, F_tmul] at this
    rw [hx, hx', ev_G, ev_G, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply] at this
    exact this
  have hα : ν.α x = ν.α x' := by
    by_contra hne
    have := key (Pi.single (M := fun a : A => TwAlg R' (MonoidHom.id A a)) (ν.α x) 1)
    rw [Pi.single_eq_same, Pi.single_eq_of_ne' hne] at this
    change algebraMap R' Ω (x • (1 : R')) = algebraMap R' Ω (x' • (0 : R')) at this
    rw [smul_one, smul_zero, map_one, map_zero] at this
    exact one_ne_zero this
  have hw : ν.α (x' * x⁻¹) = 1 := by
    rw [map_mul, map_inv, hα, mul_inv_cancel]
  have hxx : x' * x⁻¹ = 1 := eq_one_of_ker ν _ hw fun s => by
    have := key (fun _ => x⁻¹ • s)
    change algebraMap R' Ω (x • x⁻¹ • s) = algebraMap R' Ω (x' • x⁻¹ • s) at this
    rw [smul_inv_smul, ← mul_smul] at this
    exact this.symm
  obtain rfl : x' = x := mul_inv_eq_one.1 hxx
  ext y
  rw [hx, hx']

end Points

end Etale

end EtaleOrbCover

end

end TemperedFundamentalGroups
