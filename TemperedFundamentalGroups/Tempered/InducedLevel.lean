/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChange
import TemperedFundamentalGroups.Tempered.InducedAlg
import TemperedFundamentalGroups.SemistableReduction.W10Sigma
import TemperedFundamentalGroups.Andre.Pullback

/-!
# Induced tempered coverings (Blueprint §11, F7′)

Let `μ : OrbMap R A R A'` be an orbifold cover `[Spec R / A'] → [Spec R / A]` and `X'` a tempered
covering of `[Spec R / A']` with level `(B', H')`, model `𝒯'` and covering space `P'`. For a finite
group `S` with `α : S ↠ A` and `β : H' →* S` over `μ.α` (**induction data**, `IndData`), the
**induced tempered covering** `X'.ind D` of `[Spec R / A]` has

* the level `(Π x : S, B'^{(α x)}, S × H')` (`IndAlg`, `indAutHom`), `(s, k)` acting by
  `φ ↦ (x ↦ σ_k (φ (s⁻¹ * x * β k)))`, semilinear over `α s`;
* the model `∐_{x : S} 𝒯'` (`SemistableReduction.ModelCode.sigma`), the copy `x` receiving the
  copy `x` of `Spec B'` through `j'`, and `(s, k)` mapping the copy `x` to the copy
  `s * x * (β k)⁻¹` through `ρ' k`;
* the covering space `∐_{x : S} P'`, the pullback of `P'` along the fold map
  `|∐ 𝒯'_s| → |𝒯'_s|`, with `(s, k)` acting through `k`.

For `S = A` this is the push functor of the orbifold cover; for `S = H` (the group of a level
of `[Spec R / A]`) it is the auxiliary object of the counit.

The level group has to act faithfully; this holds when `B'` is nontrivial and only `1 ∈ H'` acts
trivially on `B'` (`IndData.Faithful`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {A' : Type u} [Group A'] [MulSemiringAction A' R] (μ : OrbMap R A R A')

lemma OrbMap.smul_eq (a' : A') (r : R) : μ.α a' • r = a' • r := by
  simpa using μ.map_smul a' r

/-- **Induction data** for a tempered covering `X'` of `[Spec R / A']`: a finite group `S` with
`α : S ↠ A` and `β : H' →* S` over `μ.α`. -/
structure IndData (X' : TempObj O R A') where
  /-- The index group. -/
  S : Type u
  [group : Group S]
  [fintype : Fintype S]
  [decEq : DecidableEq S]
  /-- The map to `A`. -/
  α : S →* A
  α_surj : Function.Surjective α
  /-- The map from the level group. -/
  β : X'.Lv.L.H →* S
  hβ : ∀ k, α (β k) = μ.α (k : SemilinearAut R A' X'.Lv.L.B).a

attribute [instance] IndData.group IndData.fintype IndData.decEq

/-- The faithfulness hypothesis on `X'` making the induced level group act faithfully. -/
structure IndFaithful (X' : TempObj O R A') : Prop where
  nontrivial : Nontrivial X'.Lv.L.B
  faithful : ∀ k : X'.Lv.L.H, (∀ y, (k : SemilinearAut R A' X'.Lv.L.B).σ y = y) → k = 1

namespace IndData

variable {μ} {X' : TempObj O R A'} (D : IndData μ X')

/-- The induced algebra. -/
abbrev Alg : Type u := IndAlg X'.Lv.L.B D.α

instance : Algebra.Etale R D.Alg := by
  haveI := X'.Lv.L.etale
  infer_instance

instance : Module.Finite R D.Alg := by
  haveI := X'.Lv.L.finite
  infer_instance

/-- The group `S × H'`. -/
abbrev T : Type u := D.S × X'.Lv.L.H

/-- The action of `S × H'` on the induced algebra. -/
def autHom : D.T →* SemilinearAut R A D.Alg :=
  indAutHom (OrbMap.smul_eq μ) D.β D.hβ

lemma autHom_injective (hX : IndFaithful X') : Function.Injective D.autHom :=
  haveI := hX.nontrivial
  indAutHom_injective _ _ _ hX.faithful

/-- The coded induced algebra. -/
def code : EtaleCode R := FiniteLevel.codeOf (R' := R) D.Alg

/-- The coded induced algebra is the induced algebra. -/
def e : D.code.B ≃ₐ[R] D.Alg := EquivEtale.presEquiv R D.Alg

/-- The action on the coded induced algebra. -/
def homT : D.T →* SemilinearAut R A D.code.B :=
  (SemilinearAut.congr D.e.symm).comp D.autHom

lemma homT_σ (t : D.T) (y : D.code.B) :
    (D.homT t).σ y = D.e.symm ((D.autHom t).σ (D.e y)) := rfl

lemma homT_a (t : D.T) : (D.homT t).a = D.α t.1 := rfl

lemma homT_injective (hX : IndFaithful X') : Function.Injective D.homT := by
  intro t t' h
  have ha : (D.autHom t).a = (D.autHom t').a := by
    have := congrArg SemilinearAut.a h
    exact this
  refine D.autHom_injective hX (SemilinearAut.ext ha ?_)
  ext φ x
  have := congrArg (fun g : SemilinearAut R A D.code.B => D.e (g.σ (D.e.symm φ))) h
  simp only [homT_σ, AlgEquiv.apply_symm_apply] at this
  exact congrFun this x

/-- **The induced level** `(Π x : S, B'^{(α x)}, S × H')`. -/
def level : FiniteLevel R A where
  toEtaleCode := D.code
  H := D.homT.range
  surjective a := by
    obtain ⟨s, rfl⟩ := D.α_surj a
    exact ⟨D.homT (s, 1), ⟨_, rfl⟩, rfl⟩

/-- `S × H' ≃* H`. -/
def equivT (hX : IndFaithful X') : D.T ≃* D.level.H := MonoidHom.ofInjective (D.homT_injective hX)

lemma equivT_apply (hX : IndFaithful X') (t : D.T) :
    ((D.equivT hX t : D.level.H) : SemilinearAut R A D.level.B) = D.homT t := rfl

lemma homT_equivT_symm (hX : IndFaithful X') (g : D.level.H) :
    D.homT ((D.equivT hX).symm g) = (g : SemilinearAut R A D.level.B) := by
  conv_rhs => rw [← (D.equivT hX).apply_symm_apply g]
  rfl

/-- The coded induced algebra of the level is the induced algebra. -/
def E : D.level.B ≃ₐ[R] D.Alg := D.e

/-- The evaluation of the coded induced algebra at `x`. -/
def ev (x : D.S) : D.level.B →+* X'.Lv.L.B := (indEval x).comp D.E.toRingEquiv.toRingHom

lemma ev_apply (x : D.S) (y : D.level.B) : D.ev x y = (D.E y : D.Alg) x := rfl

lemma ev_equivT (hX : IndFaithful X') (t : D.T) (x : D.S) (y : D.level.B) :
    D.ev x (((D.equivT hX t : D.level.H) : SemilinearAut R A D.level.B).σ y) =
      (t.2 : SemilinearAut R A' X'.Lv.L.B).σ (D.ev (t.1⁻¹ * x * D.β t.2) y) := by
  change ((D.e (D.e.symm ((D.autHom t).σ (D.e y))) : D.Alg) x : X'.Lv.L.B) = _
  rw [AlgEquiv.apply_symm_apply]
  rfl

lemma ev_equivT_symm (hX : IndFaithful X') (t : D.T) (x : D.S) (y : D.level.B) :
    D.ev x (((D.equivT hX t : D.level.H) : SemilinearAut R A D.level.B).σ.symm y) =
      (t.2 : SemilinearAut R A' X'.Lv.L.B).σ.symm (D.ev (t.1 * x * (D.β t.2)⁻¹) y) := by
  have h : ((D.equivT hX t : D.level.H) : SemilinearAut R A D.level.B).σ.symm y =
      ((D.equivT hX t⁻¹ : D.level.H) : SemilinearAut R A D.level.B).σ y := by
    rw [map_inv]
    rfl
  rw [h, ev_equivT]
  simp only [Prod.fst_inv, inv_inv, Prod.snd_inv, map_inv]
  rfl

lemma ev_levelStructureMap (x : D.S) (o : O) :
    D.ev x (levelStructureMap O R A D.level o) = levelStructureMap O R A' X'.Lv.L o := by
  change ((D.E (algebraMap R D.level.B (algebraMap K R o)) : D.Alg) x : X'.Lv.L.B) =
    algebraMap R X'.Lv.L.B (algebraMap K R o)
  rw [AlgEquiv.commutes, indAlg_algebraMap_apply, smul_algebraMap]

/-- The evaluation at `1` is `R`-linear. -/
def ev₁ : D.level.B →ₐ[R] X'.Lv.L.B := (indEval₁ R).comp D.E.toAlgHom

lemma ev₁_apply (y : D.level.B) : D.ev₁ y = D.ev 1 y := rfl

/-! ### The model `∐_{x : S} 𝒯'` -/

/-- The model `∐_{x : S} 𝒯'`. -/
abbrev c : ModelCode O := SemistableReduction.ModelCode.sigma (fun _ : D.S => X'.Lv.c)

/-- The inclusion of the copy `x` of `𝒯'`. -/
abbrev inc (x : D.S) : X'.Lv.c.scheme ⟶ D.c.scheme :=
  SemistableReduction.ModelCode.sigmaι (fun _ : D.S => X'.Lv.c) x

lemma inc_toSpec (x : D.S) : D.inc x ≫ D.c.toSpec = X'.Lv.c.toSpec :=
  SemistableReduction.ModelCode.sigmaι_toSpec _ x

lemma c_hom_ext {Z : Scheme.{u}} {f g : D.c.scheme ⟶ Z} (h : ∀ x, D.inc x ≫ f = D.inc x ≫ g) :
    f = g :=
  SemistableReduction.ModelCode.sigma_hom_ext _ h

/-- The ring map `B' → B'^{(α x)}` (the identity). -/
def twTo (x : D.S) : X'.Lv.L.B →+* TwAlg X'.Lv.L.B (D.α x) := RingHom.id _

/-- The ring map `B'^{(α x)} → B'` (the identity). -/
def twFrom (x : D.S) : TwAlg X'.Lv.L.B (D.α x) →+* X'.Lv.L.B := RingHom.id _

/-- The rings `B'^{(α x)}`. -/
abbrev rings : D.S → CommRingCat.{u} := fun x => CommRingCat.of (TwAlg X'.Lv.L.B (D.α x))

/-- The map `Spec (Π x, B'^{(α x)}) = ∐ Spec B' ⟶ ∐ 𝒯'`. -/
def jAlg : Spec (CommRingCat.of D.Alg) ⟶ D.c.scheme :=
  inv (sigmaSpec D.rings) ≫
    Sigma.desc fun x => Spec.map (CommRingCat.ofHom (D.twTo x)) ≫ X'.Lv.j ≫ D.inc x

lemma specMap_twFrom_twTo (x : D.S) :
    Spec.map (CommRingCat.ofHom (D.twFrom x)) ≫ Spec.map (CommRingCat.ofHom (D.twTo x)) =
      𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact Spec.map_id _

@[reassoc]
lemma specMap_twTo_twFrom (x : D.S) :
    Spec.map (CommRingCat.ofHom (D.twTo x)) ≫ Spec.map (CommRingCat.ofHom (D.twFrom x)) =
      𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact Spec.map_id _

lemma specMap_indEval (x : D.S) :
    Spec.map (CommRingCat.ofHom (indEval x : D.Alg →+* X'.Lv.L.B)) =
      Spec.map (CommRingCat.ofHom (D.twFrom x)) ≫
        Sigma.ι (fun y => Spec (D.rings y)) x ≫ sigmaSpec D.rings := by
  rw [ι_sigmaSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

lemma specMap_indEval_jAlg (x : D.S) :
    Spec.map (CommRingCat.ofHom (indEval x : D.Alg →+* X'.Lv.L.B)) ≫ D.jAlg =
      X'.Lv.j ≫ D.inc x := by
  rw [specMap_indEval, jAlg, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc,
    Sigma.ι_desc, ← Category.assoc, specMap_twFrom_twTo, Category.id_comp]

lemma alg_hom_ext {Z : Scheme.{u}} {f g : Spec (CommRingCat.of D.Alg) ⟶ Z}
    (h : ∀ x, Spec.map (CommRingCat.ofHom (indEval x : D.Alg →+* X'.Lv.L.B)) ≫ f =
      Spec.map (CommRingCat.ofHom (indEval x : D.Alg →+* X'.Lv.L.B)) ≫ g) : f = g := by
  rw [← cancel_epi (sigmaSpec D.rings)]
  refine Sigma.hom_ext _ _ fun x => ?_
  have hx := congrArg (Spec.map (CommRingCat.ofHom (D.twTo x)) ≫ ·) (h x)
  simp only [specMap_indEval, Category.assoc] at hx
  rw [specMap_twTo_twFrom_assoc, specMap_twTo_twFrom_assoc] at hx
  exact hx

/-- The map `j : Spec (coded induced algebra) ⟶ ∐ 𝒯'`. -/
def j : Spec (CommRingCat.of D.level.B) ⟶ D.c.scheme :=
  Spec.map (CommRingCat.ofHom (D.E.symm : D.Alg →+* D.level.B)) ≫ D.jAlg

@[reassoc]
lemma specMap_ev_j (x : D.S) :
    Spec.map (CommRingCat.ofHom (D.ev x)) ≫ D.j = X'.Lv.j ≫ D.inc x := by
  have h : Spec.map (CommRingCat.ofHom (D.ev x)) =
      Spec.map (CommRingCat.ofHom (indEval x : D.Alg →+* X'.Lv.L.B)) ≫
        Spec.map (CommRingCat.ofHom (D.E : D.level.B →+* D.Alg)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have h' : Spec.map (CommRingCat.ofHom (D.E : D.level.B →+* D.Alg)) ≫
      Spec.map (CommRingCat.ofHom (D.E.symm : D.Alg →+* D.level.B)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (D.E : D.level.B →+* D.Alg).comp (D.E.symm : D.Alg →+* D.level.B) = RingHom.id _ from
      RingHom.ext D.E.apply_symm_apply]
    exact Spec.map_id _
  rw [h, j, Category.assoc, reassoc_of% h', specMap_indEval_jAlg]

lemma hom_ext {Z : Scheme.{u}} {f g : Spec (CommRingCat.of D.level.B) ⟶ Z}
    (h : ∀ x, Spec.map (CommRingCat.ofHom (D.ev x)) ≫ f =
      Spec.map (CommRingCat.ofHom (D.ev x)) ≫ g) : f = g := by
  have h₁ : Spec.map (CommRingCat.ofHom (D.E.symm : D.Alg →+* D.level.B)) ≫
      Spec.map (CommRingCat.ofHom (D.E : D.level.B →+* D.Alg)) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show (D.E.symm : D.Alg →+* D.level.B).comp (D.E : D.level.B →+* D.Alg) = RingHom.id _ from
      RingHom.ext D.E.symm_apply_apply]
    exact Spec.map_id _
  have h₂ : Spec.map (CommRingCat.ofHom (D.E : D.level.B →+* D.Alg)) ≫ f =
      Spec.map (CommRingCat.ofHom (D.E : D.level.B →+* D.Alg)) ≫ g := by
    refine D.alg_hom_ext fun x => ?_
    have hx := h x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact hx
  rw [← Category.id_comp f, ← Category.id_comp g, ← h₁, Category.assoc, Category.assoc, h₂]

/-! ### The action on the model -/

/-- The morphism of `∐ 𝒯'` given by `(s, k)`: the copy `x` goes to the copy `s * x * (β k)⁻¹`
through `ρ' k`. -/
def actHom (t : D.T) : D.c.scheme ⟶ D.c.scheme :=
  (SemistableReduction.ModelCode.sigmaIso (fun _ : D.S => X'.Lv.c)).inv ≫
    Sigma.desc fun x => (X'.Lv.ρ t.2).hom ≫ D.inc (t.1 * x * (D.β t.2)⁻¹)

@[reassoc]
lemma inc_actHom (t : D.T) (x : D.S) :
    D.inc x ≫ D.actHom t = (X'.Lv.ρ t.2).hom ≫ D.inc (t.1 * x * (D.β t.2)⁻¹) := by
  simp only [actHom, SemistableReduction.ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ _

lemma actHom_mul (t t' : D.T) : D.actHom t' ≫ D.actHom t = D.actHom (t * t') := by
  refine D.c_hom_ext fun x => ?_
  rw [inc_actHom_assoc, inc_actHom, inc_actHom, ← Category.assoc, Prod.snd_mul, map_mul,
    Aut.Aut_mul_def, Iso.trans_hom]
  congr 2
  simp only [Prod.fst_mul, map_mul, mul_inv_rev]
  group

lemma actHom_one : D.actHom 1 = 𝟙 _ := by
  refine D.c_hom_ext fun x => ?_
  rw [inc_actHom, Category.comp_id, Prod.snd_one, map_one, Prod.fst_one, map_one, inv_one,
    one_mul, mul_one]
  exact Category.id_comp _

/-- **The action of `S × H'` on `∐ 𝒯'`.** -/
def act : D.T →* Aut D.c.scheme :=
  MonoidHom.mk' (fun t =>
    { hom := D.actHom t
      inv := D.actHom t⁻¹
      hom_inv_id := by rw [actHom_mul, inv_mul_cancel, actHom_one]
      inv_hom_id := by rw [actHom_mul, mul_inv_cancel, actHom_one] })
    fun t t' => by
      ext1
      simp only [Aut.Aut_mul_def, Iso.trans_hom]
      exact (D.actHom_mul t t').symm

lemma act_hom (t : D.T) : (D.act t).hom = D.actHom t := rfl

lemma actHom_toSpec (t : D.T) : D.actHom t ≫ D.c.toSpec = D.c.toSpec := by
  refine D.c_hom_ext fun x => ?_
  rw [inc_actHom_assoc, inc_toSpec, inc_toSpec, X'.Lv.ρ_toSpec]

/-- **The induced level with its model** `∐ 𝒯'`. -/
def lv (hX : IndFaithful X') : Level O R A where
  L := D.level
  c := D.c
  j := D.j
  j_toSpec := by
    refine D.hom_ext fun x => ?_
    rw [specMap_ev_j_assoc, inc_toSpec, X'.Lv.j_toSpec, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    exact (D.ev_levelStructureMap x o).symm
  ρ := D.act.comp (D.equivT hX).symm.toMonoidHom
  ρ_toSpec g := D.actHom_toSpec _
  ρ_j g := by
    obtain ⟨t, rfl⟩ := (D.equivT hX).surjective g
    refine D.hom_ext fun x => ?_
    have hring : (D.ev x).comp
        (((D.equivT hX t : D.level.H) : SemilinearAut R A D.level.B).σ.symm :
          D.level.B →+* D.level.B) =
        (((t.2 : SemilinearAut R A' X'.Lv.L.B).σ.symm : X'.Lv.L.B →+* X'.Lv.L.B)).comp
          (D.ev (t.1 * x * (D.β t.2)⁻¹)) := by
      refine RingHom.ext fun y => ?_
      exact D.ev_equivT_symm hX t x y
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, act_hom, specMap_ev_j_assoc,
      inc_actHom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hring,
      CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_ev_j, ← Category.assoc,
      X'.Lv.ρ_j, Category.assoc]

/-! ### The covering space -/

/-- The fold map `∐ 𝒯' ⟶ 𝒯'`. -/
def fold : D.c.scheme ⟶ X'.Lv.c.scheme :=
  (SemistableReduction.ModelCode.sigmaIso (fun _ : D.S => X'.Lv.c)).inv ≫
    Sigma.desc fun _ => 𝟙 _

@[reassoc (attr := simp)]
lemma inc_fold (x : D.S) : D.inc x ≫ D.fold = 𝟙 _ := by
  simp only [fold, SemistableReduction.ModelCode.sigmaι, Category.assoc, Iso.hom_inv_id_assoc]
  exact Sigma.ι_desc _ _

lemma fold_toSpec : D.fold ≫ X'.Lv.c.toSpec = D.c.toSpec :=
  D.c_hom_ext fun x => by rw [inc_fold_assoc, inc_toSpec]

lemma actHom_fold (t : D.T) : D.actHom t ≫ D.fold = D.fold ≫ (X'.Lv.ρ t.2).hom :=
  D.c_hom_ext fun x => by
    rw [inc_actHom_assoc, inc_fold, Category.comp_id, inc_fold_assoc]

/-- The fold map on special fibres. -/
def foldS (hX : IndFaithful X') : (D.lv hX).Z → X'.Lv.Z := specialFibreMap D.fold D.fold_toSpec

lemma coe_foldS (hX : IndFaithful X') (z : (D.lv hX).Z) :
    (D.foldS hX z).1 = D.fold z.1 :=
  coe_specialFibreMap _ _ _

/-- The homomorphism `H ≃ S × H' → H'`. -/
def toH' (hX : IndFaithful X') : D.level.H →* X'.Lv.L.H :=
  (MonoidHom.snd _ _).comp (D.equivT hX).symm.toMonoidHom

lemma foldS_ρs (hX : IndFaithful X') (g : D.level.H) (z : (D.lv hX).Z) :
    D.foldS hX ((D.lv hX).ρs g z) = X'.Lv.ρs (D.toH' hX g) (D.foldS hX z) := by
  apply Subtype.ext
  rw [coe_foldS, Level.ρs_apply, Level.ρs_apply, coe_foldS, ← Scheme.Hom.comp_apply]
  change (D.actHom _ ≫ D.fold) _ = _
  rw [actHom_fold]
  rfl

/-- **The induced tempered covering** of `[Spec R / A]`. -/
def obj (hX : IndFaithful X') : TempObj O R A where
  Lv := D.lv hX
  P := X'.P.pullback (D.toH' hX) (D.foldS_ρs hX) (continuous_specialFibreMap _ _)

end IndData

end

end TemperedFundamentalGroups
