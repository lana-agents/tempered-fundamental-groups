/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.Pullback
import TemperedFundamentalGroups.Setup.NoetherLine
import TemperedFundamentalGroups.SemistableReduction.StrongA

/-!
# Semistable refinements of levels (from W10)

Blueprint §10.2, A3. The admissible refinements of Theorem A are the **base changes**
(`LevelHom.IsBaseChange`): `B' ≅ B ⊗_K L` for a finite étale `K`-algebra `L` with a group `Γ` acting
transitively on `Hom_K(L, Ω)`, with group the image of `H × Γ`. From the strong form of W10
(`SemistableReduction.Statement.StrongA`, an explicit hypothesis `hW`):

* `LevelHom.IsBaseChange.isRefinement`, `LevelHom.isBaseChange_id`;
* `exists_core`: the base change along a Galois `K'/K` with a semistable model dominating given
  ones;
* `refinement_input`: every level has a semistable base change;
* `common_input`: two base changes over a morphism of levels have a common semistable base change;
* `andreInput`, `andreEquiv`: Theorem A, `temperedPi1 ≃ₜ* andreGroup`.

Auxiliary: finiteness of the groups `H` of levels (`FiniteLevel.finite_H`, for finite `A`), levels
from uncoded finite étale algebras (`LevelData`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Limits

namespace TemperedFundamentalGroups

noncomputable section


section Finiteness

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- An element of `H⁰` as an `R`-algebra automorphism. -/
def FiniteLevel.H0AlgHom (L : FiniteLevel R A) (g : L.H0) : L.B →ₐ[R] L.B :=
  { ((g : SemilinearAut R A L.B).σ : L.B →+* L.B) with
    commutes' := fun r => SemilinearAut.σ_algebraMap_of_a_eq_one (FiniteLevel.mem_H0.1 g.2) r }

lemma FiniteLevel.H0AlgHom_apply (L : FiniteLevel R A) (g : L.H0) (y : L.B) :
    L.H0AlgHom g y = (g : SemilinearAut R A L.B).σ y := rfl

open Polynomial in
/-- Over a noetherian ring, the kernel `H⁰` of a level is finite: an `R`-automorphism of the finite
étale algebra `B` is determined by the images of the generators modulo the minimal primes (`B` is
unramified and its nilradical is nilpotent), and these are roots of monic polynomials. -/
lemma FiniteLevel.finite_H0 [IsNoetherianRing R] (L : FiniteLevel R A) : Finite L.H0 := by
  classical
  haveI := L.etale
  haveI := L.finite
  let x : Fin L.n → L.B := fun k => Ideal.Quotient.mk L.I (MvPolynomial.X k)
  have hint : ∀ k, IsIntegral R (x k) := fun k => Algebra.IsIntegral.isIntegral _
  choose p hpm hp using hint
  let P := (⊥ : Ideal L.B).minimalPrimes
  haveI : Finite P := (Ideal.finite_minimalPrimes_of_isNoetherianRing L.B ⊥).to_subtype
  haveI (Q : P) : Q.1.IsPrime := Q.2.isPrime
  let T := ∀ k (Q : P), ((p k).aroots (L.B ⧸ Q.1)).toFinset
  let F : L.H0 → T := fun g k Q => ⟨Ideal.Quotient.mk Q.1 (L.H0AlgHom g (x k)), by
    rw [Multiset.mem_toFinset, mem_aroots']
    refine ⟨((hpm k).map _).ne_zero, ?_⟩
    rw [← Ideal.Quotient.mkₐ_eq_mk R, aeval_algHom_apply, aeval_algHom_apply,
      aeval_def, hp k, map_zero, map_zero]⟩
  refine Finite.of_injective F fun g₁ g₂ hF => ?_
  have hN : IsNilpotent (nilradical L.B) := IsNoetherianRing.isNilpotent_nilradical L.B
  have hgen : (Ideal.Quotient.mkₐ R (nilradical L.B)).comp (L.H0AlgHom g₁) =
      (Ideal.Quotient.mkₐ R (nilradical L.B)).comp (L.H0AlgHom g₂) := by
    refine Ideal.Quotient.algHom_ext R (MvPolynomial.algHom_ext fun k => ?_)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [Ideal.Quotient.eq, nilradical, ← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
    intro Q hQ
    have := congr_arg Subtype.val (congr_fun (congr_fun hF k) ⟨Q, hQ⟩)
    exact Ideal.Quotient.eq.1 this
  have hσ := Algebra.FormallyUnramified.lift_unique _ hN _ _ hgen
  apply Subtype.ext
  apply Subtype.ext
  refine SemilinearAut.ext ?_ ?_
  · rw [(FiniteLevel.mem_H0.1 g₁.2), (FiniteLevel.mem_H0.1 g₂.2)]
  · ext y
    exact congr($hσ y)

/-- If `A` is finite and `R` noetherian, the group `H` of a level is finite. -/
lemma FiniteLevel.finite_H [IsNoetherianRing R] [Finite A] (L : FiniteLevel R A) : Finite L.H := by
  haveI := L.finite_H0
  haveI : Finite (L.H ⧸ L.H0) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).symm.toEquiv
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := L.H0)).symm

end Finiteness

section LevelOfAlgebra

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- Transport of semilinear automorphisms along an isomorphism of `R`-algebras. -/
def SemilinearAut.transport {C C' : Type u} [CommRing C] [Algebra R C] [CommRing C']
    [Algebra R C'] (e : C' ≃ₐ[R] C) : SemilinearAut R A C →* SemilinearAut R A C' where
  toFun g := ⟨g.a, (e.toRingEquiv.trans g.σ).trans e.symm.toRingEquiv, fun r => by
    simp [g.map_algebraMap]⟩
  map_one' := SemilinearAut.ext rfl (RingEquiv.ext fun y => by simp)
  map_mul' g h := SemilinearAut.ext rfl (RingEquiv.ext fun y => by simp)

section Transport

variable {C C' : Type u} [CommRing C] [Algebra R C] [CommRing C'] [Algebra R C']
  (e : C' ≃ₐ[R] C)

@[simp] lemma SemilinearAut.transport_a (g : SemilinearAut R A C) :
    (SemilinearAut.transport e g).a = g.a := rfl

@[simp] lemma SemilinearAut.transport_σ (g : SemilinearAut R A C) (y : C') :
    (SemilinearAut.transport e g).σ y = e.symm (g.σ (e y)) := rfl

@[simp] lemma SemilinearAut.transport_σ_symm (g : SemilinearAut R A C) (y : C') :
    (SemilinearAut.transport e g).σ.symm y = e.symm (g.σ.symm (e y)) := rfl

lemma SemilinearAut.transport_injective :
    Function.Injective (SemilinearAut.transport (A := A) e) := by
  intro g h hgh
  refine SemilinearAut.ext congr(($hgh).a) (RingEquiv.ext fun y => ?_)
  have := congr(($hgh).σ (e.symm y))
  simpa using this

end Transport

variable (R) in
lemma exists_presentation (C : Type u) [CommRing C] [Algebra R C] [Algebra.FiniteType R C] :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)), Nonempty (LevelRing R n I ≃ₐ[R] C) := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹_›
  exact ⟨n, RingHom.ker f, ⟨Ideal.quotientKerAlgEquivOfSurjective hf⟩⟩

variable {K : Type u} [Field K] [Algebra K R] (O : ValuationSubring K) (R A) in
/-- **The data of a level with a model on a finite étale `R`-algebra** `C` which is not coded:
a group `Γ` acting on `C` by semilinear automorphisms, surjecting onto `A`, a model `c` with a map
`j : Spec C ⟶ c` over `O` and a compatible action of `Γ` on `c` (trivial on the kernel of the
action on `C`). -/
structure LevelData (C : Type u) [CommRing C] [Algebra R C] (Γ : Type u) [Group Γ] where
  /-- The action of `Γ` on `C`. -/
  Φ : Γ →* SemilinearAut R A C
  surjective : ∀ a : A, ∃ γ, (Φ γ).a = a
  /-- The model. -/
  c : ModelCode O
  /-- The map to the model. -/
  j : Spec (CommRingCat.of C) ⟶ c.scheme
  j_toSpec : j ≫ c.toSpec =
    Spec.map (CommRingCat.ofHom ((algebraMap R C).comp ((algebraMap K R).comp O.subtype)))
  /-- The action on the model. -/
  ρ : Γ →* Aut c.scheme
  ρ_toSpec : ∀ γ, (ρ γ).hom ≫ c.toSpec = c.toSpec
  ρ_ker : ∀ γ, Φ γ = 1 → ρ γ = 1
  ρ_j : ∀ γ, Spec.map (CommRingCat.ofHom ((Φ γ).σ.symm : C →+* C)) ≫ j = j ≫ (ρ γ).hom

namespace LevelData

variable {K : Type u} [Field K] [Algebra K R] {O : ValuationSubring K}
  {C : Type u} [CommRing C] [Algebra R C] [Algebra.Etale R C] [Module.Finite R C]
  {Γ : Type u} [Group Γ] (D : LevelData R A O C Γ)

variable (R C) in
/-- A chosen presentation of a finite étale `R`-algebra. -/
def code : EtaleCode R where
  n := (exists_presentation R C).choose
  I := (exists_presentation R C).choose_spec.choose
  etale := Algebra.Etale.of_equiv (exists_presentation R C).choose_spec.choose_spec.some.symm
  finite := Module.Finite.equiv
    (exists_presentation R C).choose_spec.choose_spec.some.symm.toLinearEquiv

variable (R C) in
/-- The presentation of a finite étale `R`-algebra. -/
def codeEquiv : (code R C).B ≃ₐ[R] C :=
  (exists_presentation R C).choose_spec.choose_spec.some

/-- The action of `Γ` on the coded algebra. -/
def Φc : Γ →* SemilinearAut R A (code R C).B :=
  (SemilinearAut.transport (codeEquiv R C)).comp D.Φ

lemma Φc_eq_one {γ : Γ} : D.Φc γ = 1 ↔ D.Φ γ = 1 := by
  rw [← (SemilinearAut.transport_injective (A := A) (codeEquiv R C)).eq_iff, map_one]
  rfl

/-- The level of the data. -/
def finiteLevel : FiniteLevel R A where
  toEtaleCode := code R C
  H := D.Φc.range
  surjective a := by
    obtain ⟨γ, hγ⟩ := D.surjective a
    exact ⟨D.Φc γ, ⟨γ, rfl⟩, hγ⟩

/-- `Γ` surjects onto the group of the level. -/
def proj : Γ →* D.finiteLevel.H :=
  D.Φc.rangeRestrict

lemma proj_surjective : Function.Surjective D.proj :=
  MonoidHom.rangeRestrict_surjective _

lemma coe_proj (γ : Γ) :
    ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B) =
      SemilinearAut.transport (codeEquiv R C) (D.Φ γ) := rfl

lemma mem_H (x : SemilinearAut R A (code R C).B) :
    x ∈ D.finiteLevel.H ↔ ∃ γ, x = SemilinearAut.transport (codeEquiv R C) (D.Φ γ) :=
  ⟨fun ⟨γ, h⟩ => ⟨γ, h.symm⟩, fun ⟨γ, h⟩ => ⟨γ, h.symm⟩⟩

lemma proj_a (γ : Γ) :
    ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B).a = (D.Φ γ).a := rfl

lemma proj_σ (γ : Γ) (y : (code R C).B) :
    ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B).σ y =
      (codeEquiv R C).symm ((D.Φ γ).σ (codeEquiv R C y)) := rfl

lemma proj_σ_symm (γ : Γ) (y : (code R C).B) :
    ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B).σ.symm y =
      (codeEquiv R C).symm ((D.Φ γ).σ.symm (codeEquiv R C y)) := rfl

/-- A homomorphism out of `Γ` which is trivial on the kernel of the action factors through the
group of the level. -/
def lift {N : Type u} [Group N] (F : Γ →* N) (hF : ∀ γ, D.Φ γ = 1 → F γ = 1) :
    D.finiteLevel.H →* N :=
  (QuotientGroup.lift D.Φc.ker F fun γ hγ => hF γ (D.Φc_eq_one.1 hγ)).comp
    (QuotientGroup.quotientKerEquivRange D.Φc).symm.toMonoidHom

lemma lift_proj {N : Type u} [Group N] (F : Γ →* N) (hF : ∀ γ, D.Φ γ = 1 → F γ = 1) (γ : Γ) :
    D.lift F hF (D.proj γ) = F γ := by
  have : (QuotientGroup.quotientKerEquivRange D.Φc).symm (D.proj γ) =
      (γ : Γ ⧸ D.Φc.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  change QuotientGroup.lift _ F (fun γ hγ => hF γ (D.Φc_eq_one.1 hγ))
    ((QuotientGroup.quotientKerEquivRange D.Φc).symm (D.proj γ)) = F γ
  rw [this]
  rfl

/-- **The level with a model** of the data. -/
def level : Level O R A where
  L := D.finiteLevel
  c := D.c
  j := Spec.map (CommRingCat.ofHom ((codeEquiv R C).symm : C →+* (code R C).B)) ≫ D.j
  j_toSpec := by
    rw [Category.assoc, D.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    exact (codeEquiv R C).symm.commutes _
  ρ := D.lift D.ρ D.ρ_ker
  ρ_toSpec x := by
    obtain ⟨γ, rfl⟩ := D.proj_surjective x
    rw [lift_proj]
    exact D.ρ_toSpec _
  ρ_j x := by
    obtain ⟨γ, rfl⟩ := D.proj_surjective x
    rw [lift_proj, Category.assoc, ← D.ρ_j γ, ← Category.assoc, ← Category.assoc,
      ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext y
    change ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B).σ.symm _ = _
    rw [proj_σ_symm]
    exact congrArg _ (congrArg _ ((codeEquiv R C).apply_symm_apply y))

lemma level_L : D.level.L = D.finiteLevel := rfl

lemma level_c : D.level.c = D.c := rfl

lemma level_j : D.level.j =
    Spec.map (CommRingCat.ofHom ((codeEquiv R C).symm : C →+* (code R C).B)) ≫ D.j := rfl

lemma level_ρ (γ : Γ) : D.level.ρ (D.proj γ) = D.ρ γ :=
  D.lift_proj _ D.ρ_ker γ

end LevelData

end LevelOfAlgebra

section Tensor

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A]
  [MulSemiringAction A R] [SMulCommClass A K R]

omit [SMulCommClass A K R] in
lemma smul_algebraMap_of_smulCommClass [SMulCommClass A K R] (a : A) (k : K) :
    a • algebraMap K R k = algebraMap K R k := by
  rw [Algebra.algebraMap_eq_smul_one, smul_comm, smul_one]

variable {B : Type u} [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]

lemma SemilinearAut.σ_algebraMap_K (g : SemilinearAut R A B) (k : K) :
    g.σ (algebraMap K B k) = algebraMap K B k := by
  rw [IsScalarTower.algebraMap_apply K R B, g.map_algebraMap,
    smul_algebraMap_of_smulCommClass]

variable (K) in
/-- A semilinear automorphism is `K`-linear (`A` acts `K`-linearly). -/
def SemilinearAut.toAlgEquivK (g : SemilinearAut R A B) : B ≃ₐ[K] B :=
  { g.σ with commutes' := SemilinearAut.σ_algebraMap_K g }

@[simp] lemma SemilinearAut.toAlgEquivK_apply (g : SemilinearAut R A B) (b : B) :
    SemilinearAut.toAlgEquivK K g b = g.σ b := rfl

@[simp] lemma SemilinearAut.toAlgEquivK_symm_apply (g : SemilinearAut R A B) (b : B) :
    (SemilinearAut.toAlgEquivK K g).symm b = g.σ.symm b := rfl

/-- The action of a group on `B` through semilinear automorphisms. -/
@[reducible] def actionOf {G : Type u} [Group G] (ν : G →* SemilinearAut R A B) :
    MulSemiringAction G B where
  smul g b := (ν g).σ b
  one_smul b := by
    change (ν 1).σ b = b
    rw [map_one]; rfl
  mul_smul g h b := by
    change (ν (g * h)).σ b = (ν g).σ ((ν h).σ b)
    rw [map_mul]; rfl
  smul_zero g := map_zero (ν g).σ
  smul_add g := map_add (ν g).σ
  smul_one g := map_one (ν g).σ
  smul_mul g := map_mul (ν g).σ

lemma smulCommClass_actionOf {G : Type u} [Group G] (ν : G →* SemilinearAut R A B) :
    letI := actionOf ν
    SMulCommClass G K B := by
  letI := actionOf ν
  refine ⟨fun g k b => ?_⟩
  change (ν g).σ (k • b) = k • (ν g).σ b
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, SemilinearAut.σ_algebraMap_K]

variable (L : Type u) [CommRing L] [Algebra K L]

/-- `(g, τ) ↦ σ_g ⊗ τ` on `B ⊗_K L`. -/
def tensorAut :
    SemilinearAut R A B × (L ≃ₐ[K] L) →* SemilinearAut R A (TensorProduct K B L) where
  toFun x := ⟨x.1.a,
    (Algebra.TensorProduct.congr (SemilinearAut.toAlgEquivK K x.1) x.2).toRingEquiv,
    fun r => by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.algebraMap_apply]
      simp [x.1.map_algebraMap]⟩
  map_one' := by
    refine SemilinearAut.ext rfl (RingEquiv.ext fun y => ?_)
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b k => simp
    | add y z hy hz => simp_all
  map_mul' x y := by
    refine SemilinearAut.ext rfl (RingEquiv.ext fun z => ?_)
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b k => simp
    | add y z hy hz => simp_all

@[simp] lemma tensorAut_a (x : SemilinearAut R A B × (L ≃ₐ[K] L)) :
    (tensorAut L x).a = x.1.a := rfl

@[simp] lemma tensorAut_σ_tmul (x : SemilinearAut R A B × (L ≃ₐ[K] L)) (b : B) (k : L) :
    (tensorAut L x).σ (b ⊗ₜ k) = x.1.σ b ⊗ₜ x.2 k := rfl

@[simp] lemma tensorAut_σ_symm_tmul (x : SemilinearAut R A B × (L ≃ₐ[K] L)) (b : B) (k : L) :
    (tensorAut L x).σ.symm (b ⊗ₜ k) = x.1.σ.symm b ⊗ₜ x.2.symm k := rfl

end Tensor



section Faithful

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A]
  [MulSemiringAction A R] [SMulCommClass A K R]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
  {L : Type u} [CommRing L] [Algebra K L]

lemma tensorAut_eq_one_fst [Nontrivial L] {x : SemilinearAut R A B × (L ≃ₐ[K] L)}
    (h : tensorAut L x = 1) : x.1 = 1 := by
  refine SemilinearAut.ext congr(($h).a) (RingEquiv.ext fun b => ?_)
  have := congr(($h).σ (b ⊗ₜ (1 : L)))
  simp only [tensorAut_σ_tmul, map_one] at this
  exact Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K L).injective this

lemma tensorAut_eq_one_snd [Nontrivial B] {x : SemilinearAut R A B × (L ≃ₐ[K] L)}
    (h : tensorAut L x = 1) : x.2 = 1 := by
  refine AlgEquiv.ext fun k => ?_
  have := congr(($h).σ ((1 : B) ⊗ₜ k))
  simp only [tensorAut_σ_tmul, map_one] at this
  exact Algebra.TensorProduct.includeRight_injective (algebraMap K B).injective this

omit [SMulCommClass A K R] [Algebra R B] [IsScalarTower K R B] in
lemma subsingleton_tensor_left [Subsingleton B] : Subsingleton (TensorProduct K B L) := by
  refine ⟨fun y z => ?_⟩
  rw [← mul_one y, ← mul_one z, Subsingleton.elim (1 : TensorProduct K B L) 0, mul_zero,
    mul_zero]

lemma tensorAut_eq_one_of_subsingleton [Subsingleton B] (x : SemilinearAut R A B × (L ≃ₐ[K] L))
    (hx : x.1.a = 1) : tensorAut L x = 1 := by
  haveI : Subsingleton (TensorProduct K B L) := by
    refine ⟨fun y z => ?_⟩
    rw [← mul_one y, ← mul_one z, Subsingleton.elim (1 : TensorProduct K B L) 0, mul_zero,
      mul_zero]
  exact SemilinearAut.ext hx (RingEquiv.ext fun _ => Subsingleton.elim _ _)

end Faithful

section TensorHom

variable {K : Type u} [Field K] (M N : Type u) [CommRing M] [Algebra K M] [CommRing N]
  [Algebra K N]

/-- `(σ, τ) ↦ σ ⊗ τ`. -/
def tensorAlgEquivHom : (M ≃ₐ[K] M) × (N ≃ₐ[K] N) →* (TensorProduct K M N ≃ₐ[K] TensorProduct K M N)
    where
  toFun x := Algebra.TensorProduct.congr x.1 x.2
  map_one' := by
    refine AlgEquiv.ext fun y => ?_
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul b k => simp
    | add y z hy hz => simp_all
  map_mul' x y := by
    refine AlgEquiv.ext fun z => ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul b k => simp
    | add y z hy hz => simp_all

@[simp] lemma tensorAlgEquivHom_tmul (x : (M ≃ₐ[K] M) × (N ≃ₐ[K] N)) (m : M) (n : N) :
    tensorAlgEquivHom M N x (m ⊗ₜ n) = x.1 m ⊗ₜ x.2 n := rfl

@[simp] lemma tensorAlgEquivHom_symm_tmul (x : (M ≃ₐ[K] M) × (N ≃ₐ[K] N)) (m : M) (n : N) :
    (tensorAlgEquivHom M N x).symm (m ⊗ₜ n) = x.1.symm m ⊗ₜ x.2.symm n := rfl

variable {M N} (Ω : Type u) [Field Ω] [Algebra K Ω]

/-- Transitive actions on the geometric points of two `K`-algebras give a transitive action on
the geometric points of their tensor product. -/
lemma transitive_tensor {Δ₁ Δ₂ : Type u} [Group Δ₁] [Group Δ₂] (θ₁ : Δ₁ →* (M ≃ₐ[K] M))
    (θ₂ : Δ₂ →* (N ≃ₐ[K] N))
    (h₁ : ∀ s₁ s₂ : M →ₐ[K] Ω, ∃ γ, s₂ = s₁.comp (θ₁ γ).toAlgHom)
    (h₂ : ∀ s₁ s₂ : N →ₐ[K] Ω, ∃ γ, s₂ = s₁.comp (θ₂ γ).toAlgHom)
    (s₁ s₂ : TensorProduct K M N →ₐ[K] Ω) :
    ∃ γ, s₂ = s₁.comp ((tensorAlgEquivHom M N).comp (θ₁.prodMap θ₂) γ).toAlgHom := by
  obtain ⟨γ₁, hγ₁⟩ := h₁ (s₁.comp Algebra.TensorProduct.includeLeft)
    (s₂.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨γ₂, hγ₂⟩ := h₂ (s₁.comp Algebra.TensorProduct.includeRight)
    (s₂.comp Algebra.TensorProduct.includeRight)
  refine ⟨(γ₁, γ₂), Algebra.TensorProduct.ext' fun m n => ?_⟩
  have e₁ := congr($hγ₁ m)
  have e₂ := congr($hγ₂ n)
  simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
    Algebra.TensorProduct.includeRight_apply] at e₁ e₂
  simp only [AlgHom.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
    MonoidHom.coe_prodMap, Prod.map]
  rw [← mul_one m, ← one_mul n, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, map_mul]
  simp [e₁, e₂, ← map_mul]

end TensorHom

/-- Two embeddings of a normal extension into a field differ by an automorphism. -/
lemma exists_algEquiv_comp_eq {K K' Ω : Type u} [Field K] [Field K'] [Field Ω] [Algebra K K']
    [Algebra K Ω] [Normal K K'] (s₁ s₂ : K' →ₐ[K] Ω) :
    ∃ τ : K' ≃ₐ[K] K', s₂ = s₁.comp τ.toAlgHom := by
  letI : Algebra K' Ω := s₁.toRingHom.toAlgebra
  haveI : IsScalarTower K K' Ω := IsScalarTower.of_algebraMap_eq fun x => (s₁.commutes x).symm
  refine ⟨Normal.algHomEquivAut K Ω K' s₂,
    ((Normal.algHomEquivAut K Ω K').symm_apply_apply s₂).symm.trans ?_⟩
  ext x
  rfl


section BaseChange

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]

/-- **Base changes**: `ℓ : Lv' ⟶ Lv` is (up to the model) the base change of `Lv` along a finite
étale `K`-algebra `L` with a group `Γ` of automorphisms acting transitively on the geometric points
`Hom_K(L, Ω)` (a nonempty set): `B' ≅ B ⊗_K L`, with `ℓ.φ.f` the inclusion `b ↦ b ⊗ 1`, `H'` the
image of `H × Γ` acting through `σ_h ⊗ θ γ`, `ℓ.φ.r` induced by the projection to `H`, and an
equivariant morphism of models. -/
def LevelHom.IsBaseChange {Lv' Lv : Level O R A} (ℓ : LevelHom O R A Lv' Lv) : Prop :=
  ∃ (L : Type u) (_ : CommRing L) (_ : Algebra K L) (_ : Algebra.Etale K L)
    (_ : Module.Finite K L) (Γ : Type u) (_ : Group Γ) (_ : Finite Γ) (θ : Γ →* (L ≃ₐ[K] L))
    (e : Lv'.L.B ≃ₐ[R] TensorProduct K Lv.L.B L),
    Nonempty (L →ₐ[K] Ω) ∧ (∀ s₁ s₂ : L →ₐ[K] Ω, ∃ γ, s₂ = s₁.comp (θ γ).toAlgHom) ∧
    ℓ.φ.f = e.symm.toAlgHom.comp Algebra.TensorProduct.includeLeft ∧
    (∀ x, x ∈ Lv'.L.H ↔ ∃ (h : Lv.L.H) (γ : Γ),
      x = SemilinearAut.transport e (tensorAut L ((h : SemilinearAut R A Lv.L.B), θ γ))) ∧
    (∀ (h : Lv.L.H) (γ : Γ) (hx : SemilinearAut.transport e
        (tensorAut L ((h : SemilinearAut R A Lv.L.B), θ γ)) ∈ Lv'.L.H),
      ℓ.φ.r ⟨_, hx⟩ = h) ∧
    ℓ.IsEquivariant

variable {Ω}

/-- **Base changes are refinements.** -/
lemma LevelHom.IsBaseChange.isRefinement {Lv' Lv : Level O R A} {ℓ : LevelHom O R A Lv' Lv}
    (hℓ : ℓ.IsBaseChange Ω) : ℓ.IsRefinement Ω := by
  obtain ⟨L, _, _, _, _, Γ, _, _, θ, e, ⟨s₀⟩, htr, hf, hH, hr, heq⟩ := hℓ
  refine ⟨fun h => ?_, fun t₁ t₂ ht => ?_, fun t => ?_, heq⟩
  · have hx := (hH _).2 ⟨h, 1, rfl⟩
    exact ⟨⟨⟨_, hx⟩, FiniteLevel.mem_H0.2 (FiniteLevel.mem_H0.1 h.2)⟩, hr h 1 hx⟩
  · let u₁ := t₁.comp e.symm.toAlgHom
    let u₂ := t₂.comp e.symm.toAlgHom
    obtain ⟨γ, hγ⟩ := htr ((u₁.restrictScalars K).comp Algebra.TensorProduct.includeRight)
      ((u₂.restrictScalars K).comp Algebra.TensorProduct.includeRight)
    have hx := (hH _).2 ⟨1, γ⁻¹, rfl⟩
    refine ⟨⟨⟨_, hx⟩, FiniteLevel.mem_H0.2 rfl⟩, hr 1 γ⁻¹ hx, ?_⟩
    have hb : ∀ b, u₁ (b ⊗ₜ 1) = u₂ (b ⊗ₜ 1) := fun b => by
      have := congr($ht b)
      simpa [hf, u₁, u₂] using this
    have key : ∀ z, u₁ ((tensorAut L (((1 : Lv.L.H) : SemilinearAut R A Lv.L.B),
        θ γ⁻¹)).σ.symm z) = u₂ z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]
      | tmul b l =>
        have hsplit : ∀ (b : Lv.L.B) (l : L), (b ⊗ₜ[K] l : TensorProduct K Lv.L.B L) =
            (b ⊗ₜ[K] 1) * (1 ⊗ₜ[K] l) := fun b l => by simp
        rw [tensorAut_σ_symm_tmul, hsplit, hsplit b l, map_mul, map_mul, hb]
        congr 1
        have := congr($hγ l)
        simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
          Algebra.TensorProduct.includeRight_apply] at this
        rw [this, map_inv]
        rfl
    refine AlgHom.ext fun y => ?_
    have := key (e y)
    simp only [u₁, u₂, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at this
    rw [← this]
    rfl
  · refine ⟨(Algebra.TensorProduct.lift t (s₀.restrictScalars K) fun _ _ => .all _ _).comp
      e.toAlgHom, ?_⟩
    rw [hf]
    ext b
    simp

lemma transport_rid_tensorAut (Lv : Level O R A) (h : SemilinearAut R A Lv.L.B)
    (τ : K ≃ₐ[K] K) :
    SemilinearAut.transport (Algebra.TensorProduct.rid K R Lv.L.B).symm (tensorAut K (h, τ)) =
      h := by
  refine SemilinearAut.ext rfl (RingEquiv.ext fun y => ?_)
  rw [SemilinearAut.transport_σ]
  simp [Subsingleton.elim τ 1]

omit [Algebra R Ω] [IsScalarTower K R Ω] in
variable (Ω) in
/-- **Identities are base changes** (along `L = K`). -/
lemma LevelHom.isBaseChange_id (Lv : Level O R A) : (LevelHom.id Lv).IsBaseChange Ω := by
  refine ⟨K, _, _, inferInstance, inferInstance, PUnit.{u + 1}, inferInstance, inferInstance, 1,
    (Algebra.TensorProduct.rid K R Lv.L.B).symm, ⟨Algebra.ofId K Ω⟩,
    fun s₁ s₂ => ⟨1, Subsingleton.elim _ _⟩, ?_, fun x => ?_, fun h γ hx => ?_, ?_⟩
  · ext b
    simp [LevelHom.id]
  · simp only [transport_rid_tensorAut]
    exact ⟨fun hx => ⟨⟨x, hx⟩, 1, rfl⟩, fun ⟨h, _, hh⟩ => hh ▸ h.2⟩
  · exact Subtype.ext (transport_rid_tensorAut Lv _ _)
  · intro h
    simp [LevelHom.id]

end BaseChange


section BCHom

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {Lv : Level O R A} {L : Type u} [CommRing L] [Algebra K L] [Nontrivial L]
  [Algebra.Etale R (TensorProduct K Lv.L.B L)] [Module.Finite R (TensorProduct K Lv.L.B L)]
  {Δ : Type u} [Group Δ] (θ : Δ →* (L ≃ₐ[K] L))
  (D : LevelData R A O (TensorProduct K Lv.L.B L) (Lv.L.H × Δ))
  (hΦ : ∀ x, D.Φ x = tensorAut L ((x.1 : SemilinearAut R A Lv.L.B), θ x.2))

omit [Algebra.Etale R (TensorProduct K Lv.L.B L)]
  [Module.Finite R (TensorProduct K Lv.L.B L)] in
include hΦ in
lemma bc_ker (x : Lv.L.H × Δ) (hx : D.Φ x = 1) : MonoidHom.fst Lv.L.H Δ x = 1 :=
  Subtype.ext (tensorAut_eq_one_fst ((hΦ x).symm.trans hx))

/-- The inclusion `B → B ⊗_K L`, on coded rings. -/
def bcIncl : Lv.L.B →ₐ[R] D.finiteLevel.B :=
  (LevelData.codeEquiv R (TensorProduct K Lv.L.B L)).symm.toAlgHom.comp
    Algebra.TensorProduct.includeLeft

omit [Nontrivial L] in
include hΦ in
lemma bcIncl_σ (γ : Lv.L.H × Δ) (y : Lv.L.B) :
    bcIncl D ((γ.1 : SemilinearAut R A Lv.L.B).σ y) =
      ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B).σ (bcIncl D y) := by
  rw [LevelData.proj_σ]
  change (LevelData.codeEquiv R _).symm ((γ.1 : SemilinearAut R A Lv.L.B).σ y ⊗ₜ 1) =
    (LevelData.codeEquiv R _).symm ((D.Φ γ).σ ((LevelData.codeEquiv R _)
      ((LevelData.codeEquiv R _).symm (y ⊗ₜ 1))))
  rw [AlgEquiv.apply_symm_apply, hΦ, tensorAut_σ_tmul, map_one]

/-- The base change morphism of levels `D.level ⟶ Lv`. -/
def bcLevelHom : D.finiteLevel ⟶ Lv.L where
  f := bcIncl D
  r := D.lift (MonoidHom.fst Lv.L.H Δ) (bc_ker θ D hΦ)
  r_a := D.proj_surjective.forall.2 fun γ => by
    have h1 := D.lift_proj (MonoidHom.fst Lv.L.H Δ) (bc_ker θ D hΦ) γ
    simp only [h1]
    rw [LevelData.proj_a, hΦ, tensorAut_a]
    rfl
  f_σ := D.proj_surjective.forall.2 fun γ y => by
    have h1 := D.lift_proj (MonoidHom.fst Lv.L.H Δ) (bc_ker θ D hΦ) γ
    simp only [h1]
    exact bcIncl_σ θ D hΦ γ y

/-- The base change morphism `D.level ⟶ Lv` (with a given morphism of models). -/
def bcHom (ψ : D.c.scheme ⟶ Lv.c.scheme) (hψ : ψ ≫ Lv.c.toSpec = D.c.toSpec)
    (hjψ : D.j ≫ ψ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
      Lv.L.B →ₐ[R] TensorProduct K Lv.L.B L).toRingHom) ≫ Lv.j) :
    LevelHom O R A D.level Lv where
  φ := bcLevelHom θ D hΦ
  ψ := ψ
  ψ_toSpec := hψ
  j_ψ := by
    change Spec.map (CommRingCat.ofHom ((LevelData.codeEquiv R (TensorProduct K Lv.L.B L)).symm :
      TensorProduct K Lv.L.B L →+* (LevelData.code R (TensorProduct K Lv.L.B L)).B)) ≫ D.j ≫ ψ =
      Spec.map (CommRingCat.ofHom (bcIncl D).toRingHom) ≫ Lv.j
    rw [hjψ, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

variable (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]

omit [Nontrivial L] [Algebra R Ω] [IsScalarTower K R Ω] in
include hΦ in
lemma isBaseChange_of [Algebra.Etale K L] [Module.Finite K L] [Finite Δ]
    (hne : Nonempty (L →ₐ[K] Ω)) (htr : ∀ s₁ s₂ : L →ₐ[K] Ω, ∃ γ, s₂ = s₁.comp (θ γ).toAlgHom)
    [IsSchemeTheoreticallyDominant D.level.j] (ℓ : LevelHom O R A D.level Lv)
    (hf : ℓ.φ.f = bcIncl D) (hr : ∀ γ, ℓ.φ.r (D.proj γ) = γ.1) : ℓ.IsBaseChange Ω := by
  refine ⟨L, _, _, inferInstance, inferInstance, Δ, inferInstance, inferInstance, θ,
    LevelData.codeEquiv R _, hne, htr, hf, fun x => ?_, fun h γ hx => ?_,
    LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant _⟩
  · refine (D.mem_H x).trans ⟨fun ⟨γ, e⟩ => ⟨γ.1, γ.2, e.trans (by rw [hΦ]; rfl)⟩,
      fun ⟨h, γ, e⟩ => ⟨(h, γ), e.trans (by rw [hΦ]; rfl)⟩⟩
  · have : (⟨_, hx⟩ : D.level.L.H) = D.proj (h, γ) := by
      apply Subtype.ext
      rw [LevelData.coe_proj, hΦ]
      rfl
    exact (congrArg ℓ.φ.r this).trans (hr _)

omit [Algebra R Ω] [IsScalarTower K R Ω] in
lemma isBaseChange_bcHom [Algebra.Etale K L] [Module.Finite K L] [Finite Δ]
    (hne : Nonempty (L →ₐ[K] Ω)) (htr : ∀ s₁ s₂ : L →ₐ[K] Ω, ∃ γ, s₂ = s₁.comp (θ γ).toAlgHom)
    [IsSchemeTheoreticallyDominant D.level.j]
    (ψ : D.c.scheme ⟶ Lv.c.scheme) (hψ : ψ ≫ Lv.c.toSpec = D.c.toSpec)
    (hjψ : D.j ≫ ψ = Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
      Lv.L.B →ₐ[R] TensorProduct K Lv.L.B L).toRingHom) ≫ Lv.j) :
    (bcHom θ D hΦ ψ hψ hjψ).IsBaseChange Ω :=
  isBaseChange_of θ D hΦ Ω hne htr _ rfl fun γ => D.lift_proj _ (bc_ker θ D hΦ) γ

end BCHom

section Common

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {L₁ L₂ : Type u} [CommRing L₁] [Algebra K L₁] [CommRing L₂] [Algebra K L₂]
  {Γ₁ Γ₂ : Type u} [Group Γ₁] [Group Γ₂] (θ₁ : Γ₁ →* (L₁ ≃ₐ[K] L₁)) (θ₂ : Γ₂ →* (L₂ ≃ₐ[K] L₂))
  (K' : Type u) [Field K'] [Algebra K K']

/-- The action of `(Γ₁ × Γ₂) × Gal(K'/K)` on `(L₁ ⊗ L₂) ⊗ K'`. -/
def commonθ : (Γ₁ × Γ₂) × (K' ≃ₐ[K] K') →*
    (TensorProduct K (TensorProduct K L₁ L₂) K' ≃ₐ[K] TensorProduct K (TensorProduct K L₁ L₂) K') :=
  (tensorAlgEquivHom (TensorProduct K L₁ L₂) K').comp
    (((tensorAlgEquivHom L₁ L₂).comp (θ₁.prodMap θ₂)).prodMap (MonoidHom.id _))

lemma commonθ_tmul (x : (Γ₁ × Γ₂) × (K' ≃ₐ[K] K')) (l₁ : L₁) (l₂ : L₂) (k : K') :
    commonθ θ₁ θ₂ K' x ((l₁ ⊗ₜ[K] l₂) ⊗ₜ[K] k) = (θ₁ x.1.1 l₁ ⊗ₜ[K] θ₂ x.1.2 l₂) ⊗ₜ[K] x.2 k :=
  rfl

lemma commonθ_eq_one [Nontrivial L₁] [Nontrivial L₂] {x : (Γ₁ × Γ₂) × (K' ≃ₐ[K] K')}
    (hx : commonθ θ₁ θ₂ K' x = 1) : θ₁ x.1.1 = 1 ∧ θ₂ x.1.2 = 1 := by
  constructor
  · refine AlgEquiv.ext fun l => ?_
    have := congr(($hx) ((l ⊗ₜ[K] (1 : L₂)) ⊗ₜ[K] (1 : K')))
    rw [commonθ_tmul, map_one, map_one] at this
    exact Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K L₂).injective
      (Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K K').injective this)
  · refine AlgEquiv.ext fun l => ?_
    have := congr(($hx) (((1 : L₁) ⊗ₜ[K] l) ⊗ₜ[K] (1 : K')))
    rw [commonθ_tmul, map_one, map_one] at this
    exact Algebra.TensorProduct.includeRight_injective (algebraMap K L₁).injective
      (Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K K').injective this)

end Common

section CommonLevel

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {L₁ L₂ : Type u} [CommRing L₁] [Algebra K L₁] [CommRing L₂] [Algebra K L₂]
  {Γ₁ Γ₂ : Type u} [Group Γ₁] [Group Γ₂] {θ₁ : Γ₁ →* (L₁ ≃ₐ[K] L₁)} {θ₂ : Γ₂ →* (L₂ ≃ₐ[K] L₂)}
  {K' : Type u} [Field K'] [Algebra K K']
  {Lv₁ Lv Lv₂ Lv' : Level O R A} (u : LevelHom O R A Lv Lv')
  {e₁ : Lv₁.L.B ≃ₐ[R] TensorProduct K Lv.L.B L₁} {e₂ : Lv₂.L.B ≃ₐ[R] TensorProduct K Lv'.L.B L₂}
  (hH₁ : ∀ x, x ∈ Lv₁.L.H ↔ ∃ (h : Lv.L.H) (γ : Γ₁),
    x = SemilinearAut.transport e₁ (tensorAut L₁ ((h : SemilinearAut R A Lv.L.B), θ₁ γ)))
  (hH₂ : ∀ x, x ∈ Lv₂.L.H ↔ ∃ (h : Lv'.L.H) (γ : Γ₂),
    x = SemilinearAut.transport e₂ (tensorAut L₂ ((h : SemilinearAut R A Lv'.L.B), θ₂ γ)))
  [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  (D : LevelData R A O (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))
    (Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))))
  (hΦ : ∀ x, D.Φ x = tensorAut (TensorProduct K (TensorProduct K L₁ L₂) K')
    ((x.1 : SemilinearAut R A Lv.L.B), commonθ θ₁ θ₂ K' x.2))

/-- The map of groups to `H₁`. -/
def commonF₁ : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K')) →* Lv₁.L.H :=
  ((SemilinearAut.transport e₁).comp ((tensorAut L₁).comp (Lv.L.H.subtype.prodMap
    (θ₁.comp ((MonoidHom.fst _ _).comp (MonoidHom.fst _ _)))))).codRestrict Lv₁.L.H
    fun x => (hH₁ _).2 ⟨x.1, x.2.1.1, rfl⟩

lemma coe_commonF₁ (x : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))) :
    (commonF₁ hH₁ x : SemilinearAut R A Lv₁.L.B) =
      SemilinearAut.transport e₁ (tensorAut L₁ ((x.1 : SemilinearAut R A Lv.L.B), θ₁ x.2.1.1)) :=
  rfl

omit [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
include hΦ in
lemma commonΦ_eq_one [Nontrivial L₁] [Nontrivial L₂] {x} (hx : D.Φ x = 1) :
    x.1 = 1 ∧ (Nontrivial Lv.L.B → θ₁ x.2.1.1 = 1 ∧ θ₂ x.2.1.2 = 1) := by
  rw [hΦ] at hx
  haveI : Nontrivial (TensorProduct K (TensorProduct K L₁ L₂) K') :=
    Algebra.TensorProduct.includeLeft_injective (S := K) (algebraMap K K').injective
      |>.nontrivial
  exact ⟨Subtype.ext (tensorAut_eq_one_fst hx), fun _ =>
    commonθ_eq_one θ₁ θ₂ K' (tensorAut_eq_one_snd hx)⟩

omit [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
include hΦ in
lemma commonF₁_ker [Nontrivial L₁] [Nontrivial L₂] (x) (hx : D.Φ x = 1) :
    commonF₁ hH₁ x = 1 := by
  obtain ⟨h1, h2⟩ := commonΦ_eq_one D hΦ hx
  apply Subtype.ext
  rw [coe_commonF₁]
  rcases subsingleton_or_nontrivial Lv.L.B with hB | hB
  · rw [tensorAut_eq_one_of_subsingleton _ (by rw [h1]; rfl), map_one]
    rfl
  · rw [h1, (h2 hB).1]
    exact (congrArg _ (map_one (tensorAut (A := A) (B := Lv.L.B) L₁))).trans (map_one _)

variable (Lv L₁ L₂ K') in
/-- `B ⊗ (L₁ ⊗ L₂) → B ⊗ ((L₁ ⊗ L₂) ⊗ K')`. -/
def commonML : TensorProduct K Lv.L.B (TensorProduct K L₁ L₂) →ₐ[R]
    TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K') :=
  Algebra.TensorProduct.map (AlgHom.id R Lv.L.B)
    (Algebra.TensorProduct.includeLeft : TensorProduct K L₁ L₂ →ₐ[K] _)

variable (Lv L₁ L₂) in
/-- `B ⊗ L₁ → B ⊗ (L₁ ⊗ L₂)`. -/
def commonM₁ : TensorProduct K Lv.L.B L₁ →ₐ[R] TensorProduct K Lv.L.B (TensorProduct K L₁ L₂) :=
  Algebra.TensorProduct.map (AlgHom.id R Lv.L.B)
    (Algebra.TensorProduct.includeLeft : L₁ →ₐ[K] TensorProduct K L₁ L₂)

variable (L₁ L₂) in
/-- `B' ⊗ L₂ → B ⊗ (L₁ ⊗ L₂)` along `u`. -/
def commonM₂ : TensorProduct K Lv'.L.B L₂ →ₐ[R] TensorProduct K Lv.L.B (TensorProduct K L₁ L₂) :=
  Algebra.TensorProduct.map u.φ.f
    (Algebra.TensorProduct.includeRight : L₂ →ₐ[K] TensorProduct K L₁ L₂)

omit [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
include hΦ in
lemma commonσ₁ (γ : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))) (z : TensorProduct K Lv.L.B L₁) :
    commonML L₁ L₂ K' Lv (commonM₁ L₁ L₂ Lv
      ((tensorAut L₁ ((γ.1 : SemilinearAut R A Lv.L.B), θ₁ γ.2.1.1)).σ z)) =
      (D.Φ γ).σ (commonML L₁ L₂ K' Lv (commonM₁ L₁ L₂ Lv z)) := by
  rw [hΦ]
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz =>
    rw [RingEquiv.map_add, map_add (commonM₁ L₁ L₂ Lv), map_add (commonML L₁ L₂ K' Lv), hy, hz,
      map_add (commonM₁ L₁ L₂ Lv), map_add (commonML L₁ L₂ K' Lv), RingEquiv.map_add]
  | tmul b l =>
    rw [tensorAut_σ_tmul]
    change (γ.1 : SemilinearAut R A Lv.L.B).σ b ⊗ₜ[K] ((θ₁ γ.2.1.1 l ⊗ₜ[K] (1 : L₂)) ⊗ₜ[K]
      (1 : K')) = (tensorAut _ ((γ.1 : SemilinearAut R A Lv.L.B), commonθ θ₁ θ₂ K' γ.2)).σ
        (b ⊗ₜ[K] ((l ⊗ₜ[K] (1 : L₂)) ⊗ₜ[K] (1 : K')))
    rw [tensorAut_σ_tmul, commonθ_tmul, map_one, map_one]

variable (e₁) in
/-- The ring map `B₁ → B₃`. -/
def commonF₁f : Lv₁.L.B →ₐ[R] D.finiteLevel.B :=
  (LevelData.codeEquiv R _).symm.toAlgHom.comp
    ((commonML L₁ L₂ K' Lv).comp ((commonM₁ L₁ L₂ Lv).comp e₁.toAlgHom))

include hΦ in
lemma commonF₁f_σ (γ : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))) (y : Lv₁.L.B) :
    commonF₁f e₁ D ((commonF₁ hH₁ γ : SemilinearAut R A Lv₁.L.B).σ y) =
      ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B).σ (commonF₁f e₁ D y) := by
  rw [LevelData.proj_σ, coe_commonF₁]
  change (LevelData.codeEquiv R _).symm (commonML L₁ L₂ K' Lv (commonM₁ L₁ L₂ Lv
    (e₁ (e₁.symm ((tensorAut L₁ ((γ.1 : SemilinearAut R A Lv.L.B), θ₁ γ.2.1.1)).σ
      (e₁ y)))))) = (LevelData.codeEquiv R _).symm ((D.Φ γ).σ ((LevelData.codeEquiv R _)
      ((LevelData.codeEquiv R _).symm (commonML L₁ L₂ K' Lv (commonM₁ L₁ L₂ Lv (e₁ y))))))
  rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, commonσ₁ D hΦ]

/-- The morphism of levels `B₃ ⟶ B₁`. -/
def commonφ₁ [Nontrivial L₁] [Nontrivial L₂] : D.finiteLevel ⟶ Lv₁.L where
  f := commonF₁f e₁ D
  r := D.lift (commonF₁ hH₁) (commonF₁_ker hH₁ D hΦ)
  r_a := D.proj_surjective.forall.2 fun γ => by
    have h1 := D.lift_proj (commonF₁ hH₁) (commonF₁_ker hH₁ D hΦ) γ
    simp only [h1]
    rw [coe_commonF₁, LevelData.proj_a, hΦ]
    rfl
  f_σ := D.proj_surjective.forall.2 fun γ y => by
    have h1 := D.lift_proj (commonF₁ hH₁) (commonF₁_ker hH₁ D hΦ) γ
    simp only [h1]
    exact commonF₁f_σ hH₁ D hΦ γ y

lemma commonφ₁_r [Nontrivial L₁] [Nontrivial L₂] (γ) :
    (commonφ₁ hH₁ D hΦ).r (D.proj γ) = commonF₁ hH₁ γ :=
  D.lift_proj _ (commonF₁_ker hH₁ D hΦ) γ

open Classical in
variable (Lv Γ₁ K' θ₂) in
/-- The action on `L₂` used for the map to `H₂` (trivial if `B = 0`). -/
@[irreducible] noncomputable def commonκ₂ : (Γ₁ × Γ₂) × (K' ≃ₐ[K] K') →* (L₂ ≃ₐ[K] L₂) :=
  if Nontrivial Lv.L.B then θ₂.comp ((MonoidHom.snd _ _).comp (MonoidHom.fst _ _)) else 1

omit [SMulCommClass A K R] in
lemma commonκ₂_mem (δ : (Γ₁ × Γ₂) × (K' ≃ₐ[K] K')) : ∃ γ, commonκ₂ Γ₁ θ₂ K' Lv δ = θ₂ γ := by
  unfold commonκ₂
  split_ifs
  · exact ⟨δ.1.2, rfl⟩
  · exact ⟨1, (map_one θ₂).symm⟩

omit [SMulCommClass A K R] in
lemma commonκ₂_of_nontrivial [Nontrivial Lv.L.B] (δ : (Γ₁ × Γ₂) × (K' ≃ₐ[K] K')) :
    commonκ₂ Γ₁ θ₂ K' Lv δ = θ₂ δ.1.2 := by
  unfold commonκ₂
  rw [if_pos ‹_›]
  rfl

omit [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
include hΦ in
lemma commonκ₂_ker [Nontrivial L₁] [Nontrivial L₂] (x) (hx : D.Φ x = 1) :
    commonκ₂ Γ₁ θ₂ K' Lv x.2 = 1 := by
  rcases subsingleton_or_nontrivial Lv.L.B with hB | hB
  · unfold commonκ₂
    rw [if_neg (not_nontrivial_iff_subsingleton.2 hB)]
    rfl
  · rw [commonκ₂_of_nontrivial]
    exact ((commonΦ_eq_one D hΦ hx).2 hB).2

/-- The map of groups to `H₂`. -/
noncomputable def commonF₂ : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K')) →* Lv₂.L.H :=
  ((SemilinearAut.transport e₂).comp ((tensorAut L₂).comp
    ((Lv'.L.H.subtype.comp u.φ.r).prodMap (commonκ₂ Γ₁ θ₂ K' Lv)))).codRestrict Lv₂.L.H
    fun x => by
      obtain ⟨γ, hγ⟩ := commonκ₂_mem (Lv := Lv) (Γ₁ := Γ₁) (K' := K') (θ₂ := θ₂) x.2
      refine (hH₂ _).2 ⟨u.φ.r x.1, γ, ?_⟩
      change SemilinearAut.transport e₂ (tensorAut L₂ (_, commonκ₂ Γ₁ θ₂ K' Lv x.2)) = _
      rw [hγ]
      rfl

lemma coe_commonF₂ (x : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))) :
    (commonF₂ u hH₂ x : SemilinearAut R A Lv₂.L.B) =
      SemilinearAut.transport e₂ (tensorAut L₂ (((u.φ.r x.1 : Lv'.L.H) :
        SemilinearAut R A Lv'.L.B), commonκ₂ Γ₁ θ₂ K' Lv x.2)) :=
  rfl

lemma commonF₂_σ (x : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))) (y : Lv₂.L.B) :
    (commonF₂ u hH₂ x : SemilinearAut R A Lv₂.L.B).σ y =
      e₂.symm ((tensorAut L₂ (((u.φ.r x.1 : Lv'.L.H) : SemilinearAut R A Lv'.L.B),
        commonκ₂ Γ₁ θ₂ K' Lv x.2)).σ (e₂ y)) :=
  rfl

omit [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
include hΦ in
lemma commonF₂_ker [Nontrivial L₁] [Nontrivial L₂] (x) (hx : D.Φ x = 1) :
    commonF₂ u hH₂ x = 1 := by
  apply Subtype.ext
  rw [coe_commonF₂, (commonΦ_eq_one D hΦ hx).1, commonκ₂_ker D hΦ x hx, map_one]
  exact (congrArg _ (map_one (tensorAut (A := A) (B := Lv'.L.B) L₂))).trans (map_one _)

omit [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
include hΦ in
lemma commonσ₂ (γ : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))) (z : TensorProduct K Lv'.L.B L₂) :
    commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u
      ((tensorAut L₂ (((u.φ.r γ.1 : Lv'.L.H) : SemilinearAut R A Lv'.L.B), θ₂ γ.2.1.2)).σ z)) =
      (D.Φ γ).σ (commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u z)) := by
  rw [hΦ]
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add y z hy hz =>
    rw [RingEquiv.map_add, map_add (commonM₂ L₁ L₂ u), map_add (commonML L₁ L₂ K' Lv), hy, hz,
      map_add (commonM₂ L₁ L₂ u), map_add (commonML L₁ L₂ K' Lv), RingEquiv.map_add]
  | tmul b l =>
    rw [tensorAut_σ_tmul]
    change u.φ.f ((u.φ.r γ.1 : SemilinearAut R A Lv'.L.B).σ b) ⊗ₜ[K]
      (((1 : L₁) ⊗ₜ[K] θ₂ γ.2.1.2 l) ⊗ₜ[K] (1 : K')) =
      (tensorAut _ ((γ.1 : SemilinearAut R A Lv.L.B), commonθ θ₁ θ₂ K' γ.2)).σ
        (u.φ.f b ⊗ₜ[K] (((1 : L₁) ⊗ₜ[K] l) ⊗ₜ[K] (1 : K')))
    rw [tensorAut_σ_tmul, commonθ_tmul, map_one, map_one, u.φ.f_σ]

variable (e₂) in
/-- The ring map `B₂ → B₃`. -/
def commonF₂f : Lv₂.L.B →ₐ[R] D.finiteLevel.B :=
  (LevelData.codeEquiv R _).symm.toAlgHom.comp
    ((commonML L₁ L₂ K' Lv).comp ((commonM₂ L₁ L₂ u).comp e₂.toAlgHom))

include hΦ in
lemma commonF₂f_σ (γ : Lv.L.H × ((Γ₁ × Γ₂) × (K' ≃ₐ[K] K'))) (y : Lv₂.L.B) :
    commonF₂f u e₂ D ((commonF₂ u hH₂ γ : SemilinearAut R A Lv₂.L.B).σ y) =
      ((D.proj γ : D.finiteLevel.H) : SemilinearAut R A D.finiteLevel.B).σ
        (commonF₂f u e₂ D y) := by
  rcases subsingleton_or_nontrivial Lv.L.B with hB | hB
  · haveI : Subsingleton (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K')) :=
      subsingleton_tensor_left
    haveI : Subsingleton D.finiteLevel.B := (LevelData.codeEquiv R _).injective.subsingleton
    exact Subsingleton.elim _ _
  have hκ := commonκ₂_of_nontrivial (Lv := Lv) (Γ₁ := Γ₁) (K' := K') (θ₂ := θ₂) γ.2
  let cs := (LevelData.codeEquiv R
    (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))).symm
  let h' : SemilinearAut R A Lv'.L.B := ((u.φ.r γ.1 : Lv'.L.H) : SemilinearAut R A Lv'.L.B)
  calc commonF₂f u e₂ D ((commonF₂ u hH₂ γ : SemilinearAut R A Lv₂.L.B).σ y)
      = cs (commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u
          ((tensorAut L₂ (h', commonκ₂ Γ₁ θ₂ K' Lv γ.2)).σ (e₂ y)))) :=
        congrArg (fun z => cs (commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u z)))
          (e₂.apply_symm_apply _)
    _ = cs (commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u
          ((tensorAut L₂ (h', θ₂ γ.2.1.2)).σ (e₂ y)))) :=
        congrArg (fun κ => cs (commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u
          ((tensorAut L₂ (h', κ)).σ (e₂ y))))) hκ
    _ = cs ((D.Φ γ).σ (commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u (e₂ y)))) :=
        congrArg cs (commonσ₂ u D hΦ γ (e₂ y))
    _ = _ := (congrArg (fun z => cs ((D.Φ γ).σ z))
        ((LevelData.codeEquiv R _).apply_symm_apply _)).symm

/-- The morphism of levels `B₃ ⟶ B₂`. -/
noncomputable def commonφ₂ [Nontrivial L₁] [Nontrivial L₂] : D.finiteLevel ⟶ Lv₂.L where
  f := commonF₂f u e₂ D
  r := D.lift (commonF₂ u hH₂) (commonF₂_ker u hH₂ D hΦ)
  r_a := D.proj_surjective.forall.2 fun γ => by
    have h1 := D.lift_proj (commonF₂ u hH₂) (commonF₂_ker u hH₂ D hΦ) γ
    simp only [h1]
    rw [coe_commonF₂, LevelData.proj_a, hΦ, SemilinearAut.transport_a, tensorAut_a,
      tensorAut_a, u.φ.r_a]
  f_σ := D.proj_surjective.forall.2 fun γ y => by
    have h1 := D.lift_proj (commonF₂ u hH₂) (commonF₂_ker u hH₂ D hΦ) γ
    simp only [h1]
    exact commonF₂f_σ u hH₂ D hΦ γ y

lemma commonφ₂_r [Nontrivial L₁] [Nontrivial L₂] (γ) :
    (commonφ₂ u hH₂ D hΦ).r (D.proj γ) = commonF₂ u hH₂ γ :=
  D.lift_proj _ (commonF₂_ker u hH₂ D hΦ) γ

omit [SMulCommClass A K R]
  [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
lemma commonML_M₁_tmul_one (y : Lv.L.B) :
    commonML L₁ L₂ K' Lv (commonM₁ L₁ L₂ Lv (y ⊗ₜ[K] 1)) = y ⊗ₜ[K] 1 := by
  change y ⊗ₜ[K] (Algebra.TensorProduct.includeLeft (R := K) (S := K)
    (A := TensorProduct K L₁ L₂) (B := K') (Algebra.TensorProduct.includeLeft (R := K) (S := K)
      (A := L₁) (B := L₂) 1)) = _
  rw [map_one, map_one]

omit [SMulCommClass A K R]
  [Algebra.Etale R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))]
  [Module.Finite R (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))] in
lemma commonML_M₂_tmul_one (y : Lv'.L.B) :
    commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u (y ⊗ₜ[K] 1)) = u.φ.f y ⊗ₜ[K] 1 := by
  change u.φ.f y ⊗ₜ[K] (Algebra.TensorProduct.includeLeft (R := K) (S := K)
    (A := TensorProduct K L₁ L₂) (B := K') (Algebra.TensorProduct.includeRight (R := K)
      (A := L₁) (B := L₂) 1)) = _
  rw [map_one, map_one]

omit [SMulCommClass A K R] in
lemma commonJψ (Lv₀ : Level O R A)
    (f : Lv₀.L.B →ₐ[R] TensorProduct K Lv.L.B (TensorProduct K L₁ L₂))
    (ψ : D.c.scheme ⟶ Lv₀.c.scheme)
    (h : D.j ≫ ψ = Spec.map (CommRingCat.ofHom (R := TensorProduct K Lv.L.B
      (TensorProduct K L₁ L₂)) (commonML L₁ L₂ K' Lv).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (R := Lv₀.L.B)
        (S := TensorProduct K Lv.L.B (TensorProduct K L₁ L₂)) f.toRingHom) ≫ Lv₀.j) :
    D.level.j ≫ ψ = Spec.map (CommRingCat.ofHom (((LevelData.codeEquiv R _).symm.toAlgHom.comp
      ((commonML L₁ L₂ K' Lv).comp f)) : Lv₀.L.B →ₐ[R] D.finiteLevel.B).toRingHom) ≫ Lv₀.j := by
  change Spec.map (CommRingCat.ofHom ((LevelData.codeEquiv R
    (TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K'))).symm :
      TensorProduct K Lv.L.B (TensorProduct K (TensorProduct K L₁ L₂) K') →+*
        (LevelData.code R (TensorProduct K Lv.L.B
          (TensorProduct K (TensorProduct K L₁ L₂) K'))).B)) ≫ D.j ≫ ψ = _
  rw [h, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  rfl

end CommonLevel

section Core

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type u} [CommRing R] [Algebra K R]
  [Algebra.Smooth K R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R]

set_option maxHeartbeats 1000000 in
-- the proof unpacks the output of W10 and checks several tensor-product identities
/-- **The core construction from W10**: for a finite étale `R`-algebra `B₀` with a group `G₀` of
semilinear automorphisms, a finite étale `K`-algebra `M` with a group `Δ` of automorphisms and
finitely many models of `Spec (B₀ ⊗_K M)`, W10 gives a finite Galois extension `K'/K` and a level
with a semistable model on `B₀ ⊗_K (M ⊗_K K')` with group the image of `G₀ × Δ × Gal(K'/K)`,
whose model dominates the given ones. -/
theorem exists_core (hW : SemistableReduction.Statement.StrongA.{u})
    [IsDomain R] [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1)
    (B₀ : Type u) [CommRing B₀] [Algebra R B₀] [Algebra K B₀] [IsScalarTower K R B₀]
    [Algebra.Etale R B₀] [Module.Finite R B₀]
    (G₀ : Type u) [Group G₀] [Finite G₀] (ν : G₀ →* SemilinearAut R A B₀)
    (hν : ∀ a, ∃ g, (ν g).a = a)
    (M : Type u) [CommRing M] [Algebra K M] [Algebra.Etale K M] [Module.Finite K M]
    (Δ : Type u) [Group Δ] [Finite Δ] (θ : Δ →* (M ≃ₐ[K] M))
    (ι : Type u) [Finite ι] (c₀ : ι → ModelCode O)
    (j₀ : ∀ i, Spec (CommRingCat.of (TensorProduct K B₀ M)) ⟶ (c₀ i).scheme)
    (hj₀ : ∀ i, j₀ i ≫ (c₀ i).toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap K (TensorProduct K B₀ M)).comp O.subtype))) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (_ : IsGalois K K') (_ : Algebra.Etale K K') (_ : Algebra.Etale K (TensorProduct K M K'))
      (_ : Module.Finite K (TensorProduct K M K'))
      (_ : Algebra.Etale R (TensorProduct K B₀ (TensorProduct K M K')))
      (_ : Module.Finite R (TensorProduct K B₀ (TensorProduct K M K')))
      (D : LevelData R A O (TensorProduct K B₀ (TensorProduct K M K'))
        (G₀ × (Δ × (K' ≃ₐ[K] K'))))
      (dom : ∀ i, D.c.scheme ⟶ (c₀ i).scheme),
      IsSemistableLevel D.level ∧ IsSchemeTheoreticallyDominant D.level.j ∧
      (∀ x, D.Φ x = tensorAut (TensorProduct K M K')
        (ν x.1, tensorAlgEquivHom M K' (θ x.2.1, x.2.2))) ∧
      (∀ i, dom i ≫ (c₀ i).toSpec = D.c.toSpec) ∧
      (∀ i, D.j ≫ dom i = Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.map
        (AlgHom.id R B₀) (Algebra.TensorProduct.includeLeft : M →ₐ[K] TensorProduct K M K') :
          TensorProduct K B₀ M →ₐ[R] TensorProduct K B₀ (TensorProduct K M K')).toRingHom)) ≫
        j₀ i) := by
  let B := TensorProduct K B₀ M
  haveI : Algebra.Etale R B := Algebra.Etale.comp R B₀ B
  haveI : Module.Finite R B := Module.Finite.trans B₀ B
  let ν' : G₀ × Δ →* SemilinearAut R A B := (tensorAut M).comp (ν.prodMap θ)
  letI := actionOf ν'
  haveI := smulCommClass_actionOf (K := K) ν'
  letI : MulSemiringAction (G₀ × Δ) R :=
    MulSemiringAction.compHom R ((SemilinearAut.toA.comp ν).comp (MonoidHom.fst G₀ Δ))
  haveI : SMulCommClass (G₀ × Δ) K R := ⟨fun g k r => smul_comm ((ν g.1).a) k r⟩
  have hequiv : ∀ (g : G₀ × Δ) (r : R), g • algebraMap R B r = algebraMap R B (g • r) := by
    intro g r
    change (ν' g).σ (algebraMap R B r) = algebraMap R B ((ν g.1).a • r)
    rw [(ν' g).map_algebraMap]
    rfl
  obtain ⟨K', _, _, _, _, O', hO', _, ϖ', hϖ', c', c, e, j, act, dom, hss, he, hjd, hjS,
    hact, hactj, hdom, hdomS⟩ :=
      hW K O hp.choose hp.choose_spec.1 hp.choose_spec.2 R hR B (G₀ × Δ) hequiv ι c₀ j₀ hj₀
  haveI hK' : Algebra.Etale K K' :=
    ⟨Algebra.FormallyEtale.of_isSeparable K K',
      Algebra.FinitePresentation.of_finiteType.1 inferInstance⟩
  let L := TensorProduct K M K'
  haveI hL : Algebra.Etale K L := Algebra.Etale.comp K M L
  haveI hLf : Module.Finite K L := Module.Finite.trans M L
  let C := TensorProduct K B₀ L
  haveI hC : Algebra.Etale R C := Algebra.Etale.comp R B₀ C
  haveI hCf : Module.Finite R C := Module.Finite.trans B₀ C
  let Φ : G₀ × (Δ × (K' ≃ₐ[K] K')) →* SemilinearAut R A C :=
    (tensorAut L).comp (ν.prodMap ((tensorAlgEquivHom M K').comp
      (θ.prodMap (MonoidHom.id _))))
  let κ : TensorProduct K K' B ≃ₐ[K] C :=
    (Algebra.TensorProduct.comm K K' B).trans (Algebra.TensorProduct.assoc K K K B₀ M K')
  let ξ : G₀ × (Δ × (K' ≃ₐ[K] K')) ≃* (G₀ × Δ) × (K' ≃ₐ[K] K') := MulEquiv.prodAssoc.symm
  have hring : ∀ γ, (κ : TensorProduct K K' B →+* C).comp (Algebra.TensorProduct.congr
      (ξ γ).2⁻¹ (MulSemiringAction.toAlgAut (G₀ × Δ) K B (ξ γ).1⁻¹)).toRingEquiv.toRingHom =
      ((Φ γ).σ.symm : C →+* C).comp κ := by
    intro γ
    refine RingHom.ext fun y => ?_
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul k x =>
      induction x using TensorProduct.induction_on with
      | zero => simp only [TensorProduct.tmul_zero, map_zero]
      | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, hy, hz]
      | tmul b m =>
        change (Algebra.TensorProduct.assoc K K K B₀ M K')
          (((ν' (γ.1⁻¹, γ.2.1⁻¹)).σ (b ⊗ₜ[K] m)) ⊗ₜ[K] γ.2.2.symm k) =
          (ν γ.1).σ.symm b ⊗ₜ[K] ((θ γ.2.1).symm m ⊗ₜ[K] γ.2.2.symm k)
        simp only [ν', MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_prodMap, Prod.map,
          map_inv]
        rw [tensorAut_σ_tmul M ((ν γ.1)⁻¹, (θ γ.2.1)⁻¹) b m,
          Algebra.TensorProduct.assoc_tmul]
        rfl
  have hj : (Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) ≫ j) ≫ c.toSpec =
      Spec.map (CommRingCat.ofHom ((algebraMap R C).comp ((algebraMap K R).comp O.subtype))) := by
    rw [Category.assoc, hjS, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    change κ (algebraMap K (TensorProduct K K' B) o) = _
    rw [κ.commutes]
    exact IsScalarTower.algebraMap_apply K R C _
  have hρj : ∀ γ, Spec.map (CommRingCat.ofHom ((Φ γ).σ.symm : C →+* C)) ≫
      Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) ≫ j =
      (Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) ≫ j) ≫
        ((act.comp ξ.toMonoidHom) γ).hom := by
    intro γ
    change _ = _ ≫ (act (ξ γ)).hom
    rw [Category.assoc, ← hactj, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hring]
  have hker : ∀ γ, Φ γ = 1 → (act.comp ξ.toMonoidHom) γ = 1 := by
    intro γ hγ
    have hid : (Algebra.TensorProduct.congr (ξ γ).2⁻¹
        (MulSemiringAction.toAlgAut (G₀ × Δ) K B (ξ γ).1⁻¹)).toRingEquiv.toRingHom =
        RingHom.id _ := by
      have := hring γ
      rw [hγ] at this
      refine RingHom.ext fun y => κ.injective ?_
      have := congr($this y)
      simpa using this
    apply Iso.ext
    change (act (ξ γ)).hom = 𝟙 _
    refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated c.toSpec ?_ j ?_
    · rw [hact, Category.id_comp]
    · rw [← hactj, hid, Category.comp_id]
      exact (congrArg (· ≫ j) (Spec.map_id _)).trans (Category.id_comp j)
  have hsurj : ∀ a : A, ∃ γ, (Φ γ).a = a := fun a =>
    let ⟨g, hg⟩ := hν a
    ⟨(g, 1), hg⟩
  let D : LevelData R A O C (G₀ × (Δ × (K' ≃ₐ[K] K'))) :=
    { Φ := Φ, surjective := hsurj, c := c,
      j := Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) ≫ j,
      j_toSpec := hj, ρ := act.comp ξ.toMonoidHom, ρ_toSpec := fun γ => hact _,
      ρ_ker := hker, ρ_j := hρj }
  refine ⟨K', inferInstance, inferInstance, inferInstance, inferInstance, hK', hL, hLf, hC, hCf,
    D, dom, ⟨K', inferInstance, inferInstance, inferInstance, O', hO', inferInstance, ϖ', hϖ', c',
      e, hss, he⟩, ?_, fun x => rfl, hdomS, fun i => ?_⟩
  · haveI : IsIso (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) :=
      κ.toRingEquiv.toCommRingCatIso.isIso_hom
    haveI : IsIso (CommRingCat.ofHom ((LevelData.codeEquiv R C).symm :
        C →+* (LevelData.code R C).B)) :=
      (LevelData.codeEquiv R C).symm.toRingEquiv.toCommRingCatIso.isIso_hom
    have h1 : IsSchemeTheoreticallyDominant
        (Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C))) := inferInstance
    have h2 : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom
        ((LevelData.codeEquiv R C).symm : C →+* (LevelData.code R C).B))) := inferInstance
    have h3 : IsSchemeTheoreticallyDominant
        (Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) ≫ j) := inferInstance
    exact (inferInstance : IsSchemeTheoreticallyDominant (Spec.map (CommRingCat.ofHom
        ((LevelData.codeEquiv R C).symm : C →+* (LevelData.code R C).B)) ≫
      Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) ≫ j))
  · change (Spec.map (CommRingCat.ofHom (κ : TensorProduct K K' B →+* C)) ≫ j) ≫ dom i = _
    rw [Category.assoc, hdom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    refine RingHom.ext fun y => ?_
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul b m => rfl

end Core


section Input

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R] (Ω : Type u) [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]

omit [Algebra R Ω] [IsScalarTower K R Ω] in
/-- `AndreInput.bc_id` for `bc := IsBaseChange`. -/
theorem bc_id_input (Lv : Level O R A) : (LevelHom.id Lv).IsBaseChange Ω :=
  LevelHom.isBaseChange_id Ω Lv

/-- `AndreInput.bc_isRefinement` for `bc := IsBaseChange`. -/
theorem bc_isRefinement_input {Lv' Lv : Level O R A} (ℓ : LevelHom O R A Lv' Lv)
    (h : ℓ.IsBaseChange Ω) : ℓ.IsRefinement Ω :=
  h.isRefinement

end Input

section Main

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] {R : Type u} [CommRing R] [Algebra K R]
  [Algebra.Smooth K R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω] [IsAlgClosed Ω]

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Algebra.Smooth K R]
  [SMulCommClass A K R] [Finite A] [Algebra R Ω] [IsScalarTower K R Ω] in
lemma nonempty_algHom_tensor_of_finiteDimensional (M K' : Type u) [CommRing M] [Algebra K M]
    [Field K'] [Algebra K K'] [FiniteDimensional K K'] (h : Nonempty (M →ₐ[K] Ω)) :
    Nonempty (TensorProduct K M K' →ₐ[K] Ω) :=
  ⟨Algebra.TensorProduct.lift h.some (IsAlgClosed.lift : K' →ₐ[K] Ω) fun _ _ => .all _ _⟩

omit [CharZero K] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [Algebra.Smooth K R]
  [SMulCommClass A K R] [Finite A] [Algebra R Ω] [IsScalarTower K R Ω] [IsAlgClosed Ω] in
lemma transitive_trivial (s₁ s₂ : K →ₐ[K] Ω) :
    ∃ γ : PUnit.{u + 1}, s₂ = s₁.comp ((1 : PUnit.{u + 1} →* (K ≃ₐ[K] K)) γ).toAlgHom :=
  ⟨1, Subsingleton.elim _ _⟩

omit [Algebra R Ω] [IsScalarTower K R Ω] in
variable (Ω) in
/-- **Every level has a semistable base change** (from W10): `AndreInput.refinement` for
`bc := IsBaseChange`. -/
theorem refinement_input (hW : SemistableReduction.Statement.StrongA.{u})
    [IsDomain R] [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1) (Lv : Level O R A) :
    ∃ (Lv₃ : Level O R A) (ℓ : LevelHom O R A Lv₃ Lv),
      IsSemistableLevel Lv₃ ∧ ℓ.IsBaseChange Ω := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  haveI := Lv.L.etale
  haveI := Lv.L.finite
  haveI := Lv.L.finite_H
  have hj₀ : (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft :
      Lv.L.B →ₐ[K] TensorProduct K Lv.L.B K).toRingHom) ≫ Lv.j) ≫ Lv.c.toSpec =
      Spec.map (CommRingCat.ofHom ((algebraMap K (TensorProduct K Lv.L.B K)).comp O.subtype)) := by
    rw [Category.assoc, Lv.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
  obtain ⟨K', _, _, _, _, hK', hL, hLf, hC, hCf, D, dom, hss, hdomj, hΦ, hdomS, hdom⟩ :=
    exists_core hW hp hR Lv.L.B Lv.L.H Lv.L.H.subtype
      (fun a => let ⟨g, hg, h⟩ := Lv.L.surjective a; ⟨⟨g, hg⟩, h⟩) K PUnit.{u + 1} 1
      PUnit.{u + 1} (fun _ => Lv.c) (fun _ => _) (fun _ => hj₀)
  haveI := hdomj
  let θ' : PUnit.{u + 1} × (K' ≃ₐ[K] K') →* (TensorProduct K K K' ≃ₐ[K] TensorProduct K K K') :=
    (tensorAlgEquivHom K K').comp ((1 : PUnit.{u + 1} →* (K ≃ₐ[K] K)).prodMap (MonoidHom.id _))
  have hne := nonempty_algHom_tensor_of_finiteDimensional (Ω := Ω) K K' ⟨Algebra.ofId K Ω⟩
  haveI : Nontrivial (TensorProduct K K K') := hne.some.toRingHom.domain_nontrivial
  have hjψ : D.j ≫ dom PUnit.unit = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft :
        Lv.L.B →ₐ[R] TensorProduct K Lv.L.B (TensorProduct K K K')).toRingHom) ≫ Lv.j := by
    rw [hdom, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  refine ⟨D.level, bcHom θ' D hΦ (dom PUnit.unit) (hdomS _) hjψ, hss,
    isBaseChange_bcHom θ' D hΦ Ω hne (fun s₁ s₂ => ?_) _ _ _⟩
  exact transitive_tensor Ω 1 (MonoidHom.id _) transitive_trivial
    (fun s₁ s₂ => exists_algEquiv_comp_eq s₁ s₂) s₁ s₂

set_option maxHeartbeats 1000000 in
-- the proof assembles the data of two base changes and of W10 in one declaration
omit [Algebra R Ω] [IsScalarTower K R Ω] in
variable (Ω) in
/-- **Two base changes over a morphism of levels have a common semistable base change** (from
W10): `AndreInput.common` for `bc := IsBaseChange`. -/
theorem common_input (hW : SemistableReduction.Statement.StrongA.{u})
    [IsDomain R] [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1)
    {Lv₁ Lv Lv₂ Lv' : Level O R A} (ℓ₁ : LevelHom O R A Lv₁ Lv) (ℓ₂ : LevelHom O R A Lv₂ Lv')
    (u : LevelHom O R A Lv Lv') (h₁ : ℓ₁.IsBaseChange Ω) (h₂ : ℓ₂.IsBaseChange Ω) :
    ∃ (Lv₃ : Level O R A) (μ₁ : LevelHom O R A Lv₃ Lv₁) (μ₂ : LevelHom O R A Lv₃ Lv₂),
      IsSemistableLevel Lv₃ ∧ (μ₁.comp ℓ₁).IsBaseChange Ω ∧ μ₁.IsEquivariant ∧
        μ₂.IsEquivariant ∧ (μ₁.comp ℓ₁).comp u = μ₂.comp ℓ₂ := by
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing K R
  haveI := Lv.L.etale
  haveI := Lv.L.finite
  haveI := Lv.L.finite_H
  obtain ⟨L₁, _, _, _, _, Γ₁, _, _, θ₁, e₁, hne₁, htr₁, hf₁, hH₁, hr₁, -⟩ := h₁
  obtain ⟨L₂, _, _, _, _, Γ₂, _, _, θ₂, e₂, hne₂, htr₂, hf₂, hH₂, hr₂, -⟩ := h₂
  haveI : Nontrivial L₁ := hne₁.some.toRingHom.domain_nontrivial
  haveI : Nontrivial L₂ := hne₂.some.toRingHom.domain_nontrivial
  let M := TensorProduct K L₁ L₂
  haveI : Algebra.Etale K M := Algebra.Etale.comp K L₁ M
  haveI : Module.Finite K M := Module.Finite.trans L₁ M
  let θ : Γ₁ × Γ₂ →* (M ≃ₐ[K] M) := (tensorAlgEquivHom L₁ L₂).comp (θ₁.prodMap θ₂)
  let ρ₁ : Lv₁.L.B →ₐ[R] TensorProduct K Lv.L.B M := (commonM₁ L₁ L₂ Lv).comp e₁.toAlgHom
  let ρ₂ : Lv₂.L.B →ₐ[R] TensorProduct K Lv.L.B M := (commonM₂ L₁ L₂ u).comp e₂.toAlgHom
  have hj : ∀ (Lv₀ : Level O R A) (ρ : Lv₀.L.B →ₐ[R] TensorProduct K Lv.L.B M),
      (Spec.map (CommRingCat.ofHom ρ.toRingHom) ≫ Lv₀.j) ≫ Lv₀.c.toSpec =
      Spec.map (CommRingCat.ofHom ((algebraMap K (TensorProduct K Lv.L.B M)).comp
        O.subtype)) := by
    intro Lv₀ ρ
    rw [Category.assoc, Lv₀.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    change ρ (algebraMap R Lv₀.L.B (algebraMap K R o)) = _
    rw [ρ.commutes]
    exact (IsScalarTower.algebraMap_apply K R (TensorProduct K Lv.L.B M) _).symm
  let c₀ : ULift.{u} Bool → ModelCode O := fun i => match i with
    | ⟨true⟩ => Lv₁.c
    | ⟨false⟩ => Lv₂.c
  let j₀ : ∀ i, Spec (CommRingCat.of (TensorProduct K Lv.L.B M)) ⟶ (c₀ i).scheme :=
    fun i => match i with
    | ⟨true⟩ => Spec.map (CommRingCat.ofHom ρ₁.toRingHom) ≫ Lv₁.j
    | ⟨false⟩ => Spec.map (CommRingCat.ofHom ρ₂.toRingHom) ≫ Lv₂.j
  have hj₀ : ∀ i, j₀ i ≫ (c₀ i).toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap K (TensorProduct K Lv.L.B M)).comp O.subtype)) := fun i => match i with
    | ⟨true⟩ => hj Lv₁ ρ₁
    | ⟨false⟩ => hj Lv₂ ρ₂
  obtain ⟨K', _, _, _, _, hK', hL, hLf, hC, hCf, D, dom, hss, hdomj, hΦ, hdomS, hdom⟩ :=
    exists_core hW hp hR Lv.L.B Lv.L.H Lv.L.H.subtype
      (fun a => let ⟨g, hg, h⟩ := Lv.L.surjective a; ⟨⟨g, hg⟩, h⟩) M (Γ₁ × Γ₂) θ
      (ULift.{u} Bool) c₀ j₀ hj₀
  haveI := hdomj
  have hΦ' : ∀ x, D.Φ x = tensorAut (TensorProduct K M K')
      ((x.1 : SemilinearAut R A Lv.L.B), commonθ θ₁ θ₂ K' x.2) := hΦ
  have hne : Nonempty (TensorProduct K M K' →ₐ[K] Ω) :=
    nonempty_algHom_tensor_of_finiteDimensional M K'
      ⟨Algebra.TensorProduct.lift hne₁.some hne₂.some fun _ _ => .all _ _⟩
  have htr : ∀ s₁ s₂ : TensorProduct K M K' →ₐ[K] Ω,
      ∃ γ, s₂ = s₁.comp (commonθ θ₁ θ₂ K' γ).toAlgHom :=
    transitive_tensor Ω θ (MonoidHom.id _) (transitive_tensor Ω θ₁ θ₂ htr₁ htr₂)
      (fun s₁ s₂ => exists_algEquiv_comp_eq s₁ s₂)
  let μ₁ : LevelHom O R A D.level Lv₁ :=
    { φ := commonφ₁ hH₁ D hΦ'
      ψ := dom ⟨true⟩
      ψ_toSpec := hdomS ⟨true⟩
      j_ψ := commonJψ D Lv₁ ρ₁ (dom ⟨true⟩) (hdom ⟨true⟩) }
  let μ₂ : LevelHom O R A D.level Lv₂ :=
    { φ := commonφ₂ u hH₂ D hΦ'
      ψ := dom ⟨false⟩
      ψ_toSpec := hdomS ⟨false⟩
      j_ψ := commonJψ D Lv₂ ρ₂ (dom ⟨false⟩) (hdom ⟨false⟩) }
  have hf : (μ₁.comp ℓ₁).φ.f = bcIncl D := by
    refine AlgHom.ext fun y => ?_
    change commonF₁f e₁ D (ℓ₁.φ.f y) = _
    rw [hf₁]
    change (LevelData.codeEquiv R _).symm (commonML L₁ L₂ K' Lv (commonM₁ L₁ L₂ Lv
      (e₁ (e₁.symm (y ⊗ₜ[K] 1))))) = (LevelData.codeEquiv R _).symm (y ⊗ₜ[K] 1)
    rw [AlgEquiv.apply_symm_apply, commonML_M₁_tmul_one]
  have hr : ∀ γ, (μ₁.comp ℓ₁).φ.r (D.proj γ) = γ.1 := fun γ => by
    change ℓ₁.φ.r ((commonφ₁ hH₁ D hΦ').r (D.proj γ)) = γ.1
    rw [commonφ₁_r]
    exact hr₁ γ.1 γ.2.1.1 ((hH₁ _).2 ⟨γ.1, γ.2.1.1, rfl⟩)
  have hfu : ((μ₁.comp ℓ₁).comp u).φ.f = (μ₂.comp ℓ₂).φ.f := by
    refine AlgHom.ext fun y => ?_
    change commonF₁f e₁ D (ℓ₁.φ.f (u.φ.f y)) = commonF₂f u e₂ D (ℓ₂.φ.f y)
    rw [hf₁, hf₂]
    change (LevelData.codeEquiv R _).symm (commonML L₁ L₂ K' Lv (commonM₁ L₁ L₂ Lv
      (e₁ (e₁.symm (u.φ.f y ⊗ₜ[K] 1))))) = (LevelData.codeEquiv R _).symm
        (commonML L₁ L₂ K' Lv (commonM₂ L₁ L₂ u (e₂ (e₂.symm (y ⊗ₜ[K] 1)))))
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, commonML_M₁_tmul_one,
      commonML_M₂_tmul_one]
  have hru : ((μ₁.comp ℓ₁).comp u).φ.r = (μ₂.comp ℓ₂).φ.r := by
    refine MonoidHom.ext (D.proj_surjective.forall.2 fun γ => ?_)
    change u.φ.r (ℓ₁.φ.r ((commonφ₁ hH₁ D hΦ').r (D.proj γ))) =
      ℓ₂.φ.r ((commonφ₂ u hH₂ D hΦ').r (D.proj γ))
    have h1 : ℓ₁.φ.r (commonF₁ hH₁ γ) = γ.1 :=
      hr₁ γ.1 γ.2.1.1 ((hH₁ _).2 ⟨γ.1, γ.2.1.1, rfl⟩)
    rw [commonφ₁_r, commonφ₂_r, h1]
    obtain ⟨γ₂, hγ₂⟩ := commonκ₂_mem (Lv := Lv) (Γ₁ := Γ₁) (K' := K') (θ₂ := θ₂) γ.2
    have hx := (hH₂ _).2 ⟨u.φ.r γ.1, γ₂, rfl⟩
    have : commonF₂ u hH₂ γ = ⟨_, hx⟩ := by
      apply Subtype.ext
      rw [coe_commonF₂, hγ₂]
    rw [this]
    exact (hr₂ _ _ hx).symm
  refine ⟨D.level, μ₁, μ₂, hss, isBaseChange_of (commonθ θ₁ θ₂ K') D hΦ' Ω hne htr _ hf hr,
    LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant _,
    LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant _, ?_⟩
  refine LevelHom.ext (FiniteLevel.Hom.ext hfu hru) ?_
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated Lv'.c.toSpec ?_ D.level.j ?_
  · rw [((μ₁.comp ℓ₁).comp u).ψ_toSpec, (μ₂.comp ℓ₂).ψ_toSpec]
  · rw [((μ₁.comp ℓ₁).comp u).j_ψ, (μ₂.comp ℓ₂).j_ψ, hfu]

variable (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The geometric input for Theorem A** from W10, with base changes as admissible refinements. -/
theorem andreInput (hW : SemistableReduction.Statement.StrongA.{u})
    [IsDomain R] [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1) :
    AndreInput O R A Ω V hV (fun ℓ => ℓ.IsBaseChange Ω) where
  bc_id := bc_id_input Ω
  bc_isRefinement := bc_isRefinement_input Ω
  pullback := pullback_input O R A V hV
  refinement := refinement_input Ω hW hp hR
  common := fun ℓ₁ ℓ₂ u h₁ h₂ => common_input Ω hW hp hR ℓ₁ ℓ₂ u h₁ h₂

/-- **Theorem A** (Blueprint §10.1), from W10: the tempered fundamental group is André's group. -/
def andreEquiv (hW : SemistableReduction.Statement.StrongA.{u})
    [IsDomain R] [PerfectField (IsLocalRing.ResidueField O)]
    (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O)
    (hR : ringKrullDim R = 1) :
    temperedPi1 O R A V hV ≃ₜ* andreGroup O R A V hV :=
  andreEquivOfInput (andreInput V hV hW hp hR)

end Main

end

end TemperedFundamentalGroups
