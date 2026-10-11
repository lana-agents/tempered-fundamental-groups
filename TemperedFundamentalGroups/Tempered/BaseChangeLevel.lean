/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Orbifold.EtaleOfAlgebra
import TemperedFundamentalGroups.Tempered.Level

/-!
# Base change of levels along a morphism of orbifold presentations (Blueprint §11, F1)

Let `[Spec R / A]` and `[Spec R' / A']` be affine orbifolds, `R → R'` an injective ring map
(`Algebra R R'`) and `α : A' →* A` a group homomorphism with `α(a') • r ↦ a' • r'`. This is a map
of orbifolds `[Spec R' / A'] → [Spec R / A]`: a finite étale cover (`R'` finite étale over `R`),
an open immersion (`R'` a localization: removing points), or an orbifold cover (`R = R'`,
`A' ≤ A`).

A level `(B, H)` of `[Spec R / A]` pulls back to the level `(R' ⊗_R B, H ×_A A')` of
`[Spec R' / A']`: the pair `(h, a')` with `h.a = α a'` acts by `a' ⊗ σ_h`
(`FiniteLevel.baseChange`). The tensor product is coded through the chosen presentation
(`EquivEtale.presEquiv`); the group `H ×_A A'` embeds since `B → R' ⊗_R B` is injective
(`B` is flat over `R` and `R → R'` is injective).

## Main definitions

* `SemilinearTensor.tensorEquiv`: the ring automorphism `r' ⊗ b ↦ f r' ⊗ g b` of `R' ⊗_R B` for
  ring automorphisms `f`, `g` semilinear over the same automorphism of `R`.
* `FiniteLevel.baseChange`: the base-changed level, with `ι : B → B'` (`FiniteLevel.bcι`) and the
  group isomorphism `bcEquiv : H ×_A A' ≃* H'`.
* `FiniteLevel.bcHom`: base change of morphisms of levels.
-/

universe u

open CategoryTheory Pi1.Orbifold TensorProduct

namespace TemperedFundamentalGroups

noncomputable section

namespace SemilinearTensor

variable {R R' B : Type u} [CommRing R] [CommRing R'] [CommRing B] [Algebra R R'] [Algebra R B]

/-- The bilinear map `(r', b) ↦ f r' ⊗ g b`, semilinear over `τ`. -/
def bil (τ : R →+* R) (f : R' →+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r)) (g : B →+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r)) :
    R' →ₛₗ[τ] B →ₛₗ[τ] R' ⊗[R] B :=
  LinearMap.mk₂'ₛₗ τ τ (fun x y => f x ⊗ₜ g y)
    (fun _ _ _ => by rw [map_add, add_tmul])
    (fun c m n => by
      rw [Algebra.smul_def, map_mul, hf, ← Algebra.smul_def, smul_tmul'])
    (fun _ _ _ => by rw [map_add, tmul_add])
    (fun c m n => by
      rw [Algebra.smul_def, map_mul, hg, ← Algebra.smul_def, tmul_smul])

/-- The ring endomorphism `r' ⊗ b ↦ f r' ⊗ g b` of `R' ⊗_R B`. -/
def tensorHom (τ : R →+* R) (f : R' →+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r)) (g : B →+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r)) :
    R' ⊗[R] B →+* R' ⊗[R] B where
  toFun := TensorProduct.lift (bil τ f hf g hg)
  map_one' := by
    rw [Algebra.TensorProduct.one_def]
    change f 1 ⊗ₜ g 1 = _
    rw [map_one, map_one]
  map_mul' x y := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul c d =>
        rw [Algebra.TensorProduct.tmul_mul_tmul]
        change f (a * c) ⊗ₜ g (b * d) = (f a ⊗ₜ g b) * (f c ⊗ₜ g d)
        rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul]
      | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add, map_add, h₁, h₂, mul_add]
    | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add, map_add, h₁, h₂, add_mul]
  map_zero' := map_zero _
  map_add' := map_add _

@[simp] lemma tensorHom_tmul (τ : R →+* R) (f : R' →+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r)) (g : B →+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r)) (x : R') (y : B) :
    tensorHom τ f hf g hg (x ⊗ₜ y) = f x ⊗ₜ g y := rfl

lemma tensorHom_comp (τ τ' : R →+* R) (f f' : R' →+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r))
    (hf' : ∀ r, f' (algebraMap R R' r) = algebraMap R R' (τ' r)) (g g' : B →+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r))
    (hg' : ∀ r, g' (algebraMap R B r) = algebraMap R B (τ' r)) (z : R' ⊗[R] B) :
    tensorHom τ f hf g hg (tensorHom τ' f' hf' g' hg' z) =
      tensorHom (τ.comp τ') (f.comp f') (fun r => by simp [hf', hf])
        (g.comp g') (fun r => by simp [hg', hg]) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

lemma tensorHom_id (z : R' ⊗[R] B) :
    tensorHom (RingHom.id R) (RingHom.id R') (fun _ => rfl) (RingHom.id B) (fun _ => rfl) z =
      z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, hx, hy]

lemma symm_semilinear {M : Type u} [CommRing M] [Algebra R M] (τ : R ≃+* R) (f : M ≃+* M)
    (hf : ∀ r, f (algebraMap R M r) = algebraMap R M (τ r)) (r : R) :
    f.symm (algebraMap R M r) = algebraMap R M (τ.symm r) := by
  apply f.injective
  rw [RingEquiv.apply_symm_apply, hf, RingEquiv.apply_symm_apply]

lemma tensorHom_symm (τ : R ≃+* R) (f : R' ≃+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r)) (g : B ≃+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r)) (z : R' ⊗[R] B) :
    tensorHom τ.toRingHom f.toRingHom (fun r => hf r) g.toRingHom (fun r => hg r)
      (tensorHom τ.symm.toRingHom f.symm.toRingHom (fun r => symm_semilinear τ f hf r)
        g.symm.toRingHom (fun r => symm_semilinear τ g hg r) z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

/-- The ring automorphism `r' ⊗ b ↦ f r' ⊗ g b` of `R' ⊗_R B`, for ring automorphisms `f`, `g`
semilinear over the ring automorphism `τ` of `R`. -/
def tensorEquiv (τ : R ≃+* R) (f : R' ≃+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r)) (g : B ≃+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r)) :
    R' ⊗[R] B ≃+* R' ⊗[R] B where
  toFun := tensorHom τ.toRingHom f.toRingHom (fun r => hf r) g.toRingHom (fun r => hg r)
  invFun := tensorHom τ.symm.toRingHom f.symm.toRingHom (fun r => symm_semilinear τ f hf r)
    g.symm.toRingHom (fun r => symm_semilinear τ g hg r)
  left_inv z := by
    have := tensorHom_symm τ.symm f.symm (symm_semilinear τ f hf) g.symm
      (symm_semilinear τ g hg) z
    simpa using this
  right_inv z := tensorHom_symm τ f hf g hg z
  map_mul' := map_mul _
  map_add' := map_add _

lemma tensorEquiv_tmul (τ : R ≃+* R) (f : R' ≃+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r)) (g : B ≃+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r)) (x : R') (y : B) :
    tensorEquiv τ f hf g hg (x ⊗ₜ y) = f x ⊗ₜ g y := rfl

lemma tensorEquiv_trans (τ τ' : R ≃+* R) (f f' : R' ≃+* R')
    (hf : ∀ r, f (algebraMap R R' r) = algebraMap R R' (τ r))
    (hf' : ∀ r, f' (algebraMap R R' r) = algebraMap R R' (τ' r)) (g g' : B ≃+* B)
    (hg : ∀ r, g (algebraMap R B r) = algebraMap R B (τ r))
    (hg' : ∀ r, g' (algebraMap R B r) = algebraMap R B (τ' r)) :
    (tensorEquiv τ' f' hf' g' hg').trans (tensorEquiv τ f hf g hg) =
      tensorEquiv (τ'.trans τ) (f'.trans f) (fun r => by simp [hf', hf])
        (g'.trans g) (fun r => by simp [hg', hg]) := by
  ext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add]

end SemilinearTensor

/-- **A map of affine orbifolds** `[Spec R' / A'] → [Spec R / A]`, given by the injective ring
map `R → R'` (`Algebra R R'`) and a group homomorphism `α : A' →* A` for which `R → R'` is
equivariant. -/
structure OrbMap (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]
    (R' : Type u) [CommRing R'] [Algebra R R'] (A' : Type u) [Group A']
    [MulSemiringAction A' R'] where
  /-- The homomorphism of groups. -/
  α : A' →* A
  /-- `R → R'` is equivariant along `α`. -/
  map_smul : ∀ (a' : A') (r : R), algebraMap R R' (α a' • r) = a' • algebraMap R R' r
  /-- `R → R'` is injective. -/
  injective : Function.Injective (algebraMap R R')

namespace FiniteLevel

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]
  {R' : Type u} [CommRing R'] [Algebra R R'] {A' : Type u} [Group A'] [MulSemiringAction A' R']
  (μ : OrbMap R A R' A')

/-- The fibre product `H ×_A A'`. -/
def Hfp (L : FiniteLevel R A) : Subgroup (L.H × A') :=
  MonoidHom.eqLocus (SemilinearAut.toA.comp (L.H.subtype.comp (MonoidHom.fst _ _)))
    (μ.α.comp (MonoidHom.snd _ _))

lemma mem_Hfp {L : FiniteLevel R A} {p : L.H × A'} :
    p ∈ L.Hfp μ ↔ (p.1 : SemilinearAut R A L.B).a = μ.α p.2 := Iff.rfl

/-- The automorphism `a' ⊗ σ_h` of `R' ⊗_R B` for `(h, a') ∈ H ×_A A'`. -/
def bcAut (L : FiniteLevel R A) (p : L.Hfp μ) : SemilinearAut R' A' (R' ⊗[R] L.B) where
  a := p.1.2
  σ := SemilinearTensor.tensorEquiv
    (MulSemiringAction.toRingEquiv A R (p.1.1 : SemilinearAut R A L.B).a)
    (MulSemiringAction.toRingEquiv A' R' p.1.2)
    (fun r => by
      simp only [MulSemiringAction.toRingEquiv_apply_apply]
      rw [(mem_Hfp μ).1 p.2, μ.map_smul])
    (p.1.1 : SemilinearAut R A L.B).σ (p.1.1 : SemilinearAut R A L.B).map_algebraMap
  map_algebraMap r' := by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      SemilinearTensor.tensorEquiv_tmul, map_one, Algebra.TensorProduct.algebraMap_apply,
      Algebra.algebraMap_self, RingHom.id_apply]
    rfl

lemma bcAut_σ_tmul (L : FiniteLevel R A) (p : L.Hfp μ) (x : R') (y : L.B) :
    (bcAut μ L p).σ (x ⊗ₜ y) = (p.1.2 • x) ⊗ₜ (p.1.1 : SemilinearAut R A L.B).σ y := rfl

/-- `(h, a') ↦ a' ⊗ σ_h` is a homomorphism. -/
def bcAutHom (L : FiniteLevel R A) : L.Hfp μ →* SemilinearAut R' A' (R' ⊗[R] L.B) where
  toFun := bcAut μ L
  map_one' := by
    refine SemilinearAut.ext rfl ?_
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [bcAut_σ_tmul]
    | add x y hx hy => rw [RingEquiv.map_add, hx, hy, RingEquiv.map_add]
  map_mul' p q := by
    refine SemilinearAut.ext rfl ?_
    ext z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      simp only [SemilinearAut.mul_σ, RingEquiv.trans_apply, bcAut_σ_tmul]
      simp [mul_smul]
    | add x y hx hy => rw [RingEquiv.map_add, hx, hy, RingEquiv.map_add]

section Code

variable (L : FiniteLevel R A)

instance : Algebra.Etale R' (R' ⊗[R] L.B) := by
  haveI := L.etale
  infer_instance

instance : Module.Finite R' (R' ⊗[R] L.B) := by
  haveI := L.finite
  infer_instance

/-- The code of a finite étale `R'`-algebra, through the chosen presentation. -/
def codeOf (C : Type u) [CommRing C] [Algebra R' C] [Algebra.Etale R' C] [Module.Finite R' C] :
    EtaleCode R' where
  n := EquivEtale.presN R' C
  I := RingHom.ker (EquivEtale.presHom R' C)
  etale := Algebra.Etale.of_equiv (EquivEtale.presEquiv R' C).symm
  finite := Module.Finite.equiv (EquivEtale.presEquiv R' C).symm.toLinearEquiv

/-- The coded base change `R' ⊗_R B`. -/
def bcCode : EtaleCode R' := codeOf (R' ⊗[R] L.B)

/-- The coded base change is `R' ⊗_R B`. -/
def bcE : (bcCode (R' := R') L).B ≃ₐ[R'] R' ⊗[R] L.B :=
  EquivEtale.presEquiv R' (R' ⊗[R] L.B)

end Code

/-- The action of `H ×_A A'` on the coded base change. -/
def bcHomH (L : FiniteLevel R A) : L.Hfp μ →* SemilinearAut R' A' (bcCode (R' := R') L).B :=
  (SemilinearAut.congr (bcE L).symm).comp (bcAutHom μ L)

lemma bcHomH_σ (L : FiniteLevel R A) (p : L.Hfp μ) (x : (bcCode (R' := R') L).B) :
    (bcHomH μ L p).σ x = (bcE L).symm ((bcAut μ L p).σ (bcE L x)) := rfl

lemma bcHomH_a (L : FiniteLevel R A) (p : L.Hfp μ) : (bcHomH μ L p).a = p.1.2 := rfl

/-- **The base-changed level** `(R' ⊗_R B, H ×_A A')` of `[Spec R' / A']`. -/
def baseChange (L : FiniteLevel R A) : FiniteLevel R' A' where
  toEtaleCode := bcCode L
  H := (bcHomH μ L).range
  surjective a' := by
    obtain ⟨h, hh, ha⟩ := L.surjective (μ.α a')
    exact ⟨bcHomH μ L ⟨(⟨h, hh⟩, a'), ha⟩, ⟨_, rfl⟩, rfl⟩

/-- The base-changed level is `R' ⊗_R B`. -/
def bcE' (L : FiniteLevel R A) : (L.baseChange μ).B ≃ₐ[R'] R' ⊗[R] L.B := bcE L

/-- The ring map `B → R' ⊗_R B`. -/
def bcι (L : FiniteLevel R A) : L.B →+* (L.baseChange μ).B :=
  (L.bcE' μ).symm.toRingEquiv.toRingHom.comp
    (Algebra.TensorProduct.includeRight : L.B →ₐ[R] R' ⊗[R] L.B).toRingHom

lemma bcE_bcι (L : FiniteLevel R A) (y : L.B) :
    L.bcE' μ (L.bcι μ y) = (1 : R') ⊗ₜ y :=
  (L.bcE' μ).apply_symm_apply _

lemma bcι_injective (L : FiniteLevel R A) : Function.Injective (L.bcι μ) := by
  haveI := L.etale
  exact (L.bcE' μ).symm.injective.comp
    (Algebra.TensorProduct.includeRight_injective (A := R') μ.injective)

lemma bcι_algebraMap (L : FiniteLevel R A) (r : R) :
    L.bcι μ (algebraMap R L.B r) = algebraMap R' (L.baseChange μ).B (algebraMap R R' r) := by
  apply (L.bcE' μ).injective
  rw [bcE_bcι, AlgEquiv.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := L.B), TensorProduct.tmul_smul,
    Algebra.algebraMap_eq_smul_one (A := R'), TensorProduct.smul_tmul']

lemma bcHomH_injective (L : FiniteLevel R A) : Function.Injective (bcHomH μ L) := by
  intro p q hpq
  have ha : p.1.2 = q.1.2 := congrArg SemilinearAut.a hpq
  have hσ : ∀ y, (p.1.1 : SemilinearAut R A L.B).σ y = (q.1.1 : SemilinearAut R A L.B).σ y := by
    intro y
    have h1 := congrArg (fun g => (bcE L) ((g : SemilinearAut R' A' _).σ ((bcE L).symm
      ((1 : R') ⊗ₜ y)))) hpq
    simp only [bcHomH_σ, AlgEquiv.apply_symm_apply, bcAut_σ_tmul, smul_one] at h1
    haveI := L.etale
    exact Algebra.TensorProduct.includeRight_injective (A := R') μ.injective h1
  refine Subtype.ext (Prod.ext (Subtype.ext (SemilinearAut.ext ?_ (RingEquiv.ext hσ))) ha)
  rw [(mem_Hfp μ).1 p.2, (mem_Hfp μ).1 q.2, ha]

/-- `H ×_A A' ≃* H'`. -/
def bcEquiv (L : FiniteLevel R A) : L.Hfp μ ≃* (L.baseChange μ).H :=
  MonoidHom.ofInjective (bcHomH_injective μ L)

lemma bcEquiv_a (L : FiniteLevel R A) (p : L.Hfp μ) :
    ((L.bcEquiv μ p : (L.baseChange μ).H) : SemilinearAut R' A' (L.baseChange μ).B).a = p.1.2 :=
  rfl

lemma bcEquiv_σ (L : FiniteLevel R A) (p : L.Hfp μ) (x : (L.baseChange μ).B) :
    ((L.bcEquiv μ p : (L.baseChange μ).H) : SemilinearAut R' A' (L.baseChange μ).B).σ x =
      (L.bcE' μ).symm ((bcAut μ L p).σ (L.bcE' μ x)) := rfl

lemma bcEquiv_σ_bcι (L : FiniteLevel R A) (p : L.Hfp μ) (y : L.B) :
    ((L.bcEquiv μ p : (L.baseChange μ).H) : SemilinearAut R' A' (L.baseChange μ).B).σ
      (L.bcι μ y) = L.bcι μ ((p.1.1 : SemilinearAut R A L.B).σ y) := by
  rw [bcEquiv_σ, bcE_bcι, bcAut_σ_tmul, smul_one]
  rfl

/-- The projection `H' ≅ H ×_A A' → H`. -/
def bcPr (L : FiniteLevel R A) : (L.baseChange μ).H →* L.H :=
  ((MonoidHom.fst _ _).comp (L.Hfp μ).subtype).comp (L.bcEquiv μ).symm.toMonoidHom

lemma bcPr_bcEquiv (L : FiniteLevel R A) (p : L.Hfp μ) : L.bcPr μ (L.bcEquiv μ p) = p.1.1 := by
  simp [bcPr]

lemma bcEquiv_symm_snd (L : FiniteLevel R A) (g : (L.baseChange μ).H) :
    ((L.bcEquiv μ).symm g).1.2 = (g : SemilinearAut R' A' (L.baseChange μ).B).a := by
  conv_rhs => rw [← (L.bcEquiv μ).apply_symm_apply g]
  rfl

lemma bcPr_a (L : FiniteLevel R A) (g : (L.baseChange μ).H) :
    (L.bcPr μ g : SemilinearAut R A L.B).a = μ.α (g : SemilinearAut R' A' (L.baseChange μ).B).a :=
  by
  rw [← bcEquiv_symm_snd]
  exact ((L.bcEquiv μ).symm g).2

lemma bcσ_bcι (L : FiniteLevel R A) (g : (L.baseChange μ).H) (y : L.B) :
    (g : SemilinearAut R' A' (L.baseChange μ).B).σ (L.bcι μ y) =
      L.bcι μ ((L.bcPr μ g : SemilinearAut R A L.B).σ y) := by
  conv_lhs => rw [← (L.bcEquiv μ).apply_symm_apply g]
  rw [bcEquiv_σ_bcι]
  rfl

lemma bcPr_mem_H0 (L : FiniteLevel R A) {g : (L.baseChange μ).H} (hg : g ∈ (L.baseChange μ).H0) :
    L.bcPr μ g ∈ L.H0 := by
  rw [mem_H0, bcPr_a, (mem_H0.1 hg), map_one]

/-- The element `(h, 1)` of `H'⁰` for `h ∈ H⁰`. -/
def bcH0 (L : FiniteLevel R A) (h : L.H0) : (L.baseChange μ).H0 :=
  ⟨L.bcEquiv μ ⟨((h : L.H), 1), by rw [mem_Hfp, map_one]; exact mem_H0.1 h.2⟩, mem_H0.2 rfl⟩

lemma bcPr_bcH0 (L : FiniteLevel R A) (h : L.H0) :
    L.bcPr μ (L.bcH0 μ h : (L.baseChange μ).H) = h := bcPr_bcEquiv μ L _

lemma bcH0_bcPr (L : FiniteLevel R A) (g : (L.baseChange μ).H0) :
    L.bcH0 μ ⟨L.bcPr μ g, bcPr_mem_H0 μ L g.2⟩ = g := by
  apply Subtype.ext
  conv_rhs => rw [← (L.bcEquiv μ).apply_symm_apply (g : (L.baseChange μ).H)]
  change L.bcEquiv μ _ = _
  congr 1
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change (1 : A') = ((L.bcEquiv μ).symm g).1.2
  rw [bcEquiv_symm_snd]
  exact (mem_H0.1 g.2).symm

variable {μ}

/-- The homomorphism `H ×_A A' → M ×_A A'` induced by a morphism of levels. -/
def bcRfp {L M : FiniteLevel R A} (φ : L ⟶ M) : L.Hfp μ →* M.Hfp μ where
  toFun p := ⟨(φ.r p.1.1, p.1.2), by rw [mem_Hfp, φ.r_a]; exact p.2⟩
  map_one' := by ext <;> simp
  map_mul' p q := by ext <;> simp

lemma bcAut_map {L M : FiniteLevel R A} (φ : L ⟶ M) (p : L.Hfp μ) (z : R' ⊗[R] M.B) :
    Algebra.TensorProduct.map (AlgHom.id R' R') φ.f ((bcAut μ M (bcRfp φ p)).σ z) =
      (bcAut μ L p).σ (Algebra.TensorProduct.map (AlgHom.id R' R') φ.f z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    rw [bcAut_σ_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      bcAut_σ_tmul]
    congr 1
    exact φ.f_σ p.1.1 b
  | add x y hx hy => rw [RingEquiv.map_add, map_add, hx, hy, map_add, RingEquiv.map_add]

variable (μ) in
/-- **Base change of a morphism of levels.** -/
def bcMap {L M : FiniteLevel R A} (φ : L ⟶ M) : L.baseChange μ ⟶ M.baseChange μ where
  f := (L.bcE' μ).symm.toAlgHom.comp
    ((Algebra.TensorProduct.map (AlgHom.id R' R') φ.f).comp (M.bcE' μ).toAlgHom)
  r := (M.bcEquiv μ).toMonoidHom.comp ((bcRfp φ).comp (L.bcEquiv μ).symm.toMonoidHom)
  r_a g := by
    change ((bcRfp φ ((L.bcEquiv μ).symm g))).1.2 = _
    exact bcEquiv_symm_snd μ L g
  f_σ g y := by
    conv_rhs => rw [← (L.bcEquiv μ).apply_symm_apply g]
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, bcEquiv_σ, AlgEquiv.apply_symm_apply]
    rw [bcAut_map]

lemma bcMap_f_bcι {L M : FiniteLevel R A} (φ : L ⟶ M) (y : M.B) :
    (bcMap μ φ).f (M.bcι μ y) = L.bcι μ (φ.f y) := by
  apply (L.bcE' μ).injective
  simp only [bcMap, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply,
    AlgEquiv.apply_symm_apply, bcE_bcι, Algebra.TensorProduct.map_tmul, map_one]

lemma bcPr_bcMap {L M : FiniteLevel R A} (φ : L ⟶ M) (g : (L.baseChange μ).H) :
    M.bcPr μ ((bcMap μ φ).r g) = φ.r (L.bcPr μ g) := by
  simp [bcMap, bcPr, bcRfp]

variable (μ) in
/-- **Base change of levels** as a functor. -/
def bcFunctor : FiniteLevel R A ⥤ FiniteLevel R' A' where
  obj L := L.baseChange μ
  map φ := bcMap μ φ
  map_id L := by
    refine Hom.ext ?_ ?_
    · refine AlgHom.ext fun x => ?_
      change (L.bcE' μ).symm ((Algebra.TensorProduct.map (AlgHom.id R' R') (AlgHom.id R L.B))
        (L.bcE' μ x)) = x
      rw [Algebra.TensorProduct.map_id, AlgHom.id_apply, AlgEquiv.symm_apply_apply]
    · refine MonoidHom.ext fun g => ?_
      change (L.bcEquiv μ) (bcRfp (𝟙 L) ((L.bcEquiv μ).symm g)) = g
      conv_rhs => rw [← (L.bcEquiv μ).apply_symm_apply g]
      rfl
  map_comp φ ψ := by
    refine Hom.ext ?_ ?_
    · refine AlgHom.ext fun x => ?_
      change (_ : (_ : FiniteLevel R' A').B) = (bcMap μ φ).f ((bcMap μ ψ).f x)
      simp only [bcMap, AlgHom.coe_comp, AlgEquiv.coe_toAlgHom, Function.comp_apply,
        AlgEquiv.apply_symm_apply]
      congr 1
      rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp]
      rfl
    · refine MonoidHom.ext fun g => ?_
      simp only [bcMap, comp_r, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MulEquiv.symm_apply_apply]
      rfl

end FiniteLevel

end

end TemperedFundamentalGroups
