/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Tempered.BaseChangeLevel

/-!
# Induced finite étale algebras (Blueprint §11, F7′)

Let `A` act on `R`, let `B'` be a finite étale `R`-algebra and let `α : S →* A` be a homomorphism
from a finite group `S`. The **twisted induced algebra** `IndAlg B' α = Π x : S, B'^{(α x)}` is the
product of copies of `B'`, the copy at `x` with structure map `r ↦ (α x)⁻¹ • r` (`TwAlg`). It is
finite étale over `R`.

If moreover `H'` is a group of semilinear automorphisms of `B'` over a group `A'` acting on `R`
through `μα : A' →* A` (`μα a' • r = a' • r`) and `β : H' →* S` lies over `μα` (`α (β k) = μα k.a`),
then `S × H'` acts on `IndAlg B' α` semilinearly (`indAut`):

`((s, k) • φ) x = σ_k (φ (s⁻¹ * x * β k))`, semilinear over `α s`.

This is the algebra of the induced level along `A' → A` (`S = A`) and of the auxiliary levels of
the counit (`S = H`), see `Tempered/InducedLevel.lean`.
-/

universe u

open Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]

section Twist

variable (R) in
/-- `R` with the structure of an `R`-algebra twisted by `a⁻¹`. -/
def TwBase (_a : A) : Type u := R

instance (a : A) : CommRing (TwBase R a) := inferInstanceAs (CommRing R)

instance (a : A) : Algebra R (TwBase R a) :=
  (MulSemiringAction.toRingHom A R a⁻¹).toAlgebra

lemma twBase_algebraMap (a : A) (r : R) :
    algebraMap R (TwBase R a) r = (a⁻¹ • r : R) := rfl

/-- `R ≃ TwBase R a` as `R`-algebras. -/
def twBaseEquiv (a : A) : R ≃ₐ[R] TwBase R a :=
  AlgEquiv.ofBijective (Algebra.ofId R (TwBase R a))
    (MulAction.bijective (a⁻¹ : A))

instance (a : A) : Algebra.Etale R (TwBase R a) := Algebra.Etale.of_equiv (twBaseEquiv a)

instance (a : A) : Module.Finite R (TwBase R a) :=
  Module.Finite.equiv (twBaseEquiv a).toLinearEquiv

variable (B' : Type u) [CommRing B'] [Algebra R B']

/-- `B'` with the structure of an `R`-algebra twisted by `a⁻¹`: `r ↦ algebraMap (a⁻¹ • r)`. -/
def TwAlg (_a : A) : Type u := B'

instance (a : A) : CommRing (TwAlg B' a) := inferInstanceAs (CommRing B')

instance (a : A) : Algebra (TwBase R a) (TwAlg B' a) := inferInstanceAs (Algebra R B')

instance (a : A) : Algebra R (TwAlg B' a) :=
  ((algebraMap (TwBase R a) (TwAlg B' a)).comp (algebraMap R (TwBase R a))).toAlgebra

instance (a : A) : IsScalarTower R (TwBase R a) (TwAlg B' a) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

lemma twAlg_algebraMap (a : A) (r : R) :
    (algebraMap R (TwAlg B' a) r : B') = algebraMap R B' (a⁻¹ • r) := rfl

instance [Algebra.Etale R B'] (a : A) : Algebra.Etale R (TwAlg B' a) :=
  haveI : Algebra.Etale (TwBase R a) (TwAlg B' a) :=
    inferInstanceAs (Algebra.Etale R B')
  Algebra.Etale.comp R (TwBase R a) (TwAlg B' a)

instance [Module.Finite R B'] (a : A) : Module.Finite R (TwAlg B' a) :=
  haveI : Module.Finite (TwBase R a) (TwAlg B' a) :=
    inferInstanceAs (Module.Finite R B')
  Module.Finite.trans (TwBase R a) (TwAlg B' a)

end Twist

section Ind

variable (B' : Type u) [CommRing B'] [Algebra R B'] {S : Type u} [Group S] (α : S →* A)

/-- **The twisted induced algebra** `Π x : S, B'^{(α x)}`. -/
abbrev IndAlg : Type u := Π x : S, TwAlg B' (α x)

variable {B'} {α}

lemma indAlg_algebraMap_apply (r : R) (x : S) :
    (algebraMap R (IndAlg B' α) r x : B') = algebraMap R B' ((α x)⁻¹ • r) := rfl

/-- The evaluation `IndAlg B' α → B'` at `x`, as a ring map. -/
def indEval (x : S) : IndAlg B' α →+* B' := Pi.evalRingHom (fun y => TwAlg B' (α y)) x

lemma indEval_apply (x : S) (φ : IndAlg B' α) : indEval x φ = φ x := rfl

lemma indEval_algebraMap (x : S) (r : R) :
    indEval x (algebraMap R (IndAlg B' α) r) = algebraMap R B' ((α x)⁻¹ • r) := rfl

variable (R) in
/-- The evaluation at `1` is `R`-linear. -/
def indEval₁ : IndAlg B' α →ₐ[R] B' where
  toRingHom := indEval 1
  commutes' r := by
    change algebraMap R B' ((α 1)⁻¹ • r) = _
    rw [map_one, inv_one, one_smul]

lemma indEval₁_apply (φ : IndAlg B' α) : indEval₁ R φ = φ 1 := rfl

/-- Constant functions. -/
def indConst (b : B') : IndAlg B' α := fun _ => b

end Ind

section Map

variable {B₁ B₂ : Type u} [CommRing B₁] [Algebra R B₁] [CommRing B₂] [Algebra R B₂]
  {S₁ S₂ : Type u} [Group S₁] [Group S₂] {α₁ : S₁ →* A} {α₂ : S₂ →* A}

/-- The map `IndAlg B₂ α₂ → IndAlg B₁ α₁`, `φ ↦ (x ↦ f (φ (θ x)))`, for `α₂ ∘ θ = α₁`. -/
def indMap (θ : S₁ → S₂) (hθ : ∀ x, α₂ (θ x) = α₁ x) (f : B₂ →ₐ[R] B₁) :
    IndAlg B₂ α₂ →ₐ[R] IndAlg B₁ α₁ where
  toFun φ x := (f (φ (θ x) : B₂) : B₁)
  map_one' := funext fun x => f.map_one
  map_mul' φ ψ := funext fun x => f.map_mul (φ (θ x) : B₂) (ψ (θ x))
  map_zero' := funext fun x => f.map_zero
  map_add' φ ψ := funext fun x => f.map_add (φ (θ x) : B₂) (ψ (θ x))
  commutes' r := funext fun x => by
    change f (algebraMap R B₂ ((α₂ (θ x))⁻¹ • r)) = algebraMap R B₁ ((α₁ x)⁻¹ • r)
    rw [AlgHom.commutes, hθ]

lemma indMap_apply (θ : S₁ → S₂) (hθ : ∀ x, α₂ (θ x) = α₁ x) (f : B₂ →ₐ[R] B₁)
    (φ : IndAlg B₂ α₂) (x : S₁) : (indMap θ hθ f φ x : B₁) = f (φ (θ x)) := rfl

end Map

section Action

variable {B' : Type u} [CommRing B'] [Algebra R B'] {S : Type u} [Group S] {α : S →* A}

/-- The ring automorphism `φ ↦ (x ↦ σ (φ (s⁻¹ * x * b)))` of `IndAlg B' α`. -/
def indRingEquiv (s b : S) (σ : B' ≃+* B') : IndAlg B' α ≃+* IndAlg B' α where
  toFun φ x := (σ (φ (s⁻¹ * x * b)) : B')
  invFun φ x := (σ.symm (φ (s * x * b⁻¹)) : B')
  left_inv φ := by
    funext x
    change σ.symm (σ (φ (s⁻¹ * (s * x * b⁻¹) * b) : B')) = (φ x : B')
    rw [RingEquiv.symm_apply_apply]
    congr 1
    group
  right_inv φ := by
    funext x
    change σ (σ.symm (φ (s * (s⁻¹ * x * b) * b⁻¹) : B')) = (φ x : B')
    rw [RingEquiv.apply_symm_apply]
    congr 1
    group
  map_mul' φ ψ := by
    funext x
    exact map_mul σ (φ (s⁻¹ * x * b) : B') (ψ (s⁻¹ * x * b) : B')
  map_add' φ ψ := by
    funext x
    exact map_add σ (φ (s⁻¹ * x * b) : B') (ψ (s⁻¹ * x * b) : B')

lemma indRingEquiv_apply (s b : S) (σ : B' ≃+* B') (φ : IndAlg B' α) (x : S) :
    (indRingEquiv s b σ φ x : B') = σ (φ (s⁻¹ * x * b)) := rfl

lemma indRingEquiv_symm_apply (s b : S) (σ : B' ≃+* B') (φ : IndAlg B' α) (x : S) :
    ((indRingEquiv s b σ).symm φ x : B') = σ.symm (φ (s * x * b⁻¹)) := rfl

variable {A' : Type u} [Group A'] [MulSemiringAction A' R] {μα : A' →* A}
  (hμ : ∀ (a' : A') (r : R), μα a' • r = a' • r) {H' : Subgroup (SemilinearAut R A' B')}
  (β : H' →* S) (hβ : ∀ k : H', α (β k) = μα (k : SemilinearAut R A' B').a)

include hμ hβ in
lemma indRingEquiv_algebraMap (s : S) (k : H') (r : R) :
    indRingEquiv (α := α) s (β k) (k : SemilinearAut R A' B').σ (algebraMap R _ r) =
      algebraMap R (IndAlg B' α) (α s • r) := by
  funext x
  change (k : SemilinearAut R A' B').σ (algebraMap R B' ((α (s⁻¹ * x * β k))⁻¹ • r)) =
    algebraMap R B' ((α x)⁻¹ • α s • r)
  rw [(k : SemilinearAut R A' B').map_algebraMap, ← hμ, ← hβ, smul_smul, smul_smul]
  congr 2
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv]
  group

/-- The semilinear automorphism of `IndAlg B' α` given by `(s, k) ∈ S × H'`. -/
def indAut (p : S × H') : SemilinearAut R A (IndAlg B' α) where
  a := α p.1
  σ := indRingEquiv p.1 (β p.2) (p.2 : SemilinearAut R A' B').σ
  map_algebraMap r := indRingEquiv_algebraMap hμ β hβ p.1 p.2 r

lemma indAut_σ_apply (p : S × H') (φ : IndAlg B' α) (x : S) :
    ((indAut hμ β hβ p).σ φ x : B') =
      (p.2 : SemilinearAut R A' B').σ (φ (p.1⁻¹ * x * β p.2)) := rfl

/-- **The action of `S × H'` on the induced algebra.** -/
def indAutHom : S × H' →* SemilinearAut R A (IndAlg B' α) where
  toFun := indAut hμ β hβ
  map_one' := by
    refine SemilinearAut.ext (map_one α) (RingEquiv.ext fun φ => funext fun x => ?_)
    change (1 : SemilinearAut R A' B').σ (φ (1⁻¹ * x * β 1)) = (φ x : B')
    rw [map_one, inv_one, one_mul, mul_one]
    rfl
  map_mul' p q := by
    refine SemilinearAut.ext (map_mul α _ _) (RingEquiv.ext fun φ => funext fun x => ?_)
    change ((p.2 * q.2 : H') : SemilinearAut R A' B').σ (φ ((p.1 * q.1)⁻¹ * x * β (p.2 * q.2))) =
      (p.2 : SemilinearAut R A' B').σ ((q.2 : SemilinearAut R A' B').σ
        (φ (q.1⁻¹ * (p.1⁻¹ * x * β p.2) * β q.2)))
    rw [Subgroup.coe_mul, SemilinearAut.mul_σ, RingEquiv.trans_apply, map_mul]
    congr 3
    group

lemma indAutHom_apply (p : S × H') : indAutHom hμ β hβ p = indAut hμ β hβ p := rfl

/-- **Faithfulness**: if `B'` is nontrivial and only `1 ∈ H'` acts trivially on `B'`, the action
of `S × H'` on the induced algebra is faithful. -/
lemma indAutHom_injective [Nontrivial B']
    (hfaith : ∀ k : H', (∀ y, (k : SemilinearAut R A' B').σ y = y) → k = 1) :
    Function.Injective (indAutHom (α := α) hμ β hβ) := by
  classical
  rw [injective_iff_map_eq_one]
  rintro ⟨s, k⟩ h
  have hσ : ∀ φ : IndAlg B' α, (indAut hμ β hβ (s, k)).σ φ = φ := fun φ => by
    rw [← indAutHom_apply, h]
    rfl
  have hx : ∀ x : S, s⁻¹ * x * β k = x := by
    intro x
    by_contra hne
    have := congrFun (hσ (Pi.single (M := fun y => TwAlg B' (α y)) (s⁻¹ * x * β k) 1)) x
    rw [indAut_σ_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hne)] at this
    have h1 : (1 : B') = 0 := (map_one (k : SemilinearAut R A' B').σ).symm.trans this
    exact one_ne_zero h1
  have hk : k = 1 := hfaith k fun y => by
    have := congrFun (hσ (indConst (α := α) y)) 1
    rw [indAut_σ_apply] at this
    exact this
  subst hk
  have := hx 1
  rw [map_one, mul_one, mul_one, inv_eq_one] at this
  rw [this]
  rfl

end Action

end

end TemperedFundamentalGroups
