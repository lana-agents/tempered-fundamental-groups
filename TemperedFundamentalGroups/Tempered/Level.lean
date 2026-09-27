/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Galois levels of an orbifold `[Spec R / A]`

Let `Y = Spec R` be an affine scheme with an action of a group `A` by ring automorphisms of `R`,
and let `Ω` be an `R`-algebra (a geometric point `ȳ : Spec Ω → Y`). This file defines the
*finite levels* over the orbifold `[Y/A]` at `ȳ`: pointed finite étale `R`-algebras `B` such that
`Spec B → [Y/A]` is Galois. These are the finite étale covers through which the tempered
fundamental group is computed (Blueprint §3.2).

For a finite étale `R`-algebra `B`, the group
`G_B = {(a, σ) : a ∈ A, σ ∈ Aut_ring(B), σ ∘ (R → B) = (R → B) ∘ (a • ·)}`
(`SemilinearAut R A B`) acts on `Spec B` over the action of `A` on `Y`; its kernel
`G_B⁰ = {(1, σ)}` is `Aut_R(B)`. It acts on the geometric fibre `B →ₐ[R] Ω` by
`g • t = t ∘ σ⁻¹`. A finite level is *Galois* if `G_B⁰` acts simply transitively on the fibre and
`G_B → A` is surjective.

Levels are coded by presentations `B = R[x₁, …, xₙ] ⧸ I`, so that `FiniteLevel R A Ω : Type u`.

## Main definitions

* `SemilinearAut R A B`: the group `G_B`, with `SemilinearAut.toA : G_B →* A`.
* `FiniteLevel R A Ω`: Galois pointed finite étale covers of `[Spec R / A]`.
* `FiniteLevel.Hom`: pointed morphisms of levels together with a compatible homomorphism of
  the groups `G_B`; `FiniteLevel` is a category.
-/

universe u

open CategoryTheory

namespace TemperedFundamentalGroups

variable (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]

/-- The group `G_B` of ring automorphisms of an `R`-algebra `B` which are semilinear over an
element of `A`. -/
@[ext]
structure SemilinearAut (B : Type u) [CommRing B] [Algebra R B] : Type u where
  /-- The element of `A` over which the automorphism lies. -/
  a : A
  /-- The ring automorphism. -/
  σ : B ≃+* B
  /-- Semilinearity. -/
  map_algebraMap : ∀ r : R, σ (algebraMap R B r) = algebraMap R B (a • r)

namespace SemilinearAut

variable {R A} {B : Type u} [CommRing B] [Algebra R B]

instance : One (SemilinearAut R A B) := ⟨⟨1, RingEquiv.refl B, fun r => by simp⟩⟩

instance : Mul (SemilinearAut R A B) :=
  ⟨fun g h => ⟨g.a * h.a, h.σ.trans g.σ, fun r => by
    simp [h.map_algebraMap, g.map_algebraMap, mul_smul]⟩⟩

instance : Inv (SemilinearAut R A B) :=
  ⟨fun g => ⟨g.a⁻¹, g.σ.symm, fun r => by
    apply g.σ.injective
    simp [g.map_algebraMap, smul_smul]⟩⟩

@[simp] lemma one_a : (1 : SemilinearAut R A B).a = 1 := rfl
@[simp] lemma one_σ : (1 : SemilinearAut R A B).σ = RingEquiv.refl B := rfl
@[simp] lemma mul_a (g h : SemilinearAut R A B) : (g * h).a = g.a * h.a := rfl
@[simp] lemma mul_σ (g h : SemilinearAut R A B) : (g * h).σ = h.σ.trans g.σ := rfl
@[simp] lemma inv_a (g : SemilinearAut R A B) : g⁻¹.a = g.a⁻¹ := rfl
@[simp] lemma inv_σ (g : SemilinearAut R A B) : g⁻¹.σ = g.σ.symm := rfl

instance : Group (SemilinearAut R A B) where
  mul_assoc g h k := SemilinearAut.ext (mul_assoc _ _ _) (by ext; rfl)
  one_mul g := SemilinearAut.ext (one_mul _) (by ext; rfl)
  mul_one g := SemilinearAut.ext (mul_one _) (by ext; rfl)
  inv_mul_cancel g := SemilinearAut.ext (inv_mul_cancel _) (by ext; simp)

/-- The projection `G_B →* A`. -/
def toA : SemilinearAut R A B →* A where
  toFun g := g.a
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] lemma toA_apply (g : SemilinearAut R A B) : toA g = g.a := rfl

/-- An element of `G_B⁰ = ker (G_B → A)` is `R`-linear. -/
lemma σ_algebraMap_of_a_eq_one {g : SemilinearAut R A B} (hg : g.a = 1) (r : R) :
    g.σ (algebraMap R B r) = algebraMap R B r := by
  rw [g.map_algebraMap, hg, one_smul]

end SemilinearAut

variable (Ω : Type u) [CommRing Ω] [Algebra R Ω]

/-- The coordinate ring `R[x₁, …, xₙ] ⧸ I` of a coded finite étale cover. -/
abbrev LevelRing (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R)) : Type u :=
  MvPolynomial (Fin n) R ⧸ I

/-- **A finite level** of the orbifold `[Spec R / A]` at the geometric point `Spec Ω → Spec R`:
a finite étale `R`-algebra `B = R[x₁, …, xₙ] ⧸ I` with a geometric point `t₀ : B →ₐ[R] Ω`, such
that `Spec B → [Spec R / A]` is Galois: `G_B⁰` acts simply transitively on the geometric fibre
and `G_B → A` is surjective. -/
structure FiniteLevel : Type u where
  /-- The number of generators. -/
  n : ℕ
  /-- The ideal of relations. -/
  I : Ideal (MvPolynomial (Fin n) R)
  /-- `B` is étale over `R`. -/
  etale : Algebra.Etale R (LevelRing R n I)
  /-- `B` is finite over `R`. -/
  finite : Module.Finite R (LevelRing R n I)
  /-- The base point of the geometric fibre. -/
  t₀ : LevelRing R n I →ₐ[R] Ω
  /-- `G_B⁰` acts simply transitively on the geometric fibre `B →ₐ[R] Ω`. -/
  simplyTransitive : ∀ t : LevelRing R n I →ₐ[R] Ω,
    ∃! g : SemilinearAut R A (LevelRing R n I),
      g.a = 1 ∧ (t : LevelRing R n I →+* Ω) = (t₀ : LevelRing R n I →+* Ω).comp g.σ.symm
  /-- `G_B → A` is surjective. -/
  surjective : Function.Surjective (SemilinearAut.toA (R := R) (A := A) (B := LevelRing R n I))

namespace FiniteLevel

variable {R A Ω}

/-- The coordinate ring of a finite level. -/
abbrev B (L : FiniteLevel R A Ω) : Type u := LevelRing R L.n L.I

/-- The group `G_B` of a finite level. -/
abbrev G (L : FiniteLevel R A Ω) : Type u := SemilinearAut R A L.B

/-- **A morphism of finite levels** `L ⟶ L'` (`Spec B → Spec B'` over `[Spec R / A]`): a pointed
`R`-algebra map `f : B' → B` together with a homomorphism `r : G_B →* G_B'` over `A` such that
`f` is `r`-equivariant. -/
@[ext]
structure Hom (L L' : FiniteLevel R A Ω) : Type u where
  /-- The map of coordinate rings (contravariant). -/
  f : L'.B →ₐ[R] L.B
  /-- Base points are preserved. -/
  pointed : L.t₀.comp f = L'.t₀
  /-- The homomorphism of groups. -/
  r : L.G →* L'.G
  /-- It lies over `A`. -/
  r_a : ∀ g, (r g).a = g.a
  /-- `f` is equivariant. -/
  f_σ : ∀ g y, f ((r g).σ y) = g.σ (f y)

noncomputable instance : Category (FiniteLevel R A Ω) where
  Hom := Hom
  id L := ⟨AlgHom.id R L.B, by ext; simp, MonoidHom.id _, fun _ => rfl, fun _ _ => rfl⟩
  comp φ ψ := ⟨φ.f.comp ψ.f, by rw [← AlgHom.comp_assoc, φ.pointed, ψ.pointed],
    ψ.r.comp φ.r, fun g => by simp [ψ.r_a, φ.r_a],
    fun g y => by simp [ψ.f_σ, φ.f_σ]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] lemma id_f (L : FiniteLevel R A Ω) : Hom.f (𝟙 L) = AlgHom.id R L.B := rfl
@[simp] lemma id_r (L : FiniteLevel R A Ω) : Hom.r (𝟙 L) = MonoidHom.id _ := rfl
@[simp] lemma comp_f {L L' L'' : FiniteLevel R A Ω} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (φ ≫ ψ).f = φ.f.comp ψ.f := rfl
@[simp] lemma comp_r {L L' L'' : FiniteLevel R A Ω} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (φ ≫ ψ).r = ψ.r.comp φ.r := rfl

end FiniteLevel

end TemperedFundamentalGroups
