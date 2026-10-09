/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Orbifold.Level

/-!
# Levels of an orbifold `[Spec R / A]`

Let `Y = Spec R` be an affine scheme with an action of a group `A` by ring automorphisms of `R`,
and let `Ω` be an `R`-algebra (a geometric point `ȳ : Spec Ω → Y`). This file defines the
*levels* through which tempered coverings of the orbifold `[Y/A]` are presented (Blueprint §3.2):
a finite étale `R`-algebra `B` together with a group `H` of ring automorphisms of `B` that are
semilinear over elements of `A` and that surjects onto `A`. The level `(B, H)` stands for the
finite étale cover `Spec B → Y` with the lift of the `A`-action given by `H`; a covering space
over it is taken modulo `H⁰ = ker (H → A)`.

For a finite étale `R`-algebra `B`, the group
`G_B = {(a, σ) : a ∈ A, σ ∈ Aut_ring(B), σ ∘ (R → B) = (R → B) ∘ (a • ·)}`
is `Pi1.Orbifold.SemilinearAut R A B` (from the `pi1` project, as are the coded finite étale
algebras `Pi1.Orbifold.EtaleCode R` and their rings `Pi1.Orbifold.LevelRing`); `H ≤ G_B`. Its
elements with `a = 1` are `R`-linear and act on the geometric fibre `B →ₐ[R] Ω` by
`g • t = t ∘ σ⁻¹` (`FiniteLevel.fibreAct`).

## Main definitions

* `FiniteLevel R A`: a coded finite étale `R`-algebra with a subgroup `H ≤ G_B` surjecting onto
  `A`; `FiniteLevel.H0` is the kernel of `H → A`.
* `FiniteLevel.Hom`: morphisms of levels (`R`-algebra maps with a compatible homomorphism of the
  groups `H`); `FiniteLevel R A` is a category.
-/

universe u

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable (R : Type u) [CommRing R] (A : Type u) [Group A] [MulSemiringAction A R]

/-- **A level** of the orbifold `[Spec R / A]`: a coded finite étale `R`-algebra `B` with a
subgroup `H` of the semilinear automorphisms which surjects onto `A`. -/
structure FiniteLevel extends EtaleCode R where
  /-- The group of automorphisms lifting the action of `A`. -/
  H : Subgroup (SemilinearAut R A (LevelRing R n I))
  /-- `H → A` is surjective. -/
  surjective : ∀ a : A, ∃ g ∈ H, g.a = a

namespace FiniteLevel

variable {R A}

/-- The coordinate ring of a level. -/
abbrev B (L : FiniteLevel R A) : Type u := LevelRing R L.n L.I

/-- The kernel `H⁰` of `H → A`. -/
def H0 (L : FiniteLevel R A) : Subgroup L.H :=
  (SemilinearAut.toA.comp L.H.subtype).ker

lemma mem_H0 {L : FiniteLevel R A} {g : L.H} : g ∈ L.H0 ↔ (g : SemilinearAut R A L.B).a = 1 :=
  Iff.rfl

/-- **A morphism of levels** `L ⟶ L'` (`Spec B → Spec B'` over `[Spec R / A]`): an `R`-algebra
map `f : B' → B` together with a homomorphism `r : H →* H'` over `A` for which `f` is
equivariant. -/
@[ext]
structure Hom (L L' : FiniteLevel R A) : Type u where
  /-- The map of coordinate rings (contravariant). -/
  f : L'.B →ₐ[R] L.B
  /-- The homomorphism of groups. -/
  r : L.H →* L'.H
  /-- It lies over `A`. -/
  r_a : ∀ g, ((r g : SemilinearAut R A L'.B)).a = (g : SemilinearAut R A L.B).a
  /-- `f` is equivariant. -/
  f_σ : ∀ g y, f ((r g : SemilinearAut R A L'.B).σ y) = (g : SemilinearAut R A L.B).σ (f y)

instance : Category (FiniteLevel R A) where
  Hom := Hom
  id L := ⟨AlgHom.id R L.B, MonoidHom.id _, fun _ => rfl, fun _ _ => rfl⟩
  comp φ ψ := ⟨φ.f.comp ψ.f, ψ.r.comp φ.r, fun g => by simp [ψ.r_a, φ.r_a],
    fun g y => by simp [ψ.f_σ, φ.f_σ]⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] lemma id_f (L : FiniteLevel R A) : Hom.f (𝟙 L) = AlgHom.id R L.B := rfl
@[simp] lemma id_r (L : FiniteLevel R A) : Hom.r (𝟙 L) = MonoidHom.id _ := rfl
@[simp] lemma comp_f {L L' L'' : FiniteLevel R A} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (φ ≫ ψ).f = φ.f.comp ψ.f := rfl
@[simp] lemma comp_r {L L' L'' : FiniteLevel R A} (φ : L ⟶ L') (ψ : L' ⟶ L'') :
    (φ ≫ ψ).r = ψ.r.comp φ.r := rfl

lemma r_mem_H0 {L L' : FiniteLevel R A} (φ : L ⟶ L') {g : L.H} (hg : g ∈ L.H0) :
    φ.r g ∈ L'.H0 := by
  rw [mem_H0] at hg ⊢
  rw [φ.r_a, hg]

section Fibre

variable (Ω : Type u) [CommRing Ω] [Algebra R Ω]

/-- The action of `H⁰` on the geometric fibre `B →ₐ[R] Ω`: `g • t = t ∘ σ_g⁻¹`. -/
def fibreAct (L : FiniteLevel R A) (g : L.H0) (t : L.B →ₐ[R] Ω) : L.B →ₐ[R] Ω :=
  { (t : L.B →+* Ω).comp ((g : SemilinearAut R A L.B).σ.symm : L.B →+* L.B) with
    commutes' := fun r => by
      have h := SemilinearAut.σ_algebraMap_of_a_eq_one (mem_H0.1 g.2) r
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
      rw [← h, RingEquiv.symm_apply_apply, AlgHom.commutes] }

@[simp] lemma fibreAct_apply (L : FiniteLevel R A) (g : L.H0) (t : L.B →ₐ[R] Ω) (y : L.B) :
    fibreAct Ω L g t y = t ((g : SemilinearAut R A L.B).σ.symm y) := rfl

lemma fibreAct_one (L : FiniteLevel R A) (t : L.B →ₐ[R] Ω) : fibreAct Ω L 1 t = t := rfl

lemma fibreAct_mul (L : FiniteLevel R A) (g h : L.H0) (t : L.B →ₐ[R] Ω) :
    fibreAct Ω L (g * h) t = fibreAct Ω L g (fibreAct Ω L h t) := rfl

/-- Morphisms of levels are equivariant on geometric fibres. -/
lemma fibreAct_comp {L L' : FiniteLevel R A} (φ : L ⟶ L') (g : L.H0) (t : L.B →ₐ[R] Ω) :
    (fibreAct Ω L g t).comp φ.f =
      fibreAct Ω L' ⟨φ.r g, r_mem_H0 φ g.2⟩ (t.comp φ.f) := by
  ext y
  simp only [AlgHom.comp_apply, fibreAct_apply]
  congr 1
  apply (g : SemilinearAut R A L.B).σ.injective
  rw [RingEquiv.apply_symm_apply, ← φ.f_σ, RingEquiv.apply_symm_apply]

end Fibre

end FiniteLevel

end

end TemperedFundamentalGroups
