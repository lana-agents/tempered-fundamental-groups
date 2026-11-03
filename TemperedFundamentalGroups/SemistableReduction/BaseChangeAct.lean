/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Flat.Basic

/-!
# Base change of a group action by algebra automorphisms (generic; MR13 (f) step 4 bridge)

For an `R`-algebra `B` (over `O`) with a group `G` acting by `R`-algebra automorphisms
`ρ : G →* (B ≃ₐ[R] B)` and an `O`-algebra `L`:

* **`BaseChangeAct.act : G →* (L ⊗_O B ≃ₐ[L] L ⊗_O B)`** (`l ⊗ b ↦ l ⊗ ρ g b`), fixing the image of
  `L ⊗_O R` (**`act_comp_map`**);
* **`act_injective`**: faithful if `ρ` is and `B → L ⊗_O B` is injective;
* **`toAlgAct`**: a ring action fixing `R` as an action by `R`-algebra automorphisms;
* **`injective_includeRight`**: `B → L ⊗_O B` is injective if `B` is flat over `O` and `O → L` is
  injective.

Used with `B = B₁` (the second chart of the lift of a tame cover, `R = R1`) and `L = K̄`: the
Galois group of the special cover acts faithfully on the generic fibre `K̄ ⊗_O B₁` over
`K̄ ⊗_O R1` (the coordinate ring of `ℙ¹_{K̄} ∖ {0, 1, a}`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace BaseChangeAct

variable (O : Type u) {R B : Type u} [CommRing O] [CommRing R] [CommRing B] [Algebra O R]
  [Algebra R B] [Algebra O B] [IsScalarTower O R B] (L : Type u) [CommRing L] [Algebra O L]
  {G : Type*} [Group G] (ρ : G →* (B ≃ₐ[R] B))

/-- The base change of an `R`-algebra endomorphism of `B` to `L ⊗_O B`. -/
noncomputable abbrev bc (f : B →ₐ[R] B) : L ⊗[O] B →ₐ[L] L ⊗[O] B :=
  Algebra.TensorProduct.map (AlgHom.id L L) (f.restrictScalars O)

lemma bc_tmul (f : B →ₐ[R] B) (l : L) (b : B) : bc O L f (l ⊗ₜ b) = l ⊗ₜ f b := rfl

lemma bc_comp (f g : B →ₐ[R] B) : (bc O L f).comp (bc O L g) = bc O L (f.comp g) :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

lemma bc_id : bc O L (AlgHom.id R B) = AlgHom.id L (L ⊗[O] B) :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

/-- **The action of `G` on `L ⊗_O B`**: `l ⊗ b ↦ l ⊗ ρ g b`. -/
noncomputable def act : G →* (L ⊗[O] B ≃ₐ[L] L ⊗[O] B) where
  toFun g := AlgEquiv.ofAlgHom (bc O L (ρ g).toAlgHom) (bc O L (ρ g⁻¹).toAlgHom)
    (Algebra.TensorProduct.ext' fun l b ↦ by
      change l ⊗ₜ ρ g (ρ g⁻¹ b) = l ⊗ₜ b
      rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl)
    (Algebra.TensorProduct.ext' fun l b ↦ by
      change l ⊗ₜ ρ g⁻¹ (ρ g b) = l ⊗ₜ b
      rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl)
  map_one' := AlgEquiv.ext fun x ↦ by
    change bc O L (ρ 1).toAlgHom x = x
    rw [map_one]
    exact AlgHom.congr_fun (bc_id O L (R := R)) x
  map_mul' g h := AlgEquiv.ext fun x ↦ by
    change bc O L (ρ (g * h)).toAlgHom x = bc O L (ρ g).toAlgHom (bc O L (ρ h).toAlgHom x)
    rw [map_mul]
    exact (AlgHom.congr_fun (bc_comp O L (ρ g).toAlgHom (ρ h).toAlgHom) x).symm

lemma act_tmul (g : G) (l : L) (b : B) : act O L ρ g (l ⊗ₜ b) = l ⊗ₜ ρ g b := rfl

/-- **The action fixes `L ⊗_O R`.** -/
lemma act_comp_map (g : G) :
    (act O L ρ g).toAlgHom.comp (Algebra.TensorProduct.map (AlgHom.id L L)
      (IsScalarTower.toAlgHom O R B)) =
      Algebra.TensorProduct.map (AlgHom.id L L) (IsScalarTower.toAlgHom O R B) :=
  Algebra.TensorProduct.ext' fun l r ↦ by
    change l ⊗ₜ ρ g (algebraMap R B r) = l ⊗ₜ algebraMap R B r
    rw [AlgEquiv.commutes]

/-- **The action on `L ⊗_O B` is faithful** if `ρ` is and `B → L ⊗_O B` is injective. -/
theorem act_injective (hρ : Function.Injective ρ)
    (hinj : Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[O] L ⊗[O] B)) :
    Function.Injective (act O L ρ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply hρ
  rw [map_one]
  ext b
  apply hinj
  change (1 : L) ⊗ₜ ρ g b = (1 : L) ⊗ₜ b
  rw [← act_tmul, hg]
  rfl

/-- **`B → L ⊗_O B` is injective** for `B` flat over `O` and `O → L` injective. -/
theorem injective_includeRight [Module.Flat O B] (hL : Function.Injective (algebraMap O L)) :
    Function.Injective (Algebra.TensorProduct.includeRight : B →ₐ[O] L ⊗[O] B) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B)
    (Algebra.linearMap O L) hL
  intro x y hxy
  apply (TensorProduct.lid O B).symm.injective
  apply h
  change (algebraMap O L 1) ⊗ₜ x = (algebraMap O L 1) ⊗ₜ y
  rw [map_one]
  exact hxy

/-- **A ring action fixing `R` is an action by `R`-algebra automorphisms.** -/
def toAlgAct {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {G : Type*} [Group G]
    (ρ : G →* (B ≃+* B)) (h : ∀ g r, ρ g (algebraMap R B r) = algebraMap R B r) :
    G →* (B ≃ₐ[R] B) where
  toFun g := { ρ g with commutes' := h g }
  map_one' := AlgEquiv.ext fun x ↦ RingEquiv.congr_fun (map_one ρ) x
  map_mul' g g' := AlgEquiv.ext fun x ↦ RingEquiv.congr_fun (map_mul ρ g g') x

lemma toAlgAct_apply {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {G : Type*} [Group G]
    (ρ : G →* (B ≃+* B)) (h : ∀ g r, ρ g (algebraMap R B r) = algebraMap R B r) (g : G) (x : B) :
    toAlgAct ρ h g x = ρ g x :=
  rfl

lemma toAlgAct_injective {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] {G : Type*}
    [Group G] (ρ : G →* (B ≃+* B)) (h : ∀ g r, ρ g (algebraMap R B r) = algebraMap R B r)
    (hρ : Function.Injective ρ) : Function.Injective (toAlgAct ρ h) := fun g g' hgg' ↦
  hρ (RingEquiv.ext fun x ↦ AlgEquiv.congr_fun hgg' x)

end BaseChangeAct

end SemistableReduction
