/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.FormalKummerReduce

/-!
# Kummer splittings pass to rings receiving the étale neighbourhood (MR12 T2 S5.4, step K1)

Let `R → N` be ring maps, `C` an `R`-algebra and `Φ : N ⊗_R C ≅ ∏ᵢ N ⊗_{Aᵢ} Bᵢ` an
`N`-algebra isomorphism, where the `Aᵢ`-algebra structure of `N` comes from ring maps
`αᵢ : Aᵢ → R`. For every `R`-algebra map `g : N → T` (**`FormalKummer.baseChangeEquiv`**):

  `T ⊗_R C ≅ T ⊗_N (N ⊗_R C) ≅ T ⊗_N ∏ᵢ N ⊗_{Aᵢ} Bᵢ ≅ ∏ᵢ T ⊗_{Aᵢ} Bᵢ`

(Mathlib `Algebra.TensorProduct.cancelBaseChange`, `piRight`), as `T`-algebras.

Use: `N = N₁/J` the special fibre of an étale neighbourhood of a node (with the reduced Kummer
splitting of `FormalKummer.splitEquiv`), `T` the completion of the special fibre `R/J` of the
chart at the node, and `g` the composite of `N₁/J → (N₁/J)^∧` with the inverse of the
isomorphism of completions `(R/J)^∧ ≅ (N₁/J)^∧` (trivial residue field extension). The result is
the formal Kummer form of the special-fibre covering at the node.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace FormalKummer

noncomputable section

section BaseChange

variable {R N T C : Type u} [CommRing R] [CommRing N] [CommRing T] [CommRing C]
  [Algebra R N] [Algebra R T] [Algebra R C] (g : N →ₐ[R] T)
  {ι : Type} [Fintype ι] [DecidableEq ι] {A Bk : ι → Type u} [∀ i, CommRing (A i)]
  [∀ i, CommRing (Bk i)] [∀ i, Algebra (A i) (Bk i)] [∀ i, Algebra (A i) N]
  [∀ i, Algebra (A i) T] (α : ∀ i, A i →+* R)
  (hN : ∀ i a, algebraMap (A i) N a = algebraMap R N (α i a))
  (hT : ∀ i a, algebraMap (A i) T a = algebraMap R T (α i a))

/-- `T` as an `N`-algebra through `g`. -/
abbrev algNT : Algebra N T := g.toRingHom.toAlgebra

omit [Fintype ι] [DecidableEq ι] in
include hN hT in
lemma isScalarTower_A (i : ι) : letI := algNT g; IsScalarTower (A i) N T :=
  letI := algNT g
  IsScalarTower.of_algebraMap_eq fun a ↦ by
    change _ = g (algebraMap (A i) N a)
    rw [hN, hT, g.commutes]

/-- **Base change of a Kummer splitting** along an `R`-algebra map `g : N → T`. -/
def baseChangeEquiv (Φ : N ⊗[R] C ≃ₐ[N] ∀ i, N ⊗[A i] Bk i) :
    T ⊗[R] C ≃ₐ[T] ∀ i, T ⊗[A i] Bk i :=
  letI := algNT g
  haveI : IsScalarTower R N T := IsScalarTower.of_algebraMap_eq fun x ↦ (g.commutes x).symm
  haveI := isScalarTower_A g α hN hT
  (Algebra.TensorProduct.cancelBaseChange R N T T C).symm.trans
    ((Algebra.TensorProduct.congr AlgEquiv.refl Φ).trans
      ((Algebra.TensorProduct.piRight N T T fun i ↦ N ⊗[A i] Bk i).trans
        (AlgEquiv.piCongrRight fun i ↦
          Algebra.TensorProduct.cancelBaseChange (A i) N T T (Bk i))))

end BaseChange

end

end FormalKummer

end SemistableReduction
