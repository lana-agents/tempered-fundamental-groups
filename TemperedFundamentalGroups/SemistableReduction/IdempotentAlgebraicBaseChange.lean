/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Trivial idempotents after an algebraic base change (generic; MR13, (f) step 3)

For a field `K`, an algebraic extension `L / K` and a `K`-algebra `B`, every element of
`L ⊗[K] B` comes from `E ⊗[K] B` for a finite subextension `E` (`exists_mem_range_incl`), and
`E ⊗[K] B → L ⊗[K] B` is injective (`B` is flat over the field `K`, `injective_incl`). Hence:

* **`IdempotentAlgebraicBaseChange.eq_zero_or_eq_one`**: if `E ⊗[K] B` has only the trivial
  idempotents for every finite subextension `E` of `L / K`, so has `L ⊗[K] B`.

Applied with `L = K̄` this reduces the geometric connectedness of the generic fibre of the lift of
a tame cover (`K̄ ⊗_K B₁[1/ϖ]`) to finite extensions `K'` of `K`
(`P1Three.connected_lift_baseChange`).
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace IdempotentAlgebraicBaseChange

variable {K L B : Type u} [Field K] [Field L] [Algebra K L] [CommRing B] [Algebra K B]

/-- The base change `E ⊗[K] B → L ⊗[K] B` of the inclusion of an intermediate field. -/
noncomputable abbrev incl (E : IntermediateField K L) : E ⊗[K] B →ₐ[K] L ⊗[K] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom K E L) (AlgHom.id K B)

lemma injective_incl (E : IntermediateField K L) : Function.Injective (incl (B := B) E) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := B)
    (IsScalarTower.toAlgHom K E L).toLinearMap (fun x y hxy ↦ Subtype.ext hxy)
  intro x y hxy
  exact h hxy

lemma incl_comp_inclusion {E E' : IntermediateField K L} (h : E ≤ E') :
    (incl (B := B) E').comp
        (Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id K B)) =
      incl E :=
  Algebra.TensorProduct.ext' fun _ _ ↦ rfl

lemma mem_range_mono {E E' : IntermediateField K L} (h : E ≤ E') {x : L ⊗[K] B}
    (hx : ∃ y, incl (B := B) E y = x) : ∃ y, incl (B := B) E' y = x := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨Algebra.TensorProduct.map (IntermediateField.inclusion h) (AlgHom.id K B) y,
    DFunLike.congr_fun (incl_comp_inclusion (B := B) h) y⟩

/-- **Every element of `L ⊗[K] B` comes from a finite subextension** (`L / K` algebraic). -/
theorem exists_mem_range_incl [Algebra.IsAlgebraic K L] (x : L ⊗[K] B) :
    ∃ E : IntermediateField K L, FiniteDimensional K E ∧ ∃ y, incl (B := B) E y = x := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨⊥, inferInstance, 0, map_zero _⟩
  | tmul l b =>
    refine ⟨IntermediateField.adjoin K {l},
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral l), ?_⟩
    exact ⟨⟨l, IntermediateField.mem_adjoin_simple_self K l⟩ ⊗ₜ b, rfl⟩
  | add x y hx hy =>
    obtain ⟨E1, h1, hx⟩ := hx
    obtain ⟨E2, h2, hy⟩ := hy
    obtain ⟨x', hx'⟩ := mem_range_mono (le_sup_left (b := E2)) hx
    obtain ⟨y', hy'⟩ := mem_range_mono (le_sup_right (a := E1)) hy
    exact ⟨E1 ⊔ E2, inferInstance, x' + y', by rw [map_add, hx', hy']⟩

/-- **Trivial idempotents after an algebraic base change**: if `E ⊗[K] B` has only the
idempotents `0`, `1` for every finite subextension `E` of the algebraic extension `L / K`, so has
`L ⊗[K] B`. -/
theorem eq_zero_or_eq_one [Algebra.IsAlgebraic K L]
    (hB : ∀ E : IntermediateField K L, FiniteDimensional K E →
      ∀ y : E ⊗[K] B, IsIdempotentElem y → y = 0 ∨ y = 1)
    {x : L ⊗[K] B} (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  obtain ⟨E, hE, y, rfl⟩ := exists_mem_range_incl (B := B) x
  have hy : IsIdempotentElem y := injective_incl E (by rw [map_mul, hx.eq])
  rcases hB E hE y hy with rfl | rfl
  · exact Or.inl (map_zero _)
  · exact Or.inr (map_one _)

end IdempotentAlgebraicBaseChange

end SemistableReduction
