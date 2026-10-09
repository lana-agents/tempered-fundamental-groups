/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.WModelGerm

open Polynomial Cardinal

/-!
# Finite-dimensionality of function fields of curves over subfields

`finiteDimensional_of_transcendental`: a function field `L` of a curve (the fraction field of a
finite type `K`-algebra, algebraic over `K'(u)` for a finite extension `K'/K`) is
finite-dimensional over every subfield `F` containing an element transcendental over `K`
(transcendence degree one).
-/

universe u

namespace TemperedFundamentalGroups

/-- **Finite-dimensionality over a subfield containing a transcendental element**: if `L₁` is
the fraction field of a finite type `K`-algebra and algebraic over `K'(u)` (`K'/K` finite), then
`L₁` is finite over every intermediate field `F` containing an element transcendental over `K`. -/
lemma finiteDimensional_of_transcendental {K K' L F B : Type u} [Field K] [Field K'] [Field L]
    [Field F] [CommRing B] [Algebra K K'] [FiniteDimensional K K'] [Algebra K' L] [Algebra K L]
    [IsScalarTower K K' L] {u : L} (hu : Transcendental K' u)
    (halg : letI := SemistableReduction.xLineAlgebra L hu; Algebra.IsAlgebraic (RatFunc K') L)
    [Algebra K F] [Algebra F L] [IsScalarTower K F L] (t : F)
    (ht : Transcendental K (algebraMap F L t)) [Algebra K B] [Algebra.FiniteType K B]
    [Algebra B L] [IsScalarTower K B L] [IsFractionRing B L] : FiniteDimensional F L := by
  haveI := SemistableReduction.ModelCode.isAlgebraic_adjoin_of_ratFunc hu halg
  have h1 : Algebra.trdeg K' L ≤ 1 := by
    have := Algebra.IsAlgebraic.trdeg_le_cardinalMk K' ({u} : Set L)
    simpa using this
  have h0 : Algebra.trdeg K K' = 0 := trdeg_eq_zero
  have hK : Algebra.trdeg K L ≤ 1 := by
    rw [← trdeg_add_eq (R := K) (S := K') (A := L), h0, zero_add]
    exact h1
  have hb : IsTranscendenceBasis K (fun _ : PUnit.{u + 1} => algebraMap F L t) :=
    (algebraicIndependent_unique_type_iff.2 ht).isTranscendenceBasis_of_trdeg_le_of_finite
      (hK.trans_eq Cardinal.mk_punit.symm)
  haveI : Algebra.IsAlgebraic F L :=
    (hb.isAlgebraic_iff (S := F)).2 fun _ => isAlgebraic_algebraMap t
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := K) (A := B)
  set S : Set L := algebraMap B L '' (s : Set B)
  haveI : Finite S := ((s.finite_toSet).image _).to_subtype
  have hfd : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hB : ∀ b : B, algebraMap B L b ∈ IntermediateField.adjoin F S := by
    intro b
    have hb : b ∈ Algebra.adjoin K (s : Set B) := hs ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply K B L, IsScalarTower.algebraMap_apply K F L]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  have htop : IntermediateField.adjoin F S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    exact div_mem (hB a) (hB b)
  rw [htop] at hfd
  exact (IntermediateField.topEquiv (F := F) (E := L)).toLinearEquiv.finiteDimensional

end TemperedFundamentalGroups
