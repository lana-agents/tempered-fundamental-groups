/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# A unit criterion from the Nullstellensatz

In a finitely generated algebra `R` over a field `k`, an element which does not vanish under
any `k`-algebra map `R → k̄` is a unit: otherwise it lies in a maximal ideal `𝔪`, and the
residue field `R ⧸ 𝔪` is finite over `k` (Zariski's lemma), hence embeds into `k̄`.
-/

namespace TemperedFundamentalGroups.Orbicurve

/-- **Nullstellensatz unit criterion.** An element of a finitely generated `k`-algebra which
does not vanish under any `k`-algebra map to `AlgebraicClosure k` is a unit. -/
theorem isUnit_of_forall_algHom_ne_zero {k R : Type*} [Field k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] {u : R}
    (h : ∀ χ : R →ₐ[k] AlgebraicClosure k, χ u ≠ 0) : IsUnit u := by
  by_contra hu
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal (Ideal.span {u})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  letI : Field (R ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite k (R ⧸ 𝔪) := finite_of_finite_type_of_isJacobsonRing k (R ⧸ 𝔪)
  haveI : Algebra.IsAlgebraic k (R ⧸ 𝔪) := Algebra.IsAlgebraic.of_finite k _
  apply h ((IsAlgClosed.lift : (R ⧸ 𝔪) →ₐ[k] AlgebraicClosure k).comp (Ideal.Quotient.mkₐ k 𝔪))
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle (Ideal.mem_span_singleton_self u)), map_zero]

end TemperedFundamentalGroups.Orbicurve
