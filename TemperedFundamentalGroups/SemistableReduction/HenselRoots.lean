/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Roots of unity lift from the residue field (MR12 S5.7, debts μ_{M'}, μ_e)

**`HenselRoots.exists_isPrimitiveRoot_lift`**: if `O` is Henselian along the kernel of a surjection
`θ : O → k` onto a field (e.g. `O` complete, `IsAdicComplete.henselianRing`), `(n : k) ≠ 0` and `k`
contains a primitive `n`-th root of unity `ζ̄`, then `O` contains a primitive `n`-th root of unity
lifting `ζ̄` (Hensel's lemma for `Xⁿ − 1`, whose roots in `k` are simple).
**`HenselRoots.exists_isPrimitiveRoot_of_residue`**: hence any `O`-algebra `K` with injective
structure map (e.g. the fraction field of a chart of the Tate model) contains one: the hypotheses
`IsPrimitiveRoot ζ M'`, `IsPrimitiveRoot ζe e` of the S5/S6 Tate statements (`TateS5`) reduce to
`μ_{M'}, μ_e ⊆ k`, a condition on the residue field (S5.7: satisfied after a finite unramified
base change).
-/

open Polynomial

namespace SemistableReduction

namespace HenselRoots

variable {O k : Type*} [CommRing O] [Field k] (θ : O →+* k) [HenselianRing O (RingHom.ker θ)]

/-- **A primitive `n`-th root of unity of the residue field lifts** (`n` invertible in `k`). -/
theorem exists_isPrimitiveRoot_lift (hθ : Function.Surjective θ) {n : ℕ} (hn : (n : k) ≠ 0)
    {ζ₀ : k} (hζ : IsPrimitiveRoot ζ₀ n) : ∃ ζ : O, IsPrimitiveRoot ζ n ∧ θ ζ = ζ₀ := by
  obtain ⟨a₀, rfl⟩ := hθ ζ₀
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hunit (x : O) (hx : θ x ≠ 0) : IsUnit (Ideal.Quotient.mk (RingHom.ker θ) x) := by
    have h := (Ne.isUnit hx).map (RingHom.quotientKerEquivOfSurjective hθ).symm
    rwa [show (RingHom.quotientKerEquivOfSurjective hθ).symm (θ x) =
      Ideal.Quotient.mk (RingHom.ker θ) x from
        (RingHom.quotientKerEquivOfSurjective hθ).symm_apply_eq.2 rfl] at h
  obtain ⟨a, ha, hsub⟩ := HenselianRing.is_henselian (X ^ n - C 1 : O[X])
    (monic_X_pow_sub_C 1 hn0) a₀
    (by rw [RingHom.mem_ker, eval_sub, eval_pow, eval_X, eval_C, map_sub, map_pow, map_one,
      hζ.pow_eq_one, sub_self])
    (hunit _ (by
      rw [derivative_sub, derivative_C, sub_zero, derivative_X_pow, eval_mul, eval_C, eval_pow,
        eval_X, map_mul, map_pow, map_natCast]
      exact mul_ne_zero hn (pow_ne_zero _ (hζ.ne_zero hn0))))
  have hθa : θ a = θ a₀ := by
    rw [← sub_eq_zero, ← map_sub]
    exact hsub
  refine ⟨a, ⟨?_, fun l hl ↦ hζ.dvd_of_pow_eq_one l ?_⟩, hθa⟩
  · rw [IsRoot, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at ha
    exact ha
  · rw [← hθa, ← map_pow, hl, map_one]

/-- **`μ_n ⊆ k` gives `μ_n ⊆ K`** for any `O`-algebra `K` with injective structure map. -/
theorem exists_isPrimitiveRoot_of_residue (hθ : Function.Surjective θ) {n : ℕ}
    (hn : (n : k) ≠ 0) {ζ₀ : k} (hζ : IsPrimitiveRoot ζ₀ n) (K : Type*) [CommRing K]
    [Algebra O K] (hinj : Function.Injective (algebraMap O K)) :
    ∃ ζ : K, IsPrimitiveRoot ζ n := by
  obtain ⟨ζ, hζ', -⟩ := exists_isPrimitiveRoot_lift θ hθ hn hζ
  exact ⟨_, hζ'.map_of_injective hinj⟩

end HenselRoots

end SemistableReduction
