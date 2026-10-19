/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.PowFlat
import TemperedFundamentalGroups.SemistableReduction.NilpotentFlatness

/-!
# From `ϖ`-purity to flatness over `O/ϖⁿ` (Blueprint §12.8, M2.4, step 3f)

**`PowFlat.flat_quotient`**: for `(ϖ)` a maximal ideal of `O` and an `O`-module `M` killed by
`ϖⁿ` with `PowFlat ϖ n M`, the module `(O/ϖⁿ) ⊗_O M` is flat over `O/ϖⁿ` (the principal
nilpotent flatness criterion `NilpotentFlatness.flat_of_pow_succ_eq_zero`; the fibre over the
field `O/ϖ` is automatically flat).
-/

universe u v

open TensorProduct

namespace SemistableReduction

namespace PowFlat

variable {O : Type u} [CommRing O] {ϖ : O} {M : Type v} [AddCommGroup M] [Module O M]

/-- `(O/ϖⁿ) ⊗_O M ≃ M` for `M` killed by `ϖⁿ`. -/
noncomputable def quotTensorEquiv (n : ℕ) (hkill : ∀ m : M, ϖ ^ n • m = 0) :
    (O ⧸ Ideal.span {ϖ} ^ n) ⊗[O] M ≃ₗ[O] M :=
  (TensorProduct.quotTensorEquivQuotSMul M (Ideal.span {ϖ} ^ n)).trans
    (Submodule.quotEquivOfEqBot _ (by
      rw [eq_bot_iff, Ideal.span_singleton_pow]
      intro x hx
      refine Submodule.smul_induction_on hx (fun r hr m _ ↦ ?_) (fun a b ha hb ↦ ?_)
      · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
        rw [Submodule.mem_bot, mul_smul, hkill, smul_zero]
      · rw [Submodule.mem_bot] at ha hb ⊢
        rw [ha, hb, add_zero]))

/-- **`ϖ`-purity gives flatness over `O/ϖⁿ`**: for `(ϖ)` maximal and `M` killed by `ϖⁿ` with
`PowFlat ϖ n M`, the module `(O/ϖⁿ) ⊗_O M` is flat over `O/ϖⁿ`. -/
theorem flat_quotient [(Ideal.span {ϖ}).IsMaximal] (n : ℕ) (h : PowFlat ϖ n M)
    (hkill : ∀ m : M, ϖ ^ n • m = 0) :
    Module.Flat (O ⧸ Ideal.span {ϖ} ^ n) ((O ⧸ Ideal.span {ϖ} ^ n) ⊗[O] M) := by
  rcases n with _ | N
  · haveI : Subsingleton (O ⧸ Ideal.span {ϖ} ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      exact Ideal.Quotient.subsingleton_iff.mpr rfl
    haveI : Subsingleton ((O ⧸ Ideal.span {ϖ} ^ 0) ⊗[O] M) := Module.subsingleton
      (O ⧸ Ideal.span {ϖ} ^ 0) _
    infer_instance
  set S := O ⧸ Ideal.span {ϖ} ^ (N + 1)
  set w : S := Ideal.Quotient.mk _ ϖ
  set e := quotTensorEquiv (ϖ := ϖ) (M := M) (N + 1) hkill
  have he : ∀ (k : ℕ) (z : S ⊗[O] M), e (w ^ k • z) = ϖ ^ k • e z := by
    intro k z
    rw [← map_pow, ← Ideal.Quotient.algebraMap_eq, algebraMap_smul, map_smul]
  have hw : w ^ (N + 1) = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.span_singleton_pow]
    exact Ideal.mem_span_singleton_self _
  have hM : ∀ z : S ⊗[O] M, w • z = 0 → ∃ z', z = w ^ N • z' := by
    intro z hz
    obtain ⟨m', hm'⟩ := h 1 (by omega) (e z) (by
      have := he 1 z
      rw [pow_one, pow_one, hz, map_zero] at this
      rw [pow_one]; exact this.symm)
    refine ⟨e.symm m', e.injective ?_⟩
    rw [he, LinearEquiv.apply_symm_apply, hm', Nat.add_sub_cancel]
  -- the fibre over the field `S/(w)`
  have hmax : (Ideal.span {w}).IsMaximal := by
    have hc : Ideal.span {w} =
        (Ideal.span {ϖ}).map (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (N + 1))) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hc]
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      ‹(Ideal.span {ϖ}).IsMaximal›).resolve_left fun htop ↦ ?_
    have h1 := congrArg (Ideal.comap (Ideal.Quotient.mk (Ideal.span {ϖ} ^ (N + 1)))) htop
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, Ideal.comap_top,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
      sup_eq_left.mpr (Ideal.pow_le_self (Nat.succ_ne_zero N))] at h1
    exact (‹(Ideal.span {ϖ}).IsMaximal›).ne_top h1
  letI := Ideal.Quotient.field (Ideal.span {w})
  exact NilpotentFlatness.flat_of_pow_succ_eq_zero w N hw hM

end PowFlat

end SemistableReduction
