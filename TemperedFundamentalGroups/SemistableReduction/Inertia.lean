/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Unramified

/-!
# The inertia group of a Galois extension of valued fields

Blueprint §9.4, D1–D3. Let `N / M` be a finite extension, `u` a valuation on `M` extended by `w`
on `N`, and suppose that every `M`-automorphism of `N` preserves `w` (`hσ`; this holds if `M` is
complete of rank one, `UniqueExtension.valuation_algEquiv_apply'`). We write `κ_u`, `κ_w` for the
residue fields and `G = Aut(N / M)`.

* D1: `G` acts on the valuation ring of `w` (`galAction`), hence on `κ_w`
  (`residueHom : G →* Aut(κ_w / κ_u)`); the *inertia group* `inertia u hσ` is its kernel, the
  `σ` with `w (σ x - x) < 1` for all `x` in the valuation ring (`mem_inertia_iff`). If `N / M` is
  Galois, `residueHom` is surjective (`residueHom_surjective`) and `κ_w / κ_u` is normal
  (`normal_residueField`), via Mathlib's `Ideal.Quotient.stabilizerHom_surjective`.
* D2: if the value group of `M` is divisible and `M` contains a primitive `ℓ`-th root of unity for
  every prime `ℓ` invertible in `κ_u`, then the inertia group is a `p`-group,
  `p = ringChar κ_u` (`isPGroup_inertia`). An element `σ` of prime order `ℓ ≠ p` has an eigenvector
  `σ θ = ζ θ` with `w θ = 1` (divisibility), and `σ ∈ T` forces `ζ̄ = 1`, contradicting
  `1 + ζ + ⋯ + ζ^(ℓ-1) = 0`, `ℓ ≠ 0` in `κ_u`.
* D3: for `N / M` Galois and `K = N^T` the fixed field of the inertia group, `κ_w / κ_K` is purely
  inseparable (`isPurelyInseparable_residueField_fixedField`) and `K / M` is unramified:
  `e(K | M) = 1`, `f(K | M) = [K : M]`, `κ_K / κ_u` separable (`unramified_fixedField_inertia`).
-/

open IsLocalRing Valuation Polynomial
open scoped Pointwise

namespace SemistableReduction

namespace FundamentalInequality

variable {M N : Type*} [Field M] [Field N] [Algebra M N]
  {Γ₀ Γ₁ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {u : Valuation M Γ₀} {w : Valuation N Γ₁} [u.HasExtension w]

local notation "O_u" => u.valuationSubring
local notation "O_w" => w.valuationSubring
local notation "κ_u" => ResidueField u.valuationSubring
local notation "κ_w" => ResidueField w.valuationSubring

section Action

variable (hσ : ∀ (σ : N ≃ₐ[M] N) (x : N), w (σ x) = w x)

/-- An `M`-automorphism preserving `w` maps the valuation ring to itself. -/
def galSMul (σ : N ≃ₐ[M] N) (x : O_w) : O_w :=
  ⟨σ x, by rw [mem_valuationSubring_iff, hσ]; exact x.2⟩

/-- **D1.** The action of `Aut(N / M)` on the valuation ring of `w`. -/
@[reducible]
def galAction : MulSemiringAction (N ≃ₐ[M] N) O_w where
  smul := galSMul hσ
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero σ := Subtype.ext (by exact map_zero σ)
  smul_add σ x y := Subtype.ext (by exact map_add σ (x : N) y)
  smul_one σ := Subtype.ext (by exact map_one σ)
  smul_mul σ x y := Subtype.ext (by exact map_mul σ (x : N) y)

lemma coe_galAction_smul (σ : N ≃ₐ[M] N) (x : O_w) :
    letI := galAction hσ
    ((σ • x : O_w) : N) = σ x :=
  rfl

lemma galAction_smulCommClass :
    letI := galAction hσ
    SMulCommClass (N ≃ₐ[M] N) O_u O_w := by
  letI := galAction hσ
  refine ⟨fun σ a x ↦ Subtype.ext ?_⟩
  rw [Algebra.smul_def, Algebra.smul_def]
  change σ ((algebraMap O_u O_w a * x : O_w) : N) = ((algebraMap O_u O_w a : O_w) : N) * σ x
  push_cast
  rw [HasExtension.coe_algebraMap_valuationSubring_eq, map_mul, AlgEquiv.commutes]

lemma galAction_mem_stabilizer (σ : N ≃ₐ[M] N) :
    letI := galAction hσ
    σ ∈ MulAction.stabilizer (N ≃ₐ[M] N) (maximalIdeal O_w) := by
  letI := galAction hσ
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_eq_comap]
  ext x
  rw [Ideal.mem_comap, Valuation.mem_maximalIdeal_iff, Valuation.mem_maximalIdeal_iff]
  change w (σ⁻¹ x) < 1 ↔ _
  rw [hσ]

variable (u) in
/-- **D1.** The action of `Aut(N / M)` on the residue field `κ_w`. -/
noncomputable def residueHom : (N ≃ₐ[M] N) →* (κ_w ≃ₐ[κ_u] κ_w) :=
  letI := galAction hσ
  letI := galAction_smulCommClass (u := u) hσ
  (Ideal.Quotient.stabilizerHom (maximalIdeal O_w) (maximalIdeal O_u) (N ≃ₐ[M] N)).comp
    ((MonoidHom.id _).codRestrict _ (galAction_mem_stabilizer hσ))

lemma residueHom_residue (σ : N ≃ₐ[M] N) (x : O_w) :
    residueHom u hσ σ (residue O_w x) = residue O_w (galSMul hσ σ x) :=
  rfl

variable (u) in
/-- **D1.** The inertia group: the kernel of the action on the residue field. -/
noncomputable def inertia : Subgroup (N ≃ₐ[M] N) :=
  (residueHom u hσ).ker

/-- `σ` is in the inertia group iff `w (σ x - x) < 1` for all `x` in the valuation ring. -/
theorem mem_inertia_iff (σ : N ≃ₐ[M] N) :
    σ ∈ inertia u hσ ↔ ∀ x : N, w x ≤ 1 → w (σ x - x) < 1 := by
  rw [inertia, MonoidHom.mem_ker, AlgEquiv.ext_iff]
  constructor
  · intro h x hx
    have := h (residue O_w ⟨x, hx⟩)
    rw [residueHom_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← _root_.map_sub,
      residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff] at this
    exact this
  · intro h x
    obtain ⟨x, rfl⟩ := residue_surjective x
    rw [residueHom_residue, AlgEquiv.one_apply, ← sub_eq_zero, ← _root_.map_sub,
      residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact h x x.2

variable [FiniteDimensional M N] [IsGalois M N]

lemma galAction_isInvariant :
    letI := galAction hσ
    Algebra.IsInvariant O_u O_w (N ≃ₐ[M] N) := by
  letI := galAction hσ
  refine ⟨fun b hb ↦ ?_⟩
  have hfix : ∀ f : N ≃ₐ[M] N, f (b : N) = b := fun f ↦ congrArg Subtype.val (hb f)
  obtain ⟨a, ha⟩ := (IsGalois.mem_bot_iff_fixed (F := M) (b : N)).2 hfix
  replace ha : algebraMap M N a = b := ha
  refine ⟨⟨a, ?_⟩, Subtype.ext ?_⟩
  · rw [mem_valuationSubring_iff, ← HasExtension.val_map_le_one_iff (vR := u) (vA := w), ha]
    exact b.2
  · exact ha

/-- **D1.** For `N / M` Galois, `Aut(N / M) → Aut(κ_w / κ_u)` is surjective. -/
theorem residueHom_surjective : Function.Surjective (residueHom u hσ) := by
  letI := galAction hσ
  haveI := galAction_smulCommClass (u := u) hσ
  haveI := galAction_isInvariant (u := u) hσ
  have key := Ideal.Quotient.stabilizerHom_surjective (N ≃ₐ[M] N) (maximalIdeal O_u)
    (maximalIdeal O_w)
  intro f
  obtain ⟨g, hg⟩ := key f
  refine ⟨g.1, AlgEquiv.ext fun x ↦ ?_⟩
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [residueHom_residue, ← hg]
  rfl

include hσ in
/-- **D1.** For `N / M` Galois, the residue field extension `κ_w / κ_u` is normal. -/
theorem normal_residueField : Normal κ_u κ_w := by
  letI := galAction hσ
  haveI := galAction_smulCommClass (u := u) hσ
  haveI := galAction_isInvariant (u := u) hσ
  have key := Ideal.Quotient.normal (N ≃ₐ[M] N) (maximalIdeal O_u) (maximalIdeal O_w)
  exact key

end Action

end FundamentalInequality

end SemistableReduction
