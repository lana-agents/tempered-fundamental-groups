/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.UnramifiedBaseChange

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

section PGroup

variable (hσ : ∀ (σ : N ≃ₐ[M] N) (x : N), w (σ x) = w x) [FiniteDimensional M N]

/-- **D2, tame inertia is trivial.** If the value group of `M` is divisible, an element of the
inertia group cannot have prime order `ℓ` invertible in `κ_u` if `M` contains a primitive `ℓ`-th
root of unity. -/
theorem notMem_inertia_of_orderOf_eq_prime
    (hdiv : ∀ (c : M) (n : ℕ), 0 < n → ∃ d : M, u d ^ n = u c)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓκ : (ℓ : κ_u) ≠ 0) {ζ : M} (hζ : IsPrimitiveRoot ζ ℓ)
    (σ : N ≃ₐ[M] N) (hσℓ : orderOf σ = ℓ) : σ ∉ inertia u hσ := by
  intro hT
  -- an eigenvector `σ v = ζ v`
  have hroot : IsRoot (minpoly M σ.toLinearMap) ζ := by
    rw [minpoly_algEquiv_toLinearMap σ (isOfFinOrder_of_finite σ), hσℓ]
    simp [hζ.pow_eq_one]
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hσv : σ v = algebraMap M N ζ * v := by
    have := hv.apply_eq_smul
    rw [AlgEquiv.toLinearMap_apply, Algebra.smul_def] at this
    exact this
  -- normalize `v` to a unit `t`
  obtain ⟨n, hn, c, hc0, hc⟩ :=
    exists_pow_valuation_eq w (Algebra.IsIntegral.isIntegral (R := M) v) hv0
  obtain ⟨d, hd⟩ := hdiv c n hn
  have hd0 : d ≠ 0 := by
    rintro rfl
    rw [Valuation.map_zero, zero_pow hn.ne', eq_comm, Valuation.zero_iff] at hd
    exact hc0 hd
  have hwd : w v = w (algebraMap M N d) := by
    have h1 : w (algebraMap M N (d ^ n)) = w (algebraMap M N c) :=
      (HasExtension.val_map_eq_iff (vR := u) (vA := w) _ _).2 (by rw [map_pow, hd])
    rw [map_pow, map_pow] at h1
    exact (pow_left_inj hn.ne').1 (hc.trans h1.symm)
  have hd' : algebraMap M N d ≠ 0 := (_root_.map_ne_zero _).2 hd0
  set t := v / algebraMap M N d
  have ht : w t = 1 := by
    rw [map_div₀, hwd, div_self ((Valuation.ne_zero_iff w).2 hd')]
  have hσt : σ t - t = algebraMap M N (ζ - 1) * t := by
    rw [map_div₀, AlgEquiv.commutes, hσv, _root_.map_sub, map_one]
    ring
  -- `σ ∈ T` forces `ζ̄ = 1`
  have hζ1 : u (ζ - 1) < 1 := by
    have := (mem_inertia_iff hσ σ).1 hT t ht.le
    rw [hσt, map_mul, ht, mul_one] at this
    exact (HasExtension.val_map_lt_one_iff u w _).1 this
  have huζ : u ζ = 1 := by
    have : u ζ ^ ℓ = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    exact (pow_left_inj hℓ.ne_zero).1 (by rw [this, one_pow])
  set ζ' : O_u := ⟨ζ, le_of_eq huζ⟩
  have hres : residue O_u ζ' = 1 := by
    rw [← sub_eq_zero, ← map_one (residue O_u), ← _root_.map_sub, residue_eq_zero_iff,
      Valuation.mem_maximalIdeal_iff]
    exact hζ1
  have hsum : ∑ i ∈ Finset.range ℓ, ζ' ^ i = 0 := by
    apply Subtype.ext
    push_cast
    exact hζ.geom_sum_eq_zero hℓ.one_lt
  apply hℓκ
  have := congrArg (residue O_u) hsum
  simpa [map_sum, hres] using this

/-- **D2.** If the value group of `M` is divisible and `M` contains a primitive `ℓ`-th root of
unity for every prime `ℓ` invertible in `κ_u`, then the inertia group is a `p`-group,
`p = char κ_u` (the trivial group if `p = 0`). -/
theorem isPGroup_inertia (hdiv : ∀ (c : M) (n : ℕ), 0 < n → ∃ d : M, u d ^ n = u c)
    (hμ : ∀ ℓ : ℕ, ℓ.Prime → (ℓ : κ_u) ≠ 0 → ∃ ζ : M, IsPrimitiveRoot ζ ℓ) :
    IsPGroup (ringChar κ_u) (inertia u hσ) := by
  intro g
  set p := ringChar κ_u
  have hn0 : orderOf g ≠ 0 := (isOfFinOrder_of_finite g).orderOf_pos.ne'
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ orderOf g → ℓ = p := by
    intro ℓ hℓ hdvd
    by_cases hℓκ : (ℓ : κ_u) = 0
    · have hpℓ : p ∣ ℓ := (ringChar.spec κ_u ℓ).1 hℓκ
      rcases hℓ.eq_one_or_self_of_dvd p hpℓ with h | h
      · exact absurd h CharP.ringChar_ne_one
      · exact h.symm
    · exfalso
      obtain ⟨ζ, hζ⟩ := hμ ℓ hℓ hℓκ
      have hord : orderOf (g ^ (orderOf g / ℓ)) = ℓ := orderOf_pow_orderOf_div hn0 hdvd
      refine notMem_inertia_of_orderOf_eq_prime hσ hdiv hℓ hℓκ hζ
        ((g ^ (orderOf g / ℓ) : inertia u hσ) : N ≃ₐ[M] N) ?_ (g ^ (orderOf g / ℓ)).2
      rw [Subgroup.orderOf_coe, hord]
  by_cases h1 : orderOf g = 1
  · exact ⟨0, by rw [pow_zero, pow_one, ← orderOf_eq_one_iff, h1]⟩
  · obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd h1
    have hp : p.Prime := hprime ℓ hℓ hdvd ▸ hℓ
    refine ⟨(orderOf g).primeFactorsList.length, ?_⟩
    rw [← Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun hd hdvd ↦ hprime _ hd hdvd,
      pow_orderOf_eq_one]

end PGroup

/-- For a normal extension, the separable degree is the number of automorphisms. -/
lemma finSepDegree_eq_card_algEquiv (F E : Type*) [Field F] [Field E] [Algebra F E]
    [Normal F E] : Field.finSepDegree F E = Nat.card (E ≃ₐ[F] E) :=
  Nat.card_congr (Normal.algHomEquivAut F (AlgebraicClosure E) E)

section FixedField

variable (hσ : ∀ (σ : N ≃ₐ[M] N) (x : N), w (σ x) = w x) [FiniteDimensional M N] [IsGalois M N]

local notation "KT" => IntermediateField.fixedField (inertia u hσ)
local notation "wT" => w.comap (algebraMap (IntermediateField.fixedField (inertia u hσ)) N)

/-- **D3.** The residue field of `N` is purely inseparable over the residue field of the fixed
field `N^T` of the inertia group. -/
theorem isPurelyInseparable_residueField_fixedField :
    IsPurelyInseparable (ResidueField (wT).valuationSubring) κ_w := by
  have hσK : ∀ (τ : N ≃ₐ[KT] N) (x : N), w (τ x) = w x :=
    fun τ x ↦ hσ (τ.restrictScalars M) x
  have : Module.Finite (ResidueField (wT).valuationSubring) κ_w := finite_residueField
  have hnorm := normal_residueField (u := wT) hσK
  have htriv : ∀ f : κ_w ≃ₐ[ResidueField (wT).valuationSubring] κ_w, f = 1 := by
    intro f
    obtain ⟨τ, rfl⟩ := residueHom_surjective (u := wT) hσK f
    have hτ : τ.restrictScalars M ∈ inertia u hσ := by
      have hmem : τ.restrictScalars M ∈ (KT).fixingSubgroup := fun x ↦ τ.commutes x
      rwa [IntermediateField.fixingSubgroup_fixedField] at hmem
    refine AlgEquiv.ext fun x ↦ ?_
    obtain ⟨x, rfl⟩ := residue_surjective x
    have h := DFunLike.congr_fun ((MonoidHom.mem_ker).1 hτ) (residue O_w x)
    rw [residueHom_residue] at h
    rw [residueHom_residue, AlgEquiv.one_apply]
    exact h
  apply isPurelyInseparable_of_finSepDegree_eq_one
  rw [finSepDegree_eq_card_algEquiv, Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun f g ↦ (htriv f).trans (htriv g).symm⟩, ⟨1⟩⟩

/-- **D3.** The fixed field `K = N^T` of the inertia group is unramified over `M`:
`e(K | M) = 1`, `f(K | M) = [K : M]` and `κ_K / κ_u` is separable. -/
theorem unramified_fixedField_inertia :
    ramificationIdx M (wT) = 1 ∧ inertiaDeg u (wT) = Module.finrank M KT ∧
      Algebra.IsSeparable κ_u (ResidueField (wT).valuationSubring) := by
  have : Module.Finite κ_u (ResidueField (wT).valuationSubring) := finite_residueField
  have : Module.Finite κ_u κ_w := finite_residueField
  have hnorm := normal_residueField (u := u) hσ
  have hpi := isPurelyInseparable_residueField_fixedField (u := u) hσ
  have : IsScalarTower κ_u (ResidueField (wT).valuationSubring) κ_w :=
    isScalarTower_residueField u (wT) w
  -- `|Aut(κ_w / κ_u)| = [G : T] = [K : M]`
  have hcard : Nat.card (κ_w ≃ₐ[κ_u] κ_w) = Module.finrank M KT := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (inertia u hσ)
    have h2 : Nat.card ((N ≃ₐ[M] N) ⧸ inertia u hσ) = Nat.card (κ_w ≃ₐ[κ_u] κ_w) :=
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
        (residueHom_surjective (u := u) hσ)).toEquiv
    rw [h2, IsGalois.card_aut_eq_finrank,
      ← IntermediateField.finrank_fixedField_eq_card, ← Module.finrank_mul_finrank M KT N] at h1
    exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1).symm
  have hsep : Field.finSepDegree κ_u (ResidueField (wT).valuationSubring) =
      Module.finrank M KT := by
    rw [← hcard, ← finSepDegree_eq_card_algEquiv,
      ← Field.finSepDegree_mul_finSepDegree_of_isAlgebraic κ_u
        (ResidueField (wT).valuationSubring) κ_w,
      IsPurelyInseparable.finSepDegree_eq_one (ResidueField (wT).valuationSubring) κ_w, mul_one]
  have hle : Field.finSepDegree κ_u (ResidueField (wT).valuationSubring) ≤ inertiaDeg u (wT) :=
    Field.finSepDegree_le_finrank _ _
  have hef := ramificationIdx_mul_inertiaDeg_le (K := M) (v := u) (w := wT)
  have he := Nat.pos_of_ne_zero (ramificationIdx_ne_zero (K := M) (wT))
  have hf : inertiaDeg u (wT) = Module.finrank M KT :=
    le_antisymm ((Nat.le_mul_of_pos_left _ he).trans hef) (hsep ▸ hle)
  refine ⟨ramificationIdx_eq_one_of_inertiaDeg_eq hf, hf, ?_⟩
  rw [← Field.finSepDegree_eq_finrank_iff, hsep, ← hf]
  rfl

end FixedField

end FundamentalInequality

end SemistableReduction
