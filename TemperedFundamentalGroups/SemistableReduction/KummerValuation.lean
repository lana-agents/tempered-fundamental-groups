/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.GaloisReduction

/-!
# Valuations on Kummer extensions

Let `M` be a field, `ℓ` a prime, `π ∈ M` nonzero and `α` an element of an extension field with
`α ^ ℓ = π`. Let `U` be a valuation subring of `M` satisfying the **Kummer condition**: for every
`β ≠ 0` in `M`, `π / β ^ ℓ` is not a unit of `U`, i.e. `U.valuation (π / β ^ ℓ) ≠ 1`.

* `mem_iff_forall`: for a valuation subring `W` of `L ⊇ M` over `U`, an element
  `∑_{i < ℓ} aᵢ αⁱ` lies in `W` iff `aᵢ ^ ℓ πⁱ ∈ U` for all `i`. Indeed, the values of the terms
  satisfy `W(aᵢ αⁱ) ^ ℓ = U(aᵢ ^ ℓ πⁱ)`, and two nonzero terms have distinct values (otherwise
  `π ^ d` would be an `ℓ`-th power up to a unit for some `0 < d < ℓ`, and Bezout makes `π` an
  `ℓ`-th power up to a unit), so the value of the sum is the maximum of the values of the terms.
* `eq_of_comap_eq` (**uniqueness**): if `E = M(α)`, then `U` has at most one extension to `E`;
  `mem_iff_mem_of_comap_eq` is the version for elements of `M[α]` inside a larger field.
  `notMem_range`: `α ∉ M`.
* `kummer_of_le`, `kummer_of_isDiscreteValuationRing`: the Kummer condition passes to smaller
  valuation subrings, and holds for a discrete valuation ring in which `π = u tⁿ` with `t` a
  uniformizer, `u` a unit and `0 < n < ℓ`.
* `exists_smul_eq_self_and_apply_ne` (**orbit argument**): for `L / M` finite Galois, `α ∈ E ⊆ L`
  with `α ∉ M`, and a valuation subring `W` of `L` whose restriction to `E` is determined by its
  restriction to `M`, some `σ ∈ Gal(L / M)` stabilizes `W` and moves `α`.
* `exists_smul_eq_self_and_apply_ne_of_pow_eq`: the combination, for a Kummer element `α ∈ L`.
-/

open Polynomial
open scoped Pointwise

namespace SemistableReduction

namespace KummerValuation

section Core

variable {M L : Type*} [Field M] [Field L] [Algebra M L]

/-- On elements of `M`, a valuation subring of `L` compares values like its restriction. -/
lemma valuation_algebraMap_le_iff (W : ValuationSubring L) (a b : M) :
    W.valuation (algebraMap M L a) ≤ W.valuation (algebraMap M L b) ↔
      (W.comap (algebraMap M L)).valuation a ≤ (W.comap (algebraMap M L)).valuation b := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hb₁ : 0 < W.valuation (algebraMap M L b) :=
    (Valuation.pos_iff _).2 ((_root_.map_ne_zero _).2 hb)
  have hb₂ : 0 < (W.comap (algebraMap M L)).valuation b := (Valuation.pos_iff _).2 hb
  rw [← div_le_one₀ hb₁, ← div_le_one₀ hb₂, ← map_div₀, ← map_div₀, ← map_div₀,
    ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_comap]

lemma valuation_algebraMap_eq_iff (W : ValuationSubring L) (a b : M) :
    W.valuation (algebraMap M L a) = W.valuation (algebraMap M L b) ↔
      (W.comap (algebraMap M L)).valuation a = (W.comap (algebraMap M L)).valuation b := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_algebraMap_le_iff,
    valuation_algebraMap_le_iff]

variable {ℓ : ℕ} {π : M}

/-- Under the Kummer condition, no power `π ^ d` with `0 < d < ℓ` has the value of an `ℓ`-th
power (Bezout). -/
lemma valuation_pow_ne (hℓ : ℓ.Prime) (hπ0 : π ≠ 0) {U : ValuationSubring M}
    (hK : ∀ β : M, β ≠ 0 → U.valuation (π / β ^ ℓ) ≠ 1) (c : M) {d : ℕ} (hd0 : 0 < d)
    (hdℓ : d < ℓ) : U.valuation c ^ ℓ ≠ U.valuation π ^ d := by
  intro h
  have hvπ : U.valuation π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
  have hc : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow hℓ.ne_zero] at h
    exact pow_ne_zero d hvπ h.symm
  have hcop : Nat.Coprime d ℓ :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hℓ).2
      (Nat.not_dvd_of_pos_of_lt hd0 hdℓ)))
  obtain ⟨s, -, hs⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hℓ.one_lt
  set t := d * s / ℓ
  have hds : d * s = ℓ * t + 1 := by
    have := Nat.div_add_mod (d * s) ℓ
    rw [hs] at this
    exact this.symm
  have hβ : c ^ s / π ^ t ≠ 0 := div_ne_zero (pow_ne_zero _ hc) (pow_ne_zero _ hπ0)
  apply hK _ hβ
  have e : π / (c ^ s / π ^ t) ^ ℓ = π ^ (ℓ * t + 1) / (c ^ ℓ) ^ s := by
    rw [div_pow, div_div_eq_mul_div]
    ring
  rw [e, map_div₀, map_pow, map_pow, map_pow, h, ← pow_mul, hds,
    div_self (pow_ne_zero _ hvπ)]

variable {α : L}

/-- **Kummer valuations.** If `α ^ ℓ = π` and the restriction `U` of `W` to `M` satisfies the
Kummer condition, then `∑_{i < ℓ} aᵢ αⁱ ∈ W` iff `aᵢ ^ ℓ πⁱ ∈ U` for all `i < ℓ`. -/
theorem mem_iff_forall (hℓ : ℓ.Prime) (hα : α ^ ℓ = algebraMap M L π) (hπ0 : π ≠ 0)
    {U : ValuationSubring M} (hK : ∀ β : M, β ≠ 0 → U.valuation (π / β ^ ℓ) ≠ 1)
    {W : ValuationSubring L} (hW : W.comap (algebraMap M L) = U) (a : ℕ → M) :
    ∑ i ∈ Finset.range ℓ, algebraMap M L (a i) * α ^ i ∈ W ↔ ∀ i < ℓ, a i ^ ℓ * π ^ i ∈ U := by
  classical
  set f : ℕ → L := fun i ↦ algebraMap M L (a i) * α ^ i with hf
  have hpow : ∀ i, W.valuation (f i) ^ ℓ = W.valuation (algebraMap M L (a i ^ ℓ * π ^ i)) := by
    intro i
    rw [← map_pow, hf, mul_pow, ← pow_mul, mul_comm i ℓ, pow_mul, hα, ← map_pow, ← map_pow,
      ← map_mul]
  have hterm : ∀ i, f i ∈ W ↔ a i ^ ℓ * π ^ i ∈ U := by
    intro i
    rw [← W.valuation_le_one_iff, ← pow_le_one_iff hℓ.ne_zero, hpow, W.valuation_le_one_iff,
      ← hW, ValuationSubring.mem_comap]
  -- two distinct terms with equal values vanish
  have hlt : ∀ i j, i < j → j < ℓ → W.valuation (f i) = W.valuation (f j) →
      W.valuation (f j) = 0 := by
    intro i j hij hjℓ he
    by_contra hne
    have haj : a j ≠ 0 := by
      rintro haj
      apply hne
      simp [hf, haj]
    have he' := congrArg (· ^ ℓ) he
    simp only [hpow] at he'
    rw [valuation_algebraMap_eq_iff, hW, map_mul, map_mul, map_pow, map_pow, map_pow,
      map_pow] at he'
    have hvπ : U.valuation π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
    have hvaj : U.valuation (a j) ^ ℓ ≠ 0 :=
      pow_ne_zero _ ((Valuation.ne_zero_iff _).2 haj)
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    apply valuation_pow_ne hℓ hπ0 hK (a i / a (i + d + 1)) (Nat.succ_pos d) (by omega)
    rw [map_div₀, div_pow, div_eq_iff hvaj]
    apply mul_right_cancel₀ (pow_ne_zero i hvπ)
    rw [he', add_assoc, pow_add]
    ac_rfl
  have hdist : ∀ i < ℓ, ∀ j < ℓ, i ≠ j → W.valuation (f i) = W.valuation (f j) →
      W.valuation (f j) = 0 := by
    intro i hi j hj hij he
    rcases lt_or_gt_of_ne hij with h | h
    · exact hlt i j h hj he
    · rw [← he]
      exact hlt j i h hi he.symm
  constructor
  · intro hx i hi
    rw [← hterm]
    obtain ⟨j, hj, hjmax⟩ := Finset.exists_max_image (Finset.range ℓ) (fun i ↦ W.valuation (f i))
      ⟨0, Finset.mem_range.2 hℓ.pos⟩
    rw [← W.valuation_le_one_iff]
    refine (hjmax i (Finset.mem_range.2 hi)).trans ?_
    rcases eq_or_ne (W.valuation (f j)) 0 with h0 | h0
    · rw [h0]
      exact zero_le
    have hsum : W.valuation (∑ i ∈ Finset.range ℓ, f i) = W.valuation (f j) := by
      refine Valuation.map_sum_eq_of_lt _ hj fun k hk ↦ ?_
      rw [Finset.mem_sdiff, Finset.mem_singleton] at hk
      exact lt_of_le_of_ne (hjmax k hk.1) fun he ↦
        h0 (hdist k (Finset.mem_range.1 hk.1) j (Finset.mem_range.1 hj) hk.2 he)
    rw [← hsum]
    exact (W.valuation_le_one_iff _).2 hx
  · intro h
    exact sum_mem fun i hi ↦ (hterm i).2 (h i (Finset.mem_range.1 hi))

/-- Every element of `M[α]` is `∑_{i < ℓ} aᵢ αⁱ` (division by `X ^ ℓ - π`). -/
lemma exists_eq_sum (hℓ : ℓ.Prime) (hα : α ^ ℓ = algebraMap M L π) {x : L}
    (hx : x ∈ Algebra.adjoin M {α}) :
    ∃ a : ℕ → M, x = ∑ i ∈ Finset.range ℓ, algebraMap M L (a i) * α ^ i := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, rfl⟩ := hx
  have hq : (X ^ ℓ - C π).Monic := monic_X_pow_sub_C π hℓ.ne_zero
  have hdeg : (X ^ ℓ - C π).natDegree = ℓ := natDegree_X_pow_sub_C
  have hq1 : X ^ ℓ - C π ≠ 1 := by
    intro h
    rw [h, natDegree_one] at hdeg
    exact hℓ.ne_zero hdeg.symm
  have hroot : aeval α (X ^ ℓ - C π) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hα, sub_self]
  have hlt : (p %ₘ (X ^ ℓ - C π)).natDegree < ℓ := by
    have := natDegree_modByMonic_lt p hq hq1
    rwa [hdeg] at this
  refine ⟨(p %ₘ (X ^ ℓ - C π)).coeff, ?_⟩
  change aeval α p = _
  rw [← aeval_modByMonic_eq_self_of_root hroot, aeval_eq_sum_range' hlt]
  simp_rw [Algebra.smul_def]

lemma isIntegral_of_pow_eq (hℓ : ℓ.Prime) (hα : α ^ ℓ = algebraMap M L π) : IsIntegral M α :=
  ⟨X ^ ℓ - C π, monic_X_pow_sub_C π hℓ.ne_zero, by
    rw [← aeval_def, map_sub, map_pow, aeval_X, aeval_C, hα, sub_self]⟩

/-- **Kummer uniqueness on `M[α]`.** Two valuation subrings of `L` with the same Kummer
restriction to `M` contain the same elements of `M[α]`. -/
theorem mem_iff_mem_of_comap_eq (hℓ : ℓ.Prime) (hα : α ^ ℓ = algebraMap M L π) (hπ0 : π ≠ 0)
    {U : ValuationSubring M} (hK : ∀ β : M, β ≠ 0 → U.valuation (π / β ^ ℓ) ≠ 1)
    {W₁ W₂ : ValuationSubring L} (h₁ : W₁.comap (algebraMap M L) = U)
    (h₂ : W₂.comap (algebraMap M L) = U) {x : L} (hx : x ∈ Algebra.adjoin M {α}) :
    x ∈ W₁ ↔ x ∈ W₂ := by
  obtain ⟨a, rfl⟩ := exists_eq_sum hℓ hα hx
  rw [mem_iff_forall hℓ hα hπ0 hK h₁, mem_iff_forall hℓ hα hπ0 hK h₂]

/-- **P1 (Kummer uniqueness).** If `E = M(α)` with `α ^ ℓ = π` and `U` satisfies the Kummer
condition, then `U` has at most one extension to `E`. -/
theorem eq_of_comap_eq (hℓ : ℓ.Prime) (hα : α ^ ℓ = algebraMap M L π) (hπ0 : π ≠ 0)
    (hgen : IntermediateField.adjoin M {α} = ⊤) {U : ValuationSubring M}
    (hK : ∀ β : M, β ≠ 0 → U.valuation (π / β ^ ℓ) ≠ 1) {W₁ W₂ : ValuationSubring L}
    (h₁ : W₁.comap (algebraMap M L) = U) (h₂ : W₂.comap (algebraMap M L) = U) : W₁ = W₂ := by
  ext x
  have hx : x ∈ (IntermediateField.adjoin M {α}).toSubalgebra := by
    rw [hgen]
    trivial
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    (isIntegral_of_pow_eq hℓ hα).isAlgebraic]
    at hx
  exact mem_iff_mem_of_comap_eq hℓ hα hπ0 hK h₁ h₂ hx

/-- Under the Kummer condition (for any valuation subring), `α ∉ M`. -/
theorem notMem_range (hα : α ^ ℓ = algebraMap M L π) (hπ0 : π ≠ 0) {U : ValuationSubring M}
    (hK : ∀ β : M, β ≠ 0 → U.valuation (π / β ^ ℓ) ≠ 1) :
    α ∉ Set.range (algebraMap M L) := by
  rintro ⟨b, rfl⟩
  rw [← map_pow] at hα
  have hb := (algebraMap M L).injective hα
  have hb0 : b ≠ 0 := by
    rintro rfl
    rcases Nat.eq_zero_or_pos ℓ with hℓ | hℓ
    · exact hK 1 one_ne_zero (by rw [hℓ, pow_zero, div_one, ← hb, hℓ, pow_zero, map_one])
    · exact hπ0 (by rw [← hb, zero_pow hℓ.ne'])
  exact hK b hb0 (by rw [← hb, div_self (pow_ne_zero _ hb0), map_one])

end Core

/-! ### Sufficient conditions for the Kummer condition -/

section Sufficient

variable {M : Type*} [Field M] {ℓ : ℕ} {π : M}

/-- **P1' (a).** The Kummer condition passes to smaller valuation subrings. -/
theorem kummer_of_le {U V : ValuationSubring M} (hUV : U ≤ V)
    (hK : ∀ β : M, β ≠ 0 → V.valuation (π / β ^ ℓ) ≠ 1) :
    ∀ β : M, β ≠ 0 → U.valuation (π / β ^ ℓ) ≠ 1 := by
  intro β hβ h
  apply hK β hβ
  rw [valuation_eq_one_iff_mem_and_inv_mem] at h ⊢
  exact ⟨h.1, hUV h.2.1, hUV h.2.2⟩

/-- **P1' (b).** In a discrete valuation ring `V`, if `π = u tⁿ` with `t` a uniformizer, `u` a
unit and `0 < n < ℓ`, then `π / β ^ ℓ` is never a unit. -/
theorem kummer_of_isDiscreteValuationRing {V : ValuationSubring M}
    [IsDiscreteValuationRing V] {t : V} (ht : Irreducible t) (u : Vˣ) {n : ℕ} (hn0 : 0 < n)
    (hnℓ : n < ℓ) (hπ : π = ((u * t ^ n : V) : M)) :
    ∀ β : M, β ≠ 0 → V.valuation (π / β ^ ℓ) ≠ 1 := by
  intro β hβ h
  have hmem : π / β ^ ℓ ∈ V := (V.valuation_le_one_iff _).1 h.le
  obtain ⟨w, hw⟩ := (V.valuation_eq_one_iff ⟨π / β ^ ℓ, hmem⟩).2 h
  rcases V.mem_or_inv_mem β with hb | hb
  · have hb0 : (⟨β, hb⟩ : V) ≠ 0 := fun h0 ↦ hβ (congrArg Subtype.val h0)
    obtain ⟨k, u', hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 ht
    have e : (u * t ^ n : V) = w * (⟨β, hb⟩ : V) ^ ℓ := by
      rw [hw]
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [div_mul_cancel₀ _ (pow_ne_zero _ hβ), hπ]
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [hk, mul_pow, ← pow_mul, ← mul_assoc] at e
    have hnk := IsDiscreteValuationRing.unit_mul_pow_congr_pow ht ht u (w * u' ^ ℓ) n (k * ℓ)
      (by rw [e]; push_cast; ring)
    exact Nat.not_dvd_of_pos_of_lt hn0 hnℓ ⟨k, by rw [hnk, mul_comm]⟩
  · have hb0 : (⟨β⁻¹, hb⟩ : V) ≠ 0 := fun h0 ↦ inv_ne_zero hβ (congrArg Subtype.val h0)
    obtain ⟨k, u', hk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 ht
    have e : (u * t ^ n : V) * (⟨β⁻¹, hb⟩ : V) ^ ℓ = w := by
      rw [hw]
      apply Subtype.ext
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
      rw [hπ, inv_pow, div_eq_mul_inv]
      simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow]
    rw [hk, mul_pow, ← pow_mul] at e
    have hnk := IsDiscreteValuationRing.unit_mul_pow_congr_pow ht ht (u * u' ^ ℓ) w
      (n + k * ℓ) 0 (by rw [pow_zero, mul_one, ← e]; push_cast; ring)
    omega

end Sufficient

/-! ### The orbit argument -/

section Orbit

variable {M L : Type*} [Field M] [Field L] [Algebra M L]

/-- Automorphisms over `M` do not change the restriction to `M`. -/
lemma comap_smul_eq (σ : L ≃ₐ[M] L) (W : ValuationSubring L) :
    (σ • W).comap (algebraMap M L) = W.comap (algebraMap M L) := by
  ext a
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    AlgEquiv.smul_def, AlgEquiv.commutes, ← ValuationSubring.mem_comap]

variable [FiniteDimensional M L] [IsGalois M L]

/-- **P2 (orbit argument).** Let `L / M` be finite Galois, `α ∈ E ⊆ L` with `α ∉ M`, and `W` a
valuation subring of `L` such that every valuation subring with the same restriction to `M`
has the same restriction to `E`. Then some `σ ∈ Gal(L / M)` stabilizes `W` and moves `α`. -/
theorem exists_smul_eq_self_and_apply_ne (E : IntermediateField M L) {α : L} (hαE : α ∈ E)
    (hα : α ∉ (⊥ : IntermediateField M L)) (W : ValuationSubring L)
    (hW : ∀ W' : ValuationSubring L, W'.comap (algebraMap M L) = W.comap (algebraMap M L) →
      W'.comap (algebraMap E L) = W.comap (algebraMap E L)) :
    ∃ σ : L ≃ₐ[M] L, σ • W = W ∧ σ α ≠ α := by
  rw [IsGalois.mem_bot_iff_fixed] at hα
  obtain ⟨g, hg⟩ := not_forall.1 hα
  obtain ⟨h, hh⟩ := GaloisReduction.exists_smul_eq (F := E) W (g • W)
    (hW (g • W) (comap_smul_eq g W)).symm
  have hres : h.restrictScalars M • W = h • W := by
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
  refine ⟨g⁻¹ * h.restrictScalars M, ?_, ?_⟩
  · rw [mul_smul, hres, hh, inv_smul_smul]
  · rw [AlgEquiv.mul_apply, AlgEquiv.restrictScalars_apply]
    have hhα : h α = α := h.commutes ⟨α, hαE⟩
    rw [hhα]
    intro e
    apply hg
    calc g α = g (g⁻¹ α) := by rw [e]
      _ = α := by rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]

/-- **P1 + P2.** Let `L / M` be finite Galois, `ℓ` prime, `α ∈ L` with `α ^ ℓ = π ≠ 0`, and `W`
a valuation subring of `L` whose restriction to `M` satisfies the Kummer condition. Then some
`σ ∈ Gal(L / M)` stabilizes `W` and moves `α`. -/
theorem exists_smul_eq_self_and_apply_ne_of_pow_eq {ℓ : ℕ} {π : M} {α : L} (hℓ : ℓ.Prime)
    (hα : α ^ ℓ = algebraMap M L π) (hπ0 : π ≠ 0) (W : ValuationSubring L)
    (hK : ∀ β : M, β ≠ 0 → (W.comap (algebraMap M L)).valuation (π / β ^ ℓ) ≠ 1) :
    ∃ σ : L ≃ₐ[M] L, σ • W = W ∧ σ α ≠ α := by
  refine exists_smul_eq_self_and_apply_ne (IntermediateField.adjoin M {α})
    (IntermediateField.mem_adjoin_simple_self M α) ?_ W ?_
  · rw [IntermediateField.mem_bot]
    exact notMem_range hα hπ0 hK
  · intro W' hW'
    ext ⟨x, hx⟩
    have hx' : x ∈ Algebra.adjoin M {α} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (isIntegral_of_pow_eq hℓ hα).isAlgebraic]
      exact hx
    exact mem_iff_mem_of_comap_eq hℓ hα hπ0 hK hW' rfl hx'

end Orbit

end KummerValuation

end SemistableReduction
