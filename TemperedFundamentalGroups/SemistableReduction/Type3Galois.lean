/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Kummer
import TemperedFundamentalGroups.SemistableReduction.LocalStability
import TemperedFundamentalGroups.SemistableReduction.GaloisReduction

/-!
# Local stability at type-3 points

Blueprint §9.10a (I.4). Let `M` be complete, the closure of `C(y)` with `‖y‖ ∉ |C^×|`, and `N / M`
finite.

* `exists_const_near_of_finite`: the residue field of `N` is that of `C` (every `w` with
  `‖w‖ = 1` is congruent to a constant);
* `exists_valueGen`: the values of `N` are `|C^×| · ‖z‖^ℤ` for some `z`;
* `exists_normal_index_prime`: a nontrivial Galois group `G` of `N / M` has a normal subgroup of
  prime index: `χ(σ) = res(σ z / z)` is a homomorphism to `k^×` whose kernel is a `p`-group (an
  eigenvector `σ v = ζ v` of an element of prime order `ℓ ≠ p` in the kernel gives `ζ̄ = 1`);
* **`ramificationIdx_eq_finrank`** (STAB3, local): `e(L | M) = [L : M]` and `f(L | M) = 1` for
  every finite `L / M` (induction along Kummer steps of prime degree, `kummer_step`).
-/

open Polynomial Finset

namespace SemistableReduction

namespace Type3

lemma one_le_multiset_prod (s : Multiset ℝ) (h : ∀ x ∈ s, 1 ≤ x) : 1 ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons]
    exact one_le_mul_of_one_le_of_one_le (h a (Multiset.mem_cons_self a s))
      (ih fun x hx ↦ h x (Multiset.mem_cons_of_mem hx))

section ValueGroup

open FundamentalInequality

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ]

/-- The `e`-th power of every value of `L` is a value of `K`. -/
lemma exists_pow_ramificationIdx_eq [FiniteDimensional K L] (w : Valuation L Γ) {x : L}
    (hx : x ≠ 0) :
    ∃ b : K, w x ^ ramificationIdx K w = w (algebraMap K L b) := by
  set H := valueGroup (w.comap (algebraMap K L))
  set G := valueGroup w
  set g : G := ⟨Units.mk0 (w x) ((Valuation.ne_zero_iff w).2 hx), valuation_mem_valueGroup w hx⟩
  set Hs := H.subgroupOf G
  have he : ramificationIdx K w = Nat.card (G ⧸ Hs) := rfl
  haveI : Finite (G ⧸ Hs) := Nat.finite_of_card_ne_zero (he ▸ ramificationIdx_ne_zero w)
  have h1 : (QuotientGroup.mk g : G ⧸ Hs) ^ ramificationIdx K w = 1 := by
    rw [he]; exact pow_card_eq_one'
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨b, hb⟩ := h1
  refine ⟨b, ?_⟩
  rw [← Valuation.comap_apply, hb]
  simp [g]

end ValueGroup

section Residue

variable {C M N : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M] [NormedAlgebra C M]
  [NormedField N] [IsUltrametricDist N] [NormedAlgebra C N] [NormedAlgebra M N]
  [IsScalarTower C M N] [FiniteDimensional M N]

omit [IsUltrametricDist C] in
/-- **The residue field of a finite extension of a type-3 field is that of `C`.** -/
theorem exists_const_near_of_finite {y : M} (hy : IsType3 C y) {w : N} (hw : ‖w‖ = 1) :
    ∃ μ : C, ‖w - algebraMap C N μ‖ < 1 := by
  classical
  have hint : IsIntegral M w := Algebra.IsIntegral.isIntegral w
  set P := minpoly M w
  have hmon : P.Monic := minpoly.monic hint
  have hcoeff : ∀ i, ‖P.coeff i‖ ≤ 1 := by
    have h1 : spectralNorm M N w = 1 := by rw [← NormedAlgebra.norm_eq_spectralNorm, hw]
    exact (spectralValue_le_one_iff hmon).1 (le_of_eq h1)
  have hl : ∀ i, ∃ l : C, ‖P.coeff i - algebraMap C M l‖ < 1 := by
    intro i
    rcases (hcoeff i).lt_or_eq with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨l, -, hl⟩ := exists_const_near hy h
      exact ⟨l, hl⟩
  choose l hl using hl
  set n := P.natDegree
  have hn : 0 < n := minpoly.natDegree_pos hint
  set Q : C[X] := X ^ n + ∑ i ∈ range n, Polynomial.C (l i) * X ^ i
  have hQmon : Q.Monic := by
    refine Polynomial.monic_X_pow_add ?_
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun i hi ↦ ?_
    refine (Polynomial.degree_C_mul_X_pow_le i (l i)).trans_lt ?_
    exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hi)
  have hQw : ‖aeval w Q‖ < 1 := by
    have hP0 : aeval w P = 0 := minpoly.aeval M w
    have hPexp : aeval w P = w ^ n + ∑ i ∈ range n, algebraMap M N (P.coeff i) * w ^ i := by
      conv_lhs => rw [hmon.as_sum]
      simp [aeval_def, eval₂_finsetSum]
      rfl
    have hQexp : aeval w Q = ∑ i ∈ range n,
        (algebraMap M N (algebraMap C M (l i) - P.coeff i)) * w ^ i := by
      rw [← sub_zero (aeval w Q), ← hP0, hPexp]
      simp only [Q, map_add, map_pow, aeval_X, map_sum, map_mul, aeval_C, map_sub,
        ← IsScalarTower.algebraMap_apply, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [hQexp]
    obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      ⟨0, Finset.mem_range.2 hn⟩
      (fun i ↦ (algebraMap M N (algebraMap C M (l i) - P.coeff i)) * w ^ i)
    refine hle.trans_lt ?_
    rw [norm_mul, norm_pow, hw, one_pow, mul_one, norm_algebraMap', norm_sub_rev]
    exact hl i
  have e := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits Q))
  rw [hQmon.leadingCoeff, Polynomial.C_1, one_mul] at e
  rw [← e, map_multiset_prod, Multiset.map_map] at hQw
  by_contra! hall
  have hge : 1 ≤ ‖(Multiset.map ((aeval w) ∘ fun a ↦ X - Polynomial.C a) Q.roots).prod‖ := by
    rw [← normHom_apply, map_multiset_prod, Multiset.map_map]
    refine one_le_multiset_prod _ ?_
    intro r hr
    obtain ⟨μ, -, rfl⟩ := Multiset.mem_map.1 hr
    simp only [Function.comp_apply, normHom_apply, map_sub, aeval_X, aeval_C]
    exact hall μ
  linarith

omit [IsUltrametricDist C] [CompleteSpace M] [NormedAlgebra C N] [IsScalarTower C M N] in
/-- **The value group of a finite extension is cyclic modulo `|C^×|`.** -/
theorem exists_valueGen {y : M} (hy : IsType3 C y) :
    ∃ z : N, z ≠ 0 ∧ ∀ v : N, v ≠ 0 → ∃ (c : C) (j : ℤ), ‖v‖ = ‖c‖ * ‖z‖ ^ j := by
  classical
  set w := NormedField.valuation (K := N)
  set e := FundamentalInequality.ramificationIdx M w
  have he0 : 0 < e := Nat.pos_of_ne_zero (FundamentalInequality.ramificationIdx_ne_zero w)
  have hy0 := hy.valTrans.norm_pos
  have hpow : ∀ v : N, v ≠ 0 → ∃ (c : C) (k : ℤ), c ≠ 0 ∧ ‖v‖ ^ e = ‖c‖ * ‖y‖ ^ k := by
    intro v hv
    obtain ⟨b, hb⟩ := exists_pow_ramificationIdx_eq (K := M) w hv
    have hb' : ‖v‖ ^ e = ‖b‖ := by
      have := congrArg (fun r : NNReal ↦ (r : ℝ)) hb
      simpa [w, NormedField.valuation_apply] using this
    have hb0 : b ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hb'
      exact (pow_pos (norm_pos_iff.2 hv) e).ne' hb'
    obtain ⟨c, k, hc, hck⟩ := exists_norm_eq hy hb0
    exact ⟨c, k, hc, hb'.trans hck⟩
  let S : AddSubgroup ℤ :=
    { carrier := {k | ∃ (v : N) (c : C), v ≠ 0 ∧ c ≠ 0 ∧ ‖v‖ ^ e = ‖c‖ * ‖y‖ ^ k}
      zero_mem' := ⟨1, 1, one_ne_zero, one_ne_zero, by simp⟩
      add_mem' := by
        rintro a b ⟨v, c, hv, hc, h⟩ ⟨v', c', hv', hc', h'⟩
        exact ⟨v * v', c * c', mul_ne_zero hv hv', mul_ne_zero hc hc', by
          rw [norm_mul, mul_pow, h, h', norm_mul, zpow_add₀ hy0.ne']; ring⟩
      neg_mem' := by
        rintro a ⟨v, c, hv, hc, h⟩
        exact ⟨v⁻¹, c⁻¹, inv_ne_zero hv, inv_ne_zero hc, by
          rw [norm_inv, inv_pow, h, norm_inv, zpow_neg, mul_inv]⟩ }
  obtain ⟨⟨d, hdS⟩, hgen⟩ := IsAddCyclic.exists_generator (α := S)
  obtain ⟨z, c₀, hz, hc₀, hzd⟩ := hdS
  refine ⟨z, hz, fun v hv ↦ ?_⟩
  obtain ⟨c, k, hc, hck⟩ := hpow v hv
  obtain ⟨t, ht⟩ := AddSubgroup.mem_zmultiples_iff.1 (hgen ⟨k, v, c, hv, hc, hck⟩)
  have htk : t * d = k := by
    have := congrArg Subtype.val ht
    simpa using this
  have key : (‖v‖ / ‖z‖ ^ t) ^ e = ‖c / c₀ ^ t‖ := by
    have hzt : (‖z‖ ^ t) ^ e = ‖c₀‖ ^ t * ‖y‖ ^ k := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hzd, mul_zpow,
        ← zpow_mul, mul_comm d t, htk]
    have hc₀t : 0 < ‖c₀‖ ^ t := zpow_pos (norm_pos_iff.2 hc₀) t
    rw [div_pow, hck, hzt, norm_div, norm_zpow]
    field_simp
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (c / c₀ ^ t) he0
  refine ⟨b, t, ?_⟩
  have hzt0 : 0 < ‖z‖ ^ t := zpow_pos (norm_pos_iff.2 hz) t
  have : ‖v‖ / ‖z‖ ^ t = ‖b‖ := by
    refine (pow_left_inj₀ (by positivity) (norm_nonneg b) he0.ne').1 ?_
    rw [key, ← norm_pow, hb]
  rwa [div_eq_iff hzt0.ne'] at this

end Residue

section Structure

variable {C M N : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [NontriviallyNormedField M] [IsUltrametricDist M] [CompleteSpace M] [NormedAlgebra C M]
  [NormedField N] [IsUltrametricDist N] [NormedAlgebra C N] [NormedAlgebra M N]
  [IsScalarTower C M N] [FiniteDimensional M N]

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

omit [IsAlgClosed C] in
/-- Elements of norm one have equal residues iff they are close. -/
lemma residue_eq_iff {a b : C} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) :
    IsLocalRing.residue (HenselComplete.integers C) ⟨a, (HenselComplete.mem_integers_iff a).2 ha⟩ =
      IsLocalRing.residue (HenselComplete.integers C) ⟨b, (HenselComplete.mem_integers_iff b).2 hb⟩
      ↔ ‖a - b‖ < 1 := by
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
  rfl

omit [IsAlgClosed C] in
lemma residue_ne_zero {a : C} (ha : ‖a‖ = 1) :
    IsLocalRing.residue (HenselComplete.integers C) ⟨a, (HenselComplete.mem_integers_iff a).2
      ha.le⟩ ≠ 0 := by
  rw [Ne, IsLocalRing.residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
  intro h
  change ‖a‖ < 1 at h
  linarith

/-- `M`-automorphisms of `N` are isometries. -/
lemma norm_algEquiv_apply (σ : N ≃ₐ[M] N) (x : N) : ‖σ x‖ = ‖x‖ := by
  have := UniqueExtension.valuation_algEquiv_apply (K := M) (NormedField.valuation (K := N)) σ x
  have := congrArg (fun r : NNReal ↦ (r : ℝ)) this
  simpa [NormedField.valuation_apply] using this

omit [CompleteSpace M] [IsUltrametricDist C] in
lemma norm_algEquiv_sub_lt [CompleteSpace M] {y : M} (hy : IsType3 C y) (σ : N ≃ₐ[M] N) {u : N}
    (hu : ‖u‖ = 1) : ‖σ u - u‖ < 1 := by
  obtain ⟨μ, hμ⟩ := exists_const_near_of_finite hy hu
  have hσμ : σ (algebraMap C N μ) = algebraMap C N μ := by
    rw [IsScalarTower.algebraMap_apply C M N, AlgEquiv.commutes]
  have h1 : ‖σ u - algebraMap C N μ‖ < 1 := by
    rw [← hσμ, ← map_sub, norm_algEquiv_apply]
    exact hμ
  rw [show σ u - u = (σ u - algebraMap C N μ) - (u - algebraMap C N μ) by ring]
  exact (norm_sub_le_max' _ _).trans_lt (max_lt h1 hμ)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **The tame part of the kernel is trivial**: an automorphism `τ` of prime order `ℓ ≠ p` with
`τ z ≡ z` cannot exist (eigenvector argument). -/
lemma false_of_orderOf_eq_prime {y : M} (hy : IsType3 C y) {z : N} (hz0 : z ≠ 0)
    (hzgen : ∀ v : N, v ≠ 0 → ∃ (c : C) (j : ℤ), ‖v‖ = ‖c‖ * ‖z‖ ^ j)
    (τ : N ≃ₐ[M] N) (hτz : ‖τ z / z - 1‖ < 1) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (hτℓ : orderOf τ = ℓ) : False := by
  haveI : NeZero (ℓ : C) := ⟨Nat.cast_ne_zero.2 hℓ.ne_zero⟩
  obtain ⟨ζC, hζC⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C ℓ
  set ζ := algebraMap C M ζC
  have hζ : IsPrimitiveRoot ζ ℓ := hζC.map_of_injective (algebraMap C M).injective
  have hroot : (minpoly M τ.toLinearMap).IsRoot ζ := by
    rw [minpoly_algEquiv_toLinearMap τ (isOfFinOrder_of_finite τ), hτℓ]
    simp [hζ.pow_eq_one]
  obtain ⟨v, hv⟩ := (Module.End.hasEigenvalue_of_isRoot hroot).exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hτv : τ v = algebraMap M N ζ * v := by
    have := hv.apply_eq_smul
    rw [AlgEquiv.toLinearMap_apply, Algebra.smul_def] at this
    exact this
  obtain ⟨c, j, hvn⟩ := hzgen v hv0
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [norm_zero, zero_mul] at hvn
    exact hv0 (norm_eq_zero.1 hvn)
  set r := τ z / z
  have hτz' : τ z = r * z := by simp only [r]; field_simp
  have hr0 : r ≠ 0 := by
    intro h0; rw [h0, zero_sub, norm_neg, norm_one] at hτz; exact lt_irrefl _ hτz
  set d : N := algebraMap C N c * z ^ j
  have hd0 : d ≠ 0 := mul_ne_zero ((_root_.map_ne_zero _).2 hc0) (zpow_ne_zero _ hz0)
  set u := v / d
  have hu : ‖u‖ = 1 := by
    simp only [u, d]
    rw [norm_div, norm_mul, norm_algebraMap', norm_zpow, ← hvn,
      div_self (norm_ne_zero_iff.2 hv0)]
  have hτd : τ d = d * r ^ j := by
    simp only [d]
    rw [map_mul, map_zpow₀, IsScalarTower.algebraMap_apply C M N, AlgEquiv.commutes, hτz',
      mul_zpow, ← IsScalarTower.algebraMap_apply]
    ring
  have hτu : τ u = algebraMap M N ζ * u * (r ^ j)⁻¹ := by
    simp only [u]
    rw [map_div₀, hτv, hτd]
    field_simp
  have h1 := norm_algEquiv_sub_lt hy τ hu
  rw [hτu] at h1
  have h2 : ‖algebraMap M N ζ * (r ^ j)⁻¹ - 1‖ < 1 := by
    have : algebraMap M N ζ * u * (r ^ j)⁻¹ - u = u * (algebraMap M N ζ * (r ^ j)⁻¹ - 1) := by
      ring
    rwa [this, norm_mul, hu, one_mul] at h1
  have h3 : ‖(r ^ j)⁻¹ - 1‖ < 1 := by
    rw [← zpow_neg]
    exact (norm_zpow_sub_one_le le_rfl hτz _).trans_lt hτz
  have hζn : ‖algebraMap M N ζ‖ = 1 := by
    have : ‖ζC‖ = 1 := by
      have h := congrArg norm hζC.pow_eq_one
      rw [norm_pow, norm_one] at h
      exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hℓ.ne_zero).1 h
    rw [norm_algebraMap', norm_algebraMap', this]
  have h4 : ‖ζC - 1‖ < 1 := by
    have e : algebraMap M N ζ - 1 =
        (algebraMap M N ζ * (r ^ j)⁻¹ - 1) - algebraMap M N ζ * ((r ^ j)⁻¹ - 1) := by ring
    have h5 : ‖algebraMap M N ζ * ((r ^ j)⁻¹ - 1)‖ < 1 := by rw [norm_mul, hζn, one_mul]; exact h3
    have := (norm_sub_le_max' (algebraMap M N ζ * (r ^ j)⁻¹ - 1)
      (algebraMap M N ζ * ((r ^ j)⁻¹ - 1))).trans_lt (max_lt h2 h5)
    rw [← e, ← map_one (algebraMap M N), ← map_sub, norm_algebraMap', ← map_one (algebraMap C M),
      ← map_sub, norm_algebraMap'] at this
    exact this
  -- `Σ ζ^i = 0` forces `‖ℓ‖ < 1`
  have hsum : ∑ i ∈ range ℓ, (ζC ^ i - 1) = -(ℓ : C) := by
    rw [Finset.sum_sub_distrib, hζC.geom_sum_eq_zero hℓ.one_lt]
    simp
  have hℓn : ‖(ℓ : C)‖ < 1 := by
    rw [← norm_neg, ← hsum]
    obtain ⟨i, -, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty
      ⟨0, Finset.mem_range.2 hℓ.pos⟩ (fun i ↦ ζC ^ i - 1)
    exact hle.trans_lt ((norm_zpow_sub_one_le le_rfl h4 i).trans_lt h4 |>.trans_eq' (by
      rw [zpow_natCast]))
  rw [norm_natCast_eq_one_of_prime_ne hp hℓ hℓp hp1] at hℓn
  exact lt_irrefl _ hℓn

include hp hp1 in
/-- **A nontrivial Galois group has a normal subgroup of prime index.** -/
theorem exists_normal_index_prime {y : M} (hy : IsType3 C y) [IsGalois M N]
    (hN : 1 < Module.finrank M N) :
    ∃ H : Subgroup (N ≃ₐ[M] N), H.Normal ∧ H.index.Prime := by
  classical
  obtain ⟨z, hz0, hzgen⟩ := exists_valueGen hy (N := N)
  have hσz : ∀ σ : N ≃ₐ[M] N, ‖σ z / z‖ = 1 := fun σ ↦ by
    rw [norm_div, norm_algEquiv_apply, div_self (norm_ne_zero_iff.2 hz0)]
  choose μ hμ using fun σ ↦ exists_const_near_of_finite hy (hσz σ)
  have hμ1 : ∀ σ, ‖μ σ‖ = 1 := fun σ ↦ by
    have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (x := σ z / z) (y := -(σ z / z - algebraMap C N (μ σ)))
      (by rw [norm_neg, hσz]; exact (hμ σ).ne')
    rw [norm_neg, hσz, max_eq_left (hμ σ).le, show σ z / z + -(σ z / z - algebraMap C N (μ σ)) =
      algebraMap C N (μ σ) by ring, norm_algebraMap'] at h
    exact h
  -- multiplicativity up to `1`-units
  have hmul : ∀ σ τ, ‖μ (σ * τ) - μ σ * μ τ‖ < 1 := by
    intro σ τ
    have e1 : (σ * τ) z / z = σ (τ z / z) * (σ z / z) := by
      rw [AlgEquiv.mul_apply, map_div₀]
      field_simp [(map_ne_zero σ).2 hz0]
    have hστ : ‖σ (τ z / z) - algebraMap C N (μ τ)‖ < 1 := by
      have hσμ : σ (algebraMap C N (μ τ)) = algebraMap C N (μ τ) := by
        rw [IsScalarTower.algebraMap_apply C M N, AlgEquiv.commutes]
      rw [← hσμ, ← map_sub, norm_algEquiv_apply]
      exact hμ τ
    have hprod : ‖σ (τ z / z) * (σ z / z) - algebraMap C N (μ τ) * algebraMap C N (μ σ)‖ < 1 := by
      rw [show σ (τ z / z) * (σ z / z) - algebraMap C N (μ τ) * algebraMap C N (μ σ) =
        σ (τ z / z) * (σ z / z - algebraMap C N (μ σ)) +
          (σ (τ z / z) - algebraMap C N (μ τ)) * algebraMap C N (μ σ) by ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
      · rw [norm_mul, norm_algEquiv_apply, hσz, one_mul]; exact hμ σ
      · rw [norm_mul, norm_algebraMap', hμ1, mul_one]; exact hστ
    have h := (norm_sub_le_max' ((σ * τ) z / z - algebraMap C N (μ (σ * τ)))
      ((σ * τ) z / z - algebraMap C N (μ τ) * algebraMap C N (μ σ))).trans_lt
        (max_lt (hμ _) (e1 ▸ hprod))
    rw [show (σ * τ) z / z - algebraMap C N (μ (σ * τ)) -
        ((σ * τ) z / z - algebraMap C N (μ τ) * algebraMap C N (μ σ)) =
        -algebraMap C N (μ (σ * τ) - μ σ * μ τ) by rw [map_sub, map_mul]; ring, norm_neg,
      norm_algebraMap'] at h
    exact h
  have hone : ‖μ 1 - 1‖ < 1 := by
    have h := hμ 1
    rw [AlgEquiv.one_apply, div_self hz0, ← map_one (algebraMap C N), ← map_sub,
      norm_algebraMap', norm_sub_rev] at h
    exact h
  let χ : (N ≃ₐ[M] N) →* 𝓀ˣ :=
    { toFun := fun σ ↦ Units.mk0 (IsLocalRing.residue (HenselComplete.integers C)
        ⟨μ σ, (HenselComplete.mem_integers_iff _).2 (hμ1 σ).le⟩) (residue_ne_zero (hμ1 σ))
      map_one' := by
        ext
        simp only [Units.val_mk0, Units.val_one]
        exact ((residue_eq_iff (hμ1 1).le (le_of_eq norm_one)).2 hone).trans (map_one _)
      map_mul' := fun σ τ ↦ by
        ext
        simp only [Units.val_mk0, Units.val_mul]
        rw [← map_mul]
        exact (residue_eq_iff (a := μ (σ * τ)) (b := μ σ * μ τ) (hμ1 _).le
          (by simp [hμ1])).2 (hmul σ τ) }
  have hχ : ∀ σ, χ σ = 1 ↔ ‖μ σ - 1‖ < 1 := fun σ ↦ by
    rw [← Units.val_eq_one]
    change IsLocalRing.residue _ _ = 1 ↔ _
    rw [← residue_eq_iff (hμ1 σ).le (le_of_eq norm_one)]
    exact Iff.of_eq (congrArg _ (map_one _).symm)
  -- the kernel is a `p`-group
  have hker : ∀ σ, χ σ = 1 → ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ orderOf σ → ℓ = p := by
    intro σ hσ ℓ hℓ hdvd
    by_contra hℓp
    have hn0 : orderOf σ ≠ 0 := (isOfFinOrder_of_finite σ).orderOf_pos.ne'
    set τ := σ ^ (orderOf σ / ℓ)
    have hτℓ : orderOf τ = ℓ := orderOf_pow_orderOf_div hn0 hdvd
    have hτ1 : χ τ = 1 := by rw [map_pow, hσ, one_pow]
    have hτz : ‖τ z / z - 1‖ < 1 := by
      have := (hχ τ).1 hτ1
      rw [show τ z / z - 1 = (τ z / z - algebraMap C N (μ τ)) + algebraMap C N (μ τ - 1) by
        rw [map_sub, map_one]; ring]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hμ τ) ?_)
      rwa [norm_algebraMap']
    exact false_of_orderOf_eq_prime hp hp1 hy hz0 hzgen τ hτz hℓ hℓp hτℓ
  by_cases htriv : ∀ σ, χ σ = 1
  · -- `G` is a `p`-group: a normal subgroup of index `p` (D4)
    have hG : IsPGroup p (N ≃ₐ[M] N) := by
      intro g
      have hn0 : orderOf g ≠ 0 := (isOfFinOrder_of_finite g).orderOf_pos.ne'
      by_cases h1 : orderOf g = 1
      · exact ⟨0, by rw [pow_zero, pow_one, ← orderOf_eq_one_iff, h1]⟩
      · refine ⟨(orderOf g).primeFactorsList.length, ?_⟩
        rw [← Nat.eq_prime_pow_of_unique_prime_dvd hn0 fun hd hdvd ↦ hker g (htriv g) _ hd hdvd,
          pow_orderOf_eq_one]
    haveI := Fact.mk hp
    obtain ⟨m, c, hc0, hcm, hc⟩ := PGroupChain.exists_chain hG ⊥
    have hbt : (⊥ : Subgroup (N ≃ₐ[M] N)) ≠ ⊤ := by
      intro h
      have hcard := IsGalois.card_aut_eq_finrank M N
      rw [← Subgroup.card_top (G := N ≃ₐ[M] N), ← h, Subgroup.card_bot] at hcard
      omega
    have hm : m ≠ 0 := by
      rintro rfl
      exact hbt (hc0.symm.trans hcm)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    obtain ⟨hle, hnormal, hidx⟩ := hc k (Nat.lt_succ_self k)
    rw [hcm] at hle hnormal hidx
    haveI : (c k).Normal := by
      have := (Subgroup.normal_subgroupOf_iff_le_normalizer hle).1 hnormal
      exact ⟨fun n hn g ↦ (this (Subgroup.mem_top g) n).1 hn⟩
    rw [Subgroup.relIndex_top_right] at hidx
    exact ⟨c k, inferInstance, hidx ▸ hp⟩
  · push Not at htriv
    obtain ⟨σ₀, hσ₀⟩ := htriv
    set R := χ.range
    haveI : Finite R := Finite.of_surjective _ χ.rangeRestrict_surjective
    haveI : IsCyclic R := isCyclic_of_injective_ringHom ((Units.coeHom 𝓀).comp R.subtype)
      (fun a b h ↦ Subtype.ext (Units.ext h))
    set m := Nat.card R
    have hm1 : 1 < m := by
      haveI : Nontrivial R := ⟨⟨⟨χ σ₀, σ₀, rfl⟩, 1, fun h ↦ hσ₀ (congrArg Subtype.val h)⟩⟩
      exact Finite.one_lt_card
    obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd hm1.ne'
    haveI := Fact.mk hℓ
    set χ' := (powMonoidHom (m / ℓ)).comp χ
    refine ⟨χ'.ker, MonoidHom.normal_ker _, ?_⟩
    rw [Subgroup.index_ker]
    have hpow : ∀ x ∈ χ'.range, x ^ ℓ = 1 := by
      rintro _ ⟨σ, rfl⟩
      have h1 : (⟨χ σ, σ, rfl⟩ : R) ^ m = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at h2
      simp only [χ', MonoidHom.comp_apply, powMonoidHom_apply, ← pow_mul,
        Nat.div_mul_cancel hℓm]
      exact h2
    have hle : Nat.card χ'.range ≤ ℓ := by
      have hsub : χ'.range ≤ rootsOfUnity ℓ 𝓀 := fun x hx ↦ (mem_rootsOfUnity ℓ x).2 (hpow x hx)
      exact (Subgroup.card_le_of_le hsub).trans (card_rootsOfUnity 𝓀 ℓ)
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
    have hgo : orderOf g = m := orderOf_eq_card_of_forall_mem_zpowers hg
    obtain ⟨σ₁, hσ₁⟩ := g.2
    have hne : χ' σ₁ ≠ 1 := by
      simp only [χ', MonoidHom.comp_apply, powMonoidHom_apply, hσ₁]
      intro h
      have h3 : g ^ (m / ℓ) = 1 := Subtype.ext (by simpa using h)
      have hdvd := orderOf_dvd_of_pow_eq_one h3
      rw [hgo] at hdvd
      have hpos : 0 < m / ℓ := Nat.div_pos (Nat.le_of_dvd (by omega) hℓm) hℓ.pos
      have h4 := Nat.le_of_dvd hpos hdvd
      have h5 := Nat.div_lt_self (by omega : 0 < m) hℓ.one_lt
      omega
    have hord : orderOf (⟨χ' σ₁, σ₁, rfl⟩ : χ'.range) = ℓ :=
      orderOf_eq_prime (Subtype.ext (hpow _ ⟨σ₁, rfl⟩)) fun h ↦ hne (congrArg Subtype.val h)
    have hdvd := orderOf_dvd_natCard (⟨χ' σ₁, σ₁, rfl⟩ : χ'.range)
    rw [hord] at hdvd
    have h6 := Nat.le_of_dvd Nat.card_pos hdvd
    rw [le_antisymm hle h6]
    exact hℓ

end Structure

section Induction

universe u

open FundamentalInequality DenseCompletion

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
include hp hp1

set_option maxHeartbeats 1000000 in
-- the instance arguments of the induction hypothesis at an intermediate field are slow to unify
/-- **Galois extensions of type-3 fields are totally ramified**: `e(N | B) = [N : B]` (strong
induction on `[N : B]` along Kummer steps of prime degree). -/
theorem ramificationIdx_eq_finrank_of_isGalois (n : ℕ) :
    ∀ (B N : Type u) [NontriviallyNormedField B] [IsUltrametricDist B] [CompleteSpace B]
      [NormedAlgebra C B] [NormedField N] [IsUltrametricDist N] [NormedAlgebra B N]
      [NormedAlgebra C N] [IsScalarTower C B N] [FiniteDimensional B N] [IsGalois B N],
      (∃ y : B, IsType3 C y) → Module.finrank B N = n →
        ramificationIdx B (NormedField.valuation (K := N)) = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B N _ _ _ _ _ _ _ _ _ _ _ hB hn
  obtain ⟨y, hy⟩ := hB
  rcases Nat.lt_or_ge 1 n with h1 | h1
  · obtain ⟨H, hH, hidx⟩ := exists_normal_index_prime hp hp1 hy (N := N) (hn ▸ h1)
    set E := IntermediateField.fixedField H
    have hEdeg : Module.finrank B E = H.index := by
      have h2 := IntermediateField.finrank_fixedField_eq_card H
      have h3 := Module.finrank_mul_finrank B E N
      have h4 := IsGalois.card_aut_eq_finrank B N
      rw [h2, ← h4, ← Subgroup.index_mul_card H] at h3
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h3
    set q := H.index
    haveI : IsGalois B E := IsGalois.of_fixedField_normal_subgroup H
    haveI := Fact.mk hidx
    haveI : NeZero (q : C) := ⟨Nat.cast_ne_zero.2 hidx.ne_zero⟩
    obtain ⟨ζC, hζC⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C q
    have hζ : IsPrimitiveRoot (algebraMap C B ζC) q :=
      hζC.map_of_injective (algebraMap C B).injective
    obtain ⟨α, ⟨f₀, hf₀⟩, hαtop⟩ := GaloisReduction.exists_kummer_generator hEdeg hζ
    have hαB : α ∉ Set.range (algebraMap B E) := by
      rintro ⟨b, rfl⟩
      rw [IntermediateField.adjoin_simple_eq_bot_iff.2 (IntermediateField.algebraMap_mem _ b)]
        at hαtop
      have := congrArg (fun K : IntermediateField B E ↦ Module.finrank B K) hαtop
      simp only [IntermediateField.finrank_bot, IntermediateField.finrank_top'] at this
      exact hidx.one_lt.ne (this.trans hEdeg)
    obtain ⟨⟨z, hz⟩, heE, -⟩ :=
      kummer_step (M := B) (E := E) hp hp1 hy hidx hEdeg hαB hf₀.symm
    have hlt : Module.finrank E N < n := by
      rw [← hn, ← Module.finrank_mul_finrank B E N, hEdeg]
      exact lt_mul_left Module.finrank_pos hidx.one_lt
    haveI : IsScalarTower C E N := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    haveI : IsGalois E N := IsGalois.tower_top_intermediateField E
    have hIH := ih _ hlt E N ⟨z, hz⟩ rfl
    rw [ramificationIdx_tower (K := B) (L := E) (NormedField.valuation (K := N)),
      comap_valuation_algebraMap, hIH, heE, ← hn, ← Module.finrank_mul_finrank B E N, hEdeg,
      mul_comm]
  · have h1' : n = 1 := le_antisymm h1 (hn ▸ Module.finrank_pos)
    subst h1'
    have hle := ramificationIdx_mul_inertiaDeg_le (K := B) (v := NormedField.valuation (K := B))
      (w := NormedField.valuation (K := N))
    have he0 := Nat.pos_of_ne_zero (ramificationIdx_ne_zero (K := B)
      (NormedField.valuation (K := N)))
    have hf0 : 0 < inertiaDeg (NormedField.valuation (K := B))
      (NormedField.valuation (K := N)) := NormedTower.inertiaDeg_pos
    rw [hn] at hle
    nlinarith

end Induction

end Type3

end SemistableReduction
