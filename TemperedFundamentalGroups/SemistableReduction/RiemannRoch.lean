/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CurveDivisor

/-!
# Riemann–Roch spaces, Riemann's inequality and the genus

Blueprint §9.5, R4–R7. Let `k` be algebraically closed and `κ / k` a function field of one
variable. For a divisor `D` (`CurveDivisor k κ`):

* `rrSpace D = L(D) = {f | ord_P f ≥ -D(P) ∀ P}` (in multiplicative notation
  `v_P(f) ≤ exp (D P)`), a `k`-subspace of `κ`, and `ell D = dim_k L(D)`;
* `finiteDimensional_rrSpace`, `ell_le_ell_add_degree` (`ℓ(D') ≤ ℓ(D) + deg (D' - D)` for
  `D ≤ D'`; the step `D → D + P` uses that the residue field of `P` is `k`), `ell_zero`;
* `ell_add_divisor`: `ℓ(D + (z)) = ℓ(D)` (multiplication by `z`);
* `degree_poleDivisor`: `deg (x)_∞ = [κ : k(x)]` for `x ∉ k` (`≤` is
  `CurvePlace.sum_poleOrder_le`; `≥`: for a basis `u` of `κ / k(x)` and `C = ∑ (uᵢ)_∞`, the
  `xʲ uᵢ` (`j ≤ m`) are independent elements of `L(m (x)_∞ + C)`, so
  `(m + 1) [κ : k(x)] ≤ 1 + m deg (x)_∞ + deg C` for all `m`); hence `degree_divisor`:
  principal divisors have degree `0`;
* `genus k κ = sup_D (deg D + 1 - ℓ(D))`, finite (`bddAbove_riemannDefect`, Stichtenoth §1.4:
  `deg D + 1 - ℓ(D)` is bounded on multiples of `(x)_∞` and every `D` is linearly equivalent to a
  divisor `≤ m (x)_∞`), **Riemann's inequality** `riemann_inequality`
  (`ℓ(D) ≥ deg D + 1 - g`), `ell_eq_of_le_degree` (equality for `deg D` large; no canonical
  divisor needed), and `genus_eq_zero_of_adjoin_eq_top` (`g(k(x)) = 0`).
-/

open IntermediateField Valuation WithZero
open scoped WithZero

namespace SemistableReduction

open CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k] [IsCurveFunctionField k κ]

section RRSpace

/-- The Riemann–Roch space `L(D) = {f | ord_P f ≥ -D(P) for all P}`. -/
def rrSpace (D : CurveDivisor k κ) : Submodule k κ where
  carrier := {f | ∀ P : CurvePlace k κ, P.valuation f ≤ exp (D P)}
  add_mem' hf hg P := (Valuation.map_add _ _ _).trans (max_le (hf P) (hg P))
  zero_mem' P := by simp
  smul_mem' c f hf P := by
    rw [Algebra.smul_def, map_mul]
    exact (mul_le_of_le_one_left' (P.valuation_algebraMap_le_one c)).trans (hf P)

lemma mem_rrSpace {D : CurveDivisor k κ} {f : κ} :
    f ∈ rrSpace D ↔ ∀ P : CurvePlace k κ, P.valuation f ≤ exp (D P) := Iff.rfl

lemma rrSpace_mono {D D' : CurveDivisor k κ} (h : D ≤ D') : rrSpace D ≤ rrSpace D' :=
  fun _ hf P ↦ (hf P).trans (exp_le_exp.2 (h P))

/-- `f ≠ 0` lies in `L(D)` iff `D + (f) ≥ 0`. -/
lemma mem_rrSpace_iff_le {D : CurveDivisor k κ} {f : κ} (hf : f ≠ 0) :
    f ∈ rrSpace D ↔ 0 ≤ D + divisor k f := by
  refine forall_congr' fun P ↦ ?_
  rw [valuation_eq_exp_neg_divisor hf, exp_le_exp, Finsupp.add_apply, Finsupp.coe_zero,
    Pi.zero_apply]
  omega

/-- `L(0) = k`. -/
lemma rrSpace_zero : rrSpace (0 : CurveDivisor k κ) = Submodule.span k {1} := by
  ext f
  rw [Submodule.mem_span_singleton]
  have : f ∈ rrSpace (0 : CurveDivisor k κ) ↔ poleNorm k f = 0 := by
    rw [← Nat.le_zero, poleNorm_le_iff]
    refine forall_congr' fun P ↦ ?_
    rw [P.poleOrder_le_iff]
    simp
  rw [this, poleNorm_eq_zero_iff]
  simp [Algebra.algebraMap_eq_smul_one, eq_comm]

/-- The dimension `ℓ(D)` of the Riemann–Roch space. -/
noncomputable def ell (D : CurveDivisor k κ) : ℕ := Module.finrank k (rrSpace D)

lemma ell_zero : ell (0 : CurveDivisor k κ) = 1 := by
  rw [ell, rrSpace_zero, finrank_span_singleton one_ne_zero]

/-- `L(D + P) ⊆ L(D) + k g` for a single `g`: the residue field of `P` is `k`. -/
lemma exists_rrSpace_add_single_le (D : CurveDivisor k κ) (P : CurvePlace k κ) :
    ∃ g : κ, rrSpace (D + Finsupp.single P 1) ≤ rrSpace D ⊔ Submodule.span k {g} := by
  classical
  by_cases h : rrSpace (D + Finsupp.single P 1) ≤ rrSpace D
  · exact ⟨0, h.trans le_sup_left⟩
  obtain ⟨g, hg, hgD⟩ := SetLike.not_le_iff_exists.1 h
  have hother {f : κ} (hf : f ∈ rrSpace (D + Finsupp.single P 1)) {Q : CurvePlace k κ}
      (hQP : Q ≠ P) : Q.valuation f ≤ exp (D Q) := by
    simpa [Finsupp.single_apply, Ne.symm hQP] using hf Q
  have hgP : P.valuation g = exp (D P + 1) := by
    refine le_antisymm (by simpa using hg P) ?_
    obtain ⟨Q, hQ⟩ := not_forall.1 hgD
    by_cases hQP : Q = P
    · subst hQP
      exact WithZero.exp_add_one_le_of_lt (not_le.1 hQ)
    · exact absurd (hother hg hQP) hQ
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [map_zero] at hgP
    exact exp_ne_zero hgP.symm
  refine ⟨g, fun f hf ↦ ?_⟩
  have hfg : f / g ∈ P.V := by
    rw [← P.valuation_le_one_iff, map_div₀, hgP, div_le_one₀ exp_pos]
    simpa using hf P
  obtain ⟨c, hc⟩ := P.exists_valuation_sub_lt_one hfg
  have hmem : f - c • g ∈ rrSpace D := by
    intro Q
    by_cases hQP : Q = P
    · subst hQP
      have : f - c • g = (f / g - algebraMap k κ c) * g := by
        rw [Algebra.smul_def]
        field_simp
      rw [this, map_mul, hgP]
      refine WithZero.le_exp_of_lt_exp_add_one ?_
      calc _ < 1 * exp (D Q + 1) := mul_lt_mul_of_pos_right hc exp_pos
        _ = _ := one_mul _
    · exact hother (sub_mem hf (Submodule.smul_mem _ c hg)) hQP
  have : f = (f - c • g) + c • g := by abel
  rw [this]
  exact Submodule.add_mem_sup hmem (Submodule.smul_mem _ c (Submodule.mem_span_singleton_self g))

lemma finiteDimensional_and_ell_add_single (D : CurveDivisor k κ) (P : CurvePlace k κ)
    [FiniteDimensional k (rrSpace D)] :
    FiniteDimensional k (rrSpace (D + Finsupp.single P 1)) ∧
      ell (D + Finsupp.single P 1) ≤ ell D + 1 := by
  obtain ⟨g, hg⟩ := exists_rrSpace_add_single_le D P
  haveI := Submodule.finiteDimensional_of_le hg
  refine ⟨this, ?_⟩
  calc ell (D + Finsupp.single P 1) ≤ Module.finrank k ↥(rrSpace D ⊔ Submodule.span k {g}) :=
        Submodule.finrank_mono hg
    _ ≤ ell D + Module.finrank k ↥(Submodule.span k {g}) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ ell D + 1 := by
        gcongr
        simpa using finrank_span_le_card ({g} : Set κ)

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma degree_nonneg {E : CurveDivisor k κ} (hE : 0 ≤ E) : 0 ≤ E.degree := by
  rw [Finsupp.degree_apply]
  exact Finset.sum_nonneg fun P _ ↦ hE P

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma eq_zero_of_degree_eq_zero {E : CurveDivisor k κ} (hE : 0 ≤ E) (h : E.degree = 0) :
    E = 0 := by
  rw [Finsupp.degree_apply] at h
  ext P
  by_cases hP : P ∈ E.support
  · exact (Finset.sum_eq_zero_iff_of_nonneg fun Q _ ↦ hE Q).1 h P hP
  · simpa using hP

lemma finiteDimensional_and_ell_le_aux (n : ℕ) :
    ∀ D D' : CurveDivisor k κ, D ≤ D' → (D' - D).degree = n →
      FiniteDimensional k (rrSpace D) →
        FiniteDimensional k (rrSpace D') ∧ ell D' ≤ ell D + n := by
  classical
  induction n with
  | zero =>
    intro D D' hle hdeg hfin
    have : D' - D = 0 := eq_zero_of_degree_eq_zero (sub_nonneg.2 hle) (by exact_mod_cast hdeg)
    rw [sub_eq_zero.1 this]
    exact ⟨hfin, le_rfl⟩
  | succ n ih =>
    intro D D' hle hdeg hfin
    obtain ⟨P, hP⟩ : ∃ P, D P < D' P := by
      by_contra! H
      have : D' = D := le_antisymm H hle
      rw [this, sub_self, map_zero] at hdeg
      omega
    set D'' := D' - Finsupp.single P 1
    have hle'' : D ≤ D'' := by
      intro Q
      simp only [D'', Finsupp.coe_sub, Pi.sub_apply, Finsupp.single_apply]
      split_ifs with h
      · subst h
        omega
      · simpa using hle Q
    have hdeg'' : (D'' - D).degree = n := by
      have : D'' - D = (D' - D) - Finsupp.single P 1 := by
        simp only [D'']
        abel
      rw [this, _root_.map_sub, hdeg, Finsupp.degree_single]
      push_cast
      ring
    obtain ⟨hfin'', hell''⟩ := ih D D'' hle'' hdeg'' hfin
    have hD' : D' = D'' + Finsupp.single P 1 := by
      simp [D'']
    haveI := hfin''
    obtain ⟨hfin', hell'⟩ := finiteDimensional_and_ell_add_single D'' P
    rw [hD']
    exact ⟨hfin', by omega⟩

/-- Riemann–Roch spaces are finite dimensional. -/
instance finiteDimensional_rrSpace (D : CurveDivisor k κ) : FiniteDimensional k (rrSpace D) := by
  have h0 : FiniteDimensional k (rrSpace (0 : CurveDivisor k κ)) := by
    rw [rrSpace_zero]
    infer_instance
  set Dp : CurveDivisor k κ := D ⊔ 0
  have hle : (0 : CurveDivisor k κ) ≤ Dp := le_sup_right
  have := (finiteDimensional_and_ell_le_aux ((Dp - 0).degree.toNat) 0 Dp hle
    (Int.toNat_of_nonneg (degree_nonneg (sub_nonneg.2 hle))).symm h0).1
  exact Submodule.finiteDimensional_of_le (rrSpace_mono (le_sup_left : D ≤ Dp))

/-- `ℓ(D') ≤ ℓ(D) + deg (D' - D)` for `D ≤ D'`. -/
theorem ell_le_ell_add_degree {D D' : CurveDivisor k κ} (h : D ≤ D') :
    (ell D' : ℤ) ≤ ell D + (D' - D).degree := by
  have hn := degree_nonneg (sub_nonneg.2 h)
  have := (finiteDimensional_and_ell_le_aux ((D' - D).degree.toNat) D D' h
    (Int.toNat_of_nonneg hn).symm inferInstance).2
  have h' : ((D' - D).degree.toNat : ℤ) = (D' - D).degree := Int.toNat_of_nonneg hn
  omega

lemma ell_le_degree_add_one {D : CurveDivisor k κ} (h : 0 ≤ D) : (ell D : ℤ) ≤ D.degree + 1 := by
  have := ell_le_ell_add_degree h
  rw [ell_zero, sub_zero] at this
  omega

/-- The **Riemann defect** `deg D + 1 - ℓ(D)`; the genus is its supremum. -/
noncomputable def riemannDefect (D : CurveDivisor k κ) : ℤ := D.degree + 1 - ell D

lemma riemannDefect_zero : riemannDefect (0 : CurveDivisor k κ) = 0 := by
  simp [riemannDefect, ell_zero]

/-- The Riemann defect is monotone. -/
lemma riemannDefect_mono {D D' : CurveDivisor k κ} (h : D ≤ D') :
    riemannDefect D ≤ riemannDefect D' := by
  have := ell_le_ell_add_degree h
  rw [_root_.map_sub] at this
  simp only [riemannDefect]
  omega

/-- Multiplication by `z` identifies `L(D + (z))` with `L(D)`. -/
lemma map_mulLeft_rrSpace_add_divisor (D : CurveDivisor k κ) {z : κ} (hz : z ≠ 0) :
    (rrSpace (D + divisor k z)).map (LinearMap.mulLeft k z) = rrSpace D := by
  ext f
  simp only [Submodule.mem_map, LinearMap.mulLeft_apply]
  constructor
  · rintro ⟨g, hg, rfl⟩ P
    rw [map_mul, valuation_eq_exp_neg_divisor hz]
    calc exp (-divisor k z P) * P.valuation g ≤ exp (-divisor k z P) * exp ((D + divisor k z) P) :=
          by gcongr; exact hg P
      _ = exp (D P) := by rw [← exp_add, Finsupp.add_apply]; congr 1; ring
  · intro hf
    refine ⟨z⁻¹ * f, fun P ↦ ?_, by field_simp⟩
    rw [map_mul, map_inv₀, valuation_eq_exp_neg_divisor hz, ← exp_neg, neg_neg,
      Finsupp.add_apply, exp_add, mul_comm (exp (D P))]
    gcongr
    exact hf P

/-- `ℓ(D + (z)) = ℓ(D)`. -/
theorem ell_add_divisor (D : CurveDivisor k κ) {z : κ} (hz : z ≠ 0) :
    ell (D + divisor k z) = ell D := by
  have hinj : Function.Injective (LinearMap.mulLeft k z) := mul_right_injective₀ hz
  rw [ell, ell, ← map_mulLeft_rrSpace_add_divisor D hz]
  exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq

end RRSpace

section Degree

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma adjoin_inv_eq (f : κ) : k⟮f⁻¹⟯ = k⟮f⟯ :=
  le_antisymm (adjoin_simple_le_iff.2 (inv_mem (mem_adjoin_simple_self k f)))
    (adjoin_simple_le_iff.2 (mem_adjoin_inv (mem_adjoin_simple_self k f)))

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
/-- Powers of a transcendental element are linearly independent. -/
lemma linearIndependent_pow_of_transcendental {x : κ} (hx : Transcendental k x) (m : ℕ) :
    LinearIndependent k fun j : Fin (m + 1) ↦ (AdjoinSimple.gen k x) ^ (j : ℕ) := by
  refine LinearIndependent.of_comp (k⟮x⟯.val.toLinearMap) ?_
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  set p : Polynomial k := ∑ i : Fin (m + 1), Polynomial.monomial (i : ℕ) (c i)
  have hp : Polynomial.aeval x p = 0 := by
    simpa [p, Polynomial.aeval_monomial, Algebra.smul_def] using hc
  have hp0 : p = 0 := by
    by_contra h
    exact hx ⟨p, h, hp⟩
  have := congrArg (fun q : Polynomial k ↦ q.coeff j) hp0
  simp only [p, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial,
    Polynomial.coeff_zero] at this
  rw [Finset.sum_eq_single j (fun i _ hij ↦ by simp [Fin.val_injective.ne hij])
    (by simp)] at this
  simpa using this

/-- The lower bound: for `u` linearly independent over `k(x)` and `C = ∑ (uᵢ)_∞`,
`(m + 1) · #u ≤ ℓ(m (x)_∞ + C)`. -/
lemma card_mul_le_ell {x : κ} (hx : x ∉ (algebraMap k κ).range) {ι : Type*} [Fintype ι]
    {u : ι → κ} (hu : LinearIndependent k⟮x⟯ u) (m : ℕ) :
    (m + 1) * Fintype.card ι ≤ ell (m • poleDivisor k x + ∑ i, poleDivisor k (u i)) := by
  set W := rrSpace (m • poleDivisor k x + ∑ i, poleDivisor k (u i))
  have hmem (j : Fin (m + 1)) (i : ι) : x ^ (j : ℕ) * u i ∈ W := by
    intro P
    rw [map_mul, map_pow, Finsupp.add_apply, Finsupp.smul_apply, poleDivisor_apply,
      Finsupp.finsetSum_apply, exp_add, exp_nsmul]
    · have h1 : P.valuation x ^ (j : ℕ) ≤ exp (P.poleOrder x : ℤ) ^ m :=
        (pow_le_pow_left₀ zero_le (P.valuation_le_exp_poleOrder x) _).trans
          (pow_le_pow_right₀ (by rw [← exp_zero, exp_le_exp]; positivity) (Nat.lt_succ_iff.1 j.2))
      have h2 : P.valuation (u i) ≤ exp (∑ i, poleDivisor k (u i) P) := by
        refine (P.valuation_le_exp_poleOrder (u i)).trans (exp_le_exp.2 ?_)
        rw [← poleDivisor_apply (k := k)]
        exact Finset.single_le_sum (f := fun i ↦ poleDivisor k (u i) P)
          (fun i _ ↦ poleDivisor_nonneg _ P) (Finset.mem_univ i)
      exact mul_le_mul' h1 h2
  have hli : LinearIndependent k fun p : Fin (m + 1) × ι ↦ (⟨_, hmem p.1 p.2⟩ : W) := by
    refine LinearIndependent.of_comp W.subtype ?_
    have := linearIndependent_smul
      (linearIndependent_pow_of_transcendental (transcendental_of_notMem_range hx) m) hu
    convert this using 2 with p
    simp [Algebra.smul_def]
  have := hli.fintype_card_le_finrank
  rw [Fintype.card_prod, Fintype.card_fin] at this
  exact this

/-- **The degree of the pole divisor** of `x ∉ k` is `[κ : k(x)]`. -/
theorem degree_poleDivisor {x : κ} (hx : x ∉ (algebraMap k κ).range) :
    (poleDivisor k x).degree = Module.finrank k⟮x⟯ κ := by
  classical
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hx)
  set n := Module.finrank k⟮x⟯ κ
  set B := poleDivisor k x
  refine le_antisymm ?_ ?_
  · rw [Finsupp.degree_apply]
    have := sum_poleOrder_le hx B.support
    simp only [B, poleDivisor_apply]
    exact_mod_cast this
  · set b := Module.finBasis k⟮x⟯ κ
    set C := ∑ i, poleDivisor k (b i)
    have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ poleDivisor_nonneg _
    have hB : 0 ≤ B := poleDivisor_nonneg _
    have key (m : ℕ) : ((m : ℤ) + 1) * n ≤ 1 + m * B.degree + C.degree := by
      have h1 := card_mul_le_ell hx b.linearIndependent m
      have h2 := ell_le_degree_add_one (D := m • B + C) (add_nonneg (nsmul_nonneg hB m) hC)
      rw [map_add, map_nsmul, nsmul_eq_mul] at h2
      simp only [Fintype.card_fin] at h1
      have : (((m + 1) * n : ℕ) : ℤ) ≤ ell (m • B + C) := by exact_mod_cast h1
      push_cast at this
      linarith
    by_contra! H
    have hn : 1 ≤ n := Module.finrank_pos
    have hCd := degree_nonneg hC
    have := key (C.degree.toNat + 1)
    have hm : ((C.degree.toNat + 1 : ℕ) : ℤ) = C.degree + 1 := by
      push_cast
      rw [Int.toNat_of_nonneg hCd]
    rw [hm] at this
    have h3 : (C.degree + 1) * B.degree ≤ (C.degree + 1) * (n - 1) :=
      mul_le_mul_of_nonneg_left (by omega) (by omega)
    nlinarith

/-- **Principal divisors have degree `0`.** -/
theorem degree_divisor (f : κ) : (divisor k f).degree = 0 := by
  rw [divisor, _root_.map_sub]
  by_cases hf : f ∈ (algebraMap k κ).range
  · obtain ⟨c, rfl⟩ := hf
    rw [← map_inv₀, poleDivisor_algebraMap, poleDivisor_algebraMap, sub_self]
  have hf' : f⁻¹ ∉ (algebraMap k κ).range := by
    rintro ⟨c, hc⟩
    exact hf ⟨c⁻¹, by rw [map_inv₀, hc, inv_inv]⟩
  rw [degree_poleDivisor hf, degree_poleDivisor hf', adjoin_inv_eq, sub_self]

lemma riemannDefect_add_divisor (D : CurveDivisor k κ) {z : κ} (hz : z ≠ 0) :
    riemannDefect (D + divisor k z) = riemannDefect D := by
  simp [riemannDefect, ell_add_divisor D hz, degree_divisor]

end Degree

section Genus

/-- On multiples of `(x)_∞` the Riemann defect is bounded by `deg C + 1 - [κ : k(x)]`, for `u`
a basis of `κ / k(x)` and `C = ∑ (uᵢ)_∞`. -/
lemma riemannDefect_nsmul_poleDivisor_le {x : κ} (hx : x ∉ (algebraMap k κ).range) {ι : Type*}
    [Fintype ι] {u : ι → κ} (hu : LinearIndependent k⟮x⟯ u)
    (hcard : Fintype.card ι = Module.finrank k⟮x⟯ κ) (m : ℕ) :
    riemannDefect (m • poleDivisor k x) ≤
      (∑ i, poleDivisor k (u i)).degree + 1 - Module.finrank k⟮x⟯ κ := by
  set C := ∑ i, poleDivisor k (u i)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ poleDivisor_nonneg _
  have h1 := card_mul_le_ell hx hu m
  have h2 := ell_le_ell_add_degree (D := m • poleDivisor k x)
    (D' := m • poleDivisor k x + C) (le_add_of_nonneg_right hC)
  rw [add_sub_cancel_left] at h2
  rw [hcard] at h1
  have h3 : (((m + 1) * Module.finrank k⟮x⟯ κ : ℕ) : ℤ) ≤ ell (m • poleDivisor k x + C) := by
    exact_mod_cast h1
  simp only [riemannDefect, map_nsmul, nsmul_eq_mul, degree_poleDivisor hx]
  push_cast at h3
  linarith

/-- Every divisor is linearly equivalent to a divisor `≤ m (x)_∞` (Stichtenoth, Lemma 1.4.15). -/
lemma exists_add_divisor_le {x : κ} (hx : x ∉ (algebraMap k κ).range) (D : CurveDivisor k κ) :
    ∃ z : κ, z ≠ 0 ∧ ∃ m : ℕ, D + divisor k z ≤ m • poleDivisor k x := by
  classical
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_of_notMem_range hx)
  set b := Module.finBasis k⟮x⟯ κ
  set n := Module.finrank k⟮x⟯ κ
  set C := ∑ i, poleDivisor k (b i)
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ ↦ poleDivisor_nonneg _
  set Dp := D ⊔ 0
  have hDp : 0 ≤ Dp := le_sup_right
  set m := (C.degree + Dp.degree).toNat
  have hm : (m : ℤ) = C.degree + Dp.degree :=
    Int.toNat_of_nonneg (add_nonneg (degree_nonneg hC) (degree_nonneg hDp))
  set B := poleDivisor k x
  have hdef := riemannDefect_nsmul_poleDivisor_le hx b.linearIndependent (by simp [n]) m
  have h2 := ell_le_ell_add_degree (D := m • B - Dp) (D' := m • B) (sub_le_self _ hDp)
  rw [sub_sub_cancel] at h2
  have hn : 1 ≤ n := Module.finrank_pos
  simp only [riemannDefect, map_nsmul, nsmul_eq_mul, degree_poleDivisor hx] at hdef
  have hpos : 0 < ell (m • B - Dp) := by
    have : (m : ℤ) * n ≥ m := le_mul_of_one_le_right (by omega) (by exact_mod_cast hn)
    have : (0 : ℤ) < ell (m • B - Dp) := by linarith
    omega
  obtain ⟨⟨z, hz⟩, hz0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0' : z ≠ 0 := fun h ↦ hz0 (Subtype.ext h)
  refine ⟨z⁻¹, inv_ne_zero hz0', m, fun P ↦ ?_⟩
  have h := (mem_rrSpace_iff_le hz0').1 hz P
  rw [divisor_inv]
  simp only [Finsupp.coe_add, Finsupp.coe_sub, Finsupp.coe_neg, Pi.add_apply, Pi.sub_apply,
    Pi.neg_apply, Finsupp.coe_zero, Pi.zero_apply] at h ⊢
  have : D P ≤ Dp P := le_sup_left (a := D) (b := 0) P
  linarith

/-- The Riemann defect is bounded above. -/
theorem bddAbove_riemannDefect : BddAbove (Set.range (riemannDefect (k := k) (κ := κ))) := by
  classical
  obtain ⟨x, hxtr, -⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ)
  have hx : x ∉ (algebraMap k κ).range := by
    rintro ⟨c, rfl⟩
    exact hxtr (isAlgebraic_algebraMap c)
  haveI := IsCurveFunctionField.finiteDimensional_adjoin hxtr
  set b := Module.finBasis k⟮x⟯ κ
  refine ⟨(∑ i, poleDivisor k (b i)).degree + 1 - Module.finrank k⟮x⟯ κ, ?_⟩
  rintro _ ⟨D, rfl⟩
  obtain ⟨z, hz, m, hle⟩ := exists_add_divisor_le hx D
  rw [← riemannDefect_add_divisor D hz]
  exact (riemannDefect_mono hle).trans
    (riemannDefect_nsmul_poleDivisor_le hx b.linearIndependent (by simp) m)

variable (k κ) in
/-- The **genus** `g = sup_D (deg D + 1 - ℓ(D))` of the function field `κ / k`. -/
noncomputable def genus : ℕ := (⨆ D : CurveDivisor k κ, riemannDefect D).toNat

lemma genus_eq_iSup : (genus k κ : ℤ) = ⨆ D : CurveDivisor k κ, riemannDefect D := by
  refine Int.toNat_of_nonneg ?_
  rw [← riemannDefect_zero (k := k) (κ := κ)]
  exact le_ciSup bddAbove_riemannDefect 0

lemma riemannDefect_le_genus (D : CurveDivisor k κ) : riemannDefect D ≤ genus k κ := by
  rw [genus_eq_iSup]
  exact le_ciSup bddAbove_riemannDefect D

/-- **Riemann's inequality** `ℓ(D) ≥ deg D + 1 - g`. -/
theorem riemann_inequality (D : CurveDivisor k κ) : D.degree + 1 - genus k κ ≤ ell D := by
  have := riemannDefect_le_genus D
  simp only [riemannDefect] at this
  omega

/-- The genus is attained. -/
theorem exists_riemannDefect_eq_genus : ∃ D : CurveDivisor k κ, riemannDefect D = genus k κ := by
  rw [genus_eq_iSup]
  exact Int.csSup_mem (Set.range_nonempty _) bddAbove_riemannDefect

/-- `ℓ(D) = deg D + 1 - g` for all divisors of large degree. -/
theorem ell_eq_of_le_degree : ∃ c : ℤ, ∀ D : CurveDivisor k κ, c ≤ D.degree →
    (ell D : ℤ) = D.degree + 1 - genus k κ := by
  obtain ⟨D₀, hD₀⟩ := exists_riemannDefect_eq_genus (k := k) (κ := κ)
  refine ⟨D₀.degree + genus k κ, fun D hD ↦ ?_⟩
  have h := riemann_inequality (D - D₀)
  rw [_root_.map_sub] at h
  have hpos : 0 < ell (D - D₀) := by
    have : (0 : ℤ) < ell (D - D₀) := by linarith
    omega
  obtain ⟨⟨z, hz⟩, hz0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have hz0' : z ≠ 0 := fun h ↦ hz0 (Subtype.ext h)
  have hle : D₀ ≤ D + divisor k z := by
    have := (mem_rrSpace_iff_le hz0').1 hz
    intro P
    have := this P
    simp only [Finsupp.coe_add, Finsupp.coe_sub, Pi.add_apply, Pi.sub_apply, Finsupp.coe_zero,
      Pi.zero_apply] at this ⊢
    linarith
  have h1 := riemannDefect_mono hle
  rw [riemannDefect_add_divisor D hz0', hD₀] at h1
  have h2 := riemannDefect_le_genus D
  simp only [riemannDefect] at h1 h2
  omega

/-- **`g(k(x)) = 0`**: a rational function field has genus `0`. -/
theorem genus_eq_zero_of_adjoin_eq_top {x : κ} (hx : k⟮x⟯ = ⊤) : genus k κ = 0 := by
  have hxr : x ∉ (algebraMap k κ).range := by
    rintro ⟨c, rfl⟩
    obtain ⟨y, hy, -⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
      (κ := κ)
    have hbot : k⟮algebraMap k κ c⟯ = ⊥ := by
      rw [IntermediateField.adjoin_simple_eq_bot_iff]
      exact IntermediateField.algebraMap_mem _ c
    have hy' : y ∈ (⊥ : IntermediateField k κ) := by
      rw [← hbot, hx]
      trivial
    obtain ⟨d, rfl⟩ := IntermediateField.mem_bot.1 hy'
    exact hy (isAlgebraic_algebraMap d)
  have hrank : Module.finrank k⟮x⟯ κ = 1 := by
    rw [hx]
    exact IntermediateField.finrank_top
  have hli : LinearIndependent k⟮x⟯ fun _ : Fin 1 ↦ (1 : κ) :=
    linearIndependent_unique_iff.2 one_ne_zero
  have hbound : ∀ D : CurveDivisor k κ, riemannDefect D ≤ 0 := by
    intro D
    obtain ⟨z, hz, m, hle⟩ := exists_add_divisor_le hxr D
    rw [← riemannDefect_add_divisor D hz]
    refine (riemannDefect_mono hle).trans ((riemannDefect_nsmul_poleDivisor_le hxr hli
      (by simp [hrank]) m).trans ?_)
    have h1 : poleDivisor k (1 : κ) = 0 := by
      simpa using poleDivisor_algebraMap (κ := κ) (1 : k)
    rw [hrank]
    simp [h1]
  obtain ⟨D, hD⟩ := exists_riemannDefect_eq_genus (k := k) (κ := κ)
  have := hbound D
  omega

end Genus

section RatFunc

omit [IsAlgClosed k] in
variable (k) in
/-- `k(X)` is a function field of one variable. -/
instance isCurveFunctionField_ratFunc : IsCurveFunctionField k (RatFunc k) := by
  refine ⟨⟨RatFunc.X, RatFunc.transcendental_X, ?_⟩⟩
  have : Module.finrank k⟮(RatFunc.X : RatFunc k)⟯ (RatFunc k) = 1 := by
    rw [RatFunc.adjoin_X]
    exact IntermediateField.finrank_top
  exact Module.finite_of_finrank_eq_succ this

variable (k) in
/-- **`g(k(X)) = 0`**. -/
theorem genus_ratFunc : genus k (RatFunc k) = 0 :=
  genus_eq_zero_of_adjoin_eq_top RatFunc.adjoin_X

end RatFunc

end SemistableReduction
