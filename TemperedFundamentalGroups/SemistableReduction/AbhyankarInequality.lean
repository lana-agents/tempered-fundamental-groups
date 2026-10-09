/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussClassification

/-!
# The Abhyankar inequality (special case)

Blueprint §9.3, W3. Let `L / K` be a field extension, `v` a valuation of `K` and `w` a valuation
of `L` extending `v` (`Valuation.HasExtension`), with residue fields `κ(v) ⊆ κ(w)`.

* `algebraicIndependent_of_residue`, `exists_valuation_aeval_eq`: elements of the valuation ring
  of `w` with algebraically independent residues over `κ(v)` are algebraically independent over
  `K`, and the value of a polynomial expression `P(x)` in them is the maximum of the values of
  the coefficients of `P` (the residue of the normalized `P(x)` is the reduced polynomial at the
  residues, which is nonzero);
* `trdeg_residueField_le`: `trdeg_{κ(v)} κ(w) ≤ trdeg_K L`;
* `exists_pow_eq_of_transcendental`: if `trdeg_K L ≤ 1` (e.g. `L = K(X)`) and `κ(w)` is
  transcendental over `κ(v)`, then `Γ_w / Γ_v` is torsion: every `w f`, `f ≠ 0`, has a power in
  `w(K)`. Otherwise `x` (with transcendental residue) and `f` are algebraically independent:
  in `Σ qⱼ(x) fʲ` the terms have pairwise distinct values `w(cⱼ) w(f)ʲ`;
* `exists_eq_of_transcendental`: for `K` algebraically closed, `Γ_w = Γ_v`;
* the case `L = K(X)`: `trdeg_residueField_ratFunc_le_one`, and (with W2) `eq_gaussRat'`: over
  an algebraically closed field, every valuation of `K(X)` extending `v` with residue field
  transcendental over `κ(v)` is a Gauss valuation.
-/

open IsLocalRing Cardinal

namespace SemistableReduction

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Γ₀ Γ₁ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁]
  {v : Valuation K Γ₀} {w : Valuation L Γ₁} [v.HasExtension w]

open ValuationResidue

namespace AbhyankarInequality

/-- A multivariate polynomial with integral coefficients lifts to the valuation ring. -/
lemma exists_mvPolynomial_map_eq {ι : Type*} (Q : MvPolynomial ι K)
    (hQ : ∀ m, v (Q.coeff m) ≤ 1) :
    ∃ P : MvPolynomial ι v.valuationSubring,
      MvPolynomial.map (algebraMap v.valuationSubring K) P = Q := by
  classical
  refine ⟨∑ m ∈ Q.support, MvPolynomial.monomial m ⟨Q.coeff m, hQ m⟩, ?_⟩
  rw [map_sum]
  simp only [MvPolynomial.map_monomial]
  exact Q.support_sum_monomial_coeff

/-- The residue of a polynomial expression is the reduced polynomial at the residues. -/
lemma residue_mvAeval {ι : Type*} (P : MvPolynomial ι v.valuationSubring)
    (x : ι → w.valuationSubring) :
    residue w.valuationSubring (MvPolynomial.aeval x P) =
      MvPolynomial.aeval (fun i ↦ residue w.valuationSubring (x i))
        (MvPolynomial.map (residue v.valuationSubring) P) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map,
    MvPolynomial.eval₂_comp_left]
  rfl

lemma coe_mvAeval {ι : Type*} (P : MvPolynomial ι v.valuationSubring)
    (x : ι → w.valuationSubring) :
    ((MvPolynomial.aeval x P : w.valuationSubring) : L) =
      MvPolynomial.aeval (fun i ↦ (x i : L))
        (MvPolynomial.map (algebraMap v.valuationSubring K) P) := by
  rw [MvPolynomial.aeval_map_algebraMap]
  exact (MvPolynomial.aeval_algebraMap_apply L x P).symm

end AbhyankarInequality

open AbhyankarInequality

/-- The value of a polynomial expression `P(x)` in elements `x` of the valuation ring of `w`
with algebraically independent residues is the value of a coefficient of `P` (the largest one).
-/
theorem exists_valuation_aeval_eq {ι : Type*} (x : ι → w.valuationSubring)
    (hx : AlgebraicIndependent (ResidueField v.valuationSubring)
      (fun i ↦ residue w.valuationSubring (x i)))
    (P : MvPolynomial ι K) (hP : P ≠ 0) :
    ∃ c : K, c ≠ 0 ∧
      w (MvPolynomial.aeval (fun i ↦ (x i : L)) P) = w (algebraMap K L c) := by
  classical
  obtain ⟨m₀, hm₀, hmax⟩ := Finset.exists_max_image P.support (fun m ↦ v (P.coeff m))
    (MvPolynomial.support_nonempty.2 hP)
  set c := P.coeff m₀
  have hc : c ≠ 0 := MvPolynomial.mem_support_iff.1 hm₀
  have hvc : v c ≠ 0 := by simpa using hc
  set Q := MvPolynomial.C c⁻¹ * P
  have hQ : ∀ m, v (Q.coeff m) ≤ 1 := fun m ↦ by
    rw [MvPolynomial.coeff_C_mul, map_mul, map_inv₀]
    by_cases hm : m ∈ P.support
    · rw [inv_mul_le_iff₀ (zero_lt_iff.2 hvc), mul_one]
      exact hmax m hm
    · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, mul_zero]
      exact zero_le
  obtain ⟨Q', hQ'⟩ := exists_mvPolynomial_map_eq Q hQ
  have hQ'm₀ : Q'.coeff m₀ = 1 := by
    apply (FaithfulSMul.algebraMap_injective v.valuationSubring K)
    rw [← MvPolynomial.coeff_map, hQ', MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc, map_one]
  have hred : MvPolynomial.map (residue v.valuationSubring) Q' ≠ 0 := by
    intro h0
    have := congrArg (MvPolynomial.coeff m₀) h0
    rw [MvPolynomial.coeff_map, hQ'm₀, map_one, MvPolynomial.coeff_zero] at this
    exact one_ne_zero this
  have hres : residue w.valuationSubring (MvPolynomial.aeval x Q') ≠ 0 := by
    have hinj : Function.Injective
        (MvPolynomial.aeval fun i ↦ residue w.valuationSubring (x i)) := hx
    rw [residue_mvAeval]
    exact fun h0 ↦ hred (hinj (h0.trans (map_zero _).symm))
  have hw1 := (residue_ne_zero_iff _).1 hres
  rw [coe_mvAeval, hQ'] at hw1
  refine ⟨c, hc, ?_⟩
  have hPQ : P = MvPolynomial.C c * Q := by
    rw [← mul_assoc, ← MvPolynomial.C_mul, mul_inv_cancel₀ hc, MvPolynomial.C_1, one_mul]
  rw [hPQ, map_mul, MvPolynomial.aeval_C, map_mul, hw1, mul_one]

/-- Elements of the valuation ring of `w` whose residues are algebraically independent over
`κ(v)` are algebraically independent over `K`. -/
theorem algebraicIndependent_of_residue {ι : Type*} (x : ι → w.valuationSubring)
    (hx : AlgebraicIndependent (ResidueField v.valuationSubring)
      (fun i ↦ residue w.valuationSubring (x i))) :
    AlgebraicIndependent K (fun i ↦ (x i : L)) := by
  rw [AlgebraicIndependent, injective_iff_map_eq_zero]
  intro P hP
  by_contra hP0
  obtain ⟨c, hc, hw⟩ := exists_valuation_aeval_eq x hx P hP0
  rw [hP, map_zero, eq_comm, Valuation.zero_iff, map_eq_zero_iff _ (algebraMap K L).injective]
    at hw
  exact hc hw

/-- **W3** (residue transcendence degree): `trdeg_{κ(v)} κ(w) ≤ trdeg_K L`. -/
theorem trdeg_residueField_le :
    Algebra.trdeg (ResidueField v.valuationSubring) (ResidueField w.valuationSubring) ≤
      Algebra.trdeg K L := by
  refine ciSup_le' fun s ↦ ?_
  set lift := Function.surjInv (residue_surjective (R := w.valuationSubring))
  have hlift : ∀ z, residue w.valuationSubring (lift z) = z :=
    Function.surjInv_eq (residue_surjective (R := w.valuationSubring))
  have hind : AlgebraicIndependent (ResidueField v.valuationSubring)
      (fun z : s.1 ↦ residue w.valuationSubring (lift z)) := by
    simp_rw [hlift]
    exact s.2
  exact (algebraicIndependent_of_residue (fun z : s.1 ↦ lift z) hind).cardinalMk_le_trdeg

/-- A finite sum whose terms have pairwise distinct nonzero values is nonzero. -/
lemma sum_ne_zero_of_valuation_ne {α : Type*} {s : Finset α} (hs : s.Nonempty) (g : α → L)
    (h0 : ∀ j ∈ s, w (g j) ≠ 0) (hne : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → w (g j) ≠ w (g k)) :
    ∑ j ∈ s, g j ≠ 0 := by
  classical
  obtain ⟨j₀, hj₀, hmax⟩ := Finset.exists_max_image s (fun j ↦ w (g j)) hs
  have hrest : w (∑ k ∈ s.erase j₀, g k) < w (g j₀) := by
    refine w.map_sum_lt (h0 j₀ hj₀) fun k hk ↦ ?_
    obtain ⟨hkj, hk⟩ := Finset.mem_erase.1 hk
    exact lt_of_le_of_ne (hmax k hk) (hne k hk j₀ hj₀ hkj)
  intro hsum
  rw [← Finset.add_sum_erase _ _ hj₀] at hsum
  have := w.map_add_eq_of_lt_left hrest
  rw [hsum, map_zero] at this
  exact h0 j₀ hj₀ this.symm

/-- **W3** (value group): if `trdeg_K L ≤ 1` and the residue field of `w` is transcendental over
that of `v`, then `Γ_w / Γ_v` is torsion. -/
theorem exists_pow_eq_of_transcendental (hL : Algebra.trdeg K L ≤ 1)
    (htr : Algebra.Transcendental (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring)) {f : L} (hf : f ≠ 0) :
    ∃ n : ℕ, 0 < n ∧ ∃ c : K, w f ^ n = w (algebraMap K L c) := by
  by_contra! H
  obtain ⟨z, hz⟩ := Algebra.transcendental_def.1 htr
  obtain ⟨x, rfl⟩ := residue_surjective z
  set xs : Unit → L := fun _ ↦ (x : L)
  have hxs : AlgebraicIndependent (ResidueField v.valuationSubring)
      (fun _ : Unit ↦ residue w.valuationSubring x) :=
    algebraicIndependent_unique_type_iff.2 hz
  have hind := algebraicIndependent_of_residue (fun _ : Unit ↦ x) hxs
  have hwf : w f ≠ 0 := by simpa using hf
  -- `f` is transcendental over `K[x]`
  have htrans : Transcendental (Algebra.adjoin K (Set.range xs)) f := by
    rintro ⟨Q, hQ0, hQf⟩
    have hval : ∀ j ∈ Q.support, ∃ c : K, c ≠ 0 ∧
        w (Q.coeff j : L) = w (algebraMap K L c) := by
      intro j hj
      have hmem : (Q.coeff j : L) ∈ (MvPolynomial.aeval (R := K) xs).range := by
        rw [← Algebra.adjoin_range_eq_range_aeval]
        exact (Q.coeff j).2
      obtain ⟨P, hP⟩ := (AlgHom.mem_range _).1 hmem
      have hP0 : P ≠ 0 := by
        rintro rfl
        rw [map_zero, eq_comm, ZeroMemClass.coe_eq_zero] at hP
        exact Polynomial.mem_support_iff.1 hj hP
      rw [← hP]
      exact exists_valuation_aeval_eq (fun _ : Unit ↦ x) hxs P hP0
    choose! c hc hcw using hval
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hQf
    refine sum_ne_zero_of_valuation_ne (w := w) (Polynomial.support_nonempty.2 hQ0) _ ?_ ?_ hQf
    · intro j hj
      change w ((Q.coeff j : L) * f ^ j) ≠ 0
      rw [map_mul, map_pow, hcw j hj]
      refine mul_ne_zero ?_ (pow_ne_zero _ hwf)
      simpa using hc j hj
    · -- distinct exponents give distinct values
      have key : ∀ j ∈ Q.support, ∀ k ∈ Q.support, j < k →
          w (algebraMap K L (c j)) * w f ^ j ≠ w (algebraMap K L (c k)) * w f ^ k := by
        intro j hj k hk hjk heq
        have hck : w (algebraMap K L (c k)) ≠ 0 := by simpa using hc k hk
        refine H (k - j) (Nat.sub_pos_of_lt hjk) (c j / c k) ?_
        rw [map_div₀, map_div₀, eq_div_iff hck]
        have : w f ^ k = w f ^ j * w f ^ (k - j) := by
          rw [← pow_add, Nat.add_sub_cancel' hjk.le]
        rw [this, ← mul_assoc, mul_comm (w (algebraMap K L (c k))), mul_assoc] at heq
        rw [mul_comm]
        exact mul_left_cancel₀ (pow_ne_zero _ hwf) (heq.symm.trans (mul_comm _ _))
      intro j hj k hk hjk
      change w ((Q.coeff j : L) * f ^ j) ≠ w ((Q.coeff k : L) * f ^ k)
      rw [map_mul, map_pow, map_mul, map_pow, hcw j hj, hcw k hk]
      rcases Nat.lt_or_gt_of_ne hjk with h | h
      · exact key j hj k hk h
      · exact (key k hk j hj h).symm
  have hpair := (AlgebraicIndependent.option_iff (x := xs) (a := f)).2 ⟨hind, htrans⟩
  have hcard := hpair.lift_cardinalMk_le_trdeg
  have h2 : lift.{0} (Algebra.trdeg K L) ≤ 1 := by
    simpa using hL
  have := hcard.trans h2
  simp at this

/-- **W3** (value group, algebraically closed case): if `K` is algebraically closed,
`trdeg_K L ≤ 1` and the residue field of `w` is transcendental over that of `v`, then the value
group of `w` is that of `v`. -/
theorem exists_eq_of_transcendental [IsAlgClosed K] (hL : Algebra.trdeg K L ≤ 1)
    (htr : Algebra.Transcendental (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring)) (f : L) :
    ∃ c : K, w f = w (algebraMap K L c) := by
  rcases eq_or_ne f 0 with rfl | hf
  · exact ⟨0, by simp⟩
  obtain ⟨n, hn, c, hc⟩ := exists_pow_eq_of_transcendental hL htr hf
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq c hn
  refine ⟨d, (pow_left_inj₀ zero_le zero_le hn.ne').1 ?_⟩
  rw [hc, ← hd, map_pow, map_pow]

/-- `K(X)` has transcendence degree `1` over `K`. -/
lemma trdeg_ratFunc : Algebra.trdeg K (RatFunc K) = 1 := by
  have := trdeg_add_eq K (Polynomial K) (A := RatFunc K)
  have h0 : Algebra.trdeg (Polynomial K) (RatFunc K) = 0 := by
    have : Algebra.IsAlgebraic (Polynomial K) (RatFunc K) :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors (Polynomial K))
    exact trdeg_eq_zero
  rw [h0, add_zero, Polynomial.trdeg_of_isDomain] at this
  exact this.symm

/-- **W3** for `K(X)`: the residue field of a valuation of `K(X)` extending `v` has transcendence
degree at most `1` over that of `v`. -/
theorem trdeg_residueField_ratFunc_le_one {w : Valuation (RatFunc K) Γ₁} [v.HasExtension w] :
    Algebra.trdeg (ResidueField v.valuationSubring) (ResidueField w.valuationSubring) ≤ 1 :=
  trdeg_residueField_le.trans trdeg_ratFunc.le

/-- **W2 + W3**: over an algebraically closed field `K`, a valuation `w` of `K(X)` extending `v`
whose residue field is transcendental over that of `v` is a Gauss valuation `gaussRat v a r` (the
value group condition of `eq_gaussRat` is automatic by W3). -/
theorem eq_gaussRat' [IsAlgClosed K] {w : Valuation (RatFunc K) Γ₀} [v.HasExtension w]
    (hw : ∀ c, w (algebraMap K (RatFunc K) c) = v c)
    (htr : Algebra.Transcendental (ResidueField v.valuationSubring)
      (ResidueField w.valuationSubring)) :
    ∃ (a : K) (r : Γ₀ˣ), w = gaussRat v a r := by
  refine eq_gaussRat hw (fun f ↦ ?_) htr
  obtain ⟨c, hc⟩ := exists_eq_of_transcendental trdeg_ratFunc.le htr f
  exact ⟨c, hc.trans (hw c)⟩

end SemistableReduction
