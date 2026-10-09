/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.RiemannRoch

/-!
# Rational residue curves with two directions

Blueprint §9.9, W7 layer S3 (the "two directions" lemma). Let `k` be algebraically closed and
`κ / k` a function field of one variable of genus `0` (the residue curve of a type-2 point of the
open annulus). If `z ∈ κ ∖ k` (the residue `x̄` of the coordinate) has exactly one zero `P` and
one pole `Q` (the two directions of the residue curve towards the two ends of the annulus), then
`κ = k(t)` for some `t` with divisor `P - Q`, and `z = λ tᵈ` with `λ ∈ kˣ` and
`d = [κ : k(z)]` (`exists_eq_smul_pow`). In particular the residue extension `κ / k(z)` is
"Kummer" (`tᵈ = λ⁻¹ z`); it is separable iff `p ∤ d`, and purely inseparable when `d` is a power
of `p` — both happen along the annuli of a wild cover.

* `divisor_eq_zero_iff`: `(f) = 0` iff `f ∈ k` (for `f ≠ 0`);
* `exists_divisor_eq_single_sub_single`: in genus `0`, every degree-`0` divisor `P - Q` is
  principal (Riemann's inequality `ℓ(Q - P) ≥ 1`);
* `adjoin_eq_top_of_poleDivisor`: an element with a single simple pole generates `κ`
  (`deg (t)_∞ = [κ : k(t)]`).
-/

open IntermediateField Valuation WithZero
open scoped WithZero

namespace SemistableReduction

open CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k] [IsCurveFunctionField k κ]

lemma poleDivisor_eq_toNat (f : κ) (P : CurvePlace k κ) :
    poleDivisor k f P = (-divisor k f P).toNat := by
  rw [poleDivisor_apply, divisor_apply, neg_neg, CurvePlace.poleOrder]

/-- `f` has trivial divisor iff it is a constant. -/
lemma divisor_eq_zero_iff {f : κ} : divisor k f = 0 ↔ f ∈ (algebraMap k κ).range := by
  constructor
  · intro h
    rw [← poleNorm_eq_zero_iff (k := k)]
    refine Nat.eq_zero_of_le_zero (poleNorm_le_iff.2 fun P ↦ ?_)
    have := poleDivisor_eq_toNat (k := k) f P
    rw [h, Finsupp.zero_apply, neg_zero, Int.toNat_zero, poleDivisor_apply] at this
    exact_mod_cast this.le
  · rintro ⟨c, rfl⟩
    rw [divisor, ← map_inv₀, poleDivisor_algebraMap, poleDivisor_algebraMap, sub_self]

lemma divisor_pow {f : κ} (hf : f ≠ 0) (n : ℕ) : divisor k (f ^ n) = n • divisor k f := by
  induction n with
  | zero => simpa using (divisor_eq_zero_iff (k := k) (f := (1 : κ))).2 ⟨1, map_one _⟩
  | succ n ih => rw [pow_succ, divisor_mul (pow_ne_zero n hf) hf, ih, succ_nsmul]

lemma divisor_div {f g : κ} (hf : f ≠ 0) (hg : g ≠ 0) :
    divisor k (f / g) = divisor k f - divisor k g := by
  rw [div_eq_mul_inv, divisor_mul hf (inv_ne_zero hg), divisor_inv, sub_eq_add_neg]

/-- **In genus `0` every divisor `P - Q` is principal** (Riemann's inequality: `ℓ(Q - P) ≥ 1`). -/
theorem exists_divisor_eq_single_sub_single (hg : genus k κ = 0) (P Q : CurvePlace k κ) :
    ∃ t : κ, t ≠ 0 ∧ divisor k t = Finsupp.single P 1 - Finsupp.single Q 1 := by
  set D : CurveDivisor k κ := Finsupp.single Q 1 - Finsupp.single P 1
  have hdeg : D.degree = 0 := by simp [D]
  have hell := riemann_inequality D
  rw [hdeg, hg] at hell
  have hpos : 0 < Module.finrank k (rrSpace D) := by
    have : (1 : ℤ) ≤ ell D := by simpa using hell
    unfold ell at this
    omega
  obtain ⟨⟨t, ht⟩, ht0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 hpos
  have ht0' : t ≠ 0 := fun h ↦ ht0 (Subtype.ext h)
  refine ⟨t, ht0', ?_⟩
  have hle := (mem_rrSpace_iff_le ht0').1 ht
  have h0 := eq_zero_of_degree_eq_zero hle (by rw [map_add, hdeg, degree_divisor, add_zero])
  rw [← sub_eq_zero, sub_eq_add_neg, add_comm]
  convert h0 using 1
  simp [D]

/-- An element with divisor `P - Q` (`P ≠ Q`) has the single simple pole `Q`, so it generates
`κ`. -/
theorem adjoin_eq_top_of_divisor {t : κ} {P Q : CurvePlace k κ} (hPQ : P ≠ Q)
    (ht : divisor k t = Finsupp.single P 1 - Finsupp.single Q 1) : k⟮t⟯ = ⊤ := by
  have htk : t ∉ (algebraMap k κ).range := by
    rw [← divisor_eq_zero_iff, ht]
    intro h
    have := congrArg (fun D : CurveDivisor k κ ↦ D P) h
    simp [hPQ.symm] at this
  have hpole : poleDivisor k t = Finsupp.single Q 1 := by
    ext R
    rw [poleDivisor_eq_toNat, ht]
    by_cases hRQ : R = Q
    · subst hRQ
      simp [hPQ]
    · by_cases hRP : R = P
      · subst hRP
        simp [hRQ]
      · simp [Ne.symm hRP, Ne.symm hRQ]
  have := degree_poleDivisor htk
  rw [hpole] at this
  refine IntermediateField.finrank_eq_one_iff_eq_top.1 ?_
  simpa using this.symm

/-- **The two-directions lemma.** Let `κ` have genus `0` and let `z ∈ κ ∖ k` have exactly one zero
`P` and one pole `Q`. Then `κ = k(t)` with `(t) = P - Q`, and `z = c · tᵈ` with `c ∈ kˣ` and
`d = [κ : k(z)]`. -/
theorem exists_eq_smul_pow (hg : genus k κ = 0) {z : κ} (hz : z ∉ (algebraMap k κ).range)
    {P Q : CurvePlace k κ} (hP : 0 < divisor k z P)
    (hPQ : ∀ R, divisor k z R ≠ 0 → R = P ∨ R = Q) :
    ∃ t : κ, k⟮t⟯ = ⊤ ∧ divisor k t = Finsupp.single P 1 - Finsupp.single Q 1 ∧
      ∃ c : k, c ≠ 0 ∧ z = algebraMap k κ c * t ^ Module.finrank k⟮z⟯ κ := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hz ⟨0, map_zero _⟩
  set a := divisor k z P
  have hsupp : ∀ R, R ≠ P → R ≠ Q → divisor k z R = 0 := fun R h1 h2 ↦ by
    by_contra h
    rcases hPQ R h with h' | h'
    exacts [h1 h', h2 h']
  have hdeg := degree_divisor (k := k) z
  have hne : P ≠ Q := by
    rintro rfl
    have : divisor k z = Finsupp.single P a := by
      ext R
      by_cases hR : R = P
      · subst hR
        simp [a]
      · simp [Ne.symm hR, hsupp R hR hR]
    rw [this] at hdeg
    simp at hdeg
    omega
  have hdz : divisor k z = Finsupp.single P a + Finsupp.single Q (divisor k z Q) := by
    ext R
    by_cases hRP : R = P
    · subst hRP
      simp [a, hne]
    · by_cases hRQ : R = Q
      · subst hRQ
        simp [Ne.symm hRP]
      · simp [Ne.symm hRP, Ne.symm hRQ, hsupp R hRP hRQ]
  have hb : divisor k z Q = -a := by
    rw [hdz, map_add] at hdeg
    simp at hdeg
    omega
  obtain ⟨t, ht0, ht⟩ := exists_divisor_eq_single_sub_single hg P Q
  refine ⟨t, adjoin_eq_top_of_divisor hne ht, ht, ?_⟩
  -- the degree `d = [κ : k(z)]` is the order `a` of the pole of `z`
  have hpole : poleDivisor k z = Finsupp.single Q (a.toNat : ℤ) := by
    ext R
    rw [poleDivisor_eq_toNat]
    by_cases hRQ : R = Q
    · subst hRQ
      simp [hb]
    · by_cases hRP : R = P
      · subst hRP
        simp [hRQ, a]
        omega
      · simp [Ne.symm hRQ, hsupp R hRP hRQ]
  have hd := degree_poleDivisor hz
  rw [hpole] at hd
  simp only [Finsupp.degree_single] at hd
  set d := Module.finrank k⟮z⟯ κ
  have had : a = d := by
    rw [← hd]
    omega
  have hdiv : divisor k (z / t ^ d) = 0 := by
    rw [divisor_div hz0 (pow_ne_zero _ ht0), divisor_pow ht0, ht, hdz, hb, had]
    ext R
    by_cases hRP : R = P
    · subst hRP
      simp [hne]
    · by_cases hRQ : R = Q
      · subst hRQ
        simp [Ne.symm hRP]
      · simp [Ne.symm hRP, Ne.symm hRQ]
  obtain ⟨c, hc⟩ := divisor_eq_zero_iff.1 hdiv
  refine ⟨c, ?_, ?_⟩
  · rintro rfl
    rw [map_zero, eq_comm, div_eq_zero_iff] at hc
    exact hc.elim hz0 (pow_ne_zero _ ht0)
  · rw [hc, div_mul_cancel₀ _ (pow_ne_zero _ ht0)]

end SemistableReduction
