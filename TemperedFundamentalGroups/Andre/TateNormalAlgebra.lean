/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Normality of the coordinate rings of the Tate model

Commutative algebra for the normality of the explicit Tate model (`Andre/TateModel.lean`).

* `TateNormal.loc R hs`: the subring `R[1/s] = {z | ∃ n, s ^ n z ∈ R}` of a field `L`;
  `TateNormal.IntClosedIn R`: `R` is integrally closed in `L`.
* `IntClosedIn.loc`: localizations of integrally closed subrings are integrally closed.
* `IntClosedIn.of_loc` (**the `s`-lemma**): if `s ∈ R` is nonzero, `s R` is a radical ideal of
  `R` and `R[1/s]` lies in an integrally closed `T ⊇ R`, then `R` is integrally closed in `L`.
* `TateNormal.isIntegrallyClosed`: for a UFD `O` and `π b₄ b₆ ∈ O` such that
  `d = X² + 4 (π X³ + π b₄ X + b₆)` is squarefree in `O[X]`, the ring
  `O[X][Y] / (Y² + X Y − (π X³ + π b₄ X + b₆))` (the chart `w = 1` of the Tate model) is an
  integrally closed domain. Proof: trace and norm for the conjugation `Y ↦ -X - Y`, and
  `d q² ∈ O[X] ⇒ q ∈ O[X]` for `q ∈ Frac O[X]`, `d` squarefree.
-/

open Polynomial

namespace TemperedFundamentalGroups.TateNormal

section Subrings

variable {L : Type*} [Field L]

/-- The subring `R[1/s] = {z | ∃ n, s ^ n * z ∈ R}` of `L`. -/
def loc (R : Subring L) {s : L} (hs : s ∈ R) : Subring L where
  carrier := {z | ∃ n : ℕ, s ^ n * z ∈ R}
  mul_mem' := by
    rintro z w ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : s ^ (n + m) * (z * w) = (s ^ n * z) * (s ^ m * w) := by ring
    rw [this]
    exact R.mul_mem hn hm
  one_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro z w ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have : s ^ (n + m) * (z + w) = s ^ m * (s ^ n * z) + s ^ n * (s ^ m * w) := by ring
    rw [this]
    exact R.add_mem (R.mul_mem (R.pow_mem hs _) hn) (R.mul_mem (R.pow_mem hs _) hm)
  zero_mem' := ⟨0, by simp⟩
  neg_mem' := by
    rintro z ⟨n, hn⟩
    exact ⟨n, by rw [mul_neg]; exact R.neg_mem hn⟩

lemma mem_loc {R : Subring L} {s : L} (hs : s ∈ R) {z : L} :
    z ∈ loc R hs ↔ ∃ n : ℕ, s ^ n * z ∈ R := Iff.rfl

lemma le_loc {R : Subring L} {s : L} (hs : s ∈ R) : R ≤ loc R hs :=
  fun z hz ↦ ⟨0, by simpa using hz⟩

/-- `R ⊆ L` is integrally closed in `L`. -/
def IntClosedIn (R : Subring L) : Prop := ∀ z : L, IsIntegral R z → z ∈ R

lemma isIntegral_of_le {R T : Subring L} (h : R ≤ T) {z : L} (hz : IsIntegral R z) :
    IsIntegral T z := by
  obtain ⟨p, hp, hpz⟩ := hz
  refine ⟨p.map (Subring.inclusion h), hp.map _, ?_⟩
  rw [eval₂_map]
  exact hpz

/-- If `e ^ N * c ∈ R` for all coefficients `c` of a monic `p` over `T ⊇ R` and `z` is a root
of `p`, then `e ^ N * z` is integral over `R`. -/
lemma isIntegral_mul_pow {R T : Subring L} (hRT : R ≤ T) {e : L} (he : e ∈ R) {N : ℕ}
    (p : T[X]) (hp : p.Monic) (hcoeff : ∀ i, e ^ N * (p.coeff i : L) ∈ R) {z : L}
    (hz : p.eval₂ T.subtype z = 0) : IsIntegral R (e ^ N * z) := by
  have heT : e ^ N ∈ T := hRT (R.pow_mem he N)
  set q : T[X] := p.scaleRoots ⟨e ^ N, heT⟩ with hq
  have hqc : ↑(q.map T.subtype).coeffs ⊆ (R : Set L) := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Polynomial.mem_coeffs_iff.1 hc
    rw [coeff_map, hq, coeff_scaleRoots]
    simp only [Subring.coe_subtype, Subring.coe_mul, Subring.coe_pow]
    rcases lt_trichotomy i p.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, p.natDegree - i = k + 1 := ⟨p.natDegree - i - 1, by omega⟩
      rw [hk, pow_succ, ← mul_assoc, mul_comm (p.coeff i : L), mul_assoc,
        mul_comm (p.coeff i : L)]
      rw [mul_comm]
      exact R.mul_mem (hcoeff i) (R.pow_mem (R.pow_mem he N) k)
    · subst hi
      rw [Nat.sub_self, pow_zero, mul_one]
      have : (p.coeff p.natDegree : L) = 1 := by
        rw [← leadingCoeff, hp.leadingCoeff]; rfl
      rw [this]
      exact R.one_mem
    · rw [coeff_eq_zero_of_natDegree_lt hi]
      simp
  refine ⟨toSubring _ R hqc, ?_, ?_⟩
  · rw [monic_toSubring]
    exact ((monic_scaleRoots_iff _).2 hp).map _
  · have h1 := scaleRoots_eval₂_eq_zero (s := (⟨e ^ N, heT⟩ : T)) T.subtype hz
    rw [← hq] at h1
    change (toSubring _ R hqc).eval₂ R.subtype (e ^ N * z) = 0
    rw [← eval_map, map_toSubring, eval_map]
    exact h1

/-- **Localizations of integrally closed subrings are integrally closed.** -/
lemma IntClosedIn.loc {R : Subring L} (hR : IntClosedIn R) {e : L} (he : e ∈ R) :
    IntClosedIn (TateNormal.loc R he) := by
  intro z ⟨p, hp, hpz⟩
  choose n hn using fun i ↦ (p.coeff i).2
  set N := ∑ i ∈ Finset.range (p.natDegree + 1), n i
  have hcoeff : ∀ i, e ^ N * ((p.coeff i : TateNormal.loc R he) : L) ∈ R := by
    intro i
    by_cases hi : i ≤ p.natDegree
    · have : n i ≤ N := Finset.single_le_sum (f := n) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
      rw [← Nat.sub_add_cancel this, pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem he _) (hn i)
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
      simp
  exact ⟨N, hR _ (isIntegral_mul_pow (le_loc he) he p hp hcoeff hpz)⟩

/-- **The `s`-lemma.** Let `R ⊆ L` with `s ∈ R` nonzero such that `s R` is a radical ideal of
`R`, and `T ⊇ R` integrally closed in `L` with `T ⊆ R[1/s]`. Then `R` is integrally closed in
`L`. -/
lemma IntClosedIn.of_loc {R T : Subring L} {s : L} (hs : s ∈ R) (hs0 : s ≠ 0)
    (hrad : ∀ x ∈ R, ∀ n : ℕ, (∃ r ∈ R, x ^ n = s * r) → ∃ r ∈ R, x = s * r)
    (hRT : R ≤ T) (hT : IntClosedIn T) (hTR : ∀ z ∈ T, ∃ n : ℕ, s ^ n * z ∈ R) :
    IntClosedIn R := by
  intro z hz
  have hex : ∃ n : ℕ, s ^ n * z ∈ R := hTR z (hT z (isIntegral_of_le hRT hz))
  classical
  set n := Nat.find hex with hn
  have hmem : s ^ n * z ∈ R := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · rw [h0, pow_zero, one_mul] at hmem
    exact hmem
  exfalso
  obtain ⟨p, hp, hpz⟩ := hz
  set y : R := ⟨s ^ n * z, hmem⟩
  set sR : R := ⟨s, hs⟩
  set q := p.scaleRoots (sR ^ n)
  have hroot : q.IsRoot y := by
    have h1 := scaleRoots_eval₂_eq_zero (s := sR ^ n) R.subtype hpz
    apply Subtype.val_injective
    rw [ZeroMemClass.coe_zero, ← h1]
    change R.subtype (q.eval y) = _
    rw [← Polynomial.eval₂_hom]
    rfl
  have hdvd := dvd_term_of_isRoot_of_dvd_terms (p := sR) p.natDegree hroot fun j hj ↦ by
    rw [coeff_scaleRoots]
    rcases lt_or_gt_of_ne hj with hj | hj
    · obtain ⟨k, hk⟩ : ∃ k, p.natDegree - j = k + 1 := ⟨p.natDegree - j - 1, by omega⟩
      obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [hk, hm]
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (dvd_pow (dvd_pow_self _ (Nat.succ_ne_zero m))
        (Nat.succ_ne_zero k)) _) _
    · rw [coeff_eq_zero_of_natDegree_lt hj]
      simp
  rw [coeff_scaleRoots, Nat.sub_self, pow_zero, mul_one, ← leadingCoeff, hp.leadingCoeff,
    one_mul] at hdvd
  obtain ⟨r, hr⟩ := hdvd
  obtain ⟨r', hr'R, hr'⟩ := hrad (s ^ n * z) hmem p.natDegree
    ⟨r, r.2, by simpa using congrArg Subtype.val hr⟩
  obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have : s ^ m * z ∈ R := by
    have : s ^ m * z = r' := by
      apply mul_left_cancel₀ hs0
      rw [← hr', hm, pow_succ]
      ring
    rw [this]
    exact hr'R
  have := Nat.find_min hex (m := m) (by omega)
  exact this ‹_›

/-- A subring of a field which is integrally closed in it is an integrally closed domain. -/
lemma IntClosedIn.isIntegrallyClosed {R : Subring L} (h : IntClosedIn R) :
    IsIntegrallyClosed R := by
  have : IsIntegrallyClosedIn R L := by
    refine ⟨Subtype.val_injective, fun {x} ↦ ⟨fun hx ↦ ⟨⟨x, h x hx⟩, rfl⟩, ?_⟩⟩
    rintro ⟨y, rfl⟩
    exact isIntegral_algebraMap
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn R L

/-- `loc` is monotone in the following sense. -/
lemma loc_le_loc {R R' : Subring L} {s s' : L} (hs : s ∈ R) (hs' : s' ∈ R')
    (hR : R ≤ loc R' hs') {t : L} (ht : t ∈ loc R' hs') (hst : s * t = 1) :
    loc R hs ≤ loc R' hs' := by
  rintro z ⟨n, hn⟩
  have : z = (s ^ n * z) * t ^ n := by
    rw [mul_comm (s ^ n) z, mul_assoc, ← mul_pow, hst, one_pow, mul_one]
  rw [this]
  exact (loc R' hs').mul_mem (hR hn) ((loc R' hs').pow_mem ht n)

end Subrings



noncomputable section

variable {O : Type*} [CommRing O]
variable (π b₄ b₆ : O)

/-- `c = π X³ + π b₄ X + b₆ ∈ O[X]`. -/
def cpoly : O[X] := C π * X ^ 3 + C (π * b₄) * X + C b₆

/-- `d = X² + 4 c`, the discriminant of `fpoly` (over `O[X]`). -/
def dpoly : O[X] := X ^ 2 + 4 * cpoly π b₄ b₆

/-- `f = Y² + X Y − c ∈ O[X][Y]`: the Tate cubic in the chart `w = 1`. -/
def fpoly : O[X][X] := X ^ 2 + C X * X - C (cpoly π b₄ b₆)

lemma eval₂_fpoly {S : Type*} [CommRing S] (g : O[X] →+* S) (y : S) :
    (fpoly π b₄ b₆).eval₂ g y = y ^ 2 + g X * y - g (cpoly π b₄ b₆) := by
  simp [fpoly]

lemma fpoly_monic : (fpoly π b₄ b₆).Monic := by
  unfold fpoly
  monicity!

lemma dpoly_coeff_two : (dpoly π b₄ b₆).coeff 2 = 1 := by
  simp [dpoly, cpoly, coeff_X_pow]

/-- The coordinate ring `O[X][Y]/(f)` of the chart `w = 1`. -/
abbrev TateRing : Type _ := AdjoinRoot (fpoly π b₄ b₆)

/-- `b = Y` in the chart ring. -/
abbrev bA : TateRing π b₄ b₆ := AdjoinRoot.root _

lemma bA_sq : bA π b₄ b₆ ^ 2 =
    -(AdjoinRoot.of _ X * bA π b₄ b₆) + AdjoinRoot.of _ (cpoly π b₄ b₆) := by
  have h := AdjoinRoot.eval₂_root (fpoly π b₄ b₆)
  rw [eval₂_fpoly] at h
  linear_combination h

lemma exists_repr (α : TateRing π b₄ b₆) :
    ∃ p q : O[X], α = AdjoinRoot.of _ p + AdjoinRoot.of _ q * bA π b₄ b₆ := by
  induction α using AdjoinRoot.induction_on with
  | ih g =>
  induction g using Polynomial.induction_on with
  | C a => exact ⟨a, 0, by simp⟩
  | add g h hg hh =>
    obtain ⟨p, q, hpq⟩ := hg
    obtain ⟨p', q', hpq'⟩ := hh
    exact ⟨p + p', q + q', by rw [map_add, hpq, hpq', map_add, map_add]; ring⟩
  | monomial n a h =>
    obtain ⟨p, q, hpq⟩ := h
    refine ⟨q * cpoly π b₄ b₆, p - q * X, ?_⟩
    have : AdjoinRoot.mk (fpoly π b₄ b₆) (C a * X ^ (n + 1)) =
        AdjoinRoot.mk (fpoly π b₄ b₆) (C a * X ^ n) * bA π b₄ b₆ := by
      rw [pow_succ, ← mul_assoc, map_mul, AdjoinRoot.mk_X]
    rw [this, hpq, map_mul, map_sub, map_mul]
    linear_combination (AdjoinRoot.of _ q) * bA_sq π b₄ b₆

lemma eval₂_conj :
    (fpoly π b₄ b₆).eval₂ (Algebra.ofId O[X] (TateRing π b₄ b₆))
      (-AdjoinRoot.of _ X - bA π b₄ b₆) = 0 := by
  rw [eval₂_fpoly]
  change _ + AdjoinRoot.of _ X * _ - AdjoinRoot.of _ _ = _
  linear_combination bA_sq π b₄ b₆

/-- The conjugation `b ↦ -a - b` of the chart ring over `O[X]`. -/
def conj : TateRing π b₄ b₆ →ₐ[O[X]] TateRing π b₄ b₆ :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId O[X] _) _ (eval₂_conj π b₄ b₆)

@[simp] lemma conj_root : conj π b₄ b₆ (bA π b₄ b₆) = -AdjoinRoot.of _ X - bA π b₄ b₆ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

@[simp] lemma conj_of (p : O[X]) : conj π b₄ b₆ (AdjoinRoot.of _ p) = AdjoinRoot.of _ p :=
  (conj π b₄ b₆).commutes p

lemma conj_conj (x : TateRing π b₄ b₆) : conj π b₄ b₆ (conj π b₄ b₆ x) = x := by
  have : (conj π b₄ b₆).comp (conj π b₄ b₆) = AlgHom.id _ _ := by
    apply AdjoinRoot.algHom_ext
    simp only [AlgHom.comp_apply, conj_root, map_sub, map_neg, AlgHom.id_apply]
    rw [conj_of]
    ring
  exact congrArg (fun φ ↦ φ x) this

lemma conj_injective : Function.Injective (conj π b₄ b₆) :=
  Function.LeftInverse.injective (conj_conj π b₄ b₆)

lemma mul_conj (p q : O[X]) :
    (AdjoinRoot.of _ p + AdjoinRoot.of _ q * bA π b₄ b₆) *
      conj π b₄ b₆ (AdjoinRoot.of _ p + AdjoinRoot.of _ q * bA π b₄ b₆) =
      AdjoinRoot.of (fpoly π b₄ b₆) (p ^ 2 - X * p * q - cpoly π b₄ b₆ * q ^ 2) := by
  simp only [map_add, map_mul, conj_of, conj_root, map_sub, map_pow]
  linear_combination (-(AdjoinRoot.of (fpoly π b₄ b₆) q) ^ 2) * bA_sq π b₄ b₆

section Domain

variable [IsDomain O]

lemma fpoly_natDegree : (fpoly π b₄ b₆).natDegree = 2 := by
  unfold fpoly
  compute_degree!

lemma not_isUnit_dpoly : ¬ IsUnit (dpoly π b₄ b₆) := by
  rw [Polynomial.isUnit_iff]
  rintro ⟨r, -, hr⟩
  have := dpoly_coeff_two π b₄ b₆
  rw [← hr, coeff_C] at this
  simp at this

/-- The discriminant `Δ` of `y² + xy = x³ + π² b₄ x + π² b₆`
(`a₁ = 1`, `a₂ = a₃ = 0`, `a₄ = π² b₄`, `a₆ = π² b₆`). -/
def tateDisc : O :=
  -(π ^ 2 * b₆ - (π ^ 2 * b₄) ^ 2) - 64 * (π ^ 2 * b₄) ^ 3 - 432 * (π ^ 2 * b₆) ^ 2 +
    72 * (π ^ 2 * b₄) * (π ^ 2 * b₆)

/-- `Δ = -π² E`; `E` is, up to `64 π`, the resultant of `d` and `d'`. -/
def tateE : O :=
  64 * b₄ ^ 3 * π ^ 4 - b₄ ^ 2 * π ^ 2 - 72 * b₄ * b₆ * π ^ 2 + 432 * b₆ ^ 2 * π ^ 2 + b₆

omit [IsDomain O] in
lemma tateDisc_eq : tateDisc π b₄ b₆ = -(π ^ 2 * tateE π b₄ b₆) := by
  simp only [tateDisc, tateE]
  ring

omit [IsDomain O] in
/-- The discriminant of a Weierstrass curve of Tate type. -/
lemma Δ_eq_tateDisc {K : Type*} [CommRing K] (φ : O →+* K) (W : WeierstrassCurve K)
    (h₁ : W.a₁ = 1) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (h₄ : W.a₄ = φ (π ^ 2 * b₄))
    (h₆ : W.a₆ = φ (π ^ 2 * b₆)) : W.Δ = φ (tateDisc π b₄ b₆) := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, h₁, h₂, h₃, h₄, h₆, tateDisc, map_sub, map_add, map_mul, map_pow,
    map_neg, map_ofNat]
  ring

/-- **`d` is squarefree for a curve of Tate type with `Δ ≠ 0`, if `2 ≠ 0`.** Indeed
`-2 U d + V d' = 8 E` for explicit `U, V ∈ O[X]`, so a square factor of `d` divides the nonzero
constant `8 E` and hence is a unit (the coefficient of `X²` in `d` is `1`). -/
theorem squarefree_dpoly (h2 : (2 : O) ≠ 0) (hΔ : tateDisc π b₄ b₆ ≠ 0) :
    Squarefree (dpoly π b₄ b₆) := by
  have hE : tateE π b₄ b₆ ≠ 0 := by
    intro h
    rw [tateDisc_eq, h, mul_zero, neg_zero] at hΔ
    exact hΔ rfl
  intro q ⟨r, hr⟩
  have hq1 : q ∣ dpoly π b₄ b₆ := ⟨q * r, by rw [hr]; ring⟩
  have hq2 : q ∣ derivative (dpoly π b₄ b₆) := by
    rw [hr, derivative_mul, derivative_mul]
    exact ⟨derivative q * r + derivative q * r + q * derivative r, by ring⟩
  set U : O[X] := C (288 * b₄ * π ^ 3 - 6 * π) * X + C (60 * b₄ * π ^ 2 - 432 * b₆ * π ^ 2 - 1)
  set V : O[X] := C (192 * b₄ * π ^ 3 - 4 * π) * X ^ 2 +
    C (56 * b₄ * π ^ 2 - 288 * b₆ * π ^ 2 - 1) * X +
    C (128 * b₄ ^ 2 * π ^ 3 - 2 * b₄ * π - 24 * b₆ * π)
  have hid : C (8 * tateE π b₄ b₆) =
      -2 * U * dpoly π b₄ b₆ + V * derivative (dpoly π b₄ b₆) := by
    have hd' : derivative (dpoly π b₄ b₆) = C (12 * π) * X ^ 2 + 2 * X + C (4 * π * b₄) := by
      simp only [dpoly, cpoly, derivative_add, derivative_mul, derivative_X_pow, derivative_C,
        derivative_X, derivative_ofNat, map_mul, map_ofNat]
      simp only [Nat.cast_ofNat, zero_mul, zero_add, mul_one, Nat.add_one_sub_one, pow_one,
        add_zero]
      rw [show (C 2 : O[X]) = 2 from map_ofNat C 2, show (C 3 : O[X]) = 3 from map_ofNat C 3]
      ring
    rw [hd']
    simp only [U, V, dpoly, cpoly, tateE, map_add, map_sub, map_mul, map_pow, map_ofNat, map_one]
    ring
  have hq : q ∣ C (8 * tateE π b₄ b₆) := by
    rw [hid]
    exact dvd_add (dvd_mul_of_dvd_right hq1 _) (dvd_mul_of_dvd_right hq2 _)
  have h8 : (8 : O) ≠ 0 := by
    rw [show (8 : O) = 2 * 2 * 2 by norm_num]
    exact mul_ne_zero (mul_ne_zero h2 h2) h2
  have hdeg : q.natDegree = 0 := by
    have := natDegree_le_of_dvd hq (C_ne_zero.2 (mul_ne_zero h8 hE))
    rwa [natDegree_C, Nat.le_zero] at this
  rw [eq_C_of_natDegree_eq_zero hdeg] at hr ⊢
  have h0 := congrArg (coeff · 2) hr
  rw [dpoly_coeff_two, ← map_mul, coeff_C_mul] at h0
  exact isUnit_C.2 (IsUnit.of_mul_eq_one (q.coeff 0 * r.coeff 2) (by rw [h0]; ring))

variable [UniqueFactorizationMonoid O]

variable {π b₄ b₆}

omit [UniqueFactorizationMonoid O] in
lemma fpoly_irreducible (hd : Squarefree (dpoly π b₄ b₆)) : Irreducible (fpoly π b₄ b₆) := by
  rw [(fpoly_monic π b₄ b₆).irreducible_iff_roots_eq_zero_of_degree_le_three
    (by rw [fpoly_natDegree]) (by rw [fpoly_natDegree]; norm_num)]
  refine Multiset.eq_zero_of_forall_notMem fun r hr ↦ ?_
  rw [mem_roots (fpoly_monic π b₄ b₆).ne_zero, IsRoot, fpoly] at hr
  simp only [eval_sub, eval_add, eval_pow, eval_X, eval_mul, eval_C] at hr
  have hsq : dpoly π b₄ b₆ = (2 * r + X) * (2 * r + X) := by
    rw [dpoly]
    linear_combination (-4 : O[X]) * hr
  exact not_isUnit_dpoly π b₄ b₆ (hsq ▸ (hd _ ⟨1, by rw [hsq, mul_one]⟩).mul
    (hd _ ⟨1, by rw [hsq, mul_one]⟩))

variable (π b₄ b₆)

instance [Fact (Squarefree (dpoly π b₄ b₆))] : IsDomain (TateRing π b₄ b₆) :=
  AdjoinRoot.isDomain_of_prime (UniqueFactorizationMonoid.irreducible_iff_prime.1
    (fpoly_irreducible Fact.out))

omit [UniqueFactorizationMonoid O] in
lemma of_injective : Function.Injective (AdjoinRoot.of (fpoly π b₄ b₆)) :=
  AdjoinRoot.of.injective_of_degree_ne_zero (by
    rw [degree_eq_natDegree (fpoly_monic π b₄ b₆).ne_zero, fpoly_natDegree]; decide)

/-- The function field of the Tate curve. -/
abbrev TateField : Type _ := FractionRing (TateRing π b₄ b₆)

omit [UniqueFactorizationMonoid O] in
lemma algebraMap_injective : Function.Injective (algebraMap O[X] (TateField π b₄ b₆)) := by
  rw [IsScalarTower.algebraMap_eq O[X] (TateRing π b₄ b₆) (TateField π b₄ b₆), RingHom.coe_comp,
    AdjoinRoot.algebraMap_eq]
  exact (IsFractionRing.injective (TateRing π b₄ b₆) _).comp (of_injective π b₄ b₆)

variable [Fact (Squarefree (dpoly π b₄ b₆))]

/-- An element of `L` which is a quotient of elements of `O[X]` and integral over `O[X]` lies
in `O[X]`. -/
lemma mem_range_of_isIntegral {w : TateField π b₄ b₆} (hw : IsIntegral O[X] w) {r s : O[X]}
    (hs : s ≠ 0) (h : w * algebraMap O[X] _ s = algebraMap O[X] _ r) :
    ∃ t, w = algebraMap O[X] (TateField π b₄ b₆) t := by
  letI : FaithfulSMul O[X] (TateField π b₄ b₆) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap_injective π b₄ b₆)
  letI := FractionRing.liftAlgebra O[X] (TateField π b₄ b₆)
  haveI := FractionRing.isScalarTower_liftAlgebra O[X] (TateField π b₄ b₆)
  set k : FractionRing O[X] := IsLocalization.mk' _ r ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩
  have hk : algebraMap (FractionRing O[X]) (TateField π b₄ b₆) k = w := by
    have hs' : algebraMap O[X] (TateField π b₄ b₆) s ≠ 0 :=
      (map_ne_zero_iff _ (algebraMap_injective π b₄ b₆)).2 hs
    simp only [k]
    rw [IsFractionRing.mk'_eq_div, map_div₀, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, ← h, mul_div_assoc, div_self hs', mul_one]
  rw [← hk, isIntegral_algebraMap_iff
    (algebraMap (FractionRing O[X]) (TateField π b₄ b₆)).injective] at hw
  obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.1 hw
  exact ⟨t, by rw [← hk, ← ht, ← IsScalarTower.algebraMap_apply]⟩

/-- The conjugation extended to the function field. -/
def conjR : TateField π b₄ b₆ →+* TateField π b₄ b₆ :=
  IsLocalization.map (M := nonZeroDivisors (TateRing π b₄ b₆)) (S := TateField π b₄ b₆)
    (T := nonZeroDivisors (TateRing π b₄ b₆)) (TateField π b₄ b₆)
    (conj π b₄ b₆ : TateRing π b₄ b₆ →+* _)
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (conj_injective π b₄ b₆))

lemma conjR_algebraMap (x : TateRing π b₄ b₆) :
    conjR π b₄ b₆ (algebraMap _ _ x) = algebraMap _ _ (conj π b₄ b₆ x) :=
  IsLocalization.map_eq (M := nonZeroDivisors (TateRing π b₄ b₆)) (S := TateField π b₄ b₆)
    (T := nonZeroDivisors (TateRing π b₄ b₆)) _ _

lemma conjR_algebraMap' (r : O[X]) :
    conjR π b₄ b₆ (algebraMap O[X] _ r) = algebraMap O[X] _ r := by
  rw [IsScalarTower.algebraMap_apply O[X] (TateRing π b₄ b₆), conjR_algebraMap]
  simp

/-- The conjugation of the function field, as an `O[X]`-algebra map. -/
def conjL : TateField π b₄ b₆ →ₐ[O[X]] TateField π b₄ b₆ :=
  { conjR π b₄ b₆ with commutes' := conjR_algebraMap' π b₄ b₆ }

-- The instance problems in `FractionRing (AdjoinRoot _)` and the many field computations are slow.
set_option synthInstance.maxHeartbeats 200000 in
-- The instance problems in `FractionRing (AdjoinRoot _)` and the many field computations are slow.
set_option maxHeartbeats 1000000 in
/-- **The chart ring `O[X][Y]/(f)` is integrally closed** when `d = X² + 4c` is squarefree. -/
theorem isIntegrallyClosed : IsIntegrallyClosed (TateRing π b₄ b₆) := by
  set L := TateField π b₄ b₆
  set ι := algebraMap O[X] L
  set σ := conjR π b₄ b₆
  have hι : ∀ p : O[X], algebraMap (TateRing π b₄ b₆) L (AdjoinRoot.of _ p) = ι p := fun p ↦
    (IsScalarTower.algebraMap_apply O[X] (TateRing π b₄ b₆) L p).symm
  set bL := algebraMap (TateRing π b₄ b₆) L (bA π b₄ b₆)
  have hbL : bL ^ 2 = -(ι X * bL) + ι (cpoly π b₄ b₆) := by
    have := congrArg (algebraMap (TateRing π b₄ b₆) L) (bA_sq π b₄ b₆)
    rwa [map_pow, map_add, map_neg, map_mul, hι, hι] at this
  have hσb : σ bL = -ι X - bL := by
    rw [conjR_algebraMap, conj_root, map_sub, map_neg, hι]
  have hσι : ∀ p, σ (ι p) = ι p := conjR_algebraMap' π b₄ b₆
  rw [isIntegrallyClosed_iff L]
  intro z hz
  haveI : Module.Finite O[X] (TateRing π b₄ b₆) := (fpoly_monic π b₄ b₆).finite_adjoinRoot
  have hzP : IsIntegral O[X] z := isIntegral_trans z hz
  obtain ⟨α, β, hβ, rfl⟩ := IsFractionRing.div_surjective (A := TateRing π b₄ b₆) z
  obtain ⟨p₀, q₀, hα⟩ := exists_repr π b₄ b₆ (α * conj π b₄ b₆ β)
  obtain ⟨p₁, q₁, hβ'⟩ := exists_repr π b₄ b₆ β
  set n := p₁ ^ 2 - X * p₁ * q₁ - cpoly π b₄ b₆ * q₁ ^ 2
  have hn : β * conj π b₄ b₆ β = AdjoinRoot.of _ n := by rw [hβ']; exact mul_conj π b₄ b₆ _ _
  have hβ0 : β ≠ 0 := nonZeroDivisors.ne_zero hβ
  have hβL : algebraMap _ L β ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact hβ0
  have hσβL : algebraMap _ L (conj π b₄ b₆ β) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact fun h ↦ hβ0 (conj_injective π b₄ b₆ (h.trans (map_zero _).symm))
  have h2 : algebraMap _ L β * algebraMap _ L (conj π b₄ b₆ β) = ι n := by
    rw [← map_mul, hn, hι]
  have hn0 : ι n ≠ 0 := h2 ▸ mul_ne_zero hβL hσβL
  have hn0' : n ≠ 0 := fun h ↦ hn0 (by rw [h, map_zero])
  obtain ⟨p, hp⟩ : ∃ p : L, p * ι n = ι p₀ := ⟨ι p₀ / ι n, div_mul_cancel₀ _ hn0⟩
  obtain ⟨q, hq⟩ : ∃ q : L, q * ι n = ι q₀ := ⟨ι q₀ / ι n, div_mul_cancel₀ _ hn0⟩
  have hzpq : algebraMap _ L α / algebraMap _ L β = p + q * bL := by
    have h1 : algebraMap _ L α * algebraMap _ L (conj π b₄ b₆ β) = ι p₀ + ι q₀ * bL := by
      rw [← map_mul, hα, map_add, map_mul, hι, hι]
    rw [div_eq_iff hβL]
    apply mul_right_cancel₀ hσβL
    rw [h1, mul_assoc, h2]
    linear_combination -hp - bL * hq
  rw [hzpq] at hzP ⊢
  have hσp : σ p = p := by
    apply mul_right_cancel₀ hn0
    calc σ p * ι n = σ (p * ι n) := by rw [map_mul, hσι]
      _ = p * ι n := by rw [hp, hσι]
  have hσq : σ q = q := by
    apply mul_right_cancel₀ hn0
    calc σ q * ι n = σ (q * ι n) := by rw [map_mul, hσι]
      _ = q * ι n := by rw [hq, hσι]
  have hσz : σ (p + q * bL) = p + q * (-ι X - bL) := by
    rw [map_add, map_mul, hσp, hσq, hσb]
  have hzσ : IsIntegral O[X] (p + q * (-ι X - bL)) := hσz ▸ hzP.map (conjL π b₄ b₆)
  -- the trace
  obtain ⟨t, ht⟩ := mem_range_of_isIntegral π b₄ b₆ (hzP.add hzσ)
    (r := 2 * p₀ - X * q₀) hn0' (by
      simp only [map_sub, map_mul, map_ofNat]
      linear_combination 2 * hp - ι X * hq)
  -- the norm
  obtain ⟨ν, hν⟩ := mem_range_of_isIntegral π b₄ b₆ (hzP.mul hzσ)
    (r := p₀ ^ 2 - X * p₀ * q₀ - cpoly π b₄ b₆ * q₀ ^ 2) (s := n ^ 2)
    (pow_ne_zero 2 hn0') (by
      simp only [map_sub, map_mul, map_pow]
      linear_combination (p * ι n + ι p₀ - ι X * q * ι n) * hp +
        (-(ι X) * ι p₀ - ι (cpoly π b₄ b₆) * (q * ι n + ι q₀)) * hq + (-(q ^ 2 * ι n ^ 2)) * hbL)
  -- `d q ∈ O[X]`
  have hdι : ι (dpoly π b₄ b₆) = ι X ^ 2 + 4 * ι (cpoly π b₄ b₆) := by
    simp [dpoly, map_ofNat]
  have hdq : (ι (dpoly π b₄ b₆) * q) ^ 2 = ι (dpoly π b₄ b₆ * (t ^ 2 - 4 * ν)) := by
    rw [map_mul, map_sub, map_mul, map_pow, map_ofNat, ← ht, ← hν]
    linear_combination (ι (dpoly π b₄ b₆) * q ^ 2) * hdι - 4 * ι (dpoly π b₄ b₆) * q ^ 2 * hbL
  obtain ⟨t₂, ht₂⟩ := mem_range_of_isIntegral π b₄ b₆ (r := dpoly π b₄ b₆ * q₀)
    (IsIntegral.of_pow two_pos (hdq ▸ isIntegral_algebraMap)) (s := n) hn0'
    (by rw [map_mul]; linear_combination ι (dpoly π b₄ b₆) * hq)
  have hd2 : dpoly π b₄ b₆ ∣ t₂ ^ 2 := by
    refine ⟨t ^ 2 - 4 * ν, algebraMap_injective π b₄ b₆ ?_⟩
    rw [map_pow, ← ht₂, hdq]
  obtain ⟨t₃, rfl⟩ := (Fact.out : Squarefree (dpoly π b₄ b₆)).isRadical 2 t₂ hd2
  have hd0 : ι (dpoly π b₄ b₆) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap_injective π b₄ b₆)).2 (Fact.out : Squarefree _).ne_zero
  have hq3 : q = ι t₃ := mul_left_cancel₀ hd0 (by rw [ht₂, map_mul])
  -- `p ∈ O[X]`
  have hbint : IsIntegral O[X] bL :=
    (AdjoinRoot.isIntegral_root' (fpoly_monic π b₄ b₆)).map
      (IsScalarTower.toAlgHom O[X] (TateRing π b₄ b₆) L)
  have hpint : IsIntegral O[X] p := by
    have := hzP.sub ((isIntegral_algebraMap (x := t₃)).mul hbint)
    rwa [← hq3, add_sub_cancel_right] at this
  obtain ⟨t₄, ht₄⟩ := mem_range_of_isIntegral π b₄ b₆ (r := p₀) (s := n) hpint hn0' hp
  refine ⟨AdjoinRoot.of _ t₄ + AdjoinRoot.of _ t₃ * bA π b₄ b₆, ?_⟩
  rw [map_add, map_mul, hι, hι, ← ht₄, hq3]

end Domain

end

end TemperedFundamentalGroups.TateNormal
