/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.Dynamics.Newton
import Mathlib.RingTheory.Flat.Basic

/-!
# The Kummer normal form of maps between cusp factors (MR12 I3, generic core, layer 3)

Morphisms of tamely ramified coverings near a marked point are, on the formal cusp factors
`A[X']/(X'^{e'} − t)` ([Mzk1] §3.9 (1′A); `Admissible.CuspPiece`), of the form
`X ↦ u X'^{e'/e}` with `u^e = 1`: an element `y` with `y^e = t = X'^{e'}` is a unit times a power
of `X'`. This file proves this in generic commutative algebra, for a ring `B` with a nonzerodivisor
`x` such that `B/x` is reduced and `B` is `x`-adically separated:

* **`CuspNormalForm.pow_dvd_of_pow_dvd`**: `x^{de} ∣ y^e ⇒ x^d ∣ y`;
* **`CuspNormalForm.exists_normalForm`**: if `y^e = x^{e'} E` for an idempotent `E`, then
  `y = x^{e'/e} u` with `u^e = E`, and `e ∣ e'` unless `E = 0`;
* for the cusp factor `B = A[X']/(X'^{e'} − t)` the hypotheses follow from those on `A` and `t`
  (`isSMulRegular_root`, `isReduced_quot_root` via `quotRootEquiv : B/(X') ≃ A/(t)`,
  `separated_root`).

The normal form at the special fibre is what lifts to the levels of the M2 patching: `u` lifts
uniquely to a root of `U^e = Ẽ` (Hensel, `e` invertible), and `ũ X̃'^{e'/e}` is then an `e`-th
root of `t̃ Ẽ` at every level.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace CuspNormalForm

variable {B : Type u} [CommRing B] {x : B} (hx : IsSMulRegular B x)
  (hred : IsReduced (B ⧸ Ideal.span {x}))

include hx in
lemma pow_regular (k : ℕ) {a b : B} (h : x ^ k * a = x ^ k * b) : a = b := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    refine ih (hx ?_)
    change x * (x ^ k * a) = x * (x ^ k * b)
    rw [← mul_assoc, ← mul_assoc, ← pow_succ', h]

include hred in
lemma dvd_of_dvd_pow {y : B} {m : ℕ} (h : x ∣ y ^ m) : x ∣ y := by
  have h0 : (Ideal.Quotient.mk (Ideal.span {x}) y) ^ m = 0 := by
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact h
  have h1 : Ideal.Quotient.mk (Ideal.span {x}) y = 0 := (IsNilpotent.eq_zero ⟨m, h0⟩)
  rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h1

include hx hred in
/-- **`x^{de} ∣ y^e ⇒ x^d ∣ y`** for a nonzerodivisor `x` with `B/x` reduced. -/
theorem pow_dvd_of_pow_dvd {e : ℕ} (he : 0 < e) : ∀ (d : ℕ) {y : B}, x ^ (d * e) ∣ y ^ e →
    x ^ d ∣ y
  | 0, y, _ => by simp
  | d + 1, y, h => by
    have h1 : x ∣ y ^ e := (dvd_pow_self x (by positivity : (d + 1) * e ≠ 0)).trans h
    obtain ⟨z, rfl⟩ := dvd_of_dvd_pow hred h1
    obtain ⟨w, hw⟩ := h
    have h2 : z ^ e = x ^ (d * e) * w := by
      refine pow_regular hx e ?_
      rw [← mul_pow, hw, ← mul_assoc, ← pow_add]
      congr 2
      ring
    have h3 := pow_dvd_of_pow_dvd he d ⟨w, h2⟩
    rw [pow_succ']
    exact mul_dvd_mul_left x h3

variable (hsep : ∀ z : B, (∀ k : ℕ, x ^ k ∣ z) → z = 0)

include hx hred hsep in
/-- An element whose `e`-th power vanishes vanishes (`B` is reduced). -/
lemma eq_zero_of_pow_eq_zero {e : ℕ} (he : 0 < e) {y : B} (hy : y ^ e = 0) : y = 0 :=
  hsep y fun d ↦ pow_dvd_of_pow_dvd hx hred he d (by rw [hy]; exact dvd_zero _)

include hsep in
/-- An idempotent divisible by `x` vanishes. -/
lemma idem_eq_zero {E : B} (hE : IsIdempotentElem E) (h : x ∣ E) : E = 0 :=
  hsep E fun k ↦ by
    rw [← hE.pow_succ_eq k]
    exact (pow_dvd_pow x (Nat.le_succ k)).trans (pow_dvd_pow_of_dvd h (k + 1))

include hx hred hsep in
/-- **The Kummer normal form**: if `y^e = x^{e'} E` for an idempotent `E`, then `y = x^{e'/e} u`
with `u^e = E`, and `e ∣ e'` unless `E = 0`. -/
theorem exists_normalForm {e e' : ℕ} (he : 0 < e) {E : B} (hE : IsIdempotentElem E) {y : B}
    (hy : y ^ e = x ^ e' * E) :
    ∃ u : B, y = x ^ (e' / e) * u ∧ u ^ e = E ∧ (E ≠ 0 → e ∣ e') := by
  set q := e' / e
  set r := e' % e
  have hqr : e' = q * e + r := by rw [mul_comm]; exact (Nat.div_add_mod e' e).symm
  obtain ⟨u, rfl⟩ : x ^ q ∣ y := pow_dvd_of_pow_dvd hx hred he q
    ⟨x ^ r * E, by rw [hy, hqr, pow_add, mul_assoc]⟩
  have hu : u ^ e = x ^ r * E := by
    refine pow_regular hx (q * e) ?_
    calc x ^ (q * e) * u ^ e = (x ^ q * u) ^ e := by rw [mul_pow, ← pow_mul]
      _ = x ^ e' * E := hy
      _ = x ^ (q * e) * (x ^ r * E) := by rw [hqr, pow_add, mul_assoc]
  by_cases hr : r = 0
  · refine ⟨u, rfl, by rw [hu, hr, pow_zero, one_mul], fun _ ↦ ?_⟩
    exact Nat.dvd_of_mod_eq_zero hr
  · have hr0 : 0 < r := Nat.pos_of_ne_zero hr
    have hre : r < e := Nat.mod_lt e' he
    -- `x ∣ u^e`, so `x ∣ u`, so `x^e ∣ x^r E`, so `x ∣ E`
    have h1 : x ∣ u := dvd_of_dvd_pow hred (m := e) ⟨x ^ (r - 1) * E, by
      rw [hu, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hr0]⟩
    obtain ⟨v, hv⟩ := pow_dvd_pow_of_dvd h1 e
    have h2 : E = x ^ (e - r) * v := by
      refine pow_regular hx r ?_
      rw [← hu, hv, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' hre.le]
    have hE0 : E = 0 := idem_eq_zero hsep hE ⟨x ^ (e - r - 1) * v, by
      rw [h2, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel (Nat.sub_pos_of_lt hre)]⟩
    have hu0 : u = 0 := eq_zero_of_pow_eq_zero hx hred hsep he (by rw [hu, hE0, mul_zero])
    exact ⟨0, by simp [hu0], by rw [hE0, zero_pow he.ne'],
      fun h ↦ absurd hE0 h⟩

end CuspNormalForm

/-! ### The cusp factor `A[X']/(X'^{e'} − t)` -/

namespace CuspNormalForm

variable {A : Type u} [CommRing A] (t : A) {e' : ℕ} (he' : 0 < e')

/-- The cusp factor `A[X']/(X'^{e'} − t)`. -/
abbrev Cusp (t : A) (e' : ℕ) : Type u := AdjoinRoot (X ^ e' - C t)

lemma root_pow : (AdjoinRoot.root (X ^ e' - C t)) ^ e' = AdjoinRoot.of (X ^ e' - C t) t := by
  have h := AdjoinRoot.eval₂_root (X ^ e' - C t)
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero] at h
  exact h

include he' in
lemma monic : (X ^ e' - C t).Monic := monic_X_pow_sub_C t he'.ne'

include he' in
/-- `t` is a nonzerodivisor on the cusp factor if it is one on `A`. -/
lemma isSMulRegular_of (ht : IsSMulRegular A t) :
    IsSMulRegular (Cusp t e') (AdjoinRoot.of (X ^ e' - C t) t) := by
  haveI : Module.Free A (Cusp t e') :=
    Module.Free.of_basis (AdjoinRoot.powerBasis' (monic t he')).basis
  have h : IsSMulRegular (Cusp t e') (algebraMap A (Cusp t e') t) := ht.of_flat
  exact h

include he' in
/-- **The root `X'` is a nonzerodivisor** if `t` is one on `A`. -/
theorem isSMulRegular_root (ht : IsSMulRegular A t) :
    IsSMulRegular (Cusp t e') (AdjoinRoot.root (X ^ e' - C t)) := by
  intro a b hab
  have hab' : AdjoinRoot.root (X ^ e' - C t) * a = AdjoinRoot.root (X ^ e' - C t) * b := hab
  refine isSMulRegular_of t he' ht ?_
  change AdjoinRoot.of _ t * a = AdjoinRoot.of _ t * b
  have hp : AdjoinRoot.root (X ^ e' - C t) ^ e' =
      AdjoinRoot.root (X ^ e' - C t) ^ (e' - 1) * AdjoinRoot.root (X ^ e' - C t) := by
    rw [← pow_succ, Nat.sub_add_cancel he']
  rw [← root_pow, hp, mul_assoc, mul_assoc, hab']

include he' in
lemma eval_zero_mem : (X ^ e' - C t).eval₂ (Ideal.Quotient.mk (Ideal.span {t})) 0 = 0 := by
  rw [eval₂_sub, eval₂_X_pow, eval₂_C, zero_pow he'.ne', zero_sub, neg_eq_zero,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span rfl

/-- The map `A[X']/(X'^{e'} − t) → A/(t)`, `X' ↦ 0`. -/
noncomputable def toQuot : Cusp t e' →+* A ⧸ Ideal.span {t} :=
  AdjoinRoot.lift (Ideal.Quotient.mk _) 0 (eval_zero_mem t he')

lemma toQuot_of (a : A) : toQuot t he' (AdjoinRoot.of _ a) = Ideal.Quotient.mk _ a :=
  AdjoinRoot.lift_of _

lemma toQuot_root : toQuot t he' (AdjoinRoot.root _) = 0 :=
  AdjoinRoot.lift_root _

/-- Every element is a constant plus a multiple of the root. -/
lemma exists_eq_of_add_root_mul (b : Cusp t e') :
    ∃ (a : A) (c : Cusp t e'), b = AdjoinRoot.of _ a + AdjoinRoot.root _ * c := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective b
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := p)
  refine ⟨p.coeff 0, AdjoinRoot.mk _ q, ?_⟩
  rw [sub_eq_iff_eq_add] at hq
  have h := congrArg (AdjoinRoot.mk (X ^ e' - C t)) hq
  rw [h, map_add, map_mul, AdjoinRoot.mk_X, AdjoinRoot.mk_C, add_comm]

/-- **The kernel of `toQuot` is generated by the root.** -/
theorem ker_toQuot :
    RingHom.ker (toQuot t he') = Ideal.span {AdjoinRoot.root (X ^ e' - C t)} := by
  refine le_antisymm (fun b hb ↦ ?_) ?_
  · obtain ⟨a, c, rfl⟩ := exists_eq_of_add_root_mul t b
    rw [RingHom.mem_ker, map_add, map_mul, toQuot_root, zero_mul, add_zero, toQuot_of,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
    obtain ⟨a', rfl⟩ := hb
    rw [Ideal.mem_span_singleton, map_mul, ← root_pow]
    exact dvd_add (dvd_mul_of_dvd_left (dvd_pow_self _ he'.ne') _) (dvd_mul_right _ _)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact toQuot_root t he'

include he' in
/-- **`B/(X')` is reduced if `A/(t)` is.** -/
theorem isReduced_quot_root (hred : IsReduced (A ⧸ Ideal.span {t})) :
    IsReduced (Cusp t e' ⧸ Ideal.span {AdjoinRoot.root (X ^ e' - C t)}) := by
  refine ⟨fun z hz ↦ ?_⟩
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨m, hm⟩ := hz
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, ← ker_toQuot t he', RingHom.mem_ker,
    map_pow] at hm
  rw [Ideal.Quotient.eq_zero_iff_mem, ← ker_toQuot t he', RingHom.mem_ker]
  exact IsNilpotent.eq_zero ⟨m, hm⟩

include he' in
/-- **The cusp factor is `X'`-adically separated** if `A` is `t`-adically separated. -/
theorem separated_root (hsep : ∀ a : A, (∀ k : ℕ, t ^ k ∣ a) → a = 0) (z : Cusp t e')
    (hz : ∀ k : ℕ, AdjoinRoot.root (X ^ e' - C t) ^ k ∣ z) : z = 0 := by
  let pb := AdjoinRoot.powerBasis' (monic t he')
  have hcoord : ∀ (k : ℕ) (j : Fin pb.dim), t ^ k ∣ pb.basis.repr z j := by
    intro k j
    obtain ⟨w, hw⟩ := hz (e' * k)
    rw [pow_mul, root_pow, ← map_pow] at hw
    have : pb.basis.repr z = t ^ k • pb.basis.repr w := by
      rw [hw, ← map_smul, Algebra.smul_def]
      rfl
    rw [this, Finsupp.smul_apply, smul_eq_mul]
    exact dvd_mul_right _ _
  have h0 : pb.basis.repr z = 0 := Finsupp.ext fun j ↦ hsep _ fun k ↦ hcoord k j
  exact pb.basis.repr.injective (h0.trans (map_zero _).symm)

end CuspNormalForm

/-! ### Lifting roots of unity along nilpotent ideals -/

namespace CuspNormalForm

variable {S : Type u} [CommRing S] {N : Ideal S} (hN : ∀ x ∈ N, IsNilpotent x) {e : ℕ}
  (he : 0 < e) (heS : IsUnit (e : S))

include heS in
lemma isUnit_derivative {w : S} (hw : IsUnit w) :
    IsUnit (aeval w (derivative (X ^ e - 1 : S[X]))) := by
  rw [derivative_sub, derivative_one, sub_zero, derivative_X_pow, map_mul, aeval_C, map_pow,
    aeval_X, Algebra.algebraMap_self, RingHom.id_apply]
  exact heS.mul (hw.pow _)

include hN he heS in
/-- **Roots of unity lift along nilpotent ideals** (`e` invertible; Newton's method,
`Polynomial.existsUnique_nilpotent_sub_and_aeval_eq_zero`). -/
theorem exists_pow_eq_one_lift (w : S) (hw : w ^ e - 1 ∈ N) :
    ∃ v : S, v - w ∈ N ∧ v ^ e = 1 := by
  have hwu : IsUnit w := by
    have h1 : IsUnit (w ^ e) := by
      have := (hN _ hw).isUnit_add_one
      rwa [sub_add_cancel] at this
    exact (isUnit_pow_iff he.ne').mp h1
  have hP : IsNilpotent (aeval w (X ^ e - 1 : S[X])) := by
    rw [map_sub, map_pow, aeval_X, map_one]
    exact hN _ hw
  obtain ⟨v, ⟨hv1, hv2⟩, -⟩ := existsUnique_nilpotent_sub_and_aeval_eq_zero hP
    (isUnit_derivative heS hwu)
  rw [map_sub, map_pow, aeval_X, map_one, sub_eq_zero] at hv2
  refine ⟨v, ?_, hv2⟩
  -- uniqueness of the root modulo `N`
  set π := Ideal.Quotient.mk N
  have hS : IsUnit ((e : S ⧸ N)) := by
    have := heS.map π
    rwa [map_natCast] at this
  have hwq : aeval (π w) (X ^ e - 1 : (S ⧸ N)[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, map_one, ← map_pow, ← map_one π, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem]
    exact hw
  have huniq := existsUnique_nilpotent_sub_and_aeval_eq_zero (x := π w)
    (P := (X ^ e - 1 : (S ⧸ N)[X])) (by rw [hwq]; exact IsNilpotent.zero)
    (isUnit_derivative hS (hwu.map π))
  have h1 : π v = π w := huniq.unique ⟨by rw [← map_sub]; exact hv1.map π,
    by rw [map_sub, map_pow, aeval_X, map_one, ← map_pow, hv2, map_one,
      sub_self]⟩ ⟨by rw [sub_self]; exact IsNilpotent.zero, hwq⟩
  rw [← Ideal.Quotient.eq]
  exact h1

end CuspNormalForm

end SemistableReduction
