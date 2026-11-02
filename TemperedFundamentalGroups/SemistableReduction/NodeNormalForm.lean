/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspPieceHom

/-!
# The Kummer normal form at a node (MR12, generic core)

This is the node analogue of `CuspNormalForm`. Near a node the special fibre of a semistable
curve is formally `k[[s, t]]/(st)`: two branches `{t = 0}` (with coordinate `s`) and `{s = 0}`
(with coordinate `t`) meeting transversally. Morphisms of tamely ramified (Kummer) coverings
near a node are, on the special fibre, of the form `s ↦ a · s'^{e'/e}` on the `s`-branch and
`t ↦ b · t'^{e'/e}` on the `t`-branch, with `a^e`, `b^e` equal to the relevant idempotent.

We prove this in generic commutative algebra. Let `B` be a commutative ring and `s t : B` with
`(s) ∩ (t) = 0` (so in particular `s t = 0`), such that each branch satisfies the hypotheses of
the cusp normal form (`AdmissibleLift.CuspHom.NFHyp`): `s` is a nonzerodivisor on `B/(t)`,
`B/(s, t)` is reduced and `B/(t)` is `s`-adically separated, and symmetrically for `t` on `B/(s)`.

* **`isReduced_of_nfHyp`**: a ring satisfying `NFHyp` for some element is reduced; hence
  (**`mem_span_of_pow_mem`**) `y^e ∈ (s) ⇒ y ∈ (s)`.
* **`exists_nodeNormalForm`**: if `y^e = s^{e'} E` with `E` idempotent and `e, e' > 0`, then
  `E = 0` or `e ∣ e'`; if `E = 0` then `y = 0`; and if `e ∣ e'` then `y = s^{e'/e} a` with
  `a^e ≡ E` modulo `t`, i.e. on the `s`-branch. The proof applies
  `CuspNormalForm.exists_normalForm` on the branch `B/(t)`, lifts the twist, and notes that the
  difference `y − s^{e'/e} a` lies in `(t)` and (as `e'/e ≥ 1` and `y ∈ (s)`) in `(s)`.
  **`exists_nodeNormalForm'`** is the symmetric statement for `t`.
* **`mk_eq_of_pow_mul_eq`**: the twist is unique on the branch.

Only the class of the twist `a` on the `s`-branch is determined, and the twists on the two
branches are independent of each other in the special fibre. A "balance" condition relating
them (as in the deformation `s t = π`) is needed only for lifting the map to the levels, not
for the special-fibre normal form proved here.
-/

universe u

namespace SemistableReduction

namespace NodeNormalForm

open CuspNormalForm AdmissibleLift

/-! ### Consequences of the branch hypotheses -/

section Branch

variable {A : Type u} [CommRing A] {x : A}

/-- **A ring satisfying the cusp normal form hypotheses for some element is reduced.** -/
theorem isReduced_of_nfHyp (h : CuspHom.NFHyp A x) : IsReduced A := by
  refine ⟨fun z ⟨m, hm⟩ ↦ ?_⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · have h1 : (1 : A) = 0 := by simpa using hm
    simpa using congrArg (z * ·) h1
  · exact eq_zero_of_pow_eq_zero h.1 h.2.1 h.2.2 hm0 hm

end Branch

section Node

variable {B : Type u} [CommRing B] {s t : B}
  (hinter : ∀ x, x ∈ Ideal.span {s} → x ∈ Ideal.span {t} → x = 0)
  (hs : CuspHom.NFHyp (B ⧸ Ideal.span {t}) (Ideal.Quotient.mk _ s))
  (ht : CuspHom.NFHyp (B ⧸ Ideal.span {s}) (Ideal.Quotient.mk _ t))

include hinter in
/-- The branches meet in `0`; in particular `s t = 0`. -/
lemma mul_eq_zero_of_inter : s * t = 0 :=
  hinter _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl))

include ht in
/-- **`y^e ∈ (s) ⇒ y ∈ (s)`**, as `B/(s)` is reduced. -/
theorem mem_span_of_pow_mem {y : B} {e : ℕ} (hy : y ^ e ∈ Ideal.span {s}) :
    y ∈ Ideal.span {s} := by
  haveI := isReduced_of_nfHyp ht
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hy ⊢
  exact IsNilpotent.eq_zero ⟨e, by rwa [map_pow] at hy⟩

include ht in
lemma mem_span_of_pow_eq {e e' : ℕ} (he' : 0 < e') {E y : B} (hy : y ^ e = s ^ e' * E) :
    y ∈ Ideal.span {s} :=
  mem_span_of_pow_mem ht (by
    rw [hy, Ideal.mem_span_singleton]
    exact dvd_mul_of_dvd_left (dvd_pow_self s he'.ne') E)

include hinter ht in
/-- An idempotent in `(t)` vanishes. -/
lemma idem_eq_zero_of_mem {E : B} (hE : IsIdempotentElem E) (h : E ∈ Ideal.span {t}) :
    E = 0 := by
  refine hinter E ?_ h
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  refine idem_eq_zero ht.2.2 (hE.map (Ideal.Quotient.mk _)) ?_
  rw [Ideal.mem_span_singleton] at h
  exact map_dvd _ h

lemma mk_pow_eq (t : B) {e e' : ℕ} {E y : B} (hy : y ^ e = s ^ e' * E) :
    Ideal.Quotient.mk (Ideal.span {t}) y ^ e =
      Ideal.Quotient.mk (Ideal.span {t}) s ^ e' * Ideal.Quotient.mk (Ideal.span {t}) E := by
  rw [← map_pow, hy, map_mul, map_pow]

include hinter hs ht in
/-- If `y^e = s^{e'} E` with `E` idempotent, then `E = 0` or `e ∣ e'`. -/
theorem eq_zero_or_dvd {e e' : ℕ} (he : 0 < e) {E y : B} (hE : IsIdempotentElem E)
    (hy : y ^ e = s ^ e' * E) : E = 0 ∨ e ∣ e' := by
  obtain ⟨u, -, -, h3⟩ := exists_normalForm hs.1 hs.2.1 hs.2.2 he
    (hE.map (Ideal.Quotient.mk (Ideal.span {t}))) (mk_pow_eq t hy)
  by_cases h : Ideal.Quotient.mk (Ideal.span {t}) E = 0
  · exact Or.inl (idem_eq_zero_of_mem hinter ht hE (Ideal.Quotient.eq_zero_iff_mem.mp h))
  · exact Or.inr (h3 h)

include hinter hs ht in
/-- If `y^e = s^{e'} E` with `e' > 0` and `E = 0`, then `y = 0`. -/
theorem eq_zero_of_idem_eq_zero {e e' : ℕ} (he' : 0 < e') {E y : B}
    (hy : y ^ e = s ^ e' * E) (hE0 : E = 0) : y = 0 := by
  refine hinter y (mem_span_of_pow_eq ht he' hy) ?_
  haveI := isReduced_of_nfHyp hs
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact IsNilpotent.eq_zero ⟨e, by rw [← map_pow, hy, hE0, mul_zero, map_zero]⟩

include hinter hs ht in
/-- The normal form `y = s^{e'/e} a`, `a^e ≡ E mod t`, when `e ∣ e'`. -/
theorem exists_nodeNormalForm_of_dvd {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {E y : B}
    (hE : IsIdempotentElem E) (hy : y ^ e = s ^ e' * E) (hdvd : e ∣ e') :
    ∃ a : B, y = s ^ (e' / e) * a ∧
      Ideal.Quotient.mk (Ideal.span {t}) (a ^ e) = Ideal.Quotient.mk (Ideal.span {t}) E := by
  obtain ⟨u, hu1, hu2, -⟩ := exists_normalForm hs.1 hs.2.1 hs.2.2 he
    (hE.map (Ideal.Quotient.mk (Ideal.span {t}))) (mk_pow_eq t hy)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective u
  have hd : 0 < e' / e := Nat.div_pos (Nat.le_of_dvd he' hdvd) he
  refine ⟨a, ?_, by rw [map_pow, hu2]⟩
  rw [← sub_eq_zero]
  refine hinter _ (Ideal.sub_mem _ (mem_span_of_pow_eq ht he' hy) ?_) ?_
  · rw [Ideal.mem_span_singleton]
    exact dvd_mul_of_dvd_left (dvd_pow_self s hd.ne') a
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_pow, hu1, sub_self]

include hinter hs ht in
/-- **The Kummer normal form at a node** (the `s`-branch): if `y^e = s^{e'} E` with `E`
idempotent and `e, e' > 0`, then `E = 0` or `e ∣ e'`; `E = 0` forces `y = 0`; and if `e ∣ e'`,
then `y = s^{e'/e} a` with `a^e ≡ E` modulo `t`. -/
theorem exists_nodeNormalForm {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {E y : B}
    (hE : IsIdempotentElem E) (hy : y ^ e = s ^ e' * E) :
    (E = 0 ∨ e ∣ e') ∧ (E = 0 → y = 0) ∧
      (e ∣ e' → ∃ a : B, y = s ^ (e' / e) * a ∧
        Ideal.Quotient.mk (Ideal.span {t}) (a ^ e) = Ideal.Quotient.mk (Ideal.span {t}) E) :=
  ⟨eq_zero_or_dvd hinter hs ht he hE hy, eq_zero_of_idem_eq_zero hinter hs ht he' hy,
    exists_nodeNormalForm_of_dvd hinter hs ht he he' hE hy⟩

include hinter hs ht in
/-- **The Kummer normal form at a node** (the `t`-branch): the symmetric statement. -/
theorem exists_nodeNormalForm' {e e' : ℕ} (he : 0 < e) (he' : 0 < e') {E y : B}
    (hE : IsIdempotentElem E) (hy : y ^ e = t ^ e' * E) :
    (E = 0 ∨ e ∣ e') ∧ (E = 0 → y = 0) ∧
      (e ∣ e' → ∃ a : B, y = t ^ (e' / e) * a ∧
        Ideal.Quotient.mk (Ideal.span {s}) (a ^ e) = Ideal.Quotient.mk (Ideal.span {s}) E) :=
  exists_nodeNormalForm (fun x h1 h2 ↦ hinter x h2 h1) ht hs he he' hE hy

include hs in
/-- **Uniqueness of the twist on the `s`-branch**: `s^d a = s^d a'` implies `a ≡ a'` mod `t`. -/
theorem mk_eq_of_pow_mul_eq {d : ℕ} {a a' : B} (h : s ^ d * a = s ^ d * a') :
    Ideal.Quotient.mk (Ideal.span {t}) a = Ideal.Quotient.mk (Ideal.span {t}) a' :=
  pow_regular hs.1 d (by rw [← map_pow, ← map_mul, ← map_mul, h])

end Node

end NodeNormalForm

end SemistableReduction
