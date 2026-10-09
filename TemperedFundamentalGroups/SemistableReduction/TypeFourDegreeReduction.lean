/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourDescent

/-!
# Degree reduction at a type-4 point: the purely inseparable case

Blueprint §9.12, leaf T4, `TypeFour.DegreeReductionFor`. Let `η` be a type-4 valuation of `C(z)`
with radius `r = inf_b η(z - b) > 0` (not attained), `Q ∈ C[z]` with `η(Q) = 1` not approximable
by `p`-th powers to the Kummer bound `A`, and `μ = inf_H η(Q - H^p) ≥ A`. We follow Temkin
(*Stable modification of relative curves*, Prop. 6.3.3, Lemma 6.3.6, case `a = 0`) in the
language of deep centres: near `η` every polynomial is a unit (`exists_deep`), and the linear
`η`-Taylor term of a polynomial is bounded by its value, `η(P') r ≤ η(P)`
(`pv_derivative_mul_rad_le`).

* `Adm η p Q b`: `b ≡ Q - H^p` modulo elements of value `< μ` (the critical coset); moves
  `adm_add` (small elements) and `adm_sub_pow` (small `p`-th powers); a constant is never in the
  coset (`not_adm_C`, since `μ` is not attained);
* **`derivative_bound`** (the `a = 0` case of `dirtylem`): if `μ > A`, `η(b') r ≤ μ` for coset
  elements of value close to `μ`; with `lc_mul_rad_pow_lt` the top coefficient of a coset element
  of degree `m ≥ 2`, `p ∤ m`, satisfies `|b_m| r^m < μ`;
* `step`, `exists_adm_natDegree_le_one`: the degree reduction down to degree `≤ 1`;
* **`final`**: from `b = β₁ z + β₀` in the coset (necessarily `|β₁| r ≥ μ`), the linear-dominant
  disc of `DegreeReductionFor` (after removing `b(a)` by a constant `p`-th power and rescaling);
* **`degreeReduction_of_kb_lt`**: the conclusion of `DegreeReductionFor` when `μ > A`;
* `DegreeReductionASFor`, **`degreeReductionFor_of_AS`**: `DegreeReductionFor` reduces to the
  Artin–Schreier case `μ = A` (Temkin's case `a ≠ 0`).
-/

set_option linter.unusedSectionVars false

open Polynomial Filter Topology
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

namespace DegRed

open GaussLimit

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

section Binom

variable {R : Type*} [CommRing R] [Algebra C R]

omit [IsUltrametricDist C] in
lemma nnnorm_choose_le [IsUltrametricDist C] {p k : ℕ} (hp : p.Prime) (hk0 : k ≠ 0) (hkp : k < p) :
    ‖((p.choose k : ℕ) : C)‖₊ ≤ ‖(p : C)‖₊ := by
  obtain ⟨m, hm⟩ := hp.dvd_choose_self hk0 hkp
  rw [hm, Nat.cast_mul, nnnorm_mul]
  exact mul_le_of_le_one_right zero_le (IsUltrametricDist.nnnorm_natCast_le_one C m)

/-- The binomial middle terms are divisible by `p`. -/
lemma val_add_pow_sub_le (w : Valuation R ℝ≥0) (hw : ∀ c : C, w (algebraMap C R c) = ‖c‖₊)
    {p : ℕ} (hp : p.Prime) {H c : R} (hH : w H ≤ 1) (hc : w c ≤ 1) :
    w ((H + c) ^ p - H ^ p - c ^ p) ≤ ‖(p : C)‖₊ * w c := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.choose_self, Nat.cast_one, mul_one, Nat.sub_self, pow_zero, Nat.choose_zero_right,
    one_mul, Nat.sub_zero]
  rw [show ∀ x y z : R, x + z + y - y - z = x by intros; ring]
  refine Valuation.map_sum_le _ fun k hk ↦ ?_
  have hk : k < n + 1 := Finset.mem_range.1 hk
  rw [show ((n + 2).choose (k + 1) : R) = algebraMap C R ((n + 2).choose (k + 1) : C) by simp,
    map_mul, map_mul, hw, map_pow, map_pow]
  have hck : w c ^ (n + 2 - (k + 1)) ≤ w c := by
    obtain ⟨j, hj⟩ : ∃ j, n + 2 - (k + 1) = j + 1 := ⟨n - k, by omega⟩
    rw [hj, pow_succ]
    exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le hc)
  calc w H ^ (k + 1) * w c ^ (n + 2 - (k + 1)) * ‖(((n + 2).choose (k + 1) : ℕ) : C)‖₊
      ≤ 1 * w c * ‖((n + 2 : ℕ) : C)‖₊ := by
        gcongr
        · exact pow_le_one₀ zero_le hH
        · exact nnnorm_choose_le hp (by omega) (by omega)
    _ = ‖((n + 2 : ℕ) : C)‖₊ * w c := by ring

end Binom


section Unit

/-- `F` is a unit around `a` for `w`: `w(F - F(a)) < |F(a)|`. -/
def IsU (w : Valuation C[X] ℝ≥0) (a : C) (F : C[X]) : Prop :=
  w (F - Polynomial.C (F.eval a)) < ‖F.eval a‖₊

variable {w : Valuation C[X] ℝ≥0} (hw : ∀ c : C, w (Polynomial.C c) = ‖c‖₊) {a : C}

include hw in
lemma val_eq_of_isU {F : C[X]} (hF : IsU w a F) : w F = ‖F.eval a‖₊ := by
  have : F = Polynomial.C (F.eval a) + (F - Polynomial.C (F.eval a)) := by ring
  rw [this, Valuation.map_add_eq_of_lt_left _ (by rwa [hw]), hw]
  simp

include hw in
lemma isU_mul {F G : C[X]} (hF : IsU w a F) (hG : IsU w a G) : IsU w a (F * G) := by
  unfold IsU at *
  have hF0 : 0 < ‖F.eval a‖₊ := lt_of_le_of_lt zero_le hF
  have hG0 : 0 < ‖G.eval a‖₊ := lt_of_le_of_lt zero_le hG
  rw [eval_mul, nnnorm_mul]
  have : F * G - Polynomial.C (F.eval a * G.eval a) =
      (F - Polynomial.C (F.eval a)) * G +
        Polynomial.C (F.eval a) * (G - Polynomial.C (G.eval a)) := by
    rw [map_mul]; ring
  rw [this]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
  · rw [map_mul, val_eq_of_isU hw hG]
    exact mul_lt_mul_of_pos_right hF hG0
  · rw [map_mul, hw]
    exact mul_lt_mul_of_pos_left hG hF0

include hw in
lemma isU_C {c : C} (hc : c ≠ 0) : IsU w a (Polynomial.C c) := by
  simp [IsU, hc]

include hw in
lemma isU_X_sub_C {α : C} (h : w (X - Polynomial.C a) < ‖a - α‖₊) :
    IsU w a (X - Polynomial.C α) := by
  unfold IsU
  simp only [eval_sub, eval_X, eval_C]
  rwa [show X - Polynomial.C α - Polynomial.C (a - α) = X - Polynomial.C a by
    rw [map_sub]; ring]

include hw in
lemma isU_prod {s : Multiset C[X]} (h : ∀ F ∈ s, IsU w a F) : IsU w a s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using isU_C hw (a := a) one_ne_zero
  | cons F s ih =>
    rw [Multiset.prod_cons]
    exact isU_mul hw (h F (Multiset.mem_cons_self F s))
      (ih fun G hG ↦ h G (Multiset.mem_cons_of_mem hG))

end Unit

section TypeFourVal

variable [IsAlgClosed C] {η : Valuation (RatFunc C) ℝ≥0}

/-- The valuation restricted to polynomials. -/
noncomputable def pv (η : Valuation (RatFunc C) ℝ≥0) : Valuation C[X] ℝ≥0 :=
  η.comap (algebraMap C[X] (RatFunc C))

lemma pv_apply (P : C[X]) : pv η P = η (algebraMap C[X] (RatFunc C) P) := rfl

lemma pv_C (hη : Splitting.IsTypeFour η) (c : C) : pv η (Polynomial.C c) = ‖c‖₊ := by
  rw [pv_apply, ratFunc_algebraMap_C, hη.map_C]; rfl

lemma radius_eq_pv (a : C) : radius η a = pv η (X - Polynomial.C a) := rfl

/-- The infimum of the radii. -/
noncomputable def rad (η : Valuation (RatFunc C) ℝ≥0) : ℝ≥0 := ⨅ a : C, radius η a

lemma rad_le (a : C) : rad η ≤ radius η a := ciInf_le (OrderBot.bddBelow _) a

lemma rad_lt (hη : Splitting.IsTypeFour η) (a : C) : rad η < radius η a := by
  obtain ⟨b, hb⟩ := hη.no_min a
  exact (rad_le b).trans_lt hb

lemma exists_radius_lt {t : ℝ≥0} (ht : rad η < t) : ∃ a : C, radius η a < t :=
  exists_lt_of_ciInf_lt ht

lemma nnnorm_sub_eq_radius (hη : Splitting.IsTypeFour η) {a b : C} (h : radius η a < radius η b) :
    ‖a - b‖₊ = radius η b :=
  (Splitting.radius_eq_nnnorm hη h).symm

lemma exists_nnnorm_between (hη : Splitting.IsTypeFour η) {t : ℝ≥0} (ht : rad η < t) :
    ∃ c : C, rad η < ‖c‖₊ ∧ ‖c‖₊ < t := by
  obtain ⟨a, ha⟩ := exists_radius_lt ht
  obtain ⟨b, hb⟩ := hη.no_min a
  refine ⟨b - a, ?_, ?_⟩ <;> rw [nnnorm_sub_eq_radius hη hb]
  · exact rad_lt hη a
  · exact ha

lemma pv_eq_prod (hη : Splitting.IsTypeFour η) (P : C[X]) :
    pv η P = ‖P.leadingCoeff‖₊ * (P.roots.map fun α ↦ radius η α).prod := by
  conv_lhs => rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
    (IsAlgClosed.card_roots_eq_natDegree (p := P))]
  rw [map_mul, pv_C hη, map_multiset_prod, Multiset.map_map]
  rfl

lemma lc_mul_rad_pow_le (hη : Splitting.IsTypeFour η) (P : C[X]) :
    ‖P.leadingCoeff‖₊ * rad η ^ P.natDegree ≤ pv η P := by
  rw [pv_eq_prod hη, ← IsAlgClosed.card_roots_eq_natDegree (p := P), ← Multiset.prod_replicate,
    ← Multiset.map_const']
  gcongr
  exact Multiset.prod_map_le_prod_map₀ _ _ (fun _ _ ↦ zero_le) fun α _ ↦ rad_le α

lemma lc_mul_rad_pow_lt (hη : Splitting.IsTypeFour η) (hrad : 0 < rad η) {P : C[X]}
    (hP : 1 ≤ P.natDegree) : ‖P.leadingCoeff‖₊ * rad η ^ P.natDegree < pv η P := by
  have hP0 : P ≠ 0 := by rintro rfl; simp at hP
  rw [pv_eq_prod hη, ← IsAlgClosed.card_roots_eq_natDegree (p := P), ← Multiset.prod_replicate,
    ← Multiset.map_const']
  refine mul_lt_mul_of_pos_left ?_ (nnnorm_pos.2 (leadingCoeff_ne_zero.2 hP0))
  refine Multiset.prod_map_lt_prod_map ?_ _ _ (fun _ _ ↦ hrad) fun α _ ↦ rad_lt hη α
  intro h
  rw [← Multiset.card_eq_zero, IsAlgClosed.card_roots_eq_natDegree] at h
  omega

/-- **Deep centres**: near the type-4 point every nonzero polynomial is a unit (its constant
Taylor coefficient strictly dominates). -/
theorem exists_deep (hη : Splitting.IsTypeFour η) {P : C[X]} (hP : P ≠ 0) :
    ∃ d : ℝ≥0, rad η < d ∧ ∀ a : C, radius η a < d →
      ∀ w : Valuation C[X] ℝ≥0, (∀ c : C, w (Polynomial.C c) = ‖c‖₊) →
        w (X - Polynomial.C a) < d → IsU w a P := by
  classical
  set S : Finset ℝ≥0 := insert (rad η + 1) (P.roots.toFinset.image (radius η))
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  refine ⟨S.min' hS, ?_, fun a ha w hw hwa ↦ ?_⟩
  · rw [Finset.lt_min'_iff]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact lt_add_one _
    · obtain ⟨α, -, rfl⟩ := Finset.mem_image.1 hx
      exact rad_lt hη α
  · have hroot : ∀ α ∈ P.roots, S.min' hS ≤ radius η α := fun α hα ↦
      Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
        (Multiset.mem_toFinset.2 hα)))
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C
      (IsAlgClosed.card_roots_eq_natDegree (p := P))]
    refine isU_mul hw (isU_C hw (leadingCoeff_ne_zero.2 hP)) (isU_prod hw fun F hF ↦ ?_)
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hF
    refine isU_X_sub_C hw ?_
    rw [nnnorm_sub_eq_radius hη (ha.trans_le (hroot α hα))]
    exact hwa.trans_le (hroot α hα)

lemma eval_nnnorm_eq (hη : Splitting.IsTypeFour η) {P : C[X]} {a : C} (hP : IsU (pv η) a P) :
    ‖P.eval a‖₊ = pv η P :=
  (val_eq_of_isU (pv_C hη) hP).symm

/-- The Gauss valuation of the disc of radius `ρ` around `a`. -/
noncomputable abbrev gw (a : C) (ρ : ℝ≥0ˣ) : Valuation C[X] ℝ≥0 :=
  gauss (NormedField.valuation (K := C)) a ρ

lemma gw_C (a : C) (ρ : ℝ≥0ˣ) (c : C) : gw a ρ (Polynomial.C c) = ‖c‖₊ := by
  rw [gauss_C]; rfl

lemma gw_X_sub_C (a : C) (ρ : ℝ≥0ˣ) : gw a ρ (X - Polynomial.C a) = ρ := by
  rw [gauss_apply, map_sub, taylor_X, taylor_C, add_sub_cancel_right]
  exact Gauss.sup_X

lemma nnnorm_taylor_coeff_le (a : C) (ρ : ℝ≥0ˣ) (P : C[X]) (i : ℕ) :
    ‖(taylor a P).coeff i‖₊ * (ρ : ℝ≥0) ^ i ≤ gw a ρ P :=
  Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := ρ) _ i

lemma comp_affine_coeff (P : C[X]) (a c : C) (i : ℕ) :
    (P.comp (Polynomial.C c * X + Polynomial.C a)).coeff i = c ^ i * (taylor a P).coeff i := by
  rw [taylor_apply, mul_comm (c ^ i), ← comp_C_mul_X_coeff, comp_assoc]
  congr 2
  simp [add_comp]

/-- `η(P') r ≤ η(P)`. -/
theorem pv_derivative_mul_rad_le (hη : Splitting.IsTypeFour η) (P : C[X]) :
    pv η (derivative P) * rad η ≤ pv η P := by
  rcases eq_or_ne (derivative P) 0 with h | h
  · simp [h]
  rcases eq_zero_or_pos (rad η) with hr | hr
  · simp [hr]
  have hP : P ≠ 0 := by rintro rfl; simp at h
  obtain ⟨d₁, hd₁, h₁⟩ := exists_deep hη hP
  obtain ⟨d₂, hd₂, h₂⟩ := exists_deep hη h
  obtain ⟨a, ha⟩ := exists_radius_lt (lt_min hd₁ hd₂)
  have ha₁ := ha.trans_le (min_le_left _ _)
  have ha₂ := ha.trans_le (min_le_right _ _)
  have hP' := eval_nnnorm_eq hη (h₂ a ha₂ (pv η) (pv_C hη) ha₂)
  have hPP := eval_nnnorm_eq hη (h₁ a ha₁ (pv η) (pv_C hη) ha₁)
  set ρ : ℝ≥0ˣ := Units.mk0 (rad η) hr.ne'
  have hU := h₁ a ha₁ (gw a ρ) (gw_C a ρ) (by rw [gw_X_sub_C]; exact hd₁)
  have hterm := nnnorm_taylor_coeff_le a ρ (P - Polynomial.C (P.eval a)) 1
  rw [map_sub, taylor_C, coeff_sub, coeff_C, if_neg one_ne_zero, sub_zero, taylor_coeff_one,
    pow_one] at hterm
  rw [← hP', ← hPP]
  exact hterm.trans hU.le

lemma radius_eq_val (a : C) : η (RatFunc.X - algebraMap C (RatFunc C) a) = radius η a := by
  rw [radius, map_sub (algebraMap C[X] (RatFunc C)), RatFunc.algebraMap_X, ratFunc_algebraMap_C]

lemma exists_deep_le (hη : Splitting.IsTypeFour η) (P : C[X]) :
    ∃ d : ℝ≥0, rad η < d ∧ ∀ a : C, radius η a < d → ∀ ρ : ℝ≥0ˣ, (ρ : ℝ≥0) < d →
      gw a ρ P ≤ pv η P := by
  rcases eq_or_ne P 0 with rfl | hP
  · exact ⟨rad η + 1, lt_add_one _, fun _ _ _ _ ↦ by simp⟩
  obtain ⟨d, hd, hdeep⟩ := exists_deep hη hP
  refine ⟨d, hd, fun a ha ρ hρ ↦ ?_⟩
  rw [val_eq_of_isU (gw_C a ρ) (hdeep a ha _ (gw_C a ρ) (by rw [gw_X_sub_C]; exact hρ)),
    eval_nnnorm_eq hη (hdeep a ha _ (pv_C hη) ha)]

lemma nnnorm_eval_le_gw (a : C) (ρ : ℝ≥0ˣ) (P : C[X]) : ‖P.eval a‖₊ ≤ gw a ρ P := by
  simpa [taylor_coeff_zero] using nnnorm_taylor_coeff_le a ρ P 0

lemma nnnorm_comp_coeff_le (P : C[X]) (a : C) {c : C} (hc : c ≠ 0) (i : ℕ) :
    ‖(P.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖₊ ≤
      gw a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc)) P := by
  rw [comp_affine_coeff, nnnorm_mul, nnnorm_pow, mul_comm]
  have := nnnorm_taylor_coeff_le a (Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc)) P i
  rwa [Units.val_mk0] at this

lemma comp_coeff_sub_C (P : C[X]) (a c k : C) {i : ℕ} (hi : 1 ≤ i) :
    (P.comp (Polynomial.C c * X + Polynomial.C a)).coeff i =
      ((P - Polynomial.C k).comp (Polynomial.C c * X + Polynomial.C a)).coeff i := by
  rw [sub_comp, C_comp, coeff_sub, coeff_C, if_neg (by omega), sub_zero]

end TypeFourVal

section Reduction

variable [IsAlgClosed C] {η : Valuation (RatFunc C) ℝ≥0} {p : ℕ}

variable (η p) in
/-- The best approximation level `μ = inf_H η(Q - H^p)` over polynomials `H`. -/
noncomputable def mu (Q : C[X]) : ℝ≥0 := ⨅ H : C[X], pv η (Q - H ^ p)

lemma mu_le {Q : C[X]} (H : C[X]) : mu η p Q ≤ pv η (Q - H ^ p) :=
  ciInf_le (OrderBot.bddBelow _) H

lemma exists_lt_of_mu_lt {Q : C[X]} {t : ℝ≥0} (h : mu η p Q < t) :
    ∃ H : C[X], pv η (Q - H ^ p) < t :=
  exists_lt_of_ciInf_lt h

variable (η p) in
/-- `b` lies in the critical coset: `Q - H^p ≡ b` modulo elements of value `< μ`. -/
def Adm (Q b : C[X]) : Prop := ∃ H : C[X], pv η (Q - H ^ p - b) < mu η p Q

variable (C p) in
/-- The Kummer bound `A = ‖p‖^(p/(p-1))` in `ℝ≥0`. -/
noncomputable def kb : ℝ≥0 := ‖(p : C)‖₊ ^ ((p : ℝ) / (p - 1))

lemma coe_kb : (kb C p : ℝ) = kummerBound C p := by
  rw [kb, NNReal.coe_rpow, coe_nnnorm]; rfl

lemma kb_pow_pred (hp : p.Prime) : kb C p ^ (p - 1) = ‖(p : C)‖₊ ^ p := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hpm : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le, Nat.cast_one]
  rw [kb, ← NNReal.rpow_natCast, ← NNReal.rpow_mul, hpm, div_mul_cancel₀ _ (by linarith),
    NNReal.rpow_natCast]

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma kb_lt_one (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) : kb C p < 1 := by
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  exact NNReal.rpow_lt_one (by rwa [← NNReal.coe_lt_coe, coe_nnnorm])
    (div_pos (by linarith) (by linarith))

omit [IsAlgClosed C] in
lemma nnnorm_natCast_eq_one (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {m : ℕ} (hm : ¬ p ∣ m) :
    ‖(m : C)‖₊ = 1 := by
  have hcop : Nat.Coprime p m := (Nat.coprime_or_dvd_of_prime hp m).resolve_right hm
  have h1 : ((Nat.gcd p m : ℤ) : C) = 1 := by rw [hcop]; simp
  rw [Nat.gcd_eq_gcd_ab, Int.cast_add, Int.cast_mul, Int.cast_mul] at h1
  refine le_antisymm (IsUltrametricDist.nnnorm_natCast_le_one C m) ?_
  by_contra hlt
  push Not at hlt
  have : ‖(1 : C)‖₊ < 1 := by
    rw [← h1]
    refine lt_of_le_of_lt (IsUltrametricDist.nnnorm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [nnnorm_mul]
      refine lt_of_lt_of_le (mul_lt_one_of_nonneg_of_lt_one_left zero_le ?_
        (IsUltrametricDist.nnnorm_intCast_le_one C _)) le_rfl
      simpa [← NNReal.coe_lt_coe] using hp1
    · rw [nnnorm_mul]
      exact mul_lt_one_of_nonneg_of_lt_one_left zero_le (by simpa using hlt)
        (IsUltrametricDist.nnnorm_intCast_le_one C _)
  simp at this

variable (hη : Splitting.IsTypeFour η) (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {Q : C[X]}
  (hQ : pv η Q = 1)

include hη hQ in
lemma pv_eq_one_of_lt {H : C[X]} (hp0 : p ≠ 0) (h : pv η (Q - H ^ p) < 1) : pv η H = 1 := by
  have h1 : pv η (H ^ p) = pv η Q :=
    Valuation.map_eq_of_sub_lt _ (by rw [Valuation.map_sub_swap, hQ]; exact h)
  rw [map_pow, hQ] at h1
  exact (pow_eq_one_iff_of_nonneg zero_le hp0).1 h1

include hη in
lemma pv_algebraMap (c : C) : pv η (algebraMap C C[X] c) = ‖c‖₊ := by
  rw [algebraMap_eq]; exact pv_C hη c

include hη hp hp1 hQ in
/-- `A ≤ μ` from the non-approximability hypothesis. -/
lemma kb_le_mu (hNS : ∀ H : RatFunc C, H ≠ 0 →
      kummerBound C p * (η H : ℝ) ^ p < η (algebraMap C[X] (RatFunc C) Q - H ^ p)) :
    kb C p ≤ mu η p Q := by
  have hA1 : kb C p < 1 := kb_lt_one hp hp1
  refine le_ciInf fun H ↦ ?_
  rcases eq_or_ne H 0 with rfl | hH0
  · rw [zero_pow hp.ne_zero, sub_zero, hQ]; exact hA1.le
  have hH' : algebraMap C[X] (RatFunc C) H ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  have := hNS _ hH'
  rw [← map_pow, ← map_sub, ← coe_kb] at this
  change (kb C p : ℝ) * (pv η H : ℝ) ^ p < pv η (Q - H ^ p) at this
  rcases le_or_gt 1 (pv η H) with h1 | h1
  · have h2 : (1 : ℝ) ≤ (pv η H : ℝ) ^ p := one_le_pow₀ (by exact_mod_cast h1)
    have h3 : (kb C p : ℝ) ≤ (kb C p : ℝ) * (pv η H : ℝ) ^ p :=
      le_mul_of_one_le_right (NNReal.coe_nonneg _) h2
    exact_mod_cast (h3.trans this.le)
  · have h2 : pv η (H ^ p) < pv η Q := by
      rw [map_pow, hQ]; exact pow_lt_one₀ zero_le h1 hp.ne_zero
    rw [Valuation.map_sub_eq_of_lt_left _ h2, hQ]; exact hA1.le

include hη hQ in
lemma mu_lt_one (hp0 : 0 < p) : mu η p Q < 1 := by
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨d, hd, hdeep⟩ := exists_deep hη hQ0
  obtain ⟨a, ha⟩ := exists_radius_lt hd
  have hU := hdeep a ha (pv η) (pv_C hη) ha
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (Q.eval a) hp0
  refine lt_of_le_of_lt (mu_le (Polynomial.C δ)) ?_
  rw [← map_pow, hδ, ← hQ, ← eval_nnnorm_eq hη hU]
  exact hU

include hη hQ in
lemma adm_lower {b : C[X]} (hb : Adm η p Q b) : mu η p Q ≤ pv η b := by
  obtain ⟨H, hH⟩ := hb
  by_contra hlt
  push Not at hlt
  have := mu_le (η := η) (p := p) (Q := Q) H
  rw [show Q - H ^ p = (Q - H ^ p - b) + b by ring] at this
  exact absurd (this.trans (Valuation.map_add _ _ _)) (not_le.2 (max_lt hH hlt))

lemma adm_add {b d : C[X]} (hb : Adm η p Q b) (hd : pv η d < mu η p Q) :
    Adm η p Q (b + d) := by
  obtain ⟨H, hH⟩ := hb
  refine ⟨H, ?_⟩
  rw [show Q - H ^ p - (b + d) = (Q - H ^ p - b) - d by ring]
  exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hH hd)

lemma adm_sub {b d : C[X]} (hb : Adm η p Q b) (hd : pv η d < mu η p Q) :
    Adm η p Q (b - d) := by
  rw [sub_eq_add_neg]; exact adm_add hb (by rwa [Valuation.map_neg])

variable {E : ℝ≥0} (hμE : mu η p Q < E) (hE1 : E < 1)
  (hpE : ‖(p : C)‖₊ ^ p * E < mu η p Q ^ p)

include hpE hp in
lemma nnnorm_p_mul_lt {x : ℝ≥0} (hx : x ^ p ≤ E) : ‖(p : C)‖₊ * x < mu η p Q := by
  refine lt_of_pow_lt_pow_left₀ p zero_le ?_
  rw [mul_pow]
  exact lt_of_le_of_lt (by gcongr) hpE

include hη hQ hp hμE hE1 hpE in
/-- Subtracting a small `p`-th power stays in the coset. -/
lemma adm_sub_pow {b c : C[X]} (hb : Adm η p Q b) (hbE : pv η b ≤ E) (hc : pv η c ^ p ≤ E) :
    Adm η p Q (b - c ^ p) := by
  obtain ⟨H, hH⟩ := hb
  have hH1 : pv η H = 1 := by
    refine pv_eq_one_of_lt hη hQ hp.ne_zero ?_
    rw [show Q - H ^ p = (Q - H ^ p - b) + b by ring]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hH.trans (hμE.trans hE1))
      (hbE.trans_lt hE1))
  have hc1 : pv η c ≤ 1 := by
    by_contra h
    push Not at h
    exact absurd (hc.trans hE1.le) (not_le.2 (one_lt_pow₀ h hp.ne_zero))
  refine ⟨H + c, ?_⟩
  rw [show Q - (H + c) ^ p - (b - c ^ p) = (Q - H ^ p - b) - ((H + c) ^ p - H ^ p - c ^ p) by
    ring]
  refine lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hH ?_)
  exact lt_of_le_of_lt (val_add_pow_sub_le (pv η) (pv_algebraMap hη) hp hH1.le hc1)
    (nnnorm_p_mul_lt hp hpE hc)

include hη hQ hp hμE hE1 hpE in
/-- A constant is never in the coset (`μ` is not attained). -/
lemma not_adm_C {β : C} (hb : Adm η p Q (Polynomial.C β)) (hβ : ‖β‖₊ ≤ E) : False := by
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq β hp.pos
  have := adm_sub_pow hη hp hQ hμE hE1 hpE hb (by rwa [pv_C hη]) (c := Polynomial.C δ)
    (by rwa [pv_C hη, ← nnnorm_pow, hδ])
  obtain ⟨H, hH⟩ := this
  rw [← map_pow, hδ, sub_self, sub_zero] at hH
  exact absurd (mu_le H) (not_le.2 hH)

include hη hQ hp hμE hE1 hpE in
/-- **Temkin's derivative bound** (the purely inseparable case of `dirtylem`): the linear
η-Taylor term of an element of the coset is at most `μ`. -/
lemma derivative_bound (hAμ : kb C p ≤ mu η p Q) {b : C[X]} (hb : Adm η p Q b)
    (hbE : pv η b ≤ E) : pv η (derivative b) * rad η ≤ mu η p Q := by
  by_contra hlt
  push Not at hlt
  obtain ⟨H, hH⟩ := hb
  set e := Q - H ^ p - b with he
  obtain ⟨H₁, hH₁⟩ := exists_lt_of_mu_lt hlt
  have hb'b := pv_derivative_mul_rad_le hη b
  have hH1 : pv η H = 1 := by
    refine pv_eq_one_of_lt hη hQ hp.ne_zero ?_
    rw [show Q - H ^ p = e + b by rw [he]; ring]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hH.trans (hμE.trans hE1))
      (hbE.trans_lt hE1))
  have hH₁1 : pv η H₁ = 1 :=
    pv_eq_one_of_lt hη hQ hp.ne_zero ((hH₁.trans_le hb'b).trans_le hbE |>.trans hE1)
  set c := H₁ - H with hc
  have hc1 : pv η c ≤ 1 :=
    (Valuation.map_sub _ _ _).trans (max_le hH₁1.le hH1.le)
  set D := H₁ ^ p - H ^ p with hD
  have hDeq : D = b + e - (Q - H₁ ^ p) := by rw [hD, he]; ring
  have hDE : pv η D ≤ E := by
    rw [hDeq]
    refine (Valuation.map_sub _ _ _).trans (max_le ((Valuation.map_add _ _ _).trans
      (max_le hbE (hH.le.trans hμE.le))) ?_)
    exact (hH₁.le.trans hb'b).trans hbE
  -- `η(D') r ≤ |p| η(c)`
  have hkey1 : pv η (derivative D) * rad η ≤ ‖(p : C)‖₊ * pv η c := by
    have hderiv : derivative D = Polynomial.C (p : C) *
        (H₁ ^ (p - 1) * derivative c + (H₁ ^ (p - 1) - H ^ (p - 1)) * derivative H) := by
      rw [hD, derivative_sub, derivative_pow, derivative_pow, hc, derivative_sub]; ring
    have hgeom : pv η (H₁ ^ (p - 1) - H ^ (p - 1)) ≤ pv η c := by
      rw [← (Commute.all H₁ H).geom_sum₂_mul, map_mul]
      refine mul_le_of_le_one_left zero_le (Valuation.map_sum_le _ fun i _ ↦ ?_)
      rw [map_mul, map_pow, map_pow, hH₁1, hH1, one_pow, one_pow, one_mul]
    rw [hderiv, map_mul, pv_C hη, mul_assoc]
    gcongr
    refine (mul_le_mul_of_nonneg_right (Valuation.map_add _ _ _) zero_le).trans ?_
    rw [max_mul_of_nonneg _ _ zero_le]
    refine max_le ?_ ?_
    · rw [map_mul, map_pow, hH₁1, one_pow, one_mul]
      exact pv_derivative_mul_rad_le hη c
    · rw [map_mul, mul_assoc]
      refine (mul_le_mul_of_nonneg_right hgeom zero_le).trans ?_
      exact mul_le_of_le_one_right zero_le ((pv_derivative_mul_rad_le hη H).trans hH1.le)
  -- `η(b') r ≤ η(D') r`
  have hkey2 : pv η (derivative b) * rad η ≤ pv η (derivative D) * rad η := by
    have hbeq : derivative b = derivative (Q - H₁ ^ p) + derivative D - derivative e := by
      rw [← derivative_add, ← derivative_sub]; congr 1; rw [hDeq]; ring
    have h1 : pv η (derivative (Q - H₁ ^ p)) * rad η < pv η (derivative b) * rad η :=
      lt_of_le_of_lt (pv_derivative_mul_rad_le hη _) hH₁
    have h3 : pv η (derivative e) * rad η < pv η (derivative b) * rad η :=
      lt_of_le_of_lt (pv_derivative_mul_rad_le hη _) (hH.trans hlt)
    by_contra h2
    push Not at h2
    have hle : pv η (derivative b) ≤ max (max (pv η (derivative (Q - H₁ ^ p)))
        (pv η (derivative D))) (pv η (derivative e)) := by
      rw [hbeq]
      exact (Valuation.map_sub _ _ _).trans (max_le_max (Valuation.map_add _ _ _) le_rfl)
    have := mul_le_mul_of_nonneg_right hle (zero_le (a := rad η))
    rw [max_mul_of_nonneg _ _ zero_le, max_mul_of_nonneg _ _ zero_le] at this
    exact absurd this (not_le.2 (max_lt (max_lt h1 h2) h3))
  -- `|p| η(c) ≤ μ`
  have hkey3 : ‖(p : C)‖₊ * pv η c ≤ mu η p Q := by
    rcases le_or_gt (pv η c ^ p) E with hcE | hcE
    · exact (nnnorm_p_mul_lt hp hpE hcE).le
    · have hbin := val_add_pow_sub_le (pv η) (pv_algebraMap hη) hp hH1.le hc1
      rw [show H + c = H₁ by rw [hc]; ring, ← hD, Valuation.map_sub_eq_of_lt_right _
        (by rw [map_pow]; exact hDE.trans_lt hcE), map_pow] at hbin
      have hc0 : 0 < pv η c := by
        by_contra h0
        push Not at h0
        rw [le_zero_iff.1 h0, zero_pow hp.ne_zero] at hcE
        exact absurd hcE (not_lt.2 zero_le)
      have hpow : pv η c ^ (p - 1) ≤ ‖(p : C)‖₊ := by
        rw [← mul_le_mul_iff_of_pos_right hc0, ← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
        exact hbin
      refine le_trans ?_ hAμ
      refine (pow_le_pow_iff_left₀ zero_le zero_le (Nat.sub_ne_zero_of_lt hp.one_lt)).1 ?_
      rw [kb_pow_pred hp, mul_pow]
      calc ‖(p : C)‖₊ ^ (p - 1) * pv η c ^ (p - 1) ≤ ‖(p : C)‖₊ ^ (p - 1) * ‖(p : C)‖₊ := by
            gcongr
        _ = ‖(p : C)‖₊ ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
  exact absurd (hlt.trans_le (hkey2.trans (hkey1.trans hkey3))) (lt_irrefl _)

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma natDegree_sub_lc_lt {b : C[X]} (hb : 1 ≤ b.natDegree) (z : C) :
    (b - Polynomial.C b.leadingCoeff * (X - Polynomial.C z) ^ b.natDegree).natDegree <
      b.natDegree := by
  set q := Polynomial.C b.leadingCoeff * (X - Polynomial.C z) ^ b.natDegree
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hlc : b.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 hb0
  have hq : b.degree = q.degree := by
    rw [degree_C_mul hlc, degree_pow, degree_X_sub_C, nsmul_one, degree_eq_natDegree hb0]
  have hqlc : b.leadingCoeff = q.leadingCoeff := by
    rw [leadingCoeff_mul, leadingCoeff_C, leadingCoeff_pow, leadingCoeff_X_sub_C, one_pow,
      mul_one]
  rcases eq_or_ne (b - q) 0 with h | h
  · rw [h, natDegree_zero]; omega
  · exact natDegree_lt_natDegree h (degree_sub_lt hq hb0 hqlc)

variable [CharZero C]

include hη hQ hp hp1 hμE hE1 hpE in
/-- **One step of Temkin's degree reduction**: the top term of an element of the coset of degree
`m ≥ 2` can be removed, by a `p`-th power if `p ∣ m` and by an element of value `< μ` otherwise
(`dirtylem`). -/
lemma step (hAμ : kb C p ≤ mu η p Q) (hrad : 0 < rad η) {b : C[X]} (hb : Adm η p Q b)
    (hbE : pv η b ≤ E) (hm : 2 ≤ b.natDegree) :
    ∃ z : C, Adm η p Q (b - Polynomial.C b.leadingCoeff * (X - Polynomial.C z) ^ b.natDegree) ∧
      pv η (b - Polynomial.C b.leadingCoeff * (X - Polynomial.C z) ^ b.natDegree) ≤ E := by
  have hb0 : b ≠ 0 := by rintro rfl; simp at hm
  have hlower := adm_lower hη hQ hb
  by_cases hpm : p ∣ b.natDegree
  · obtain ⟨k, hk⟩ := hpm
    obtain ⟨d, hd, hdeep⟩ := exists_deep hη hb0
    obtain ⟨a, ha⟩ := exists_radius_lt hd
    have hUp := hdeep a ha (pv η) (pv_C hη) ha
    set ρ : ℝ≥0ˣ := Units.mk0 (radius η a) (radius_ne_zero η a)
    have hUg := hdeep a ha (gw a ρ) (gw_C a ρ) (by rw [gw_X_sub_C]; exact ha)
    have hterm := nnnorm_taylor_coeff_le a ρ (b - Polynomial.C (b.eval a)) b.natDegree
    rw [map_sub, taylor_C, coeff_sub, coeff_C, if_neg (by omega), sub_zero,
      coeff_taylor_natDegree] at hterm
    have hlt : ‖b.leadingCoeff‖₊ * radius η a ^ b.natDegree < pv η b := by
      rw [← eval_nnnorm_eq hη hUp]; exact hterm.trans_lt hUg
    obtain ⟨c₀, hc₀⟩ := IsAlgClosed.exists_pow_nat_eq b.leadingCoeff hp.pos
    set c := Polynomial.C c₀ * (X - Polynomial.C a) ^ k
    have hcp : c ^ p = Polynomial.C b.leadingCoeff * (X - Polynomial.C a) ^ b.natDegree := by
      rw [mul_pow, ← map_pow, hc₀, ← pow_mul, hk, mul_comm k p]
    have hcv : pv η c ^ p < pv η b := by
      rw [← map_pow, hcp, map_mul, map_pow, pv_C hη]; exact hlt
    refine ⟨a, ?_, ?_⟩
    · rw [← hcp]; exact adm_sub_pow hη hp hQ hμE hE1 hpE hb hbE (hcv.trans_le hbE).le
    · rw [← hcp, Valuation.map_sub_eq_of_lt_left _ (by rw [map_pow]; exact hcv)]; exact hbE
  · have hder := derivative_bound hη hp hQ hμE hE1 hpE hAμ hb hbE
    have hlt' := lc_mul_rad_pow_lt hη hrad (P := derivative b)
      (by rw [natDegree_derivative]; omega)
    rw [leadingCoeff_derivative, natDegree_derivative, nnnorm_mul,
      nnnorm_natCast_eq_one hp hp1 hpm, mul_one] at hlt'
    have hm' : ‖b.leadingCoeff‖₊ * rad η ^ b.natDegree < mu η p Q := by
      calc ‖b.leadingCoeff‖₊ * rad η ^ b.natDegree
          = ‖b.leadingCoeff‖₊ * rad η ^ (b.natDegree - 1) * rad η := by
            rw [mul_assoc, ← pow_succ, Nat.sub_add_cancel (by omega)]
        _ < pv η (derivative b) * rad η := mul_lt_mul_of_pos_right hlt' hrad
        _ ≤ mu η p Q := hder
    have hev : ∀ᶠ t in 𝓝[>] (rad η), ‖b.leadingCoeff‖₊ * t ^ b.natDegree < mu η p Q :=
      (ContinuousAt.eventually_lt (f := fun t : ℝ≥0 ↦ ‖b.leadingCoeff‖₊ * t ^ b.natDegree)
        (g := fun _ ↦ mu η p Q) (by fun_prop) continuousAt_const hm').filter_mono
        nhdsWithin_le_nhds
    obtain ⟨t, ht, ht'⟩ := (hev.and self_mem_nhdsWithin).exists
    obtain ⟨z, hz⟩ := exists_radius_lt (Set.mem_Ioi.1 ht')
    have hd : pv η (Polynomial.C b.leadingCoeff * (X - Polynomial.C z) ^ b.natDegree) <
        mu η p Q := by
      rw [map_mul, map_pow, pv_C hη, ← radius_eq_pv]
      exact lt_of_le_of_lt (by gcongr) ht
    refine ⟨z, adm_sub hb hd, ?_⟩
    rw [Valuation.map_sub_eq_of_lt_left _ (hd.trans_le hlower)]; exact hbE

include hη hQ hp hp1 hμE hE1 hpE in
/-- **Temkin's degree reduction** (Prop. 6.3.3, type 4, case `a = 0`): the coset contains an
element of degree `≤ 1`. -/
lemma exists_adm_natDegree_le_one (hAμ : kb C p ≤ mu η p Q) (hrad : 0 < rad η) :
    ∀ n : ℕ, ∀ b : C[X], b.natDegree = n → Adm η p Q b → pv η b ≤ E →
      ∃ b₁ : C[X], Adm η p Q b₁ ∧ pv η b₁ ≤ E ∧ b₁.natDegree ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro b hn hb hbE
    by_cases h1 : b.natDegree ≤ 1
    · exact ⟨b, hb, hbE, h1⟩
    obtain ⟨z, hz, hzE⟩ := step hη hp hp1 hQ hμE hE1 hpE hAμ hrad hb hbE (by omega)
    exact ih _ (hn ▸ natDegree_sub_lc_lt (by omega) z) _ rfl hz hzE

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma kb_pos (hp : p.Prime) : 0 < kb C p := by
  refine NNReal.rpow_pos (nnnorm_pos.2 ?_)
  exact_mod_cast hp.ne_zero

include hη hQ hp hp1 hμE hE1 hpE in
/-- **The endgame data** from a coset element of degree `≤ 1`. -/
theorem final (hAμ : kb C p ≤ mu η p Q) {b : C[X]} (hb : Adm η p Q b) (hbE : pv η b ≤ E)
    (hdeg : b.natDegree ≤ 1) (a₀ : C) (ρ₀ : ℝ≥0)
    (hρ₀ : η (RatFunc.X - algebraMap C (RatFunc C) a₀) < ρ₀) :
    ∃ (H : C[X]) (a c : C), c ≠ 0 ∧
      η (RatFunc.X - algebraMap C (RatFunc C) a) < ‖c‖₊ ∧ ‖c‖₊ ≤ ρ₀ ∧ ‖a - a₀‖₊ ≤ ρ₀ ∧
      ‖H.eval a‖ = 1 ∧
      (∀ i, 1 ≤ i → ‖(H.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ < 1) ∧
      Q.eval a = H.eval a ^ p ∧
      ∃ M : ℝ, kummerBound C p < M ∧
        ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff 1‖ = M ∧
        ∀ i, ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ ≤ M := by
  have hlower := adm_lower hη hQ hb
  -- `b` has degree one
  have hdeg1 : b.natDegree = 1 := by
    rcases Nat.lt_or_ge b.natDegree 1 with h0 | h1
    · exfalso
      have hb' : b = Polynomial.C (b.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
      rw [hb'] at hb
      exact not_adm_C hη hp hQ hμE hE1 hpE hb (by rw [← pv_C hη, ← hb']; exact hbE)
    · omega
  set β₁ := b.coeff 1 with hβ₁def
  set β₀ := b.coeff 0 with hβ₀def
  have hbeq : b = Polynomial.C β₁ * X + Polynomial.C β₀ := eq_X_add_C_of_natDegree_le_one hdeg
  have hb0 : b ≠ 0 := by rintro rfl; simp at hdeg1
  have hβ₁ : β₁ ≠ 0 := by
    have := leadingCoeff_ne_zero.2 hb0
    rwa [leadingCoeff, hdeg1] at this
  -- `μ ≤ |β₁| r`
  have hβr : mu η p Q ≤ ‖β₁‖₊ * rad η := by
    by_contra hlt
    push Not at hlt
    have hβ0 : 0 < ‖β₁‖₊ := nnnorm_pos.2 hβ₁
    have hr' : rad η < mu η p Q / ‖β₁‖₊ := by rwa [lt_div_iff₀ hβ0, mul_comm]
    obtain ⟨z, hz⟩ := exists_radius_lt hr'
    have hd : pv η (Polynomial.C β₁ * (X - Polynomial.C z)) < mu η p Q := by
      rw [map_mul, pv_C hη, ← radius_eq_pv]
      calc ‖β₁‖₊ * radius η z < ‖β₁‖₊ * (mu η p Q / ‖β₁‖₊) := mul_lt_mul_of_pos_left hz hβ0
        _ = mu η p Q := mul_div_cancel₀ _ hβ0.ne'
    have hconst : b - Polynomial.C β₁ * (X - Polynomial.C z) = Polynomial.C (β₀ + β₁ * z) := by
      rw [hbeq, map_add, map_mul]; ring
    have h2 := adm_sub hb hd
    rw [hconst] at h2
    refine not_adm_C hη hp hQ hμE hE1 hpE h2 ?_
    rw [← pv_C hη, ← hconst]
    exact (Valuation.map_sub _ _ _).trans (max_le hbE (hd.le.trans hμE.le))
  obtain ⟨H, hH⟩ := hb
  set e := Q - H ^ p - b with he
  have hH1 : pv η H = 1 := by
    refine pv_eq_one_of_lt hη hQ hp.ne_zero ?_
    rw [show Q - H ^ p = e + b by rw [he]; ring]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (hH.trans (hμE.trans hE1))
      (hbE.trans_lt hE1))
  have hH0 : H ≠ 0 := by rintro rfl; simp at hH1
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at hQ
  obtain ⟨dH, hdH, hH'⟩ := exists_deep hη hH0
  obtain ⟨dQ, hdQ, hQ'⟩ := exists_deep hη hQ0
  obtain ⟨db, hdb, hb'⟩ := exists_deep hη hb0
  obtain ⟨de, hde, he'⟩ := exists_deep_le hη e
  have hρ₀r : rad η < ρ₀ := (rad_lt hη a₀).trans (by rwa [radius_eq_val] at hρ₀)
  obtain ⟨c, hc1, hc2⟩ := exists_nnnorm_between hη
    (lt_min (lt_min hdH hdQ) (lt_min (lt_min hdb hde) hρ₀r))
  have hc0 : c ≠ 0 := nnnorm_pos.1 (lt_of_le_of_lt zero_le hc1)
  have hcH : ‖c‖₊ < dH := hc2.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hcQ : ‖c‖₊ < dQ := hc2.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hcb : ‖c‖₊ < db :=
    hc2.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hce : ‖c‖₊ < de :=
    hc2.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hcρ₀ : ‖c‖₊ < ρ₀ := hc2.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨a, ha⟩ := exists_radius_lt hc1
  set ρ : ℝ≥0ˣ := Units.mk0 ‖c‖₊ (nnnorm_ne_zero_iff.2 hc0) with hρ
  have hgX : gw a ρ (X - Polynomial.C a) = ‖c‖₊ := gw_X_sub_C a ρ
  have hUHp := hH' a (ha.trans hcH) (pv η) (pv_C hη) (ha.trans hcH)
  have hUHg := hH' a (ha.trans hcH) (gw a ρ) (gw_C a ρ) (by rw [hgX]; exact hcH)
  have hHa : ‖H.eval a‖₊ = 1 := by rw [eval_nnnorm_eq hη hUHp, hH1]
  have hQa : ‖Q.eval a‖₊ = 1 := by
    rw [eval_nnnorm_eq hη (hQ' a (ha.trans hcQ) (pv η) (pv_C hη) (ha.trans hcQ)), hQ]
  have hba : ‖b.eval a‖₊ = pv η b :=
    eval_nnnorm_eq hη (hb' a (ha.trans hcb) (pv η) (pv_C hη) (ha.trans hcb))
  have hge : gw a ρ e < mu η p Q := (he' a (ha.trans hce) ρ hce).trans_lt hH
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (b.eval a) hp.pos
  have hδE : ‖δ‖₊ ^ p ≤ E := by rw [← nnnorm_pow, hδ, hba]; exact hbE
  have hδ1 : ‖δ‖₊ < 1 := by
    by_contra h
    push Not at h
    exact absurd (hδE.trans_lt hE1) (not_lt.2 (one_le_pow₀ h))
  have hpδ : ‖(p : C)‖₊ * ‖δ‖₊ < mu η p Q := nnnorm_p_mul_lt hp hpE hδE
  set H₂ := H + Polynomial.C δ with hH₂
  have hH₂a : H₂.eval a = H.eval a + δ := by simp [H₂]
  have hH₂n : ‖H₂.eval a‖₊ = 1 := by
    rw [hH₂a, IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm (by rw [hHa]; exact hδ1.ne'),
      hHa, max_eq_left hδ1.le]
  have hH₂sub : H₂ - Polynomial.C (H₂.eval a) = H - Polynomial.C (H.eval a) := by
    rw [hH₂a, hH₂, map_add]; ring
  have hgH₂ : gw a ρ H₂ = 1 := by
    have hU : IsU (gw a ρ) a H₂ := by
      unfold IsU; rw [hH₂sub, hH₂n]; unfold IsU at hUHg; rwa [hHa] at hUHg
    rw [val_eq_of_isU (gw_C a ρ) hU, hH₂n]
  have hgH : gw a ρ H = 1 := by rw [val_eq_of_isU (gw_C a ρ) hUHg, hHa]
  have hH₂0 : H₂.eval a ≠ 0 := nnnorm_ne_zero_iff.1 (by rw [hH₂n]; exact one_ne_zero)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (Q.eval a / H₂.eval a ^ p) hp.pos
  have hun : ‖u‖₊ = 1 := by
    have := congrArg nnnorm hu
    rw [nnnorm_pow, nnnorm_div, nnnorm_pow, hQa, hH₂n, one_pow, div_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hp.ne_zero).1 this
  set Hout := Polynomial.C u * H₂ with hHout
  have hHouta : Hout.eval a = u * H₂.eval a := by simp [Hout]
  have hQHa : Q.eval a = Hout.eval a ^ p := by
    rw [hHouta, mul_pow, hu, div_mul_cancel₀ _ (pow_ne_zero _ hH₂0)]
  -- the remainder `R`
  set Xδ := H₂ ^ p - H ^ p - Polynomial.C δ ^ p with hXδ
  set R := Polynomial.C (1 - u ^ p) * H₂ ^ p + (e - Xδ) with hR
  have hδC : Polynomial.C δ ^ p = Polynomial.C β₁ * Polynomial.C a + Polynomial.C β₀ := by
    rw [← map_pow, hδ, ← map_mul, ← map_add]
    congr 1
    conv_lhs => rw [hbeq]
    simp
  have hG : Q - Hout ^ p = Polynomial.C β₁ * (X - Polynomial.C a) + R := by
    rw [hR, hXδ, hHout, mul_pow, ← map_pow, map_sub, map_one, he]
    linear_combination hbeq - hδC
  have hR0 : R.eval a = 0 := by
    have h := congrArg (eval a) hG
    rw [eval_sub, eval_pow, ← hQHa, sub_self, eval_add, eval_mul, eval_C, eval_sub, eval_X,
      eval_C, sub_self, mul_zero, zero_add] at h
    exact h.symm
  have hgC : ∀ k : C, gw a ρ (algebraMap C C[X] k) = ‖k‖₊ := fun k ↦ by
    rw [algebraMap_eq]; exact gw_C a ρ k
  have hgXδ : gw a ρ Xδ ≤ ‖(p : C)‖₊ * ‖δ‖₊ := by
    have := val_add_pow_sub_le (gw a ρ) hgC hp hgH.le (c := Polynomial.C δ)
      (by rw [gw_C]; exact hδ1.le)
    rwa [gw_C] at this
  have hgeX : gw a ρ (e - Xδ) < mu η p Q :=
    lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt hge (hgXδ.trans_lt hpδ))
  have hu1 : ‖1 - u ^ p‖₊ < mu η p Q := by
    have h := hR0
    rw [hR, eval_add, eval_mul, eval_C, eval_pow] at h
    have h' : ‖(1 - u ^ p) * H₂.eval a ^ p‖₊ = ‖(e - Xδ).eval a‖₊ := by
      rw [eq_neg_of_add_eq_zero_left h, nnnorm_neg]
    rw [nnnorm_mul, nnnorm_pow, hH₂n, one_pow, mul_one] at h'
    rw [h']
    exact (nnnorm_eval_le_gw a ρ _).trans_lt hgeX
  have hgR : gw a ρ R < mu η p Q := by
    rw [hR]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ hgeX)
    rw [map_mul, map_pow, gw_C, hgH₂, one_pow, mul_one]
    exact hu1
  have hM : mu η p Q < ‖β₁‖₊ * ‖c‖₊ :=
    hβr.trans_lt (mul_lt_mul_of_pos_left hc1 (nnnorm_pos.2 hβ₁))
  have hRi : ∀ i, ‖(R.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖₊ < mu η p Q :=
    fun i ↦ (nnnorm_comp_coeff_le R a hc0 i).trans_lt hgR
  have hcoeff : ∀ i, ((Q - Hout ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff i =
      (if i = 1 then β₁ * c else 0) + (R.comp (Polynomial.C c * X + Polynomial.C a)).coeff i := by
    intro i
    rw [hG, add_comp, coeff_add]
    congr 1
    rw [mul_comp, C_comp, sub_comp, X_comp, C_comp,
      show Polynomial.C c * X + Polynomial.C a - Polynomial.C a = Polynomial.C c * X by ring,
      ← mul_assoc, ← map_mul, coeff_C_mul_X]
  -- conclusion
  refine ⟨Hout, a, c, hc0, by rw [radius_eq_val]; exact ha, hcρ₀.le, ?_, ?_, ?_, hQHa, ?_⟩
  · have hsplit : Polynomial.C (a - a₀) = (X - Polynomial.C a₀) - (X - Polynomial.C a) := by
      rw [map_sub]; ring
    rw [← pv_C hη, hsplit]
    refine (Valuation.map_sub _ _ _).trans (max_le ?_ ?_)
    · rw [← radius_eq_pv, ← radius_eq_val]; exact hρ₀.le
    · rw [← radius_eq_pv]; exact (ha.trans hcρ₀).le
  · rw [hHouta, norm_mul, ← coe_nnnorm, ← coe_nnnorm, hun, hH₂n]; norm_num
  · intro i hi
    rw [comp_coeff_sub_C _ a c (Hout.eval a) hi]
    have h1 := nnnorm_comp_coeff_le (Hout - Polynomial.C (Hout.eval a)) a hc0 i
    have h2 : Hout - Polynomial.C (Hout.eval a) =
        Polynomial.C u * (H - Polynomial.C (H.eval a)) := by
      rw [hHouta, hHout, map_mul, ← hH₂sub]; ring
    rw [h2, map_mul, gw_C, hun, one_mul] at h1
    have h3 : gw a ρ (H - Polynomial.C (H.eval a)) < 1 := by
      have := hUHg; unfold IsU at this; rwa [hHa] at this
    have := h1.trans_lt h3
    rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one] at this
    rw [h2]; exact this
  · refine ⟨‖β₁‖ * ‖c‖, ?_, ?_, fun i ↦ ?_⟩
    · rw [← coe_kb]
      have := hAμ.trans_lt hM
      rw [← NNReal.coe_lt_coe, NNReal.coe_mul, coe_nnnorm, coe_nnnorm] at this
      exact this
    · rw [hcoeff 1, if_pos rfl]
      have hlt : ‖(R.comp (Polynomial.C c * X + Polynomial.C a)).coeff 1‖ < ‖β₁ * c‖ := by
        have := (hRi 1).trans hM
        rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm] at this
        rwa [norm_mul]
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hlt.ne', max_eq_left hlt.le,
        norm_mul]
    · have hlt : ‖(R.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ < ‖β₁‖ * ‖c‖ := by
        have := (hRi i).trans hM
        rwa [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm, coe_nnnorm] at this
      rw [hcoeff i]
      split_ifs with h
      · subst h
        rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_mul]; exact hlt.ne'),
          norm_mul, max_eq_left (by rw [← norm_mul]; exact (norm_mul β₁ c ▸ hlt).le)]
      · rw [zero_add]; exact hlt.le

end Reduction

section Main

variable [IsAlgClosed C] [CharZero C]

/-- **Degree reduction in the purely inseparable case `μ > A`** (Temkin, Prop. 6.3.3 and
Lemma 6.3.6 for `a = 0`). -/
theorem degreeReduction_of_kb_lt {η : Valuation (RatFunc C) ℝ≥0} (hη : Splitting.IsTypeFour η)
    (hr : ∃ r : ℝ≥0, 0 < r ∧ ∀ b : C, r ≤ η (RatFunc.X - algebraMap C (RatFunc C) b))
    {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {Q : C[X]}
    (hQ : η (algebraMap C[X] (RatFunc C) Q) = 1)
    (hNS : ∀ H : RatFunc C, H ≠ 0 →
      kummerBound C p * (η H : ℝ) ^ p < η (algebraMap C[X] (RatFunc C) Q - H ^ p))
    (hlt : kb C p < mu η p Q) (a₀ : C) (ρ₀ : ℝ≥0)
    (hρ₀ : η (RatFunc.X - algebraMap C (RatFunc C) a₀) < ρ₀) :
    ∃ (H : C[X]) (a c : C), c ≠ 0 ∧
      η (RatFunc.X - algebraMap C (RatFunc C) a) < ‖c‖₊ ∧ ‖c‖₊ ≤ ρ₀ ∧ ‖a - a₀‖₊ ≤ ρ₀ ∧
      ‖H.eval a‖ = 1 ∧
      (∀ i, 1 ≤ i → ‖(H.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ < 1) ∧
      Q.eval a = H.eval a ^ p ∧
      ∃ M : ℝ, kummerBound C p < M ∧
        ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff 1‖ = M ∧
        ∀ i, ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ ≤ M := by
  have hQ' : pv η Q = 1 := hQ
  have hAμ := kb_le_mu hη hp hp1 hQ' hNS
  have hmu1 := mu_lt_one hη hQ' hp.pos
  have hmu0 : 0 < mu η p Q := (kb_pos hp).trans_le hAμ
  have hrad : 0 < rad η := by
    obtain ⟨r, hr0, hrb⟩ := hr
    exact hr0.trans_le (le_ciInf fun b ↦ by rw [← radius_eq_val]; exact hrb b)
  have hpn : 0 < ‖(p : C)‖₊ := nnnorm_pos.2 (by exact_mod_cast hp.ne_zero)
  have hkey : ‖(p : C)‖₊ ^ p * mu η p Q < mu η p Q ^ p := by
    have h1 : ‖(p : C)‖₊ ^ p < mu η p Q ^ (p - 1) := by
      rw [← kb_pow_pred hp]
      exact pow_lt_pow_left₀ hlt zero_le (Nat.sub_ne_zero_of_lt hp.one_lt)
    calc ‖(p : C)‖₊ ^ p * mu η p Q < mu η p Q ^ (p - 1) * mu η p Q :=
          mul_lt_mul_of_pos_right h1 hmu0
      _ = mu η p Q ^ p := by rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le]
  have hpp : 0 < ‖(p : C)‖₊ ^ p := pow_pos hpn p
  have hB : mu η p Q < mu η p Q ^ p / ‖(p : C)‖₊ ^ p := by
    rw [lt_div_iff₀ hpp, mul_comm]; exact hkey
  obtain ⟨E, hE1, hE2⟩ := exists_between (lt_min hmu1 hB)
  have hE1' : E < 1 := hE2.trans_le (min_le_left _ _)
  have hpE : ‖(p : C)‖₊ ^ p * E < mu η p Q ^ p := by
    have := mul_lt_mul_of_pos_left (hE2.trans_le (min_le_right _ _)) hpp
    rwa [mul_div_cancel₀ _ hpp.ne'] at this
  obtain ⟨H₀, hH₀⟩ := exists_lt_of_mu_lt hE1
  have hadm : Adm η p Q (Q - H₀ ^ p) := ⟨H₀, by rw [sub_self, map_zero]; exact hmu0⟩
  obtain ⟨b, hb, hbE, hdeg⟩ := exists_adm_natDegree_le_one hη hp hp1 hQ' hE1 hE1' hpE hAμ hrad
    _ _ rfl hadm hH₀.le
  exact final hη hp hp1 hQ' hE1 hE1' hpE hAμ hb hbE hdeg a₀ ρ₀ hρ₀

end Main

section AS

variable (C) in
/-- **Degree reduction in the Artin–Schreier case** `μ = A` (Temkin, Lemma 6.3.6 for `a = 1`):
the statement of `DegreeReductionFor` under the additional hypothesis that `Q` is approximable by
`p`-th powers up to every bound `> A`. -/
def DegreeReductionASFor (p : ℕ) : Prop :=
  ∀ η : Valuation (RatFunc C) ℝ≥0, Splitting.IsTypeFour η →
    (∃ r : ℝ≥0, 0 < r ∧ ∀ b : C, r ≤ η (RatFunc.X - algebraMap C (RatFunc C) b)) →
    ∀ Q : C[X], η (algebraMap C[X] (RatFunc C) Q) = 1 →
    (∀ H : RatFunc C, H ≠ 0 →
      kummerBound C p * (η H : ℝ) ^ p < η (algebraMap C[X] (RatFunc C) Q - H ^ p)) →
    (∀ ε : ℝ, kummerBound C p < ε →
      ∃ H : C[X], (η (algebraMap C[X] (RatFunc C) (Q - H ^ p)) : ℝ) < ε) →
    ∀ (a₀ : C) (ρ₀ : ℝ≥0), η (RatFunc.X - algebraMap C (RatFunc C) a₀) < ρ₀ →
    ∃ (H : C[X]) (a c : C), c ≠ 0 ∧
      η (RatFunc.X - algebraMap C (RatFunc C) a) < ‖c‖₊ ∧ ‖c‖₊ ≤ ρ₀ ∧ ‖a - a₀‖₊ ≤ ρ₀ ∧
      ‖H.eval a‖ = 1 ∧
      (∀ i, 1 ≤ i → ‖(H.comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ < 1) ∧
      Q.eval a = H.eval a ^ p ∧
      ∃ M : ℝ, kummerBound C p < M ∧
        ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff 1‖ = M ∧
        ∀ i, ‖((Q - H ^ p).comp (Polynomial.C c * X + Polynomial.C a)).coeff i‖ ≤ M

variable [IsAlgClosed C] [CharZero C]

/-- **`DegreeReductionFor` from its Artin–Schreier case**: if `μ > A` the purely inseparable
case applies (`degreeReduction_of_kb_lt`); otherwise `μ = A`. -/
theorem degreeReductionFor_of_AS {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
    (hAS : DegreeReductionASFor C p) : DegreeReductionFor C p := by
  intro η hη hr Q hQ hNS a₀ ρ₀ hρ₀
  rcases lt_or_ge (kb C p) (mu η p Q) with hlt | hle
  · exact degreeReduction_of_kb_lt hη hr hp hp1 hQ hNS hlt a₀ ρ₀ hρ₀
  · refine hAS η hη hr Q hQ hNS (fun ε hε ↦ ?_) a₀ ρ₀ hρ₀
    have hA0 : (0 : ℝ) ≤ kummerBound C p := by rw [← coe_kb]; exact NNReal.coe_nonneg _
    have hε0 : 0 ≤ ε := hA0.trans hε.le
    obtain ⟨H, hH⟩ := exists_lt_of_mu_lt (η := η) (p := p) (Q := Q) (t := ε.toNNReal)
      (lt_of_le_of_lt hle (by rw [← NNReal.coe_lt_coe, coe_kb, Real.coe_toNNReal _ hε0]; exact hε))
    refine ⟨H, ?_⟩
    have := NNReal.coe_lt_coe.2 hH
    rwa [Real.coe_toNNReal _ hε0] at this

end AS

end DegRed

end TypeFour

end SemistableReduction
