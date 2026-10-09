/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3AS

/-!
# Kummer extensions of prime degree of type-3 fields

Blueprint §9.10a (I.3). Let `M` be complete, the closure of `C(y)` with `‖y‖ ∉ |C^×|`, and
`E = M(θ)` of prime degree `q` with `θ^q ∈ M`. Then `e(E | M) = q`, `f(E | M) = 1` and `E` is
again the closure of `C(z)` for a value-transcendental `z` (`kummer_step`).

Write `θ^q = c y^j (1 + ε)`. If `q ∤ j` this is the generator lemma (I.2). Otherwise `θ` is
a `q`-th root of a `1`-unit `u₀`; for `q ≠ p` the `1`-unit is a `q`-th power (tame roots), which
is impossible; for `q = p` Phase 1 (`phase1`) and Phase 2 (`phase2`) produce either a `p`-th root
of `u₀` (impossible) or an element `η` resp. `X` of `E` with `η^p = a y^m (1 + ε')`, `p ∤ m`
(the dichotomy "`e = p` or a `p`-th power").
-/

open Finset

namespace SemistableReduction

namespace Type3

section Units

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

/-- Products of `1`-units. -/
lemma exists_one_add_mul {ε₁ ε₂ : E} (h₁ : ‖ε₁‖ < 1) (h₂ : ‖ε₂‖ < 1) :
    ∃ ε : E, ‖ε‖ < 1 ∧ (1 + ε₁) * (1 + ε₂) = 1 + ε := by
  refine ⟨ε₁ + ε₂ + ε₁ * ε₂, ?_, by ring⟩
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt
    ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h₁ h₂)) ?_)
  rw [norm_mul]
  nlinarith [norm_nonneg ε₁, norm_nonneg ε₂]

/-- Quotients of `1`-units. -/
lemma exists_one_add_div {ε₁ ε₂ : E} (h₁ : ‖ε₁‖ < 1) (h₂ : ‖ε₂‖ < 1) :
    ∃ ε : E, ‖ε‖ < 1 ∧ (1 + ε₁) / (1 + ε₂) = 1 + ε := by
  have hn : ‖1 + ε₂‖ = 1 := norm_eq_one_of_norm_sub_one_lt (by rwa [add_sub_cancel_left])
  have h0 : 1 + ε₂ ≠ 0 := by intro h; rw [h, norm_zero] at hn; exact zero_ne_one hn
  refine ⟨(ε₁ - ε₂) / (1 + ε₂), ?_, by field_simp; ring⟩
  rw [norm_div, hn, div_one]
  exact (norm_sub_le_max' _ _).trans_lt (max_lt h₁ h₂)

end Units

section RootsOfUnity

variable {C E : Type*} [Field C] [IsAlgClosed C] [Field E] [Algebra C E]

/-- Every root of unity of `E` comes from the algebraically closed `C`. -/
lemma exists_algebraMap_eq_of_pow_eq_one {q : ℕ} (hq : 0 < q) {t : E} (ht : t ^ q = 1) :
    ∃ ζ : C, algebraMap C E ζ = t := by
  classical
  set P : Polynomial C := Polynomial.X ^ q - 1
  have hP : P ≠ 0 := Polynomial.X_pow_sub_C_ne_zero hq 1
  have e := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (Polynomial.splits_iff_card_roots.1 (IsAlgClosed.splits P))
  have h0 : Polynomial.aeval t P = 0 := by simp [P, ht]
  rw [← e, map_mul, Polynomial.aeval_C, map_multiset_prod, Multiset.map_map] at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exfalso
    rw [map_eq_zero_iff _ (algebraMap C E).injective, Polynomial.leadingCoeff_eq_zero] at h
    exact hP h
  · obtain ⟨ζ, -, hζ⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h)
    refine ⟨ζ, ?_⟩
    simp only [Function.comp_apply, map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hζ
    exact (sub_eq_zero.1 hζ).symm

end RootsOfUnity

section Norms

variable {C : Type*} [NormedField C] [IsUltrametricDist C]

/-- A prime `q ≠ p` is a unit when `‖p‖ < 1`. -/
lemma norm_natCast_eq_one_of_prime_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : q ≠ p)
    (hp1 : ‖(p : C)‖ < 1) : ‖(q : C)‖ = 1 := by
  refine le_antisymm (IsUltrametricDist.norm_natCast_le_one C q) (not_lt.1 fun hlt ↦ ?_)
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hq hp).2 hpq
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * q + b * p = 1 := by
    refine ⟨Nat.gcdA q p, Nat.gcdB q p, ?_⟩
    rw [mul_comm, mul_comm _ (p : ℤ), ← Nat.gcd_eq_gcd_ab, hcop]
    rfl
  have h1 : (1 : C) = a * q + b * p := by exact_mod_cast congrArg (Int.cast (R := C)) hab.symm
  have h2 := IsUltrametricDist.norm_add_le_max ((a : C) * q) ((b : C) * p)
  rw [← h1, norm_one, norm_mul, norm_mul] at h2
  have ha := IsUltrametricDist.norm_intCast_le_one C a
  have hb := IsUltrametricDist.norm_intCast_le_one C b
  have : max (‖(a : C)‖ * ‖(q : C)‖) (‖(b : C)‖ * ‖(p : C)‖) < 1 := max_lt
    (lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) ha) hlt)
    (lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hb) hp1)
  linarith

end Norms

section Good

variable {E : Type*} [NormedField E] [IsUltrametricDist E] {p : ℕ} (hp : p.Prime) {π : E}
  (hπ : π ^ (p - 1) = -(p : E)) (hπ1 : ‖π‖ < 1)
include hp hπ hπ1

/-- **The Kummer good case**: if `(1 + η)^p = 1 + G` with `‖G‖ > ‖π‖^p`, then
`η^p = G (1 + ε)` with `‖ε‖ < 1`. -/
theorem exists_pow_eq_of_kummer {η G : E} (hη : (1 + η) ^ p = 1 + G) (hG : ‖π‖ ^ p < ‖G‖) :
    ∃ ε : E, ‖ε‖ < 1 ∧ η ^ p = G * (1 + ε) := by
  have hpn : ‖(p : E)‖ = ‖π‖ ^ (p - 1) := by rw [← norm_pow, hπ, norm_neg]
  have hp2 := hp.two_le
  set S := (1 + η) ^ p - 1 ^ p - η ^ p with hS
  set R := max ‖η‖ (‖η‖ ^ (p - 1))
  have hR : ∀ j ∈ Ioo 0 p, ‖(1 : E)‖ ^ j * ‖η‖ ^ (p - j) ≤ R := by
    intro j hj
    have hj' := Finset.mem_Ioo.1 hj
    rw [norm_one, one_pow, one_mul]
    rcases le_or_gt ‖η‖ 1 with h1 | h1
    · exact (pow_le_of_le_one (norm_nonneg _) h1 (by omega)).trans (le_max_left _ _)
    · exact (pow_le_pow_right₀ h1.le (by omega)).trans (le_max_right _ _)
  have hSle : ‖S‖ ≤ ‖(p : E)‖ * R := norm_add_pow_sub_le' hp 1 η (by positivity) hR
  have hGS : G = η ^ p + S := by rw [hS, one_pow]; linear_combination -hη
  have hπη : ‖π‖ < ‖η‖ := by
    by_contra! hle
    have hη1 : ‖η‖ < 1 := hle.trans_lt hπ1
    have hRη : R = ‖η‖ := max_eq_left (pow_le_of_le_one (norm_nonneg _) hη1.le (by omega))
    have h1 : ‖S‖ ≤ ‖π‖ ^ p := by
      refine hSle.trans ?_
      rw [hRη, hpn]
      calc ‖π‖ ^ (p - 1) * ‖η‖ ≤ ‖π‖ ^ (p - 1) * ‖π‖ :=
            mul_le_mul_of_nonneg_left hle (by positivity)
        _ = ‖π‖ ^ p := by rw [← pow_succ]; congr 1; omega
    have h2 : ‖η ^ p‖ ≤ ‖π‖ ^ p := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hle p
    have := IsUltrametricDist.norm_add_le_max (η ^ p) S
    rw [← hGS] at this
    linarith [max_le h2 h1]
  have hη0 : 0 < ‖η‖ := (norm_nonneg π).trans_lt hπη
  have hSlt : ‖S‖ < ‖η ^ p‖ := by
    refine hSle.trans_lt ?_
    rw [hpn, norm_pow]
    rcases le_or_gt ‖η‖ 1 with h1 | h1
    · have hRη : R = ‖η‖ := max_eq_left (pow_le_of_le_one (norm_nonneg _) h1 (by omega))
      rw [hRη]
      calc ‖π‖ ^ (p - 1) * ‖η‖ < ‖η‖ ^ (p - 1) * ‖η‖ :=
            mul_lt_mul_of_pos_right (pow_lt_pow_left₀ hπη (norm_nonneg _) (by omega)) hη0
        _ = ‖η‖ ^ p := by rw [← pow_succ]; congr 1; omega
    · have hRη : R = ‖η‖ ^ (p - 1) := max_eq_right (le_self_pow₀ h1.le (by omega))
      rw [hRη]
      calc ‖π‖ ^ (p - 1) * ‖η‖ ^ (p - 1) < 1 * ‖η‖ ^ (p - 1) :=
            mul_lt_mul_of_pos_right (pow_lt_one₀ (norm_nonneg _) hπ1 (by omega))
              (pow_pos hη0 _)
        _ ≤ ‖η‖ * ‖η‖ ^ (p - 1) := mul_le_mul_of_nonneg_right h1.le (by positivity)
        _ = ‖η‖ ^ p := by rw [← pow_succ']; congr 1; omega
  have hGn : ‖G‖ = ‖η ^ p‖ := by
    rw [hGS, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hSlt.ne', max_eq_left hSlt.le]
  have hG0 : G ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hGn; exact (pow_pos hη0 p).ne' (by rw [hGn, norm_pow])
  refine ⟨-S / G, ?_, ?_⟩
  · rw [norm_div, norm_neg, hGn, div_lt_one (by rw [norm_pow]; exact pow_pos hη0 p)]
    exact hSlt
  · field_simp
    linear_combination -hGS

/-- **The Artin–Schreier good case**: if `(1 + π X)^p = 1 + π^p c` with `‖c‖ > 1`, then
`X^p = c (1 + ε)` with `‖ε‖ < 1`. -/
theorem exists_pow_eq_of_as (hπ0 : π ≠ 0) {X c : E} (hX : (1 + π * X) ^ p = 1 + π ^ p * c)
    (hc : 1 < ‖c‖) : ∃ ε : E, ‖ε‖ < 1 ∧ X ^ p = c * (1 + ε) := by
  have hp2 := hp.two_le
  have hπp0 : π ^ p ≠ 0 := pow_ne_zero _ hπ0
  have hπpn : 0 < ‖π‖ ^ p := pow_pos (norm_pos_iff.2 hπ0) p
  have hexp := one_add_pi_pow hp hπ X
  have hXc : X ^ p = c + (X - pmid p π X / π ^ p) := by
    have : π ^ p * (X ^ p - X) + pmid p π X = π ^ p * c := by
      linear_combination hX.symm.trans hexp |>.symm
    field_simp
    linear_combination this
  have hmid := norm_pmid_le hp hπ hπ1.le X
  have hmidπ : ‖pmid p π X / π ^ p‖ ≤ ‖π‖ * max 1 ‖X‖ ^ (p - 1) := by
    rw [norm_div, norm_pow, div_le_iff₀ hπpn]
    calc ‖pmid p π X‖ ≤ ‖π‖ ^ (p + 1) * max 1 ‖X‖ ^ (p - 1) := hmid
      _ = ‖π‖ * max 1 ‖X‖ ^ (p - 1) * ‖π‖ ^ p := by ring
  have hX1 : 1 < ‖X‖ := by
    by_contra! hle
    have hm : max 1 ‖X‖ = 1 := max_eq_left hle
    rw [hm, one_pow, mul_one] at hmidπ
    have h1 : ‖X ^ p - X‖ ≤ 1 := (norm_sub_le_max' _ _).trans (max_le
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hle) hle)
    have : c = (X ^ p - X) + pmid p π X / π ^ p := by linear_combination -hXc
    have h2 := IsUltrametricDist.norm_add_le_max (X ^ p - X) (pmid p π X / π ^ p)
    rw [← this] at h2
    linarith [max_le h1 (hmidπ.trans hπ1.le)]
  have hm : max 1 ‖X‖ = ‖X‖ := max_eq_right hX1.le
  rw [hm] at hmidπ
  set W := X - pmid p π X / π ^ p
  have hW : ‖W‖ < ‖X ^ p‖ := by
    rw [norm_pow]
    refine (norm_sub_le_max' _ _).trans_lt (max_lt ?_ (hmidπ.trans_lt ?_))
    · exact lt_self_pow₀ hX1 hp.one_lt
    · calc ‖π‖ * ‖X‖ ^ (p - 1) < 1 * ‖X‖ ^ (p - 1) :=
            mul_lt_mul_of_pos_right hπ1 (pow_pos (by linarith) _)
        _ ≤ ‖X‖ * ‖X‖ ^ (p - 1) := mul_le_mul_of_nonneg_right hX1.le (by positivity)
        _ = ‖X‖ ^ p := by rw [← pow_succ']; congr 1; omega
  have hcn : ‖c‖ = ‖X ^ p‖ := by
    have : c = X ^ p - W := by rw [hXc]; ring
    rw [this, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [norm_neg]; exact hW.ne'), norm_neg, max_eq_left hW.le]
  have hc0 : c ≠ 0 := by intro h0; rw [h0, norm_zero] at hc; linarith
  refine ⟨W / c, ?_, ?_⟩
  · rw [norm_div, hcn, div_lt_one (by rw [← hcn]; linarith)]
    exact hW
  · rw [hXc]
    field_simp

end Good

section NoRoot

variable (C : Type*) {M E : Type*} [Field C] [IsAlgClosed C] [Field M] [Field E] [Algebra C M]
  [Algebra C E] [Algebra M E] [IsScalarTower C M E]
include C

/-- A `q`-th root of `u` outside `M` excludes `q`-th roots of `u` in `M`. -/
lemma pow_ne_of_notMem {q : ℕ} (hq : 0 < q) {θ : E} (hθ : θ ∉ Set.range (algebraMap M E))
    {u : M} (hu : θ ^ q = algebraMap M E u) (s : M) : s ^ q ≠ u := by
  intro hs
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [zero_pow hq.ne'] at hs
    rw [← hs, map_zero, pow_eq_zero_iff hq.ne'] at hu
    exact hθ ⟨0, by rw [hu, map_zero]⟩
  have hs' : algebraMap M E s ≠ 0 := (map_ne_zero _).2 hs0
  obtain ⟨ζ, hζ⟩ := exists_algebraMap_eq_of_pow_eq_one (C := C) hq
    (t := θ / algebraMap M E s) (by rw [div_pow, hu, ← hs, map_pow, div_self (pow_ne_zero _ hs')])
  apply hθ
  refine ⟨algebraMap C M ζ * s, ?_⟩
  rw [map_mul, ← IsScalarTower.algebraMap_apply, hζ]
  field_simp

end NoRoot

section Main

variable {C M E : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [NormedField M] [IsUltrametricDist M] [NormedAlgebra C M]
  [NormedField E] [IsUltrametricDist E] [NormedAlgebra C E] [NormedAlgebra M E]
  [IsScalarTower C M E]

omit [IsAlgClosed C] [IsUltrametricDist E] [IsUltrametricDist C] [IsUltrametricDist M] in
lemma algebraMap_mono (y : M) (c : C) (n : ℤ) :
    algebraMap M E (mono y c n) = algebraMap C E c * algebraMap M E y ^ n := by
  rw [mono, map_mul, ← IsScalarTower.algebraMap_apply, map_zpow₀]

variable [CharZero C] [CompleteSpace M] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
include hp hp1

/-- **The Kummer step** (Blueprint §9.10a (I.3)). -/
theorem kummer_step {y : M} (hy : IsType3 C y) {q : ℕ} (hq : q.Prime)
    (hdeg : Module.finrank M E = q) {θ : E} (hθ : θ ∉ Set.range (algebraMap M E)) {f₀ : M}
    (hf₀ : θ ^ q = algebraMap M E f₀) :
    (∃ z : E, IsType3 C z) ∧
      FundamentalInequality.ramificationIdx M (NormedField.valuation (K := E)) = q ∧
      FundamentalInequality.inertiaDeg (NormedField.valuation (K := M))
        (NormedField.valuation (K := E)) = 1 := by
  suffices key : ∃ (η : E) (a : C) (m : ℤ) (ε : E), a ≠ 0 ∧ ¬ (q : ℤ) ∣ m ∧ ‖ε‖ < 1 ∧
      η ^ q = algebraMap C E a * algebraMap M E y ^ m * (1 + ε) by
    obtain ⟨η, a, m, ε, ha, hqm, hε, hη⟩ := key
    exact ⟨isType3_of_pow_eq hy hq hdeg ha hqm hε hη,
      ramificationIdx_eq_of_pow_eq hy hq hdeg ha hqm hε hη⟩
  classical
  have hθ0 : θ ≠ 0 := fun h0 ↦ hθ ⟨0, by rw [h0, map_zero]⟩
  have hf0 : f₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf₀
    exact hθ0 (pow_eq_zero_iff hq.ne_zero |>.1 hf₀)
  obtain ⟨c, j, hc0, hcn, hclt⟩ := exists_dom_mono hy hf0
  have hmono0 : mono y c j ≠ 0 := by
    rw [mono]
    exact mul_ne_zero ((map_ne_zero _).2 hc0) (zpow_ne_zero _ hy.valTrans.ne_zero)
  have hmn : ‖mono y c j‖ = ‖f₀‖ := by rw [norm_mono, hcn]
  set ε₀ := f₀ / mono y c j - 1 with hε₀
  have hε₀1 : ‖ε₀‖ < 1 := by
    rw [hε₀, show f₀ / mono y c j - 1 = (f₀ - mono y c j) / mono y c j by field_simp, norm_div,
      hmn, div_lt_one (norm_pos_iff.2 hf0)]
    exact hclt
  have hf₀eq : f₀ = mono y c j * (1 + ε₀) := by rw [hε₀]; field_simp; ring
  set y' := algebraMap M E y
  have hθq : θ ^ q = algebraMap C E c * y' ^ j * (1 + algebraMap M E ε₀) := by
    rw [hf₀, hf₀eq, map_mul, algebraMap_mono, map_add, map_one]
  by_cases hqj : (q : ℤ) ∣ j
  swap
  · exact ⟨θ, c, j, algebraMap M E ε₀, hc0, hqj, by rwa [norm_algebraMap'], hθq⟩
  obtain ⟨k, rfl⟩ := hqj
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq c hq.pos
  have hb0 : b ≠ 0 := by rintro rfl; rw [zero_pow hq.ne_zero] at hb; exact hc0 hb.symm
  have hy'0 : y' ≠ 0 := (map_ne_zero _).2 hy.valTrans.ne_zero
  set d : E := algebraMap C E b * y' ^ k
  have hd0 : d ≠ 0 := mul_ne_zero ((map_ne_zero _).2 hb0) (zpow_ne_zero _ hy'0)
  set θ₁ := θ / d
  set u₀ : M := 1 + ε₀
  have hθ₁ : θ₁ ^ q = algebraMap M E u₀ := by
    have hdq : d ^ q = algebraMap C E c * y' ^ ((q : ℤ) * k) := by
      simp only [d, mul_pow, ← map_pow, hb]
      rw [← zpow_natCast (y' ^ k), ← zpow_mul, mul_comm k]
    have hc' : algebraMap C E c ≠ 0 := (map_ne_zero _).2 hc0
    rw [div_pow, hθq, hdq, map_add, map_one]
    field_simp
  have hθ₁M : θ₁ ∉ Set.range (algebraMap M E) := by
    rintro ⟨t, ht⟩
    apply hθ
    refine ⟨t * (algebraMap C M b * y ^ k), ?_⟩
    have hdd : algebraMap M E (algebraMap C M b * y ^ k) = d := by
      rw [map_mul, ← IsScalarTower.algebraMap_apply, map_zpow₀]
    rw [map_mul, ht, hdd, div_mul_cancel₀ θ hd0]
  have hnoroot := pow_ne_of_notMem C hq.pos hθ₁M hθ₁
  have hu₀1 : ‖u₀ - 1‖ < 1 := by simpa [u₀] using hε₀1
  by_cases hqp : q = p
  swap
  · -- tame: `u₀` is a `q`-th power
    have hqn : ‖(q : M)‖ = 1 := by
      rw [← map_natCast (algebraMap C M), norm_algebraMap']
      exact norm_natCast_eq_one_of_prime_ne hp hq hqp hp1
    obtain ⟨X, -, hX⟩ := exists_pow_eq_one_add hqn hε₀1
    exact absurd hX (hnoroot (1 + X))
  subst hqp
  -- the wild case `q = p`
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (-(q : C)) (Nat.sub_pos_of_lt hq.one_lt)
  obtain ⟨lam, hlam⟩ := IsAlgClosed.exists_pow_nat_eq π two_pos
  have hq0 : (q : C) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.sub_pos_of_lt hq.one_lt).ne'] at hπ
    exact hq0 (neg_eq_zero.1 hπ.symm)
  have hπn : ‖π‖ ^ (q - 1) = ‖(q : C)‖ := by rw [← norm_pow, hπ, norm_neg]
  have hπ1 : ‖π‖ < 1 := by
    by_contra! h1
    have := one_le_pow₀ (n := q - 1) h1
    linarith [hπn ▸ hp1]
  obtain ⟨hl0, hl1, -, -, -, -⟩ := as_consts hq hlam hπ0 hπ1
  set A := ‖π‖ ^ q
  have hA0 : 0 < A := pow_pos (norm_pos_iff.2 hπ0) q
  have hA1 : A < 1 := pow_lt_one₀ (norm_nonneg _) hπ1 hq.ne_zero
  have hqM : ‖(q : M)‖ = ‖(q : C)‖ := by rw [← map_natCast (algebraMap C M), norm_algebraMap']
  have hp0 : 0 < ‖(q : M)‖ := by rw [hqM]; exact norm_pos_iff.2 hq0
  have hAfix : ‖(q : M)‖ * A ^ (q : ℝ)⁻¹ = A := by
    rw [Real.pow_rpow_inv_natCast (norm_nonneg _) hq.ne_zero, hqM, ← hπn, ← pow_succ,
      Nat.sub_add_cancel hq.one_le]
  have hT : 1 < ‖lam‖⁻¹ := (one_lt_inv₀ hl0).2 hl1
  obtain ⟨h, Ψ, hΨ, hh, hinv⟩ := phase1 hq hy hp0 hA0 hA1 hAfix hu₀1 hT
  have hh1 : ‖h‖ = 1 := norm_eq_one_of_norm_sub_one_lt hh
  have hhq : ‖h ^ q‖ = 1 := by rw [norm_pow, hh1, one_pow]
  have hh0 : h ^ q ≠ 0 := by intro h0; rw [h0, norm_zero] at hhq; exact zero_ne_one hhq
  set πE := algebraMap C E π
  have hπE : πE ^ (q - 1) = -(q : E) := by rw [← map_pow, hπ, map_neg, map_natCast]
  have hπEn : ‖πE‖ = ‖π‖ := norm_algebraMap' E π
  have hπE0 : πE ≠ 0 := (map_ne_zero _).2 hπ0
  by_cases hgood : A * ‖lam‖⁻¹ < ‖lev y Ψ‖
  · -- the Kummer good case
    set g := u₀ - h ^ q with hg
    have hΨ0 : Ψ ≠ 0 := by
      rintro rfl
      rw [lev_zero, norm_zero] at hgood
      linarith [mul_pos hA0 (inv_pos.2 hl0)]
    obtain ⟨m, hm0, hm, hdom⟩ := exists_dom hy.valTrans hΨ0
    have hqm : ¬ (q : ℤ) ∣ m := hΨ m (Finsupp.mem_support_iff.2 hm0)
    have hgΨ : ‖g - lev y Ψ‖ < ‖lev y Ψ‖ := hinv.trans_lt hgood
    have hgn : ‖g‖ = ‖lev y Ψ‖ := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hgΨ.ne
      rwa [sub_add_cancel, max_eq_right hgΨ.le] at this
    have hmono := norm_lev_sub_mono_lt hy.valTrans hm0 hm hdom
    have hmn : ‖mono y (Ψ m) m‖ = ‖lev y Ψ‖ := by rw [norm_mono, hm]; rfl
    have hgm : ‖g - mono y (Ψ m) m‖ < ‖mono y (Ψ m) m‖ := by
      rw [hmn]
      have := IsUltrametricDist.norm_add_le_max (g - lev y Ψ) (lev y Ψ - mono y (Ψ m) m)
      rw [show g - lev y Ψ + (lev y Ψ - mono y (Ψ m) m) = g - mono y (Ψ m) m by ring] at this
      exact this.trans_lt (max_lt hgΨ hmono)
    have hmono0 : mono y (Ψ m) m ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hgm
      exact (norm_nonneg _).not_gt hgm
    set ε₁ := g / mono y (Ψ m) m - 1 with hε₁def
    have hε₁ : ‖ε₁‖ < 1 := by
      rw [hε₁def, show g / mono y (Ψ m) m - 1 = (g - mono y (Ψ m) m) / mono y (Ψ m) m by
        field_simp, norm_div, div_lt_one (norm_pos_iff.2 hmono0)]
      exact hgm
    have hhq1 : ‖h ^ q - 1‖ < 1 := by
      have := norm_zpow_sub_one_le (le_refl _) hh (q : ℤ)
      rw [zpow_natCast] at this
      exact this.trans_lt hh
    obtain ⟨ε₂, hε₂, hε₂eq⟩ := exists_one_add_div hε₁ hhq1
    set G := g / h ^ q with hGdef
    have hGeq : G = mono y (Ψ m) m * (1 + ε₂) := by
      rw [← hε₂eq, add_sub_cancel, hGdef, add_sub_cancel]
      field_simp
    have hGn : ‖G‖ = ‖lev y Ψ‖ := by rw [hGdef, norm_div, hhq, div_one, hgn]
    have hhE : algebraMap M E h ≠ 0 := (map_ne_zero _).2 (by
      intro h0; rw [h0, norm_zero] at hh1; exact zero_ne_one hh1)
    set η := θ₁ / algebraMap M E h - 1
    have hη : (1 + η) ^ q = 1 + algebraMap M E G := by
      have h1 : (1 : M) + G = u₀ / h ^ q := by rw [hGdef, hg]; field_simp; ring
      rw [show 1 + η = θ₁ / algebraMap M E h by simp only [η]; ring, div_pow, hθ₁, ← map_pow,
        ← map_div₀, ← map_one (algebraMap M E), ← map_add, h1]
    obtain ⟨ε₃, hε₃, hε₃eq⟩ := exists_pow_eq_of_kummer hq hπE (hπEn ▸ hπ1) hη (by
      rw [hπEn, norm_algebraMap', hGn]
      exact (le_mul_of_one_le_right hA0.le hT.le).trans_lt hgood)
    obtain ⟨ε₄, hε₄, hε₄eq⟩ := exists_one_add_mul (E := E) (ε₁ := algebraMap M E ε₂)
      (by rwa [norm_algebraMap']) hε₃
    refine ⟨η, Ψ m, m, ε₄, hm0, hqm, hε₄, ?_⟩
    rw [hε₃eq, hGeq, map_mul, algebraMap_mono, map_add, map_one, mul_assoc, hε₄eq]
  · -- the Artin–Schreier regime
    push Not at hgood
    have hgA : ‖u₀ - h ^ q‖ ≤ A * ‖lam‖⁻¹ := by
      have := IsUltrametricDist.norm_add_le_max (u₀ - h ^ q - lev y Ψ) (lev y Ψ)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hinv hgood)
    set π' := algebraMap C M π
    have hπ'0 : π' ≠ 0 := (map_ne_zero _).2 hπ0
    have hπ'n : ‖π'‖ = ‖π‖ := norm_algebraMap' M π
    have hπ' : π' ^ (q - 1) = -(q : M) := by rw [← map_pow, hπ, map_neg, map_natCast]
    set c := (u₀ / h ^ q - 1) / π' ^ q with hcdef
    have hπ'q : π' ^ q ≠ 0 := pow_ne_zero _ hπ'0
    have hc : u₀ / h ^ q = 1 + π' ^ q * c := by rw [hcdef]; field_simp; ring
    have hcT : ‖c‖ ≤ ‖lam‖⁻¹ := by
      rw [hcdef, show u₀ / h ^ q - 1 = (u₀ - h ^ q) / h ^ q by field_simp, norm_div, norm_div,
        hhq, div_one, norm_pow, hπ'n, div_le_iff₀ hA0]
      linarith [hgA]
    have hε0pos : 0 < max ‖lam‖ (‖π‖ ^ (q - 1)) := lt_max_of_lt_left hl0
    obtain ⟨F, hF⟩ := exists_lev_near hy c hε0pos
    obtain ⟨h', c', hh', hc', halt⟩ :=
      phase2 hq hπ hlam hπ0 hπ1 hy.valTrans _ h c F rfl hh1 hc hcT hF.le
    have hh'0 : h' ≠ 0 := by intro h0; rw [h0, norm_zero] at hh'; exact zero_ne_one hh'
    rcases halt with hc'1 | ⟨hc'1, a, ha, m, hqm, ε, hε, hceq⟩
    · -- `u₀` would be a `q`-th power
      have hw : ‖π' ^ q * c'‖ < ‖π'‖ ^ q := by
        rw [norm_mul, norm_pow]
        exact mul_lt_of_lt_one_right (pow_pos (norm_pos_iff.2 hπ'0) q) hc'1
      obtain ⟨X, -, hX⟩ := exists_pow_eq_one_add_of_lt hq hπ' hπ'0 (hπ'n ▸ hπ1) hw
      refine absurd ?_ (hnoroot (h' * (1 + π' * X)))
      rw [mul_pow, hX, ← hc']
      field_simp
    · have hhE : algebraMap M E h' ≠ 0 := (map_ne_zero _).2 hh'0
      set X := (θ₁ / algebraMap M E h' - 1) / πE
      have hX : (1 + πE * X) ^ q = 1 + πE ^ q * algebraMap M E c' := by
        have h1 : 1 + πE * X = θ₁ / algebraMap M E h' := by simp only [X]; field_simp; ring
        rw [h1, div_pow, hθ₁, ← map_pow, ← map_div₀, hc', map_add, map_one, map_mul, map_pow,
          ← IsScalarTower.algebraMap_apply]
      obtain ⟨ε₅, hε₅, hε₅eq⟩ := exists_pow_eq_of_as hq hπE (hπEn ▸ hπ1) hπE0 hX (by
        rwa [norm_algebraMap'])
      obtain ⟨ε₆, hε₆, hε₆eq⟩ := exists_one_add_mul (E := E) (ε₁ := algebraMap M E ε)
        (by rwa [norm_algebraMap']) hε₅
      refine ⟨X, a, m, ε₆, ha, hqm, hε₆, ?_⟩
      rw [hε₅eq, hceq, map_mul, map_mul, map_zpow₀, ← IsScalarTower.algebraMap_apply, map_add,
        map_one, mul_assoc, hε₆eq]


end Main

end Type3

end SemistableReduction
