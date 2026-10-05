/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeUpwardMain

/-!
# Germs of Gauss valuations at the outer vertex

Blueprint §9.10, L3, R4(ii) (the germ lemmas G1–G3). Let `w_s = w_{0,s}` be the Gauss valuations
of `C(x)` and `v` the extensions of `w_{0,1}` to `F'`.

* `CurvePlace.valuation_aeval_eq`: for a place `Q` and `π` in its maximal ideal, a polynomial
  `p ≠ 0` with constant coefficients satisfies `Q(p(π)) = Q(π)^{ord₀ p}`;
* `eventually_gaussRat_le_one`: (**bridge**) if `gauss₁(a) ≤ 1` and the residue of `a` is regular
  at a zero of `x̄`, then `w_s(a) ≤ 1` for all `s < 1` close to `1`.
-/

open Polynomial WithZero
open scoped NNReal

namespace SemistableReduction

namespace CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ)

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma aeval_mem_V {π : κ} (hπ : π ∈ Q.V) (p : k[X]) : aeval π p ∈ Q.V := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add]; exact add_mem hp hq
  | monomial n c =>
    rw [aeval_monomial]
    exact mul_mem (Q.algebraMap_mem c) (pow_mem hπ n)

/-- `Q(p(π)) = Q(π)^{ord₀ p}` for `π` in the maximal ideal of `Q`. -/
lemma valuation_aeval_eq {π : κ} (hπ : Q.valuation π < 1) {p : k[X]} (hp : p ≠ 0) :
    Q.valuation (aeval π p) = Q.valuation π ^ p.natTrailingDegree := by
  obtain ⟨q, hpq, hndvd⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp 0
  rw [rootMultiplicity_eq_natTrailingDegree', map_zero, sub_zero] at hpq
  have hq0 : q.eval 0 ≠ 0 := by
    intro h0
    apply hndvd
    rw [map_zero, sub_zero, X_dvd_iff, coeff_zero_eq_eval_zero]
    exact h0
  have hπV : π ∈ Q.V := Q.valuation_le_one_iff.1 hπ.le
  have hq1 : Q.valuation (aeval π q) = 1 := by
    refine le_antisymm (Q.valuation_le_one_iff.2 (Q.aeval_mem_V hπV q)) (not_lt.1 fun h ↦ ?_)
    have := Q.res_eq_zero_of_lt_one h
    rw [Q.res_aeval hπ, coeff_zero_eq_eval_zero] at this
    exact hq0 this
  conv_lhs => rw [hpq]
  rw [map_mul, map_pow, aeval_X, map_mul, map_pow, hq1, mul_one]

end CurvePlace

section PolyGerm

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]

/-- **Germ of a Gauss norm below `1`.** If `‖q_j‖ = 1` and the coefficients `p_i`, `i < j`, of a
polynomial `p` with integral coefficients are small, then `w_{0,s}(p) ≤ w_{0,s}(q)` for `s < 1`
close to `1`. -/
lemma exists_sup_le_sup {p q : C[X]} (hp : ∀ i, ‖p.coeff i‖ ≤ 1) {j : ℕ}
    (hqj : ‖q.coeff j‖ = 1) (hpj : ∀ i < j, ‖p.coeff i‖ < 1) :
    ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ s : ℝ≥0ˣ, s₀ < (s : ℝ≥0) → (s : ℝ≥0) ≤ 1 →
      Gauss.sup (NormedField.valuation (K := C)) s p ≤
        Gauss.sup (NormedField.valuation (K := C)) s q := by
  set r : ℝ≥0 := (Finset.range j).sup fun i ↦ ‖p.coeff i‖₊
  have hr : r < 1 := by
    refine (Finset.sup_lt_iff zero_lt_one).2 fun i hi ↦ ?_
    have := hpj i (Finset.mem_range.1 hi)
    exact_mod_cast this
  have key : ∀ s : ℝ≥0ˣ, r < (s : ℝ≥0) ^ j → (s : ℝ≥0) ≤ 1 →
      Gauss.sup (NormedField.valuation (K := C)) s p ≤
        Gauss.sup (NormedField.valuation (K := C)) s q := by
    intro s hrs hs1
    refine le_trans ?_ (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := s) q j)
    have hqj' : ‖q.coeff j‖₊ = 1 := by ext; simpa using hqj
    simp only [Gauss.term, NormedField.valuation_apply, hqj', one_mul]
    refine Gauss.sup_le_iff.2 fun i ↦ ?_
    simp only [Gauss.term, NormedField.valuation_apply]
    rcases lt_or_ge i j with hij | hij
    · have h1 : ‖p.coeff i‖₊ ≤ r :=
        Finset.le_sup (f := fun i ↦ ‖p.coeff i‖₊) (Finset.mem_range.2 hij)
      calc ‖p.coeff i‖₊ * (s : ℝ≥0) ^ i ≤ r * 1 :=
            mul_le_mul' h1 (pow_le_one₀ zero_le hs1)
        _ ≤ (s : ℝ≥0) ^ j := by rw [mul_one]; exact hrs.le
    · have h1 : ‖p.coeff i‖₊ ≤ 1 := by exact_mod_cast hp i
      calc ‖p.coeff i‖₊ * (s : ℝ≥0) ^ i ≤ 1 * (s : ℝ≥0) ^ i := mul_le_mul_left h1 _
        _ ≤ (s : ℝ≥0) ^ j := by rw [one_mul]; exact pow_le_pow_of_le_one zero_le hs1 hij
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · refine ⟨0, zero_lt_one, fun s _ hs1 ↦ key s ?_ hs1⟩
    simp only [Finset.range_zero, Finset.sup_empty, bot_eq_zero', pow_zero, r]
    exact zero_lt_one
  refine ⟨r ^ ((j : ℝ)⁻¹), NNReal.rpow_lt_one hr (by positivity), fun s hs hs1 ↦ key s ?_ hs1⟩
  calc r = (r ^ ((j : ℝ)⁻¹)) ^ j := (NNReal.rpow_inv_natCast_pow r hj.ne').symm
    _ < (s : ℝ≥0) ^ j := pow_lt_pow_left₀ hs zero_le hj.ne'

end PolyGerm

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm TubeCount IsLocalRing

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)
local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

section Germ

variable (C) in
/-- `a ∈ C(x)` is **integral near the outer boundary**: `w_{0,s}(a) ≤ 1` for all `s < 1` close
to `1`. -/
def IsGermLE (a : RatFunc C) : Prop :=
  ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ s : ℝ≥0ˣ, s₀ < (s : ℝ≥0) → (s : ℝ≥0) < 1 → w s a ≤ 1

omit [IsAlgClosed C] in
lemma gaussRat_algebraMap_poly (s : ℝ≥0ˣ) (p : C[X]) :
    w s (algebraMap C[X] (RatFunc C) p) = Gauss.sup (NormedField.valuation (K := C)) s p := by
  rw [gaussRat_algebraMap, gauss_apply, taylor_zero]

omit [IsAlgClosed C] in
lemma exists_lift_integers {f : C[X]} (hf : ∀ i, ‖f.coeff i‖ ≤ 1) :
    ∃ P : (HenselComplete.integers C)[X], P.map (algebraMap _ C) = f := by
  have : f ∈ Polynomial.lifts (algebraMap (HenselComplete.integers C) C) := by
    rw [lifts_iff_coeff_lifts]
    exact fun n ↦ ⟨⟨f.coeff n, (HenselComplete.mem_integers_iff _).2 (hf n)⟩, rfl⟩
  obtain ⟨P, hP⟩ := this
  exact ⟨P, by rw [← hP, coe_mapRingHom]⟩

omit [IsAlgClosed C] in
lemma residue_eq_zero_iff_norm (o : HenselComplete.integers C) :
    residue _ o = 0 ↔ ‖(o : C)‖ < 1 := by
  rw [residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]

/-- **The germ bridge.** If `w_{0,1}(a) ≤ 1` and the residue of `a` is regular at a zero `Q₀` of
`x̄` (on some residue curve `κ(v₀)`), then `w_{0,s}(a) ≤ 1` for all `s < 1` close to `1`: writing
`a = p / q` with `‖q‖ = 1`, the order of `ā` at `x̄ = 0` is the difference of the trailing degrees
of `p̄` and `q̄`, and `w_{0,s}(p) ≤ w_{0,s}(q)` near `1` (`exists_sup_le_sup`). -/
theorem isGermLE_of_red {a : RatFunc C} (ha : gauss1 C a ≤ 1) (v₀ : Ext C F')
    {Q₀ : CurvePlace 𝓀 (ResidueField v₀.1.valuationSubring)}
    (hQ₀ : Q₀ ∈ zeros 𝓀 (red C (xF C F') v₀))
    (hreg : red C (algebraMap (RatFunc C) F' a) v₀ ∈ Q₀.V) : IsGermLE C a := by
  obtain ⟨γ, hγ0, q, hq, hq1, hqc⟩ := exists_normalize a.denom_ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [Gauss.sup_zero] at hq1
    exact zero_ne_one hq1
  set p : C[X] := Polynomial.C γ⁻¹ * a.num
  have hq0' : algebraMap C[X] (RatFunc C) q ≠ 0 := by simpa using hq0
  have hpq : a * algebraMap C[X] (RatFunc C) q = algebraMap C[X] (RatFunc C) p := by
    have hden : algebraMap C[X] (RatFunc C) a.denom ≠ 0 := by simpa using a.denom_ne_zero
    have h1 : a * algebraMap C[X] (RatFunc C) a.denom = algebraMap C[X] (RatFunc C) a.num := by
      have := RatFunc.num_div_denom a
      rw [div_eq_iff hden] at this
      exact this.symm
    have e1 : algebraMap C[X] (RatFunc C) (Polynomial.C γ⁻¹) *
        algebraMap C[X] (RatFunc C) (Polynomial.C γ) = 1 := by
      rw [← map_mul, ← Polynomial.C_mul, inv_mul_cancel₀ hγ0, Polynomial.C_1, map_one]
    rw [hq, map_mul] at h1
    simp only [p, map_mul, ← h1]
    linear_combination (a * algebraMap C[X] (RatFunc C) q) * e1.symm
  have hp1 : Gauss.sup (NormedField.valuation (K := C)) 1 p ≤ 1 := by
    rw [← gauss1_algebraMap, ← hpq, map_mul, gauss1_algebraMap, hq1, mul_one]
    exact ha
  have hpc (i : ℕ) : ‖p.coeff i‖ ≤ 1 := by
    have := (Gauss.term_le_sup (v := NormedField.valuation (K := C)) (r := 1) p i).trans hp1
    simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply] at this
    exact_mod_cast this
  obtain ⟨P, hP⟩ := exists_lift_integers hpc
  obtain ⟨Q, hQ⟩ := exists_lift_integers hqc
  set pb := P.map (residue (HenselComplete.integers C))
  set qb := Q.map (residue (HenselComplete.integers C))
  have hcoeffP (i : ℕ) : ((P.coeff i : HenselComplete.integers C) : C) = p.coeff i := by
    rw [← hP, coeff_map]; rfl
  have hcoeffQ (i : ℕ) : ((Q.coeff i : HenselComplete.integers C) : C) = q.coeff i := by
    rw [← hQ, coeff_map]; rfl
  have hqb0 : qb ≠ 0 := by
    obtain ⟨i, hi⟩ := Gauss.exists_term_eq_sup (v := NormedField.valuation (K := C)) (r := 1) q
    rw [hq1] at hi
    simp only [Gauss.term, Units.val_one, one_pow, mul_one, NormedField.valuation_apply] at hi
    intro h
    have h' : qb.coeff i = 0 := by rw [h, coeff_zero]
    rw [coeff_map, residue_eq_zero_iff_norm, hcoeffQ] at h'
    have : ‖q.coeff i‖ = 1 := by rw [← coe_nnnorm, hi, NNReal.coe_one]
    exact absurd h' (by rw [this]; exact lt_irrefl 1)
  set j := qb.natTrailingDegree
  have hqj : ‖q.coeff j‖ = 1 := by
    have hne : qb.coeff j ≠ 0 := trailingCoeff_nonzero_iff_nonzero.2 hqb0
    rw [coeff_map, Ne, residue_eq_zero_iff_norm, hcoeffQ, not_lt] at hne
    exact le_antisymm (hqc j) hne
  have hpj : ∀ i < j, ‖p.coeff i‖ < 1 := by
    intro i hi
    rw [← hcoeffP, ← residue_eq_zero_iff_norm, ← coeff_map]
    change pb.coeff i = 0
    by_cases hpb0 : pb = 0
    · rw [hpb0, coeff_zero]
    refine coeff_eq_zero_of_lt_natTrailingDegree (lt_of_lt_of_le hi ?_)
    have hx1 : v₀.1 (xF C F') ≤ 1 := (valuation_xF v₀).le
    have hredp : red C (algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) p)) v₀ =
        aeval (red C (xF C F') v₀) pb := by
      rw [← aeval_xF, ← hP]
      exact red_aeval_of_le hx1 P
    have hredq : red C (algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) q)) v₀ =
        aeval (red C (xF C F') v₀) qb := by
      rw [← aeval_xF, ← hQ]
      exact red_aeval_of_le hx1 Q
    have hav : v₀.1 (algebraMap (RatFunc C) F' a) ≤ 1 := by rw [valuation_algebraMap]; exact ha
    have hqv : v₀.1 (algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) q)) = 1 := by
      rw [valuation_algebraMap, gauss1_algebraMap, hq1]
    have hqb' : aeval (red C (xF C F') v₀) qb ≠ 0 := by
      rw [← hredq, Ne, red_eq_zero_iff hqv.le, hqv]
      exact lt_irrefl 1
    have hmul := red_mul hav hqv.le
    rw [← map_mul, hpq, hredp, hredq] at hmul
    have hdiv : red C (algebraMap (RatFunc C) F' a) v₀ =
        aeval (red C (xF C F') v₀) pb / aeval (red C (xF C F') v₀) qb :=
      eq_div_of_mul_eq hqb' hmul.symm
    rw [hdiv] at hreg
    have h := ((res_div_aeval Q₀ (valuation_x_lt_one hQ₀) (red_xF_ne_zero' v₀) hpb0
      hqb0).1).1 hreg
    rwa [rootMultiplicity_eq_natTrailingDegree', rootMultiplicity_eq_natTrailingDegree'] at h
  obtain ⟨s₀, hs₀, hle⟩ := exists_sup_le_sup hpc hqj hpj
  refine ⟨s₀, hs₀, fun s hs hs1 ↦ ?_⟩
  have ha' : a = algebraMap C[X] (RatFunc C) p / algebraMap C[X] (RatFunc C) q :=
    eq_div_of_mul_eq hq0' hpq
  have hpos : 0 < Gauss.sup (NormedField.valuation (K := C)) s q :=
    pos_iff_ne_zero.2 fun h ↦ hq0 (Gauss.sup_eq_zero_iff.1 h)
  rw [ha', map_div₀, gaussRat_algebraMap_poly, gaussRat_algebraMap_poly]
  exact div_le_one_of_le₀ (hle s hs hs1.le) hpos.le

omit [IsAlgClosed C] in
lemma isGermLE_zero : IsGermLE C 0 := ⟨0, zero_lt_one, fun s _ _ ↦ by simp⟩

omit [IsAlgClosed C] in
lemma IsGermLE.add {a b : RatFunc C} (ha : IsGermLE C a) (hb : IsGermLE C b) :
    IsGermLE C (a + b) := by
  obtain ⟨s₁, hs₁, h₁⟩ := ha
  obtain ⟨s₂, hs₂, h₂⟩ := hb
  refine ⟨max s₁ s₂, max_lt hs₁ hs₂, fun s hs hs1 ↦ ?_⟩
  exact (Valuation.map_add _ _ _).trans (max_le (h₁ s ((le_max_left _ _).trans_lt hs) hs1)
    (h₂ s ((le_max_right _ _).trans_lt hs) hs1))

omit [IsAlgClosed C] in
lemma IsGermLE.const_mul {a : RatFunc C} (ha : IsGermLE C a) {l : C} (hl : ‖l‖ ≤ 1) :
    IsGermLE C (algebraMap C (RatFunc C) l * a) := by
  obtain ⟨s₀, hs₀, h⟩ := ha
  refine ⟨s₀, hs₀, fun s hs hs1 ↦ ?_⟩
  rw [map_mul, gaussRat_algebraMap_C, NormedField.valuation_apply]
  exact mul_le_one' (by exact_mod_cast hl) (h s hs hs1)

omit [IsAlgClosed C] in
/-- Finitely many germ-integral functions are simultaneously integral near the boundary. -/
lemma exists_forall_isGermLE {ι : Type*} (S : Finset ι) (f : ι → RatFunc C)
    (hf : ∀ i ∈ S, IsGermLE C (f i)) :
    ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ s : ℝ≥0ˣ, s₀ < (s : ℝ≥0) → (s : ℝ≥0) < 1 → ∀ i ∈ S, w s (f i) ≤ 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, zero_lt_one, fun _ _ _ i hi ↦ absurd hi (Finset.notMem_empty i)⟩
  | insert a S ha ih =>
    obtain ⟨s₁, hs₁, h₁⟩ := hf a (Finset.mem_insert_self a S)
    obtain ⟨s₂, hs₂, h₂⟩ := ih fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)
    refine ⟨max s₁ s₂, max_lt hs₁ hs₂, fun s hs hs1 i hi ↦ ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h₁ s ((le_max_left _ _).trans_lt hs) hs1
    · exact h₂ s ((le_max_right _ _).trans_lt hs) hs1 i hi

variable (C) in
/-- The germ-integral functions, as an additive submonoid. -/
def germSubmonoid : AddSubmonoid (RatFunc C) where
  carrier := {a | IsGermLE C a}
  zero_mem' := isGermLE_zero
  add_mem' ha hb := ha.add hb

/-- **Coefficients from values** (Lagrange interpolation at nodes with distinct residues): a
polynomial over a `C`-algebra `K` whose values at all integral constants lie in an additive
submonoid `G` stable under integral constants has all its coefficients in `G`. -/
lemma coeff_mem_of_eval_mem {K : Type*} [Field K] [Algebra C K] (G : AddSubmonoid K)
    (hG : ∀ l : C, ‖l‖ ≤ 1 → ∀ a ∈ G, algebraMap C K l * a ∈ G) (P : K[X])
    (heval : ∀ t : C, ‖t‖ ≤ 1 → P.eval (algebraMap C K t) ∈ G) (i : ℕ) : P.coeff i ∈ G := by
  classical
  set n := P.natDegree
  let e : Fin (n + 1) ↪ 𝓀 := Fin.valEmbedding.trans (Infinite.natEmbedding 𝓀)
  choose t ht using fun j : Fin (n + 1) ↦ residue_surjective (e j)
  set ν : Fin (n + 1) → K := fun j ↦ algebraMap C K (t j)
  have hdist (j l : Fin (n + 1)) (hjl : j ≠ l) : ‖((t j : C) - t l)‖ = 1 := by
    refine le_antisymm ((HenselComplete.mem_integers_iff _).1 (t j - t l).2) (not_lt.1 fun h ↦ ?_)
    have h0 : residue _ (t j - t l) = 0 := (residue_eq_zero_iff_norm _).2 h
    rw [map_sub, ht, ht, sub_eq_zero] at h0
    exact hjl (e.injective h0)
  have hinj : Set.InjOn ν (Finset.univ : Finset (Fin (n + 1))) := by
    intro j _ l _ hjl
    by_contra hne
    have h1 := hdist j l hne
    have h2 : ((t j : C) - t l) = 0 := by
      rw [sub_eq_zero]
      exact (algebraMap C K).injective hjl
    rw [h2, norm_zero] at h1
    exact zero_ne_one h1
  have hdeg : P.degree < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt degree_le_natDegree (by exact_mod_cast Nat.lt_succ_self n)
  set φ : HenselComplete.integers C →+* K := (algebraMap C K).comp (Subring.subtype _)
  have hbasis (j : Fin (n + 1)) : Lagrange.basis Finset.univ ν j ∈ Polynomial.lifts φ := by
    refine prod_mem fun l hl ↦ ?_
    have hjl : j ≠ l := (Finset.ne_of_mem_erase hl).symm
    have hinv : ‖((t j : C) - t l)⁻¹‖ ≤ 1 := by rw [norm_inv, hdist j l hjl, inv_one]
    have h1 : (ν j - ν l)⁻¹ = φ ⟨_, (HenselComplete.mem_integers_iff _).2 hinv⟩ := by
      change _ = algebraMap C K ((t j : C) - t l)⁻¹
      rw [map_inv₀, map_sub]
    have h2 : -ν l = φ (-t l) := by
      change _ = algebraMap C K (-(t l : C))
      rw [map_neg]
    have h3 : X - Polynomial.C (ν l) = X + Polynomial.C (φ (-t l)) := by
      rw [← h2, Polynomial.C_neg, sub_eq_add_neg]
    rw [Lagrange.basisDivisor, h1, h3]
    exact mul_mem (C_mem_lifts _ _) (add_mem (X_mem_lifts _) (C_mem_lifts _ _))
  rw [Lagrange.eq_interpolate hinj hdeg, Lagrange.interpolate_apply, finsetSum_coeff]
  refine sum_mem fun j _ ↦ ?_
  rw [coeff_C_mul]
  obtain ⟨o, ho⟩ := (lifts_iff_coeff_lifts _).1 (hbasis j) i
  rw [← ho, mul_comm]
  exact hG o ((HenselComplete.mem_integers_iff _).1 o.2) _
    (heval _ ((HenselComplete.mem_integers_iff _).1 (t j).2))

/-- A root of a monic polynomial with integral coefficients is integral. -/
lemma valuation_le_one_of_aeval_eq_zero {K L Γ : Type*} [Field K] [Field L] [Algebra K L]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation L Γ) {P : K[X]} (hP : P.Monic) {y : L}
    (hy : aeval y P = 0) (hc : ∀ i, v (algebraMap K L (P.coeff i)) ≤ 1) : v y ≤ 1 := by
  by_contra! h
  set n := P.natDegree
  rw [aeval_eq_sum_range, Finset.sum_range_succ, hP.coeff_natDegree, one_smul] at hy
  have hlt : v (∑ i ∈ Finset.range n, P.coeff i • y ^ i) < v y ^ n := by
    refine Valuation.map_sum_lt _ (pow_ne_zero _ (ne_of_gt (zero_lt_one.trans h))) fun i hi ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow]
    calc v (algebraMap K L (P.coeff i)) * v y ^ i ≤ 1 * v y ^ i := mul_le_mul_left (hc i) _
      _ < v y ^ n := by rw [one_mul]; exact pow_lt_pow_right₀ h (Finset.mem_range.1 hi)
  have heq : y ^ n = -∑ i ∈ Finset.range n, P.coeff i • y ^ i := eq_neg_of_add_eq_zero_right hy
  have h2 : v y ^ n = v (∑ i ∈ Finset.range n, P.coeff i • y ^ i) := by
    rw [← map_pow, heq, Valuation.map_neg]
  rw [← h2] at hlt
  exact lt_irrefl _ hlt

end Germ

section Norm

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- The norm of an element integral at the outer vertex, with residues regular at the zeros of
`x̄`, is integral near the outer boundary: its residue is the product of the residue norms
(`residue_norm_eq_prod`), which are regular at `x̄ = 0` (`res_norm_residue`). -/
theorem isGermLE_norm {z : F'} (hz : ∀ v : Ext C F', v.1 z ≤ 1)
    (hzQ : ∀ v : Ext C F', ∀ Q ∈ zeros 𝓀 (red C (xF C F') v), red C z v ∈ Q.V) (v₀ : Ext C F')
    {Q₀ : CurvePlace 𝓀 (ResidueField v₀.1.valuationSubring)}
    (hQ₀ : Q₀ ∈ zeros 𝓀 (red C (xF C F') v₀)) : IsGermLE C (Algebra.norm (RatFunc C) z) := by
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  obtain ⟨hN1, hres⟩ := residue_norm_eq_prod ramificationIdx_eq_one
    (sum_inertiaDeg_eq hp hp1 (F := F')) (gnorm_le_iff.2 hz)
  refine isGermLE_of_red hN1 v₀ hQ₀ ?_
  rw [red_algebraMap_rat v₀ hN1, hres, map_prod]
  refine prod_mem fun v _ ↦ ?_
  obtain ⟨Qv, hQv⟩ := exists_mem_zeros v
  exact (res_algebraMap_eq _ v v₀ hQv hQ₀ (res_norm_residue v hQv (hzQ v)).1).1

include hp hp1 in
/-- **Integrality near the outer boundary (G2/G3).** An element `y ∈ F'` integral at the outer
vertex whose residues are regular at all zeros of `x̄` has value `≤ 1` at every extension of
`w_{0,s}` for all `s < 1` close to `1`: the coefficients of its characteristic polynomial are
integral near the boundary, by Lagrange interpolation (`coeff_mem_of_eval_mem`) from the norms
`N(y - t) = ± χ_y(t)` (`isGermLE_norm`). -/
theorem exists_valuation_le_one_near {y : F'} (hy : ∀ v : Ext C F', v.1 y ≤ 1)
    (hyQ : ∀ v : Ext C F', ∀ Q ∈ zeros 𝓀 (red C (xF C F') v), red C y v ∈ Q.V) (v₀ : Ext C F')
    {Q₀ : CurvePlace 𝓀 (ResidueField v₀.1.valuationSubring)}
    (hQ₀ : Q₀ ∈ zeros 𝓀 (red C (xF C F') v₀)) :
    ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ s : ℝ≥0ˣ, s₀ < (s : ℝ≥0) → (s : ℝ≥0) < 1 →
      ∀ w' : GaussExtension (0 : C) s F', w'.1 y ≤ 1 := by
  set P := normPoly (RatFunc C) y
  have hcoeff : ∀ i, IsGermLE C (P.coeff i) := by
    refine coeff_mem_of_eval_mem (germSubmonoid C) (fun l hl a ha ↦ IsGermLE.const_mul ha hl) P
      fun t ht ↦ ?_
    set z := y - algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) t)
    have hN := norm_sub_algebraMap (F := RatFunc C) y (algebraMap C (RatFunc C) t)
    have heq : P.eval (algebraMap C (RatFunc C) t) = algebraMap C (RatFunc C)
        ((-1) ^ Module.finrank (RatFunc C) F') * Algebra.norm (RatFunc C) z := by
      rw [hN, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow,
        one_mul]
    change IsGermLE C _
    rw [heq]
    refine IsGermLE.const_mul ?_ (by simp)
    have htv (v : Ext C F') :
        v.1 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) t)) ≤ 1 := by
      rw [valuation_algebraMap, gauss1_algebraMap_C]
      exact_mod_cast ht
    have hzv (v : Ext C F') : v.1 z ≤ 1 :=
      (Valuation.map_sub _ _ _).trans (max_le (hy v) (htv v))
    refine isGermLE_norm hp hp1 hzv (fun v Q hQ ↦ ?_) v₀ hQ₀
    rw [red_sub (hy v) (htv v), ← IsScalarTower.algebraMap_apply,
      red_algebraMap_C t (by exact_mod_cast ht)]
    exact sub_mem (hyQ v Q hQ) (Q.algebraMap_mem _)
  obtain ⟨s₀, hs₀, h⟩ := exists_forall_isGermLE (Finset.range (P.natDegree + 1)) P.coeff
    fun i _ ↦ hcoeff i
  refine ⟨s₀, hs₀, fun s hs hs1 w' ↦ ?_⟩
  refine valuation_le_one_of_aeval_eq_zero w'.1 (monic_normPoly (F := RatFunc C) y) ?_ fun i ↦ ?_
  · rw [normPoly, map_pow, minpoly.aeval, zero_pow Module.finrank_pos.ne']
  · rw [← Valuation.comap_apply, w'.2]
    by_cases hi : i ≤ P.natDegree
    · exact h s hs hs1 i (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero]
      exact zero_le

end Norm

section Clearing

omit [IsAlgClosed C] in
lemma gaussRat_prod_X_sub_C (s : ℝ≥0ˣ) (M : Multiset C) :
    w s (algebraMap C[X] (RatFunc C) (M.map fun a ↦ X - Polynomial.C a).prod) =
      (M.map fun a ↦ max ‖a‖₊ (s : ℝ≥0)).prod := by
  rw [map_multiset_prod, map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl fun a _ ↦ gaussRat_X_sub_C s a

/-- **Clearing the poles of a denominator near the boundary.** For `h ∈ C[x] ∖ 0` there are
`τ = κ h / xᴺ` and `s₂ < 1` with `w_{0,s}(τ) = 1` for all `s ∈ [s₂, 1]`: the zeros of `h` in the
open unit disc are cancelled by `xᴺ`, the others have absolute value `≥ 1`. -/
lemma exists_clearing {h : C[X]} (h0 : h ≠ 0) :
    ∃ s₂ : ℝ≥0, s₂ < 1 ∧ ∃ τ : RatFunc C, ∃ N : ℕ, ∃ κ : C,
      τ * RatFunc.X ^ N = algebraMap C[X] (RatFunc C) (Polynomial.C κ * h) ∧
      ∀ s : ℝ≥0ˣ, s₂ ≤ (s : ℝ≥0) → (s : ℝ≥0) ≤ 1 → w s τ = 1 := by
  classical
  set R := h.roots
  set D := R.filter fun a ↦ ‖a‖₊ < 1
  set B := R.filter fun a ↦ ¬ ‖a‖₊ < 1
  have hR : R = D + B := (Multiset.filter_add_not _ R).symm
  set s₂ := D.toFinset.sup fun a ↦ ‖a‖₊
  have hs₂ : s₂ < 1 := by
    refine (Finset.sup_lt_iff zero_lt_one).2 fun a ha ↦ ?_
    exact (Multiset.mem_filter.1 (Multiset.mem_toFinset.1 ha)).2
  have hB1 : ∀ a ∈ B, 1 ≤ ‖a‖₊ := fun a ha ↦ not_lt.1 (Multiset.mem_filter.1 ha).2
  have hB0 : (0 : C) ∉ B := fun h0B ↦ by simpa using hB1 0 h0B
  have hlc : h.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.2 h0
  have hBp : B.prod ≠ 0 := Multiset.prod_ne_zero hB0
  set κ := (h.leadingCoeff * B.prod)⁻¹
  set N := Multiset.card D
  have hX : (RatFunc.X : RatFunc C) ^ N ≠ 0 := pow_ne_zero _ RatFunc.X_ne_zero
  refine ⟨s₂, hs₂, algebraMap C[X] (RatFunc C) (Polynomial.C κ * h) / RatFunc.X ^ N, N, κ,
    div_mul_cancel₀ _ hX, fun s hs hs1 ↦ ?_⟩
  have hfac : h = Polynomial.C h.leadingCoeff * (R.map fun a ↦ X - Polynomial.C a).prod :=
    (C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree).symm
  have hw : w s (algebraMap C[X] (RatFunc C) h) =
      ‖h.leadingCoeff‖₊ * (R.map fun a ↦ max ‖a‖₊ (s : ℝ≥0)).prod := by
    conv_lhs => rw [hfac]
    rw [map_mul, map_mul, gaussRat_algebraMap, gauss_C, NormedField.valuation_apply,
      gaussRat_prod_X_sub_C]
  have hD : (D.map fun a ↦ max ‖a‖₊ (s : ℝ≥0)).prod = (s : ℝ≥0) ^ N := by
    rw [Multiset.map_congr rfl fun a ha ↦ max_eq_right
      ((Finset.le_sup (f := fun a ↦ ‖a‖₊) (Multiset.mem_toFinset.2 ha)).trans hs),
      Multiset.map_const', Multiset.prod_replicate]
  have hB : (B.map fun a ↦ max ‖a‖₊ (s : ℝ≥0)).prod = (B.map fun a ↦ ‖a‖₊).prod := by
    rw [Multiset.map_congr rfl fun a ha ↦ max_eq_left (hs1.trans (hB1 a ha))]
  have hBn : ‖B.prod‖₊ = (B.map fun a ↦ ‖a‖₊).prod := by
    have := map_multiset_prod (NormedField.valuation (K := C)) B
    simpa using this
  have hs0 : (s : ℝ≥0) ^ N ≠ 0 := pow_ne_zero _ s.ne_zero
  have hBn0 : (B.map fun a ↦ ‖a‖₊).prod ≠ 0 := by rw [← hBn]; exact nnnorm_ne_zero_iff.2 hBp
  have hlc0 : ‖h.leadingCoeff‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 hlc
  rw [map_div₀, map_pow, AnnulusUnit.gaussRat_X, map_mul, map_mul,
    gaussRat_algebraMap (p := Polynomial.C κ), gauss_C, NormedField.valuation_apply, hw, hR,
    Multiset.map_add, Multiset.prod_add, hD, hB]
  simp only [κ, nnnorm_inv, nnnorm_mul, hBn]
  field_simp

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- A polynomial denominator: `h y` is integral over `C[x]` for some `h ≠ 0`. -/
lemma exists_denominator (y : F') : ∃ h : C[X], h ≠ 0 ∧
    IsIntegral (Algebra.adjoin C {xF C F'})
      (algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) h) * y) := by
  letI : Algebra C[X] F' := ((algebraMap (RatFunc C) F').comp
    (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) F' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨h, h0, hint⟩ := exists_integral_multiples C[X] (RatFunc C) {y}
  refine ⟨h, h0, ?_⟩
  have hf := hint y (Finset.mem_singleton_self y)
  rw [Algebra.smul_def] at hf
  have hrange : Algebra.adjoin C {xF C F'} = (aeval (xF C F') : C[X] →ₐ[C] F').range :=
    Algebra.adjoin_singleton_eq_range_aeval C (xF C F')
  set ψ : C[X] →+* Algebra.adjoin C {xF C F'} :=
    (Subalgebra.equivOfEq _ _ hrange.symm).toRingHom.comp
      (aeval (xF C F') : C[X] →ₐ[C] F').rangeRestrict.toRingHom
  refine IsIntegral.map_of_comp_eq ψ (RingHom.id F') (RingHom.ext fun P ↦ ?_) hf
  change aeval (xF C F') P = algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) P)
  exact aeval_xF P

end Clearing

section Tau

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) F']

include hp hp1 in
omit [Algebra.IsSeparable (RatFunc C) F'] in
/-- **Regularity at the node points near the boundary (G2).** For `y` as in
`exists_valuation_le_one_near`, there is `s₀ < 1` such that for every node chart
`O_C[x, c/x]` with `s₀ < |c| < 1` some `τ` of the node chart, not in the node ideal, has
`τ y ∈ R' = Rint c F'` (maximum principle `isIntegral_of_le`, with the poles of `y` cleared by
`exists_clearing`). -/
theorem exists_tau_near {y : F'} (hy : ∀ v : Ext C F', v.1 y ≤ 1)
    (hyQ : ∀ v : Ext C F', ∀ Q ∈ zeros 𝓀 (red C (xF C F') v), red C y v ∈ Q.V) (v₀ : Ext C F')
    {Q₀ : CurvePlace 𝓀 (ResidueField v₀.1.valuationSubring)}
    (hQ₀ : Q₀ ∈ zeros 𝓀 (red C (xF C F') v₀)) :
    ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ c : C, (hc0 : c ≠ 0) → s₀ < ‖c‖₊ → ‖c‖ < 1 →
      ∃ τ : nodeRing c, τ ∉ tubeIdeal c ∧
        IsIntegral (nodeRing c) (algebraMap (RatFunc C) F' (τ : RatFunc C) * y) := by
  obtain ⟨s₁, hs₁, hB⟩ := exists_valuation_le_one_near hp hp1 hy hyQ v₀ hQ₀
  obtain ⟨h, h0, hint⟩ := exists_denominator (C := C) y
  obtain ⟨s₂, hs₂, τ, N, κ, hτ, hw⟩ := exists_clearing h0
  refine ⟨max s₁ s₂, max_lt hs₁ hs₂, fun c hc0 hcs hc1 ↦ ?_⟩
  have hc1' : ‖c‖₊ < 1 := by exact_mod_cast hc1
  set sc : ℝ≥0ˣ := Units.mk0 ‖c‖₊ (by simpa using hc0)
  have hwc : w sc τ = 1 := hw sc ((le_max_right _ _).trans hcs.le) hc1'.le
  have hw1 : w 1 τ = 1 := hw 1 hs₂.le le_rfl
  have hmem : τ ∈ nodeRing c := mem_nodeRing_of_mul_pow hc0 hτ hw1.le hwc.le
  refine ⟨⟨τ, hmem⟩, fun hτm ↦ ?_, ?_⟩
  · obtain ⟨t, ht1, ht2⟩ := exists_between hc1'
    set st : ℝ≥0ˣ := Units.mk0 t (ne_of_gt (lt_of_le_of_lt zero_le ht1))
    have hst : st ∈ segment c := ⟨ht1, ht2⟩
    have h1 := (mem_tubeIdeal_iff _ hst).1 hτm
    rw [show ((⟨τ, hmem⟩ : nodeRing c) : RatFunc C) = τ from rfl,
      hw st (((le_max_right _ _).trans hcs.le).trans ht1.le) ht2.le] at h1
    exact lt_irrefl 1 h1
  · refine isIntegral_of_le hp hp1 hc0 (N := N) ?_ (fun v ↦ ?_) (fun v ↦ ?_)
    · have hκ : algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) (Polynomial.C κ)) =
          algebraMap C F' κ := by
        rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]
      have heq : xF C F' ^ N * (algebraMap (RatFunc C) F' τ * y) = algebraMap C F' κ *
          (algebraMap (RatFunc C) F' (algebraMap C[X] (RatFunc C) h) * y) := by
        rw [← mul_assoc, xF, ← map_pow, ← map_mul, mul_comm (RatFunc.X ^ N), hτ, map_mul,
          map_mul, hκ, mul_assoc]
      change IsIntegral _ (xF C F' ^ N * (algebraMap (RatFunc C) F' τ * y))
      rw [heq]
      exact IsIntegral.mul (isIntegral_algebraMap (x := (⟨algebraMap C F' κ,
        Subalgebra.algebraMap_mem _ κ⟩ : Algebra.adjoin C {xF C F'}))) hint
    · change v.1 (algebraMap (RatFunc C) F' τ * y) ≤ 1
      rw [map_mul, valuation_algebraMap]
      exact mul_le_one' hw1.le (hy v)
    · change v.1 (algebraMap (RatFunc C) F' τ * y) ≤ 1
      have hrad : invRad hc0 1 = sc := by
        ext
        simp [coe_invRad, sc]
      have hvy : v.1 y ≤ 1 := hB (invRad hc0 1) (by
        rw [hrad]; exact (le_max_left _ _).trans_lt hcs) (by rw [hrad]; exact hc1') v
      have hwr : w (invRad hc0 1) τ = 1 := by rw [hrad]; exact hwc
      rw [map_mul, ← Valuation.comap_apply, v.2, hwr, one_mul]
      exact hvy

end Tau

end GaussTube

end SemistableReduction
