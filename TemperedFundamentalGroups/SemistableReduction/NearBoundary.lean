/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeUpwardMain

/-!
# Exact node data near the outer boundary (R4(ii))

Blueprint §9.10, L3, R4(ii) (BL Lemma 2.4: every disc close enough to the outer boundary is
exhausting), proved unconditionally by the germ technique. Let `w_s = w_{0,s}` be the Gauss
valuations of `C(x)` and `v` the extensions of `w_{0,1}` to `F'`.

* `isGermLE_of_red` (germ bridge): if `w_1(a) ≤ 1` and `ā` is regular at a zero of `x̄`, then
  `w_s(a) ≤ 1` for all `s < 1` close to `1`;
* `exists_valuation_le_one_near` (G2/G3): if `y` is integral at every `v` and its residues are
  regular at all zeros of `x̄`, then `w'(y) ≤ 1` for every `w' ∣ w_s`, `s < 1` close to `1`
  (the norms `N(y - t)` are germ-integral by `residue_norm_eq_prod`; Lagrange interpolation
  `coeff_mem_of_eval_mem` passes to the characteristic polynomial);
* `exists_tau_near`: such `y` becomes integral over the node chart `O_C[x, c/x]`,
  `|c|` close to `1`, after multiplication by some `τ` outside the node ideal;
* `exists_lift_red` (G1): residue families on the outer residue curves lift to `F'`;
* **`nonempty_nodeData_of_coord`** (reusable, any radius): exact node data `NodeData` from a
  coordinate `u` with `σ x = e uᵈ` (`σ, e ∉ P'`) and `σ_u u ∈ R'` reducing to a uniformizer;
* `exists_near_branch`, **`exists_near_nodeData`**: near the boundary, every point over the node
  has a single outer branch and exact node data;
* **`exists_near_isNodeODP`**: near the boundary every point over the node is an ODP (with R4(i),
  `isNodeODP_of_le`); **`belowGerm`**: the disc form, via `AffineTwist.IsExhausting`.
-/

open Polynomial WithZero
open scoped NNReal

namespace SemistableReduction

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

section Construct

/-- **Exact node data from a node coordinate** (reusable, any radius). Let `P'` be a prime of
`R' = Rint c F'` and `u ∈ F'` with `σ x = e uᵈ` (`σ, e ∈ R' ∖ P'`), `σ_u u ∈ R'` (`σ_u ∉ P'`)
reducing to a uniformizer at the branch `b₁`. Then `u, v = κ / u` with `κᵈ = c` are exact node
data at `P'`: `σ v ∈ R'` since `(σ v)ᵈ = σ^{d-1} e · (c / x)`. -/
theorem nonempty_nodeData_of_coord {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)
    {P' : Ideal (Rint c F')} [P'.IsPrime] {b₁ : OuterBranch C F'} {d : ℕ} (hd : 1 ≤ d) (u : F')
    (σ e : Rint c F') (hσ : σ ∉ P') (he : e ∉ P') (hx : (σ : F') * xF C F' = e * u ^ d)
    (uR σu : Rint c F') (hσu : σu ∉ P') (huR : (uR : F') = σu * u)
    (hval : b₁.2.1.valuation (redHom hc b₁.1 uR) = exp (-1)) : Nonempty (NodeData hc P' b₁) := by
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq c (by omega : 0 < d)
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hκ
    exact hc0 hκ.symm
  have hσ0 : (σ : F') ≠ 0 := fun h ↦ hσ (by
    rw [show σ = 0 from Subtype.ext h]
    exact P'.zero_mem)
  have hx0 : xF C F' ≠ 0 := by
    simpa [xF] using (RatFunc.X_ne_zero : (RatFunc.X : RatFunc C) ≠ 0)
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), mul_zero] at hx
    exact mul_ne_zero hσ0 hx0 hx
  set v : F' := algebraMap C F' κ / u
  have huv : u * v = algebraMap C F' κ := mul_div_cancel₀ _ hu0
  have hy : ((yR c : Rint c F') : F') = algebraMap C F' c / xF C F' := by
    change algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) c / RatFunc.X) = _
    rw [map_div₀, ← IsScalarTower.algebraMap_apply]
  set r : Rint c F' := σ ^ (d - 1) * e * yR c
  have hpow : ((σ : F') * v) ^ d = (r : F') := by
    refine mul_right_cancel₀ (pow_ne_zero d hu0) ?_
    have h1 : ((σ : F') * v) ^ d * u ^ d = (σ : F') ^ d * algebraMap C F' c := by
      rw [← mul_pow, mul_assoc, mul_comm v u, huv, mul_pow, ← map_pow, hκ]
    have h2 : (σ : F') ^ d = (σ : F') ^ (d - 1) * σ := (pow_sub_one_mul (by omega) _).symm
    rw [h1]
    simp only [r, Subalgebra.coe_mul, Subalgebra.coe_pow, hy]
    rw [mul_assoc, mul_assoc, mul_comm _ (u ^ d), ← mul_assoc (e : F'), ← hx, h2]
    field_simp
  have hint : IsIntegral (nodeRing c) ((σ : F') * v) :=
    IsIntegral.of_pow (by omega : 0 < d) (hpow ▸ r.2)
  exact ⟨⟨d, hd, u, v, κ, hκ0, huv, σ, e, hσ, he, hx, uR, σu, hσu, huR, ⟨_, hint⟩, σ, hσ, rfl,
    hval⟩⟩

end Construct

section Lift

local notation "κ₁" => ResidueField (Valuation.valuationSubring (gauss1 C))

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- **Lifting residue families (G1).** Every family of residues `z_v ∈ κ(v)`, one on each residue
curve of the outer vertex, is the reduction of a single `y ∈ F'` integral at all `v`: write `z_v`
in the basis of `κ(v)` formed by the residues of the orthonormal basis of G6.3 and lift the
coefficients. -/
theorem exists_lift_red (z : ∀ v : Ext C F', ResidueField v.1.valuationSubring) :
    ∃ y : F', (∀ v : Ext C F', v.1 y ≤ 1) ∧ ∀ v : Ext C F', red C y v = z v := by
  classical
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  obtain ⟨b, -, hsmall, hres⟩ := exists_orthonormal_basis' ramificationIdx_eq_one
    (sum_inertiaDeg_eq hp hp1 (F := F'))
  choose ℓ hℓli hℓ using hres
  set O := (gauss1 C).valuationSubring
  have hfin (v : Ext C F') : Module.Finite κ₁ (ResidueField v.1.valuationSubring) :=
    finite_residueField
  have hne (v : Ext C F') : Nonempty (Fin (inertiaDeg (gauss1 C) v.1)) :=
    ⟨⟨0, Module.finrank_pos⟩⟩
  let β (v : Ext C F') : Module.Basis (Fin (inertiaDeg (gauss1 C) v.1)) κ₁
      (ResidueField v.1.valuationSubring) :=
    basisOfLinearIndependentOfCardEqFinrank (hℓli v) (by rw [Fintype.card_fin]; rfl)
  have hβ (v : Ext C F') (l) : β v l = residue v.1.valuationSubring (ℓ v l) := by
    simp [β, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hb1 (i : OIndex C F') (v : Ext C F') : v.1 (b i) ≤ 1 := by
    by_cases hw : v = i.1
    · subst hw
      have : (b i : F') = (b i - ℓ i.1 i.2) + ℓ i.1 i.2 := by ring
      rw [this]
      exact (Valuation.map_add _ _ _).trans (max_le (hℓ i.1 i.2).le (ℓ i.1 i.2).2)
    · exact (hsmall i v hw).le
  have hredb (i : OIndex C F') (v : Ext C F') :
      red C (b i) v = if h : i.1 = v then h ▸ β i.1 i.2 else 0 := by
    split_ifs with h
    · subst h
      rw [hβ, ← sub_eq_zero, ← red_of_le (ℓ i.1 i.2).2, ← red_sub (hb1 i i.1) (ℓ i.1 i.2).2,
        red_eq_zero_iff (by
          have : (b i : F') - ℓ i.1 i.2 = b i + -(ℓ i.1 i.2 : F') := sub_eq_add_neg _ _
          rw [this]
          exact (Valuation.map_add _ _ _).trans (max_le (hb1 i i.1) (by
            rw [Valuation.map_neg]; exact (ℓ i.1 i.2).2)))]
      exact hℓ i.1 i.2
    · exact (red_eq_zero_iff (hb1 i v)).2 (hsmall i v (Ne.symm h))
  -- lifts of the coefficients
  choose o ho using fun i : OIndex C F' ↦ residue_surjective ((β i.1).repr (z i.1) i.2)
  set y : F' := ∑ i, algebraMap (RatFunc C) F' (o i : RatFunc C) * b i
  have hterm (i : OIndex C F') (v : Ext C F') :
      v.1 (algebraMap (RatFunc C) F' (o i : RatFunc C) * b i) ≤ 1 := by
    rw [map_mul, valuation_algebraMap]
    exact mul_le_one' (o i).2 (hb1 i v)
  refine ⟨y, fun v ↦ ?_, fun v ↦ ?_⟩
  · exact Valuation.map_sum_le _ fun i _ ↦ hterm i v
  · rw [red_sum _ _ fun i _ ↦ hterm i v]
    simp_rw [red_algebraMap_mul _ (o _).2 (hb1 _ v), hredb]
    rw [Fintype.sum_sigma, Finset.sum_eq_single v]
    · conv_rhs => rw [← (β v).sum_repr (z v)]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      simp only [dite_eq_ite, if_true]
      rw [Algebra.smul_def]
      congr 2
      exact ho ⟨v, l⟩
    · intro v' _ hw'
      refine Finset.sum_eq_zero fun l _ ↦ ?_
      simp [hw']
    · simp

end Lift

section Branch

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma red_inv_of_eq_one {v : Ext C F'} {f : F'} (hf : v.1 f = 1) :
    red C f⁻¹ v = (red C f v)⁻¹ := by
  have hf' : v.1 f⁻¹ ≤ 1 := by rw [map_inv₀, hf, inv_one]
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact zero_ne_one hf
  have h := red_mul hf.le hf'
  rw [mul_inv_cancel₀ hf0, red_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma valuation_eq_one_of_red_ne_zero {v : Ext C F'} {f : F'} (hf : v.1 f ≤ 1)
    (h : red C f v ≠ 0) : v.1 f = 1 :=
  le_antisymm hf (not_lt.1 fun hlt ↦ h ((red_eq_zero_iff hf).2 hlt))

lemma notMem_placeIdeal_iff {c : C} (hc : ‖c‖ < 1) (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (Y : Rint c F') :
    Y ∉ placeIdeal hc v hQ ↔ Q.valuation (red C (Y : F') v) = 1 := by
  rw [mem_placeIdeal_iff]
  have hm := red_mem_V hc v Y hQ
  refine ⟨fun h ↦ CurvePlace.valuation_eq_one_of_res_ne_zero Q hm h, fun h h0 ↦ ?_⟩
  have := Q.valuation_sub_res_lt_one hm
  rw [h0, map_zero, sub_zero, h] at this
  exact lt_irrefl 1 this

lemma notMem_placeIdeal_of_notMem_tubeIdeal {c : C} (hc : ‖c‖ < 1) (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) {τ : nodeRing c} (hτ : τ ∉ tubeIdeal c) :
    algebraMap (nodeRing c) (Rint c F') τ ∉ placeIdeal hc v hQ := by
  have hc1 : ‖c‖₊ < 1 := by exact_mod_cast hc
  obtain ⟨t, ht1, ht2⟩ := exists_between hc1
  set st : ℝ≥0ˣ := Units.mk0 t (ne_of_gt (lt_of_le_of_lt zero_le ht1))
  have hst : st ∈ segment c := ⟨ht1, ht2⟩
  intro hmem
  exact hτ ((mem_tubeIdeal_iff_placeHom hc hst v hQ τ).2 hmem)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
lemma coe_algebraMap_rint {c : C} (τ : nodeRing c) :
    ((algebraMap (nodeRing c) (Rint c F') τ : Rint c F') : F') =
      algebraMap (RatFunc C) F' (τ : RatFunc C) := rfl

lemma valuation_algebraMap_le_one {c : C} (hc : ‖c‖ < 1) (v : Ext C F') (τ : nodeRing c) :
    v.1 (algebraMap (RatFunc C) F' (τ : RatFunc C)) ≤ 1 := by
  rw [← coe_algebraMap_rint]
  exact valuation_le_one_R hc v _

lemma Qval_algebraMap_eq_one {c : C} (hc : ‖c‖ < 1) (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) {τ : nodeRing c} (hτ : τ ∉ tubeIdeal c) :
    Q.valuation (red C (algebraMap (RatFunc C) F' (τ : RatFunc C)) v) = 1 := by
  rw [← coe_algebraMap_rint]
  exact (notMem_placeIdeal_iff hc v hQ _).1 (notMem_placeIdeal_of_notMem_tubeIdeal hc v hQ hτ)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Exact node data near the boundary, one branch at a time (R4(ii)).** For a zero `Q` of `x̄`
on a residue curve `κ(v)` of the outer vertex there is `s₀ < 1` such that for all node charts
`O_C[x, c/x]` with `s₀ < |c| < 1`, the point `P'` of `R'` of the branch `(v, Q)` has `(v, Q)` as
its only outer branch and carries exact node data. Construction: `ū ∈ κ(v)` with `ord_Q ū = 1`
regular at the other zeros of `x̄`, `f̄` with `f̄(Q) ≠ 0` vanishing to high order at the other
zeros, lifted (G1) to `u, f ∈ F'` with `ū = 1`, `f̄ = 0` on the other residue curves; `u`, `f` and
`f x / uᵈ` (`d = ord_Q x̄`) become integral over the node chart after multiplication by elements
`τ ∉` node ideal (G2, `exists_tau_near`), and `σ x = e uᵈ` with `σ = τ₃ τ_f f`,
`e = τ_f τ₃ f x / uᵈ` (`nonempty_nodeData_of_coord`). -/
theorem exists_near_branch (v : Ext C F')
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) :
    ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ c : C, (hc0 : c ≠ 0) → s₀ < ‖c‖₊ → ∀ hc : ‖c‖ < 1,
      outerBranches hc (placeIdeal hc v hQ) = {⟨v, ⟨Q, hQ⟩⟩} ∧
        Nonempty (NodeData hc (placeIdeal hc v hQ) ⟨v, ⟨Q, hQ⟩⟩) := by
  classical
  set xb := red C (xF C F') v
  set d := ord xb Q
  have hd : 1 ≤ d := one_le_ord hQ
  have hxb0 : xb ≠ 0 := red_xF_ne_zero' v
  have hxQ : Q.valuation xb = exp (-(d : ℤ)) := valuation_x hQ
  have hxQ' (Q' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (hQ' : Q' ∈ zeros 𝓀 xb) :
      Q'.valuation xb < 1 := valuation_x_lt_one hQ'
  -- the residues `ū` and `f̄`
  obtain ⟨ub, hubQ, hubT⟩ := CurvePlace.exists_valuation_eq_and_le Q (zeros 𝓀 xb) (-1)
    (fun _ ↦ 1) (fun _ ↦ one_ne_zero)
  have hub0 : ub ≠ 0 := by
    rintro rfl
    rw [map_zero] at hubQ
    exact exp_ne_zero hubQ.symm
  have hubV (Q' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (hQ' : Q' ∈ zeros 𝓀 xb) :
      Q'.valuation ub ≤ 1 := by
    by_cases hQQ : Q' = Q
    · rw [hQQ, hubQ, ← exp_zero, exp_le_exp]
      omega
    · exact hubT Q' hQ' hQQ
  have hne (Q' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :
      Q'.valuation (ub ^ d * xb) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 (mul_ne_zero (pow_ne_zero _ hub0) hxb0)
  obtain ⟨fb, hfbQ, hfbT⟩ := CurvePlace.exists_valuation_eq_and_le Q (zeros 𝓀 xb) 0
    (fun Q' ↦ Q'.valuation (ub ^ d * xb)) hne
  have hfbT' (Q' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (hQ' : Q' ∈ zeros 𝓀 xb)
      (hQQ : Q' ≠ Q) : Q'.valuation fb < 1 := by
    refine (hfbT Q' hQ' hQQ).trans_lt ?_
    rw [map_mul, map_pow]
    exact mul_lt_one_of_nonneg_of_lt_one_right (pow_le_one₀ zero_le (hubV Q' hQ')) zero_le
      (hxQ' Q' hQ')
  -- the lifts `u` and `f`
  obtain ⟨u, hu1, hured⟩ := exists_lift_red hp hp1
    (Function.update (β := fun v ↦ ResidueField v.1.valuationSubring) (fun _ ↦ 1) v ub)
  obtain ⟨f, hf1, hfred⟩ := exists_lift_red hp hp1
    (Function.update (β := fun v ↦ ResidueField v.1.valuationSubring) (fun _ ↦ 0) v fb)
  have huv : red C u v = ub := by rw [hured, Function.update_self]
  have huv' (v' : Ext C F') (h : v' ≠ v) : red C u v' = 1 := by
    rw [hured, Function.update_of_ne h]
  have hfv : red C f v = fb := by rw [hfred, Function.update_self]
  have hfv' (v' : Ext C F') (h : v' ≠ v) : red C f v' = 0 := by
    rw [hfred, Function.update_of_ne h]
  have hu_eq (v' : Ext C F') : v'.1 u = 1 := by
    refine valuation_eq_one_of_red_ne_zero (hu1 v') ?_
    by_cases h : v' = v
    · subst h
      rw [huv]
      exact hub0
    · rw [huv' v' h]
      exact one_ne_zero
  have hu0 : u ≠ 0 := by
    rintro rfl
    have := hu_eq v
    rw [map_zero] at this
    exact zero_ne_one this
  set g := f * xF C F' * (u ^ d)⁻¹
  have hud (v' : Ext C F') : v'.1 (u ^ d) = 1 := by rw [map_pow, hu_eq, one_pow]
  have hg1 (v' : Ext C F') : v'.1 g ≤ 1 := by
    simp only [g, map_mul, map_inv₀, hud, valuation_xF, inv_one, mul_one]
    exact hf1 v'
  have hgred (v' : Ext C F') :
      red C g v' = red C f v' * red C (xF C F') v' * ((red C u v') ^ d)⁻¹ := by
    rw [red_mul (by rw [map_mul, valuation_xF, mul_one]; exact hf1 v')
      (by rw [map_inv₀, hud, inv_one]), red_mul (hf1 v') (valuation_xF v').le,
      red_inv_of_eq_one (hud v'), red_pow (hu_eq v').le]
  -- the hypotheses of `exists_tau_near`
  have hyQu : ∀ v' : Ext C F', ∀ Q' ∈ zeros 𝓀 (red C (xF C F') v'), red C u v' ∈ Q'.V := by
    intro v' Q' hQ'
    by_cases h : v' = v
    · subst h
      rw [huv]
      exact Q'.valuation_le_one_iff.1 (hubV Q' hQ')
    · rw [huv' v' h]
      exact one_mem _
  have hfbV (Q' : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) (hQ' : Q' ∈ zeros 𝓀 xb) :
      Q'.valuation fb ≤ 1 := by
    by_cases hQQ : Q' = Q
    · rw [hQQ, hfbQ, exp_zero]
    · exact (hfbT' Q' hQ' hQQ).le
  have hyQf : ∀ v' : Ext C F', ∀ Q' ∈ zeros 𝓀 (red C (xF C F') v'), red C f v' ∈ Q'.V := by
    intro v' Q' hQ'
    by_cases h : v' = v
    · subst h
      rw [hfv]
      exact Q'.valuation_le_one_iff.1 (hfbV Q' hQ')
    · rw [hfv' v' h]
      exact zero_mem _
  have hgQ : Q.valuation (fb * xb * (ub ^ d)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv₀, map_pow, hfbQ, hxQ, hubQ, exp_zero, one_mul, ← exp_nsmul,
      ← exp_neg]
    simp
  have hyQg : ∀ v' : Ext C F', ∀ Q' ∈ zeros 𝓀 (red C (xF C F') v'), red C g v' ∈ Q'.V := by
    intro v' Q' hQ'
    rw [hgred]
    by_cases h : v' = v
    · subst h
      rw [hfv, huv]
      refine Q'.valuation_le_one_iff.1 ?_
      by_cases hQQ : Q' = Q
      · rw [hQQ, hgQ]
      · have hu0' : Q'.valuation ub ^ d ≠ 0 :=
          pow_ne_zero _ ((Valuation.ne_zero_iff _).2 hub0)
        have h1 := hfbT Q' hQ' hQQ
        rw [map_mul, map_pow] at h1
        rw [map_mul, map_mul, map_inv₀, map_pow]
        calc Q'.valuation fb * Q'.valuation xb * (Q'.valuation ub ^ d)⁻¹ ≤
              Q'.valuation ub ^ d * Q'.valuation xb * Q'.valuation xb *
                (Q'.valuation ub ^ d)⁻¹ := by gcongr
          _ = Q'.valuation xb * Q'.valuation xb := by field_simp
          _ ≤ 1 := mul_le_one' (hxQ' Q' hQ').le (hxQ' Q' hQ').le
    · rw [hfv' v' h, zero_mul, zero_mul]
      exact zero_mem _
  obtain ⟨s₁, hs₁, H₁⟩ := exists_tau_near hp hp1 hu1 hyQu v hQ
  obtain ⟨s₂, hs₂, H₂⟩ := exists_tau_near hp hp1 hf1 hyQf v hQ
  obtain ⟨s₃, hs₃, H₃⟩ := exists_tau_near hp hp1 hg1 hyQg v hQ
  refine ⟨max s₁ (max s₂ s₃), max_lt hs₁ (max_lt hs₂ hs₃), fun c hc0 hcs hc ↦ ?_⟩
  obtain ⟨τu, hτu, hintu⟩ := H₁ c hc0 ((le_max_left _ _).trans_lt hcs) hc
  obtain ⟨τf, hτf, hintf⟩ := H₂ c hc0
    (((le_max_left _ _).trans (le_max_right _ _)).trans_lt hcs) hc
  obtain ⟨τg, hτg, hintg⟩ := H₃ c hc0
    (((le_max_right _ _).trans (le_max_right _ _)).trans_lt hcs) hc
  let P' := placeIdeal hc v hQ
  haveI : P'.IsPrime := (placeIdeal_isMaximal hc v hQ).isPrime
  let Tu := algebraMap (nodeRing c) (Rint c F') τu
  let Tf := algebraMap (nodeRing c) (Rint c F') τf
  let Tg := algebraMap (nodeRing c) (Rint c F') τg
  have hval1 (τ : nodeRing c) (hτ : τ ∉ tubeIdeal c) :
      Q.valuation (red C (algebraMap (RatFunc C) F' (τ : RatFunc C)) v) = 1 :=
    Qval_algebraMap_eq_one hc v hQ hτ
  have hle1 (τ : nodeRing c) : v.1 (algebraMap (RatFunc C) F' (τ : RatFunc C)) ≤ 1 :=
    valuation_algebraMap_le_one hc v τ
  let U : Rint c F' := ⟨_, hintu⟩
  let Fm : Rint c F' := ⟨_, hintf⟩
  let G : Rint c F' := ⟨_, hintg⟩
  have hFm : Q.valuation (red C (Fm : F') v) = 1 := by
    change Q.valuation (red C (algebraMap (RatFunc C) F' (τf : RatFunc C) * f) v) = 1
    rw [red_mul (hle1 τf) (hf1 v), map_mul, hval1 τf hτf, hfv, hfbQ, exp_zero, one_mul]
  have hG : Q.valuation (red C (G : F') v) = 1 := by
    change Q.valuation (red C (algebraMap (RatFunc C) F' (τg : RatFunc C) * g) v) = 1
    rw [red_mul (hle1 τg) (hg1 v), map_mul, hval1 τg hτg, hgred, hfv, huv, one_mul]
    exact hgQ
  have hFmP : Fm ∉ P' := (notMem_placeIdeal_iff hc v hQ _).2 hFm
  have hσ : Tg * Fm ∉ P' := by
    rw [notMem_placeIdeal_iff, Subalgebra.coe_mul,
      red_mul (valuation_le_one_R hc v _) (valuation_le_one_R hc v _), map_mul, hFm, mul_one]
    exact hval1 τg hτg
  have he : Tf * G ∉ P' := by
    rw [notMem_placeIdeal_iff, Subalgebra.coe_mul,
      red_mul (valuation_le_one_R hc v _) (valuation_le_one_R hc v _), map_mul, hG, mul_one]
    exact hval1 τf hτf
  have hx : ((Tg * Fm : Rint c F') : F') * xF C F' = ((Tf * G : Rint c F') : F') * u ^ d := by
    change (algebraMap (RatFunc C) F' (τg : RatFunc C) *
      (algebraMap (RatFunc C) F' (τf : RatFunc C) * f)) * xF C F' =
      (algebraMap (RatFunc C) F' (τf : RatFunc C) *
        (algebraMap (RatFunc C) F' (τg : RatFunc C) * (f * xF C F' * (u ^ d)⁻¹))) * u ^ d
    field_simp
  have hval : Q.valuation (redHom hc v U) = exp (-1) := by
    rw [redHom_apply]
    change Q.valuation (red C (algebraMap (RatFunc C) F' (τu : RatFunc C) * u) v) = exp (-1)
    rw [red_mul (hle1 τu) (hu1 v), map_mul, hval1 τu hτu, huv, hubQ, one_mul]
  have hTu : Tu ∉ P' := notMem_placeIdeal_of_notMem_tubeIdeal hc v hQ hτu
  refine ⟨Set.ext fun b' ↦ ⟨fun hb' ↦ ?_, fun hb' ↦ ?_⟩,
    nonempty_nodeData_of_coord hc hc0 hd u (Tg * Fm) (Tf * G) hσ he hx U Tu hTu rfl hval⟩
  · obtain ⟨v', Q', hQ'⟩ := b'
    change placeIdeal hc v' hQ' = P' at hb'
    have hFm' : Fm ∉ placeIdeal hc v' hQ' := hb' ▸ hFmP
    rw [notMem_placeIdeal_iff] at hFm'
    change Q'.valuation (red C (algebraMap (RatFunc C) F' (τf : RatFunc C) * f) v') = 1 at hFm'
    rw [red_mul (valuation_algebraMap_le_one hc v' τf) (hf1 v'), map_mul] at hFm'
    have hτle : Q'.valuation (red C (algebraMap (RatFunc C) F' (τf : RatFunc C)) v') ≤ 1 := by
      have := red_mem_V hc v' Tf hQ'
      rw [coe_algebraMap_rint] at this
      exact Q'.valuation_le_one_iff.2 this
    by_cases hv : v' = v
    · subst hv
      by_cases hQQ : Q' = Q
      · subst hQQ
        rfl
      · exfalso
        rw [hfv] at hFm'
        have := mul_lt_one_of_nonneg_of_lt_one_right hτle zero_le (hfbT' Q' hQ' hQQ)
        rw [hFm'] at this
        exact lt_irrefl 1 this
    · exfalso
      rw [hfv' v' hv, map_zero, mul_zero] at hFm'
      exact zero_ne_one hFm'
  · rw [Set.mem_singleton_iff] at hb'
    subst hb'
    rfl

variable [Algebra.IsSeparable (RatFunc C) F']

include hp hp1 in
/-- **R4(ii): exact node data at all points near the outer boundary.** There is `s₀ < 1` such
that for every node chart `O_C[x, c/x]` with `s₀ < |c| < 1`, every point `P'` of `R' = Rint c F'`
over the node has a single outer branch `b₁` and exact node data. No descent is involved: the
data are constructed directly (`exists_near_branch`), for the finitely many branches. -/
theorem exists_near_nodeData :
    ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ c : C, (hc0 : c ≠ 0) → s₀ < ‖c‖₊ → ∀ hc : ‖c‖ < 1,
      ∀ P' : Ideal (Rint c F'), P'.IsMaximal →
        P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c →
          ∃ b₁ : OuterBranch C F', outerBranches hc P' = {b₁} ∧ Nonempty (NodeData hc P' b₁) := by
  classical
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  choose S hS hB using fun b : OuterBranch C F' ↦ exists_near_branch hp hp1 b.1 b.2.2
  refine ⟨Finset.univ.sup S, (Finset.sup_lt_iff zero_lt_one).2 fun b _ ↦ hS b,
    fun c hc0 hcs hc P' hP' hP ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_outerBranch hp hp1 hc hc0 P' hP
  obtain ⟨h₁, hN⟩ := hB b c hc0 ((Finset.le_sup (Finset.mem_univ b)).trans_lt hcs) hc
  rw [hb] at h₁ hN
  exact ⟨b, h₁, hN⟩

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- A point of `R''` over the node restricts to a point of `R'` over the node (`|c'| < |c''|`). -/
lemma comap_rintMap_comap {c' c'' : C} (hc'' : ‖c''‖ < 1) (hc0'' : c'' ≠ 0)
    (hlt : ‖c'‖ < ‖c''‖) (P'' : Ideal (Rint c'' F'))
    (hP'' : P''.comap (algebraMap (nodeRing c'') (Rint c'' F')) = tubeIdeal c'') :
    (P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0''))).comap
      (algebraMap (nodeRing c') (Rint c' F')) = tubeIdeal c' := by
  have hc1 : ‖c''‖₊ < 1 := by exact_mod_cast hc''
  obtain ⟨t, ht1, ht2⟩ := exists_between hc1
  set st : ℝ≥0ˣ := Units.mk0 t (ne_of_gt (lt_of_le_of_lt zero_le ht1))
  have hst'' : st ∈ segment c'' := ⟨ht1, ht2⟩
  have hst' : st ∈ segment c' :=
    ⟨lt_trans (show ‖c'‖₊ < ‖c''‖₊ by exact_mod_cast hlt) ht1, ht2⟩
  ext a
  have heq : rintMap (F' := F') (nodeRing_le hlt.le hc0'')
      (algebraMap (nodeRing c') (Rint c' F') a) =
      algebraMap (nodeRing c'') (Rint c'' F') ⟨a, nodeRing_le hlt.le hc0'' a.2⟩ :=
    Subtype.ext (by rw [coe_rintMap, coe_algebraMap_rint, coe_algebraMap_rint])
  rw [Ideal.mem_comap, Ideal.mem_comap, heq, ← Ideal.mem_comap, hP'', mem_tubeIdeal_iff _ hst'',
    mem_tubeIdeal_iff _ hst']

include hp hp1 in
/-- **R4(ii): every annulus close enough to the outer boundary is exhausting** (BL Lemma 2.4).
There is `s₀ < 1` such that for every `c''` with `s₀ < |c''| < 1`, every point of
`R'' = Rint c'' F'` over the node is an ordinary double point over `C`: it lies over a point of
`R' = Rint c' F'` (`c' = c''²`, still near the boundary) with exact node data
(`exists_near_nodeData`), and R4(i) (`isNodeODP_of_le`) applies. -/
theorem exists_near_isNodeODP :
    ∃ s₀ : ℝ≥0, s₀ < 1 ∧ ∀ c'' : C, (hc0'' : c'' ≠ 0) → s₀ < ‖c''‖₊ → ∀ hc'' : ‖c''‖ < 1,
      ∀ P'' : Ideal (Rint c'' F'), P''.IsMaximal →
        P''.comap (algebraMap (nodeRing c'') (Rint c'' F')) = tubeIdeal c'' →
          IsNodeODP hc'' hc0'' P'' := by
  obtain ⟨s₁, hs₁, H⟩ := exists_near_nodeData (F' := F') hp hp1
  refine ⟨NNReal.sqrt s₁, by rw [← NNReal.sqrt_one, NNReal.sqrt_lt_sqrt]; exact hs₁,
    fun c'' hc0'' hcs hc'' P'' hP''m hP'' ↦ ?_⟩
  set c' := c'' ^ 2
  have hc0' : c' ≠ 0 := pow_ne_zero _ hc0''
  have hn : 0 < ‖c''‖ := norm_pos_iff.2 hc0''
  have hlt : ‖c'‖ < ‖c''‖ := by
    rw [norm_pow]
    nlinarith
  have hc' : ‖c'‖ < 1 := hlt.trans hc''
  have hcs' : s₁ < ‖c'‖₊ := by
    rw [nnnorm_pow]
    by_contra h
    exact absurd hcs (not_lt.2 (NNReal.le_sqrt_iff_sq_le.2 (not_lt.1 h)))
  set P' := P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0''))
  have hcomap := comap_rintMap_comap hc'' hc0'' hlt P'' hP''
  haveI : P'.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := nodeRing c') _
      (by rw [hcomap]; exact tubeIdeal_isMaximal hc' hc0')
  obtain ⟨b₁, h₁, ⟨N⟩⟩ := H c' hc0' hcs' hc' P' inferInstance hcomap
  exact isNodeODP_of_le hp hp1 hc' hc'' hc0' hc0'' hlt P'' hP'' rfl h₁ N

end Branch

omit [IsUltrametricDist C] in
/-- Absolute values of `C` come arbitrarily close to `1` from below. -/
lemma exists_nnnorm_between {s₀ : ℝ≥0} (hs₀ : s₀ < 1) : ∃ e : C, s₀ < ‖e‖₊ ∧ ‖e‖₊ < 1 := by
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one C
  have hπ0' : 0 < ‖π‖₊ := by exact_mod_cast hπ0
  have hπ1' : ‖π‖₊ < 1 := by exact_mod_cast hπ1
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hπ0' hs₀
  have hN0 : N ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hN
    exact absurd (hN.trans hπ1') (lt_irrefl 1)
  obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq π (Nat.pos_of_ne_zero hN0)
  have hen : ‖e‖₊ ^ N = ‖π‖₊ := by rw [← nnnorm_pow, he]
  refine ⟨e, lt_of_pow_lt_pow_left₀ N zero_le (hen ▸ hN), not_le.1 fun h ↦ ?_⟩
  have := one_le_pow₀ (n := N) h
  rw [hen] at this
  exact absurd (this.trans_lt hπ1') (lt_irrefl 1)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **R4(ii), disc form** (`BelowGerm`, BL Lemma 2.4): for every residue class
`U = {|x - a| < |c|}` there is `e`, `0 < |e| < 1`, such that every closed disc
`D = {|x - a| ≤ |c c'|}` with `|e| ≤ |c'| < 1` is exhausting. Unconditional: no descent and no
interim `NodeData` hypothesis (the exact node data are constructed near the boundary,
`exists_near_nodeData`). -/
theorem belowGerm (a c : C) (hc : c ≠ 0) :
    ∃ e : C, e ≠ 0 ∧ ‖e‖ < 1 ∧ ∀ (c' : C) (hc' : ‖c'‖ < 1) (hc0' : c' ≠ 0), ‖e‖ ≤ ‖c'‖ →
      AffineTwist.IsExhausting a hc hc' hc0' F' := by
  haveI : Algebra.IsSeparable (RatFunc C) (AffineTwist.Aff a c hc F') :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨s₀, hs₀, H⟩ := exists_near_isNodeODP (F' := AffineTwist.Aff a c hc F') hp hp1
  obtain ⟨e, hse, he1⟩ := exists_nnnorm_between (C := C) hs₀
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hse
    exact absurd hse (not_lt.2 zero_le)
  refine ⟨e, he0, by exact_mod_cast he1, fun c' hc' hc0' hle P' hP' hP ↦ ?_⟩
  have hle' : ‖e‖₊ ≤ ‖c'‖₊ := by exact_mod_cast hle
  exact H c' hc0' (hse.trans_le hle') hc' P' hP' hP

end GaussTube

end SemistableReduction
