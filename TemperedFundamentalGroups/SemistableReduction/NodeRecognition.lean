/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SmoothPoint
import TemperedFundamentalGroups.SemistableReduction.NodeDouble

/-!
# Recognizing ordinary double points over the node from parameters of the branches

Blueprint §9.10, L3 (R2/R3 over `C`, the two-branch analogue of S7(c)). Let `ρ₁, ρ₂ : R → K₁, K₂`
be the reductions of a ring to the two components through a point, `Q₁, Q₂` the branches.

* `CurvePlace.res_aeval`, `res_eq_coeff_zero`: the residue of a polynomial in a uniformizer is its
  constant coefficient;
* `exists_jet₂`: if the constants lift to `R` compatibly and `u', v' ∈ R` with `ρ₂ u' = 0`,
  `ρ₁ v' = 0` reduce to uniformizers at `Q₁`, `Q₂`, every element `(a, b)` of the fibre product
  `{a(Q₁) = b(Q₂)}` is approximated by `(ρ₁ y, ρ₂ y)` modulo every power of the maximal ideals;
* **`GaussTube.exists_fp_of_params`** (the node chart `Rint c F'`): hence, at a point `P'` over the
  node with an outer branch `(v₁, Q₁)` and an inner branch `(w₂, Q₂)` (each the only zero of the
  coordinate on its component with point `P'`) and such parameters `u', v' ∈ R'`, the local ring
  reaches the fibre product exactly (`NodeDouble.exists_fp`), and every `z ∈ P'` is
  `s z ≡ a u' + b v'` on both components (`exists_sub_mem_ker_of_params`): `P'` is an ordinary
  double point over `C` ([KA, Lemma 1.30], valuative form).
-/

open Polynomial WithZero

namespace SemistableReduction

namespace CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ] (Q : CurvePlace k κ)

/-- The residue of a polynomial with constant coefficients in an element of the maximal ideal is
its constant coefficient. -/
lemma res_aeval {π : κ} (hπ : Q.valuation π < 1) (p : k[X]) : Q.res (aeval π p) = p.coeff 0 := by
  have hπV : π ∈ Q.V := Q.valuation_le_one_iff.1 hπ.le
  have hV (q : k[X]) : aeval π q ∈ Q.V := by
    induction q using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | monomial n c =>
      rw [aeval_monomial]
      exact mul_mem (Q.algebraMap_mem c) (pow_mem hπV n)
  conv_lhs => rw [← X_mul_divX_add p]
  rw [map_add, map_mul, aeval_X, aeval_C, Q.res_add (mul_mem hπV (hV _)) (Q.algebraMap_mem _),
    Q.res_mul hπV (hV _), Q.res_eq_zero_of_lt_one hπ, zero_mul, zero_add, Q.res_algebraMap]

/-- If `a` is approximated by a polynomial in a uniformizer, its residue is the constant
coefficient. -/
lemma res_eq_coeff_zero {π : κ} (hπ : Q.valuation π < 1) {a : κ} (ha : a ∈ Q.V) {p : k[X]}
    (hp : Q.valuation (a - aeval π p) < 1) : Q.res a = p.coeff 0 := by
  have hq : aeval π p ∈ Q.V := by
    have : aeval π p = a - (a - aeval π p) := by ring
    rw [this]
    exact sub_mem ha (Q.valuation_le_one_iff.1 hp.le)
  rw [show a = (a - aeval π p) + aeval π p by ring, Q.res_add (Q.valuation_le_one_iff.1 hp.le) hq,
    Q.res_eq_zero_of_lt_one hp, zero_add, Q.res_aeval hπ]

end CurvePlace

namespace NodeRecognition

variable {R : Type*} [CommRing R] {K₁ K₂ : Type*} [Field K₁] [Field K₂]
  (ρ₁ : R →+* K₁) (ρ₂ : R →+* K₂)
  {k : Type*} [Field k] [Algebra k K₁] [Algebra k K₂] [IsAlgClosed k]
  [IsCurveFunctionField k K₁] [IsCurveFunctionField k K₂]
  (Q₁ : CurvePlace k K₁) (Q₂ : CurvePlace k K₂)

/-- **Jets of the fibre product from parameters of the two branches.** -/
theorem exists_jet₂
    (hk : ∀ c : k, ∃ r : R, ρ₁ r = algebraMap k K₁ c ∧ ρ₂ r = algebraMap k K₂ c)
    {u' v' : R} (hu₁ : Q₁.valuation (ρ₁ u') = exp (-1)) (hu₂ : ρ₂ u' = 0)
    (hv₁ : ρ₁ v' = 0) (hv₂ : Q₂.valuation (ρ₂ v') = exp (-1))
    {a : K₁} (ha : a ∈ Q₁.V) {b : K₂} (hb : b ∈ Q₂.V) (hab : Q₁.res a = Q₂.res b) (M : ℕ) :
    ∃ y : R, Q₁.valuation (ρ₁ y - a) ≤ exp (-(M : ℤ)) ∧
      Q₂.valuation (ρ₂ y - b) ≤ exp (-(M : ℤ)) := by
  choose lift hlift₁ hlift₂ using hk
  obtain ⟨p, hp⟩ := SmoothPoint.exists_jet Q₁ hu₁ ha (M + 1)
  obtain ⟨q, hq⟩ := SmoothPoint.exists_jet Q₂ hv₂ hb (M + 1)
  have hlt (n : ℕ) : exp (-((n + 1 : ℕ) : ℤ)) < (1 : ℤᵐ⁰) := by
    rw [← exp_zero, exp_lt_exp]; omega
  have hle (n : ℕ) : exp (-((n + 1 : ℕ) : ℤ)) ≤ exp (-(n : ℤ)) := by
    rw [exp_le_exp]; omega
  have hπ₁ : Q₁.valuation (ρ₁ u') < 1 := by rw [hu₁, ← exp_zero, exp_lt_exp]; omega
  have hπ₂ : Q₂.valuation (ρ₂ v') < 1 := by rw [hv₂, ← exp_zero, exp_lt_exp]; omega
  have h0 : p.coeff 0 = q.coeff 0 := by
    rw [← Q₁.res_eq_coeff_zero hπ₁ ha (hp.trans_lt (hlt M)),
      ← Q₂.res_eq_coeff_zero hπ₂ hb (hq.trans_lt (hlt M)), hab]
  -- `y = p(u') + (q - q(0))(v')` with lifted coefficients
  set y : R := (p.sum fun i c ↦ lift c * u' ^ i) + (q.sum fun j c ↦ lift c * v' ^ j) -
    lift (q.coeff 0)
  have hsum₁ (r : R) (π : K₁) (hr : ρ₁ r = π) (p : k[X]) :
      ρ₁ (p.sum fun i c ↦ lift c * r ^ i) = aeval π p := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, hlift₁, hr]
  have hsum₂ (r : R) (π : K₂) (hr : ρ₂ r = π) (p : k[X]) :
      ρ₂ (p.sum fun i c ↦ lift c * r ^ i) = aeval π p := by
    rw [aeval_def, eval₂_eq_sum, Polynomial.sum_def, Polynomial.sum_def, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, map_pow, hlift₂, hr]
  have hzero₁ : ρ₁ (q.sum fun j c ↦ lift c * v' ^ j) = algebraMap k K₁ (q.coeff 0) := by
    rw [hsum₁ v' 0 hv₁, aeval_def, eval₂_at_zero]
  have hzero₂ : ρ₂ (p.sum fun i c ↦ lift c * u' ^ i) = algebraMap k K₂ (p.coeff 0) := by
    rw [hsum₂ u' 0 hu₂, aeval_def, eval₂_at_zero]
  refine ⟨y, ?_, ?_⟩
  · have : ρ₁ y - a = -(a - aeval (ρ₁ u') p) := by
      simp only [y, map_sub, map_add, hsum₁ u' _ rfl, hzero₁, hlift₁]
      ring
    rw [this, Valuation.map_neg]
    exact hp.trans (hle M)
  · have : ρ₂ y - b = -(b - aeval (ρ₂ v') q) := by
      simp only [y, map_sub, map_add, hsum₂ v' _ rfl, hzero₂, hlift₂, h0]
      ring
    rw [this, Valuation.map_neg]
    exact hq.trans (hle M)

end NodeRecognition

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma rintEquiv_constR (b : HenselComplete.integers C) :
    rintEquiv hc0 (constR c b : Rint c F') = constR c b := by
  apply Subtype.ext
  change toInv hc0 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) b)) =
    algebraMap (RatFunc C) (Inv c hc0 F') (algebraMap C (RatFunc C) b)
  rw [algebraMap_inv_apply, inv_apply, AlgHom.commutes]

lemma redHomInv_constR (w₂ : Ext C (Inv c hc0 F')) (b : HenselComplete.integers C) :
    redHomInv hc hc0 w₂ (constR c b) = algebraMap 𝓀 _ (IsLocalRing.residue _ b) := by
  change redHom hc w₂ (rintEquiv hc0 (constR c b)) = _
  rw [rintEquiv_constR, redHom_constR]

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Ordinary double points over `C` from parameters of the branches** ([KA, Lemma 1.30],
valuative form). At a point `P'` of the normalized node with an outer branch `(v₁, Q₁)` and an
inner branch `(w₂, Q₂)`, each the only zero of the coordinate on its component with point `P'`,
and `u', v' ∈ R'` with `ρ₂ u' = 0`, `ρ₁ v' = 0` reducing to uniformizers at `Q₁`, `Q₂`, the local
ring reaches the fibre product `{(a, b) ∈ O_{Q₁} × O_{Q₂} | a(Q₁) = b(Q₂)}` exactly. -/
theorem exists_fp_of_params (v₁ : Ext C F')
    {Q₁ : CurvePlace 𝓀 (IsLocalRing.ResidueField v₁.1.valuationSubring)}
    (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C F') v₁)) (w₂ : Ext C (Inv c hc0 F'))
    {Q₂ : CurvePlace 𝓀 (IsLocalRing.ResidueField w₂.1.valuationSubring)}
    (hQ₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂))
    (hP : placeIdeal hc w₂ hQ₂ = (placeIdeal hc v₁ hQ₁).comap (rintEquiv hc0).symm.toRingHom)
    (hoth₁ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v₁)), R ≠ Q₁ →
      placeIdeal hc v₁ hR ≠ placeIdeal hc v₁ hQ₁)
    (hoth₂ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂)), R ≠ Q₂ →
      placeIdeal hc w₂ hR ≠ placeIdeal hc w₂ hQ₂)
    {u' v' : Rint c F'} (hu₁ : Q₁.valuation (redHom hc v₁ u') = exp (-1))
    (hu₂ : redHomInv hc hc0 w₂ u' = 0) (hv₁ : redHom hc v₁ v' = 0)
    (hv₂ : Q₂.valuation (redHomInv hc hc0 w₂ v') = exp (-1))
    {a : IsLocalRing.ResidueField v₁.1.valuationSubring} (ha : a ∈ Q₁.V)
    {b : IsLocalRing.ResidueField w₂.1.valuationSubring} (hb : b ∈ Q₂.V)
    (hab : Q₁.res a = Q₂.res b) :
    ∃ y s : Rint c F', s ∉ placeIdeal hc v₁ hQ₁ ∧ redHom hc v₁ y = a * redHom hc v₁ s ∧
      redHomInv hc hc0 w₂ y = b * redHomInv hc hc0 w₂ s := by
  haveI : (placeIdeal hc v₁ hQ₁).IsMaximal := placeIdeal_isMaximal hc v₁ hQ₁
  refine exists_fp hc hc0 hp hp1 v₁ hQ₁ w₂ hQ₂ hP hoth₁ hoth₂
    (fun a ha b hb hab M ↦ ?_) ha hb hab
  obtain ⟨y, hy₁, hy₂⟩ := NodeRecognition.exists_jet₂ (redHom hc v₁) (redHomInv hc hc0 w₂) Q₁ Q₂
    (fun c' ↦ by
      obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective c'
      exact ⟨constR c b', redHom_constR hc v₁ b', redHomInv_constR hc hc0 w₂ b'⟩)
    hu₁ hu₂ hv₁ hv₂ ha hb hab M
  refine ⟨y, 1, Ideal.IsMaximal.ne_top inferInstance ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one),
    ?_, ?_⟩
  · rwa [map_one, div_one]
  · rwa [map_one, div_one]

include hp hp1 in
/-- **The ordinary double point over `C`**: under the hypotheses of `exists_fp_of_params`, every
`z ∈ P'` satisfies `ρⱼ (s z - a u' - b v') = 0` (`j = 1, 2`) for some `a, b ∈ R'`, `s ∉ P'`. -/
theorem exists_sub_mem_ker_of_params (v₁ : Ext C F')
    {Q₁ : CurvePlace 𝓀 (IsLocalRing.ResidueField v₁.1.valuationSubring)}
    (hQ₁ : Q₁ ∈ zeros 𝓀 (red C (xF C F') v₁)) (w₂ : Ext C (Inv c hc0 F'))
    {Q₂ : CurvePlace 𝓀 (IsLocalRing.ResidueField w₂.1.valuationSubring)}
    (hQ₂ : Q₂ ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂))
    (hP : placeIdeal hc w₂ hQ₂ = (placeIdeal hc v₁ hQ₁).comap (rintEquiv hc0).symm.toRingHom)
    (hoth₁ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v₁)), R ≠ Q₁ →
      placeIdeal hc v₁ hR ≠ placeIdeal hc v₁ hQ₁)
    (hoth₂ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂)), R ≠ Q₂ →
      placeIdeal hc w₂ hR ≠ placeIdeal hc w₂ hQ₂)
    {u' v' : Rint c F'} (hu₁ : Q₁.valuation (redHom hc v₁ u') = exp (-1))
    (hu₂ : redHomInv hc hc0 w₂ u' = 0) (hv₁ : redHom hc v₁ v' = 0)
    (hv₂ : Q₂.valuation (redHomInv hc hc0 w₂ v') = exp (-1))
    {z : Rint c F'} (hz : z ∈ placeIdeal hc v₁ hQ₁) :
    ∃ a b s : Rint c F', s ∉ placeIdeal hc v₁ hQ₁ ∧
      redHom hc v₁ (s * z - a * u' - b * v') = 0 ∧
      redHomInv hc hc0 w₂ (s * z - a * u' - b * v') = 0 := by
  haveI : (placeIdeal hc v₁ hQ₁).IsMaximal := placeIdeal_isMaximal hc v₁ hQ₁
  refine exists_sub_mem_ker hc hc0 hp hp1 v₁ hQ₁ w₂ hQ₂ hP hoth₁ hoth₂
    (fun a ha b hb hab M ↦ ?_) hu₁ hu₂ hv₁ hv₂ hz
  obtain ⟨y, hy₁, hy₂⟩ := NodeRecognition.exists_jet₂ (redHom hc v₁) (redHomInv hc hc0 w₂) Q₁ Q₂
    (fun c' ↦ by
      obtain ⟨b', rfl⟩ := IsLocalRing.residue_surjective c'
      exact ⟨constR c b', redHom_constR hc v₁ b', redHomInv_constR hc hc0 w₂ b'⟩)
    hu₁ hu₂ hv₁ hv₂ ha hb hab M
  refine ⟨y, 1, Ideal.IsMaximal.ne_top inferInstance ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one),
    ?_, ?_⟩
  · rwa [map_one, div_one]
  · rwa [map_one, div_one]

end GaussTube

end SemistableReduction
