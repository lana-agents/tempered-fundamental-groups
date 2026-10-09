/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourTransfer

/-!
# Components through a point of the vertex chart

Blueprint §9.12, leaf T4, part (G). For a maximal ideal `P'` of `R' = DRint 0 1 G` over the
residue point, a component `v` (an extension of `w_{0,1}`) *passes through* `P'` if some zero of
`x̄` on `κ(v)` has the point `P'` (`Through`).

* `exists_away'`: some `z ∈ R' ∖ P'` has value `< 1` at every component not through `P'`;
* `exists_lift'`: an element `f` integral over `C[x]` of value `≤ 1` at the components through
  `P'` becomes an element of `R'` after multiplication by a power of `z`;
* `valuation_eq_one_of_notMem`: an element of `R' ∖ P'` has value `1` at every component
  through `P'`, and a residue `≠ 0` at the branch;
* **`exists_res_eq`** (the residue at `P'`): for such `f` and a valuation `ξ` with centre `P'`,
  there is `c ∈ O_C` with `ξ(f - c) < 1` and `f̄_v(Q) = c̄` at every branch `(v, Q)` through `P'`.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open FundamentalInequality GaussStability GaussFibre GaussTube DiscCount SmoothVertex PlaceNorm
  CurvePlace

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

attribute [local instance] GaussFibre.isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

/-- The component `v` passes through `P'`: some zero of `x̄` on `κ(v)` has the point `P'`. -/
def Through (P' : Ideal (DRint (0 : C) 1 G)) (v : Ext C G) : Prop :=
  ∃ (Q : CurvePlace (ResidueField (HenselComplete.integers C))
      (ResidueField v.1.valuationSubring))
    (hQ : Q ∈ zeros (ResidueField (HenselComplete.integers C)) (red C (xF C G) v)),
    placeIdealD v hQ = P'

/-- **Away from the other components.** -/
theorem exists_away' (P' : Ideal (DRint (0 : C) 1 G)) [hP : P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) =
      discIdeal (0 : C) 1) [Finite (Ext C G)] :
    ∃ z : DRint (0 : C) 1 G, z ∉ P' ∧ ∀ v : Ext C G, ¬ Through P' v → v.1 (z : G) < 1 := by
  classical
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  have hcomp : ∀ v : Ext C G, ¬ Through P' v →
      ∃ z : DRint (0 : C) 1 G, redD v z = 0 ∧ z ∉ P' := by
    intro v hv
    by_contra! H
    obtain ⟨Q, hQ, hQP⟩ := exists_branch_of_ker_le v P' hP' fun z hz ↦ H z hz
    exact hv ⟨Q, hQ, hQP⟩
  choose! zz hzz using hcomp
  set S := Finset.univ.filter fun v : Ext C G ↦ ¬ Through P' v
  refine ⟨S.prod zz, fun hz ↦ ?_, fun v hv ↦ ?_⟩
  · obtain ⟨v, hv, hzv⟩ := (Ideal.IsPrime.prod_mem_iff (hp := hP.isPrime)).1 hz
    exact (hzz v (Finset.mem_filter.1 hv).2).2 hzv
  · have h0 : redD v (S.prod zz) = 0 := by
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_filter.2 ⟨Finset.mem_univ v, hv⟩) (hzz v hv).1
    rw [redD_apply, red_eq_zero_iff (valuation_le_one_D v _)] at h0
    exact h0

/-- An element outside `P'` has value `1` and a nonzero residue at the branches through `P'`. -/
lemma valuation_eq_one_of_notMem {P' : Ideal (DRint (0 : C) 1 G)} {z : DRint (0 : C) 1 G}
    (hz : z ∉ P') {v : Ext C G} {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    {hQ : Q ∈ zeros 𝓀 (red C (xF C G) v)} (hQP : placeIdealD v hQ = P') :
    v.1 (z : G) = 1 ∧ Q.res (red C (z : G) v) ≠ 0 := by
  have hres : Q.res (red C (z : G) v) ≠ 0 := by
    intro h
    exact hz (hQP ▸ (mem_placeIdealD_iff v hQ z).2 h)
  refine ⟨le_antisymm (valuation_le_one_D v z) (not_lt.1 fun hlt ↦ hres ?_), hres⟩
  rw [(red_eq_zero_iff (valuation_le_one_D v z)).2 hlt, Q.res_zero]

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Clearing the components not through `P'`.** -/
theorem exists_lift' {P' : Ideal (DRint (0 : C) 1 G)} {z : DRint (0 : C) 1 G}
    (hz : ∀ v : Ext C G, ¬ Through P' v → v.1 (z : G) < 1) {f : G}
    (hf : IsIntegral (Algebra.adjoin C {xF C G}) f)
    (hfv : ∀ v : Ext C G, Through P' v → v.1 f ≤ 1) :
    ∃ N : ℕ, ∀ M ≥ N, IsIntegral (discRing (0 : C) 1) ((z : G) ^ M * f) := by
  classical
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  have hv : ∀ v : Ext C G, ∃ N : ℕ, ¬ Through P' v → ∀ M ≥ N, v.1 ((z : G) ^ M * f) ≤ 1 := by
    intro v
    by_cases hvv : Through P' v
    · exact ⟨0, fun h ↦ absurd hvv h⟩
    by_cases hf0 : v.1 f = 0
    · exact ⟨0, fun _ M _ ↦ by rw [map_mul, hf0, mul_zero]; exact zero_le⟩
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (inv_pos.2 (pos_iff_ne_zero.2 hf0)) (hz v hvv)
    refine ⟨N, fun _ M hM ↦ ?_⟩
    rw [map_mul, map_pow]
    have h1 : v.1 (z : G) ^ M ≤ v.1 (z : G) ^ N :=
      pow_le_pow_of_le_one zero_le (hz v hvv).le hM
    calc v.1 (z : G) ^ M * v.1 f ≤ (v.1 f)⁻¹ * v.1 f := mul_le_mul_left (h1.trans hN.le) _
      _ = 1 := inv_mul_cancel₀ hf0
  choose N hN using hv
  refine ⟨Finset.univ.sup N, fun M hM ↦ isIntegral_of_le hp hp1
    (((isIntegral_adjoin z).pow M).mul hf) fun v ↦ ?_⟩
  by_cases hvv : Through P' v
  · rw [map_mul, map_pow]
    exact mul_le_one' (pow_le_one' (valuation_le_one_D v z) M) (hfv v hvv)
  · exact hN v hvv M ((Finset.le_sup (Finset.mem_univ v)).trans hM)

include hp hp1 in
/-- **The residue at `P'`.** Let `ξ` be a valuation of `G` with centre `P'` on `R'`, `z ∈ R' ∖ P'`
small on the components not through `P'`, and `f` integral over `C[x]` of value `≤ 1` at the
components through `P'`. Then there is `c ∈ O_C` with `ξ(f - c) < 1`, and at every branch `(v, Q)`
through `P'`: `v(f) ≤ 1`, `f̄ ∈ O_Q` and `f̄(Q) = c̄`. -/
theorem exists_res_eq {P' : Ideal (DRint (0 : C) 1 G)} [hP : P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 G)) =
      discIdeal (0 : C) 1)
    {ξ : Valuation G ℝ≥0} (hξ : ∀ y : DRint (0 : C) 1 G, y ∈ P' ↔ ξ (y : G) < 1)
    (hξle : ∀ y : DRint (0 : C) 1 G, ξ (y : G) ≤ 1)
    {z : DRint (0 : C) 1 G} (hzP : z ∉ P') (hz : ∀ v : Ext C G, ¬ Through P' v → v.1 (z : G) < 1)
    {f : G} (hf : IsIntegral (Algebra.adjoin C {xF C G}) f)
    (hfv : ∀ v : Ext C G, Through P' v → v.1 f ≤ 1) :
    ∃ c : HenselComplete.integers C, ξ (f - algebraMap C G c) < 1 ∧
      ∀ (v : Ext C G) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
        (hQ : Q ∈ zeros 𝓀 (red C (xF C G) v)), placeIdealD v hQ = P' →
        red C f v ∈ Q.V ∧ Q.res (red C f v) = residue _ c := by
  classical
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  obtain ⟨N, hN⟩ := exists_lift' hp hp1 hz hf hfv
  set F₀ : DRint (0 : C) 1 G := ⟨_, hN N le_rfl⟩
  set Z₀ : DRint (0 : C) 1 G := z ^ N
  have hZ₀ : Z₀ ∉ P' := fun h ↦ hzP (hP.isPrime.mem_of_pow_mem N h)
  -- a branch through `P'`
  obtain ⟨⟨v₀, Q₀, hQ₀⟩, hb₀⟩ := exists_mem_discBranches hp hp1 P' hP'
  have hP₀ : placeIdealD v₀ hQ₀ = P' := hb₀
  set φ := placeHomD v₀ hQ₀
  have hφZ : φ Z₀ ≠ 0 := fun h ↦ hZ₀ (hP₀ ▸ (RingHom.mem_ker).2 h)
  obtain ⟨c, hc⟩ := residue_surjective (φ F₀ / φ Z₀)
  have hdiff : F₀ - constD c * Z₀ ∈ P' := by
    rw [← hP₀]
    change φ (F₀ - constD c * Z₀) = 0
    rw [_root_.map_sub, map_mul, placeHomD_constD, hc, div_mul_cancel₀ _ hφZ, sub_self]
  have hZcoe : ((Z₀ : DRint (0 : C) 1 G) : G) = (z : G) ^ N := by simp [Z₀]
  have hξZ : ξ (Z₀ : G) = 1 :=
    le_antisymm (hξle Z₀) (not_lt.1 fun h ↦ hZ₀ ((hξ Z₀).2 h))
  refine ⟨c, ?_, fun v Q hQ hQP ↦ ?_⟩
  · have h1 := (hξ _).1 hdiff
    have hcoe : ((F₀ - constD c * Z₀ : DRint (0 : C) 1 G) : G) =
        (Z₀ : G) * (f - algebraMap C G c) := by
      change (z : G) ^ N * f - algebraMap (RatFunc C) G (algebraMap C (RatFunc C) c) * (z : G) ^ N
        = _
      rw [← IsScalarTower.algebraMap_apply, hZcoe]; ring
    rwa [hcoe, map_mul, hξZ, one_mul] at h1
  · obtain ⟨hvz, hresz⟩ := valuation_eq_one_of_notMem hzP hQP
    have hvf := hfv v ⟨Q, hQ, hQP⟩
    have hQz : Q.valuation (red C (z : G) v) = 1 :=
      (notMem_placeIdealD_iff v hQ z).1 (hQP ▸ hzP)
    have hzV : red C (z : G) v ∈ Q.V := redD_mem_V v z (xbar_mem_V v hQ)
    have hredF : red C ((F₀ : DRint (0 : C) 1 G) : G) v = red C (z : G) v ^ N * red C f v := by
      change red C ((z : G) ^ N * f) v = _
      rw [red_mul (by rw [map_pow, hvz, one_pow]) hvf, red_pow (le_of_eq hvz)]
    have hFV : red C ((F₀ : DRint (0 : C) 1 G) : G) v ∈ Q.V := redD_mem_V v F₀ (xbar_mem_V v hQ)
    have hzne : red C (z : G) v ≠ 0 := fun h ↦ by rw [h, map_zero] at hQz; exact zero_ne_one hQz
    have hfV : red C f v ∈ Q.V := by
      have : red C f v = red C ((F₀ : DRint (0 : C) 1 G) : G) v * (red C (z : G) v ^ N)⁻¹ := by
        rw [hredF]; field_simp
      rw [this, ← Q.valuation_le_one_iff, map_mul, map_inv₀, map_pow, hQz, one_pow, inv_one,
        mul_one, Q.valuation_le_one_iff]
      exact hFV
    refine ⟨hfV, ?_⟩
    have h0 : Q.res (redD v (F₀ - constD c * Z₀)) = 0 :=
      (mem_placeIdealD_iff v hQ _).1 (hQP ▸ hdiff)
    have hred : redD v (F₀ - constD c * Z₀) =
        red C (z : G) v ^ N * (red C f v - algebraMap 𝓀 _ (residue _ c)) := by
      rw [_root_.map_sub, map_mul, redD_constD, map_pow, redD_apply, redD_apply, hredF]
      ring
    rw [hred, Q.res_mul (pow_mem hzV N)
      (sub_mem hfV (Q.algebraMap_mem _)), Q.res_sub_algebraMap hfV] at h0
    have hpow : Q.res (red C (z : G) v ^ N) ≠ 0 := by
      rw [show red C (z : G) v ^ N = ∏ _i ∈ Finset.range N, red C (z : G) v by simp,
        CurvePlace.res_prod _ _ _ fun _ _ ↦ hzV, Finset.prod_const, Finset.card_range]
      exact pow_ne_zero _ hresz
    exact sub_eq_zero.1 ((mul_eq_zero.1 h0).resolve_left hpow)

/-! ### Values, valuations on the chart, transported places -/

section Misc

omit [Algebra C G] [IsScalarTower C (RatFunc C) G] [CharZero C] in
/-- The values of an extension of `w_{0,1}` are norms of `C`. -/
theorem ext_exists_eq_nnnorm (v : Ext C G) {y : G} (hy : y ≠ 0) :
    ∃ γ : C, γ ≠ 0 ∧ v.1 y = ‖γ‖₊ := by
  obtain ⟨n, hn, φ, hφ, h⟩ := exists_pow_valuation_eq v.1
    (Algebra.IsIntegral.isIntegral (R := RatFunc C) y) hy
  rw [valuation_algebraMap] at h
  have hnorm : ∀ P : C[X], P ≠ 0 → ∃ γ : C, γ ≠ 0 ∧
      gauss1 C (algebraMap C[X] (RatFunc C) P) = ‖γ‖₊ := by
    intro P hP
    obtain ⟨i, hi⟩ := Gauss.exists_term_eq_sup (v := NormedField.valuation (K := C)) (r := 1) P
    rw [gauss1_algebraMap, ← hi]
    refine ⟨P.coeff i, fun h0 ↦ ?_, by simp [Gauss.term, NormedField.valuation_apply]⟩
    have : Gauss.sup (NormedField.valuation (K := C)) 1 P = 0 := by
      rw [← hi]; simp [Gauss.term, h0]
    exact hP (Gauss.sup_eq_zero_iff.1 this)
  obtain ⟨γ₁, hγ₁, h₁⟩ := hnorm _ (RatFunc.num_ne_zero hφ)
  obtain ⟨γ₂, hγ₂, h₂⟩ := hnorm _ (RatFunc.denom_ne_zero φ)
  rw [← RatFunc.num_div_denom φ, map_div₀, h₁, h₂, ← nnnorm_div] at h
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_pow_nat_eq (γ₁ / γ₂) hn
  refine ⟨δ, fun h0 ↦ div_ne_zero hγ₁ hγ₂ (by rw [← hδ, h0, zero_pow hn.ne']), ?_⟩
  rw [← hδ, nnnorm_pow] at h
  exact (pow_left_inj₀ zero_le zero_le hn.ne').1 h

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) G] [CharZero C] in
/-- A valuation which is `≤ 1` on `O_C` and on `x` is `≤ 1` on `R' = DRint 0 1 G`. -/
theorem val_le_one_of_xF {w : Valuation G ℝ≥0}
    (hC : ∀ c : C, ‖c‖ ≤ 1 → w (algebraMap (RatFunc C) G (algebraMap C (RatFunc C) c)) ≤ 1)
    (hx : w (xF C G) ≤ 1) (y : DRint (0 : C) 1 G) : w (y : G) ≤ 1 := by
  have hpoly : ∀ a : discRing (0 : C) 1, w (algebraMap (RatFunc C) G a) ≤ 1 := by
    rintro ⟨a, ha⟩
    obtain ⟨Q, hQ, rfl⟩ := mem_discRing_iff.1 ha
    have hQ' := nnnorm_coeff_le_one hQ
    change w (algebraMap (RatFunc C) G (algebraMap C[X] (RatFunc C) Q)) ≤ 1
    rw [← RatFunc.aeval_X_left_eq_algebraMap, ← Polynomial.aeval_algebraMap_apply,
      aeval_eq_sum_range]
    refine Valuation.map_sum_le _ fun i _ ↦ ?_
    rw [Algebra.smul_def, map_mul, map_pow]
    refine mul_le_one' ?_ (pow_le_one' hx _)
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) G]
    exact hC _ (by exact_mod_cast hQ' i)
  let φ : discRing (0 : C) 1 →+* w.integer :=
    { toFun := fun a ↦ ⟨algebraMap (RatFunc C) G a, hpoly a⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp
      map_zero' := by ext; simp
      map_add' := fun a b ↦ by ext; simp }
  have hint : IsIntegral w.integer (y : G) :=
    IsIntegral.map_of_comp_eq φ (RingHom.id G) (by ext; rfl) y.2
  exact (Valuation.integer.integers w).mem_of_integral hint

end Misc

section Places

variable {k κ κ' : Type*} [Field k] [Field κ] [Field κ'] [Algebra k κ] [Algebra k κ']
  [IsAlgClosed k] [IsCurveFunctionField k κ] [IsCurveFunctionField k κ']

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
/-- The residue of a transported place. -/
lemma res_map (ε : κ ≃ₐ[k] κ') (Q : CurvePlace k κ) {a : κ'} (ha : a ∈ (Q.map ε).V) :
    (Q.map ε).res a = Q.res (ε.symm a) := by
  refine (Q.map ε).res_eq_of_valuation_sub_lt_one ?_
  rw [valuation_map, _root_.map_sub, AlgEquiv.commutes]
  exact Q.valuation_sub_res_lt_one ha

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField k κ']
  in
/-- Multiplication by a unit at `Q`. -/
lemma mem_and_res_iff (Q : CurvePlace k κ) {u f : κ} (hu : Q.valuation u = 1) (N : ℕ)
    (hf : u ^ N * f ∈ Q.V) : f ∈ Q.V ∧ (Q.res (u ^ N * f) = 0 ↔ Q.res f = 0) := by
  have hu0 : u ≠ 0 := fun h ↦ by rw [h, map_zero] at hu; exact zero_ne_one hu
  have huV : u ∈ Q.V := Q.valuation_le_one_iff.1 hu.le
  have hfV : f ∈ Q.V := by
    have : f = u ^ N * f * (u ^ N)⁻¹ := by field_simp
    rw [this, ← Q.valuation_le_one_iff, map_mul, map_inv₀, map_pow, hu, one_pow, inv_one,
      mul_one, Q.valuation_le_one_iff]
    exact hf
  refine ⟨hfV, ?_⟩
  have hpow : Q.res (u ^ N) ≠ 0 := by
    intro h
    have := Q.valuation_sub_res_lt_one (pow_mem huV N)
    rw [h, map_zero, sub_zero, map_pow, hu, one_pow] at this
    exact lt_irrefl 1 this
  rw [Q.res_mul (pow_mem huV N) hfV, mul_eq_zero, or_iff_right hpow]

end Places

end TypeFour

end SemistableReduction
