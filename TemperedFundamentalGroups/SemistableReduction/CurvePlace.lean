/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.FundamentalInequality

/-!
# Places and pole orders of a function field of one variable

Blueprint §9.4, E1 (residue-curve infrastructure, also for W5/W6). Let `k` be an algebraically
closed field and `κ / k` a function field of one variable (`IsCurveFunctionField k κ`: `κ` is
finite over `k(x)` for some `x` transcendental over `k`). We define

* `CurvePlace k κ`: the places of `κ / k`, i.e. the valuation subrings `V ≠ κ` of `κ` containing
  `k`;
* `CurvePlace.valuation P : Valuation κ ℤᵐ⁰`, the normalized discrete valuation of a place
  (every place is a discrete valuation ring, `CurvePlace.isDiscreteValuationRing`);
* `CurvePlace.poleOrder P f : ℕ`, the pole order of `f` at `P` (`0` if `f` has no pole at `P`);
* `poleNorm k f : ℕ`, the maximal pole order of `f` over all places.

Main results: every place is a DVR (`CurvePlace.isDiscreteValuationRing`), every `f` has
uniformly bounded pole orders (`CurvePlace.exists_valuation_le`), and `‖·‖ = poleNorm k` satisfies
`‖f + g‖ ≤ max ‖f‖ ‖g‖` (`poleNorm_add_le`), `‖c • f‖ ≤ ‖f‖` for `c ∈ k` (`poleNorm_smul_le`),
`‖f ^ n‖ = n ‖f‖` (`poleNorm_pow`) and `‖f‖ = 0 ↔ f ∈ k` (`poleNorm_eq_zero_iff`).

## Proof outline

Fix `x` transcendental with `κ / k(x)` finite of degree `n`.

* For a valuation `w` of `κ` trivial on `k` and `u` with `w u < 1`, `w (Q(u)) = w(u)^{ord₀ Q}`
  for polynomials `Q ∈ k[X]` (`valuation_aeval_eq`); hence the values of `k(u)` are the powers
  of `w u`.
* Every place contains an element `u` with `x ∈ k(u)` and `w u < 1`: `u = x⁻¹` if `x ∉ V`,
  otherwise `u = x - α` for some `α ∈ k` (else all polynomials in `x` are units, `k(x) ⊆ V`, and
  `κ ⊆ V` since `κ / k(x)` is algebraic, `valuation_le_of_aeval_eq_zero`).
* The value group of `V` contains the cyclic group of values of `k(x)` with finite index
  (`FundamentalInequality.ramificationIdx_ne_zero`), so it is cyclic and `V` is a DVR.
* Normalizing, `ord_P(u) ≤ n` for such `u` (`e ≤ n` by the fundamental inequality), which bounds
  the pole orders of `r(x)/s(x)` at all places uniformly in terms of `deg s`, and then those of
  any `f ∈ κ` in terms of the coefficients of its minimal polynomial over `k(x)`.
* A non-constant `f` is not integral over `k`, so it has a pole
  (`Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn`, Chevalley).
-/

open IntermediateField Polynomial Valuation IsDedekindDomain WithZero
open scoped WithZero

namespace SemistableReduction

/-- `κ` is a function field of one variable over `k`: `κ` is a finite extension of `k(x)` for
some `x ∈ κ` transcendental over `k`. -/
class IsCurveFunctionField (k κ : Type*) [Field k] [Field κ] [Algebra k κ] : Prop where
  exists_transcendental_finiteDimensional :
    ∃ x : κ, Transcendental k x ∧ FiniteDimensional k⟮x⟯ κ

section Group

/-- A subgroup `G'` of a torsion-free commutative group is cyclic if it contains a subgroup `H`
of a cyclic group with finite index: `g ↦ g ^ [G' : H]` embeds `G'` into a cyclic group. -/
lemma isCyclic_of_relIndex_ne_zero {G : Type*} [CommGroup G] [IsMulTorsionFree G]
    {H G' : Subgroup G} {g : G} (hH : H ≤ Subgroup.zpowers g) (h : H.relIndex G' ≠ 0) :
    IsCyclic G' := by
  let φ : G' →* Subgroup.zpowers g :=
    { toFun := fun y ↦ ⟨y ^ H.relIndex G', hH (H.pow_relIndex_mem y.2)⟩
      map_one' := by ext; simp
      map_mul' := fun a b ↦ by ext; simp [mul_pow] }
  have hφ : Function.Injective φ := fun a b hab ↦ by
    have := congrArg (fun z : Subgroup.zpowers g ↦ (z : G)) hab
    exact Subtype.ext (pow_left_injective h this)
  exact isCyclic_of_surjective (MonoidHom.ofInjective hφ).symm.toMonoidHom (MulEquiv.surjective _)

end Group

section Valuation

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ]
  {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {w : Valuation κ Γ}

/-- A valuation which is `≤ 1` on `k` is trivial on `k`. -/
lemma valuation_algebraMap_eq_one (hk : ∀ c : k, w (algebraMap k κ c) ≤ 1) {c : k}
    (hc : c ≠ 0) : w (algebraMap k κ c) = 1 := by
  refine le_antisymm (hk c) ?_
  have h := hk c⁻¹
  rw [map_inv₀, map_inv₀] at h
  exact (inv_le_one₀ ((Valuation.pos_iff w).2 ((_root_.map_ne_zero _).2 hc))).1 h

lemma valuation_aeval_le_one (hk : ∀ c : k, w (algebraMap k κ c) ≤ 1) {u : κ} (hu : w u ≤ 1)
    (Q : k[X]) : w (aeval u Q) ≤ 1 := by
  rw [aeval_eq_sum_range]
  refine map_sum_le w fun i _ ↦ ?_
  rw [Algebra.smul_def, map_mul, map_pow]
  exact mul_le_one' (hk _) (pow_le_one' hu _)

/-- If `w` is trivial on `k` and `w u < 1`, then `w (Q(u)) = w(u) ^ ord₀ Q`. -/
lemma valuation_aeval_eq (hk : ∀ c : k, w (algebraMap k κ c) ≤ 1) {u : κ} (hu : w u < 1)
    {Q : k[X]} (hQ : Q ≠ 0) : w (aeval u Q) = w u ^ Q.rootMultiplicity 0 := by
  obtain ⟨g, hg, hdvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q hQ 0
  have hg0 : g.coeff 0 ≠ 0 := fun h ↦ hdvd (by simpa [X_dvd_iff] using h)
  have hwg : w (aeval u g) = 1 := by
    rw [← divX_mul_X_add g, map_add, map_mul, aeval_X, aeval_C, add_comm,
      Valuation.map_add_eq_of_lt_left, valuation_algebraMap_eq_one hk hg0]
    rw [valuation_algebraMap_eq_one hk hg0, map_mul]
    calc w (aeval u g.divX) * w u ≤ 1 * w u := by
          gcongr
          exact valuation_aeval_le_one hk hu.le _
      _ < 1 := by rwa [one_mul]
  conv_lhs => rw [hg]
  simp [hwg]

/-- If `w` is trivial on `k` and `w u < 1`, the values of the nonzero elements of `k(u)` are the
powers of `w u`. -/
lemma exists_valuation_eq_zpow (hk : ∀ c : k, w (algebraMap k κ c) ≤ 1) {u : κ} (hu : w u < 1)
    (hu0 : u ≠ 0) {y : κ} (hy : y ∈ k⟮u⟯) (hy0 : y ≠ 0) : ∃ n : ℤ, w y = w u ^ n := by
  obtain ⟨r, s, rfl⟩ := (mem_adjoin_simple_iff k y).1 hy
  obtain ⟨hr, hs⟩ := div_ne_zero_iff.1 hy0
  have hr' : r ≠ 0 := by rintro rfl; simp at hr
  have hs' : s ≠ 0 := by rintro rfl; simp at hs
  refine ⟨(r.rootMultiplicity 0 : ℤ) - s.rootMultiplicity 0, ?_⟩
  rw [map_div₀, valuation_aeval_eq hk hu hr', valuation_aeval_eq hk hu hs',
    zpow_sub₀ ((Valuation.ne_zero_iff w).2 hu0),
    zpow_natCast, zpow_natCast]

/-- A root `y` of a monic polynomial whose coefficients have values `≤ b` (with `1 ≤ b`) has
value `≤ b`. -/
lemma valuation_le_of_aeval_eq_zero {K : Type*} [Field K] [Algebra K κ] {P : K[X]}
    (hP : P.Monic) {y : κ} (hy : aeval y P = 0) {b : Γ} (hb : 1 ≤ b)
    (hc : ∀ i, w (algebraMap K κ (P.coeff i)) ≤ b) : w y ≤ b := by
  by_contra! hlt
  have hy1 : 1 < w y := hb.trans_lt hlt
  set m := P.natDegree
  have hm : m ≠ 0 := by
    intro hm
    rw [Polynomial.eq_one_of_monic_natDegree_zero hP hm, map_one] at hy
    exact one_ne_zero hy
  rw [hP.as_sum, map_add, map_pow, aeval_X, add_eq_zero_iff_eq_neg] at hy
  have key : w (y ^ m) < w (y ^ m) := by
    conv_lhs => rw [hy]
    rw [Valuation.map_neg, map_sum, map_pow]
    refine map_sum_lt w ((zero_lt_one.trans (one_lt_pow₀ hy1 hm)).ne') fun i hi ↦ ?_
    rw [map_mul, map_pow, aeval_C, aeval_X, map_mul, map_pow]
    have hi : i + 1 ≤ m := Finset.mem_range.1 hi
    calc w (algebraMap K κ (P.coeff i)) * w y ^ i ≤ b * w y ^ i := by
          gcongr
          exact hc i
      _ < w y * w y ^ i := by
          gcongr
          exact pow_pos (zero_lt_one.trans hy1) i
      _ = w y ^ (i + 1) := (pow_succ' _ _).symm
      _ ≤ w y ^ m := pow_le_pow_right₀ hy1.le hi
  exact lt_irrefl _ key

end Valuation

section Factor

variable {k κ : Type*} [Field k] [IsAlgClosed k] [Field κ] [Algebra k κ]

/-- Over an algebraically closed `k`, `s(u) = lc(s) · ∏_{α root of s} (u - α)`. -/
lemma aeval_eq_prod (s : k[X]) (u : κ) :
    aeval u s = algebraMap k κ s.leadingCoeff *
      (s.roots.map fun α ↦ u - algebraMap k κ α).prod := by
  conv_lhs =>
    rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (p := s) IsAlgClosed.card_roots_eq_natDegree]
  simp [map_multiset_prod, Multiset.map_map]

omit [IsAlgClosed k] in
lemma mem_adjoin_sub {x u : κ} (hxu : x ∈ k⟮u⟯) (α : k) : x ∈ k⟮u - algebraMap k κ α⟯ := by
  refine adjoin_simple_le_iff.2 ?_ hxu
  simpa using add_mem (mem_adjoin_simple_self k (u - algebraMap k κ α))
    (IntermediateField.algebraMap_mem k⟮u - algebraMap k κ α⟯ α)

end Factor

namespace FundamentalInequality

variable {L : Type*} [Field L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

/-- The value group `valueGroup w` agrees with Mathlib's `MonoidWithZeroHom.valueGroup`. -/
lemma valueGroup_eq (w : Valuation L Γ) :
    valueGroup w = MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass w) := by
  ext g
  refine ⟨fun ⟨x, hx⟩ ↦ MonoidWithZeroHom.mem_valueGroup _ ⟨x, hx⟩, fun hg ↦ ?_⟩
  obtain ⟨a, ha, x, -, hax⟩ := (MonoidWithZeroHom.mem_valueGroup_iff_of_comm' _).1 hg
  refine ⟨x / a, ?_⟩
  change w a ≠ 0 at ha
  change w a * g = w x at hax
  rw [map_div₀, ← hax, mul_div_cancel_left₀ _ ha]

end FundamentalInequality

variable (k κ : Type*) [Field k] [Field κ] [Algebra k κ]

/-- A place of the function field `κ / k`: a valuation subring `V ≠ κ` of `κ` containing `k`. -/
@[ext]
structure CurvePlace where
  /-- The valuation ring of the place. -/
  V : ValuationSubring κ
  algebraMap_mem : ∀ c : k, algebraMap k κ c ∈ V
  ne_top : V ≠ ⊤

namespace CurvePlace

variable {k κ}

/-- If `k` is algebraically closed and `f ∈ κ` is not in `k`, then `f` has a pole at some place:
`f` is not integral over `k`, so some valuation subring containing `k` avoids `f`. -/
theorem exists_not_mem [IsAlgClosed k] {f : κ} (hf : f ∉ (algebraMap k κ).range) :
    ∃ P : CurvePlace k κ, f ∉ P.V := by
  have hfR : f ∉ (integralClosure k κ).toSubring := fun h ↦ hf <|
    minpoly.mem_range_of_degree_eq_one k f
      (IsAlgClosed.degree_eq_one_of_irreducible k (minpoly.irreducible h))
  obtain ⟨V, hRV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hfR
  refine ⟨⟨V, fun c ↦ hRV (isIntegral_algebraMap (x := c)), ?_⟩, hfV⟩
  rintro rfl
  exact hfV trivial

variable (P : CurvePlace k κ)

lemma valuationSubring_valuation_algebraMap_le_one (c : k) :
    P.V.valuation (algebraMap k κ c) ≤ 1 :=
  (P.V.valuation_le_one_iff _).2 (P.algebraMap_mem c)

variable [IsAlgClosed k]

/-- If `κ / k(x)` is algebraic, every place contains some `u ≠ 0` with `x ∈ k(u)` and `v(u) < 1`
(namely `x⁻¹` or some `x - α`). -/
lemma exists_mem_adjoin_valuation_lt_one {x : κ} [Algebra.IsAlgebraic k⟮x⟯ κ] :
    ∃ u : κ, u ≠ 0 ∧ x ∈ k⟮u⟯ ∧ P.V.valuation u < 1 := by
  set w := P.V.valuation
  have hk := P.valuationSubring_valuation_algebraMap_le_one
  by_cases hx : x ∈ P.V
  · by_contra! H
    -- all polynomials in `x` which do not vanish are units of `V`
    have hpoly (s : k[X]) (hs : aeval x s ≠ 0) : w (aeval x s) = 1 := by
      have hs0 : s ≠ 0 := by rintro rfl; simp at hs
      rw [aeval_eq_prod] at hs ⊢
      rw [map_mul, valuation_algebraMap_eq_one hk (leadingCoeff_ne_zero.2 hs0), one_mul,
        map_multiset_prod]
      refine Multiset.prod_eq_one fun a ha ↦ ?_
      obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
      obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hb
      have hne : x - algebraMap k κ α ≠ 0 := fun h0 ↦ (right_ne_zero_of_mul hs)
        (Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨α, hα, h0⟩))
      exact le_antisymm ((P.V.valuation_le_one_iff _).2 (sub_mem hx (P.algebraMap_mem α)))
        (H _ hne (mem_adjoin_sub (mem_adjoin_simple_self k x) α))
    have hK (y : k⟮x⟯) : w y ≤ 1 := by
      obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff k (y : κ)).1 y.2
      rw [hrs, map_div₀]
      by_cases hs : aeval x s = 0
      · simp [hs]
      rw [hpoly s hs, div_one]
      exact valuation_aeval_le_one hk ((P.V.valuation_le_one_iff _).2 hx) r
    refine P.ne_top (top_unique fun f _ ↦ (P.V.valuation_le_one_iff f).1 ?_)
    exact valuation_le_of_aeval_eq_zero (K := k⟮x⟯)
      (minpoly.monic (Algebra.IsIntegral.isIntegral f)) (minpoly.aeval _ f) le_rfl
      fun i ↦ hK ((minpoly k⟮x⟯ f).coeff i)
  · have hx0 : x ≠ 0 := by rintro rfl; exact hx (zero_mem _)
    refine ⟨x⁻¹, inv_ne_zero hx0, ?_, ?_⟩
    · simpa using inv_mem (mem_adjoin_simple_self k x⁻¹)
    · rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (not_le.1 fun h ↦ hx ((P.V.valuation_le_one_iff x).1 h))

variable [IsCurveFunctionField k κ]

/-- The value group of a place is cyclic and nontrivial: it contains the values of `k(x)`, which
are the powers of `v(u)`, with finite index. -/
theorem isCyclic_valueGroup :
    IsCyclic (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass P.V.valuation)) ∧
      Nontrivial (MonoidWithZeroHom.valueGroup (MonoidWithZeroHom.ofClass P.V.valuation)) := by
  obtain ⟨x, -, hfin⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ)
  obtain ⟨u, hu0, hxu, hu⟩ := P.exists_mem_adjoin_valuation_lt_one (x := x)
  set w := P.V.valuation
  have hk := P.valuationSubring_valuation_algebraMap_le_one
  have hwu : w u ≠ 0 := (Valuation.ne_zero_iff w).2 hu0
  rw [← FundamentalInequality.valueGroup_eq]
  refine ⟨isCyclic_of_relIndex_ne_zero (g := Units.mk0 (w u) hwu) ?_
    (FundamentalInequality.ramificationIdx_ne_zero (K := k⟮x⟯) w), ?_⟩
  · rintro g ⟨y, hy⟩
    replace hy : w (y : κ) = g := by simpa using hy
    have hy0 : (y : κ) ≠ 0 := by
      rintro h
      rw [h, map_zero] at hy
      exact g.ne_zero hy.symm
    obtain ⟨m, hm⟩ := exists_valuation_eq_zpow hk hu hu0 (adjoin_simple_le_iff.2 hxu y.2) hy0
    refine ⟨m, Units.ext ?_⟩
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← hy, hm]
  · refine (Subgroup.nontrivial_iff_exists_ne_one _).2 ⟨Units.mk0 (w u) hwu, ⟨u, rfl⟩, ?_⟩
    intro h
    have := congrArg Units.val h
    rw [Units.val_mk0, Units.val_one] at this
    exact hu.ne this

/-- Every place of a function field of one variable over an algebraically closed field is a
discrete valuation ring. -/
instance isDiscreteValuationRing : IsDiscreteValuationRing P.V := by
  obtain ⟨h1, h2⟩ := P.isCyclic_valueGroup
  have := Valuation.valuationSubring_isDiscreteValuationRing P.V.valuation
  rwa [ValuationSubring.valuationSubring_valuation] at this

/-- The normalized discrete valuation of a place, with values in `ℤᵐ⁰` (a uniformizer has value
`exp (-1)`). -/
noncomputable def valuation : Valuation κ ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal P.V).valuation κ

lemma valuation_le_one_iff {f : κ} : P.valuation f ≤ 1 ↔ f ∈ P.V := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h
    exact a.2
  · change P.valuation (algebraMap P.V κ ⟨f, h⟩) ≤ 1
    rw [valuation, HeightOneSpectrum.valuation_of_algebraMap]
    exact HeightOneSpectrum.intValuation_le_one _ _

/-- The normalized valuation is equivalent to the valuation of the valuation subring. -/
lemma isEquiv : P.valuation.IsEquiv P.V.valuation := by
  refine (isEquiv_iff_valuationSubring _ _).2 ?_
  ext f
  rw [mem_valuationSubring_iff, mem_valuationSubring_iff, valuation_le_one_iff,
    ValuationSubring.valuation_le_one_iff]

lemma valuation_lt_one_iff {f : κ} : P.valuation f < 1 ↔ P.V.valuation f < 1 := by
  simpa using P.isEquiv.lt_iff_lt (x := f) (y := 1)

lemma valuation_algebraMap_le_one (c : k) : P.valuation (algebraMap k κ c) ≤ 1 :=
  P.valuation_le_one_iff.2 (P.algebraMap_mem c)

lemma exists_valuation_eq_exp_neg_one : ∃ π : κ, P.valuation π = exp (-1) :=
  HeightOneSpectrum.valuation_exists_uniformizer κ _

/-- If `κ / k(x)` has degree `n`, `u ≠ 0` lies in the valuation ring and `x ∈ k(u)`, then
`ord_P(u) ≤ n`: the values of `k(x)` are the powers of `v(u)`, and their index `e` in the value
group `ℤ` satisfies `e ≤ n` (fundamental inequality). -/
lemma exp_neg_finrank_le_valuation {x : κ} [FiniteDimensional k⟮x⟯ κ] {u : κ} (hu0 : u ≠ 0)
    (hxu : x ∈ k⟮u⟯) (hu : P.valuation u ≤ 1) :
    exp (-(Module.finrank k⟮x⟯ κ : ℤ)) ≤ P.valuation u := by
  set w := P.valuation
  set n := Module.finrank k⟮x⟯ κ
  rcases hu.lt_or_eq with hlt | heq
  swap
  · rw [heq, ← exp_zero, exp_le_exp]
    omega
  have hwu : w u ≠ 0 := (Valuation.ne_zero_iff w).2 hu0
  have hH : FundamentalInequality.valueGroup (w.comap (algebraMap k⟮x⟯ κ)) ≤
      Subgroup.zpowers (Units.mk0 (w u) hwu) := by
    rintro g ⟨y, hy⟩
    replace hy : w (y : κ) = g := by simpa using hy
    have hy0 : (y : κ) ≠ 0 := by
      rintro h
      rw [h, map_zero] at hy
      exact g.ne_zero hy.symm
    obtain ⟨m, hm⟩ := exists_valuation_eq_zpow P.valuation_algebraMap_le_one hlt hu0
      (adjoin_simple_le_iff.2 hxu y.2) hy0
    refine ⟨m, Units.ext ?_⟩
    rw [Units.val_zpow_eq_zpow_val, Units.val_mk0, ← hy, hm]
  set e := FundamentalInequality.ramificationIdx k⟮x⟯ w
  have he0 : e ≠ 0 := FundamentalInequality.ramificationIdx_ne_zero w
  have hen : e ≤ n := by
    have h1 := FundamentalInequality.ramificationIdx_mul_inertiaDeg_le
      (v := w.comap (algebraMap k⟮x⟯ κ)) (w := w)
    have := FundamentalInequality.finite_residueField (v := w.comap (algebraMap k⟮x⟯ κ)) (w := w)
    have h2 : 0 < FundamentalInequality.inertiaDeg (w.comap (algebraMap k⟮x⟯ κ)) w :=
      Module.finrank_pos
    exact le_of_mul_le_of_one_le_left h1 h2
  obtain ⟨π, hπ⟩ := P.exists_valuation_eq_exp_neg_one
  have hπ0 : (exp (-1) : ℤᵐ⁰) ≠ 0 := exp_ne_zero
  have hg : Units.mk0 _ hπ0 ∈ FundamentalInequality.valueGroup w := ⟨π, hπ⟩
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1
    (hH ((FundamentalInequality.valueGroup _).pow_relIndex_mem hg))
  have hj' := congrArg (fun g : ℤᵐ⁰ˣ ↦ log (g : ℤᵐ⁰)) hj
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_pow_eq_pow_val, log_zpow,
    log_pow, log_exp] at hj'
  change j • log (w u) = e • (-1 : ℤ) at hj'
  have hlog : log (w u) < 0 := by
    rw [← exp_lt_exp, exp_log hwu, exp_zero]
    exact hlt
  rw [← exp_log hwu, exp_le_exp]
  simp only [smul_eq_mul, nsmul_eq_mul, mul_neg, mul_one] at hj'
  have : (e : ℤ) ≤ n := by exact_mod_cast hen
  have : (0 : ℤ) < e := by exact_mod_cast Nat.pos_of_ne_zero he0
  have hj1 : 0 < j := by
    by_contra! hj0
    nlinarith
  nlinarith

/-- For `u` in the valuation ring with `x ∈ k(u)` and `s(u) ≠ 0`, `ord_P(s(u)) ≤ n · deg s`. -/
lemma exp_le_valuation_aeval {x : κ} [FiniteDimensional k⟮x⟯ κ] {u : κ} (hxu : x ∈ k⟮u⟯)
    (hu : P.valuation u ≤ 1) {s : k[X]} (hs : aeval u s ≠ 0) :
    exp (-(Module.finrank k⟮x⟯ κ * s.natDegree : ℤ)) ≤ P.valuation (aeval u s) := by
  have hs0 : s ≠ 0 := by rintro rfl; simp at hs
  rw [aeval_eq_prod] at hs ⊢
  rw [map_mul, valuation_algebraMap_eq_one P.valuation_algebraMap_le_one
    (leadingCoeff_ne_zero.2 hs0), one_mul, map_multiset_prod]
  have key : ∀ a ∈ (s.roots.map fun α ↦ u - algebraMap k κ α).map P.valuation,
      exp (-(Module.finrank k⟮x⟯ κ : ℤ)) ≤ a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Multiset.mem_map.1 ha
    obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hb
    have hne : u - algebraMap k κ α ≠ 0 := fun h0 ↦ (right_ne_zero_of_mul hs)
      (Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨α, hα, h0⟩))
    refine P.exp_neg_finrank_le_valuation hne (mem_adjoin_sub hxu α) ?_
    exact (Valuation.map_sub _ _ _).trans (max_le hu (P.valuation_algebraMap_le_one α))
  refine le_trans (le_of_eq ?_) (Multiset.pow_card_le_prod key)
  rw [Multiset.card_map, Multiset.card_map, IsAlgClosed.card_roots_eq_natDegree, ← exp_nsmul]
  congr 1
  simp [mul_comm]

/-- For `u` in the valuation ring with `x ∈ k(u)`: `r(u)/s(u)` has pole order `≤ n · deg s`. -/
lemma valuation_div_le {x : κ} [FiniteDimensional k⟮x⟯ κ] {u : κ} (hxu : x ∈ k⟮u⟯)
    (hu : P.valuation u ≤ 1) (r s : k[X]) :
    P.valuation (aeval u r / aeval u s) ≤ exp (Module.finrank k⟮x⟯ κ * s.natDegree : ℤ) := by
  by_cases hs : aeval u s = 0
  · simp [hs]
  have h := P.exp_le_valuation_aeval hxu hu hs
  have hpos : 0 < P.valuation (aeval u s) := (exp_pos).trans_le h
  rw [map_div₀, div_le_iff₀ hpos]
  calc P.valuation (aeval u r) ≤ 1 := valuation_aeval_le_one P.valuation_algebraMap_le_one hu r
    _ = exp (Module.finrank k⟮x⟯ κ * s.natDegree : ℤ) *
        exp (-(Module.finrank k⟮x⟯ κ * s.natDegree : ℤ)) := by rw [← exp_add]; simp
    _ ≤ _ := by gcongr

end CurvePlace

variable {k κ} [IsAlgClosed k]

/-- The elements of `k(x)` have uniformly bounded pole orders at all places. -/
lemma CurvePlace.exists_valuation_le_of_mem_adjoin [IsCurveFunctionField k κ] {x : κ}
    [FiniteDimensional k⟮x⟯ κ] {c : κ} (hc : c ∈ k⟮x⟯) :
    ∃ N : ℕ, ∀ P : CurvePlace k κ, P.valuation c ≤ exp (N : ℤ) := by
  obtain ⟨r, s, hrs⟩ := (mem_adjoin_simple_iff k c).1 hc
  have hxinv : x ∈ k⟮x⁻¹⟯ := by simpa using inv_mem (mem_adjoin_simple_self k x⁻¹)
  obtain ⟨r', s', hrs'⟩ := (mem_adjoin_simple_iff k c).1 (adjoin_simple_le_iff.2 hxinv hc)
  set n := Module.finrank k⟮x⟯ κ
  refine ⟨n * s.natDegree + n * s'.natDegree, fun P ↦ ?_⟩
  by_cases hx : P.valuation x ≤ 1
  · rw [hrs]
    refine (P.valuation_div_le (mem_adjoin_simple_self k x) hx r s).trans ?_
    rw [exp_le_exp]
    push_cast
    nlinarith [Nat.zero_le (n * s'.natDegree)]
  · have hx' : P.valuation x⁻¹ ≤ 1 := by
      rw [map_inv₀]
      exact inv_le_one_of_one_le₀ (not_le.1 hx).le
    rw [hrs']
    refine (P.valuation_div_le hxinv hx' r' s').trans ?_
    rw [exp_le_exp]
    push_cast
    nlinarith [Nat.zero_le (n * s.natDegree)]

/-- Every `f ∈ κ` has uniformly bounded pole orders at all places: bound the coefficients of its
minimal polynomial over `k(x)`. -/
theorem CurvePlace.exists_valuation_le [IsCurveFunctionField k κ] (f : κ) :
    ∃ N : ℕ, ∀ P : CurvePlace k κ, P.valuation f ≤ exp (N : ℤ) := by
  obtain ⟨x, -, hfin⟩ := IsCurveFunctionField.exists_transcendental_finiteDimensional (k := k)
    (κ := κ)
  have hc (i : ℕ) : ∃ N : ℕ, ∀ P : CurvePlace k κ,
      P.valuation ((minpoly k⟮x⟯ f).coeff i : κ) ≤ exp (N : ℤ) :=
    exists_valuation_le_of_mem_adjoin ((minpoly k⟮x⟯ f).coeff i).2
  choose N hN using hc
  refine ⟨(Finset.range ((minpoly k⟮x⟯ f).natDegree + 1)).sup N, fun P ↦ ?_⟩
  refine valuation_le_of_aeval_eq_zero (K := k⟮x⟯)
    (minpoly.monic (Algebra.IsIntegral.isIntegral f)) (minpoly.aeval _ f)
    (by rw [← exp_zero, exp_le_exp]; positivity) fun i ↦ ?_
  by_cases hi : i ≤ (minpoly k⟮x⟯ f).natDegree
  · refine (hN i P).trans ?_
    rw [exp_le_exp, Nat.cast_le]
    exact Finset.le_sup (f := N) (Finset.mem_range.2 (Nat.lt_succ_of_le hi))
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero, map_zero]
    exact zero_le

namespace CurvePlace

variable [IsCurveFunctionField k κ] (P : CurvePlace k κ)

/-- The pole order of `f` at the place `P`: `max 0 (-ord_P f)`. -/
noncomputable def poleOrder (f : κ) : ℕ := (log (P.valuation f)).toNat

lemma poleOrder_le_iff {f : κ} {N : ℕ} : P.poleOrder f ≤ N ↔ P.valuation f ≤ exp (N : ℤ) := by
  rw [poleOrder, Int.toNat_le]
  by_cases hf : f = 0
  · simp [hf]
  · rw [← exp_le_exp, exp_log ((Valuation.ne_zero_iff _).2 hf)]

lemma poleOrder_eq_zero_iff {f : κ} : P.poleOrder f = 0 ↔ f ∈ P.V := by
  rw [← Nat.le_zero, poleOrder_le_iff, Nat.cast_zero, exp_zero, valuation_le_one_iff]

lemma poleOrder_add_le (f g : κ) :
    P.poleOrder (f + g) ≤ max (P.poleOrder f) (P.poleOrder g) := by
  rw [poleOrder_le_iff]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · exact P.poleOrder_le_iff.1 (le_max_left _ _)
  · exact P.poleOrder_le_iff.1 (le_max_right _ _)

lemma poleOrder_algebraMap_mul_le (c : k) (f : κ) :
    P.poleOrder (algebraMap k κ c * f) ≤ P.poleOrder f := by
  rw [poleOrder_le_iff, map_mul]
  exact (mul_le_of_le_one_left' (P.valuation_algebraMap_le_one c)).trans
    (P.poleOrder_le_iff.1 le_rfl)

lemma poleOrder_pow (f : κ) (n : ℕ) : P.poleOrder (f ^ n) = n * P.poleOrder f := by
  rw [poleOrder, poleOrder, map_pow, log_pow, nsmul_eq_mul]
  rcases le_or_gt (log (P.valuation f)) 0 with h | h
  · rw [Int.toNat_eq_zero.2 h, Int.toNat_eq_zero.2 (mul_nonpos_of_nonneg_of_nonpos
      (Int.natCast_nonneg n) h), mul_zero]
  · rw [Int.toNat_mul (Int.natCast_nonneg n) h.le, Int.toNat_natCast]

lemma poleOrder_algebraMap (c : k) : P.poleOrder (algebraMap k κ c) = 0 :=
  P.poleOrder_eq_zero_iff.2 (P.algebraMap_mem c)

lemma bddAbove_poleOrder (f : κ) :
    BddAbove (Set.range fun P : CurvePlace k κ ↦ P.poleOrder f) := by
  obtain ⟨N, hN⟩ := exists_valuation_le (k := k) f
  exact ⟨N, by rintro _ ⟨P, rfl⟩; exact P.poleOrder_le_iff.2 (hN P)⟩

end CurvePlace

open CurvePlace

variable [IsCurveFunctionField k κ]

variable (k) in
/-- The pole norm `‖f‖` of `f ∈ κ`: the maximal pole order of `f` over all places of `κ / k`. -/
noncomputable def poleNorm (f : κ) : ℕ := ⨆ P : CurvePlace k κ, P.poleOrder f

lemma poleNorm_le_iff {f : κ} {N : ℕ} : poleNorm k f ≤ N ↔ ∀ P : CurvePlace k κ,
    P.poleOrder f ≤ N := by
  rcases isEmpty_or_nonempty (CurvePlace k κ) with h | h
  · simp [poleNorm]
  · exact ciSup_le_iff (bddAbove_poleOrder f)

lemma poleOrder_le_poleNorm (P : CurvePlace k κ) (f : κ) : P.poleOrder f ≤ poleNorm k f :=
  le_ciSup (bddAbove_poleOrder f) P

/-- `poleNorm` is attained at some place (if there is one). -/
lemma exists_poleOrder_eq_poleNorm [Nonempty (CurvePlace k κ)] (f : κ) :
    ∃ P : CurvePlace k κ, P.poleOrder f = poleNorm k f :=
  Nat.sSup_mem (Set.range_nonempty _) (bddAbove_poleOrder f)

lemma poleNorm_add_le (f g : κ) : poleNorm k (f + g) ≤ max (poleNorm k f) (poleNorm k g) :=
  poleNorm_le_iff.2 fun P ↦ (P.poleOrder_add_le f g).trans
    (max_le_max (poleOrder_le_poleNorm P f) (poleOrder_le_poleNorm P g))

lemma poleNorm_smul_le (c : k) (f : κ) : poleNorm k (c • f) ≤ poleNorm k f :=
  poleNorm_le_iff.2 fun P ↦ by
    rw [Algebra.smul_def]
    exact (P.poleOrder_algebraMap_mul_le c f).trans (poleOrder_le_poleNorm P f)

lemma poleNorm_pow (f : κ) (n : ℕ) : poleNorm k (f ^ n) = n * poleNorm k f := by
  refine le_antisymm (poleNorm_le_iff.2 fun P ↦ ?_) ?_
  · rw [P.poleOrder_pow]
    exact Nat.mul_le_mul_left n (poleOrder_le_poleNorm P f)
  · rcases isEmpty_or_nonempty (CurvePlace k κ) with h | h
    · simp [poleNorm]
    · obtain ⟨P, hP⟩ := exists_poleOrder_eq_poleNorm (k := k) f
      rw [← hP, ← P.poleOrder_pow]
      exact poleOrder_le_poleNorm P _

lemma poleNorm_neg (f : κ) : poleNorm k (-f) = poleNorm k f := by
  have h (g : κ) : poleNorm k (-g) ≤ poleNorm k g := by
    simpa using poleNorm_smul_le (-1 : k) g
  exact le_antisymm (h f) (by simpa using h (-f))

/-- `‖f‖ = 0` iff `f` is a constant: a non-constant has a pole (`CurvePlace.exists_not_mem`). -/
lemma poleNorm_eq_zero_iff {f : κ} : poleNorm k f = 0 ↔ f ∈ (algebraMap k κ).range := by
  rw [← Nat.le_zero, poleNorm_le_iff]
  simp_rw [Nat.le_zero, poleOrder_eq_zero_iff]
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra hf
    obtain ⟨P, hP⟩ := exists_not_mem hf
    exact hP (h P)
  · rintro ⟨c, rfl⟩ P
    exact P.algebraMap_mem c

lemma poleNorm_algebraMap (c : k) : poleNorm k (algebraMap k κ c) = 0 :=
  poleNorm_eq_zero_iff.2 ⟨c, rfl⟩

end SemistableReduction
