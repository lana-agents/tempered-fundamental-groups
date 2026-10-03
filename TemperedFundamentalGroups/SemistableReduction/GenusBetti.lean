/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SharpGenus

/-!
# The genus inequality with the first Betti number of the dual graph

Blueprint §9.5, the `b₁(Γ)` refinement over one Gauss point.

* `CurvePlace.exists_interpolating`: on a function field of one variable, for `D` of large degree,
  a finite set `S` of places and `Q₀ ∉ S`, some `f ∈ L(D)` has exact order `-D(Q₀)` at `Q₀` and
  order `> -D(Q)` at all `Q ∈ S` (Riemann–Roch for large degree, R7);
* `GEdge`: an edge of the special fibre over the Gauss point, recorded with its two branches
  (places `Q` of `κ(w)` and `Q'` of `κ(w')`) and its chart;
* **`sum_genus_add_le`**: for edges `e₀, …, e_{n-1}` such that the second branch of each edge is
  not a branch of an earlier edge (and differs from its own first branch),
  `Σ_w g(κ(w)) + n ≤ g(F) + #{w} - 1`. For the edges at the nodes of a semistable special fibre
  (`n = #E`) this is `Σ_w g(κ(w)) + b₁(Γ) ≤ g(F)`, `b₁(Γ) = #E - #V + 1`.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace CurvePlace

variable {k κ : Type*} [Field k] [Field κ] [Algebra k κ] [IsAlgClosed k]
  [IsCurveFunctionField k κ]

lemma res_eq_zero_iff (Q : CurvePlace k κ) {y : κ} (hy : y ∈ Q.V) :
    Q.res y = 0 ↔ Q.valuation y < 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ Q.res_eq_of_valuation_sub_lt_one (by simpa using h)⟩
  simpa [h] using Q.valuation_sub_res_lt_one hy

/-- The divisor `Σ_{Q ∈ S} Q`. -/
noncomputable def sumPlaces (S : Finset (CurvePlace k κ)) : CurveDivisor k κ :=
  ∑ Q ∈ S, Finsupp.single Q 1

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
open Classical in
lemma sumPlaces_apply (S : Finset (CurvePlace k κ)) (Q : CurvePlace k κ) :
    sumPlaces S Q = if Q ∈ S then 1 else 0 := by
  simp only [sumPlaces, Finsupp.finsetSum_apply, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

omit [IsAlgClosed k] [IsCurveFunctionField k κ] in
lemma degree_sumPlaces (S : Finset (CurvePlace k κ)) : (sumPlaces S).degree = S.card := by
  simp [sumPlaces, map_sum]

/-- **Interpolation** (R7): for `D` of large degree, finitely many places `S` and `Q₀ ∉ S`, there
is `f ∈ L(D)` with `v_{Q₀}(f) = exp (D Q₀)` and `v_Q(f) < exp (D Q)` for `Q ∈ S`. -/
theorem exists_interpolating : ∃ c : ℤ, ∀ (D : CurveDivisor k κ) (S : Finset (CurvePlace k κ))
    (Q₀ : CurvePlace k κ), Q₀ ∉ S → c + S.card ≤ D.degree →
      ∃ f ∈ rrSpace D, Q₀.valuation f = exp (D Q₀) ∧ ∀ Q ∈ S, Q.valuation f < exp (D Q) := by
  classical
  obtain ⟨c, hc⟩ := ell_eq_of_le_degree (k := k) (κ := κ)
  refine ⟨c + 1, fun D S Q₀ hQ₀ hdeg ↦ ?_⟩
  set D' := D - sumPlaces S
  set D'' := D' - Finsupp.single Q₀ 1
  have h1 := hc D' (by
    rw [_root_.map_sub, degree_sumPlaces]
    linarith)
  have h2 := hc D'' (by
    rw [_root_.map_sub, _root_.map_sub, degree_sumPlaces, Finsupp.degree_single]
    linarith)
  have hdeg'' : D''.degree = D'.degree - 1 := by
    rw [_root_.map_sub, Finsupp.degree_single]
  have hle : D'' ≤ D' := sub_le_self _ (fun Q ↦ by simp [Finsupp.single_apply]; split_ifs <;> simp)
  have hlt : rrSpace D'' < rrSpace D' := by
    refine lt_of_le_of_ne (rrSpace_mono hle) fun h ↦ ?_
    have : ell D'' = ell D' := by rw [ell, ell, h]
    have h3 : (ell D'' : ℤ) = ell D' := by exact_mod_cast this
    rw [h1, h2, hdeg''] at h3
    linarith
  obtain ⟨f, hf, hf''⟩ := SetLike.exists_of_lt hlt
  have hD' (Q : CurvePlace k κ) : D' Q = D Q - if Q ∈ S then 1 else 0 := by
    simp [D', sumPlaces_apply]
  refine ⟨f, rrSpace_mono (sub_le_self _ ?_) hf, ?_, fun Q hQ ↦ ?_⟩
  · intro Q
    rw [sumPlaces_apply]
    split_ifs <;> simp
  · obtain ⟨Q, hQ⟩ := not_forall.1 hf''
    have hQ₀Q : Q = Q₀ := by
      by_contra hne
      apply hQ
      have := hf Q
      simpa [D'', Finsupp.single_apply, Ne.symm hne] using this
    subst hQ₀Q
    refine le_antisymm ((hf Q).trans (by rw [hD', if_neg hQ₀, sub_zero])) ?_
    have := WithZero.exp_add_one_le_of_lt (not_le.1 hQ)
    simpa [D'', hD', hQ₀] using this
  · refine (hf Q).trans_lt ?_
    rw [hD', if_pos hQ, exp_lt_exp]
    omega

end CurvePlace

open FundamentalInequality GaussStability LatticeReduction DenseCompletion

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [Fintype (Ext C F)]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable (C F) in
/-- The chart `x` (`true`) or `x⁻¹` (`false`). -/
noncomputable def chartElt (b : Bool) : F := if b then xF C F else (xF C F)⁻¹

variable (C F) in
/-- The twist of the chart: `1` for `x`, `x̄⁻ᵐ` for `x⁻¹`. -/
noncomputable def tau (m : ℕ) (b : Bool) (v : Ext C F) : ResidueField v.1.valuationSubring :=
  if b then 1 else (red C (xF C F) v)⁻¹ ^ m

section Twist

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField
  isCurveFunctionField_F

omit [IsScalarTower C (RatFunc C) F] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma chartElt_mem_intRing (b : Bool) : chartElt C F b ∈ intRing C F (chartElt C F b) := by
  cases b
  · exact xF_inv_mem_intRing
  · exact xF_mem_intRing

omit [Fintype (Ext C F)] in
/-- The twist has the value prescribed by `m (x̄)_∞` at the places of the chart. -/
lemma valuation_tau (m : ℕ) (b : Bool) (v : Ext C F)
    (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
    (hQ : red C (chartElt C F b) v ∈ Q.V) :
    Q.valuation (tau C F m b v) = exp (-(m • poleDivisor 𝓀 (red C (xF C F) v)) Q) := by
  cases b with
  | true =>
    simp only [chartElt, if_true] at hQ
    simp [tau, Q.poleOrder_eq_zero_iff.2 hQ]
  | false =>
    simp only [chartElt, Bool.false_eq_true, if_false, red_inv_xF] at hQ
    simp only [tau, Bool.false_eq_true, if_false, Finsupp.smul_apply, poleDivisor_apply,
      map_pow, map_inv₀]
    by_cases hx : red C (xF C F) v ∈ Q.V
    · have h1 := Q.valuation_le_one_iff.2 hx
      have h2 := Q.valuation_le_one_iff.2 hQ
      rw [map_inv₀] at h2
      have hx0 : Q.valuation (red C (xF C F) v) ≠ 0 :=
        (Valuation.ne_zero_iff _).2 (red_xF_ne_zero v)
      have h3 : Q.valuation (red C (xF C F) v) = 1 :=
        le_antisymm h1 ((inv_le_one₀ (zero_lt_iff.2 hx0)).1 h2)
      rw [h3, Q.poleOrder_eq_zero_iff.2 hx]
      simp
    · rw [Q.valuation_eq_exp_poleOrder hx, ← exp_neg, ← exp_nsmul, smul_neg]

omit [Fintype (Ext C F)] in
lemma mul_tau_mem (m : ℕ) (b : Bool) {v : Ext C F}
    {Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)}
    (hQ : red C (chartElt C F b) v ∈ Q.V)
    {a : ResidueField v.1.valuationSubring}
    (ha : a ∈ rrSpace (m • poleDivisor 𝓀 (red C (xF C F) v))) :
    a * tau C F m b v ∈ Q.V := by
  refine Q.valuation_le_one_iff.1 ?_
  rw [map_mul, valuation_tau m b v Q hQ]
  calc Q.valuation a * exp (-(m • poleDivisor 𝓀 (red C (xF C F) v)) Q) ≤
      exp ((m • poleDivisor 𝓀 (red C (xF C F) v)) Q) *
        exp (-(m • poleDivisor 𝓀 (red C (xF C F) v)) Q) := by gcongr; exact ha Q
    _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]

variable (C F) in
/-- An edge of the special fibre over the Gauss point: two branches `Q` (of `κ(w)`) and `Q'` (of
`κ(w')`) through a common closed point of the chart `b`. -/
structure GEdge where
  /-- The first component. -/
  w : Ext C F
  /-- The second component. -/
  w' : Ext C F
  /-- The branch on the first component. -/
  Q : CurvePlace 𝓀 (ResidueField w.1.valuationSubring)
  /-- The branch on the second component. -/
  Q' : CurvePlace 𝓀 (ResidueField w'.1.valuationSubring)
  /-- The chart. -/
  chart : Bool
  hQ : ∀ a ∈ redRing C F (chartElt C F chart), a w ∈ Q.V
  hQ' : ∀ a ∈ redRing C F (chartElt C F chart), a w' ∈ Q'.V
  hQQ' : ∀ a ∈ redRing C F (chartElt C F chart),
    (Q.valuation (a w) < 1 ↔ Q'.valuation (a w') < 1)

namespace GEdge

variable (e : GEdge C F)

lemma red_chart_mem_Q : red C (chartElt C F e.chart) e.w ∈ e.Q.V :=
  e.hQ _ (red_mem_redRing (chartElt_mem_intRing e.chart))

lemma red_chart_mem_Q' : red C (chartElt C F e.chart) e.w' ∈ e.Q'.V :=
  e.hQ' _ (red_mem_redRing (chartElt_mem_intRing e.chart))

/-- The gluing functional of an edge. -/
noncomputable def φ (m : ℕ) : Module.Dual 𝓀 (piRR C F m) :=
  glue m (tau C F m e.chart) e.Q e.Q'
    (fun _ ha ↦ mul_tau_mem m e.chart e.red_chart_mem_Q (ha e.w trivial))
    (fun _ ha ↦ mul_tau_mem m e.chart e.red_chart_mem_Q' (ha e.w' trivial))

lemma φ_apply (m : ℕ) (a : piRR C F m) :
    e.φ m a = e.Q.res (a.1 e.w * tau C F m e.chart e.w) -
      e.Q'.res (a.1 e.w' * tau C F m e.chart e.w') := rfl

/-- The gluing functional vanishes on the reductions of `L(m (x)_∞)`. -/
lemma φ_eq_zero (m : ℕ) {a : piRR C F m} (ha : a ∈ redSpan C F m) : e.φ m a = 0 := by
  refine (Submodule.span_le (p := LinearMap.ker (e.φ m))).2 ?_ ha
  rintro _ ⟨f, hf, hn, hfa⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, φ_apply, hfa, sub_eq_zero]
  have hfw (v : Ext C F) : v.1 f ≤ 1 := (le_gnorm v f).trans hn
  set g : F := if e.chart then 1 else (xF C F)⁻¹ ^ m
  have hgw (v : Ext C F) : v.1 g ≤ 1 := by
    simp only [g]
    split_ifs
    · simp
    · rw [map_pow, valuation_xF_inv, one_pow]
  have hred (v : Ext C F) : red C f v * tau C F m e.chart v = red C (f * g) v := by
    rw [red_mul (hfw v) (hgw v)]
    congr 1
    simp only [g, tau]
    split_ifs
    · exact red_one.symm
    · rw [red_pow (valuation_xF_inv v).le, red_inv_xF]
  have hint : f * g ∈ intRing C F (chartElt C F e.chart) := by
    simp only [g, chartElt]
    split_ifs
    · rw [mul_one]
      exact ⟨isIntegral_of_mem_rrSpace hf, hn⟩
    · exact ⟨isIntegral_div_of_mem_rrSpace hf,
        (gnorm_mul_le _ _).trans (mul_le_one' hn (gnorm_xF_inv_pow m))⟩
  simp only [hred]
  exact res_eq_of_edge e.hQ e.hQQ' (red_mem_redRing hint)

end GEdge

end Twist

section Betti

variable [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField
  isCurveFunctionField_F

omit [Fintype (Ext C F)] in
/-- A vector supported at one component, with value of order `> -D(Q)` at `Q`, has vanishing
twisted residue at `Q`. -/
lemma res_single_mul_eq_zero [DecidableEq (Ext C F)] (m : ℕ) {W : Ext C F}
    (f : ResidueField W.1.valuationSubring)
    (p : Σ v : Ext C F, CurvePlace 𝓀 (ResidueField v.1.valuationSubring))
    (τ : Π v : Ext C F, ResidueField v.1.valuationSubring)
    (hτ : p.2.valuation (τ p.1) = exp (-(m • poleDivisor 𝓀 (red C (xF C F) p.1)) p.2))
    (hf : ∀ Q : CurvePlace 𝓀 (ResidueField W.1.valuationSubring), (⟨W, Q⟩ : Σ v : Ext C F,
      CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) = p →
      Q.valuation f < exp ((m • poleDivisor 𝓀 (red C (xF C F) W)) Q)) :
    p.2.res ((Pi.single W f : Π v : Ext C F, ResidueField v.1.valuationSubring) p.1 *
      τ p.1) = 0 := by
  obtain ⟨v, Q⟩ := p
  by_cases hv : v = W
  · subst hv
    rw [Pi.single_eq_same]
    refine Q.res_eq_of_valuation_sub_lt_one ?_
    rw [map_zero, sub_zero, map_mul, hτ]
    calc Q.valuation f * exp (-(m • poleDivisor 𝓀 (red C (xF C F) v)) Q) <
        exp ((m • poleDivisor 𝓀 (red C (xF C F) v)) Q) *
          exp (-(m • poleDivisor 𝓀 (red C (xF C F) v)) Q) :=
          mul_lt_mul_of_pos_right (hf Q rfl) exp_pos
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  · rw [Pi.single_eq_of_ne hv, zero_mul, CurvePlace.res_zero]

/-- A branch: a component together with a place of its residue curve. -/
abbrev mkB (v : Ext C F) (Q : CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :
    Σ v : Ext C F, CurvePlace 𝓀 (ResidueField v.1.valuationSubring) := ⟨v, Q⟩

omit [Fintype (Ext C F)] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma mkB_injective (v : Ext C F) : Function.Injective (mkB (C := C) (F := F) v) :=
  fun _ _ h ↦ eq_of_heq (Sigma.mk.inj h).2

omit [Fintype (Ext C F)] in
lemma single_mem_piRR [DecidableEq (Ext C F)] (m : ℕ) {W : Ext C F}
    {g : ResidueField W.1.valuationSubring}
    (hg : g ∈ rrSpace (m • poleDivisor 𝓀 (red C (xF C F) W))) :
    (Pi.single W g : Π v : Ext C F, ResidueField v.1.valuationSubring) ∈ piRR C F m := by
  intro v _
  by_cases hv : v = W
  · subst hv
    rw [Pi.single_eq_same]
    exact hg
  · rw [Pi.single_eq_of_ne hv]
    exact zero_mem _

/-- The branches of an edge as pairs (component, place). -/
abbrev GEdge.b₁ (e : GEdge C F) : Σ v : Ext C F, CurvePlace 𝓀 (ResidueField v.1.valuationSubring) :=
  ⟨e.w, e.Q⟩

/-- The second branch of an edge. -/
abbrev GEdge.b₂ (e : GEdge C F) : Σ v : Ext C F, CurvePlace 𝓀 (ResidueField v.1.valuationSubring) :=
  ⟨e.w', e.Q'⟩

variable {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
include hb

/-- **Counting with independent edges**: if the second branch of every edge is new (not a branch
of an earlier edge, nor the first branch of the same edge), then for `m ≫ 0`,
`ℓ(m (x)_∞) + n ≤ Σ_w ℓ_{κ(w)}(m (x̄)_∞)`. -/
theorem exists_ell_add_le (n : ℕ) (E : ℕ → GEdge C F) (hloop : ∀ l < n, (E l).b₂ ≠ (E l).b₁)
    (hnew : ∀ l' < n, ∀ l < l', (E l').b₂ ≠ (E l).b₁ ∧ (E l').b₂ ≠ (E l).b₂) :
    ∃ M : ℕ, ∀ m, M ≤ m → ell (m • poleDivisor C (xF C F)) + n ≤
      ∑ w : Ext C F, ell (m • poleDivisor 𝓀 (red C (xF C F) w)) := by
  classical
  haveI := nonempty_ext_of_orthonormal hb
  choose c hc using fun v : Ext C F ↦
    CurvePlace.exists_interpolating (k := 𝓀) (κ := ResidueField v.1.valuationSubring)
  refine ⟨∑ v, (c v).toNat + 2 * n + 1, fun m hm ↦ ?_⟩
  set D : Π v : Ext C F, CurveDivisor 𝓀 (ResidueField v.1.valuationSubring) :=
    fun v ↦ m • poleDivisor 𝓀 (red C (xF C F) v)
  have hdeg (v : Ext C F) : c v + (2 * n + 1 : ℕ) ≤ (D v).degree := by
    have hf : 1 ≤ inertiaDeg (gauss1 C) v.1 := by
      haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
        (ResidueField v.1.valuationSubring) := finite_residueField
      exact Module.finrank_pos
    rw [show (D v).degree = m * inertiaDeg (gauss1 C) v.1 by
      simp only [D]
      rw [map_nsmul, degree_poleDivisor (red_xF_notMem_range v), finrank_adjoin_red_x,
        nsmul_eq_mul]]
    have h1 : (c v).toNat ≤ ∑ v, (c v).toNat :=
      Finset.single_le_sum (f := fun v ↦ (c v).toNat) (fun _ _ ↦ Nat.zero_le _)
        (Finset.mem_univ v)
    have h2 : (m : ℤ) ≤ m * inertiaDeg (gauss1 C) v.1 := by
      exact_mod_cast Nat.le_mul_of_pos_right m hf
    have h3 := Int.self_le_toNat (c v)
    have h4 : ((∑ v, (c v).toNat + 2 * n + 1 : ℕ) : ℤ) ≤ m := by exact_mod_cast hm
    push_cast at h4 ⊢
    have h5 : ((c v).toNat : ℤ) ≤ ∑ v, ((c v).toNat : ℤ) := by exact_mod_cast h1
    linarith
  -- the forbidden branches for the test vector of the edge `l`
  set T : ℕ → Finset (Σ v : Ext C F, CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) :=
    fun l ↦ insert (E l).b₁ ((Finset.range l).biUnion fun i ↦ {(E i).b₁, (E i).b₂})
  have hTcard (l : ℕ) (hl : l < n) : (T l).card ≤ 2 * n + 1 := by
    refine (Finset.card_insert_le _ _).trans ?_
    have := Finset.card_biUnion_le (s := Finset.range l)
      (t := fun i ↦ ({(E i).b₁, (E i).b₂} : Finset _))
    have h2 : ∑ i ∈ Finset.range l, ({(E i).b₁, (E i).b₂} : Finset _).card ≤
        ∑ _i ∈ Finset.range l, 2 := Finset.sum_le_sum fun i _ ↦ Finset.card_le_two
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul] at h2
    omega
  set S : (l : ℕ) → Finset (CurvePlace 𝓀 (ResidueField (E l).w'.1.valuationSubring)) :=
    fun l ↦ (T l).preimage (mkB (E l).w') fun _ _ _ _ h ↦ mkB_injective _ h
  have hS (l : ℕ) (Q) : Q ∈ S l ↔ (⟨(E l).w', Q⟩ : Σ v : Ext C F,
      CurvePlace 𝓀 (ResidueField v.1.valuationSubring)) ∈ T l := Finset.mem_preimage
  have hQ0 (l : ℕ) (hl : l < n) : (E l).Q' ∉ S l := by
    rw [hS]
    simp only [T, Finset.mem_insert, Finset.mem_biUnion, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton, not_or, not_exists, not_and]
    exact ⟨hloop l hl, fun i hi ↦ hnew l hl i hi⟩
  have hScard (l : ℕ) (hl : l < n) : (S l).card ≤ 2 * n + 1 := by
    refine le_trans (Finset.card_le_card_of_injOn (mkB (E l).w') (fun Q hQ ↦ ?_)
      fun _ _ _ _ h ↦ mkB_injective _ h) (hTcard l hl)
    exact (hS l Q).1 hQ
  have hex (l : ℕ) (hl : l < n) := hc (E l).w' (D (E l).w') (S l) (E l).Q' (hQ0 l hl)
    (le_trans (by have := hScard l hl; push_cast; omega) (hdeg (E l).w'))
  choose! f hfmem hfQ0 hfS using hex
  set tv : ℕ → piRR C F m := fun l ↦
    if hl : l < n then ⟨_, single_mem_piRR m (hfmem l hl)⟩ else 0
  have htv (l : ℕ) (hl : l < n) : (tv l).1 = Pi.single (E l).w' (f l) := by
    simp only [tv, dif_pos hl]
  have hzero (l : ℕ) (hl : l < n) (p) (hp : p ∈ T l) (τ : Π v : Ext C F,
      ResidueField v.1.valuationSubring)
      (hτ : p.2.valuation (τ p.1) = exp (-(m • poleDivisor 𝓀 (red C (xF C F) p.1)) p.2)) :
      p.2.res ((tv l).1 p.1 * τ p.1) = 0 := by
    rw [htv l hl]
    exact res_single_mul_eq_zero m (f l) p τ hτ fun Q hQ ↦
      hfS l hl Q ((hS l Q).2 (hQ ▸ hp))
  have hτ₁ (l : ℕ) : (E l).b₁.2.valuation (tau C F m (E l).chart (E l).b₁.1) =
      exp (-(m • poleDivisor 𝓀 (red C (xF C F) (E l).b₁.1)) (E l).b₁.2) :=
    valuation_tau m _ _ _ (E l).red_chart_mem_Q
  have hτ₂ (l : ℕ) : (E l).b₂.2.valuation (tau C F m (E l).chart (E l).b₂.1) =
      exp (-(m • poleDivisor 𝓀 (red C (xF C F) (E l).b₂.1)) (E l).b₂.2) :=
    valuation_tau m _ _ _ (E l).red_chart_mem_Q'
  have hcount := GraphCount.add_le_finrank_of_triangular (redSpan C F m) n
    (fun l ↦ (E l).φ m) tv (fun l _ a ha ↦ (E l).φ_eq_zero m ha) (fun l hl ↦ ?_)
    (fun l l' hll' hl' ↦ ?_)
  · rw [← finrank_piRR]
    refine le_trans (Nat.add_le_add_right ?_ _) hcount
    set W := (redSpan C F m).map (piRR C F m).subtype
    have hW : Module.finrank 𝓀 W = Module.finrank 𝓀 (redSpan C F m) :=
      (Submodule.equivMapOfInjective _ (Submodule.injective_subtype _) _).finrank_eq.symm
    rw [← hW]
    exact finrank_le_of_red_mem b hb (rrSpace (m • poleDivisor C (xF C F))) W
      fun f hf hn ↦ ⟨⟨_, fun w _ ↦ red_mem_rrSpace hb hf hn w⟩,
        Submodule.subset_span ⟨f, hf, hn, rfl⟩, rfl⟩
  · -- the diagonal: the new branch sees the test vector
    simp only [GEdge.φ_apply]
    have h1 := hzero l hl (E l).b₁ (Finset.mem_insert_self _ _) _ (hτ₁ l)
    simp only at h1
    rw [h1, zero_sub, neg_ne_zero, htv l hl, Pi.single_eq_same, Ne,
      CurvePlace.res_eq_zero_iff _ (mul_tau_mem m _ (E l).red_chart_mem_Q' (hfmem l hl)),
      map_mul, hfQ0 l hl]
    have := hτ₂ l
    simp only at this
    rw [this, ← exp_add, add_neg_cancel, exp_zero]
    exact lt_irrefl 1
  · -- earlier edges do not see the test vector
    have hmem (p) (hp : p = (E l).b₁ ∨ p = (E l).b₂) : p ∈ T l' := by
      refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨l, Finset.mem_range.2 hll', ?_⟩)
      rcases hp with rfl | rfl <;> simp
    simp only [GEdge.φ_apply]
    have h1 := hzero l' hl' (E l).b₁ (hmem _ (Or.inl rfl)) _ (hτ₁ l)
    have h2 := hzero l' hl' (E l).b₂ (hmem _ (Or.inr rfl)) _ (hτ₂ l)
    simp only at h1 h2
    rw [h1, h2, sub_zero]

omit hb in
/-- From a Riemann–Roch count `ℓ(m (x)_∞) + r ≤ Σ_w ℓ_{κ(w)}(m (x̄)_∞)` for `m ≫ 0` to the genus
inequality `Σ_w g(κ(w)) + r ≤ g(F) + #{w} - 1`. -/
theorem sum_genus_add_le_of_ell
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F) (r : ℕ)
    (h : ∃ M : ℕ, ∀ m, M ≤ m → ell (m • poleDivisor C (xF C F)) + r ≤
      ∑ w : Ext C F, ell (m • poleDivisor 𝓀 (red C (xF C F) w))) :
    (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) + r ≤
      genus C F + Fintype.card (Ext C F) - 1 := by
  classical
  obtain ⟨M, hM⟩ := h
  obtain ⟨cF, hcF⟩ := ell_eq_of_le_degree (k := C) (κ := F)
  choose cw hcw using fun w : Ext C F ↦
    ell_eq_of_le_degree (k := 𝓀) (κ := ResidueField w.1.valuationSubring)
  set N := Module.finrank (RatFunc C) F
  set m : ℕ := M + cF.toNat + ∑ w, (cw w).toNat
  have hN : 1 ≤ N := Module.finrank_pos
  have hdegF : (m • poleDivisor C (xF C F)).degree = m * N := by
    rw [map_nsmul, degree_poleDivisor xF_notMem_range, finrank_adjoin_xF, nsmul_eq_mul]
  have hfw (w : Ext C F) : 1 ≤ inertiaDeg (gauss1 C) w.1 := by
    haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := finite_residueField
    exact Module.finrank_pos
  have hdegw (w : Ext C F) : (m • poleDivisor 𝓀 (red C (xF C F) w)).degree =
      m * inertiaDeg (gauss1 C) w.1 := by
    rw [map_nsmul, degree_poleDivisor (red_xF_notMem_range w), finrank_adjoin_red_x,
      nsmul_eq_mul]
  have hsumpos : (0 : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) := Finset.sum_nonneg fun _ _ ↦ by positivity
  have hm1 : cF ≤ m := by
    have := Int.self_le_toNat cF
    push_cast [m]
    linarith [Int.natCast_nonneg M]
  have hmw (w : Ext C F) : cw w ≤ m := by
    have h1 := Int.self_le_toNat (cw w)
    have h2 : ((cw w).toNat : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) :=
      Finset.single_le_sum (f := fun w ↦ ((cw w).toNat : ℤ)) (fun _ _ ↦ by positivity)
        (Finset.mem_univ w)
    push_cast [m]
    linarith [Int.natCast_nonneg cF.toNat, Int.natCast_nonneg M]
  have hF := hcF _ (by
    rw [hdegF]
    nlinarith)
  have hw (w : Ext C F) := hcw w _ (by
    rw [hdegw]
    have := hfw w
    have : (m : ℤ) ≤ m * inertiaDeg (gauss1 C) w.1 := by
      exact_mod_cast Nat.le_mul_of_pos_right m this
    linarith [hmw w])
  have hle := hM m (by omega)
  have hle' : (ell (m • poleDivisor C (xF C F)) : ℤ) + r ≤
      ∑ w : Ext C F, (ell (m • poleDivisor 𝓀 (red C (xF C F) w)) : ℤ) := by
    exact_mod_cast hle
  rw [hF, hdegF] at hle'
  simp only [hw, hdegw] at hle'
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hle'
  have hsumZ : (∑ w : Ext C F, (inertiaDeg (gauss1 C) w.1 : ℤ)) = N := by
    exact_mod_cast hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hle'
  rw [hsumZ] at hle'
  linarith

/-- **The genus inequality with the first Betti number** over the Gauss point: for edges
`e₀, …, e_{n-1}` of the special fibre whose second branches are new, `Σ_w g(κ(w)) + n ≤ g(F) +
#{w} - 1`; for the `#E` nodes of a semistable fibre this reads `Σ_w g(κ(w)) + b₁(Γ) ≤ g(F)`. -/
theorem sum_genus_add_le
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F)
    (n : ℕ) (E : ℕ → GEdge C F) (hloop : ∀ l < n, (E l).b₂ ≠ (E l).b₁)
    (hnew : ∀ l' < n, ∀ l < l', (E l').b₂ ≠ (E l).b₁ ∧ (E l').b₂ ≠ (E l).b₂) :
    (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) + n ≤
      genus C F + Fintype.card (Ext C F) - 1 :=
  sum_genus_add_le_of_ell hsum n (exists_ell_add_le hb n E hloop hnew)

end Betti

end GaussFibre

end SemistableReduction
