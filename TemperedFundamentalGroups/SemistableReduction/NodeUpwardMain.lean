/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeUpward

/-!
# Upward closure of exhausting discs: the main step

Blueprint §9.10, L3, R4(i) (`isNodeODP_of_le`); see `NodeUpward`.
-/

open Polynomial WithZero
open scoped NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm TubeCount

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) F']

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- An inner branch of `P''` (on the inner vertex `w_{0,|c''|}` of `R''`) is centred at
`P' = P'' ∩ R'` in `R'`. -/
lemma inner_center {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1) (hc0' : c' ≠ 0)
    (hc0'' : c'' ≠ 0) (hlt : ‖c'‖ < ‖c''‖) (P'' : Ideal (Rint c'' F'))
    [(P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0''))).IsMaximal]
    (w : Ext C (Inv c'' hc0'' F'))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Inv c'' hc0'' F')) w))
    (hb : placeIdeal hc'' w hQ = P''.comap (rintEquiv hc0'').symm.toRingHom)
    (y : Rint c' F') :
    w.1 (toInv hc0'' (y : F')) < 1 ↔
      y ∈ P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0'')) := by
  set ι := rintMap (F' := F') (nodeRing_le hlt.le hc0'')
  set P' := P''.comap ι
  have hdir : ∀ y : Rint c' F', w.1 (toInv hc0'' (y : F')) < 1 → y ∈ P' := by
    intro y hy
    have hmem : rintEquiv hc0'' (ι y) ∈ placeIdeal hc'' w hQ := by
      rw [mem_placeIdeal_iff]
      have hle := valuation_le_one_R hc'' w (rintEquiv hc0'' (ι y))
      rw [coe_rintEquiv, coe_rintMap] at hle ⊢
      rw [(red_eq_zero_iff hle).2 hy, Q.res_zero]
    rw [hb, Ideal.mem_comap, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply] at hmem
    exact Ideal.mem_comap.2 hmem
  set s₀ : ℝ≥0ˣ := Units.mk0 ‖c''‖₊ (by simpa using hc0'')
  have hs₀ : s₀ ∈ segment c' := ⟨show ‖c'‖₊ < ‖c''‖₊ by rw [← NNReal.coe_lt_coe]; simpa using hlt,
    show ‖c''‖₊ < 1 by rw [← NNReal.coe_lt_coe]; simpa using hc''⟩
  have hrad : invRad hc0'' s₀ = 1 := by
    ext
    simp [coe_invRad, s₀, hc0'']
  let w₀ : GaussExtension (0 : C) s₀ F' :=
    ⟨w.1.comap (toInv hc0'').toRingHom, Valuation.ext fun φ ↦ by
      rw [Valuation.comap_apply, Valuation.comap_apply]
      have := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u (inv hc0'' φ)) w.2
      simp only [Valuation.comap_apply, algebraMap_inv_apply, inv_inv_apply] at this
      change w.1 (toInv hc0'' (algebraMap (RatFunc C) F' φ)) = _
      rw [this, ← hrad, ← gaussRat_inv hc0'' s₀, inv_inv_apply]⟩
  have hcen : center hs₀ w₀ = P' :=
    (center_isMaximal hc' hc0' hs₀ w₀).eq_of_le (Ideal.IsMaximal.ne_top inferInstance)
      fun y hy ↦ hdir y hy
  exact ⟨hdir y, fun hy ↦ by rw [← hcen] at hy; exact hy⟩

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- The vertex degree of a point with a single outer branch. -/
lemma vertexDegree_eq_ord_of_eq_singleton {c : C} (hc : ‖c‖ < 1) [Fintype (Ext C F')]
    {P : Ideal (Rint c F')} {b : OuterBranch C F'} (h : outerBranches hc P = {b}) :
    vertexDegree hc P = ord (red C (xF C F') b.1) b.2.1 := by
  classical
  have hmem : ∀ b' : OuterBranch C F', placeIdeal hc b'.1 b'.2.2 = P ↔ b' = b := fun b' ↦ by
    change b' ∈ outerBranches hc P ↔ _
    rw [h, Set.mem_singleton_iff]
  rw [vertexDegree_eq_sum, Finset.sum_eq_single_of_mem b
    (Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_attach _ _⟩)]
  · rw [if_pos ((hmem b).2 rfl)]
  · intro b' _ hne
    rw [if_neg fun h' ↦ hne ((hmem ⟨b'.1, b'.2⟩).1 h')]

include hp hp1 in
/-- Every point of `R'` over the node lies on an outer branch. -/
lemma exists_outerBranch {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0) (P : Ideal (Rint c F'))
    [P.IsMaximal] (hP : P.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c) :
    ∃ b : OuterBranch C F', placeIdeal hc b.1 b.2.2 = P := by
  classical
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have hc0' : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hr2 : ‖r‖ ^ 2 = ‖c‖ := by rw [← norm_pow, hr]
  have hr0 : 0 < ‖r‖ := by nlinarith [norm_nonneg r]
  have hr1 : ‖r‖ < 1 := by nlinarith [norm_nonneg r]
  have hrc : ‖c‖ < ‖r‖ := by nlinarith [norm_nonneg r]
  set s : ℝ≥0ˣ := Units.mk0 ‖r‖₊ (by simpa using hr0.ne')
  have hs : s ∈ segment c := ⟨show ‖c‖₊ < ‖r‖₊ by rw [← NNReal.coe_lt_coe]; simpa using hrc,
    show ‖r‖₊ < 1 by rw [← NNReal.coe_lt_coe]; simpa using hr1⟩
  have hcs : NormedField.valuation r = (s : ℝ≥0) := by simp [s, NormedField.valuation_apply]
  haveI : Finite (GaussExtension (0 : C) s F') := finite_gaussExtension 0 s
  letI : Fintype (GaussExtension (0 : C) s F') := Fintype.ofFinite _
  obtain ⟨w', hw'⟩ := exists_center_eq hp hp1 hc hc0 hs hcs P hP
  have htube_pos : 0 < tubeDegree hs P := by
    rw [tubeDegree]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ w', hw'⟩))
    exact Nat.mul_pos (Nat.pos_of_ne_zero (ramificationIdx_ne_zero w'.1))
      NormedTower.inertiaDeg_pos
  rw [tubeDegree_eq_vertexDegree hp hp1 hc hc0 hs hcs P, vertexDegree_eq_sum] at htube_pos
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero htube_pos.ne'
  by_cases h : placeIdeal hc b.1 b.2.2 = P
  · exact ⟨⟨b.1, b.2⟩, h⟩
  · rw [if_neg h] at hb
    exact absurd rfl hb

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- The outer branches of `P''` are those of `P' = P'' ∩ R'`. -/
lemma outerBranches_eq_singleton {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1)
    (hc0'' : c'' ≠ 0) (hlt : ‖c'‖ < ‖c''‖) {P'' : Ideal (Rint c'' F')} {P' : Ideal (Rint c' F')}
    (hP' : P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0'')) = P')
    {b₁ : OuterBranch C F'} (h₁ : outerBranches hc' P' = {b₁})
    (hex : ∃ b : OuterBranch C F', placeIdeal hc'' b.1 b.2.2 = P'') :
    outerBranches hc'' P'' = {b₁} := by
  have hsub : ∀ b : OuterBranch C F', placeIdeal hc'' b.1 b.2.2 = P'' → b = b₁ := by
    intro b hb
    have : b ∈ outerBranches hc' P' := by
      change placeIdeal hc' b.1 b.2.2 = P'
      ext y
      rw [mem_placeIdeal_iff, ← hP', Ideal.mem_comap, ← hb, mem_placeIdeal_iff, coe_rintMap]
    rw [h₁] at this
    exact this
  obtain ⟨b, hb⟩ := hex
  have hbb := hsub b hb
  subst hbb
  ext b'
  rw [Set.mem_singleton_iff]
  exact ⟨hsub b', fun h ↦ h ▸ hb⟩

include hp hp1 in
/-- The vertex degrees of a point over the node at the outer and at the inner vertex agree (both
are the tube degree, S6). -/
lemma vertexDegree_eq_vertexDegree_inv {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)
    [Fintype (Ext C F')] [Fintype (Ext C (Inv c hc0 F'))] (P : Ideal (Rint c F'))
    [P.IsMaximal] :
    vertexDegree hc P =
      vertexDegree (F' := Inv c hc0 F') hc (P.comap (rintEquiv hc0).symm.toRingHom) := by
  classical
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq c two_pos
  have hc0' : 0 < ‖c‖ := norm_pos_iff.2 hc0
  have hr2 : ‖r‖ ^ 2 = ‖c‖ := by rw [← norm_pow, hr]
  have hr0 : 0 < ‖r‖ := by nlinarith [norm_nonneg r]
  have hr1 : ‖r‖ < 1 := by nlinarith [norm_nonneg r]
  have hrc : ‖c‖ < ‖r‖ := by nlinarith [norm_nonneg r]
  set s : ℝ≥0ˣ := Units.mk0 ‖r‖₊ (by simpa using hr0.ne')
  have hs : s ∈ segment c := ⟨show ‖c‖₊ < ‖r‖₊ by rw [← NNReal.coe_lt_coe]; simpa using hrc,
    show ‖r‖₊ < 1 by rw [← NNReal.coe_lt_coe]; simpa using hr1⟩
  have hcs : NormedField.valuation r = (s : ℝ≥0) := by simp [s, NormedField.valuation_apply]
  haveI : Finite (GaussExtension (0 : C) s F') := finite_gaussExtension 0 s
  letI : Fintype (GaussExtension (0 : C) s F') := Fintype.ofFinite _
  rw [← tubeDegree_eq_vertexDegree hp hp1 hc hc0 hs hcs P,
    tubeDegree_eq_vertexDegree_inv hc0 hp hp1 hc hs hcs P]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F'] [CharZero C]
  [Algebra.IsSeparable (RatFunc C) F'] in
omit [IsUltrametricDist C] [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- The coordinate of the inversion is `c/x`. -/
lemma xF_inv {c : C} (hc0 : c ≠ 0) :
    xF C (Inv c hc0 F') =
      toInv hc0 (algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) c / RatFunc.X)) := by
  change toInv hc0 (algebraMap (RatFunc C) F' (inv hc0 RatFunc.X)) = _
  rw [inv_apply, invHom_X]

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- The key identity `(c''/x) · e = σ · v₀^d`, `v₀ = (κ/γ) v`, `κ^d = c''`. -/
lemma NodeData.key {c c'' : C} {hc : ‖c‖ < 1} {P' : Ideal (Rint c F')} {b₁ : OuterBranch C F'}
    (N : NodeData hc P' b₁) {κ : C} (hκ : κ ^ N.d = c'') :
    algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) c'' / RatFunc.X) * (N.e : F') =
      (N.σ : F') * (algebraMap C F' (κ / N.γ) * N.v) ^ N.d := by
  have hX : xF C F' ≠ 0 := by
    simp only [xF, ne_eq, map_eq_zero]
    exact RatFunc.X_ne_zero
  have hγ : algebraMap C F' N.γ ≠ 0 := by simpa using N.γ_ne_zero
  have hu : N.u ≠ 0 := by
    intro hu
    have := N.mul_eq
    rw [hu, zero_mul] at this
    exact hγ this.symm
  have hv : N.v = algebraMap C F' N.γ / N.u := by
    rw [eq_div_iff hu, mul_comm, N.mul_eq]
  have hxe := N.x_eq
  rw [map_div₀, ← IsScalarTower.algebraMap_apply]
  change algebraMap C F' c'' / xF C F' * (N.e : F') = _
  rw [hv, map_div₀, ← hκ, map_pow, div_mul_eq_mul_div, div_eq_iff hX, mul_pow, div_pow, div_pow,
    div_mul_div_cancel₀ (pow_ne_zero _ hγ)]
  have hud : N.u ^ N.d ≠ 0 := pow_ne_zero _ hu
  field_simp
  linear_combination (-(algebraMap C F' κ ^ N.d)) * hxe

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- At an inner branch of `P''`, elements of `R' ∖ P'` are residue-units. -/
lemma inner_unit {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1) (hc0' : c' ≠ 0)
    (hc0'' : c'' ≠ 0) (hlt : ‖c'‖ < ‖c''‖) {P'' : Ideal (Rint c'' F')}
    {P' : Ideal (Rint c' F')} [P'.IsMaximal]
    (hP' : P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0'')) = P')
    {b₁ : OuterBranch C F'} (hP₁ : placeIdeal hc' b₁.1 b₁.2.2 = P')
    (w : Ext C (Inv c'' hc0'' F'))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Inv c'' hc0'' F')) w))
    (hb : placeIdeal hc'' w hQ = P''.comap (rintEquiv hc0'').symm.toRingHom)
    {y : Rint c' F'} (hy : y ∉ P') :
    w.1 (toInv hc0'' (y : F')) = 1 ∧ Q.valuation (red C (toInv hc0'' (y : F')) w) = 1 := by
  haveI : (P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0''))).IsMaximal := hP' ▸ ‹_›
  have hcen := fun z ↦ (inner_center hc' hc'' hc0' hc0'' hlt P'' w hQ hb z).trans
    (by rw [hP'])
  obtain ⟨κ, hκ⟩ := exists_sub_constR_mem hc' b₁ y
  rw [hP₁] at hκ
  have hsub : toInv hc0'' ((y - constR c' κ : Rint c' F') : F') =
      toInv hc0'' (y : F') - algebraMap C (Inv c'' hc0'' F') (κ : C) := by
    have hconst : ((constR c' κ : Rint c' F') : F') = algebraMap C F' (κ : C) := by
      change algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) κ) = _
      rw [← IsScalarTower.algebraMap_apply]
    rw [Subalgebra.coe_sub, map_sub, hconst]
    rfl
  have h1 : w.1 (toInv hc0'' (y : F') - algebraMap C (Inv c'' hc0'' F') (κ : C)) < 1 := by
    rw [← hsub]
    exact (hcen _).2 hκ
  have hκ1 : ‖(κ : C)‖₊ = 1 := by
    refine le_antisymm (by exact_mod_cast (HenselComplete.mem_integers_iff _).1 κ.2) ?_
    by_contra! hlt1
    apply hy
    refine (hcen y).1 ?_
    have h2 : w.1 (algebraMap C (Inv c'' hc0'' F') (κ : C)) < 1 := by
      rw [valuation_algebraMap_C']
      exact hlt1
    have : toInv hc0'' (y : F') = (toInv hc0'' (y : F') - algebraMap C (Inv c'' hc0'' F') κ) +
        algebraMap C (Inv c'' hc0'' F') κ := by ring
    rw [this]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt h1 h2)
  exact val_and_Qval_eq_one w Q hκ1 h1

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- **The inner branches of `P''`.** At an inner branch `(w, Q)` of `P''`, the inner coordinate
`c''/x` reduces to `λ v̄₀^d` with `v₀ = (κ/γ) v`, so `ord_Q (c''/x)‾ = d m` with
`Q(v̄₀) = exp(-m)`, `m ≥ 1`. -/
lemma inner_ord {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1) (hc0' : c' ≠ 0)
    (hc0'' : c'' ≠ 0) (hlt : ‖c'‖ < ‖c''‖) {P'' : Ideal (Rint c'' F')}
    {P' : Ideal (Rint c' F')} [P'.IsMaximal]
    (hP' : P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0'')) = P')
    {b₁ : OuterBranch C F'} (hP₁ : placeIdeal hc' b₁.1 b₁.2.2 = P') (N : NodeData hc' P' b₁)
    {κ : C} (hκ : κ ^ N.d = c'') (w : Ext C (Inv c'' hc0'' F'))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Inv c'' hc0'' F')) w))
    (hb : placeIdeal hc'' w hQ = P''.comap (rintEquiv hc0'').symm.toRingHom) :
    w.1 (toInv hc0'' (algebraMap C F' (κ / N.γ) * N.v)) = 1 ∧
      ∃ m : ℕ, 1 ≤ m ∧
        Q.valuation (red C (toInv hc0'' (algebraMap C F' (κ / N.γ) * N.v)) w) =
          exp (-(m : ℤ)) ∧ ord (red C (xF C (Inv c'' hc0'' F')) w) Q = N.d * m := by
  set V := toInv hc0'' (algebraMap C F' (κ / N.γ) * N.v)
  have hd0 : N.d ≠ 0 := by have := N.one_le_d; omega
  obtain ⟨hσ1, hσQ⟩ := inner_unit hc' hc'' hc0' hc0'' hlt hP' hP₁ w hQ hb N.σ_notMem
  obtain ⟨he1, heQ⟩ := inner_unit hc' hc'' hc0' hc0'' hlt hP' hP₁ w hQ hb N.e_notMem
  have hkey : xF C (Inv c'' hc0'' F') * toInv hc0'' (N.e : F') =
      toInv hc0'' (N.σ : F') * V ^ N.d := by
    rw [xF_inv, ← map_mul, N.key hκ, map_mul, map_pow]
  have hA : w.1 (xF C (Inv c'' hc0'' F')) = 1 := valuation_xF w
  have hV : w.1 V = 1 := by
    have h := congrArg w.1 hkey
    rw [map_mul, map_mul, map_pow, hA, he1, hσ1, one_mul, one_mul] at h
    rcases lt_trichotomy (w.1 V) 1 with hlt' | heq | hgt
    · exact absurd h.symm (pow_lt_one₀ zero_le hlt' hd0).ne
    · exact heq
    · exact absurd h.symm (one_lt_pow₀ hgt hd0).ne'
  refine ⟨hV, ?_⟩
  have hred : red C (xF C (Inv c'' hc0'' F')) w * red C (toInv hc0'' (N.e : F')) w =
      red C (toInv hc0'' (N.σ : F')) w * red C V w ^ N.d := by
    rw [← red_mul hA.le he1.le, hkey, red_mul hσ1.le (by rw [map_pow, hV, one_pow]),
      red_pow hV.le]
  have hQv := congrArg Q.valuation hred
  rw [map_mul, map_mul, map_pow, heQ, hσQ, mul_one, one_mul, valuation_x hQ] at hQv
  -- `v̄₀ ∈ O_Q` and nonzero
  have hVle : Q.valuation (red C V w) ≤ 1 := by
    by_contra! hgt
    have := one_lt_pow₀ hgt hd0
    rw [← hQv] at this
    exact absurd this (not_lt.2 (by rw [← exp_zero, exp_le_exp]; omega))
  have hV0 : red C V w ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_pow hd0] at hQv
    exact exp_ne_zero hQv
  obtain ⟨m, hm⟩ := ConductorLocal.valuation_le_exp_of_ne_zero Q hV0
    (Q.valuation_le_one_iff.1 hVle)
  rw [hm, ← exp_nsmul] at hQv
  have hord := exp_injective hQv
  simp only [nsmul_eq_mul, mul_neg] at hord
  have hord' : ord (red C (xF C (Inv c'' hc0'' F')) w) Q = N.d * m := by
    have : (ord (red C (xF C (Inv c'' hc0'' F')) w) Q : ℤ) = (N.d : ℤ) * m := by linarith
    exact_mod_cast this
  have h1 := one_le_ord hQ
  refine ⟨m, ?_, hm, hord'⟩
  by_contra! hm0
  interval_cases m
  rw [mul_zero] at hord'
  omega

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- Multiplying by residue-units does not change the residue-valuation at an inner branch. -/
lemma inner_param {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1) (hc0' : c' ≠ 0)
    (hc0'' : c'' ≠ 0) (hlt : ‖c'‖ < ‖c''‖) {P'' : Ideal (Rint c'' F')}
    {P' : Ideal (Rint c' F')} [P'.IsMaximal]
    (hP' : P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0'')) = P')
    {b₁ : OuterBranch C F'} (hP₁ : placeIdeal hc' b₁.1 b₁.2.2 = P')
    (w : Ext C (Inv c'' hc0'' F'))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Inv c'' hc0'' F')) w))
    (hb : placeIdeal hc'' w hQ = P''.comap (rintEquiv hc0'').symm.toRingHom)
    {y₁ y₂ : Rint c' F'} (hy₁ : y₁ ∉ P') (hy₂ : y₂ ∉ P') {z : F'}
    (hz : w.1 (toInv hc0'' z) = 1) :
    Q.valuation (red C (toInv hc0'' ((y₁ : F') * (y₂ : F') * z)) w) =
      Q.valuation (red C (toInv hc0'' z) w) := by
  obtain ⟨h₁, hQ₁⟩ := inner_unit hc' hc'' hc0' hc0'' hlt hP' hP₁ w hQ hb hy₁
  obtain ⟨h₂, hQ₂⟩ := inner_unit hc' hc'' hc0' hc0'' hlt hP' hP₁ w hQ hb hy₂
  have e : toInv hc0'' ((y₁ : F') * (y₂ : F') * z) =
      toInv hc0'' (y₁ : F') * toInv hc0'' (y₂ : F') * toInv hc0'' z := by
    rw [map_mul, map_mul]
  have hw12 : w.1 (toInv hc0'' (y₁ : F') * toInv hc0'' (y₂ : F')) ≤ 1 := by
    rw [map_mul, h₁, h₂, one_mul]
  rw [e, red_mul hw12 hz.le, red_mul h₁.le h₂.le, map_mul, map_mul, hQ₁, hQ₂, one_mul, one_mul]

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- At an inner branch of `P''`, elements of `P'` are small. -/
lemma inner_lt_one {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1) (hc0' : c' ≠ 0)
    (hc0'' : c'' ≠ 0) (hlt : ‖c'‖ < ‖c''‖) {P'' : Ideal (Rint c'' F')}
    {P' : Ideal (Rint c' F')} [P'.IsMaximal]
    (hP' : P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0'')) = P')
    (w : Ext C (Inv c'' hc0'' F'))
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField w.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C (Inv c'' hc0'' F')) w))
    (hb : placeIdeal hc'' w hQ = P''.comap (rintEquiv hc0'').symm.toRingHom)
    {y : Rint c' F'} (hy : y ∈ P') : w.1 (toInv hc0'' (y : F')) < 1 := by
  haveI : (P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0''))).IsMaximal := hP' ▸ ‹_›
  exact (inner_center hc' hc'' hc0' hc0'' hlt P'' w hQ hb y).2 (hP' ▸ hy)

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] in
/-- The inner parameter is small at the outer vertex. -/
lemma outer_param {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1) {P' : Ideal (Rint c' F')}
    {b₁ : OuterBranch C F'} (hP₁ : placeIdeal hc' b₁.1 b₁.2.2 = P') (N : NodeData hc' P' b₁)
    {κ : C} (hκ : κ ^ N.d = c'') :
    b₁.1.1 ((N.σ : F') * (N.σv : F') * (algebraMap C F' (κ / N.γ) * N.v)) < 1 := by
  have hγ0 : (N.γ : C) ≠ 0 := N.γ_ne_zero
  have hv : b₁.1.1 N.v = ‖N.γ‖₊ := by
    have h := congrArg b₁.1.1 N.mul_eq
    rw [map_mul, N.val_u hc' hP₁, one_mul, valuation_algebraMap_C'] at h
    exact h
  simp only [map_mul, valuation_algebraMap_C', val_one_of_notMem hc' hP₁ N.σ_notMem,
    val_one_of_notMem hc' hP₁ N.σv_notMem, one_mul, hv, nnnorm_div]
  rw [div_mul_cancel₀ _ (nnnorm_ne_zero_iff.2 hγ0)]
  have hκn : ‖κ‖₊ ^ N.d = ‖c''‖₊ := by rw [← nnnorm_pow, hκ]
  have hc''1 : ‖c''‖₊ < 1 := by rw [← NNReal.coe_lt_coe]; simpa using hc''
  by_contra! hge
  have := one_le_pow₀ (n := N.d) hge
  rw [hκn] at this
  exact absurd hc''1 (not_lt.2 this)

include hp hp1 in
/-- **R4(i): upward closure** ([AW, Lemma `BLlem` (i)], valuative form over `C`). Let
`|c'| < |c''| < 1`, `P''` a point of `R'' = Rint c'' F'` over the node, and `P' = P'' ∩ R'` its
image in `R' = Rint c' F'`. If `P'` has exactly one outer branch `b₁` and exact node data
(`NodeData`, the interim hypothesis of §9.10 L3 (a1)), then `P''` is an ordinary double point:
its outer branch is `b₁`, its unique inner branch lies on the unique extension of `w_{0,|c''|}`
centred at `P'`, and `σ_u u`, `σ σ_v (κ/γ) v` (`κ^d = c''`) are parameters of the two branches. -/
theorem isNodeODP_of_le {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1) (hc0' : c' ≠ 0)
    (hc0'' : c'' ≠ 0) (hlt : ‖c'‖ < ‖c''‖) (P'' : Ideal (Rint c'' F')) [P''.IsMaximal]
    (hP'' : P''.comap (algebraMap (nodeRing c'') (Rint c'' F')) = tubeIdeal c'')
    {P' : Ideal (Rint c' F')}
    (hP' : P''.comap (rintMap (F' := F') (nodeRing_le hlt.le hc0'')) = P')
    {b₁ : OuterBranch C F'} (h₁ : outerBranches hc' P' = {b₁}) (N : NodeData hc' P' b₁) :
    IsNodeODP hc'' hc0'' P'' := by
  classical
  have hP₁ : placeIdeal hc' b₁.1 b₁.2.2 = P' := by
    have : b₁ ∈ outerBranches hc' P' := by rw [h₁]; exact Set.mem_singleton b₁
    exact this
  haveI : P'.IsMaximal := hP₁ ▸ placeIdeal_isMaximal hc' b₁.1 b₁.2.2
  haveI : Finite (Ext C F') := finite_ext (F := F') hp hp1
  letI : Fintype (Ext C F') := Fintype.ofFinite _
  haveI : Finite (Ext C (Inv c'' hc0'' F')) := finite_ext (F := Inv c'' hc0'' F') hp hp1
  letI : Fintype (Ext C (Inv c'' hc0'' F')) := Fintype.ofFinite _
  -- the outer side
  have h₁'' : outerBranches hc'' P'' = {b₁} := outerBranches_eq_singleton hc' hc'' hc0'' hlt hP'
    h₁ (exists_outerBranch hp hp1 hc'' hc0'' P'' hP'')
  have hvdeg : vertexDegree hc'' P'' = N.d := by
    rw [vertexDegree_eq_ord_of_eq_singleton hc'' h₁'']
    exact N.ord_x hc' hP₁
  -- the inner side
  set P''i := P''.comap (rintEquiv hc0'').symm.toRingHom with hP''i
  have hvdi : vertexDegree (F' := Inv c'' hc0'' F') hc'' P''i = N.d := by
    rw [← vertexDegree_eq_vertexDegree_inv hp hp1 hc'' hc0'' P'', hvdeg]
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq c'' N.one_le_d
  rw [vertexDegree_eq_sum] at hvdi
  obtain ⟨b₂, -, hb₂, hoth⟩ := exists_unique_of_sum_eq _ _ N.one_le_d (fun b _ ↦ by
    by_cases h : placeIdeal hc'' b.1 b.2.2 = P''i
    · right
      rw [if_pos h]
      obtain ⟨-, m, hm1, -, hord⟩ := inner_ord hc' hc'' hc0' hc0'' hlt hP' hP₁ N hκ b.1 b.2.2 h
      rw [hord]
      exact Nat.le_mul_of_pos_right _ hm1
    · left
      rw [if_neg h]) hvdi
  have hb₂P : placeIdeal hc'' b₂.1 b₂.2.2 = P''i := by
    by_contra h
    rw [if_neg h] at hb₂
    exact absurd hb₂.symm (by have := N.one_le_d; omega)
  rw [if_pos hb₂P] at hb₂
  have h₂'' : innerBranches hc'' hc0'' P'' = {b₂} := by
    ext b
    rw [Set.mem_singleton_iff]
    constructor
    · intro hb
      by_contra hne
      have hb' : placeIdeal hc'' b.1 b.2.2 = P''i := hb
      have := hoth b (Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_attach _ _⟩) hne
      rw [if_pos hb'] at this
      have h1 := one_le_ord b.2.2
      omega
    · rintro rfl
      exact hb₂P
  -- the parameters
  obtain ⟨hV1, m, hm1, hmV, hord⟩ :=
    inner_ord hc' hc'' hc0' hc0'' hlt hP' hP₁ N hκ b₂.1 b₂.2.2 hb₂P
  have hm : m = 1 := by
    rw [hord] at hb₂
    have := N.one_le_d
    nlinarith
  rw [hm, Nat.cast_one] at hmV
  have hpow : ((N.σ : F') * (N.σv : F') * (algebraMap C F' (κ / N.γ) * N.v)) ^ N.d =
      (N.σ : F') ^ (N.d - 1) * (N.σv : F') ^ N.d * (N.e : F') *
        algebraMap (RatFunc C) F' (algebraMap C (RatFunc C) c'' / RatFunc.X) := by
    have hk := N.key hκ
    have hd1 : N.d = N.d - 1 + 1 := by have := N.one_le_d; omega
    rw [mul_pow, mul_pow]
    conv_lhs => rw [hd1, pow_succ]
    rw [← hd1]
    linear_combination ((N.σ : F') ^ (N.d - 1) * (N.σv : F') ^ N.d) * hk.symm
  have hzint : IsIntegral (nodeRing c'')
      ((N.σ : F') * (N.σv : F') * (algebraMap C F' (κ / N.γ) * N.v)) := by
    have hint (y : Rint c' F') : IsIntegral (nodeRing c'') (y : F') :=
      isIntegral_of_nodeRing_le (nodeRing_le hlt.le hc0'') y.2
    refine IsIntegral.of_pow (n := N.d) (by have := N.one_le_d; omega) ?_
    rw [hpow]
    refine ((((hint N.σ).pow _).mul ((hint N.σv).pow _)).mul (hint N.e)).mul ?_
    exact isIntegral_algebraMap (x := (⟨_, div_X_mem_nodeRing c''⟩ : nodeRing c''))
  obtain ⟨zR, hzR⟩ : ∃ zR : Rint c'' F',
      (zR : F') = (N.σ : F') * (N.σv : F') * (algebraMap C F' (κ / N.γ) * N.v) :=
    ⟨⟨_, hzint⟩, rfl⟩
  have hσv1 := inner_unit hc' hc'' hc0' hc0'' hlt hP' hP₁ b₂.1 b₂.2.2 hb₂P N.σv_notMem
  have hσ1 := inner_unit hc' hc'' hc0' hc0'' hlt hP' hP₁ b₂.1 b₂.2.2 hb₂P N.σ_notMem
  have hv₂ : b₂.2.1.valuation (redHomInv hc'' hc0'' b₂.1 zR) = exp (-1) := by
    rw [redHomInv_apply, hzR, inner_param hc' hc'' hc0' hc0'' hlt hP' hP₁ b₂.1 b₂.2.2 hb₂P
      N.σ_notMem N.σv_notMem hV1]
    exact hmV
  refine isNodeODP_of_params hc'' hc0'' hp hp1 h₁'' h₂''
    (u' := rintMap (nodeRing_le hlt.le hc0'') N.uR) (v' := zR) ?_ ?_ ?_ hv₂
  · -- `σ_u u` is a uniformizer at the outer branch
    rw [redHom_rintMap hc' hc'']
    exact N.uR_val
  · -- `σ_u u` vanishes on the inner branch
    have hlt0 : b₁.2.1.valuation (redHom hc' b₁.1 N.uR) < 1 := by
      rw [N.uR_val, ← exp_zero, exp_lt_exp]
      omega
    have huR' : N.uR ∈ placeIdeal hc' b₁.1 b₁.2.2 :=
      (mem_placeIdeal_iff hc' b₁.1 b₁.2.2 N.uR).2 (b₁.2.1.res_eq_zero_of_lt_one hlt0)
    have huR : N.uR ∈ P' := (congrArg (fun I ↦ N.uR ∈ I) hP₁).mp huR'
    have hlt1 := inner_lt_one hc' hc'' hc0' hc0'' hlt hP' b₂.1 b₂.2.2 hb₂P huR
    exact (redHomInv_rintMap hc'' hc0'' _ b₂.1 N.uR).trans ((red_eq_zero_iff hlt1.le).2 hlt1)
  · -- `z` vanishes on the outer branch
    have h : b₁.1.1 (zR : F') < 1 :=
      (congrArg (fun z ↦ b₁.1.1 z < 1) hzR).mpr (outer_param hc' hc'' hP₁ N hκ)
    exact (red_eq_zero_iff (valuation_le_one_R hc'' b₁.1 zR)).2 h

end GaussTube

end SemistableReduction
