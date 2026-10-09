/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Exhausting

/-!
# Upward closure of exhausting discs

Blueprint §9.10, L3, R4(i). Let `|c'| < |c''| < 1` and `R' = Rint c' F' ⊆ R'' = Rint c'' F'` the
integral closures of the node charts `O_C[x, c'/x] ⊆ O_C[x, c''/x]` (the annulus
`|c''| < |x| < 1` is a sub-annulus of `|c'| < |x| < 1`).

* `nodeRing_le`, `rintMap`: the inclusion `R' → R''`;
* `exists_center_eq`: every maximal ideal over the node is the centre of an extension of every
  Gauss point of the open segment (positive tube degree, Cayley–Hamilton);
* `NodeData`: **exact node data** at a point `P'` of `R'` over the node: `u, v ∈ F'` with
  `u v = γ ∈ C`, `σ x = e u^d` (`σ, e ∈ R' ∖ P'`), `σ_u u, σ_v v ∈ R'` (`σ_u, σ_v ∉ P'`) and
  `σ_u u` reducing to a uniformizer at the outer branch. This is an *interim hypothesis*: it is
  produced from `IsNodeODP` by descent to a DVR and the node deformation (§9.10 L3 (a1), open);
* **`isNodeODP_of_le`** (R4(i)): if `P'` is an ordinary double point with exact node data, then
  every point `P''` of `R''` over the node lying over `P'` is an ordinary double point.
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

/-! ### The inclusion of node charts -/

section Le

variable {c' c'' : C}

omit [IsAlgClosed C] in
lemma nodeRing_le (h : ‖c'‖ ≤ ‖c''‖) (hc'' : c'' ≠ 0) : nodeRing c' ≤ nodeRing c'' := by
  refine Subring.closure_le.2 ?_
  rintro z (hz | hz)
  · exact Subring.subset_closure (Or.inl hz)
  · rcases hz with rfl | hz
    · exact X_mem_nodeRing c''
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      have hX : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
      have hc : algebraMap C (RatFunc C) c'' ≠ 0 := by simpa using hc''
      have : algebraMap C (RatFunc C) c' / RatFunc.X = algebraMap C (RatFunc C) (c' / c'') *
          (algebraMap C (RatFunc C) c'' / RatFunc.X) := by
        rw [map_div₀]
        field_simp
      rw [this]
      refine mul_mem (algebraMap_mem_nodeRing ?_) (div_X_mem_nodeRing c'')
      rw [norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
lemma isIntegral_of_nodeRing_le (hle : nodeRing c' ≤ nodeRing c'') {y : F'}
    (hy : IsIntegral (nodeRing c') y) : IsIntegral (nodeRing c'') y := by
  obtain ⟨p, hm, hp⟩ := hy
  refine ⟨p.map (Subring.inclusion hle), hm.map _, ?_⟩
  rw [Polynomial.eval₂_map]
  exact hp

/-- The inclusion `R' = Rint c' F' → R'' = Rint c'' F'`. -/
noncomputable def rintMap (hle : nodeRing c' ≤ nodeRing c'') : Rint c' F' →+* Rint c'' F' where
  toFun y := ⟨y, isIntegral_of_nodeRing_le hle y.2⟩
  map_one' := Subtype.ext (show ((1 : Rint c' F') : F') = 1 from rfl)
  map_mul' x y := Subtype.ext (show ((x * y : Rint c' F') : F') = (x : F') * (y : F') from rfl)
  map_zero' := Subtype.ext (show ((0 : Rint c' F') : F') = 0 from rfl)
  map_add' x y := Subtype.ext (show ((x + y : Rint c' F') : F') = (x : F') + (y : F') from rfl)

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
@[simp]
lemma coe_rintMap (hle : nodeRing c' ≤ nodeRing c'') (y : Rint c' F') :
    ((rintMap hle y : Rint c'' F') : F') = y :=
  Subtype.coe_mk (p := (· ∈ Rint c'' F')) _ _

end Le

omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] [IsAlgClosed C]
  [FiniteDimensional (RatFunc C) F'] in
@[simp]
lemma coe_rintEquiv {c : C} (hc0 : c ≠ 0) (y : Rint c F') :
    ((rintEquiv hc0 y : Rint c (Inv c hc0 F')) : Inv c hc0 F') = toInv hc0 (y : F') :=
  Subtype.coe_mk (p := (· ∈ Rint c (Inv c hc0 F'))) _ _

lemma redHom_rintMap {c' c'' : C} (hc' : ‖c'‖ < 1) (hc'' : ‖c''‖ < 1)
    (hle : nodeRing c' ≤ nodeRing c'') (v : Ext C F') (y : Rint c' F') :
    redHom hc'' v (rintMap hle y) = redHom hc' v y := by
  rw [redHom_apply, redHom_apply, coe_rintMap]

lemma redHomInv_apply {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0) (w : Ext C (Inv c hc0 F'))
    (y : Rint c F') : redHomInv hc hc0 w y = red C (toInv hc0 (y : F')) w := by
  rw [← coe_rintEquiv hc0 y, ← redHom_apply hc]
  rfl

lemma redHomInv_rintMap {c' c'' : C} (hc'' : ‖c''‖ < 1) (hc0'' : c'' ≠ 0)
    (hle : nodeRing c' ≤ nodeRing c'') (w : Ext C (Inv c'' hc0'' F')) (y : Rint c' F') :
    redHomInv hc'' hc0'' w (rintMap hle y) = red C (toInv hc0'' (y : F')) w := by
  rw [redHomInv_apply, coe_rintMap]

/-! ### Every point over the node is a centre -/

section Pos

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) F']

include hp hp1 in
omit [Algebra C F'] [IsScalarTower C (RatFunc C) F'] in
/-- **Every maximal ideal of `R'` over the node is a centre**: for every radius `s` of the open
segment, some extension of `w_{0,s}` is centred at it (its tube degree is positive: the
constant term of the characteristic polynomial of an element of `P'` outside the other centres
lies in the node ideal, Cayley–Hamilton). -/
theorem exists_center_eq {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0) {s : ℝ≥0ˣ}
    (hs : s ∈ segment c) {cs : C} (hcs : NormedField.valuation cs = (s : ℝ≥0))
    [Finite (GaussExtension (0 : C) s F')] (P' : Ideal (Rint c F')) [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c) :
    ∃ w' : GaussExtension (0 : C) s F', center hs w' = P' := by
  classical
  letI : Fintype (GaussExtension (0 : C) s F') := Fintype.ofFinite _
  set T : Finset (Ideal (Rint c F')) := (Finset.univ.image (center hs)).erase P'
  obtain ⟨e, he1, heQ⟩ := exists_separating P' T fun Q hQ ↦ by
    obtain ⟨hne, hQ⟩ := Finset.mem_erase.1 hQ
    obtain ⟨w', -, rfl⟩ := Finset.mem_image.1 hQ
    exact ⟨center_isMaximal hc hc0 hs w', hne⟩
  set f : Rint c F' := 1 - e
  have hfP : f ∈ P' := by
    have := P'.neg_mem he1
    rwa [neg_sub] at this
  obtain ⟨P, hP⟩ := exists_lift_normPoly hc0 hc.le f.2
  have hfilter : ∀ w' : GaussExtension (0 : C) s F', w'.1 (f : F') < 1 ↔ center hs w' = P' := by
    intro w'
    constructor
    · intro hlt
      by_contra hne
      have he : w'.1 (e : F') < 1 := (mem_center_iff hs w' e).1
        (heQ _ (Finset.mem_erase.2 ⟨hne, Finset.mem_image_of_mem _ (Finset.mem_univ w')⟩))
      have : w'.1 (f : F') = 1 := by
        rw [show (f : F') = 1 + -(e : F') by simp [f]; ring,
          Valuation.map_add_eq_of_lt_left _ (by rw [Valuation.map_neg, map_one]; exact he),
          map_one]
      exact lt_irrefl 1 (this ▸ hlt)
    · intro h
      rw [← mem_center_iff hs w', h]
      exact hfP
  have hcount := sum_ramificationIdx_mul_inertiaDeg_eq hp hp1 hcs hs (f : F') P hP
    fun w' ↦ valuation_le_one_of_isIntegral hs w' f.2
  -- the constant term of `P` lies in the node ideal
  have hPmonic : P.Monic := by
    have hm := monic_normPoly (F := RatFunc C) (f : F')
    rw [← hP] at hm
    exact monic_of_injective (nodeRing c).subtype_injective hm
  have h0 : P.coeff 0 ∈ tubeIdeal c := by
    rw [← hP', Ideal.mem_comap]
    have hroot : aeval f P = 0 := by
      apply Subtype.val_injective
      change (Rint c F').val (aeval f P) = 0
      rw [← aeval_algHom_apply, aeval_def, show algebraMap (nodeRing c) F' =
        (algebraMap (RatFunc C) F').comp (nodeRing c).subtype from rfl, ← eval₂_map, hP,
        ← aeval_def, normPoly, map_pow]
      change aeval (f : F') (minpoly (RatFunc C) (f : F')) ^ _ = 0
      rw [minpoly.aeval, zero_pow Module.finrank_pos.ne']
    have hdecomp := congrArg (aeval f) (X_mul_divX_add P)
    rw [map_add, map_mul, aeval_X, aeval_C, hroot] at hdecomp
    have : algebraMap (nodeRing c) (Rint c F') (P.coeff 0) = -(f * aeval f P.divX) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact hdecomp
    rw [this]
    exact P'.neg_mem (P'.mul_mem_right _ hfP)
  have hne : P.map (Ideal.Quotient.mk (tubeIdeal c)) ≠ 0 :=
    (hPmonic.map _).ne_zero_of_ne (by
      haveI := tubeIdeal_isMaximal hc hc0
      exact zero_ne_one)
  have hpos : 0 < (P.map (Ideal.Quotient.mk (tubeIdeal c))).natTrailingDegree := by
    refine Nat.pos_of_ne_zero fun h ↦ ?_
    rw [natTrailingDegree_eq_zero] at h
    rcases h with h | h
    · exact hne h
    · exact h (by rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem]; exact h0)
  rw [← hcount] at hpos
  obtain ⟨w', hw', -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
  exact ⟨w', (hfilter w').1 (Finset.mem_filter.1 hw').2⟩

end Pos

/-! ### Helpers on branches and points -/

section Helpers

/-- A sum of naturals each `0` or `≥ d` with total `d ≥ 1` has exactly one nonzero term, equal
to `d`. -/
lemma exists_unique_of_sum_eq {ι : Type*} (S : Finset ι) (g : ι → ℕ) {d : ℕ} (hd : 1 ≤ d)
    (hg : ∀ i ∈ S, g i = 0 ∨ d ≤ g i) (hsum : ∑ i ∈ S, g i = d) :
    ∃ i ∈ S, g i = d ∧ ∀ j ∈ S, j ≠ i → g j = 0 := by
  classical
  obtain ⟨i, hi, hi0⟩ : ∃ i ∈ S, g i ≠ 0 := by
    by_contra! h
    rw [Finset.sum_eq_zero h] at hsum
    omega
  have hgi : d ≤ g i := (hg i hi).resolve_left hi0
  have hle : g i + ∑ j ∈ S.erase i, g j = d := by rw [Finset.add_sum_erase _ _ hi, hsum]
  refine ⟨i, hi, by omega, fun j hj hji ↦ ?_⟩
  have : ∑ j ∈ S.erase i, g j = 0 := by omega
  exact (Finset.sum_eq_zero_iff.1 this) j (Finset.mem_erase.2 ⟨hji, hj⟩)

variable {c : C} (hc : ‖c‖ < 1)

/-- An element outside the point of a branch has value `1` at its vertex. -/
lemma valuation_eq_one_of_notMem (b : OuterBranch C F') {y : Rint c F'}
    (hy : y ∉ placeIdeal hc b.1 b.2.2) : b.1.1 (y : F') = 1 := by
  refine le_antisymm (valuation_le_one_R hc b.1 y) (not_lt.1 fun hlt ↦ hy ?_)
  rw [mem_placeIdeal_iff, (red_eq_zero_iff (valuation_le_one_R hc b.1 y)).2 hlt, b.2.1.res_zero]

/-- Every element of `R'` is a constant modulo the point of a branch. -/
lemma exists_sub_constR_mem (b : OuterBranch C F') (y : Rint c F') :
    ∃ κ : HenselComplete.integers C, y - constR c κ ∈ placeIdeal hc b.1 b.2.2 := by
  obtain ⟨κ, hκ⟩ := IsLocalRing.residue_surjective (placeHom hc b.1 b.2.2 y)
  refine ⟨κ, ?_⟩
  rw [placeIdeal, RingHom.mem_ker, map_sub, ← hκ]
  change _ - b.2.1.res (redHom hc b.1 (constR c κ)) = 0
  rw [redHom_constR, b.2.1.res_algebraMap, sub_self]

open Classical in
/-- The vertex degree as a sum over the branches. -/
lemma vertexDegree_eq_sum [Fintype (Ext C F')] (P : Ideal (Rint c F')) :
    vertexDegree hc P = ∑ b ∈ Finset.univ.sigma fun v : Ext C F' ↦
      (zeros 𝓀 (red C (xF C F') v)).attach,
      if placeIdeal hc b.1 b.2.2 = P then ord (red C (xF C F') b.1) b.2.1 else 0 := by
  rw [vertexDegree, Finset.sum_sigma]

end Helpers

/-! ### Exact node data and the upward closure -/

section Upward

/-- A residue-unit has valuation one. -/
lemma CurvePlace.valuation_eq_one_of_res_ne_zero {κ : Type*} [Field κ] [Algebra 𝓀 κ]
    [IsCurveFunctionField 𝓀 κ] (Q : CurvePlace 𝓀 κ) {y : κ} (hy : y ∈ Q.V)
    (hres : Q.res y ≠ 0) : Q.valuation y = 1 :=
  le_antisymm (Q.valuation_le_one_iff.2 hy) (not_lt.1 fun h ↦ hres (Q.res_eq_zero_of_lt_one h))

/-- **Exact node data** at a point `P'` of `R' = Rint c F'` over the node, with outer branch
`b₁`: `u, v ∈ F'` with `u v = γ ∈ C`, `σ x = e u^d` with `σ, e ∈ R' ∖ P'`, `σ_u u, σ_v v ∈ R'`
(`σ_u, σ_v ∉ P'`), and `σ_u u` reducing to a uniformizer at the outer branch.

This is an **interim hypothesis** (Blueprint §9.10, R4, open obligation (a1)): it is to be
produced from `IsNodeODP` by descent to a DVR `O_E` (S7.9) and the node deformation
`IsOrdinaryDoublePoint.exists_node`. -/
structure NodeData {c : C} (hc : ‖c‖ < 1) (P' : Ideal (Rint c F')) (b₁ : OuterBranch C F') where
  /-- The multiplicity. -/
  d : ℕ
  one_le_d : 1 ≤ d
  /-- The outer node coordinate. -/
  u : F'
  /-- The inner node coordinate. -/
  v : F'
  /-- The thickness. -/
  γ : C
  γ_ne_zero : γ ≠ 0
  mul_eq : u * v = algebraMap C F' γ
  /-- A denominator. -/
  σ : Rint c F'
  /-- The unit in `x = ε u^d`, `ε = e / σ`. -/
  e : Rint c F'
  σ_notMem : σ ∉ P'
  e_notMem : e ∉ P'
  x_eq : (σ : F') * xF C F' = (e : F') * u ^ d
  /-- `σ_u u ∈ R'`. -/
  uR : Rint c F'
  /-- A denominator of `u`. -/
  σu : Rint c F'
  σu_notMem : σu ∉ P'
  uR_eq : (uR : F') = (σu : F') * u
  /-- `σ_v v ∈ R'`. -/
  vR : Rint c F'
  /-- A denominator of `v`. -/
  σv : Rint c F'
  σv_notMem : σv ∉ P'
  vR_eq : (vR : F') = (σv : F') * v
  uR_val : b₁.2.1.valuation (redHom hc b₁.1 uR) = exp (-1)

section OuterFacts

variable {c : C} (hc : ‖c‖ < 1) {P' : Ideal (Rint c F')} {b₁ : OuterBranch C F'}
  (hP₁ : placeIdeal hc b₁.1 b₁.2.2 = P') (N : NodeData hc P' b₁)
include hP₁

lemma val_one_of_notMem {y : Rint c F'} (hy : y ∉ P') : b₁.1.1 (y : F') = 1 :=
  valuation_eq_one_of_notMem hc b₁ (hP₁ ▸ hy)

lemma Qval_one_of_notMem {y : Rint c F'} (hy : y ∉ P') :
    b₁.2.1.valuation (redHom hc b₁.1 y) = 1 := by
  refine CurvePlace.valuation_eq_one_of_res_ne_zero _ (red_mem_V hc b₁.1 y b₁.2.2) fun h ↦ hy ?_
  rw [← hP₁, mem_placeIdeal_iff]
  exact h

lemma NodeData.val_u : b₁.1.1 N.u = 1 := by
  have h := congrArg b₁.1.1 N.x_eq
  rw [map_mul, map_mul, map_pow, val_one_of_notMem hc hP₁ N.σ_notMem,
    val_one_of_notMem hc hP₁ N.e_notMem,
    valuation_xF, one_mul, one_mul] at h
  rcases lt_trichotomy (b₁.1.1 N.u) 1 with hlt | heq | hgt
  · exact absurd h.symm (pow_lt_one₀ zero_le hlt (by have := N.one_le_d; omega)).ne
  · exact heq
  · exact absurd h.symm (one_lt_pow₀ hgt (by have := N.one_le_d; omega)).ne'

lemma NodeData.Qval_u : b₁.2.1.valuation (red C N.u b₁.1) = exp (-1) := by
  have h := N.uR_val
  rw [redHom_apply, N.uR_eq, red_mul (valuation_le_one_R hc b₁.1 N.σu) (N.val_u hc hP₁).le,
    map_mul, ← redHom_apply hc, Qval_one_of_notMem hc hP₁ N.σu_notMem, one_mul] at h
  exact h

lemma NodeData.ord_x : ord (red C (xF C F') b₁.1) b₁.2.1 = N.d := by
  have hσ := val_one_of_notMem hc hP₁ N.σ_notMem
  have he := val_one_of_notMem hc hP₁ N.e_notMem
  have h : red C ((N.σ : F') * xF C F') b₁.1 = red C ((N.e : F') * N.u ^ N.d) b₁.1 := by
    rw [N.x_eq]
  rw [red_mul hσ.le (valuation_xF _).le, red_mul he.le (by rw [map_pow, N.val_u hc hP₁, one_pow]),
    red_pow (N.val_u hc hP₁).le] at h
  have h2 := congrArg b₁.2.1.valuation h
  have e1 : b₁.2.1.valuation (red C (N.σ : F') b₁.1) = 1 := Qval_one_of_notMem hc hP₁ N.σ_notMem
  have e2 : b₁.2.1.valuation (red C (N.e : F') b₁.1) = 1 := Qval_one_of_notMem hc hP₁ N.e_notMem
  rw [map_mul, map_mul, map_pow, e1, e2, N.Qval_u hc hP₁, one_mul, one_mul,
    valuation_x b₁.2.2] at h2
  have h3 : exp (-(ord (red C (xF C F') b₁.1) b₁.2.1 : ℤ)) = exp (-(N.d : ℤ)) := by
    rw [h2, ← exp_nsmul]
    congr 1
    simp
  have := exp_injective h3
  omega

end OuterFacts

section Red

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

/-- An element congruent to a constant of norm one has value one and residue-valuation one at
every place. -/
lemma val_and_Qval_eq_one (w : Ext C F) (Q : CurvePlace 𝓀 (IsLocalRing.ResidueField
    w.1.valuationSubring)) {z : F} {κ : C} (hκ : ‖κ‖₊ = 1)
    (hz : w.1 (z - algebraMap C F κ) < 1) :
    w.1 z = 1 ∧ Q.valuation (red C z w) = 1 := by
  have hκw : w.1 (algebraMap C F κ) = 1 := by rw [valuation_algebraMap_C', hκ]
  have hzκ : z = (z - algebraMap C F κ) + algebraMap C F κ := by ring
  have hwz : w.1 z = 1 := by
    rw [hzκ, Valuation.map_add_eq_of_lt_right _ (hκw ▸ hz), hκw]
  refine ⟨hwz, ?_⟩
  have hred : red C z w = algebraMap 𝓀 _ (IsLocalRing.residue (HenselComplete.integers C)
      ⟨κ, (HenselComplete.mem_integers_iff κ).2 (by
        rw [← coe_nnnorm, hκ, NNReal.coe_one])⟩) := by
    rw [hzκ, red_add hz.le hκw.le, (red_eq_zero_iff hz.le).2 hz, zero_add,
      red_algebraMap_C κ hκ.le]
  rw [hred]
  refine SemistableReduction.valuation_algebraMap_eq_one Q.valuation_algebraMap_le_one ?_
  rw [Ne, IsLocalRing.residue_eq_zero_iff, HenselComplete.mem_maximalIdeal_iff_norm_lt_one]
  simp [← coe_nnnorm, hκ]

end Red

section Main

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) F']

omit [CharZero C] [Algebra.IsSeparable (RatFunc C) F'] [IsAlgClosed C] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] in
/-- Finitely many extensions of a Gauss valuation. -/
lemma finite_gaussExtension (a : C) (r : ℝ≥0ˣ) [Algebra.IsSeparable (RatFunc C) F'] :
    Finite (GaussExtension a r F') := by
  haveI : Fact (DenseRange (algebraMap (GaussField a r)
      (UniformSpace.Completion (GaussField a r)))) :=
    ⟨DenseCompletion.denseRange_algebraMap_completion _⟩
  haveI := LocalGlobal.finite_extension (F := GaussField a r)
    (UniformSpace.Completion (GaussField a r)) (F' := F')
  exact Finite.of_equiv _ gaussExtensionEquiv.symm


end Main

end Upward

end GaussTube

end SemistableReduction
