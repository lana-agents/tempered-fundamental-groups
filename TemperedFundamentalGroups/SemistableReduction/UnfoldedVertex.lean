/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTree

/-!
# Vertices through a node of a convex Gauss tree (Blueprint §9.7, XL6)

Let `V₀ ⊇ O` be a valuation subring of `K(X)` whose specialization on the join model of a convex
reduced family of Gauss valuations lies in two distinct vertices `W₁ ≠ W₂`
(`ModelCode.IsUnfolded`). Then the specialization is the local ring of a node chart
`O[t, c' / t]` (`t = (X - a j) / c m`, `c' = c j / c m`, `v(c') < 1`) containing `t` and `c' / t`,
and every vertex `W` containing the specialization has `t` or `c' / t` as a unit, and is the Gauss
valuation of `t` resp. of `c' / t` in that case (`exists_nodeChart_of_two_vertices`):

* `localAt_eq_of_center_le`: such a vertex is the local ring of the chart at its centre;
* `IsGaussCoord.eq_of_nodeChart`: a local ring of `O[y, c / y]` in which `y` is a unit is the Gauss
  valuation of `y`;
* `not_isTypeTwo_of_nodeChart`: a local ring of `O[y, c / y]` in which `y` and `c / y` vanish has
  residue field algebraic over that of `O` (all its elements are congruent to constants).
-/

universe u

open Polynomial

namespace SemistableReduction

section Vertex

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

open ZariskiModel

/-- **A vertex containing the specialization of `V`** is the local ring at its centre of every
subring `B` computing that specialization. -/
theorem localAt_eq_of_center_le {M : ZariskiModel (baseRing F v.valuationSubring)}
    (hM : M.IsProper) (hs : M.IsSeparated) {V : ValuationSubring F}
    (hV : baseRing F v.valuationSubring ≤ V.toSubring) {B : Subring F}
    (hcen : M.center hM V hV = localAt B V) {W : ValuationSubring F} (hW : W ∈ M.vertexSet)
    (hle : M.center hM V hV ≤ W.toSubring) : localAt B W = W.toSubring := by
  obtain ⟨A, hA, hAV⟩ := hM V hV
  have hAc : M.center hM V hV = localAt A V := center_eq hM hs hV hA hAV
  have hAW : A ≤ W.toSubring := fun a ha ↦ hle (hAc ▸ le_localAt ha)
  have hBW : B ≤ W.toSubring := fun b hb ↦ hle (hcen ▸ le_localAt hb)
  have hAB : A ≤ localAt B W := by
    intro a ha
    have : a ∈ localAt B V := hcen ▸ hAc ▸ le_localAt ha
    obtain ⟨s, hs, hsV, has⟩ := mem_localAt.1 this
    have hsinv : s⁻¹ ∈ W := hle (hcen ▸ inv_mem_localAt hs hsV)
    have hs0 : s ≠ 0 := by rintro rfl; simp at hsV
    exact mem_localAt.2 ⟨s, hs, valuation_eq_one_of_mem_of_inv_mem hs0 (hBW hs) hsinv, has⟩
  refine le_antisymm (localAt_le hBW) ?_
  rw [← localAt_eq_of_mem_vertexSet hs hW hA hAW]
  calc localAt A W ≤ localAt (localAt B W) W := localAt_mono hAB
    _ = localAt B W := localAt_eq_of_le le_localAt le_rfl

/-- The node chart is symmetric in its two coordinates. -/
lemma nodeChart_div {y : F} {c : K} (hy : y ≠ 0) (hc : c ≠ 0) :
    nodeChart v (algebraMap K F c / y) c = nodeChart v y c := by
  have hc' : algebraMap K F c ≠ 0 := by simpa using hc
  have e : algebraMap K F c / (algebraMap K F c / y) = y := by field_simp
  apply le_antisymm
  · refine nodeChart_le baseRing_le_nodeChart div_mem_nodeChart ?_
    rw [e]; exact self_mem_nodeChart
  · refine nodeChart_le baseRing_le_nodeChart ?_ self_mem_nodeChart
    have := div_mem_nodeChart (v := v) (y := algebraMap K F c / y) (c := c)
    rwa [e] at this

/-- **A local ring of `O[y, c / y]` in which `y` is a unit is the Gauss valuation of `y`.** -/
theorem IsGaussCoord.eq_of_nodeChart {w : Valuation F Γ₀} {y : F} (h : IsGaussCoord v w y)
    (hv : ∃ ϖ : K, ϖ ≠ 0 ∧ v ϖ < 1) {c : K} (hc : v c ≤ 1) {W : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = v.valuationSubring)
    (hBW : nodeChart v y c ≤ W.toSubring) (hloc : localAt (nodeChart v y c) W = W.toSubring)
    (hy : W.valuation y = 1) : W = w.valuationSubring := by
  have hyP : y ∈ polyChart v y := self_mem_polyChart y
  have hPB : polyChart v y ≤ nodeChart v y c :=
    polyChart_le baseRing_le_nodeChart self_mem_nodeChart
  have hPW := hPB.trans hBW
  have hBP : nodeChart v y c ≤ localAt (polyChart v y) W := by
    refine nodeChart_le ((baseRing_le_polyChart y).trans le_localAt) (le_localAt hyP) ?_
    rw [div_eq_mul_inv]
    exact mul_mem (le_localAt (baseRing_le_polyChart y (algebraMap_mem_baseRing hc)))
      (inv_mem_localAt hyP hy)
  have hloc' : localAt (polyChart v y) W = W.toSubring := by
    refine le_antisymm (localAt_le hPW) ?_
    rw [← hloc]
    calc localAt (nodeChart v y c) W ≤ localAt (localAt (polyChart v y) W) W := localAt_mono hBP
      _ = localAt (polyChart v y) W := localAt_eq_of_le le_localAt le_rfl
  exact h.eq_of_localAt_eq hW hPW hv hloc'

/-- **A local ring of `O[y, c / y]` at a point where `y` and `c / y` vanish is not of type 2**:
every element is congruent to a constant. -/
theorem not_isTypeTwo_of_nodeChart {y : F} {c : K} {W : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = v.valuationSubring)
    (hloc : localAt (nodeChart v y c) W = W.toSubring)
    (hy : W.valuation y < 1) (hcy : W.valuation (algebraMap K F c / y) < 1) :
    ¬ IsTypeTwo v.valuationSubring W := by
  have hO : ∀ o : K, v o ≤ 1 → W.valuation (algebraMap K F o) ≤ 1 := fun o ho ↦
    (GaussTree.valuation_algebraMap_le_one_iff hW).2 ho
  let S : Subring F :=
    { carrier := {z | z ∈ W ∧ ∃ o : K, v o ≤ 1 ∧ W.valuation (z - algebraMap K F o) < 1}
      mul_mem' := by
        rintro z₁ z₂ ⟨h₁, o₁, ho₁, hz₁⟩ ⟨h₂, o₂, ho₂, hz₂⟩
        refine ⟨mul_mem h₁ h₂, o₁ * o₂, by rw [map_mul]; exact mul_le_one' ho₁ ho₂, ?_⟩
        have e : z₁ * z₂ - algebraMap K F (o₁ * o₂) =
            z₁ * (z₂ - algebraMap K F o₂) + algebraMap K F o₂ * (z₁ - algebraMap K F o₁) := by
          rw [map_mul]; ring
        rw [e]
        refine (W.valuation.map_add _ _).trans_lt (max_lt ?_ ?_) <;> rw [map_mul]
        · exact (mul_le_of_le_one_left' ((W.valuation_le_one_iff _).2 h₁)).trans_lt hz₂
        · exact (mul_le_of_le_one_left' (hO o₂ ho₂)).trans_lt hz₁
      one_mem' := ⟨W.one_mem, 1, by simp, by simp⟩
      add_mem' := by
        rintro z₁ z₂ ⟨h₁, o₁, ho₁, hz₁⟩ ⟨h₂, o₂, ho₂, hz₂⟩
        refine ⟨add_mem h₁ h₂, o₁ + o₂, (v.map_add _ _).trans (max_le ho₁ ho₂), ?_⟩
        have e : z₁ + z₂ - algebraMap K F (o₁ + o₂) =
            (z₁ - algebraMap K F o₁) + (z₂ - algebraMap K F o₂) := by
          rw [map_add]; ring
        rw [e]
        exact (W.valuation.map_add _ _).trans_lt (max_lt hz₁ hz₂)
      zero_mem' := ⟨W.zero_mem, 0, by simp, by simp⟩
      neg_mem' := by
        rintro z ⟨h, o, ho, hz⟩
        refine ⟨neg_mem h, -o, by rwa [Valuation.map_neg], ?_⟩
        have e : -z - algebraMap K F (-o) = -(z - algebraMap K F o) := by rw [map_neg]; ring
        rwa [e, Valuation.map_neg] }
  have hBS : nodeChart v y c ≤ S := by
    refine nodeChart_le ?_ ⟨?_, 0, by simp, by simpa using hy⟩ ⟨?_, 0, by simp, by simpa using hcy⟩
    · rintro _ ⟨o, ho, rfl⟩
      exact ⟨(W.valuation_le_one_iff _).1 (hO o ho), o, ho, by simp⟩
    · exact (W.valuation_le_one_iff _).1 hy.le
    · exact (W.valuation_le_one_iff _).1 hcy.le
  have hall : ∀ z ∈ W, ∃ o : K, v o ≤ 1 ∧ W.valuation (z - algebraMap K F o) < 1 := by
    intro z hz
    have hz' : z ∈ localAt (nodeChart v y c) W := by rw [hloc]; exact hz
    obtain ⟨s, hs, hsW, hzs⟩ := mem_localAt.1 hz'
    obtain ⟨-, o₂, ho₂, hs₂⟩ := hBS hs
    obtain ⟨-, o₁, ho₁, hz₁⟩ := hBS hzs
    have ho₂W : W.valuation (algebraMap K F o₂) = 1 := by
      refine le_antisymm (hO o₂ ho₂) (not_lt.1 fun hlt ↦ ?_)
      have e : s = (s - algebraMap K F o₂) + algebraMap K F o₂ := by ring
      have := (W.valuation.map_add (s - algebraMap K F o₂) (algebraMap K F o₂)).trans_lt
        (max_lt hs₂ hlt)
      rw [← e, hsW] at this
      exact lt_irrefl _ this
    have ho₂0 : algebraMap K F o₂ ≠ 0 := fun h0 ↦ by simp [h0] at ho₂W
    have ho₂0' : o₂ ≠ 0 := fun h0 ↦ ho₂0 (by simp [h0])
    have hvo₂ : v o₂ = 1 := by
      refine le_antisymm ho₂ (not_lt.1 fun hlt ↦ ?_)
      have := (GaussTree.valuation_algebraMap_lt_one_iff hW).2 hlt
      rw [ho₂W] at this
      exact lt_irrefl _ this
    refine ⟨o₁ / o₂, by rw [map_div₀, hvo₂, div_one]; exact ho₁, ?_⟩
    have e : z - algebraMap K F (o₁ / o₂) =
        ((z * s - algebraMap K F o₁) - z * (s - algebraMap K F o₂)) / algebraMap K F o₂ := by
      rw [map_div₀]; field_simp; ring
    rw [e, map_div₀, ho₂W, div_one]
    refine (W.valuation.map_sub _ _).trans_lt (max_lt hz₁ ?_)
    rw [map_mul]
    exact (mul_le_of_le_one_left' ((W.valuation_le_one_iff _).2 hz)).trans_lt hs₂
  rintro ⟨z, hz, hP⟩
  obtain ⟨o, ho, hzo⟩ := hall z hz
  have hP' := hP (X - C ⟨o, ho⟩) (by
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    exact X_sub_C_ne_zero _)
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub, aeval_X, aeval_C] at hP'
  change W.valuation (z - algebraMap K F o) = 1 at hP'
  rw [hP'] at hzo
  exact lt_irrefl _ hzo

end Vertex

section RatFunc

open GaussTree ZariskiModel

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀}

local notation "⟪" k "⟫" => algebraMap K (RatFunc K) k

/-- The Gauss coordinate `(X - a) / c` of the Gauss valuation of radius `|c|`. -/
lemma isGaussCoord_coord {a c : K} (hc : c ≠ 0) :
    IsGaussCoord v (gaussRat v a (Units.mk0 (v c) ((v.ne_zero_iff).2 hc)))
      (coord (RatFunc.X : RatFunc K) a c) := by
  rw [← gaussCoord_eq_coord hc]
  exact isGaussCoord_gaussCoord rfl

/-- **Two vertices through the specialization** of `V₀` on the join model of a convex reduced
family force a node chart `O[t, c' / t]` (XL6). -/
theorem exists_nodeChart_of_two_vertices {ι : Type*} [Fintype ι] [Nonempty ι] {a c : ι → K}
    (hc : ∀ i, c i ≠ 0) (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hrank : ∀ O' : ValuationSubring K, v.valuationSubring ≤ O' →
      O' = v.valuationSubring ∨ O' = ⊤) (hv : ∃ ϖ : K, ϖ ≠ 0 ∧ v ϖ < 1)
    {V : ValuationSubring (RatFunc K)}
    (hV : baseRing (RatFunc K) v.valuationSubring ≤ V.toSubring)
    {W₁ W₂ : ValuationSubring (RatFunc K)} (hW₁ : W₁ ∈ (gaussJoinModel v a c).vertexSet)
    (hW₂ : W₂ ∈ (gaussJoinModel v a c).vertexSet) (hne : W₁ ≠ W₂)
    (hle₁ : (gaussJoinModel v a c).center gaussJoinModel_isProper V hV ≤ W₁.toSubring)
    (hle₂ : (gaussJoinModel v a c).center gaussJoinModel_isProper V hV ≤ W₂.toSubring) :
    ∃ (j m : ι) (Wt Ws : ValuationSubring (RatFunc K)), c j ≠ 0 ∧ c m ≠ 0 ∧
      v (c j / c m) < 1 ∧
      coord RatFunc.X (a j) (c m) ∈
        (gaussJoinModel v a c).center gaussJoinModel_isProper V hV ∧
      ⟪c j / c m⟫ / coord RatFunc.X (a j) (c m) ∈
        (gaussJoinModel v a c).center gaussJoinModel_isProper V hV ∧
      ∀ W ∈ (gaussJoinModel v a c).vertexSet,
        (gaussJoinModel v a c).center gaussJoinModel_isProper V hV ≤ W.toSubring →
        (W.valuation (coord RatFunc.X (a j) (c m)) = 1 ∨
          W.valuation (⟪c j / c m⟫ / coord RatFunc.X (a j) (c m)) = 1) ∧
        (W.valuation (coord RatFunc.X (a j) (c m)) = 1 → W = Wt) ∧
        (W.valuation (⟪c j / c m⟫ / coord RatFunc.X (a j) (c m)) = 1 → W = Ws) := by
  set M := gaussJoinModel v a c
  obtain ⟨B, hB, hBV, hcen⟩ := gaussJoinModel_center_eq hc hconv hred hrank hV
  have hloc : ∀ W ∈ M.vertexSet, M.center gaussJoinModel_isProper V hV ≤ W.toSubring →
      localAt B W = W.toSubring := fun W hW hle ↦
    localAt_eq_of_center_le gaussJoinModel_isProper gaussJoinModel_isSeparated hV hcen hW hle
  have hBW : ∀ W : ValuationSubring (RatFunc K),
      M.center gaussJoinModel_isProper V hV ≤ W.toSubring → B ≤ W.toSubring :=
    fun W hle b hb ↦ hle (hcen ▸ le_localAt hb)
  rcases hB with ⟨i, rfl⟩ | ⟨i, rfl⟩ | ⟨j, m, hjm, hjm', rfl⟩
  · -- a line chart: both vertices are the Gauss valuation of its coordinate
    have h := isGaussCoord_coord (v := v) (a := a i) (hc i)
    exact absurd ((h.eq_of_localAt_eq hW₁.1 (hBW _ hle₁) hv (hloc _ hW₁ hle₁)).trans
      (h.eq_of_localAt_eq hW₂.1 (hBW _ hle₂) hv (hloc _ hW₂ hle₂)).symm) hne
  · have h := (isGaussCoord_coord (v := v) (a := a i) (hc i)).inv
    exact absurd ((h.eq_of_localAt_eq hW₁.1 (hBW _ hle₁) hv (hloc _ hW₁ hle₁)).trans
      (h.eq_of_localAt_eq hW₂.1 (hBW _ hle₂) hv (hloc _ hW₂ hle₂)).symm) hne
  · set t := coord (RatFunc.X : RatFunc K) (a j) (c m)
    have ht := isGaussCoord_coord (v := v) (a := a j) (hc m)
    have hs' := (isGaussCoord_coord (v := v) (a := a j) (hc j)).inv
    rw [← div_coord_eq_inv (hc j) (hc m)] at hs'
    have hlt : v (c j) < v (c m) := lt_of_le_of_ne hjm.1 fun h ↦
      hjm' (hred j m hjm (discLE_symm_of_eq hjm h))
    have hc'1 : v (c j / c m) < 1 := by
      rw [map_div₀, div_lt_one₀ (zero_lt_iff.2 ((v.ne_zero_iff).2 (hc m)))]
      exact hlt
    have hc'0 : c j / c m ≠ 0 := div_ne_zero (hc j) (hc m)
    refine ⟨j, m,
      (gaussRat v (a j) (Units.mk0 (v (c m)) ((v.ne_zero_iff).2 (hc m)))).valuationSubring,
      (gaussRat v (a j) (Units.mk0 (v (c j)) ((v.ne_zero_iff).2 (hc j)))).valuationSubring,
      hc j, hc m, hc'1, hcen ▸ le_localAt self_mem_nodeChart,
      hcen ▸ le_localAt div_mem_nodeChart, fun W hW hle ↦ ⟨?_, fun h1 ↦ ?_, fun h1 ↦ ?_⟩⟩
    · by_contra hcon
      push Not at hcon
      have hlt₁ : W.valuation t < 1 := lt_of_le_of_ne
        ((W.valuation_le_one_iff _).2 (hBW W hle self_mem_nodeChart)) hcon.1
      have hlt₂ : W.valuation (⟪c j / c m⟫ / t) < 1 := lt_of_le_of_ne
        ((W.valuation_le_one_iff _).2 (hBW W hle div_mem_nodeChart)) hcon.2
      exact not_isTypeTwo_of_nodeChart hW.1 (hloc W hW hle) hlt₁ hlt₂ hW.2.1
    · exact ht.eq_of_nodeChart hv hc'1.le hW.1 (hBW W hle) (hloc W hW hle) h1
    · have hB' := nodeChart_div (v := v) ht.ne_zero hc'0
      have hloc' := hloc W hW hle
      have hBW' := hBW W hle
      rw [← hB'] at hloc' hBW'
      exact hs'.eq_of_nodeChart hv hc'1.le hW.1 hBW' hloc' h1

end RatFunc

end SemistableReduction
