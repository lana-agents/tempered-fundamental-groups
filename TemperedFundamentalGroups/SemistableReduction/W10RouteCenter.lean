/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussTree
import TemperedFundamentalGroups.SemistableReduction.W10Stable

/-!
# Routing points of the special fibre of the tree model (G4, part 1)

Blueprint §9.7a, step 4 (G4 (ii)). A refinement of `GaussTree.exists_standard_localAt_eq` on the
special fibre (`W ∩ K = O`): the local ring of the join model at the center of `W` is that of a
standard chart `B ⊆ W` of one of three **routed** kinds (`Routed`):

* a vertex chart `O[t m]`, `W` not in the residue direction of any smaller disc `D j ⊊ D m`
  (`t m - (a j - a m)/c m` is a `W`-unit);
* an edge chart `O[u, c'/u]` of an **edge** `(j, m)` (no disc strictly between), `W` centered at
  the node (`u`, `c'/u ∈ 𝔪_W`);
* the chart `O[(t ρ)⁻¹]` at `∞` of the **root** `ρ`, `W` centered at `∞` (`(t ρ)⁻¹ ∈ 𝔪_W`).

`localAt_eq_routed`: the same for any chart of the join model contained in `W`, and
`localAt_normChart_eq_routed`: the same for the normalizations in an extension `F'`.
-/

universe u

open Polynomial

namespace SemistableReduction

open ZariskiModel GaussTree

namespace W10Route

variable {K F : Type u} [Field K] [Field F] [Algebra K F] {Γ₀ : Type*}
  [LinearOrderedCommGroupWithZero Γ₀] {v : Valuation K Γ₀}

local notation "⟪" k "⟫" => algebraMap K F k

section Center

variable (v) {ι : Type*} (a c : ι → K) (x : F) (W : ValuationSubring F)

/-- The **routed standard charts** at a point of the special fibre (see the module docstring). -/
def Routed (B : Subring F) : Prop :=
  (∃ m, B = polyChart v (coord x (a m) (c m)) ∧ coord x (a m) (c m) ∈ W ∧
      ∀ j, DiscLE v a c j m → j ≠ m →
        W.valuation (coord x (a m) (c m) - ⟪(a j - a m) / c m⟫) = 1) ∨
  (∃ j m, DiscLE v a c j m ∧ j ≠ m ∧
      (∀ k, DiscLE v a c j k → DiscLE v a c k m → k = j ∨ k = m) ∧
      B = nodeChart v (coord x (a j) (c m)) (c j / c m) ∧
      W.valuation (coord x (a j) (c m)) < 1 ∧
      W.valuation (⟪c j / c m⟫ / coord x (a j) (c m)) < 1) ∨
  (∃ ρ, (∀ i, DiscLE v a c i ρ) ∧ B = polyChart v (coord x (a ρ) (c ρ))⁻¹ ∧
      W.valuation (coord x (a ρ) (c ρ))⁻¹ < 1)

variable {v a c x W}

/-- **Routing on the special fibre**: for `W ∩ K = O`, the local ring of the join chart at the
center of `W` is that of a routed standard chart `B ⊆ W`. -/
theorem exists_routed [Finite ι] [Nonempty ι] (hc : ∀ i, c i ≠ 0)
    (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hWO : W.comap (algebraMap K F) = v.valuationSubring) :
    ∃ B, Routed v a c x W B ∧ B ≤ W.toSubring ∧ B ≤ joinChart v a c x W ∧
      localAt (joinChart v a c x W) W = localAt B W := by
  classical
  haveI := Fintype.ofFinite ι
  set R := baseRing F v.valuationSubring
  have hW : R ≤ W.toSubring := baseRing_le_iff.2 hWO.ge
  obtain ⟨ρ, hρ⟩ := exists_root hconv hred
  have hRC : R ≤ joinChart v a c x W := baseRing_le_joinChart
  have hK1 {i j : ι} (h : DiscLE v a c i j) {B : Subring F} (hRB : R ≤ B) :
      ⟪c i / c j⟫ ∈ B ∧ ⟪(a i - a j) / c j⟫ ∈ B :=
    ⟨algebraMap_mem_of_le_one hRB (h.div_le_one hc).1,
      algebraMap_mem_of_le_one hRB (h.div_le_one hc).2⟩
  by_cases hI : ∃ i, (coord x (a i) (c i)) ∈ W
  · obtain ⟨m, hmW, hmin⟩ := Finset.exists_min_image
      (Finset.univ.filter fun i ↦ (coord x (a i) (c i)) ∈ W) (fun i ↦ v (c i))
      (by obtain ⟨i, hi⟩ := hI; exact ⟨i, by simpa using hi⟩)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmW hmin
    have hbelow : ∀ i, (coord x (a i) (c i)) ∈ W → DiscLE v a c m i := by
      intro i hi
      rcases discLE_or_discLE_of_mem hc hWO hmW hi with h | h
      · exact h
      · exact discLE_symm_of_eq h (le_antisymm h.1 (hmin i hi))
    have habove : ∀ i, DiscLE v a c m i → (coord x (a i) (c i)) ∈ W := by
      intro i h
      rw [coord_eq_mul_add (a := a m) (hc m) (hc i)]
      obtain ⟨h₁, h₂⟩ := hK1 h hW
      exact W.add_mem _ _ (W.mul_mem _ _ h₁ hmW) h₂
    have hδW (i : ι) (h : DiscLE v a c i m) : ⟪(a i - a m) / c m⟫ ∈ W := (hK1 h hW).2
    have hunit (i : ι) (h : DiscLE v a c i m)
        (hn : ¬W.valuation ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) < 1) :
        W.valuation ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) = 1 :=
      le_antisymm ((W.valuation_le_one_iff _).2 (sub_mem hmW (hδW i h))) (not_lt.1 hn)
    by_cases hS : ∃ j, DiscLE v a c j m ∧ j ≠ m ∧
        W.valuation ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) < 1
    · obtain ⟨j, hjS, hjmax⟩ := Finset.exists_max_image
        (Finset.univ.filter fun j ↦ DiscLE v a c j m ∧ j ≠ m ∧
          W.valuation ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) < 1) (fun j ↦ v (c j))
        (by obtain ⟨j, hj⟩ := hS; exact ⟨j, by simpa using hj⟩)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hjS hjmax
      obtain ⟨hjm, hjne, hjres⟩ := hjS
      set u := coord x (a j) (c m)
      set N := nodeChart v u (c j / c m)
      have hRN : R ≤ N := baseRing_le_nodeChart
      have hu : u = (coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫ :=
        (coord_sub_eq_coord (hc m)).symm
      have hdiv : ⟪c j / c m⟫ / u = (coord x (a j) (c j))⁻¹ := div_coord_eq_inv (hc j) (hc m)
      have htmN : (coord x (a m) (c m)) ∈ N := by
        have : (coord x (a m) (c m)) = u + ⟪(a j - a m) / c m⟫ := by rw [hu]; ring
        rw [this]
        exact N.add_mem self_mem_nodeChart (hK1 hjm hRN).2
      have htjN : (coord x (a j) (c j))⁻¹ ∈ N := hdiv ▸ div_mem_nodeChart
      have hjW : (coord x (a j) (c j)) ∉ W := fun h ↦ hjne (hred j m hjm (hbelow j h))
      -- the edge property
      have hedge : ∀ k, DiscLE v a c j k → DiscLE v a c k m → k = j ∨ k = m := by
        intro k hjk hkm
        by_cases hkm' : k = m
        · exact .inr hkm'
        refine .inl ?_
        have hcm : 0 < v (c m) := zero_lt_iff.2 ((v.ne_zero_iff).2 (hc m))
        have hvk : v (c k) < v (c m) :=
          lt_of_le_of_ne hkm.1 fun he ↦ hkm' (hred k m hkm (discLE_symm_of_eq hkm he))
        have hkW : W.valuation ((coord x (a m) (c m)) - ⟪(a k - a m) / c m⟫) < 1 := by
          have hsplit : (coord x (a m) (c m)) - ⟪(a k - a m) / c m⟫ =
              ((coord x (a m) (c m)) - ⟪(a j - a m) / c m⟫) + ⟪(a j - a k) / c m⟫ := by
            rw [show (a k - a m) / c m = (a j - a m) / c m - (a j - a k) / c m by
              rw [div_sub_div_same]; ring_nf, map_sub]
            ring
          have hsmall : W.valuation ⟪(a j - a k) / c m⟫ < 1 := by
            rw [valuation_algebraMap_lt_one_iff hWO, map_div₀, div_lt_one₀ hcm]
            exact lt_of_le_of_lt hjk.2 hvk
          rw [hsplit]
          exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hjres hsmall)
        have hkj : v (c k) ≤ v (c j) := hjmax k ⟨hkm, hkm', hkW⟩
        exact (hred j k hjk (discLE_symm_of_eq hjk (le_antisymm hjk.1 hkj))).symm
      have hjinv : W.valuation (coord x (a j) (c j))⁻¹ < 1 := by
        have hmem : (coord x (a j) (c j))⁻¹ ∈ W := (W.mem_or_inv_mem _).resolve_left hjW
        refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 hmem) fun h1 ↦ hjW ?_
        have hne : (coord x (a j) (c j)) ≠ 0 := by
          rintro h0
          rw [h0, inv_zero, map_zero] at h1
          exact zero_ne_one h1
        have : W.valuation (coord x (a j) (c j)) = 1 := by
          rw [map_inv₀] at h1
          exact inv_eq_one.1 h1
        exact (W.valuation_le_one_iff _).1 this.le
      refine ⟨N, .inr (.inl ⟨j, m, hjm, hjne, hedge, rfl,
        by rw [← coord_sub_eq_coord (hc m)]; exact hjres,
        by rw [div_coord_eq_inv (hc j) (hc m)]; exact hjinv⟩), ?_, ?_,
        localAt_joinChart_eq hRN ?_ ?_⟩
      · refine nodeChart_le hW (hu ▸ sub_mem hmW (hδW j hjm)) (hdiv ▸ ?_)
        exact (W.mem_or_inv_mem _).resolve_left hjW
      · exact nodeChart_le hRC (hu ▸ Subring.sub_mem _ (mem_joinChart_of_mem hmW)
          (hRC (hK1 hjm le_rfl).2)) (hdiv ▸ inv_mem_joinChart_of_notMem hjW)
      · exact nodeChart_le hRC (hu ▸ Subring.sub_mem _ (mem_joinChart_of_mem hmW)
          (hRC (hK1 hjm le_rfl).2)) (hdiv ▸ inv_mem_joinChart_of_notMem hjW)
      · intro i
        by_cases hi : (coord x (a i) (c i)) ∈ W
        · rw [gen_of_mem hi]
          obtain ⟨h₁, h₂⟩ := hK1 (hbelow i hi) hRN
          exact coord_mem_localAt (hc m) (hc i) (le_localAt htmN) (le_localAt h₁)
            (le_localAt h₂)
        · rw [gen_of_notMem hi]
          have hmi : ¬DiscLE v a c m i := fun h ↦ hi (habove i h)
          by_cases him : DiscLE v a c i m
          · by_cases hiS : W.valuation ((coord x (a m) (c m)) - ⟪(a i - a m) / c m⟫) < 1
            · have hine : i ≠ m := by
                rintro rfl
                exact hi hmW
              have hij : DiscLE v a c i j := discLE_of_residue hconv hred hc hWO him hine hiS
                hjm hjne hjres fun k hk hkne hkW ↦ hjmax k ⟨hk, hkne, hkW⟩
              obtain ⟨h₁, h₂⟩ := hK1 hij hRN
              exact inv_coord_mem_localAt_of_inv (hc j) (hc i) htjN hjW (le_localAt h₁)
                (le_localAt h₂) (hK1 hij hW).2
            · exact inv_coord_mem_localAt_of_unit hRN (hc m) (hc i) htmN
                (him.div_le_one hc).1 (him.div_le_one hc).2 (hunit i him hiS)
          · obtain ⟨hfar, hfar'⟩ := lt_of_not_discLE him hmi
            exact inv_coord_mem_localAt_of_far hRN (hc m) (hc i) hWO htmN hmW hfar hfar'
    · push Not at hS
      set P := polyChart v (coord x (a m) (c m))
      have hRP : R ≤ P := baseRing_le_polyChart _
      have htmP : (coord x (a m) (c m)) ∈ P := self_mem_polyChart _
      refine ⟨P, .inl ⟨m, rfl, hmW, fun j hjm hjne ↦ hunit j hjm (not_lt.2 (hS j hjm hjne))⟩,
        polyChart_le hW hmW, polyChart_le hRC (mem_joinChart_of_mem hmW),
        localAt_joinChart_eq hRP (polyChart_le hRC (mem_joinChart_of_mem hmW)) fun i ↦ ?_⟩
      by_cases hi : (coord x (a i) (c i)) ∈ W
      · rw [gen_of_mem hi]
        obtain ⟨h₁, h₂⟩ := hK1 (hbelow i hi) hRP
        exact coord_mem_localAt (hc m) (hc i) (le_localAt htmP) (le_localAt h₁)
          (le_localAt h₂)
      · rw [gen_of_notMem hi]
        have hmi : ¬DiscLE v a c m i := fun h ↦ hi (habove i h)
        by_cases him : DiscLE v a c i m
        · have hine : i ≠ m := by
            rintro rfl
            exact hi hmW
          exact inv_coord_mem_localAt_of_unit hRP (hc m) (hc i) htmP
            (him.div_le_one hc).1 (him.div_le_one hc).2
            (hunit i him (not_lt.2 (hS i him hine)))
        · obtain ⟨hfar, hfar'⟩ := lt_of_not_discLE him hmi
          exact inv_coord_mem_localAt_of_far hRP (hc m) (hc i) hWO htmP hmW hfar hfar'
  · push Not at hI
    set P := polyChart v (coord x (a ρ) (c ρ))⁻¹
    have hRP : R ≤ P := baseRing_le_polyChart _
    have hρP : (coord x (a ρ) (c ρ))⁻¹ ∈ P := self_mem_polyChart _
    have hρinv : W.valuation (coord x (a ρ) (c ρ))⁻¹ < 1 := by
      have hmem : (coord x (a ρ) (c ρ))⁻¹ ∈ W := (W.mem_or_inv_mem _).resolve_left (hI ρ)
      refine lt_of_le_of_ne ((W.valuation_le_one_iff _).2 hmem) fun h1 ↦ hI ρ ?_
      have : W.valuation (coord x (a ρ) (c ρ)) = 1 := by
        rw [map_inv₀] at h1
        exact inv_eq_one.1 h1
      exact (W.valuation_le_one_iff _).1 this.le
    refine ⟨P, .inr (.inr ⟨ρ, hρ, rfl, hρinv⟩), polyChart_le hW ((W.mem_or_inv_mem _).resolve_left
      (hI ρ)), polyChart_le hRC (inv_mem_joinChart_of_notMem (hI ρ)),
      localAt_joinChart_eq hRP (polyChart_le hRC (inv_mem_joinChart_of_notMem (hI ρ)))
      fun i ↦ ?_⟩
    rw [gen_of_notMem (hI i)]
    obtain ⟨h₁, h₂⟩ := hK1 (hρ i) hRP
    exact inv_coord_mem_localAt_of_inv (hc ρ) (hc i) hρP (hI ρ) (le_localAt h₁) (le_localAt h₂)
      (hK1 (hρ i) hW).2

/-- **Routing of charts of the join model**: for `W ∩ K = O` and any chart `J ⊆ W` of the join
model of the lines `t i`, the local ring of `J` at the center of `W` is that of a routed standard
chart `B ⊆ W`. -/
theorem exists_routed_of_mem [Fintype ι] [Nonempty ι] (hc : ∀ i, c i ≠ 0)
    (hconv : IsConvex v a c) (hred : IsReduced v a c)
    (hWO : W.comap (algebraMap K F) = v.valuationSubring) {J : Subring F}
    (hJ : J ∈ (ZariskiModel.lines v fun i ↦ coord x (a i) (c i)).charts) (hJW : J ≤ W.toSubring) :
    ∃ B, Routed v a c x W B ∧ B ≤ W.toSubring ∧ localAt J W = localAt B W := by
  classical
  have hW : baseRing F v.valuationSubring ≤ W.toSubring := baseRing_le_iff.2 hWO.ge
  obtain ⟨B, hB, hBW, -, hloc⟩ := exists_routed (x := x) hc hconv hred hWO
  refine ⟨B, hB, hBW, ?_⟩
  have hmem : joinChart v a c x W ∈ (ZariskiModel.lines v fun i ↦ coord x (a i) (c i)).charts := by
    refine mem_iJoin_charts.2 ⟨_, fun i ↦ ?_, rfl⟩
    split_ifs
    · exact mem_line_charts.2 (.inl rfl)
    · exact mem_line_charts.2 (.inr rfl)
  rw [← center_eq lines_isProper lines_isSeparated hW hJ hJW,
    center_eq lines_isProper lines_isSeparated hW hmem (joinChart_le hW), hloc]

end Center

end W10Route

end SemistableReduction
