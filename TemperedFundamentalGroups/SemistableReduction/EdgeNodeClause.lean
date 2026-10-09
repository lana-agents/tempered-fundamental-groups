/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeBranchVertex
import TemperedFundamentalGroups.SemistableReduction.NoLoopsBranches

/-!
# Edge nodes: two components and the node clause of `IsUnfolded` (StrongComponentA (a))

Let `c` be a semistable W-model over `O = O_v` of a field `L ⊇ K(X)` and `y` a point whose germs
are the local ring `localAt T W` of the normalized edge chart `T` of an edge `(j, m)` of a Gauss
tree (`O[t, c'/t]`, `t = (X - a j)/r m`, `c' = r j / r m`) at a valuation `W` centred on its node.
Then (`edgeNode`):

* `y` lies on two distinct components of the special fibre (the branches over the two Gauss
  valuations, `exists_branches_edge`, `exists_two_components`);
* every `f ∈ K(X)` whose image is a germ at `y` lies in the Gauss valuation rings
  `w_{a j, |r m|}` and `w_{a j, |r j|}`, which are distinct.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode _root_.SemistableReduction
  _root_.SemistableReduction.ZariskiModel _root_.SemistableReduction.GaussTree

section Comap

variable {F F' : Type*} [Field F] [Field F'] [Algebra F F'] {Γ : Type*}
  [LinearOrderedCommGroupWithZero Γ]

lemma valuation_eq_one_of_comap {V : ValuationSubring F'} {G : Valuation F Γ}
    (h : V.comap (algebraMap F F') = G.valuationSubring) {z : F} (hz : G z = 1) :
    V.valuation (algebraMap F F' z) = 1 := by
  rw [← _root_.SemistableReduction.valuation_comap_eq_one_iff, h,
    valuationSubring_valuation_eq_one_iff]
  exact hz

lemma valuation_lt_one_of_comap {V : ValuationSubring F'} {G : Valuation F Γ}
    (h : V.comap (algebraMap F F') = G.valuationSubring) {z : F} (hz : G z < 1) :
    V.valuation (algebraMap F F' z) < 1 := by
  have hmem : z ∈ V.comap (algebraMap F F') := by
    rw [h]; exact (Valuation.mem_valuationSubring_iff _ _).2 hz.le
  refine lt_of_le_of_ne ((V.valuation_le_one_iff _).2 hmem) fun h1 ↦ ?_
  rw [← _root_.SemistableReduction.valuation_comap_eq_one_iff, h,
    valuationSubring_valuation_eq_one_iff] at h1
  rw [h1] at hz
  exact lt_irrefl _ hz

lemma mem_of_comap {V : ValuationSubring F'} {G : ValuationSubring F}
    (h : V.comap (algebraMap F F') = G) {z : F} (hz : algebraMap F F' z ∈ V) : z ∈ G := by
  rw [← h]; exact hz

end Comap

variable {K : Type u} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  {v : Valuation K Γ₀} {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {c : TemperedFundamentalGroups.ModelCode O}
  {L : Type u} [Field L] [Algebra K L] [Algebra O L] [IsScalarTower O K L]
  [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L] {x : L}
  {j : Spec (CommRingCat.of L) ⟶ c.scheme}

local notation "⟪" k "⟫" => algebraMap K (RatFunc K) k

/-- **Edge nodes** of a semistable W-model: two components through the node, and the germs from
`K(X)` lie in the two (distinct) Gauss valuation rings of the edge. -/
theorem edgeNode (hW : IsWModel O L x c j) (hvO : v.valuationSubring = O) {ϖ : O}
    (hϖ : Irreducible ϖ) (hss : IsSemistable ϖ c) {ι : Type*} {a r : ι → K} {jj m : ι}
    (hrj : r jj ≠ 0) (hrm : r m ≠ 0) {W : ValuationSubring L}
    (hTW : normChart L (nodeChart v (coord (RatFunc.X : RatFunc K) (a jj) (r m)) (r jj / r m)) ≤
      W.toSubring)
    (hWb : (W.comap (algebraMap (RatFunc K) L)).comap (algebraMap K (RatFunc K)) =
      v.valuationSubring)
    (hy : W.valuation (algebraMap (RatFunc K) L (coord (RatFunc.X : RatFunc K) (a jj) (r m))) < 1)
    (hcy : W.valuation (algebraMap (RatFunc K) L
      (⟪r jj / r m⟫ / coord (RatFunc.X : RatFunc K) (a jj) (r m))) < 1)
    {y : c.scheme} (hgerm : germs c j y = (localAt (normChart L
      (nodeChart v (coord (RatFunc.X : RatFunc K) (a jj) (r m)) (r jj / r m))) W : Set L)) :
    (∃ v₁ ∈ components c, ∃ w₁ ∈ components c, v₁ ≠ w₁ ∧ y ∈ v₁ ∧ y ∈ w₁) ∧
    (∀ f : RatFunc K, algebraMap (RatFunc K) L f ∈ germs c j y →
      f ∈ (gaussRat v (a jj) (Units.mk0 (v (r m)) ((v.ne_zero_iff).2 hrm))).valuationSubring ∧
      f ∈ (gaussRat v (a jj) (Units.mk0 (v (r jj)) ((v.ne_zero_iff).2 hrj))).valuationSubring) ∧
    (gaussRat v (a jj) (Units.mk0 (v (r m)) ((v.ne_zero_iff).2 hrm))).valuationSubring ≠
      (gaussRat v (a jj) (Units.mk0 (v (r jj)) ((v.ne_zero_iff).2 hrj))).valuationSubring := by
  set y₀ := coord (RatFunc.X : RatFunc K) (a jj) (r m) with hy₀def
  set c' := r jj / r m with hc'def
  set S := nodeChart v y₀ c'
  set T := normChart L S
  set Gm := gaussRat v (a jj) (Units.mk0 (v (r m)) ((v.ne_zero_iff).2 hrm))
  set Gj := gaussRat v (a jj) (Units.mk0 (v (r jj)) ((v.ne_zero_iff).2 hrj))
  have hc'0 : c' ≠ 0 := div_ne_zero hrj hrm
  have hgm : IsGaussCoord v Gm y₀ := isGaussCoord_coord hrm
  have hgj : IsGaussCoord v Gj (coord (RatFunc.X : RatFunc K) (a jj) (r jj)) :=
    isGaussCoord_coord hrj
  have hy0 : y₀ ≠ 0 := hgm.ne_zero
  have hc' : v c' < 1 := valuation_lt_one_of_node hy0 hc'0 hWb hy hcy
  obtain ⟨⟨Vm, hVm, hVmc⟩, ⟨Vj, hVj, hVjc⟩⟩ := exists_branches_edge hrj hrm hTW hWb hy hcy
  -- the coordinates
  have hX0 : (RatFunc.X - ⟪a jj⟫ : RatFunc K) ≠ 0 := by
    have := hgm.ne_zero
    simp only [hy₀def, coord] at this
    exact (div_ne_zero_iff.1 this).1
  have hrj' : (⟪r jj⟫ : RatFunc K) ≠ 0 := by simpa using hrj
  have hrm' : (⟪r m⟫ : RatFunc K) ≠ 0 := by simpa using hrm
  have ey : y₀ = coord (RatFunc.X : RatFunc K) (a jj) (r jj) * ⟪c'⟫ := by
    simp only [hy₀def, hc'def, coord, map_div₀]
    field_simp
  have ecy : ⟪c'⟫ / y₀ = (coord (RatFunc.X : RatFunc K) (a jj) (r jj))⁻¹ := by
    simp only [hy₀def, hc'def, coord, map_div₀]
    field_simp
  have hGm1 : Gm y₀ = 1 := hgm.valuation_self
  have hGj : Gj y₀ < 1 := by
    rw [ey, map_mul, hgj.valuation_self, one_mul, hgj.valuation_algebraMap]
    exact hc'
  have hGjc : Gj (⟪c'⟫ / y₀) = 1 := by rw [ecy]; exact hgj.inv.valuation_self
  -- germs
  have hgermW : ∀ f ∈ germs c j y, f ∈ localAt T W := fun f hf ↦ by
    rw [hgerm] at hf; exact hf
  have hST : ∀ s ∈ S, algebraMap (RatFunc K) L s ∈ germs c j y := fun s hs ↦ by
    rw [hgerm]; exact le_localAt (map_le_normChart S ⟨s, hs, rfl⟩)
  have ht : algebraMap (RatFunc K) L y₀ ∈ germs c j y := hST _ self_mem_nodeChart
  have ht' : algebraMap (RatFunc K) L (⟪c'⟫ / y₀) ∈ germs c j y := hST _ div_mem_nodeChart
  have hnu : ∀ z : RatFunc K, W.valuation (algebraMap (RatFunc K) L z) < 1 →
      ∀ w ∈ germs c j y, algebraMap (RatFunc K) L z * w ≠ 1 := by
    intro z hz w hw h1
    have hwW : W.valuation w ≤ 1 :=
      (W.valuation_le_one_iff _).2 (localAt_le hTW (hgermW w hw))
    have := mul_lt_one_of_lt_of_le hz hwW
    rw [← map_mul, h1, map_one] at this
    exact lt_irrefl _ this
  -- `ϖ` in the branches
  have hvϖ : v (ϖ : K) < 1 := by
    have hmem : (ϖ : K) ∈ v.valuationSubring := hvO ▸ ϖ.2
    refine lt_of_le_of_ne ((Valuation.mem_valuationSubring_iff _ _).1 hmem) fun h1 ↦
      hϖ.not_isUnit ?_
    have hinv' : (ϖ : K)⁻¹ ∈ v.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, h1, inv_one]
    have hinv : (ϖ : K)⁻¹ ∈ O := hvO ▸ hinv'
    have hϖ0 : (ϖ : K) ≠ 0 := by
      intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
    exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hϖ0))
  have hϖL : algebraMap O L ϖ = algebraMap (RatFunc K) L ⟪(ϖ : K)⟫ := by
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O K L]; rfl
  have hϖV : ∀ {V : ValuationSubring L} {G : Valuation (RatFunc K) Γ₀} {z : RatFunc K},
      IsGaussCoord v G z → V.comap (algebraMap (RatFunc K) L) = G.valuationSubring →
      V.valuation (algebraMap O L ϖ) < 1 := by
    intro V G z hG hVG
    rw [hϖL]
    exact valuation_lt_one_of_comap hVG (by rw [hG.valuation_algebraMap]; exact hvϖ)
  refine ⟨?_, fun f hf ↦ ⟨mem_of_comap hVmc (hVm (hgermW _ hf)),
    mem_of_comap hVjc (hVj (hgermW _ hf))⟩, fun heq ↦ ?_⟩
  · exact exists_two_components hW hϖ hss (fun f hf ↦ hVm (hgermW f hf))
      (fun f hf ↦ hVj (hgermW f hf)) (hϖV hgm hVmc) (hϖV hgj hVjc) ht ht'
      (hnu _ hy) (hnu _ hcy) (valuation_eq_one_of_comap hVmc hGm1)
      (valuation_eq_one_of_comap hVjc hGjc) (valuation_lt_one_of_comap hVjc hGj)
  · -- `y₀⁻¹` is in `O_{Gm}` but not in `O_{Gj}`
    have h1 : y₀⁻¹ ∈ Gm.valuationSubring := by
      rw [Valuation.mem_valuationSubring_iff, map_inv₀, hGm1, inv_one]
    rw [heq, Valuation.mem_valuationSubring_iff, map_inv₀] at h1
    have h0 : Gj y₀ ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
    exact absurd h1 (not_le.2 ((one_lt_inv₀ (pos_iff_ne_zero.2 h0)).2 hGj))

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
