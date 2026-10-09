/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Node

/-!
# Exact node data at an annulus through a type-3 point

Blueprint §9.10a (II.2), (II.3). Let `R' = Rint c G` be the normalized node chart of an annulus
`|c| < |x| < 1` containing a type-3 radius `ρ`. An element `y ∈ G` is *good* (`IsGood`) if
`τ y ∈ R'` for some `τ` of the node chart outside the node ideal. Suppose

* the extensions of `w_{0,ρ}` are separated by good elements (`hsep`), and
* every extension `ξ` of `w_{0,ρ}` has a good node coordinate `u` and a good `S` with `ξ(S) = 1`
  such that `S x / uᵈ` is good and `x / uᵈ` has value one at `ξ`, `d ≥ e(ξ)` (`hcoord`).

Then every point `P'` of `R'` over the node is the centre of exactly one extension `ξ` of
`w_{0,ρ}`; its vertex degree is the tube degree at `ρ`, i.e. `e(ξ) ≤ d` (STAB3), and `σ x = e uᵈ`
(`σ = τ₃ S τ₁`, `e = τ₃ τ₁ S x / uᵈ`) gives exact node data (`exists_nodeData_of_type3`).
-/

open Polynomial WithZero
open scoped NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm TubeCount

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {G : Type*} [Field G] [Algebra (RatFunc C) G] [Algebra C G]
  [IsScalarTower C (RatFunc C) G] [FiniteDimensional (RatFunc C) G]

variable (G) in
/-- `y` is good for the node chart `O_C[x, c/x]`: `τ y ∈ R'` for some `τ` outside the node ideal. -/
def IsGood (c : C) (y : G) : Prop :=
  ∃ τ : nodeRing c, τ ∉ tubeIdeal c ∧ IsIntegral (nodeRing c) (algebraMap (RatFunc C) G τ * y)

omit [IsAlgClosed C] [Algebra C G] [IsScalarTower C (RatFunc C) G]
  [FiniteDimensional (RatFunc C) G] in
/-- Elements of the node chart outside the node ideal have value one on the open segment. -/
lemma gaussRat_eq_one_of_notMem {c : C} {τ : nodeRing c} (hτ : τ ∉ tubeIdeal c) {s : ℝ≥0ˣ}
    (hs : s ∈ segment c) : gaussRat (NormedField.valuation (K := C)) 0 s τ = 1 :=
  le_antisymm (gaussRat_le_one τ.2 hs) (not_lt.1 fun h ↦ hτ ((mem_tubeIdeal_iff τ hs).2 h))

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) G]

include hp hp1 in
/-- **Exact node data at an annulus through a type-3 point.** -/
theorem exists_nodeData_of_type3 {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0) {ρ : ℝ≥0ˣ}
    (hρ : ρ ∈ segment c) (hirr : ∀ z : C, ‖z‖₊ ≠ (ρ : ℝ≥0))
    (hsep : ∀ ξ ξ' : GaussExtension (0 : C) ρ G, ξ ≠ ξ' →
      ∃ y : G, IsGood G c y ∧ ξ.1 y < 1 ∧ ξ'.1 y = 1)
    (hcoord : ∀ ξ : GaussExtension (0 : C) ρ G, ∃ (d : ℕ) (u S : G), 1 ≤ d ∧
      ramificationIdx (RatFunc C) ξ.1 ≤ d ∧ IsGood G c u ∧ IsGood G c S ∧ ξ.1 S = 1 ∧
        IsGood G c (S * (xF C G / u ^ d)) ∧ ξ.1 (xF C G / u ^ d) = 1)
    (P' : Ideal (Rint c G)) [P'.IsMaximal]
    (hP : P'.comap (algebraMap (nodeRing c) (Rint c G)) = tubeIdeal c) :
    ∃ b₁ : OuterBranch C G, outerBranches hc P' = {b₁} ∧ Nonempty (NodeData hc P' b₁) := by
  classical
  haveI : Finite (Ext C G) := finite_ext (F := G) hp hp1
  letI : Fintype (Ext C G) := Fintype.ofFinite _
  haveI : Finite (GaussExtension (0 : C) ρ G) := finite_gaussExtension 0 ρ
  letI : Fintype (GaussExtension (0 : C) ρ G) := Fintype.ofFinite _
  -- a radius `s` of the value group in the open segment
  obtain ⟨cs, hcs1, hcs2⟩ : ∃ cs : C, ‖c‖₊ < ‖cs‖₊ ∧ ‖cs‖₊ < 1 := by
    have h1 : ‖c‖₊ < 1 := by exact_mod_cast hc
    obtain ⟨t, ht1, ht2⟩ := exists_between h1
    obtain ⟨e, he1, he2⟩ := exists_nnnorm_between (C := C) ht2
    exact ⟨e, ht1.trans he1, he2⟩
  set s : ℝ≥0ˣ := Units.mk0 ‖cs‖₊ (ne_of_gt (lt_of_le_of_lt zero_le hcs1))
  have hs : s ∈ segment c := ⟨hcs1, hcs2⟩
  have hcss : NormedField.valuation cs = (s : ℝ≥0) := rfl
  haveI : Finite (GaussExtension (0 : C) s G) := finite_gaussExtension 0 s
  letI : Fintype (GaussExtension (0 : C) s G) := Fintype.ofFinite _
  have htube : tubeDegree hρ P' = vertexDegree hc P' := by
    rw [tubeDegree_eq_of_stable hc hc0 hρ hs (localStable_of_irrat hp hp1 hirr)
      (localStable_of_eq hp hp1 hcss) P', tubeDegree_eq_vertexDegree hp hp1 hc hc0 hs hcss P']
  -- some extension of `w_{0,ρ}` is centred at `P'`
  obtain ⟨w₀, hw₀⟩ := exists_center_eq hp hp1 hc hc0 hs hcss P' hP
  have hpos : 0 < tubeDegree hρ P' := by
    rw [tubeDegree_eq_of_stable hc hc0 hρ hs (localStable_of_irrat hp hp1 hirr)
      (localStable_of_eq hp hp1 hcss) P', tubeDegree]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ w₀, hw₀⟩))
    exact Nat.mul_pos (Nat.pos_of_ne_zero (ramificationIdx_ne_zero w₀.1))
      NormedTower.inertiaDeg_pos
  obtain ⟨ξ, hξ⟩ : ∃ ξ : GaussExtension (0 : C) ρ G, center hρ ξ = P' := by
    by_contra! hno
    rw [tubeDegree, Finset.filter_false_of_mem fun ξ _ ↦ hno ξ, Finset.sum_empty] at hpos
    exact lt_irrefl 0 hpos
  -- it is the only one
  have huniq : ∀ ξ' : GaussExtension (0 : C) ρ G, center hρ ξ' = P' → ξ' = ξ := by
    intro ξ' hξ'
    by_contra hne
    obtain ⟨y, ⟨τ, hτ, hint⟩, hy1, hy2⟩ := hsep ξ ξ' (Ne.symm hne)
    set z : Rint c G := ⟨_, hint⟩
    have hτρ := gaussRat_eq_one_of_notMem hτ hρ
    have hzv : ∀ η : GaussExtension (0 : C) ρ G, η.1 (z : G) = η.1 y := fun η ↦ by
      change η.1 (algebraMap (RatFunc C) G τ * y) = _
      rw [map_mul, ← Valuation.comap_apply, η.2, hτρ, one_mul]
    have hz : z ∈ P' := by rw [← hξ, mem_center_iff, hzv]; exact hy1
    rw [← hξ', mem_center_iff, hzv, hy2] at hz
    exact lt_irrefl 1 hz
  have htξ : tubeDegree hρ P' = ramificationIdx (RatFunc C) ξ.1 := by
    rw [tubeDegree, Finset.sum_eq_single_of_mem ξ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hξ⟩)
      fun ξ' hξ' hne ↦ absurd (huniq ξ' (Finset.mem_filter.1 hξ').2) hne,
      inertiaDeg_eq_one_of_irrat hp hp1 hirr, mul_one]
  -- the node coordinate
  obtain ⟨d, u, S, hd, hed, ⟨τ₂, hτ₂, hint₂⟩, ⟨τ₃, hτ₃, hint₃⟩, hS1, ⟨τ₁, hτ₁, hint₁⟩, hξ1⟩ :=
    hcoord ξ
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega), div_zero, map_zero] at hξ1
    exact zero_ne_one hξ1
  have hτρ₁ := gaussRat_eq_one_of_notMem hτ₁ hρ
  have hτρ₂ := gaussRat_eq_one_of_notMem hτ₂ hρ
  have hτρ₃ := gaussRat_eq_one_of_notMem hτ₃ hρ
  have hval : ∀ (τ : nodeRing c), gaussRat (NormedField.valuation (K := C)) 0 ρ τ = 1 →
      ξ.1 (algebraMap (RatFunc C) G τ) = 1 := fun τ hτ ↦ by
    rw [← Valuation.comap_apply, ξ.2, hτ]
  set σS : Rint c G := ⟨_, hint₃⟩
  set σ : Rint c G := σS * algebraMap (nodeRing c) (Rint c G) τ₁
  set e : Rint c G := algebraMap (nodeRing c) (Rint c G) τ₃ * ⟨_, hint₁⟩
  set σu : Rint c G := algebraMap (nodeRing c) (Rint c G) τ₂
  set uR : Rint c G := ⟨_, hint₂⟩
  have hσ : σ ∉ P' := by
    rw [← hξ, mem_center_iff]
    change ¬ ξ.1 (algebraMap (RatFunc C) G τ₃ * S * algebraMap (RatFunc C) G τ₁) < 1
    rw [map_mul, map_mul, hval τ₃ hτρ₃, hval τ₁ hτρ₁, hS1]
    simp
  have hσu : σu ∉ P' := by
    rw [← hξ, mem_center_iff]
    change ¬ ξ.1 (algebraMap (RatFunc C) G τ₂) < 1
    rw [hval τ₂ hτρ₂]
    exact lt_irrefl 1
  have he : e ∉ P' := by
    rw [← hξ, mem_center_iff]
    change ¬ ξ.1 (algebraMap (RatFunc C) G τ₃ *
      (algebraMap (RatFunc C) G τ₁ * (S * (xF C G / u ^ d)))) < 1
    rw [map_mul, map_mul, map_mul, hval τ₁ hτρ₁, hval τ₃ hτρ₃, hξ1, hS1]
    simp
  have hx : (σ : G) * xF C G = e * u ^ d := by
    change algebraMap (RatFunc C) G τ₃ * S * algebraMap (RatFunc C) G τ₁ * xF C G =
      algebraMap (RatFunc C) G τ₃ * (algebraMap (RatFunc C) G τ₁ * (S * (xF C G / u ^ d))) *
        u ^ d
    field_simp
  exact exists_nodeData_of_coord hc hp hp1 hc0 P' hP hd (htube ▸ htξ ▸ hed) u σ e hσ he hx uR σu
    hσu rfl

end GaussTube

end SemistableReduction
