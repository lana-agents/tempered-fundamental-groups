/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Chart
import TemperedFundamentalGroups.SemistableReduction.Type3Value
import TemperedFundamentalGroups.SemistableReduction.TypeThreeGermTwo
import TemperedFundamentalGroups.SemistableReduction.TypeTwoGerm

/-!
# Exact node data on the inverted charts around a type-3 point

Blueprint §9.10a (II.2)–(II.4). Let `ρ ∉ |C^×|`. For every extension `ξ` of `w_{0,ρ}` to `F` we
fix (`exists_fixed_data`)

* `d ≥ e(ξ)` and `u` with `ξ(u)ᵈ ρ = |c₀|`, `|c₀| ≥ ρ`, `u ≡ 1` at the other extensions;
* `S` with `ξ(S) = 1` and `ξ'(S) < ρ / |c₀|` at the other extensions.

These finitely many elements are integral near `ρ` (`near_valuation_le_one`) and have finitely many
poles. Hence there are `r₁ < ρ < |C₀|` such that for every chart `s = κ / (x - b)`
(`κ = c₃ C₀`, `r₁ ≤ |κ| < ρ`, `|b| ≤ |κ|`) the elements `S`, `μ u` (`μᵈ = κ / c₀`) and
`S s / (μ u)ᵈ` are good (`isGood_chart`), and every point over the node of the chart has exact node
data (**`exists_chart_nodeData`**, via `exists_nodeData_of_type3`).

**The two-sided type-3 germ** (`S8A.typeThreeGermTwoFor`, Blueprint §9.12 O6.1h): for an edge
`D(a, |c₁|) ⊊ D(a, |c₂|)` with `r₁ ≤ |c₁| < ρ < |c₂| ≤ ρ₂` and a representation `(a', c, c')`, the
inverted coordinate `c' / ((x - a') / c) = c c' / (x - a')` is the chart coordinate with
`b = a' - a`, `c₃ = c c' / C₀` (over `Aff a 1 F`); R4(i) (`isNodeODP_of_le`) shrinks the annulus
from `|C₀|` to `|c|`, and `nodeGood_of_inv` returns to the coordinate `(x - a') / c`. Hence
`S8A.typeThreeGermFor : TypeThreeGermFor C F` (the `W7.Leaves.typeThree` leaf), unconditionally.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace Type3

open AffineTwist GaussTube GaussStability FundamentalInequality TypeThree GaussFibre
  ZariskiModel PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [hST : IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

section Values

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma val_C {t : ℝ≥0ˣ} (v : GaussExtension (0 : C) t F) (c : C) :
    v.1 (algebraMap C F c) = ‖c‖₊ := by
  rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, ← Valuation.comap_apply, v.2, gaussRat_C]

omit [IsAlgClosed C] [Algebra C F] [FiniteDimensional (RatFunc C) F] hST in
lemma val_xF {t : ℝ≥0ˣ} (v : GaussExtension (0 : C) t F) : v.1 (xF C F) = t := by
  change v.1 (algebraMap (RatFunc C) F RatFunc.X) = t
  rw [← Valuation.comap_apply, v.2, gaussRat_X]

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
lemma val_xF_sub {t : ℝ≥0ˣ} (v : GaussExtension (0 : C) t F) {b : C} (hb : ‖b‖₊ ≤ t) :
    v.1 (xF C F - algebraMap C F b) = t := by
  have h : xF C F - algebraMap C F b =
      algebraMap (RatFunc C) F (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) := by
    rw [map_sub, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C,
      IsScalarTower.algebraMap_apply C (RatFunc C) F]
    rfl
  rw [h, ← Valuation.comap_apply, v.2, gaussRat_X_sub_C, max_eq_right hb]

variable (F) in
/-- Extensions of equal Gauss points. -/
def gaussExtCongr {r r' : ℝ≥0ˣ} (h : r = r') :
    GaussExtension (0 : C) r F ≃ GaussExtension (0 : C) r' F where
  toFun v := ⟨v.1, h ▸ v.2⟩
  invFun v := ⟨v.1, h ▸ v.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Values

section Fixed

variable [Algebra.IsSeparable (RatFunc C) F]

/-- **The fixed elements at an extension `ξ` of a type-3 point.** -/
theorem exists_fixed_data {ρ : ℝ≥0} (hρ : IsIrrat C ρ) {ρu : ℝ≥0ˣ} (hρu : (ρu : ℝ≥0) = ρ)
    (ξ : GaussExtension (0 : C) ρu F) :
    ∃ (d : ℕ) (u S : F) (c₀ : C), 1 ≤ d ∧ ramificationIdx (RatFunc C) ξ.1 ≤ d ∧ c₀ ≠ 0 ∧
      ξ.1 u ^ d * ρ = ‖c₀‖₊ ∧ ξ.1 S = 1 ∧
      (∀ η : GaussExtension (0 : C) ρu F, η ≠ ξ → η.1 S < 1) ∧
      ∀ η : GaussExtension (0 : C) ρu F, η.1 S ≤ 1 ∧
        η.1 (u ^ d * xF C F / algebraMap C F c₀) ≤ 1 ∧
        η.1 (S * algebraMap C F c₀ / (xF C F * u ^ d)) ≤ 1 := by
  classical
  obtain ⟨d, z, c, hd, hed, hc, hzc⟩ := exists_coord_value hρ hρu ξ
  have hρ0 : ρ ≠ 0 := hρ.pos.ne'
  have hc0 : ‖c‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 hc
  obtain ⟨l, hl⟩ := NormedField.exists_lt_nnnorm C (max 1 (ρ / ‖c‖₊))
  have hl1 : 1 ≤ ‖l‖₊ := (le_max_left _ _).trans hl.le
  have hl0 : ‖l‖₊ ≠ 0 := (lt_of_lt_of_le one_pos hl1).ne'
  set c₀ := l ^ d * c
  have hc₀n : ‖c₀‖₊ = ‖l‖₊ ^ d * ‖c‖₊ := by rw [nnnorm_mul, nnnorm_pow]
  have hc₀ : c₀ ≠ 0 := by
    rw [← nnnorm_ne_zero_iff, hc₀n]; exact mul_ne_zero (pow_ne_zero _ hl0) hc0
  have hc₀0 : ‖c₀‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 hc₀
  have hρc₀ : ρ ≤ ‖c₀‖₊ := by
    have h1 : ρ / ‖c‖₊ ≤ ‖l‖₊ := (le_max_right _ _).trans hl.le
    have h2 : ‖l‖₊ ≤ ‖l‖₊ ^ d := le_self_pow₀ hl1 (by omega)
    rw [hc₀n]
    calc ρ = ρ / ‖c‖₊ * ‖c‖₊ := (div_mul_cancel₀ ρ hc0).symm
      _ ≤ ‖l‖₊ ^ d * ‖c‖₊ := mul_le_mul_left (h1.trans h2) _
  clear_value c₀
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_pow (by omega), zero_mul] at hzc
    exact hc0 hzc.symm
  set lz := algebraMap C F l * z
  have hlz : ξ.1 lz = ‖l‖₊ * ξ.1 z := by rw [map_mul, val_C]
  have hlz0 : 0 < ξ.1 lz := by
    rw [hlz]
    exact pos_iff_ne_zero.2 (mul_ne_zero hl0 ((Valuation.ne_zero_iff _).2 hz))
  -- the coordinate `u`
  obtain ⟨u, hu⟩ := exists_approx_ext (r := ρu) (fun η ↦ if η = ξ then lz else 1)
    (ε := min 1 (ξ.1 lz)) (lt_min one_pos hlz0)
  have huξ : ξ.1 u = ξ.1 lz := by
    have h := hu ξ
    rw [if_pos rfl] at h
    exact Valuation.map_eq_of_sub_lt _ (h.trans_le (min_le_right _ _))
  have huη : ∀ η : GaussExtension (0 : C) ρu F, η ≠ ξ → η.1 u = 1 := by
    intro η hη
    have h := hu η
    rw [if_neg hη] at h
    have := Valuation.map_eq_of_sub_lt η.1 ((h.trans_le (min_le_left _ _)).trans_eq
      (map_one η.1).symm)
    rwa [map_one] at this
  -- the separating element `S`
  have hq : 0 < ρ / ‖c₀‖₊ := div_pos hρ.pos (pos_iff_ne_zero.2 hc₀0)
  have hq1 : ρ / ‖c₀‖₊ ≤ 1 := div_le_one_of_le₀ hρc₀ zero_le
  obtain ⟨S, hS⟩ := exists_approx_ext (r := ρu) (fun η ↦ if η = ξ then 1 else 0)
    (ε := min 1 (ρ / ‖c₀‖₊)) (lt_min one_pos hq)
  have hSξ : ξ.1 S = 1 := by
    have h := hS ξ
    rw [if_pos rfl] at h
    have := Valuation.map_eq_of_sub_lt ξ.1 ((h.trans_le (min_le_left _ _)).trans_eq
      (map_one ξ.1).symm)
    rwa [map_one] at this
  have hSη : ∀ η : GaussExtension (0 : C) ρu F, η ≠ ξ → η.1 S < ρ / ‖c₀‖₊ := by
    intro η hη
    have h := hS η
    rw [if_neg hη, sub_zero] at h
    exact h.trans_le (min_le_right _ _)
  have hkey : ξ.1 u ^ d * ρ = ‖c₀‖₊ := by
    rw [huξ, hlz, mul_pow, mul_assoc, hzc, hc₀n]
  refine ⟨d, u, S, c₀, hd, hed, hc₀, hkey, hSξ, fun η hη ↦ (hSη η hη).trans_le hq1,
    fun η ↦ ?_⟩
  have hv2 : η.1 (u ^ d * xF C F / algebraMap C F c₀) = η.1 u ^ d * ρ / ‖c₀‖₊ := by
    rw [map_div₀, map_mul, map_pow, val_xF, val_C, hρu]
  have hv3 : η.1 (S * algebraMap C F c₀ / (xF C F * u ^ d)) =
      η.1 S * ‖c₀‖₊ / (ρ * η.1 u ^ d) := by
    rw [map_div₀, map_mul, map_mul, map_pow, val_xF, val_C, hρu]
  rw [hv2, hv3]
  by_cases hη : η = ξ
  · subst hη
    rw [hSξ, one_mul, mul_comm ρ, hkey, div_self hc₀0]
    exact ⟨le_rfl, le_rfl, le_rfl⟩
  · rw [huη η hη, one_pow, one_mul, mul_one]
    refine ⟨((hSη η hη).trans_le hq1).le, hq1, ?_⟩
    rw [div_le_one (pos_iff_ne_zero.2 hρ0)]
    calc η.1 S * ‖c₀‖₊ ≤ ρ / ‖c₀‖₊ * ‖c₀‖₊ := mul_le_mul_left (hSη η hη).le _
      _ = ρ := div_mul_cancel₀ ρ hc₀0

end Fixed

section Chart

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) F]

include hp hp1 in
/-- **Exact node data on the inverted charts around a type-3 point.** There are `r₁ < ρ < |C₀|`
such that for every chart `s = c₃ C₀ / (x - b)` with `r₁ ≤ |c₃ C₀| < ρ` and `|b| ≤ |c₃ C₀|`, every
point over the node of `O_C[s, c₃/s]` has exactly one outer branch and exact node data. -/
theorem exists_chart_nodeData {ρ : ℝ≥0} (hρ : IsIrrat C ρ) :
    ∃ r₁ : ℝ≥0, r₁ < ρ ∧ ∃ (C₀ : C) (hC₀ : C₀ ≠ 0), ρ < ‖C₀‖₊ ∧
      ∀ (b c₃ : C) (hc₃ : c₃ ≠ 0) (hc₃1 : ‖c₃‖ < 1), r₁ ≤ ‖c₃ * C₀‖₊ → ‖c₃ * C₀‖₊ < ρ →
        ‖b‖₊ ≤ ‖c₃ * C₀‖₊ →
        ∀ P' : Ideal (Rint c₃ (Chart F b C₀ c₃ hC₀ hc₃)), P'.IsMaximal →
          P'.comap (algebraMap (nodeRing c₃) (Rint c₃ (Chart F b C₀ c₃ hC₀ hc₃))) =
            tubeIdeal c₃ →
          ∃ b₁ : OuterBranch C (Chart F b C₀ c₃ hC₀ hc₃), outerBranches hc₃1 P' = {b₁} ∧
            Nonempty (NodeData hc₃1 P' b₁) := by
  classical
  have hρ0 : ρ ≠ 0 := hρ.pos.ne'
  set ρu : ℝ≥0ˣ := Units.mk0 ρ hρ0
  have hρu : (ρu : ℝ≥0) = ρ := rfl
  haveI : Finite (GaussExtension (0 : C) ρu F) := finite_gaussExtension 0 ρu
  letI : Fintype (GaussExtension (0 : C) ρu F) := Fintype.ofFinite _
  choose d u S c₀ hd hed hc₀ hkey hSξ hSη hbd using exists_fixed_data (F := F) hρ hρu
  choose ZS hZS using fun ξ ↦ exists_mul_prod_isIntegral (C := C) (F' := F) (S ξ)
  choose Zu hZu using fun ξ ↦ exists_mul_prod_isIntegral (C := C) (F' := F) (u ξ)
  choose Zi hZi using fun ξ ↦ exists_mul_prod_isIntegral (C := C) (F' := F) (u ξ)⁻¹
  set Zall : Finset C := Finset.univ.biUnion fun ξ ↦ (ZS ξ + Zu ξ + Zi ξ).toFinset
  -- the radii near `ρ`
  have hnear : Near ρ fun s ↦ (∀ ξ, ∀ v : GaussExtension (0 : C) s F, v.1 (S ξ) ≤ 1 ∧
      v.1 (u ξ ^ d ξ * xF C F / algebraMap C F (c₀ ξ)) ≤ 1 ∧
      v.1 (S ξ * algebraMap C F (c₀ ξ) / (xF C F * u ξ ^ d ξ)) ≤ 1) ∧
      ∀ z ∈ Zall, ‖z‖₊ ≠ (s : ℝ≥0) := by
    refine (near_forall hρ.pos fun ξ ↦ ?_).and (near_finset hρ.pos Zall fun z _ ↦ ?_)
    · have h1 := near_valuation_le_one hρ hρu (y := S ξ) fun η ↦ (hbd ξ η).1
      have h2 := near_valuation_le_one hρ hρu fun η ↦ (hbd ξ η).2.1
      have h3 := near_valuation_le_one hρ hρu fun η ↦ (hbd ξ η).2.2
      exact (h1.and (h2.and h3)).mono fun s hs v ↦ ⟨hs.1 v, hs.2.1 v, hs.2.2 v⟩
    · exact near_of_eventually hρ.pos (P := fun t ↦ ‖z‖₊ ≠ t)
        ((eventually_ne_nhds (hρ z).symm).mono fun t ht ↦ Ne.symm ht)
  obtain ⟨s₁, s₂, hs₁, hs₂, hs⟩ := hnear
  have hroot : ∀ z ∈ Zall, ‖z‖₊ ≤ s₁ ∨ s₂ ≤ ‖z‖₊ := by
    intro z hz
    by_contra! h
    have hz0 : ‖z‖₊ ≠ 0 := (lt_of_le_of_lt zero_le h.1).ne'
    exact (hs (Units.mk0 _ hz0) h.1 h.2).2 z hz rfl
  obtain ⟨r₁, hr₁a, hr₁b⟩ := exists_between hs₁
  obtain ⟨C₀, hC₀a, hC₀b⟩ := EdgeRepair.exists_norm_mem_Ioo (C := C)
    (show (0 : ℝ) < ρ from hρ.pos) (show (ρ : ℝ) < s₂ from hs₂)
  have hC₀a' : ρ < ‖C₀‖₊ := by exact_mod_cast hC₀a
  have hC₀b' : ‖C₀‖₊ < s₂ := by exact_mod_cast hC₀b
  have hC₀ : C₀ ≠ 0 := by
    rintro rfl
    rw [nnnorm_zero] at hC₀a'
    exact (zero_le).not_gt hC₀a'
  refine ⟨r₁, hr₁b, C₀, hC₀, hC₀a', fun b c₃ hc₃ hc₃1 hr hκρ hb P' hmax hP ↦ ?_⟩
  haveI := hmax
  set κ := c₃ * C₀ with hκ_def
  have hκ0 : κ ≠ 0 := mul_ne_zero hc₃ hC₀
  have hκpos : 0 < ‖κ‖₊ := nnnorm_pos.2 hκ0
  have hc₃0 : 0 < ‖c₃‖₊ := nnnorm_pos.2 hc₃
  have hκn : ‖κ‖₊ = ‖c₃‖₊ * ‖C₀‖₊ := nnnorm_mul _ _
  have hb' : ‖b‖ ≤ ‖c₃ * C₀‖ := by exact_mod_cast hb
  -- radii between the boundary radii lie in `(s₁, s₂)`
  have hsb : ∀ t : ℝ≥0ˣ, ‖κ‖₊ ≤ (t : ℝ≥0) → (t : ℝ≥0) ≤ ‖C₀‖₊ → ∀ ξ,
      ∀ v : GaussExtension (0 : C) t F, v.1 (S ξ) ≤ 1 ∧
        v.1 (u ξ ^ d ξ * xF C F / algebraMap C F (c₀ ξ)) ≤ 1 ∧
        v.1 (S ξ * algebraMap C F (c₀ ξ) / (xF C F * u ξ ^ d ξ)) ≤ 1 :=
    fun t h1 h2 ↦ (hs t (lt_of_lt_of_le hr₁a (hr.trans h1)) (h2.trans_lt hC₀b')).1
  have hZall : ∀ z ∈ Zall, ‖z‖ ≤ ‖κ‖ ∨ ‖C₀‖ ≤ ‖z‖ := by
    intro z hz
    rcases hroot z hz with h | h
    · left
      have : ‖z‖₊ ≤ ‖κ‖₊ := h.trans (hr₁a.le.trans hr)
      exact_mod_cast this
    · right
      have : ‖C₀‖₊ ≤ ‖z‖₊ := hC₀b'.le.trans h
      exact_mod_cast this
  have hmemS : ∀ ξ, ∀ z ∈ ZS ξ, z ∈ Zall := fun ξ z hz ↦ Finset.mem_biUnion.2
    ⟨ξ, Finset.mem_univ _, Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inl
      (Multiset.mem_add.2 (Or.inl hz))))⟩
  have hmemu : ∀ ξ, ∀ z ∈ Zu ξ, z ∈ Zall := fun ξ z hz ↦ Finset.mem_biUnion.2
    ⟨ξ, Finset.mem_univ _, Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inl
      (Multiset.mem_add.2 (Or.inr hz))))⟩
  have hmemi : ∀ ξ, ∀ z ∈ Zi ξ, z ∈ Zall := fun ξ z hz ↦ Finset.mem_biUnion.2
    ⟨ξ, Finset.mem_univ _, Multiset.mem_toFinset.2 (Multiset.mem_add.2 (Or.inr hz))⟩
  -- good elements of the chart
  set G := Chart F b C₀ c₃ hC₀ hc₃
  have hgood : ∀ (y a : F) (Z : Multiset C), (∀ z ∈ Z, ‖z‖ ≤ ‖κ‖ ∨ ‖C₀‖ ≤ ‖z‖) →
      y * (Z.map fun z ↦ xF C F - algebraMap C F z).prod = a →
      IsIntegral (Algebra.adjoin C {xF C F}) a →
      (∀ t : ℝ≥0ˣ, ‖κ‖₊ ≤ (t : ℝ≥0) → (t : ℝ≥0) ≤ ‖C₀‖₊ →
        ∀ v : GaussExtension (0 : C) t F, v.1 y ≤ 1) →
      IsGood G c₃ (toChart F hC₀ hc₃ y) := by
    intro y a Z hZ hya ha hv
    refine isGood_chart hC₀ hc₃ hp hp1 hc₃1 hb' Z hZ hya ha (hv _ ?_ ?_) (hv _ ?_ ?_)
    · rw [coe_chartRad, Units.val_one, div_one]
    · rw [coe_chartRad, Units.val_one, div_one, hκn]
      exact mul_le_of_le_one_left zero_le (by exact_mod_cast hc₃1.le)
    · rw [coe_chartRad, coe_invRad, Units.val_one, div_one, hκn, mul_div_cancel_left₀ _ hc₃0.ne']
      exact mul_le_of_le_one_left zero_le (by exact_mod_cast hc₃1.le)
    · rw [coe_chartRad, coe_invRad, Units.val_one, div_one, hκn, mul_div_cancel_left₀ _ hc₃0.ne']
  have hgS : ∀ ξ, IsGood G c₃ (toChart F hC₀ hc₃ (S ξ)) := fun ξ ↦
    hgood (S ξ) _ (ZS ξ) (fun z hz ↦ hZall z (hmemS ξ z hz)) rfl (hZS ξ)
      fun t h1 h2 v ↦ (hsb t h1 h2 ξ v).1
  have hu0 : ∀ ξ, u ξ ≠ 0 := by
    intro ξ h0
    have := hkey ξ
    rw [h0, map_zero, zero_pow (by have := hd ξ; omega), zero_mul] at this
    exact hc₀ ξ (nnnorm_eq_zero.1 this.symm)
  have hx0 : xF C F ≠ 0 := by
    change algebraMap (RatFunc C) F RatFunc.X ≠ 0
    rw [map_ne_zero_iff _ (algebraMap (RatFunc C) F).injective]
    exact RatFunc.X_ne_zero
  have hxb : xF C F - algebraMap C F b ≠ 0 := by
    change algebraMap (RatFunc C) F RatFunc.X - algebraMap C F b ≠ 0
    rw [IsScalarTower.algebraMap_apply C (RatFunc C) F, ← map_sub,
      map_ne_zero_iff _ (algebraMap (RatFunc C) F).injective, sub_ne_zero]
    intro h
    have := congrArg RatFunc.intDegree h
    simp at this
  have hκF : algebraMap C F κ ≠ 0 := (_root_.map_ne_zero _).2 hκ0
  have hgu : ∀ ξ (μ : C), ‖μ‖₊ ^ d ξ = ‖κ‖₊ / ‖c₀ ξ‖₊ →
      IsGood G c₃ (toChart F hC₀ hc₃ (algebraMap C F μ * u ξ)) := by
    intro ξ μ hμ
    refine hgood _ (algebraMap C F μ * ((u ξ) * ((Zu ξ).map fun z ↦
      xF C F - algebraMap C F z).prod)) (Zu ξ) (fun z hz ↦ hZall z (hmemu ξ z hz)) (by ring)
      ((isIntegral_algebraMap (x := (⟨_, Subalgebra.algebraMap_mem _ μ⟩ :
        Algebra.adjoin C {xF C F}))).mul (hZu ξ)) fun t h1 h2 v ↦ ?_
    have h := (hsb t h1 h2 ξ v).2.1
    rw [map_div₀, map_mul, map_pow, val_xF, val_C] at h
    have hc0 : ‖c₀ ξ‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 (hc₀ ξ)
    have hd0 : d ξ ≠ 0 := by have := hd ξ; omega
    rw [map_mul, val_C, ← pow_le_one_iff_of_nonneg zero_le hd0, mul_pow, hμ]
    rw [div_le_one (pos_iff_ne_zero.2 hc0)] at h
    rw [div_mul_eq_mul_div, div_le_one (pos_iff_ne_zero.2 hc0)]
    calc ‖κ‖₊ * v.1 (u ξ) ^ d ξ ≤ (t : ℝ≥0) * v.1 (u ξ) ^ d ξ := mul_le_mul_left h1 _
      _ ≤ ‖c₀ ξ‖₊ := by rw [mul_comm]; exact h
  -- the element `S s / (μ u)ᵈ`
  set y₃ : (GaussExtension (0 : C) ρu F) → F := fun ξ ↦ S ξ * algebraMap C F (c₀ ξ) *
    (u ξ)⁻¹ ^ d ξ * (xF C F - algebraMap C F b)⁻¹
  have hgy₃ : ∀ ξ, IsGood G c₃ (toChart F hC₀ hc₃ (y₃ ξ)) := by
    intro ξ
    refine hgood _ (algebraMap C F (c₀ ξ) * ((S ξ) * ((ZS ξ).map fun z ↦
      xF C F - algebraMap C F z).prod) * ((u ξ)⁻¹ * ((Zi ξ).map fun z ↦
      xF C F - algebraMap C F z).prod) ^ d ξ) (ZS ξ + d ξ • Zi ξ + {b}) ?_ ?_ ?_ ?_
    · intro z hz
      rcases Multiset.mem_add.1 hz with hz | hz
      · rcases Multiset.mem_add.1 hz with hz | hz
        · exact hZall z (hmemS ξ z hz)
        · exact hZall z (hmemi ξ z (Multiset.mem_of_mem_nsmul hz))
      · rw [Multiset.mem_singleton.1 hz]
        exact Or.inl hb'
    · simp only [y₃, Multiset.map_add, Multiset.prod_add, Multiset.map_nsmul,
        Multiset.prod_nsmul, Multiset.map_singleton, Multiset.prod_singleton]
      field_simp
      ring
    · exact ((isIntegral_algebraMap (x := (⟨_, Subalgebra.algebraMap_mem _ (c₀ ξ)⟩ :
        Algebra.adjoin C {xF C F}))).mul (hZS ξ)).mul ((hZi ξ).pow _)
    · intro t h1 h2 v
      have h := (hsb t h1 h2 ξ v).2.2
      have heq : y₃ ξ = S ξ * algebraMap C F (c₀ ξ) / (xF C F * u ξ ^ d ξ) *
          (xF C F / (xF C F - algebraMap C F b)) := by
        have := hu0 ξ
        simp only [y₃, inv_pow]
        field_simp
      have hbt : ‖b‖₊ ≤ (t : ℝ≥0) := hb.trans h1
      rw [heq, map_mul, map_div₀ v.1 (xF C F), val_xF, val_xF_sub v hbt, div_self t.ne_zero,
        mul_one]
      exact h
  -- the chart at `ρ`
  set ρ' : ℝ≥0ˣ := Units.mk0 (‖κ‖₊ / ρ) (div_ne_zero hκpos.ne' hρ0)
  have hρ'v : (ρ' : ℝ≥0) = ‖κ‖₊ / ρ := rfl
  have hρseg : ρ' ∈ segment c₃ := by
    refine ⟨?_, ?_⟩
    · rw [hρ'v, lt_div_iff₀ hρ.pos, hκn]
      exact mul_lt_mul_of_pos_left hC₀a' hc₃0
    · rw [hρ'v, div_lt_one hρ.pos]
      exact hκρ
  have hirr' : ∀ z : C, ‖z‖₊ ≠ (ρ' : ℝ≥0) := by
    intro z hz
    rw [hρ'v] at hz
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [nnnorm_zero] at hz
      exact (div_ne_zero hκpos.ne' hρ0) hz.symm
    refine hρ (κ / z) ?_
    rw [nnnorm_div, hz, div_div_cancel₀ hκpos.ne']
  have hbt : ‖b‖₊ * ρ' ≤ ‖κ‖₊ := by
    rw [hρ'v, mul_div_assoc', div_le_iff₀ hρ.pos, mul_comm ‖κ‖₊]
    exact mul_le_mul_left (hb.trans hκρ.le) _
  have hrad : chartRad hC₀ hc₃ ρ' = ρu := Units.ext (by
    rw [coe_chartRad, hρ'v, hρu, div_div_cancel₀ hκpos.ne'])
  set E : GaussExtension (0 : C) ρ' G ≃ GaussExtension (0 : C) ρu F :=
    (chartExt hC₀ hc₃ ρ' hbt).trans (gaussExtCongr F hrad)
  have hE : ∀ ν y, (E ν).1 y = ν.1 (toChart F hC₀ hc₃ y) := fun _ _ ↦ rfl
  have heE : ∀ ν, ramificationIdx (RatFunc C) (E ν).1 = ramificationIdx (RatFunc C) ν.1 :=
    fun ν ↦ ramificationIdx_chartExt hC₀ hc₃ hbt ν
  refine exists_nodeData_of_type3 hp hp1 hc₃1 hc₃ hρseg hirr' (fun ν ν' hne ↦ ?_)
    (fun ν ↦ ?_) P' hP
  · refine ⟨toChart F hC₀ hc₃ (S (E ν')), hgS _, ?_, ?_⟩
    · rw [← hE]
      exact hSη (E ν') (E ν) fun h ↦ hne (E.injective h)
    · rw [← hE]
      exact hSξ (E ν')
  · set ξ := E ν
    have hd0 : 0 < d ξ := hd ξ
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_pow_nat_eq (κ / c₀ ξ) hd0
    have hμn : ‖μ‖₊ ^ d ξ = ‖κ‖₊ / ‖c₀ ξ‖₊ := by rw [← nnnorm_pow, hμ, nnnorm_div]
    have hc0 : algebraMap C F (c₀ ξ) ≠ 0 := (_root_.map_ne_zero _).2 (hc₀ ξ)
    have hxG : xF C G / toChart F hC₀ hc₃ (algebraMap C F μ * u ξ) ^ d ξ =
        toChart F hC₀ hc₃ (algebraMap C F κ / (xF C F - algebraMap C F b) /
          (algebraMap C F μ * u ξ) ^ d ξ) := by
      rw [xF_chart, ← map_pow, ← map_div₀]
    refine ⟨d ξ, toChart F hC₀ hc₃ (algebraMap C F μ * u ξ), toChart F hC₀ hc₃ (S ξ), hd ξ,
      (heE ν) ▸ hed ξ, hgu ξ μ hμn, hgS ξ, by rw [← hE]; exact hSξ ξ, ?_, ?_⟩
    · rw [hxG, ← map_mul]
      convert hgy₃ ξ using 2
      simp only [y₃, inv_pow]
      rw [mul_pow, ← map_pow, hμ, map_div₀]
      have := hu0 ξ
      field_simp
    · rw [hxG, ← hE, map_div₀, map_div₀, map_pow, map_mul (E ν).1 (algebraMap C F μ), val_C, val_C,
        val_xF_sub ξ (hb.trans hκρ.le), hρu, mul_pow, hμn]
      have hc0n : ‖c₀ ξ‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 (hc₀ ξ)
      have hk := hkey ξ
      have hne : ρ * (‖κ‖₊ / ‖c₀ ξ‖₊ * ξ.1 (u ξ) ^ d ξ) ≠ 0 :=
        mul_ne_zero hρ0 (mul_ne_zero (div_ne_zero hκpos.ne' hc0n)
          (pow_ne_zero _ ((Valuation.ne_zero_iff _).2 (hu0 ξ))))
      rw [div_div, div_eq_one_iff_eq hne, mul_left_comm, mul_comm ρ, hk,
        div_mul_cancel₀ _ hc0n]

end Chart

omit [IsAlgClosed C] in
/-- The chart coordinate over `Aff a 1 F` is the inverted coordinate of `(x - a') / c`. -/
lemma chart_aff_eq {a b a' C₀ c₃ c c' : C} (hC₀ : C₀ ≠ 0) (hc₃ : c₃ ≠ 0) (hc : c ≠ 0)
    (hc' : c' ≠ 0) (hab : a + b = a') (hκ : c₃ * C₀ = c * c') (φ : RatFunc C) :
    aff a 1 one_ne_zero (aff b C₀ hC₀ (inv hc₃ (aff 0 1 one_ne_zero φ))) =
      aff a' c hc (inv hc' φ) := by
  rw [aff_zero_one]
  have h := congrArg (fun χ : RatFunc C →ₐ[C] RatFunc C ↦ χ φ)
    (ratFunc_algHom_ext
      (φ := ((aff a 1 one_ne_zero).toAlgHom.comp (aff b C₀ hC₀).toAlgHom).comp (inv hc₃).toAlgHom)
      (ψ := (aff a' c hc).toAlgHom.comp (inv hc').toAlgHom) ?_)
  · exact h
  subst hab
  obtain rfl : c₃ = c * c' / C₀ := (eq_div_iff hC₀).2 hκ
  simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, aff_apply, inv_apply, affHom_X, invHom_X,
    map_div₀, AlgHom.commutes, gaussCoord_eq, map_mul, map_sub, map_inv₀, inv_one, map_one,
    one_mul, map_add]
  have hX : ∀ e : C, (RatFunc.X : RatFunc C) - algebraMap C (RatFunc C) e ≠ 0 := by
    intro e h0
    have := congrArg RatFunc.intDegree (sub_eq_zero.1 h0)
    simp at this
  have hC : algebraMap C (RatFunc C) C₀ ≠ 0 := by simpa using hC₀
  have hc0 : algebraMap C (RatFunc C) c ≠ 0 := by simpa using hc
  have h2 : (RatFunc.X : RatFunc C) - algebraMap C (RatFunc C) a -
      algebraMap C (RatFunc C) b ≠ 0 := by
    rw [sub_sub, ← map_add]
    exact hX (a + b)
  field_simp
  linear_combination (-(algebraMap C (RatFunc C) c')) * mul_inv_cancel₀ h2

end Type3

namespace S8A

open GaussTube AffineTwist Type3 TypeThree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- **O6.1h: the two-sided germ of annuli at a type-3 point**, unconditional. -/
theorem typeThreeGermTwoFor : TypeThreeGermTwoFor C F := by
  intro a ρ hρ hirr
  set ρn : NNReal := ⟨ρ, hρ.le⟩
  have hirr' : IsIrrat C ρn := fun z hz ↦ hirr z (by
    rw [← coe_nnnorm, hz]
    rfl)
  obtain ⟨r₁, hr₁, C₀, hC₀, hC₀ρ, H⟩ :=
    exists_chart_nodeData (F := Aff a 1 one_ne_zero F) hp hp1 hirr'
  have hC₀ρ' : ρ < ‖C₀‖ := by
    have : (ρn : ℝ) < ‖C₀‖₊ := by exact_mod_cast hC₀ρ
    exact this
  have hr₁' : (r₁ : ℝ) < ρ := by
    have : (r₁ : ℝ) < ρn := by exact_mod_cast hr₁
    exact this
  refine ⟨r₁, hr₁', (ρ + ‖C₀‖) / 2, by linarith,
    fun c₁ c₂ hc₁0 hr hc₁ρ hρc₂ hc₂ρ₂ ↦ ?_⟩
  intro a' c c' hc hc' hc0' hE hG
  have hc₂0 : c₂ ≠ 0 := by
    rintro rfl
    rw [norm_zero] at hρc₂
    linarith
  obtain ⟨h1, h2⟩ := (BallTree.closedBall_eq_closedBall_iff' hc₁0 (mul_ne_zero hc hc0')).1 hE
  obtain ⟨h3, -⟩ := (BallTree.closedBall_eq_closedBall_iff' hc₂0 hc).1 hG
  set b := a' - a
  set c₃ := c * c' / C₀
  have hc₃ : c₃ ≠ 0 := div_ne_zero (mul_ne_zero hc hc0') hC₀
  have hκ : c₃ * C₀ = c * c' := div_mul_cancel₀ _ hC₀
  have hcC : ‖c‖ < ‖C₀‖ := by rw [← h3]; linarith
  have hlt : ‖c₃‖ < ‖c'‖ := by
    rw [norm_div, norm_mul, div_lt_iff₀ (norm_pos_iff.2 hC₀)]
    have := norm_pos_iff.2 hc0'
    nlinarith
  have hc₃1 : ‖c₃‖ < 1 := hlt.trans hc'
  have hr' : r₁ ≤ ‖c₃ * C₀‖₊ := by
    rw [hκ]
    have : (r₁ : ℝ) ≤ ‖c * c'‖ := h1 ▸ hr
    exact_mod_cast this
  have hκρ : ‖c₃ * C₀‖₊ < ρn := by
    rw [hκ]
    have : ‖c * c'‖ < (ρn : ℝ) := h1 ▸ hc₁ρ
    exact_mod_cast this
  have hb : ‖b‖₊ ≤ ‖c₃ * C₀‖₊ := by
    rw [hκ]
    have : ‖b‖ ≤ ‖c * c'‖ := by
      rw [norm_sub_rev, ← h1]
      exact h2
    exact_mod_cast this
  set G := Chart (Aff a 1 one_ne_zero F) b C₀ c₃ hC₀ hc₃
  have hNG : NodeGood G c' hc' hc0' := by
    intro P'' hmax hP''
    set P' := P''.comap (rintMap (F' := G) (nodeRing_le hlt.le hc0'))
    have hcomap := comap_rintMap_comap hc' hc0' hlt P'' hP''
    haveI : P'.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := nodeRing c₃) _
        (by rw [hcomap]; exact tubeIdeal_isMaximal hc₃1 hc₃)
    obtain ⟨b₁, hb₁, ⟨N⟩⟩ := H b c₃ hc₃ hc₃1 hr' hκρ hb P' inferInstance hcomap
    exact isNodeODP_of_le hp hp1 hc₃1 hc' hc₃ hc0' hlt P'' hP'' rfl hb₁ N
  have hinv : NodeGood (GaussTube.Inv c' hc0' (Aff a' c hc F)) c' hc' hc0' := by
    let e : G ≃+* GaussTube.Inv c' hc0' (Aff a' c hc F) := RingEquiv.refl F
    refine nodeGood_of_algebraMap_eq e (fun φ ↦ ?_) hc' hc0' hNG
    change algebraMap (RatFunc C) F
        (aff a 1 one_ne_zero (aff b C₀ hC₀ (inv hc₃ (aff 0 1 one_ne_zero φ)))) =
      algebraMap (RatFunc C) F (aff a' c hc (inv hc0' φ))
    rw [chart_aff_eq (a' := a') hC₀ hc₃ hc hc0' (by simp [b]) hκ]
  exact nodeGood_of_inv hc' hc0' hinv

include hp hp1 in
/-- **O6.1h: the type-3 germ** (`W7.Leaves.typeThree`), unconditional: `DefinedOverDVR` is not
needed. -/
theorem typeThreeGermFor (_hdef : DefinedOverDVR C F) : TypeThreeGermFor C F :=
  typeThreeGermFor_of_two (typeThreeGermTwoFor hp hp1)

end S8A

end SemistableReduction
