/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Type3Core
import TemperedFundamentalGroups.SemistableReduction.TreeNode

/-!
# The inverted chart of an annulus

Blueprint §9.10a (II.4). For `b, C₀, c₃ ∈ C^×`-data let `κ = c₃ C₀` and `H` the field `F` with the
coordinate `s = κ / (x - b)` (`Chart`, the twist `Aff 0 1 (Inv c₃ (Aff b C₀ F))`). The node chart
`O_C[s, c₃/s]` of `H` is the annulus `|κ| ≤ |x - b| ≤ |C₀|` with its outer boundary at
`|x - b| = |κ|`.

* `algebraMap_chart`, `chartψ_X`, `chartψ_symm_X`: `H` is `F` twisted by `ψ`, `ψ(x) = s`;
* `gaussRat_chartψ_symm`: `w_{0,t} ∘ ψ⁻¹ = w_{0,|κ|/t}` if `|b| ≤ |κ|/t`;
* `chartExt`: the extensions of `w_{0,t}` to `H` are the extensions of `w_{0,|κ|/t}` to `F`.
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace Type3

open AffineTwist GaussTube GaussStability FundamentalInequality

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [hST : IsScalarTower C (RatFunc C) F]

local notation "w" => gaussRat (NormedField.valuation (K := C)) 0

variable (F) in
/-- The chart `s = c₃ C₀ / (x - b)`. -/
abbrev Chart (b C₀ c₃ : C) (hC₀ : C₀ ≠ 0) (hc₃ : c₃ ≠ 0) : Type _ :=
  Aff (0 : C) 1 one_ne_zero (GaussTube.Inv c₃ hc₃ (Aff b C₀ hC₀ F))

/-- The coordinate change of the chart. -/
noncomputable def chartψ (b C₀ c₃ : C) (hC₀ : C₀ ≠ 0) (hc₃ : c₃ ≠ 0) :
    RatFunc C ≃ₐ[C] RatFunc C :=
  (aff 0 1 one_ne_zero).trans ((inv hc₃).trans (aff b C₀ hC₀))

variable {b C₀ c₃ : C} (hC₀ : C₀ ≠ 0) (hc₃ : c₃ ≠ 0)

variable (F) in
/-- The identity `F → H`. -/
noncomputable def toChart : F ≃+* Chart F b C₀ c₃ hC₀ hc₃ := RingEquiv.refl F

omit [IsAlgClosed C] [Algebra C F] hST in
lemma algebraMap_chart (φ : RatFunc C) :
    algebraMap (RatFunc C) (Chart F b C₀ c₃ hC₀ hc₃) φ =
      toChart F hC₀ hc₃ (algebraMap (RatFunc C) F (chartψ b C₀ c₃ hC₀ hc₃ φ)) := rfl

omit [IsAlgClosed C] in
lemma aff_zero_one (φ : RatFunc C) : aff (0 : C) 1 one_ne_zero φ = φ := by
  have h : (aff (0 : C) 1 one_ne_zero).toAlgHom = AlgHom.id C (RatFunc C) := by
    refine ratFunc_algHom_ext ?_
    change aff (0 : C) 1 one_ne_zero RatFunc.X = RatFunc.X
    rw [aff_apply, affHom_X, gaussCoord_eq]
    simp
  exact congrArg (fun χ : RatFunc C →ₐ[C] RatFunc C ↦ χ φ) h

omit [IsAlgClosed C] in
lemma chartψ_X : chartψ b C₀ c₃ hC₀ hc₃ RatFunc.X =
    algebraMap C (RatFunc C) (c₃ * C₀) / (RatFunc.X - algebraMap C (RatFunc C) b) := by
  rw [chartψ, AlgEquiv.trans_apply, AlgEquiv.trans_apply, aff_zero_one, inv_apply, invHom_X,
    map_div₀, AlgEquiv.commutes, aff_apply, affHom_X, gaussCoord_eq]
  have hC : algebraMap C (RatFunc C) C₀ ≠ 0 := by simpa using hC₀
  rw [map_mul, map_inv₀]
  field_simp

omit [IsAlgClosed C] in
lemma chartψ_symm_X : (chartψ b C₀ c₃ hC₀ hc₃).symm RatFunc.X =
    algebraMap C (RatFunc C) b + algebraMap C (RatFunc C) (c₃ * C₀) / RatFunc.X := by
  apply (chartψ b C₀ c₃ hC₀ hc₃).injective
  rw [AlgEquiv.apply_symm_apply, map_add, map_div₀, AlgEquiv.commutes, AlgEquiv.commutes,
    chartψ_X]
  have hκ : algebraMap C (RatFunc C) (c₃ * C₀) ≠ 0 := by
    simpa using mul_ne_zero hc₃ hC₀
  have hXb : RatFunc.X - algebraMap C (RatFunc C) b ≠ 0 := by
    intro h
    have := congrArg RatFunc.intDegree (sub_eq_zero.1 h)
    simp at this
  field_simp
  ring

variable (b) in
/-- The radius `|κ| / t` corresponding to `t`. -/
noncomputable def chartRad (t : ℝ≥0ˣ) : ℝ≥0ˣ :=
  Units.mk0 ‖c₃ * C₀‖₊ (by simpa using mul_ne_zero hc₃ hC₀) * t⁻¹

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma coe_chartRad (t : ℝ≥0ˣ) : ((chartRad hC₀ hc₃ t : ℝ≥0ˣ) : ℝ≥0) = ‖c₃ * C₀‖₊ / t := by
  simp [chartRad, div_eq_mul_inv]

/-- **Gauss points under the chart**: `w_{0,t} ∘ ψ⁻¹ = w_{0,|κ|/t}` if `|b| ≤ |κ|/t`. -/
theorem gaussRat_chartψ_symm (t : ℝ≥0ˣ) (hbt : ‖b‖₊ * t ≤ ‖c₃ * C₀‖₊) (φ : RatFunc C) :
    w t ((chartψ b C₀ c₃ hC₀ hc₃).symm φ) = w (chartRad hC₀ hc₃ t) φ := by
  set κ := c₃ * C₀
  have ht0 : (t : ℝ≥0) ≠ 0 := t.ne_zero
  have hb : ‖b‖₊ ≤ ‖κ‖₊ / t := by rw [le_div_iff₀ (pos_iff_ne_zero.2 ht0)]; exact hbt
  have h := valuation_ratFunc_ext_of_linear
    (w₁ := (w t).comap (chartψ b C₀ c₃ hC₀ hc₃).symm.toRingEquiv.toRingHom)
    (w₂ := w (chartRad hC₀ hc₃ t)) (fun β ↦ ?_) (fun β ↦ ?_)
  · exact congrArg (fun v : Valuation (RatFunc C) ℝ≥0 ↦ v φ) h
  · change w t ((chartψ b C₀ c₃ hC₀ hc₃).symm (algebraMap C (RatFunc C) β)) = _
    rw [AlgEquiv.commutes, gaussRat_C, gaussRat_C]
  · change w t ((chartψ b C₀ c₃ hC₀ hc₃).symm (algebraMap C[X] (RatFunc C) (X - Polynomial.C β)))
      = _
    have hβ : algebraMap C[X] (RatFunc C) (Polynomial.C β) = algebraMap C (RatFunc C) β := by
      rw [IsScalarTower.algebraMap_apply C C[X] (RatFunc C)]; rfl
    rw [GaussTube.gaussRat_X_sub_C, _root_.map_sub, RatFunc.algebraMap_X, hβ, _root_.map_sub,
      AlgEquiv.commutes, chartψ_symm_X, coe_chartRad]
    have hX : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
    have e : algebraMap C (RatFunc C) b + algebraMap C (RatFunc C) κ / RatFunc.X -
        algebraMap C (RatFunc C) β = (algebraMap C (RatFunc C) κ -
          algebraMap C (RatFunc C) (β - b) * RatFunc.X) / RatFunc.X := by
      rw [map_sub]; field_simp; ring
    rw [e, map_div₀, gaussRat_C_sub_mul_X, AnnulusUnit.gaussRat_X, ← max_div_div_right zero_le,
      mul_div_cancel_right₀ _ ht0]
    -- `max (|κ|/t) |β - b| = max |β| (|κ|/t)`
    rcases le_or_gt ‖β‖₊ (‖κ‖₊ / t) with hβt | hβt
    · have h1 : ‖β - b‖₊ ≤ ‖κ‖₊ / t := by
        have := IsUltrametricDist.nnnorm_add_le_max β (-b)
        rw [← sub_eq_add_neg, nnnorm_neg] at this
        exact this.trans (max_le hβt hb)
      rw [max_eq_left h1, max_eq_right hβt]
    · have h1 : ‖β - b‖₊ = ‖β‖₊ := by
        have := IsUltrametricDist.nnnorm_add_eq_max_of_nnnorm_ne_nnnorm (x := β) (y := -b)
          (by rw [nnnorm_neg]; exact (hb.trans_lt hβt).ne')
        rwa [← sub_eq_add_neg, nnnorm_neg, max_eq_left (hb.trans hβt.le)] at this
      rw [h1, max_eq_right hβt.le, max_eq_left hβt.le]

/-- **Extensions under the chart.** -/
noncomputable def chartExt (t : ℝ≥0ˣ) (hbt : ‖b‖₊ * t ≤ ‖c₃ * C₀‖₊) :
    GaussExtension (0 : C) t (Chart F b C₀ c₃ hC₀ hc₃) ≃
      GaussExtension (0 : C) (chartRad hC₀ hc₃ t) F where
  toFun v := ⟨v.1.comap (toChart F hC₀ hc₃).toRingHom, Valuation.ext fun φ ↦ by
    have h := congrArg (fun u : Valuation (RatFunc C) ℝ≥0 ↦ u ((chartψ b C₀ c₃ hC₀ hc₃).symm φ))
      v.2
    simp only [Valuation.comap_apply, algebraMap_chart, AlgEquiv.apply_symm_apply] at h
    rw [Valuation.comap_apply, Valuation.comap_apply, ← gaussRat_chartψ_symm hC₀ hc₃ t hbt, ← h]
    rfl⟩
  invFun v := ⟨v.1.comap (toChart F hC₀ hc₃).symm.toRingHom, Valuation.ext fun φ ↦ by
    rw [Valuation.comap_apply, Valuation.comap_apply, algebraMap_chart]
    change v.1 ((toChart F hC₀ hc₃).symm (toChart F hC₀ hc₃
      (algebraMap (RatFunc C) F (chartψ b C₀ c₃ hC₀ hc₃ φ)))) = _
    rw [RingEquiv.symm_apply_apply, ← Valuation.comap_apply, v.2,
      ← gaussRat_chartψ_symm hC₀ hc₃ t hbt, AlgEquiv.symm_apply_apply]⟩
  left_inv _ := rfl
  right_inv _ := rfl

omit [Algebra C F] hST in
lemma chartExt_apply {t : ℝ≥0ˣ} (hbt : ‖b‖₊ * t ≤ ‖c₃ * C₀‖₊)
    (v : GaussExtension (0 : C) t (Chart F b C₀ c₃ hC₀ hc₃)) (y : F) :
    (chartExt hC₀ hc₃ t hbt v).1 y = v.1 (toChart F hC₀ hc₃ y) := rfl

omit [Algebra C F] hST in
/-- The ramification index is unchanged by the chart. -/
lemma ramificationIdx_chartExt {t : ℝ≥0ˣ} (hbt : ‖b‖₊ * t ≤ ‖c₃ * C₀‖₊)
    (v : GaussExtension (0 : C) t (Chart F b C₀ c₃ hC₀ hc₃)) :
    ramificationIdx (RatFunc C) (chartExt hC₀ hc₃ t hbt v).1 = ramificationIdx (RatFunc C) v.1 := by
  have h1 : valueGroup (chartExt hC₀ hc₃ t hbt v).1 = valueGroup v.1 := by
    ext g
    simp only [mem_valueGroup_iff]
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨toChart F hC₀ hc₃ x, hx⟩, fun ⟨x, hx⟩ ↦
      ⟨(toChart F hC₀ hc₃).symm x, hx⟩⟩
  have h2 : valueGroup ((chartExt hC₀ hc₃ t hbt v).1.comap (algebraMap (RatFunc C) F)) =
      valueGroup (v.1.comap (algebraMap (RatFunc C) (Chart F b C₀ c₃ hC₀ hc₃))) := by
    ext g
    simp only [mem_valueGroup_iff, Valuation.comap_apply]
    constructor
    · rintro ⟨φ, hφ⟩
      refine ⟨(chartψ b C₀ c₃ hC₀ hc₃).symm φ, ?_⟩
      rw [algebraMap_chart, AlgEquiv.apply_symm_apply]
      exact hφ
    · rintro ⟨φ, hφ⟩
      exact ⟨chartψ b C₀ c₃ hC₀ hc₃ φ, hφ⟩
  rw [ramificationIdx, ramificationIdx, h1, h2]

omit [IsAlgClosed C] in
/-- The coordinate of the chart is `κ / (x - b)`. -/
lemma xF_chart : GaussFibre.xF C (Chart F b C₀ c₃ hC₀ hc₃) = toChart F hC₀ hc₃
    (algebraMap C F (c₃ * C₀) / (GaussFibre.xF C F - algebraMap C F b)) := by
  change toChart F hC₀ hc₃ (algebraMap (RatFunc C) F (chartψ b C₀ c₃ hC₀ hc₃ RatFunc.X)) = _
  rw [chartψ_X, map_div₀, map_sub, ← IsScalarTower.algebraMap_apply,
    ← IsScalarTower.algebraMap_apply]

section Integral

variable {E : Type*} [Field E] [Algebra C E]

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- `s^E q(x) ∈ C[s]` if `s x ∈ C[s]` and `deg q ≤ E`. -/
lemma pow_mul_aeval_mem {x s : E} {β κ : C}
    (hxs : s * x = algebraMap C E β * s + algebraMap C E κ) (q : C[X]) {N : ℕ}
    (hq : q.natDegree ≤ N) : s ^ N * aeval x q ∈ Algebra.adjoin C {s} := by
  have hsx : s * x ∈ Algebra.adjoin C {s} := by
    rw [hxs]
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ β) (Algebra.self_mem_adjoin_singleton C s))
      (Subalgebra.algebraMap_mem _ κ)
  have hs : s ∈ Algebra.adjoin C {s} := Algebra.self_mem_adjoin_singleton C s
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hq), Finset.mul_sum]
  refine Subalgebra.sum_mem _ fun i hi ↦ ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  rw [Algebra.smul_def, show s ^ N * (algebraMap C E (q.coeff i) * x ^ i) =
    algebraMap C E (q.coeff i) * (s ^ (N - i) * (s * x) ^ i) by
      rw [mul_pow, ← mul_assoc (s ^ (N - i)), ← pow_add, Nat.sub_add_cancel hi']; ring]
  exact mul_mem (Subalgebra.algebraMap_mem _ _) (mul_mem (pow_mem hs _) (pow_mem hsx _))

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- **Integrality in the inverted coordinate.** If `s x = β s + κ` and `Y` is integral over
`C[x]`, then `sᴺ Y` is integral over `C[s]` for some `N`. -/
theorem exists_isIntegral_pow_mul {x s : E} {β κ : C}
    (hxs : s * x = algebraMap C E β * s + algebraMap C E κ) {Y : E}
    (hY : IsIntegral (Algebra.adjoin C {x}) Y) :
    ∃ N : ℕ, IsIntegral (Algebra.adjoin C {s}) (s ^ N * Y) := by
  classical
  obtain ⟨P, hPm, hPY⟩ := hY
  -- polynomials representing the coefficients
  have hcoeff : ∀ i, ∃ q : C[X], aeval x q = (P.coeff i : E) := fun i ↦ by
    have : (P.coeff i : E) ∈ (aeval x : C[X] →ₐ[C] E).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (P.coeff i).2
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  choose q hq using hcoeff
  set n := P.natDegree
  set D := (Finset.range n).sup fun i ↦ (q i).natDegree
  have hqD : ∀ i < n, (q i).natDegree ≤ D := fun i hi ↦
    Finset.le_sup (f := fun i ↦ (q i).natDegree) (Finset.mem_range.2 hi)
  refine ⟨D, ?_⟩
  set A := Algebra.adjoin C {s}
  have hmem : ∀ i < n, s ^ (D * (n - i)) * (P.coeff i : E) ∈ A := by
    intro i hi
    have h1 : s ^ D * aeval x (q i) ∈ A := pow_mul_aeval_mem hxs (q i) (hqD i hi)
    have h2 : D ≤ D * (n - i) := Nat.le_mul_of_pos_right D (Nat.sub_pos_of_lt hi)
    rw [← hq i, show s ^ (D * (n - i)) = s ^ (D * (n - i) - D) * s ^ D by
      rw [← pow_add, Nat.sub_add_cancel h2], mul_assoc]
    exact mul_mem (pow_mem (Algebra.self_mem_adjoin_singleton C s) _) h1
  set c : ℕ → A := fun i ↦ if h : i < n then ⟨_, hmem i h⟩ else 0
  have hc : ∀ i < n, (c i : E) = s ^ (D * (n - i)) * (P.coeff i : E) := fun i hi ↦ by
    simp only [c, dif_pos hi]
  refine ⟨X ^ n + ∑ i ∈ Finset.range n, Polynomial.C (c i) * X ^ i, ?_, ?_⟩
  · refine Polynomial.monic_X_pow_add ?_
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe n)).2 fun i hi ↦ ?_
    exact (Polynomial.degree_C_mul_X_pow_le i (c i)).trans_lt
      (WithBot.coe_lt_coe.2 (Finset.mem_range.1 hi))
  · have hP : (Y ^ n + ∑ i ∈ Finset.range n, (P.coeff i : E) * Y ^ i) = 0 := by
      rw [← hPY]
      conv_rhs => rw [hPm.as_sum]
      simp only [eval₂_add, eval₂_finsetSum, eval₂_X_pow, eval₂_mul, eval₂_C]
      rfl
    simp only [eval₂_add, eval₂_finsetSum, eval₂_X_pow, eval₂_mul, eval₂_C]
    have : ∑ i ∈ Finset.range n, algebraMap A E (c i) * (s ^ D * Y) ^ i =
        s ^ (D * n) * ∑ i ∈ Finset.range n, (P.coeff i : E) * Y ^ i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi ↦ ?_
      have hi' := Finset.mem_range.1 hi
      change (c i : E) * _ = _
      rw [hc i hi', mul_pow, ← pow_mul,
        show s ^ (D * n) = s ^ (D * (n - i)) * s ^ (D * i) by
          rw [← pow_add, ← mul_add, Nat.sub_add_cancel hi'.le]]
      ring
    rw [this, mul_pow, ← pow_mul, ← mul_add, hP, mul_zero]

end Integral

section Good

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) [FiniteDimensional (RatFunc C) F]

/-- An inner factor `1 + λ s` (`|λ| ≤ 1`). -/
noncomputable def tauIn (l : C) : RatFunc C := 1 + algebraMap C (RatFunc C) l * RatFunc.X

/-- An outer factor `1 + ν c₃ / s` (`|ν| ≤ 1`). -/
noncomputable def tauOut (c₃ ν : C) : RatFunc C :=
  1 + algebraMap C (RatFunc C) ν * (algebraMap C (RatFunc C) c₃ / RatFunc.X)

omit [IsAlgClosed C] [CharZero C] in
lemma tauIn_mem {l : C} (hl : ‖l‖ ≤ 1) (c : C) : tauIn l ∈ nodeRing c :=
  add_mem (one_mem _) (mul_mem (algebraMap_mem_nodeRing hl)
    (ZariskiModel.self_mem_nodeChart (v := NormedField.valuation (K := C))))

omit [IsAlgClosed C] [CharZero C] in
lemma tauOut_mem {ν : C} (hν : ‖ν‖ ≤ 1) (c₃ : C) : tauOut c₃ ν ∈ nodeRing c₃ :=
  add_mem (one_mem _) (mul_mem (algebraMap_mem_nodeRing hν)
    (ZariskiModel.div_mem_nodeChart (v := NormedField.valuation (K := C))))

omit [IsAlgClosed C] in
lemma gaussRat_tauIn {l : C} (hl : ‖l‖ ≤ 1) {t : ℝ≥0ˣ} (ht : (t : ℝ≥0) ≤ 1) :
    w t (tauIn l) = 1 := by
  have e : tauIn l = algebraMap C (RatFunc C) 1 - algebraMap C (RatFunc C) (-l) * RatFunc.X := by
    simp [tauIn, sub_eq_add_neg]
  rw [e, gaussRat_C_sub_mul_X, nnnorm_one, nnnorm_neg]
  refine max_eq_left ?_
  calc ‖l‖₊ * (t : ℝ≥0) ≤ 1 * 1 := mul_le_mul' (by exact_mod_cast hl) ht
    _ = 1 := one_mul 1

omit [IsAlgClosed C] [CharZero C] in
lemma gaussRat_tauOut {c₃ ν : C} (hν : ‖ν‖ ≤ 1) {t : ℝ≥0ˣ} (ht : ‖c₃‖₊ ≤ (t : ℝ≥0)) :
    w t (tauOut c₃ ν) = 1 := by
  have hX : (RatFunc.X : RatFunc C) ≠ 0 := RatFunc.X_ne_zero
  have e : tauOut c₃ ν =
      algebraMap C[X] (RatFunc C) (X - Polynomial.C (-(ν * c₃))) / RatFunc.X := by
    simp only [tauOut, map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_neg, map_mul]
    field_simp
    rw [← RatFunc.algebraMap_eq_C]
    ring
  rw [e, map_div₀, GaussTube.gaussRat_X_sub_C, AnnulusUnit.gaussRat_X, nnnorm_neg, nnnorm_mul]
  have hle : ‖ν‖₊ * ‖c₃‖₊ ≤ (t : ℝ≥0) := by
    calc ‖ν‖₊ * ‖c₃‖₊ ≤ 1 * ‖c₃‖₊ := mul_le_mul_of_nonneg_right (by exact_mod_cast hν) zero_le
      _ ≤ _ := by rw [one_mul]; exact ht
  rw [max_eq_right hle, div_self t.ne_zero]

/-- The factor of `x - z` in the chart. -/
noncomputable def tauZ (b C₀ c₃ z : C) : RatFunc C :=
  if ‖z‖ ≤ ‖c₃ * C₀‖ then tauIn ((b - z) / (c₃ * C₀)) else tauOut c₃ (c₃ * C₀ / ((b - z) * c₃))

include hp hp1 hST in
/-- **Good elements of the chart.** Let `y (x - z₁) ⋯ (x - zₖ) = a` with `a` integral over `C[x]`
and every `zᵢ` outside the open annulus `|κ| < |x| < |C₀|`. If `y` is integral at all extensions
of the two boundary Gauss points `w_{0,|κ|}`, `w_{0,|C₀|}`, then `y` is good for the node chart of
`Chart F b C₀ c₃`. -/
theorem isGood_chart (hc₃1 : ‖c₃‖ < 1) (hb : ‖b‖ ≤ ‖c₃ * C₀‖) {y a : F} (Z : Multiset C)
    (hZ : ∀ z ∈ Z, ‖z‖ ≤ ‖c₃ * C₀‖ ∨ ‖C₀‖ ≤ ‖z‖)
    (hya : y * (Z.map fun z ↦ GaussFibre.xF C F - algebraMap C F z).prod = a)
    (ha : IsIntegral (Algebra.adjoin C {GaussFibre.xF C F}) a)
    (hout : ∀ v : GaussExtension (0 : C) (chartRad hC₀ hc₃ 1) F, v.1 y ≤ 1)
    (hin : ∀ v : GaussExtension (0 : C) (chartRad hC₀ hc₃ (GaussTube.invRad hc₃ 1)) F,
      v.1 y ≤ 1) :
    IsGood (Chart F b C₀ c₃ hC₀ hc₃) c₃ (toChart F hC₀ hc₃ y) := by
  classical
  set e := toChart F hC₀ hc₃
  have hκ0 : (c₃ * C₀) ≠ 0 := mul_ne_zero hc₃ hC₀
  have hC₀pos : 0 < ‖C₀‖ := norm_pos_iff.2 hC₀
  have hκC : ‖(c₃ * C₀)‖ < ‖C₀‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg c₃]
  -- coordinates
  set x : Chart F b C₀ c₃ hC₀ hc₃ := e (GaussFibre.xF C F)
  set sH : Chart F b C₀ c₃ hC₀ hc₃ := GaussFibre.xF C (Chart F b C₀ c₃ hC₀ hc₃)
  have hs : sH = algebraMap C _ (c₃ * C₀) / (x - algebraMap C _ b) := xF_chart (F := F) hC₀ hc₃
  have hκH : algebraMap C (Chart F b C₀ c₃ hC₀ hc₃) (c₃ * C₀) ≠ 0 :=
    (_root_.map_ne_zero _).2 hκ0
  have hs0 : sH ≠ 0 := by
    change algebraMap (RatFunc C) _ RatFunc.X ≠ 0
    rw [map_ne_zero_iff _ (algebraMap (RatFunc C) _).injective]
    exact RatFunc.X_ne_zero
  have hxb : x - algebraMap C _ b ≠ 0 := by
    intro h; rw [h, div_zero] at hs; exact hs0 hs
  have hxs : x - algebraMap C _ b = algebraMap C _ (c₃ * C₀) / sH := by rw [hs]; field_simp
  have hX : algebraMap (RatFunc C) (Chart F b C₀ c₃ hC₀ hc₃) RatFunc.X = sH := rfl
  -- the factors
  set σ : C → Chart F b C₀ c₃ hC₀ hc₃ := fun z ↦
    if ‖z‖ ≤ ‖(c₃ * C₀)‖ then algebraMap C _ (c₃ * C₀) / sH else algebraMap C _ (b - z)
  have hbz : ∀ z ∈ Z, ¬ ‖z‖ ≤ ‖(c₃ * C₀)‖ → ‖b - z‖ = ‖z‖ ∧ b - z ≠ 0 := by
    intro z hz hzk
    have hzC : ‖C₀‖ ≤ ‖z‖ := (hZ z hz).resolve_left hzk
    have hbzlt : ‖b‖ < ‖z‖ := hb.trans_lt (hκC.trans_le hzC)
    have h1 : ‖b - z‖ = ‖z‖ := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := b) (y := -z)
        (by rw [norm_neg]; exact hbzlt.ne)
      rwa [← sub_eq_add_neg, norm_neg, max_eq_right hbzlt.le] at this
    refine ⟨h1, fun h0 ↦ ?_⟩
    rw [h0, norm_zero] at h1
    exact (norm_nonneg b).not_gt (h1 ▸ hbzlt)
  have hfac : ∀ z ∈ Z, e (GaussFibre.xF C F - algebraMap C F z) =
      σ z * algebraMap (RatFunc C) _ (tauZ b C₀ c₃ z) := by
    intro z hz
    have hxz : e (GaussFibre.xF C F - algebraMap C F z) = x - algebraMap C _ z := rfl
    rw [hxz]
    simp only [σ, tauZ]
    split_ifs with hzk
    · simp only [tauIn, map_add, map_one, map_mul, hX, ← IsScalarTower.algebraMap_apply]
      have : x - algebraMap C _ z = (x - algebraMap C _ b) + algebraMap C _ (b - z) := by
        rw [map_sub]; ring
      rw [this, hxs, map_div₀, map_sub]
      field_simp
      rw [map_mul]
      ring
    · obtain ⟨-, hbz0⟩ := hbz z hz hzk
      have hbzH : algebraMap C (Chart F b C₀ c₃ hC₀ hc₃) (b - z) ≠ 0 :=
        (_root_.map_ne_zero _).2 hbz0
      have hc₃H : algebraMap C (Chart F b C₀ c₃ hC₀ hc₃) c₃ ≠ 0 := (_root_.map_ne_zero _).2 hc₃
      simp only [tauOut, map_add, map_one, map_mul, map_div₀, hX,
        ← IsScalarTower.algebraMap_apply]
      have : x - algebraMap C _ z = (x - algebraMap C _ b) + algebraMap C _ (b - z) := by
        rw [map_sub]; ring
      rw [this, hxs, map_mul]
      field_simp
      ring
  set τ : RatFunc C := (Z.map (tauZ b C₀ c₃)).prod
  have hτmem : τ ∈ nodeRing c₃ := by
    refine Subring.multiset_prod_mem _ _ fun f hf ↦ ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hf
    simp only [tauZ]
    split_ifs with hzk
    · refine tauIn_mem ?_ c₃
      rw [norm_div, div_le_one (norm_pos_iff.2 hκ0)]
      have := IsUltrametricDist.norm_add_le_max b (-z)
      rw [← sub_eq_add_neg, norm_neg] at this
      exact this.trans (max_le hb hzk)
    · refine tauOut_mem ?_ c₃
      obtain ⟨h1, h2⟩ := hbz z hz hzk
      have hzC := (hZ z hz).resolve_left hzk
      have hz0 : 0 < ‖z‖ := hC₀pos.trans_le hzC
      have hc0 : 0 < ‖c₃‖ := norm_pos_iff.2 hc₃
      simp only [norm_div, norm_mul, h1]
      rw [div_le_one (by positivity)]
      nlinarith
  have hτval : ∀ t : ℝ≥0ˣ, ‖c₃‖₊ ≤ (t : ℝ≥0) → (t : ℝ≥0) ≤ 1 → w t τ = 1 := by
    intro t ht1 ht2
    rw [map_multiset_prod, Multiset.map_map]
    refine Multiset.prod_eq_one fun r hr ↦ ?_
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hr
    simp only [Function.comp_apply, tauZ]
    split_ifs with hzk
    · refine gaussRat_tauIn ?_ ht2
      rw [norm_div, div_le_one (norm_pos_iff.2 hκ0)]
      have := IsUltrametricDist.norm_add_le_max b (-z)
      rw [← sub_eq_add_neg, norm_neg] at this
      exact this.trans (max_le hb hzk)
    · refine gaussRat_tauOut ?_ ht1
      obtain ⟨h1, h2⟩ := hbz z hz hzk
      have hzC := (hZ z hz).resolve_left hzk
      have hz0 : 0 < ‖z‖ := hC₀pos.trans_le hzC
      have hc0 : 0 < ‖c₃‖ := norm_pos_iff.2 hc₃
      simp only [norm_div, norm_mul, h1]
      rw [div_le_one (by positivity)]
      nlinarith
  -- `τ` is outside the node ideal
  have hc₃nn : ‖c₃‖₊ < 1 := by exact_mod_cast hc₃1
  obtain ⟨t₀, ht₀1, ht₀2⟩ := exists_between hc₃nn
  set t₀' : ℝ≥0ˣ := Units.mk0 t₀ (ne_of_gt (lt_of_le_of_lt zero_le ht₀1))
  have ht₀ : t₀' ∈ segment c₃ := ⟨ht₀1, ht₀2⟩
  have hτtube : (⟨τ, hτmem⟩ : nodeRing c₃) ∉ tubeIdeal c₃ := by
    rw [mem_tubeIdeal_iff _ ht₀]
    change ¬ w t₀' τ < 1
    rw [hτval t₀' ht₀1.le ht₀2.le]
    exact lt_irrefl 1
  refine ⟨⟨τ, hτmem⟩, hτtube, ?_⟩
  -- the product formula
  have hσinv : ∀ z ∈ Z, (σ z)⁻¹ ∈ Algebra.adjoin C {sH} := by
    intro z hz
    simp only [σ]
    split_ifs with hzk
    · rw [inv_div, div_eq_mul_inv, ← map_inv₀]
      exact mul_mem (Algebra.self_mem_adjoin_singleton C sH) (Subalgebra.algebraMap_mem _ _)
    · rw [← map_inv₀]; exact Subalgebra.algebraMap_mem _ _
  have hσ0 : ∀ z ∈ Z, σ z ≠ 0 := by
    intro z hz
    simp only [σ]
    split_ifs with hzk
    · exact div_ne_zero hκH hs0
    · exact (_root_.map_ne_zero _).2 (hbz z hz hzk).2
  have hmul : algebraMap (RatFunc C) _ τ * e y = e a * (Z.map fun z ↦ (σ z)⁻¹).prod := by
    have h1 : e y * (Z.map fun z ↦ σ z * algebraMap (RatFunc C) _ (tauZ b C₀ c₃ z)).prod =
        e a := by
      rw [← hya, map_mul, map_multiset_prod, Multiset.map_map]
      congr 1
      exact congrArg Multiset.prod (Multiset.map_congr rfl fun z hz ↦ (hfac z hz).symm)
    rw [Multiset.prod_map_mul, show (Z.map fun z ↦ algebraMap (RatFunc C)
        (Chart F b C₀ c₃ hC₀ hc₃) (tauZ b C₀ c₃ z)).prod = algebraMap (RatFunc C) _ τ by
      rw [map_multiset_prod, Multiset.map_map]; rfl] at h1
    have hP0 : (Z.map σ).prod ≠ 0 := Multiset.prod_ne_zero fun h ↦ by
      obtain ⟨z, hz, h0⟩ := Multiset.mem_map.1 h
      exact hσ0 z hz h0
    have hinv : (Z.map fun z ↦ (σ z)⁻¹).prod = ((Z.map σ).prod)⁻¹ := by
      rw [← Multiset.prod_map_inv]
    rw [hinv, ← h1]
    field_simp
  -- integrality via the maximum principle
  have hxs' : sH * x = algebraMap C _ b * sH + algebraMap C _ (c₃ * C₀) := by
    have := hxs
    field_simp at this
    linear_combination this
  obtain ⟨N, hN⟩ := exists_isIntegral_pow_mul (x := x) (s := sH) hxs' (Y := e a) ha
  haveI : Algebra.IsSeparable (RatFunc C) (Chart F b C₀ c₃ hC₀ hc₃) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  refine GaussTube.isIntegral_of_le hp hp1 hc₃ (N := N) ?_ (fun v ↦ ?_) (fun v ↦ ?_)
  · rw [hmul, ← mul_assoc]
    exact hN.mul (isIntegral_algebraMap (x := (⟨_, Subalgebra.multiset_prod_mem _ fun r hr ↦ by
      obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hr
      exact hσinv z hz⟩ : Algebra.adjoin C {sH})))
  · rw [map_mul, ← Valuation.comap_apply, v.2, hτval 1 (by simpa using hc₃nn.le) le_rfl, one_mul]
    exact hout (chartExt hC₀ hc₃ 1 (by rw [Units.val_one, mul_one]; exact_mod_cast hb) v)
  · have hrad : ((GaussTube.invRad hc₃ 1 : ℝ≥0ˣ) : ℝ≥0) = ‖c₃‖₊ := by
      simp [GaussTube.coe_invRad]
    rw [map_mul, ← Valuation.comap_apply, v.2, hτval _ hrad.ge (by rw [hrad]; exact hc₃nn.le),
      one_mul]
    refine hin (chartExt hC₀ hc₃ _ ?_ v)
    rw [hrad]
    calc ‖b‖₊ * ‖c₃‖₊ ≤ ‖(c₃ * C₀)‖₊ * 1 := mul_le_mul' (by exact_mod_cast hb) hc₃nn.le
      _ = ‖(c₃ * C₀)‖₊ := mul_one _

end Good

end Type3

end SemistableReduction
