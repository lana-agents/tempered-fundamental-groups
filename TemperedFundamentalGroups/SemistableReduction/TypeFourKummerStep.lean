/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TypeFourKummer
import TemperedFundamentalGroups.SemistableReduction.TypeFourDescent

/-!
# The Kummer step at a type-4 point

Blueprint §9.12, leaf T4: `TypeFour.KummerStepFor` from the degree reduction
`TypeFour.DegreeReductionFor`.

* `natDegree_eq_one_of_coordDense`: density of `C(x)` forces local degree one (converse of
  `coordDense_of_natDegree_eq_one`).
-/

open Polynomial
open scoped NNReal

namespace SemistableReduction

namespace TypeFour

open DiscCount LocalGlobal DenseCompletion

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {a c : C}

section LocalDegree

variable {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F'] [Algebra C F'] [IsScalarTower C (RatFunc C) F']

omit [IsUltrametricDist C] [IsAlgClosed C] in
/-- **Density gives local degree one**: if `C(x)` is dense in `(F', extValuation g)`, the
factor `g` has degree one. -/
theorem natDegree_eq_one_of_coordDense (ν : DiscVal a c)
    (g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) F')
    (hd : CoordDense C (extValuation g) (algebraMap (RatFunc C) F' RatFunc.X)) :
    g.1.natDegree = 1 := by
  set K := UniformSpace.Completion (DiscField ν)
  set L := Local K g.1
  set S : Set L := Set.range (algebraMap K L)
  have hiso : Isometry (algebraMap K L) :=
    AddMonoidHomClass.isometry_of_norm _ fun x ↦ norm_algebraMap' L x
  have hS : IsClosed S := hiso.isClosedEmbedding.isClosed_range
  have hsub : ∀ y : F', toLocal g y ∈ S := by
    intro y
    rw [← hS.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨P, Q, -, hPQ⟩ := hd y ⟨ε, hε.le⟩ hε
    set φ : RatFunc C := algebraMap C[X] (RatFunc C) P / algebraMap C[X] (RatFunc C) Q
    have hφ : aeval (algebraMap (RatFunc C) F' RatFunc.X) P /
        aeval (algebraMap (RatFunc C) F' RatFunc.X) Q = algebraMap (RatFunc C) F' φ := by
      rw [aeval_X_eq, aeval_X_eq, ← map_div₀]
    refine ⟨algebraMap K L (algebraMap (DiscField ν) K (WithAbs.toAbs _ φ)), ⟨_, rfl⟩, ?_⟩
    rw [hφ, extValuation_apply] at hPQ
    have h1 : algebraMap (RatFunc C) F' φ = algebraMap (DiscField ν) F' (WithAbs.toAbs _ φ) :=
      rfl
    rw [h1, map_sub, toLocal_algebraMap] at hPQ
    rw [dist_eq_norm]
    exact_mod_cast hPQ
  have hall : ∀ z : L, z ∈ S := by
    intro z
    have hz : z ∈ closure (Set.range (toLocal g)) := (denseRange_toLocal g) z
    have : closure (Set.range (toLocal g)) ⊆ S :=
      hS.closure_subset_iff.2 (by rintro _ ⟨y, rfl⟩; exact hsub y)
    exact this hz
  have htop : (⊥ : Subalgebra K L) = ⊤ := by
    refine eq_top_iff.2 fun z _ ↦ ?_
    obtain ⟨k, hk⟩ := hall z
    exact hk ▸ Subalgebra.algebraMap_mem _ k
  have hfin : Module.finrank K L = 1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  rw [← finrank_local]
  exact hfin

end LocalDegree

/-! ### Newton's method in a valued field -/

section Newton

variable {F : Type*} [Field F] (v : Valuation F ℝ≥0)

local notation "𝒪" => v.valuationSubring

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
lemma val_le_one (a : 𝒪) : v (a : F) ≤ 1 := (Valuation.mem_valuationSubring_iff _ _).1 a.2

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
lemma isUnit_iff_val_eq_one (a : 𝒪) : IsUnit a ↔ v (a : F) = 1 :=
  (Valuation.valuationSubring.integers v).isUnit_iff_valuation_eq_one

/-- One Newton step inside the valuation ring. -/
noncomputable def vNewton (Φ : 𝒪[X]) (y : 𝒪) : 𝒪 :=
  open Classical in
  if hu : IsUnit (Φ.derivative.eval y) then y - Φ.eval y * ↑hu.unit⁻¹ else y

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
/-- **The Newton step** for a valuation: if `Φ'(y)` is a unit and `v(Φ(y)) < 1`, then
`Φ'(y')` is a unit, `v(Φ(y')) ≤ v(Φ(y))^2` and `v(y' - y) ≤ v(Φ(y))`. -/
lemma vNewton_spec (Φ : 𝒪[X]) {y : 𝒪} (hu : IsUnit (Φ.derivative.eval y))
    (hlt : v ((Φ.eval y : 𝒪) : F) < 1) :
    IsUnit (Φ.derivative.eval (vNewton v Φ y)) ∧
      v ((Φ.eval (vNewton v Φ y) : 𝒪) : F) ≤ v ((Φ.eval y : 𝒪) : F) ^ 2 ∧
      v (((vNewton v Φ y : 𝒪) : F) - y) ≤ v ((Φ.eval y : 𝒪) : F) := by
  set h : 𝒪 := -(Φ.eval y * ↑hu.unit⁻¹) with hh
  have hstep : vNewton v Φ y = y + h := by
    rw [vNewton, dif_pos hu, hh, sub_eq_add_neg]
  have hunorm : v ((↑hu.unit⁻¹ : 𝒪) : F) = 1 :=
    (isUnit_iff_val_eq_one v _).1 (Units.isUnit _)
  have hnorm : v (h : F) = v ((Φ.eval y : 𝒪) : F) := by
    rw [hh]
    push_cast
    rw [Valuation.map_neg, map_mul, hunorm, mul_one]
  have hfx : Φ.eval y + Φ.derivative.eval y * h = 0 := by
    rw [hh, mul_neg, ← mul_assoc, mul_comm (Φ.derivative.eval y), mul_assoc,
      show Φ.derivative.eval y * (↑hu.unit⁻¹ : 𝒪) = 1 from hu.mul_val_inv, mul_one,
      add_neg_cancel]
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := Φ.derivative.evalSubFactor (y + h) y
    rw [add_sub_cancel_left] at hz
    have hd : Φ.derivative.eval (y + h) = Φ.derivative.eval y + z * h := by
      rw [← hz]; ring
    rw [hstep, isUnit_iff_val_eq_one, hd]
    push_cast
    have h1 : v ((Φ.derivative.eval y : 𝒪) : F) = 1 := (isUnit_iff_val_eq_one v _).1 hu
    have h2 : v ((z : F) * h) < 1 := by
      rw [map_mul, hnorm]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one v z)) hlt
    rw [Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact h2), h1]
  · obtain ⟨k, hk⟩ := Φ.binomExpansion y h
    rw [hstep, hk, hfx, zero_add]
    push_cast
    rw [map_mul, map_pow, hnorm]
    exact mul_le_of_le_one_left' (val_le_one v k)
  · rw [hstep]
    push_cast
    rw [add_sub_cancel_left, hnorm]

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
/-- Near a point with unit derivative, `Φ` is an isometry: `v(Φ(Y) - Φ(y)) = v(Y - y)`. -/
lemma val_eval_sub (Φ : 𝒪[X]) {y Y : 𝒪} (hu : IsUnit (Φ.derivative.eval y))
    (hY : v ((Y : F) - y) < 1) :
    v (((Φ.eval Y : 𝒪) : F) - (Φ.eval y : 𝒪)) = v ((Y : F) - y) := by
  obtain ⟨k, hk⟩ := Φ.binomExpansion y (Y - y)
  rw [add_sub_cancel] at hk
  have e : ((Φ.eval Y : 𝒪) : F) - (Φ.eval y : 𝒪) =
      ((Y : F) - y) * (((Φ.derivative.eval y : 𝒪) : F) + (k : F) * ((Y : F) - y)) := by
    rw [hk]; push_cast; ring
  have h1 : v ((Φ.derivative.eval y : 𝒪) : F) = 1 := (isUnit_iff_val_eq_one v _).1 hu
  have h2 : v ((k : F) * ((Y : F) - y)) < 1 := by
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (val_le_one v k)) hY
  rw [e, map_mul, Valuation.map_add_eq_of_lt_left _ (by rw [h1]; exact h2), h1, mul_one]

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
/-- **Newton approximation of an approximate root**: iterating from `y₀` (simple root modulo the
maximal ideal), the iterates approach every `Y ≡ y₀` up to `v(Φ(Y))`. -/
lemma exists_vNewton_approx (Φ : 𝒪[X]) {y₀ Y : 𝒪} (hu : IsUnit (Φ.derivative.eval y₀))
    (hlt : v ((Φ.eval y₀ : 𝒪) : F) < 1) (hY : v ((Y : F) - y₀) < 1) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ k : ℕ, v ((Y : F) - ((vNewton v Φ)^[k] y₀ : 𝒪)) ≤ max (v ((Φ.eval Y : 𝒪) : F)) ε := by
  set q := v ((Φ.eval y₀ : 𝒪) : F)
  have key : ∀ k : ℕ, IsUnit (Φ.derivative.eval ((vNewton v Φ)^[k] y₀)) ∧
      v ((Φ.eval ((vNewton v Φ)^[k] y₀) : 𝒪) : F) ≤ q ^ (2 ^ k) ∧
      v ((((vNewton v Φ)^[k] y₀ : 𝒪) : F) - y₀) ≤ q := by
    intro k
    induction k with
    | zero => exact ⟨hu, by simp [q], by simp⟩
    | succ k ih =>
      obtain ⟨hu', hq', hd'⟩ := ih
      have hlt' : v ((Φ.eval ((vNewton v Φ)^[k] y₀) : 𝒪) : F) < 1 :=
        hq'.trans_lt (pow_lt_one₀ zero_le hlt (pow_ne_zero _ two_ne_zero))
      obtain ⟨h1, h2, h3⟩ := vNewton_spec v Φ hu' hlt'
      rw [Function.iterate_succ_apply']
      refine ⟨h1, h2.trans ((pow_le_pow_left₀ zero_le hq' 2).trans_eq ?_), ?_⟩
      · rw [← pow_mul, ← pow_succ]
      · rw [show (((vNewton v Φ ((vNewton v Φ)^[k] y₀) : 𝒪) : F) - y₀) =
          ((((vNewton v Φ ((vNewton v Φ)^[k] y₀) : 𝒪) : F) - ((vNewton v Φ)^[k] y₀ : 𝒪)) +
            ((((vNewton v Φ)^[k] y₀ : 𝒪) : F) - y₀)) by ring]
        exact (Valuation.map_add _ _ _).trans (max_le (h3.trans
          (hq'.trans (pow_le_of_le_one zero_le hlt.le (pow_ne_zero _ two_ne_zero)))) hd')
  -- choose `k` with `q^(2^k) ≤ ε`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q ^ (2 ^ k) ≤ ε := by
    have hq1 : (q : ℝ) < 1 := by exact_mod_cast hlt
    have := DiscGerm.tendsto_pow_two_pow (q.2) hq1
    obtain ⟨k, hk⟩ := (this.eventually (gt_mem_nhds (show (0 : ℝ) < ε from hε))).exists
    exact ⟨k, by exact_mod_cast hk.le⟩
  obtain ⟨hu', hq', hd'⟩ := key k
  refine ⟨k, ?_⟩
  have hYk : v ((Y : F) - ((vNewton v Φ)^[k] y₀ : 𝒪)) < 1 := by
    rw [show (Y : F) - ((vNewton v Φ)^[k] y₀ : 𝒪) =
      ((Y : F) - y₀) - ((((vNewton v Φ)^[k] y₀ : 𝒪) : F) - y₀) by ring]
    exact (Valuation.map_sub _ _ _).trans_lt (max_lt hY (hd'.trans_lt hlt))
  rw [← val_eval_sub v Φ hu' hYk]
  exact (Valuation.map_sub _ _ _).trans (max_le_max le_rfl (hq'.trans hk))

omit [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C] in
/-- The Newton iterates stay in any subfield containing the coefficients and the start. -/
lemma vNewton_iterate_mem (Φ : 𝒪[X]) (N : Subfield F) (hΦ : ∀ i, ((Φ.coeff i : 𝒪) : F) ∈ N)
    {y₀ : 𝒪} (hy₀ : (y₀ : F) ∈ N) (k : ℕ) : (((vNewton v Φ)^[k] y₀ : 𝒪) : F) ∈ N := by
  have heval : ∀ (P : 𝒪[X]), (∀ i, ((P.coeff i : 𝒪) : F) ∈ N) → ∀ y : 𝒪, (y : F) ∈ N →
      ((P.eval y : 𝒪) : F) ∈ N := by
    intro P hP y hy
    rw [eval_eq_sum_range]
    push_cast
    exact sum_mem fun i _ ↦ mul_mem (hP i) (pow_mem hy i)
  have hder : ∀ i, ((Φ.derivative.coeff i : 𝒪) : F) ∈ N := fun i ↦ by
    rw [coeff_derivative]; push_cast; exact mul_mem (hΦ _) (by simpa using natCast_mem N (i + 1))
  induction k with
  | zero => exact hy₀
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set y := (vNewton v Φ)^[k] y₀
    unfold vNewton
    split_ifs with hu
    · have : ((↑hu.unit⁻¹ : 𝒪) : F) = ((Φ.derivative.eval y : 𝒪) : F)⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have h1 : ((hu.unit⁻¹ : 𝒪ˣ) : 𝒪) * Φ.derivative.eval y = 1 := hu.val_inv_mul
        exact congrArg Subtype.val h1
      push_cast
      rw [this]
      exact sub_mem ih (mul_mem (heval Φ hΦ y ih) (inv_mem (heval _ hder y ih)))
    · exact ih

end Newton

/-! ### Closures of subfields for a valuation -/

section Closure

variable {F : Type*} [Field F] (v : Valuation F ℝ≥0)

/-- The closure `{y | ∀ ε > 0, ∃ z ∈ N, v(y - z) < ε}` of a subfield. -/
def vClosure (N : Subfield F) : Subfield F where
  carrier := {y | ∀ ε : ℝ≥0, 0 < ε → ∃ z ∈ N, v (y - z) < ε}
  zero_mem' ε hε := ⟨0, zero_mem _, by simpa using hε⟩
  one_mem' ε hε := ⟨1, one_mem _, by simpa using hε⟩
  add_mem' {y y'} hy hy' ε hε := by
    obtain ⟨z, hz, h⟩ := hy ε hε
    obtain ⟨z', hz', h'⟩ := hy' ε hε
    refine ⟨z + z', add_mem hz hz', ?_⟩
    rw [show y + y' - (z + z') = (y - z) + (y' - z') by ring]
    exact (Valuation.map_add _ _ _).trans_lt (max_lt h h')
  neg_mem' {y} hy ε hε := by
    obtain ⟨z, hz, h⟩ := hy ε hε
    exact ⟨-z, neg_mem hz, by rwa [neg_sub_neg, ← Valuation.map_neg, neg_sub]⟩
  mul_mem' {y y'} hy hy' ε hε := by
    -- bounds
    set B := max (v y) (max (v y') 1)
    have hB : 0 < B := lt_max_of_lt_right (lt_max_of_lt_right zero_lt_one)
    set δ := min (ε / B) 1
    have hδ : 0 < δ := lt_min (div_pos hε hB) zero_lt_one
    obtain ⟨z, hz, h⟩ := hy δ hδ
    obtain ⟨z', hz', h'⟩ := hy' δ hδ
    refine ⟨z * z', mul_mem hz hz', ?_⟩
    have hz'B : v z' ≤ B := by
      have : z' = y' - (y' - z') := by ring
      rw [this]
      exact (Valuation.map_sub _ _ _).trans (max_le (le_max_of_le_right (le_max_left _ _))
        (h'.le.trans ((min_le_right _ _).trans (le_max_of_le_right (le_max_right _ _)))))
    rw [show y * y' - z * z' = y * (y' - z') + (y - z) * z' by ring]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ?_)
    · rw [map_mul]
      calc v y * v (y' - z') ≤ B * v (y' - z') := by gcongr; exact le_max_left _ _
        _ < B * (ε / B) := mul_lt_mul_of_pos_left (h'.trans_le (min_le_left _ _)) hB
        _ = ε := mul_div_cancel₀ _ hB.ne'
    · rw [map_mul]
      calc v (y - z) * v z' ≤ v (y - z) * B := by gcongr
        _ < (ε / B) * B := mul_lt_mul_of_pos_right (h.trans_le (min_le_left _ _)) hB
        _ = ε := div_mul_cancel₀ _ hB.ne'
  inv_mem' {y} hy ε hε := by
    by_cases hy0 : y = 0
    · exact ⟨0, zero_mem _, by simpa [hy0] using hε⟩
    have hv : 0 < v y := zero_le.lt_of_ne (Ne.symm ((map_ne_zero v).2 hy0))
    set δ := min (v y) (ε * v y ^ 2)
    have hδ : 0 < δ := lt_min hv (mul_pos hε (pow_pos hv 2))
    obtain ⟨z, hz, h⟩ := hy δ hδ
    have hyz : v (z - y) < v y := by
      rw [← Valuation.map_neg, neg_sub]
      exact h.trans_le (min_le_left _ _)
    have hzy : v z = v y := Valuation.map_eq_of_sub_lt v hyz
    have hz0 : z ≠ 0 := by
      intro h0; rw [h0, map_zero] at hzy; exact hv.ne hzy
    refine ⟨z⁻¹, inv_mem hz, ?_⟩
    rw [show y⁻¹ - z⁻¹ = (z - y) / (y * z) by field_simp, map_div₀, map_mul, hzy,
      ← Valuation.map_neg, neg_sub, ← pow_two, div_lt_iff₀ (pow_pos hv 2)]
    exact h.trans_le (min_le_right _ _)

lemma le_vClosure (N : Subfield F) : N ≤ vClosure v N := fun y hy ε hε ↦
  ⟨y, hy, by simpa using hε⟩

lemma vClosure_le_of_le {N N' : Subfield F} (h : N' ≤ vClosure v N) :
    vClosure v N' ≤ vClosure v N := by
  intro y hy ε hε
  obtain ⟨z, hz, h1⟩ := hy ε hε
  obtain ⟨z', hz', h2⟩ := h hz ε hε
  refine ⟨z', hz', ?_⟩
  rw [show y - z' = (y - z) + (z - z') by ring]
  exact (Valuation.map_add _ _ _).trans_lt (max_lt h1 h2)

end Closure

section DenseClosure

variable {F : Type*} [Field F] [Algebra C F] (v : Valuation F ℝ≥0)

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma denseOn_iff {S : Set F} {w : F} :
    DenseOn C v S w ↔ S ⊆ vClosure v (IntermediateField.adjoin C {w}).toSubfield := by
  constructor
  · intro h y hy ε hε
    obtain ⟨P, Q, -, hPQ⟩ := h y hy ε hε
    refine ⟨aeval w P / aeval w Q, ?_, hPQ⟩
    exact (IntermediateField.mem_adjoin_simple_iff C _).2 ⟨P, Q, rfl⟩
  · intro h y hy ε hε
    obtain ⟨z, hz, hyz⟩ := h hy ε hε
    obtain ⟨P, Q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff C _).1 hz
    by_cases hQ : aeval w Q = 0
    · refine ⟨0, 1, by simp, ?_⟩
      rw [hQ, div_zero] at hyz
      simpa using hyz
    · exact ⟨P, Q, hQ, hyz⟩

end DenseClosure

/-! ### The coordinate `s` -/

section Coordinate

open GaussFibre

variable {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F]
  [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F]

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]
  [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F] in
lemma coordAlgHom_X_sub_C {s : F} (hs : Transcendental C s) (b : C) :
    coordAlgHom hs (algebraMap C[X] (RatFunc C) (X - Polynomial.C b)) = s - algebraMap C F b := by
  rw [coordAlgHom_algebraMap]; simp

/-- **The point in the coordinate `s` is of type 4.** -/
theorem isTypeFour_coord {ξ' : Valuation F ℝ≥0} (hconst : ∀ b : C, ξ' (algebraMap C F b) = ‖b‖₊)
    (hξ : Splitting.IsTypeFour (ξ'.comap (algebraMap (RatFunc C) F))) {s : F}
    (hs : Transcendental C s) :
    Splitting.IsTypeFour (ξ'.comap (coordAlgHom hs).toRingHom) where
  map_C b := by
    simp only [Valuation.comap_apply]
    change ξ' (coordAlgHom hs (algebraMap C (RatFunc C) b)) = _
    rw [AlgHom.commutes, hconst, NormedField.valuation_apply]
  no_min b := by
    have hs0 : s - algebraMap C F b ≠ 0 := by
      intro h
      apply hs
      exact ⟨X - Polynomial.C b, X_sub_C_ne_zero b, by simpa [sub_eq_zero] using h⟩
    obtain ⟨b', hb'⟩ := exists_const_sub_lt_finite hconst hξ hs0
    refine ⟨b + b', ?_⟩
    simp only [GaussLimit.radius, Valuation.comap_apply]
    change ξ' (coordAlgHom hs _) < ξ' (coordAlgHom hs _)
    rw [coordAlgHom_X_sub_C, coordAlgHom_X_sub_C, map_add, ← sub_sub]
    exact hb'

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F]
  [Algebra (RatFunc C) F] [IsScalarTower C (RatFunc C) F] in
/-- Polynomials in `s` lie in the closure of the constants if `s` does. -/
lemma aeval_mem_vClosure {v : Valuation F ℝ≥0} {s : F}
    (hs : s ∈ vClosure v (algebraMap C F).fieldRange) (P : C[X]) :
    aeval s P ∈ vClosure v (algebraMap C F).fieldRange := by
  rw [aeval_eq_sum_range]
  refine sum_mem fun i _ ↦ ?_
  rw [Algebra.smul_def]
  exact mul_mem (le_vClosure v _ ⟨_, rfl⟩) (pow_mem hs i)

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] in
/-- **The point in the coordinate `s` is not a point of `Ĉ ∖ C`**: if `C(s)` is dense in an
intermediate field `K` and the radius of `ξ` in the coordinate `x` is bounded below, so is the
radius in `s`. -/
theorem exists_radius_bound_coord {ξ' : Valuation F ℝ≥0}
    (hr : ∃ r : ℝ≥0, 0 < r ∧ ∀ b : C,
      r ≤ ξ' (algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) b)))
    {K : IntermediateField (RatFunc C) F} {s : F} (hd : DenseOn C ξ' K s) :
    ∃ r : ℝ≥0, 0 < r ∧ ∀ b : C, r ≤ ξ' (s - algebraMap C F b) := by
  obtain ⟨r, hr0, hr⟩ := hr
  by_contra! h
  set Cr := (algebraMap C F).fieldRange
  have hs : s ∈ vClosure ξ' Cr := fun ε hε ↦ by
    obtain ⟨b, hb⟩ := h ε hε
    exact ⟨algebraMap C F b, ⟨b, rfl⟩, hb⟩
  have hCs : (IntermediateField.adjoin C {s}).toSubfield ≤ vClosure ξ' Cr := by
    intro y hy
    obtain ⟨P, Q, rfl⟩ := (IntermediateField.mem_adjoin_simple_iff C y).1 hy
    exact div_mem (aeval_mem_vClosure hs P) (aeval_mem_vClosure hs Q)
  have hK : (K : Set F) ⊆ vClosure ξ' Cr :=
    ((denseOn_iff ξ').1 hd).trans (vClosure_le_of_le ξ' hCs)
  have hx : algebraMap (RatFunc C) F RatFunc.X ∈ K := IntermediateField.algebraMap_mem _ _
  obtain ⟨z, ⟨b, rfl⟩, hz⟩ := hK hx r hr0
  have := hr b
  rw [map_sub, ← IsScalarTower.algebraMap_apply] at this
  exact absurd hz (not_lt.2 this)

end Coordinate

/-! ### Integrality on small discs -/

section Integral

open GaussLimit TubeCount IntermediateField

variable {L : Type*} [Field L] [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L]

/-- **Integrality on small discs**: an element integral over `C[x]` of value `≤ 1` at every
extension of a type-4 point `ξ` is integral over the disc chart of every small disc around `ξ`. -/
theorem exists_isIntegral_discRing {ξ : Valuation (RatFunc C) ℝ≥0} (hξ : Splitting.IsTypeFour ξ)
    (ν : DiscVal a c) (hν : ν.val = ξ) {z : L}
    (hzint : ∃ P : C[X][X], P.Monic ∧ aeval z (P.map (algebraMap C[X] (RatFunc C))) = 0)
    (hval : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) L,
      ‖toLocal g z‖ ≤ 1) :
    ∃ a₀ : C, ∀ a b : C, radius ξ a ≤ radius ξ a₀ → radius ξ b < radius ξ a →
      IsIntegral (discRing b (a - b)) z := by
  classical
  letI : Algebra C[X] L :=
    ((algebraMap (RatFunc C) L).comp (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨P, hPm, hPz⟩ := hzint
  have hzint' : IsIntegral C[X] z :=
    ⟨P, hPm, by rw [← aeval_def, ← aeval_map_algebraMap (RatFunc C)]; exact hPz⟩
  set P₀ : C[X][X] := minpoly C[X] z ^ Module.finrank (RatFunc C)⟮z⟯ L
  have hP₀ : P₀.map (algebraMap C[X] (RatFunc C)) = normPoly (RatFunc C) z := by
    rw [Polynomial.map_pow, normPoly,
      minpoly.isIntegrallyClosed_eq_field_fractions' (RatFunc C) hzint']
  have hP₀m : P₀.Monic := (minpoly.monic hzint').pow _
  have hcoeff (i : ℕ) : ξ (algebraMap C[X] (RatFunc C) (P₀.coeff i)) ≤ 1 := by
    haveI : Infinite (DiscField ν) :=
      Infinite.of_injective _ (algebraMap C (DiscField ν)).injective
    haveI : Infinite (RatFunc C) :=
      Infinite.of_injective _ (algebraMap C (RatFunc C)).injective
    have hle := norm_coeff_normPoly_le_one (F := DiscField ν)
      (K := UniformSpace.Completion (DiscField ν)) (F' := L) (y := z) hval i
    have hmap := normPoly_map_ringEquiv (WithAbs.equiv ν.val.toAbsoluteValue).symm
      (F₂ := DiscField ν) (by ext; rfl) z
    rw [← hmap, coeff_map, ← hP₀, coeff_map, WithAbs.norm_eq_apply_ofAbs] at hle
    rw [← hν]
    exact_mod_cast hle
  choose A hA using fun i : ℕ ↦ exists_forall_eq_gaussRat hξ.map_C (P₀.coeff i)
  obtain ⟨i₀, -, hi₀⟩ := (Finset.range (P₀.natDegree + 1)).exists_min_image
    (fun i ↦ radius ξ (A i)) ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩
  refine ⟨A i₀, fun a b ha hb ↦ ?_⟩
  have hab := Splitting.sub_ne_zero_of_radius_lt hξ hb
  have hmem (i : ℕ) : algebraMap C[X] (RatFunc C) (P₀.coeff i) ∈ discRing b (a - b) := by
    by_cases hi : i ≤ P₀.natDegree
    · refine Splitting.algebraMap_mem_discRing_of_le hab ?_
      have hrad : radius ξ a ≤ radius ξ (A i) :=
        ha.trans (hi₀ i (Finset.mem_range.2 (Nat.lt_succ_of_le hi)))
      have hu : radiusUnit ξ a = Units.mk0 ‖a - b‖₊ (nnnorm_ne_zero_iff.2 hab) := by
        ext
        rw [val_radiusUnit, Units.val_mk0, Splitting.radius_eq_nnnorm hξ hb, ← nnnorm_neg,
          neg_sub]
      rw [← Splitting.gaussRat_eq_of_le (a := a) (b := b) (r := Units.mk0 ‖a - b‖₊ _) le_rfl,
        ← hu, ← hA i a hrad]
      exact hcoeff i
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi), map_zero]
      exact Subring.zero_mem _
  have hc : (↑(P₀.map (algebraMap C[X] (RatFunc C))).coeffs : Set (RatFunc C)) ⊆
      discRing b (a - b) := by
    intro f hf
    obtain ⟨n, -, rfl⟩ := mem_coeffs_iff.1 hf
    rw [coeff_map]
    exact hmem n
  refine ⟨(P₀.map (algebraMap C[X] (RatFunc C))).toSubring _ hc,
    (monic_toSubring _ _ _).2 (hP₀m.map _), ?_⟩
  rw [show algebraMap (discRing b (a - b)) L =
    (algebraMap (RatFunc C) L).comp (discRing b (a - b)).subtype from rfl, ← eval₂_map,
    map_toSubring, ← aeval_def, hP₀, normPoly, map_pow]
  change aeval z (minpoly (RatFunc C) z) ^ _ = 0
  rw [minpoly.aeval, zero_pow Module.finrank_pos.ne']

omit [IsUltrametricDist C] [IsAlgClosed C] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L] in
lemma exists_monic_of_isIntegral {z : L}
    (h : letI : Algebra C[X] L :=
      ((algebraMap (RatFunc C) L).comp (algebraMap C[X] (RatFunc C))).toAlgebra
      IsIntegral C[X] z) :
    ∃ P : C[X][X], P.Monic ∧ aeval z (P.map (algebraMap C[X] (RatFunc C))) = 0 := by
  letI : Algebra C[X] L :=
    ((algebraMap (RatFunc C) L).comp (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  obtain ⟨P, hPm, hPz⟩ := h
  exact ⟨P, hPm, by rw [aeval_map_algebraMap, aeval_def]; exact hPz⟩

omit [FiniteDimensional (RatFunc C) L] in
/-- Every element becomes integral over `C[x]` after multiplication by a polynomial of value
one at a type-4 point. -/
lemma exists_poly_mul_integral {ξ : Valuation (RatFunc C) ℝ≥0} (hξ : Splitting.IsTypeFour ξ)
    (z : L) : ∃ d : C[X], ξ (algebraMap C[X] (RatFunc C) d) = 1 ∧
      ∃ P : C[X][X], P.Monic ∧
        aeval (algebraMap (RatFunc C) L (algebraMap C[X] (RatFunc C) d) * z)
          (P.map (algebraMap C[X] (RatFunc C))) = 0 := by
  letI : Algebra C[X] L :=
    ((algebraMap (RatFunc C) L).comp (algebraMap C[X] (RatFunc C))).toAlgebra
  haveI : IsScalarTower C[X] (RatFunc C) L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI := IsLocalization.isAlgebraic (RatFunc C) (nonZeroDivisors C[X])
  haveI := Algebra.IsAlgebraic.trans C[X] (RatFunc C) L
  obtain ⟨d, hd0, hdint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := C[X]) z).exists_integral_multiple
  obtain ⟨γ, hγ⟩ := Splitting.exists_nnnorm_eq hξ d
  have hξd : ξ (algebraMap C[X] (RatFunc C) d) ≠ 0 := by
    rw [Ne, map_eq_zero, IsFractionRing.to_map_eq_zero_iff]; exact hd0
  have hγ0 : γ ≠ 0 := by
    rintro rfl; rw [nnnorm_zero] at hγ; exact hξd hγ.symm
  refine ⟨Polynomial.C γ⁻¹ * d, ?_, ?_⟩
  · rw [map_mul, ratFunc_algebraMap_C, map_mul, hξ.map_C, ← hγ]
    change ‖γ⁻¹‖₊ * ‖γ‖₊ = 1
    rw [nnnorm_inv, inv_mul_cancel₀ (nnnorm_ne_zero_iff.2 hγ0)]
  · refine exists_monic_of_isIntegral ?_
    have : algebraMap (RatFunc C) L (algebraMap C[X] (RatFunc C) (Polynomial.C γ⁻¹ * d)) * z =
        (Polynomial.C γ⁻¹ * d) • z := by rw [Algebra.smul_def]; rfl
    rw [this, mul_smul]
    exact hdint.smul _

end Integral

/-! ### Polynomial approximants of an element at a type-4 point -/

section Germ

open GaussLimit Filter Topology DiscGerm

variable {L : Type*} [Field L] [Algebra (RatFunc C) L] [FiniteDimensional (RatFunc C) L]
  [Algebra.IsSeparable (RatFunc C) L] [Algebra C L] [IsScalarTower C (RatFunc C) L]

/-- **Uniform polynomial approximants at a type-4 point of local degree one.** If `C(x)` is
dense in `(L, ξL)` over a type-4 point, then for `y ≠ 0` there are `u ≠ 0` (making `y u^p`
integral, of value one) and polynomials `Qₙ(t)`, `t = (x - b₀)/c₀`, converging to `y u^p` at
`ξL` and uniformly Cauchy on the disc `|t| ≤ |l|`, which contains `ξL` (DiscGerm on the sheet). -/
theorem exists_germ_approx {p : ℕ} (hp0 : 0 < p) {ξL : Valuation L ℝ≥0}
    (hconst : ∀ b : C, ξL (algebraMap C L b) = ‖b‖₊)
    (hη : Splitting.IsTypeFour (ξL.comap (algebraMap (RatFunc C) L)))
    (hd : CoordDense C ξL (algebraMap (RatFunc C) L RatFunc.X)) {y : L} (hy : y ≠ 0) :
    ∃ (u : L) (b₀ c₀ l : C) (Q : ℕ → C[X]) (q : ℝ), u ≠ 0 ∧ c₀ ≠ 0 ∧ l ≠ 0 ∧ ‖l‖ < 1 ∧
      ξL (algebraMap (RatFunc C) L (RatFunc.X - algebraMap C (RatFunc C) b₀)) < ‖l * c₀‖₊ ∧
      0 ≤ q ∧ q < 1 ∧ ξL (y * u ^ p) = 1 ∧ (∀ n i, ‖(Q n).coeff i‖ ≤ 1) ∧
      (∀ m n i, ‖(Q m - Q n).coeff i‖ * ‖l‖ ^ i ≤ max (q ^ (2 ^ m)) (q ^ (2 ^ n))) ∧
      Tendsto (fun n ↦ (ξL (y * u ^ p -
        algebraMap (RatFunc C) L (aeval (gaussCoord b₀ c₀) (Q n))) : ℝ)) atTop (𝓝 0) := by
  classical
  set η := ξL.comap (algebraMap (RatFunc C) L)
  obtain ⟨a₁, c₁, ν, hν⟩ := exists_discVal hη
  obtain ⟨g₀, hg₀⟩ := exists_eq_extValuation' ν (ξ' := ξL) hν.symm
  -- the value of `y`
  obtain ⟨b, hb⟩ := exists_const_sub_lt_finite hconst hη hy
  have hyb : ξL y = ‖b‖₊ := by
    rw [← hconst]
    exact (Valuation.map_eq_of_sub_lt ξL (by rwa [← Valuation.map_neg, neg_sub])).symm
  have hb0 : b ≠ 0 := by
    rintro rfl; rw [nnnorm_zero, map_eq_zero] at hyb; exact hy hyb
  obtain ⟨κ, hκ⟩ := IsAlgClosed.exists_pow_nat_eq b⁻¹ hp0
  have hκ0 : κ ≠ 0 := by rintro rfl; rw [zero_pow hp0.ne'] at hκ; exact inv_ne_zero hb0 hκ.symm
  have hκb : ‖κ‖ ^ p * ‖b‖ = 1 := by
    rw [← norm_pow, hκ, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.2 hb0)]
  -- a bound for `y` at all extensions
  obtain ⟨B, hB⟩ := Finite.exists_le (fun g : Factor (DiscField ν)
    (UniformSpace.Completion (DiscField ν)) L ↦ ‖toLocal g y‖)
  set B' := max B 1
  have hB'0 : 0 < B' := lt_max_of_lt_right zero_lt_one
  have hκ0' : 0 < ‖κ‖ ^ p := pow_pos (norm_pos_iff.2 hκ0) p
  set ε : ℝ := min 1 (1 / (‖κ‖ ^ p * B'))
  have hε : 0 < ε := lt_min zero_lt_one (by positivity)
  obtain ⟨z, hz1, hzo⟩ := exists_approx (K := UniformSpace.Completion (DiscField ν)) g₀ (1 : L)
    hε
  have hz₀ : ‖toLocal g₀ z‖ = 1 := by
    rw [map_sub, map_one] at hz1
    exact (norm_eq_of_norm_sub_lt (by rw [norm_one]; exact hz1.trans_le (min_le_left _ _))).trans
      norm_one
  -- integrality over `C[x]`
  obtain ⟨d₁, hd₁, P₁, hP₁m, hP₁⟩ := exists_poly_mul_integral hη z
  obtain ⟨d₂, hd₂, P₂, hP₂m, hP₂⟩ := exists_poly_mul_integral hη y
  set D₁ := algebraMap (RatFunc C) L (algebraMap C[X] (RatFunc C) d₁)
  set D₂ := algebraMap (RatFunc C) L (algebraMap C[X] (RatFunc C) d₂)
  have hD₁ : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) L,
      ‖toLocal g D₁‖ = 1 := fun g ↦ by
    rw [norm_toLocal_algebraMap, hν]; exact_mod_cast hd₁
  have hD₂ : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) L,
      ‖toLocal g D₂‖ = 1 := fun g ↦ by
    rw [norm_toLocal_algebraMap, hν]; exact_mod_cast hd₂
  set Kκ := algebraMap (RatFunc C) L (algebraMap C (RatFunc C) κ)
  have hKκ : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) L,
      ‖toLocal g Kκ‖ = ‖κ‖ := fun g ↦ by
    rw [norm_toLocal_algebraMap, ν.isDiscVal.map_C]; rfl
  set u := Kκ * (D₁ * z) * D₂
  have hnorm : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) L,
      ‖toLocal g (y * u ^ p)‖ = ‖toLocal g y‖ * (‖κ‖ ^ p * ‖toLocal g z‖ ^ p) := fun g ↦ by
    simp only [u, map_mul, map_pow, norm_mul, norm_pow, hD₁, hD₂, hKκ, one_mul, mul_one]
    ring
  have hyg₀ : ‖toLocal g₀ y‖ = ‖b‖ := by
    rw [← coe_nnnorm, ← extValuation_apply, hg₀, hyb]; rfl
  have hval1 : ‖toLocal g₀ (y * u ^ p)‖ = 1 := by
    rw [hnorm, hyg₀, hz₀, one_pow, mul_one, mul_comm, hκb]
  have hval : ∀ g : Factor (DiscField ν) (UniformSpace.Completion (DiscField ν)) L,
      ‖toLocal g (y * u ^ p)‖ ≤ 1 := by
    intro g
    by_cases hg : g = g₀
    · rw [hg, hval1]
    · rw [hnorm]
      have hzg := hzo g hg
      have hz1' : ‖toLocal g z‖ ^ p ≤ ε :=
        (pow_le_of_le_one (norm_nonneg _) (hzg.le.trans (min_le_left _ _)) hp0.ne').trans hzg.le
      calc ‖toLocal g y‖ * (‖κ‖ ^ p * ‖toLocal g z‖ ^ p)
          ≤ B' * (‖κ‖ ^ p * ε) := by
            gcongr
            exact (hB g).trans (le_max_left _ _)
        _ ≤ B' * (‖κ‖ ^ p * (1 / (‖κ‖ ^ p * B'))) := by gcongr; exact min_le_right _ _
        _ = 1 := by field_simp
  have hyu1 : ξL (y * u ^ p) = 1 := by
    rw [← hg₀, extValuation_apply]; exact NNReal.coe_injective (by simpa using hval1)
  -- integrality over `C[x]`
  have hint : ∃ P : C[X][X], P.Monic ∧
      aeval (y * u ^ p) (P.map (algebraMap C[X] (RatFunc C))) = 0 := by
    refine exists_monic_of_isIntegral ?_
    letI : Algebra C[X] L :=
      ((algebraMap (RatFunc C) L).comp (algebraMap C[X] (RatFunc C))).toAlgebra
    haveI : IsScalarTower C[X] (RatFunc C) L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have h1 : IsIntegral C[X] (D₁ * z) := ⟨P₁, hP₁m, by
      rw [← aeval_def, ← aeval_map_algebraMap (RatFunc C)]; exact hP₁⟩
    have h2 : IsIntegral C[X] (D₂ * y) := ⟨P₂, hP₂m, by
      rw [← aeval_def, ← aeval_map_algebraMap (RatFunc C)]; exact hP₂⟩
    have hK : IsIntegral C[X] Kκ := by
      have : Kκ = algebraMap C[X] L (Polynomial.C κ) := by
        simp [Kκ, RingHom.algebraMap_toAlgebra]
      rw [this]; exact isIntegral_algebraMap
    have hD : IsIntegral C[X] D₂ := by
      have : D₂ = algebraMap C[X] L d₂ := rfl
      rw [this]; exact isIntegral_algebraMap
    have e : y * u ^ p = Kκ ^ p * (D₁ * z) ^ p * D₂ ^ (p - 1) * (D₂ * y) := by
      simp only [u]
      obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp0).symm⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [e]
    exact (((hK.pow _).mul (h1.pow _)).mul (hD.pow _)).mul h2
  -- small discs: integrality and separation
  obtain ⟨a₀, ha₀⟩ := exists_isIntegral_discRing hη ν hν hint hval
  obtain ⟨a₂, ha₂⟩ := Splitting.exists_center_injective (F' := L) hη
  obtain ⟨a, ha₀a, ha₂a⟩ : ∃ a : C, radius η a ≤ radius η a₀ ∧ radius η a ≤ radius η a₂ := by
    rcases le_total (radius η a₀) (radius η a₂) with h | h
    · exact ⟨a₀, le_rfl, h⟩
    · exact ⟨a₂, h, le_rfl⟩
  obtain ⟨b₀, hb₀⟩ := hη.no_min a
  have hc₀ : a - b₀ ≠ 0 := Splitting.sub_ne_zero_of_radius_lt hη hb₀
  obtain ⟨ν', hν'⟩ : ∃ ν' : DiscVal b₀ (a - b₀), ν'.val = η :=
    ⟨⟨η, Splitting.isDiscVal hη hb₀⟩, rfl⟩
  set y' : DRint b₀ (a - b₀) L := ⟨y * u ^ p, ha₀ a b₀ ha₀a hb₀⟩
  have hdv := Splitting.isDiscVal_comap (F' := L) hη (ξ' := ξL) rfl hb₀
  set P' := center hdv
  haveI : P'.IsMaximal := center_isMaximal hc₀ hdv
  obtain ⟨g₁, hg₁⟩ := exists_eq_extValuation' ν' (ξ' := ξL) hν'.symm
  have hcen₁ : center (isDiscVal_comap_extValuation g₁) = P' := by
    ext w; simp only [mem_center_iff, hg₁, P']
  have h1 : discDegree ν' P' = 1 := by
    rw [discDegree, Finset.sum_eq_single_of_mem g₁ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hcen₁⟩)]
    · rw [← hg₁] at hd
      exact natDegree_eq_one_of_coordDense ν' g₁ hd
    · intro g hg hne
      exfalso
      refine hne (extValuation_injective ?_)
      rw [hg₁]
      exact ha₂ a b₀ ha₂a hb₀ _ _ ((Splitting.comap_extValuation ν' g).trans hν') rfl
        (Finset.mem_filter.1 hg).2
  -- the radius
  have hrad : (0 : ℝ) < radius η b₀ / ‖a - b₀‖ :=
    div_pos (by exact_mod_cast pos_iff_ne_zero.2 (radius_ne_zero η b₀)) (norm_pos_iff.2 hc₀)
  have hrad1 : radius η b₀ / ‖a - b₀‖ < 1 := by
    rw [div_lt_one (norm_pos_iff.2 hc₀), ← coe_nnnorm, NNReal.coe_lt_coe, ← nnnorm_neg,
      neg_sub, ← Splitting.radius_eq_nnnorm hη hb₀]
    exact hb₀
  obtain ⟨l, hl1, hl2⟩ := exists_norm_between (C := C) hrad hrad1
  have hl0 : l ≠ 0 := by rintro rfl; simp at hl1; linarith
  -- the germ
  obtain ⟨G, Q, -, hQ1, hunif, hconv⟩ := exists_germ hc₀ ν' P' h1 y'
  obtain ⟨q, hq0, hq1, hql⟩ := hunif l hl0 hl2
  have hu0 : u ≠ 0 := by
    have hz0 : z ≠ 0 := by rintro rfl; rw [map_zero, norm_zero] at hz₀; exact zero_ne_one hz₀
    have hd0 : ∀ {d : C[X]}, η (algebraMap C[X] (RatFunc C) d) = 1 →
        algebraMap (RatFunc C) L (algebraMap C[X] (RatFunc C) d) ≠ 0 := by
      intro d hd h0
      rw [map_eq_zero_iff _ (algebraMap (RatFunc C) L).injective] at h0
      rw [h0, map_zero] at hd; exact zero_ne_one hd
    refine mul_ne_zero (mul_ne_zero ?_ (mul_ne_zero (hd0 hd₁) hz0)) (hd0 hd₂)
    simpa [Kκ] using hκ0
  refine ⟨u, b₀, a - b₀, l, Q, q, hu0, hc₀, hl0, hl2, ?_, hq0, hq1, hyu1,
    fun n i ↦ by exact_mod_cast hQ1 n i, fun m n i ↦ ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, nnnorm_mul, NNReal.coe_mul, coe_nnnorm, coe_nnnorm]
    have : (ξL (algebraMap (RatFunc C) L (RatFunc.X - algebraMap C (RatFunc C) b₀)) : ℝ) =
        radius η b₀ := by
      simp only [radius, η, Valuation.comap_apply]
      congr 2
      simp only [map_sub, RatFunc.algebraMap_X, ratFunc_algebraMap_C]
    rw [this]
    rwa [div_lt_iff₀ (norm_pos_iff.2 hc₀)] at hl1
  · have hcoe : ‖(Q m - Q n).coeff i‖ =
        ‖(PowerSeries.coeff i G - ((Q n).coeff i : UniformSpace.Completion C)) -
          (PowerSeries.coeff i G - ((Q m).coeff i : UniformSpace.Completion C))‖ := by
      rw [sub_sub_sub_cancel_left, ← UniformSpace.Completion.coe_sub,
        UniformSpace.Completion.norm_coe, coeff_sub]
    rw [hcoe]
    calc _ ≤ max ‖PowerSeries.coeff i G - ((Q n).coeff i : UniformSpace.Completion C)‖
          ‖PowerSeries.coeff i G - ((Q m).coeff i : UniformSpace.Completion C)‖ * ‖l‖ ^ i :=
          mul_le_mul_of_nonneg_right (Idem.norm_sub_le_max' _ _) (pow_nonneg (norm_nonneg _) _)
      _ = max (‖PowerSeries.coeff i G - ((Q n).coeff i : UniformSpace.Completion C)‖ * ‖l‖ ^ i)
          (‖PowerSeries.coeff i G - ((Q m).coeff i : UniformSpace.Completion C)‖ * ‖l‖ ^ i) :=
          max_mul_of_nonneg _ _ (pow_nonneg (norm_nonneg _) _)
      _ ≤ max (q ^ (2 ^ m)) (q ^ (2 ^ n)) := by
          rw [max_comm (q ^ (2 ^ m))]
          exact max_le_max (hql n i) (hql m i)
  · have h2 := tendsto_iff_norm_sub_tendsto_zero.1 (hconv ν' g₁ hcen₁)
    refine h2.congr fun n ↦ ?_
    set w := algebraMap (RatFunc C) L (aeval (gaussCoord b₀ (a - b₀)) (Q n))
    have e : toLocal g₁ w - toLocal g₁ (y' : L) = -toLocal g₁ ((y' : L) - w) := by
      rw [show (toLocal g₁) ((y' : L) - w) = toLocal g₁ (y' : L) - toLocal g₁ w from
        map_sub (toLocal g₁) _ _, neg_sub]
    rw [e, norm_neg, ← coe_nnnorm, ← extValuation_apply, hg₁]

end Germ

end TypeFour

end SemistableReduction
