/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussStability
import TemperedFundamentalGroups.SemistableReduction.PthPower
import TemperedFundamentalGroups.SemistableReduction.NormedTower
import TemperedFundamentalGroups.SemistableReduction.DiscLimit

/-!
# Covers split over small discs around unramified classical points

Blueprint §9.9, S8.2a.

* `exists_root_of_scaled`: Hensel's lemma with a scaling, in a complete non-archimedean field: if
  `δ = f'(a) ≠ 0`, `‖tₖ‖ ‖λ‖^(k-1) ≤ ‖δ‖` for the Taylor coefficients `tₖ` of `f` at `a`
  (`k ≥ 2`) and `‖f(a)‖ < ‖λ‖ ‖δ‖`, then `f` has a root `y` with `‖y - a‖ < ‖λ‖` (Hensel for the
  integral polynomial `f(a + λZ) / (λ δ)`, whose reduction has the simple root `0`);
* `natDegree_eq_one_of_splits`: for `F' = F(θ)` and a complete `K ⊇ F`, if a polynomial
  vanishing at `θ` splits over `K`, every local factor `K[X]/(g)` of `F' ⊗_F K` is `K` itself.
-/

open Polynomial IsLocalRing Valuation NNReal

namespace SemistableReduction

open FundamentalInequality DenseCompletion

namespace SplitDisc

/-! ### Hensel's lemma with a scaling -/

section Hensel

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

omit [IsUltrametricDist K] in
lemma coeff_comp_C_mul_X (p : K[X]) (r : K) (k : ℕ) :
    (p.comp (C r * X)).coeff k = p.coeff k * r ^ k := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [add_comp, coeff_add, coeff_add, hp, hq, add_mul]
  | monomial n c =>
    rw [← C_mul_X_pow_eq_monomial, mul_comp, C_comp, X_pow_comp, mul_pow, ← C_pow, ← mul_assoc,
      ← C_mul, coeff_C_mul_X_pow, coeff_C_mul_X_pow]
    split_ifs with h
    · rw [h]
    · rw [zero_mul]

variable [CompleteSpace K]

local notation "𝒪" => HenselComplete.integers K

/-- **Hensel's lemma with a scaling.** Let `δ = f'(a) ≠ 0` and `λ ≠ 0` with
`‖tₖ‖ ‖λ‖^(k-1) ≤ ‖δ‖` for the Taylor coefficients `tₖ` of `f` at `a`, `k ≥ 2`, and
`‖f(a)‖ < ‖λ‖ ‖δ‖`. Then `f` has a root `y` with `‖y - a‖ < ‖λ‖`. -/
theorem exists_root_of_scaled (f : K[X]) {a l : K} (hl : l ≠ 0)
    (hδ : f.derivative.eval a ≠ 0)
    (ht : ∀ k, 2 ≤ k → ‖(taylor a f).coeff k‖ * ‖l‖ ^ (k - 1) ≤ ‖f.derivative.eval a‖)
    (h0 : ‖f.eval a‖ < ‖l‖ * ‖f.derivative.eval a‖) :
    ∃ y, f.IsRoot y ∧ ‖y - a‖ < ‖l‖ := by
  set δ := f.derivative.eval a with hδdef
  set g : K[X] := C (l * δ)⁻¹ * (taylor a f).comp (C l * X) with hg
  have hcoeff (k : ℕ) : g.coeff k = (l * δ)⁻¹ * ((taylor a f).coeff k * l ^ k) := by
    rw [hg, coeff_C_mul, coeff_comp_C_mul_X]
  have hld : 0 < ‖l‖ * ‖δ‖ := mul_pos (norm_pos_iff.2 hl) (norm_pos_iff.2 hδ)
  have hg0 : ‖g.coeff 0‖ < 1 := by
    rw [hcoeff, taylor_coeff_zero, pow_zero, mul_one, norm_mul, norm_inv, norm_mul,
      inv_mul_lt_iff₀ hld, mul_one]
    exact h0
  have hg1 : g.coeff 1 = 1 := by
    rw [hcoeff, taylor_coeff_one, pow_one, ← hδdef]
    field_simp
  have hgk (k : ℕ) : ‖g.coeff k‖ ≤ 1 := by
    rcases k with _ | _ | k
    · exact hg0.le
    · rw [zero_add, hg1, norm_one]
    · rw [hcoeff, norm_mul, norm_inv, norm_mul, norm_mul, norm_pow, inv_mul_le_iff₀ hld, mul_one]
      have := ht (k + 2) (by omega)
      rw [show k + 2 - 1 = k + 1 by omega] at this
      calc ‖(taylor a f).coeff (k + 2)‖ * ‖l‖ ^ (k + 2)
          = ‖l‖ * (‖(taylor a f).coeff (k + 2)‖ * ‖l‖ ^ (k + 1)) := by ring
        _ ≤ ‖l‖ * ‖δ‖ := mul_le_mul_of_nonneg_left this (norm_nonneg _)
  obtain ⟨g', hg'⟩ := PthPower.exists_map_eq g hgk
  have hev (z : 𝒪) : g.eval (z : K) = ((g'.eval z : 𝒪) : K) := by
    rw [← hg', eval_map]
    exact eval₂_at_apply (algebraMap 𝒪 K) z
  have hder (z : 𝒪) : g.derivative.eval (z : K) = ((g'.derivative.eval z : 𝒪) : K) := by
    rw [← hg', derivative_map, eval_map]
    exact eval₂_at_apply (algebraMap 𝒪 K) z
  have hcoe0 : ((0 : 𝒪) : K) = 0 := rfl
  obtain ⟨z, hz, hz0⟩ := HenselComplete.exists_root_of_isUnit g' (a₀ := 0)
    ((HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).2 (by
      rw [← hev, hcoe0, ← coeff_zero_eq_eval_zero]
      exact hg0))
    ((HenselComplete.isUnit_iff_norm_eq_one _).2 (by
      rw [← hder, hcoe0, ← coeff_zero_eq_eval_zero, coeff_derivative, hg1]
      simp))
  have hzK : g.eval (z : K) = 0 := by
    rw [hev, hz.eq_zero]
    rfl
  have hz1 : ‖(z : K)‖ < 1 := by
    have := (HenselComplete.mem_maximalIdeal_iff_norm_lt_one _).1 hz0
    simpa using this
  refine ⟨a + l * z, ?_, ?_⟩
  · have h1 : g.eval (z : K) = (l * δ)⁻¹ * f.eval (a + l * z) := by
      rw [hg, eval_mul, eval_C, eval_comp, eval_mul, eval_C, eval_X, taylor_eval, add_comm]
    rw [h1, mul_eq_zero] at hzK
    exact hzK.resolve_left (inv_ne_zero (mul_ne_zero hl hδ))
  · rw [add_sub_cancel_left, norm_mul]
    exact mul_lt_of_lt_one_right (norm_pos_iff.2 hl) hz1

end Hensel

/-! ### Splitting and local degree one -/

section Abstract

open LocalGlobal

variable {F K F' : Type*} [NormedField F] [IsUltrametricDist F]
  [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra F K]
  [Field F'] [Algebra F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

omit [IsUltrametricDist F] [IsUltrametricDist K] [CompleteSpace K] in
/-- If `F' = F(θ)` and a nonzero polynomial vanishing at `θ` splits over the complete field
`K ⊇ F`, then every factor of `F' ⊗_F K` is `K`: the local factors have degree one. -/
theorem natDegree_eq_one_of_splits {θ : F'} (hθ : Algebra.adjoin F {θ} = ⊤) {Q : F[X]}
    (hQ0 : Q ≠ 0) (hQ : aeval θ Q = 0) (hs : (Q.map (algebraMap F K)).Splits)
    (g : Factor F K F') : g.1.natDegree = 1 := by
  have hθL : toLocal g θ ∈ (algebraMap K (Local K g.1)).range := by
    refine hs.mem_range_of_isRoot (map_ne_zero hQ0) ?_
    rw [IsRoot, map_map, ← IsScalarTower.algebraMap_eq, eval_map_algebraMap, aeval_algHom_apply,
      hQ, map_zero]
  let S : Subalgebra F (Local K g.1) := (Algebra.ofId K (Local K g.1)).range.restrictScalars F
  have hle : Algebra.adjoin F {toLocal g θ} ≤ S := by
    refine Algebra.adjoin_le (Set.singleton_subset_iff.2 ?_)
    obtain ⟨c, hc⟩ := hθL
    exact ⟨c, hc⟩
  have hgen : root g.1 ∈ S := by
    rw [← toLocal_gen]
    apply hle
    rw [← Set.image_singleton, ← AlgHom.map_adjoin, hθ]
    exact ⟨_, Algebra.mem_top, rfl⟩
  obtain ⟨c, hc⟩ := hgen
  have hdvd : g.1 ∣ X - C c := by
    rw [← AdjoinRoot.mk_eq_zero, _root_.map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero]
    exact hc.symm
  have := natDegree_le_of_dvd hdvd (X_sub_C_ne_zero c)
  rw [natDegree_X_sub_C] at this
  exact le_antisymm this (irreducible_of_mem_factors g.2).natDegree_pos

/-- Under the hypotheses of `natDegree_eq_one_of_splits`, `F'` has exactly `[F' : F]` extensions
of the norm of `F`. -/
theorem card_extension_eq_finrank (hd : DenseRange (algebraMap F K)) {θ : F'}
    (hθ : Algebra.adjoin F {θ} = ⊤) {Q : F[X]}
    (hQ0 : Q ≠ 0) (hQ : aeval θ Q = 0) (hs : (Q.map (algebraMap F K)).Splits) :
    Nat.card (Extension F F') = Module.finrank F F' := by
  haveI := Fact.mk hd
  rw [card_extension K, ← sum_natDegree_factors (K := K), Finset.card_eq_sum_ones]
  exact Finset.sum_congr rfl fun g hg ↦ (natDegree_eq_one_of_splits hθ hQ0 hQ hs ⟨g, hg⟩).symm

/-- Under the hypotheses of `natDegree_eq_one_of_splits`, every extension of the norm of `F` to
`F'` has `e = f = 1`. -/
theorem ramificationIdx_eq_one_and_inertiaDeg_eq_one (hd : DenseRange (algebraMap F K))
    {θ : F'} (hθ : Algebra.adjoin F {θ} = ⊤)
    {Q : F[X]} (hQ0 : Q ≠ 0) (hQ : aeval θ Q = 0) (hs : (Q.map (algebraMap F K)).Splits)
    (w : Extension F F') :
    ramificationIdx F w.1 = 1 ∧ inertiaDeg (NormedField.valuation (K := F)) w.1 = 1 := by
  haveI := Fact.mk hd
  obtain ⟨g, rfl⟩ := (extensionEquiv (K := K)).surjective w
  change ramificationIdx F (extValuation g) = 1 ∧
    inertiaDeg (NormedField.valuation (K := F)) (extValuation g) = 1
  rw [ramificationIdx_extValuation, inertiaDeg_extValuation]
  have hfr : Module.finrank K (Local K g.1) = 1 := by
    rw [finrank_local, natDegree_eq_one_of_splits hθ hQ0 hQ hs g]
  have hle := ramificationIdx_mul_inertiaDeg_le (K := K) (L := Local K g.1)
    (v := NormedField.valuation (K := K)) (w := NormedField.valuation (K := Local K g.1))
  have he := ramificationIdx_ne_zero (K := K) (NormedField.valuation (K := Local K g.1))
  have hf := NormedTower.inertiaDeg_pos (v := NormedField.valuation (K := K))
    (w := NormedField.valuation (K := Local K g.1))
  rw [hfr] at hle
  have he1 : 1 ≤ ramificationIdx K (NormedField.valuation (K := Local K g.1)) :=
    Nat.one_le_iff_ne_zero.2 he
  constructor <;> nlinarith

end Abstract

/-! ### Estimates on a small disc -/

section Estimates

variable {E : Type*} [NontriviallyNormedField E]

open DiscLimit (lin)

/-- The maximal absolute value of the Taylor coefficients of `h` at `a`. -/
noncomputable def taylorBound (a : E) (h : E[X]) : ℝ≥0 :=
  (Finset.range (h.natDegree + 1)).sup fun k ↦ ‖(taylor a h).coeff k‖₊

@[simp]
lemma taylorBound_zero (a : E) : taylorBound a 0 = 0 := by
  simp [taylorBound]

variable {w : Valuation (RatFunc E) ℝ≥0}

/-- On the closed unit disc `w(X - a) ≤ 1` around `a`, `w(h)` is bounded by the Taylor
coefficients of `h` at `a`. -/
lemma valuation_le_taylorBound (hw : ∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) {a : E}
    (hX : w (lin a) ≤ 1) (h : E[X]) :
    w (algebraMap E[X] (RatFunc E) h) ≤ taylorBound a h := by
  conv_lhs => rw [← sum_taylor_eq h a]
  rw [Polynomial.sum_def, map_sum]
  refine Valuation.map_sum_le _ fun k hk ↦ ?_
  simp only [map_mul, map_pow, ratFunc_algebraMap_C, hw]
  have hk' : k ∈ Finset.range (h.natDegree + 1) := by
    rw [Finset.mem_range, Nat.lt_succ_iff, ← natDegree_taylor h a]
    exact le_natDegree_of_mem_supp k hk
  calc ‖(taylor a h).coeff k‖₊ * w (lin a) ^ k ≤ ‖(taylor a h).coeff k‖₊ * 1 :=
        mul_le_mul_right (pow_le_one' hX k) _
    _ ≤ taylorBound a h := by
        rw [mul_one]
        exact Finset.le_sup (f := fun k ↦ ‖(taylor a h).coeff k‖₊) hk'

/-- A polynomial vanishing at `a` is small on a small disc around `a`. -/
lemma valuation_le_of_isRoot (hw : ∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) {a : E}
    (hX : w (lin a) ≤ 1) {h : E[X]} (ha : h.IsRoot a) :
    w (algebraMap E[X] (RatFunc E) h) ≤ taylorBound a (h /ₘ (X - C a)) * w (lin a) := by
  conv_lhs => rw [← mul_divByMonic_eq_iff_isRoot.2 ha]
  rw [map_mul, Valuation.map_mul, mul_comm]
  exact mul_le_mul_left (valuation_le_taylorBound hw hX _) _

/-- On a small disc around `a`, `w(h) = |h(a)|` (if the disc is small compared to `|h(a)|`). -/
lemma valuation_eq_of_lt (hw : ∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) {a : E}
    (hX : w (lin a) ≤ 1) {h : E[X]}
    (hlt : taylorBound a ((h - C (h.eval a)) /ₘ (X - C a)) * w (lin a) < ‖h.eval a‖₊) :
    w (algebraMap E[X] (RatFunc E) h) = ‖h.eval a‖₊ := by
  have hroot : (h - C (h.eval a)).IsRoot a := by simp
  have h1 := valuation_le_of_isRoot hw hX hroot
  rw [show h = (h - C (h.eval a)) + C (h.eval a) by ring, map_add,
    Valuation.map_add_eq_of_lt_right, ratFunc_algebraMap_C, hw]
  · simp
  · rw [ratFunc_algebraMap_C, hw]
    exact h1.trans_lt hlt

end Estimates

/-- Taylor expansion commutes with base change. -/
lemma map_taylor {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S) (r : R)
    (p : R[X]) : (taylor r p).map φ = taylor (φ r) (p.map φ) := by
  rw [taylor_apply, taylor_apply, Polynomial.map_comp, Polynomial.map_add, map_X, map_C]

/-! ### Splitting over a small disc -/

section Disc

open DiscLimit (lin)
open UniformSpace Filter Topology

variable {E : Type*} [NontriviallyNormedField E]

/-- The completion of `E(X)` at a real valuation `w`. -/
abbrev Compl (w : Valuation (RatFunc E) ℝ≥0) : Type _ := Completion (WithAbs w.toAbsoluteValue)

/-- The map `E[X] → \hat{E(X)}_w`. -/
noncomputable def ι (w : Valuation (RatFunc E) ℝ≥0) : E[X] →+* Compl w :=
  (algebraMap (WithAbs w.toAbsoluteValue) (Compl w)).comp
    (algebraMap E[X] (WithAbs w.toAbsoluteValue))

lemma norm_ι (w : Valuation (RatFunc E) ℝ≥0) (h : E[X]) :
    ‖ι w h‖ = w (algebraMap E[X] (RatFunc E) h) := by
  rw [ι, RingHom.comp_apply]
  erw [algebraMap_completion]
  rw [Completion.norm_coe, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq]
  rfl

/-- **Roots near a simple root of the specialization.** Let `P ∈ E[x][Y]` and `β` a simple root
of `P(a, Y)`. For every `ρ > 0` there is `s > 0` such that for every real valuation `w` of `E(x)`
extending the norm of `E` with `w(x - a) < s` (of any type), `P` has a root `y` in the completion
of `E(x)` at `w` with `‖y - β‖ < ρ`. -/
theorem exists_isRoot_near (P : E[X][X]) {a β : E} (hβ : (P.map (evalRingHom a)).IsRoot β)
    (hd : (P.map (evalRingHom a)).derivative.eval β ≠ 0) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ s : ℝ≥0, 0 < s ∧ ∀ w : Valuation (RatFunc E) ℝ≥0,
      (∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) → w (lin a) < s →
        ∃ y : Compl w, (P.map (ι w)).IsRoot y ∧ ‖y - ι w (C β)‖ < ρ := by
  set P₀ := P.map (evalRingHom a)
  set d := P₀.derivative.eval β
  set t : ℕ → E[X] := fun k ↦ (taylor (C β) P).coeff k with ht
  have ht_eval (k : ℕ) : (t k).eval a = (taylor β P₀).coeff k := by
    have := congrArg (fun q ↦ q.coeff k) (map_taylor (evalRingHom a) (C β) P)
    simp only [coeff_map, coe_evalRingHom, eval_C] at this
    exact this
  have ht0 : (t 0).IsRoot a := by
    rw [IsRoot, ht_eval, taylor_coeff_zero]
    exact hβ
  have ht1 : (t 1).eval a = d := by rw [ht_eval, taylor_coeff_one]
  set B : ℝ≥0 := (Finset.range ((taylor (C β) P).natDegree + 1)).sup fun k ↦ taylorBound a (t k)
  have hB (k : ℕ) : taylorBound a (t k) ≤ B := by
    by_cases hk : k ≤ (taylor (C β) P).natDegree
    · exact Finset.le_sup (f := fun k ↦ taylorBound a (t k))
        (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
    · rw [ht]
      dsimp only
      rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hk), taylorBound_zero]
      exact bot_le
  have hd0 : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hB1 : (0 : ℝ) < B + 1 := by positivity
  obtain ⟨l, hl0, hlr⟩ := NormedField.exists_norm_lt E
    (lt_min hρ (lt_min one_pos (div_pos hd0 hB1)))
  have hlρ : ‖l‖ < ρ := hlr.trans_le (min_le_left _ _)
  have hl1 : ‖l‖ ≤ 1 := (hlr.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hlB : ‖l‖ * (B + 1) ≤ ‖d‖ :=
    ((lt_div_iff₀ hB1).1 (hlr.trans_le ((min_le_right _ _).trans (min_le_right _ _)))).le
  set M0 := taylorBound a (t 0 /ₘ (X - C a))
  set M1 := taylorBound a ((t 1 - C ((t 1).eval a)) /ₘ (X - C a))
  have hd0' : 0 < ‖d‖₊ := nnnorm_pos.2 hd
  have hl0' : 0 < ‖l‖₊ := nnnorm_pos.2 (norm_pos_iff.1 hl0)
  refine ⟨min 1 (min (‖d‖₊ / (M1 + 1)) (‖l‖₊ * ‖d‖₊ / (M0 + 1))),
    lt_min one_pos (lt_min (div_pos hd0' (by positivity))
      (div_pos (mul_pos hl0' hd0') (by positivity))), fun w hw hlt ↦ ?_⟩
  have hX : w (lin a) ≤ 1 := hlt.le.trans (min_le_left _ _)
  have hs1 : w (lin a) * (M1 + 1) < ‖d‖₊ :=
    (lt_div_iff₀ (by positivity)).1 (hlt.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hs2 : w (lin a) * (M0 + 1) < ‖l‖₊ * ‖d‖₊ :=
    (lt_div_iff₀ (by positivity)).1 (hlt.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hT1 : w (algebraMap E[X] (RatFunc E) (t 1)) = ‖d‖₊ := by
    rw [← ht1]
    refine valuation_eq_of_lt hw hX ?_
    rw [show ‖(t 1).eval a‖₊ = ‖d‖₊ by rw [ht1]]
    refine lt_of_le_of_lt ?_ hs1
    rw [mul_comm (w (lin a))]
    gcongr
    exact le_self_add
  have hT0 : w (algebraMap E[X] (RatFunc E) (t 0)) < ‖l‖₊ * ‖d‖₊ := by
    refine (valuation_le_of_isRoot hw hX ht0).trans_lt (lt_of_le_of_lt ?_ hs2)
    rw [mul_comm (w (lin a))]
    gcongr
    exact le_self_add
  have htay (k : ℕ) : (taylor (ι w (C β)) (P.map (ι w))).coeff k = ι w (t k) := by
    rw [← map_taylor, coeff_map]
  have hnl : ‖ι w (C l)‖ = ‖l‖ := by
    rw [norm_ι, ratFunc_algebraMap_C, hw, coe_nnnorm]
  have hder : (P.map (ι w)).derivative.eval (ι w (C β)) = ι w (t 1) := by
    rw [← taylor_coeff_one, htay]
  have hval : (P.map (ι w)).eval (ι w (C β)) = ι w (t 0) := by
    rw [← taylor_coeff_zero, htay]
  have hnd : ‖ι w (t 1)‖ = ‖d‖ := by rw [norm_ι, hT1, coe_nnnorm]
  obtain ⟨y, hy, hya⟩ := exists_root_of_scaled (P.map (ι w)) (a := ι w (C β)) (l := ι w (C l))
    (norm_ne_zero_iff.1 (by rw [hnl]; exact hl0.ne'))
    (by rw [hder]; exact norm_ne_zero_iff.1 (by rw [hnd]; exact hd0.ne'))
    (fun k hk ↦ by
      rw [htay, hder, hnd, hnl, norm_ι]
      have h1 : (w (algebraMap E[X] (RatFunc E) (t k)) : ℝ) ≤ B :=
        NNReal.coe_le_coe.2 ((valuation_le_taylorBound hw hX _).trans (hB k))
      have h2 : ‖l‖ ^ (k - 1) ≤ ‖l‖ := pow_le_of_le_one (norm_nonneg _) hl1 (by omega)
      calc (w (algebraMap E[X] (RatFunc E) (t k)) : ℝ) * ‖l‖ ^ (k - 1) ≤ B * ‖l‖ :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ ≤ ‖d‖ := by nlinarith [norm_nonneg l])
    (by
      rw [hval, hder, hnd, hnl, norm_ι]
      have := NNReal.coe_lt_coe.2 hT0
      simpa using this)
  exact ⟨y, hy, hya.trans_eq hnl |>.trans hlρ⟩

lemma norm_ι_C_sub (w : Valuation (RatFunc E) ℝ≥0) (hw : ∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊)
    (b b' : E) : ‖ι w (C b) - ι w (C b')‖ = ‖b - b'‖ := by
  rw [← _root_.map_sub, ← C_sub, norm_ι, ratFunc_algebraMap_C, hw, coe_nnnorm]

/-- **S8.2a, splitting.** Let `P ∈ E[x][Y]` be monic in `Y` with separable specialization
`P(a, Y)`, `E` algebraically closed. There is `s > 0` such that for every real valuation `w` of
`E(x)` extending the norm of `E` with `w(x - a) < s` (of any type), `P` splits into linear
factors over the completion of `E(x)` at `w`. -/
theorem exists_forall_splits [IsAlgClosed E] (P : E[X][X]) (hP : P.Monic) (a : E)
    (hsep : (P.map (evalRingHom a)).Separable) :
    ∃ s : ℝ≥0, 0 < s ∧ ∀ w : Valuation (RatFunc E) ℝ≥0,
      (∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) → w (lin a) < s → (P.map (ι w)).Splits := by
  classical
  set P₀ := P.map (evalRingHom a)
  set R := P₀.roots.toFinset
  let sep : E → ℝ := fun β ↦
    (insert 1 ((R.erase β).image fun β' ↦ ‖β - β'‖)).min' (Finset.insert_nonempty _ _)
  have hsep_pos (β : E) : 0 < sep β := by
    refine (Finset.lt_min'_iff _ _).2 fun z hz ↦ ?_
    rcases Finset.mem_insert.1 hz with h | h
    · rw [h]
      exact one_pos
    · obtain ⟨β', hβ', rfl⟩ := Finset.mem_image.1 h
      exact norm_pos_iff.2 (sub_ne_zero.2 (Finset.ne_of_mem_erase hβ').symm)
  have hsep_le {β β' : E} (hβ' : β' ∈ R) (hne : β' ≠ β) : sep β ≤ ‖β - β'‖ :=
    Finset.min'_le _ _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem _ (Finset.mem_erase.2 ⟨hne, hβ'⟩)))
  have hev : ∀ β ∈ R, ∀ᶠ s in 𝓝[>] (0 : ℝ≥0), ∀ w : Valuation (RatFunc E) ℝ≥0,
      (∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) → w (lin a) < s →
        ∃ y : Compl w, (P.map (ι w)).IsRoot y ∧ ‖y - ι w (C β)‖ < sep β := by
    intro β hβ
    have hroot : P₀.IsRoot β := (mem_roots'.1 (Multiset.mem_toFinset.1 hβ)).2
    have hd : P₀.derivative.eval β ≠ 0 := by
      have := hsep.aeval_derivative_ne_zero (x := β) (by simpa [aeval_def] using hroot)
      simpa [aeval_def] using this
    obtain ⟨s, hs, H⟩ := exists_isRoot_near P hroot hd (hsep_pos β)
    filter_upwards [Ioo_mem_nhdsGT hs] with s' hs' w hw hlt using H w hw (hlt.trans hs'.2)
  obtain ⟨s, hall, hs0⟩ := (((Filter.eventually_all_finset R).2 hev).and
    self_mem_nhdsWithin).exists
  refine ⟨s, hs0, fun w hw hlt ↦ ?_⟩
  choose! y hy using fun β hβ ↦ hall β hβ w hw hlt
  have hinj : Set.InjOn y R := by
    intro β hβ β' hβ' heq
    by_contra hne
    have h1 := (hy β hβ).2
    have h2 := (hy β' hβ').2
    rw [heq] at h1
    have h1' : ‖ι w (C β) - y β'‖ < ‖β - β'‖ := by
      rw [norm_sub_rev]
      exact h1.trans_le (hsep_le hβ' (Ne.symm hne))
    have h2' : ‖y β' - ι w (C β')‖ < ‖β - β'‖ := by
      rw [norm_sub_rev β]
      exact h2.trans_le (hsep_le hβ hne)
    have : ‖ι w (C β) - ι w (C β')‖ < ‖β - β'‖ := by
      have := dist_triangle_max (ι w (C β)) (y β') (ι w (C β'))
      rw [dist_eq_norm, dist_eq_norm, dist_eq_norm] at this
      exact this.trans_lt (max_lt h1' h2')
    rw [norm_ι_C_sub w hw] at this
    exact lt_irrefl _ this
  have hne0 : P.map (ι w) ≠ 0 := (hP.map _).ne_zero
  rw [splits_iff_card_roots]
  refine le_antisymm (card_roots' _) ?_
  calc (P.map (ι w)).natDegree = P₀.natDegree := by rw [hP.natDegree_map, hP.natDegree_map]
    _ = R.card := by
      rw [Multiset.toFinset_card_of_nodup (nodup_roots hsep), IsAlgClosed.card_roots_eq_natDegree]
    _ = (R.image y).card := (Finset.card_image_of_injOn hinj).symm
    _ ≤ (P.map (ι w)).roots.toFinset.card := Finset.card_le_card fun z hz ↦ by
        obtain ⟨β, hβ, rfl⟩ := Finset.mem_image.1 hz
        exact Multiset.mem_toFinset.2 ((mem_roots hne0).2 (hy β hβ).1)
    _ ≤ _ := Multiset.toFinset_card_le _

end Disc

/-! ### Extensions of a valuation of `E(X)` -/

section Ext

open DiscLimit (lin)
open UniformSpace LocalGlobal

universe u

variable {E : Type*} [NontriviallyNormedField E] (w : Valuation (RatFunc E) ℝ≥0)
  (F' : Type*) [Field F'] [Algebra (RatFunc E) F']

/-- The real valuations of `F'` extending the valuation `w` of `E(X)`. -/
def ValExt : Type _ := {w' : Valuation F' ℝ≥0 // w'.comap (algebraMap (RatFunc E) F') = w}

instance (w' : ValExt w F') : w.HasExtension w'.1 := hasExtension_of_comap_eq w'.2

variable {w F'}

lemma algebraMap_withAbs_apply (x : WithAbs w.toAbsoluteValue) :
    algebraMap (WithAbs w.toAbsoluteValue) F' x = algebraMap (RatFunc E) F' x.ofAbs := rfl

lemma comap_withAbs (w' : Valuation F' ℝ≥0) :
    w'.comap (algebraMap (WithAbs w.toAbsoluteValue) F') =
        NormedField.valuation (K := WithAbs w.toAbsoluteValue) ↔
      w'.comap (algebraMap (RatFunc E) F') = w := by
  constructor
  · intro h
    ext y
    have := congrArg (fun v : Valuation (WithAbs w.toAbsoluteValue) ℝ≥0 ↦
      v (WithAbs.toAbs _ y)) h
    simp only [comap_apply, algebraMap_withAbs_apply, valuation_withAbs] at this
    rw [comap_apply, this]
  · intro h
    ext x
    have := congrArg (fun v : Valuation (RatFunc E) ℝ≥0 ↦ v x.ofAbs) h
    simp only [comap_apply] at this
    rw [comap_apply, algebraMap_withAbs_apply, valuation_withAbs, this]

/-- The extensions of `w` are the extensions of the norm of `E(X)` normed by `w`. -/
def valExtEquiv : ValExt w F' ≃ Extension (WithAbs w.toAbsoluteValue) F' where
  toFun w' := ⟨w'.1, (comap_withAbs w'.1).2 w'.2⟩
  invFun w' := ⟨w'.1, (comap_withAbs w'.1).1 w'.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma ramificationIdx_withAbs (w' : Valuation F' ℝ≥0) :
    ramificationIdx (WithAbs w.toAbsoluteValue) w' = ramificationIdx (RatFunc E) w' := by
  have h : valueGroup (w'.comap (algebraMap (WithAbs w.toAbsoluteValue) F')) =
      valueGroup (w'.comap (algebraMap (RatFunc E) F')) := by
    ext g
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.ofAbs, hx⟩, fun ⟨y, hy⟩ ↦ ⟨WithAbs.toAbs _ y, hy⟩⟩
  rw [ramificationIdx, ramificationIdx, h]

lemma inertiaDeg_withAbs (w' : ValExt w F') :
    inertiaDeg (NormedField.valuation (K := WithAbs w.toAbsoluteValue)) (valExtEquiv w').1 =
      inertiaDeg w w'.1 := by
  let e : (NormedField.valuation (K := WithAbs w.toAbsoluteValue)).valuationSubring ≃+*
      w.valuationSubring :=
    { toFun := fun x ↦ ⟨x.1.ofAbs, by
        have := x.2
        rwa [mem_valuationSubring_iff, valuation_withAbs] at this⟩
      invFun := fun y ↦ ⟨WithAbs.toAbs _ y.1, by
        rw [mem_valuationSubring_iff, valuation_withAbs]
        exact y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  refine Algebra.finrank_eq_of_equiv_equiv (IsLocalRing.ResidueField.mapEquiv e)
    (RingEquiv.refl _) ?_
  ext r
  obtain ⟨x, rfl⟩ := residue_surjective r
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, IsLocalRing.ResidueField.mapEquiv_apply,
    IsLocalRing.ResidueField.map_residue]
  rw [HasExtension.algebraMap_residue_eq_residue_algebraMap,
    HasExtension.algebraMap_residue_eq_residue_algebraMap]
  rfl

lemma adjoin_withAbs {θ : F'} (hθ : Algebra.adjoin (RatFunc E) {θ} = ⊤) :
    Algebra.adjoin (WithAbs w.toAbsoluteValue) {θ} = ⊤ := by
  have hrange : Set.range (algebraMap (WithAbs w.toAbsoluteValue) F') =
      Set.range (algebraMap (RatFunc E) F') := by
    ext z
    exact ⟨fun ⟨x, hx⟩ ↦ ⟨x.ofAbs, hx⟩, fun ⟨y, hy⟩ ↦ ⟨WithAbs.toAbs _ y, hy⟩⟩
  apply Subalgebra.toSubring_injective
  rw [Algebra.adjoin_eq_ring_closure, hrange, ← Algebra.adjoin_eq_ring_closure, hθ,
    Algebra.top_toSubring, Algebra.top_toSubring]

lemma aeval_withAbs (P : E[X][X]) (θ : F') :
    aeval θ (P.map (algebraMap E[X] (WithAbs w.toAbsoluteValue))) =
      aeval θ (P.map (algebraMap E[X] (RatFunc E))) := by
  rw [aeval_def, aeval_def, eval₂_map, eval₂_map]
  rfl

/-- The completion of `E(X)` at `w` is nontrivially normed if `w` extends the norm of `E`. -/
noncomputable abbrev nontriviallyNormedFieldCompl
    (hw : ∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) :
    NontriviallyNormedField (Completion (WithAbs w.toAbsoluteValue)) where
  __ : NormedField (Completion (WithAbs w.toAbsoluteValue)) := inferInstance
  non_trivial :=
    let ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := E)
    ⟨((algebraMap E (WithAbs w.toAbsoluteValue) x : WithAbs w.toAbsoluteValue) :
        Completion (WithAbs w.toAbsoluteValue)), by
      rw [Completion.norm_coe, WithAbs.algebraMap_right_apply, WithAbs.norm_toAbs_eq,
        Valuation.toAbsoluteValue_apply, hw, coe_nnnorm]
      exact hx⟩

/-- **S8.2a (unramified classical points).** Let `E` be algebraically closed, `P ∈ E[x][Y]` monic
in `Y` with separable specialization `P(a, Y)`. There is `s > 0` such that for every real valuation
`w` of `E(x)` extending the norm of `E` with `w(x - a) < s` (of any type) and every finite
separable `F' = E(x)(θ)` with `P(θ) = 0`: `w` has exactly `[F' : E(x)]` extensions to `F'`, each
with `e = f = 1`. In other words, the cover is trivial over the small disc `|x - a| < s`. -/
theorem exists_forall_card_eq_finrank [IsAlgClosed E] (P : E[X][X]) (hP : P.Monic) (a : E)
    (hsep : (P.map (evalRingHom a)).Separable) :
    ∃ s : ℝ≥0, 0 < s ∧ ∀ w : Valuation (RatFunc E) ℝ≥0,
      (∀ c, w (algebraMap E (RatFunc E) c) = ‖c‖₊) → w (lin a) < s →
      ∀ (F' : Type u) [Field F'] [Algebra (RatFunc E) F'] [FiniteDimensional (RatFunc E) F']
        [Algebra.IsSeparable (RatFunc E) F'] (θ : F'), Algebra.adjoin (RatFunc E) {θ} = ⊤ →
        aeval θ (P.map (algebraMap E[X] (RatFunc E))) = 0 →
        Nat.card (ValExt w F') = Module.finrank (RatFunc E) F' ∧
          ∀ w' : ValExt w F', ramificationIdx (RatFunc E) w'.1 = 1 ∧ inertiaDeg w w'.1 = 1 := by
  obtain ⟨s, hs, H⟩ := exists_forall_splits P hP a hsep
  refine ⟨s, hs, fun w hw hlt F' _ _ _ _ θ hθ hPθ ↦ ?_⟩
  set F := WithAbs w.toAbsoluteValue
  letI : NontriviallyNormedField (Completion F) := nontriviallyNormedFieldCompl hw
  have hd : DenseRange (algebraMap F (Completion F)) := denseRange_algebraMap_completion F
  have hθF : Algebra.adjoin F {θ} = ⊤ := adjoin_withAbs hθ
  set Q : F[X] := P.map (algebraMap E[X] F)
  have hQ0 : Q ≠ 0 := (hP.map _).ne_zero
  have hQθ : aeval θ Q = 0 := (aeval_withAbs P θ).trans hPθ
  have hQs : (Q.map (algebraMap F (Completion F))).Splits := by
    rw [Polynomial.map_map]
    exact H w hw hlt
  have hdeg : Module.finrank F F' = Module.finrank (RatFunc E) F' :=
    Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv _) (RingEquiv.refl F') (by ext; rfl)
  refine ⟨?_, fun w' ↦ ?_⟩
  · rw [Nat.card_congr valExtEquiv, ← hdeg]
    exact card_extension_eq_finrank (K := Completion F) hd hθF hQ0 hQθ hQs
  · obtain ⟨he, hf⟩ := ramificationIdx_eq_one_and_inertiaDeg_eq_one (K := Completion F) hd hθF
      hQ0 hQθ hQs (valExtEquiv w')
    rw [← ramificationIdx_withAbs (w := w), ← inertiaDeg_withAbs]
    exact ⟨he, hf⟩

end Ext

end SplitDisc

end SemistableReduction
