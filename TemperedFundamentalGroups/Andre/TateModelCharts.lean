/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateNormalAlgebra
import TemperedFundamentalGroups.Andre.TateModel
import TemperedFundamentalGroups.SemistableReduction.ProjScheme


/-!
# The charts of the Tate model are integrally closed

Let `O` be a discrete valuation ring with uniformizer `π` and `b₄ b₆ ∈ O` such that
`d = X² + 4 (π X³ + π b₄ X + b₆)` is squarefree in `O[X]`. Let `L` be the function field of the
Tate curve (`TateNormal.TateField`, the fraction field of `O[X][Y]/(Y² + XY − c)`), with the
generic point `[a : b : 1]` of the cubic `F = v²w + uvw − πu³ − πb₄uw² − b₆w³`
(`TateNormal.coords`; `a = x/π`, `b = y/π`).

* `F_dvd_of_eval_eq_zero`: a homogeneous polynomial vanishing at `[a : b : 1]` is a multiple of
  `F` (the homogeneous kernel of the generic point is `(F)`).
* `map_eq_zero_of_ev_eq_zero`: the kernel of a chart `O[u, v, w] → L`, `x_j ↦ x_j / x_i`
  (evaluated at the generic point), is killed by every ring map with `x_i ↦ 1`, `F ↦ 0`.
* `intClosedIn_chart_two`, `intClosedIn_chart_zero`, `intClosedIn_chart_one`: the three standard
  charts `O[x_j / x_i] ⊆ L` are integrally closed in `L`. The chart `w ≠ 0` is
  `O[X][Y]/(f)` (`TateNormal.isIntegrallyClosed`); the chart `u ≠ 0` follows by the `s`-lemma
  `IntClosedIn.of_loc` for `s = w/u` (its quotient is `k[v/u]`); the chart `v ≠ 0` by the
  `s`-lemma for `s = u/v` (its quotient is `O[t]/(t − b₆ t³)`, reduced as `2 ≠ 0`).
-/

open Polynomial

namespace TemperedFundamentalGroups.TateNormal

noncomputable section

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable (π b₄ b₆ : O) [Fact (Squarefree (dpoly π b₄ b₆))]

local notation "L" => TateField π b₄ b₆

local notation "Pol" => MvPolynomial (Fin (2 + 1)) O

/-- `a = X` in the function field. -/
abbrev aL : L := algebraMap O[X] L X

/-- `b = Y` in the function field. -/
abbrev bL : L := algebraMap (TateRing π b₄ b₆) L (bA π b₄ b₆)

/-- The homogeneous coordinates `[a : b : 1]` of the generic point of the Tate model. -/
abbrev coords : Fin (2 + 1) → L := ![aL π b₄ b₆, bL π b₄ b₆, 1]

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma algebraMap_O_apply (o : O) :
    algebraMap O L o = algebraMap O[X] L (Polynomial.C o) := by
  rw [IsScalarTower.algebraMap_apply O O[X] L]
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma algebraMap_of (p : O[X]) :
    algebraMap (TateRing π b₄ b₆) L (AdjoinRoot.of _ p) = algebraMap O[X] L p :=
  (IsScalarTower.algebraMap_apply O[X] (TateRing π b₄ b₆) L p).symm

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma bL_sq : bL π b₄ b₆ ^ 2 =
    -(aL π b₄ b₆ * bL π b₄ b₆) + algebraMap O[X] L (cpoly π b₄ b₆) := by
  have := congrArg (algebraMap (TateRing π b₄ b₆) L) (bA_sq π b₄ b₆)
  rwa [map_pow, map_add, map_neg, map_mul, algebraMap_of, algebraMap_of] at this

/-- Dehomogenization at `w = 1`: `O[u, v, w] → O[X][Y]`, `u ↦ X`, `v ↦ Y`, `w ↦ 1`. -/
def dehom : MvPolynomial (Fin (2 + 1)) O →+* O[X][X] :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp Polynomial.C) ![Polynomial.C X, X, 1]

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma dehom_F : dehom (TateModel.F π b₄ b₆) = fpoly π b₄ b₆ := by
  simp [dehom, TateModel.F, fpoly, cpoly]
  ring

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma eval_eq_dehom (g : MvPolynomial (Fin (2 + 1)) O) :
    MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) g =
      algebraMap (TateRing π b₄ b₆) L (AdjoinRoot.mk _ (dehom g)) := by
  rw [← MvPolynomial.coe_eval₂Hom, ← RingHom.comp_apply, ← RingHom.comp_apply]
  congr 1
  refine MvPolynomial.ringHom_ext (fun o ↦ ?_) (fun i ↦ ?_)
  · simp [dehom, algebraMap_O_apply, IsScalarTower.algebraMap_apply O[X] (TateRing π b₄ b₆) L]
  · fin_cases i
    · simp [dehom, IsScalarTower.algebraMap_apply O[X] (TateRing π b₄ b₆) L]
    · simp [dehom]
    · simp [dehom]

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma eval_F : MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) (TateModel.F π b₄ b₆) = 0 := by
  rw [eval_eq_dehom, dehom_F, AdjoinRoot.mk_self, map_zero]

omit [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma X_two_not_dvd_F (hπ : π ≠ 0) : ¬ (MvPolynomial.X 2 : MvPolynomial (Fin (2 + 1)) O) ∣
    TateModel.F π b₄ b₆ := by
  rintro ⟨Q, hQ⟩
  have h := congrArg (MvPolynomial.eval₂Hom MvPolynomial.C
    ![MvPolynomial.X 0, MvPolynomial.X 1, 0]) hQ
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, MvPolynomial.eval₂Hom_C_eq_bind₁, TateModel.F,
    Fin.isValue, RingHom.coe_coe, map_sub, map_add, map_mul, map_pow,
    MvPolynomial.bind₁_X_right, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.cons_val,
    mul_zero, add_zero, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, zero_sub, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, zero_mul, neg_eq_zero, mul_eq_zero,
    MvPolynomial.C_eq_zero, pow_eq_zero_iff, MvPolynomial.X_ne_zero, or_false] at h
  exact hπ h

omit [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- **The homogeneous elements of the kernel of the generic point are multiples of `F`.** -/
theorem F_dvd_of_eval_eq_zero (hπ : π ≠ 0) {g : MvPolynomial (Fin (2 + 1)) O} {n : ℕ}
    (hg : g.IsHomogeneous n)
    (h0 : MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) g = 0) :
    TateModel.F π b₄ b₆ ∣ g := by
  classical
  set w : MvPolynomial (Fin (2 + 1)) O := MvPolynomial.X 2
  set Loc := Localization.Away w
  set μ : Loc := IsLocalization.Away.invSelf w
  have hμ : algebraMap Pol Loc w * μ = 1 := IsLocalization.Away.mul_invSelf w
  set H : O[X][X] →+* Loc := Polynomial.eval₂RingHom
    (Polynomial.eval₂RingHom ((algebraMap Pol Loc).comp MvPolynomial.C)
      (μ * algebraMap Pol Loc (MvPolynomial.X 0)))
      (μ * algebraMap Pol Loc (MvPolynomial.X 1))
  have hHD : H.comp dehom = MvPolynomial.eval₂Hom ((algebraMap Pol Loc).comp MvPolynomial.C)
      (fun i ↦ μ * algebraMap Pol Loc (MvPolynomial.X i)) := by
    refine MvPolynomial.ringHom_ext (fun o ↦ ?_) (fun i ↦ ?_)
    · simp [H, dehom]
    · fin_cases i
      · simp [H, dehom]
      · simp [H, dehom]
      · simp [H, dehom, w, mul_comm μ, hμ]
  have hhom : ∀ {g : MvPolynomial (Fin (2 + 1)) O} {n : ℕ}, g.IsHomogeneous n →
      H (dehom g) = μ ^ n * algebraMap Pol Loc g := by
    intro g n hg
    rw [← RingHom.comp_apply, hHD, MvPolynomial.coe_eval₂Hom,
      eval₂_mul_of_isHomogeneous hg]
    congr 1
    rw [← MvPolynomial.coe_eval₂Hom]
    congr 1
    exact MvPolynomial.ringHom_ext (fun o ↦ by simp) (fun i ↦ by simp)
  -- `f ∣ dehom g`
  rw [eval_eq_dehom, map_eq_zero_iff _ (IsFractionRing.injective _ _),
    AdjoinRoot.mk_eq_zero, ← dehom_F] at h0
  obtain ⟨S, hS⟩ := h0
  obtain ⟨⟨s', ⟨_, m, rfl⟩⟩, hs'⟩ := IsLocalization.surj (Submonoid.powers w) (H S)
  simp only at hs'
  have hF3 := hhom (TateModel.isHomogeneous_F π b₄ b₆)
  have key : algebraMap Pol Loc (g * w ^ (3 + m)) =
      algebraMap Pol Loc (TateModel.F π b₄ b₆ * s' * w ^ n) := by
    have h1 := congrArg H hS
    rw [map_mul, hhom hg, hF3] at h1
    have hwμ : ∀ k : ℕ, algebraMap Pol Loc w ^ k * μ ^ k = 1 := fun k ↦ by
      rw [← mul_pow, hμ, one_pow]
    simp only [map_mul, map_pow]
    calc algebraMap Pol Loc g * algebraMap Pol Loc w ^ (3 + m)
        = (μ ^ n * algebraMap Pol Loc g) * algebraMap Pol Loc w ^ (n + 3 + m) := by
          linear_combination (-(algebraMap Pol Loc g *
            algebraMap Pol Loc w ^ (3 + m))) * hwμ n
      _ = (μ ^ 3 * algebraMap Pol Loc (TateModel.F π b₄ b₆) * H S) *
          algebraMap Pol Loc w ^ (n + 3 + m) := by rw [h1]
      _ = algebraMap Pol Loc (TateModel.F π b₄ b₆) * (H S * algebraMap Pol Loc w ^ m) *
          algebraMap Pol Loc w ^ n := by
          linear_combination (algebraMap Pol Loc
            (TateModel.F π b₄ b₆) * H S * algebraMap Pol Loc w ^ (m + n))
            * hwμ 3
      _ = _ := by rw [← map_pow, hs']
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers w) Loc).1 key
  simp only at hk
  have hdvd : w ^ (k + (3 + m)) ∣ TateModel.F π b₄ b₆ * (s' * w ^ (k + n)) := by
    refine ⟨g, ?_⟩
    rw [pow_add]
    linear_combination -hk
  have hw := (MvPolynomial.X_prime (σ := Fin (2 + 1)) (R := O) (i := 2)).pow_dvd_of_dvd_mul_left
    _ (X_two_not_dvd_F π b₄ b₆ hπ) hdvd
  obtain ⟨T, hT⟩ := hw
  refine ⟨T, ?_⟩
  have hw0 : w ^ (k + (3 + m)) ≠ 0 := pow_ne_zero _ (MvPolynomial.X_ne_zero _)
  apply mul_left_cancel₀ hw0
  linear_combination hk + TateModel.F π b₄ b₆ * hT

omit [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma aL_ne_zero : aL π b₄ b₆ ≠ 0 :=
  (map_ne_zero_iff _ (algebraMap_injective π b₄ b₆)).2 Polynomial.X_ne_zero

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma bL_ne_zero (hπ : π ≠ 0) : bL π b₄ b₆ ≠ 0 := by
  intro h
  have h1 := bL_sq π b₄ b₆
  rw [h, zero_pow two_ne_zero, mul_zero, neg_zero, zero_add, eq_comm,
    map_eq_zero_iff _ (algebraMap_injective π b₄ b₆)] at h1
  have h3 := congrArg (Polynomial.coeff · 3) h1
  simp only [cpoly, map_mul, coeff_add, coeff_C_mul, coeff_X_pow, ↓reduceIte, mul_one,
    coeff_mul_X, coeff_mul_C, coeff_C_succ, zero_mul, add_zero, coeff_zero] at h3
  exact hπ h3

lemma coords_ne_zero (hπ : π ≠ 0) (i : Fin (2 + 1)) : coords π b₄ b₆ i ≠ 0 := by
  fin_cases i
  · exact aL_ne_zero π b₄ b₆
  · exact bL_ne_zero π b₄ b₆ hπ
  · exact one_ne_zero

/-- The evaluation at the affine coordinates of the chart `x_i ≠ 0`. -/
def ev (i : Fin (2 + 1)) : MvPolynomial (Fin (2 + 1)) O →+* L :=
  MvPolynomial.eval₂Hom (algebraMap O L) fun j ↦ coords π b₄ b₆ j / coords π b₄ b₆ i

lemma eval_homogeneous {g : MvPolynomial (Fin (2 + 1)) O} {n : ℕ} (hg : g.IsHomogeneous n)
    (hπ : π ≠ 0) (i : Fin (2 + 1)) :
    MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) g =
      coords π b₄ b₆ i ^ n * ev π b₄ b₆ i g := by
  rw [ev, MvPolynomial.coe_eval₂Hom, ← eval₂_mul_of_isHomogeneous hg]
  congr 1
  funext j
  rw [mul_div_cancel₀ _ (coords_ne_zero π b₄ b₆ hπ i)]

lemma ev_F (hπ : π ≠ 0) (i : Fin (2 + 1)) : ev π b₄ b₆ i (TateModel.F π b₄ b₆) = 0 := by
  have h := eval_homogeneous π b₄ b₆ (TateModel.isHomogeneous_F π b₄ b₆) hπ i
  rw [eval_F] at h
  exact (mul_eq_zero.1 h.symm).resolve_left (pow_ne_zero _ (coords_ne_zero π b₄ b₆ hπ i))

/-- **The kernel of a chart.** A ring map `φ` with `φ (x_i) = 1` and `φ F = 0` kills the kernel of
the evaluation at the affine coordinates of the chart `x_i ≠ 0`. -/
theorem map_eq_zero_of_ev_eq_zero (hπ : π ≠ 0) (i : Fin (2 + 1)) {T : Type*} [CommRing T]
    (φ : MvPolynomial (Fin (2 + 1)) O →+* T) (hφi : φ (MvPolynomial.X i) = 1)
    (hφF : φ (TateModel.F π b₄ b₆) = 0) {P : MvPolynomial (Fin (2 + 1)) O}
    (hP : ev π b₄ b₆ i P = 0) : φ P = 0 := by
  classical
  set N := P.totalDegree
  set g := ∑ d ∈ Finset.range (N + 1),
    MvPolynomial.X i ^ (N - d) * MvPolynomial.homogeneousComponent d P
  have hg : g.IsHomogeneous N := by
    refine MvPolynomial.IsHomogeneous.sum _ _ _ fun d hd ↦ ?_
    have hd' : d ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hd)
    have := (MvPolynomial.isHomogeneous_X_pow (R := O) i (N - d)).mul
      (MvPolynomial.homogeneousComponent_isHomogeneous d P)
    rwa [Nat.sub_add_cancel hd'] at this
  have hsum : ∑ d ∈ Finset.range (N + 1), MvPolynomial.homogeneousComponent d P = P :=
    MvPolynomial.sum_homogeneousComponent P
  have hevg : ev π b₄ b₆ i g = ev π b₄ b₆ i P := by
    simp only [g, map_sum, map_mul, map_pow]
    have : ∀ d ∈ Finset.range (N + 1), ev π b₄ b₆ i (MvPolynomial.X i) ^ (N - d) *
        ev π b₄ b₆ i (MvPolynomial.homogeneousComponent d P) =
        ev π b₄ b₆ i (MvPolynomial.homogeneousComponent d P) := by
      intro d _
      rw [ev, MvPolynomial.eval₂Hom_X', div_self (coords_ne_zero π b₄ b₆ hπ i), one_pow,
        one_mul]
    rw [Finset.sum_congr rfl this, ← map_sum, hsum]
  have hg0 : MvPolynomial.eval₂ (algebraMap O L) (coords π b₄ b₆) g = 0 := by
    rw [eval_homogeneous π b₄ b₆ hg hπ i, hevg, hP, mul_zero]
  obtain ⟨S, hS⟩ := F_dvd_of_eval_eq_zero π b₄ b₆ hπ hg hg0
  have hφg : φ g = φ P := by
    rw [← hsum]
    simp only [g, map_sum, map_mul, map_pow, hφi, one_pow, one_mul]
  rw [← hφg, hS, map_mul, hφF, zero_mul]

/-- The image of `O` in the function field. -/
abbrev baseRing : Subring L := (algebraMap O L).range

/-- The standard affine chart `O[x_j / x_i]` of the Tate model, as a subring of `L`. -/
abbrev chart (i : Fin (2 + 1)) : Subring L :=
  SemistableReduction.projChart (baseRing π b₄ b₆) (coords π b₄ b₆) i

lemma ev_mem_chart (i : Fin (2 + 1)) (P : MvPolynomial (Fin (2 + 1)) O) :
    ev π b₄ b₆ i P ∈ chart π b₄ b₆ i :=
  SemistableReduction.ProjScheme.eval₂_mem_projChart (coords π b₄ b₆) _ rfl i P

lemma exists_ev_eq {i : Fin (2 + 1)} {x : L} (hx : x ∈ chart π b₄ b₆ i) :
    ∃ P, ev π b₄ b₆ i P = x := by
  have : chart π b₄ b₆ i ≤ (ev π b₄ b₆ i).range :=
    SemistableReduction.projChart_le (by rintro _ ⟨o, rfl⟩; exact ⟨MvPolynomial.C o, by simp [ev]⟩)
      fun j ↦ ⟨MvPolynomial.X j, by simp [ev]⟩
  exact this hx

lemma mem_chart_two_of (y : L) (hy : y ∈ chart π b₄ b₆ 2) (p : O[X]) :
    algebraMap O[X] L p * y ∈ chart π b₄ b₆ 2 := by
  induction p using Polynomial.induction_on generalizing y with
  | C o =>
    rw [← algebraMap_O_apply]
    exact (chart π b₄ b₆ 2).mul_mem (SemistableReduction.base_le_projChart 2 ⟨o, rfl⟩) hy
  | add p q hp hq => rw [map_add, add_mul]; exact add_mem (hp y hy) (hq y hy)
  | monomial n o h =>
    have ha : aL π b₄ b₆ ∈ chart π b₄ b₆ 2 := by
      have := SemistableReduction.div_mem_projChart (R := baseRing π b₄ b₆)
        (f := coords π b₄ b₆) 2 0
      simpa using this
    have := h (aL π b₄ b₆ * y) ((chart π b₄ b₆ 2).mul_mem ha hy)
    rw [pow_succ, ← mul_assoc, map_mul]
    convert this using 1
    ring

/-- The chart `x_2 ≠ 0` is the image of `O[X][Y]/(f)`. -/
lemma chart_two_eq : chart π b₄ b₆ 2 = (algebraMap (TateRing π b₄ b₆) L).range := by
  apply le_antisymm
  · refine SemistableReduction.projChart_le ?_ fun j ↦ ?_
    · rintro _ ⟨o, rfl⟩
      exact ⟨algebraMap O _ o, (IsScalarTower.algebraMap_apply _ _ _ _).symm⟩
    · fin_cases j
      · exact ⟨AdjoinRoot.of _ X, by simp [algebraMap_of]⟩
      · exact ⟨bA π b₄ b₆, by simp⟩
      · exact ⟨1, by simp⟩
  · rintro _ ⟨α, rfl⟩
    obtain ⟨p, q, rfl⟩ := exists_repr π b₄ b₆ α
    rw [map_add, map_mul, algebraMap_of, algebraMap_of]
    have hb : bL π b₄ b₆ ∈ chart π b₄ b₆ 2 := by
      have := SemistableReduction.div_mem_projChart (R := baseRing π b₄ b₆)
        (f := coords π b₄ b₆) 2 1
      simpa using this
    refine add_mem ?_ (mem_chart_two_of π b₄ b₆ _ hb q)
    simpa using mem_chart_two_of π b₄ b₆ 1 (one_mem _) p

lemma intClosedIn_chart_two : IntClosedIn (chart π b₄ b₆ 2) := by
  haveI := isIntegrallyClosed π b₄ b₆
  intro z hz
  rw [chart_two_eq] at hz ⊢
  obtain ⟨p, hp, hpz⟩ := hz
  have hlift : p.map (algebraMap (TateRing π b₄ b₆) L).range.subtype ∈
      Polynomial.lifts (algebraMap (TateRing π b₄ b₆) L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    exact (p.coeff n).2
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift (hp.map _)
  have : IsIntegral (TateRing π b₄ b₆) z := by
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, Polynomial.eval_map]
    exact hpz
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 this
  exact ⟨y, rfl⟩

lemma coords_div (hπ : π ≠ 0) :
    coords π b₄ b₆ 0 / coords π b₄ b₆ 0 = 1 ∧ coords π b₄ b₆ 1 / coords π b₄ b₆ 1 = 1 ∧
      coords π b₄ b₆ 2 / coords π b₄ b₆ 2 = 1 :=
  ⟨div_self (coords_ne_zero π b₄ b₆ hπ 0), div_self (coords_ne_zero π b₄ b₆ hπ 1),
    div_self (coords_ne_zero π b₄ b₆ hπ 2)⟩

lemma mem_chart (i j : Fin (2 + 1)) : coords π b₄ b₆ j / coords π b₄ b₆ i ∈ chart π b₄ b₆ i :=
  SemistableReduction.div_mem_projChart i j

lemma ev_X (i j : Fin (2 + 1)) :
    ev π b₄ b₆ i (MvPolynomial.X j) = coords π b₄ b₆ j / coords π b₄ b₆ i := by
  simp [ev]

lemma ev_C (i : Fin (2 + 1)) (o : O) : ev π b₄ b₆ i (MvPolynomial.C o) = algebraMap O L o := by
  simp [ev]

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- `F = w (v² + u v − b₆ w² − π b₄ u w) − π u³`. -/
lemma F_eq_w : TateModel.F π b₄ b₆ = MvPolynomial.X 2 * (MvPolynomial.X 1 ^ 2 +
    MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C b₆ * MvPolynomial.X 2 ^ 2 -
    MvPolynomial.C (π * b₄) * MvPolynomial.X 0 * MvPolynomial.X 2) -
    MvPolynomial.C π * MvPolynomial.X 0 ^ 3 := by
  simp only [TateModel.F]
  ring

/-- The `x_2 / x_0`-adic radicality for the chart `x_0 ≠ 0`: `R / (x_2/x_0) = k[x_1/x_0]`. -/
lemma radical_chart_zero (hπ : Irreducible π) :
    ∀ x ∈ chart π b₄ b₆ 0, ∀ n : ℕ,
      (∃ r ∈ chart π b₄ b₆ 0, x ^ n = coords π b₄ b₆ 2 / coords π b₄ b₆ 0 * r) →
      ∃ r ∈ chart π b₄ b₆ 0, x = coords π b₄ b₆ 2 / coords π b₄ b₆ 0 * r := by
  classical
  intro x hx n ⟨r, hr, hxr⟩
  obtain ⟨P, rfl⟩ := exists_ev_eq π b₄ b₆ hx
  obtain ⟨Q, rfl⟩ := exists_ev_eq π b₄ b₆ hr
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hπm : IsLocalRing.residue O π = 0 :=
    (IsLocalRing.residue_eq_zero_iff π).2 ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  set θ : MvPolynomial (Fin (2 + 1)) O →+* (IsLocalRing.ResidueField O)[X] :=
    MvPolynomial.eval₂Hom (Polynomial.C.comp (IsLocalRing.residue O)) ![1, X, 0]
  have hθF : θ (TateModel.F π b₄ b₆) = 0 := by
    simp [θ, TateModel.F, hπm]
  have hev : ev π b₄ b₆ 0 (P ^ n - MvPolynomial.X 2 * Q) = 0 := by
    rw [map_sub, map_pow, map_mul, ev_X, hxr, sub_self]
  have h1 := map_eq_zero_of_ev_eq_zero π b₄ b₆ hπ0 0 θ (by simp [θ]) hθF hev
  have hθP : θ P = 0 := by
    rw [map_sub, map_pow, map_mul, sub_eq_zero] at h1
    exact IsReduced.eq_zero _ ⟨n, by rw [h1]; simp [θ]⟩
  -- `P ∈ (x_0 - 1, x_2, π)`
  set I : Ideal (MvPolynomial (Fin (2 + 1)) O) :=
    Ideal.span {MvPolynomial.X 0 - 1, MvPolynomial.X 2, MvPolynomial.C π}
  have hCπ : MvPolynomial.C π ∈ I := Ideal.subset_span (by simp)
  have hX2 : MvPolynomial.X 2 ∈ I := Ideal.subset_span (by simp)
  have hX0 : MvPolynomial.X 0 - 1 ∈ I := Ideal.subset_span (by simp)
  let ψ₀ : IsLocalRing.ResidueField O →+* MvPolynomial (Fin (2 + 1)) O ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp MvPolynomial.C) fun c hc ↦ by
      rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hc
      obtain ⟨c', rfl⟩ := hc
      simp only [RingHom.coe_comp, Function.comp_apply, map_mul]
      rw [Ideal.Quotient.eq_zero_iff_mem.2 hCπ, zero_mul]
  let ψ : (IsLocalRing.ResidueField O)[X] →+* MvPolynomial (Fin (2 + 1)) O ⧸ I :=
    Polynomial.eval₂RingHom ψ₀ (Ideal.Quotient.mk I (MvPolynomial.X 1))
  have hψθ : ψ.comp θ = Ideal.Quotient.mk I := by
    refine MvPolynomial.ringHom_ext (fun o ↦ ?_) (fun i ↦ ?_)
    · simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_C, RingHom.comp_apply]
      change Polynomial.eval₂ ψ₀ _ (Polynomial.C _) = _
      rw [Polynomial.eval₂_C]
      rfl
    · fin_cases i
      · simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X']
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, map_one]
        rw [← map_one (Ideal.Quotient.mk I)]
        exact (Ideal.Quotient.eq.2 hX0).symm
      · simp [θ, ψ]
      · simp only [RingHom.comp_apply, θ, MvPolynomial.eval₂Hom_X']
        simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.2 hX2).symm
  have hPI : P ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hψθ, RingHom.comp_apply, hθP, map_zero]
  -- the image of `I` in the chart is contained in `(x_2/x_0)`
  have hπs : ∃ r ∈ chart π b₄ b₆ 0,
      algebraMap O L π = coords π b₄ b₆ 2 / coords π b₄ b₆ 0 * r := by
    have h := ev_F π b₄ b₆ hπ0 0
    rw [F_eq_w, map_sub, map_mul (ev π b₄ b₆ 0) (MvPolynomial.X 2),
      map_mul (ev π b₄ b₆ 0) (MvPolynomial.C π), map_pow (ev π b₄ b₆ 0) (MvPolynomial.X 0),
      ev_X, ev_X, ev_C, (coords_div π b₄ b₆ hπ0).1, one_pow, mul_one, sub_eq_zero] at h
    exact ⟨_, ev_mem_chart π b₄ b₆ 0 _, h.symm⟩
  refine Submodule.span_induction (p := fun P _ ↦ ∃ r ∈ chart π b₄ b₆ 0,
    ev π b₄ b₆ 0 P = coords π b₄ b₆ 2 / coords π b₄ b₆ 0 * r) ?_ ?_ ?_ ?_ hPI
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨0, zero_mem _, by rw [map_sub, ev_X, (coords_div π b₄ b₆ hπ0).1, map_one,
        sub_self, mul_zero]⟩
    · exact ⟨1, one_mem _, by rw [ev_X, mul_one]⟩
    · rw [ev_C]; exact hπs
  · exact ⟨0, zero_mem _, by rw [map_zero, mul_zero]⟩
  · rintro y z - - ⟨r, hr, hy⟩ ⟨r', hr', hz⟩
    exact ⟨r + r', add_mem hr hr', by rw [map_add, hy, hz, mul_add]⟩
  · rintro a y - ⟨r, hr, hy⟩
    refine ⟨ev π b₄ b₆ 0 a * r, mul_mem (ev_mem_chart π b₄ b₆ 0 a) hr, ?_⟩
    rw [smul_eq_mul, map_mul, hy]
    ring

omit [IsDomain O] [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma coords_two : coords π b₄ b₆ 2 = 1 := rfl

/-- **The chart `x_0 ≠ 0` is integrally closed.** -/
theorem intClosedIn_chart_zero (hπ : Irreducible π) :
    IntClosedIn (chart π b₄ b₆ 0) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have ha : coords π b₄ b₆ 0 ∈ chart π b₄ b₆ 2 := by
    simpa [coords_two] using mem_chart π b₄ b₆ 2 0
  have hc0 := coords_ne_zero π b₄ b₆ hπ0 0
  refine IntClosedIn.of_loc (mem_chart π b₄ b₆ 0 2)
    (div_ne_zero (coords_ne_zero π b₄ b₆ hπ0 2) hc0) (radical_chart_zero π b₄ b₆ hπ)
    (T := loc (chart π b₄ b₆ 2) ha) ?_ ((intClosedIn_chart_two π b₄ b₆).loc ha) ?_
  · refine SemistableReduction.projChart_le
      ((SemistableReduction.base_le_projChart 2).trans (le_loc ha)) fun j ↦ ⟨1, ?_⟩
    rw [pow_one, mul_div_cancel₀ _ hc0]
    simpa [coords_two] using mem_chart π b₄ b₆ 2 j
  · intro z hz
    have hle : chart π b₄ b₆ 2 ≤ loc (chart π b₄ b₆ 0) (mem_chart π b₄ b₆ 0 2) := by
      refine SemistableReduction.projChart_le
        ((SemistableReduction.base_le_projChart 0).trans (le_loc _)) fun j ↦ ⟨1, ?_⟩
      rw [pow_one, coords_two, div_one, mul_comm, ← mul_div_assoc, mul_one]
      exact mem_chart π b₄ b₆ 0 j
    exact loc_le_loc ha _ hle (le_loc _ (mem_chart π b₄ b₆ 0 2))
      (by rw [coords_two, mul_one_div_cancel hc0]) hz

omit [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma two_ne_zero' (hd : Squarefree (dpoly π b₄ b₆)) : (2 : O) ≠ 0 := by
  intro h2
  have h4' : (4 : O) = 0 := by rw [show (4 : O) = 2 * 2 by norm_num, h2, mul_zero]
  have h4 : (4 : O[X]) = 0 := by rw [← map_ofNat Polynomial.C 4, h4', map_zero]
  have hdX : dpoly π b₄ b₆ = X * X := by rw [dpoly, h4, zero_mul, add_zero, sq]
  exact Polynomial.not_isUnit_X (hd X ⟨1, by rw [hdX, mul_one]⟩)

omit [IsDiscreteValuationRing O] [Fact (Squarefree (dpoly π b₄ b₆))] in
/-- `1 - b₆ X²` is squarefree if `2 ≠ 0`. -/
lemma squarefree_one_sub (h2 : (2 : O) ≠ 0) :
    Squarefree (1 - Polynomial.C b₆ * X ^ 2 : O[X]) := by
  intro q ⟨r, hr⟩
  -- `q` divides `2 e - X e' = 2`
  have hq1 : q ∣ (1 - Polynomial.C b₆ * X ^ 2 : O[X]) := ⟨q * r, by rw [hr]; ring⟩
  have hq2 : q ∣ Polynomial.derivative (1 - Polynomial.C b₆ * X ^ 2 : O[X]) := by
    rw [hr, Polynomial.derivative_mul, Polynomial.derivative_mul]
    exact ⟨Polynomial.derivative q * r + Polynomial.derivative q * r +
      q * Polynomial.derivative r, by ring⟩
  have hq : q ∣ (2 : O[X]) := by
    have : (2 : O[X]) = 2 * (1 - Polynomial.C b₆ * X ^ 2) -
        X * Polynomial.derivative (1 - Polynomial.C b₆ * X ^ 2) := by
      simp only [map_sub, Polynomial.derivative_one, Polynomial.derivative_mul,
        Polynomial.derivative_C, zero_mul, zero_add, Polynomial.derivative_X_pow]
      simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, zero_sub]
      rw [← map_ofNat Polynomial.C 2]
      ring
    rw [this]
    exact dvd_sub (dvd_mul_of_dvd_right hq1 _) (dvd_mul_of_dvd_right hq2 _)
  have hdeg : q.natDegree = 0 := by
    have h2' : (2 : O[X]) ≠ 0 := by
      rw [← map_ofNat Polynomial.C 2]; exact Polynomial.C_ne_zero.2 h2
    have := Polynomial.natDegree_le_of_dvd hq h2'
    rw [← map_ofNat Polynomial.C 2, Polynomial.natDegree_C] at this
    omega
  rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg] at hr ⊢
  have h0 := congrArg (Polynomial.coeff · 0) hr
  simp only [coeff_sub, coeff_one_zero, mul_coeff_zero, coeff_C_zero, coeff_X_pow,
    OfNat.zero_ne_ofNat, ↓reduceIte, mul_zero, sub_zero] at h0
  exact Polynomial.isUnit_C.2 (IsUnit.of_mul_eq_one (q.coeff 0 * r.coeff 0)
    (by rw [h0]; ring))

omit [Fact (Squarefree (dpoly π b₄ b₆))] in
lemma squarefree_g (h2 : (2 : O) ≠ 0) :
    Squarefree (X - Polynomial.C b₆ * X ^ 3 : O[X]) := by
  have : (X - Polynomial.C b₆ * X ^ 3 : O[X]) = X * (1 - Polynomial.C b₆ * X ^ 2) := by ring
  rw [this, squarefree_mul_iff]
  refine ⟨IsCoprime.isRelPrime ⟨Polynomial.C b₆ * X, 1, by ring⟩,
    Polynomial.irreducible_X.squarefree, squarefree_one_sub b₆ h2⟩

/-- The `x_0 / x_1`-adic radicality for the chart `x_1 ≠ 0`:
`R / (x_0/x_1) = O[t]/(t - b₆ t³)` is reduced. -/
lemma radical_chart_one (hπ0 : π ≠ 0) :
    ∀ x ∈ chart π b₄ b₆ 1, ∀ n : ℕ,
      (∃ r ∈ chart π b₄ b₆ 1, x ^ n = coords π b₄ b₆ 0 / coords π b₄ b₆ 1 * r) →
      ∃ r ∈ chart π b₄ b₆ 1, x = coords π b₄ b₆ 0 / coords π b₄ b₆ 1 * r := by
  classical
  intro x hx n ⟨r, hr, hxr⟩
  obtain ⟨P, rfl⟩ := exists_ev_eq π b₄ b₆ hx
  obtain ⟨Q, rfl⟩ := exists_ev_eq π b₄ b₆ hr
  set g₀ : O[X] := X - Polynomial.C b₆ * X ^ 3
  have hg₀ : Squarefree g₀ := squarefree_g b₆ (two_ne_zero' π b₄ b₆ Fact.out)
  set θ₀ : MvPolynomial (Fin (2 + 1)) O →+* O[X] :=
    MvPolynomial.eval₂Hom Polynomial.C ![0, 1, X]
  set θ := (Ideal.Quotient.mk (Ideal.span {g₀})).comp θ₀
  have hθF : θ (TateModel.F π b₄ b₆) = 0 := by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨1, by simp [θ₀, TateModel.F, g₀]⟩
  have hev : ev π b₄ b₆ 1 (P ^ n - MvPolynomial.X 0 * Q) = 0 := by
    rw [map_sub, map_pow, map_mul, ev_X, hxr, sub_self]
  have h1 := map_eq_zero_of_ev_eq_zero π b₄ b₆ hπ0 1 θ (by simp [θ, θ₀]) hθF hev
  have hθP : θ P = 0 := by
    rw [map_sub, map_pow, map_mul, sub_eq_zero] at h1
    have h0 : θ (MvPolynomial.X 0) = 0 := by simp [θ, θ₀]
    rw [h0, zero_mul, RingHom.comp_apply, ← map_pow, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton] at h1
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact hg₀.isRadical n _ h1
  -- `P ∈ (x_0, x_1 - 1, F)`
  set I : Ideal (MvPolynomial (Fin (2 + 1)) O) :=
    Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1 - 1, TateModel.F π b₄ b₆}
  have hX0 : MvPolynomial.X 0 ∈ I := Ideal.subset_span (by simp)
  have hX1 : MvPolynomial.X 1 - 1 ∈ I := Ideal.subset_span (by simp)
  have hF : TateModel.F π b₄ b₆ ∈ I := Ideal.subset_span (by simp)
  have hg₀I : MvPolynomial.X 2 - MvPolynomial.C b₆ * MvPolynomial.X 2 ^ 3 ∈ I := by
    have : MvPolynomial.X 2 - MvPolynomial.C b₆ * MvPolynomial.X 2 ^ 3 =
        TateModel.F π b₄ b₆ - (MvPolynomial.X 1 - 1) * ((MvPolynomial.X 1 + 1) * MvPolynomial.X 2)
        - MvPolynomial.X 0 * (MvPolynomial.X 1 * MvPolynomial.X 2 -
          MvPolynomial.C π * MvPolynomial.X 0 ^ 2 -
          MvPolynomial.C (π * b₄) * MvPolynomial.X 2 ^ 2) := by
      simp only [TateModel.F]
      ring
    rw [this]
    exact sub_mem (sub_mem hF (I.mul_mem_right _ hX1)) (I.mul_mem_right _ hX0)
  let ψ₀ : O[X] →+* MvPolynomial (Fin (2 + 1)) O ⧸ I :=
    Polynomial.eval₂RingHom ((Ideal.Quotient.mk I).comp MvPolynomial.C)
      (Ideal.Quotient.mk I (MvPolynomial.X 2))
  let ψ : O[X] ⧸ Ideal.span {g₀} →+* MvPolynomial (Fin (2 + 1)) O ⧸ I :=
    Ideal.Quotient.lift _ ψ₀ fun y hy ↦ by
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy
      have : ψ₀ g₀ = 0 := by
        simp only [ψ₀, g₀, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_sub, Polynomial.eval₂_X,
          Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, RingHom.comp_apply]
        rw [← map_pow, ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
        exact hg₀I
      rw [map_mul, this, mul_zero]
  have hψθ : ψ.comp θ = Ideal.Quotient.mk I := by
    refine MvPolynomial.ringHom_ext (fun o ↦ ?_) (fun i ↦ ?_)
    · simp [θ, θ₀, ψ, ψ₀]
    · fin_cases i
      · simp only [RingHom.comp_apply, θ, θ₀, MvPolynomial.eval₂Hom_X']
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, map_zero]
        exact (Ideal.Quotient.eq_zero_iff_mem.2 hX0).symm
      · simp only [RingHom.comp_apply, θ, θ₀, MvPolynomial.eval₂Hom_X']
        simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, map_one]
        rw [← map_one (Ideal.Quotient.mk I)]
        exact (Ideal.Quotient.eq.2 hX1).symm
      · simp [θ, θ₀, ψ, ψ₀]
  have hPI : P ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← hψθ, RingHom.comp_apply, hθP, map_zero]
  refine Submodule.span_induction (p := fun P _ ↦ ∃ r ∈ chart π b₄ b₆ 1,
    ev π b₄ b₆ 1 P = coords π b₄ b₆ 0 / coords π b₄ b₆ 1 * r) ?_ ?_ ?_ ?_ hPI
  · intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨1, one_mem _, by rw [ev_X, mul_one]⟩
    · exact ⟨0, zero_mem _, by rw [map_sub, ev_X, (coords_div π b₄ b₆ hπ0).2.1, map_one,
        sub_self, mul_zero]⟩
    · exact ⟨0, zero_mem _, by rw [ev_F π b₄ b₆ hπ0, mul_zero]⟩
  · exact ⟨0, zero_mem _, by rw [map_zero, mul_zero]⟩
  · rintro y z - - ⟨r, hr, hy⟩ ⟨r', hr', hz⟩
    exact ⟨r + r', add_mem hr hr', by rw [map_add, hy, hz, mul_add]⟩
  · rintro a y - ⟨r, hr, hy⟩
    refine ⟨ev π b₄ b₆ 1 a * r, mul_mem (ev_mem_chart π b₄ b₆ 1 a) hr, ?_⟩
    rw [smul_eq_mul, map_mul, hy]
    ring

/-- **The chart `x_1 ≠ 0` is integrally closed.** -/
theorem intClosedIn_chart_one (hπ : Irreducible π) :
    IntClosedIn (chart π b₄ b₆ 1) := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hc0 := coords_ne_zero π b₄ b₆ hπ0 0
  have hc1 := coords_ne_zero π b₄ b₆ hπ0 1
  have hba : coords π b₄ b₆ 1 / coords π b₄ b₆ 0 ∈ chart π b₄ b₆ 0 := mem_chart π b₄ b₆ 0 1
  refine IntClosedIn.of_loc (mem_chart π b₄ b₆ 1 0) (div_ne_zero hc0 hc1)
    (radical_chart_one π b₄ b₆ hπ0)
    (T := loc (chart π b₄ b₆ 0) hba) ?_ ((intClosedIn_chart_zero π b₄ b₆ hπ).loc hba) ?_
  · refine SemistableReduction.projChart_le
      ((SemistableReduction.base_le_projChart 0).trans (le_loc hba)) fun j ↦ ⟨1, ?_⟩
    rw [pow_one, div_mul_div_comm, mul_comm (coords π b₄ b₆ 1), ← div_mul_div_comm,
      div_self hc1, mul_one]
    exact mem_chart π b₄ b₆ 0 j
  · intro z hz
    have hle : chart π b₄ b₆ 0 ≤ loc (chart π b₄ b₆ 1) (mem_chart π b₄ b₆ 1 0) := by
      refine SemistableReduction.projChart_le
        ((SemistableReduction.base_le_projChart 1).trans (le_loc _)) fun j ↦ ⟨1, ?_⟩
      rw [pow_one, div_mul_div_comm, mul_comm (coords π b₄ b₆ 0), ← div_mul_div_comm,
        div_self hc0, mul_one]
      exact mem_chart π b₄ b₆ 1 j
    exact loc_le_loc hba _ hle (le_loc _ (mem_chart π b₄ b₆ 1 0))
      (by rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero hc0 hc1)]) hz

end

end TemperedFundamentalGroups.TateNormal
