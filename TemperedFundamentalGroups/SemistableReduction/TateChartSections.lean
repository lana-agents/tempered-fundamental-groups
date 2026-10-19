/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.TateProjection
import TemperedFundamentalGroups.SemistableReduction.TateTwoChart
import TemperedFundamentalGroups.SemistableReduction.LinearProjectionKer

/-!
# The algebraic charts of the Tate model are its rings of sections (Blueprint §12.8, M2.3 (g))

Let `V_k = ι⁻¹ D₊(ℓ_k)` be the charts of the projection `TateProjection.toP1` from `[0 : t : 1]`
(`ℓ₀ = v − t w`, `ℓ₁ = u`) of the Tate model `𝒯 = TateModel.model π b₄ b₆`. Then

* `TateChartSections.f0 : T0 → Γ(V₀)` (`h ↦ u/ℓ₀`, `z ↦ w/ℓ₀`, over `O[X] = Γ(D₊(y₀))` via
  `baseRes`), `TateChartSections.f1 : T1 → Γ(V₁)` (`h' ↦ ℓ₀/u`, `w ↦ w/u`);
* if `T0` (resp. `T1`) is reduced, `f0` (resp. `f1`) is an isomorphism
  (**`TateChartSections.equiv0`**, **`TateChartSections.equiv1`**).

Proof: `Γ(V_k) = (O[u,v,w]_{(ℓ_k)})₀ ⧸ √(F/ℓ_k³)` (`LinearProjection.ker_secRes`), and evaluation
at the coordinates `(h, 1 + t z, z)` (resp. `(1, h' + t w, w)`) of `T_k` kills `F/ℓ_k³`
(`F/ℓ₀³ = ε G₀`), giving the inverse.
-/

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization

namespace TemperedFundamentalGroups

namespace TateChartSections

open SemistableReduction SemistableReduction.LinearProjection SemistableReduction.TateTwoChart
  TateProjection

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

variable {O : Type u} [CommRing O] (π b₄ t κ : O) {b₆ : O} (hκ : κ * (t ^ 2 - b₆) = 1)

local notation "𝒜" m => MvPolynomial.homogeneousSubmodule (Fin (m + 1)) O

instance isReduced_model (π b₄ b₆ : O) :
    IsReduced (TateModel.modelIdeal π b₄ b₆).subscheme :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal _

include hκ in
lemma isUnit_ε : IsUnit (t ^ 2 - b₆) :=
  IsUnit.of_mul_eq_one κ (by rw [mul_comm]; exact hκ)

lemma κ_eq : κ = ↑(isUnit_ε t κ hκ).unit⁻¹ := by
  have h := (isUnit_ε t κ hκ).val_inv_mul
  linear_combination (↑(isUnit_ε t κ hκ).unit⁻¹ : O) * hκ - κ * h

/-- `F / ℓ_k³` restricts to zero on the chart `V_k`. -/
lemma secRes_F (b₆ : O) (k : Fin (1 + 1)) :
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) k
      (Away.isLocalizationElem ((linHom (lin t) (lin_mem t)).map_mem (X_mem' k))
        (F_mem3 π b₄ b₆)) = 0 := by
  have h := ker_secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) k (F_mem3 π b₄ b₆) three_pos
    (TateModel.range_ι π b₄ b₆)
  exact RingHom.mem_ker.1 (h ▸ Ideal.le_radical (Ideal.mem_span_singleton_self _))

/-! ### The chart `ℓ₀ ≠ 0` -/

/-- The coordinates `(h, 1 + t z, z)` of `[u : v : w] / ℓ₀` in `T0`. -/
def c0 : Fin (2 + 1) → T0 π b₄ t κ :=
  ![h0 π b₄ t κ, 1 + algebraMap O _ t * z0 π b₄ t κ, z0 π b₄ t κ]

lemma aeval_c0_lin : aeval (c0 π b₄ t κ) (linHom (lin t) (lin_mem t) (X 0)) = 1 := by
  rw [linHom_X, lin_zero]
  simp [c0]

/-- Evaluation `(O[u,v,w]_{(ℓ₀)})₀ → T0` at `(h, 1 + t z, z)`. -/
def g0 : Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 0)) →+* T0 π b₄ t κ :=
  awayEval (c0 π b₄ t κ) _ (aeval_c0_lin π b₄ t κ)

include hκ in
lemma g0_F : g0 π b₄ t κ (Away.isLocalizationElem ((linHom (lin t) (lin_mem t)).map_mem
    (X_mem' 0)) (F_mem3 π b₄ b₆)) = 0 := by
  rw [g0, awayEval_mk, pow_one]
  have h := eq0 π b₄ t κ
  have hk : algebraMap O (T0 π b₄ t κ) κ *
      (algebraMap O _ t ^ 2 - algebraMap O _ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  simp only [TateModel.F, c0, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h ⊢
  simp only [map_ofNat] at h
  linear_combination (algebraMap O (T0 π b₄ t κ) t ^ 2 - algebraMap O _ b₆) * h -
    ((2 * algebraMap O _ t + (algebraMap O _ t - algebraMap O _ π * algebraMap O _ b₄) *
      h0 π b₄ t κ) * z0 π b₄ t κ ^ 2 + (1 + h0 π b₄ t κ) * z0 π b₄ t κ -
      algebraMap O _ π * h0 π b₄ t κ ^ 3) * hk

lemma polyToChart_C (k : Fin (1 + 1)) (o : O) :
    ProjectiveLine.polyToChart (A := O) k (Polynomial.C o) = cst k o := by
  simp only [ProjectiveLine.polyToChart, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
    RingHom.coe_comp, Function.comp_apply]
  rfl

lemma polyToChart_X0 : ProjectiveLine.polyToChart (A := O) 0 Polynomial.X = H₀ := by
  simp only [ProjectiveLine.polyToChart, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

lemma polyToChart_X1 : ProjectiveLine.polyToChart (A := O) 1 Polynomial.X = H₁ := by
  simp only [ProjectiveLine.polyToChart, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rfl

lemma cst_mul (k : Fin (1 + 1)) (a b : O) : cst k (a * b) = cst k a * cst k b := by
  simp only [cst, map_mul]

lemma map_G0 : (G0 π b₄ t κ).map (ProjectiveLine.polyToChart (A := O) 0) =
    cubic₀ π b₄ (isUnit_ε t κ hκ) := by
  conv_lhs => rw [κ_eq t κ hκ]
  simp only [G0, cubic₀, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, map_add, map_mul,
    map_sub, map_one, map_pow, polyToChart_C, polyToChart_X0, cst_mul]
  ring

variable (b₆) in
/-- `O[X] = Γ(D₊(y₀)) → Γ(V₀)`. -/
def i0 : Polynomial O →+* Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0, ⊤) :=
  (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0).comp
    (ProjectiveLine.polyToChart (A := O) 0)

include hκ in
lemma eval_G0 : (G0 π b₄ t κ).eval₂ (i0 π b₄ t b₆)
    (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (coordFrac (lin t) (lin_mem t) 0 2)) =
      0 := by
  rw [i0, ← Polynomial.eval₂_map, map_G0 π b₄ t κ hκ, baseRes, ← Polynomial.hom_eval₂,
    eval_cubic₀, map_mul, secRes_F, mul_zero]

/-- **`T0 → Γ(V₀)`**: `h ↦ u/ℓ₀`, `z ↦ w/ℓ₀`. -/
def f0 : T0 π b₄ t κ →+* Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0, ⊤) :=
  AdjoinRoot.lift (i0 π b₄ t b₆) _ (eval_G0 π b₄ t κ hκ)

lemma f0_of (q : Polynomial O) : f0 π b₄ t κ hκ (AdjoinRoot.of _ q) =
    baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (ProjectiveLine.polyToChart (A := O) 0 q) :=
  AdjoinRoot.lift_of _

lemma f0_z0 : f0 π b₄ t κ hκ (z0 π b₄ t κ) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (coordFrac (lin t) (lin_mem t) 0 2) :=
  AdjoinRoot.lift_root _

lemma f0_algebraMap (o : O) : f0 π b₄ t κ hκ (algebraMap O _ o) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0
      (fromZeroRingHom (𝒜 2) _ (algebraMap O _ o)) := by
  rw [← of_C, f0_of, polyToChart_C, baseRes, RingHom.comp_apply, awayMap_fromZero]

lemma f0_h0 : f0 π b₄ t κ hκ (h0 π b₄ t κ) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (coordFrac (lin t) (lin_mem t) 0 0) := by
  rw [h0, f0_of, polyToChart_X0, baseRes, RingHom.comp_apply, ← coordFrac_zero_zero]

include hκ in
lemma ker_le0 [IsReduced (T0 π b₄ t κ)] :
    RingHom.ker (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0) ≤
      RingHom.ker (g0 π b₄ t κ) := by
  rw [ker_secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (F_mem3 π b₄ b₆) three_pos
    (TateModel.range_ι π b₄ b₆)]
  rintro a ⟨n, hn⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hn
  have h : IsNilpotent (g0 π b₄ t κ a) :=
    ⟨n, by rw [← map_pow, hc, map_mul, g0_F π b₄ t κ hκ, zero_mul]⟩
  exact h.eq_zero

/-- The inverse `Γ(V₀) → T0` (for `T0` reduced), induced by evaluation at `(h, 1 + t z, z)`. -/
def gbar0 [IsReduced (T0 π b₄ t κ)] :
    Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0, ⊤) →+* T0 π b₄ t κ :=
  (Ideal.Quotient.lift _ (g0 π b₄ t κ) fun _ ha ↦ RingHom.mem_ker.1 (ker_le0 π b₄ t κ hκ ha)).comp
    (RingHom.quotientKerEquivOfSurjective
      (secRes_surjective (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0)).symm.toRingHom

lemma gbar0_secRes [IsReduced (T0 π b₄ t κ)] (a : Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 0))) :
    gbar0 π b₄ t κ hκ (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a) = g0 π b₄ t κ a := by
  have h : (RingHom.quotientKerEquivOfSurjective
      (secRes_surjective (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0)).symm
        (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 a) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [gbar0, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h, Ideal.Quotient.lift_mk]

lemma gbar0_f0 [IsReduced (T0 π b₄ t κ)] :
    (gbar0 π b₄ t κ hκ).comp (f0 π b₄ t κ hκ) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro o
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [of_C, f0_algebraMap, gbar0_secRes, g0, awayEval_fromZero]
    · change gbar0 π b₄ t κ hκ (f0 π b₄ t κ hκ (h0 π b₄ t κ)) = h0 π b₄ t κ
      rw [f0_h0, gbar0_secRes, g0, awayEval_coordFrac]
      rfl
  · change gbar0 π b₄ t κ hκ (f0 π b₄ t κ hκ (z0 π b₄ t κ)) = z0 π b₄ t κ
    rw [f0_z0, gbar0_secRes, g0, awayEval_coordFrac]
    rfl

lemma f0_g0 : (f0 π b₄ t κ hκ).comp (g0 π b₄ t κ) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 := by
  refine awayHom_ext (lin t) (lin_mem t) 0 (fun o ↦ ?_) (fun i ↦ ?_)
  · rw [RingHom.comp_apply, g0, awayEval_fromZero, f0_algebraMap]
  · rw [RingHom.comp_apply, g0, awayEval_coordFrac]
    fin_cases i
    · exact f0_h0 π b₄ t κ hκ
    · change f0 π b₄ t κ hκ (1 + algebraMap O _ t * z0 π b₄ t κ) =
        secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 (coordFrac (lin t) (lin_mem t) 0 1)
      rw [map_add, map_one, map_mul, f0_algebraMap, f0_z0, coordFrac_zero_one, awayMap_fromZero,
        map_add, map_one, map_mul]
    · exact f0_z0 π b₄ t κ hκ

/-- **The chart `T0` is the ring of sections of the Tate model over `V₀ = ι⁻¹ D₊(v − t w)`**
(for `T0` reduced). -/
def equiv0 [IsReduced (T0 π b₄ t κ)] :
    T0 π b₄ t κ ≃+* Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0, ⊤) :=
  RingEquiv.ofRingHom (f0 π b₄ t κ hκ) (gbar0 π b₄ t κ hκ)
    (RingHom.ext fun x ↦ by
      obtain ⟨a, rfl⟩ := secRes_surjective (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 0 x
      rw [RingHom.comp_apply, gbar0_secRes, ← RingHom.comp_apply, f0_g0, RingHom.id_apply])
    (gbar0_f0 π b₄ t κ hκ)

lemma equiv0_apply [IsReduced (T0 π b₄ t κ)] (x : T0 π b₄ t κ) :
    equiv0 π b₄ t κ hκ x = f0 π b₄ t κ hκ x := rfl

/-! ### The chart `u ≠ 0` -/

/-- The coordinates `(1, h' + t w, w)` of `[u : v : w] / u` in `T1`. -/
def c1 : Fin (2 + 1) → T1 π b₄ t κ :=
  ![1, h1 π b₄ t κ + algebraMap O _ t * w1 π b₄ t κ, w1 π b₄ t κ]

lemma aeval_c1_lin : aeval (c1 π b₄ t κ) (linHom (lin t) (lin_mem t) (X 1)) = 1 := by
  rw [linHom_X, lin_one]
  simp [c1]

/-- Evaluation `(O[u,v,w]_{(u)})₀ → T1` at `(1, h' + t w, w)`. -/
def g1 : Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 1)) →+* T1 π b₄ t κ :=
  awayEval (c1 π b₄ t κ) _ (aeval_c1_lin π b₄ t κ)

include hκ in
lemma g1_F : g1 π b₄ t κ (Away.isLocalizationElem ((linHom (lin t) (lin_mem t)).map_mem
    (X_mem' 1)) (F_mem3 π b₄ b₆)) = 0 := by
  rw [g1, awayEval_mk, pow_one]
  have h := eqn1 π b₄ t κ hκ
  simp only [TateModel.F, c1, map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h ⊢
  linear_combination h

lemma g1_mapH₁ : g1 π b₄ t κ (Away.map (linHom (lin t) (lin_mem t)) (X 1) (H₁ (O := O))) =
    h1 π b₄ t κ := by
  have h := congrArg (g1 π b₄ t κ) (coordFrac_one_one (O := O) t)
  rw [map_add, map_mul, awayMap_fromZero, g1, awayEval_coordFrac, awayEval_coordFrac,
    awayEval_fromZero] at h
  change h1 π b₄ t κ + algebraMap O _ t * w1 π b₄ t κ = _ + algebraMap O _ t * w1 π b₄ t κ at h
  rw [g1]
  linear_combination -h

lemma map_G1 : (G1 π b₄ t κ).map (ProjectiveLine.polyToChart (A := O) 1) =
    cubic₁ π b₄ (isUnit_ε t κ hκ) := by
  conv_lhs => rw [κ_eq t κ hκ]
  simp only [G1, cubic₁, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X, map_add, map_mul,
    map_sub, map_pow, polyToChart_C, polyToChart_X1, cst_mul]
  ring

variable (b₆) in
/-- `O[X] = Γ(D₊(y₁)) → Γ(V₁)`. -/
def i1 : Polynomial O →+* Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1, ⊤) :=
  (baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1).comp
    (ProjectiveLine.polyToChart (A := O) 1)

include hκ in
lemma eval_G1 : (G1 π b₄ t κ).eval₂ (i1 π b₄ t b₆)
    (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (coordFrac (lin t) (lin_mem t) 1 2)) =
      0 := by
  rw [i1, ← Polynomial.eval₂_map, map_G1 π b₄ t κ hκ, baseRes, ← Polynomial.hom_eval₂,
    eval_cubic₁, map_mul, secRes_F, mul_zero]

/-- **`T1 → Γ(V₁)`**: `h' ↦ ℓ₀/u`, `w ↦ w/u`. -/
def f1 : T1 π b₄ t κ →+* Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1, ⊤) :=
  AdjoinRoot.lift (i1 π b₄ t b₆) _ (eval_G1 π b₄ t κ hκ)

lemma f1_of (q : Polynomial O) : f1 π b₄ t κ hκ (AdjoinRoot.of _ q) =
    baseRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (ProjectiveLine.polyToChart (A := O) 1 q) :=
  AdjoinRoot.lift_of _

lemma f1_w1 : f1 π b₄ t κ hκ (w1 π b₄ t κ) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (coordFrac (lin t) (lin_mem t) 1 2) :=
  AdjoinRoot.lift_root _

lemma f1_algebraMap (o : O) : f1 π b₄ t κ hκ (algebraMap O _ o) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1
      (fromZeroRingHom (𝒜 2) _ (algebraMap O _ o)) := by
  rw [← of_C, f1_of, polyToChart_C, baseRes, RingHom.comp_apply, awayMap_fromZero]

lemma f1_h1 : f1 π b₄ t κ hκ (h1 π b₄ t κ) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1
      (Away.map (linHom (lin t) (lin_mem t)) (X 1) (H₁ (O := O))) := by
  rw [h1, f1_of, polyToChart_X1, baseRes, RingHom.comp_apply]

include hκ in
lemma ker_le1 [IsReduced (T1 π b₄ t κ)] :
    RingHom.ker (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1) ≤
      RingHom.ker (g1 π b₄ t κ) := by
  rw [ker_secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (F_mem3 π b₄ b₆) three_pos
    (TateModel.range_ι π b₄ b₆)]
  rintro a ⟨n, hn⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.1 hn
  have h : IsNilpotent (g1 π b₄ t κ a) :=
    ⟨n, by rw [← map_pow, hc, map_mul, g1_F π b₄ t κ hκ, zero_mul]⟩
  exact h.eq_zero

/-- The inverse `Γ(V₁) → T1` (for `T1` reduced), induced by evaluation at `(1, h' + t w, w)`. -/
def gbar1 [IsReduced (T1 π b₄ t κ)] :
    Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1, ⊤) →+* T1 π b₄ t κ :=
  (Ideal.Quotient.lift _ (g1 π b₄ t κ) fun _ ha ↦ RingHom.mem_ker.1 (ker_le1 π b₄ t κ hκ ha)).comp
    (RingHom.quotientKerEquivOfSurjective
      (secRes_surjective (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1)).symm.toRingHom

lemma gbar1_secRes [IsReduced (T1 π b₄ t κ)] (a : Away (𝒜 2) (linHom (lin t) (lin_mem t) (X 1))) :
    gbar1 π b₄ t κ hκ (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a) = g1 π b₄ t κ a := by
  have h : (RingHom.quotientKerEquivOfSurjective
      (secRes_surjective (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1)).symm
        (secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 a) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  simp only [gbar1, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, h, Ideal.Quotient.lift_mk]

lemma gbar1_f1 [IsReduced (T1 π b₄ t κ)] :
    (gbar1 π b₄ t κ hκ).comp (f1 π b₄ t κ hκ) = RingHom.id _ := by
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro o
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [of_C, f1_algebraMap, gbar1_secRes, g1, awayEval_fromZero]
    · change gbar1 π b₄ t κ hκ (f1 π b₄ t κ hκ (h1 π b₄ t κ)) = h1 π b₄ t κ
      rw [f1_h1, gbar1_secRes, g1_mapH₁]
  · change gbar1 π b₄ t κ hκ (f1 π b₄ t κ hκ (w1 π b₄ t κ)) = w1 π b₄ t κ
    rw [f1_w1, gbar1_secRes, g1, awayEval_coordFrac]
    rfl

lemma f1_g1 : (f1 π b₄ t κ hκ).comp (g1 π b₄ t κ) =
    secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 := by
  refine awayHom_ext (lin t) (lin_mem t) 1 (fun o ↦ ?_) (fun i ↦ ?_)
  · rw [RingHom.comp_apply, g1, awayEval_fromZero, f1_algebraMap]
  · rw [RingHom.comp_apply, g1, awayEval_coordFrac]
    fin_cases i
    · change f1 π b₄ t κ hκ 1 =
        secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (coordFrac (lin t) (lin_mem t) 1 0)
      rw [map_one, coordFrac_one_zero, map_one]
    · change f1 π b₄ t κ hκ (h1 π b₄ t κ + algebraMap O _ t * w1 π b₄ t κ) =
        secRes (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 (coordFrac (lin t) (lin_mem t) 1 1)
      rw [map_add, map_mul, f1_h1, f1_algebraMap, f1_w1, coordFrac_one_one, awayMap_fromZero,
        map_add, map_mul]
    · exact f1_w1 π b₄ t κ hκ

/-- **The chart `T1` is the ring of sections of the Tate model over `V₁ = ι⁻¹ D₊(u)`**
(for `T1` reduced). -/
def equiv1 [IsReduced (T1 π b₄ t κ)] :
    T1 π b₄ t κ ≃+* Γ(V (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1, ⊤) :=
  RingEquiv.ofRingHom (f1 π b₄ t κ hκ) (gbar1 π b₄ t κ hκ)
    (RingHom.ext fun x ↦ by
      obtain ⟨a, rfl⟩ := secRes_surjective (lin t) (lin_mem t) (TateModel.ι π b₄ b₆) 1 x
      rw [RingHom.comp_apply, gbar1_secRes, ← RingHom.comp_apply, f1_g1, RingHom.id_apply])
    (gbar1_f1 π b₄ t κ hκ)

lemma equiv1_apply [IsReduced (T1 π b₄ t κ)] (x : T1 π b₄ t κ) :
    equiv1 π b₄ t κ hκ x = f1 π b₄ t κ hκ x := rfl

end

end TateChartSections

end TemperedFundamentalGroups
