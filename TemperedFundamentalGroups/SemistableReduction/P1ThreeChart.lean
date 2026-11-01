/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraOfRings

/-!
# `ℙ¹_O` with the three cusps `0, 1, ∞` as two-chart rings over `ℙ¹_O` (MR13 A1)

The M2 lifting machinery (special-fibre datum → levels → glueing over the two charts of `ℙ¹_O` →
algebraisation, `NodeEtaleGlue.Overlap`, `ProjectiveLine.AdicChartAlgSystem`) needs a finite
model over `ℙ¹_O = Proj O[X, Y]` whose cusps lie over `X = 0` or `X = ∞` (no cusp in the overlap
`D(X)`). For the vertex `ℙ¹ ∖ {0, 1, ∞}` of the special fibre of the Tate curve (MR13 plan, Route B,
item A1: the lifting half of tame specialisation, cf. [SGA1] XIII, proof of Cor 2.12) we use the
degree-`2` map
`h = t (t − 1) : ℙ¹_t → ℙ¹_X`,
which sends `0, 1 ↦ 0` and `∞ ↦ ∞` and is étale over `D(X)` away from the ramification point
`t = 1/2` (an étale point of the base, not a cusp). Its two charts are monic quadrics over the
chart rings of `ℙ¹_O`:

* **`P1Three.R0 = O[X][t]/(t² − t − X)`** `≅ O[t]` (`X ↦ h = t² − t`), the chart `ℙ¹_t ∖ {∞}`;
* **`P1Three.R1 = O[Y][s]/(s² + Y s − Y)`** `≅ O[s][1/(1 − s)]` (`s = 1/t`, `Y ↦ s²/(1 − s)`), the
  chart `ℙ¹_t ∖ {0, 1}`; here `(1 − s)(Y + 1 + s) = 1` (`P1Three.one_sub_s1_mul`);
* both are free of rank two over `O[X]` (`Module.Free`, `Module.Finite`);
* the overlap `R01 = R1[1/Y]`, and **`P1Three.rho0 : R0 → R01`** (`X ↦ 1/Y`, `t ↦ 1/s`) exhibits
  `R01` as `R0[1/X]` (**`P1Three.overlapEquiv`**, inverse `Y ↦ 1/X`, `s ↦ (t − 1)/X`);
* **`P1Three.twoChart`**: this model as `ProjectiveLine.TwoChartRings O` (`x = X`, `y = Y`).

The cusps are `V(X) = {t = 0} ⊔ {t = 1}` in `R0` (two disjoint sections, `t` and `t − 1` are
comaximal: `P1Three.span_t0_sub_one`) and `V(s)` in `R1` (`V(Y) = V(s²)` there).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace P1Three

noncomputable section

variable (O : Type u) [CommRing O]

/-- The monic quadric `t² − t − X ∈ O[X][t]` of the chart `ℙ¹_t ∖ {∞}`. -/
def G0 : O[X][X] := X ^ 2 - X - C X

/-- The monic quadric `s² + Y s − Y ∈ O[Y][s]` of the chart `ℙ¹_t ∖ {0, 1}`. -/
def G1 : O[X][X] := X ^ 2 + C X * X - C X

lemma monic_G0 : (G0 O).Monic := by
  unfold G0
  monicity!

lemma monic_G1 : (G1 O).Monic := by
  unfold G1
  monicity!

/-- The chart ring `O[t]` over `D₊(Y)` of the base (`X ↦ t² − t`). -/
abbrev R0 : Type u := AdjoinRoot (G0 O)

/-- The chart ring `O[s][1/(1 − s)]` over `D₊(X)` of the base (`Y ↦ s²/(1 − s)`). -/
abbrev R1 : Type u := AdjoinRoot (G1 O)

instance : Module.Free O[X] (R0 O) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_G0 O)).basis

instance : Module.Finite O[X] (R0 O) :=
  (AdjoinRoot.powerBasis' (monic_G0 O)).finite

instance : Module.Free O[X] (R1 O) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_G1 O)).basis

instance : Module.Finite O[X] (R1 O) :=
  (AdjoinRoot.powerBasis' (monic_G1 O)).finite

/-- The base coordinate `X = t² − t` in `R0`. -/
abbrev x0 : R0 O := AdjoinRoot.of _ X

/-- The coordinate `t` in `R0`. -/
abbrev t0 : R0 O := AdjoinRoot.root _

/-- The base coordinate `Y` in `R1`. -/
abbrev y1 : R1 O := AdjoinRoot.of _ X

/-- The coordinate `s = 1/t` in `R1`. -/
abbrev s1 : R1 O := AdjoinRoot.root _

/-- The relation `t² − t = X` in `R0`. -/
lemma eq0 : t0 O ^ 2 - t0 O - x0 O = 0 := by
  have h : AdjoinRoot.mk (G0 O) (X ^ 2 - X - C X) = 0 := AdjoinRoot.mk_self
  simpa only [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h

/-- The relation `s² + Y s − Y = 0` in `R1`. -/
lemma eq1 : s1 O ^ 2 + y1 O * s1 O - y1 O = 0 := by
  have h : AdjoinRoot.mk (G1 O) (X ^ 2 + C X * X - C X) = 0 := AdjoinRoot.mk_self
  simpa only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] using h

/-- `X = t (t − 1)`. -/
lemma x0_eq : x0 O = t0 O * (t0 O - 1) := by
  linear_combination -(eq0 O)

/-- The two cusps `t = 0`, `t = 1` over `X = 0` are disjoint: `(t, t − 1) = (1)`. -/
lemma span_t0_sub_one : Ideal.span {t0 O, t0 O - 1} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h : (1 : R0 O) = 1 * t0 O + (-1) * (t0 O - 1) := by ring
  rw [h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- `1 − s` is a unit of `R1`: `(1 − s)(Y + 1 + s) = 1`. -/
lemma one_sub_s1_mul : (1 - s1 O) * (y1 O + 1 + s1 O) = 1 := by
  linear_combination -(eq1 O)

/-- `Y (1 − s) = s²` in `R1`. -/
lemma y1_mul : y1 O * (1 - s1 O) = s1 O ^ 2 := by
  linear_combination -(eq1 O)

/-! ### The overlap -/

/-- The overlap `R01 = R1[1/Y]`. -/
abbrev R01 : Type u := Localization.Away (y1 O)

/-- `1/Y` in the overlap. -/
abbrev yinv : R01 O := IsLocalization.Away.invSelf (y1 O)

/-- `s` in the overlap. -/
abbrev so : R01 O := algebraMap (R1 O) _ (s1 O)

/-- `Y` in the overlap. -/
abbrev yo : R01 O := algebraMap (R1 O) _ (y1 O)

/-- `1/s = s (Y + 1 + s)/Y` in the overlap. -/
abbrev sinv : R01 O := so O * yinv O * (yo O + 1 + so O)

lemma y1_mul_yinv : yo O * yinv O = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma eq1_R01 : so O ^ 2 + yo O * so O - yo O = 0 := by
  have h := congrArg (algebraMap (R1 O) (R01 O)) (eq1 O)
  simpa only [map_add, map_sub, map_mul, map_pow, map_zero] using h

lemma so_mul_sinv : so O * sinv O = 1 := by
  linear_combination (yinv O * (yo O + 1 + so O) - yo O * yinv O) * eq1_R01 O +
    y1_mul_yinv O

lemma yinv_mul_so_sq : yinv O * so O ^ 2 = 1 - so O := by
  linear_combination yinv O * eq1_R01 O + (1 - so O) * y1_mul_yinv O

lemma eval_G0_rho : (G0 O).eval₂
    ((Polynomial.aeval (yinv O) : O[X] →ₐ[O] R01 O) : O[X] →+* R01 O) (sinv O) = 0 := by
  have hY := yinv_mul_so_sq O
  have hS := so_mul_sinv O
  simp only [G0, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, RingHom.coe_coe, Polynomial.aeval_X]
  linear_combination (-(sinv O) ^ 2) * hY +
    (sinv O + yinv O * (so O * sinv O + 1) - sinv O ^ 2 * so O + sinv O ^ 2 * so O) * hS

/-- **The restriction `ρ₀ : R0 → R01`**: `X ↦ 1/Y`, `t ↦ 1/s`. -/
def rho0 : R0 O →ₐ[O] R01 O :=
  AdjoinRoot.liftAlgHom (G0 O) (Polynomial.aeval (yinv O)) (sinv O) (eval_G0_rho O)

lemma rho0_x0 : rho0 O (x0 O) = yinv O := by
  simp [rho0]

lemma rho0_t0 : rho0 O (t0 O) = sinv O := by
  simp [rho0]

/-! ### The inverse map `R1[1/Y] → R0[1/X]` -/

/-- `R0[1/X]`. -/
abbrev R0x : Type u := Localization.Away (x0 O)

/-- `1/X` in `R0[1/X]`. -/
abbrev xinv : R0x O := IsLocalization.Away.invSelf (x0 O)

/-- `t` in `R0[1/X]`. -/
abbrev tx : R0x O := algebraMap (R0 O) _ (t0 O)

/-- `X` in `R0[1/X]`. -/
abbrev xo : R0x O := algebraMap (R0 O) _ (x0 O)

lemma x0_mul_xinv : xo O * xinv O = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma eq0_R0x : tx O ^ 2 - tx O - xo O = 0 := by
  have h := congrArg (algebraMap (R0 O) (R0x O)) (eq0 O)
  simpa only [map_sub, map_pow, map_zero] using h

lemma eval_G1_sigma : (G1 O).eval₂
    ((Polynomial.aeval (xinv O) : O[X] →ₐ[O] R0x O) : O[X] →+* R0x O)
    ((tx O - 1) * xinv O) = 0 := by
  simp only [G1, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    RingHom.coe_coe, Polynomial.aeval_X]
  linear_combination xinv O ^ 2 * eq0_R0x O + xinv O * x0_mul_xinv O

/-- `σ : R1 → R0[1/X]`: `Y ↦ 1/X`, `s ↦ (t − 1)/X = 1/t`. -/
def sigma1 : R1 O →ₐ[O] R0x O :=
  AdjoinRoot.liftAlgHom (G1 O) (Polynomial.aeval (xinv O)) ((tx O - 1) * xinv O)
    (eval_G1_sigma O)

lemma sigma1_y1 : sigma1 O (y1 O) = xinv O := by
  simp [sigma1]

lemma sigma1_s1 : sigma1 O (s1 O) = (tx O - 1) * xinv O := by
  simp [sigma1]

lemma eq_of_mul_eq_one {S : Type*} [CommRing S] {a x y : S} (hx : a * x = 1) (hy : a * y = 1) :
    x = y := by
  linear_combination y * hx - x * hy

lemma isUnit_rho0_x0 : IsUnit (rho0 O (x0 O)) := by
  rw [rho0_x0]
  exact IsUnit.of_mul_eq_one_right _ (y1_mul_yinv O)

lemma isUnit_sigma1_y1 : IsUnit (sigma1 O (y1 O)) := by
  rw [sigma1_y1]
  exact IsUnit.of_mul_eq_one_right _ (x0_mul_xinv O)

/-- `R0[1/X] → R01` induced by `ρ₀`. -/
def phi : R0x O →ₐ[O] R01 O :=
  IsLocalization.Away.liftAlgHom (x0 O) (isUnit_rho0_x0 O)

/-- `R01 → R0[1/X]` induced by `σ`. -/
def psi : R01 O →ₐ[O] R0x O :=
  IsLocalization.Away.liftAlgHom (y1 O) (isUnit_sigma1_y1 O)

lemma phi_algebraMap (a : R0 O) : phi O (algebraMap _ _ a) = rho0 O a :=
  IsLocalization.Away.lift_eq _ (isUnit_rho0_x0 O) a

lemma psi_algebraMap (a : R1 O) : psi O (algebraMap _ _ a) = sigma1 O a :=
  IsLocalization.Away.lift_eq _ (isUnit_sigma1_y1 O) a

lemma phi_xinv : phi O (xinv O) = yo O := by
  refine eq_of_mul_eq_one (a := yinv O) ?_ ?_
  · have h := congrArg (phi O) (x0_mul_xinv O)
    rwa [map_mul, phi_algebraMap, rho0_x0, map_one] at h
  · rw [mul_comm]; exact y1_mul_yinv O

lemma psi_yinv : psi O (yinv O) = xo O := by
  refine eq_of_mul_eq_one (a := xinv O) ?_ ?_
  · have h := congrArg (psi O) (y1_mul_yinv O)
    rwa [map_mul, psi_algebraMap, sigma1_y1, map_one] at h
  · rw [mul_comm]; exact x0_mul_xinv O

lemma phi_psi (x : R01 O) : phi O (psi O x) = x := by
  have : (phi O).comp (psi O) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (y1 O))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change phi O (psi O (algebraMap _ _ (y1 O))) = algebraMap _ _ (y1 O)
      rw [psi_algebraMap, sigma1_y1, phi_xinv]
    · change phi O (psi O (algebraMap _ _ (s1 O))) = algebraMap _ _ (s1 O)
      rw [psi_algebraMap, sigma1_s1, map_mul, map_sub, map_one, phi_xinv, phi_algebraMap,
        rho0_t0]
      linear_combination (-(sinv O)) * eq1_R01 O + (yo O + so O) * so_mul_sinv O
  exact AlgHom.congr_fun this x

lemma psi_phi (x : R0x O) : psi O (phi O x) = x := by
  have : (psi O).comp (phi O) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (x0 O))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change psi O (phi O (algebraMap _ _ (x0 O))) = algebraMap _ _ (x0 O)
      rw [phi_algebraMap, rho0_x0, psi_yinv]
    · change psi O (phi O (algebraMap _ _ (t0 O))) = algebraMap _ _ (t0 O)
      rw [phi_algebraMap, rho0_t0, map_mul, map_mul, map_add, map_add, map_one, psi_yinv,
        psi_algebraMap, psi_algebraMap, sigma1_s1, sigma1_y1]
      linear_combination ((tx O - 1) * (tx O * xinv O + 1) + 1) * x0_mul_xinv O +
        xinv O * eq0_R0x O
  exact AlgHom.congr_fun this x

/-- **The overlap is `R0[1/X]`**: `R0[1/X] ≃ R1[1/Y]` (`X ↦ 1/Y`, `t ↦ 1/s`). -/
def overlapEquiv : R0x O ≃ₐ[O] R01 O :=
  AlgEquiv.ofAlgHom (phi O) (psi O) (AlgHom.ext (phi_psi O)) (AlgHom.ext (psi_phi O))

/-- The unit `T = 1/Y` of the overlap. -/
def uT : (R01 O)ˣ where
  val := yinv O
  inv := yo O
  val_inv := by rw [mul_comm]; exact y1_mul_yinv O
  inv_val := y1_mul_yinv O

/-- **`ℙ¹_t` with the cusps `0, 1, ∞` as two-chart rings over `ℙ¹_O`** via `h = t (t − 1)`
(`x = X`, `y = Y`). -/
def twoChart : ProjectiveLine.TwoChartRings O where
  R0 := R0 O
  R1 := R1 O
  R01 := R01 O
  x := x0 O
  y := y1 O
  u := uT O
  ρ0 := rho0 O
  ρ1 := IsScalarTower.toAlgHom O (R1 O) (R01 O)
  ρ0_x := rho0_x0 O
  ρ1_y := rfl
  exists0 z := by
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (x0 O))
      ((overlapEquiv O).symm z)
    refine ⟨m, k, ?_⟩
    change (overlapEquiv O).symm z * algebraMap _ _ (x0 O ^ k) = algebraMap _ _ m at hm
    have h := congrArg (overlapEquiv O) hm
    simp only [map_mul, map_pow, AlgEquiv.apply_symm_apply] at h
    change z * phi O (algebraMap _ _ (x0 O)) ^ k = phi O (algebraMap _ _ m) at h
    rw [phi_algebraMap, phi_algebraMap, rho0_x0] at h
    rw [mul_comm]
    exact h
  ker0 m hm := by
    have h : algebraMap (R0 O) (R0x O) m = 0 := by
      apply (overlapEquiv O).injective
      change phi O _ = _
      rw [phi_algebraMap, map_zero]
      exact hm
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (x0 O)) _ m).1 h
    exact ⟨k, hk⟩
  exists1 z := by
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (y1 O)) z
    refine ⟨m, k, ?_⟩
    change z * algebraMap _ _ (y1 O ^ k) = algebraMap _ _ m at hm
    change (algebraMap _ _ (y1 O)) ^ k * z = algebraMap _ _ m
    rw [mul_comm, ← map_pow]
    exact hm
  ker1 m hm := by
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (y1 O)) _ m).1 hm
    exact ⟨k, hk⟩

end

end P1Three

end SemistableReduction
