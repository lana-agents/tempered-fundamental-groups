/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraOfRings

/-!
# `ℙ¹_O` with three cusps as two-chart rings over `ℙ¹_O` (MR13 A1)

The M2 lifting machinery (special-fibre datum → levels → glueing over the two charts of `ℙ¹_O` →
algebraisation, `NodeEtaleGlue.Overlap`, `ProjectiveLine.AdicChartAlgSystem`) needs a finite
model over `ℙ¹_O = Proj O[X, Y]` whose cusps all lie over `X = 0` (the cusp patch lives on the
first chart, outside the overlap `D(X)`; the differentials of the second chart must be killed by
a constant, `NodeEtaleGlue.Overlap.kills_shift`). For the vertex `ℙ¹ ∖ {three points}` of the
special fibre of the Tate curve (MR13 plan, Route B, item A1: the lifting half of tame
specialisation, cf. [SGA1] XIII, proof of Cor 2.12) we use, for `a ∈ O`, the degree-`3` map

`h = t (t − 1) (t − a) : ℙ¹_t → ℙ¹_X`,

whose fibre over `X = 0` consists of the three cusps `t = 0, 1, a` (simple zeros of `h`; their
reductions are distinct iff `ā ≠ 0, 1`) and whose fibre over `X = ∞` is `t = ∞` (a triple pole,
not a cusp). Its two charts are monic cubics over the chart rings of `ℙ¹_O`:

* **`P1Three.R0 = O[X][t]/(t³ − (1 + a) t² + a t − X)`** `≅ O[t]` (`X ↦ h`), the chart
  `ℙ¹_t ∖ {∞}`, containing the three cusps;
* **`P1Three.R1 = O[Y][s]/(s³ − a Y s² + (1 + a) Y s − Y)`** (`s = 1/t`,
  `Y = s³/((1 − s)(1 − a s))`), the chart `ℙ¹_t ∖ {0, 1, a}`: here `1 − s` and `1 − a s` are units
  (`P1Three.one_sub_s1_mul`, `one_sub_a_s1_mul`);
* both are free of rank three over `O[X]` (`Module.Free`, `Module.Finite`);
* the overlap `R01 = R1[1/Y]`, and **`P1Three.rho0 : R0 → R01`** (`X ↦ 1/Y`, `t ↦ 1/s`) exhibits
  `R01` as `R0[1/X]` (**`P1Three.overlapEquiv`**, inverse `Y ↦ 1/X`, `s ↦ 1/t = (t − 1)(t − a)/X`);
* **`P1Three.twoChart`**: this model as `ProjectiveLine.TwoChartRings O` (`x = X`, `y = Y`).
-/

universe u

open Polynomial

namespace SemistableReduction

namespace P1Three

noncomputable section

variable (O : Type u) [CommRing O] (a : O)

/-- The monic cubic `t³ − (1 + a) t² + a t − X ∈ O[X][t]` of the chart `ℙ¹_t ∖ {∞}`. -/
def G0 : O[X][X] := X ^ 3 - C (C (1 + a)) * X ^ 2 + C (C a) * X - C X

/-- The monic cubic `s³ − a Y s² + (1 + a) Y s − Y ∈ O[Y][s]` of the chart `ℙ¹_t ∖ {0, 1, a}`. -/
def G1 : O[X][X] := X ^ 3 - C (C a * X) * X ^ 2 + C (C (1 + a) * X) * X - C X

lemma monic_G0 : (G0 O a).Monic := by
  unfold G0
  monicity!

lemma monic_G1 : (G1 O a).Monic := by
  unfold G1
  monicity!

/-- The chart ring `O[t]` over `D₊(Y)` of the base (`X ↦ t (t − 1) (t − a)`). -/
abbrev R0 : Type u := AdjoinRoot (G0 O a)

/-- The chart ring over `D₊(X)` of the base (`Y ↦ s³/((1 − s)(1 − a s))`). -/
abbrev R1 : Type u := AdjoinRoot (G1 O a)

instance : Module.Free O[X] (R0 O a) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_G0 O a)).basis

instance : Module.Finite O[X] (R0 O a) :=
  (AdjoinRoot.powerBasis' (monic_G0 O a)).finite

instance : Module.Free O[X] (R1 O a) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' (monic_G1 O a)).basis

instance : Module.Finite O[X] (R1 O a) :=
  (AdjoinRoot.powerBasis' (monic_G1 O a)).finite

/-- The base coordinate `X = t (t − 1) (t − a)` in `R0`. -/
abbrev x0 : R0 O a := AdjoinRoot.of _ X

/-- The coordinate `t` in `R0`. -/
abbrev t0 : R0 O a := AdjoinRoot.root _

/-- The base coordinate `Y` in `R1`. -/
abbrev y1 : R1 O a := AdjoinRoot.of _ X

/-- The coordinate `s = 1/t` in `R1`. -/
abbrev s1 : R1 O a := AdjoinRoot.root _

lemma of_C (G : O[X][X]) (o : O) : AdjoinRoot.of G (C o) = algebraMap O (AdjoinRoot G) o := by
  rw [AdjoinRoot.algebraMap_eq', RingHom.comp_apply, Polynomial.algebraMap_apply]
  rfl

/-- The relation `t³ − (1 + a) t² + a t = X` in `R0`. -/
lemma eq0 : t0 O a ^ 3 - algebraMap O _ (1 + a) * t0 O a ^ 2 + algebraMap O _ a * t0 O a -
    x0 O a = 0 := by
  have h : AdjoinRoot.mk (G0 O a) (X ^ 3 - C (C (1 + a)) * X ^ 2 + C (C a) * X - C X) = 0 :=
    AdjoinRoot.mk_self
  simpa only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, of_C] using h

/-- The relation `s³ − a Y s² + (1 + a) Y s − Y = 0` in `R1`. -/
lemma eq1 : s1 O a ^ 3 - algebraMap O _ a * y1 O a * s1 O a ^ 2 +
    algebraMap O _ (1 + a) * y1 O a * s1 O a - y1 O a = 0 := by
  have h : AdjoinRoot.mk (G1 O a) (X ^ 3 - C (C a * X) * X ^ 2 + C (C (1 + a) * X) * X - C X) =
      0 := AdjoinRoot.mk_self
  simpa only [map_add, map_sub, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, of_C] using h

/-- `X = t (t − 1) (t − a)`. -/
lemma x0_eq : x0 O a = t0 O a * (t0 O a - 1) * (t0 O a - algebraMap O _ a) := by
  have h := eq0 O a
  rw [map_add, map_one] at h
  linear_combination -h

/-- `1 − s` is a unit of `R1`. -/
lemma one_sub_s1_mul : (1 - s1 O a) * (1 + s1 O a + s1 O a ^ 2 +
    y1 O a * (1 - algebraMap O _ a * s1 O a)) = 1 := by
  have h := eq1 O a
  rw [map_add, map_one] at h
  linear_combination -h

/-- `1 − a s` is a unit of `R1`. -/
lemma one_sub_a_s1_mul : (1 - algebraMap O _ a * s1 O a) * (1 + algebraMap O _ a * s1 O a +
    algebraMap O _ a ^ 2 * s1 O a ^ 2 + algebraMap O _ a ^ 3 * y1 O a * (1 - s1 O a)) = 1 := by
  have h := eq1 O a
  rw [map_add, map_one] at h
  linear_combination -(algebraMap O (R1 O a) a ^ 3) * h

/-! ### The overlap -/

/-- The overlap `R01 = R1[1/Y]`. -/
abbrev R01 : Type u := Localization.Away (y1 O a)

/-- `1/Y` in the overlap. -/
abbrev yinv : R01 O a := IsLocalization.Away.invSelf (y1 O a)

/-- `s` in the overlap. -/
abbrev so : R01 O a := algebraMap (R1 O a) _ (s1 O a)

/-- `Y` in the overlap. -/
abbrev yo : R01 O a := algebraMap (R1 O a) _ (y1 O a)

/-- `a` in the overlap. -/
abbrev ao : R01 O a := algebraMap O (R01 O a) a

/-- `1/s = s² (1/Y) (1/(1 − s)) (1/(1 − a s))` in the overlap. -/
def sinv : R01 O a := so O a ^ 2 * yinv O a * (1 + so O a + so O a ^ 2 +
    yo O a * (1 - ao O a * so O a)) * (1 + ao O a * so O a + ao O a ^ 2 * so O a ^ 2 +
    ao O a ^ 3 * yo O a * (1 - so O a))

lemma y1_mul_yinv : yo O a * yinv O a = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma eq1_R01 : so O a ^ 3 - ao O a * yo O a * so O a ^ 2 + (1 + ao O a) * yo O a * so O a -
    yo O a = 0 := by
  have h := congrArg (algebraMap (R1 O a) (R01 O a)) (eq1 O a)
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_one,
    ← IsScalarTower.algebraMap_apply] at h
  linear_combination h

lemma so_mul_sinv : so O a * sinv O a = 1 := by
  have h := eq1_R01 O a
  have hI := y1_mul_yinv O a
  have h1 : (1 - so O a) * (1 + so O a + so O a ^ 2 + yo O a * (1 - ao O a * so O a)) = 1 := by
    linear_combination -h
  have h2 : (1 - ao O a * so O a) * (1 + ao O a * so O a + ao O a ^ 2 * so O a ^ 2 +
      ao O a ^ 3 * yo O a * (1 - so O a)) = 1 := by
    linear_combination -(ao O a ^ 3) * h
  have h3 : so O a ^ 3 = yo O a * (1 - so O a) * (1 - ao O a * so O a) := by
    linear_combination h
  set w1 := 1 + so O a + so O a ^ 2 + yo O a * (1 - ao O a * so O a)
  set w2 := 1 + ao O a * so O a + ao O a ^ 2 * so O a ^ 2 + ao O a ^ 3 * yo O a * (1 - so O a)
  calc so O a * sinv O a = so O a ^ 3 * yinv O a * w1 * w2 := by rw [sinv]; ring
    _ = (yo O a * yinv O a) * ((1 - so O a) * w1) * ((1 - ao O a * so O a) * w2) := by
        rw [h3]; ring
    _ = 1 := by rw [hI, h1, h2, one_mul, one_mul]

lemma eval_G0_rho : (G0 O a).eval₂
    ((Polynomial.aeval (yinv O a) : O[X] →ₐ[O] R01 O a) : O[X] →+* R01 O a) (sinv O a) = 0 := by
  have hS := so_mul_sinv O a
  have hI := y1_mul_yinv O a
  have h := eq1_R01 O a
  -- `yinv s³ = (1 − s)(1 − a s)`
  have hY : yinv O a * so O a ^ 3 = (1 - so O a) * (1 - ao O a * so O a) := by
    linear_combination yinv O a * h + ((1 - so O a) * (1 - ao O a * so O a)) * hI
  simp only [G0, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, RingHom.coe_coe,
    Polynomial.aeval_X, Polynomial.aeval_C, map_add, map_one, eval₂_one]
  set σ := sinv O a
  set s := so O a
  linear_combination (-σ ^ 3) * hY + ((1 + ao O a) * σ ^ 2 - ao O a * σ * (s * σ + 1) +
    yinv O a * ((s * σ) ^ 2 + s * σ + 1) - σ ^ 3 * ((1 + ao O a) * s - ao O a * s ^ 2) +
    σ ^ 3 * ((1 + ao O a) * s - ao O a * s ^ 2)) * hS

/-- **The restriction `ρ₀ : R0 → R01`**: `X ↦ 1/Y`, `t ↦ 1/s`. -/
def rho0 : R0 O a →ₐ[O] R01 O a :=
  AdjoinRoot.liftAlgHom (G0 O a) (Polynomial.aeval (yinv O a)) (sinv O a) (eval_G0_rho O a)

lemma rho0_x0 : rho0 O a (x0 O a) = yinv O a := by
  simp [rho0]

lemma rho0_t0 : rho0 O a (t0 O a) = sinv O a := by
  simp [rho0]

/-! ### The inverse map `R1[1/Y] → R0[1/X]` -/

/-- `R0[1/X]`. -/
abbrev R0x : Type u := Localization.Away (x0 O a)

/-- `1/X` in `R0[1/X]`. -/
abbrev xinv : R0x O a := IsLocalization.Away.invSelf (x0 O a)

/-- `t` in `R0[1/X]`. -/
abbrev tx : R0x O a := algebraMap (R0 O a) _ (t0 O a)

/-- `X` in `R0[1/X]`. -/
abbrev xo : R0x O a := algebraMap (R0 O a) _ (x0 O a)

/-- `a` in `R0[1/X]`. -/
abbrev ax : R0x O a := algebraMap O (R0x O a) a

/-- `1/t = (t − 1)(t − a)/X` in `R0[1/X]`. -/
def tinv : R0x O a := (tx O a - 1) * (tx O a - ax O a) * xinv O a

lemma x0_mul_xinv : xo O a * xinv O a = 1 :=
  IsLocalization.Away.mul_invSelf _

lemma eq0_R0x : tx O a ^ 3 - (1 + ax O a) * tx O a ^ 2 + ax O a * tx O a - xo O a = 0 := by
  have h := congrArg (algebraMap (R0 O a) (R0x O a)) (eq0 O a)
  simp only [map_add, map_sub, map_mul, map_pow, map_zero, map_one,
    ← IsScalarTower.algebraMap_apply] at h
  linear_combination h

lemma tx_mul_tinv : tx O a * tinv O a = 1 := by
  rw [tinv]
  linear_combination xinv O a * eq0_R0x O a + x0_mul_xinv O a

lemma eval_G1_sigma : (G1 O a).eval₂
    ((Polynomial.aeval (xinv O a) : O[X] →ₐ[O] R0x O a) : O[X] →+* R0x O a) (tinv O a) = 0 := by
  have hT := tx_mul_tinv O a
  have hX := x0_mul_xinv O a
  have h := eq0_R0x O a
  simp only [G1, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C, RingHom.coe_coe,
    Polynomial.aeval_X, Polynomial.aeval_C, map_add, map_mul, map_one, eval₂_one]
  set τ := tinv O a
  set t := tx O a
  -- `τ³ (1 − xinv (t³ − (1 + a) t² + a t)) = τ³ (1 − xinv X) = 0`, up to `t τ = 1`
  linear_combination (-τ ^ 3 * xinv O a) * h - τ ^ 3 * hX +
    (ax O a * xinv O a * τ ^ 2 - (1 + ax O a) * xinv O a * τ * (1 + t * τ) +
      xinv O a * (1 + t * τ + t ^ 2 * τ ^ 2)) * hT

/-- `σ : R1 → R0[1/X]`: `Y ↦ 1/X`, `s ↦ 1/t`. -/
def sigma1 : R1 O a →ₐ[O] R0x O a :=
  AdjoinRoot.liftAlgHom (G1 O a) (Polynomial.aeval (xinv O a)) (tinv O a) (eval_G1_sigma O a)

lemma sigma1_y1 : sigma1 O a (y1 O a) = xinv O a := by
  simp [sigma1]

lemma sigma1_s1 : sigma1 O a (s1 O a) = tinv O a := by
  simp [sigma1]

lemma eq_of_mul_eq_one {S : Type*} [CommRing S] {a x y : S} (hx : a * x = 1) (hy : a * y = 1) :
    x = y := by
  linear_combination y * hx - x * hy

lemma isUnit_rho0_x0 : IsUnit (rho0 O a (x0 O a)) := by
  rw [rho0_x0]
  exact IsUnit.of_mul_eq_one_right _ (y1_mul_yinv O a)

lemma isUnit_sigma1_y1 : IsUnit (sigma1 O a (y1 O a)) := by
  rw [sigma1_y1]
  exact IsUnit.of_mul_eq_one_right _ (x0_mul_xinv O a)

/-- `R0[1/X] → R01` induced by `ρ₀`. -/
def phi : R0x O a →ₐ[O] R01 O a :=
  IsLocalization.Away.liftAlgHom (x0 O a) (isUnit_rho0_x0 O a)

/-- `R01 → R0[1/X]` induced by `σ`. -/
def psi : R01 O a →ₐ[O] R0x O a :=
  IsLocalization.Away.liftAlgHom (y1 O a) (isUnit_sigma1_y1 O a)

lemma phi_algebraMap (b : R0 O a) : phi O a (algebraMap _ _ b) = rho0 O a b :=
  IsLocalization.Away.lift_eq _ (isUnit_rho0_x0 O a) b

lemma psi_algebraMap (b : R1 O a) : psi O a (algebraMap _ _ b) = sigma1 O a b :=
  IsLocalization.Away.lift_eq _ (isUnit_sigma1_y1 O a) b

lemma phi_xinv : phi O a (xinv O a) = yo O a := by
  refine eq_of_mul_eq_one (a := yinv O a) ?_ ?_
  · have h := congrArg (phi O a) (x0_mul_xinv O a)
    rwa [map_mul, phi_algebraMap, rho0_x0, map_one] at h
  · rw [mul_comm]; exact y1_mul_yinv O a

lemma psi_yinv : psi O a (yinv O a) = xo O a := by
  refine eq_of_mul_eq_one (a := xinv O a) ?_ ?_
  · have h := congrArg (psi O a) (y1_mul_yinv O a)
    rwa [map_mul, psi_algebraMap, sigma1_y1, map_one] at h
  · rw [mul_comm]; exact x0_mul_xinv O a

lemma phi_tinv : phi O a (tinv O a) = so O a := by
  refine eq_of_mul_eq_one (a := sinv O a) ?_ ?_
  · have h := congrArg (phi O a) (tx_mul_tinv O a)
    rwa [map_mul, phi_algebraMap, rho0_t0, map_one] at h
  · rw [mul_comm]; exact so_mul_sinv O a

lemma psi_sinv : psi O a (sinv O a) = tx O a := by
  refine eq_of_mul_eq_one (a := tinv O a) ?_ ?_
  · have h := congrArg (psi O a) (so_mul_sinv O a)
    rwa [map_mul, psi_algebraMap, sigma1_s1, map_one] at h
  · rw [mul_comm]; exact tx_mul_tinv O a

lemma phi_psi (x : R01 O a) : phi O a (psi O a x) = x := by
  have : (phi O a).comp (psi O a) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (y1 O a))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change phi O a (psi O a (algebraMap _ _ (y1 O a))) = algebraMap _ _ (y1 O a)
      rw [psi_algebraMap, sigma1_y1, phi_xinv]
    · change phi O a (psi O a (algebraMap _ _ (s1 O a))) = algebraMap _ _ (s1 O a)
      rw [psi_algebraMap, sigma1_s1, phi_tinv]
  exact AlgHom.congr_fun this x

lemma psi_phi (x : R0x O a) : psi O a (phi O a x) = x := by
  have : (psi O a).comp (phi O a) = AlgHom.id O _ := by
    refine IsLocalization.algHom_ext (Submonoid.powers (x0 O a))
      (AdjoinRoot.algHom_ext' (Polynomial.algHom_ext ?_) ?_)
    · change psi O a (phi O a (algebraMap _ _ (x0 O a))) = algebraMap _ _ (x0 O a)
      rw [phi_algebraMap, rho0_x0, psi_yinv]
    · change psi O a (phi O a (algebraMap _ _ (t0 O a))) = algebraMap _ _ (t0 O a)
      rw [phi_algebraMap, rho0_t0, psi_sinv]
  exact AlgHom.congr_fun this x

/-- **The overlap is `R0[1/X]`**: `R0[1/X] ≃ R1[1/Y]` (`X ↦ 1/Y`, `t ↦ 1/s`). -/
def overlapEquiv : R0x O a ≃ₐ[O] R01 O a :=
  AlgEquiv.ofAlgHom (phi O a) (psi O a) (AlgHom.ext (phi_psi O a)) (AlgHom.ext (psi_phi O a))

/-- The unit `T = 1/Y` of the overlap. -/
def uT : (R01 O a)ˣ where
  val := yinv O a
  inv := yo O a
  val_inv := by rw [mul_comm]; exact y1_mul_yinv O a
  inv_val := y1_mul_yinv O a

/-- **`ℙ¹_t` with the cusps `0, 1, a` as two-chart rings over `ℙ¹_O`** via
`h = t (t − 1) (t − a)` (`x = X`, `y = Y`). -/
def twoChart : ProjectiveLine.TwoChartRings O where
  R0 := R0 O a
  R1 := R1 O a
  R01 := R01 O a
  x := x0 O a
  y := y1 O a
  u := uT O a
  ρ0 := rho0 O a
  ρ1 := IsScalarTower.toAlgHom O (R1 O a) (R01 O a)
  ρ0_x := rho0_x0 O a
  ρ1_y := rfl
  exists0 z := by
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (x0 O a))
      ((overlapEquiv O a).symm z)
    refine ⟨m, k, ?_⟩
    change (overlapEquiv O a).symm z * algebraMap _ _ (x0 O a ^ k) = algebraMap _ _ m at hm
    have h := congrArg (overlapEquiv O a) hm
    simp only [map_mul, map_pow, AlgEquiv.apply_symm_apply] at h
    change z * phi O a (algebraMap _ _ (x0 O a)) ^ k = phi O a (algebraMap _ _ m) at h
    rw [phi_algebraMap, phi_algebraMap, rho0_x0] at h
    rw [mul_comm]
    exact h
  ker0 m hm := by
    have h : algebraMap (R0 O a) (R0x O a) m = 0 := by
      apply (overlapEquiv O a).injective
      change phi O a _ = _
      rw [phi_algebraMap, map_zero]
      exact hm
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (x0 O a)) _ m).1 h
    exact ⟨k, hk⟩
  exists1 z := by
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalization.surj (Submonoid.powers (y1 O a)) z
    refine ⟨m, k, ?_⟩
    change z * algebraMap _ _ (y1 O a ^ k) = algebraMap _ _ m at hm
    change (algebraMap _ _ (y1 O a)) ^ k * z = algebraMap _ _ m
    rw [mul_comm, ← map_pow]
    exact hm
  ker1 m hm := by
    obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers (y1 O a)) _ m).1 hm
    exact ⟨k, hk⟩

end

end P1Three

end SemistableReduction
