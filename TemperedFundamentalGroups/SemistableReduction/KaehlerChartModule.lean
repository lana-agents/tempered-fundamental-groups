/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Kaehler.TensorProduct
import FormalSchemes.ChartModule

/-!
# The relative differentials of a finite morphism to `ℙ¹_A` as a chart module

(Blueprint §12.8, M2.5 (f).) Let `R₀, R₁, R₀₁` be the rings of a scheme `𝒳` over the two charts
of `ℙ¹_A` and their overlap (`R₀₁ = R₀[1/x] = R₁[1/y]`, `x y = 1` in `R₀₁`), and `S₀, S₁, S₀₁`
those of a scheme `𝒴` over `𝒳` (`S₀₁ = S₀[1/x] = S₁[1/y]`). The modules of relative differentials
`Ω[S₀⁄R₀]`, `Ω[S₁⁄R₁]`, `Ω[S₀₁⁄R₀₁]` with the maps `KaehlerDifferential.map` form a chart module
**`KaehlerChart.chartModule`** (the quasi-coherent sheaf `Ω_{𝒴/𝒳}` pushed forward to `ℙ¹_A`): the
localization axioms are `KaehlerDifferential.isLocalizedModule` (`Ω[S[1/x]⁄R[1/x]] = Ω[S⁄R][1/x]`).
**`KaehlerChart.finite_x0`**: it is coherent if `S₀` is finite over `A[X]` (`X ↦ x`) and
`Ω[S₀⁄R₀]` is finite over `S₀`.
-/

universe u

open Polynomial

namespace KaehlerChart

section MulLin

variable (A : Type u) [CommRing A] (R : Type u) {S : Type u} [CommRing R] [CommRing S]
  [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S]

/-- Multiplication by an element of `S` on `Ω[S⁄R]`, as an `A`-linear map. -/
noncomputable def mulLin (s : S) : Ω[S⁄R] →ₗ[A] Ω[S⁄R] :=
  ((LinearMap.lsmul S Ω[S⁄R]) s).restrictScalars A

lemma mulLin_apply (s : S) (ω : Ω[S⁄R]) : mulLin A R s ω = s • ω := rfl

lemma mulLin_pow_apply (s : S) (k : ℕ) (ω : Ω[S⁄R]) : (mulLin A R s ^ k) ω = s ^ k • ω := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, ih, mulLin_apply, pow_succ', mul_smul]

end MulLin

section Unit

variable {R0 : Type u} (S0 S01 : Type u) [CommRing R0] [CommRing S0] [CommRing S01]
  [Algebra R0 S0] [Algebra S0 S01] (x : R0) [IsLocalization.Away (algebraMap R0 S0 x) S01]

lemma isUnit_x : IsUnit (algebraMap S0 S01 (algebraMap R0 S0 x)) :=
  IsLocalization.Away.algebraMap_isUnit _

/-- The unit `T = x` of the overlap. -/
noncomputable def unitT : S01ˣ := (isUnit_x S0 S01 x).unit

lemma unitT_val : ((unitT S0 S01 x : S01ˣ) : S01) = algebraMap S0 S01 (algebraMap R0 S0 x) := rfl

end Unit

lemma smulOfUnit_pow_apply {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M] (v : Sˣ)
    (k : ℕ) (z : M) : (LinearEquiv.smulOfUnit v ^ k) z = (v : S) ^ k • z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, pow_succ', mul_smul]
    rfl

lemma restrictScalars_pow_apply (A : Type u) {S M : Type u} [CommRing A] [CommRing S]
    [Algebra A S] [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    (e : M ≃ₗ[S] M) (k : ℕ) (z : M) : ((e.restrictScalars A) ^ k) z = (e ^ k) z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, pow_succ', LinearEquiv.mul_apply]; rfl

lemma restrictScalars_symm_pow_apply (A : Type u) {S M : Type u} [CommRing A] [CommRing S]
    [Algebra A S] [AddCommGroup M] [Module S M] [Module A M] [IsScalarTower A S M]
    (e : M ≃ₗ[S] M) (k : ℕ) (z : M) : ((e.restrictScalars A).symm ^ k) z = (e.symm ^ k) z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', LinearEquiv.mul_apply, ih, pow_succ', LinearEquiv.mul_apply]; rfl

lemma smulOfUnit_symm_pow_apply {S M : Type u} [CommRing S] [AddCommGroup M] [Module S M]
    (v : Sˣ) (k : ℕ) (z : M) :
    ((LinearEquiv.smulOfUnit v).symm ^ k) z = ((v⁻¹ : Sˣ) : S) ^ k • z := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, pow_succ', mul_smul]
    rfl

variable (A : Type u) [CommRing A] {R0 R1 R01 S0 S1 S01 : Type u}
  [CommRing R0] [CommRing R1] [CommRing R01] [CommRing S0] [CommRing S1] [CommRing S01]
  [Algebra A R0] [Algebra A R1] [Algebra A R01] [Algebra A S0] [Algebra A S1] [Algebra A S01]
  [Algebra R0 S0] [Algebra R1 S1] [Algebra R01 S01]
  [IsScalarTower A R0 S0] [IsScalarTower A R1 S1] [IsScalarTower A R01 S01]
  [Algebra R0 R01] [Algebra R1 R01] [Algebra S0 S01] [Algebra S1 S01]
  [Algebra R0 S01] [Algebra R1 S01]
  [IsScalarTower R0 R01 S01] [IsScalarTower R0 S0 S01] [IsScalarTower R1 R01 S01]
  [IsScalarTower R1 S1 S01] [IsScalarTower A S0 S01] [IsScalarTower A S1 S01]
  (x : R0) (y : R1) [IsLocalization.Away x R01] [IsLocalization.Away y R01]
  [IsLocalization.Away (algebraMap R0 S0 x) S01] [IsLocalization.Away (algebraMap R1 S1 y) S01]

omit [IsLocalization.Away (algebraMap R1 S1 y) S01] in
lemma unitT_inv (hxy : algebraMap R0 S01 x * algebraMap R1 S01 y = 1) :
    ((unitT S0 S01 x)⁻¹ : S01ˣ) = algebraMap S1 S01 (algebraMap R1 S1 y) := by
  rw [← IsScalarTower.algebraMap_apply R1 S1 S01]
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [unitT_val, ← IsScalarTower.algebraMap_apply R0 S0 S01, hxy]

omit [IsLocalization.Away y R01] [IsLocalization.Away (algebraMap R1 S1 y) S01] in
lemma isLocalizedModule0 :
    IsLocalizedModule (Submonoid.powers x)
      ((KaehlerDifferential.map R0 R01 S0 S01).restrictScalars R0) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S0 (Submonoid.powers x)) S01 := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  infer_instance

omit [IsLocalization.Away x R01] [IsLocalization.Away (algebraMap R0 S0 x) S01] in
lemma isLocalizedModule1 :
    IsLocalizedModule (Submonoid.powers y)
      ((KaehlerDifferential.map R1 R01 S1 S01).restrictScalars R1) := by
  haveI : IsLocalization (Algebra.algebraMapSubmonoid S1 (Submonoid.powers y)) S01 := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  infer_instance

/-- **The chart module of relative differentials** `Ω_{𝒴/𝒳}` on `ℙ¹_A`. -/
noncomputable def chartModule (hxy : algebraMap R0 S01 x * algebraMap R1 S01 y = 1) :
    ProjectiveLine.ChartModule A where
  M0 := ModuleCat.of A Ω[S0⁄R0]
  M1 := ModuleCat.of A Ω[S1⁄R1]
  M01 := ModuleCat.of A Ω[S01⁄R01]
  x0 := mulLin A R0 (algebraMap R0 S0 x)
  x1 := mulLin A R1 (algebraMap R1 S1 y)
  t := (LinearEquiv.smulOfUnit (unitT S0 S01 x)).restrictScalars A
  r0 := (KaehlerDifferential.map R0 R01 S0 S01).restrictScalars A
  r1 := (KaehlerDifferential.map R1 R01 S1 S01).restrictScalars A
  r0_x0 m := by
    change KaehlerDifferential.map R0 R01 S0 S01 (algebraMap R0 S0 x • m) =
      (unitT S0 S01 x : S01) • KaehlerDifferential.map R0 R01 S0 S01 m
    rw [map_smul, unitT_val, ← IsScalarTower.algebraMap_apply R0 S0 S01, algebraMap_smul,
      algebraMap_smul]
  r1_x1 m := by
    change KaehlerDifferential.map R1 R01 S1 S01 (algebraMap R1 S1 y • m) =
      ((unitT S0 S01 x)⁻¹ : S01ˣ) • KaehlerDifferential.map R1 R01 S1 S01 m
    rw [map_smul, Units.smul_def, unitT_inv (S0 := S0) (S1 := S1) x y hxy,
      ← IsScalarTower.algebraMap_apply R1 S1 S01, algebraMap_smul, algebraMap_smul]
  exists_r0 z := by
    haveI := isLocalizedModule0 (R01 := R01) (S0 := S0) (S01 := S01) x
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers x)
      ((KaehlerDifferential.map R0 R01 S0 S01).restrictScalars R0) z
    refine ⟨m, k, ?_⟩
    rw [restrictScalars_pow_apply, smulOfUnit_pow_apply, unitT_val,
      ← IsScalarTower.algebraMap_apply, ← map_pow,
      algebraMap_smul]
    exact hm
  ker_r0 m hm := by
    haveI := isLocalizedModule0 (R01 := R01) (S0 := S0) (S01 := S01) x
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers x)
      (f := (KaehlerDifferential.map R0 R01 S0 S01).restrictScalars R0) (x₁ := m) (x₂ := 0)
      (hm.trans (map_zero _).symm)
    refine ⟨k, ?_⟩
    change (mulLin A R0 (algebraMap R0 S0 x) ^ k) m = 0
    rw [mulLin_pow_apply, ← map_pow, algebraMap_smul]
    simpa [Submonoid.smul_def] using hk
  exists_r1 z := by
    haveI := isLocalizedModule1 (R01 := R01) (S1 := S1) (S01 := S01) y
    obtain ⟨⟨m, ⟨_, k, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers y)
      ((KaehlerDifferential.map R1 R01 S1 S01).restrictScalars R1) z
    refine ⟨m, k, ?_⟩
    rw [restrictScalars_symm_pow_apply, smulOfUnit_symm_pow_apply,
      unitT_inv (S0 := S0) (S1 := S1) x y hxy, ← IsScalarTower.algebraMap_apply,
      ← map_pow, algebraMap_smul]
    exact hm
  ker_r1 m hm := by
    haveI := isLocalizedModule1 (R01 := R01) (S1 := S1) (S01 := S01) y
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers y)
      (f := (KaehlerDifferential.map R1 R01 S1 S01).restrictScalars R1) (x₁ := m) (x₂ := 0)
      (hm.trans (map_zero _).symm)
    refine ⟨k, ?_⟩
    change (mulLin A R1 (algebraMap R1 S1 y) ^ k) m = 0
    rw [mulLin_pow_apply, ← map_pow, algebraMap_smul]
    simpa [Submonoid.smul_def] using hk

variable (hxy : algebraMap R0 S01 x * algebraMap R1 S01 y = 1)

set_option hygiene false in
local notation "CM" => chartModule (R0 := R0) (R1 := R1) (R01 := R01) (S0 := S0) (S1 := S1)
  (S01 := S01) A x y hxy

/-- The `A[X]`-module structure of the first chart is multiplication through `p : A[X] → S₀`
(`X ↦ x`). -/
lemma aeval_x0_apply (p : A[X] →+* S0)
    (hpX : p X = algebraMap R0 S0 x) (hpC : ∀ a, p (C a) = algebraMap A S0 a) (q : A[X])
    (ω : Ω[S0⁄R0]) :
    Polynomial.aeval (CM).x0 q ω = p q • ω := by
  induction q using Polynomial.induction_on generalizing ω with
  | C a =>
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, hpC, algebraMap_smul]
    rfl
  | add q r hq hr =>
    rw [map_add, LinearMap.add_apply, hq, hr, map_add, add_smul]
    rfl
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X, map_mul p, hpX,
      mul_smul, ← h]
    rfl

/-- **The chart module of differentials is coherent on the first chart** if `S₀` is finite over
`A[X]` (through `p`, `X ↦ x`) and `Ω[S₀⁄R₀]` is finite over `S₀`. -/
theorem finite_x0 (p : A[X] →+* S0)
    (hpX : p X = algebraMap R0 S0 x) (hpC : ∀ a, p (C a) = algebraMap A S0 a)
    (hfin : letI := p.toAlgebra; Module.Finite A[X] S0) [Module.Finite S0 Ω[S0⁄R0]] :
    Module.Finite A[X] (Module.AEval' (CM).x0) := by
  letI := p.toAlgebra
  letI : Module A[X] Ω[S0⁄R0] := Module.compHom Ω[S0⁄R0] p
  haveI : IsScalarTower A[X] S0 Ω[S0⁄R0] := ⟨fun q s ω ↦ by
    change (p q * s) • ω = p q • s • ω
    rw [mul_smul]⟩
  haveI : Module.Finite A[X] Ω[S0⁄R0] := Module.Finite.trans S0 Ω[S0⁄R0]
  let f : Ω[S0⁄R0] →ₗ[A[X]] Module.AEval' (CM).x0 :=
    { toFun := fun ω ↦ Module.AEval'.of (CM).x0 ω
      map_add' := fun ω ω' ↦ map_add _ ω ω'
      map_smul' := fun q ω ↦ by
        change Module.AEval'.of _ (p q • ω) = q • Module.AEval'.of _ ω
        rw [← aeval_x0_apply (R01 := R01) (S1 := S1) A x y hxy p hpX hpC]
        rfl }
  exact Module.Finite.of_surjective f fun v ↦
    ⟨(Module.AEval'.of (CM).x0).symm v, by
      change Module.AEval'.of _ ((Module.AEval'.of _).symm v) = v
      rw [LinearEquiv.apply_symm_apply]⟩

/-- The `A[X]`-module structure of the second chart is multiplication through `p : A[X] → S₁`
(`X ↦ y`). -/
lemma aeval_x1_apply (p : A[X] →+* S1)
    (hpX : p X = algebraMap R1 S1 y) (hpC : ∀ a, p (C a) = algebraMap A S1 a) (q : A[X])
    (ω : Ω[S1⁄R1]) :
    Polynomial.aeval (CM).x1 q ω = p q • ω := by
  induction q using Polynomial.induction_on generalizing ω with
  | C a =>
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, hpC, algebraMap_smul]
    rfl
  | add q r hq hr =>
    rw [map_add, LinearMap.add_apply, hq, hr, map_add, add_smul]
    rfl
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X, map_mul p, hpX,
      mul_smul, ← h]
    rfl

/-- **The chart module of differentials is coherent on the second chart** if `S₁` is finite over
`A[X]` (through `p`, `X ↦ y`) and `Ω[S₁⁄R₁]` is finite over `S₁`. -/
theorem finite_x1 (p : A[X] →+* S1)
    (hpX : p X = algebraMap R1 S1 y) (hpC : ∀ a, p (C a) = algebraMap A S1 a)
    (hfin : letI := p.toAlgebra; Module.Finite A[X] S1) [Module.Finite S1 Ω[S1⁄R1]] :
    Module.Finite A[X] (Module.AEval' (CM).x1) := by
  letI := p.toAlgebra
  letI : Module A[X] Ω[S1⁄R1] := Module.compHom Ω[S1⁄R1] p
  haveI : IsScalarTower A[X] S1 Ω[S1⁄R1] := ⟨fun q s ω ↦ by
    change (p q * s) • ω = p q • s • ω
    rw [mul_smul]⟩
  haveI : Module.Finite A[X] Ω[S1⁄R1] := Module.Finite.trans S1 Ω[S1⁄R1]
  let f : Ω[S1⁄R1] →ₗ[A[X]] Module.AEval' (CM).x1 :=
    { toFun := fun ω ↦ Module.AEval'.of (CM).x1 ω
      map_add' := fun ω ω' ↦ map_add _ ω ω'
      map_smul' := fun q ω ↦ by
        change Module.AEval'.of _ (p q • ω) = q • Module.AEval'.of _ ω
        rw [← aeval_x1_apply (R01 := R01) (S0 := S0) A x y hxy p hpX hpC]
        rfl }
  exact Module.Finite.of_surjective f fun v ↦
    ⟨(Module.AEval'.of (CM).x1).symm v, by
      change Module.AEval'.of _ ((Module.AEval'.of _).symm v) = v
      rw [LinearEquiv.apply_symm_apply]⟩

end KaehlerChart
