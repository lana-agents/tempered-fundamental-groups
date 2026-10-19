/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.ChartAlgebraRingHom
import TemperedFundamentalGroups.SemistableReduction.ReducedFibreNormal

/-!
# The algebraized covering is the normalised model (Blueprint §12.8, M2.5, step (e))

Let `(M, B)` be a chart algebra on `ℙ¹_A`, coherent on the first chart. Then

* the `A[X]`-module structure of `M₀` is multiplication by `polyHom0` (`AlgStr.toRing0_aeval`),
  so
  `B₀` is a finite `A[X]`-algebra (`AlgStr.finite_polyHom0`);
* **`AlgStr.isIntegralClosure_ring0`**: if `A[X] → B₀` factors through a ring `T` (the chart ring of
  a base model), `ϖ ∈ A` is a nonzerodivisor of `B₀` and `B₀ ⧸ (ϖ)` is reduced, then `B₀` is the
  integral closure of `T` in `B₀[1/ϖ]` (`isIntegralClosure_of_away`);
* `AlgStr.isIntegralClosure_ring0_of_isHom`: the same for `T = D.R0` and a morphism of chart
  algebras `D.algStr → B` from two-chart rings `D` (the structure map `𝒴 → 𝒳`);
* `TwoChartTower.isIntegralClosure_shift0`: for a flat algebraization of a tower of two-chart rings
  (`systemShift` with `I = (ϖ)`), the reducedness hypothesis is reducedness of the level-`0` ring
  `(E 0).R0` (`quotEquivShift0`), regularity of `ϖ` comes from flatness over `A[X]`
  (`const0_mem_nonZeroDivisors`).
Second-chart versions: `isIntegralClosure_ring1`, `isIntegralClosure_ring1_of_isHom`,
`isIntegralClosure_shift1`.
-/

universe u

open Polynomial

namespace ProjectiveLine

namespace ChartModule

namespace AlgStr

variable {A : Type u} [CommRing A] {M : ChartModule A} (B : AlgStr M)

/-- The `A[X]`-module structure of `M₀` is multiplication by `polyHom0`. -/
lemma toRing0_aeval (p : A[X]) (m : B.Ring0) :
    B.toRing0 (Polynomial.aeval M.x0 p (B.ofRing0 m)) = B.polyHom0 p * m := by
  induction p using Polynomial.induction_on generalizing m with
  | C a =>
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, toRing0_smul]
    simp [polyHom0]
    rfl
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, map_add, add_mul, ← hp, ← hq]
    rfl
  | monomial n a h =>
    have hx : M.x0 (B.ofRing0 m) = B.ofRing0 (B.X0 * m) := B.x0_eq_mul m
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X, hx, h]
    simp only [polyHom0, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    ring

lemma toRing1_aeval (p : A[X]) (m : B.Ring1) :
    B.toRing1 (Polynomial.aeval M.x1 p (B.ofRing1 m)) = B.polyHom1 p * m := by
  induction p using Polynomial.induction_on generalizing m with
  | C a =>
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply, toRing1_smul]
    simp [polyHom1]
    rfl
  | add p q hp hq =>
    rw [map_add, LinearMap.add_apply, map_add, add_mul, ← hp, ← hq]
    rfl
  | monomial n a h =>
    have hx : M.x1 (B.ofRing1 m) = B.ofRing1 (B.X1 * m) := B.x1_eq_mul m
    rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X, hx, h]
    simp only [polyHom1, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_mul, Polynomial.eval₂_C,
      Polynomial.eval₂_X_pow, Polynomial.eval₂_X]
    ring

/-- `B₀` is a finite `A[X]`-algebra (through `polyHom0`) if `M₀` is a finite `A[X]`-module. -/
theorem finite_polyHom0 [Module.Finite A[X] (Module.AEval' M.x0)] :
    letI := B.polyHom0.toAlgebra
    Module.Finite A[X] B.Ring0 := by
  letI := B.polyHom0.toAlgebra
  let f : Module.AEval' M.x0 →ₗ[A[X]] B.Ring0 :=
    { toFun := fun v ↦ B.toRing0 ((Module.AEval'.of M.x0).symm v)
      map_add' := fun v w ↦ by rw [map_add]; rfl
      map_smul' := fun p v ↦ by
        rw [Module.AEval.of_symm_smul, RingHom.id_apply, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        exact B.toRing0_aeval p _ }
  exact Module.Finite.of_surjective f fun m ↦ ⟨Module.AEval'.of M.x0 (B.ofRing0 m), by
    change B.toRing0 ((Module.AEval'.of M.x0).symm (Module.AEval'.of M.x0 (B.ofRing0 m))) = m
    rw [LinearEquiv.symm_apply_apply]
    rfl⟩

/-- `B₁` is a finite `A[X]`-algebra (through `polyHom1`) if `M₁` is a finite `A[X]`-module. -/
theorem finite_polyHom1 [Module.Finite A[X] (Module.AEval' M.x1)] :
    letI := B.polyHom1.toAlgebra
    Module.Finite A[X] B.Ring1 := by
  letI := B.polyHom1.toAlgebra
  let f : Module.AEval' M.x1 →ₗ[A[X]] B.Ring1 :=
    { toFun := fun v ↦ B.toRing1 ((Module.AEval'.of M.x1).symm v)
      map_add' := fun v w ↦ by rw [map_add]; rfl
      map_smul' := fun p v ↦ by
        rw [Module.AEval.of_symm_smul, RingHom.id_apply, Algebra.smul_def,
          RingHom.algebraMap_toAlgebra]
        exact B.toRing1_aeval p _ }
  exact Module.Finite.of_surjective f fun m ↦ ⟨Module.AEval'.of M.x1 (B.ofRing1 m), by
    change B.toRing1 ((Module.AEval'.of M.x1).symm (Module.AEval'.of M.x1 (B.ofRing1 m))) = m
    rw [LinearEquiv.symm_apply_apply]
    rfl⟩

/-- A ring through which `polyHom` factors makes a finite `A[X]`-algebra integral. -/
lemma isIntegral_of_factor {R T : Type u} [CommRing R] [CommRing T] [Algebra T R]
    (φ : A[X] →+* R) (g : A[X] →+* T) (hg : (algebraMap T R).comp g = φ)
    (hfin : letI := φ.toAlgebra; Module.Finite A[X] R) : Algebra.IsIntegral T R := by
  letI := φ.toAlgebra
  letI := g.toAlgebra
  haveI : IsScalarTower A[X] T R := IsScalarTower.of_algebraMap_eq' hg.symm
  haveI : Algebra.IsIntegral A[X] R := Algebra.IsIntegral.of_finite A[X] R
  exact ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := A[X]) x).tower_top⟩

variable {ϖ : A}

/-- **The normalised model, first chart**: `B₀` is the integral closure of `T` in `B₀[1/ϖ]`. -/
theorem isIntegralClosure_ring0 [Module.Finite A[X] (Module.AEval' M.x0)] {T L : Type u}
    [CommRing T] [CommRing L] [Algebra T B.Ring0] [Algebra B.Ring0 L] [Algebra T L]
    [IsScalarTower T B.Ring0 L] [IsLocalization.Away (B.const0 ϖ) L] (g : A[X] →+* T)
    (hg : (algebraMap T B.Ring0).comp g = B.polyHom0) (hϖ : B.const0 ϖ ∈ nonZeroDivisors B.Ring0)
    (hred : IsReduced (B.Ring0 ⧸ Ideal.span {B.const0 ϖ})) : IsIntegralClosure B.Ring0 T L := by
  haveI := isIntegral_of_factor B.polyHom0 g hg B.finite_polyHom0
  exact SemistableReduction.isIntegralClosure_of_away (B.const0 ϖ) hϖ hred

/-- **The normalised model, second chart**: `B₁` is the integral closure of `T` in `B₁[1/ϖ]`. -/
theorem isIntegralClosure_ring1 [Module.Finite A[X] (Module.AEval' M.x1)] {T L : Type u}
    [CommRing T] [CommRing L] [Algebra T B.Ring1] [Algebra B.Ring1 L] [Algebra T L]
    [IsScalarTower T B.Ring1 L] [IsLocalization.Away (B.const1 ϖ) L] (g : A[X] →+* T)
    (hg : (algebraMap T B.Ring1).comp g = B.polyHom1) (hϖ : B.const1 ϖ ∈ nonZeroDivisors B.Ring1)
    (hred : IsReduced (B.Ring1 ⧸ Ideal.span {B.const1 ϖ})) : IsIntegralClosure B.Ring1 T L := by
  haveI := isIntegral_of_factor B.polyHom1 g hg B.finite_polyHom1
  exact SemistableReduction.isIntegralClosure_of_away (B.const1 ϖ) hϖ hred

/-- The `D.R0`-algebra structure of `B₀` given by a morphism of chart algebras `D.algStr → B`. -/
noncomputable abbrev algR0 {D : TwoChartRings A} {φ : Hom D.chartModule M}
    (h : D.algStr.IsHom B φ) : Algebra D.R0 B.Ring0 :=
  (h.ringHom0.comp (TwoChartRings.ring0Equiv D).symm.toRingHom).toAlgebra

/-- The `D.R1`-algebra structure of `B₁` given by a morphism of chart algebras `D.algStr → B`. -/
noncomputable abbrev algR1 {D : TwoChartRings A} {φ : Hom D.chartModule M}
    (h : D.algStr.IsHom B φ) : Algebra D.R1 B.Ring1 :=
  (h.ringHom1.comp (TwoChartRings.ring1Equiv D).symm.toRingHom).toAlgebra

lemma ring0Equiv_symm_aeval (D : TwoChartRings A) (p : A[X]) :
    (TwoChartRings.ring0Equiv D).symm (Polynomial.aeval D.x p) = D.algStr.polyHom0 p := by
  apply (TwoChartRings.ring0Equiv D).injective
  have := Polynomial.hom_eval₂ p D.algStr.const0
    ((TwoChartRings.ring0Equiv D) : D.algStr.Ring0 →+* D.R0) D.algStr.X0
  rw [RingEquiv.apply_symm_apply, polyHom0, Polynomial.coe_eval₂RingHom]
  refine Eq.trans ?_ this.symm
  rw [Polynomial.aeval_def]
  congr 1
  · ext a
    exact ((TwoChartRings.ring0Equiv_const0 D a)).symm
  · exact (TwoChartRings.ring0Equiv_X0 D).symm

lemma ring1Equiv_symm_aeval (D : TwoChartRings A) (p : A[X]) :
    (TwoChartRings.ring1Equiv D).symm (Polynomial.aeval D.y p) = D.algStr.polyHom1 p := by
  apply (TwoChartRings.ring1Equiv D).injective
  have := Polynomial.hom_eval₂ p D.algStr.const1
    ((TwoChartRings.ring1Equiv D) : D.algStr.Ring1 →+* D.R1) D.algStr.X1
  rw [RingEquiv.apply_symm_apply, polyHom1, Polynomial.coe_eval₂RingHom]
  refine Eq.trans ?_ this.symm
  rw [Polynomial.aeval_def]
  congr 1
  · ext a
    exact ((TwoChartRings.ring1Equiv_const1 D a)).symm
  · exact (TwoChartRings.ring1Equiv_X1 D).symm

/-- **The normalised model over two-chart rings, first chart**: for a morphism of chart algebras
`D.algStr → B` (the structure map `𝒴 → 𝒳`), `B₀` is the integral closure of `D.R0` in `B₀[1/ϖ]`. -/
theorem isIntegralClosure_ring0_of_isHom [Module.Finite A[X] (Module.AEval' M.x0)]
    {D : TwoChartRings A} {φ : Hom D.chartModule M} (h : D.algStr.IsHom B φ) {L : Type u}
    [CommRing L] [Algebra B.Ring0 L] [IsLocalization.Away (B.const0 ϖ) L]
    (hϖ : B.const0 ϖ ∈ nonZeroDivisors B.Ring0)
    (hred : IsReduced (B.Ring0 ⧸ Ideal.span {B.const0 ϖ})) :
    letI := B.algR0 h
    letI : Algebra D.R0 L := ((algebraMap B.Ring0 L).comp (algebraMap D.R0 B.Ring0)).toAlgebra
    IsIntegralClosure B.Ring0 D.R0 L := by
  letI := B.algR0 h
  letI : Algebra D.R0 L := ((algebraMap B.Ring0 L).comp (algebraMap D.R0 B.Ring0)).toAlgebra
  haveI : IsScalarTower D.R0 B.Ring0 L := IsScalarTower.of_algebraMap_eq' rfl
  refine B.isIntegralClosure_ring0 (Polynomial.aeval D.x).toRingHom ?_ hϖ hred
  ext p
  · change h.ringHom0 ((TwoChartRings.ring0Equiv D).symm (Polynomial.aeval D.x (C _))) = _
    rw [ring0Equiv_symm_aeval, h.ringHom0_polyHom0]
    rfl
  · change h.ringHom0 ((TwoChartRings.ring0Equiv D).symm (Polynomial.aeval D.x X)) = _
    rw [ring0Equiv_symm_aeval, h.ringHom0_polyHom0]

/-- **The normalised model over two-chart rings, second chart.** -/
theorem isIntegralClosure_ring1_of_isHom [Module.Finite A[X] (Module.AEval' M.x1)]
    {D : TwoChartRings A} {φ : Hom D.chartModule M} (h : D.algStr.IsHom B φ) {L : Type u}
    [CommRing L] [Algebra B.Ring1 L] [IsLocalization.Away (B.const1 ϖ) L]
    (hϖ : B.const1 ϖ ∈ nonZeroDivisors B.Ring1)
    (hred : IsReduced (B.Ring1 ⧸ Ideal.span {B.const1 ϖ})) :
    letI := B.algR1 h
    letI : Algebra D.R1 L := ((algebraMap B.Ring1 L).comp (algebraMap D.R1 B.Ring1)).toAlgebra
    IsIntegralClosure B.Ring1 D.R1 L := by
  letI := B.algR1 h
  letI : Algebra D.R1 L := ((algebraMap B.Ring1 L).comp (algebraMap D.R1 B.Ring1)).toAlgebra
  haveI : IsScalarTower D.R1 B.Ring1 L := IsScalarTower.of_algebraMap_eq' rfl
  refine B.isIntegralClosure_ring1 (Polynomial.aeval D.y).toRingHom ?_ hϖ hred
  ext p
  · change h.ringHom1 ((TwoChartRings.ring1Equiv D).symm (Polynomial.aeval D.y (C _))) = _
    rw [ring1Equiv_symm_aeval, h.ringHom1_polyHom1]
    rfl
  · change h.ringHom1 ((TwoChartRings.ring1Equiv D).symm (Polynomial.aeval D.y X)) = _
    rw [ring1Equiv_symm_aeval, h.ringHom1_polyHom1]

/-- Constants regular on a flat chart algebra, second chart (cf. `const0_mem_nonZeroDivisors`). -/
lemma const1_mem_nonZeroDivisors [Module.Flat A[X] (Module.AEval' M.x1)] {a : A}
    (ha : (Polynomial.C a : A[X]) ∈ nonZeroDivisors A[X]) :
    B.const1 a ∈ nonZeroDivisors B.Ring1 := by
  have hreg : IsSMulRegular (Module.AEval' M.x1) (Polynomial.C a) :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors ha
  refine mem_nonZeroDivisors_iff_right.2 fun m hm ↦ ?_
  rw [mul_comm] at hm
  have h1 : a • B.ofRing1 m = 0 := by
    have : B.toRing1 (a • B.ofRing1 m) = B.const1 a * m := B.toRing1_smul a (B.ofRing1 m)
    rw [hm] at this
    exact this
  have h2 : (Polynomial.C a : A[X]) • Module.AEval'.of M.x1 (B.ofRing1 m) =
      (Polynomial.C a : A[X]) • 0 := by
    rw [smul_zero, ← Polynomial.algebraMap_eq, algebraMap_smul, ← map_smul, h1, map_zero]
  exact (Module.AEval'.of M.x1).injective ((hreg h2).trans (map_zero _).symm)

end AlgStr

end ChartModule

end ProjectiveLine

namespace SemistableReduction

namespace TwoChartTower

open ProjectiveLine ProjectiveLine.ChartModule

variable {A : Type u} [CommRing A] {ϖ : A} {E : ℕ → TwoChartRings A}
  {e : ∀ n, TwoChartMap (E (n + 1)) (E n)}
  {he0 : ∀ n, Function.Surjective (e n).f0} {he1 : ∀ n, Function.Surjective (e n).f1}
  {hker0 : ∀ n, RingHom.ker (e n).f0 =
    (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap A (E (n + 1)).R0)}
  {hker1 : ∀ n, RingHom.ker (e n).f1 =
    (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap A (E (n + 1)).R1)}
  {hkill0 : ∀ n, (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap A (E n).R0) = ⊥}
  {hkill1 : ∀ n, (Ideal.span {ϖ} ^ (n + 1)).map (algebraMap A (E n).R1) = ⊥}
  {hfin0 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x0)}
  {hfin1 : ∀ n, Module.Finite A[X] (Module.AEval' (E n).chartModule.x1)}
  {N : ChartModule A} {B : AlgStr N}
  {α : ∀ n, Hom N ((systemShift (Ideal.span {ϖ}) E e he0 he1 hker0 hker1 hkill0 hkill1
    hfin0 hfin1).M n)}

/-- The special fibre `B₀ ⧸ (ϖ)` of the algebraization is the level-`0` ring. -/
noncomputable def specialFibreEquiv0 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemShift (Ideal.span {ϖ}) E e he0 he1 hker0 hker1 hkill0 hkill1
      hfin0 hfin1).alg n) (α n)) :
    B.Ring0 ⧸ Ideal.span {B.const0 ϖ} ≃+* (E 0).R0 :=
  (Ideal.quotEquivOfEq (by rw [zero_add, pow_one, Ideal.map_span, Set.image_singleton])).trans
    (quotEquivShift0 hα hB 0)

/-- The special fibre `B₁ ⧸ (ϖ)` of the algebraization is the level-`0` ring. -/
noncomputable def specialFibreEquiv1 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemShift (Ideal.span {ϖ}) E e he0 he1 hker0 hker1 hkill0 hkill1
      hfin0 hfin1).alg n) (α n)) :
    B.Ring1 ⧸ Ideal.span {B.const1 ϖ} ≃+* (E 0).R1 :=
  (Ideal.quotEquivOfEq (by rw [zero_add, pow_one, Ideal.map_span, Set.image_singleton])).trans
    (quotEquivShift1 hα hB 0)

/-- **M2.5 (e), first chart, for a flat algebraization of a tower of two-chart rings**: if the
level-`0` ring is reduced, `ϖ` is regular on `A[X]` and `D.algStr → B` is a morphism of chart
algebras (the structure map to the base model), then `B₀` is the integral closure of `D.R0` in
`B₀[1/ϖ]`: the algebraized covering is the normalised model. -/
theorem isIntegralClosure_shift0 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemShift (Ideal.span {ϖ}) E e he0 he1 hker0 hker1 hkill0 hkill1
      hfin0 hfin1).alg n) (α n))
    [Module.Finite A[X] (Module.AEval' N.x0)] [Module.Flat A[X] (Module.AEval' N.x0)]
    (hϖ : (Polynomial.C ϖ : A[X]) ∈ nonZeroDivisors A[X]) [IsReduced (E 0).R0]
    {D : TwoChartRings A} {φ : Hom D.chartModule N} (h : D.algStr.IsHom B φ) {L : Type u}
    [CommRing L] [Algebra B.Ring0 L] [IsLocalization.Away (B.const0 ϖ) L] :
    letI := B.algR0 h
    letI : Algebra D.R0 L := ((algebraMap B.Ring0 L).comp (algebraMap D.R0 B.Ring0)).toAlgebra
    IsIntegralClosure B.Ring0 D.R0 L :=
  B.isIntegralClosure_ring0_of_isHom h (B.const0_mem_nonZeroDivisors hϖ)
    (isReduced_of_injective (specialFibreEquiv0 hα hB).toRingHom
      (specialFibreEquiv0 hα hB).injective)

/-- **M2.5 (e), second chart, for a flat algebraization of a tower of two-chart rings.** -/
theorem isIntegralClosure_shift1 (hα : ∀ n, Function.Surjective (α n).f0 ∧
      Function.Surjective (α n).f1 ∧ LinearMap.ker (α n).f0 = Ideal.span {ϖ} ^ n • ⊤ ∧
      LinearMap.ker (α n).f1 = Ideal.span {ϖ} ^ n • ⊤)
    (hB : ∀ n, B.IsHom ((systemShift (Ideal.span {ϖ}) E e he0 he1 hker0 hker1 hkill0 hkill1
      hfin0 hfin1).alg n) (α n))
    [Module.Finite A[X] (Module.AEval' N.x1)] [Module.Flat A[X] (Module.AEval' N.x1)]
    (hϖ : (Polynomial.C ϖ : A[X]) ∈ nonZeroDivisors A[X]) [IsReduced (E 0).R1]
    {D : TwoChartRings A} {φ : Hom D.chartModule N} (h : D.algStr.IsHom B φ) {L : Type u}
    [CommRing L] [Algebra B.Ring1 L] [IsLocalization.Away (B.const1 ϖ) L] :
    letI := B.algR1 h
    letI : Algebra D.R1 L := ((algebraMap B.Ring1 L).comp (algebraMap D.R1 B.Ring1)).toAlgebra
    IsIntegralClosure B.Ring1 D.R1 L :=
  B.isIntegralClosure_ring1_of_isHom h (B.const1_mem_nonZeroDivisors hϖ)
    (isReduced_of_injective (specialFibreEquiv1 hα hB).toRingHom
      (specialFibreEquiv1 hα hB).injective)

end TwoChartTower

end SemistableReduction
