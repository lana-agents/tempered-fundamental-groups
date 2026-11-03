/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateS6Datum

/-!
# Maps of covers from maps of their normalisations over `T1` (generic; MR12 I3)

For covers `C`, `C'` (`TateS6.CovData` over two-chart rings `D` with `D.R1` a domain and `K` its
fraction field) and a ring map `g : C.B₁ → C'.B₁` of the normalisations of `D.R1` that is the
identity on `D.R1`:

* `TateS6.CovData.injective_of_map1`: `g` is injective (its kernel contracts to `0` in `D.R1`
  and `C.B₁` is integral over `D.R1`);
* **`TateS6.CovData.ofMap1`**: the `K`-algebra map `C.L → C'.L` extending `g` (`C.L` is the
  fraction field of `C.B₁`);
* **`TateS6.CovData.map1_ofMap1`**: `map1 (ofMap1 g) = g`.

This is the step "chart algebra map of the normalisations → map of covers" of I3 surjectivity.
-/

universe u

namespace SemistableReduction

namespace TateS6

noncomputable section

namespace CovData

variable {A : Type u} [CommRing A] {K : Type u} [Field K] {D : ProjectiveLine.TwoChartRings A}
  {Rn Rc : Type u} [CommRing Rn] [CommRing Rc] [Algebra D.R1 K] [Algebra Rn K] [Algebra Rc K]
  [Algebra D.R0 Rc] {toN : D.R1 → Rn} {dT : D.R1} {c0 : D.R0} {ϖ1 : D.R1} {ϖ0 : D.R0}
  {I0 : Ideal D.R0} {q e : ℕ} {C C' : CovData K D Rn Rc toN dT c0 ϖ1 ϖ0 I0 q e}
  [IsDomain D.R1] [IsFractionRing D.R1 K]

variable (g : C.B₁ →+* C'.B₁)
  (hg : ∀ a, g (algebraMap D.R1 C.B₁ a) = algebraMap D.R1 C'.B₁ a)

include hg in
/-- A map of normalisations over `D.R1` is injective. -/
lemma injective_of_map1 : Function.Injective g := by
  haveI : Algebra.IsIntegral D.R1 C.B₁ := IsIntegralClosure.isIntegral_algebra D.R1 C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  rw [injective_iff_map_eq_zero]
  intro b hb
  have hk : RingHom.ker g = ⊥ := by
    refine Ideal.eq_bot_of_comap_eq_bot (R := D.R1) ?_
    refine eq_bot_iff.2 fun a ha ↦ ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, hg] at ha
    have h1 : algebraMap D.R1 C'.L a = 0 := by
      rw [IsScalarTower.algebraMap_apply D.R1 C'.B₁ C'.L, ha, map_zero]
    rw [IsScalarTower.algebraMap_apply D.R1 K C'.L] at h1
    have h2 := (FaithfulSMul.algebraMap_injective K C'.L) (h1.trans (map_zero _).symm)
    exact (Submodule.mem_bot _).2 ((IsFractionRing.injective D.R1 K) (h2.trans (map_zero _).symm))
  rw [← RingHom.mem_ker, hk] at hb
  exact hb

/-- `C.L` is the fraction field of `C.B₁`. -/
lemma isFractionRing_B₁ : IsFractionRing C.B₁ C.L := by
  haveI : Algebra.IsAlgebraic K C.L := Algebra.IsAlgebraic.of_finite K C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  exact IsIntegralClosure.isFractionRing_of_finite_extension D.R1 K C.L C.B₁

/-- **The map of covers extending a map of normalisations over `D.R1`.** -/
def ofMap1 : C.L →ₐ[K] C'.L :=
  haveI := isFractionRing_B₁ (C := C)
  haveI : Algebra.IsIntegral D.R1 C.B₁ := IsIntegralClosure.isIntegral_algebra D.R1 C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  { IsFractionRing.lift (K := C.L) (g := (algebraMap C'.B₁ C'.L).comp g)
      ((IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L).comp
        (injective_of_map1 g hg)) with
    commutes' := fun k ↦ by
      have h : ((IsFractionRing.lift (K := C.L) (g := (algebraMap C'.B₁ C'.L).comp g)
          ((IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L).comp
            (injective_of_map1 g hg))).comp (algebraMap K C.L)) = algebraMap K C'.L := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors D.R1) (RingHom.ext fun a ↦ ?_)
        simp only [RingHom.comp_apply]
        rw [← IsScalarTower.algebraMap_apply D.R1 K C.L,
          IsScalarTower.algebraMap_apply D.R1 C.B₁ C.L, IsFractionRing.lift_algebraMap,
          RingHom.comp_apply, hg, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
      exact RingHom.congr_fun h k }

include hg in
lemma ofMap1_algebraMap (b : C.B₁) :
    ofMap1 g hg (algebraMap C.B₁ C.L b) = algebraMap C'.B₁ C'.L (g b) := by
  haveI := isFractionRing_B₁ (C := C)
  haveI : Algebra.IsIntegral D.R1 C.B₁ := IsIntegralClosure.isIntegral_algebra D.R1 C.L
  haveI : IsDomain C.B₁ := (IsIntegralClosure.algebraMap_injective C.B₁ D.R1 C.L).isDomain _
  exact IsFractionRing.lift_algebraMap (K := C.L) (g := (algebraMap C'.B₁ C'.L).comp g)
    ((IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L).comp
    (injective_of_map1 g hg)) b

include hg in
/-- **`map1` of the extension is the given map.** -/
lemma map1_ofMap1 (b : C.B₁) : map1 (ofMap1 g hg) b = g b :=
  IsIntegralClosure.algebraMap_injective C'.B₁ D.R1 C'.L (by
    rw [algebraMap_map1, ofMap1_algebraMap])

end CovData

end

end TateS6

end SemistableReduction
