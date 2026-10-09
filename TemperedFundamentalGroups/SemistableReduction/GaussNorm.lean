/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.GaussStability
import TemperedFundamentalGroups.SemistableReduction.NormFormula

/-!
# The norm formula over a Gauss point

Blueprint §9.9, W7 layer S2 (Gauss-point form). `C` algebraically closed of characteristic `0`
with `‖p‖ < 1`, `w = w_{a,r}` a Gauss valuation of `C(X)` (`r = ‖c‖`) and `F' / C(X)` finite
separable. Then

* `factorEquiv`: the factors of the minimal polynomial over the completion are the extensions
  `w'` (B3); `natDegree_eq_ramificationIdx_mul_inertiaDeg`: the local degree
  `[\hat F'_{w'} : \hat F_w]` of every extension is `e(w') f(w')` (W4 and `e · f ≤ [L : K]`
  termwise);
* **`gaussRat_norm_eq_prod`**: `w(N_{F'/C(X)} y) = ∏_{w' ∣ w} w'(y) ^ (e(w') f(w'))` (with
  `e = 1`, `GaussFibre.ramificationIdx_eq_one` for `w_{0,1}`).

Along a segment of Gauss points `w_{0,s}` the left side is monomial in `s` as long as `N y` has
no zero or pole of absolute value in the segment (`AnnulusUnit.isMonomialOn_of_roots`).
-/

open Polynomial NNReal

namespace SemistableReduction

open FundamentalInequality

namespace GaussStability

open LocalGlobal

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1) {a : C} {r : ℝ≥0ˣ} {c : C}
  (hc : NormedField.valuation c = (r : ℝ≥0))
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']
  [Algebra.IsSeparable (RatFunc C) F']

instance : Fact (DenseRange (@algebraMap (GaussField a r)
    (UniformSpace.Completion (GaussField a r)) _ _ NormedAlgebra.toAlgebra)) :=
  ⟨UniformSpace.Completion.denseRange_coe⟩

omit [IsAlgClosed C] [CharZero C] in
/-- The norm of `N_{F'/C(X)}(y)` in the Gauss norm, as a product over the factors of the
minimal polynomial over the completion, with exponents the local degrees. -/
lemma nnnorm_norm_eq_prod_factor (y : F') :
    gaussRat (NormedField.valuation (K := C)) a r (Algebra.norm (RatFunc C) y) =
      ∏ g : Factor (GaussField a r) (UniformSpace.Completion (GaussField a r)) F',
        extValuation g y ^ g.1.natDegree := by
  rw [← norm_algebraMap_norm_eq_prod (K := UniformSpace.Completion (GaussField a r))]
  refine NNReal.eq ?_
  rw [coe_nnnorm, norm_algebraMap', norm_gaussField]
  have := Algebra.norm_eq_of_ringEquiv (WithAbs.equiv _) (C := F')
    (A := GaussField a r) (B := RatFunc C) (by ext; rfl) y
  rw [← this]
  rfl

/-- The bijection between the factors of the minimal polynomial over the completion of
`(C(X), w_{a,r})` and the extensions of `w_{a,r}` to `F'` (B3). -/
noncomputable def factorEquiv :
    Factor (GaussField a r) (UniformSpace.Completion (GaussField a r)) F' ≃
      GaussExtension a r F' :=
  (extensionEquiv (K := UniformSpace.Completion (GaussField a r))).trans
    gaussExtensionEquiv.symm

omit [IsAlgClosed C] [CharZero C] in
lemma factorEquiv_apply_val
    (g : Factor (GaussField a r) (UniformSpace.Completion (GaussField a r)) F') :
    (factorEquiv g).1 = extValuation g := rfl

omit [IsAlgClosed C] [CharZero C] in
/-- `e · f` of the extension attached to a factor `g` is at most `deg g`. -/
lemma ramificationIdx_mul_inertiaDeg_factorEquiv_le
    (g : Factor (GaussField a r) (UniformSpace.Completion (GaussField a r)) F') :
    ramificationIdx (RatFunc C) (factorEquiv g).1 *
        inertiaDeg (gaussRat (NormedField.valuation (K := C)) a r) (factorEquiv g).1 ≤
      g.1.natDegree := by
  rw [← inertiaDeg_gaussField, ← ramificationIdx_gaussField (a := a) (r := r)]
  change ramificationIdx (GaussField a r) (extValuation g) *
      inertiaDeg (NormedField.valuation (K := GaussField a r)) (extValuation g) ≤ _
  rw [ramificationIdx_extValuation, inertiaDeg_extValuation, ← finrank_local]
  exact ramificationIdx_mul_inertiaDeg_le

include hp hp1 hc in
/-- **The local degree is `e · f`** at every extension of a Gauss valuation (W4 termwise). -/
theorem natDegree_eq_ramificationIdx_mul_inertiaDeg
    (g : Factor (GaussField a r) (UniformSpace.Completion (GaussField a r)) F') :
    g.1.natDegree = ramificationIdx (RatFunc C) (factorEquiv g).1 *
        inertiaDeg (gaussRat (NormedField.valuation (K := C)) a r) (factorEquiv g).1 := by
  classical
  have hW4 := finsum_ramificationIdx_mul_inertiaDeg_eq (a := a) hc hp hp1 (F' := F')
  rw [← finsum_comp_equiv (factorEquiv (a := a) (r := r) (F' := F')),
    finsum_eq_sum_of_fintype] at hW4
  have hsum := sum_natDegree_factors (F := GaussField a r)
    (K := UniformSpace.Completion (GaussField a r)) (F' := F')
  rw [← Finset.sum_coe_sort (factors _ _ F') natDegree] at hsum
  have hdeg : Module.finrank (GaussField a r) F' = Module.finrank (RatFunc C) F' :=
    Algebra.finrank_eq_of_equiv_equiv (WithAbs.equiv _) (RingEquiv.refl F') (by ext; rfl)
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (fun g _ ↦ ramificationIdx_mul_inertiaDeg_factorEquiv_le (F' := F') g)).1
    (by rw [hW4, hsum, hdeg]) g (Finset.mem_univ g)
  exact this.symm

include hp hp1 hc in
/-- **The norm formula over a Gauss point**:
`w_{a,r}(N_{F'/C(X)} y) = ∏_{w' ∣ w_{a,r}} w'(y) ^ (e(w') f(w'))` (and `e = 1`, as the value group
of `C` is divisible). -/
theorem gaussRat_norm_eq_prod [Fintype (GaussExtension a r F')] (y : F') :
    gaussRat (NormedField.valuation (K := C)) a r (Algebra.norm (RatFunc C) y) =
      ∏ w : GaussExtension a r F', w.1 y ^ (ramificationIdx (RatFunc C) w.1 *
        inertiaDeg (gaussRat (NormedField.valuation (K := C)) a r) w.1) := by
  rw [nnnorm_norm_eq_prod_factor,
    ← (factorEquiv (a := a) (r := r) (F' := F')).prod_comp]
  refine Finset.prod_congr rfl fun g _ ↦ ?_
  rw [natDegree_eq_ramificationIdx_mul_inertiaDeg hp hp1 hc g]
  rfl

end GaussStability

end SemistableReduction
