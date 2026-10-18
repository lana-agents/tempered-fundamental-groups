/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.KummerPatch

/-!
# A Kummer factor over an arbitrary flat base (Blueprint §12.8, M2.3 (d'))

`KummerPatch` treats the Kummer algebra `R̂ ⊗_A B` over the whole formal neighbourhood `R̂` of
the nodes. An admissible covering has one Kummer factor `S_j ⊗_{A_j} B_j` per ramification
index, over the part `S_j = R̂/(1 − ε_j)` of `R̂` (flat over `A_j` by
`FormalPatchProd.flat_quotient_one_sub`). For any base `S` flat over `A = A π e`:

* `KummerFactor.algebraMap_fA`: `u + v ↦ 1 ⊗ (s^e + t^e)`;
* `KummerFactor.eq_zero_of_mul_eq_zero`: `u + v` is a nonzerodivisor on `S ⊗_A B`;
* **`KummerFactor.flat_localization`**: `(S ⊗_A B)_{u+v}` is flat over `S` (`e` invertible);
* `KummerFactor.finite`: `S ⊗_A B` is finite over `S`.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace KummerFactor

open KummerEtale

noncomputable section

variable {O : Type u} [CommRing O] (π : O) {e : ℕ} (S : Type u) [CommRing S] [Algebra (A π e) S]

lemma algebraMap_fA : algebraMap (A π e) (S ⊗[A π e] B π) (fA π) =
    (1 : S) ⊗ₜ[A π e] algebraMap (A π e) (B π) (fA π) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one (A := S),
    Algebra.algebraMap_eq_smul_one (A := B π), TensorProduct.smul_tmul]

/-- **`u + v` is a nonzerodivisor on a Kummer factor** over a flat base. -/
theorem eq_zero_of_mul_eq_zero (he : 0 < e) [Module.Flat (A π e) S] (z : S ⊗[A π e] B π)
    (hz : algebraMap (A π e) (S ⊗[A π e] B π) (fA π) * z = 0) : z = 0 :=
  eq_zero_of_mul_eq_zero_tensor π he S hz

/-- **A Kummer factor is flat over its base away from the node** (`e` invertible). -/
theorem flat_localization (he : 0 < e) (heu : IsUnit (e : O)) [Module.Flat (A π e) S] :
    Module.Flat S (Localization.Away (algebraMap (A π e) (S ⊗[A π e] B π) (fA π))) := by
  haveI := KummerPatch.flat_Bf (π := π) he heu
  let ι := IsLocalization.Away.tensorProductEquivTMulRight (A π e) S
    (algebraMap (A π e) (B π) (fA π)) (Bf π e)
  haveI : Module.Flat S (Localization.Away
      ((1 : S) ⊗ₜ[A π e] algebraMap (A π e) (B π) (fA π))) :=
    Module.Flat.of_linearEquiv ι.symm.toLinearEquiv
  rw [algebraMap_fA]
  infer_instance

/-- A Kummer factor is finite over its base. -/
theorem finite (he : 0 < e) : Module.Finite S (S ⊗[A π e] B π) :=
  haveI : Module.Finite (A π e) (B π) := Node.kummer_finite π he
  inferInstance

end

end KummerFactor

end SemistableReduction
