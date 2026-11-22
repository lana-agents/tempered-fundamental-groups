/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Overlap
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.RingHom.Finite

/-!
# Finiteness, étaleness and rank of `C[1/s]` over `S[1/s]` (MR13 step 7, D1)

For an `S`-algebra `C`, `s ∈ S` and `W = S[1/s]`, the algebra `C[1/s]` over `W`
(`AwayAlg.alg`, the base change of `C` along `S → W`):

* **`AwayAlg.finite_alg`**: `C[1/s]` is finite over `W` if `C` is finite over `S`;
* **`AwayAlg.etale_alg`**: `C[1/s]` is étale over `W` if `C` is étale over `S`;
* **`AwayAlg.finrank_alg`**: `rank_W C[1/s] = rank_S C` if `S` is a domain and `s ≠ 0`.
-/

universe u

open Module

namespace SemistableReduction

namespace AwayAlg

noncomputable section

variable {S W C : Type u} [CommRing S] [CommRing W] [CommRing C] [Algebra S W] [Algebra S C]
  (s : S) [IsLocalization.Away s W]

lemma finite_alg [Module.Finite S C] :
    letI := alg (C := C) (W := W) s
    Module.Finite W (Localization.Away (algebraMap S C s)) := by
  letI := alg (C := C) (W := W) s
  exact RingHom.finite_algebraMap.mp (RingHom.finite_localizationPreserves.away
    (algebraMap S C) s W (Localization.Away (algebraMap S C s))
    (RingHom.finite_algebraMap.mpr inferInstance))

lemma etale_alg [Algebra.Etale S C] :
    letI := alg (C := C) (W := W) s
    Algebra.Etale W (Localization.Away (algebraMap S C s)) := by
  letI := alg (C := C) (W := W) s
  exact RingHom.etale_algebraMap.mp
    (RingHom.Etale.propertyIsLocal.localizationAwayPreserves (algebraMap S C) s W
      (Localization.Away (algebraMap S C s)) (RingHom.etale_algebraMap.mpr inferInstance))

lemma finrank_alg [IsDomain S] (hs : s ≠ 0) :
    letI := alg (C := C) (W := W) s
    finrank W (Localization.Away (algebraMap S C s)) = finrank S C := by
  letI := alg (C := C) (W := W) s
  haveI := tower (C := C) (W := W) s
  have hle : Submonoid.powers s ≤ nonZeroDivisors S :=
    Submonoid.powers_le.2 (mem_nonZeroDivisors_of_ne_zero hs)
  have h1 : finrank W (Localization.Away (algebraMap S C s)) =
      finrank S (Localization.Away (algebraMap S C s)) := by
    simp only [Module.finrank, IsLocalization.rank_eq W (Submonoid.powers s) hle]
  haveI : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers s))
      (Localization.Away (algebraMap S C s)) := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  haveI : IsLocalizedModule (Submonoid.powers s)
      (IsScalarTower.toAlgHom S C (Localization.Away (algebraMap S C s))).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  rw [h1]
  exact IsLocalizedModule.finrank_eq (Submonoid.powers s)
    (IsScalarTower.toAlgHom S C (Localization.Away (algebraMap S C s))).toLinearMap hle

end

end AwayAlg

end SemistableReduction
