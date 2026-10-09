/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Normality descends along faithfully flat maps (W8′, XL6)

`isIntegrallyClosed_of_faithfullyFlat`: the Zariski local ring at a node is normal, being
faithfully flat under an étale local ring of the node (moved from `NodeBranches`).
-/

open Polynomial

namespace SemistableReduction

section Normal

/-- **Normality descends along faithfully flat maps** of domains. -/
theorem isIntegrallyClosed_of_faithfullyFlat {D E : Type*} [CommRing D] [IsDomain D]
    [CommRing E] [IsDomain E] [IsIntegrallyClosed E] [Algebra D E] [Module.FaithfullyFlat D E] :
    IsIntegrallyClosed D := by
  have hDE : Function.Injective (algebraMap D E) := FaithfulSMul.algebraMap_injective D E
  have hf : Function.Injective ((algebraMap E (FractionRing E)).comp (algebraMap D E)) :=
    (IsFractionRing.injective E (FractionRing E)).comp hDE
  let ψ : FractionRing D →+* FractionRing E :=
    IsFractionRing.lift (A := D) (K := FractionRing D) hf
  have hψa : ∀ a, ψ (algebraMap D (FractionRing D) a) =
      algebraMap E (FractionRing E) (algebraMap D E a) := fun a ↦
    IsFractionRing.lift_algebraMap (A := D) (K := FractionRing D) hf a
  have hψ : ψ.comp (algebraMap D (FractionRing D)) =
      (algebraMap E (FractionRing E)).comp (algebraMap D E) := by
    ext a; exact hψa a
  rw [isIntegrallyClosed_iff (FractionRing D)]
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hint : IsIntegral E
      (ψ (algebraMap D (FractionRing D) a / algebraMap D (FractionRing D) b)) := by
    obtain ⟨p, hp, hpx⟩ := hx
    refine ⟨p.map (algebraMap D E), hp.map _, ?_⟩
    rw [eval₂_map, ← hψ, ← hom_eval₂, hpx, map_zero]
  obtain ⟨e, he⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  have hfb : algebraMap E (FractionRing E) (algebraMap D E b) ≠ 0 :=
    (map_ne_zero_iff _ hf).mpr hb0
  rw [map_div₀, hψa, hψa, eq_div_iff hfb] at he
  have hmem : algebraMap D E a ∈ (Ideal.span {b}).map (algebraMap D E) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    refine ⟨e, IsFractionRing.injective E (FractionRing E) ?_⟩
    rw [map_mul]
    exact he
  rw [← Ideal.mem_comap, Ideal.comap_map_eq_self_of_faithfullyFlat,
    Ideal.mem_span_singleton'] at hmem
  obtain ⟨c, rfl⟩ := hmem
  refine ⟨c, ?_⟩
  rw [map_mul, mul_div_cancel_right₀ _
    ((map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))).mpr hb0)]

end Normal

end SemistableReduction
