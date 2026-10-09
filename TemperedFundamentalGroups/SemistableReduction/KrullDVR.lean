/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Normal noetherian domains are intersections of their DVR localizations (W7, S9)

Blueprint §9.9, S9. For a noetherian integrally closed domain `D` with fraction field `F`, an
element `f ∈ F` which lies in `D_𝔮` for every prime `𝔮` such that `D_𝔮` is a discrete valuation
ring lies in `D` (`mem_of_forall_isDiscreteValuationRing`). This is the Krull property used to
show that functions with trivial divisor near a node are units.

Proof (classical). Write `f = a / b` with `a ∉ (b)`. Among the ideals `((b) : r a)` with
`r a ∉ (b)` choose a maximal one `𝔮 = ((b) : y)` (noetherian); it is prime, `f ∉ D_𝔮`, and in
`L = D_𝔮` the maximal ideal `𝔪` satisfies `𝔪 y ⊆ (b)`, `y ∉ (b)`. Then either `y / b` is
integral over `L` (impossible) or `𝔪 (y / b) = L`, so `𝔪` is principal and `L` is a DVR
(`isDiscreteValuationRing_of_mul_mem_span`, the argument of Mathlib's
`maximalIdeal_isPrincipal_of_isDedekindDomain`).
-/

open IsLocalRing

namespace SemistableReduction

/-- A noetherian local normal domain with `𝔪 y ⊆ (b)`, `y ∉ (b)` for some `0 ≠ b ∈ 𝔪` is a
discrete valuation ring. -/
theorem isDiscreteValuationRing_of_mul_mem_span (L : Type*) [CommRing L] [IsDomain L]
    [IsNoetherianRing L] [IsLocalRing L] [IsIntegrallyClosed L] {b y : L} (hb : b ≠ 0)
    (hbm : b ∈ maximalIdeal L) (h1 : ∀ m ∈ maximalIdeal L, m * y ∈ Ideal.span {b})
    (h2 : y ∉ Ideal.span {b}) : IsDiscreteValuationRing L := by
  have hnf : ¬ IsField L := fun hF ↦ by
    have := (isField_iff_maximalIdeal_eq).mp hF
    rw [this] at hbm
    exact hb ((Submodule.mem_bot L).mp hbm)
  refine ((IsDiscreteValuationRing.TFAE L hnf).out 0 4).mpr ?_
  let K := FractionRing L
  let x : K := algebraMap L K y / algebraMap L K b
  let M := Submodule.map (Algebra.linearMap L K) (maximalIdeal L)
  have hb₃ : algebraMap L K b ≠ 0 := IsFractionRing.to_map_eq_zero_iff.not.mpr hb
  have hk : ∀ m ∈ maximalIdeal L, ∃ k : L, algebraMap L K k = x * algebraMap L K m := by
    intro m hm
    obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp (h1 m hm)
    refine ⟨k, ?_⟩
    simp only [x]
    rw [div_mul_eq_mul_div, eq_div_iff hb₃, ← map_mul, ← map_mul, hk, mul_comm]
  by_cases hx : ∀ z ∈ M, x * z ∈ M
  · exfalso
    have := isIntegral_of_smul_mem_submodule M ?_ ?_ x hx
    · obtain ⟨z, e⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral this
      refine h2 (Ideal.mem_span_singleton'.mpr ⟨z, ?_⟩)
      apply IsFractionRing.injective L K
      rw [map_mul, e, div_mul_cancel₀ _ hb₃]
    · rw [Submodule.ne_bot_iff]
      exact ⟨_, ⟨b, hbm, rfl⟩, hb₃⟩
    · exact Submodule.FG.map _ (IsNoetherian.noetherian _)
  · push Not at hx
    obtain ⟨_, ⟨m, hm, rfl⟩, hxm⟩ := hx
    obtain ⟨k, hk'⟩ := hk m hm
    have hkm : k ∉ maximalIdeal L := fun h ↦ hxm ⟨k, h, by simpa using hk'⟩
    have hku : IsUnit k := by simpa [mem_maximalIdeal, mem_nonunits_iff] using hkm
    refine ⟨⟨m, le_antisymm (fun m' hm' ↦ ?_) ?_⟩⟩
    · obtain ⟨k', hk''⟩ := hk m' hm'
      have e : k' * m = k * m' := IsFractionRing.injective L K (by
        rw [map_mul, map_mul, hk'', hk']; ring)
      refine Ideal.mem_span_singleton'.mpr ⟨k' * hku.unit⁻¹, ?_⟩
      calc k' * ↑hku.unit⁻¹ * m = ↑hku.unit⁻¹ * (k' * m) := by ring
        _ = ↑hku.unit⁻¹ * (k * m') := by rw [e]
        _ = m' := by rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
    · rwa [Submodule.span_le, Set.singleton_subset_iff]

/-- **Krull property**: a noetherian normal domain is the intersection of its localizations that
are discrete valuation rings. -/
theorem mem_of_forall_isDiscreteValuationRing {D F : Type*} [CommRing D] [IsDomain D]
    [IsNoetherianRing D] [IsIntegrallyClosed D] [Field F] [Algebra D F] [IsFractionRing D F]
    (f : F) (h : ∀ 𝔮 : Ideal D, ∀ _ : 𝔮.IsPrime,
      IsDiscreteValuationRing (Localization.AtPrime 𝔮) →
        ∃ a : D, ∃ s ∉ 𝔮, algebraMap D F s * f = algebraMap D F a) :
    ∃ a : D, algebraMap D F a = f := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) f
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap D F b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  by_cases ha : a ∈ Ideal.span {b}
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    exact ⟨c, by rw [map_mul, mul_div_cancel_right₀ _ hbF]⟩
  exfalso
  -- the colon ideals `((b) : c)`
  let J : D → Ideal D := fun c ↦ (Ideal.span {b}).colon {c}
  have hJ : ∀ c s, s ∈ J c ↔ s * c ∈ Ideal.span {b} := fun c s ↦ by
    simp [J, Submodule.mem_colon_singleton, smul_eq_mul]
  let 𝒮 : Set (Ideal D) := {I | ∃ r : D, r * a ∉ Ideal.span {b} ∧ I = J (r * a)}
  obtain ⟨𝔮, ⟨r, hr, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr inferInstance 𝒮
    ⟨J (1 * a), 1, by simpa using ha, rfl⟩
  set y := r * a
  have hle : ∀ z, J y ≤ J (z * y) := fun z s hs ↦ by
    rw [hJ] at hs ⊢
    rw [mul_left_comm]
    exact Ideal.mul_mem_left _ z hs
  have hprime : (J y).IsPrime := by
    refine ⟨fun htop ↦ hr ?_, fun {s t} hst ↦ ?_⟩
    · simpa using (hJ y 1).mp (htop ▸ Submodule.mem_top)
    · by_contra! H
      obtain ⟨hs, ht⟩ := H
      have hsy : s * y ∉ Ideal.span {b} := fun h ↦ hs ((hJ y s).mpr h)
      have hmem : J (s * y) ∈ 𝒮 := ⟨s * r, by rwa [mul_assoc], by rw [mul_assoc]⟩
      have heq : J (s * y) = J y :=
        le_antisymm (by
          by_contra hne
          exact hmax _ hmem (lt_of_le_of_ne (hle s) (fun h ↦ hne (h ▸ le_rfl)))) (hle s)
      apply ht
      rw [← heq, hJ, ← mul_assoc, mul_comm t s]
      exact (hJ y (s * t)).mp hst
  haveI := hprime
  have hDVR : IsDiscreteValuationRing (Localization.AtPrime (J y)) := by
    let L := Localization.AtPrime (J y)
    haveI : IsIntegrallyClosed L :=
      isIntegrallyClosed_of_isLocalization L (J y).primeCompl
        ((J y).primeCompl_le_nonZeroDivisors)
    have hinj : Function.Injective (algebraMap D L) :=
      IsLocalization.injective L ((J y).primeCompl_le_nonZeroDivisors)
    refine isDiscreteValuationRing_of_mul_mem_span L (b := algebraMap D L b)
      (y := algebraMap D L y) (fun h0 ↦ hb0 (hinj (by rw [h0, map_zero]))) ?_ ?_ ?_
    · rw [← Localization.AtPrime.map_eq_maximalIdeal]
      refine Ideal.mem_map_of_mem _ ((hJ y b).mpr ?_)
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self b)
    · intro m hm
      obtain ⟨⟨m', t⟩, hmt⟩ := IsLocalization.surj (J y).primeCompl m
      have hm' : m' ∈ J y := by
        have : algebraMap D L m' ∈ maximalIdeal L := by
          rw [← hmt]; exact Ideal.mul_mem_right _ _ hm
        by_contra hc
        exact this (IsLocalization.map_units L (⟨m', hc⟩ : (J y).primeCompl))
      obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp ((hJ y m').mp hm')
      refine Ideal.mem_span_singleton'.mpr
        ⟨algebraMap D L k * (IsLocalization.map_units L t).unit⁻¹, ?_⟩
      have ht := IsLocalization.map_units L t
      have e1 : algebraMap D L k * algebraMap D L b = algebraMap D L m' * algebraMap D L y := by
        rw [← map_mul, ← map_mul, hk]
      simp only at hmt
      calc algebraMap D L k * ↑ht.unit⁻¹ * algebraMap D L b
          = ↑ht.unit⁻¹ * (algebraMap D L k * algebraMap D L b) := by ring
        _ = ↑ht.unit⁻¹ * (m * algebraMap D L t * algebraMap D L y) := by rw [e1, ← hmt]
        _ = (↑ht.unit⁻¹ * algebraMap D L t) * (m * algebraMap D L y) := by ring
        _ = m * algebraMap D L y := by rw [IsUnit.val_inv_mul, one_mul]
    · intro hmem
      obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.mp hmem
      obtain ⟨⟨k', t⟩, hkt⟩ := IsLocalization.surj (J y).primeCompl k
      simp only at hkt
      have : algebraMap D L (k' * b) = algebraMap D L (t * y) := by
        rw [map_mul, map_mul, ← hkt, mul_right_comm, hk, mul_comm]
      obtain ⟨u, hu⟩ := (IsLocalization.eq_iff_exists (J y).primeCompl L).mp this
      apply (u * t).2
      change ((u : D) * t) ∈ J y
      rw [hJ]
      refine Ideal.mem_span_singleton'.mpr ⟨u * k', ?_⟩
      rw [mul_assoc, hu]
      ring
  -- `f ∉ D_𝔮`
  obtain ⟨c, s, hs, hsc⟩ := h (J y) hprime hDVR
  apply hs
  rw [hJ]
  change s * (r * a) ∈ _
  rw [mul_left_comm]
  apply Ideal.mul_mem_left
  refine Ideal.mem_span_singleton'.mpr ⟨c, IsFractionRing.injective D F ?_⟩
  rw [map_mul, map_mul, ← hsc, mul_div_assoc', div_mul_cancel₀ _ hbF]

end SemistableReduction
