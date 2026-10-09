/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeBranches

/-!
# Divisors at node germs (Blueprint §10.3.8, CrossingX1, CX5)

* `IsODPGerm.divisor`: in a node germ which is an ordinary double point (`IsODPGerm`, output of
  `ModelCode.exists_nodeGerm`), every divisor of a power of `ϖ` is `ε ϖ ^ α u ^ e` or
  `ε ϖ ^ α v ^ e` with `ε` a unit of `P` (`IsOrdinaryDoublePoint.eq_unit_mul_of_dvd`);
* `IsODPGerm.isNoetherianRing`: the germ ring is noetherian.
-/

open IsLocalRing

namespace SemistableReduction

/-- **Divisors of powers of `ϖ` on a node germ.** -/
theorem IsODPGerm.divisor {K L : Type u} [Field K] [Field L] [Algebra K L]
    {O : ValuationSubring K} [IsDiscreteValuationRing O] {ϖ : O} {P : Subring L} {u v : L}
    {n : ℕ} (h : IsODPGerm O ϖ P u v n) (hϖ : Irreducible ϖ) (hn : 1 ≤ n) {t : L} (ht : t ∈ P)
    {m : ℕ} (hr : ∃ r ∈ P, t * r = algebraMap K L (ϖ : K) ^ m) :
    ∃ ε ∈ P, ε⁻¹ ∈ P ∧ ∃ α e : ℕ, t = ε * algebraMap K L (ϖ : K) ^ α * u ^ e ∨
      t = ε * algebraMap K L (ϖ : K) ^ α * v ^ e := by
  obtain ⟨D, _, _, _, _, _, _, u', v', 𝔔₁, 𝔔₂, ι, hinj, hP, hιO, hu, hv, huv, H⟩ := h
  have hϖ0 : algebraMap O D ϖ ≠ 0 := fun h0 ↦ by
    have := congrArg ι h0
    rw [hιO, map_zero, map_eq_zero_iff _ (algebraMap K L).injective] at this
    exact hϖ.ne_zero (Subtype.ext this)
  rw [← hP] at ht
  obtain ⟨d, rfl⟩ := ht
  obtain ⟨r, hrP, hdr⟩ := hr
  rw [← hP] at hrP
  obtain ⟨d', rfl⟩ := hrP
  have hdvd : d ∣ algebraMap O D ϖ ^ m := ⟨d', hinj (by rw [map_mul, hdr, map_pow, hιO])⟩
  haveI := H.isPrime₁
  haveI := H.isPrime₂
  obtain ⟨ε, α, e, he | he⟩ := H.eq_unit_mul_of_dvd hn huv hϖ0 hdvd
  · refine ⟨ι ε, hP ▸ ⟨ε, rfl⟩, ?_, α, e, .inl ?_⟩
    · have : (ι ε)⁻¹ = ι ↑ε⁻¹ := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ ?_, ← map_mul, Units.inv_mul, map_one]
        exact fun h0 ↦ ε.ne_zero (hinj (by rw [h0, map_zero]))
      rw [this]; exact hP ▸ ⟨_, rfl⟩
    · rw [he, map_mul, map_mul, map_pow, map_pow, hιO, hu]
  · refine ⟨ι ε, hP ▸ ⟨ε, rfl⟩, ?_, α, e, .inr ?_⟩
    · have : (ι ε)⁻¹ = ι ↑ε⁻¹ := by
        rw [eq_comm, ← mul_eq_one_iff_eq_inv₀ ?_, ← map_mul, Units.inv_mul, map_one]
        exact fun h0 ↦ ε.ne_zero (hinj (by rw [h0, map_zero]))
      rw [this]; exact hP ▸ ⟨_, rfl⟩
    · rw [he, map_mul, map_mul, map_pow, map_pow, hιO, hv]

/-- The germ ring of an ordinary double point is noetherian. -/
theorem IsODPGerm.isNoetherianRing {K L : Type u} [Field K] [Field L] [Algebra K L]
    {O : ValuationSubring K} {ϖ : O} {P : Subring L} {u v : L} {n : ℕ}
    (h : IsODPGerm O ϖ P u v n) : IsNoetherianRing P := by
  obtain ⟨D, _, _, _, _, _, _, u', v', 𝔔₁, 𝔔₂, ι, hinj, hP, -⟩ := h
  subst hP
  exact isNoetherianRing_of_ringEquiv D (RingEquiv.ofBijective ι.rangeRestrict
    ⟨fun a b h ↦ hinj (congrArg Subtype.val h), ι.rangeRestrict_surjective⟩)

end SemistableReduction
