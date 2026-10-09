/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeDeformation

/-!
# Ordinary double points from the fibre product of the branches (O1, step (4))

Blueprint §9.12, O1 (S7.9, the algebraic end). Let `D` be a local ring over a ring `O`,
`ϖ ∈ O`, and `ψᵢ : D → Vᵢ` (`i = 1, 2`) maps to local domains whose residue maps
`rᵢ : Vᵢ → k` agree on `D`. Suppose that the special fibre `D / ϖ D` *is* the fibre product of the
branches: `ker ψ₁ ∩ ker ψ₂ = ϖ D`, and every `(a, b)` with `r₁ a = r₂ b` is `(ψ₁ z, ψ₂ z)`; that
the residues of the `Vᵢ` come from `O`, and that `u', v' ∈ D` map to `(t₁, 0)`, `(0, t₂)` with
`tᵢ` generating the maximal ideal of `Vᵢ`. Then the closed point of `D` is an ordinary double
point with coordinates `u', v'` and branches `ker ψ₁`, `ker ψ₂`
(`isOrdinaryDoublePoint_of_fibreProduct`). No normality or noetherianity is needed.
-/

open IsLocalRing

namespace SemistableReduction

variable {O D V₁ V₂ k : Type*} [CommRing O] [CommRing D] [IsLocalRing D] [Algebra O D]
  [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂]
  [Field k]

/-- **Ordinary double points from the fibre product of the two branches.** -/
theorem isOrdinaryDoublePoint_of_fibreProduct {ϖ : O} (ψ₁ : D →+* V₁) (ψ₂ : D →+* V₂)
    (r₁ : V₁ →+* k) (r₂ : V₂ →+* k) (hr₁ : ∀ a, r₁ a = 0 ↔ a ∈ maximalIdeal V₁)
    (hr₂ : ∀ b, r₂ b = 0 ↔ b ∈ maximalIdeal V₂)
    (hcomp : ∀ z, r₁ (ψ₁ z) = r₂ (ψ₂ z))
    (hker : ∀ z, ψ₁ z = 0 → ψ₂ z = 0 → z ∈ Ideal.span {algebraMap O D ϖ})
    (hϖ₁ : ψ₁ (algebraMap O D ϖ) = 0) (hϖ₂ : ψ₂ (algebraMap O D ϖ) = 0)
    (hfp : ∀ a b, r₁ a = r₂ b → ∃ z, ψ₁ z = a ∧ ψ₂ z = b)
    (hO₁ : ∀ a : V₁, ∃ o : O, r₁ (ψ₁ (algebraMap O D o)) = r₁ a)
    (hO₂ : ∀ b : V₂, ∃ o : O, r₁ (ψ₁ (algebraMap O D o)) = r₂ b)
    {u' v' : D} (hu₁ : maximalIdeal V₁ = Ideal.span {ψ₁ u'}) (hu₂ : ψ₂ u' = 0)
    (hv₂ : maximalIdeal V₂ = Ideal.span {ψ₂ v'}) (hv₁ : ψ₁ v' = 0)
    (hu0 : ψ₁ u' ≠ 0) (hv0 : ψ₂ v' ≠ 0) :
    IsOrdinaryDoublePoint ϖ u' v' (RingHom.ker ψ₁) (RingHom.ker ψ₂) := by
  set p := algebraMap O D ϖ with hp
  -- the non-units of `D` are the elements with vanishing residue
  have hp_nonunit : ¬ IsUnit p := fun h ↦ by
    have := h.map ψ₁
    rw [hϖ₁] at this
    exact not_isUnit_zero this
  have hunit : ∀ z, z ∈ maximalIdeal D ↔ r₁ (ψ₁ z) = 0 := by
    intro z
    constructor
    · intro hz
      by_contra h0
      have ha : IsUnit (ψ₁ z) := by
        by_contra hna; exact h0 ((hr₁ _).mpr ((mem_maximalIdeal _).mpr hna))
      have hb : IsUnit (ψ₂ z) := by
        by_contra hnb
        exact h0 (by rw [hcomp]; exact (hr₂ _).mpr ((mem_maximalIdeal _).mpr hnb))
      have e₁ : r₁ ↑ha.unit⁻¹ = (r₁ (ψ₁ z))⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← map_mul, IsUnit.val_inv_mul, map_one])
      have e₂ : r₂ ↑hb.unit⁻¹ = (r₂ (ψ₂ z))⁻¹ :=
        eq_inv_of_mul_eq_one_left (by rw [← map_mul, IsUnit.val_inv_mul, map_one])
      obtain ⟨w, hw₁, hw₂⟩ := hfp ↑ha.unit⁻¹ ↑hb.unit⁻¹ (by rw [e₁, e₂, hcomp])
      have h1 : z * w - 1 ∈ Ideal.span {p} := hker _
        (by rw [map_sub, map_mul, hw₁, IsUnit.mul_val_inv, map_one, sub_self])
        (by rw [map_sub, map_mul, hw₂, IsUnit.mul_val_inv, map_one, sub_self])
      have hpm : Ideal.span {p} ≤ maximalIdeal D := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact (mem_maximalIdeal _).mpr hp_nonunit
      have h2 : z * w ∈ maximalIdeal D := Ideal.mul_mem_right _ _ hz
      have h3 := sub_mem h2 (hpm h1)
      rw [sub_sub_cancel] at h3
      exact (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).mpr h3)
    · intro h hz
      exact (mem_maximalIdeal _).mp ((hr₁ _).mp h) (hz.map ψ₁)
  have hpm : p ∈ maximalIdeal D := (mem_maximalIdeal _).mpr hp_nonunit
  have hu'₁ : ψ₁ u' ∈ maximalIdeal V₁ := by rw [hu₁]; exact Ideal.subset_span rfl
  have hv'₂ : ψ₂ v' ∈ maximalIdeal V₂ := by rw [hv₂]; exact Ideal.subset_span rfl
  -- lifts of elements of one branch
  have hlift₁ : ∀ a : V₁, ∃ z, ψ₁ z = a ∧ ∃ o : O, ψ₂ z = ψ₂ (algebraMap O D o) := by
    intro a
    obtain ⟨o, ho⟩ := hO₁ a
    obtain ⟨z, hz₁, hz₂⟩ := hfp a (ψ₂ (algebraMap O D o)) (by rw [← hcomp, ho])
    exact ⟨z, hz₁, o, hz₂⟩
  have hlift₂ : ∀ b : V₂, ∃ z, ψ₂ z = b ∧ ∃ o : O, ψ₁ z = ψ₁ (algebraMap O D o) := by
    intro b
    obtain ⟨o, ho⟩ := hO₂ b
    obtain ⟨z, hz₁, hz₂⟩ := hfp (ψ₁ (algebraMap O D o)) b ho
    exact ⟨z, hz₂, o, hz₁⟩
  refine
    { maximalIdeal_eq := le_antisymm (fun z hz ↦ ?_) ?_
      residue := fun z ↦ ?_
      mul_mem := hker _ (by rw [map_mul, hv₁, mul_zero]) (by rw [map_mul, hu₂, zero_mul])
      isPrime₁ := RingHom.ker_isPrime ψ₁
      isPrime₂ := RingHom.ker_isPrime ψ₂
      mem₁ := hϖ₁
      mem₂ := hϖ₂
      notMem₁ := hu0
      notMem₂ := hv0
      reduced₁ := fun z hz ↦ ⟨u', hu0, hker _
        (by rw [map_mul, (RingHom.mem_ker).mp hz, mul_zero]) (by rw [map_mul, hu₂, zero_mul])⟩
      reduced₂ := fun z hz ↦ ⟨v', hv0, hker _ (by rw [map_mul, hv₁, zero_mul])
        (by rw [map_mul, (RingHom.mem_ker).mp hz, mul_zero])⟩
      branches := fun 𝔔 h𝔔 hp𝔔 ↦ ?_ }
  · -- `𝔪 ⊆ (ϖ, u', v')`
    have hz₁ : ψ₁ z ∈ maximalIdeal V₁ := (hr₁ _).mp ((hunit z).mp hz)
    have hz₂ : ψ₂ z ∈ maximalIdeal V₂ := (hr₂ _).mp (by rw [← hcomp]; exact (hunit z).mp hz)
    rw [hu₁, Ideal.mem_span_singleton'] at hz₁
    rw [hv₂, Ideal.mem_span_singleton'] at hz₂
    obtain ⟨c₁, hc₁⟩ := hz₁
    obtain ⟨c₂, hc₂⟩ := hz₂
    obtain ⟨a, ha₁, -⟩ := hlift₁ c₁
    obtain ⟨b, hb₂, -⟩ := hlift₂ c₂
    have hrest : z - a * u' - b * v' ∈ Ideal.span {p} := hker _
      (by rw [map_sub, map_sub, map_mul, map_mul, ha₁, hv₁, ← hc₁, mul_zero, sub_zero, sub_self])
      (by rw [map_sub, map_sub, map_mul, map_mul, hu₂, hb₂, ← hc₂, mul_zero, sub_zero,
        sub_self])
    have hz : z = (z - a * u' - b * v') + a * u' + b * v' := by ring
    rw [hz]
    refine add_mem (add_mem (Ideal.span_mono (by simp [hp]) hrest) ?_) ?_
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    · exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
  · rw [Ideal.span_le]
    rintro w (rfl | rfl | rfl)
    · exact hpm
    · exact (hunit _).mpr ((hr₁ _).mpr hu'₁)
    · exact (hunit _).mpr (by rw [hv₁, map_zero])
  · obtain ⟨o, ho⟩ := hO₁ (ψ₁ z)
    exact ⟨o, (hunit _).mpr (by rw [map_sub, map_sub, ho, sub_self])⟩
  · have hle : RingHom.ker ψ₁ * RingHom.ker ψ₂ ≤ 𝔔 := by
      rw [Ideal.mul_le]
      intro a ha b hb
      have : a * b ∈ Ideal.span {p} := hker _
        (by rw [map_mul, (RingHom.mem_ker).mp ha, zero_mul])
        (by rw [map_mul, (RingHom.mem_ker).mp hb, mul_zero])
      exact (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hp𝔔)) this
    exact h𝔔.mul_le.mp hle

end SemistableReduction
