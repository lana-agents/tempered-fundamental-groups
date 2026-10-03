/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.ZariskiModel

/-!
# Reduction of geometric points

Blueprint §9.6 (W5), layer M3b. A geometric point of the generic fibre of a model of `F` is a
place `D ⊇ K` of `F` (a valuation subring, e.g. the local ring of a closed point of the curve)
together with an embedding `ρ : D → Ω` of its residue field into a field `Ω ⊇ K` carrying a
valuation subring `V` with `V ∩ K = O`. Its **reduction** is the specialization of the
*composite* valuation subring `ρ⁻¹(V) ⊆ D` of `F` (`compositeValuationSubring`), a valuation
subring over `O` (`comap_compositeValuationSubring`), so it lies in the special fibre
(`center_mem_specialFibre`).
-/


open IsLocalRing

namespace SemistableReduction

variable {F Ω : Type*} [Field F] [Field Ω]

/-- The composite of a valuation subring `D` of `F` and a valuation subring `V` of `Ω` along a
ring map `ρ : D → Ω` killing the maximal ideal: `ρ⁻¹(V)`, a valuation subring of `F`. -/
def compositeValuationSubring (D : ValuationSubring F) (ρ : D →+* Ω)
    (hρ : ∀ d : D, d ∈ maximalIdeal D → ρ d = 0) (V : ValuationSubring Ω) :
    ValuationSubring F where
  carrier := {f | ∃ h : f ∈ D, ρ ⟨f, h⟩ ∈ V}
  mul_mem' := by
    rintro x y ⟨hx, hxV⟩ ⟨hy, hyV⟩
    refine ⟨D.mul_mem _ _ hx hy, ?_⟩
    have : ρ ⟨x * y, D.mul_mem _ _ hx hy⟩ = ρ ⟨x, hx⟩ * ρ ⟨y, hy⟩ := by
      rw [← map_mul]; rfl
    rw [this]
    exact V.mul_mem _ _ hxV hyV
  one_mem' := ⟨D.one_mem, by
    have : ρ ⟨1, D.one_mem⟩ = 1 := by rw [← map_one ρ]; rfl
    rw [this]; exact V.one_mem⟩
  add_mem' := by
    rintro x y ⟨hx, hxV⟩ ⟨hy, hyV⟩
    refine ⟨D.add_mem _ _ hx hy, ?_⟩
    have : ρ ⟨x + y, D.add_mem _ _ hx hy⟩ = ρ ⟨x, hx⟩ + ρ ⟨y, hy⟩ := by
      rw [← map_add]; rfl
    rw [this]
    exact V.add_mem _ _ hxV hyV
  zero_mem' := ⟨D.zero_mem, by
    have : ρ ⟨0, D.zero_mem⟩ = 0 := by rw [← map_zero ρ]; rfl
    rw [this]; exact V.zero_mem⟩
  neg_mem' := by
    rintro x ⟨hx, hxV⟩
    refine ⟨D.neg_mem _ hx, ?_⟩
    have : ρ ⟨-x, D.neg_mem _ hx⟩ = -ρ ⟨x, hx⟩ := by
      rw [← map_neg]; rfl
    rw [this]
    exact V.neg_mem _ hxV
  mem_or_inv_mem' := by
    intro f
    have hρ0 : ρ ⟨0, D.zero_mem⟩ = 0 := by rw [← map_zero ρ]; rfl
    by_cases hf : f ∈ D
    · by_cases hfV : ρ ⟨f, hf⟩ ∈ V
      · exact .inl ⟨hf, hfV⟩
      · right
        have hne : ρ ⟨f, hf⟩ ≠ 0 := by
          rintro h
          rw [h] at hfV
          exact hfV V.zero_mem
        have hunit : IsUnit (⟨f, hf⟩ : D) := by
          by_contra hnu
          exact hne (hρ _ ((mem_maximalIdeal _).2 hnu))
        have hf0 : f ≠ 0 := by
          rintro rfl
          exact hne hρ0
        have hinv : f⁻¹ ∈ D := by
          obtain ⟨u, hu⟩ := hunit
          have : ((u⁻¹ : Dˣ) : F) = f⁻¹ := by
            have h : ((u⁻¹ : Dˣ) : D).1 * (u : D).1 = 1 := congrArg Subtype.val u.inv_mul
            rw [hu] at h
            exact eq_inv_of_mul_eq_one_left h
          rw [← this]
          exact (u⁻¹ : Dˣ).1.2
        refine ⟨hinv, ?_⟩
        have hprod : ρ ⟨f⁻¹, hinv⟩ * ρ ⟨f, hf⟩ = 1 := by
          rw [← map_mul, ← map_one ρ]
          congr 1
          exact Subtype.ext (inv_mul_cancel₀ hf0)
        rw [eq_inv_of_mul_eq_one_left hprod]
        exact (V.mem_or_inv_mem _).resolve_left hfV
    · right
      have hinv : f⁻¹ ∈ D := (D.mem_or_inv_mem f).resolve_left hf
      refine ⟨hinv, ?_⟩
      have hmax : (⟨f⁻¹, hinv⟩ : D) ∈ maximalIdeal D := by
        rw [mem_maximalIdeal, mem_nonunits_iff]
        rintro ⟨u, hu⟩
        apply hf
        have : ((u⁻¹ : Dˣ) : F) = f := by
          have h : ((u⁻¹ : Dˣ) : D).1 * (u : D).1 = 1 := congrArg Subtype.val u.inv_mul
          rw [hu] at h
          have := eq_inv_of_mul_eq_one_left h
          rw [this]
          exact inv_inv f
        rw [← this]
        exact (u⁻¹ : Dˣ).1.2
      rw [hρ _ hmax]
      exact V.zero_mem

variable {K : Type*} [Field K] [Algebra K F] [Algebra K Ω]

/-- The composite valuation subring lies over `O` when `D ⊇ K`, `ρ` is `K`-linear and
`V ∩ K = O`. -/
lemma comap_compositeValuationSubring {O : ValuationSubring K} (D : ValuationSubring F)
    (hKD : ∀ k : K, algebraMap K F k ∈ D) (ρ : D →+* Ω)
    (hρ : ∀ d : D, d ∈ maximalIdeal D → ρ d = 0)
    (hρK : ∀ k : K, ρ ⟨algebraMap K F k, hKD k⟩ = algebraMap K Ω k) (V : ValuationSubring Ω)
    (hV : V.comap (algebraMap K Ω) = O) :
    (compositeValuationSubring D ρ hρ V).comap (algebraMap K F) = O := by
  ext k
  rw [ValuationSubring.mem_comap, ← hV, ValuationSubring.mem_comap]
  constructor
  · rintro ⟨h, hV'⟩
    rwa [show (⟨algebraMap K F k, h⟩ : D) = ⟨algebraMap K F k, hKD k⟩ from rfl, hρK] at hV'
  · intro hk
    exact ⟨hKD k, by rw [hρK]; exact hk⟩

namespace ZariskiModel

variable {O : ValuationSubring K} {M : ZariskiModel (baseRing F O)}

/-- **Specializations of valuations over `O` lie in the special fibre.** -/
theorem center_mem_specialFibre (hM : M.IsProper) {W : ValuationSubring F}
    (hW : W.comap (algebraMap K F) = O) :
    M.center hM W (baseRing_le_iff.2 hW.ge) ∈ M.specialFibre := by
  refine ⟨center_mem_points hM W _, fun o ho hno h ↦ hno ?_⟩
  have h' : (algebraMap K F o)⁻¹ ∈ W := center_le hM W _ h
  rw [← map_inv₀, ← ValuationSubring.mem_comap, hW] at h'
  exact h'

end ZariskiModel

end SemistableReduction
