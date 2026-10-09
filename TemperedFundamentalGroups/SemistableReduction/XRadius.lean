/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XLength

/-!
# Radii under restriction of the function field (Blueprint §9.7, XL7)

Let `L₂ ⊆ L₁` (over `K`), `x, ϖ₀ ∈ L₂`, `U'` a valuation subring of `L̄₁` and `φ : L̄₂ → L̄₁` a
`K`-embedding extending `L₂ → L₁`. If `U'` has Gauss data `(a, ρ)` on the x-line and its restriction
`U'.comap φ` has Gauss data `(b, σ)`, then `ρ = σ` (`rho_eq_of_restrict`): the normalised radius
of a Gauss point does not depend on the field it is computed in.
-/

open Polynomial

namespace SemistableReduction

/-- Preimages of algebraic elements under embeddings of algebraically closed fields. -/
lemma exists_preimage_of_isAlgebraic {K A B : Type*} [Field K] [Field A] [Field B] [Algebra K A]
    [Algebra K B] [IsAlgClosed A] (φ : A →ₐ[K] B) {a : B} (ha : IsAlgebraic K a) :
    ∃ c : A, φ c = a := by
  set p := minpoly K a
  have hp0 : p ≠ 0 := minpoly.ne_zero ha.isIntegral
  set q := p.map (algebraMap K A)
  have hq : q.map (φ : A →+* B) = p.map (algebraMap K B) := by
    rw [Polynomial.map_map]; congr 1; ext k; simp
  have hroots := Polynomial.Splits.roots_map (IsAlgClosed.splits q) (φ : A →+* B)
  rw [hq] at hroots
  have hmem : a ∈ (p.map (algebraMap K B)).roots := by
    rw [mem_roots (Polynomial.map_ne_zero hp0), IsRoot, eval_map_algebraMap, minpoly.aeval]
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨c, -, hc⟩ := hmem
  exact ⟨c, hc⟩

/-- Order on comap valuations. -/
lemma comap_valuation_le_iff {A B : Type*} [Field A] [Field B] (U : ValuationSubring B)
    (f : A →+* B) (y z : A) :
    (U.comap f).valuation y ≤ (U.comap f).valuation z ↔ U.valuation (f y) ≤ U.valuation (f z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp only [map_zero, le_zero_iff, map_eq_zero]
  have hz' : f z ≠ 0 := (map_ne_zero f).2 hz
  have h1 : (U.comap f).valuation y ≤ (U.comap f).valuation z ↔ y / z ∈ U.comap f := by
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀,
      div_le_one₀ (zero_lt_iff.2 (by simpa using hz))]
  have h2 : U.valuation (f y) ≤ U.valuation (f z) ↔ f y / f z ∈ U := by
    rw [← ValuationSubring.valuation_le_one_iff, map_div₀,
      div_le_one₀ (zero_lt_iff.2 (by simpa using hz'))]
  rw [h1, h2, ValuationSubring.mem_comap, map_div₀]

variable {K L₁ L₂ : Type*} [Field K] [Field L₁] [Field L₂] [Algebra K L₁] [Algebra K L₂]

/-- **The radius does not change under restriction.** -/
theorem rho_eq_of_restrict (φ : Fbar L₂ →ₐ[K] Fbar L₁) {x ϖ₀ : Fbar L₂} (hϖ0 : ϖ₀ ≠ 0)
    {U' : ValuationSubring (Fbar L₁)} (hlt : U'.valuation (φ ϖ₀) < 1) {a : Kbar K L₁} {ρ : ℚ}
    (ha : IsXGauss (φ ϖ₀) (φ x) a ρ U') {b : Kbar K L₂} {σ : ℚ}
    (hb : IsXGauss ϖ₀ x b σ (U'.comap (φ : Fbar L₂ →+* Fbar L₁))) : ρ = σ := by
  have hφa : ∀ c : Kbar K L₂, φ (algebraMap (Kbar K L₂) (Fbar L₂) c) ∈
      algebraicClosure K (Fbar L₁) := fun c ↦ by
    have : IsAlgebraic K (algebraMap (Kbar K L₂) (Fbar L₂) c) := mem_algebraicClosure_iff.1 c.2
    exact mem_algebraicClosure_iff.2 (this.algHom φ)
  -- `U'(x - a) ≤ U'(x - φ b)`
  have h1 := ha.valuation_le ⟨_, hφa b⟩
  -- `V(x - b) ≤ V(x - c)` with `φ c = a`
  obtain ⟨c, hc⟩ := exists_preimage_of_isAlgebraic φ (mem_algebraicClosure_iff.1 a.2)
  have hcK : c ∈ algebraicClosure K (Fbar L₂) := by
    have := mem_algebraicClosure_iff.1 a.2
    rw [← hc] at this
    exact mem_algebraicClosure_iff.2 ((isAlgebraic_algHom_iff φ φ.toRingHom.injective).1 this)
  have h2 := hb.valuation_le ⟨c, hcK⟩
  rw [comap_valuation_le_iff] at h2
  simp only [map_sub] at h2
  have e1 : φ (algebraMap (Kbar K L₂) (Fbar L₂) b) = algebraMap (Kbar K L₁) (Fbar L₁) ⟨_, hφa b⟩ :=
    rfl
  have e2 : (φ : Fbar L₂ →+* Fbar L₁) (algebraMap (Kbar K L₂) (Fbar L₂) ⟨c, hcK⟩) =
      algebraMap (Kbar K L₁) (Fbar L₁) a := hc
  rw [e2] at h2
  have heq : U'.valuation (φ x - algebraMap (Kbar K L₁) (Fbar L₁) a) =
      U'.valuation (φ x - algebraMap (Kbar K L₁) (Fbar L₁) ⟨_, hφa b⟩) := by
    refine le_antisymm h1 ?_
    exact h2
  -- transfer `σ`
  have hσ : IsLogValue U' (φ ϖ₀) (φ x - algebraMap (Kbar K L₁) (Fbar L₁) a) σ := by
    have h := hb.1
    unfold IsLogValue at h ⊢
    rw [heq]
    set y := x - algebraMap (Kbar K L₂) (Fbar L₂) b
    have h' : (U'.comap (φ : Fbar L₂ →+* Fbar L₁)).valuation (y ^ σ.den) =
        (U'.comap (φ : Fbar L₂ →+* Fbar L₁)).valuation (ϖ₀ ^ σ.num) := by
      rw [map_pow, map_zpow₀]; exact h
    have h'' : U'.valuation ((φ : Fbar L₂ →+* Fbar L₁) (y ^ σ.den)) =
        U'.valuation ((φ : Fbar L₂ →+* Fbar L₁) (ϖ₀ ^ σ.num)) :=
      le_antisymm ((comap_valuation_le_iff _ _ _ _).1 h'.le)
        ((comap_valuation_le_iff _ _ _ _).1 h'.ge)
    rw [map_pow, map_zpow₀, map_pow, map_zpow₀] at h''
    simpa [y, map_sub] using h''
  have hw0 : U'.valuation (φ ϖ₀) ≠ 0 := by
    simpa using (map_ne_zero (φ : Fbar L₂ →+* Fbar L₁)).2 hϖ0
  exact IsLogValue.unique hw0 hlt ha.1 hσ

omit [Algebra K L₁] [Algebra K L₂] in
/-- **The radius does not change under restriction**, for arbitrary fields of centres: it suffices
that the centres correspond under `φ`. -/
theorem rho_eq_of_restrict' {A₁ A₂ : Type*} [Field A₁] [Field A₂] [Algebra A₁ (Fbar L₁)]
    [Algebra A₂ (Fbar L₂)] (φ : Fbar L₂ →+* Fbar L₁) {x ϖ₀ : Fbar L₂} (hϖ0 : ϖ₀ ≠ 0)
    {U' : ValuationSubring (Fbar L₁)} (hlt : U'.valuation (φ ϖ₀) < 1) {a : A₁} {ρ : ℚ}
    (ha : IsXGauss (φ ϖ₀) (φ x) a ρ U') {b : A₂} {σ : ℚ} (hb : IsXGauss ϖ₀ x b σ (U'.comap φ))
    (hb₁ : ∃ c₁ : A₁, algebraMap A₁ (Fbar L₁) c₁ = φ (algebraMap A₂ (Fbar L₂) b))
    (ha₂ : ∃ c₂ : A₂, φ (algebraMap A₂ (Fbar L₂) c₂) = algebraMap A₁ (Fbar L₁) a) : ρ = σ := by
  obtain ⟨c₁, hc₁⟩ := hb₁
  obtain ⟨c₂, hc₂⟩ := ha₂
  have h1 := ha.valuation_le c₁
  rw [hc₁] at h1
  have h2 := hb.valuation_le c₂
  rw [comap_valuation_le_iff] at h2
  simp only [map_sub] at h2
  rw [hc₂] at h2
  have heq : U'.valuation (φ x - algebraMap A₁ (Fbar L₁) a) =
      U'.valuation (φ x - φ (algebraMap A₂ (Fbar L₂) b)) := le_antisymm h1 h2
  have hσ : IsLogValue U' (φ ϖ₀) (φ x - algebraMap A₁ (Fbar L₁) a) σ := by
    have h := hb.1
    unfold IsLogValue at h ⊢
    rw [heq]
    set y := x - algebraMap A₂ (Fbar L₂) b
    have h' : (U'.comap φ).valuation (y ^ σ.den) = (U'.comap φ).valuation (ϖ₀ ^ σ.num) := by
      rw [map_pow, map_zpow₀]; exact h
    have h'' : U'.valuation (φ (y ^ σ.den)) = U'.valuation (φ (ϖ₀ ^ σ.num)) :=
      le_antisymm ((comap_valuation_le_iff _ _ _ _).1 h'.le)
        ((comap_valuation_le_iff _ _ _ _).1 h'.ge)
    rw [map_pow, map_zpow₀, map_pow, map_zpow₀] at h''
    simpa [y, map_sub] using h''
  have hw0 : U'.valuation (φ ϖ₀) ≠ 0 := by
    simpa using (map_ne_zero φ).2 hϖ0
  exact IsLogValue.unique hw0 hlt ha.1 hσ

end SemistableReduction
