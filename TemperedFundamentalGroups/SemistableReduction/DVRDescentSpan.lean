/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NodeDouble
import TemperedFundamentalGroups.SemistableReduction.ConstantDescent

/-!
# The reductions of the node chart are finitely generated (O1, step (D))

Blueprint §9.12, O1 (S7.9 (iii)). Let `R' = Rint c F'`, `v₁` an outer and `w₂` an inner vertex,
`ρ = (ρ₁, ρ₂) : R' → κ(v₁) × κ(w₂)` the two reductions. The image `Λ = ρ(R')` is a module over
`k[X, Y]` (`X ↦ (x̄, 0)`, `Y ↦ (0, ȳ)`), contained in `Ã₁ × Ã₂` (the integral closures of
`k[x̄]`, `k[ȳ]`, finite by `CurveGenerators.exists_generators`), hence finitely generated:
**`exists_spanning`**: there are finitely many `r_j ∈ R'` such that every subring `B ⊆ R'`
containing them and `x, c/x` spans all reductions over `k` (`ConstantDescent.IsSpanned`):
`ρ(y) = Σ λ_α ρ(x^a (c/x)^b r_j)`.
-/

open Polynomial IsLocalRing Valuation

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm ConstantDescent

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => ResidueField (HenselComplete.integers C)

/-- Spanned elements from finite sums over any finset. -/
lemma isSpanned_of_finset {k R κ₁ κ₂ : Type*} [Field k] [CommRing R] [Field κ₁] [Field κ₂]
    [Algebra k κ₁] [Algebra k κ₂] {B : Subring R} {ρ₁ : R →+* κ₁} {ρ₂ : R →+* κ₂}
    {ι : Type*} (s : Finset ι) (lam : ι → k) (b : ι → R) (hb : ∀ i ∈ s, b i ∈ B) {y : R}
    (h₁ : ρ₁ y = ∑ i ∈ s, algebraMap k κ₁ (lam i) * ρ₁ (b i))
    (h₂ : ρ₂ y = ∑ i ∈ s, algebraMap k κ₂ (lam i) * ρ₂ (b i)) :
    IsSpanned k B ρ₁ ρ₂ y := by
  classical
  let e := s.equivFin
  refine ⟨s.card, fun j ↦ lam (e.symm j), fun j ↦ b (e.symm j), fun j ↦ hb _ (e.symm j).2, ?_, ?_⟩
  · rw [h₁, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e _ _ fun i ↦ by simp).trans rfl
  · rw [h₂, ← Finset.sum_coe_sort s]
    exact (Fintype.sum_equiv e _ _ fun i ↦ by simp).trans rfl

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)

include hc0 in
lemma redHomInv_xR (w₂ : Ext C (Inv c hc0 F')) : redHomInv hc hc0 w₂ (xR c) = 0 := by
  change redHom hc w₂ (rintEquiv hc0 (xR c)) = 0
  rw [rintEquiv_xR, redHom_yR]

lemma redHomInv_yR (w₂ : Ext C (Inv c hc0 F')) :
    redHomInv hc hc0 w₂ (yR c) = red C (xF C (Inv c hc0 F')) w₂ := by
  change redHom hc w₂ (rintEquiv hc0 (yR c)) = _
  rw [rintEquiv_yR, redHom_xR]

set_option maxHeartbeats 1000000 in
-- the expansion of the `k[X, Y]`-action in monomials is elaboration-heavy
/-- **The reductions of the node chart are spanned over `k` by finitely many of them** (times
monomials in `x`, `c/x`). -/
theorem exists_spanning (v₁ : Ext C F') (w₂ : Ext C (Inv c hc0 F')) :
    ∃ (N : ℕ) (r : Fin N → Rint c F'), ∀ B : Subring (Rint c F'), (∀ j, r j ∈ B) →
      xR c ∈ B → yR c ∈ B → ∀ y, IsSpanned 𝓀 B (redHom hc v₁) (redHomInv hc hc0 w₂) y := by
  classical
  set ρ₁ := redHom hc v₁
  set ρ₂ := redHomInv hc hc0 w₂
  set xb := red C (xF C F') v₁
  set yb := red C (xF C (Inv c hc0 F')) w₂
  have hρ₁x : ρ₁ (xR c) = xb := redHom_xR hc v₁
  have hρ₁y : ρ₁ (yR c) = 0 := redHom_yR hc v₁
  have hρ₂x : ρ₂ (xR c) = 0 := redHomInv_xR hc hc0 w₂
  have hρ₂y : ρ₂ (yR c) = yb := redHomInv_yR hc hc0 w₂
  let κ₁ := ResidueField v₁.1.valuationSubring
  let κ₂ := ResidueField w₂.1.valuationSubring
  let A := MvPolynomial (Fin 2) 𝓀
  let ψ : A →ₐ[𝓀] κ₁ × κ₂ := MvPolynomial.aeval ![(xb, 0), (0, yb)]
  letI : Algebra A (κ₁ × κ₂) := ψ.toRingHom.toAlgebra
  have hsmul : ∀ (a : A) (m : κ₁ × κ₂), a • m = ψ a * m := fun a m ↦ Algebra.smul_def a m
  have hψ₁ : ∀ a : A, (ψ a).1 = MvPolynomial.aeval ![xb, 0] a := by
    intro a
    have := congrArg (fun f : A →ₐ[𝓀] κ₁ ↦ f a)
      (MvPolynomial.comp_aeval (R := 𝓀) ![(xb, 0), (0, yb)] (AlgHom.fst 𝓀 κ₁ κ₂))
    simp only [AlgHom.comp_apply] at this
    refine this.trans ?_
    congr 2
    funext i
    fin_cases i <;> rfl
  have hψ₂ : ∀ a : A, (ψ a).2 = MvPolynomial.aeval ![0, yb] a := by
    intro a
    have := congrArg (fun f : A →ₐ[𝓀] κ₂ ↦ f a)
      (MvPolynomial.comp_aeval (R := 𝓀) ![(xb, 0), (0, yb)] (AlgHom.snd 𝓀 κ₁ κ₂))
    simp only [AlgHom.comp_apply] at this
    refine this.trans ?_
    congr 2
    funext i
    fin_cases i <;> rfl
  -- the action on reductions, expanded in monomials
  have hexp₁ : ∀ (a : A) (r : Rint c F'), (ψ a).1 * ρ₁ r = ∑ d ∈ a.support,
      algebraMap 𝓀 κ₁ (a.coeff d) * ρ₁ (xR c ^ d 0 * yR c ^ d 1 * r) := by
    intro a r
    rw [hψ₁, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Fin.prod_univ_two, map_mul, map_mul, map_pow, map_pow, hρ₁x, hρ₁y]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  have hexp₂ : ∀ (a : A) (r : Rint c F'), (ψ a).2 * ρ₂ r = ∑ d ∈ a.support,
      algebraMap 𝓀 κ₂ (a.coeff d) * ρ₂ (xR c ^ d 0 * yR c ^ d 1 * r) := by
    intro a r
    rw [hψ₂, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq', Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [Fin.prod_univ_two, map_mul, map_mul, map_pow, map_pow, hρ₂x, hρ₂y]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  -- the generators of the integral closures
  haveI := IsCurveFunctionField.finiteDimensional_adjoin (transcendental_red_x (F := F') v₁)
  haveI := IsCurveFunctionField.finiteDimensional_adjoin
    (transcendental_red_x (F := Inv c hc0 F') w₂)
  obtain ⟨G₁, -, hsp₁⟩ := CurveGenerators.exists_generators (transcendental_red_x (F := F') v₁)
  obtain ⟨G₂, -, hsp₂⟩ :=
    CurveGenerators.exists_generators (transcendental_red_x (F := Inv c hc0 F') w₂)
  let ρ : Rint c F' → κ₁ × κ₂ := fun y ↦ (ρ₁ y, ρ₂ y)
  let N : Submodule A (κ₁ × κ₂) :=
    Submodule.span A ((G₁.image fun g ↦ ((g, 0) : κ₁ × κ₂)) ∪ (G₂.image fun g ↦ (0, g)) :
      Finset (κ₁ × κ₂))
  have hle : Submodule.span A (Set.range ρ) ≤ N := by
    rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    obtain ⟨c₁, hc₁⟩ := hsp₁ _ (redHom_isIntegral hc v₁ y)
    obtain ⟨c₂, hc₂⟩ := hsp₂ _ (redHom_isIntegral hc w₂ (rintEquiv hc0 y))
    have e : ρ y = ∑ g ∈ G₁, (Polynomial.aeval (MvPolynomial.X 0 : A) (c₁ g)) • ((g, 0) : κ₁ × κ₂)
        + ∑ g ∈ G₂, (Polynomial.aeval (MvPolynomial.X 1 : A) (c₂ g)) • ((0, g) : κ₁ × κ₂) := by
      have a₁ : ∀ P : 𝓀[X], (ψ (Polynomial.aeval (MvPolynomial.X 0 : A) P)).1 =
          Polynomial.aeval xb P := fun P ↦ by
        rw [hψ₁, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]; rfl
      have a₂ : ∀ P : 𝓀[X], (ψ (Polynomial.aeval (MvPolynomial.X 1 : A) P)).2 =
          Polynomial.aeval yb P := fun P ↦ by
        rw [hψ₂, ← Polynomial.aeval_algHom_apply, MvPolynomial.aeval_X]; rfl
      refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, Prod.fst_sum, hsmul, Prod.fst_mul, mul_zero,
          Finset.sum_const_zero, add_zero, a₁]
        exact hc₁
      · simp only [Prod.snd_add, Prod.snd_sum, hsmul, Prod.snd_mul, mul_zero,
          Finset.sum_const_zero, zero_add, a₂]
        exact hc₂
    rw [e]
    refine add_mem
      (Submodule.sum_mem _ fun g hg ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      (Submodule.sum_mem _ fun g hg ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_))
    · simp [hg]
    · simp [hg]
  -- `Λ` is finitely generated
  have hNfg : N.FG := Submodule.fg_span (Finset.finite_toSet _)
  haveI : IsNoetherian A N := isNoetherian_of_fg_of_noetherian N hNfg
  have hΛ : (Submodule.span A (Set.range ρ)).FG := isNoetherian_submodule.mp ‹_› _ hle
  obtain ⟨t, ht, htspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).mp hΛ
  choose rr hrr using fun m : t ↦ ht m.2
  refine ⟨t.card, fun j ↦ rr (t.equivFin.symm j), fun B hB hx hy y ↦ ?_⟩
  have hrrB : ∀ m : t, rr m ∈ B := fun m ↦ by
    have := hB (t.equivFin m)
    simpa using this
  have hmem : ρ y ∈ Submodule.span A (t : Set (κ₁ × κ₂)) := by
    rw [← htspan]; exact Submodule.subset_span ⟨y, rfl⟩
  obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.mp hmem
  have hsum : ρ y = ∑ m ∈ t.attach, f m • ρ (rr m) := by
    rw [← hf, ← Finset.sum_attach]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [hrr m]
  refine isSpanned_of_finset (t.attach.sigma fun m ↦ (f m).support)
    (fun md ↦ (f md.1).coeff md.2) (fun md ↦ xR c ^ md.2 0 * yR c ^ md.2 1 * rr md.1)
    (fun md _ ↦ B.mul_mem (B.mul_mem (B.pow_mem hx _) (B.pow_mem hy _)) (hrrB _)) ?_ ?_
  · have := congrArg Prod.fst hsum
    simp only [Prod.fst_sum, hsmul, Prod.fst_mul] at this
    rw [show ρ₁ y = (ρ y).1 from rfl, this, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    exact hexp₁ _ _
  · have := congrArg Prod.snd hsum
    simp only [Prod.snd_sum, hsmul, Prod.snd_mul] at this
    rw [show ρ₂ y = (ρ y).2 from rfl, this, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    exact hexp₂ _ _

end GaussTube

end SemistableReduction
