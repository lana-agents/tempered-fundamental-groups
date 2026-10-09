/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.NearBoundary
import TemperedFundamentalGroups.SemistableReduction.Type3Tube

/-!
# Exact node data from a node coordinate of the right degree

Blueprint §9.10a (II.3). Let `P'` be a point of `R' = Rint c F'` over the node and `u ∈ F'` with
`σ x = e uᵈ` (`σ, e ∈ R' ∖ P'`) and `σ_u u ∈ R'` (`σ_u ∉ P'`). At every outer branch of `P'` the
order of `x̄` is `d` times the order of `ū`, hence `≥ d`. If the vertex degree of `P'` (the sum
of these orders) is at most `d`, then `P'` has exactly one outer branch, `ū` is a uniformizer
there, and `P'` carries exact node data (`exists_nodeData_of_coord`).
-/

open Polynomial WithZero
open scoped NNReal

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm TubeCount

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

/-- In `ℤᵐ⁰`, a nonzero value below `1` is at most `exp (-1)`. -/
lemma le_exp_neg_one {v : ℤᵐ⁰} (h0 : v ≠ 0) (h1 : v < 1) : v ≤ exp (-1) := by
  rw [← exp_log h0] at h1 ⊢
  rw [← exp_zero, exp_lt_exp] at h1
  rw [exp_le_exp]
  omega

section Branch

variable {c : C} (hc : ‖c‖ < 1)

set_option maxHeartbeats 1000000 in
-- the rewrites with the valuations of the residues at the branch are slow to unify
/-- At an outer branch of `P'`, `ord x̄ = d · ord ū` for a node coordinate `u`: the order of `x̄`
is at least `d`, and equals `d` only if `ū` is a uniformizer. -/
lemma ord_x_of_coord {P' : Ideal (Rint c F')} (b : OuterBranch C F')
    (hb : placeIdeal hc b.1 b.2.2 = P') {d : ℕ} (hd : 1 ≤ d) (u : F') (σ e : Rint c F')
    (hσ : σ ∉ P') (he : e ∉ P') (hx : (σ : F') * xF C F' = e * u ^ d) (uR σu : Rint c F')
    (hσu : σu ∉ P') (huR : (uR : F') = σu * u) :
    d ≤ ord (red C (xF C F') b.1) b.2.1 ∧ (ord (red C (xF C F') b.1) b.2.1 = d →
      b.2.1.valuation (redHom hc b.1 uR) = exp (-1)) := by
  have hσv := val_one_of_notMem hc hb hσ
  have hev := val_one_of_notMem hc hb he
  have hσuv := val_one_of_notMem hc hb hσu
  have hu1 : b.1.1 u = 1 := by
    have h := congrArg b.1.1 hx
    rw [map_mul, map_mul, map_pow, hσv, hev, valuation_xF, one_mul, one_mul] at h
    rcases lt_trichotomy (b.1.1 u) 1 with hlt | heq | hgt
    · exact absurd h.symm (pow_lt_one₀ zero_le hlt (by omega)).ne
    · exact heq
    · exact absurd h.symm (one_lt_pow₀ hgt (by omega)).ne'
  have hQu : b.2.1.valuation (red C u b.1) = b.2.1.valuation (redHom hc b.1 uR) := by
    rw [redHom_apply, huR, red_mul (valuation_le_one_R hc b.1 σu) hu1.le, map_mul,
      ← redHom_apply hc, Qval_one_of_notMem hc hb hσu, one_mul]
  have h : red C ((σ : F') * xF C F') b.1 = red C ((e : F') * u ^ d) b.1 := by rw [hx]
  rw [red_mul hσv.le (valuation_xF _).le, red_mul hev.le (by rw [map_pow, hu1, one_pow]),
    red_pow hu1.le] at h
  have h2 := congrArg b.2.1.valuation h
  have e1 : b.2.1.valuation (red C (σ : F') b.1) = 1 := Qval_one_of_notMem hc hb hσ
  have e2 : b.2.1.valuation (red C (e : F') b.1) = 1 := Qval_one_of_notMem hc hb he
  rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, e1, e2, one_mul, one_mul,
    valuation_x b.2.2, hQu] at h2
  set vu := b.2.1.valuation (redHom hc b.1 uR)
  have hvu0 : vu ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by omega)] at h2
    exact exp_ne_zero h2
  have hvu1 : vu ≤ 1 := (b.2.1.valuation_le_one_iff).2 (red_mem_V hc b.1 uR b.2.2)
  obtain ⟨m, hm⟩ : ∃ m : ℤ, vu = exp m := ⟨log vu, (exp_log hvu0).symm⟩
  rw [hm, ← exp_nsmul] at h2
  have h3 := exp_injective h2
  simp only [nsmul_eq_mul] at h3
  have hord := one_le_ord b.2.2
  have hm0 : m ≤ -1 := by
    by_contra! hm0
    have : (0 : ℤ) ≤ (d : ℤ) * m := mul_nonneg (by positivity) (by omega)
    omega
  refine ⟨?_, fun hd' ↦ ?_⟩
  · have : (d : ℤ) ≤ (ord (red C (xF C F') b.1) b.2.1 : ℤ) := by nlinarith
    exact_mod_cast this
  · rw [hm]
    congr 1
    rw [hd'] at h3
    have hd0 : (0 : ℤ) < d := by exact_mod_cast hd
    nlinarith

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  [Algebra.IsSeparable (RatFunc C) F']

include hp hp1 in
/-- **Exact node data from a node coordinate of the right degree.** -/
theorem exists_nodeData_of_coord (hc0 : c ≠ 0) [Fintype (Ext C F')] (P' : Ideal (Rint c F'))
    [P'.IsMaximal] (hP : P'.comap (algebraMap (nodeRing c) (Rint c F')) = tubeIdeal c) {d : ℕ}
    (hd : 1 ≤ d) (hvd : vertexDegree hc P' ≤ d) (u : F') (σ e : Rint c F') (hσ : σ ∉ P')
    (he : e ∉ P') (hx : (σ : F') * xF C F' = e * u ^ d) (uR σu : Rint c F') (hσu : σu ∉ P')
    (huR : (uR : F') = σu * u) :
    ∃ b₁ : OuterBranch C F', outerBranches hc P' = {b₁} ∧ Nonempty (NodeData hc P' b₁) := by
  classical
  obtain ⟨b₀, hb₀⟩ := exists_outerBranch hp hp1 hc hc0 P' hP
  set S := Finset.univ.sigma fun v : Ext C F' ↦ (zeros 𝓀 (red C (xF C F') v)).attach
  set f : (Σ v : Ext C F', {Q // Q ∈ zeros 𝓀 (red C (xF C F') v)}) → ℕ := fun b ↦
    if placeIdeal hc b.1 b.2.2 = P' then ord (red C (xF C F') b.1) b.2.1 else 0
  have hvsum : vertexDegree hc P' = ∑ b ∈ S, f b := vertexDegree_eq_sum hc P'
  have hmem : ∀ b : OuterBranch C F', (⟨b.1, b.2⟩ : Σ v : Ext C F',
      {Q // Q ∈ zeros 𝓀 (red C (xF C F') v)}) ∈ S := fun b ↦
    Finset.mem_sigma.2 ⟨Finset.mem_univ _, Finset.mem_attach _ _⟩
  have key := fun b hb ↦ ord_x_of_coord hc b hb hd u σ e hσ he hx uR σu hσu huR
  have hfb : ∀ b : OuterBranch C F', placeIdeal hc b.1 b.2.2 = P' →
      f ⟨b.1, b.2⟩ = ord (red C (xF C F') b.1) b.2.1 := fun b hb ↦ if_pos hb
  -- uniqueness of the branch
  have huniq : ∀ b : OuterBranch C F', placeIdeal hc b.1 b.2.2 = P' → b = b₀ := by
    intro b hb
    by_contra hne
    have hne' : (⟨b.1, b.2⟩ : Σ v : Ext C F', {Q // Q ∈ zeros 𝓀 (red C (xF C F') v)}) ≠
        ⟨b₀.1, b₀.2⟩ := fun h ↦ hne (by obtain ⟨_, _⟩ := b; obtain ⟨_, _⟩ := b₀; exact h)
    have h2 := Finset.add_le_sum (f := f) (fun _ _ ↦ Nat.zero_le _) (hmem b) (hmem b₀) hne'
    rw [hfb b hb, hfb b₀ hb₀, ← hvsum] at h2
    have := (key b hb).1
    have := (key b₀ hb₀).1
    omega
  have hord : ord (red C (xF C F') b₀.1) b₀.2.1 = d := by
    have h1 := Finset.single_le_sum (f := f) (fun _ _ ↦ Nat.zero_le _) (hmem b₀)
    rw [hfb b₀ hb₀, ← hvsum] at h1
    exact le_antisymm (h1.trans hvd) (key b₀ hb₀).1
  refine ⟨b₀, ?_, nonempty_nodeData_of_coord hc hc0 hd u σ e hσ he hx uR σu hσu huR
    ((key b₀ hb₀).2 hord)⟩
  ext b
  rw [Set.mem_singleton_iff]
  exact ⟨fun hb ↦ huniq b hb, fun h ↦ h ▸ hb₀⟩

end Branch

end GaussTube

end SemistableReduction
