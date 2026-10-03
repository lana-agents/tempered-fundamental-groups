/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.SectionLift

/-!
# The genus formula with the total `δ` of the special fibre

Blueprint §9.9, S7⁺.6. Let `H_m = secSpace m ⊆ Π_w κ(w)` be the sections of `O(m (x̄)_∞)` on the
special fibre of the normalization of `ℙ¹_{O_C}` in `F` (Čech form: `v ∈ redRing x` with
`x̄⁻ᵐ v ∈ redRing x⁻¹`). Then `H_m ⊆ W_m = Π_w L(m (x̄)_∞)` (G6.5), and for `m ≫ 0`
`dim H_m = ℓ(m (x)_∞)` (S7⁺.5: every section lifts; reductions of independent lifts are
independent). With Riemann–Roch on `F` and on the residue curves:

  `g(F) + #{w} - 1 = Σ_w g(κ(w)) + codim_{W_m} H_m`  (`genus_add_card_sub_one_eq`),

i.e. `g(F) = 1 + Σ_w (g(κ(w)) - 1) + δ` with `δ = codim_{W_m} H_m` the total `δ`-invariant of the
special fibre.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal

namespace SemistableReduction

open FundamentalInequality GaussStability CurvePlace LatticeReduction

namespace GaussFibre

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F] [Fintype (Ext C F)]

local notation "𝓀" => ResidueField (HenselComplete.integers C)

attribute [local instance] isCurveFunctionField_F isCurveFunctionField
  DiscreteCoefficients.isAlgClosed_residueField

variable (C F) in
/-- The sections of `O(m (x̄)_∞)` on the special fibre: elements `v` of the reduced chart ring at
`0` with `x̄⁻ᵐ v` in the reduced chart ring at `∞`. -/
def secSpace (m : ℕ) : Submodule 𝓀 (Π w : Ext C F, ResidueField w.1.valuationSubring) where
  carrier := {v | v ∈ redRing C F (xF C F) ∧ ∃ u ∈ redRing C F (xF C F)⁻¹,
    ∀ w, v w = red C (xF C F) w ^ m * u w}
  add_mem' := by
    rintro v v' ⟨hv, u, hu, huv⟩ ⟨hv', u', hu', huv'⟩
    exact ⟨add_mem hv hv', u + u', add_mem hu hu', fun w ↦ by
      simp only [Pi.add_apply, huv w, huv' w, mul_add]⟩
  zero_mem' := ⟨zero_mem _, 0, zero_mem _, fun w ↦ by simp⟩
  smul_mem' := by
    rintro c v ⟨hv, u, hu, huv⟩
    have hc (t : F) : (c • v : Π w : Ext C F, ResidueField w.1.valuationSubring) =
        (fun w : Ext C F ↦ algebraMap 𝓀 (ResidueField w.1.valuationSubring) c) * v := by
      funext w
      simp [Algebra.smul_def]
    refine ⟨?_, (fun w : Ext C F ↦ algebraMap 𝓀 (ResidueField w.1.valuationSubring) c) * u,
      mul_mem (algebraMap_mem_redRing _ c) hu, fun w ↦ ?_⟩
    · rw [hc 0]
      exact mul_mem (algebraMap_mem_redRing _ c) hv
    · simp only [Pi.smul_apply, Pi.mul_apply, huv w, Algebra.smul_def]
      ring

/-- Reductions of elements of `L(m (x)_∞)` of norm `≤ 1` are sections. -/
lemma red_mem_secSpace {m : ℕ} {f : F} (hf : f ∈ rrSpace (m • poleDivisor C (xF C F)))
    (hn : gnorm C f ≤ 1) : (fun w ↦ red C f w) ∈ secSpace C F m := by
  have hx1 : gnorm C ((xF C F)⁻¹ ^ m) ≤ 1 :=
    gnorm_le_iff.2 fun w ↦ by rw [map_pow, valuation_xF_inv, one_pow]
  refine ⟨red_mem_redRing ⟨isIntegral_of_mem_rrSpace hf, hn⟩,
    _, red_mem_redRing ⟨isIntegral_div_of_mem_rrSpace hf,
      (gnorm_mul_le _ _).trans (mul_le_one' hn hx1)⟩, fun w ↦ ?_⟩
  have hfw : w.1 f ≤ 1 := (le_gnorm w f).trans hn
  have hxw : w.1 ((xF C F)⁻¹ ^ m) ≤ 1 := by rw [map_pow, valuation_xF_inv, one_pow]
  have hx0 : red C (xF C F) w ≠ 0 := fun h ↦ transcendental_red_x w (h ▸ isAlgebraic_zero)
  change red C f w = _
  rw [red_mul hfw hxw, red_pow (valuation_xF_inv w).le, red_inv_xF, mul_left_comm, ← mul_pow,
    mul_inv_cancel₀ hx0, one_pow, mul_one]

variable {ι : Type*} [Fintype ι] {b : Module.Basis ι (RatFunc C) F}
  (hb : ∀ φ : ι → RatFunc C, gnorm C (∑ i, φ i • b i) = Finset.univ.sup fun i ↦ gauss1 C (φ i))
include hb

/-- **G6.5 for sections**: `H_m ⊆ Π_w L(m (x̄)_∞)`. -/
theorem secSpace_le_piRR (m : ℕ) : secSpace C F m ≤ piRR C F m := by
  rintro v ⟨⟨a, ha, rfl⟩, _, ⟨b', hb', rfl⟩, huv⟩ w -
  intro Q
  dsimp only
  rw [Finsupp.smul_apply, poleDivisor_apply, nsmul_eq_mul]
  by_cases hx : red C (xF C F) w ∈ Q.V
  · have := red_mem_of_isIntegral hb ha.2 ha.1 w Q.V Q.algebraMap_mem hx
    refine (Q.valuation_le_one_iff.2 this).trans ?_
    rw [← exp_zero, exp_le_exp]
    positivity
  · have hxinv : red C (xF C F)⁻¹ w ∈ Q.V := by
      rw [red_inv_xF]
      exact (Q.V.mem_or_inv_mem _).resolve_left hx
    have hmem := red_mem_of_isIntegral_inv hb hb'.2 hb'.1 w Q.V Q.algebraMap_mem hxinv
    simp only at huv
    rw [huv w, map_mul, map_pow, Q.valuation_eq_exp_poleOrder hx]
    calc exp (Q.poleOrder (red C (xF C F) w) : ℤ) ^ m * Q.valuation (red C b' w) ≤
        exp (Q.poleOrder (red C (xF C F) w) : ℤ) ^ m * 1 := by
          gcongr
          exact Q.valuation_le_one_iff.2 hmem
      _ = _ := by rw [mul_one, ← exp_nsmul, nsmul_eq_mul]

lemma finiteDimensional_secSpace (m : ℕ) : FiniteDimensional 𝓀 (secSpace C F m) :=
  Submodule.finiteDimensional_of_le (secSpace_le_piRR hb m)

omit [IsAlgClosed C] [FiniteDimensional (RatFunc C) F] hb in
/-- Lifts of independent reductions are independent. -/
lemma linearIndependent_of_red {n : ℕ} {f : Fin n → F} (hf1 : ∀ i, gnorm C (f i) ≤ 1)
    (hind : LinearIndependent 𝓀 fun i ↦ (fun w ↦ red C (f i) w :
      Π w : Ext C F, ResidueField w.1.valuationSubring)) :
    LinearIndependent C f := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  obtain ⟨i₀, hi₀⟩ := hne
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun i ↦ ‖c i‖₊) ⟨i₀, Finset.mem_univ _⟩
  have hcj : c j ≠ 0 := by
    intro h
    have := hj i₀ (Finset.mem_univ _)
    rw [h, nnnorm_zero, nonpos_iff_eq_zero, nnnorm_eq_zero] at this
    exact hi₀ this
  set d : Fin n → C := fun i ↦ (c j)⁻¹ * c i
  have hd1 (i : Fin n) : ‖d i‖₊ ≤ 1 := by
    rw [nnnorm_mul, nnnorm_inv, inv_mul_le_one₀ (nnnorm_pos.2 hcj)]
    exact hj i (Finset.mem_univ i)
  have hdj : d j = 1 := inv_mul_cancel₀ hcj
  have hsum : ∑ i, d i • f i = 0 := by
    simp only [d, mul_smul, ← Finset.smul_sum, hc, smul_zero]
  set r : Fin n → 𝓀 := fun i ↦ residue (HenselComplete.integers C) ⟨d i, by
    simpa using hd1 i⟩
  have hr : ∑ i, r i • (fun w ↦ red C (f i) w :
      Π w : Ext C F, ResidueField w.1.valuationSubring) = 0 := by
    funext w
    have hw (i : Fin n) : w.1 (d i • f i) ≤ 1 := by
      rw [Algebra.smul_def, map_mul, valuation_algebraMap_C']
      exact mul_le_one' (hd1 i) ((le_gnorm w _).trans (hf1 i))
    have := congrArg (fun g ↦ red C g w) hsum
    simp only [red_zero] at this
    rw [red_sum _ _ fun i _ ↦ hw i] at this
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun i _ ↦
      (red_smul _ (hd1 i) ((le_gnorm w _).trans (hf1 i))).symm
  have := Fintype.linearIndependent_iff.1 hind r hr j
  simp only [r, hdj] at this
  rw [show (⟨(1 : C), by simp⟩ : HenselComplete.integers C) = 1 from rfl, map_one] at this
  exact one_ne_zero this

variable [CharZero C]

/-- **Every section lifts** (S7⁺.5): for `m ≫ 0`, `dim H_m = ℓ(m (x)_∞)`. -/
theorem exists_finrank_secSpace_eq : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    Module.finrank 𝓀 (secSpace C F m) = ell (m • poleDivisor C (xF C F)) := by
  obtain ⟨m₀, hm₀⟩ := exists_lift (b := b) hb
  refine ⟨m₀, fun m hm ↦ le_antisymm ?_ ?_⟩
  · -- lift a basis
    haveI := finiteDimensional_secSpace hb m
    haveI : Module.Free 𝓀 (secSpace C F m) := Module.Free.of_divisionRing _ _
    set B := Module.finBasis 𝓀 (secSpace C F m)
    have hlift (i : Fin (Module.finrank 𝓀 (secSpace C F m))) :
        ∃ f ∈ rrSpace (m • poleDivisor C (xF C F)), gnorm C f ≤ 1 ∧
          (fun w ↦ red C f w) = (B i : Π w : Ext C F, ResidueField w.1.valuationSubring) := by
      obtain ⟨⟨a, ha, hav⟩, u, ⟨b', hb', rfl⟩, huv⟩ := (B i).2
      obtain ⟨f, hf, hfn, hfa⟩ := hm₀ m hm a ha b' hb' fun w ↦ by
        rw [← huv w]
        exact congrFun hav w
      exact ⟨f, hf, hfn, funext fun w ↦ (hfa w).trans (congrFun hav w)⟩
    choose f hf hfn hfB using hlift
    have hli : LinearIndependent C fun i ↦
        (⟨f i, hf i⟩ : rrSpace (m • poleDivisor C (xF C F))) := by
      refine LinearIndependent.of_comp (rrSpace (m • poleDivisor C (xF C F))).subtype ?_
      refine linearIndependent_of_red (f := f) hfn ?_
      have hfun : (fun i ↦ (fun w ↦ red C (f i) w :
          Π w : Ext C F, ResidueField w.1.valuationSubring)) =
          fun i ↦ (B i : Π w : Ext C F, ResidueField w.1.valuationSubring) := funext hfB
      rw [hfun]
      exact B.linearIndependent.map' (secSpace C F m).subtype (Submodule.ker_subtype _)
    have := hli.fintype_card_le_finrank
    simpa [ell] using this
  · haveI := nonempty_ext_of_orthonormal hb
    haveI := finiteDimensional_secSpace hb m
    exact finrank_le_of_red_mem b hb _ _ fun f hf hn ↦ red_mem_secSpace hf hn

/-- **The genus formula with total `δ`** (S7⁺.6): for `m ≫ 0`,
`g(F) + #{w} - 1 = Σ_w g(κ(w)) + codim_{W_m} H_m`. -/
theorem genus_add_card_sub_one_eq
    (hsum : ∑ w : Ext C F, inertiaDeg (gauss1 C) w.1 = Module.finrank (RatFunc C) F) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → secSpace C F m ≤ piRR C F m ∧
      (genus C F : ℤ) + Fintype.card (Ext C F) - 1 =
        (∑ w : Ext C F, (genus 𝓀 (ResidueField w.1.valuationSubring) : ℤ)) +
          ((Module.finrank 𝓀 (piRR C F m) : ℤ) - Module.finrank 𝓀 (secSpace C F m)) := by
  classical
  obtain ⟨m₁, hm₁⟩ := exists_finrank_secSpace_eq hb
  obtain ⟨cF, hcF⟩ := ell_eq_of_le_degree (k := C) (κ := F)
  choose cw hcw using fun w : Ext C F ↦
    ell_eq_of_le_degree (k := 𝓀) (κ := ResidueField w.1.valuationSubring)
  set N := Module.finrank (RatFunc C) F
  have hN : 1 ≤ N := Module.finrank_pos
  refine ⟨m₁ + cF.toNat + ∑ w, (cw w).toNat, fun m hm ↦ ⟨secSpace_le_piRR hb m, ?_⟩⟩
  have hdegF : (m • poleDivisor C (xF C F)).degree = m * N := by
    rw [map_nsmul, degree_poleDivisor xF_notMem_range, finrank_adjoin_xF, nsmul_eq_mul]
  have hxw (w : Ext C F) :
      red C (xF C F) w ∉ (algebraMap 𝓀 (ResidueField w.1.valuationSubring)).range := by
    rintro ⟨c, hc⟩
    exact transcendental_red_x w (hc ▸ isAlgebraic_algebraMap c)
  have hfw (w : Ext C F) : 1 ≤ inertiaDeg (gauss1 C) w.1 := by
    haveI : Module.Finite (ResidueField (gauss1 C).valuationSubring)
      (ResidueField w.1.valuationSubring) := finite_residueField
    exact Module.finrank_pos
  have hdegw (w : Ext C F) : (m • poleDivisor 𝓀 (red C (xF C F) w)).degree =
      m * inertiaDeg (gauss1 C) w.1 := by
    rw [map_nsmul, degree_poleDivisor (hxw w), finrank_adjoin_red_x, nsmul_eq_mul]
  have hm1 : cF ≤ m := by
    have h1 := Int.self_le_toNat cF
    have h2 : (0 : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) := Finset.sum_nonneg fun _ _ ↦ by positivity
    have h3 : ((m₁ + cF.toNat + ∑ w, (cw w).toNat : ℕ) : ℤ) ≤ m := by exact_mod_cast hm
    push_cast at h3
    linarith [Int.natCast_nonneg m₁]
  have hmw (w : Ext C F) : cw w ≤ m := by
    have h1 := Int.self_le_toNat (cw w)
    have h2 : ((cw w).toNat : ℤ) ≤ ∑ w, ((cw w).toNat : ℤ) :=
      Finset.single_le_sum (f := fun w ↦ ((cw w).toNat : ℤ)) (fun _ _ ↦ by positivity)
        (Finset.mem_univ w)
    have h3 : ((m₁ + cF.toNat + ∑ w, (cw w).toNat : ℕ) : ℤ) ≤ m := by exact_mod_cast hm
    push_cast at h3
    linarith [Int.natCast_nonneg m₁, Int.natCast_nonneg cF.toNat]
  have hF := hcF _ (by rw [hdegF]; nlinarith)
  have hw (w : Ext C F) := hcw w _ (by
    rw [hdegw]
    have : (m : ℤ) ≤ m * inertiaDeg (gauss1 C) w.1 := by
      exact_mod_cast Nat.le_mul_of_pos_right m (hfw w)
    linarith [hmw w])
  have hsec := hm₁ m (by omega)
  rw [hsec, finrank_piRR]
  push_cast
  rw [hF, hdegF]
  simp only [hw, hdegw]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsumZ : (∑ w : Ext C F, (inertiaDeg (gauss1 C) w.1 : ℤ)) = N := by
    exact_mod_cast hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsumZ]
  ring

end GaussFibre

end SemistableReduction
