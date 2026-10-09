/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.HarmonicXWalk
import TemperedFundamentalGroups.SemistableReduction.HarmonicX3
import TemperedFundamentalGroups.SemistableReduction.CrossingX1Proof

/-!
# Proof of `Statement.HarmonicX` (Blueprint §9.7, W8′)

* (X0) `x0`; (X3) `ModelCode.x3`;
* (X2): along a crossing walk, `e₁ l i ≥ e' |ΔE i|` for the exponents `E` of the coordinate `u'`
  of `y'` (`walk_exponents`), so `e₁ ∑ l i ≥ e' |E k - E 0| = e₁ e' n' / e₂ = e₁ l'`;
* (X1): the crossing walk of `crossingX1_inc` has strictly monotone exponents of `u'` (directly,
  or through `u' v' = ϖ₂ ^ n'`, `exp_sum`), so every inequality is an equality and the sum of
  `|ΔE i|` telescopes.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction

open CentreGerms ValuativeCentre ModelCode CrossingSource _root_.SemistableReduction

/-- Telescoping for increasing exponents. -/
lemma sum_abs_of_lt {k : ℕ} (E : Fin (k + 1) → ℕ) (h : ∀ i : Fin k, E i.castSucc < E i.succ) :
    ∑ i : Fin k, |(E i.succ : ℚ) - E i.castSucc| = |(E (Fin.last k) : ℚ) - E 0| := by
  have h1 : ∀ i : Fin k, |(E i.succ : ℚ) - E i.castSucc| = (E i.succ : ℚ) - E i.castSucc :=
    fun i ↦ abs_of_nonneg (sub_nonneg.2 (by exact_mod_cast (h i).le))
  rw [Finset.sum_congr rfl fun i _ ↦ h1 i, sum_succ_sub_castSucc k (fun i ↦ (E i : ℚ))]
  refine (abs_of_nonneg ?_).symm
  rw [← sum_succ_sub_castSucc k (fun i ↦ (E i : ℚ))]
  exact Finset.sum_nonneg fun i _ ↦ by
    have := h i; simp only [sub_nonneg]; exact_mod_cast this.le

/-- Telescoping for decreasing exponents. -/
lemma sum_abs_of_gt {k : ℕ} (E : Fin (k + 1) → ℕ) (h : ∀ i : Fin k, E i.succ < E i.castSucc) :
    ∑ i : Fin k, |(E i.succ : ℚ) - E i.castSucc| = |(E (Fin.last k) : ℚ) - E 0| := by
  have h1 : ∀ i : Fin k, |(E i.succ : ℚ) - E i.castSucc| = -((E i.succ : ℚ) - E i.castSucc) :=
    fun i ↦ abs_of_nonpos (by have := h i; simp only [sub_nonpos]; exact_mod_cast this.le)
  rw [Finset.sum_congr rfl fun i _ ↦ h1 i, Finset.sum_neg_distrib,
    sum_succ_sub_castSucc k (fun i ↦ (E i : ℚ))]
  refine (abs_of_nonpos ?_).symm
  rw [← sum_succ_sub_castSucc k (fun i ↦ (E i : ℚ))]
  exact Finset.sum_nonpos fun i _ ↦ by
    have := h i; simp only [sub_nonpos]; exact_mod_cast this.le

/-- **The exponents of `u'` and `v'` add up.** -/
lemma exp_sum {K K₁ K₂ L₁ L₂ : Type u} [Field K] [Field K₁] [Field K₂] [Field L₁] [Field L₂]
    [Algebra K K₁] [Algebra K K₂] [Algebra K₁ L₁] [Algebra K₂ L₂] [Algebra L₂ L₁]
    [Algebra K L₁] [Algebra K L₂] [IsScalarTower K K₁ L₁] [IsScalarTower K K₂ L₂]
    [IsScalarTower K L₂ L₁] {O₁ : ValuationSubring K₁} {O₂ : ValuationSubring K₂}
    {ϖ₁ : O₁} {ϖ₂ : O₂} {ϖ : K} {η₁ : O₁ˣ} {η₂ : O₂ˣ} {e₁ e₂ : ℕ}
    (hϖK₁ : algebraMap K K₁ ϖ = (η₁ : K₁) * (ϖ₁ : K₁) ^ e₁)
    (hϖK₂ : algebraMap K K₂ ϖ = (η₂ : K₂) * (ϖ₂ : K₂) ^ e₂) (W : ValuationSubring L₁)
    (hO₁W : ∀ o : O₁, algebraMap K₁ L₁ (o : K₁) ∈ W)
    (hO₂W : ∀ o : O₂, algebraMap L₂ L₁ (algebraMap K₂ L₂ (o : K₂)) ∈ W)
    (hWϖ : W.valuation (algebraMap K₁ L₁ (ϖ₁ : K₁)) < 1)
    (hW0 : W.valuation (algebraMap K₁ L₁ (ϖ₁ : K₁)) ≠ 0) {u' v' : L₂} {n' : ℕ}
    (huv : u' * v' = algebraMap K₂ L₂ (ϖ₂ : K₂) ^ n') {E q m : ℕ}
    (hE : W.valuation (algebraMap L₂ L₁ u') = W.valuation (algebraMap K₁ L₁ (ϖ₁ : K₁)) ^ E)
    (hq : W.valuation (algebraMap L₂ L₁ v' ^ m) =
      W.valuation (algebraMap K₁ L₁ (ϖ₁ : K₁)) ^ q) :
    E * m * e₂ + q * e₂ = e₁ * n' * m := by
  obtain ⟨ζ, hζ, hζ', hζ0, hζϖ⟩ := exists_zeta (P := W.toSubring) hϖK₁ hϖK₂ hO₁W hO₂W
  have hWζ : W.valuation ζ = 1 := (valuation_eq_one_iff_mem_and_inv_mem W).2 ⟨hζ0, hζ, hζ'⟩
  set p := W.valuation (algebraMap K₁ L₁ (ϖ₁ : K₁))
  have h1 : W.valuation (algebraMap L₂ L₁ u') * W.valuation (algebraMap L₂ L₁ v') =
      W.valuation (algebraMap L₂ L₁ (algebraMap K₂ L₂ (ϖ₂ : K₂))) ^ n' := by
    rw [← map_mul, ← map_mul, huv, map_pow, map_pow]
  have h2 : W.valuation (algebraMap L₂ L₁ (algebraMap K₂ L₂ (ϖ₂ : K₂))) ^ e₂ = p ^ e₁ := by
    rw [← map_pow, hζϖ, map_mul, hWζ, one_mul, map_pow]
  rw [map_pow] at hq
  refine pow_inj hW0 hWϖ ?_
  calc p ^ (E * m * e₂ + q * e₂)
      = ((W.valuation (algebraMap L₂ L₁ u') * W.valuation (algebraMap L₂ L₁ v')) ^ m) ^ e₂ := by
        rw [mul_pow, hE, hq, ← pow_mul, mul_pow, ← pow_mul, ← pow_mul, ← pow_add]
    _ = p ^ (e₁ * n' * m) := by
        rw [h1, pow_right_comm _ m e₂, pow_right_comm _ n' e₂, h2, ← pow_mul, ← pow_mul, mul_assoc]

/-- **`Statement.HarmonicX` holds.** -/
theorem harmonicX : Statement.HarmonicX.{u} := by
  intro K _ _ O _ _ ϖ hϖ K₁ K₂ _ _ _ _ _ _ O₁ O₂ h₁ h₂ _ _ ϖ₁ ϖ₂ hϖ₁ hϖ₂ L₁ L₂
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x c c' ψ j j' hU₁ hU₂ hj hψO _ _ hsplit₁ hsplit₂ hloops₁
    hloops₂
  haveI : Algebra.IsAlgebraic K K₁ := Algebra.IsAlgebraic.of_finite K K₁
  haveI : Algebra.IsAlgebraic K K₂ := Algebra.IsAlgebraic.of_finite K K₂
  obtain ⟨η₁, e₁, he₁, hϖK₁⟩ := exists_ramification h₁ hϖ hϖ₁
  obtain ⟨η₂, e₂, he₂, hϖK₂⟩ := exists_ramification h₂ hϖ hϖ₂
  have hW := hU₁.isWModel
  have hW' := hU₂.isWModel
  have hL₁ : algebraMap K L₁ (ϖ : K) = algebraMap K₁ L₁ (algebraMap K K₁ ϖ) :=
    IsScalarTower.algebraMap_apply K K₁ L₁ _
  have hL₂ : algebraMap K L₂ (ϖ : K) = algebraMap K₂ L₂ (algebraMap K K₂ ϖ) :=
    IsScalarTower.algebraMap_apply K K₂ L₂ _
  have he₁0 : (e₁ : ℚ) ≠ 0 := by exact_mod_cast he₁.ne'
  have he₂0 : (e₂ : ℚ) ≠ 0 := by exact_mod_cast he₂.ne'
  -- the x-length of a node of `c'`
  have hy'data : ∀ y' : c'.scheme, IsNodePt c' y' → ∃ (Q : Subring L₂) (u' v' ε' : L₂) (n' : ℕ)
      (a' β' : K₂) (e' α' : ℕ) (v₁' v₂' : Set c'.scheme) (hv₁' : v₁' ∈ components c')
      (hv₂' : v₂' ∈ components c'),
      UnfoldedNodeGerm O₂ ϖ₂ Q u' v' n' x a' β' e' α' ε' (Wc hW' hv₁') (Wc hW' hv₂') ∧
      NodeBranches O₂ ϖ₂ Q (algebraMap O₂ L₂) u' v' n' (Wc hW' hv₁') (Wc hW' hv₂') ∧
      (Q : Set L₂) = germs c' j' y' ∧ y' ∈ v₁' ∧ y' ∈ v₂' ∧
      ∀ l', IsXLength (algebraMap K L₂ ϖ) O₂ ϖ₂ c' j' x y' l' → l' = e' * n' / e₂ := by
    intro y' hy'
    obtain ⟨Q, u', v', n', a', β', e', α', ε', v₁', v₂', hv₁', hv₂', H', HB', hQg, hy₁', hy₂', -,
      -, hdiv', hsec'⟩ := exists_unfoldedNodeGerm hU₂ hϖ₂ hsplit₂.1 hloops₂ hy'
    refine ⟨Q, u', v', ε', n', a', β', e', α', v₁', v₂', hv₁', hv₂', H', HB', hQg, hy₁', hy₂',
      fun l' hl' ↦ ?_⟩
    rw [hL₂] at hl'
    exact (isXLength_iff_of_unfolded hW' hϖ₂ he₂ hϖK₂ H' HB' hQg hdiv' hsec' l').1 hl'
  refine ⟨fun y hy ↦ ?_, ?_, ?_, x3 h₁ h₂ hϖ₂ hψO⟩
  · -- (X0)
    rw [hL₁]
    exact x0 hU₁ hϖ₁ hsplit₁.1 hloops₁ he₁ hϖK₁ y hy
  · -- (X1)
    intro y' hy' w₁' hw₁' w₂' hw₂' hne hyw₁ hyw₂ v hv hψv l' hl'
    obtain ⟨Q, u', v', ε', n', a', β', e', α', v₁', v₂', hv₁', hv₂', H', HB', hQg, hy₁', hy₂',
      hl'eq⟩ := hy'data y' hy'
    have hdense : Dense (Set.range j'.base) := by
      rw [dense_iff_closure_eq]
      refine Set.eq_univ_of_forall fun y ↦ ?_
      exact closure_mono (Set.singleton_subset_iff.2 (Set.mem_range_self _))
        (specializes_iff_mem_closure.1 (specializes_of_isWModel hW' y))
    obtain ⟨w, hw0, hcross, hwk, a, m, ha, hm, hinc⟩ := crossingX1_inc K O K₁ K₂ O₁ O₂ h₁ h₂ ϖ₁
      ϖ₂ hϖ₁ hϖ₂ L₁ L₂ (algebraMap L₂ L₁ x) c c' ψ j j' hU₁ hj hψO hsplit₁ hloops₁ hdense y' w₁'
      w₂' hw₁' hw₂' hne hyw₁ hyw₂ Q u' v' n' hQg H'.germ HB'.core.u_nonunit HB'.core.v_nonunit
      v hv hψv
    have hnode : ∀ i, IsNodePt c (w.x i) := fun i ↦ (w.joins i).1
    choose l hl using fun i ↦ (x0 hU₁ hϖ₁ hsplit₁.1 hloops₁ he₁ hϖK₁ (w.x i) (hnode i)).1
    obtain ⟨E, hE, hrel, hends⟩ := walk_exponents hϖ₁ hϖ₂ he₁ he₂ hϖK₁ hϖK₂ hU₁ hU₂ hsplit₁.1
      hloops₁ hsplit₂.1 hloops₂ hj hv₁' hv₂' H' HB' hy' hQg hy₁' hy₂' hw₁' hw₂' hne hyw₁ hyw₂ w
      hcross (by rw [hw0]; exact hψv) hwk l hl
    have hϖL : algebraMap K₁ L₁ (ϖ₁ : K₁) = algebraMap O₁ L₁ ϖ₁ := algebraMap_O_K ϖ₁
    have hWϖ : ∀ i, (Wc hW (w.mem_components i)).valuation (algebraMap O₁ L₁ ϖ₁) < 1 :=
      fun i ↦ valuation_ϖ_lt_one hW hϖ₁ ((w.mem_components i).2.1 (gp_mem _))
        (Wc_spec hW _)
    have hW0 : ∀ i, (Wc hW (w.mem_components i)).valuation (algebraMap O₁ L₁ ϖ₁) ≠ 0 :=
      fun i ↦ by rw [← hϖL]; simpa using fun h ↦ hϖ₁.ne_zero (Subtype.ext h)
    -- monotonicity of the exponents
    have hmono : (∀ i : Fin w.k, E i.castSucc < E i.succ) ∨
        (∀ i : Fin w.k, E i.succ < E i.castSucc) := by
      rcases ha with rfl | rfl
      · refine .inl fun i ↦ ?_
        obtain ⟨q, q', hqq, h1, h2⟩ := hinc i
        rw [map_pow, hE, ← pow_mul] at h1 h2
        have e1 := pow_inj (hW0 _) (hWϖ _) h1
        have e2 := pow_inj (hW0 _) (hWϖ _) h2
        exact (Nat.mul_lt_mul_right hm).1 (by rw [e1, e2]; exact hqq)
      · refine .inr fun i ↦ ?_
        obtain ⟨q, q', hqq, h1, h2⟩ := hinc i
        have key : ∀ (k : Fin (w.k + 1)) (q : ℕ),
            (Wc hW (w.mem_components k)).valuation (algebraMap L₂ L₁ a ^ m) =
              (Wc hW (w.mem_components k)).valuation (algebraMap O₁ L₁ ϖ₁) ^ q →
            E k * m * e₂ + q * e₂ = e₁ * n' * m := by
          intro k q hq
          have hgerm : ∀ f ∈ germs c j (gp (w.mem_components k)),
              f ∈ Wc hW (w.mem_components k) := fun f hf ↦
            ((isCentre_iff_dominates c j (specializes_of_isWModel hW _) _).1
              (Wc_spec hW (w.mem_components k))).1 hf
          refine exp_sum hϖK₁ hϖK₂ _ (fun o ↦ ?_) (fun o ↦ ?_) (hϖL ▸ hWϖ k) (hϖL ▸ hW0 k)
            H'.germ.mul_eq (hϖL ▸ hE k) (hϖL ▸ hq)
          · rw [algebraMap_O_K]; exact hgerm _ (algebraMap_mem_germs hW _ o)
          · rw [algebraMap_O_K]
            exact hgerm _ (germs_map ψ j j' hj _ (algebraMap_mem_germs hW' _ o))
        have k1 := key _ _ h1
        have k2 := key _ _ h2
        have : E i.succ * m * e₂ < E i.castSucc * m * e₂ := by
          have : q * e₂ < q' * e₂ := Nat.mul_lt_mul_of_pos_right hqq he₂
          omega
        exact (Nat.mul_lt_mul_right hm).1 ((Nat.mul_lt_mul_right he₂).1 this)
    have hsum : ∑ i : Fin w.k, |(E i.succ : ℚ) - E i.castSucc| =
        |(E (Fin.last w.k) : ℚ) - E 0| := by
      rcases hmono with h | h
      · exact sum_abs_of_lt E h
      · exact sum_abs_of_gt E h
    have hli : ∀ i, l i = e' * |(E i.succ : ℚ) - E i.castSucc| / e₁ := fun i ↦ by
      have hne : E i.castSucc ≠ E i.succ := by
        rcases hmono with h | h
        · exact (h i).ne
        · exact (h i).ne'
      rw [← (hrel i).2 hne]; field_simp
    refine ⟨w, hw0, hcross, hwk, l, fun i ↦ by rw [hL₁]; exact hl i, ?_⟩
    rw [hl'eq l' hl', Finset.sum_congr rfl fun i _ ↦ hli i, ← Finset.sum_div,
      ← Finset.mul_sum, hsum]
    field_simp
    linear_combination (e' : ℚ) * hends
  · -- (X2)
    intro y' hy' w₁' hw₁' w₂' hw₂' hne hyw₁ hyw₂ w hcross hψ0 hψk l hl l' hl'
    obtain ⟨Q, u', v', ε', n', a', β', e', α', v₁', v₂', hv₁', hv₂', H', HB', hQg, hy₁', hy₂',
      hl'eq⟩ := hy'data y' hy'
    have hl₁ : ∀ i, IsXLength (algebraMap K₁ L₁ (algebraMap K K₁ ϖ)) O₁ ϖ₁ c j
        (algebraMap L₂ L₁ x) (w.x i) (l i) := fun i ↦ by rw [← hL₁]; exact hl i
    obtain ⟨E, -, hrel, hends⟩ := walk_exponents hϖ₁ hϖ₂ he₁ he₂ hϖK₁ hϖK₂ hU₁ hU₂ hsplit₁.1
      hloops₁ hsplit₂.1 hloops₂ hj hv₁' hv₂' H' HB' hy' hQg hy₁' hy₂' hw₁' hw₂' hne hyw₁ hyw₂ w
      hcross hψ0 hψk l hl₁
    rw [hl'eq l' hl']
    have h1 : (e' : ℚ) * |(E (Fin.last w.k) : ℚ) - E 0| ≤ (∑ i, l i) * e₁ := by
      calc (e' : ℚ) * |(E (Fin.last w.k) : ℚ) - E 0|
          ≤ e' * ∑ i : Fin w.k, |(E i.succ : ℚ) - E i.castSucc| :=
            mul_le_mul_of_nonneg_left (abs_sub_le_sum_abs (fun i ↦ (E i : ℚ))) (by positivity)
        _ = ∑ i : Fin w.k, e' * |(E i.succ : ℚ) - E i.castSucc| := Finset.mul_sum _ _ _
        _ ≤ ∑ i : Fin w.k, l i * e₁ := Finset.sum_le_sum fun i _ ↦ (hrel i).1
        _ = (∑ i, l i) * e₁ := (Finset.sum_mul _ _ _).symm
    have he₁pos : (0 : ℚ) < e₁ := by exact_mod_cast he₁
    have he₂pos : (0 : ℚ) < e₂ := by exact_mod_cast he₂
    rw [div_le_iff₀ he₂pos]
    have h2 : (e' : ℚ) * |(E (Fin.last w.k) : ℚ) - E 0| * e₂ = e' * (e₁ * n') := by
      rw [mul_assoc, hends]
    nlinarith

end TemperedFundamentalGroups.SemistableReduction
