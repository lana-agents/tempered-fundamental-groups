/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.TreeDivisor

/-!
# Reductions at the vertices away from the nodes

Blueprint §9.9, S7.5. Let `T` be tree data, `D_m = m Σⱼ (x - bⱼ)₀` (`TreeData.D`), and
`f ∈ L(D_m)` with value `≤ 1` at all extensions of all vertices. For an extension `W` of the vertex
`i` with residue curve `κ(W)` and `x̄ᵢ` the reduction of the vertex coordinate:

* `isIntegral_clear`: `f Πⱼ (x - bⱼ)ᵐ` is integral over `C[x]`;
* `valuation_red_le_affine`: at a place `Q` of `κ(W)` where `x̄ᵢ` is regular and which is not a
  zero of the reduction of an edge coordinate of a child edge, `ord_Q f̄ ≥ -m ord_Q (x̄ᵢ - β̄ᵢ)`
  (`βᵢ = (bᵢ - aᵢ)/cᵢ`);
* `valuation_red_le_root`: at a pole of `x̄ᵢ`, for a vertex without parent edge, `f̄` is regular.
-/

open Polynomial IsLocalRing Valuation WithZero
open scoped NNReal IntermediateField

namespace SemistableReduction

open FundamentalInequality GaussStability GaussFibre

namespace TreeCount

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] (T : TreeData C)
  {F' : Type*} [Field F'] [Algebra C F'] [IsAlgClosed C] [IsCurveFunctionField C F']
  {x₀ : F'} (hx₀ : Transcendental C x₀)

local notation "𝓀" => ResidueField (HenselComplete.integers C)

variable (x₀) in
/-- The divisor `D_m = m Σⱼ (x₀ - bⱼ)₀`. -/
noncomputable def TreeData.D (m : ℕ) : CurveDivisor C F' :=
  m • ∑ j, zeroDiv C (x₀ - algebraMap C F' (T.b j))

omit [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField C F'] in
include hx₀ in
lemma xF_sub_ne_zero (b : C) : x₀ - algebraMap C F' b ≠ 0 := by
  intro h
  apply hx₀
  rw [sub_eq_zero.1 h]
  exact isAlgebraic_algebraMap b

omit [IsUltrametricDist C] in
include hx₀ in
/-- **Clearing the poles**: `f Πⱼ (x - bⱼ)ᵐ` is integral over `C[x]`. -/
lemma isIntegral_clear {m : ℕ} {f : F'} (hf : f ∈ rrSpace (T.D x₀ m)) :
    IsIntegral (Algebra.adjoin C {x₀})
      (f * ∏ j, (x₀ - algebraMap C F' (T.b j)) ^ m) := by
  refine CurveGenerators.isIntegral_of_forall_mem fun P hP ↦ P.valuation_le_one_iff.1 ?_
  exact valuation_mul_prod_le Finset.univ _ (fun j ↦ xF_sub_ne_zero hx₀ (T.b j)) m hf P
    fun j _ ↦ sub_mem hP (P.algebraMap_mem _)

omit [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField C F'] in
/-- Affine changes of the generator do not change `C[t]`. -/
lemma adjoin_affine {t : F'} {α β : C} (hα : α ≠ 0) :
    Algebra.adjoin C {algebraMap C F' α * t + algebraMap C F' β} = Algebra.adjoin C {t} := by
  refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_le ?_)
  · rintro _ rfl
    exact add_mem (mul_mem (Subalgebra.algebraMap_mem _ _) (Algebra.self_mem_adjoin_singleton C t))
      (Subalgebra.algebraMap_mem _ _)
  · intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    have ht : t = algebraMap C F' α⁻¹ * (algebraMap C F' α * t + algebraMap C F' β) -
        algebraMap C F' (β / α) := by
      have : algebraMap C F' α ≠ 0 := by simpa using hα
      rw [map_inv₀, map_div₀]
      field_simp
      ring
    have hmem : algebraMap C F' α⁻¹ * (algebraMap C F' α * t + algebraMap C F' β) -
        algebraMap C F' (β / α) ∈
          Algebra.adjoin C {algebraMap C F' α * t + algebraMap C F' β} :=
      sub_mem (mul_mem (Subalgebra.algebraMap_mem _ _)
        (Algebra.self_mem_adjoin_singleton C _)) (Subalgebra.algebraMap_mem _ _)
    rwa [← ht] at hmem

omit [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField C F'] in
lemma vc_eq_affine (i : T.ι) : T.vc x₀ i =
    algebraMap C F' (T.c i)⁻¹ * x₀ + algebraMap C F' (-(T.a i / T.c i)) := by
  have : algebraMap C F' (T.c i) ≠ 0 := by simpa using T.hc i
  simp only [TreeData.vc, vcoord, map_inv₀, _root_.map_neg, map_div₀]
  field_simp
  ring

omit [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField C F'] in
lemma adjoin_vc (i : T.ι) : Algebra.adjoin C {T.vc x₀ i} = Algebra.adjoin C {x₀} := by
  rw [vc_eq_affine]
  exact adjoin_affine (inv_ne_zero (T.hc i))

omit [IsUltrametricDist C] [IsAlgClosed C] [IsCurveFunctionField C F'] in
/-- Integrality over a smaller subalgebra implies integrality over a larger one. -/
lemma isIntegral_of_adjoin_le {A B : Subalgebra C F'} (h : A ≤ B) {g : F'} (hg : IsIntegral A g) :
    IsIntegral B g :=
  IsIntegral.map_of_comp_eq (Subalgebra.inclusion h).toRingHom (RingHom.id F') rfl hg

/-- `βᵢ = (bᵢ - aᵢ) / cᵢ`, the direction of `bᵢ` at the vertex `i`. -/
noncomputable def TreeData.β (i : T.ι) : C := (T.b i - T.a i) / T.c i

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma TreeData.norm_β_le (i : T.ι) : ‖T.β i‖ ≤ 1 := by
  rw [TreeData.β, norm_div, div_le_one (norm_pos_iff.2 (T.hc i))]
  exact T.hb_mem i

/-- The residue of `βᵢ`. -/
noncomputable def TreeData.βbar (i : T.ι) : 𝓀 :=
  residue (HenselComplete.integers C) ⟨T.β i, (HenselComplete.mem_integers_iff _).2 (T.norm_β_le i)⟩

omit [IsAlgClosed C] [IsCurveFunctionField C F'] in
lemma valuation_xF_sub {i : T.ι} {W : TypeTwo C F'} (hW : IsOver (T.hvc hx₀ i) W) (b : C) :
    W.val (x₀ - algebraMap C F' b) = max ‖T.c i‖₊ ‖b - T.a i‖₊ := by
  have hc : algebraMap C F' (T.c i) ≠ 0 := by simpa using T.hc i
  have heq : x₀ - algebraMap C F' b =
      algebraMap C F' (T.c i) * (T.vc x₀ i - algebraMap C F' ((b - T.a i) / T.c i)) := by
    simp only [TreeData.vc, vcoord, map_div₀, _root_.map_sub]
    field_simp
    ring
  rw [heq, map_mul, TypeTwo.valuation_algebraMap, hW.valuation_sub, nnnorm_div,
    mul_max_of_nonneg _ _ zero_le, mul_div_cancel₀ _ (nnnorm_ne_zero_iff.2 (T.hc i)), mul_one,
    max_comm]

/-- The normalizing constant of `x - bⱼ` at the vertex `i`. -/
noncomputable def TreeData.lam (i j : T.ι) : C :=
  open scoped Classical in if ‖T.b j - T.a i‖ ≤ ‖T.c i‖ then T.c i else T.a i - T.b j

omit [IsUltrametricDist C] [IsAlgClosed C] in
lemma TreeData.lam_ne_zero (i j : T.ι) : T.lam i j ≠ 0 := by
  unfold TreeData.lam
  split_ifs with h
  · exact T.hc i
  · intro h0
    apply h
    rw [sub_eq_zero.1 h0, sub_self, norm_zero]
    exact norm_nonneg _

omit [IsAlgClosed C] [IsCurveFunctionField C F'] in
lemma valuation_fac {i : T.ι} {W : TypeTwo C F'} (hW : IsOver (T.hvc hx₀ i) W) (j : T.ι) :
    W.val ((x₀ - algebraMap C F' (T.b j)) * (algebraMap C F' (T.lam i j))⁻¹) = 1 := by
  rw [map_mul, map_inv₀, TypeTwo.valuation_algebraMap, valuation_xF_sub T hx₀ hW]
  have hl : ‖T.lam i j‖₊ ≠ 0 := nnnorm_ne_zero_iff.2 (T.lam_ne_zero i j)
  unfold TreeData.lam
  split_ifs with h
  · rw [max_eq_left (by exact_mod_cast h), mul_inv_cancel₀ (nnnorm_ne_zero_iff.2 (T.hc i))]
  · have h' : ‖T.c i‖₊ ≤ ‖T.b j - T.a i‖₊ := by
      have := (not_le.1 h).le
      exact_mod_cast this
    rw [max_eq_right h', ← nnnorm_neg (T.a i - T.b j), neg_sub,
      mul_inv_cancel₀ (nnnorm_ne_zero_iff.2 fun h0 ↦ h (by rw [h0, norm_zero]; positivity))]

section Affine

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Reductions at affine places away from the child directions**:
`ord_Q f̄ ≥ -m ord_Q (x̄ᵢ - β̄ᵢ)` at every place `Q` of `κ(W)` where `x̄ᵢ` is regular and the
reductions of the child edge coordinates are units. -/
theorem valuation_red_le_affine {m : ℕ} {f : F'} (hf : f ∈ rrSpace (T.D x₀ m))
    {i : T.ι} (hn : ∀ W : TypeTwo C F', IsOver (T.hvc hx₀ i) W → W.val f ≤ 1)
    {W : TypeTwo C F'} (hW : IsOver (T.hvc hx₀ i) W)
    (Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring)) (hQ : W.red (T.vc x₀ i) ∈ Q.V)
    (hQe : ∀ e, T.par e = i → (W.red (T.ec x₀ e))⁻¹ ∈ Q.V) :
    Q.valuation (W.red f) ≤
      exp ((m • zeroDiv 𝓀 (W.red (T.vc x₀ i) - algebraMap 𝓀 _ (T.βbar i))) Q) := by
  classical
  set fac : T.ι → F' := fun j ↦
    (x₀ - algebraMap C F' (T.b j)) * (algebraMap C F' (T.lam i j))⁻¹
  set g := f * ∏ j, fac j ^ m
  have hfac (W' : TypeTwo C F') (hW' : IsOver (T.hvc hx₀ i) W') (j : T.ι) :
      W'.val (fac j) = 1 := valuation_fac T hx₀ hW' j
  -- integrality and bounds
  have hint : IsIntegral (Algebra.adjoin C {T.vc x₀ i}) g := by
    refine isIntegral_of_adjoin_le (adjoin_vc T i).ge ?_
    have : g = (f * ∏ j, (x₀ - algebraMap C F' (T.b j)) ^ m) *
        algebraMap C F' (∏ j, (T.lam i j)⁻¹ ^ m) := by
      simp only [g, fac, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow, map_inv₀]
      ring
    rw [this]
    exact (isIntegral_clear T hx₀ hf).mul
      (isIntegral_algebraMap (x := (⟨_, Subalgebra.algebraMap_mem _ _⟩ :
        Algebra.adjoin C {x₀})))
  have hg (W' : TypeTwo C F') (hW' : IsOver (T.hvc hx₀ i) W') : W'.val g ≤ 1 := by
    simp only [g, map_mul, map_prod, map_pow, hfac W' hW', one_pow, Finset.prod_const_one,
      mul_one]
    exact hn W' hW'
  have hred := TypeTwo.red_mem_of_isIntegral hp hp1 (T.hvc hx₀ i) hW hg hint Q hQ
  have hf1 : W.val f ≤ 1 := hn W hW
  have hfac1 (j : T.ι) : W.val (fac j) ≤ 1 := (hfac W hW j).le
  have hpow (j : T.ι) : W.val (fac j ^ m) ≤ 1 := by rw [map_pow, hfac W hW j, one_pow]
  have hprod1 : W.val (∏ j, fac j ^ m) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one' fun j _ ↦ hpow j
  rw [TypeTwo.red_mul hf1 hprod1, TypeTwo.red_prod _ _ fun j _ ↦ hpow j] at hred
  -- the factors
  set z := W.red (T.vc x₀ i) - algebraMap 𝓀 _ (T.βbar i)
  have hzi : W.red (fac i) = z := by
    have : fac i = T.vc x₀ i - algebraMap C F' (T.β i) := by
      simp only [fac, TreeData.lam, if_pos (T.hb_mem i), TreeData.vc, vcoord, TreeData.β,
        map_div₀, _root_.map_sub]
      have : algebraMap C F' (T.c i) ≠ 0 := by simpa using T.hc i
      field_simp
      ring
    rw [this, TypeTwo.red_sub (by rw [hW.valuation_self]) (by
      rw [TypeTwo.valuation_algebraMap]; exact_mod_cast T.norm_β_le i),
      TypeTwo.red_algebraMap _ (T.norm_β_le i)]
    rfl
  have hunit (j : T.ι) (hj : j ≠ i) : Q.valuation (W.red (fac j)) = 1 := by
    by_cases hjd : ‖T.b j - T.a i‖ ≤ ‖T.c i‖
    · obtain ⟨e, he, hej⟩ := T.hb_dir i j hj hjd
      have hec : W.val (T.ec x₀ e) = 1 := by
        rw [← he] at hW
        exact ((T.isOver_ec_iff hx₀ e W).1 hW).valuation_self
      have heq : W.red (fac j) = W.red (T.ec x₀ e) := by
        refine TypeTwo.red_eq_of_sub (hfac1 j) hec.le ?_
        have : fac j - T.ec x₀ e = algebraMap C F' ((T.a (T.chi e) - T.b j) / T.c i) := by
          simp only [fac, TreeData.lam, if_pos hjd, TreeData.ec, vcoord, he, map_div₀,
            _root_.map_sub]
          have : algebraMap C F' (T.c i) ≠ 0 := by simpa using T.hc i
          field_simp
          ring
        rw [this, TypeTwo.valuation_algebraMap, nnnorm_div]
        rw [div_lt_one (nnnorm_pos.2 (T.hc i)), ← nnnorm_neg, neg_sub]
        exact_mod_cast hej
      rw [heq]
      have hmem : W.red (T.ec x₀ e) ∈ Q.V := by
        have : T.ec x₀ e = algebraMap C F' 1 * T.vc x₀ i + algebraMap C F'
            (-((T.a (T.chi e) - T.a i) / T.c i)) := by rw [T.ec_eq, he]
        rw [this, map_one, one_mul, TypeTwo.red_add (by rw [hW.valuation_self])
          (by rw [TypeTwo.valuation_algebraMap, nnnorm_neg, nnnorm_div, div_le_one
            (nnnorm_pos.2 (T.hc i))]; exact_mod_cast (he ▸ T.hedge_a e)),
          TypeTwo.red_algebraMap _ (by rw [norm_neg, norm_div, div_le_one
            (norm_pos_iff.2 (T.hc i))]; exact he ▸ T.hedge_a e)]
        exact add_mem hQ (Q.algebraMap_mem _)
      have h1 := Q.valuation_le_one_iff.2 hmem
      have h2 := Q.valuation_le_one_iff.2 (hQe e he)
      rw [map_inv₀] at h2
      have h0 : W.red (T.ec x₀ e) ≠ 0 := TypeTwo.red_ne_zero hec
      exact le_antisymm h1 ((inv_le_one₀ ((Valuation.pos_iff _).2 h0)).1 h2)
    · have heq : W.red (fac j) = 1 := by
        rw [← TypeTwo.red_one (W := W)]
        refine TypeTwo.red_eq_of_sub (hfac1 j) (by simp) ?_
        have hab : T.a i - T.b j ≠ 0 := fun h0 ↦ hjd (by
          rw [show T.b j - T.a i = 0 by rw [← neg_sub, h0, neg_zero], norm_zero]
          exact norm_nonneg _)
        have : fac j - 1 = algebraMap C F' (T.c i / (T.a i - T.b j)) * T.vc x₀ i := by
          simp only [fac, TreeData.lam, if_neg hjd, TreeData.vc, vcoord, map_div₀,
            _root_.map_sub]
          have : algebraMap C F' (T.a i) - algebraMap C F' (T.b j) ≠ 0 := by
            rw [← _root_.map_sub, Ne, map_eq_zero_iff _ (algebraMap C F').injective]
            exact hab
          have : algebraMap C F' (T.c i) ≠ 0 := by simpa using T.hc i
          field_simp
          ring
        rw [this, map_mul, TypeTwo.valuation_algebraMap, hW.valuation_self, mul_one,
          nnnorm_div, div_lt_one (nnnorm_pos.2 hab)]
        have h3 : ‖T.c i‖ < ‖T.a i - T.b j‖ := by
          rw [← norm_neg (T.a i - T.b j), neg_sub]; exact not_le.1 hjd
        exact_mod_cast h3
      rw [heq, map_one]
  -- conclude
  have hz1 : W.val (T.vc x₀ i - algebraMap C F' (T.β i)) = 1 := by
    rw [hW.valuation_sub, max_eq_right (by exact_mod_cast T.norm_β_le i)]
  have hz : z = W.red (T.vc x₀ i - algebraMap C F' (T.β i)) := by
    rw [TypeTwo.red_sub (by rw [hW.valuation_self]) (by
      rw [TypeTwo.valuation_algebraMap]; exact_mod_cast T.norm_β_le i),
      TypeTwo.red_algebraMap _ (T.norm_β_le i)]
    rfl
  have hz0 : z ≠ 0 := by rw [hz]; exact TypeTwo.red_ne_zero hz1
  have hzQ : z ∈ Q.V := sub_mem hQ (Q.algebraMap_mem _)
  have hprod : Q.valuation (∏ j, W.red (fac j ^ m)) = Q.valuation z ^ m := by
    rw [map_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
      Finset.prod_eq_one fun j hj ↦ by
        rw [TypeTwo.red_pow (hfac1 j), map_pow, hunit j (Finset.ne_of_mem_erase hj), one_pow],
      mul_one, TypeTwo.red_pow (hfac1 i), map_pow, hzi]
  have h1 := Q.valuation_le_one_iff.2 hred
  rw [map_mul, hprod, valuation_eq_exp_neg_zeroDiv Q hz0 hzQ, ← exp_nsmul] at h1
  rw [Finsupp.smul_apply]
  have : Q.valuation (W.red f) = Q.valuation (W.red f) * exp (m • -zeroDiv 𝓀 z Q) *
      exp (m • zeroDiv 𝓀 z Q) := by
    rw [mul_assoc, ← exp_add, smul_neg, neg_add_cancel, exp_zero, mul_one]
  rw [this]
  calc Q.valuation (W.red f) * exp (m • -zeroDiv 𝓀 z Q) * exp (m • zeroDiv 𝓀 z Q) ≤
      1 * exp (m • zeroDiv 𝓀 z Q) := by gcongr
    _ = exp (m • zeroDiv 𝓀 z Q) := one_mul _

include hp hp1 in
/-- **Reductions at the poles of the coordinate of a parentless vertex**: `f̄` is regular. -/
theorem valuation_red_le_root {m : ℕ} {f : F'} (hf : f ∈ rrSpace (T.D x₀ m))
    {i : T.ι} (hroot : ∀ e, T.chi e ≠ i)
    (hn : ∀ W : TypeTwo C F', IsOver (T.hvc hx₀ i) W → W.val f ≤ 1)
    {W : TypeTwo C F'} (hW : IsOver (T.hvc hx₀ i) W)
    (Q : CurvePlace 𝓀 (ResidueField W.val.valuationSubring)) (hQ : W.red (T.vc x₀ i) ∉ Q.V) :
    Q.valuation (W.red f) ≤ 1 := by
  classical
  have hc : algebraMap C F' (T.c i) ≠ 0 := by simpa using T.hc i
  have hxa : x₀ - algebraMap C F' (T.a i) ≠ 0 := xF_sub_ne_zero hx₀ _
  have hvc0 : T.vc x₀ i ≠ 0 := by
    simp only [TreeData.vc, vcoord]
    exact div_ne_zero hxa hc
  set β : T.ι → C := fun j ↦ (T.b j - T.a i) / T.c i
  have hβ (j : T.ι) : ‖β j‖ ≤ 1 := by
    simp only [β, norm_div]
    rw [div_le_one (norm_pos_iff.2 (T.hc i))]
    exact T.hroot i hroot j
  set fac : T.ι → F' := fun j ↦ 1 - algebraMap C F' (β j) * (T.vc x₀ i)⁻¹
  have hfac_eq (j : T.ι) : fac j = (x₀ - algebraMap C F' (T.b j)) *
      (x₀ - algebraMap C F' (T.a i))⁻¹ := by
    simp only [fac, β, TreeData.vc, vcoord, map_div₀, _root_.map_sub, inv_div]
    field_simp
    ring
  set g := f * ∏ j, fac j ^ m
  -- integrality over `C[x̃⁻¹]`
  have hint : IsIntegral (Algebra.adjoin C {(T.vc x₀ i)⁻¹}) g := by
    refine CurveGenerators.isIntegral_of_forall_mem fun P hP ↦ ?_
    have hinv : (x₀ - algebraMap C F' (T.a i))⁻¹ ∈ P.V := by
      have : (x₀ - algebraMap C F' (T.a i))⁻¹ = algebraMap C F' (T.c i)⁻¹ *
          (T.vc x₀ i)⁻¹ := by
        simp only [TreeData.vc, vcoord, map_inv₀, inv_div]
        field_simp
      rw [this]
      exact mul_mem (P.algebraMap_mem _) hP
    by_cases hx : x₀ ∈ P.V
    · have hg : g = (f * ∏ j, (x₀ - algebraMap C F' (T.b j)) ^ m) *
          ((x₀ - algebraMap C F' (T.a i))⁻¹) ^ (m * Fintype.card T.ι) := by
        simp only [g, hfac_eq, mul_pow, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, ← pow_mul]
        ring
      rw [hg]
      exact mul_mem (P.valuation_le_one_iff.1 (valuation_mul_prod_le Finset.univ _
        (fun j ↦ xF_sub_ne_zero hx₀ (T.b j)) m hf P fun j _ ↦ sub_mem hx (P.algebraMap_mem _)))
        (pow_mem hinv _)
    · -- a pole of `x`: `f` is regular there
      have hfP : f ∈ P.V := by
        refine P.valuation_le_one_iff.1 ((hf P).trans ?_)
        rw [TreeData.D, Finsupp.smul_apply, Finsupp.finsetSum_apply,
          Finset.sum_eq_zero fun j _ ↦ ?_, smul_zero, exp_zero]
        rw [zeroDiv, poleDivisor_apply, Nat.cast_eq_zero, P.poleOrder_eq_zero_iff]
        refine (P.V.mem_or_inv_mem _).resolve_left fun h ↦ hx ?_
        have : x₀ = (x₀ - algebraMap C F' (T.b j)) + algebraMap C F' (T.b j) := by
          ring
        rw [this]
        exact add_mem h (P.algebraMap_mem _)
      refine mul_mem hfP (prod_mem fun j _ ↦ pow_mem ?_ _)
      rw [hfac_eq]
      have : (x₀ - algebraMap C F' (T.b j)) * (x₀ - algebraMap C F' (T.a i))⁻¹ =
          1 + algebraMap C F' (T.a i - T.b j) * (x₀ - algebraMap C F' (T.a i))⁻¹ := by
        rw [_root_.map_sub]
        field_simp
        ring
      rw [this]
      exact add_mem (one_mem _) (mul_mem (P.algebraMap_mem _) hinv)
  -- bounds
  have hfac1 (W' : TypeTwo C F') (hW' : IsOver (T.hvc hx₀ i) W') (j : T.ι) :
      W'.val (fac j) = 1 := by
    rw [hfac_eq, map_mul, map_inv₀, valuation_xF_sub T hx₀ hW', valuation_xF_sub T hx₀ hW',
      sub_self, nnnorm_zero, max_eq_left zero_le, max_eq_left (by exact_mod_cast T.hroot i hroot j),
      mul_inv_cancel₀ (nnnorm_ne_zero_iff.2 (T.hc i))]
  have hg (W' : TypeTwo C F') (hW' : IsOver (T.hvc hx₀ i) W') : W'.val g ≤ 1 := by
    simp only [g, map_mul, map_prod, map_pow, hfac1 W' hW', one_pow, Finset.prod_const_one,
      mul_one]
    exact hn W' hW'
  have hvc1 : W.val (T.vc x₀ i) = 1 := hW.valuation_self
  have hQinv : W.red (T.vc x₀ i)⁻¹ ∈ Q.V := by
    rw [TypeTwo.red_inv hvc1]
    exact (Q.V.mem_or_inv_mem _).resolve_left hQ
  have hred := TypeTwo.red_mem_of_isIntegral_inv hp hp1 (T.hvc hx₀ i) hW hg hint Q hQinv
  have hpow (j : T.ι) : W.val (fac j ^ m) ≤ 1 := by rw [map_pow, hfac1 W hW j, one_pow]
  have hprod1 : W.val (∏ j, fac j ^ m) ≤ 1 := by
    rw [map_prod]
    exact Finset.prod_le_one' fun j _ ↦ hpow j
  rw [TypeTwo.red_mul (hn W hW) hprod1, TypeTwo.red_prod _ _ fun j _ ↦ hpow j] at hred
  -- the factors are units at `Q`
  have hsmall : Q.valuation (W.red (T.vc x₀ i)⁻¹) < 1 := by
    rw [TypeTwo.red_inv hvc1, map_inv₀]
    have h := (Q.valuation_le_one_iff.2 ((Q.V.mem_or_inv_mem _).resolve_left hQ))
    rw [map_inv₀] at h
    refine lt_of_le_of_ne h fun h1 ↦ hQ ?_
    rw [← Q.valuation_le_one_iff, ← inv_inv (Q.valuation _), h1, inv_one]
  have hunit (j : T.ι) : Q.valuation (W.red (fac j)) = 1 := by
    have hinv1 : W.val (T.vc x₀ i)⁻¹ = 1 := by rw [map_inv₀, hvc1, inv_one]
    have hβ1 : W.val (algebraMap C F' (β j)) ≤ 1 := by
      rw [TypeTwo.valuation_algebraMap]; exact_mod_cast hβ j
    have hprod2 : W.val (algebraMap C F' (β j) * (T.vc x₀ i)⁻¹) ≤ 1 := by
      rw [map_mul]; exact mul_le_one' hβ1 hinv1.le
    have : W.red (fac j) = 1 - W.red (algebraMap C F' (β j)) * W.red (T.vc x₀ i)⁻¹ := by
      simp only [fac]
      rw [TypeTwo.red_sub (by simp) hprod2, TypeTwo.red_one, TypeTwo.red_mul hβ1 hinv1.le]
    rw [this]
    have hs : Q.valuation (W.red (algebraMap C F' (β j)) * W.red (T.vc x₀ i)⁻¹) < 1 := by
      rw [map_mul]
      have h1 : Q.valuation (W.red (algebraMap C F' (β j))) ≤ 1 := by
        rw [TypeTwo.red_algebraMap _ (hβ j)]
        exact Q.valuation_algebraMap_le_one _
      exact mul_lt_one_of_nonneg_of_lt_one_right h1 zero_le hsmall
    rw [Valuation.map_one_sub_of_lt _ hs]
  have h1 := Q.valuation_le_one_iff.2 hred
  rw [map_mul, map_prod, Finset.prod_eq_one fun j _ ↦ by
    rw [TypeTwo.red_pow (hfac1 W hW j).le, map_pow, hunit j, one_pow], mul_one] at h1
  exact h1

end Affine

end TreeCount

end SemistableReduction
