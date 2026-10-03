/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.Exhausting

/-!
# Points of the normalized node chart

Blueprint §9.9, S7.5. Let `R' = Rint c F'` be the integral closure of the node chart.

* `ringHom_eq_of_ker_eq`: two homomorphisms `R' → k` which are the residue map on the constants
  and have the same kernel coincide; hence all branches through a point `P'` have the same
  residue map `R' → R'/P' = k` (`placeHom_eq_of_mem_outer`, `placeHom_rintEquiv_eq_of_mem_inner`);
* `isNodeODP_of_jets`: a point with one outer and one inner branch at which the local ring
  approximates the fibre product of the two branches to every order is an ordinary double point
  (`IsNodeODP`).
-/

open WithZero

namespace SemistableReduction

namespace GaussTube

open FundamentalInequality GaussStability GaussFibre ZariskiModel PlaceNorm

universe u

variable {C : Type u} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  {F' : Type*} [Field F'] [Algebra (RatFunc C) F'] [Algebra C F']
  [IsScalarTower C (RatFunc C) F'] [FiniteDimensional (RatFunc C) F']

attribute [local instance] isCurveFunctionField DiscreteCoefficients.isAlgClosed_residueField

local notation "𝓀" => IsLocalRing.ResidueField (HenselComplete.integers C)

variable {c : C} (hc : ‖c‖ < 1) (hc0 : c ≠ 0)

omit [IsAlgClosed C] [Algebra C F'] [IsScalarTower C (RatFunc C) F']
  [FiniteDimensional (RatFunc C) F'] in
/-- Two homomorphisms `R' → k` which are the residue map on the constants and have the same kernel
coincide. -/
lemma ringHom_eq_of_ker_eq {f g : Rint c F' →+* 𝓀}
    (hf : ∀ b, f (constR c b) = IsLocalRing.residue _ b)
    (hg : ∀ b, g (constR c b) = IsLocalRing.residue _ b) (h : RingHom.ker f = RingHom.ker g) :
    f = g := by
  ext r
  obtain ⟨b, hb⟩ := IsLocalRing.residue_surjective (f r)
  have hmem : r - constR c b ∈ RingHom.ker f := by
    rw [RingHom.mem_ker, map_sub, hf, hb, sub_self]
  rw [h, RingHom.mem_ker, map_sub, hg, sub_eq_zero] at hmem
  rw [hmem, ← hb]

/-- The residue map of a branch on the constants. -/
lemma placeHom_constR (v : Ext C F')
    {Q : CurvePlace 𝓀 (IsLocalRing.ResidueField v.1.valuationSubring)}
    (hQ : Q ∈ zeros 𝓀 (red C (xF C F') v)) (b : HenselComplete.integers C) :
    placeHom hc v hQ (constR c b) = IsLocalRing.residue _ b := by
  change Q.res (redHom hc v (constR c b)) = _
  rw [redHom_constR, Q.res_algebraMap]

/-- All outer branches through a point have the same residue map. -/
lemma placeHom_eq_of_mem_outer {P' : Ideal (Rint c F')} {b b' : OuterBranch C F'}
    (hb : b ∈ outerBranches hc P') (hb' : b' ∈ outerBranches hc P') :
    placeHom hc b.1 b.2.2 = placeHom hc b'.1 b'.2.2 :=
  ringHom_eq_of_ker_eq (placeHom_constR hc b.1 b.2.2) (placeHom_constR hc b'.1 b'.2.2)
    (hb.trans hb'.symm)

/-- An inner branch through a point has the residue map of the outer branches. -/
lemma placeHom_rintEquiv_eq_of_mem_inner {P' : Ideal (Rint c F')} {b : OuterBranch C F'}
    {b' : OuterBranch C (Inv c hc0 F')} (hb : b ∈ outerBranches hc P')
    (hb' : b' ∈ innerBranches hc hc0 P') :
    (placeHom hc b'.1 b'.2.2).comp (rintEquiv hc0).toRingHom = placeHom hc b.1 b.2.2 := by
  refine ringHom_eq_of_ker_eq (fun β ↦ ?_) (placeHom_constR hc b.1 b.2.2) ?_
  · change placeHom hc b'.1 b'.2.2 (rintEquiv hc0 (constR c β)) = _
    rw [rintEquiv_constR, placeHom_constR]
  · rw [← RingHom.comap_ker]
    change (placeIdeal hc b'.1 b'.2.2).comap _ = placeIdeal hc b.1 b.2.2
    rw [hb', hb, Ideal.comap_comap]
    convert Ideal.comap_id P'
    ext r
    exact congrArg Subtype.val ((rintEquiv hc0).symm_apply_apply r)

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)

include hp hp1 in
/-- **Ordinary double points from jets**: a point with exactly one outer branch `(v₁, Q₁)` and one
inner branch `(w₂, Q₂)` at which every pair `(a, b)` of the fibre product is approximated by
fractions of `R'` to every order is an ordinary double point. -/
theorem isNodeODP_of_jets {P' : Ideal (Rint c F')} {b₁ : OuterBranch C F'}
    {b₂ : OuterBranch C (Inv c hc0 F')} (h₁ : outerBranches hc P' = {b₁})
    (h₂ : innerBranches hc hc0 P' = {b₂})
    (hjet : ∀ a ∈ b₁.2.1.V, ∀ b ∈ b₂.2.1.V, b₁.2.1.res a = b₂.2.1.res b → ∀ M : ℕ,
      ∃ y s : Rint c F', s ∉ P' ∧
        b₁.2.1.valuation (redHom hc b₁.1 y / redHom hc b₁.1 s - a) ≤ exp (-(M : ℤ)) ∧
        b₂.2.1.valuation (redHomInv hc hc0 b₂.1 y / redHomInv hc hc0 b₂.1 s - b) ≤
          exp (-(M : ℤ))) :
    IsNodeODP hc hc0 P' := by
  obtain ⟨v₁, Q₁, hQ₁⟩ := b₁
  obtain ⟨w₂, Q₂, hQ₂⟩ := b₂
  have hP₁ : placeIdeal hc v₁ hQ₁ = P' := by
    have : (⟨v₁, Q₁, hQ₁⟩ : OuterBranch C F') ∈ outerBranches hc P' := by rw [h₁]; rfl
    exact this
  have hP₂ : placeIdeal hc w₂ hQ₂ = P'.comap (rintEquiv hc0).symm.toRingHom := by
    have : (⟨w₂, Q₂, hQ₂⟩ : OuterBranch C (Inv c hc0 F')) ∈ innerBranches hc hc0 P' := by
      rw [h₂]; rfl
    exact this
  have hoth₁ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C F') v₁)), R ≠ Q₁ →
      placeIdeal hc v₁ hR ≠ placeIdeal hc v₁ hQ₁ := by
    intro R hR hne heq
    have : (⟨v₁, R, hR⟩ : OuterBranch C F') ∈ outerBranches hc P' := by
      change placeIdeal hc v₁ hR = P'
      rw [heq, hP₁]
    rw [h₁, Set.mem_singleton_iff] at this
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact hne (congrArg Subtype.val this)
  have hoth₂ : ∀ R (hR : R ∈ zeros 𝓀 (red C (xF C (Inv c hc0 F')) w₂)), R ≠ Q₂ →
      placeIdeal hc w₂ hR ≠ placeIdeal hc w₂ hQ₂ := by
    intro R hR hne heq
    have : (⟨w₂, R, hR⟩ : OuterBranch C (Inv c hc0 F')) ∈ innerBranches hc hc0 P' := by
      change placeIdeal hc w₂ hR = _
      rw [heq, hP₂]
    rw [h₂, Set.mem_singleton_iff] at this
    simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at this
    exact hne (congrArg Subtype.val this)
  subst hP₁
  exact ⟨⟨v₁, Q₁, hQ₁⟩, ⟨w₂, Q₂, hQ₂⟩, h₁, h₂, fun a ha b hb hab ↦
    exists_fp hc hc0 hp hp1 v₁ hQ₁ w₂ hQ₂ hP₂ hoth₁ hoth₂ (hjet · · · ·) ha hb hab⟩

end GaussTube

end SemistableReduction
