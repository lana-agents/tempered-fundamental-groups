/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingSource
import TemperedFundamentalGroups.SemistableReduction.SemistableFibreDim

/-!
# Two components through a point from two branch valuations (StrongComponentA (a), NoLoops)

Let `c` be a semistable W-model over a DVR. If `V` is a valuation subring of `L` containing the
germs at a point `y`, with `ϖ ∈ 𝔪_V`, and some non-unit germ `t` at `y` is a `V`-unit, then the
centre `η` of `V` is a generalization of `y`, `η ≠ y`, and `closure {η}` is a component of the
special fibre (`exists_component_of_branch`; maximality by the dimension bound of the special
fibre, `not_chain_Z`). Two such valuations `V₁, V₂` with `V₁(t) = 1 > V₂(t)` give two distinct
components through `y` (`exists_two_components`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {c : TemperedFundamentalGroups.ModelCode O}
  {L : Type u} [Field L] [Algebra K L] [Algebra O L] [IsScalarTower O K L] {x : L}
  {j : Spec (CommRingCat.of L) ⟶ c.scheme}

variable (hW : IsWModel O L x c j)
include hW

/-- **Centres of valuations with `ϖ ∈ 𝔪_V` lie in the special fibre.** -/
lemma mem_Z_of_isCentre {ϖ : O} (hϖ : Irreducible ϖ) {V : ValuationSubring L} {z : c.scheme}
    (hV : IsCentre j V z) (hϖV : V.valuation (algebraMap O L ϖ) < 1) : z ∈ Z c := by
  by_contra hz
  have h := IsCentre.specializes hV
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    c.scheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  letI := ModelCode.sectionsAlgebra c U
  have hmem : algebraMap O Γ(c.scheme, U) ϖ ∉ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal :=
    fun hm ↦ hz ((ModelCode.mem_Z_iff hϖ hU hzU).2 hm)
  rw [ModelCode.mem_primeIdealOf_iff, not_not, Scheme.mem_basicOpen (hx := hzU)] at hmem
  obtain ⟨t, ht⟩ := (isUnit_iff_exists_mul j h _).1 hmem
  have hV' := (isCentre_iff j h V).1 hV
  have h1 := hV'.1 t
  rw [stalkTo_germ, ← ModelCode.toL, ← baseHom_eq_toL, baseHom_eq_of_isWModel hW] at ht
  have h2 := congrArg V.valuation ht
  rw [map_mul, map_one] at h2
  have h3 : V.valuation ((stalkTo j h).hom t) ≤ 1 := (V.valuation_le_one_iff _).2 h1
  have : V.valuation (algebraMap O L ϖ) * V.valuation ((stalkTo j h).hom t) < 1 :=
    mul_lt_one_of_lt_of_le hϖV h3
  rw [h2] at this
  exact lt_irrefl _ this

/-- **A branch valuation gives a component through `y`.** -/
theorem exists_component_of_branch {ϖ : O} (hϖ : Irreducible ϖ) (hss : IsSemistable ϖ c)
    {y : c.scheme} {V : ValuationSubring L} (hyV : ∀ f ∈ germs c j y, f ∈ V)
    (hϖV : V.valuation (algebraMap O L ϖ) < 1) {t : L} (ht : t ∈ germs c j y)
    (htu : ∀ w ∈ germs c j y, t * w ≠ 1) (htV : V.valuation t = 1) :
    ∃ η : c.scheme, IsCentre j V η ∧ η ⤳ y ∧ closure {η} ∈ components c := by
  have hsy := specializes_of_isWModel hW y
  have hV : ∀ s, (stalkTo j hsy).hom s ∈ V := fun s ↦
    hyV _ (by rw [germs_eq_range c j hsy]; exact ⟨s, rfl⟩)
  set η := c.scheme.fromSpecStalk y
    ((Spec.map (CommRingCat.ofHom ((stalkTo j hsy).hom.codRestrict V.toSubring hV)))
      (closedPoint V))
  have hη : IsCentre j V η := isCentre_fromSpecStalk j hsy V hV
  have hηy : η ⤳ y := by
    have : η ∈ Set.range (c.scheme.fromSpecStalk y) := ⟨_, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at this
  have hηZ : η ∈ Z c := mem_Z_of_isCentre hW hϖ hη hϖV
  have hne : ¬ y ⤳ η := by
    intro hyη
    have heq : η = y := (hηy.antisymm hyη).eq
    have hdom := (isCentre_iff_dominates c j (specializes_of_isWModel hW η) V).1 hη
    rw [heq] at hdom
    have := hdom.2 t ht htu
    rw [htV] at this
    exact lt_irrefl _ this
  refine ⟨η, hη, hηy, isIrreducible_singleton.closure,
    closure_minimal (Set.singleton_subset_iff.2 hηZ) (isClosed_Z c), fun w hw hwZ hηw ↦ ?_⟩
  have hw' : IsIrreducible (closure w) := hw.closure
  have hwZ' : closure w ⊆ Z c := closure_minimal hwZ (isClosed_Z c)
  set g := hw'.genericPoint
  have hg : IsGenericPoint g (closure w) := by
    have := hw'.isGenericPoint_genericPoint_closure
    rwa [isClosed_closure.closure_eq] at this
  have hgη : g ⤳ η := hg.specializes (subset_closure (hηw (subset_closure rfl)))
  by_cases hgη' : η ⤳ g
  · have heq : g = η := (hgη.antisymm hgη').eq
    refine le_antisymm (fun z hz ↦ ?_) hηw
    have : z ∈ closure w := subset_closure hz
    rw [← hg.def, heq] at this
    exact this
  · exact (not_chain_Z hϖ hss (hwZ' hg.mem) hηy hgη hne hgη').elim

/-- **Two branch valuations separated by a germ give two components through `y`.** -/
theorem exists_two_components {ϖ : O} (hϖ : Irreducible ϖ) (hss : IsSemistable ϖ c)
    {y : c.scheme} {V₁ V₂ : ValuationSubring L} (hy₁ : ∀ f ∈ germs c j y, f ∈ V₁)
    (hy₂ : ∀ f ∈ germs c j y, f ∈ V₂) (hϖ₁ : V₁.valuation (algebraMap O L ϖ) < 1)
    (hϖ₂ : V₂.valuation (algebraMap O L ϖ) < 1) {t₁ t₂ : L} (ht₁ : t₁ ∈ germs c j y)
    (ht₂ : t₂ ∈ germs c j y) (htu₁ : ∀ w ∈ germs c j y, t₁ * w ≠ 1)
    (htu₂ : ∀ w ∈ germs c j y, t₂ * w ≠ 1) (h₁ : V₁.valuation t₁ = 1)
    (h₂ : V₂.valuation t₂ = 1) (h₁₂ : V₂.valuation t₁ < 1) :
    ∃ v ∈ components c, ∃ w ∈ components c, v ≠ w ∧ y ∈ v ∧ y ∈ w := by
  obtain ⟨η₁, hη₁, hη₁y, hc₁⟩ := exists_component_of_branch hW hϖ hss hy₁ hϖ₁ ht₁ htu₁ h₁
  obtain ⟨η₂, hη₂, hη₂y, hc₂⟩ := exists_component_of_branch hW hϖ hss hy₂ hϖ₂ ht₂ htu₂ h₂
  refine ⟨_, hc₁, _, hc₂, fun heq ↦ ?_, specializes_iff_mem_closure.1 hη₁y,
    specializes_iff_mem_closure.1 hη₂y⟩
  have hη : η₁ = η₂ := by
    have a : η₁ ⤳ η₂ := specializes_iff_mem_closure.2 (heq ▸ subset_closure rfl)
    have b : η₂ ⤳ η₁ := specializes_iff_mem_closure.2 (heq.symm ▸ subset_closure rfl)
    exact (a.antisymm b).eq
  subst hη
  -- `t₁` is a non-unit germ at `η₁`, so `V₁(t₁) < 1`
  have hd₁ := (isCentre_iff_dominates c j (specializes_of_isWModel hW η₁) V₁).1 hη₁
  have hd₂ := (isCentre_iff_dominates c j (specializes_of_isWModel hW η₁) V₂).1 hη₂
  have ht₁η : t₁ ∈ germs c j η₁ := germs_anti c j hη₁y ht₁
  have hnu : ∀ w ∈ germs c j η₁, t₁ * w ≠ 1 := by
    intro w hw h1
    have h3 := congrArg V₂.valuation h1
    rw [map_mul, map_one] at h3
    have h4 : V₂.valuation w ≤ 1 := (V₂.valuation_le_one_iff _).2 (hd₂.1 hw)
    have := mul_lt_one_of_lt_of_le h₁₂ h4
    rw [h3] at this
    exact lt_irrefl _ this
  have := hd₁.2 t₁ ht₁η hnu
  rw [h₁] at this
  exact lt_irrefl _ this

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
