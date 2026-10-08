/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# Lifting along coverings over spaces with a generic point

Auxiliary results for the construction of universal coverings of curves
(`TemperedFundamentalGroups.Topology.UniversalCovering`).

* `TemperedFundamentalGroups.isEvenlyCovered_of_sections`: a criterion for a point to be evenly
  covered, in terms of a family of continuous local sections whose images are open and
  partition the preimage of a neighbourhood.
* `TemperedFundamentalGroups.exists_lift_of_generic`: if every nonempty open subset of `A`
  contains a fixed point `η` (for instance, `A` is an irreducible closed subset of a sober space
  and `η` its generic point), then every continuous map `A → Y` lifts along every covering map
  `P → Y`, through every point of the fibre.
* `TemperedFundamentalGroups.continuousAt_of_finite_cover`: continuity at a point from continuity
  within finitely many sets whose union is a neighbourhood.
-/

open Set Topology Filter

namespace TemperedFundamentalGroups

section Criterion

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- A point `x` is evenly covered by `f` if it has an open neighbourhood `U` with a family of
continuous sections of `f` over `U` whose images are open and such that every point over `U` lies
on exactly one of them. -/
theorem isEvenlyCovered_of_sections {f : E → X} (hf : Continuous f) {x : X} {U : Set X}
    (hU : IsOpen U) (hx : x ∈ U) {J : Type*} (σ : J → X → E) (hσ : ∀ j, ContinuousOn (σ j) U)
    (hfσ : ∀ j, ∀ u ∈ U, f (σ j u) = u) (hopen : ∀ j, IsOpen (σ j '' U))
    (huniq : ∀ e, f e ∈ U → ∃! j, σ j (f e) = e) : IsEvenlyCovered f x (f ⁻¹' {x}) := by
  letI : TopologicalSpace J := ⊥
  haveI : DiscreteTopology J := ⟨rfl⟩
  have hmem : ∀ (j : J) (u : U), σ j u ∈ f ⁻¹' U := fun j u ↦ by
    simp only [mem_preimage, hfσ j u u.2, u.2]
  have key : ∀ (e : E) (j : J), f e ∈ U → (σ j (f e) = e ↔ e ∈ σ j '' U) := by
    intro e j he
    refine ⟨fun h ↦ ⟨f e, he, h⟩, ?_⟩
    rintro ⟨u, hu, rfl⟩
    rw [hfσ j u hu]
  have H : IsEvenlyCovered f x J := by
    let Φ : f ⁻¹' U ≃ₜ U × J :=
    { toFun e := (⟨f e, e.2⟩, (huniq e e.2).choose)
      invFun uj := ⟨σ uj.2 uj.1, hmem uj.2 uj.1⟩
      left_inv e := Subtype.ext (huniq e e.2).choose_spec.1
      right_inv uj := by
        obtain ⟨u, j⟩ := uj
        have h1 : f (σ j u) = u := hfσ j u u.2
        refine Prod.ext (Subtype.ext h1) ?_
        refine ((huniq _ (hmem j u)).unique (huniq _ (hmem j u)).choose_spec.1 ?_)
        change σ j (f (σ j u)) = σ j u
        rw [h1]
      continuous_toFun := by
        refine Continuous.prodMk ((hf.comp continuous_subtype_val).subtype_mk _)
          (continuous_discrete_rng.2 fun j ↦ ?_)
        have : (fun e : f ⁻¹' U ↦ (huniq e e.2).choose) ⁻¹' {j} =
            Subtype.val ⁻¹' (σ j '' U) := by
          ext e
          simp only [mem_preimage, mem_singleton_iff]
          rw [← key e j e.2]
          exact ⟨fun h ↦ h ▸ (huniq e e.2).choose_spec.1,
            fun h ↦ ((huniq e e.2).unique (huniq e e.2).choose_spec.1 h)⟩
        rw [this]
        exact (hopen j).preimage continuous_subtype_val
      continuous_invFun := by
        refine continuous_prod_of_discrete_right.2 fun j ↦ ?_
        exact ((continuousOn_iff_continuous_restrict.1 (hσ j))).subtype_mk _ }
    exact ⟨inferInstance, U, hx, hU, hU.preimage hf, Φ, fun e ↦ rfl⟩
  exact H.to_isEvenlyCovered_preimage

end Criterion

section Generic

variable {A : Type*} [TopologicalSpace A]

/-- An open set containing a point that lies in every nonempty open set is preconnected. -/
theorem isPreconnected_of_generic {η : A} (hη : ∀ U : Set A, IsOpen U → U.Nonempty → η ∈ U)
    {W : Set A} (hW : IsOpen W) (hηW : η ∈ W) : IsPreconnected W := by
  intro u v hu hv _ hWu hWv
  exact ⟨η, hηW, hη _ (hW.inter hu) hWu |>.2, hη _ (hW.inter hv) hWv |>.2⟩

/-- A space in which a fixed point lies in every nonempty open set is preconnected. -/
theorem preconnectedSpace_of_generic {η : A}
    (hη : ∀ U : Set A, IsOpen U → U.Nonempty → η ∈ U) : PreconnectedSpace A :=
  ⟨isPreconnected_of_generic hη isOpen_univ (mem_univ η)⟩

variable {Y P : Type*} [TopologicalSpace Y] [TopologicalSpace P]

/-- Lifting over a space with a generic point: if every nonempty open subset of `A` contains `η`,
then every continuous map `h : A → Y` lifts along a covering map `q : P → Y` through every point
of the fibre. -/
theorem exists_lift_of_generic {q : P → Y} (hq : IsCoveringMap q) {η : A}
    (hη : ∀ U : Set A, IsOpen U → U.Nonempty → η ∈ U) {h : A → Y} (hh : Continuous h) (a : A)
    (y : P) (hy : q y = h a) : ∃ f : A → P, Continuous f ∧ q ∘ f = h ∧ f a = y := by
  classical
  choose _ U hU hUo _ H hH using fun a' ↦ hq (h a')
  have hηU : ∀ a', h η ∈ U a' := fun a' ↦
    hη _ ((hUo a').preimage hh) ⟨a', hU a'⟩
  -- the point over `h η` on the sheet of `y` over `U a`
  have hyU : y ∈ q ⁻¹' U a := by rw [mem_preimage, hy]; exact hU a
  let yη : P := ((H a).symm (⟨h η, hηU a⟩, (H a ⟨y, hyU⟩).2)).1
  have hqyη : q yη = h η := by
    have := hH a ((H a).symm (⟨h η, hηU a⟩, (H a ⟨y, hyU⟩).2))
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hyηU : ∀ a', yη ∈ q ⁻¹' U a' := fun a' ↦ by rw [mem_preimage, hqyη]; exact hηU a'
  -- the local lift over `h ⁻¹' U a'` through `yη`
  let L : A → A → P := fun a' b ↦
    if hb : h b ∈ U a' then ((H a').symm (⟨h b, hb⟩, (H a' ⟨yη, hyηU a'⟩).2)).1 else y
  have hLq : ∀ a' b, h b ∈ U a' → q (L a' b) = h b := by
    intro a' b hb
    simp only [L, dif_pos hb]
    have := hH a' ((H a').symm (⟨h b, hb⟩, (H a' ⟨yη, hyηU a'⟩).2))
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm
  have hLη : ∀ a', L a' η = yη := by
    intro a'
    simp only [L, dif_pos (hηU a')]
    have e1 : (⟨h η, hηU a'⟩ : U a') = (H a' ⟨yη, hyηU a'⟩).1 := Subtype.ext (by
      rw [hH]; exact hqyη.symm)
    rw [e1, Prod.mk.eta, Homeomorph.symm_apply_apply]
  have hLc : ∀ a', ContinuousOn (L a') (h ⁻¹' U a') := by
    intro a'
    rw [continuousOn_iff_continuous_restrict]
    have : (h ⁻¹' U a').restrict (L a') = fun b : h ⁻¹' U a' ↦
        ((H a').symm (⟨h b, b.2⟩, (H a' ⟨yη, hyηU a'⟩).2)).1 := by
      funext b; simp only [restrict_apply, L]; exact dif_pos b.2
    rw [this]
    fun_prop
  -- two local lifts agree on the overlap
  have hLL : ∀ a' a'' b, h b ∈ U a' → h b ∈ U a'' → L a' b = L a'' b := by
    intro a' a'' b hb' hb''
    have hW : IsOpen (h ⁻¹' U a' ∩ h ⁻¹' U a'') :=
      ((hUo a').preimage hh).inter ((hUo a'').preimage hh)
    refine hq.eqOn_of_comp_eqOn (isPreconnected_of_generic hη hW ⟨hηU a', hηU a''⟩)
      ((hLc a').mono inter_subset_left) ((hLc a'').mono inter_subset_right)
      (fun c hc ↦ ?_) (a := η) ⟨hηU a', hηU a''⟩ (by rw [hLη, hLη]) ⟨hb', hb''⟩
    simp only [Function.comp_apply, hLq a' c hc.1, hLq a'' c hc.2]
  refine ⟨fun b ↦ L b b, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun a' ↦ ?_
    have hnhds : h ⁻¹' U a' ∈ 𝓝 a' := ((hUo a').preimage hh).mem_nhds (hU a')
    refine (((hLc a').continuousAt hnhds)).congr ?_
    filter_upwards [hnhds] with b hb
    exact hLL a' b b hb (hU b)
  · funext b; exact hLq b b (hU b)
  · change L a a = y
    simp only [L, dif_pos (hU a)]
    have e1 : (H a ⟨yη, hyηU a⟩).2 = (H a ⟨y, hyU⟩).2 := by
      simp only [yη]
      have : (⟨((H a).symm (⟨h η, hηU a⟩, (H a ⟨y, hyU⟩).2)).1, hyηU a⟩ : q ⁻¹' U a) =
          (H a).symm (⟨h η, hηU a⟩, (H a ⟨y, hyU⟩).2) := rfl
      rw [this, Homeomorph.apply_symm_apply]
    have e2 : (⟨h a, hU a⟩ : U a) = (H a ⟨y, hyU⟩).1 := Subtype.ext (by rw [hH]; exact hy.symm)
    rw [e1, e2, Prod.mk.eta, Homeomorph.symm_apply_apply]

end Generic

/-- Continuity at a point from continuity within finitely many sets whose union is a
neighbourhood of the point. -/
theorem continuousAt_of_finite_cover {α β ι : Type*} [TopologicalSpace α] [TopologicalSpace β]
    [Finite ι] {f : α → β} {x : α} (A : ι → Set α) (hA : ⋃ i, A i ∈ 𝓝 x)
    (h : ∀ i, ContinuousWithinAt f (A i) x) : ContinuousAt f x := by
  rw [← continuousWithinAt_iff_continuousAt hA, ContinuousWithinAt, nhdsWithin_iUnion]
  exact tendsto_iSup.2 h

end TemperedFundamentalGroups
