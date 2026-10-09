/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CrossingNode

/-!
# Centres inside a component and zeros of functions (Blueprint §10.3.8, CrossingX1, CX2/CX6)

For a W-model `c` (proper over `O`):

* `centre_specializes`: if `R ≤ W` have centres `z` and `η`, then `η ⤳ z`;
* `exists_centre`: a valuation subring containing the base has a centre;
* `exists_le_centre`: inside the centre valuation of a component there is a valuation centred at
  any given point of the component;
* `exists_zero`: a function `g` with a pole at a point of a component (and `W(g) = 1` at its
  generic point) has a zero at some point of the component.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CrossingSource

open CentreGerms ValuativeCentre ModelCode

/-- **Centres of smaller valuation rings are specializations.** -/
theorem centre_specializes {R : Type u} [CommRing R] {L : Type u} [Field L]
    {c : TemperedFundamentalGroups.ModelCode R} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
    {V W : ValuationSubring L} (hVW : V ≤ W) {z η : c.scheme} (hz : IsCentre j V z)
    (hη : IsCentre j W η) : η ⤳ z := by
  have h := IsCentre.specializes hz
  obtain ⟨hV, -⟩ := (isCentre_iff j h V).1 hz
  have hW : ∀ s, (stalkTo j h).hom s ∈ W := fun s ↦ hVW (hV s)
  have := centre_unique c.toSpec hη (isCentre_fromSpecStalk j h W hW)
  rw [this]
  have hmem := Set.mem_range_self (f := c.scheme.fromSpecStalk z)
    ((Spec.map (CommRingCat.ofHom ((stalkTo j h).hom.codRestrict W.toSubring hW)))
      (closedPoint W))
  rw [Scheme.range_fromSpecStalk] at hmem
  exact hmem

variable {K L : Type u} [Field K] [Field L] [Algebra K L] {O : ValuationSubring K}
  [IsDiscreteValuationRing O] [Algebra O L] [IsScalarTower O K L] {x : L}
  {c : TemperedFundamentalGroups.ModelCode O} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
  (hW : IsWModel O L x c j)

include hW

omit [IsDiscreteValuationRing O] in
/-- **Valuations containing the base have a centre** (properness). -/
theorem exists_centre {V : ValuationSubring L} (hV : ∀ o : O, algebraMap O L o ∈ V) :
    ∃ z, IsCentre j V z := by
  let a : CommRingCat.of O ⟶ CommRingCat.of V :=
    CommRingCat.ofHom ((algebraMap O L).codRestrict V.toSubring hV)
  have hg : j ≫ c.toSpec = genMap V ≫ Spec.map a := by
    rw [toSpec_comp, genMap, ← Spec.map_comp]
    congr 1
    ext o
    exact baseHom_eq_of_isWModel hW o
  obtain ⟨l, hl, -⟩ := exists_lift c.toSpec j V a hg
  exact ⟨_, l, hl, rfl⟩

omit [IsDiscreteValuationRing O] in
/-- **Valuations centred at points of a component, inside its centre valuation.** -/
theorem exists_le_centre {η z : c.scheme} (hηz : η ⤳ z) {W : ValuationSubring L}
    (hWη : IsCentre j W η) :
    ∃ R : ValuationSubring L, R ≤ W ∧ IsCentre j R z := by
  have h := specializes_of_isWModel hW z
  obtain ⟨R, hRW, hR, hloc⟩ := CompositeValuation.exists_le_dominates W (stalkTo j h).hom
    (fun s ↦ germs_le hW hWη hηz _ (by rw [germs_eq_range c j h]; exact ⟨s, rfl⟩))
  exact ⟨R, hRW, (isCentre_iff j h R).2 ⟨hR, hloc⟩⟩

/-- **A function with a pole on a component has a zero on it.** -/
theorem exists_zero {ϖ : O} (hϖ : Irreducible ϖ) {v : Set c.scheme} (hv : v ∈ components c)
    {W : ValuationSubring L} (hWc : IsCentre j W (gp hv)) {g : L} (hg : W.valuation g = 1)
    {z : c.scheme} (hzv : z ∈ v)
    (hpole : ∀ R : ValuationSubring L, IsCentre j R z → R.valuation g⁻¹ < 1) :
    ∃ z' ∈ v, ∃ R : ValuationSubring L, IsCentre j R z' ∧ R.valuation g < 1 := by
  obtain ⟨R, hRW, hRz⟩ := exists_le_centre hW (gp_specializes hv hzv) hWc
  have hg0 : g ≠ 0 := fun h ↦ by simp [h] at hg
  have hgW : g ∈ W := (W.valuation_le_one_iff _).1 hg.le
  have hgiW : g⁻¹ ∈ W := (W.valuation_le_one_iff _).1 (by rw [map_inv₀, hg, inv_one])
  have hφm : ∀ o ∈ maximalIdeal O, W.valuation (algebraMap O L o) < 1 := fun o ho ↦ by
    obtain ⟨o', rfl⟩ := Ideal.mem_span_singleton'.1 (hϖ.maximalIdeal_eq ▸ ho)
    rw [map_mul, map_mul, mul_comm]
    exact (mul_le_of_le_one_right' ((W.valuation_le_one_iff _).2
      (germs_le hW hWc (gp_specializes hv hzv) _ (algebraMap_mem_germs hW z o')))).trans_lt
      (valuation_ϖ_lt_one hW hϖ (hv.2.1 (gp_mem hv)) hWc)
  have hRO : ∀ o : O, algebraMap O L o ∈ R := fun o ↦
    ((isCentre_iff_dominates c j (specializes_of_isWModel hW z) R).1 hRz).1
      (algebraMap_mem_germs hW z o)
  obtain ⟨R', hR'W, hR'O, hR'g⟩ := CompositeValuation.exists_le_lt_one W (algebraMap O L) hφm
    hgW hgiW hRW hRO (hpole R hRz)
  obtain ⟨z', hz'⟩ := exists_centre hW hR'O
  refine ⟨z', ?_, R', hz', hR'g⟩
  rw [← closure_gp hv, ← specializes_iff_mem_closure]
  exact centre_specializes hR'W hz' hWc

/-- A valuation subring centred at the generic point of a component. -/
noncomputable def Wc {v : Set c.scheme} (hv : v ∈ components c) : ValuationSubring L :=
  (exists_isCentre j (specializes_of_isWModel hW (gp hv))).choose

omit [IsDiscreteValuationRing O] in
lemma Wc_spec {v : Set c.scheme} (hv : v ∈ components c) : IsCentre j (Wc hW hv) (gp hv) :=
  (exists_isCentre j (specializes_of_isWModel hW (gp hv))).choose_spec

/-- **At most two components through a node.** -/
theorem two_components {ϖ : O} (hϖ : Irreducible ϖ) (hsplit : HasSplitNodes ϖ c)
    (hloops : NoLoops c) {z : c.scheme} (hz : IsNodePt c z) {w₁ w₂ w₃ : Set c.scheme}
    (h₁ : w₁ ∈ components c) (h₂ : w₂ ∈ components c) (h₃ : w₃ ∈ components c) (hz₁ : z ∈ w₁)
    (hz₂ : z ∈ w₂) (hz₃ : z ∈ w₃) : w₁ = w₂ ∨ w₁ = w₃ ∨ w₂ = w₃ := by
  obtain ⟨P, a, b, m, hPg, hcore, hloc, hnoeth, -⟩ := node_data hW hϖ hsplit hloops hz
  have hb := fun {w} (hw : w ∈ components c) (hzw : z ∈ w) ↦
    branch hW hϖ hloops hz hPg hcore hw hzw (Wc_spec hW hw)
  have hne := fun {w w'} (hw : w ∈ components c) (hw' : w' ∈ components c) (hzw : z ∈ w)
    (hzw' : z ∈ w') ↦ branch_ne hW hϖ hPg hcore hw hw' hzw hzw' (Wc_spec hW hw) (Wc_spec hW hw')
  have hne' := fun {w w'} (hw : w ∈ components c) (hw' : w' ∈ components c) (hzw : z ∈ w)
    (hzw' : z ∈ w') ↦
      branch_ne hW hϖ hPg hcore.swap hw hw' hzw hzw' (Wc_spec hW hw) (Wc_spec hW hw')
  rcases hb h₁ hz₁ with ⟨a₁, b₁⟩ | ⟨b₁, a₁⟩ <;> rcases hb h₂ hz₂ with ⟨a₂, b₂⟩ | ⟨b₂, a₂⟩ <;>
    rcases hb h₃ hz₃ with ⟨a₃, b₃⟩ | ⟨b₃, a₃⟩
  · exact .inl (hne h₁ h₂ hz₁ hz₂ a₁ b₁ a₂ b₂)
  · exact .inl (hne h₁ h₂ hz₁ hz₂ a₁ b₁ a₂ b₂)
  · exact .inr (.inl (hne h₁ h₃ hz₁ hz₃ a₁ b₁ a₃ b₃))
  · exact .inr (.inr (hne' h₂ h₃ hz₂ hz₃ b₂ a₂ b₃ a₃))
  · exact .inr (.inr (hne h₂ h₃ hz₂ hz₃ a₂ b₂ a₃ b₃))
  · exact .inr (.inl (hne' h₁ h₃ hz₁ hz₃ b₁ a₁ b₃ a₃))
  · exact .inl (hne' h₁ h₂ hz₁ hz₂ b₁ a₁ b₂ a₂)
  · exact .inl (hne' h₁ h₂ hz₁ hz₂ b₁ a₁ b₂ a₂)

end TemperedFundamentalGroups.SemistableReduction.CrossingSource
