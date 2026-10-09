/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.TateCovering

/-!
# The `ℤ`-covering of a 2-gon with an action preserving the pieces (B3d)

`TateCovering.Decomp.toCode` codes the `ℤ`-covering `D.Space` of `C ∪ E` for a trivial action of
`G` on `Z`. Here `G` may act on `Z` by homeomorphisms preserving `C`, `E`, `Cp` and `Cq`
(`Decomp.Preserves`). It lifts to `D.Space` by `(z, n) ↦ (g z, n)` (`liftAct`), commuting with
the deck translations, and gives a covering code `toCodeEq` with the same carrier and topology as
`toCode`. The deck group still acts simply transitively on the fibres (`existsUnique_deckCodeEq`).
-/

universe u

open Set Topology

namespace TemperedFundamentalGroups.TateCovering

namespace Decomp

variable {Z : Type u} [TopologicalSpace Z] (D : Decomp Z)

/-- A homeomorphism of `Z` preserves the decomposition. -/
def Preserves (h : Z ≃ₜ Z) : Prop :=
  ∀ z, (h z ∈ D.C ↔ z ∈ D.C) ∧ (h z ∈ D.Cp ↔ z ∈ D.Cp) ∧ (h z ∈ D.Cq ↔ z ∈ D.Cq)

variable {D}

lemma Preserves.shift {h : Z ≃ₜ Z} (hh : D.Preserves h) (z : Z) : D.shift (h z) = D.shift z := by
  by_cases hz : z ∈ D.C
  · rw [D.shift_of_mem hz, D.shift_of_mem ((hh z).1.2 hz)]
  · rw [D.shift_of_notMem hz, D.shift_of_notMem fun h' ↦ hz ((hh z).1.1 h')]

lemma Preserves.symm {h : Z ≃ₜ Z} (hh : D.Preserves h) : D.Preserves h.symm := fun z ↦ by
  have := hh (h.symm z)
  rw [Homeomorph.apply_symm_apply] at this
  exact ⟨this.1.symm, this.2.1.symm, this.2.2.symm⟩

lemma continuous_lift {h : Z ≃ₜ Z} (hh : D.Preserves h) :
    Continuous (fun x : D.Space ↦ (⟨h x.pt, x.n⟩ : D.Space)) := by
  refine continuous_iff.2 ⟨h.continuous.comp D.continuous_pt, fun k ↦ ?_, fun k ↦ ?_⟩
  · convert D.isOpen_sheet₁ k using 1
    ext x
    change (h x.pt ∉ D.Cq ∧ x.n = k) ↔ (x.pt ∉ D.Cq ∧ x.n = k)
    rw [(hh x.pt).2.2]
  · convert D.isOpen_sheet₂ k using 1
    ext x
    change (h x.pt ∉ D.Cp ∧ x.n - D.shift (h x.pt) = k) ↔ (x.pt ∉ D.Cp ∧ x.n - D.shift x.pt = k)
    rw [(hh x.pt).2.1, hh.shift]

/-- The lift `(z, n) ↦ (h z, n)` of a homeomorphism preserving the decomposition. -/
def lift {h : Z ≃ₜ Z} (hh : D.Preserves h) : D.Space ≃ₜ D.Space where
  toFun x := ⟨h x.pt, x.n⟩
  invFun x := ⟨h.symm x.pt, x.n⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  continuous_toFun := continuous_lift hh
  continuous_invFun := continuous_lift hh.symm

@[simp] lemma lift_pt {h : Z ≃ₜ Z} (hh : D.Preserves h) (x : D.Space) :
    (lift hh x).pt = h x.pt := rfl

@[simp] lemma lift_n {h : Z ≃ₜ Z} (hh : D.Preserves h) (x : D.Space) : (lift hh x).n = x.n := rfl

lemma lift_deck {h : Z ≃ₜ Z} (hh : D.Preserves h) (d : Multiplicative ℤ) (x : D.Space) :
    lift hh (D.deck d x) = D.deck d (lift hh x) := rfl

variable (D) {G : Type u} [Group G]

/-- The lifted action of `G` on `D.Space`. -/
def liftAct (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g)) : G →* (D.Space ≃ₜ D.Space) where
  toFun g := lift (hρ g)
  map_one' := by
    ext x
    · simp
    · rfl
  map_mul' g g' := by
    ext x
    · simp
    · rfl

/-- **The `ℤ`-covering as a covering code, for an action preserving the decomposition.** -/
def toCodeEq (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g)) : CoveringCode ρ where
  carrier := univ
  top := D.codeTop
  isCoveringMap := by
    letI := D.codeTop
    exact D.isCoveringMap.comp_homeomorph D.codeHomeomorph
  act := letI := D.codeTop
    { toFun := fun g ↦ (D.codeHomeomorph.trans (D.liftAct ρ hρ g)).trans D.codeHomeomorph.symm
      map_one' := by
        ext x : 1
        simp only [map_one, Homeomorph.trans_apply]
        exact D.codeHomeomorph.symm_apply_apply x
      map_mul' := fun g g' ↦ by
        ext x : 1
        change D.codeHomeomorph.symm (D.liftAct ρ hρ (g * g') (D.codeHomeomorph x)) =
          D.codeHomeomorph.symm (D.liftAct ρ hρ g (D.codeHomeomorph
            (D.codeHomeomorph.symm (D.liftAct ρ hρ g' (D.codeHomeomorph x)))))
        rw [Homeomorph.apply_symm_apply, map_mul, Homeomorph.mul_apply] }
  act_fst g x := rfl

/-- The deck action on the coded covering. -/
def deckCodeEq (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g)) :
    Multiplicative ℤ →* ((D.toCodeEq ρ hρ).carrier ≃ₜ (D.toCodeEq ρ hρ).carrier) where
  toFun d := letI := D.codeTop
    (D.codeHomeomorph.trans (D.deck d)).trans D.codeHomeomorph.symm
  map_one' := by
    letI := D.codeTop
    ext x : 1
    simp only [map_one, Homeomorph.trans_apply]
    exact D.codeHomeomorph.symm_apply_apply x
  map_mul' d e := by
    letI := D.codeTop
    ext x : 1
    change D.codeHomeomorph.symm (D.deck (d * e) (D.codeHomeomorph x)) =
      D.codeHomeomorph.symm (D.deck d (D.codeHomeomorph
        (D.codeHomeomorph.symm (D.deck e (D.codeHomeomorph x)))))
    rw [Homeomorph.apply_symm_apply, map_mul, Homeomorph.mul_apply]

lemma deckCodeEq_fst (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g)) (d : Multiplicative ℤ)
    (x : (D.toCodeEq ρ hρ).carrier) : (D.deckCodeEq ρ hρ d x).1.1 = x.1.1 :=
  rfl

/-- The deck transformations commute with the action. -/
lemma deckCodeEq_act (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g)) (d : Multiplicative ℤ)
    (g : G) (x : (D.toCodeEq ρ hρ).carrier) :
    D.deckCodeEq ρ hρ d ((D.toCodeEq ρ hρ).act g x) =
      (D.toCodeEq ρ hρ).act g (D.deckCodeEq ρ hρ d x) := by
  letI := D.codeTop
  change D.codeHomeomorph.symm (D.deck d (D.codeHomeomorph (D.codeHomeomorph.symm
      (D.liftAct ρ hρ g (D.codeHomeomorph x))))) =
    D.codeHomeomorph.symm (D.liftAct ρ hρ g (D.codeHomeomorph (D.codeHomeomorph.symm
      (D.deck d (D.codeHomeomorph x)))))
  rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]
  rfl

/-- The deck group acts simply transitively on the fibres of the coded covering. -/
lemma existsUnique_deckCodeEq (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g))
    {x y : (D.toCodeEq ρ hρ).carrier} (h : x.1.1 = y.1.1) :
    ∃! d : Multiplicative ℤ, D.deckCodeEq ρ hρ d x = y := by
  letI := D.codeTop
  obtain ⟨d, hd, hu⟩ := D.existsUnique_deck (x := D.codeHomeomorph x) (y := D.codeHomeomorph y) h
  refine ⟨d, ?_, fun e he => hu e ?_⟩
  · change D.codeHomeomorph.symm (D.deck d (D.codeHomeomorph x)) = y
    rw [hd]
    exact D.codeHomeomorph.symm_apply_apply y
  · rw [← he]
    change _ = D.codeHomeomorph (D.codeHomeomorph.symm _)
    rw [Homeomorph.apply_symm_apply]
    rfl

/-- The coded covering is connected under the hypotheses of `connectedSpace`. -/
lemma connectedSpace_toCodeEq (ρ : G →* (Z ≃ₜ Z)) (hρ : ∀ g, D.Preserves (ρ g))
    (hC : IsPreconnected D.C) (hE : IsPreconnected D.E) (hp : D.Cp.Nonempty)
    (hq : D.Cq.Nonempty) : ConnectedSpace (D.toCodeEq ρ hρ).carrier := by
  letI := D.codeTop
  have := D.connectedSpace hC hE hp hq
  exact D.codeHomeomorph.symm.surjective.connectedSpace D.codeHomeomorph.symm.continuous

end Decomp

end TemperedFundamentalGroups.TateCovering
