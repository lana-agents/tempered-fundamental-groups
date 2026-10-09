/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.XHarmonic

/-!
# Germs along maps of models (Blueprint §9.7, XL7)

For `ψ : c ⟶ c'` compatible with the generic points (`j ≫ ψ = Spec(L₂ → L₁) ≫ j'`), the germs of
`c'` at `ψ y` map into the germs of `c` at `y` (`germs_map`): a section of `c'` near `ψ y` pulls
back along `ψ` to a section of `c` near `y` with the same image in `L₁`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

variable {L₁ L₂ : Type u} [Field L₁] [Field L₂] [Algebra L₂ L₁]
  {O₁ O₂ : Type u} [CommRing O₁] [CommRing O₂] {c : TemperedFundamentalGroups.ModelCode O₁}
  {c' : TemperedFundamentalGroups.ModelCode O₂}

/-- **Germs along a map of models** (XL7): if `j ≫ ψ = Spec(L₂ → L₁) ≫ j'`, then the image in `L₁`
of a germ of `c'` at `ψ y` is a germ of `c` at `y`. -/
theorem germs_map (ψ : c.scheme ⟶ c'.scheme) (j : Spec (CommRingCat.of L₁) ⟶ c.scheme)
    (j' : Spec (CommRingCat.of L₂) ⟶ c'.scheme)
    (hj : j ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j') (y : c.scheme) {f : L₂}
    (hf : f ∈ germs c' j' (ψ y)) : algebraMap L₂ L₁ f ∈ germs c j y := by
  obtain ⟨U', hy, h', s', rfl⟩ := hf
  have h : ⊤ ≤ j ⁻¹ᵁ (ψ ⁻¹ᵁ U') := by
    intro p _
    change ψ (j p) ∈ U'
    rw [← Scheme.Hom.comp_apply, hj, Scheme.Hom.comp_apply]
    exact h' trivial
  refine ⟨ψ ⁻¹ᵁ U', hy, h, ψ.app U' s', ?_⟩
  have e1 : (j.appLE (ψ ⁻¹ᵁ U') ⊤ h).hom (ψ.app U' s') =
      ((j ≫ ψ).appLE U' ⊤ (by simpa using h)).hom s' := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [e1]
  have e2 : (j ≫ ψ).appLE U' ⊤ (by simpa using h) =
      (Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁)) ≫ j').appLE U' ⊤ (by
        rw [← hj]; simpa using h) := by
    congr 1
  rw [e2, ← Scheme.Hom.appLE_comp_appLE (U := U') (V := ⊤) (W := ⊤) (e₁ := h')
    (e₂ := le_rfl)]
  have e3 : (Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁))).appLE ⊤ ⊤ le_rfl =
      (Spec.map (CommRingCat.ofHom (algebraMap L₂ L₁))).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [e3]
  have e4 := congrArg (fun g ↦ g.hom ((j'.appLE U' ⊤ h').hom s'))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap L₂ L₁)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e4 ⊢
  exact e4

/-- **Generic points of components map to generic points**: if `ψ '' closure {η} = closure {η'}`
then `ψ η = η'`. -/
theorem map_genericPoint (ψ : c.scheme ⟶ c'.scheme) {η : c.scheme} {η' : c'.scheme}
    (h : ψ '' closure {η} = closure {η'}) : ψ η = η' := by
  have hmem : ψ η ∈ closure ({η'} : Set c'.scheme) := by
    rw [← h]; exact ⟨η, subset_closure rfl, rfl⟩
  have h1 : closure ({ψ η} : Set c'.scheme) = closure {η'} := by
    apply le_antisymm
    · exact closure_minimal (Set.singleton_subset_iff.mpr hmem) isClosed_closure
    · rw [← h]
      refine (image_closure_subset_closure_image ψ.continuous).trans ?_
      rw [Set.image_singleton]
  exact IsGenericPoint.eq (x := ψ η) (S := closure {η'}) h1 isGenericPoint_closure

end TemperedFundamentalGroups.SemistableReduction.ModelCode
