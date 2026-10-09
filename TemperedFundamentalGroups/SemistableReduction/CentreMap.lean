/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CentreGerms

/-!
# Centres along morphisms (Blueprint §10.3.8, CrossingX1, CX1)

For `ψ : X ⟶ Y` and points `g : Spec F ⟶ X`, `g' : Spec F' ⟶ Y` with `g ≫ ψ = Spec(F' → F) ≫ g'`:

* `stalkTo_comp`: the stalk maps are compatible with `ψ`;
* `IsCentre.comap`: if `V` has centre `x`, then `V ∩ F'` has centre `ψ x`;
* `germs_anti`: germs grow under generalization.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CentreGerms

open ValuativeCentre

variable {X Y : Scheme.{u}} {F F' : Type u} [Field F] [Field F'] [Algebra F' F]

lemma closedPoint_map (g : Spec (CommRingCat.of F) ⟶ X) (g' : Spec (CommRingCat.of F') ⟶ Y)
    (ψ : X ⟶ Y) (hj : g ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap F' F)) ≫ g') :
    ψ (g (closedPoint F)) = g' (closedPoint F') := by
  rw [← Scheme.Hom.comp_apply, hj, Scheme.Hom.comp_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- Images of pulled back sections (the computation of `ModelCode.germs_map`). -/
lemma map_appLE (g : Spec (CommRingCat.of F) ⟶ X) (g' : Spec (CommRingCat.of F') ⟶ Y)
    (ψ : X ⟶ Y) (hj : g ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap F' F)) ≫ g')
    {V : Y.Opens} (e' : ⊤ ≤ g' ⁻¹ᵁ V) (e : ⊤ ≤ g ⁻¹ᵁ (ψ ⁻¹ᵁ V)) (t : Γ(Y, V)) :
    algebraMap F' F ((Scheme.ΓSpecIso (CommRingCat.of F')).hom.hom ((g'.appLE V ⊤ e').hom t)) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((g.appLE (ψ ⁻¹ᵁ V) ⊤ e).hom (ψ.app V t)) := by
  have e1 : (g.appLE (ψ ⁻¹ᵁ V) ⊤ e).hom (ψ.app V t) =
      ((g ≫ ψ).appLE V ⊤ (by simpa using e)).hom t := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  rw [e1]
  have e2 : (g ≫ ψ).appLE V ⊤ (by simpa using e) =
      (Spec.map (CommRingCat.ofHom (algebraMap F' F)) ≫ g').appLE V ⊤ (by
        rw [← hj]; simpa using e) := by
    congr 1
  rw [e2, ← Scheme.Hom.appLE_comp_appLE (U := V) (V := ⊤) (W := ⊤) (e₁ := e')
    (e₂ := le_rfl)]
  have e3 : (Spec.map (CommRingCat.ofHom (algebraMap F' F))).appLE ⊤ ⊤ le_rfl =
      (Spec.map (CommRingCat.ofHom (algebraMap F' F))).appTop :=
    Scheme.Hom.appLE_eq_app _
  rw [e3]
  have e4 := congrArg (fun φ ↦ φ.hom ((g'.appLE V ⊤ e').hom t))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap F' F)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e4 ⊢
  exact e4.symm

lemma specializes_map (g : Spec (CommRingCat.of F) ⟶ X) (g' : Spec (CommRingCat.of F') ⟶ Y)
    (ψ : X ⟶ Y) (hj : g ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap F' F)) ≫ g') {x : X}
    (h : g (closedPoint F) ⤳ x) : g' (closedPoint F') ⤳ ψ x := by
  rw [← closedPoint_map g g' ψ hj]
  exact h.map ψ.continuous

/-- **Stalk maps along `ψ`.** -/
theorem stalkTo_comp (g : Spec (CommRingCat.of F) ⟶ X) (g' : Spec (CommRingCat.of F') ⟶ Y)
    (ψ : X ⟶ Y) (hj : g ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap F' F)) ≫ g') {x : X}
    (h : g (closedPoint F) ⤳ x) (s : Y.presheaf.stalk (ψ x)) :
    algebraMap F' F ((stalkTo g' (specializes_map g g' ψ hj h)).hom s) =
      (stalkTo g h).hom (ψ.stalkMap x s) := by
  obtain ⟨V, hV, t, rfl⟩ := Y.presheaf.exists_germ_eq s
  rw [stalkTo_germ, Scheme.Hom.germ_stalkMap_apply, stalkTo_germ]
  exact map_appLE g g' ψ hj _ _ t

/-- The valuation of `V` is `< 1` at `x` iff `x = 0` or `x⁻¹ ∉ V`. -/
lemma valuation_lt_one_iff_inv {K : Type*} [Field K] (V : ValuationSubring K) (x : K) :
    V.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ V := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [← ValuationSubring.valuation_le_one_iff, map_inv₀, not_le]
  have h0 : V.valuation x ≠ 0 := by simpa using hx
  simp only [hx, false_or]
  exact (one_lt_inv₀ (zero_lt_iff.2 h0)).symm

lemma valuation_comap_lt_one_iff (V : ValuationSubring F) (x : F') :
    (V.comap (algebraMap F' F)).valuation x < 1 ↔ V.valuation (algebraMap F' F x) < 1 := by
  rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

lemma valuation_comap_lt_one_iff' {K L : Type*} [Field K] [Field L] (V : ValuationSubring L)
    (f : K →+* L) (x : K) : (V.comap f).valuation x < 1 ↔ V.valuation (f x) < 1 := by
  rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap, map_inv₀,
    map_eq_zero]

lemma valuation_eq_one_iff' {K : Type*} [Field K] (V : ValuationSubring K) (x : K) :
    V.valuation x = 1 ↔ x ∈ V ∧ ¬ V.valuation x < 1 := by
  rw [← V.valuation_le_one_iff]
  exact ⟨fun h ↦ ⟨h.le, by rw [h]; exact lt_irrefl _⟩, fun ⟨h₁, h₂⟩ ↦
    le_antisymm h₁ (not_lt.1 h₂)⟩

lemma valuation_comap_eq_one_iff {K L : Type*} [Field K] [Field L] (V : ValuationSubring L)
    (f : K →+* L) (x : K) : (V.comap f).valuation x = 1 ↔ V.valuation (f x) = 1 := by
  rw [valuation_eq_one_iff', valuation_eq_one_iff', valuation_comap_lt_one_iff',
    ValuationSubring.mem_comap]

/-- **Centres map along morphisms.** -/
theorem IsCentre.comap (g : Spec (CommRingCat.of F) ⟶ X) (g' : Spec (CommRingCat.of F') ⟶ Y)
    (ψ : X ⟶ Y) (hj : g ≫ ψ = Spec.map (CommRingCat.ofHom (algebraMap F' F)) ≫ g')
    {V : ValuationSubring F} {x : X} (hc : IsCentre g V x) :
    IsCentre g' (V.comap (algebraMap F' F)) (ψ x) := by
  have h : g (closedPoint F) ⤳ x := by
    obtain ⟨l, hl, rfl⟩ := hc
    rw [← hl, Scheme.Hom.comp_apply]
    refine Specializes.map ?_ l.continuous
    exact (IsLocalRing.specializes_closedPoint _)
  obtain ⟨hV, hloc⟩ := (isCentre_iff g h V).1 hc
  refine (isCentre_iff g' (specializes_map g g' ψ hj h) _).2 ⟨fun s ↦ ?_, fun s hs ↦ ?_⟩
  · change algebraMap F' F _ ∈ V
    rw [stalkTo_comp g g' ψ hj h]
    exact hV _
  · rw [valuation_comap_lt_one_iff, stalkTo_comp g g' ψ hj h]
    exact hloc _ (map_nonunit (ψ.stalkMap x).hom s hs)

variable {O : Type u} [CommRing O]

/-- **Germs grow under generalization.** -/
lemma germs_anti (c : TemperedFundamentalGroups.ModelCode O)
    (g : Spec (CommRingCat.of F) ⟶ c.scheme)
    {x y : c.scheme} (h : x ⤳ y) : ModelCode.germs c g y ⊆ ModelCode.germs c g x := by
  rintro f ⟨U, hy, hU, s, rfl⟩
  exact ⟨U, h.mem_open U.isOpen hy, hU, s, rfl⟩

end TemperedFundamentalGroups.SemistableReduction.CentreGerms
