/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.ValuativeCentre

/-!
# Composite valuations and specialization of centres (Blueprint §10.3.8, I4)

Let `V` be a valuation subring of a field `F` and `U` a valuation subring of the residue field
`κ(V)`. The **composite** `ValuationSubring.comp V U = {y ∈ V | ȳ ∈ U}` is a valuation subring
of `F` contained in `V` (`ValuationSubring.comp_le`).

* `ValuationSubring.exists_le_isLocalHom`: every ring map `φ : S → V` from a local ring factors
  through a local map `S → W` to a valuation subring `W ≤ V` (`W` the composite of `V` with a
  valuation subring of `κ(V)` dominating the image of `S`);
* `ValuativeCentre.IsCentre.exists_le_of_specializes`: if `η` is the centre of `V` with respect to
  `g : Spec F ⟶ X` and `η ⤳ x`, then `x` is the centre of some valuation subring `W ≤ V`
  (apply the above to `𝒪_{X,x} → 𝒪_{X,η} → V`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups

noncomputable section

namespace ValuationSubring

variable {F : Type u} [Field F]

lemma inv_mem_of_isUnit {V : ValuationSubring F} {y : V} (hy : IsUnit y) : (y : F)⁻¹ ∈ V := by
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hy
  have hw' : (y : F) * w = 1 := congrArg Subtype.val hw
  rw [inv_eq_of_mul_eq_one_right hw']
  exact w.2

/-- The **composite** of a valuation subring `V ⊆ F` with a valuation subring `U` of its residue
field: the elements of `V` whose residue lies in `U`. -/
def comp (V : ValuationSubring F) (U : ValuationSubring (ResidueField V)) :
    ValuationSubring F where
  toSubring := (U.toSubring.comap (residue V)).map V.subtype
  mem_or_inv_mem' y := by
    by_cases hy : y ∈ V
    · by_cases hu : IsUnit (⟨y, hy⟩ : V)
      · rcases U.mem_or_inv_mem (residue V ⟨y, hy⟩) with h | h
        · exact Or.inl ⟨⟨y, hy⟩, h, rfl⟩
        · have hi := inv_mem_of_isUnit hu
          refine Or.inr ⟨⟨y⁻¹, hi⟩, ?_, rfl⟩
          have hy0 : y ≠ 0 := by
            rintro rfl
            exact hu.ne_zero rfl
          have hm : (⟨y, hy⟩ : V) * ⟨y⁻¹, hi⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hy0)
          have hr : residue V ⟨y, hy⟩ * residue V ⟨y⁻¹, hi⟩ = 1 := by
            rw [← map_mul, hm, map_one]
          change residue V _ ∈ U
          rw [← inv_eq_of_mul_eq_one_right hr]
          exact h
      · refine Or.inl ⟨⟨y, hy⟩, ?_, rfl⟩
        change residue V _ ∈ U
        rw [(residue_eq_zero_iff _).2 hu]
        exact U.zero_mem
    · have hi : y⁻¹ ∈ V := (V.mem_or_inv_mem y).resolve_left hy
      refine Or.inr ⟨⟨y⁻¹, hi⟩, ?_, rfl⟩
      have hu : ¬ IsUnit (⟨y⁻¹, hi⟩ : V) := fun hu ↦ hy (by
        have := inv_mem_of_isUnit hu
        rwa [inv_inv] at this)
      change residue V _ ∈ U
      rw [(residue_eq_zero_iff _).2 hu]
      exact U.zero_mem

lemma mem_comp_iff {V : ValuationSubring F} {U : ValuationSubring (ResidueField V)} {y : F} :
    y ∈ comp V U ↔ ∃ h : y ∈ V, residue V ⟨y, h⟩ ∈ U := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, hz⟩
  · rintro ⟨h, hU⟩
    exact ⟨⟨y, h⟩, hU, rfl⟩

lemma comp_le (V : ValuationSubring F) (U : ValuationSubring (ResidueField V)) : comp V U ≤ V :=
  fun _ hy ↦ (mem_comp_iff.1 hy).1

/-- **Composite valuations dominating a local ring**: a ring map `φ : S → V` from a local ring
to a valuation subring factors through a *local* map `S → W` to a valuation subring `W ≤ V`. -/
theorem exists_le_isLocalHom (V : ValuationSubring F) {S : Type u} [CommRing S] [IsLocalRing S]
    (φ : S →+* V) : ∃ (W : ValuationSubring F) (_ : W ≤ V) (φ' : S →+* W),
      IsLocalHom φ' ∧ ∀ s, (φ' s : F) = φ s := by
  obtain ⟨U, hU, hloc⟩ := exists_factor_valuationRing ((residue V).comp φ)
  have hmem : ∀ s, (φ s : F) ∈ comp V U := fun s ↦ mem_comp_iff.2 ⟨(φ s).2, hU s⟩
  refine ⟨comp V U, comp_le V U, (V.subtype.comp φ).codRestrict (comp V U).toSubring hmem,
    ⟨fun s hs ↦ ?_⟩, fun _ ↦ rfl⟩
  obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.1 hs
  have hw' : (φ s : F) * w = 1 := congrArg Subtype.val hw
  obtain ⟨hwV, hwU⟩ := mem_comp_iff.1 w.2
  have hsw : φ s * ⟨w, hwV⟩ = 1 := Subtype.ext hw'
  refine hloc.map_nonunit s (isUnit_iff_exists_inv.2 ⟨⟨_, hwU⟩, Subtype.ext ?_⟩)
  change residue V (φ s) * residue V ⟨w, hwV⟩ = 1
  rw [← map_mul, hsw, map_one]

end ValuationSubring

namespace ValuativeCentre

variable {X : Scheme.{u}} {F : Type u} [Field F]

/-- **Centres specialize along smaller valuation subrings**: if `η` is the centre of `V` and
`η ⤳ x`, then `x` is the centre of a valuation subring `W ≤ V` (a composite of `V` with a
valuation subring of its residue field). -/
theorem IsCentre.exists_le_of_specializes {g : Spec (CommRingCat.of F) ⟶ X}
    {V : ValuationSubring F} {η x : X} (hV : IsCentre g V η) (h : η ⤳ x) :
    ∃ W : ValuationSubring F, W ≤ V ∧ IsCentre g W x := by
  obtain ⟨l, hl, rfl⟩ := hV
  let φ₀ : X.presheaf.stalk x ⟶ CommRingCat.of V :=
    X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo l
  obtain ⟨W, hWV, φ', hloc, hφ'⟩ := ValuationSubring.exists_le_isLocalHom V φ₀.hom
  let f' : X.presheaf.stalk x ⟶ CommRingCat.of W := CommRingCat.ofHom φ'
  haveI : IsLocalHom f'.hom := hloc
  refine ⟨W, hWV, Spec.map f' ≫ X.fromSpecStalk x, ?_, ?_⟩
  · have hf : f' ≫ CommRingCat.ofHom (algebraMap W F) =
        φ₀ ≫ CommRingCat.ofHom (algebraMap V F) := by
      ext s
      exact hφ' s
    rw [genMap, ← Category.assoc, ← Spec.map_comp, hf, Spec.map_comp, Spec.map_comp,
      Category.assoc, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk, ← genMap, hl]
  · rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

end ValuativeCentre

end

end TemperedFundamentalGroups
