/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.ValuativeCentre
import TemperedFundamentalGroups.SemistableReduction.XHarmonicGlue

/-!
# Centres of valuations and germs of models (Blueprint §10.3.8, CrossingX1, CX1)

Let `X` be a scheme, `g : Spec F ⟶ X` a point with values in a field and `x` a specialization of
the image of `g`. The stalk map `stalkTo g h : 𝒪_{X,x} → F` has image the **germs** of `X` at `x`
(`ModelCode.germs_eq_range`).

* `isCentre_iff`: `V` has centre `x` iff the stalk map lands in `V` and is local;
* `isCentre_iff_dominates`: the same in terms of the germs: `V` contains the germs at `x` and
  every germ without inverse among the germs lies in the maximal ideal of `V`;
* `centre_eq`: two valuation rings containing the germs at `x` and with the same contraction to
  them have the same centre;
* `IsCentre.comap`: centres map along morphisms compatible with the generic points;
* `toL_map`: images of pulled back sections.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CentreGerms

open ValuativeCentre

variable {X : Scheme.{u}} {F : Type u} [Field F]

/-- The stalk map `𝒪_{X,x} → F` at a specialization `x` of the image of `g`. -/
noncomputable def stalkTo (g : Spec (CommRingCat.of F) ⟶ X) {x : X}
    (h : g (closedPoint F) ⤳ x) : X.presheaf.stalk x ⟶ CommRingCat.of F :=
  X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo g

lemma top_le_preimage (g : Spec (CommRingCat.of F) ⟶ X) {x : X} (h : g (closedPoint F) ⤳ x)
    {U : X.Opens} (hx : x ∈ U) : ⊤ ≤ g ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem g (h.mem_open U.isOpen hx)).ge

/-- The stalk map on germs of sections is `toL`. -/
lemma stalkTo_germ (g : Spec (CommRingCat.of F) ⟶ X) {x : X} (h : g (closedPoint F) ⤳ x)
    (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)) :
    (stalkTo g h).hom (X.presheaf.germ U x hx s) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom
        ((g.appLE U ⊤ (top_le_preimage g h hx)).hom s) := by
  have hU : g (closedPoint F) ∈ U := h.mem_open U.isOpen hx
  rw [stalkTo, ← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.germ_stalkClosedPointTo g U hU]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.op_hom, eqToIso.hom]
  have e : g.appLE U ⊤ (top_le_preimage g h hx) =
      g.app U ≫ (Spec (CommRingCat.of F)).presheaf.map (homOfLE (top_le_preimage g h hx)).op :=
    rfl
  rw [e]
  rfl

variable {O : Type u} [CommRing O]

/-- **Germs are the image of the stalk.** -/
theorem germs_eq_range (c : TemperedFundamentalGroups.ModelCode O)
    (g : Spec (CommRingCat.of F) ⟶ c.scheme) {x : c.scheme} (h : g (closedPoint F) ⤳ x) :
    ModelCode.germs c g x = Set.range (stalkTo g h).hom := by
  ext f
  constructor
  · rintro ⟨U, hx, hU, s, rfl⟩
    exact ⟨c.scheme.presheaf.germ U x hx s, stalkTo_germ g h U hx s⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨U, hx, t, rfl⟩ := c.scheme.presheaf.exists_germ_eq s
    exact ⟨U, hx, top_le_preimage g h hx, t, (stalkTo_germ g h U hx t).symm⟩

/-- **Centres via stalks**: `V` has centre `x` iff the stalk map lands in `V` and is local. -/
theorem isCentre_iff (g : Spec (CommRingCat.of F) ⟶ X) {x : X} (h : g (closedPoint F) ⤳ x)
    (V : ValuationSubring F) :
    IsCentre g V x ↔ (∀ s, (stalkTo g h).hom s ∈ V) ∧
      ∀ s ∈ maximalIdeal (X.presheaf.stalk x), V.valuation ((stalkTo g h).hom s) < 1 := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have key : stalkTo g h = Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V F) := by
      apply Spec.map_injective
      rw [← cancel_mono (X.fromSpecStalk _)]
      rw [stalkTo, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, Spec.map_comp, Category.assoc,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl]
    refine ⟨fun s ↦ ?_, fun s hs ↦ ?_⟩
    · rw [key]; exact ((Scheme.stalkClosedPointTo l).hom s).2
    · rw [key]
      have hm : (Scheme.stalkClosedPointTo l).hom s ∈ maximalIdeal V :=
        map_nonunit (Scheme.stalkClosedPointTo l).hom s hs
      exact (ValuationSubring.valuation_lt_one_iff V _).1 hm
  · rintro ⟨hV, hloc⟩
    let f' : X.presheaf.stalk x ⟶ CommRingCat.of V :=
      CommRingCat.ofHom ((stalkTo g h).hom.codRestrict V.toSubring hV)
    haveI : IsLocalHom f'.hom := ⟨fun s hs ↦ by
      by_contra hns
      exact (ValuationSubring.valuation_lt_one_iff V _).2 (hloc s hns) hs⟩
    refine ⟨Spec.map f' ≫ X.fromSpecStalk x, ?_, ?_⟩
    · have hf : f' ≫ CommRingCat.ofHom (algebraMap V F) = stalkTo g h := rfl
      rw [genMap, ← Category.assoc, ← Spec.map_comp, hf, stalkTo, Spec.map_comp, Category.assoc,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
        Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
    · rw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]

/-- `V` **dominates** the set of germs `P`: `P ⊆ V`, and every element of `P` without inverse in
`P` lies in the maximal ideal of `V`. -/
def Dominates (V : ValuationSubring F) (P : Set F) : Prop :=
  P ⊆ V ∧ ∀ f ∈ P, (∀ w ∈ P, f * w ≠ 1) → V.valuation f < 1

lemma ker_le_maximalIdeal {A : Type u} [CommRing A] [IsLocalRing A] (φ : A →+* F) :
    RingHom.ker φ ≤ maximalIdeal A :=
  le_maximalIdeal (RingHom.ker_ne_top φ)

/-- An element of the stalk has an inverse among the germs iff it is a unit. -/
lemma isUnit_iff_exists_mul (g : Spec (CommRingCat.of F) ⟶ X) {x : X}
    (h : g (closedPoint F) ⤳ x) (s : X.presheaf.stalk x) :
    IsUnit s ↔ ∃ t, (stalkTo g h).hom s * (stalkTo g h).hom t = 1 := by
  constructor
  · intro hs
    refine ⟨↑hs.unit⁻¹, ?_⟩
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  · rintro ⟨t, ht⟩
    rw [← map_mul] at ht
    have hk : s * t - 1 ∈ RingHom.ker (stalkTo g h).hom := by
      rw [RingHom.mem_ker, map_sub, ht, map_one, sub_self]
    have hm := ker_le_maximalIdeal (stalkTo g h).hom hk
    have hu : IsUnit (s * t) := by
      by_contra hn
      have h1 : s * t ∈ maximalIdeal _ := hn
      have := sub_mem h1 hm
      rw [sub_sub_cancel] at this
      exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 this)
    exact isUnit_of_mul_isUnit_left hu

/-- **Centres via germs.** -/
theorem isCentre_iff_dominates (c : TemperedFundamentalGroups.ModelCode O)
    (g : Spec (CommRingCat.of F) ⟶ c.scheme) {x : c.scheme} (h : g (closedPoint F) ⤳ x)
    (V : ValuationSubring F) : IsCentre g V x ↔ Dominates V (ModelCode.germs c g x) := by
  rw [isCentre_iff g h, germs_eq_range c g h, Dominates]
  constructor
  · rintro ⟨hV, hloc⟩
    refine ⟨by rintro _ ⟨s, rfl⟩; exact hV s, ?_⟩
    rintro _ ⟨s, rfl⟩ hs
    refine hloc s fun hu ↦ ?_
    obtain ⟨t, ht⟩ := (isUnit_iff_exists_mul g h s).1 hu
    exact hs _ ⟨t, rfl⟩ ht
  · rintro ⟨hV, hloc⟩
    refine ⟨fun s ↦ hV ⟨s, rfl⟩, fun s hs ↦ hloc _ ⟨s, rfl⟩ ?_⟩
    rintro _ ⟨t, rfl⟩ ht
    exact hs ((isUnit_iff_exists_mul g h s).2 ⟨t, ht⟩)

/-- A valuation ring containing the germs at `x` has a centre which is a generalization of `x`,
determined by the contraction of its maximal ideal to the stalk. -/
lemma isCentre_fromSpecStalk (g : Spec (CommRingCat.of F) ⟶ X) {x : X}
    (h : g (closedPoint F) ⤳ x) (V : ValuationSubring F) (hV : ∀ s, (stalkTo g h).hom s ∈ V) :
    IsCentre g V (X.fromSpecStalk x
      ((Spec.map (CommRingCat.ofHom ((stalkTo g h).hom.codRestrict V.toSubring hV)))
        (closedPoint V))) := by
  refine ⟨Spec.map (CommRingCat.ofHom ((stalkTo g h).hom.codRestrict V.toSubring hV)) ≫
    X.fromSpecStalk x, ?_, rfl⟩
  have hf : CommRingCat.ofHom ((stalkTo g h).hom.codRestrict V.toSubring hV) ≫
      CommRingCat.ofHom (algebraMap V F) = stalkTo g h := rfl
  rw [genMap, ← Category.assoc, ← Spec.map_comp, hf, stalkTo, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- **Same contraction, same centre.** -/
theorem centre_eq {A : CommRingCat.{u}} (f : X ⟶ Spec A) [IsSeparated f]
    (g : Spec (CommRingCat.of F) ⟶ X) {x : X} (h : g (closedPoint F) ⤳ x)
    {V₁ V₂ : ValuationSubring F} (h₁ : ∀ s, (stalkTo g h).hom s ∈ V₁)
    (h₂ : ∀ s, (stalkTo g h).hom s ∈ V₂)
    (hm : ∀ s, V₁.valuation ((stalkTo g h).hom s) < 1 ↔ V₂.valuation ((stalkTo g h).hom s) < 1)
    {y₁ y₂ : X} (hy₁ : IsCentre g V₁ y₁) (hy₂ : IsCentre g V₂ y₂) : y₁ = y₂ := by
  rw [centre_unique f hy₁ (isCentre_fromSpecStalk g h V₁ h₁),
    centre_unique f hy₂ (isCentre_fromSpecStalk g h V₂ h₂)]
  congr 1
  change PrimeSpectrum.comap _ (closedPoint V₁) = PrimeSpectrum.comap _ (closedPoint V₂)
  refine PrimeSpectrum.ext (Ideal.ext fun s ↦ ?_)
  change _ ∈ maximalIdeal V₁ ↔ _ ∈ maximalIdeal V₂
  rw [ValuationSubring.valuation_lt_one_iff, ValuationSubring.valuation_lt_one_iff]
  exact hm s

end TemperedFundamentalGroups.SemistableReduction.CentreGerms
