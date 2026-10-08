/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.W10RouteTwist

/-!
# Twisted `E`-forms (G4, part 5)

Blueprint §9.7a, step 4 (G4 (ii)). The descent statements are applied to the twists
`Aff a c F'` (vertex and edge charts) and `Inv 1 (Aff a c F')` (the chart at `∞` of the root) of
`F' / C(x)`, with the corresponding twists of the `E`-form `F₀`:

* `ratFuncMap_aff`, `ratFuncMap_inv`: `ratFuncMap φ` commutes with the twists;
* `χAff`, `χInvAff` and their compatibility (`isCompat_χAff`, `isCompat_χInvAff`);
* `adjoin_eq_top_of_range_subset`: generators of `F'` generate the twists;
* `isSeparable_of_charZero`: separability in characteristic `0`;
* `mem_normChart_poly_iff`, `mem_normChart_node_iff`, `mem_normChart_inv_iff` and `chartEquiv`:
  the normalized standard charts over `E` are the twisted charts `DRint 0 1`, `Rint c'`
  (TreeBridge over `E`).
-/

universe u

open IsLocalRing Polynomial

namespace SemistableReduction

namespace W10Route

open GaussTube DiscCount AffineTwist SmoothVertex TreeBridge GaussTree ZariskiModel

section RatFuncMap

variable {E C : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  [NontriviallyNormedField C] [IsUltrametricDist C] (φ : E →+* C)

omit [IsUltrametricDist E] [IsUltrametricDist C] in
lemma ratFuncMap_ext {f g : RatFunc E →+* RatFunc C}
    (hC : ∀ e, f (algebraMap E (RatFunc E) e) = g (algebraMap E (RatFunc E) e))
    (hX : f RatFunc.X = g RatFunc.X) : f = g := by
  refine IsLocalization.ringHom_ext (nonZeroDivisors E[X])
    (Polynomial.ringHom_ext (fun e ↦ ?_) ?_)
  · simpa [ratFunc_algebraMap_C] using hC e
  · simpa [RatFunc.algebraMap_X] using hX

lemma ratFuncMap_aff {aE cE : E} (hcE : cE ≠ 0) {a c : C} (ha : φ aE = a) (hcc : φ cE = c)
    (hc : c ≠ 0) (f : RatFunc E) :
    ratFuncMap φ (aff aE cE hcE f) = aff a c hc (ratFuncMap φ f) := by
  subst ha hcc
  have key := ratFuncMap_ext (f := (ratFuncMap φ).comp (aff aE cE hcE).toRingEquiv.toRingHom)
    (g := (aff (φ aE) (φ cE) hc).toRingEquiv.toRingHom.comp (ratFuncMap φ)) (fun e ↦ ?_) ?_
  · exact RingHom.congr_fun key f
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ratFuncMap_algebraMap_C]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, aff_apply, affHom_X, ratFuncMap_gaussCoord,
      DVRDescent.ratFuncMap_X]

omit [IsUltrametricDist E] [IsUltrametricDist C] in
lemma ratFuncMap_inv {cE : E} (hcE : cE ≠ 0) {c : C} (hcc : φ cE = c) (hc : c ≠ 0)
    (f : RatFunc E) : ratFuncMap φ (inv hcE f) = inv hc (ratFuncMap φ f) := by
  subst hcc
  have key := ratFuncMap_ext (f := (ratFuncMap φ).comp (inv hcE).toRingEquiv.toRingHom)
    (g := (inv hc).toRingEquiv.toRingHom.comp (ratFuncMap φ)) (fun e ↦ ?_) ?_
  · exact RingHom.congr_fun key f
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes, ratFuncMap_algebraMap_C]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingHom.coe_coe, AlgEquiv.coe_ringEquiv, inv_apply, invHom_X, map_div₀,
      ratFuncMap_algebraMap_C, DVRDescent.ratFuncMap_X]

end RatFuncMap

section Twists

variable {E C : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  [NontriviallyNormedField C] [IsUltrametricDist C] {φ : E →+* C}
  {F₀ F' : Type*} [Field F₀] [Field F'] [Algebra (RatFunc E) F₀] [Algebra (RatFunc C) F']
  (χ : F₀ →+* F') {aE cE : E} (hcE : cE ≠ 0) {a c : C} (hc : c ≠ 0)

/-- `χ` between the twists `Aff aE cE F₀ → Aff a c F'`. -/
noncomputable def χAff : Aff aE cE hcE F₀ →+* Aff a c hc F' :=
  (toAff hc).toRingHom.comp (χ.comp (toAff hcE).symm.toRingHom)

omit [IsUltrametricDist E] [IsUltrametricDist C] [Algebra (RatFunc E) F₀]
  [Algebra (RatFunc C) F'] in
@[simp]
lemma χAff_toAff (y : F₀) :
    χAff (aE := aE) (a := a) χ hcE hc (toAff hcE y) = toAff hc (χ y) := rfl

/-- `χ` between the twists `Inv 1 (Aff aE cE F₀) → Inv 1 (Aff a c F')`. -/
noncomputable def χInvAff :
    Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀) →+* Inv (1 : C) one_ne_zero (Aff a c hc F') :=
  (toInv one_ne_zero).toRingHom.comp ((χAff χ hcE hc).comp (toInv one_ne_zero).symm.toRingHom)

omit [IsUltrametricDist E] [IsUltrametricDist C] [Algebra (RatFunc E) F₀]
  [Algebra (RatFunc C) F'] in
@[simp]
lemma χInvAff_toInv (y : F₀) :
    χInvAff (aE := aE) (a := a) χ hcE hc (toInv one_ne_zero (toAff hcE y)) =
      toInv one_ne_zero (toAff hc (χ y)) :=
  rfl

variable {χ}

lemma isCompat_χAff (hχ : DVRDescent.IsCompat φ χ) (ha : φ aE = a) (hcc : φ cE = c) :
    DVRDescent.IsCompat φ (χAff (aE := aE) (a := a) χ hcE hc) := fun f ↦ by
  change toAff hc (χ (algebraMap (RatFunc E) F₀ (aff aE cE hcE f))) =
    toAff hc (algebraMap (RatFunc C) F' (aff a c hc (ratFuncMap φ f)))
  rw [hχ, ratFuncMap_aff φ hcE ha hcc hc]

lemma isCompat_χInvAff (hχ : DVRDescent.IsCompat φ χ) (ha : φ aE = a) (hcc : φ cE = c) :
    DVRDescent.IsCompat φ (χInvAff (aE := aE) (a := a) χ hcE hc) := fun f ↦ by
  change toInv one_ne_zero (χAff χ hcE hc (algebraMap (RatFunc E) (Aff aE cE hcE F₀)
      (inv one_ne_zero f))) =
    toInv one_ne_zero (algebraMap (RatFunc C) (Aff a c hc F') (inv one_ne_zero (ratFuncMap φ f)))
  rw [isCompat_χAff hcE hc hχ ha hcc, ratFuncMap_inv φ one_ne_zero (map_one φ) one_ne_zero]

end Twists

/-- Generators of a ring over the range of `f₁` generate it over any larger range. -/
lemma closure_eq_top_of_range_subset {R G : Type*} [CommRing R] [CommRing G] (f₁ f₂ : R →+* G)
    (h : Set.range f₁ ⊆ Set.range f₂) (s : Set G)
    (hs : Subring.closure (Set.range f₁ ∪ s) = ⊤) : Subring.closure (Set.range f₂ ∪ s) = ⊤ :=
  eq_top_iff.2 (hs ▸ Subring.closure_mono (Set.union_subset_union_left _ h))

/-- `adjoin s = ⊤` in terms of the ring closure. -/
lemma adjoin_eq_top_iff {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] (s : Set A) :
    Algebra.adjoin R s = ⊤ ↔ Subring.closure (Set.range (algebraMap R A) ∪ s) = ⊤ := by
  rw [← Algebra.adjoin_eq_ring_closure, ← Algebra.toSubring_eq_top]

/-- Separability in characteristic `0`. -/
lemma isSeparable_of_charZero {E : Type*} [Field E] [CharZero E] (G : Type*) [Field G]
    [Algebra (RatFunc E) G] [FiniteDimensional (RatFunc E) G] :
    Algebra.IsSeparable (RatFunc E) G := by
  haveI : CharZero (RatFunc E) :=
    charZero_of_injective_algebraMap (algebraMap E (RatFunc E)).injective
  infer_instance

section Charts

variable {E : Type*} [NontriviallyNormedField E] [IsUltrametricDist E]
  {F₀ : Type*} [Field F₀] [Algebra (RatFunc E) F₀] {aE cE : E} (hcE : cE ≠ 0)

set_option hygiene false in
local notation "νE" => NormedField.valuation (K := E)

/-- The normalized vertex chart over `E` is the twisted vertex chart. -/
lemma mem_normChart_poly_iff (z : F₀) :
    z ∈ normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)) ↔
      toAff hcE z ∈ DRint (0 : E) 1 (Aff aE cE hcE F₀) := by
  rw [← map_drint_aff hcE]
  exact ⟨fun ⟨w, hw, hwz⟩ ↦ hwz ▸ hw, fun h ↦ ⟨_, h, rfl⟩⟩

/-- The normalized node chart over `E` is the twisted node chart. -/
lemma mem_normChart_node_iff (c' : E) (z : F₀) :
    z ∈ normChart F₀ (nodeChart νE (coord (RatFunc.X : RatFunc E) aE cE) c') ↔
      toAff hcE z ∈ Rint c' (Aff aE cE hcE F₀) := by
  rw [← map_rint_aff hcE c']
  exact ⟨fun ⟨w, hw, hwz⟩ ↦ hwz ▸ hw, fun h ↦ ⟨_, h, rfl⟩⟩

/-- The normalized chart at `∞` over `E` is the twisted vertex chart of the inversion. -/
lemma mem_normChart_inv_iff (z : F₀) :
    z ∈ normChart F₀ (polyChart νE (coord (RatFunc.X : RatFunc E) aE cE)⁻¹) ↔
      toInv one_ne_zero (toAff hcE z) ∈
        DRint (0 : E) 1 (Inv (1 : E) one_ne_zero (Aff aE cE hcE F₀)) := by
  rw [← map_drint_inv_aff hcE]
  exact ⟨fun ⟨w, hw, hwz⟩ ↦ hwz ▸ hw, fun h ↦ ⟨_, h, rfl⟩⟩

end Charts

/-- A ring isomorphism of subrings from a ring isomorphism of the ambient rings. -/
noncomputable def chartEquiv {F F₂ : Type*} [Field F] [Field F₂] (τ : F ≃+* F₂) (A : Subring F)
    {R : Type*} [CommRing R] [Algebra R F₂] (B : Subalgebra R F₂) (h : ∀ z, z ∈ A ↔ τ z ∈ B) :
    A ≃+* B where
  toFun z := ⟨τ z, (h z).1 z.2⟩
  invFun w := ⟨τ.symm w, (h _).2 (by rw [RingEquiv.apply_symm_apply]; exact w.2)⟩
  left_inv z := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

@[simp]
lemma coe_chartEquiv {F F₂ : Type*} [Field F] [Field F₂] (τ : F ≃+* F₂) (A : Subring F)
    {R : Type*} [CommRing R] [Algebra R F₂] (B : Subalgebra R F₂) (h : ∀ z, z ∈ A ↔ τ z ∈ B)
    (z : A) : ((chartEquiv τ A B h z : B) : F₂) = τ z := rfl

end W10Route

end SemistableReduction
