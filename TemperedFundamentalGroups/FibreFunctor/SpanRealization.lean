/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Orbifold.FibreAut

/-!
# Restricting fibre-functor automorphisms to a subcategory reached by `Φ`-bijective spans

Let `Φ : C ⥤ Type w` and let `D` be a full subcategory of `C` (a property of objects). A
**`Φ`-span** from `X` to `D` (`FibreAut.PhiSpan`) is a diagram `X ⟵ W ⟶ c` with `c ∈ D` whose two
morphisms become bijections under `Φ`. Suppose that

* (S1) every object has an admissible `Φ`-span to `D` (for a chosen class of admissible spans
  containing the identity spans of objects of `D`), and
* (S2) admissible spans can be refined along morphisms: for `u : X ⟶ Y` and admissible spans
  `s` of `X`, `s'` of `Y` there are an admissible span `t` of `X` and morphisms from `t` to `s`
  (over `X`) and to `s'` (over `u`), including morphisms between the `D`-ends, making the obvious
  squares commute.

Then restricting automorphisms of `Φ` to `D` is an isomorphism of topological groups
(`FibreAut.restrictEquivOfPhiSpans`). Every automorphism of `Φ|_D` is transported along the
spans; (S2) makes the result independent of the span and natural.

This is how the tempered group defined through all projective models is identified with the one
defined through semistable models only (Blueprint §10): an object is reached from an object over
a semistable level by pulling back along a domination of models, which is `Φ`-bijective.
-/

universe w v u

open CategoryTheory Pi1.Orbifold Pi1.Orbifold.FibreAut

namespace TemperedFundamentalGroups

namespace FibreAut

variable {C : Type u} [Category.{v} C] (Φ : C ⥤ Type w) (D : ObjectProperty C)

/-- A `Φ`-span `X ⟵ W ⟶ ι c` from an object `X` to the full subcategory `D`. -/
structure PhiSpan (X : C) where
  /-- The apex. -/
  W : C
  /-- The end in `D`. -/
  c : D.FullSubcategory
  /-- The leg to `X`. -/
  m : W ⟶ X
  /-- The leg to `D`. -/
  n : W ⟶ D.ι.obj c
  bij_m : Function.Bijective (Φ.map m)
  bij_n : Function.Bijective (Φ.map n)

/-- The hypotheses (S1), (S2), for a class `adm` of admissible spans containing the identity spans
of objects of `D`. -/
structure HasPhiSpans (adm : ∀ X : C, PhiSpan Φ D X → Prop) : Prop where
  /-- Every object has an admissible span. -/
  nonempty : ∀ X : C, ∃ s : PhiSpan Φ D X, adm X s
  /-- Admissible spans can be refined along morphisms. -/
  refine : ∀ {X Y : C} (u : X ⟶ Y) (s : PhiSpan Φ D X) (s' : PhiSpan Φ D Y), adm X s → adm Y s' →
    ∃ (t : PhiSpan Φ D X) (w : t.W ⟶ s.W) (v : t.c ⟶ s.c) (w' : t.W ⟶ s'.W) (v' : t.c ⟶ s'.c),
      adm X t ∧ w ≫ s.m = t.m ∧ t.n ≫ D.ι.map v = w ≫ s.n ∧
      w' ≫ s'.m = t.m ≫ u ∧ t.n ≫ D.ι.map v' = w' ≫ s'.n

variable {Φ D}

namespace PhiSpan

variable {X : C} (s : PhiSpan Φ D X)

/-- The bijection `Φ W ≃ Φ X`. -/
noncomputable def em : Φ.obj s.W ≃ Φ.obj X := Equiv.ofBijective _ s.bij_m

/-- The bijection `Φ W ≃ Φ c`. -/
noncomputable def en : Φ.obj s.W ≃ Φ.obj (D.ι.obj s.c) := Equiv.ofBijective _ s.bij_n

/-- The permutation of `Φ X` transported from an automorphism of `Φ|_D` along the span. -/
noncomputable def transport (β : FibreAut (D.ι ⋙ Φ)) (x : Φ.obj X) : Φ.obj X :=
  s.em (s.en.symm (β.app s.c (s.en (s.em.symm x))))

lemma em_apply (y : Φ.obj s.W) : s.em y = Φ.map s.m y := rfl

lemma en_apply (y : Φ.obj s.W) : s.en y = Φ.map s.n y := rfl

/-- The transport intertwines `Φ m` with the transport along the `W`-end. -/
lemma transport_map_m (β : FibreAut (D.ι ⋙ Φ)) (y : Φ.obj s.W) :
    s.transport β (Φ.map s.m y) = Φ.map s.m (s.en.symm (β.app s.c (Φ.map s.n y))) := by
  rw [transport, ← em_apply, Equiv.symm_apply_apply, em_apply, en_apply]

end PhiSpan

/-- **The comparison lemma.** If `t` refines `s` over `u : X ⟶ Y` (`w : t.W ⟶ s.W` with
`w ≫ s.m = t.m ≫ u`, and a morphism `v` of the `D`-ends compatible with `w`), then the transport
along `s` after `Φ u` equals `Φ u` after the transport along `t`. -/
lemma transport_naturality {X Y : C} (u : X ⟶ Y) (s : PhiSpan Φ D Y) (t : PhiSpan Φ D X)
    (w : t.W ⟶ s.W) (v : t.c ⟶ s.c) (hw : w ≫ s.m = t.m ≫ u)
    (hv : t.n ≫ D.ι.map v = w ≫ s.n) (β : FibreAut (D.ι ⋙ Φ)) (x : Φ.obj X) :
    s.transport β (Φ.map u x) = Φ.map u (t.transport β x) := by
  obtain ⟨y, rfl⟩ := t.bij_m.2 x
  have h1 : Φ.map u (Φ.map t.m y) = Φ.map s.m (Φ.map w y) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, hw]
  rw [h1, s.transport_map_m, t.transport_map_m]
  -- `β` is natural along `v`
  have hβ : β.app s.c (Φ.map (D.ι.map v) (Φ.map t.n y)) =
      Φ.map (D.ι.map v) (β.app t.c (Φ.map t.n y)) :=
    app_naturality β v (Φ.map t.n y)
  have h2 : Φ.map s.n (Φ.map w y) = Φ.map (D.ι.map v) (Φ.map t.n y) := by
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, hv]
  rw [h2]
  change Φ.map s.m (s.en.symm (β.app s.c (Φ.map (D.ι.map v) (Φ.map t.n y)))) = _
  rw [hβ]
  -- write the transported element of `t.W`
  set z := t.en.symm (β.app t.c (Φ.map t.n y))
  have hz : Φ.map t.n z = β.app t.c (Φ.map t.n y) := t.en.apply_symm_apply _
  have h3 : Φ.map (D.ι.map v) (β.app t.c (Φ.map t.n y)) = s.en (Φ.map w z) := by
    rw [PhiSpan.en_apply, ← hz, ← Functor.map_comp_apply, ← Functor.map_comp_apply, hv]
  rw [h3, Equiv.symm_apply_apply, ← Functor.map_comp_apply, ← Functor.map_comp_apply, hw]

variable {adm : ∀ X : C, PhiSpan Φ D X → Prop} (hS : HasPhiSpans Φ D adm)
include hS

/-- The transport does not depend on the span. -/
lemma transport_eq {X : C} (s₁ s₂ : PhiSpan Φ D X) (h₁ : adm X s₁) (h₂ : adm X s₂)
    (β : FibreAut (D.ι ⋙ Φ)) : s₁.transport β = s₂.transport β := by
  obtain ⟨t, w₁, v₁, w₂, v₂, -, h₁, h₁', h₂, h₂'⟩ := hS.refine (𝟙 X) s₁ s₂ h₁ h₂
  funext x
  have e₁ := transport_naturality (𝟙 X) s₁ t w₁ v₁ (by rw [h₁, Category.comp_id]) h₁' β x
  have e₂ := transport_naturality (𝟙 X) s₂ t w₂ v₂ h₂ h₂' β x
  simp only [CategoryTheory.Functor.map_id, types_id_apply] at e₁ e₂
  rw [e₁, e₂]

/-- The transport is natural. -/
lemma transport_natural {X Y : C} (u : X ⟶ Y) (s : PhiSpan Φ D X) (s' : PhiSpan Φ D Y)
    (hs : adm X s) (hs' : adm Y s') (β : FibreAut (D.ι ⋙ Φ)) (x : Φ.obj X) :
    s'.transport β (Φ.map u x) = Φ.map u (s.transport β x) := by
  obtain ⟨t, -, -, w', v', ht, -, -, h₂, h₂'⟩ := hS.refine u s s' hs hs'
  rw [transport_naturality u s' t w' v' h₂ h₂' β x, transport_eq hS t s ht hs]

/-- The chosen admissible span of an object. -/
noncomputable def chosenSpan (X : C) : PhiSpan Φ D X := (hS.nonempty X).choose

lemma chosenSpan_adm (X : C) : adm X (chosenSpan hS X) := (hS.nonempty X).choose_spec

omit hS in
lemma transport_mul {X : C} (s : PhiSpan Φ D X) (β γ : FibreAut (D.ι ⋙ Φ)) (x : Φ.obj X) :
    s.transport (β * γ) x = s.transport β (s.transport γ x) := by
  simp only [PhiSpan.transport, Equiv.symm_apply_apply, Equiv.apply_symm_apply, mul_app]

omit hS in
lemma transport_one {X : C} (s : PhiSpan Φ D X) (x : Φ.obj X) : s.transport 1 x = x := by
  simp only [PhiSpan.transport, one_app, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

/-- The permutation of `Φ X` transported along the chosen span. -/
noncomputable def transportEquiv (β : FibreAut (D.ι ⋙ Φ)) (X : C) : Φ.obj X ≃ Φ.obj X where
  toFun := (chosenSpan hS X).transport β
  invFun := (chosenSpan hS X).transport β⁻¹
  left_inv x := by rw [← transport_mul, inv_mul_cancel, transport_one]
  right_inv x := by rw [← transport_mul, mul_inv_cancel, transport_one]

/-- The automorphism of `Φ` extending an automorphism of `Φ|_D`. -/
noncomputable def extendSpan (β : FibreAut (D.ι ⋙ Φ)) : FibreAut Φ :=
  show Φ ≅ Φ from NatIso.ofComponents (fun X => (transportEquiv hS β X).toIso)
    (fun {X Y} u => by
      ext x
      exact transport_natural hS u (chosenSpan hS X) (chosenSpan hS Y) (chosenSpan_adm hS X)
        (chosenSpan_adm hS Y) β x)

lemma extendSpan_app (β : FibreAut (D.ι ⋙ Φ)) (X : C) (x : Φ.obj X) :
    (extendSpan hS β).app X x = (chosenSpan hS X).transport β x := rfl

/-- The identity span of an object of `D`. -/
noncomputable def idSpan (c : D.FullSubcategory) : PhiSpan Φ D (D.ι.obj c) where
  W := D.ι.obj c
  c := c
  m := 𝟙 _
  n := 𝟙 _
  bij_m := by rw [CategoryTheory.Functor.map_id]; exact Function.bijective_id
  bij_n := by rw [CategoryTheory.Functor.map_id]; exact Function.bijective_id

omit hS in
lemma idSpan_transport (c : D.FullSubcategory) (β : FibreAut (D.ι ⋙ Φ))
    (x : Φ.obj (D.ι.obj c)) : (idSpan c).transport β x = β.app c x := by
  have h : ∀ y : Φ.obj (D.ι.obj c), (idSpan (Φ := Φ) c).em y = y := fun y ↦ by
    rw [PhiSpan.em_apply]; simp [idSpan]; rfl
  have h' : ∀ y : Φ.obj (D.ι.obj c), (idSpan (Φ := Φ) c).en y = y := fun y ↦ by
    rw [PhiSpan.en_apply]; simp [idSpan]; rfl
  have hs : ∀ y : Φ.obj (D.ι.obj c), (idSpan (Φ := Φ) c).em.symm y = y := fun y ↦ by
    rw [Equiv.symm_apply_eq, h]
  have hs' : ∀ y : Φ.obj (D.ι.obj c), (idSpan (Φ := Φ) c).en.symm y = y := fun y ↦ by
    rw [Equiv.symm_apply_eq, h']
  simp only [PhiSpan.transport, hs, h', hs', h]
  rfl

omit hS in
/-- The restriction of `Φ` to `D` as a functor, with the identity comparison. -/
abbrev restrictD : FibreAut Φ →* FibreAut (D.ι ⋙ Φ) := restrict D.ι (Iso.refl _)

omit hS in
lemma restrictD_app (α : FibreAut Φ) (c : D.FullSubcategory) (x : Φ.obj (D.ι.obj c)) :
    (restrictD α).app c x = α.app (D.ι.obj c) x := rfl

omit hS in
/-- Transport of a restricted automorphism is the automorphism itself. -/
lemma transport_restrictD {X : C} (s : PhiSpan Φ D X) (α : FibreAut Φ) (x : Φ.obj X) :
    s.transport (restrictD α) x = α.app X x := by
  obtain ⟨y, rfl⟩ := s.bij_m.2 x
  rw [s.transport_map_m, restrictD_app, app_naturality α s.n y, ← PhiSpan.en_apply,
    Equiv.symm_apply_apply, app_naturality α s.m y]

lemma restrictD_extendSpan (hid : ∀ c, adm (D.ι.obj c) (idSpan c)) (β : FibreAut (D.ι ⋙ Φ)) :
    restrictD (extendSpan hS β) = β := by
  ext c x
  rw [restrictD_app, extendSpan_app, transport_eq hS _ (idSpan c) (chosenSpan_adm hS _) (hid c),
    idSpan_transport]

lemma extendSpan_restrictD (α : FibreAut Φ) : extendSpan hS (restrictD α) = α := by
  ext X x
  rw [extendSpan_app, transport_restrictD]

/-- **Restriction to a subcategory reached by `Φ`-bijective spans is an isomorphism of topological
groups.** -/
noncomputable def restrictEquivOfPhiSpans (hid : ∀ c, adm (D.ι.obj c) (idSpan c)) :
    FibreAut Φ ≃ₜ* FibreAut (D.ι ⋙ Φ) where
  toFun := restrictD
  invFun := extendSpan hS
  left_inv := extendSpan_restrictD hS
  right_inv := restrictD_extendSpan hS hid
  map_mul' := map_mul restrictD
  continuous_toFun := continuous_restrict _ _
  continuous_invFun := by
    classical
    let ψ : FibreAut (D.ι ⋙ Φ) →* FibreAut Φ :=
      { toFun := extendSpan hS
        map_one' := by
          rw [← map_one (restrictD (Φ := Φ) (D := D)), extendSpan_restrictD]
        map_mul' := fun β γ ↦ by
          conv_lhs => rw [← restrictD_extendSpan hS hid β, ← restrictD_extendSpan hS hid γ,
            ← map_mul, extendSpan_restrictD] }
    change Continuous ψ
    refine continuous_of_stabilizer Φ ψ fun S => ?_
    let T : Finset (Σ c : D.FullSubcategory, (D.ι ⋙ Φ).obj c) := S.image fun p =>
      ⟨(chosenSpan hS p.1).c,
        (chosenSpan hS p.1).en ((chosenSpan hS p.1).em.symm p.2)⟩
    refine Filter.mem_of_superset (stabilizer_mem_nhds_one _ T) fun β hβ p hp => ?_
    have hT := hβ ⟨(chosenSpan hS p.1).c, (chosenSpan hS p.1).en ((chosenSpan hS p.1).em.symm p.2)⟩
      (Finset.mem_image.2 ⟨p, hp, rfl⟩)
    change (chosenSpan hS p.1).transport β p.2 = p.2
    rw [PhiSpan.transport]
    rw [hT, Equiv.symm_apply_apply, Equiv.apply_symm_apply]

end FibreAut

end TemperedFundamentalGroups
