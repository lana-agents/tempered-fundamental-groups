/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Orbifold.FibreAut

/-!
# Restriction along a base change with a push: injectivity and image (Blueprint §11, F7)

Let `G : C ⥤ C'` with `e : G ⋙ F' ≅ F` (base change along a cover `X' → X`, so that
`FibreAut.restrict G e : Aut F' →* Aut F` is the map `π₁(X') → π₁(X)`). Suppose there is a
**push** `P : C' ⥤ C` (restriction of scalars along the cover) with

* injections `ι : F' X' ↪ F (P X')`, natural in `X'`;
* an object `E` of `C` (the cover itself) with a point `x₀ ∈ F E`, and morphisms
  `τ : P X' ⟶ E` natural in `X'`, such that the image of `ι` is the fibre of `F τ` over `x₀`;
* morphisms `π : P (G Y) ⟶ Y` with `F π ∘ ι = e` and `u : X' ⟶ G (P X')` with `e ∘ F' u = ι`.

Then `FibreAut.restrict G e` is injective with image the stabilizer of `x₀`
(`PushData.injective_restrict`, `PushData.range_restrict`), and an automorphism `γ'` fixes
`x ∈ F' X'` iff its image fixes `ι x` (`PushData.restrict_app_ι`). If `F E` is finite, the image
has finite index (`PushData.finiteIndex_range_restrict`).
-/

universe w v v' u u'

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ Type w}
  {F' : C' ⥤ Type w} {G : C ⥤ C'} {e : G ⋙ F' ≅ F}

/-- **Push data** for a base change `G` with `e : G ⋙ F' ≅ F` (see the module docstring). -/
structure PushData (G : C ⥤ C') (e : G ⋙ F' ≅ F) where
  /-- The push functor. -/
  P : C' ⥤ C
  /-- The fibre injections. -/
  ι : ∀ X', F'.obj X' → F.obj (P.obj X')
  ι_injective : ∀ X', Function.Injective (ι X')
  ι_natural : ∀ {X' Y'} (m : X' ⟶ Y') (x : F'.obj X'), ι Y' (F'.map m x) = F.map (P.map m) (ι X' x)
  /-- The cover, as an object of `C`. -/
  E : C
  /-- Its base point. -/
  x₀ : F.obj E
  /-- The structure morphisms to the cover. -/
  τ : ∀ X', P.obj X' ⟶ E
  τ_natural : ∀ {X' Y'} (m : X' ⟶ Y'), P.map m ≫ τ Y' = τ X'
  range_ι : ∀ X' (y : F.obj (P.obj X')), (∃ x, ι X' x = y) ↔ F.map (τ X') y = x₀
  /-- The counit. -/
  π : ∀ Y, P.obj (G.obj Y) ⟶ Y
  π_ι : ∀ Y (z : F'.obj (G.obj Y)), F.map (π Y) (ι (G.obj Y) z) = e.hom.app Y z
  /-- The unit. -/
  u : ∀ X', X' ⟶ G.obj (P.obj X')
  u_ι : ∀ X' (x : F'.obj X'), e.hom.app (P.obj X') (F'.map (u X') x) = ι X' x

namespace PushData

variable (D : PushData G e)

lemma restrict_app_ι (γ : FibreAut F') (X' : C') (x : F'.obj X') :
    (FibreAut.restrict G e γ).app (D.P.obj X') (D.ι X' x) = D.ι X' (γ.app X' x) := by
  have h : e.inv.app (D.P.obj X') (D.ι X' x) = F'.map (D.u X') x := by
    rw [← D.u_ι]
    exact Iso.hom_inv_id_app_apply e _ _
  rw [FibreAut.restrict_app, h]
  change e.hom.app _ (γ.app (G.obj (D.P.obj X')) (F'.map (D.u X') x)) = _
  rw [FibreAut.app_naturality, D.u_ι]

lemma restrict_app_ι_eq_iff (γ : FibreAut F') (X' : C') (x : F'.obj X') :
    (FibreAut.restrict G e γ).app (D.P.obj X') (D.ι X' x) = D.ι X' x ↔ γ.app X' x = x := by
  rw [restrict_app_ι]
  exact (D.ι_injective X').eq_iff

include D in
theorem injective_restrict : Function.Injective (FibreAut.restrict G e) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  ext X' x
  rw [FibreAut.one_app, ← restrict_app_ι_eq_iff D, hγ, FibreAut.one_app]

/-- The pointwise stabilizer of the base point `x₀ ∈ F E`. -/
def stab (D : PushData G e) : Subgroup (FibreAut F) where
  carrier := {γ | γ.app D.E D.x₀ = D.x₀}
  one_mem' := rfl
  mul_mem' {γ δ} hγ hδ := by
    simp only [Set.mem_setOf_eq, FibreAut.mul_app] at *
    rw [hδ, hγ]
  inv_mem' {γ} hγ := by
    simp only [Set.mem_setOf_eq] at *
    conv_lhs => rw [← hγ]
    exact FibreAut.inv_app_app γ _ _

lemma mem_stab {γ : FibreAut F} : γ ∈ D.stab ↔ γ.app D.E D.x₀ = D.x₀ := Iff.rfl

lemma isOpen_stab : IsOpen (D.stab : Set (FibreAut F)) :=
  FibreAut.isOpen_stabilizer_singleton F D.E D.x₀

lemma restrict_mem_stab (γ : FibreAut F') : FibreAut.restrict G e γ ∈ D.stab := by
  have hx : ∀ x : F'.obj (G.obj D.E), F.map (D.τ _) (D.ι _ x) = D.x₀ :=
    fun x => (D.range_ι _ _).1 ⟨x, rfl⟩
  let x : F'.obj (G.obj D.E) := e.inv.app D.E D.x₀
  rw [mem_stab]
  calc (FibreAut.restrict G e γ).app D.E D.x₀
      = (FibreAut.restrict G e γ).app D.E (F.map (D.τ _) (D.ι _ x)) := by rw [hx x]
    _ = F.map (D.τ _) ((FibreAut.restrict G e γ).app _ (D.ι _ x)) :=
        FibreAut.app_naturality _ _ _
    _ = D.x₀ := by rw [restrict_app_ι, hx]

/-- The lift of an automorphism fixing `x₀`: on `F' X'` it is the restriction of its action on
`F (P X')` along `ι`. -/
noncomputable def liftApp (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (x : F'.obj X') :
    F'.obj X' :=
  ((D.range_ι X' (γ.app (D.P.obj X') (D.ι X' x))).2 (by
    rw [← FibreAut.app_naturality, (D.range_ι X' _).1 ⟨x, rfl⟩]
    exact hγ)).choose

lemma ι_liftApp (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (x : F'.obj X') :
    D.ι X' (D.liftApp γ hγ X' x) = γ.app (D.P.obj X') (D.ι X' x) :=
  ((D.range_ι X' (γ.app (D.P.obj X') (D.ι X' x))).2 (by
    rw [← FibreAut.app_naturality, (D.range_ι X' _).1 ⟨x, rfl⟩]
    exact hγ)).choose_spec

lemma liftApp_inv (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (x : F'.obj X') :
    D.liftApp γ⁻¹ (D.stab.inv_mem hγ) X' (D.liftApp γ hγ X' x) = x := by
  apply D.ι_injective X'
  rw [ι_liftApp, ι_liftApp, FibreAut.inv_app_app]

lemma liftApp_natural (γ : FibreAut F) (hγ : γ ∈ D.stab) {X' Y' : C'} (m : X' ⟶ Y')
    (x : F'.obj X') : D.liftApp γ hγ Y' (F'.map m x) = F'.map m (D.liftApp γ hγ X' x) := by
  apply D.ι_injective Y'
  rw [ι_liftApp, D.ι_natural, D.ι_natural, ι_liftApp, FibreAut.app_naturality]

/-- **The lift** of an automorphism fixing `x₀`. -/
noncomputable def lift (γ : FibreAut F) (hγ : γ ∈ D.stab) : FibreAut F' :=
  show F' ≅ F' from NatIso.ofComponents
    (fun X' => (Equiv.mk (D.liftApp γ hγ X') (D.liftApp γ⁻¹ (D.stab.inv_mem hγ) X')
      (D.liftApp_inv γ hγ X') (by
        have := D.liftApp_inv γ⁻¹ (D.stab.inv_mem hγ) X'
        simp only [inv_inv] at this
        exact this)).toIso)
    fun {X' Y'} m => by
      ext x
      exact D.liftApp_natural γ hγ m x

lemma lift_app (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (x : F'.obj X') :
    (D.lift γ hγ).app X' x = D.liftApp γ hγ X' x := rfl

lemma restrict_lift (γ : FibreAut F) (hγ : γ ∈ D.stab) :
    FibreAut.restrict G e (D.lift γ hγ) = γ := by
  ext Y y
  rw [FibreAut.restrict_app, lift_app]
  set z := e.inv.app Y y
  have hz : y = e.hom.app Y z := (Iso.inv_hom_id_app_apply e Y y).symm
  rw [← D.π_ι, ι_liftApp, ← FibreAut.app_naturality, D.π_ι, hz]

theorem range_restrict : (FibreAut.restrict G e).range = D.stab := by
  ext γ
  constructor
  · rintro ⟨γ', rfl⟩
    exact D.restrict_mem_stab γ'
  · intro hγ
    exact ⟨D.lift γ hγ, D.restrict_lift γ hγ⟩

/-- The action of `Aut F` on the fibre `F E`. -/
@[reducible] noncomputable def fibreAction (D : PushData G e) : MulAction (FibreAut F) (F.obj D.E) where
  smul γ x := γ.app D.E x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma stab_eq : D.stab = @MulAction.stabilizer _ _ _ D.fibreAction D.x₀ := rfl

theorem finiteIndex_range_restrict [Finite (F.obj D.E)] :
    (FibreAut.restrict G e).range.FiniteIndex := by
  letI := D.fibreAction
  rw [range_restrict, stab_eq]
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self D.x₀) (Set.toFinite _)

end PushData

end TemperedFundamentalGroups
