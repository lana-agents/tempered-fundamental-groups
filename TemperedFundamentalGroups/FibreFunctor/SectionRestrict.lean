/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Pi1.Orbifold.FibreAut

/-!
# Restriction along a functor with a quasi-inverse on fibres (Blueprint §11, F8)

Let `G : C ⥤ C'` with `e : G ⋙ F' ≅ F`, so that `FibreAut.restrict G e : Aut F' →* Aut F`.

* If every object `X'` of `C'` receives a morphism `w : G (S X') ⟶ X'` from an object in the
  image of `G` which is **surjective on fibres**, then `FibreAut.restrict G e` is injective and
  inducing (`injective_restrict_of_dominated`, `isInducing_restrict_of_dominated`).
* If moreover (`SectionData`) the `w` are bijective on fibres and natural for maps
  `S X' ⟶ S Y'` lifting the morphisms of `C'`, and every `Y` has a morphism
  `π : S (G Y) ⟶ Y` compatible with `w` and `e`, then `FibreAut.restrict G e` is bijective
  (`SectionData.bijective_restrict`), an open embedding (`SectionData.isOpenEmbedding_restrict`),
  and an isomorphism of topological groups (`SectionData.restrictEquiv`).
-/

universe w v v' u u'

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ Type w}
  {F' : C' ⥤ Type w} {G : C ⥤ C'} {e : G ⋙ F' ≅ F}

lemma restrict_app_e (γ : FibreAut F') (Y : C) (y : F'.obj (G.obj Y)) :
    (FibreAut.restrict G e γ).app Y (e.hom.app Y y) = e.hom.app Y (γ.app (G.obj Y) y) := by
  rw [FibreAut.restrict_app]
  congr 2
  exact Iso.hom_inv_id_app_apply e Y y

lemma e_hom_app_injective (Y : C) : Function.Injective (e.hom.app Y) := fun a b h => by
  have := congrArg (e.inv.app Y) h
  rwa [Iso.hom_inv_id_app_apply, Iso.hom_inv_id_app_apply] at this

lemma restrict_app_e_eq_iff (γ : FibreAut F') (Y : C) (y : F'.obj (G.obj Y)) :
    (FibreAut.restrict G e γ).app Y (e.hom.app Y y) = e.hom.app Y y ↔
      γ.app (G.obj Y) y = y := by
  rw [restrict_app_e]
  exact (e_hom_app_injective Y).eq_iff

section Dominated

variable (S : C' → C) (w : ∀ X', G.obj (S X') ⟶ X')
  (hw : ∀ X', Function.Surjective (F'.map (w X')))
include hw

omit hw in
/-- An automorphism fixing `y` fixes its image under `w`. -/
lemma app_w_of_restrict (γ : FibreAut F') (X' : C') (y : F'.obj (G.obj (S X')))
    (h : (FibreAut.restrict G e γ).app (S X') (e.hom.app _ y) = e.hom.app _ y) :
    γ.app X' (F'.map (w X') y) = F'.map (w X') y := by
  rw [FibreAut.app_naturality, (restrict_app_e_eq_iff γ _ y).1 h]

/-- **Injectivity** of the restriction when every object is dominated on fibres by an object in
the image of `G`. -/
theorem injective_restrict_of_dominated : Function.Injective (FibreAut.restrict G e) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  ext X' x
  obtain ⟨y, rfl⟩ := hw X' x
  rw [FibreAut.one_app]
  exact app_w_of_restrict S w γ X' y (by rw [hγ, FibreAut.one_app])

theorem isInducing_restrict_of_dominated : Topology.IsInducing (FibreAut.restrict G e) := by
  classical
  rw [IsTopologicalGroup.isInducing_iff_nhds_one]
  refine le_antisymm ((FibreAut.continuous_restrict G e).tendsto' 1 1 (map_one _)).le_comap ?_
  rw [((FibreAut.nhds_one_hasBasis F).comap _).le_basis_iff (FibreAut.nhds_one_hasBasis F')]
  intro T _
  refine ⟨T.image (fun p => (⟨S p.1, e.hom.app _ (hw p.1 p.2).choose⟩ : Σ c : C, F.obj c)),
    trivial, fun γ hγ p hp => ?_⟩
  have h := hγ _ (Finset.mem_image_of_mem _ hp)
  have := app_w_of_restrict S w γ p.1 _ h
  rwa [(hw p.1 p.2).choose_spec] at this

end Dominated

/-- **Section data** for `G` with `e : G ⋙ F' ≅ F`: a lift `S` of the objects and morphisms of
`C'` to `C` with comparison morphisms `w : G (S X') ⟶ X'` bijective on fibres, and maps
`π : S (G Y) ⟶ Y` compatible with `w` and `e`. -/
structure SectionData (G : C ⥤ C') (e : G ⋙ F' ≅ F) where
  /-- The lift of objects. -/
  S : C' → C
  /-- The lift of morphisms. -/
  map : ∀ {X' Y' : C'} (_ : X' ⟶ Y'), S X' ⟶ S Y'
  /-- The comparison morphisms. -/
  w : ∀ X', G.obj (S X') ⟶ X'
  w_natural : ∀ {X' Y' : C'} (m : X' ⟶ Y'), G.map (map m) ≫ w Y' = w X' ≫ m
  w_bijective : ∀ X', Function.Bijective (F'.map (w X'))
  /-- The maps `S (G Y) ⟶ Y`. -/
  π : ∀ Y, S (G.obj Y) ⟶ Y
  π_e : ∀ Y (z : F'.obj (G.obj (S (G.obj Y)))),
    F.map (π Y) (e.hom.app _ z) = e.hom.app Y (F'.map (w (G.obj Y)) z)

namespace SectionData

variable (D : SectionData G e)
include D

/-- The fibre bijection `F' (G (S X')) ≃ F' X'`. -/
noncomputable def W (X' : C') : F'.obj (G.obj (D.S X')) ≃ F'.obj X' :=
  Equiv.ofBijective _ (D.w_bijective X')

lemma W_apply (X' : C') (y : F'.obj (G.obj (D.S X'))) : D.W X' y = F'.map (D.w X') y := rfl

lemma map_W {X' Y' : C'} (m : X' ⟶ Y') (y : F'.obj (G.obj (D.S X'))) :
    F'.map m (D.W X' y) = D.W Y' (F'.map (G.map (D.map m)) y) := by
  rw [W_apply, W_apply]
  change (F'.map (D.w X') ≫ F'.map m) y = (F'.map (G.map (D.map m)) ≫ F'.map (D.w Y')) y
  rw [← F'.map_comp, ← F'.map_comp, D.w_natural]

omit D in
lemma e_hom_map (Y Z : C) (g : Y ⟶ Z) (y : F'.obj (G.obj Y)) :
    e.hom.app Z (F'.map (G.map g) y) = F.map g (e.hom.app Y y) :=
  NatTrans.naturality_apply e.hom g y

omit D in
lemma e_inv_map (Y Z : C) (g : Y ⟶ Z) (y : F.obj Y) :
    e.inv.app Z (F.map g y) = F'.map (G.map g) (e.inv.app Y y) :=
  NatTrans.naturality_apply e.inv g y

/-- The lift of `γ ∈ Aut F` on the fibre `F' X'`. -/
noncomputable def liftApp (γ : FibreAut F) (X' : C') (x : F'.obj X') : F'.obj X' :=
  D.W X' (e.inv.app _ (γ.app (D.S X') (e.hom.app _ ((D.W X').symm x))))

lemma liftApp_inv (γ : FibreAut F) (X' : C') (x : F'.obj X') :
    D.liftApp γ⁻¹ X' (D.liftApp γ X' x) = x := by
  simp only [liftApp, Equiv.symm_apply_apply, Iso.inv_hom_id_app_apply, FibreAut.inv_app_app,
    Iso.hom_inv_id_app_apply, Equiv.apply_symm_apply]

lemma liftApp_natural (γ : FibreAut F) {X' Y' : C'} (m : X' ⟶ Y') (x : F'.obj X') :
    D.liftApp γ Y' (F'.map m x) = F'.map m (D.liftApp γ X' x) := by
  obtain ⟨y, rfl⟩ := (D.W X').surjective x
  rw [liftApp, liftApp, map_W, Equiv.symm_apply_apply, Equiv.symm_apply_apply, map_W, e_hom_map,
    FibreAut.app_naturality, e_inv_map]

/-- **The lift** of an automorphism of `F` to an automorphism of `F'`. -/
noncomputable def lift (γ : FibreAut F) : FibreAut F' :=
  show F' ≅ F' from NatIso.ofComponents
    (fun X' => (Equiv.mk (D.liftApp γ X') (D.liftApp γ⁻¹ X') (D.liftApp_inv γ X') (by
        have := D.liftApp_inv γ⁻¹ X'
        simp only [inv_inv] at this
        exact this)).toIso)
    fun {X' Y'} m => by
      ext x
      exact D.liftApp_natural γ m x

lemma lift_app (γ : FibreAut F) (X' : C') (x : F'.obj X') :
    (D.lift γ).app X' x = D.liftApp γ X' x := rfl

lemma restrict_lift (γ : FibreAut F) : FibreAut.restrict G e (D.lift γ) = γ := by
  ext Y y
  rw [FibreAut.restrict_app, lift_app, liftApp]
  set z := (D.W (G.obj Y)).symm (e.inv.app Y y)
  have hz : y = e.hom.app Y (D.W (G.obj Y) z) := by
    rw [Equiv.apply_symm_apply, Iso.inv_hom_id_app_apply]
  rw [W_apply, ← D.π_e, Iso.inv_hom_id_app_apply, ← FibreAut.app_naturality, D.π_e, ← W_apply,
    ← hz]

theorem surjective_restrict : Function.Surjective (FibreAut.restrict G e) :=
  fun γ => ⟨D.lift γ, D.restrict_lift γ⟩

lemma w_surjective (X' : C') : Function.Surjective (F'.map (D.w X')) :=
  (D.w_bijective X').2

theorem injective_restrict : Function.Injective (FibreAut.restrict G e) :=
  injective_restrict_of_dominated D.S D.w D.w_surjective

theorem bijective_restrict : Function.Bijective (FibreAut.restrict G e) :=
  ⟨D.injective_restrict, D.surjective_restrict⟩

theorem isOpenEmbedding_restrict : Topology.IsOpenEmbedding (FibreAut.restrict G e) := by
  refine ⟨⟨isInducing_restrict_of_dominated D.S D.w D.w_surjective, D.injective_restrict⟩, ?_⟩
  rw [D.surjective_restrict.range_eq]
  exact isOpen_univ

/-- **The restriction is an isomorphism of topological groups.** -/
noncomputable def restrictEquiv : FibreAut F' ≃ₜ* FibreAut F where
  toMulEquiv := MulEquiv.ofBijective (FibreAut.restrict G e) D.bijective_restrict
  continuous_toFun := FibreAut.continuous_restrict G e
  continuous_invFun := by
    change Continuous (Equiv.ofBijective _ D.bijective_restrict).symm
    exact (Equiv.toHomeomorphOfContinuousOpen (Equiv.ofBijective _ D.bijective_restrict)
      (FibreAut.continuous_restrict G e) D.isOpenEmbedding_restrict.isOpenMap).symm.continuous

lemma restrictEquiv_apply (γ : FibreAut F') : D.restrictEquiv γ = FibreAut.restrict G e γ := rfl

end SectionData

end TemperedFundamentalGroups
