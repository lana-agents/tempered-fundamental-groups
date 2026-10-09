/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Pi1.Orbifold.FibreAut

/-!
# Automorphism groups of fibre functors along realizations

Let `F : D ⥤ Type w` be a fibre functor and `R : C ⥤ D` a functor with `R ⋙ F ≅ Φ`. We call `R`
a *realization* (`FibreAut.IsRealization`) if

* every object of `D` is isomorphic to some `R c`, and
* every morphism `u : R c ⟶ R c'` is realized *after refinement*: there are `c''` and morphisms
  `m : c'' ⟶ c`, `m' : c'' ⟶ c'` with `R m` an isomorphism and `R m ≫ u = R m'`.

Then restriction `FibreAut F → FibreAut Φ` is an isomorphism of topological groups
(`FibreAut.restrictEquivOfIsRealization`).

This is the formal part of the identification of the tempered fundamental group defined through
integral models with André's tempered fundamental group (Blueprint §4, step 3): the
realization functor sends a level with a model and an equivariant covering space of the special
fibre to the corresponding tempered covering of the analytic space. (That this functor is a
realization is the geometric input, cited in Blueprint §4, steps 1–2.) The same lemma compares
different small presentations of one category of coverings.
-/

universe w v v' u u'

open CategoryTheory Pi1.Orbifold Pi1.Orbifold.FibreAut

namespace TemperedFundamentalGroups

namespace FibreAut

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D] {F : D ⥤ Type w}
  {Φ : C ⥤ Type w}

/-- `R : C ⥤ D` is a *realization*: essentially surjective, and every morphism between
realizations is realized after refinement along a morphism realized as an isomorphism. -/
structure IsRealization (R : C ⥤ D) : Prop where
  /-- Every object is isomorphic to a realization. -/
  essSurj : ∀ d : D, ∃ c : C, Nonempty (R.obj c ≅ d)
  /-- Every morphism between realizations is realized after refinement. -/
  refine : ∀ {c c' : C} (u : R.obj c ⟶ R.obj c'),
    ∃ (c'' : C) (m : c'' ⟶ c) (m' : c'' ⟶ c'), IsIso (R.map m) ∧ R.map m ≫ u = R.map m'

variable (R : C ⥤ D) (e : R ⋙ F ≅ Φ)

/-- The action of an automorphism of `Φ` on `F (R c)`, transported along `e`. -/
def transported (β : FibreAut Φ) (c : C) : F.obj (R.obj c) ≅ F.obj (R.obj c) :=
  e.app c ≪≫ (show Φ ≅ Φ from β).app c ≪≫ (e.app c).symm

lemma transported_hom_apply (β : FibreAut Φ) (c : C) (x : F.obj (R.obj c)) :
    (transported R e β c).hom x = e.inv.app c (β.app c (e.hom.app c x)) := rfl

/-- The transported action is natural for morphisms coming from `C`. -/
lemma transported_naturality (β : FibreAut Φ) {c c' : C} (m : c ⟶ c') (x : F.obj (R.obj c)) :
    (transported R e β c').hom (F.map (R.map m) x) =
      F.map (R.map m) ((transported R e β c).hom x) := by
  rw [transported_hom_apply, transported_hom_apply]
  have h₁ := NatTrans.naturality_apply e.hom m x
  have h₂ := NatTrans.naturality_apply e.inv m (β.app c (e.hom.app c x))
  simp only [Functor.comp_map] at h₁ h₂
  rw [h₁, app_naturality, ← h₂]

variable {R}

/-- Along a realization, the transported action is natural for all morphisms between
realizations. -/
lemma transported_naturality' (hR : IsRealization R) (β : FibreAut Φ) {c c' : C}
    (u : R.obj c ⟶ R.obj c') (x : F.obj (R.obj c)) :
    (transported R e β c').hom (F.map u x) = F.map u ((transported R e β c).hom x) := by
  obtain ⟨c'', m, m', hm, hmu⟩ := hR.refine u
  -- write `x = F (R m) y`
  obtain ⟨y, rfl⟩ : ∃ y, F.map (R.map m) y = x :=
    ⟨F.map (inv (R.map m)) x, by rw [← Functor.map_comp_apply, IsIso.inv_hom_id,
      Functor.map_id_apply]⟩
  rw [← Functor.map_comp_apply, hmu, transported_naturality, transported_naturality,
    ← Functor.map_comp_apply, hmu]

lemma transported_conj (hR : IsRealization R) (β : FibreAut Φ) {c c' : C} {d d' : D}
    (i : R.obj c ≅ d) (i' : R.obj c' ≅ d') (f : d ⟶ d') (x : F.obj d) :
    F.map i'.hom ((transported R e β c').hom (F.map i'.inv (F.map f x))) =
      F.map f (F.map i.hom ((transported R e β c).hom (F.map i.inv x))) := by
  have h := transported_naturality' e hR β (i.hom ≫ f ≫ i'.inv) (F.map i.inv x)
  have h1 : F.map (i.hom ≫ f ≫ i'.inv) (F.map i.inv x) = F.map i'.inv (F.map f x) := by
    rw [← Functor.map_comp_apply]
    simp
  rw [h1] at h
  rw [h, ← Functor.map_comp_apply, ← Functor.map_comp_apply]
  simp

variable (R)

/-- The automorphism of `F` induced by an automorphism of `Φ` along a realization. -/
noncomputable def extend (hR : IsRealization R) (β : FibreAut Φ) : FibreAut F :=
  show F ≅ F from NatIso.ofComponents
    (fun d => (F.mapIso (hR.essSurj d).choose_spec.some).symm ≪≫
      transported R e β (hR.essSurj d).choose ≪≫ F.mapIso (hR.essSurj d).choose_spec.some)
    (fun {d d'} f => by
      ext x
      exact transported_conj e hR β _ _ f x)

lemma extend_app (hR : IsRealization R) (β : FibreAut Φ) (d : D) (x : F.obj d) :
    (extend R e hR β).app d x =
      F.map (hR.essSurj d).choose_spec.some.hom
        ((transported R e β (hR.essSurj d).choose).hom
          (F.map (hR.essSurj d).choose_spec.some.inv x)) := rfl

lemma restrict_extend (hR : IsRealization R) (β : FibreAut Φ) :
    restrict R e (extend R e hR β) = β := by
  ext c x
  rw [restrict_app, extend_app]
  set i := (hR.essSurj (R.obj c)).choose_spec.some
  rw [transported_naturality' e hR β i.inv, ← Functor.map_comp_apply, Iso.inv_hom_id,
    Functor.map_id_apply, transported_hom_apply]
  simp only [Iso.inv_hom_id_app_apply]

lemma restrict_injective (hR : IsRealization R) : Function.Injective (restrict R e) := by
  intro α β h
  ext d x
  obtain ⟨c, ⟨i⟩⟩ := hR.essSurj d
  have hc : ∀ y, α.app (R.obj c) y = β.app (R.obj c) y := by
    intro y
    have := congrArg (fun σ : FibreAut Φ => σ.app c (e.hom.app c y)) h
    simp only [restrict_app, Iso.hom_inv_id_app_apply] at this
    have := congrArg (e.inv.app c) this
    simpa only [Iso.hom_inv_id_app_apply] using this
  obtain ⟨y, rfl⟩ : ∃ y, F.map i.hom y = x :=
    ⟨F.map i.inv x, by rw [← Functor.map_comp_apply, Iso.inv_hom_id, Functor.map_id_apply]⟩
  rw [app_naturality, app_naturality, hc]

lemma restrict_bijective_of_isRealization (hR : IsRealization R) :
    Function.Bijective (restrict R e) :=
  ⟨restrict_injective R e hR, fun β => ⟨extend R e hR β, restrict_extend R e hR β⟩⟩

/-- **Restriction along a realization is an isomorphism of topological groups.** -/
noncomputable def restrictEquivOfIsRealization (hR : IsRealization R) :
    FibreAut F ≃ₜ* FibreAut Φ where
  toMulEquiv := MulEquiv.ofBijective (restrict R e) (restrict_bijective_of_isRealization R e hR)
  continuous_toFun := continuous_restrict R e
  continuous_invFun := by
    classical
    let ψ : FibreAut Φ →* FibreAut F :=
      (MulEquiv.ofBijective (restrict R e) (restrict_bijective_of_isRealization R e hR)).symm
    refine continuous_of_stabilizer F ψ fun S => ?_
    -- the stabilizer of the transported finite set is sent into the stabilizer of `S`
    let T : Finset (Σ c : C, Φ.obj c) := S.image fun p =>
      ⟨(hR.essSurj p.1).choose,
        e.hom.app _ (F.map (hR.essSurj p.1).choose_spec.some.inv p.2)⟩
    refine Filter.mem_of_superset (stabilizer_mem_nhds_one Φ T) fun β hβ p hp => ?_
    set c := (hR.essSurj p.1).choose
    set i := (hR.essSurj p.1).choose_spec.some
    have hT := hβ ⟨c, e.hom.app _ (F.map i.inv p.2)⟩ (Finset.mem_image.2 ⟨p, hp, rfl⟩)
    simp only at hT
    have hψ : restrict R e (ψ β) = β :=
      (MulEquiv.ofBijective (restrict R e) _).apply_symm_apply β
    have key : (ψ β).app (R.obj c) (F.map i.inv p.2) = F.map i.inv p.2 := by
      have := congrArg (fun σ : FibreAut Φ => σ.app c (e.hom.app c (F.map i.inv p.2))) hψ
      simp only [restrict_app, Iso.hom_inv_id_app_apply] at this
      rw [hT] at this
      have := congrArg (e.inv.app c) this
      simpa only [Iso.hom_inv_id_app_apply] using this
    change (ψ β).app p.1 p.2 = p.2
    have := app_naturality (ψ β) i.hom (F.map i.inv p.2)
    rw [key, ← Functor.map_comp_apply, Iso.inv_hom_id, Functor.map_id_apply] at this
    exact this

@[simp] lemma restrictEquivOfIsRealization_apply (hR : IsRealization R) (σ : FibreAut F) :
    restrictEquivOfIsRealization R e hR σ = restrict R e σ := rfl

/-- An essentially surjective, full functor is a realization. -/
lemma isRealization_of_full (R : C ⥤ D) [R.EssSurj] [R.Full] : IsRealization R where
  essSurj d := ⟨R.objPreimage d, ⟨R.objObjPreimageIso d⟩⟩
  refine {c c'} u := ⟨c, 𝟙 c, R.preimage u, by rw [CategoryTheory.Functor.map_id]; infer_instance,
    by simp⟩

end FibreAut

end TemperedFundamentalGroups
