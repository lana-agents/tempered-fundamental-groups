/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.FibreFunctor.PushRestrict

/-!
# Restriction along a base change with a partial push and a counit span (Blueprint §11, F7′)

A variant of `PushData` (`FibreFunctor/PushRestrict.lean`) for orbifold covers: the push `P` is
only defined on the *good* objects of `C'` (a property `good'`; objects which are not good have
empty fibres), it need not be a functor (only `ι` and `τ` have to be natural), and the counit is
replaced by a span `P (G Y) ⟵ W ⟶ Y` whose first leg hits the image of `ι` exactly over `ι`:

* `π_surj`: every `ι z` is the image of some `w ∈ F W` under `F π₁`;
* `π_ι`: if `F π₁ w = ι z`, then `F π₂ w = e z`.

Then `FibreAut.restrict G e` is injective with image the stabilizer of `x₀`
(`SpanPushData.injective_restrict`, `SpanPushData.range_restrict`), an open embedding, and its
image has finite index if `F E` is finite.
-/

universe w v v' u u'

open CategoryTheory Pi1.Orbifold

namespace TemperedFundamentalGroups

variable {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ Type w}
  {F' : C' ⥤ Type w} {G : C ⥤ C'} {e : G ⋙ F' ≅ F}

/-- **Span push data** for a base change `G` with `e : G ⋙ F' ≅ F` (see the module docstring). -/
structure SpanPushData (G : C ⥤ C') (e : G ⋙ F' ≅ F) where
  /-- The good objects. -/
  good : C' → Prop
  empty : ∀ X', ¬ good X' → IsEmpty (F'.obj X')
  /-- The push of a good object. -/
  P : ∀ X', good X' → C
  /-- The push of a morphism of good objects. -/
  Pmap : ∀ {X' Y'} (hX : good X') (hY : good Y'), (X' ⟶ Y') → (P X' hX ⟶ P Y' hY)
  /-- The fibre injections. -/
  ι : ∀ X' (hX : good X'), F'.obj X' → F.obj (P X' hX)
  ι_injective : ∀ X' hX, Function.Injective (ι X' hX)
  ι_natural : ∀ {X' Y'} (hX : good X') (hY : good Y') (m : X' ⟶ Y') (x : F'.obj X'),
    ι Y' hY (F'.map m x) = F.map (Pmap hX hY m) (ι X' hX x)
  /-- The cover, as an object of `C`. -/
  E : C
  /-- Its base point. -/
  x₀ : F.obj E
  /-- The structure morphisms to the cover. -/
  τ : ∀ X' (hX : good X'), P X' hX ⟶ E
  τ_natural : ∀ {X' Y'} (hX : good X') (hY : good Y') (m : X' ⟶ Y'),
    Pmap hX hY m ≫ τ Y' hY = τ X' hX
  range_ι : ∀ X' hX (y : F.obj (P X' hX)), (∃ x, ι X' hX x = y) ↔ F.map (τ X' hX) y = x₀
  /-- The unit. -/
  u : ∀ X' (hX : good X'), X' ⟶ G.obj (P X' hX)
  u_ι : ∀ X' hX (x : F'.obj X'), e.hom.app (P X' hX) (F'.map (u X' hX) x) = ι X' hX x
  /-- The apex of the counit span. -/
  W : ∀ Y, good (G.obj Y) → C
  π₁ : ∀ Y (hY : good (G.obj Y)), W Y hY ⟶ P (G.obj Y) hY
  π₂ : ∀ Y (hY : good (G.obj Y)), W Y hY ⟶ Y
  π_surj : ∀ Y hY (z : F'.obj (G.obj Y)), ∃ w, F.map (π₁ Y hY) w = ι _ hY z
  π_ι : ∀ Y hY (z : F'.obj (G.obj Y)) (w : F.obj (W Y hY)),
    F.map (π₁ Y hY) w = ι _ hY z → F.map (π₂ Y hY) w = e.hom.app Y z

namespace SpanPushData

variable (D : SpanPushData G e)

lemma good_of_mem {X' : C'} (x : F'.obj X') : D.good X' := by
  by_contra h
  exact (D.empty X' h).false x

lemma restrict_app_ι (γ : FibreAut F') (X' : C') (hX : D.good X') (x : F'.obj X') :
    (FibreAut.restrict G e γ).app (D.P X' hX) (D.ι X' hX x) = D.ι X' hX (γ.app X' x) := by
  have h : e.inv.app (D.P X' hX) (D.ι X' hX x) = F'.map (D.u X' hX) x := by
    rw [← D.u_ι]
    exact Iso.hom_inv_id_app_apply e _ _
  rw [FibreAut.restrict_app, h]
  change e.hom.app _ (γ.app (G.obj (D.P X' hX)) (F'.map (D.u X' hX) x)) = _
  rw [FibreAut.app_naturality, D.u_ι]

include D in
theorem injective_restrict : Function.Injective (FibreAut.restrict G e) := by
  rw [injective_iff_map_eq_one]
  intro γ hγ
  ext X' x
  have hX := D.good_of_mem x
  apply D.ι_injective X' hX
  rw [FibreAut.one_app, ← restrict_app_ι D, hγ, FibreAut.one_app]

/-- The pointwise stabilizer of the base point `x₀ ∈ F E`. -/
def stab : Subgroup (FibreAut F) where
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
  let x : F'.obj (G.obj D.E) := e.inv.app D.E D.x₀
  have hX : D.good (G.obj D.E) := D.good_of_mem x
  have hx : ∀ x : F'.obj (G.obj D.E), F.map (D.τ _ hX) (D.ι _ hX x) = D.x₀ :=
    fun x => (D.range_ι _ hX _).1 ⟨x, rfl⟩
  rw [mem_stab]
  calc (FibreAut.restrict G e γ).app D.E D.x₀
      = (FibreAut.restrict G e γ).app D.E (F.map (D.τ _ hX) (D.ι _ hX x)) := by rw [hx x]
    _ = F.map (D.τ _ hX) ((FibreAut.restrict G e γ).app _ (D.ι _ hX x)) :=
        FibreAut.app_naturality _ _ _
    _ = D.x₀ := by rw [restrict_app_ι, hx]

lemma exists_ι (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (hX : D.good X')
    (x : F'.obj X') : ∃ x', D.ι X' hX x' = γ.app (D.P X' hX) (D.ι X' hX x) :=
  (D.range_ι X' hX _).2 (by
    rw [← FibreAut.app_naturality, (D.range_ι X' hX _).1 ⟨x, rfl⟩]
    exact hγ)

/-- The lift of an automorphism fixing `x₀`, on a fibre element. -/
noncomputable def liftApp (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (x : F'.obj X') :
    F'.obj X' :=
  (D.exists_ι γ hγ X' (D.good_of_mem x) x).choose

lemma ι_liftApp (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (hX : D.good X') (x : F'.obj X') :
    D.ι X' hX (D.liftApp γ hγ X' x) = γ.app (D.P X' hX) (D.ι X' hX x) :=
  (D.exists_ι γ hγ X' (D.good_of_mem x) x).choose_spec

lemma liftApp_inv (γ : FibreAut F) (hγ : γ ∈ D.stab) (X' : C') (x : F'.obj X') :
    D.liftApp γ⁻¹ (D.stab.inv_mem hγ) X' (D.liftApp γ hγ X' x) = x := by
  have hX := D.good_of_mem x
  apply D.ι_injective X' hX
  rw [ι_liftApp _ _ _ _ hX, ι_liftApp _ _ _ _ hX, FibreAut.inv_app_app]

lemma liftApp_natural (γ : FibreAut F) (hγ : γ ∈ D.stab) {X' Y' : C'} (m : X' ⟶ Y')
    (x : F'.obj X') : D.liftApp γ hγ Y' (F'.map m x) = F'.map m (D.liftApp γ hγ X' x) := by
  have hX := D.good_of_mem x
  have hY := D.good_of_mem (F'.map m x)
  apply D.ι_injective Y' hY
  rw [ι_liftApp _ _ _ _ hY, D.ι_natural hX hY, D.ι_natural hX hY, ι_liftApp _ _ _ _ hX,
    FibreAut.app_naturality]

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
  have hy : y = e.hom.app Y z := (Iso.inv_hom_id_app_apply e Y y).symm
  have hY : D.good (G.obj Y) := D.good_of_mem z
  obtain ⟨w, hw⟩ := D.π_surj Y hY z
  have h₁ : F.map (D.π₁ Y hY) (γ.app _ w) = D.ι _ hY (D.liftApp γ hγ _ z) := by
    rw [← FibreAut.app_naturality, hw, ι_liftApp _ _ _ _ hY]
  rw [← D.π_ι Y hY _ _ h₁, ← FibreAut.app_naturality, D.π_ι Y hY z w hw, hy]

theorem range_restrict : (FibreAut.restrict G e).range = D.stab := by
  ext γ
  constructor
  · rintro ⟨γ', rfl⟩
    exact D.restrict_mem_stab γ'
  · intro hγ
    exact ⟨D.lift γ hγ, D.restrict_lift γ hγ⟩

/-- The action of `Aut F` on the fibre `F E`. -/
@[reducible] noncomputable def fibreAction : MulAction (FibreAut F) (F.obj D.E) where
  smul γ x := γ.app D.E x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma stab_eq : D.stab = @MulAction.stabilizer _ _ _ D.fibreAction D.x₀ := rfl

theorem finiteIndex_range_restrict [Finite (F.obj D.E)] :
    (FibreAut.restrict G e).range.FiniteIndex := by
  letI := D.fibreAction
  rw [D.range_restrict, D.stab_eq]
  refine ⟨?_⟩
  rw [MulAction.index_stabilizer]
  exact Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self D.x₀) (Set.toFinite _)

include D in
theorem isInducing_restrict : Topology.IsInducing (FibreAut.restrict G e) := by
  classical
  rw [IsTopologicalGroup.isInducing_iff_nhds_one]
  refine le_antisymm ((FibreAut.continuous_restrict G e).tendsto' 1 1 (map_one _)).le_comap ?_
  rw [((FibreAut.nhds_one_hasBasis F).comap _).le_basis_iff (FibreAut.nhds_one_hasBasis F')]
  intro S _
  refine ⟨S.image (fun p => (⟨D.P p.1 (D.good_of_mem p.2), D.ι p.1 (D.good_of_mem p.2) p.2⟩ :
    Σ c : C, F.obj c)), trivial, fun γ hγ p hp => ?_⟩
  have := hγ _ (Finset.mem_image_of_mem _ hp)
  have hX := D.good_of_mem p.2
  apply D.ι_injective p.1 hX
  rw [← restrict_app_ι D γ p.1 hX]
  exact this

include D in
/-- **`FibreAut.restrict G e` is an open embedding** onto the stabilizer of `x₀`. -/
theorem isOpenEmbedding_restrict : Topology.IsOpenEmbedding (FibreAut.restrict G e) := by
  refine ⟨⟨D.isInducing_restrict, D.injective_restrict⟩, ?_⟩
  have : Set.range (FibreAut.restrict G e) = (D.stab : Set (FibreAut F)) := by
    rw [← D.range_restrict, MonoidHom.coe_range]
  rw [this]
  exact D.isOpen_stab

end SpanPushData

end TemperedFundamentalGroups
