/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib

/-!
# The automorphism group of a fibre functor as a topological group

For a functor `F : C ⥤ Type w` (a "fibre functor"), `FibreAut F` is the group `Aut F` of natural
automorphisms of `F`, equipped with the topology of pointwise convergence on the (discrete)
fibres: a basis of neighbourhoods of `1` is given by the pointwise stabilizers of finitely many
fibre elements `(c, x)`, `x ∈ F.obj c`. This is the topology of André's tempered fundamental
group (*Period mappings and differential equations*, III.1–2) and of Grothendieck's étale
fundamental group; it makes `FibreAut F` a (non-archimedean) topological group, Hausdorff.

A functor `G : C' ⥤ C` together with an isomorphism `G ⋙ F ≅ F'` induces a continuous group
homomorphism `FibreAut F →* FibreAut F'` (restriction of automorphisms), `FibreAut.restrict`.

## Main definitions

* `TemperedFundamentalGroups.FibreAut F`: the group `Aut F`, with its topology.
* `FibreAut.stabilizer F S`: the pointwise stabilizer of a finite set of fibre elements.
* `FibreAut.restrict G e`: the continuous homomorphism induced by `G` and `e : G ⋙ F ≅ F'`.
-/

universe w v v' u u'

open CategoryTheory

namespace TemperedFundamentalGroups

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- The automorphism group of a functor `F : C ⥤ Type w`, to be equipped with the topology of
pointwise convergence on the fibres `F.obj c`. -/
def FibreAut : Type (max u w) := Aut F

namespace FibreAut

instance : Group (FibreAut F) := inferInstanceAs (Group (Aut F))

variable {F}

/-- The action of an automorphism on the fibre `F.obj c`. -/
def app (σ : FibreAut F) (c : C) (x : F.obj c) : F.obj c := (show F ≅ F from σ).hom.app c x

@[simp] lemma one_app (c : C) (x : F.obj c) : (1 : FibreAut F).app c x = x := rfl

lemma mul_app (σ τ : FibreAut F) (c : C) (x : F.obj c) :
    (σ * τ).app c x = σ.app c (τ.app c x) := rfl

@[simp] lemma inv_app_app (σ : FibreAut F) (c : C) (x : F.obj c) :
    σ⁻¹.app c (σ.app c x) = x :=
  Iso.hom_inv_id_app_apply (show F ≅ F from σ) c x

@[simp] lemma app_inv_app (σ : FibreAut F) (c : C) (x : F.obj c) :
    σ.app c (σ⁻¹.app c x) = x :=
  Iso.inv_hom_id_app_apply (show F ≅ F from σ) c x

lemma app_naturality (σ : FibreAut F) {c d : C} (f : c ⟶ d) (x : F.obj c) :
    σ.app d (F.map f x) = F.map f (σ.app c x) :=
  NatTrans.naturality_apply (show F ≅ F from σ).hom f x

@[ext] lemma ext {σ τ : FibreAut F} (h : ∀ c x, σ.app c x = τ.app c x) : σ = τ :=
  Aut.ext (NatTrans.ext (funext fun c => ConcreteCategory.hom_ext _ _ fun x => h c x))

variable (F)

/-- The pointwise stabilizer of a finite set `S` of fibre elements. -/
def stabilizer (S : Finset (Σ c : C, F.obj c)) : Subgroup (FibreAut F) where
  carrier := {σ | ∀ p ∈ S, σ.app p.1 p.2 = p.2}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {σ τ} hσ hτ p hp => by
    rw [mul_app, hτ p hp, hσ p hp]
  inv_mem' := fun {σ} hσ p hp => by
    conv_lhs => rw [← hσ p hp]
    exact inv_app_app σ p.1 p.2

variable {F}

lemma mem_stabilizer {S : Finset (Σ c : C, F.obj c)} {σ : FibreAut F} :
    σ ∈ stabilizer F S ↔ ∀ p ∈ S, σ.app p.1 p.2 = p.2 := Iff.rfl

lemma stabilizer_anti {S T : Finset (Σ c : C, F.obj c)} (h : S ⊆ T) :
    stabilizer F T ≤ stabilizer F S :=
  fun _ hσ p hp => hσ p (h hp)

open Classical in
/-- Translating a finite set of fibre elements by an automorphism. -/
noncomputable def translate (τ : FibreAut F) (S : Finset (Σ c : C, F.obj c)) :
    Finset (Σ c : C, F.obj c) :=
  S.image fun p => ⟨p.1, τ.app p.1 p.2⟩

lemma conj_mem_stabilizer {S : Finset (Σ c : C, F.obj c)} (τ : FibreAut F) {σ : FibreAut F}
    (hσ : σ ∈ stabilizer F (translate τ⁻¹ S)) : τ * σ * τ⁻¹ ∈ stabilizer F S := by
  classical
  intro p hp
  have := hσ ⟨p.1, τ⁻¹.app p.1 p.2⟩ (Finset.mem_image.2 ⟨p, hp, rfl⟩)
  simp only at this
  rw [mul_app, mul_app, this, app_inv_app]

variable (F)

/-- The group filter basis of pointwise stabilizers of finite sets of fibre elements. -/
abbrev groupFilterBasis : GroupFilterBasis (FibreAut F) where
  sets := Set.range fun S => (stabilizer F S : Set (FibreAut F))
  nonempty := ⟨_, ⟨∅, rfl⟩⟩
  inter_sets := by
    classical
    rintro _ _ ⟨S, rfl⟩ ⟨T, rfl⟩
    exact ⟨_, ⟨S ∪ T, rfl⟩, fun σ hσ =>
      ⟨stabilizer_anti Finset.subset_union_left hσ,
        stabilizer_anti Finset.subset_union_right hσ⟩⟩
  one' := by
    rintro _ ⟨S, rfl⟩
    exact (stabilizer F S).one_mem
  mul' := by
    rintro _ ⟨S, rfl⟩
    refine ⟨_, ⟨S, rfl⟩, ?_⟩
    rintro _ ⟨σ, hσ, τ, hτ, rfl⟩
    exact (stabilizer F S).mul_mem hσ hτ
  inv' := by
    rintro _ ⟨S, rfl⟩
    exact ⟨_, ⟨S, rfl⟩, fun σ hσ => (stabilizer F S).inv_mem hσ⟩
  conj' := by
    rintro τ _ ⟨S, rfl⟩
    exact ⟨_, ⟨translate τ⁻¹ S, rfl⟩, fun σ hσ => conj_mem_stabilizer τ hσ⟩

instance : TopologicalSpace (FibreAut F) := (groupFilterBasis F).topology

instance : IsTopologicalGroup (FibreAut F) := (groupFilterBasis F).isTopologicalGroup

lemma nhds_one_hasBasis :
    (nhds (1 : FibreAut F)).HasBasis (fun _ => True)
      fun S : Finset (Σ c : C, F.obj c) => (stabilizer F S : Set (FibreAut F)) := by
  have := (groupFilterBasis F).nhds_one_hasBasis
  refine ⟨fun U => ?_⟩
  rw [this.mem_iff]
  constructor
  · rintro ⟨_, ⟨S, rfl⟩, hS⟩
    exact ⟨S, trivial, hS⟩
  · rintro ⟨S, -, hS⟩
    exact ⟨_, ⟨S, rfl⟩, hS⟩

lemma stabilizer_mem_nhds_one (S : Finset (Σ c : C, F.obj c)) :
    (stabilizer F S : Set (FibreAut F)) ∈ nhds (1 : FibreAut F) :=
  (nhds_one_hasBasis F).mem_of_mem trivial

lemma isOpen_stabilizer (S : Finset (Σ c : C, F.obj c)) :
    IsOpen (stabilizer F S : Set (FibreAut F)) :=
  Subgroup.isOpen_of_mem_nhds _ (stabilizer_mem_nhds_one F S)

open Classical in
/-- The stabilizer of a single fibre element is open. -/
lemma isOpen_stabilizer_singleton (c : C) (x : F.obj c) :
    IsOpen {σ : FibreAut F | σ.app c x = x} := by
  have := isOpen_stabilizer F {⟨c, x⟩}
  convert this using 1
  ext σ
  simp [mem_stabilizer]

/-- The evaluation `σ ↦ σ x` on a fibre is locally constant, i.e. continuous for the discrete
topology on the fibre. -/
lemma isOpen_setOf_app_eq (c : C) (x y : F.obj c) :
    IsOpen {σ : FibreAut F | σ.app c x = y} := by
  rw [isOpen_iff_forall_mem_open]
  intro σ hσ
  refine ⟨(σ⁻¹ * ·) ⁻¹' {τ : FibreAut F | τ.app c x = x}, ?_, ?_, ?_⟩
  · intro τ hτ
    simp only [Set.mem_preimage, Set.mem_setOf_eq, mul_app] at hτ hσ ⊢
    calc τ.app c x = σ.app c (σ⁻¹.app c (τ.app c x)) := (app_inv_app σ c _).symm
      _ = y := by rw [hτ, hσ]
  · exact (isOpen_stabilizer_singleton F c x).preimage (continuous_const_mul _)
  · simp

instance : T2Space (FibreAut F) := by
  rw [(groupFilterBasis F).t2Space_iff_sInter_subset]
  · intro σ hσ
    ext c x
    have := hσ _ ⟨{⟨c, x⟩}, rfl⟩
    exact this ⟨c, x⟩ (Finset.mem_singleton_self _)
  · rfl

/-- The pointwise stabilizer of a finite set of fibre elements, as an open subgroup. -/
def openStabilizer (S : Finset (Σ c : C, F.obj c)) : OpenSubgroup (FibreAut F) :=
  ⟨stabilizer F S, isOpen_stabilizer F S⟩

/-- `FibreAut F` is a non-archimedean (prodiscrete) group: open subgroups form a basis of
neighbourhoods of `1`. -/
instance : NonarchimedeanGroup (FibreAut F) where
  is_nonarchimedean U hU := by
    obtain ⟨S, -, hS⟩ := (nhds_one_hasBasis F).mem_iff.1 hU
    exact ⟨openStabilizer F S, hS⟩

/-- A homomorphism into `FibreAut F` is continuous as soon as the preimage of every
pointwise stabilizer is a neighbourhood of `1`. -/
lemma continuous_of_stabilizer {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* FibreAut F)
    (h : ∀ S : Finset (Σ c : C, F.obj c), φ ⁻¹' (stabilizer F S : Set (FibreAut F)) ∈ nhds 1) :
    Continuous φ := by
  refine continuous_of_continuousAt_one φ ?_
  rw [ContinuousAt, map_one, (nhds_one_hasBasis F).tendsto_right_iff]
  exact fun S _ => h S

section Restrict

variable {C' : Type u'} [Category.{v'} C'] {F} {F' : C' ⥤ Type w}

/-- The homomorphism `Aut F → Aut F'` induced by a functor `G : C' ⥤ C` with `G ⋙ F ≅ F'`:
an automorphism of `F` is restricted along `G` and transported along `e`. -/
def restrict (G : C' ⥤ C) (e : G ⋙ F ≅ F') : FibreAut F →* FibreAut F' where
  toFun σ := e.symm ≪≫ Functor.isoWhiskerLeft G (show F ≅ F from σ) ≪≫ e
  map_one' := by
    apply Aut.ext
    ext c x
    exact Iso.inv_hom_id_app_apply e c x
  map_mul' σ τ := by
    apply Aut.ext
    ext c x
    change e.hom.app c ((σ * τ).app (G.obj c) (e.inv.app c x)) =
      e.hom.app c (σ.app (G.obj c) (e.inv.app c (e.hom.app c (τ.app (G.obj c)
        (e.inv.app c x)))))
    rw [Iso.hom_inv_id_app_apply]
    rfl

lemma restrict_app (G : C' ⥤ C) (e : G ⋙ F ≅ F') (σ : FibreAut F) (c : C') (x : F'.obj c) :
    (restrict G e σ).app c x = e.hom.app c (σ.app (G.obj c) (e.inv.app c x)) := rfl

lemma continuous_restrict (G : C' ⥤ C) (e : G ⋙ F ≅ F') : Continuous (restrict G e) := by
  classical
  refine continuous_of_stabilizer _ _ fun S => ?_
  refine Filter.mem_of_superset
    (stabilizer_mem_nhds_one F (S.image fun p => ⟨G.obj p.1, e.inv.app p.1 p.2⟩)) ?_
  intro σ hσ p hp
  have h := hσ ⟨G.obj p.1, e.inv.app p.1 p.2⟩ (Finset.mem_image.2 ⟨p, hp, rfl⟩)
  simp only at h
  rw [restrict_app, h]
  exact Iso.inv_hom_id_app_apply e p.1 p.2

end Restrict

end FibreAut

end TemperedFundamentalGroups

namespace TemperedFundamentalGroups

namespace FibreAut

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- The set of automorphisms taking a prescribed value at a fibre element is clopen. -/
lemma isClopen_setOf_app_eq (c : C) (x y : F.obj c) :
    IsClopen {σ : FibreAut F | σ.app c x = y} := by
  refine ⟨?_, isOpen_setOf_app_eq F c x y⟩
  rw [← isOpen_compl_iff]
  have : {σ : FibreAut F | σ.app c x = y}ᶜ = ⋃ z ∈ {z | z ≠ y}, {σ | σ.app c x = z} := by
    ext σ; simp
  rw [this]
  exact isOpen_biUnion fun z _ => isOpen_setOf_app_eq F c x z

instance : TotallySeparatedSpace (FibreAut F) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro σ τ hστ
  obtain ⟨c, x, h⟩ : ∃ c x, σ.app c x ≠ τ.app c x := by
    by_contra! h
    exact hστ (ext h)
  exact ⟨_, isClopen_setOf_app_eq F c x (σ.app c x), rfl, h.symm⟩

/-- If all fibres are finite, the automorphism group of the fibre functor is compact (it is then
a profinite group). -/
lemma compactSpace_of_finite [∀ c, Finite (F.obj c)] : CompactSpace (FibreAut F) := by
  refine ⟨isCompact_iff_ultrafilter_le_nhds.2 fun 𝒰 _ => ?_⟩
  have key : ∀ (c : C) (x : F.obj c), ∃ y, {τ : FibreAut F | τ.app c x = y} ∈ 𝒰 := by
    intro c x
    obtain ⟨y, hy⟩ := (Ultrafilter.map (fun τ : FibreAut F => τ.app c x) 𝒰).eq_pure_of_finite
    refine ⟨y, ?_⟩
    have : ({y} : Set (F.obj c)) ∈ Ultrafilter.map (fun τ : FibreAut F => τ.app c x) 𝒰 := by
      rw [hy]; exact Filter.mem_pure.2 rfl
    exact this
  have keyInv : ∀ (c : C) (x : F.obj c), ∃ y, {τ : FibreAut F | τ⁻¹.app c x = y} ∈ 𝒰 := by
    intro c x
    obtain ⟨y, hy⟩ := (Ultrafilter.map (fun τ : FibreAut F => τ⁻¹.app c x) 𝒰).eq_pure_of_finite
    refine ⟨y, ?_⟩
    have : ({y} : Set (F.obj c)) ∈ Ultrafilter.map (fun τ : FibreAut F => τ⁻¹.app c x) 𝒰 := by
      rw [hy]; exact Filter.mem_pure.2 rfl
    exact this
  choose y hy using key
  choose y' hy' using keyInv
  have hne : ∀ {s t : Set (FibreAut F)}, s ∈ 𝒰 → t ∈ 𝒰 → (s ∩ t).Nonempty :=
    fun hs ht => Ultrafilter.nonempty_of_mem (Filter.inter_mem hs ht)
  let σ : FibreAut F := show Aut F from
    { hom :=
        { app := fun c => TypeCat.ofHom (y c)
          naturality := fun c d f => by
            ext x
            obtain ⟨τ, h₁, h₂⟩ := hne (hy d (F.map f x)) (hy c x)
            simp only [Set.mem_setOf_eq] at h₁ h₂
            change y d (F.map f x) = F.map f (y c x)
            rw [← h₁, ← h₂, app_naturality] }
      inv :=
        { app := fun c => TypeCat.ofHom (y' c)
          naturality := fun c d f => by
            ext x
            obtain ⟨τ, h₁, h₂⟩ := hne (hy' d (F.map f x)) (hy' c x)
            simp only [Set.mem_setOf_eq] at h₁ h₂
            change y' d (F.map f x) = F.map f (y' c x)
            rw [← h₁, ← h₂, app_naturality] }
      hom_inv_id := by
        ext c x
        obtain ⟨τ, h₁, h₂⟩ := hne (hy c x) (hy' c (y c x))
        simp only [Set.mem_setOf_eq] at h₁ h₂
        change y' c (y c x) = x
        rw [← h₂, ← h₁, inv_app_app]
      inv_hom_id := by
        ext c x
        obtain ⟨τ, h₁, h₂⟩ := hne (hy' c x) (hy c (y' c x))
        simp only [Set.mem_setOf_eq] at h₁ h₂
        change y c (y' c x) = x
        rw [← h₂, ← h₁, app_inv_app] }
  have hσ : ∀ c x, σ.app c x = y c x := fun _ _ => rfl
  refine ⟨σ, Set.mem_univ _, ?_⟩
  intro U hU
  rw [← map_mul_left_nhds_one σ] at hU
  obtain ⟨S, -, hS⟩ := (nhds_one_hasBasis F).mem_iff.1 hU
  have hmem : (⋂ p ∈ S, {τ : FibreAut F | τ.app p.1 p.2 = y p.1 p.2}) ∈ 𝒰 :=
    (Filter.biInter_finset_mem S).2 fun p _ => hy p.1 p.2
  refine Filter.mem_of_superset hmem fun τ hτ => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hτ
  have : σ⁻¹ * τ ∈ stabilizer F S := by
    intro p hp
    rw [mul_app, hτ p hp, ← hσ, inv_app_app]
  have := hS this
  simpa using this

end FibreAut

end TemperedFundamentalGroups
