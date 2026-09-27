/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# Special fibre and specialization of geometric points

Let `O` be a local ring and `f : X ⟶ Spec O`. The *special fibre* of `f` is the preimage of the
closed point of `Spec O` (as a subspace of the underlying space of `X`).

Now let `O ⊆ K` be a valuation subring, `K → Ω` a field extension and `V ⊆ Ω` a valuation
subring with `V ∩ K = O`. For `f` universally closed and separated, every `Ω`-point
`x : Spec Ω ⟶ X` over `Spec K → Spec O` extends uniquely to `Spec V ⟶ X` (valuative criterion);
its value at the closed point of `Spec V` is the *specialization* `sp f V hV x hx` of `x`, a point
of the special fibre. Specialization is natural in morphisms over `Spec O`.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups

section SpecialFibre

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The special fibre of `f : X ⟶ Spec R` for a local ring `R`: the preimage of the closed point,
as a set of points of `X`. -/
def specialFibre {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Set X :=
  f ⁻¹' {(closedPoint R : PrimeSpectrum R)}

lemma mem_specialFibre {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    x ∈ specialFibre f ↔ f x = (closedPoint R : PrimeSpectrum R) :=
  Iff.rfl

variable {X X' X'' : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
  {f' : X' ⟶ Spec (CommRingCat.of R)} {f'' : X'' ⟶ Spec (CommRingCat.of R)}

lemma mem_specialFibre_of_comp (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) {x : X}
    (hx : x ∈ specialFibre f) : ψ x ∈ specialFibre f' := by
  rw [mem_specialFibre, ← Scheme.Hom.comp_apply, hψ]
  exact hx

/-- A morphism `ψ : X ⟶ X'` over `Spec R` maps the special fibre of `X` into that of `X'`. -/
def specialFibreMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) : specialFibre f → specialFibre f' :=
  fun x ↦ ⟨ψ x.1, mem_specialFibre_of_comp ψ hψ x.2⟩

@[simp]
lemma coe_specialFibreMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) (x : specialFibre f) :
    (specialFibreMap ψ hψ x : X') = ψ x :=
  rfl

@[fun_prop]
lemma continuous_specialFibreMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) :
    Continuous (specialFibreMap ψ hψ) :=
  (ψ.continuous.comp continuous_subtype_val).subtype_mk _

@[simp]
lemma specialFibreMap_id (x : specialFibre f) :
    specialFibreMap (𝟙 X) (Category.id_comp f) x = x :=
  rfl

lemma specialFibreMap_comp (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) (φ : X' ⟶ X'') (hφ : φ ≫ f'' = f')
    (x : specialFibre f) :
    specialFibreMap (ψ ≫ φ) (by rw [Category.assoc, hφ, hψ]) x =
      specialFibreMap φ hφ (specialFibreMap ψ hψ x) :=
  rfl

/-- The map of special fibres induced by a morphism over `Spec R`, as a continuous map. -/
def specialFibreContinuousMap (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) :
    C(specialFibre f, specialFibre f') :=
  ⟨specialFibreMap ψ hψ, continuous_specialFibreMap ψ hψ⟩

/-- An isomorphism over `Spec R` induces a homeomorphism of special fibres. In particular an
automorphism `e : X ≅ X` with `e.hom ≫ f = f` acts on the special fibre of `f`. -/
def specialFibreHomeomorph (e : X ≅ X') (he : e.hom ≫ f' = f) :
    specialFibre f ≃ₜ specialFibre f' where
  toFun := specialFibreMap e.hom he
  invFun := specialFibreMap e.inv (by rw [← he, e.inv_hom_id_assoc])
  left_inv x := by
    ext
    simp [← Scheme.Hom.comp_apply]
  right_inv x := by
    ext
    simp [← Scheme.Hom.comp_apply]
  continuous_toFun := continuous_specialFibreMap _ _
  continuous_invFun := continuous_specialFibreMap _ _

@[simp]
lemma coe_specialFibreHomeomorph (e : X ≅ X') (he : e.hom ≫ f' = f) (x : specialFibre f) :
    (specialFibreHomeomorph e he x : X') = e.hom x :=
  rfl

end SpecialFibre

section Specialization

variable {K : Type u} [Field K] (O : ValuationSubring K)
variable {Ω : Type u} [Field Ω] [Algebra K Ω] (V : ValuationSubring Ω)
  (hV : V.comap (algebraMap K Ω) = O)

/-- The inclusion `O → Ω` (restriction of `K → Ω`). -/
def valToField : O →+* Ω :=
  (algebraMap K Ω).comp O.subtype

variable {O V} in
lemma valToField_mem (a : O) : valToField O a ∈ V ↔ (a : K) ∈ V.comap (algebraMap K Ω) :=
  (ValuationSubring.mem_comap).symm

include hV in
/-- The local homomorphism `O → V` induced by `K → Ω`, when `V ∩ K = O`. -/
def valToVal : O →+* V :=
  (valToField O).codRestrict V.toSubring fun a ↦ by
    change _ ∈ V
    rw [valToField_mem, hV]
    exact a.2

@[simp]
lemma coe_valToVal (a : O) : (valToVal O V hV a : Ω) = valToField O a :=
  rfl

lemma valToVal_comp_algebraMap :
    (algebraMap V Ω).comp (valToVal O V hV) = valToField O :=
  rfl

instance isLocalHom_valToVal : IsLocalHom (valToVal O V hV) := by
  refine ⟨fun a ha ↦ ?_⟩
  obtain ⟨u, hu⟩ := ha.exists_left_inv
  have hu' : (u : Ω) * algebraMap K Ω a = 1 := congrArg Subtype.val hu
  have ha0 : (a : K) ≠ 0 := by
    rintro h
    simp [h] at hu'
  have hinv : (u : Ω) = algebraMap K Ω (a : K)⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_left hu'
  have hmem : (a : K)⁻¹ ∈ V.comap (algebraMap K Ω) := by
    rw [ValuationSubring.mem_comap, ← hinv]
    exact u.2
  rw [hV] at hmem
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩

lemma valToVal_closedPoint :
    PrimeSpectrum.comap (valToVal O V hV) (closedPoint V) = closedPoint O :=
  comap_closedPoint _

variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O))

/-- The valuative square attached to an `Ω`-point `x` of `X` over `Spec K → Spec O`. -/
noncomputable def spSquare (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) : ValuativeCommSq f where
  R := V
  K := Ω
  i₁ := x
  i₂ := Spec.map (CommRingCat.ofHom (valToVal O V hV))
  commSq := ⟨by
    rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, valToVal_comp_algebraMap]⟩

variable {O V hV f}

/-- The lift `Spec V ⟶ X` of an `Ω`-point given by the valuative criterion. -/
noncomputable def spLift [UniversallyClosed f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    (spSquare O V hV f x hx).commSq.LiftStruct :=
  have hf : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f)).1
  (hf (spSquare O V hV f x hx)).exists_lift.some

lemma spLift_fac_left [UniversallyClosed f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ (spLift (hV := hV) x hx).l = x :=
  (spLift x hx).fac_left

lemma spLift_fac_right [UniversallyClosed f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    (spLift (hV := hV) x hx).l ≫ f = Spec.map (CommRingCat.ofHom (valToVal O V hV)) :=
  (spLift x hx).fac_right

lemma spLift_unique [UniversallyClosed f] [IsSeparated f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O)))
    (ℓ : Spec (CommRingCat.of V) ⟶ X)
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ ℓ = x)
    (h₂ : ℓ ≫ f = Spec.map (CommRingCat.ofHom (valToVal O V hV))) :
    ℓ = (spLift (hV := hV) x hx).l := by
  have := IsSeparated.valuativeCriterion f (spSquare O V hV f x hx)
  exact congrArg CommSq.LiftStruct.l (Subsingleton.elim (⟨ℓ, h₁, h₂⟩ :
    (spSquare O V hV f x hx).commSq.LiftStruct) _)

lemma spLift_closedPoint_mem [UniversallyClosed f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    (spLift (hV := hV) x hx).l (closedPoint V) ∈ specialFibre f := by
  rw [mem_specialFibre, ← Scheme.Hom.comp_apply, spLift_fac_right]
  exact valToVal_closedPoint O V hV

end Specialization

section Specialization

variable {K : Type u} [Field K] {O : ValuationSubring K}
variable {Ω : Type u} [Field Ω] [Algebra K Ω] {V : ValuationSubring Ω}
  {hV : V.comap (algebraMap K Ω) = O} {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of O)}

/-- The specialization of an `Ω`-point `x` of `X` over `Spec K → Spec O`: the image of the closed
point of `Spec V` under the unique lift `Spec V ⟶ X` given by the valuative criterion. -/
noncomputable def sp {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O)) [UniversallyClosed f]
    [IsSeparated f] (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
    (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) : specialFibre f :=
  ⟨(spLift (hV := hV) x hx).l (closedPoint V), spLift_closedPoint_mem x hx⟩

/-- Characterization of the specialization by any lift `Spec V ⟶ X`. -/
lemma sp_eq_of_lift [UniversallyClosed f] [IsSeparated f] (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O)))
    (ℓ : Spec (CommRingCat.of V) ⟶ X)
    (h₁ : Spec.map (CommRingCat.ofHom (algebraMap V Ω)) ≫ ℓ = x)
    (h₂ : ℓ ≫ f = Spec.map (CommRingCat.ofHom (valToVal O V hV))) :
    (sp f V hV x hx : X) = ℓ (closedPoint V) := by
  rw [spLift_unique x hx ℓ h₁ h₂]
  rfl

/-- Naturality of specialization for morphisms over `Spec O`. -/
lemma sp_comp {X' : Scheme.{u}} {f' : X' ⟶ Spec (CommRingCat.of O)}
    [UniversallyClosed f] [IsSeparated f] [UniversallyClosed f'] [IsSeparated f']
    (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    sp f' V hV (x ≫ ψ) (by rw [Category.assoc, hψ, hx]) =
      specialFibreMap ψ hψ (sp f V hV x hx) := by
  ext
  rw [sp_eq_of_lift (x ≫ ψ) _ ((spLift (hV := hV) x hx).l ≫ ψ)
    (by rw [← Category.assoc, spLift_fac_left])
    (by rw [Category.assoc, hψ]; exact spLift_fac_right x hx)]
  rfl

lemma coe_sp_comp {X' : Scheme.{u}} {f' : X' ⟶ Spec (CommRingCat.of O)}
    [UniversallyClosed f] [IsSeparated f] [UniversallyClosed f'] [IsSeparated f']
    (ψ : X ⟶ X') (hψ : ψ ≫ f' = f) (x : Spec (CommRingCat.of Ω) ⟶ X)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    (sp f' V hV (x ≫ ψ) (by rw [Category.assoc, hψ, hx]) : X') = ψ (sp f V hV x hx) := by
  rw [sp_comp ψ hψ]
  rfl

end Specialization

end TemperedFundamentalGroups
