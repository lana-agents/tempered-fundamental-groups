/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.CentreMap
import TemperedFundamentalGroups.SemistableReduction.WModelGerm

/-!
# The base of a model seen from a point (Blueprint §10.3.8, CrossingX1, CX1)

For a model `c` over `R` and `g : Spec F ⟶ c`, `baseHom c g : R → F` is the image of the
structure map (global sections). It lands in all germs, `g ≫ c.toSpec = Spec(baseHom)`
(`toSpec_comp`), uniformizers are in the maximal ideal of valuations centred in the special fibre
(`valuation_baseHom_lt_one`), and for W-models `baseHom` is the algebra map (`baseHom_eq`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace TemperedFundamentalGroups.SemistableReduction.CentreGerms

open ValuativeCentre

variable {F : Type u} [Field F]

/-- The image of `g` specializes to the centre. -/
lemma IsCentre.specializes {X : Scheme.{u}} {g : Spec (CommRingCat.of F) ⟶ X}
    {V : ValuationSubring F} {x : X} (hc : IsCentre g V x) : g (closedPoint F) ⤳ x := by
  obtain ⟨l, hl, rfl⟩ := hc
  rw [← hl, Scheme.Hom.comp_apply]
  exact (IsLocalRing.specializes_closedPoint _).map l.continuous

variable {R : Type u} [CommRing R]

lemma top_le_preimage_top {X : Scheme.{u}} (g : Spec (CommRingCat.of F) ⟶ X) :
    ⊤ ≤ g ⁻¹ᵁ (⊤ : X.Opens) :=
  fun _ _ ↦ trivial

/-- The base `R → F` seen from `g`. -/
noncomputable def baseHom (c : TemperedFundamentalGroups.ModelCode R)
    (g : Spec (CommRingCat.of F) ⟶ c.scheme) : R →+* F :=
  letI := ModelCode.sectionsAlgebra c ⊤
  (ModelCode.toLHom g (top_le_preimage_top g)).comp (algebraMap R Γ(c.scheme, ⊤))

lemma baseHom_mem_germs (c : TemperedFundamentalGroups.ModelCode R)
    (g : Spec (CommRingCat.of F) ⟶ c.scheme) (x : c.scheme) (r : R) :
    baseHom c g r ∈ ModelCode.germs c g x :=
  letI := ModelCode.sectionsAlgebra c ⊤
  ⟨⊤, trivial, top_le_preimage_top g, algebraMap R Γ(c.scheme, ⊤) r, rfl⟩

/-- `baseHom` through any open. -/
lemma baseHom_eq_toL (c : TemperedFundamentalGroups.ModelCode R)
    (g : Spec (CommRingCat.of F) ⟶ c.scheme) {U : c.scheme.Opens} (hU : ⊤ ≤ g ⁻¹ᵁ U) (r : R) :
    letI := ModelCode.sectionsAlgebra c U
    baseHom c g r = ModelCode.toL g hU (algebraMap R Γ(c.scheme, U) r) := by
  letI := ModelCode.sectionsAlgebra c U
  letI := ModelCode.sectionsAlgebra c ⊤
  have e : algebraMap R Γ(c.scheme, U) r =
      (c.scheme.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
        (algebraMap R Γ(c.scheme, ⊤) r) := by
    change ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.toSpec.appTop ≫
      c.scheme.presheaf.map (homOfLE le_top).op).hom r =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ c.toSpec.appTop ≫
        c.scheme.presheaf.map (homOfLE le_top).op ≫
        c.scheme.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom r
    rw [← Functor.map_comp]
    rfl
  rw [e, ModelCode.toL_res g le_top hU (top_le_preimage_top g)]
  rfl

/-- **The structure map through `g`.** -/
theorem toSpec_comp (c : TemperedFundamentalGroups.ModelCode R)
    (g : Spec (CommRingCat.of F) ⟶ c.scheme) :
    g ≫ c.toSpec = Spec.map (CommRingCat.ofHom (baseHom c g)) := by
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso (CommRingCat.of F)).hom, Scheme.ΓSpecIso_naturality,
    ← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv, Iso.inv_hom_id_assoc]
  ext r
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
    CommRingCat.hom_ofHom]
  change _ = ModelCode.toL g (top_le_preimage_top g) _
  rw [ModelCode.toL]
  congr 1
  simp [Scheme.Hom.appLE, Scheme.Hom.appTop, RingHom.algebraMap_toAlgebra]

/-- **Uniformizers at points of the special fibre.** -/
theorem valuation_baseHom_lt_one {O : Type u} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ)
    (c : TemperedFundamentalGroups.ModelCode O) (g : Spec (CommRingCat.of F) ⟶ c.scheme)
    {x : c.scheme} (hx : x ∈ ModelCode.Z c) {V : ValuationSubring F} (hV : IsCentre g V x) :
    V.valuation (baseHom c g ϖ) < 1 := by
  have h := IsCentre.specializes hV
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    c.scheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  letI := ModelCode.sectionsAlgebra c U
  have hmem := (ModelCode.mem_Z_iff hϖ hU hxU).1 hx
  rw [ModelCode.mem_primeIdealOf_iff, Scheme.mem_basicOpen (hx := hxU)] at hmem
  have hloc := ((isCentre_iff g h V).1 hV).2 _ hmem
  rwa [stalkTo_germ, ← ModelCode.toL, ← baseHom_eq_toL] at hloc

end TemperedFundamentalGroups.SemistableReduction.CentreGerms
