/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.FracGalois
import TemperedFundamentalGroups.Andre.ValuativeCentre
import TemperedFundamentalGroups.Tempered.Category

/-!
# G-transitivity: auxiliary results (Blueprint §10.3.8, I4)

* `image_eq_closure`, `image_mem_irreducibleComponents`: images of irreducible components under
  closed maps (to a space of dimension `≤ 1`, if not contracted);
* `isClosedMap_specialFibreMap'`: model maps over `O` are closed on special fibres;
* `Level.gen`: the generic point `Spec L ⟶ 𝒯` of the model of a level (`L` a fraction field of
  `B`); `Level.gen_specializes`: if `j` is scheme-theoretically dominant and `B` a domain, every
  point of the model is a specialization of it;
* `Level.isCentre_comap` (**restriction of centres**): along a model map `ψ` over a level map
  `φ : B₀ → B`, a valuation subring `W` of `L = Frac B` with centre `x` restricts to a valuation
  subring of `F₀ = Frac B₀` with centre `ψ x` (valuative criteria for the proper model of `B₀`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Set Topology TopologicalSpace

namespace TemperedFundamentalGroups

noncomputable section

section Topology

variable {Z Z' : Type u} [TopologicalSpace Z] [TopologicalSpace Z']

/-- The image of the closure of a point under a continuous closed map. -/
lemma image_eq_closure {f : Z → Z'} (hf : Continuous f) (hfc : IsClosedMap f) {v : Set Z}
    {η : Z} (hη : closure {η} = v) : f '' v = closure {f η} := by
  rw [← hη]
  refine subset_antisymm ((image_closure_subset_closure_image hf).trans (by rw [image_singleton]))
    ?_
  exact (hfc _ isClosed_closure).closure_subset_iff.2
    (singleton_subset_iff.2 ⟨η, subset_closure rfl, rfl⟩)

/-- **A non-contracted component is mapped onto a component** by a continuous closed map to a
`T₀` quasi-sober noetherian space of dimension `≤ 1`. -/
lemma image_mem_irreducibleComponents [NoetherianSpace Z'] [T0Space Z'] [QuasiSober Z']
    (hdim' : topologicalKrullDim Z' ≤ 1) {f : Z → Z'} (hf : Continuous f) (hfc : IsClosedMap f)
    {v : Set Z} {η : Z} (hη : closure {η} = v) (hc : ¬ ∃ y, f '' v = {y}) :
    f '' v ∈ irreducibleComponents Z' := by
  have himg := image_eq_closure hf hfc hη
  have hirr : IsIrreducible (f '' v) := by
    rw [himg]
    exact isIrreducible_singleton.closure
  have hcl' : IsClosed (f '' v) := by rw [himg]; exact isClosed_closure
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ hirr
  have heq : f '' v = C := by
    by_contra hne
    have hz : ∃ z ∈ f '' v, z ≠ f η := by
      by_contra h
      push Not at h
      refine hc ⟨f η, subset_antisymm (fun z hz => h z hz) ?_⟩
      rw [himg]
      exact singleton_subset_iff.2 (subset_closure rfl)
    obtain ⟨z, hz, hzη⟩ := hz
    let A : IrreducibleCloseds Z' := ⟨closure {z}, isIrreducible_singleton.closure,
      isClosed_closure⟩
    let B : IrreducibleCloseds Z' := ⟨f '' v, hirr, hcl'⟩
    let C' : IrreducibleCloseds Z' := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
    have hAB : A < B := by
      refine lt_of_le_of_ne (show closure {z} ⊆ f '' v from
        hcl'.closure_subset_iff.2 (singleton_subset_iff.2 hz)) fun h => hzη ?_
      have h' : closure {z} = closure {f η} := (congrArg SetLike.coe h).trans himg
      exact (inseparable_iff_closure_eq.2 h').eq
    have hBC : B < C' := lt_of_le_of_ne hsub fun h => hne (congrArg SetLike.coe h)
    exact not_lt_lt_of_topologicalKrullDim_le_one hdim' hAB hBC
  rw [heq]
  exact hC

end Topology

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- Model maps over `O` are closed on special fibres (the models are proper over `O`). -/
lemma isClosedMap_specialFibreMap' {c c' : ModelCode O} (ψ : c.scheme ⟶ c'.scheme)
    (hψ : ψ ≫ c'.toSpec = c.toSpec) : IsClosedMap (specialFibreMap ψ hψ) := by
  haveI : UniversallyClosed (ψ ≫ c'.toSpec) := by rw [hψ]; infer_instance
  haveI : UniversallyClosed ψ := UniversallyClosed.of_comp_of_isSeparated ψ c'.toSpec
  intro C hC
  have hZ : IsClosed (specialFibre c.toSpec) :=
    (IsLocalRing.isClosed_singleton_closedPoint O).preimage c.toSpec.continuous
  have h₁ : IsClosed ((↑) '' C : Set c.scheme) := hZ.isClosedMap_subtype_val _ hC
  have h₂ := ψ.isClosedMap _ h₁
  convert h₂.preimage continuous_subtype_val using 1
  ext z
  simp only [mem_image, mem_preimage]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.1, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨y, hy, rfl⟩, hz⟩
    exact ⟨y, hy, Subtype.ext hz⟩

namespace Level

/-- **The generic point** `Spec L ⟶ Spec B ⟶ 𝒯` of the model of a level. -/
abbrev gen (Lv : Level O R A) (L : Type u) [Field L] [Algebra Lv.L.B L] :
    Spec (CommRingCat.of L) ⟶ Lv.c.scheme :=
  Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B L)) ≫ Lv.j

/-- If `j` is scheme-theoretically dominant and `B ⊆ L` is a domain, every point of the model
specializes from the generic point. -/
lemma gen_specializes (Lv : Level O R A) (L : Type u) [Field L] [Algebra Lv.L.B L]
    [FaithfulSMul Lv.L.B L] [IsSchemeTheoreticallyDominant Lv.j] (x : Lv.c.scheme) :
    Lv.gen L (closedPoint L) ⤳ x := by
  haveI : QuasiCompact (Lv.j ≫ Lv.c.toSpec) := by rw [Lv.j_toSpec]; infer_instance
  haveI : QuasiCompact Lv.j := QuasiCompact.of_comp Lv.j Lv.c.toSpec
  haveI : IsDominant Lv.j := inferInstance
  have hd : DenseRange Lv.j := Lv.j.denseRange
  let p₀ : Spec (CommRingCat.of Lv.L.B) := Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B L))
    (closedPoint L)
  have hp₀ : ∀ q : Spec (CommRingCat.of Lv.L.B), p₀ ⤳ q := by
    intro q
    refine (PrimeSpectrum.le_iff_specializes (R := Lv.L.B) p₀ q).1 ?_
    intro b hb
    change b ∈ (PrimeSpectrum.comap (algebraMap Lv.L.B L) (closedPoint L)).asIdeal at hb
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap] at hb
    have : algebraMap Lv.L.B L b = 0 := by
      simpa [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot] using hb
    rw [(FaithfulSMul.algebraMap_injective Lv.L.B L).eq_iff.1 (this.trans (map_zero _).symm)]
    exact zero_mem _
  have hsub : range Lv.j ⊆ closure {Lv.gen L (closedPoint L)} := by
    rintro _ ⟨q, rfl⟩
    exact specializes_iff_mem_closure.1 ((hp₀ q).map Lv.j.continuous)
  rw [specializes_iff_mem_closure]
  exact closure_minimal hsub isClosed_closure (hd.closure_range.symm ▸ mem_univ x)

open ValuativeCentre in
/-- **Restriction of centres along model maps.** Let `ψ : 𝒯 ⟶ 𝒯₀` be a model map over `O`
compatible with a level map `φ : B₀ → B`, and `f : F₀ → L` the induced map of fraction fields.
If `x` is the centre of a valuation subring `W ⊆ L`, then `ψ x` is the centre of `W ∩ F₀`. -/
lemma isCentre_comap (Lv Lv₀ : Level O R A) {L F₀ : Type u} [Field L] [Field F₀]
    [Algebra Lv.L.B L] [Algebra Lv₀.L.B F₀] (φ : Lv₀.L.B →ₐ[R] Lv.L.B) (f : F₀ →+* L)
    (hf : ∀ b, f (algebraMap Lv₀.L.B F₀ b) = algebraMap Lv.L.B L (φ b))
    (ψ : Lv.c.scheme ⟶ Lv₀.c.scheme)
    (hjψ : Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (φ : Lv₀.L.B →+* Lv.L.B)) ≫ Lv₀.j)
    {W : ValuationSubring L} {x : Lv.c.scheme} (hW : IsCentre (Lv.gen L) W x) :
    IsCentre (Lv₀.gen F₀) (W.comap f) (ψ x) := by
  obtain ⟨l, hl, rfl⟩ := hW
  -- the structure map `O → W`
  obtain ⟨h, hh⟩ := Spec.map_surjective (l ≫ Lv.c.toSpec)
  have key : h ≫ CommRingCat.ofHom (algebraMap W L) =
      CommRingCat.ofHom (levelStructureMap O R A Lv.L) ≫
        CommRingCat.ofHom (algebraMap Lv.L.B L) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hh, ← Category.assoc, ← genMap, hl, Spec.map_comp, Category.assoc,
      Lv.j_toSpec]
  have hmem : ∀ o : O, f (algebraMap Lv₀.L.B F₀ (levelStructureMap O R A Lv₀.L o)) ∈ W := by
    intro o
    rw [hf]
    have h1 : φ (levelStructureMap O R A Lv₀.L o) = levelStructureMap O R A Lv.L o := by
      simp [levelStructureMap]
    rw [h1]
    have h2 := congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of L => g o) key
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
    rw [← h2]
    exact (h.hom o).2
  set W₀ := W.comap f
  let a : O →+* W₀ :=
    ((algebraMap Lv₀.L.B F₀).comp (levelStructureMap O R A Lv₀.L)).codRestrict W₀.toSubring
      fun o => hmem o
  obtain ⟨l₀, hl₀, -⟩ := exists_lift Lv₀.c.toSpec (Lv₀.gen F₀) W₀ (CommRingCat.ofHom a) (by
    rw [Category.assoc, Lv₀.j_toSpec, genMap, ← Spec.map_comp, ← Spec.map_comp]
    rfl)
  -- the inclusion `W₀ → W` is local
  let incl : W₀ →+* W := (f.comp W₀.subtype).codRestrict W.toSubring fun y => y.2
  haveI : IsLocalHom incl := by
    refine ⟨fun y hy => ?_⟩
    obtain ⟨z, hz⟩ := isUnit_iff_exists_inv.1 hy
    have hz' : f (y : F₀) * (z : L) = 1 := congrArg Subtype.val hz
    have hy0 : (y : F₀) ≠ 0 := by
      intro h0
      rw [h0, map_zero, zero_mul] at hz'
      exact zero_ne_one hz'
    have hinv : (y : F₀)⁻¹ ∈ W₀ := by
      change f (y : F₀)⁻¹ ∈ W
      rw [map_inv₀, inv_eq_of_mul_eq_one_right hz']
      exact z.2
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy0)⟩
  have hm : Spec.map (CommRingCat.ofHom incl) ≫ l₀ = l ≫ ψ := by
    refine lift_unique Lv₀.c.toSpec W _ _ ?_
    have e₁ : genMap W ≫ Spec.map (CommRingCat.ofHom incl) =
        Spec.map (CommRingCat.ofHom f) ≫ genMap W₀ := by
      rw [genMap, genMap, ← Spec.map_comp, ← Spec.map_comp]
      rfl
    rw [← Category.assoc, e₁, Category.assoc, hl₀, ← Category.assoc (genMap W) l ψ, hl]
    simp only [Level.gen, Category.assoc]
    rw [hjψ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
    have e₂ : CommRingCat.ofHom (algebraMap Lv₀.L.B F₀) ≫ CommRingCat.ofHom f =
        CommRingCat.ofHom (φ : Lv₀.L.B →+* Lv.L.B) ≫ CommRingCat.ofHom (algebraMap Lv.L.B L) :=
      CommRingCat.hom_ext (RingHom.ext fun b => hf b)
    rw [e₂]
  refine ⟨l₀, hl₀, ?_⟩
  have hc : Spec.map (CommRingCat.ofHom incl) (closedPoint W) = closedPoint W₀ :=
    IsLocalRing.comap_closedPoint incl
  have := congrArg (fun m => m (closedPoint W)) hm
  simp only [Scheme.Hom.comp_apply] at this
  rw [hc] at this
  exact this

end Level

end

end TemperedFundamentalGroups
