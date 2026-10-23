/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.WCentre

/-!
# Discrete valuations at the generic points of the special fibre (Blueprint §10.3.8, I4)

Let `Lv` be a level carrying W-model data `D : WData x Lv`, `F` a fraction field of its ring `B`
and `ζ` the generic point of an irreducible component of the special fibre of the model. A
valuation subring `V ⊆ F` with centre `ζ` is a **discrete valuation ring**
(`WData.isDiscreteValuationRing_of_isCentre`), and the image `ϖ_F` of a uniformizer `ϖ` of `O`
in `F` is a nonzero element of the maximal ideal of `V`, hence `ϖ_F = u t ^ n` with `t` a
uniformizer of `V`, `u` a unit and `n ≥ 1` (`WData.exists_eq_unit_mul_pow_of_isCentre`).

* `ValuativeCentre.isNoetherianRing_of_isCentre`: a valuation subring with centre `ι 𝔭` at a
  point of a noetherian affine chart `ι : Spec A ⟶ X`, through which the generic point factors
  and where the local ring `A_𝔭 → F` has image a valuation subring, is the image of `A_𝔭`,
  hence noetherian;
* `WData.exists_chart`: the chart data of `WData.centreDetermines` (an affine noetherian chart of
  the W-model around `ζ` whose local ring at `ζ` is a valuation subring of `F`);
* `Level.exists_isLocalHom_of_isCentre`: if `V` has centre in the special fibre, the structure
  map `O → B → F` factors through a local map `O → V`.

A noetherian valuation ring which is not a field is a discrete valuation ring
(`IsDiscreteValuationRing.TFAE`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Set Topology TopologicalSpace

namespace TemperedFundamentalGroups

namespace ValuativeCentre

variable {X : Scheme.{u}} {F : Type u} [Field F]

/-- **Valuation subrings centred at a point of a noetherian chart are noetherian** if the local
ring of the chart at that point is a valuation subring of `F`. -/
theorem isNoetherianRing_of_isCentre {A : CommRingCat.{u}} [IsNoetherianRing A]
    (ι : Spec A ⟶ X) [IsOpenImmersion ι] (f : A ⟶ CommRingCat.of F) (p : Spec A)
    (hval : ∀ y : F, (∃ a, ∃ s ∉ p.asIdeal, y * f s = f a) ∨
      (∃ a, ∃ s ∉ p.asIdeal, y⁻¹ * f s = f a))
    {V : ValuationSubring F} (hV : IsCentre (Spec.map f ≫ ι) V (ι p)) : IsNoetherianRing V := by
  obtain ⟨l, hl, hlp⟩ := hV
  have hrange : Set.range l ⊆ Set.range ι := by
    rintro _ ⟨z, rfl⟩
    have hz : z ⤳ closedPoint V :=
      (PrimeSpectrum.le_iff_specializes z (closedPoint V)).1 (le_maximalIdeal z.2.ne_top)
    have hz' := hz.map l.continuous
    rw [hlp] at hz'
    exact hz'.mem_open ι.isOpenEmbedding.isOpen_range ⟨p, rfl⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift ι l hrange)
  have hfac : Spec.map φ ≫ ι = l := by rw [hφ, IsOpenImmersion.lift_fac]
  have hf : φ ≫ CommRingCat.ofHom (algebraMap V F) = f := by
    apply Spec.map_injective
    rw [← cancel_mono ι, Spec.map_comp, Category.assoc, hfac, ← hl]
  have hfa (a : A) : f a = (φ a : F) := by rw [← hf]; rfl
  have hcp : Spec.map φ (closedPoint V) = p :=
    ι.isOpenEmbedding.injective (by rw [← Scheme.Hom.comp_apply, hfac, hlp])
  have hmem (s : A) : s ∈ p.asIdeal ↔ φ s ∈ maximalIdeal V := by
    rw [← hcp]
    rfl
  have hunit' (s : A) (hs : s ∉ p.asIdeal) : IsUnit (φ s) := by
    rw [hmem, mem_maximalIdeal, mem_nonunits_iff, not_not] at hs
    exact hs
  have hunit (s : A) (hs : s ∉ p.asIdeal) : V.valuation (f s) = 1 := by
    rw [hfa, ← V.valuation_eq_one_iff]
    exact hunit' s hs
  -- every element of `V` is a fraction `f a / f s` with `s ∉ 𝔭`
  have H : ∀ y ∈ V, ∃ a, ∃ s ∉ p.asIdeal, y * f s = f a := by
    intro y hy
    rcases eq_or_ne y 0 with rfl | hy0
    · exact ⟨0, 1, p.2.ne_top ∘ (Ideal.eq_top_iff_one _).2, by simp⟩
    rcases hval y with h | ⟨a, s, hs, hys⟩
    · exact h
    by_cases ha : a ∈ p.asIdeal
    · exfalso
      have hlt : V.valuation (f a) < 1 := by
        rw [hfa, ← ValuationSubring.valuation_lt_one_iff]
        exact (hmem a).1 ha
      have h1 : V.valuation y⁻¹ < 1 := by
        rwa [← hys, map_mul, hunit s hs, mul_one] at hlt
      have h2 : V.valuation y ≤ 1 := (V.valuation_le_one_iff y).2 hy
      have h3 : V.valuation (y * y⁻¹) < 1 := by
        rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' h2) h1
      rw [mul_inv_cancel₀ hy0, map_one] at h3
      exact lt_irrefl _ h3
    · refine ⟨s, a, ha, ?_⟩
      rw [← hys, ← mul_assoc, mul_inv_cancel₀ hy0, one_mul]
  -- `V` is the image of `A_𝔭`
  let ψ : Localization.AtPrime p.asIdeal →+* V :=
    IsLocalization.lift (M := p.asIdeal.primeCompl) (g := φ.hom) fun s ↦ hunit' s s.2
  have hsurj : Function.Surjective ψ := by
    intro v
    obtain ⟨a, s, hs, hys⟩ := H v v.2
    refine ⟨IsLocalization.mk' (Localization.AtPrime p.asIdeal) a
      (⟨s, hs⟩ : p.asIdeal.primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    apply Subtype.ext
    change (φ a : F) = (φ s : F) * v
    rw [← hfa, ← hfa, ← hys, mul_comm]
  haveI : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
    IsLocalization.isNoetherianRing p.asIdeal.primeCompl _ inferInstance
  exact isNoetherianRing_of_surjective _ _ ψ hsurj

end ValuativeCentre

open ValuativeCentre

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- **If the centre lies in the special fibre, `O → V` is local**: for a valuation subring `V`
of a field `F` over the ring of a level with centre `z` in the special fibre, the structure map
`O → B → F` factors through a local map `O → V`. -/
lemma Level.exists_isLocalHom_of_isCentre (Lv : Level O R A) {F : Type u} [Field F]
    [Algebra Lv.L.B F] {V : ValuationSubring F} {z : Lv.c.scheme}
    (hV : IsCentre (Lv.gen F) V z) (hz : z ∈ specialFibre Lv.c.toSpec) :
    ∃ φ : O →+* V, IsLocalHom φ ∧
      ∀ o, (φ o : F) = algebraMap Lv.L.B F (levelStructureMap O R A Lv.L o) := by
  obtain ⟨l, hl, rfl⟩ := hV
  obtain ⟨h, hh⟩ := Spec.map_surjective (l ≫ Lv.c.toSpec)
  have key : h ≫ CommRingCat.ofHom (algebraMap V F) =
      CommRingCat.ofHom (levelStructureMap O R A Lv.L) ≫
        CommRingCat.ofHom (algebraMap Lv.L.B F) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hh, ← Category.assoc, ← genMap, hl, Spec.map_comp, Category.assoc,
      Lv.j_toSpec]
  have hcp : Spec.map h (closedPoint V) = closedPoint O := by
    rw [hh, Scheme.Hom.comp_apply]
    exact hz
  refine ⟨h.hom, ⟨fun o ho ↦ ?_⟩, fun o ↦ ?_⟩
  · by_contra hno
    have hm : o ∈ (closedPoint O).asIdeal := hno
    rw [← hcp] at hm
    exact hm ho
  · have := congrArg (fun g : CommRingCat.of O ⟶ CommRingCat.of F => g o) key
    simpa using this

/-- **The uniformizer lies in the maximal ideal of a valuation centred in the special fibre**:
the image `ϖ_F` in `F` of a nonzero nonunit `ϖ ∈ O` is a nonzero element of the maximal ideal of
any valuation subring `V ⊆ F` with centre in the special fibre (`B` a domain, `F = Frac B`). -/
lemma Level.exists_mem_maximalIdeal_of_isCentre (Lv : Level O R A) [IsDomain Lv.L.B]
    {F : Type u} [Field F] [Algebra Lv.L.B F] [IsFractionRing Lv.L.B F] {V : ValuationSubring F}
    {z : Lv.c.scheme} (hV : IsCentre (Lv.gen F) V z) (hz : z ∈ specialFibre Lv.c.toSpec)
    (ϖ : O) (hϖ : ϖ ∈ maximalIdeal O) (hϖ0 : ϖ ≠ 0) :
    ∃ w : V, (w : F) = algebraMap Lv.L.B F (levelStructureMap O R A Lv.L ϖ) ∧ w ≠ 0 ∧
      w ∈ maximalIdeal V := by
  obtain ⟨φ, hφ, hφF⟩ := Lv.exists_isLocalHom_of_isCentre hV hz
  refine ⟨φ ϖ, hφF ϖ, fun h ↦ ?_, map_nonunit φ ϖ hϖ⟩
  have h' := congrArg Subtype.val h
  rw [hφF] at h'
  have hinj : Function.Injective (algebraMap Lv.L.B F) := IsFractionRing.injective _ _
  have hinj' : Function.Injective ((algebraMap R Lv.L.B).comp (algebraMap K R)) :=
    RingHom.injective _
  refine hϖ0 (Subtype.ext (hinj' (hinj ?_)))
  refine h'.trans ?_
  simp

/-- **The chart of a W-model around a generic point of the special fibre** (the data behind
`WData.centreDetermines`): an affine noetherian open chart `ι : Spec A ⟶ 𝒯` through which the
generic point `Spec F ⟶ 𝒯` factors, with a point `𝔭 ↦ ζ` at which the local ring `A_𝔭 → F` has
image a valuation subring of `F`. -/
theorem WData.exists_chart [IsDiscreteValuationRing O] {x : R} {Lv : Level O R A}
    (D : WData x Lv) [T0Space Lv.Z] (F : Type u) [Field F] [Algebra Lv.L.B F]
    [IsFractionRing Lv.L.B F] (ζ : Lv.Z) (hζ : closure {ζ} ∈ irreducibleComponents Lv.Z) :
    ∃ (Ach : CommRingCat.{u}) (_ : IsNoetherianRing Ach) (ι : Spec Ach ⟶ Lv.c.scheme)
      (_ : IsOpenImmersion ι) (f : Ach ⟶ CommRingCat.of F) (p : Spec Ach),
      Spec.map f ≫ ι = Lv.gen F ∧ ι p = (ζ : Lv.c.scheme) ∧
      ∀ y : F, (∃ a, ∃ s ∉ p.asIdeal, y * f s = f a) ∨
        (∃ a, ∃ s ∉ p.asIdeal, y⁻¹ * f s = f a) := by
  haveI := D.isDomain
  obtain ⟨hx, ι, _, _, a, b, hWM⟩ := D.wmodel.isWModel
  letI := SemistableReduction.xLineAlgebra D.L₁ hx
  haveI : IsScalarTower D.K' (RatFunc D.K') D.L₁ := IsScalarTower.of_algebraMap_eq fun k ↦ by
    change algebraMap D.K' D.L₁ k = RatFunc.liftAlgHom _ _ (algebraMap D.K' (RatFunc D.K') k)
    rw [AlgHom.commutes]
  obtain ⟨halg, hb, n, g, hg, hpts, e₂, he₂, hj₂⟩ := hWM
  let E := D.e ≪≫ e₂
  let R₀ := _root_.SemistableReduction.baseRing D.L₁ D.O'.valuation.valuationSubring
  have hR : (algebraMap D.O' D.L₁).range = R₀ := by
    ext y
    constructor
    · rintro ⟨o, rfl⟩
      refine ⟨(o : D.K'), (Valuation.mem_valuationSubring_iff _ _).2
        ((D.O'.valuation_le_one_iff _).2 o.2), ?_⟩
      exact (IsScalarTower.algebraMap_apply D.O' D.K' D.L₁ o).symm
    · rintro ⟨o, ho, rfl⟩
      refine ⟨⟨o, (D.O'.valuation_le_one_iff _).1 ((Valuation.mem_valuationSubring_iff _ _).1 ho)⟩,
        ?_⟩
      exact IsScalarTower.algebraMap_apply D.O' D.K' D.L₁ _
  obtain ⟨i, hi⟩ := _root_.SemistableReduction.ProjScheme.exists_mem_chartOpen hg (E.hom ζ.1)
  rw [← _root_.SemistableReduction.ProjScheme.opensRange_chartι R₀ hR hg i] at hi
  obtain ⟨p, hp⟩ := hi
  let ch := _root_.SemistableReduction.ProjScheme.chartι R₀ hR hg i
  let Ach := _root_.SemistableReduction.projChart R₀ g i
  haveI : IsNoetherianRing Ach := isNoetherianRing_projChart hR g i
  letI := _root_.SemistableReduction.ProjScheme.projChartAlgebra (f := g) R₀ hR i
  let ϖa : Ach := algebraMap D.O' Ach D.ϖ'
  have hϖa : (ϖa : D.L₁) ≠ 0 := by
    change algebraMap D.O' D.L₁ D.ϖ' ≠ 0
    rw [IsScalarTower.algebraMap_apply D.O' D.K' D.L₁]
    refine (map_ne_zero _).2 fun h ↦ D.hϖ'.ne_zero (Subtype.ext h)
  have hspec : ∀ q : Spec (CommRingCat.of Ach),
      (_root_.SemistableReduction.ProjScheme.projModelCode D.O' hg).toSpec (ch q) =
        closedPoint D.O' ↔ ϖa ∈ q.asIdeal := by
    intro q
    rw [← Scheme.Hom.comp_apply, _root_.SemistableReduction.ProjScheme.chartι_toSpec R₀ hR hg i]
    constructor
    · intro h
      have hm : D.ϖ' ∈ (closedPoint D.O').asIdeal := D.hϖ'.not_isUnit
      have h' := congrArg PrimeSpectrum.asIdeal h
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal] at h'
      rw [← h'] at hm
      exact hm
    · intro h
      apply PrimeSpectrum.ext
      rw [Spec.map_apply, PrimeSpectrum.comap_asIdeal]
      have hle : maximalIdeal D.O' ≤
          q.asIdeal.comap (CommRingCat.ofHom (algebraMap D.O' Ach)).hom := by
        rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).1 D.hϖ']
        exact (Ideal.span_singleton_le_iff_mem _).2 h
      exact ((maximalIdeal.isMaximal D.O').eq_of_le (Ideal.comap_isPrime _ _).ne_top hle).symm
  have htoSpec : E.inv ≫ Lv.c.toSpec =
      (_root_.SemistableReduction.ProjScheme.projModelCode D.O' hg).toSpec ≫
        Spec.map (CommRingCat.ofHom ((algebraMap K D.K').restrict O D.O'
          (fun y hy => by rw [← D.hO'] at hy; exact hy))) := by
    rw [← D.toSpec_eq, ← he₂]
    simp [E]
  have hLv : ∀ y, E.inv y ∈ specialFibre Lv.c.toSpec ↔
      (_root_.SemistableReduction.ProjScheme.projModelCode D.O' hg).toSpec y =
        closedPoint D.O' := by
    intro y
    rw [mem_specialFibre, ← Scheme.Hom.comp_apply, htoSpec, Scheme.Hom.comp_apply]
    exact spec_restrict_eq_closedPoint_iff D.hO' _
  have hinv : E.inv (ch p) = ζ.1 := by
    change E.inv (_root_.SemistableReduction.ProjScheme.chartι R₀ hR hg i p) = ζ.1
    rw [hp, ← Scheme.Hom.comp_apply, E.hom_inv_id]
    rfl
  have hap : ϖa ∈ p.asIdeal := (hspec p).1 ((hLv _).1 (hinv ▸ ζ.2))
  have hmin : p.asIdeal ∈ (Ideal.span {ϖa}).minimalPrimes := by
    refine ⟨⟨p.2, (Ideal.span_singleton_le_iff_mem _).2 hap⟩, fun q ⟨hq, hqa⟩ hqp ↦ ?_⟩
    let q' : Spec (CommRingCat.of Ach) := ⟨q, hq⟩
    have hsp : q' ⤳ p := (PrimeSpectrum.le_iff_specializes q' p).1 hqp
    have hmemZ : E.inv (ch q') ∈ specialFibre Lv.c.toSpec :=
      (hLv _).2 ((hspec q').2 ((Ideal.span_singleton_le_iff_mem _).1 hqa))
    have hz : (⟨_, hmemZ⟩ : Lv.Z) ⤳ ζ := by
      rw [← Topology.IsInducing.subtypeVal.specializes_iff]
      change E.inv (ch q') ⤳ ζ.1
      rw [← hinv]
      exact (hsp.map ch.continuous).map E.inv.continuous
    have h1 : E.inv (ch q') = E.inv (ch p) := by
      rw [hinv]
      exact congrArg Subtype.val (eq_of_specializes_of_mem_irreducibleComponents hζ hz)
    have h2 : ch q' = ch p := by
      have key : ∀ y, E.hom (E.inv y) = y := fun y ↦ by
        rw [← Scheme.Hom.comp_apply, E.inv_hom_id]
        rfl
      have := congrArg E.hom h1
      rwa [key, key] at this
    have h3 : q' = p := ch.isOpenEmbedding.injective h2
    exact (congrArg PrimeSpectrum.asIdeal h3).ge
  -- the local ring of the chart at `𝔭` is a valuation subring of `L₁`
  obtain ⟨hint, hfrac⟩ := localSubring_props D.O' a b hb g hpts i p.asIdeal
  have hvalL := LocalSubring.ofPrime_mem_or_inv_mem Ach p.asIdeal hϖa hmin hint hfrac
  have hmemS : ∀ y : D.L₁, y ∈ (LocalSubring.ofPrime Ach p.asIdeal).toSubring →
      ∃ a : Ach, ∃ s ∉ p.asIdeal, y * s = a := by
    intro y hy
    obtain ⟨⟨a', s'⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl
      (⟨y, hy⟩ : (LocalSubring.ofPrime Ach p.asIdeal).toSubring)
    exact ⟨a', s', s'.2, congrArg Subtype.val h⟩
  -- transport to `F`
  let τ : D.L₁ ≃ₐ[Lv.L.B] F := IsLocalization.algEquiv (nonZeroDivisors Lv.L.B) D.L₁ F
  let f : CommRingCat.of Ach ⟶ CommRingCat.of F :=
    CommRingCat.ofHom ((τ : D.L₁ →+* F).comp Ach.subtype)
  have hval : ∀ y : F, (∃ a, ∃ s ∉ p.asIdeal, y * f s = f a) ∨
      (∃ a, ∃ s ∉ p.asIdeal, y⁻¹ * f s = f a) := by
    intro y
    have hy : τ (τ.symm y) = y := τ.apply_symm_apply y
    rcases hvalL (τ.symm y) with h | h
    · obtain ⟨a', s, hs, e⟩ := hmemS _ h
      refine Or.inl ⟨a', s, hs, ?_⟩
      have := congrArg τ e
      rwa [map_mul, hy] at this
    · obtain ⟨a', s, hs, e⟩ := hmemS _ h
      refine Or.inr ⟨a', s, hs, ?_⟩
      have := congrArg τ e
      rwa [map_mul, map_inv₀, hy] at this
  have hτ : CommRingCat.ofHom (algebraMap Lv.L.B D.L₁) ≫ CommRingCat.ofHom (τ : D.L₁ →+* F) =
      CommRingCat.ofHom (algebraMap Lv.L.B F) :=
    CommRingCat.hom_ext (RingHom.ext fun b ↦ τ.commutes b)
  have h1 : Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B F)) =
      Spec.map (CommRingCat.ofHom (τ : D.L₁ →+* F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B D.L₁)) := by
    rw [← hτ, Spec.map_comp]
  have h2 : Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B D.L₁)) ≫ Lv.j ≫ D.e.hom ≫ e₂.hom =
      (_root_.SemistableReduction.ProjScheme.toProj D.O' hg).toImage := by
    rw [← hj₂, D.hj]
    simp only [Category.assoc]
  have hgen : Lv.gen F ≫ E.hom = Spec.map f ≫ ch := by
    simp only [Level.gen, E, Iso.trans_hom, h1, Category.assoc]
    rw [h2, _root_.SemistableReduction.ProjScheme.toImage_eq_SpecMap_comp_chartι R₀ hR hg i,
      ← Category.assoc, ← Spec.map_comp]
    rfl
  refine ⟨CommRingCat.of Ach, inferInstanceAs (IsNoetherianRing Ach), ch ≫ E.inv,
    inferInstance, f, p, ?_, by rw [Scheme.Hom.comp_apply]; exact hinv, hval⟩
  rw [← Category.assoc, ← hgen, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **Valuations centred at generic points of the special fibre of a W-model are discrete**
(Blueprint §10.3.8, I4). -/
theorem WData.isDiscreteValuationRing_of_isCentre [IsDiscreteValuationRing O] {x : R}
    {Lv : Level O R A} (D : WData x Lv) [T0Space Lv.Z] (F : Type u) [Field F]
    [Algebra Lv.L.B F] [IsFractionRing Lv.L.B F] (ζ : Lv.Z)
    (hζ : closure {ζ} ∈ irreducibleComponents Lv.Z) {V : ValuationSubring F}
    (hV : IsCentre (Lv.gen F) V (ζ : Lv.c.scheme)) : IsDiscreteValuationRing V := by
  haveI := D.isDomain
  obtain ⟨Ach, _, ι, _, f, p, hgen, hp, hval⟩ := D.exists_chart F ζ hζ
  have hV' := hV
  rw [← hgen, ← hp] at hV'
  haveI := isNoetherianRing_of_isCentre ι f p hval hV'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨w, -, h0, hm⟩ := Lv.exists_mem_maximalIdeal_of_isCentre hV ζ.2 ϖ hϖ.not_isUnit
    hϖ.ne_zero
  have hnf : ¬ IsField V := fun h ↦ h0 (by
    rw [(isField_iff_maximalIdeal_eq).1 h] at hm
    exact hm)
  haveI : ValuationRing V := inferInstance
  exact ((IsDiscreteValuationRing.TFAE V hnf).out 0 1).2 this

/-- **The uniformizer of `O` in a discrete valuation centred at a generic point of the special
fibre**: `ϖ_F = u t ^ n` with `t` a uniformizer of `V`, `u ∈ Vˣ` and `n ≥ 1`. -/
theorem WData.exists_eq_unit_mul_pow_of_isCentre [IsDiscreteValuationRing O] {x : R}
    {Lv : Level O R A} (D : WData x Lv) [T0Space Lv.Z] (F : Type u) [Field F]
    [Algebra Lv.L.B F] [IsFractionRing Lv.L.B F] (ζ : Lv.Z)
    (hζ : closure {ζ} ∈ irreducibleComponents Lv.Z) {V : ValuationSubring F}
    (hV : IsCentre (Lv.gen F) V (ζ : Lv.c.scheme)) (ϖ : O) (hϖ : Irreducible ϖ) :
    ∃ (t : V) (_ : Irreducible t) (u : Vˣ) (n : ℕ), 0 < n ∧
      algebraMap Lv.L.B F (levelStructureMap O R A Lv.L ϖ) = ((u * t ^ n : V) : F) := by
  haveI := D.isDomain
  haveI := D.isDiscreteValuationRing_of_isCentre F ζ hζ hV
  obtain ⟨w, hw, h0, hm⟩ := Lv.exists_mem_maximalIdeal_of_isCentre hV ζ.2 ϖ hϖ.not_isUnit
    hϖ.ne_zero
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible h0 ht
  refine ⟨t, ht, u, n, Nat.pos_of_ne_zero fun hn ↦ ?_, hw.symm⟩
  rw [hn, pow_zero, mul_one] at hm
  exact (mem_maximalIdeal _).1 hm u.isUnit

end

end TemperedFundamentalGroups
