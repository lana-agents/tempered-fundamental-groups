/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.WCentreLocal
import TemperedFundamentalGroups.Andre.GTransitive
import TemperedFundamentalGroups.Andre.LengthW

/-!
# The centre determines the valuation on W-models (Blueprint §10.3.8, I4)

For a level `Lv` carrying W-model data `D : WData x Lv` and a fraction field `F` of its ring `B`,
at the generic point `ζ` of every irreducible component of the special fibre the centre
determines the valuation of `F` (`WData.centreDetermines`, `Pres.centreDetermines`): the
hypothesis `hval₀` of `exists_aut_image_eq`, which is discharged for presentations of members of
`galClassW` in `exists_aut_image_eq_of_pres`.

Proof. The model is isomorphic to the projective model `projModelCode O' g` of the W-model, whose
affine charts `Spec R[g j / g i]` are open immersions through which the generic point factors
(`ProjScheme.toImage_eq_SpecMap_comp_chartι`). If `ζ` corresponds to the prime `𝔭` of the chart
`A = R[g j / g i]`, then `𝔭` is minimal over the uniformizer `ϖ'` of `O'` (`ζ` is a generic point
of the special fibre), so the local ring `A_𝔭 ⊆ L₁` is a valuation subring of `L₁`
(`LocalSubring.ofPrime_mem_or_inv_mem`, `localSubring_props`: noetherian, of dimension one by
Krull's principal ideal theorem, integrally closed with fraction field `L₁` as a local ring of the
normalization of a Gauss-tree model). A valuation subring `V` with centre `ζ` then maps the chart
into `V` with `𝔭 = 𝔪_V ∩ A`, so `V` dominates `A_𝔭`, hence equals it
(`ValuativeCentre.centreDetermines_of_openImmersion`).
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Set Topology TopologicalSpace

namespace TemperedFundamentalGroups

namespace ValuativeCentre

variable {X Y : Scheme.{u}} {F : Type u} [Field F]

lemma IsCentre.comp {g : Spec (CommRingCat.of F) ⟶ X} {V : ValuationSubring F} {x : X}
    (h : IsCentre g V x) (ψ : X ⟶ Y) : IsCentre (g ≫ ψ) V (ψ x) := by
  obtain ⟨l, hl, rfl⟩ := h
  exact ⟨l ≫ ψ, by rw [← Category.assoc, hl], rfl⟩

lemma CentreDetermines.of_comp {g : Spec (CommRingCat.of F) ⟶ X} {x : X} (ψ : X ⟶ Y)
    (h : CentreDetermines (g ≫ ψ) (ψ x)) : CentreDetermines g x :=
  fun _ _ h₁ h₂ ↦ h _ _ (h₁.comp ψ) (h₂.comp ψ)

/-- **The centre determines the valuation, through an affine chart.** -/
theorem centreDetermines_of_openImmersion {A : CommRingCat.{u}} (ι : Spec A ⟶ X)
    [IsOpenImmersion ι] (f : A ⟶ CommRingCat.of F) (p : Spec A)
    (hval : ∀ y : F, (∃ a, ∃ s ∉ p.asIdeal, y * f s = f a) ∨
      (∃ a, ∃ s ∉ p.asIdeal, y⁻¹ * f s = f a)) :
    CentreDetermines (Spec.map f ≫ ι) (ι p) := by
  suffices H : ∀ V : ValuationSubring F, IsCentre (Spec.map f ≫ ι) V (ι p) →
      ∀ y : F, y ∈ V ↔ ∃ a, ∃ s ∉ p.asIdeal, y * f s = f a by
    intro V₁ V₂ h₁ h₂
    ext y
    rw [H V₁ h₁, H V₂ h₂]
  rintro V ⟨l, hl, hlp⟩
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
  have hunit (s : A) (hs : s ∉ p.asIdeal) : V.valuation (f s) = 1 := by
    rw [hfa, ← V.valuation_eq_one_iff]
    rw [hmem, mem_maximalIdeal, mem_nonunits_iff, not_not] at hs
    exact hs
  have hs0 (s : A) (hs : s ∉ p.asIdeal) : f s ≠ 0 := fun h ↦ by
    have := hunit s hs
    rw [h, map_zero] at this
    exact zero_ne_one this
  intro y
  constructor
  · intro hy
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
  · rintro ⟨a, s, hs, hys⟩
    have : y = f a * (f s)⁻¹ := by rw [← hys, mul_inv_cancel_right₀ (hs0 s hs)]
    rw [← V.valuation_le_one_iff, this, map_mul, map_inv₀, hunit s hs, inv_one, mul_one,
      V.valuation_le_one_iff, hfa]
    exact (φ a).2

end ValuativeCentre

open ValuativeCentre

/-- A point specializing to the generic point of an irreducible component is that generic
point (`T₀`). -/
lemma eq_of_specializes_of_mem_irreducibleComponents {Z : Type*} [TopologicalSpace Z]
    [T0Space Z] {ζ z : Z} (hζ : closure {ζ} ∈ irreducibleComponents Z) (h : z ⤳ ζ) : z = ζ := by
  have h1 : closure {ζ} ⊆ closure {z} :=
    closure_minimal (singleton_subset_iff.2 (specializes_iff_mem_closure.1 h)) isClosed_closure
  have h2 := hζ.2 isIrreducible_singleton.closure h1
  exact (h.antisymm (specializes_iff_mem_closure.2 (h2 (subset_closure rfl)))).eq

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- **The centre determines the valuation at the generic points of the special fibre of a
W-model** (Blueprint §10.3.8, I4). -/
theorem WData.centreDetermines [IsDiscreteValuationRing O] {x : R} {Lv : Level O R A}
    (D : WData x Lv) [T0Space Lv.Z] (F : Type u) [Field F] [Algebra Lv.L.B F]
    [IsFractionRing Lv.L.B F] (ζ : Lv.Z) (hζ : closure {ζ} ∈ irreducibleComponents Lv.Z) :
    CentreDetermines (Lv.gen F) (ζ : Lv.c.scheme) := by
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
  refine CentreDetermines.of_comp E.hom ?_
  rw [hgen]
  rw [← hp]
  exact centreDetermines_of_openImmersion ch f p hval

/-- **`hval₀` for members of `galClassW`**: on the level of a presentation, the centre
determines the valuation at the generic points of the components of the special fibre. -/
theorem Pres.centreDetermines [IsDiscreteValuationRing O] {x : R} {X : TempObj O R A}
    (P : Pres x X) (F : Type u) [Field F] [Algebra P.Lv.L.B F] [IsFractionRing P.Lv.L.B F]
    (ζ : P.Lv.Z) (hζ : closure {ζ} ∈ irreducibleComponents P.Lv.Z) :
    CentreDetermines (P.Lv.gen F) (ζ : P.Lv.c.scheme) :=
  P.D.centreDetermines F ζ hζ

/-- **G-transitivity for presentations** (Blueprint §10.3.8, I4): `exists_aut_image_eq` for a
morphism `m : U ⟶ U₀` of the Galois objects of two presentations, with `hval₀` discharged by
`Pres.centreDetermines`. The Galois property `hgal` of the source (part of `galClassW`, not of
`Pres`) is a hypothesis. -/
theorem exists_aut_image_eq_of_pres [IsDiscreteValuationRing O] {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] [Algebra R Ω] {x : R} {X Y : TempObj O R A} (P : Pres x X) (P₀ : Pres x Y)
    (t₀ : P.Lv.L.B →ₐ[R] Ω)
    (hgal : ∀ t : P.Lv.L.B →ₐ[R] Ω, ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B,
      t₀.comp (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B) = t)
    (m : P.U ⟶ P₀.U) {v v' : Set P.Lv.Z} (hv : v ∈ irreducibleComponents P.Lv.Z)
    (hv' : v' ∈ irreducibleComponents P.Lv.Z)
    (hc : ¬ ∃ y, specialFibreMap m.ψ m.ψ_toSpec '' v = {y})
    (heq : specialFibreMap m.ψ m.ψ_toSpec '' v = specialFibreMap m.ψ m.ψ_toSpec '' v') :
    ∃ σ : P.Lv.L.B ≃ₐ[R] P.Lv.L.B, (σ : P.Lv.L.B →ₐ[R] P.Lv.L.B).comp m.φ.f = m.φ.f ∧
      ∃ (ψσ : P.Lv.c.scheme ⟶ P.Lv.c.scheme) (hψσ : ψσ ≫ P.Lv.c.toSpec = P.Lv.c.toSpec),
        P.Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : P.Lv.L.B →+* P.Lv.L.B)) ≫ P.Lv.j ∧
        specialFibreMap ψσ hψσ '' v = v' := by
  haveI := P.D.isDomain
  haveI := P₀.D.isDomain
  exact exists_aut_image_eq P.Lv P₀.Lv t₀ hgal P.idem P.act (FractionRing P₀.Lv.L.B)
    (FractionRing P.Lv.L.B) P₀.hdim (fun ζ hζ ↦ P₀.centreDetermines _ ζ hζ) m.φ.f m.ψ
    m.ψ_toSpec m.j_ψ hv hv' hc heq

end

end TemperedFundamentalGroups
