/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.WModelChart
import TemperedFundamentalGroups.SemistableReduction.ModelGerms
import TemperedFundamentalGroups.SemistableReduction.NoLoopsPrimes
import TemperedFundamentalGroups.SemistableReduction.NodeGermL
import TemperedFundamentalGroups.SemistableReduction.TrdegOne
import TemperedFundamentalGroups.SemistableReduction.MonomialUnique

/-!
# Exact node coordinates at nodes of W-models (W8′, XL1)

Blueprint §9.7 (XL1). At a node point `y` of a split semistable W-model `c` of `L` without loops,
the germs at `y` form a local subring `P ⊆ L` which is a node germ
(`NodeGerm O' ϖ P u v n`, `n` the thickness) for exact coordinates `u v = ϖ ^ n`, flat over the
node via `(u, v)` (`exists_nodeGerm`).

* `exists_wChart`: an affine chart `U ∋ y` of a W-model, through which the generic point factors,
  whose sections embed into `L` with fraction field `L`, as an `O'`-algebra of finite type.
-/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing Polynomial

namespace TemperedFundamentalGroups.SemistableReduction.ModelCode

open _root_.SemistableReduction

variable {K' L : Type u} [Field K'] [Field L] [Algebra K' L] {O' : ValuationSubring K'}
  [Algebra O' L] [IsScalarTower O' K' L]

/-- Sections of models along morphisms over the base are algebra maps. -/
lemma app_algebraMap {c c' : TemperedFundamentalGroups.ModelCode O'} (f : c.scheme ⟶ c'.scheme)
    (hf : f ≫ c'.toSpec = c.toSpec) (V : c'.scheme.Opens) (o : O') :
    letI := sectionsAlgebra c' V
    letI := sectionsAlgebra c (f ⁻¹ᵁ V)
    (f.app V).hom (algebraMap O' Γ(c'.scheme, V) o) = algebraMap O' Γ(c.scheme, f ⁻¹ᵁ V) o := by
  letI := sectionsAlgebra c' V
  letI := sectionsAlgebra c (f ⁻¹ᵁ V)
  change ((Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ c'.toSpec.appTop ≫
      c'.scheme.presheaf.map (homOfLE le_top).op ≫ f.app V).hom o =
    ((Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ c.toSpec.appTop ≫
      c.scheme.presheaf.map (homOfLE le_top).op).hom o
  congr 2
  rw [← hf, Scheme.Hom.comp_appTop, Scheme.Hom.naturality]
  rfl

lemma range_algebraMap_eq_baseRing' :
    (algebraMap O' L).range = baseRing L O'.valuation.valuationSubring := by
  rw [ValuationSubring.valuationSubring_valuation]
  ext z
  constructor
  · rintro ⟨o, rfl⟩
    rw [IsScalarTower.algebraMap_apply O' K' L]
    exact ⟨o, o.2, rfl⟩
  · rintro ⟨o, ho, rfl⟩
    refine ⟨⟨o, ho⟩, ?_⟩
    rw [IsScalarTower.algebraMap_apply O' K' L]
    rfl

/-- **An affine chart of a W-model at a point**: the generic point factors through it, its
sections embed into `L` (`toL`) compatibly with `O'`, with fraction field `L`, and they form an
`O'`-algebra of finite type. -/
theorem exists_wChart {x : L} {c : TemperedFundamentalGroups.ModelCode O'}
    {j : Spec (CommRingCat.of L) ⟶ c.scheme} (hW : IsWModel O' L x c j) (y : c.scheme) :
    ∃ (U : c.scheme.Opens) (_ : IsAffineOpen U) (_ : y ∈ U) (h : ⊤ ≤ j ⁻¹ᵁ U),
      Function.Injective (toL j h) ∧
      (∀ f : L, ∃ a b : Γ(c.scheme, U), toL j h b ≠ 0 ∧ f = toL j h a / toL j h b) ∧
      (letI := sectionsAlgebra c U;
        (∀ o : O', toL j h (algebraMap O' _ o) = algebraMap O' L o) ∧
          Algebra.FiniteType O' Γ(c.scheme, U)) := by
  obtain ⟨hx, ι, _, _, a, b, halg, hb, n, g, hg, hpts, eiso, he1, he2⟩ := hW
  obtain ⟨i, hi⟩ := ProjScheme.exists_mem_chartOpen (O := O') hg (eiso.hom y)
  let V := ProjScheme.chartOpen O' hg i
  let U := eiso.hom ⁻¹ᵁ V
  have hU : IsAffineOpen U := (ProjScheme.isAffineOpen_chartOpen hg i).preimage eiso.hom
  have h : ⊤ ≤ j ⁻¹ᵁ U := by
    have := ProjScheme.top_le_toImage_preimage_chartOpen (O := O') hg i
    rw [← he2] at this
    exact this
  -- `toL` on `U` is the chart map
  have key : ∀ s : Γ((ProjScheme.projModelCode O' hg).scheme, V),
      toL j h ((eiso.hom.app V).hom s) = (ProjScheme.chartHom' O' hg i).hom s := by
    intro s
    simp only [toL, ProjScheme.chartHom']
    rw [Scheme.Hom.app_eq_appLE]
    change ((eiso.hom.appLE V U le_rfl ≫ j.appLE U ⊤ h) ≫ _).hom s = _
    rw [Scheme.Hom.appLE_comp_appLE, ProjScheme.appLE_congr_hom he2]
    rfl
  have hbij : Function.Bijective (eiso.hom.app V).hom := ConcreteCategory.bijective_of_isIso _
  have hR := range_algebraMap_eq_baseRing' (O' := O') (K' := K') (L := L)
  refine ⟨U, hU, hi, h, ?_, ?_, ?_, ?_⟩
  · intro s t hst
    obtain ⟨s', rfl⟩ := hbij.2 s
    obtain ⟨t', rfl⟩ := hbij.2 t
    rw [key, key] at hst
    rw [ProjScheme.chartHom'_injective hg i hst]
  · intro f
    have hf : f ∈ Subfield.closure (projChart (baseRing L O'.valuation.valuationSubring) g i :
        Set L) := by
      rw [subfield_closure_projChart_eq_top hx hb halg hpts i]; trivial
    obtain ⟨p, hp, q, hq, rfl⟩ := Subfield.mem_closure_iff.mp hf
    rw [Subring.closure_eq] at hp hq
    rw [← ProjScheme.range_chartHom' _ hR hg i] at hp hq
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨q', rfl⟩ := hq
    by_cases hq0 : (ProjScheme.chartHom' O' hg i).hom q' = 0
    · refine ⟨0, 1, ?_, ?_⟩
      · rw [← toLHom_apply, map_one]; exact one_ne_zero
      · rw [hq0, div_zero, ← toLHom_apply, ← toLHom_apply, map_zero, zero_div]
    · refine ⟨(eiso.hom.app V).hom p', (eiso.hom.app V).hom q', ?_, ?_⟩
      · rw [key]; exact hq0
      · rw [key, key]
  · intro o
    letI := sectionsAlgebra c U
    letI := sectionsAlgebra (ProjScheme.projModelCode O' hg) V
    rw [← app_algebraMap eiso.hom he1 V o, key, ProjScheme.chartHom'_algebraMap]
  · letI := sectionsAlgebra c U
    letI := sectionsAlgebra (ProjScheme.projModelCode O' hg) V
    letI := ProjScheme.projChartAlgebra (O := O') (f := g) _ hR i
    haveI := finiteType_projChart (O' := O') hR g i
    let φ : Γ((ProjScheme.projModelCode O' hg).scheme, V) →ₐ[O'] Γ(c.scheme, U) :=
      { (eiso.hom.app V).hom with commutes' := fun o ↦ app_algebraMap eiso.hom he1 V o }
    let eφ : Γ((ProjScheme.projModelCode O' hg).scheme, V) ≃ₐ[O'] Γ(c.scheme, U) :=
      AlgEquiv.ofBijective φ hbij
    exact Algebra.FiniteType.equiv inferInstance ((ProjScheme.chartEquiv _ hR hg i).symm.trans eφ)

omit [Algebra O' L] [IsScalarTower O' K' L] in
/-- Algebraic over `K'(x)` implies algebraic over `K'[x]`. -/
lemma isAlgebraic_adjoin_of_ratFunc {x : L} (hx : Transcendental K' x)
    (h : letI := xLineAlgebra L hx; Algebra.IsAlgebraic (RatFunc K') L) :
    Algebra.IsAlgebraic (Algebra.adjoin K' {x}) L := by
  letI := xLineAlgebra L hx
  letI : Algebra K'[X] L := (aeval x : K'[X] →ₐ[K'] L).toRingHom.toAlgebra
  haveI : IsScalarTower K'[X] (RatFunc K') L := IsScalarTower.of_algebraMap_eq fun p ↦ by
    change aeval x p = RatFunc.liftAlgHom _ _ (algebraMap K'[X] (RatFunc K') p)
    have := RatFunc.liftAlgHom_apply_div (aeval x : K'[X] →ₐ[K'] L) (fun p hp ↦ by
      simp only [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero, ne_eq] at hp ⊢
      exact fun h ↦ hp ((injective_iff_map_eq_zero _).mp
        (transcendental_iff_injective.mp hx) p h)) p 1
    rw [map_one, div_one, map_one, div_one] at this
    exact this.symm
  -- `K'[X] ≅ K'[x]`
  let ψ : K'[X] →+* Algebra.adjoin K' {x} :=
    (aeval x : K'[X] →ₐ[K'] L).toRingHom.codRestrict _ fun p ↦ by
      rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨p, rfl⟩
  letI : Algebra K'[X] (Algebra.adjoin K' {x}) := ψ.toAlgebra
  haveI : IsScalarTower K'[X] (Algebra.adjoin K' {x}) L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hψ : Function.Injective (algebraMap K'[X] (Algebra.adjoin K' {x})) := fun p q hpq ↦
    transcendental_iff_injective.mp hx (congrArg Subtype.val hpq)
  refine ⟨fun f ↦ ?_⟩
  have h1 : IsAlgebraic K'[X] f :=
    (IsFractionRing.isAlgebraic_iff K'[X] (RatFunc K') L).mpr (h.isAlgebraic f)
  exact h1.extendScalars hψ

omit [Algebra K' L] [IsScalarTower O' K' L] in
/-- The `O'`-algebra structures on sections are compatible with restriction. -/
lemma res_algebraMap {c : TemperedFundamentalGroups.ModelCode O'} {U V : c.scheme.Opens}
    (hVU : V ≤ U) (o : O') :
    letI := sectionsAlgebra c U
    letI := sectionsAlgebra c V
    (c.scheme.presheaf.map (homOfLE hVU).op).hom (algebraMap O' Γ(c.scheme, U) o) =
      algebraMap O' Γ(c.scheme, V) o := by
  letI := sectionsAlgebra c U
  letI := sectionsAlgebra c V
  change ((Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ c.toSpec.appTop ≫
      c.scheme.presheaf.map (homOfLE le_top).op ≫ c.scheme.presheaf.map (homOfLE hVU).op).hom o =
    ((Scheme.ΓSpecIso (CommRingCat.of O')).inv ≫ c.toSpec.appTop ≫
      c.scheme.presheaf.map (homOfLE le_top).op).hom o
  rw [← Functor.map_comp]
  rfl

variable [IsDiscreteValuationRing O']

/-- **Node germs of W-models** (XL1, Blueprint §9.7). Let `c` be a W-model of `L` (over a DVR
`O'` with uniformizer `ϖ`) with split nodes and without loops, and `y` a node point of `c`, of
thickness `n ≥ 1`. Then the germs at `y` form a local subring `P ⊆ L` which is a node germ
`NodeGerm O' ϖ P u v n` for exact coordinates `u v = ϖ ^ n`, with `ϖ, u, v` in the maximal ideal,
`u` transcendental over `K'`, `P` flat over the node `O'[u, v] ⧸ (u v - ϖ ^ n)` via `(u, v)` (the
image consisting of polynomials in `u, v`), and `u, v` are sections, vanishing at `y`, over an
open `V ∋ y` containing the generic point (the data of `ModelCode.IsXLength`); `P` is the image of
a normal noetherian ordinary double point (`IsODPGerm`, input of the divisor lemma). -/
theorem exists_nodeGerm {ϖ : O'} (hϖ : Irreducible ϖ) {x : L}
    {c : TemperedFundamentalGroups.ModelCode O'} {j : Spec (CommRingCat.of L) ⟶ c.scheme}
    (hW : IsWModel O' L x c j) (hsplit : HasSplitNodes ϖ c) (hloops : NoLoops c) {y : c.scheme}
    (hy : IsNodePt c y) :
    ∃ (P : Subring L) (u v : L) (n : ℕ) (h : NodeGerm O' ϖ P u v n),
      1 ≤ n ∧ IsNodeOfThickness ϖ c y n ∧ (P : Set L) = germs c j y ∧
      (∃ _ : IsLocalRing P, (⟨_, h.algebraMap_mem ϖ⟩ : P) ∈ maximalIdeal P ∧
        (⟨u, h.u_mem⟩ : P) ∈ maximalIdeal P ∧ (⟨v, h.v_mem⟩ : P) ∈ maximalIdeal P) ∧
      Transcendental K' u ∧
      (∃ φ : _root_.SemistableReduction.Node O' (ϖ ^ n) →+* P,
        (letI := φ.toAlgebra; Module.Flat (_root_.SemistableReduction.Node O' (ϖ ^ n)) P) ∧
        (∀ b, (φ b : L) ∈
          Subring.closure (Set.range (fun o : O' ↦ algebraMap K' L (o : K')) ∪ {u, v})) ∧
        (∀ o : O', (φ (algebraMap O' _ o) : L) = algebraMap K' L (o : K')) ∧
        (φ (_root_.SemistableReduction.Node.u _) : L) = u ∧
        (φ (_root_.SemistableReduction.Node.v _) : L) = v) ∧
      (∃ (V : c.scheme.Opens) (hyV : y ∈ V) (hV : ⊤ ≤ j ⁻¹ᵁ V) (su sv : Γ(c.scheme, V)),
        letI := sectionsAlgebra c V
        su * sv = algebraMap O' Γ(c.scheme, V) (ϖ ^ n) ∧
        ¬ IsUnit ((c.scheme.presheaf.germ V y hyV).hom su) ∧
        ¬ IsUnit ((c.scheme.presheaf.germ V y hyV).hom sv) ∧
        toL j hV su = u ∧ toL j hV sv = v) ∧
      _root_.SemistableReduction.IsODPGerm O' ϖ P u v n := by
  classical
  obtain ⟨hx, -, -, -, -, -, halg, -⟩ := id hW
  -- the split chart, at the singular point
  obtain ⟨U₀, hU₀, hy₀, n, C, _, g, f, 𝔮, hg, hf, h𝔮, hc, hO, hres⟩ := hsplit y hy
  letI := sectionsAlgebra c U₀
  have hns : ¬ IsEtaleLocallyAt O' O'[X] (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal :=
    fun hs ↦ hy.2 ⟨U₀, hU₀, hy₀, hs⟩
  have hu : f (Node.u _) ∈ 𝔮 := by
    by_contra h
    exact hns (isEtaleLocallyAt_polynomial_of_notMem hg hf h𝔮 hc hO (.inl h))
  have hv : f (Node.v _) ∈ 𝔮 := by
    by_contra h
    exact hns (isEtaleLocallyAt_polynomial_of_notMem hg hf h𝔮 hc hO (.inr h))
  have hsp₀ : IsSplitNodeAt ϖ n (hU₀.primeIdealOf ⟨y, hy₀⟩).asIdeal :=
    ⟨C, inferInstance, g, f, 𝔮, hg, hf, h𝔮, hc, hO, hu, hv, hres⟩
  have hn : 1 ≤ n := IsNodeAt.pos ⟨C, inferInstance, g, f, 𝔮, hg, hf, h𝔮, hc, hO, hu, hv⟩
  have hthick : IsNodeOfThickness ϖ c y n :=
    ⟨hy, U₀, hU₀, hy₀, C, inferInstance, g, f, 𝔮, hg, hf, h𝔮, hc, hO⟩
  -- the W-chart
  obtain ⟨U, hU, hyU, h, hinj, hfrac, hO', hFT⟩ := exists_wChart hW y
  letI := sectionsAlgebra c U
  have hsp := isSplitNodeAt_transfer hϖ hU hU₀ hyU hy₀ hsp₀
  haveI : IsDomain Γ(c.scheme, U) := hinj.isDomain (toLHom j h)
  set 𝔭 := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal
  obtain ⟨P₁, P₂, hp₁, hp₂, hϖ₁, hϖ₂, hle₁, hle₂, hmin₁, hmin₂, hne⟩ :=
    exists_minimal_primes_of_noLoops hϖ hloops hy hU hyU
  have hιO : ∀ o : O', toLHom j h (algebraMap O' _ o) = algebraMap K' L (o : K') := fun o ↦ by
    rw [toLHom_apply, hO', IsScalarTower.algebraMap_apply O' K' L]
    rfl
  obtain ⟨P, u, v, hG, hPset, hloc, htr, hflat, ⟨a, b, s, hs, hua, hvb⟩, hODP⟩ :=
    _root_.SemistableReduction.exists_nodeGerm_of_split (O := O') hϖ hn (toLHom j h) hinj hιO
      hfrac hx (isAlgebraic_adjoin_of_ratFunc hx halg) 𝔭 hsp P₁ P₂ hϖ₁ hϖ₂ hle₁ hle₂ hmin₁
      hmin₂ hne
  have hPg : (P : Set L) = germs c j y := by
    rw [hPset, germs_eq_of_isAffineOpen j hU hyU h hinj]
    rfl
  refine ⟨P, u, v, n, hG, hn, hthick, hPg, hloc, htr, hflat, ?_, hODP⟩
  obtain ⟨_, -, humax, hvmax⟩ := hloc
  -- sections over `V = D(s)`
  have hι0 : ∀ z : Γ(c.scheme, U), z ∉ 𝔭 → toL j h z ≠ 0 := fun z hz h0 ↦
    hz (by rw [show z = 0 from hinj (by rw [h0, ← toLHom_apply, map_zero])]; exact zero_mem _)
  set V := c.scheme.basicOpen s
  have hVU : V ≤ U := c.scheme.basicOpen_le s
  have hyV : y ∈ V := by
    by_contra hn'; exact hs ((mem_primeIdealOf_iff hU hyU s).mpr hn')
  have hV : ⊤ ≤ j ⁻¹ᵁ V := top_le_preimage_basicOpen j h s (hι0 s hs)
  let r : Γ(c.scheme, U) →+* Γ(c.scheme, V) := (c.scheme.presheaf.map (homOfLE hVU).op).hom
  have hrs : IsUnit (r s) := c.scheme.toRingedSpace.isUnit_res_basicOpen s
  have htoLr : ∀ z, toL j hV (r z) = toL j h z := fun z ↦ toL_res j hVU hV h z
  let sinv : Γ(c.scheme, V) := ↑hrs.unit⁻¹
  have hsinv : toL j hV sinv = (toL j h s)⁻¹ := by
    have : toL j hV (r s) * toL j hV sinv = 1 := by
      rw [← toLHom_apply, ← toLHom_apply, ← map_mul, IsUnit.mul_val_inv, map_one]
    rw [htoLr] at this
    exact eq_inv_of_mul_eq_one_right this
  have hsu : toL j hV (r a * sinv) = u := by
    rw [← toLHom_apply, map_mul, toLHom_apply, toLHom_apply, htoLr, hsinv, hua, div_eq_mul_inv]
    rfl
  have hsv : toL j hV (r b * sinv) = v := by
    rw [← toLHom_apply, map_mul, toLHom_apply, toLHom_apply, htoLr, hsinv, hvb, div_eq_mul_inv]
    rfl
  -- `toL` is injective on `V`
  have hinjV : Function.Injective (toLHom j hV) := by
    letI : Algebra Γ(c.scheme, U) Γ(c.scheme, V) := r.toAlgebra
    haveI : IsLocalization.Away s Γ(c.scheme, V) := hU.isLocalization_basicOpen s
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a', m⟩, hm⟩ := IsLocalization.surj (Submonoid.powers s) z
    have h1 : toL j h a' = 0 := by
      rw [← htoLr]
      change toL j hV (algebraMap _ _ a') = 0
      rw [← hm, ← toLHom_apply, map_mul, hz, zero_mul]
    have ha' : a' = 0 := hinj (by rw [h1]; exact (map_zero (toLHom j h)).symm)
    rw [ha', map_zero] at hm
    exact (IsLocalization.map_units Γ(c.scheme, V) m).mul_left_eq_zero.mp hm
  -- non-units at `y`
  have key : ∀ (z : Γ(c.scheme, V)) (w : L) (hw : w ∈ P), w ≠ 0 → toL j hV z = w →
      (⟨w, hw⟩ : P) ∈ maximalIdeal P → ¬ IsUnit ((c.scheme.presheaf.germ V y hyV).hom z) := by
    intro z w hw hw0 hzw hwm hunit
    have hyW : y ∈ c.scheme.basicOpen z := (Scheme.mem_basicOpen _ z y hyV).mpr hunit
    have hWV : c.scheme.basicOpen z ≤ V := c.scheme.basicOpen_le z
    have hW : ⊤ ≤ j ⁻¹ᵁ c.scheme.basicOpen z := top_le_preimage_basicOpen j hV z (hzw ▸ hw0)
    have hrz : IsUnit ((c.scheme.presheaf.map (homOfLE hWV).op).hom z) :=
      c.scheme.toRingedSpace.isUnit_res_basicOpen z
    have h1 : toL j hW ((c.scheme.presheaf.map (homOfLE hWV).op).hom z) *
        toL j hW ↑hrz.unit⁻¹ = 1 := by
      rw [← toLHom_apply, ← toLHom_apply, ← map_mul, IsUnit.mul_val_inv, map_one]
    rw [toL_res j hWV hW hV, hzw] at h1
    have hmem : toL j hW ↑hrz.unit⁻¹ ∈ P := by
      rw [← SetLike.mem_coe, hPg]; exact toL_mem_germs j hW hyW _
    have : IsUnit (⟨w, hw⟩ : P) := IsUnit.of_mul_eq_one (⟨_, hmem⟩ : P) (Subtype.ext h1)
    exact hwm this
  have hu0 : u ≠ 0 := fun h0 ↦ htr (h0 ▸ isAlgebraic_zero)
  have hv0 : v ≠ 0 := by
    refine right_ne_zero_of_mul (a := u) ?_
    rw [hG.mul_eq]
    refine pow_ne_zero _ ?_
    rw [map_ne_zero_iff _ (algebraMap K' L).injective]
    exact fun h0 ↦ hϖ.ne_zero (Subtype.ext h0)
  letI := sectionsAlgebra c V
  refine ⟨V, hyV, hV, r a * sinv, r b * sinv, ?_, key _ u hG.u_mem hu0 hsu humax,
    key _ v hG.v_mem hv0 hsv hvmax, hsu, hsv⟩
  apply hinjV
  rw [map_mul, toLHom_apply, toLHom_apply, hsu, hsv, hG.mul_eq, toLHom_apply,
    ← res_algebraMap hVU, htoLr, ← toLHom_apply, hιO]
  push_cast
  rfl

end TemperedFundamentalGroups.SemistableReduction.ModelCode
