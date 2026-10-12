/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.CurveTowerNodes
import TemperedFundamentalGroups.SemistableReduction.UnfoldedNoSwap

/-!
# No branch inversions in André's tower (Blueprint §12.5, C12 (d); §12.7, M3)

An automorphism `b` of a tempered covering over a W-model level acts on the W-model `c'` by
`τ = e⁻¹ ∘ ψ_b ∘ e`, compatibly with the generic point through the automorphism
`σ = fracMap (φ_b)` of the function field `L₁` (`WData.j₁_comp_wMap`); `σ` fixes the x-line
`x ∈ R` and the constants `K` (`φ_b` is an `R`-algebra map). By
`CrossingSource.exists_branches_not_swapped` (the two branches of a node restrict to Gauss points
of the x-line of different radii, and `σ` preserves radii), **an automorphism fixing a node
fixes both components through it** (`WData.compHomeo_eq_of_fixed`). In the tree of the dual
graph, an edge vertex has exactly one neighbour over each component through its node
(`Tree.eq_nbr`), so the stage groups act **without branch inversions**:

* `UData.noBranchSwap`, **`noBranchSwap_andreTower`**: André's tree tower has no branch
  inversions (`TreeTower.NoBranchSwap`), unconditionally;
* **`pscAdj_andreTower_of_estranged'`**, **`isGraphic_iff_andreTower_of_estranged'`**: `PSCAdj`
  and CG3' for André's group under estrangement and nontrivial edge-like subgroups only.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology TopologicalSpace

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {x : R}

namespace WData

variable {X : TempObj O R A} (D : WData x X.Lv)

/-- The automorphism of the function field of an endomorphism. -/
def fracEnd (m : X ⟶ X) : D.L₁ →+* D.L₁ :=
  haveI := D.isDomain
  haveI := X.Lv.L.etale
  haveI := X.Lv.L.finite
  fracMap D.L₁ D.L₁ m.φ.f

lemma fracEnd_algebraMap (m : X ⟶ X) (b : X.Lv.L.B) :
    D.fracEnd m (algebraMap X.Lv.L.B D.L₁ b) = algebraMap X.Lv.L.B D.L₁ (m.φ.f b) := by
  haveI := D.isDomain
  haveI := X.Lv.L.etale
  haveI := X.Lv.L.finite
  exact fracMap_algebraMap _ _

/-- **The model endomorphism is compatible with the generic point.** -/
lemma j₁_comp_wMap (m : X ⟶ X) :
    D.j₁ ≫ wMap m D D = Spec.map (CommRingCat.ofHom (D.fracEnd m)) ≫ D.j₁ := by
  rw [D.hj]
  simp only [wMap, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc X.Lv.j m.ψ, m.j_ψ]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  congr 3
  exact RingHom.ext fun b ↦ (D.fracEnd_algebraMap m b).symm

lemma fracEnd_xL (m : X ⟶ X) : D.fracEnd m D.xL = D.xL := by
  rw [WData.xL, fracEnd_algebraMap, AlgHom.commutes]

lemma fracEnd_algebraMap_K (m : X ⟶ X) (k : K) :
    letI := D.algKL
    D.fracEnd m (algebraMap K D.L₁ k) = algebraMap K D.L₁ k := by
  change D.fracEnd m (algebraMap X.Lv.L.B D.L₁ _) = algebraMap X.Lv.L.B D.L₁ _
  rw [fracEnd_algebraMap, RingHom.comp_apply, AlgHom.commutes]

variable [IsDiscreteValuationRing O]

/-- A uniformizer of `O` is a power of the uniformizer of `O'` up to a unit. -/
lemma exists_uniformizer_eq : ∃ (ϖ₀ : O) (e₀ : ℕ) (η : D.O'ˣ), 1 ≤ e₀ ∧
    algebraMap K D.K' (ϖ₀ : K) = (η : D.K') * (D.ϖ' : D.K') ^ e₀ := by
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O
  set ι := (algebraMap K D.K').restrict O D.O' (fun y hy => by rw [← D.hO'] at hy; exact hy)
  have hinj : Function.Injective ι := fun a b h ↦
    Subtype.ext ((algebraMap K D.K').injective (congrArg Subtype.val h))
  obtain ⟨e₀, η, h⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff ι hinj).2 hϖ₀.ne_zero) D.hϖ'
  have he₀ : 1 ≤ e₀ := by
    by_contra h0
    have : e₀ = 0 := by omega
    rw [this, pow_zero, mul_one] at h
    haveI := isLocalHom_restrict D.hO'
    exact hϖ₀.not_isUnit ((isUnit_map_iff ι ϖ₀).1 (h ▸ η.isUnit))
  refine ⟨ϖ₀, e₀, η, he₀, ?_⟩
  have := congrArg Subtype.val h
  exact this

include D in
/-- **M3: an automorphism fixing a special point fixes the components through it.** -/
theorem compHomeo_eq_of_fixed [NoetherianSpace X.Lv.Z] [T0Space X.Lv.Z] [QuasiSober X.Lv.Z]
    (hdim : topologicalKrullDim X.Lv.Z ≤ 1) (b : X ≅ X) {s : X.Lv.Z}
    (hs : s ∈ (curveConfig X.Lv.Z hdim).S) (hbs : TempObj.zHomeo b s = s)
    (i : irreducibleComponents X.Lv.Z) (hsi : s ∈ i.1) :
    compHomeo (TempObj.zHomeo b) i = i := by
  letI := D.algKL
  haveI := D.isScalarTower_K
  haveI : Algebra.IsAlgebraic K D.K' := Algebra.IsAlgebraic.of_finite K D.K'
  obtain ⟨ϖ₀, e₀, η, he₀, hϖ₀⟩ := D.exists_uniformizer_eq
  have hy := D.isNodePt_of_mem_S SemistableReduction.nodeOfTwoComponents hs
  obtain ⟨v₁, hv₁, v₂, hv₂, hne, -, -, honly, hno⟩ :=
    SemistableReduction.CrossingSource.exists_branches_not_swapped D.wmodel D.hϖ' D.split
      D.noLoops (K₀ := K) he₀ hϖ₀ hy
  -- endomorphisms over the x-line do not map `v₁` to `v₂`
  have hno' : ∀ m : X ⟶ X, wMap m D D '' v₁ ≠ v₂ := fun m ↦
    hno _ (D.fracEnd m) (D.j₁_comp_wMap m) (D.fracEnd_xL m) (D.fracEnd_algebraMap_K m)
  have himg : ∀ (m : X ⟶ X) (C : Set X.Lv.Z),
      wMap m D D '' D.compSet C = D.compSet (specialFibreMap m.ψ m.ψ_toSpec '' C) :=
    fun m C ↦ WData.image_compSet m D D C
  have hzb : specialFibreMap b.hom.ψ b.hom.ψ_toSpec = TempObj.zHomeo b := rfl
  have hzb' : specialFibreMap b.inv.ψ b.inv.ψ_toSpec '' (TempObj.zHomeo b '' i.1) = i.1 := by
    rw [Set.image_image]
    convert Set.image_id i.1 using 2 with z
    apply Subtype.ext
    change b.inv.ψ (b.hom.ψ z.1) = z.1
    rw [← Scheme.Hom.comp_apply, ← TempObj.comp_ψ, b.hom_inv_id]
    rfl
  by_contra hne_i
  set i' := compHomeo (TempObj.zHomeo b) i
  have hi' : i'.1 = TempObj.zHomeo b '' i.1 := rfl
  have hcs : ∀ k : irreducibleComponents X.Lv.Z, s ∈ k.1 →
      D.compSet k.1 = v₁ ∨ D.compSet k.1 = v₂ := fun k hk ↦
    honly _ (D.compSet_mem k.2) (D.pt_mem_compSet_iff.2 hk)
  have hsi' : s ∈ i'.1 := by rw [hi', ← hbs]; exact ⟨s, hsi, rfl⟩
  have hdist : D.compSet i.1 ≠ D.compSet i'.1 := fun h ↦
    hne_i (Subtype.ext (D.compSet_injective h)).symm
  rcases hcs i hsi with h₁ | h₁ <;> rcases hcs i' hsi' with h₂ | h₂
  · exact hdist (h₁.trans h₂.symm)
  · apply hno' b.hom
    rw [← h₁, ← h₂, himg, hzb, hi']
  · apply hno' b.inv
    rw [← h₁, ← h₂, himg, hi', hzb']
  · exact hdist (h₁.trans h₂.symm)

end WData

section Heads

variable {Lv : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H] [NoetherianSpace Lv.Z]
  [T0Space Lv.Z] [QuasiSober Lv.Z] {hdim : topologicalKrullDim Lv.Z ≤ 1} {z₀ : Lv.Z}
  (b : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀)

lemma autVmap_head_inr {t : UTree hdim z₀} {s : Lv.Z} (hs : t.1.head? = some (.inr s)) :
    (autVmap b t).1.head? = some (.inr (zHomeoU b s)) := by
  obtain ⟨s', hs', hpt⟩ := vmap_inr_of_over (hηU hdim) (uTreeMap_fst b)
    (curveConfig_mem_S_homeo hdim (zHomeoU b)) hs
  rw [uTreeMap_fst] at hpt
  change zHomeoU b (canonPt t) = s' at hpt
  rw [canonPt_of_inr hs] at hpt
  change (vmap (hηU hdim) (uTreeMap b.hom) t).1.head? = _
  rw [hs', hpt]

lemma eta_injective_curveConfig {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [T0Space X] [QuasiSober X] (hdim : topologicalKrullDim X ≤ 1) :
    Function.Injective (curveConfig X hdim).η := fun i k h ↦ by
  have hi := i.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents i.1 i.2)
  have hk := k.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents k.1 k.2)
  change i.2.1.genericPoint = k.2.1.genericPoint at h
  apply Subtype.ext
  rw [← hi.def, ← hk.def, h]

lemma autVmap_head_inl {t : UTree hdim z₀} {i : irreducibleComponents Lv.Z}
    (hi : t.1.head? = some (.inl i)) :
    (autVmap b t).1.head? = some (.inl (compHomeo (zHomeoU b) i)) := by
  obtain ⟨j, hj, hpt⟩ := vmap_inl_of_over (hηU hdim) (hηU hdim) (uTreeMap_fst b)
    (fun i ↦ ⟨_, curveConfig_η_homeo hdim (zHomeoU b) i⟩) hi
  rw [uTreeMap_fst] at hpt
  change zHomeoU b (canonPt t) = _ at hpt
  rw [canonPt_of_inl hi, curveConfig_η_homeo hdim (zHomeoU b) i] at hpt
  change (vmap (hηU hdim) (uTreeMap b.hom) t).1.head? = _
  rw [hj, eta_injective_curveConfig hdim hpt]

/-- **No branch inversions for an automorphism of `U`** fixing the components through every
fixed special point. -/
lemma autTree_adj_fixed
    (hfix : ∀ s ∈ (curveConfig Lv.Z hdim).S, zHomeoU b s = s →
      ∀ i : irreducibleComponents Lv.Z, s ∈ i.1 → compHomeo (zHomeoU b) i = i)
    {e w : UTree hdim z₀} (hk : Tree.kind e = false) (hadj : e.Adj w) (he : autTree b e = e) :
    autTree b w = w := by
  obtain ⟨s, hs⟩ := Tree.kind_eq_false_iff.1 hk
  obtain ⟨i, hi, hsS, hsi⟩ := head_inl_of_adj e.2 w.2 hadj hs
  have hbs : zHomeoU b s = s := by
    have h := autVmap_head_inr b hs
    rw [← autTree_apply, he, hs] at h
    simpa using h.symm
  have hw' := autVmap_head_inl b hi
  rw [hfix s hsS hbs i hsi] at hw'
  have hadj' : e.Adj (autTree b w) := by
    have := (adj_autTree_iff b e w).2 hadj
    rwa [he] at this
  have hv : (curveConfig Lv.Z hdim).Adj (.inr s) (.inl i) := ⟨hsS, hsi⟩
  exact (Tree.eq_nbr hadj' hs hv hw').trans (Tree.eq_nbr hadj hs hv hi).symm

end Heads

variable {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- **No branch inversions for the stage group of a member over a W-model level.** -/
theorem UData.treeAut_noBranchSwap [IsDiscreteValuationRing O] {X : TempObj O R A}
    (D : UData Ω X) (W : WData x D.Lv) (a : Aut X) {e w : D.Tr} (hk : Tree.kind e = false)
    (hadj : e.Adj w) (he : D.treeAut a e = e) : D.treeAut a w = w :=
  autTree_adj_fixed (D.e.conjAut a) (fun _ hs hbs i hsi ↦
    WData.compHomeo_eq_of_fixed (X := universalObj D.Lv D.hdim D.z₀) W D.hdim (D.e.conjAut a)
      hs hbs i hsi) hk hadj he

section Andre

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

/-- **M3: the tree tower of a curve has no branch inversions.** -/
theorem noBranchSwap_curveTower : (curveTower (R := R) (A := A) V hV hp hR).NoBranchSwap := by
  intro p g e w hk hadj he
  obtain ⟨a, rfl⟩ := eq_stageOf g
  change (curveData V hV hR p).stageTree V hV (stageOf a) w = w
  change (curveData V hV hR p).stageTree V hV (stageOf a) e = e at he
  rw [UData.stageTree_stageOf] at he ⊢
  exact UData.treeAut_noBranchSwap _ (WData.nonempty_of_isW (curveData_isW V hV hR p)).some a
    hk hadj he

variable [Finite A] [SMulCommClass A K R]

/-- **M3: André's tree tower has no branch inversions** (unconditionally). -/
theorem noBranchSwap_andreTower : (andreTower (R := R) (A := A) V hV hp hR).NoBranchSwap :=
  noBranchSwap_curveTower V hV hp hR

/-- **`PSCAdj` for André's group** under estrangement and nontrivial edge-like subgroups
(node reflection M1 and no branch inversions M3 are proved). -/
theorem pscAdj_andreTower_of_estranged'
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj :=
  pscAdj_andreTower_of_estranged V hV hp hR hE (noBranchSwap_andreTower V hV hp hR) hedge

/-- **CG3' for André's group** against a functorial estranged tree tower without branch
inversions, under estrangement and nontrivial edge-like subgroups. -/
theorem isGraphic_iff_andreTower_of_estranged' {Γ' : Type*} [Group Γ'] {J' : Type*}
    [Category J'] [IsCofilteredOrEmpty J'] {T' : TreeTower Γ' J'}
    {α : andreGroup O R A V hV ≃* Γ'}
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥)
    (hT' : T'.IsFunctorial) (hE' : T'.Estranged) (hB' : T'.NoBranchSwap)
    (hedge' : ∀ e : T'.Sys, (∀ j, ∃ (k : J') (_ : k ⟶ j), T'.kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR) T' α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α :=
  isGraphic_iff_andreTower_of_estranged V hV hp hR hE (noBranchSwap_andreTower V hV hp hR) hedge
    hT' hE' hB' hedge'

/-- **CG3' between the André groups of two curves**: an isomorphism of André's groups is graphic
if and only if it is group-theoretically verticial, provided both trees towers are estranged and
have nontrivial edge-like subgroups (functoriality and the absence of branch inversions are
proved). -/
theorem isGraphic_iff_andreTower_andreTower
    {K₂ : Type u} [Field K₂] [CharZero K₂] {O₂ : ValuationSubring K₂}
    [IsDiscreteValuationRing O₂] [IsAdicComplete (IsLocalRing.maximalIdeal O₂) O₂]
    [PerfectField (IsLocalRing.ResidueField O₂)]
    {R₂ : Type u} [CommRing R₂] [Algebra K₂ R₂] [Algebra.Smooth K₂ R₂] [IsDomain R₂]
    {A₂ : Type u} [Group A₂] [MulSemiringAction A₂ R₂] [Subsingleton A₂] [Finite A₂]
    [SMulCommClass A₂ K₂ R₂]
    {Ω₂ : Type u} [Field Ω₂] [IsAlgClosed Ω₂] [Algebra K₂ Ω₂] [Algebra R₂ Ω₂]
    [IsScalarTower K₂ R₂ Ω₂] (V₂ : ValuationSubring Ω₂) (hV₂ : V₂.comap (algebraMap K₂ Ω₂) = O₂)
    (hp₂ : ∃ p : ℕ, p.Prime ∧ (p : O₂) ∈ IsLocalRing.maximalIdeal O₂)
    (hR₂ : ringKrullDim R₂ = 1) {α : andreGroup O R A V hV ≃* andreGroup O₂ R₂ A₂ V₂ hV₂}
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥)
    (hE₂ : (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂).Estranged)
    (hedge₂ : ∀ e : (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O₂ R₂ A₂ V₂ hV₂) (galW O₂ R₂ A₂ Ω₂ hR₂)) (_ : k ⟶ j),
        (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR)
        (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂) α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR)
        (andreTower (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂) α := by
  haveI := isCofiltered_ptGalW (R := R₂) (A := A₂) V₂ hV₂ hp₂ hR₂
  exact isGraphic_iff_andreTower_of_estranged' V hV hp hR hE hedge
    (isFunctorial_andreTower_galW V₂ hV₂ hp₂ hR₂) hE₂ (noBranchSwap_andreTower V₂ hV₂ hp₂ hR₂)
    hedge₂

end Andre

end

end TemperedFundamentalGroups
