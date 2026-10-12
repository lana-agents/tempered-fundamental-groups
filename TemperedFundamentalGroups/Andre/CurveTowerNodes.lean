/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.CurveTowerFull
import TemperedFundamentalGroups.Andre.WEdgeLifting
import TemperedFundamentalGroups.SemistableReduction.NodeReflection

/-!
# Node reflection for André's tower (Blueprint §12.5, C11; §12.7, M1)

The morphisms of tempered coverings between objects over W-model levels **reflect nodes**
(`WData.reflectsSpecial`): a point `z` of the special fibre lying on a single component `C`
which maps to a special point (a point on two components, a node of the W-model) has the same
image as the generic point of `C`. This is the scheme form of M1,
`SemistableReduction.ModelCode.map_eq_of_isNodePt`, transported along the identifications of the
special fibres of the levels with those of their W-models (`WData.mem_Z_iff`, `WData.compSet`),
with the relation of uniformizers coming from the common base `O` (`WData.exists_rel`).

Hence the hypothesis `hN` of `Andre/CurveTowerFull.lean` holds for all transition maps of
André's tower (`reflectsNodes_curveData`), and:

* **`isFunctorial_andreTower_galW`**: André's tree tower is functorial on all levels,
  unconditionally;
* **`exists_le_stab_andreTower_of_estranged`**, **`exists_le_stab_andreTower_of_le_estranged`**,
  **`exists_eq_stab_of_maximal_of_estranged`** ([SemiAnbd] Thm. 3.7(iii)/(iv), system form) under
  estrangement alone;
* **`pscAdj_andreTower_of_estranged`**, **`isGraphic_iff_andreTower_of_estranged`** (CG3' for
  André's group) under estrangement, no branch inversions and nontrivial edge-like subgroups.
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

variable [IsDiscreteValuationRing O] {X Y : TempObj O R A} (m : X ⟶ Y) (D : WData x X.Lv)
  (D' : WData x Y.Lv)

/-- The model map between the W-models of the levels of a morphism. -/
abbrev wMap : D.c'.scheme ⟶ D'.c'.scheme := D.e.inv ≫ m.ψ ≫ D'.e.hom

/-- **The relation of uniformizers along a morphism of W-models**: `ψ^*(ϖ₂) ^ a = ϖ₁ ^ e ε`
with `a ≥ 1` and `ε` a unit (both are powers of a uniformizer of `O` up to units). -/
lemma exists_rel : ∃ (a e : ℕ) (ε : Γ(D.c'.scheme, ⊤)), 1 ≤ a ∧ IsUnit ε ∧
    (wMap m D D').appTop.hom (SemistableReduction.ModelCode.globHom D'.c' D'.ϖ') ^ a =
      SemistableReduction.ModelCode.globHom D.c' D.ϖ' ^ e * ε := by
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible O
  set ι₁ := (algebraMap K D.K').restrict O D.O' (fun y hy => by rw [← D.hO'] at hy; exact hy)
  set ι₂ := (algebraMap K D'.K').restrict O D'.O' (fun y hy => by rw [← D'.hO'] at hy; exact hy)
  have hinj₁ : Function.Injective ι₁ := fun a b h ↦
    Subtype.ext ((algebraMap K D.K').injective (congrArg Subtype.val h))
  have hinj₂ : Function.Injective ι₂ := fun a b h ↦
    Subtype.ext ((algebraMap K D'.K').injective (congrArg Subtype.val h))
  obtain ⟨e, u₁, h₁⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff ι₁ hinj₁).2 hϖ₀.ne_zero) D.hϖ'
  obtain ⟨a, u₂, h₂⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    ((map_ne_zero_iff ι₂ hinj₂).2 hϖ₀.ne_zero) D'.hϖ'
  have ha : 1 ≤ a := by
    by_contra h0
    have : a = 0 := by omega
    rw [this, pow_zero, mul_one] at h₂
    haveI := isLocalHom_restrict D'.hO'
    exact hϖ₀.not_isUnit ((isUnit_map_iff ι₂ ϖ₀).1 (h₂ ▸ u₂.isUnit))
  have hψ : wMap m D D' ≫ D'.c'.toSpec ≫ Spec.map (CommRingCat.ofHom ι₂) =
      D.c'.toSpec ≫ Spec.map (CommRingCat.ofHom ι₁) := by
    simp only [wMap, Category.assoc]
    rw [D'.toSpec_eq, m.ψ_toSpec, D.toSpec_e_inv]
  obtain ⟨ε, hε, hrel⟩ := SemistableReduction.ModelCode.exists_rel_of_comp_eq ι₁ ι₂ _ hψ
    u₁.isUnit u₂.isUnit (by rw [h₁, mul_comm]) (by rw [h₂, mul_comm])
  exact ⟨a, e, ε, ha, hε, hrel⟩

omit [IsDiscreteValuationRing O] in
lemma isInducing_pt : IsInducing D.pt :=
  D.e.hom.isOpenEmbedding.isInducing.comp IsInducing.subtypeVal

variable [NoetherianSpace X.Lv.Z] [T0Space X.Lv.Z] [QuasiSober X.Lv.Z]
  (hdim : topologicalKrullDim X.Lv.Z ≤ 1)
  [NoetherianSpace Y.Lv.Z] [T0Space Y.Lv.Z] [QuasiSober Y.Lv.Z]
  (hdim' : topologicalKrullDim Y.Lv.Z ≤ 1)

include D D' in
/-- **Node reflection along morphisms of W-model levels (M1)**: a point `z` on a single
component `C` of the special fibre whose image is a special point has the image of the generic
point of `C`. -/
theorem map_eta_eq (i : irreducibleComponents X.Lv.Z) {z : X.Lv.Z}
    (hz : z ∈ (curveConfig X.Lv.Z hdim).C i) (hzS : z ∉ (curveConfig X.Lv.Z hdim).S)
    (hψ : specialFibreMap m.ψ m.ψ_toSpec z ∈ (curveConfig Y.Lv.Z hdim').S) :
    specialFibreMap m.ψ m.ψ_toSpec ((curveConfig X.Lv.Z hdim).η i) =
      specialFibreMap m.ψ m.ψ_toSpec z := by
  set η := (curveConfig X.Lv.Z hdim).η i
  have hcl : IsClosed i.1 := isClosed_of_mem_irreducibleComponents i.1 i.2
  have hgen : IsGenericPoint η i.1 := i.2.1.isGenericPoint_genericPoint hcl
  obtain ⟨a, e, ε, ha, hε, hrel⟩ := exists_rel m D D'
  refine D'.pt_injective ?_
  rw [← WData.map_pt, ← WData.map_pt]
  refine SemistableReduction.ModelCode.map_eq_of_isNodePt D.hϖ' D'.hϖ' D'.semistable _ ha hε hrel
    ((D.mem_Z_iff z.1).1 z.2) ?_ ((hgen.specializes hz).map D.continuous_pt)
    ((D.mem_Z_iff η.1).1 η.2) ?_ ?_
  · intro hn
    obtain ⟨v, hv, w, hw, hvw, hzv, hzw⟩ := D.noLoops _ hn
    obtain ⟨Cv, rfl⟩ := D.exists_compSet_eq hv
    obtain ⟨Cw, rfl⟩ := D.exists_compSet_eq hw
    exact hzS ⟨Cv, Cw, fun h ↦ hvw (by rw [h]), D.pt_mem_compSet_iff.1 hzv,
      D.pt_mem_compSet_iff.1 hzw⟩
  · intro y hy hyη
    obtain ⟨y₀, rfl⟩ := D.exists_pt_eq hy
    have hy₀ : y₀ ⤳ η := (D.isInducing_pt.specializes_iff).1 hyη
    have hsub : i.1 ⊆ closure {y₀} := by
      rw [← hgen.def]
      exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hy₀))
        isClosed_closure
    have heq := i.2.2 isIrreducible_singleton.closure hsub
    have hy₀gen : IsGenericPoint y₀ i.1 := by
      rw [IsGenericPoint]
      exact le_antisymm heq hsub
    rw [hy₀gen.eq hgen]
  · rw [WData.map_pt]
    exact D'.isNodePt_of_mem_S SemistableReduction.nodeOfTwoComponents hψ

include D D' in
/-- **Morphisms of W-model levels reflect nodes.** -/
theorem reflectsSpecial :
    ReflectsSpecial (curveConfig X.Lv.Z hdim) (curveConfig Y.Lv.Z hdim')
      (specialFibreMap m.ψ m.ψ_toSpec) := by
  intro i z hz hzS hψ
  rw [map_eta_eq m D D' hdim hdim' i hz hzS hψ]
  exact hψ

end WData

variable {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- **Morphisms between universal Galois objects over W-model levels reflect nodes.** -/
theorem UData.reflectsNodes_of_wData [IsDiscreteValuationRing O] {X Y : TempObj O R A}
    (Dx : UData Ω X) (Dy : UData Ω Y) (F : X ⟶ Y) (Wx : WData x Dx.Lv) (Wy : WData x Dy.Lv) :
    Dx.ReflectsNodes Dy F :=
  WData.reflectsSpecial (X := universalObj Dx.Lv Dx.hdim Dx.z₀)
    (Y := universalObj Dy.Lv Dy.hdim Dy.z₀) (Dx.e.inv ≫ F ≫ Dy.e.hom) Wx Wy Dx.hdim Dy.hdim

section Andre

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)

omit [CharZero K] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  [PerfectField (IsLocalRing.ResidueField O)] [IsDomain R] [Subsingleton A] [IsAlgClosed Ω] in
/-- **M1 for André's tower: all transition maps reflect nodes.** -/
theorem reflectsNodes_curveData {p q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}
    (f : p ⟶ q) : ReflectsNodes V hV (curveData V hV hR) f :=
  UData.reflectsNodes_of_wData _ _ _ (WData.nonempty_of_isW (curveData_isW V hV hR p)).some
    (WData.nonempty_of_isW (curveData_isW V hV hR q)).some

variable [Finite A] [SMulCommClass A K R]

/-- **C11 + M1: André's tree tower is functorial on all levels** (unconditionally). -/
theorem isFunctorial_andreTower_galW : (andreTower (R := R) (A := A) V hV hp hR).IsFunctorial :=
  isFunctorial_andreTower V hV hp hR fun f ↦ reflectsNodes_curveData V hV hR f

/-- **[SemiAnbd] Thm. 3.7(iii) for André's group (system form), from estrangement alone**: every
nontrivial compact subgroup of André's group fixes a compatible system of vertices of the trees
of all levels. -/
theorem exists_le_stab_andreTower_of_estranged
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s :=
  exists_le_stab_andreTower V hV hp hR (fun f ↦ reflectsNodes_curveData V hV hR f) hE H hH1 hH

/-- **The same for a subgroup** `Δ` of André's group (e.g. the geometric subgroup): if the tower
pulled back to `Δ` is estranged, every nontrivial compact subgroup of `Δ` fixes a compatible
system of vertices. -/
theorem exists_le_stab_andreTower_of_le_estranged (Δ : Subgroup (andreGroup O R A V hV))
    (hE : ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged)
    (H : Subgroup (andreGroup O R A V hV)) (hHΔ : H ≤ Δ) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s :=
  exists_le_stab_andreTower_of_le V hV hp hR (fun f ↦ reflectsNodes_curveData V hV hR f) Δ hE H
    hHΔ hH1 hH

/-- **[SemiAnbd] Thm. 3.7(iv) for André's group (system form), from estrangement alone**: a
nontrivial maximal compact subgroup of André's group is the stabilizer of a system. -/
theorem exists_eq_stab_of_maximal_of_estranged
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV)))
    (hmax : ∀ H' : Subgroup (andreGroup O R A V hV), IsCompact (H' : Set (andreGroup O R A V hV)) →
      H ≤ H' → H' = H) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H = TreeTower.stab s :=
  exists_eq_stab_of_maximal V hV hp hR (fun f ↦ reflectsNodes_curveData V hV hR f) hE H hH1 hH
    hmax

/-- **`PSCAdj` for André's group** under estrangement, no branch inversions and nontrivial
edge-like subgroups. -/
theorem pscAdj_andreTower_of_estranged
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (hB : (andreTower (R := R) (A := A) V hV hp hR).NoBranchSwap)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj :=
  pscAdj_andreTower V hV hp hR (fun f ↦ reflectsNodes_curveData V hV hR f) hE hB hedge

/-- **CG3' for André's group** under estrangement, no branch inversions and nontrivial edge-like
subgroups (on both sides). -/
theorem isGraphic_iff_andreTower_of_estranged {Γ' : Type*} [Group Γ'] {J' : Type*} [Category J']
    [IsCofilteredOrEmpty J'] {T' : TreeTower Γ' J'} {α : andreGroup O R A V hV ≃* Γ'}
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (hB : (andreTower (R := R) (A := A) V hV hp hR).NoBranchSwap)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥)
    (hT' : T'.IsFunctorial) (hE' : T'.Estranged) (hB' : T'.NoBranchSwap)
    (hedge' : ∀ e : T'.Sys, (∀ j, ∃ (k : J') (_ : k ⟶ j), T'.kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    TreeTower.IsGraphic (andreTower (R := R) (A := A) V hV hp hR) T' α ↔
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α :=
  isGraphic_iff_andreTower V hV hp hR (fun f ↦ reflectsNodes_curveData V hV hR f) hE hB hedge
    hT' hE' hB' hedge'

end Andre

end

end TemperedFundamentalGroups
