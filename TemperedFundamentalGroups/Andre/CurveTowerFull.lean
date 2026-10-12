/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.CurveTowerFunctor
import TemperedFundamentalGroups.SemiAnbd.CombGC

/-!
# Functoriality of the whole tree tower of a curve from node reflection (Blueprint §12.5, C11)

The maps of vertices of the tree tower of a curve fail to compose only in one configuration
(`CurveConfig.vmap_comp_eq_or_adj`): a point `y` of a sheet over a component `C` of a level
whose image under the next transition map is a node, while the image of the generic point of `C`
is not. Here `y` is the image of a canonical point (a component contracted to a smooth point of
`C`). Excluding this configuration — **node reflection**: *a point on a single component `C` of
the special fibre maps to a node only if the generic point of `C` does* (`ReflectsSpecial`) —
makes the maps preserve sheets, hence compose, along **all** morphisms, with no restriction to a
subsystem of non-contracting levels (contracting components onto points, even onto nodes, is
allowed). For morphisms of semistable models node reflection is a local statement of commutative
algebra (Blueprint §12.5, C11: going-down at points isolated in their fibres over a normal node);
it is the hypothesis `hN` below and is not proved here.

* **`CurveConfig.preservesSheets_of_reflectsSpecial`**: a continuous map of tree coverings over a
  map `ψ` of the underlying spaces reflecting special points in this sense preserves sheets.
* `uZMap`, **`UData.ReflectsNodes`**, `UData.vmapHom_comp_of_reflectsNodes`,
  **`stageTower_map_comp_of_reflectsNodes`**, **`isFunctorial_stageTower`**: the tree tower of a
  curve is functorial on all levels if every morphism reflects nodes.
* For André's group (scheme case, Theorem A hypotheses): **`isFunctorial_andreTower`**;
  **`exists_le_stab_andreTower`** ([SemiAnbd] Thm. 3.7(iii), system form): under node reflection
  and estrangement, every nontrivial compact subgroup of André's group fixes a compatible system
  of vertices of the trees of **all** levels; **`exists_eq_stab_of_maximal`** (3.7(iv), system
  form): nontrivial maximal compact subgroups are stabilizers of systems;
  **`pscAdj_andreTower`**, **`isGraphic_iff_andreTower`** (CG3' for André's group).
* `TreeTower.not_HI_of_le_fixAt` (C10, the bridge mechanism: a stabilizer contained in the
  stabilizer of a neighbour at all deep levels violates `(HI)`) and `TreeTower.isVert_of_stab_le`
  (an `(HI)` system whose stabilizer lies in a verticial subgroup is verticial: since curve
  transition maps do not preserve colours, decomposition groups of components lying over a node
  of a lower level are compact but in no verticial subgroup, so "verticial" must be read as
  "stabilizer of a system" for curves).
-/

universe u v u' v'

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology TopologicalSpace

namespace TemperedFundamentalGroups

/-! ### The abstract obstruction lemmas (C10) -/

namespace TreeTower

variable {Γ : Type*} [Group Γ] {J : Type*} [Category J] {T : TreeTower Γ J}

/-- **C10, the bridge mechanism**: if below some level `j` the stabilizer of a system always fixes
some neighbour of the system, the system does not satisfy `(HI)` (the decomposition group of a
semistable bridge in a tame tower is the inertia group of its nodes). -/
theorem not_HI_of_le_fixAt {s : T.Sys} (j : J)
    (h : ∀ (k : J) (_ : k ⟶ j), ∃ w, (T.graph k).Adj (s.1 k) w ∧ stab s ≤ T.fixAt k w) :
    ¬ T.HI s := by
  intro hs
  obtain ⟨k, f, hk⟩ := hs 1 j
  obtain ⟨w, hw, hle⟩ := h k f
  have h1 : (T.fixAt k w).relIndex (stab s) = 1 := Subgroup.relIndex_eq_one.2 hle
  rcases hk w hw with h0 | h0 <;> omega

/-- An `(HI)` system whose stabilizer lies in a verticial subgroup is itself verticial (W4). -/
theorem isVert_of_stab_le {s s' : T.Sys} (hs : T.HI s) (hle : stab s ≤ stab s')
    (hs' : IsVert s') : IsVert s := by
  rw [eq_of_stab_le hs hle]
  exact hs'

end TreeTower

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}
  {Z' : Type u'} [TopologicalSpace Z'] {ι' : Type v'} {K' : CurveConfig Z' ι'} {r' : ι'}

variable (K K') in
/-- **Node reflection** for a map `ψ : Z → Z'`: a point on a single component `C` (not special)
goes to a special point only if the generic point of `C` does (i.e. `C` is contracted onto that
special point). -/
def ReflectsSpecial (ψ : Z → Z') : Prop :=
  ∀ i z, z ∈ K.C i → z ∉ K.S → ψ z ∈ K'.S → ψ (K.η i) ∈ K'.S

/-- The colour of the sheet of a point of the tree covering: a component exactly when the point
is not special. -/
lemma Cover.kind_eq_true_iff (y : K.Cover r) : Tree.kind y.1.2 = true ↔ y.1.1 ∉ K.S := by
  rcases y.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, hsS, hs⟩
  · rw [Tree.kind_eq_true_iff.2 ⟨i, hi⟩]
    exact ⟨fun _ ↦ (Cover.mem_piece_inl hi).2, fun _ ↦ rfl⟩
  · rw [Tree.kind_eq_false_iff.2 ⟨s, hs⟩, Cover.eq_of_inr hs]
    simp [hsS]

/-- **C11: continuous maps of tree coverings over a node-reflecting map preserve sheets.** -/
theorem preservesSheets_of_reflectsSpecial (hη : ∀ i, K.η i ∉ K.S) {f : K.Cover r → K'.Cover r'}
    {ψ : Z → Z'} (hfψ : ∀ x, (f x).1.1 = ψ x.1.1) (hR : ReflectsSpecial K K' ψ)
    (hf : Continuous f) : PreservesSheets hη f := by
  intro x
  rcases x.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · have hsp := (canon_specializes_of_inl hη hi).map hf
    rcases Cover.eq_or_adj_of_specializes hsp with h | h
    · exact h.symm
    · exfalso
      have hx := Cover.mem_piece_inl hi
      have hc : (f (canon hη x.1.2)).1.1 = ψ (K.η i) := by
        rw [hfψ]; change ψ (canonPt x.1.2) = _; rw [canonPt_of_inl hi]
      have hzz : ψ (K.η i) ⤳ ψ x.1.1 := by
        rw [← hc, ← hfψ]
        exact (specializes_prod.1 ((subtype_specializes_iff _ _).1 hsp)).1
      refine Tree.kind_ne_of_adj h ?_
      by_cases hS : ψ (K.η i) ∈ K'.S
      · have heq : ψ x.1.1 = ψ (K.η i) :=
          hzz.mem_closed (K'.isClosed_singleton _ hS) rfl
        have h₁ : Tree.kind (f x).1.2 = false := by
          rw [Bool.eq_false_iff, ne_eq, Cover.kind_eq_true_iff, hfψ, heq, not_not]
          exact hS
        have h₂ : Tree.kind (f (canon hη x.1.2)).1.2 = false := by
          rw [Bool.eq_false_iff, ne_eq, Cover.kind_eq_true_iff, hc, not_not]
          exact hS
        rw [h₁, h₂]
      · have h₁ : Tree.kind (f x).1.2 = true := by
          rw [Cover.kind_eq_true_iff, hfψ]
          exact fun h ↦ hS (hR i _ hx.1 hx.2 h)
        have h₂ : Tree.kind (f (canon hη x.1.2)).1.2 = true := by
          rw [Cover.kind_eq_true_iff, hc]
          exact hS
        rw [h₁, h₂]
  · conv_lhs => rw [eq_canon_of_inr hη hs]
    rfl

end CurveConfig

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

section ZMap

variable {Lv Lv' : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H] [NoetherianSpace Lv.Z]
  [T0Space Lv.Z] [QuasiSober Lv.Z] {hdim : topologicalKrullDim Lv.Z ≤ 1} {z₀ : Lv.Z}
  [Finite Lv'.L.H] [Subsingleton Lv'.L.H] [NoetherianSpace Lv'.Z] [T0Space Lv'.Z]
  [QuasiSober Lv'.Z] {hdim' : topologicalKrullDim Lv'.Z ≤ 1} {z₀' : Lv'.Z}

/-- The map of special fibres of a morphism of universal Galois objects. -/
def uZMap (F : universalObj Lv hdim z₀ ⟶ universalObj Lv' hdim' z₀') : Lv.Z → Lv'.Z := fun z ↦
  ⟨F.ψ (z.1 : Lv.c.scheme), by
    have h := z.2
    rw [mem_specialFibre] at h ⊢
    change (F.ψ ≫ (universalObj Lv' hdim' z₀').Lv.c.toSpec) z.1 = _
    rw [F.ψ_toSpec]
    exact h⟩

omit [Subsingleton Lv.L.H] in
lemma uTreeMap_fst_eq (F : universalObj Lv hdim z₀ ⟶ universalObj Lv' hdim' z₀')
    (x : universalCovering Lv.Z hdim z₀) : (uTreeMap F x).1.1 = uZMap F x.1.1 :=
  Subtype.ext (uTreeMap_spec F x)

end ZMap

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace UData

variable {X Y W : TempObj O R A} (Dx : UData Ω X) (Dy : UData Ω Y) (Dw : UData Ω W)

/-- A morphism of Galois objects **reflects nodes** if its map of special fibres (between the
models of the universal objects) is node-reflecting (`ReflectsSpecial`). -/
def ReflectsNodes (F : X ⟶ Y) : Prop :=
  ReflectsSpecial (curveConfig Dx.Lv.Z Dx.hdim) (curveConfig Dy.Lv.Z Dy.hdim)
    (uZMap (Dx.e.inv ≫ F ≫ Dy.e.hom))

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- Node-reflecting morphisms preserve sheets of the tree coverings. -/
lemma preservesSheets_of_reflectsNodes {F : X ⟶ Y} (hF : Dx.ReflectsNodes Dy F) :
    PreservesSheets (hηU Dx.hdim) (uTreeMap (Dx.e.inv ≫ F ≫ Dy.e.hom)) :=
  preservesSheets_of_reflectsSpecial (hηU Dx.hdim)
    (uTreeMap_fst_eq _) hF (continuous_uTreeMap _)

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **C11**: the maps of vertices compose along `F ≫ G` when `G` reflects nodes. -/
theorem vmapHom_comp_of_reflectsNodes (F : X ⟶ Y) {G : Y ⟶ W} (hG : Dy.ReflectsNodes Dw G) :
    Dx.vmapHom Dw (F ≫ G) = Dy.vmapHom Dw G ∘ Dx.vmapHom Dy F := by
  unfold vmapHom
  rw [uTreeMap_comp_conj Dx Dy Dw]
  exact vmap_comp_of_preservesSheets _ _ _ (Dy.preservesSheets_of_reflectsNodes Dw hG)

end UData

section Tower

variable {𝒢 : ObjectProperty (TempObj O R A)}
  (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
  (D : ∀ p : PtGal (tempFibre O R A V hV) 𝒢, UData Ω p.G)

/-- A pointed morphism reflects nodes. -/
def ReflectsNodes {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q) : Prop :=
  (D p).ReflectsNodes (D q) (ptHomMor V hV f)

/-- **C11**: the maps of the tree tower of a curve compose along `f ≫ g` if `g` reflects nodes. -/
theorem stageTower_map_comp_of_reflectsNodes {p q r : PtGal (tempFibre O R A V hV) 𝒢}
    (f : p ⟶ q) {g : q ⟶ r} (hg : ReflectsNodes V hV D g) (x : (D p).Tr) :
    (stageTower V hV hgal hrig D).map (f ≫ g) x =
      (stageTower V hV hgal hrig D).map g ((stageTower V hV hgal hrig D).map f x) := by
  change (D p).vmapHom (D r) (ptHomMor V hV (f ≫ g)) x = _
  rw [(D p).vmapHom_eq_of_fibreMap_eq V hV (D r) (fibreMap_ptHomMor_comp V hV f g)]
  exact congrFun ((D p).vmapHom_comp_of_reflectsNodes (D q) (D r) _ hg) x

/-- **C11: the tree tower of a curve is functorial on all levels** if every morphism of levels
reflects nodes. -/
theorem isFunctorial_stageTower
    (hN : ∀ {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q), ReflectsNodes V hV D f) :
    (stageTower V hV hgal hrig D).IsFunctorial where
  map_id p x := stageTower_map_id V hV hgal hrig D p x
  map_comp f g x := stageTower_map_comp_of_reflectsNodes V hV hgal hrig D f (hN g) x

end Tower

section Andre

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
  [Finite A] [SMulCommClass A K R]

/-- **C11: André's tree tower is functorial on all levels** if the transition maps reflect
nodes. -/
theorem isFunctorial_andreTower
    (hN : ∀ {p q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ q),
      ReflectsNodes V hV (curveData V hV hR) f) :
    (andreTower (R := R) (A := A) V hV hp hR).IsFunctorial := by
  have h := isFunctorial_stageTower V hV
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 (curveData V hV hR) hN
  exact ⟨h.map_id, h.map_comp⟩

omit [Finite A] [SMulCommClass A K R] in
include hp in
/-- The pointed Galois objects over W-model levels form a cofiltered category. -/
lemma isCofiltered_ptGalW : IsCofiltered (PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :=
  isCofiltered (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.1
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2

/-- **C11, [SemiAnbd] Thm. 3.7(iii) for André's group (system form)**: if the transition maps
reflect nodes and André's tree tower is estranged, every nontrivial compact subgroup of André's
group fixes a compatible system of vertices of the trees of all levels. -/
theorem exists_le_stab_andreTower
    (hN : ∀ {p q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ q),
      ReflectsNodes V hV (curveData V hV hR) f)
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  exact TreeTower.exists_le_stab_of_estranged (isFunctorial_andreTower V hV hp hR hN) hE
    (fun j v ↦ finite_neighborSet_stageTower V hV
      (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
      (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 (curveData V hV hR) j v)
    H hH1 (fun j ↦ finite_map_of_isCompact_andre V hV hp hR H hH j)

/-- **C11, the same for a subgroup** `Δ` of André's group (e.g. the geometric subgroup, the
kernel of the map to `Gal(K̄/K)`, which is where [SemiAnbd] works): if the tower pulled back to
`Δ` is estranged, every nontrivial compact subgroup of `Δ` fixes a compatible system of
vertices. -/
theorem exists_le_stab_andreTower_of_le
    (hN : ∀ {p q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ q),
      ReflectsNodes V hV (curveData V hV hR) f)
    (Δ : Subgroup (andreGroup O R A V hV))
    (hE : ((andreTower (R := R) (A := A) V hV hp hR).comap Δ.subtype).Estranged)
    (H : Subgroup (andreGroup O R A V hV)) (hHΔ : H ≤ Δ) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H ≤ TreeTower.stab s := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  set T := andreTower (R := R) (A := A) V hV hp hR
  have hT := isFunctorial_andreTower V hV hp hR hN
  have hT' : (T.comap Δ.subtype).IsFunctorial := ⟨hT.map_id, hT.map_comp⟩
  have hH1' : H.subgroupOf Δ ≠ ⊥ := by
    rw [Ne, Subgroup.subgroupOf_eq_bot]
    exact fun h ↦ hH1 (disjoint_self.1 (h.mono_right hHΔ))
  have hfin : ∀ j, Finite ((H.subgroupOf Δ).map ((T.comap Δ.subtype).ρ j)) := fun j ↦ by
    have h := finite_map_of_isCompact_andre V hV hp hR H hH j
    have heq : (H.subgroupOf Δ).map ((T.comap Δ.subtype).ρ j) = H.map (T.ρ j) := by
      change (H.subgroupOf Δ).map ((T.ρ j).comp Δ.subtype) = _
      rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_of_le_left hHΔ]
    rw [heq]
    exact h
  obtain ⟨s, hs⟩ := TreeTower.exists_le_stab_of_estranged hT' hE
    (fun j v ↦ finite_neighborSet_stageTower V hV
      (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
      (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 (curveData V hV hR) j v)
    _ hH1' hfin
  refine ⟨(T.comapSys Δ.subtype).symm s, fun g hg ↦ ?_⟩
  have h := hs (show (⟨g, hHΔ hg⟩ : Δ) ∈ H.subgroupOf Δ from hg)
  rw [show s = T.comapSys Δ.subtype ((T.comapSys Δ.subtype).symm s) from
    ((T.comapSys Δ.subtype).apply_symm_apply s).symm, TreeTower.stab_comap] at h
  exact h

/-- **C11, [SemiAnbd] Thm. 3.7(iv) for André's group (system form)**: under the same hypotheses,
a nontrivial maximal compact subgroup of André's group is the stabilizer of a system. -/
theorem exists_eq_stab_of_maximal
    (hN : ∀ {p q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ q),
      ReflectsNodes V hV (curveData V hV hR) f)
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV)))
    (hmax : ∀ H' : Subgroup (andreGroup O R A V hV), IsCompact (H' : Set (andreGroup O R A V hV)) →
      H ≤ H' → H' = H) :
    ∃ s : (andreTower (R := R) (A := A) V hV hp hR).Sys, H = TreeTower.stab s := by
  obtain ⟨s, hs⟩ := exists_le_stab_andreTower V hV hp hR hN hE H hH1 hH
  exact ⟨s, (hmax _ (isCompact_stab_andreTower V hV hp hR s) hs).symm⟩

/-- **C11, `PSCAdj` for André's group**: under node reflection, estrangement, no branch inversions
and nontrivial edge-like subgroups, André's tree tower satisfies the adjacency hypothesis. -/
theorem pscAdj_andreTower
    (hN : ∀ {p q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ q),
      ReflectsNodes V hV (curveData V hV hR) f)
    (hE : (andreTower (R := R) (A := A) V hV hp hR).Estranged)
    (hB : (andreTower (R := R) (A := A) V hV hp hR).NoBranchSwap)
    (hedge : ∀ e : (andreTower (R := R) (A := A) V hV hp hR).Sys,
      (∀ j, ∃ (k : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) (_ : k ⟶ j),
        (andreTower (R := R) (A := A) V hV hp hR).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    (andreTower (R := R) (A := A) V hV hp hR).PSCAdj := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  exact TreeTower.pscAdj_of_estranged (isFunctorial_andreTower V hV hp hR hN) hE hB hedge

/-- **C11, CG3' for André's group**: for an isomorphism `α` of André's group with the group of a
functorial estranged tree tower without branch inversions and with nontrivial edge-like subgroups
(e.g. André's tower of a second curve under the same hypotheses), `α` is graphic if and only if
it is group-theoretically verticial. -/
theorem isGraphic_iff_andreTower {Γ' : Type*} [Group Γ'] {J' : Type*} [Category J']
    [IsCofilteredOrEmpty J'] {T' : TreeTower Γ' J'} {α : andreGroup O R A V hV ≃* Γ'}
    (hN : ∀ {p q : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)} (f : p ⟶ q),
      ReflectsNodes V hV (curveData V hV hR) f)
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
      TreeTower.IsGroupTheoreticallyVerticial (andreTower (R := R) (A := A) V hV hp hR) T' α := by
  haveI := isCofiltered_ptGalW (R := R) (A := A) V hV hp hR
  exact TreeTower.isGraphic_iff_of_estranged (isFunctorial_andreTower V hV hp hR hN) hT' hE hE'
    hB hB' hedge hedge'

end Andre

end

end TemperedFundamentalGroups
