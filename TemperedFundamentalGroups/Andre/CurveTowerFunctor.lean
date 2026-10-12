/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.CurveTower
import TemperedFundamentalGroups.SemiAnbd.TreeTowerCompact

/-!
# Functoriality of the tree tower of a curve (Blueprint §12.5, C7–C9)

The maps of vertices of the tree tower of a curve (`stageTower`, `curveTower`, `andreTower`) send
a vertex to the tree coordinate of the image of its canonical point. They are not functorial in
general: a transition map may contract a component to a closed non-special point, and then the
image of the generic point is not the canonical point of its vertex. We show:

* **`CurveConfig.finite_neighborSet`** (**C7**): the tree of a configuration with finitely many
  components is locally finite; hence so are the trees of the stage tower
  (`finite_neighborSet_stageTower`).
* **`stageTower_map_id`**, **`stageTower_map_comp_eq_or_adj`** (**C8**): the maps along identities
  are identities, and the maps along composites differ from the composites of the maps by at most
  one step (`CurveConfig.vmap_comp_eq_or_adj`: the image of a point of a sheet over a component is
  a specialisation of the image of the generic point).
* **`stageTower_map_comp`**, **`isFunctorial_restrict_stageTower`** (**C8**): along
  *non-contracting* morphisms (`NonContracting`: the map of tree coverings sends canonical points
  to canonical points) the maps compose, so the tower restricted to any subsystem of levels with
  non-contracting transition maps is functorial.
* **`finite_map_of_isCompact`**, **`finite_map_of_isCompact_andre`**: compact subgroups of
  `lim Π_Lv` and of André's group have finite images in the (discrete) stage groups.
* **`exists_le_stab_restrict_andreTower`** (**C9**, W6 for curves, conditional): if André's tower
  restricted to a cofiltered subsystem of non-contracting levels is estranged, every nontrivial
  compact subgroup of André's group fixes a compatible system of vertices of that subsystem;
  **`pscAdj_restrict_andreTower`**: under estrangement, no branch inversions and nontrivial
  edge-like subgroups, the restricted tower satisfies `PSCAdj` (so CG3 applies).

Neither the existence of a cofinal subsystem of non-contracting levels (semistable models
refining each other: simultaneous semistable reduction) nor estrangement is proved here.
-/

universe u v u' v'

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology TopologicalSpace

namespace TemperedFundamentalGroups

namespace CurveConfig

variable {Z : Type u} [TopologicalSpace Z] {ι : Type v} {K : CurveConfig Z ι} {r : ι}

/-- **C7**: the tree of a configuration with finitely many components is locally finite. -/
theorem finite_neighborSet [Finite ι] (t : K.Tree r) :
    ((treeGraph K r).neighborSet t).Finite := by
  -- the children of `t` are determined by their last vertex
  have hinj : Set.InjOn (fun t' : K.Tree r ↦ t'.1.head?) {t' | t'.1.tail = t.1} := by
    rintro ⟨la, pa⟩ ha ⟨lb, pb⟩ hb h
    simp only [Set.mem_setOf_eq] at ha hb h
    have hla := pa.ne_nil
    have hlb := pb.ne_nil
    apply Tree.ext
    change la = lb
    cases la <;> cases lb <;> simp_all
  have hch : {t' : K.Tree r | t'.1.tail = t.1}.Finite := by
    refine Set.Finite.of_finite_image ?_ hinj
    refine ((Set.finite_range (fun i : ι ↦ some (Sum.inl i : ι ⊕ Z))).union
      (K.finite_S.image (fun s ↦ some (Sum.inr s : ι ⊕ Z)))).subset ?_
    rintro _ ⟨a, -, rfl⟩
    rcases a.2.head_cases with ⟨i, hi⟩ | ⟨s, hs, hsh⟩
    · exact .inl ⟨i, hi.symm⟩
    · exact .inr ⟨s, hs, hsh.symm⟩
  have hpar : {t' : K.Tree r | t'.1 = t.1.tail}.Subsingleton := fun a ha b hb ↦
    Tree.ext (ha.trans hb.symm)
  refine (hpar.finite.union hch).subset fun t' ht' ↦ ?_
  rcases ht' with h | h
  · exact .inr h
  · exact .inl h.symm

variable (hη : ∀ i, K.η i ∉ K.S)
  {Z' : Type u'} [TopologicalSpace Z'] {ι' : Type v'} {K' : CurveConfig Z' ι'} {r' : ι'}
  {Z'' : Type*} [TopologicalSpace Z''] {ι'' : Type*} {K'' : CurveConfig Z'' ι''} {r'' : ι''}

/-- **C8**: the map of vertices of a composite differs from the composite of the maps of vertices
by at most one step: the image of a point of a sheet over a component is a specialisation of the
image of the canonical (generic) point. -/
theorem vmap_comp_eq_or_adj (hη' : ∀ j, K'.η j ∉ K'.S) (f : K.Cover r → K'.Cover r')
    {g : K'.Cover r' → K''.Cover r''} (hg : Continuous g) (t : K.Tree r) :
    vmap hη (g ∘ f) t = vmap hη' g (vmap hη f t) ∨
      (vmap hη (g ∘ f) t).Adj (vmap hη' g (vmap hη f t)) := by
  change (g (f (canon hη t))).1.2 = (g (canon hη' (f (canon hη t)).1.2)).1.2 ∨
    (g (f (canon hη t))).1.2.Adj (g (canon hη' (f (canon hη t)).1.2)).1.2
  set y := f (canon hη t)
  rcases y.1.2.2.head_cases with ⟨i, hi⟩ | ⟨s, -, hs⟩
  · rcases Cover.eq_or_adj_of_specializes ((canon_specializes_of_inl hη' hi).map hg) with h | h
    · exact .inl h.symm
    · exact .inr h
  · rw [← eq_canon_of_inr hη' hs]
    exact .inl rfl

end CurveConfig

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma fibreMap_id_apply {X : TempObj O R A} (x : Fibre Ω V hV X) :
    fibreMap V hV (𝟙 X) x = x := by
  induction x using Quotient.inductionOn
  rfl

namespace UData

variable {X Y W : TempObj O R A} (Dx : UData Ω X) (Dy : UData Ω Y) (Dw : UData Ω W)

/-- Morphisms with the same map of fibres induce the same map of vertices. -/
lemma vmapHom_eq_of_fibreMap_eq {F F' : X ⟶ Y} (h : fibreMap V hV F = fibreMap V hV F') :
    Dx.vmapHom Dy F = Dx.vmapHom Dy F' := by
  have hfib : fibreMap V hV (Dx.e.inv ≫ F ≫ Dy.e.hom) =
      fibreMap V hV (Dx.e.inv ≫ F' ≫ Dy.e.hom) := by
    funext x
    rw [fibreMap_comp_apply, fibreMap_comp_apply, fibreMap_comp_apply V hV Dx.e.inv,
      fibreMap_comp_apply V hV F', h]
  have htm : uTreeMap (Dx.e.inv ≫ F ≫ Dy.e.hom) = uTreeMap (Dx.e.inv ≫ F' ≫ Dy.e.hom) :=
    treeMap_eq_of_fibreMap_eq V hV Dx.hidem hfib
  unfold vmapHom
  rw [htm]

/-- An endomorphism acting trivially on fibres induces the identity on vertices. -/
lemma vmapHom_eq_id {F : X ⟶ X} (h : fibreMap V hV F = id) : Dx.vmapHom Dx F = id := by
  rw [Dx.vmapHom_eq_of_fibreMap_eq V hV Dx (F' := 𝟙 X)
    (by funext x; rw [h, fibreMap_id_apply]; rfl)]
  unfold vmapHom
  rw [Category.id_comp, Iso.inv_hom_id, uTreeMap_id]
  rfl

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma uTreeMap_comp_conj (F : X ⟶ Y) (G : Y ⟶ W) :
    uTreeMap (Dx.e.inv ≫ (F ≫ G) ≫ Dw.e.hom) =
      uTreeMap (Dy.e.inv ≫ G ≫ Dw.e.hom) ∘ uTreeMap (Dx.e.inv ≫ F ≫ Dy.e.hom) := by
  rw [← uTreeMap_comp]
  congr 1
  simp

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **C8**: the map of vertices of a composite differs from the composite of the maps by at most
one step. -/
theorem vmapHom_comp_eq_or_adj (F : X ⟶ Y) (G : Y ⟶ W) (t : Dx.Tr) :
    Dx.vmapHom Dw (F ≫ G) t = Dy.vmapHom Dw G (Dx.vmapHom Dy F t) ∨
      (Dx.vmapHom Dw (F ≫ G) t).Adj (Dy.vmapHom Dw G (Dx.vmapHom Dy F t)) := by
  unfold vmapHom
  rw [uTreeMap_comp_conj Dx Dy Dw]
  exact vmap_comp_eq_or_adj _ (hηU Dy.hdim) _ (continuous_uTreeMap _) t

/-- A morphism of Galois objects is **non-contracting** if its map of tree coverings sends
canonical points to canonical points (no component is mapped to a closed non-special point). -/
def NonContracting (F : X ⟶ Y) : Prop :=
  PreservesCanon (hηU Dx.hdim) (hηU Dy.hdim) (uTreeMap (Dx.e.inv ≫ F ≫ Dy.e.hom))

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **C8**: along non-contracting morphisms the maps of vertices compose. -/
theorem vmapHom_comp {F : X ⟶ Y} (hF : Dx.NonContracting Dy F) (G : Y ⟶ W) :
    Dx.vmapHom Dw (F ≫ G) = Dy.vmapHom Dw G ∘ Dx.vmapHom Dy F := by
  unfold vmapHom
  rw [uTreeMap_comp_conj Dx Dy Dw]
  exact vmap_comp_of_preservesCanon _ _ _ hF

end UData

section Tower

variable {𝒢 : ObjectProperty (TempObj O R A)}
  (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
  (D : ∀ p : PtGal (tempFibre O R A V hV) 𝒢, UData Ω p.G)

/-- A pointed morphism is non-contracting. -/
def NonContracting {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q) : Prop :=
  (D p).NonContracting (D q) (ptHomMor V hV f)

lemma fibreMap_ptHomMor_id (p : PtGal (tempFibre O R A V hV) 𝒢) :
    fibreMap V hV (ptHomMor V hV (𝟙 p)) = id :=
  funext fun x ↦ fibreMap_ptHomMor V hV (𝟙 p) x

lemma fibreMap_ptHomMor_comp {p q r : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q)
    (g : q ⟶ r) :
    fibreMap V hV (ptHomMor V hV (f ≫ g)) = fibreMap V hV (ptHomMor V hV f ≫ ptHomMor V hV g) := by
  funext x
  rw [fibreMap_ptHomMor, fibreMap_comp_apply, fibreMap_ptHomMor, fibreMap_ptHomMor]
  rfl

/-- **C8**: the maps of the tree tower of a curve along identities are identities. -/
theorem stageTower_map_id (p : PtGal (tempFibre O R A V hV) 𝒢) (x : (D p).Tr) :
    (stageTower V hV hgal hrig D).map (𝟙 p) x = x :=
  congrFun ((D p).vmapHom_eq_id V hV (fibreMap_ptHomMor_id V hV p)) x

/-- **C8**: the maps of the tree tower of a curve along composites differ from the composites of
the maps by at most one step. -/
theorem stageTower_map_comp_eq_or_adj {p q r : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q)
    (g : q ⟶ r) (x : (D p).Tr) :
    (stageTower V hV hgal hrig D).map (f ≫ g) x =
        (stageTower V hV hgal hrig D).map g ((stageTower V hV hgal hrig D).map f x) ∨
      ((stageTower V hV hgal hrig D).graph r).Adj ((stageTower V hV hgal hrig D).map (f ≫ g) x)
        ((stageTower V hV hgal hrig D).map g ((stageTower V hV hgal hrig D).map f x)) := by
  change (D p).vmapHom (D r) (ptHomMor V hV (f ≫ g)) x = _ ∨
    ((D p).vmapHom (D r) (ptHomMor V hV (f ≫ g)) x).Adj _
  rw [(D p).vmapHom_eq_of_fibreMap_eq V hV (D r) (fibreMap_ptHomMor_comp V hV f g)]
  exact (D p).vmapHom_comp_eq_or_adj (D q) (D r) _ _ x

/-- **C8**: along non-contracting morphisms the maps of the tree tower of a curve compose. -/
theorem stageTower_map_comp {p q r : PtGal (tempFibre O R A V hV) 𝒢} {f : p ⟶ q}
    (hf : NonContracting V hV D f) (g : q ⟶ r) (x : (D p).Tr) :
    (stageTower V hV hgal hrig D).map (f ≫ g) x =
      (stageTower V hV hgal hrig D).map g ((stageTower V hV hgal hrig D).map f x) := by
  change (D p).vmapHom (D r) (ptHomMor V hV (f ≫ g)) x = _
  rw [(D p).vmapHom_eq_of_fibreMap_eq V hV (D r) (fibreMap_ptHomMor_comp V hV f g)]
  exact congrFun ((D p).vmapHom_comp (D q) (D r) hf _) x

/-- **C8**: the tree tower of a curve restricted to a subsystem of levels with non-contracting
transition maps is functorial. -/
theorem isFunctorial_restrict_stageTower {J' : Type*} [Category J']
    (F : J' ⥤ PtGal (tempFibre O R A V hV) 𝒢) (hF : ∀ {j k : J'} (f : j ⟶ k),
      NonContracting V hV D (F.map f)) :
    ((stageTower V hV hgal hrig D).restrict F).IsFunctorial :=
  TreeTower.isFunctorial_restrict F (fun _ x ↦ stageTower_map_id V hV hgal hrig D _ x)
    (fun f _ x ↦ stageTower_map_comp V hV hgal hrig D (hF f) _ x)

/-- **C7**: the trees of the tree tower of a curve are locally finite. -/
theorem finite_neighborSet_stageTower (p : PtGal (tempFibre O R A V hV) 𝒢)
    (v : (stageTower V hV hgal hrig D).V p) :
    (((stageTower V hV hgal hrig D).graph p).neighborSet v).Finite :=
  finite_neighborSet (K := curveConfig (D p).Lv.Z (D p).hdim) v

/-- Compact subgroups of `lim Π_Lv` have finite images in the (discrete) stage groups. -/
theorem finite_map_of_isCompact (H : Subgroup (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig))
    (hH : IsCompact (H : Set (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig)))
    (p : PtGal (tempFibre O R A V hV) 𝒢) :
    Finite (H.map ((stageTower V hV hgal hrig D).ρ p)) := by
  have hc : Continuous fun γ : limGroup (tempFibre O R A V hV) 𝒢 hgal hrig ↦ γ.1 p :=
    (continuous_apply p).comp continuous_subtype_val
  have hfin := (hH.image hc).finite_of_discrete
  have h : (SetLike.coe (H.map ((stageTower V hV hgal hrig D).ρ p))).Finite := by
    rw [Subgroup.coe_map]; exact hfin
  exact h.to_subtype

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

/-- Compact subgroups of André's group have finite images in the stage groups. -/
theorem finite_map_of_isCompact_andre (H : Subgroup (andreGroup O R A V hV))
    (hH : IsCompact (H : Set (andreGroup O R A V hV)))
    (p : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)) :
    Finite (H.map ((andreTower (R := R) (A := A) V hV hp hR).ρ p)) := by
  set φ := (andreGroupHomeoLim (R := R) (A := A) V hV hp hR)
  have hH' : IsCompact (SetLike.coe (H.map φ.toMulEquiv.toMonoidHom)) := by
    rw [Subgroup.coe_map]; exact hH.image φ.continuous
  have := finite_map_of_isCompact V hV _ _ (curveData V hV hR) _ hH' p
  rwa [Subgroup.map_map] at this

/-- **C9, W6 for André's group (conditional)**: if André's tree tower restricted to a cofiltered
subsystem `F` of levels with non-contracting transition maps is estranged, every nontrivial
compact subgroup of André's group fixes a compatible system of vertices of the subsystem. -/
theorem exists_le_stab_restrict_andreTower {J' : Type*} [Category J'] [IsCofilteredOrEmpty J']
    (F : J' ⥤ PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (hF : ∀ {j k : J'} (f : j ⟶ k), NonContracting V hV (curveData V hV hR) (F.map f))
    (hE : ((andreTower (R := R) (A := A) V hV hp hR).restrict F).Estranged)
    (H : Subgroup (andreGroup O R A V hV)) (hH1 : H ≠ ⊥)
    (hH : IsCompact (H : Set (andreGroup O R A V hV))) :
    ∃ s : ((andreTower (R := R) (A := A) V hV hp hR).restrict F).Sys, H ≤ TreeTower.stab s := by
  have h := isFunctorial_restrict_stageTower V hV
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 (curveData V hV hR) F hF
  have hT : ((andreTower (R := R) (A := A) V hV hp hR).restrict F).IsFunctorial :=
    ⟨h.map_id, h.map_comp⟩
  exact TreeTower.exists_le_stab_of_estranged hT hE
    (fun j v ↦ finite_neighborSet_stageTower V hV
      (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
      (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 (curveData V hV hR) (F.obj j) v)
    H hH1
    (fun j ↦ finite_map_of_isCompact_andre V hV hp hR H hH (F.obj j))

/-- **C9, `PSCAdj` for André's group (conditional)**: André's tree tower restricted to a
cofiltered subsystem of non-contracting levels satisfies the adjacency hypothesis of CG3 as soon
as it is estranged, has no branch inversions and has nontrivial edge-like subgroups. -/
theorem pscAdj_restrict_andreTower {J' : Type*} [Category J'] [IsCofilteredOrEmpty J']
    (F : J' ⥤ PtGal (tempFibre O R A V hV) (galW O R A Ω hR))
    (hF : ∀ {j k : J'} (f : j ⟶ k), NonContracting V hV (curveData V hV hR) (F.map f))
    (hE : ((andreTower (R := R) (A := A) V hV hp hR).restrict F).Estranged)
    (hB : ((andreTower (R := R) (A := A) V hV hp hR).restrict F).NoBranchSwap)
    (hedge : ∀ e : ((andreTower (R := R) (A := A) V hV hp hR).restrict F).Sys,
      (∀ j, ∃ (k : J') (_ : k ⟶ j),
        ((andreTower (R := R) (A := A) V hV hp hR).restrict F).kind k (e.1 k) = false) →
      TreeTower.stab e ≠ ⊥) :
    ((andreTower (R := R) (A := A) V hV hp hR).restrict F).PSCAdj := by
  have h := isFunctorial_restrict_stageTower V hV
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).1
    (galoisLimitData_galW (R := R) (A := A) V hV hp hR).2.2 (curveData V hV hR) F hF
  exact TreeTower.pscAdj_of_estranged ⟨h.map_id, h.map_comp⟩ hE hB hedge

end Andre

end

end TemperedFundamentalGroups
