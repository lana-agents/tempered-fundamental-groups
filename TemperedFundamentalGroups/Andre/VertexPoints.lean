/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.CurveTower
import TemperedFundamentalGroups.Andre.GTransitiveAux

/-!
# Points of the special fibre attached to the vertices of the trees (Blueprint §12.5, C6)

Scheme case. Let `D : UData Ω X` exhibit `X` as a universal Galois object over the level `D.Lv`.
Every vertex `t` of the tree `D.Tr` of the dual graph has a **point** `D.vertexPt t` of the
special fibre `D.Lv.Z`: the projection of its canonical point (`CurveConfig.canonPt`).

* `UData.closure_vertexPt_mem`: a vertex of vertex kind gives the generic point of an
  irreducible component; `UData.vertexPt_mem_S`: a vertex of edge kind gives a special point
  (a point on two components); `UData.vertexPt_specializes`: the point of a vertex of vertex kind
  specialises to the points of its neighbours.
* For a morphism `F : X ⟶ Y` of Galois objects: the model map `UData.modelMap` (over `O`,
  compatible with the level map `UData.levelMap` through `j`, `UData.j_modelMap`) and the induced
  map of special fibres `UData.fibreMapZ`, along which the map of trees `vmapHom` lies.
* **`UData.fibreMapZ_vertexPt_of_edge`**: if the image of a vertex of edge kind has edge kind,
  its point maps to the point of the image.
* **`UData.fibreMapZ_vertexPt_of_vertex`** (no contraction at midpoints): if a vertex `t` of
  vertex kind has a neighbour `m` (of edge kind) whose image has edge kind, and the image of `t`
  has vertex kind, then the generic point of the component of `t` maps to the generic point of
  the component of the image of `t`.
* The same statements for the pointed morphisms of the tree towers `stageTower` and
  `curveTower` (`ptModelMap`, `ptLevelMap`, `ptFibreMap`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology TopologicalSpace Set

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig

section Topology

variable {Z : Type u} [TopologicalSpace Z] [T0Space Z]

/-- In a `T₀` space of dimension `≤ 1`, a point `y` of an irreducible component `C` that
specialises to a different point is the generic point of `C`. -/
lemma closure_eq_of_specializes_of_ne (hdim : topologicalKrullDim Z ≤ 1) {C : Set Z}
    (hC : C ∈ irreducibleComponents Z) {y z : Z} (hy : y ∈ C) (hyz : y ⤳ z) (hne : y ≠ z) :
    closure {y} = C := by
  have hCc := isClosed_of_mem_irreducibleComponents C hC
  have hsub : closure {y} ⊆ C := hCc.closure_subset_iff.2 (singleton_subset_iff.2 hy)
  by_contra hyC
  let A : IrreducibleCloseds Z := ⟨closure {z}, isIrreducible_singleton.closure,
    isClosed_closure⟩
  let B : IrreducibleCloseds Z := ⟨closure {y}, isIrreducible_singleton.closure,
    isClosed_closure⟩
  let C' : IrreducibleCloseds Z := ⟨C, hC.1, hCc⟩
  have hAB : A < B := by
    refine lt_of_le_of_ne (show closure {z} ⊆ closure {y} from
      isClosed_closure.closure_subset_iff.2
        (singleton_subset_iff.2 (specializes_iff_mem_closure.1 hyz))) fun h ↦ hne ?_
    exact (inseparable_iff_closure_eq.2 (congrArg SetLike.coe h).symm).eq
  have hBC : B < C' := lt_of_le_of_ne hsub fun h ↦ hyC (congrArg SetLike.coe h)
  exact not_lt_lt_of_topologicalKrullDim_le_one hdim hAB hBC

end Topology

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]

namespace UData

section Points

variable {X : TempObj O R A} (D : UData Ω X)

/-- The configuration of irreducible components of the special fibre of the level of `D`. -/
abbrev config : CurveConfig D.Lv.Z (irreducibleComponents D.Lv.Z) := curveConfig D.Lv.Z D.hdim

/-- **The point of a vertex** of the tree: the projection of its canonical point (the generic
point of its component for a vertex of vertex kind, its special point for one of edge kind). -/
def vertexPt (t : D.Tr) : D.Lv.Z := canonPt t

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma vertexPt_eq_canon (t : D.Tr) : D.vertexPt t = (canon (hηU D.hdim) t).1.1 := rfl

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma vertexPt_of_inl {t : D.Tr} {i : irreducibleComponents D.Lv.Z}
    (hi : t.1.head? = some (.inl i)) : D.vertexPt t = D.config.η i :=
  canonPt_of_inl hi

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma vertexPt_of_inr {t : D.Tr} {s : D.Lv.Z} (hs : t.1.head? = some (.inr s)) :
    D.vertexPt t = s :=
  canonPt_of_inr hs

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- The closure of the generic point of a component is the component. -/
lemma closure_η (i : irreducibleComponents D.Lv.Z) : closure {D.config.η i} = i.1 :=
  i.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents i.1 i.2)

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **The point of a vertex of vertex kind is the generic point of a component.** -/
theorem closure_vertexPt_mem {t : D.Tr} (ht : Tree.kind t = true) :
    closure {D.vertexPt t} ∈ irreducibleComponents D.Lv.Z := by
  obtain ⟨i, hi⟩ := Tree.kind_eq_true_iff.1 ht
  rw [D.vertexPt_of_inl hi, D.closure_η]
  exact i.2

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **The point of a vertex of edge kind is a special point** (it lies on two components). -/
theorem vertexPt_mem_S {t : D.Tr} (ht : Tree.kind t = false) : D.vertexPt t ∈ D.config.S := by
  rcases t.2.head_cases with ⟨i, hi⟩ | ⟨s, hsS, hs⟩
  · rw [Tree.kind_eq_true_iff.2 ⟨i, hi⟩] at ht
    cases ht
  · rwa [D.vertexPt_of_inr hs]

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- The point of a vertex of vertex kind is not special. -/
theorem vertexPt_notMem_S {t : D.Tr} (ht : Tree.kind t = true) : D.vertexPt t ∉ D.config.S := by
  obtain ⟨i, hi⟩ := Tree.kind_eq_true_iff.1 ht
  rw [D.vertexPt_of_inl hi]
  exact hηU D.hdim i

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **The point of a vertex of vertex kind specialises to the points of its neighbours.** -/
theorem vertexPt_specializes {t m : D.Tr} (ht : Tree.kind t = true) (h : t.Adj m) :
    D.vertexPt t ⤳ D.vertexPt m := by
  obtain ⟨i, hi⟩ := Tree.kind_eq_true_iff.1 ht
  exact (canon_specializes (hηU D.hdim) hi h).map
    (continuous_fst.comp continuous_subtype_val)

end Points

section Maps

variable {X Y : TempObj O R A} (Dx : UData Ω X) (Dy : UData Ω Y)

/-- The morphism of universal Galois objects conjugate to `F : X ⟶ Y`. -/
abbrev conjHom (F : X ⟶ Y) :
    universalObj Dx.Lv Dx.hdim Dx.z₀ ⟶ universalObj Dy.Lv Dy.hdim Dy.z₀ :=
  Dx.e.inv ≫ F ≫ Dy.e.hom

/-- **The model map** `𝒯_x ⟶ 𝒯_y` of a morphism `F : X ⟶ Y` (through the identifications with the
universal Galois objects); the map of trees `vmapHom F` lies over it. -/
def modelMap (F : X ⟶ Y) : Dx.Lv.c.scheme ⟶ Dy.Lv.c.scheme := (Dx.conjHom Dy F).ψ

/-- **The level map** `B_y → B_x` of a morphism `F : X ⟶ Y`. -/
def levelMap (F : X ⟶ Y) : Dy.Lv.L.B →ₐ[R] Dx.Lv.L.B := (Dx.conjHom Dy F).φ.f

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- The model map lies over `O`. -/
lemma modelMap_toSpec (F : X ⟶ Y) : Dx.modelMap Dy F ≫ Dy.Lv.c.toSpec = Dx.Lv.c.toSpec :=
  (Dx.conjHom Dy F).ψ_toSpec

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- The model map is compatible with the level map. -/
lemma j_modelMap (F : X ⟶ Y) :
    Dx.Lv.j ≫ Dx.modelMap Dy F =
      Spec.map (CommRingCat.ofHom (Dx.levelMap Dy F : Dy.Lv.L.B →+* Dx.Lv.L.B)) ≫ Dy.Lv.j :=
  (Dx.conjHom Dy F).j_ψ

/-- **The map of special fibres** of a morphism `F : X ⟶ Y`. -/
def fibreMapZ (F : X ⟶ Y) : Dx.Lv.Z → Dy.Lv.Z :=
  specialFibreMap (Dx.modelMap Dy F) (Dx.modelMap_toSpec Dy F)

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma coe_fibreMapZ (F : X ⟶ Y) (z : Dx.Lv.Z) :
    (Dx.fibreMapZ Dy F z : Dy.Lv.c.scheme) = Dx.modelMap Dy F (z : Dx.Lv.c.scheme) := rfl

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma continuous_fibreMapZ (F : X ⟶ Y) : Continuous (Dx.fibreMapZ Dy F) :=
  continuous_specialFibreMap _ _

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma isClosedMap_fibreMapZ (F : X ⟶ Y) : IsClosedMap (Dx.fibreMapZ Dy F) :=
  isClosedMap_specialFibreMap' _ _

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- The map of tree coverings of `F` lies over the map of special fibres. -/
lemma uTreeMap_fst_eq (F : X ⟶ Y) (x : universalCovering Dx.Lv.Z Dx.hdim Dx.z₀) :
    (uTreeMap (Dx.conjHom Dy F) x).1.1 = Dx.fibreMapZ Dy F x.1.1 :=
  Subtype.ext (uTreeMap_spec _ x)

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma vmapHom_eq (F : X ⟶ Y) (t : Dx.Tr) :
    Dx.vmapHom Dy F t = (uTreeMap (Dx.conjHom Dy F) (canon (hηU Dx.hdim) t)).1.2 := rfl

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **Points of vertices of edge kind** whose images have edge kind are mapped to the points of
the images: the image of the canonical point lies over a special point, hence is canonical. -/
theorem fibreMapZ_vertexPt_of_edge (F : X ⟶ Y) {m : Dx.Tr}
    (hm' : Tree.kind (Dx.vmapHom Dy F m) = false) :
    Dx.fibreMapZ Dy F (Dx.vertexPt m) = Dy.vertexPt (Dx.vmapHom Dy F m) := by
  obtain ⟨s, hs⟩ := Tree.kind_eq_false_iff.1 hm'
  rw [vertexPt_eq_canon, ← uTreeMap_fst_eq]
  exact congrArg (fun x ↦ x.1.1) (eq_canon_of_inr (hηU Dy.hdim) hs)

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **No contraction at midpoints.** Let `t` be a vertex of vertex kind with a neighbour `m`
whose image under `vmapHom F` has edge kind, and suppose the image of `t` has vertex kind. Then
the generic point of the component of `t` maps to the generic point of the component of the
image of `t`: the image `y` of `η_t` lies on that component, is not special, and specialises to
the (special) image of the point of `m`, so it is not closed, hence generic (dimension `≤ 1`). -/
theorem fibreMapZ_vertexPt_of_vertex (F : X ⟶ Y) {t m : Dx.Tr} (h : t.Adj m)
    (ht : Tree.kind t = true) (ht' : Tree.kind (Dx.vmapHom Dy F t) = true)
    (hm' : Tree.kind (Dx.vmapHom Dy F m) = false) :
    Dx.fibreMapZ Dy F (Dx.vertexPt t) = Dy.vertexPt (Dx.vmapHom Dy F t) := by
  obtain ⟨j, hj⟩ := Tree.kind_eq_true_iff.1 ht'
  set y := Dx.fibreMapZ Dy F (Dx.vertexPt t) with hy_def
  have hy : y ∈ j.1 \ Dy.config.S := by
    rw [hy_def, vertexPt_eq_canon, ← uTreeMap_fst_eq]
    exact Cover.mem_piece_inl hj
  have hsp : y ⤳ Dy.vertexPt (Dx.vmapHom Dy F m) := by
    rw [← Dx.fibreMapZ_vertexPt_of_edge Dy F hm']
    exact (Dx.vertexPt_specializes ht h).map (Dx.continuous_fibreMapZ Dy F)
  have hne : y ≠ Dy.vertexPt (Dx.vmapHom Dy F m) := fun he ↦
    hy.2 (he ▸ Dy.vertexPt_mem_S hm')
  have hcl := closure_eq_of_specializes_of_ne Dy.hdim j.2 hy.1 hsp hne
  rw [Dy.vertexPt_of_inl hj]
  exact (show IsGenericPoint y j.1 from hcl).eq
    (show IsGenericPoint (Dy.config.η j) j.1 from Dy.closure_η j)

end Maps

end UData

section Tower

variable (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  {𝒢 : ObjectProperty (TempObj O R A)}
  (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
  (D : ∀ p : PtGal (tempFibre O R A V hV) 𝒢, UData Ω p.G)

variable {p q : PtGal (tempFibre O R A V hV) 𝒢}

/-- The model map of a pointed morphism. -/
def ptModelMap (f : p ⟶ q) : (D p).Lv.c.scheme ⟶ (D q).Lv.c.scheme :=
  (D p).modelMap (D q) (ptHomMor V hV f)

/-- The level map of a pointed morphism. -/
def ptLevelMap (f : p ⟶ q) : (D q).Lv.L.B →ₐ[R] (D p).Lv.L.B :=
  (D p).levelMap (D q) (ptHomMor V hV f)

/-- The map of special fibres of a pointed morphism. -/
def ptFibreMap (f : p ⟶ q) : (D p).Lv.Z → (D q).Lv.Z :=
  (D p).fibreMapZ (D q) (ptHomMor V hV f)

lemma ptModelMap_toSpec (f : p ⟶ q) :
    ptModelMap V hV D f ≫ (D q).Lv.c.toSpec = (D p).Lv.c.toSpec :=
  UData.modelMap_toSpec _ _ _

lemma j_ptModelMap (f : p ⟶ q) :
    (D p).Lv.j ≫ ptModelMap V hV D f =
      Spec.map (CommRingCat.ofHom (ptLevelMap V hV D f : (D q).Lv.L.B →+* (D p).Lv.L.B)) ≫
        (D q).Lv.j :=
  UData.j_modelMap _ _ _

lemma ptFibreMap_eq (f : p ⟶ q) :
    ptFibreMap V hV D f = specialFibreMap (ptModelMap V hV D f) (ptModelMap_toSpec V hV D f) :=
  rfl

lemma coe_ptFibreMap (f : p ⟶ q) (z : (D p).Lv.Z) :
    (ptFibreMap V hV D f z : (D q).Lv.c.scheme) = ptModelMap V hV D f (z : (D p).Lv.c.scheme) :=
  rfl

lemma continuous_ptFibreMap (f : p ⟶ q) : Continuous (ptFibreMap V hV D f) :=
  UData.continuous_fibreMapZ _ _ _

lemma isClosedMap_ptFibreMap (f : p ⟶ q) : IsClosedMap (ptFibreMap V hV D f) :=
  UData.isClosedMap_fibreMapZ _ _ _

lemma stageTower_map (f : p ⟶ q) (t : (D p).Tr) :
    (stageTower V hV hgal hrig D).map f t = (D p).vmapHom (D q) (ptHomMor V hV f) t := rfl

/-- In the stage tower, the point of a vertex of edge kind whose image has edge kind is mapped to
the point of the image. -/
theorem ptFibreMap_vertexPt_of_edge (f : p ⟶ q) {m : (stageTower V hV hgal hrig D).V p}
    (hm' : (stageTower V hV hgal hrig D).kind q ((stageTower V hV hgal hrig D).map f m) = false) :
    ptFibreMap V hV D f ((D p).vertexPt m) =
      (D q).vertexPt ((stageTower V hV hgal hrig D).map f m) :=
  UData.fibreMapZ_vertexPt_of_edge _ _ _ hm'

/-- **No contraction at midpoints** in the stage tower (`UData.fibreMapZ_vertexPt_of_vertex`). -/
theorem ptFibreMap_vertexPt_of_vertex (f : p ⟶ q) {t m : (stageTower V hV hgal hrig D).V p}
    (h : ((stageTower V hV hgal hrig D).graph p).Adj t m)
    (ht : (stageTower V hV hgal hrig D).kind p t = true)
    (ht' : (stageTower V hV hgal hrig D).kind q ((stageTower V hV hgal hrig D).map f t) = true)
    (hm' : (stageTower V hV hgal hrig D).kind q ((stageTower V hV hgal hrig D).map f m) = false) :
    ptFibreMap V hV D f ((D p).vertexPt t) =
      (D q).vertexPt ((stageTower V hV hgal hrig D).map f t) :=
  UData.fibreMapZ_vertexPt_of_vertex _ _ _ h ht ht' hm'

end Tower

section Curve

variable [CharZero K] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [PerfectField (IsLocalRing.ResidueField O)]
  [Algebra.Smooth K R] [IsDomain R] [Subsingleton A] [IsAlgClosed Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (hp : ∃ p : ℕ, p.Prime ∧ (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1)
  {l j : PtGal (tempFibre O R A V hV) (galW O R A Ω hR)}

lemma curveTower_map (f : l ⟶ j) (t : (curveData V hV hR l).Tr) :
    (curveTower (R := R) (A := A) V hV hp hR).map f t =
      (curveData V hV hR l).vmapHom (curveData V hV hR j) (ptHomMor V hV f) t := rfl

/-- In the curve tower, the point of a vertex of edge kind whose image has edge kind is mapped to
the point of the image. -/
theorem curveTower_vertexPt_of_edge (f : l ⟶ j)
    {m : (curveTower (R := R) (A := A) V hV hp hR).V l}
    (hm' : (curveTower (R := R) (A := A) V hV hp hR).kind j
      ((curveTower (R := R) (A := A) V hV hp hR).map f m) = false) :
    ptFibreMap V hV (curveData V hV hR) f ((curveData V hV hR l).vertexPt m) =
      (curveData V hV hR j).vertexPt ((curveTower (R := R) (A := A) V hV hp hR).map f m) :=
  UData.fibreMapZ_vertexPt_of_edge _ _ _ hm'

/-- **No contraction at midpoints** in the curve tower. -/
theorem curveTower_vertexPt_of_vertex (f : l ⟶ j)
    {t m : (curveTower (R := R) (A := A) V hV hp hR).V l}
    (h : ((curveTower (R := R) (A := A) V hV hp hR).graph l).Adj t m)
    (ht : (curveTower (R := R) (A := A) V hV hp hR).kind l t = true)
    (ht' : (curveTower (R := R) (A := A) V hV hp hR).kind j
      ((curveTower (R := R) (A := A) V hV hp hR).map f t) = true)
    (hm' : (curveTower (R := R) (A := A) V hV hp hR).kind j
      ((curveTower (R := R) (A := A) V hV hp hR).map f m) = false) :
    ptFibreMap V hV (curveData V hV hR) f ((curveData V hV hR l).vertexPt t) =
      (curveData V hV hR j).vertexPt ((curveTower (R := R) (A := A) V hV hp hR).map f t) :=
  UData.fibreMapZ_vertexPt_of_vertex _ _ _ h ht ht' hm'

end Curve

end

end TemperedFundamentalGroups
