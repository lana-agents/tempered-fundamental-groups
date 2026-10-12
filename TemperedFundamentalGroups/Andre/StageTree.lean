/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.DualGraphPi1
import TemperedFundamentalGroups.Andre.StageFunctor
import TemperedFundamentalGroups.Andre.StageTorsion
import TemperedFundamentalGroups.SemiAnbd.CoverVertex

/-!
# The stage groups act on the trees of the dual graphs (Blueprint §12.5, C5)

Scheme case (`H` trivial). Let `U = universalObj Lv hdim z₀` be the Galois object over the
universal covering `Z̃ = K.Cover r` of the special fibre `Z` (`K = curveConfig Z hdim`, the
configuration of irreducible components and their intersection points). An automorphism `a` of
`U` acts on `Z̃` (`treeMap a.hom`, §11.3 G6.4) over the homeomorphism `zHomeo a` of `Z` induced by
its model automorphism. Homeomorphisms of `Z` permute the irreducible components, their generic
points (`curveConfig_η_homeo`) and the special points (`curveConfig_mem_S_homeo`), so
`treeMap a.hom` preserves canonical points and sheets (`SemiAnbd/CoverVertex.lean`), and
induces a coloured automorphism of the tree `K.Tree r`.

* `treeMap_comp`, `treeMap_id`, and **`treeMap_eq_of_fibreMap_eq`**: morphisms of Galois objects
  with the same map of fibres induce the same map of trees (connected `B`, scheme-theoretically
  dominant `j`).
* `autTree : Aut U →* Equiv.Perm (K.Tree r)`, with `adj_autTree_iff`, `kind_autTree`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology TopologicalSpace

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig

section Homeo

variable {X : Type u} [TopologicalSpace X] [NoetherianSpace X] [T0Space X] [QuasiSober X]
  (hdim : topologicalKrullDim X ≤ 1) (h : X ≃ₜ X)

omit [NoetherianSpace X] [T0Space X] [QuasiSober X] in
lemma image_mem_irreducibleComponents_homeo {C : Set X} (hC : C ∈ irreducibleComponents X) :
    h '' C ∈ irreducibleComponents X := by
  have := preimage_mem_irreducibleComponents hC h.symm.isOpenEmbedding
    (by rw [h.symm.surjective.range_eq, Set.inter_univ]; exact hC.1.1)
  rwa [h.preimage_symm] at this

/-- The permutation of irreducible components induced by a homeomorphism. -/
def compHomeo (i : irreducibleComponents X) : irreducibleComponents X :=
  ⟨h '' i.1, image_mem_irreducibleComponents_homeo h i.2⟩

/-- Homeomorphisms send generic points of components to generic points of components. -/
lemma curveConfig_η_homeo (i : irreducibleComponents X) :
    h ((curveConfig X hdim).η i) = (curveConfig X hdim).η (compHomeo h i) := by
  have hcl := isClosed_of_mem_irreducibleComponents i.1 i.2
  have h₁ := (i.2.1.isGenericPoint_genericPoint hcl).image h.continuous
  rw [(h.isClosedMap _ hcl).closure_eq] at h₁
  exact h₁.eq ((compHomeo h i).2.1.isGenericPoint_genericPoint
    (isClosed_of_mem_irreducibleComponents _ (compHomeo h i).2))

lemma curveConfig_mem_S_homeo_of_mem {z : X} (hz : z ∈ (curveConfig X hdim).S) :
    h z ∈ (curveConfig X hdim).S := by
  obtain ⟨i, j, hij, hi, hj⟩ := hz
  refine ⟨compHomeo h i, compHomeo h j, fun he ↦ hij (Subtype.ext ?_), ⟨z, hi, rfl⟩,
    ⟨z, hj, rfl⟩⟩
  have := congrArg (fun k : irreducibleComponents X ↦ h ⁻¹' k.1) he
  simpa [compHomeo, h.preimage_image] using this

/-- Homeomorphisms preserve and reflect the special points (points on two components). -/
lemma curveConfig_mem_S_homeo (z : X) :
    h z ∈ (curveConfig X hdim).S ↔ z ∈ (curveConfig X hdim).S := by
  refine ⟨fun hz ↦ ?_, curveConfig_mem_S_homeo_of_mem hdim h⟩
  have := curveConfig_mem_S_homeo_of_mem hdim h.symm hz
  rwa [Homeomorph.symm_apply_apply] at this

end Homeo

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

section TreeMap

variable {Lv Lv' Lv'' : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H] [Finite Lv'.L.H]
  [Subsingleton Lv'.L.H] [Finite Lv''.L.H] [Subsingleton Lv''.L.H]
  {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}
  {E' : Type u} [TopologicalSpace E'] {p' : E' → Lv'.Z}
  {hp' : IsUniversalCovering.{u, u, u, u} p'} {hc' : ∀ z, (p' ⁻¹' {z}).Countable}
  {E'' : Type u} [TopologicalSpace E''] {p'' : E'' → Lv''.Z}
  {hp'' : IsUniversalCovering.{u, u, u, u} p''} {hc'' : ∀ z, (p'' ⁻¹' {z}).Countable}

omit [Subsingleton Lv.L.H] [Subsingleton Lv''.L.H] in
lemma treeMap_comp (F : obj Lv hp hc ⟶ obj Lv' hp' hc') (G : obj Lv' hp' hc' ⟶ obj Lv'' hp'' hc'') :
    treeMap (F ≫ G) = treeMap G ∘ treeMap F := by
  funext e
  unfold treeMap
  change ((Θ Lv'' hp'' hc'').symm (G.h (F.h (Θ Lv hp hc ⟨1, e⟩)))).2 = _
  rw [h_Θ_one F e]
  rfl

omit [Subsingleton Lv.L.H] in
lemma treeMap_id : treeMap (𝟙 (obj Lv hp hc)) = id := by
  funext e
  unfold treeMap
  change ((Θ Lv hp hc).symm (Θ Lv hp hc ⟨1, e⟩)).2 = e
  rw [Homeomorph.symm_apply_apply]

variable [ConnectedSpace Lv.Z] [Nonempty E]

omit [Subsingleton Lv.L.H] [Finite Lv''.L.H] [Subsingleton Lv''.L.H] in
/-- **Morphisms of Galois objects with the same map of fibres induce the same map of trees**
(for a connected `B` and a scheme-theoretically dominant `j`): the level maps agree (rigidity of
connected étale algebras), hence the model maps (`j` is dominant), and the maps of trees are lifts
of the same map agreeing at one point. -/
theorem treeMap_eq_of_fibreMap_eq [IsSchemeTheoreticallyDominant Lv.j]
    (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1) [Nonempty (Lv.L.B →ₐ[R] Ω)]
    {F F' : obj Lv hp hc ⟶ obj Lv' hp' hc'} (h : fibreMap V hV F = fibreMap V hV F') :
    treeMap F = treeMap F' := by
  obtain ⟨t⟩ := ‹Nonempty (Lv.L.B →ₐ[R] Ω)›
  obtain ⟨e, he⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
  obtain ⟨he₁, h₁⟩ := fibreMap_prePt V hV F t e he
  obtain ⟨he₂, h₂⟩ := fibreMap_prePt V hV F' t e he
  have hx := congrFun h (Quotient.mk _ (prePt V hV t e he))
  rw [h₁, h₂] at hx
  obtain ⟨ht, hee⟩ := (mk_prePt_eq_iff V hV he₁ he₂).1 hx
  haveI : Algebra.Etale R (obj Lv' hp' hc').Lv.L.B := Lv'.L.etale
  haveI : Module.Finite R (obj Lv' hp' hc').Lv.L.B := Lv'.L.finite
  have hφ : F.φ.f = F'.φ.f := algHom_eq_of_comp_eq hidem F.φ.f F'.φ.f t ht
  have : IsSchemeTheoreticallyDominant (obj Lv hp hc).Lv.j := ‹IsSchemeTheoreticallyDominant Lv.j›
  have hψ : F.ψ = F'.ψ :=
    ext_of_isSchemeTheoreticallyDominant_of_isSeparated (obj Lv' hp' hc').Lv.c.toSpec
      (F.ψ_toSpec.trans F'.ψ_toSpec.symm) (obj Lv hp hc).Lv.j (by rw [F.j_ψ, F'.j_ψ, hφ])
  refine lift_ext hp hp'.isCoveringMap (continuous_treeMap F) (continuous_treeMap F')
    (funext fun e ↦ Subtype.ext ?_) e hee
  simp only [Function.comp_apply]
  rw [treeMap_spec, treeMap_spec, hψ]

omit [ConnectedSpace Lv.Z] [Nonempty E] in
/-- An endomorphism of a Galois object acting trivially on the level and on the tree acts
trivially on fibres. -/
lemma fibreMap_eq_self_of [Subsingleton A] (F : obj Lv hp hc ⟶ obj Lv hp hc)
    (hφ : F.φ.f = AlgHom.id R _) (htm : treeMap F = id) (x : Fibre Ω V hV (obj Lv hp hc)) :
    fibreMap V hV F x = x := by
  obtain ⟨q, e, hq, rfl⟩ := exists_rep V hV x
  change Quotient.mk _ (preMap V hV F q) = Quotient.mk _ q
  congr 1
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · change q.1.1.comp F.φ.f = q.1.1
    rw [hφ]
    rfl
  · change F.h q.1.2 = q.1.2
    rw [hq, h_Θ_one, htm]
    rfl

end TreeMap

section Universal

/-- The model automorphism of an automorphism of a tempered covering. -/
def TempObj.schemeIso {X : TempObj O R A} (a : X ≅ X) : X.Lv.c.scheme ≅ X.Lv.c.scheme where
  hom := a.hom.ψ
  inv := a.inv.ψ
  hom_inv_id := congrArg TempObj.Hom.ψ a.hom_inv_id
  inv_hom_id := congrArg TempObj.Hom.ψ a.inv_hom_id

/-- The homeomorphism of the special fibre induced by an automorphism. -/
def TempObj.zHomeo {X : TempObj O R A} (a : X ≅ X) : X.Lv.Z ≃ₜ X.Lv.Z :=
  specialFibreHomeomorph (TempObj.schemeIso a) a.hom.ψ_toSpec

lemma TempObj.coe_zHomeo {X : TempObj O R A} (a : X ≅ X) (z : X.Lv.Z) :
    ((TempObj.zHomeo a z : X.Lv.Z) : X.Lv.c.scheme) = a.hom.ψ (z : X.Lv.c.scheme) := rfl

variable {Lv Lv' Lv'' : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H] [NoetherianSpace Lv.Z]
  [T0Space Lv.Z] [QuasiSober Lv.Z] (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z)
  [Finite Lv'.L.H] [Subsingleton Lv'.L.H] [NoetherianSpace Lv'.Z] [T0Space Lv'.Z]
  [QuasiSober Lv'.Z] (hdim' : topologicalKrullDim Lv'.Z ≤ 1) (z₀' : Lv'.Z)
  [Finite Lv''.L.H] [Subsingleton Lv''.L.H] [NoetherianSpace Lv''.Z] [T0Space Lv''.Z]
  [QuasiSober Lv''.Z] (hdim'' : topologicalKrullDim Lv''.Z ≤ 1) (z₀'' : Lv''.Z)

/-- The tree of the dual graph of `Lv` (its universal covering based at `z₀`). -/
abbrev UTree : Type u := (curveConfig Lv.Z hdim).Tree (universalCovering.root hdim z₀)

omit [Finite Lv.L.H] [Subsingleton Lv.L.H] in
lemma hηU : ∀ i, (curveConfig Lv.Z hdim).η i ∉ (curveConfig Lv.Z hdim).S :=
  curveConfig_η_notMem_S hdim

variable {hdim z₀ hdim' z₀' hdim'' z₀''}

/-- The map of universal coverings induced by a morphism of universal Galois objects. -/
def uTreeMap (F : universalObj Lv hdim z₀ ⟶ universalObj Lv' hdim' z₀') :
    universalCovering Lv.Z hdim z₀ → universalCovering Lv'.Z hdim' z₀' :=
  treeMap (hp := universalCovering.isUniversalCovering.{u, u, u} hdim z₀)
    (hc := (universalCovering.isUniversalCovering.{u, u, u} hdim z₀).countable_fibre)
    (hp' := universalCovering.isUniversalCovering.{u, u, u} hdim' z₀')
    (hc' := (universalCovering.isUniversalCovering.{u, u, u} hdim' z₀').countable_fibre) F

omit [Subsingleton Lv.L.H] [Subsingleton Lv'.L.H] in
lemma continuous_uTreeMap (F : universalObj Lv hdim z₀ ⟶ universalObj Lv' hdim' z₀') :
    Continuous (uTreeMap F) :=
  continuous_treeMap _

omit [Subsingleton Lv.L.H] in
lemma uTreeMap_spec (F : universalObj Lv hdim z₀ ⟶ universalObj Lv' hdim' z₀')
    (x : universalCovering Lv.Z hdim z₀) :
    (((uTreeMap F x).1.1 : Lv'.Z) : Lv'.c.scheme) = F.ψ (x.1.1 : Lv.c.scheme) :=
  treeMap_spec F x

omit [Subsingleton Lv.L.H] [Subsingleton Lv''.L.H] in
lemma uTreeMap_comp (F : universalObj Lv hdim z₀ ⟶ universalObj Lv' hdim' z₀')
    (G : universalObj Lv' hdim' z₀' ⟶ universalObj Lv'' hdim'' z₀'') :
    uTreeMap (F ≫ G) = uTreeMap G ∘ uTreeMap F :=
  treeMap_comp F G

omit [Subsingleton Lv.L.H] in
lemma uTreeMap_id : uTreeMap (𝟙 (universalObj Lv hdim z₀)) = id :=
  treeMap_id

/-- The homeomorphism of the special fibre of an automorphism of `U = universalObj`. -/
def zHomeoU (a : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀) : Lv.Z ≃ₜ Lv.Z :=
  TempObj.zHomeo (X := universalObj Lv hdim z₀) a

/-- The map of trees of an automorphism of `U = universalObj` lies over `zHomeoU`. -/
lemma uTreeMap_fst (a : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀)
    (x : universalCovering Lv.Z hdim z₀) :
    (uTreeMap a.hom x).1.1 = zHomeoU a x.1.1 :=
  Subtype.ext (uTreeMap_spec a.hom x)

/-- The action of an automorphism of `U` on the vertices of the tree. -/
def autVmap (a : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀) :
    UTree hdim z₀ → UTree hdim z₀ :=
  vmap (hηU hdim) (uTreeMap a.hom)

lemma preservesCanon_aut (a : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀) :
    PreservesCanon (hηU hdim) (hηU hdim) (uTreeMap a.hom) :=
  preservesCanon_of_over _ _ (uTreeMap_fst a)
    (fun i ↦ ⟨_, curveConfig_η_homeo hdim (zHomeoU a) i⟩)
    (curveConfig_mem_S_homeo hdim (zHomeoU a))

lemma preservesSheets_aut (a : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀) :
    PreservesSheets (hηU hdim) (uTreeMap a.hom) :=
  preservesSheets_of_over _ (hηU hdim) (uTreeMap_fst a)
    (fun i ↦ ⟨_, curveConfig_η_homeo hdim (zHomeoU a) i⟩)
    (curveConfig_mem_S_homeo hdim (zHomeoU a)) (continuous_uTreeMap _)

lemma kind_autVmap (a : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀) (t : UTree hdim z₀) :
    Tree.kind (autVmap a t) = Tree.kind t :=
  kind_vmap_of_over _ (hηU hdim) (uTreeMap_fst a)
    (fun i ↦ ⟨_, curveConfig_η_homeo hdim (zHomeoU a) i⟩)
    (curveConfig_mem_S_homeo hdim (zHomeoU a)) t

lemma autVmap_comp (a b : universalObj Lv hdim z₀ ≅ universalObj Lv hdim z₀) :
    autVmap (b ≪≫ a) = autVmap a ∘ autVmap b := by
  unfold autVmap
  rw [Iso.trans_hom, uTreeMap_comp]
  exact vmap_comp_of_preservesCanon _ _ _ (preservesCanon_aut b)

omit [Subsingleton Lv.L.H] in
lemma autVmap_refl : autVmap (Iso.refl (universalObj Lv hdim z₀)) = id := by
  unfold autVmap
  rw [Iso.refl_hom, uTreeMap_id]
  rfl

/-- **The action of `Aut U` on the tree of the dual graph.** -/
def autTree : Aut (universalObj Lv hdim z₀) →* Equiv.Perm (UTree hdim z₀) where
  toFun a :=
    { toFun := autVmap a
      invFun := autVmap a.symm
      left_inv t := by
        rw [← Function.comp_apply (f := autVmap a.symm), ← autVmap_comp, Iso.self_symm_id,
          autVmap_refl, id]
      right_inv t := by
        rw [← Function.comp_apply (f := autVmap a), ← autVmap_comp, Iso.symm_self_id,
          autVmap_refl, id] }
  map_one' := Equiv.ext fun t ↦ congrFun autVmap_refl t
  map_mul' a b := Equiv.ext fun t ↦ by
    rw [Aut.Aut_mul_def]
    exact congrFun (autVmap_comp a b) t

lemma autTree_apply (a : Aut (universalObj Lv hdim z₀)) (t : UTree hdim z₀) :
    autTree a t = autVmap a t := rfl

lemma kind_autTree (a : Aut (universalObj Lv hdim z₀)) (t : UTree hdim z₀) :
    Tree.kind (autTree a t) = Tree.kind t :=
  kind_autVmap a t

lemma adj_autTree_of_adj (a : Aut (universalObj Lv hdim z₀)) {t t' : UTree hdim z₀}
    (h : t.Adj t') : (autTree a t).Adj (autTree a t') := by
  rcases vmap_adj (hηU hdim) (continuous_uTreeMap a.hom) h with h' | h'
  · exact h'
  · exact absurd ((autTree a).injective h') (fun he ↦ Tree.not_adj_self t (he ▸ h))

/-- **`Aut U` acts on the tree by graph automorphisms.** -/
lemma adj_autTree_iff (a : Aut (universalObj Lv hdim z₀)) (t t' : UTree hdim z₀) :
    (autTree a t).Adj (autTree a t') ↔ t.Adj t' := by
  refine ⟨fun h ↦ ?_, adj_autTree_of_adj a⟩
  have := adj_autTree_of_adj a⁻¹ h
  rwa [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Equiv.Perm.one_apply, Equiv.Perm.one_apply] at this

end Universal

section Stage

variable {Lv : Level O R A} [Finite Lv.L.H] [Subsingleton Lv.L.H] [NoetherianSpace Lv.Z]
  [T0Space Lv.Z] [QuasiSober Lv.Z] {hdim : topologicalKrullDim Lv.Z ≤ 1} {z₀ : Lv.Z}
  [ConnectedSpace Lv.Z] [IsSchemeTheoreticallyDominant Lv.j] [Nonempty (Lv.L.B →ₐ[R] Ω)]

/-- Endomorphisms of `U = universalObj` with the same map of fibres have the same map of trees. -/
lemma uTreeMap_eq_of_fibreMap_eq (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    {F F' : universalObj Lv hdim z₀ ⟶ universalObj Lv hdim z₀}
    (h : fibreMap V hV F = fibreMap V hV F') : uTreeMap F = uTreeMap F' :=
  treeMap_eq_of_fibreMap_eq V hV hidem h

/-- Automorphisms of `U` with the same map of fibres act in the same way on the tree. -/
lemma autTree_eq_of_fibreMap_eq (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    {a b : Aut (universalObj Lv hdim z₀)} (h : fibreMap V hV a.hom = fibreMap V hV b.hom) :
    autTree a = autTree b := by
  refine Equiv.ext fun t ↦ ?_
  change vmap (hηU hdim) (uTreeMap a.hom) t = vmap (hηU hdim) (uTreeMap b.hom) t
  rw [uTreeMap_eq_of_fibreMap_eq V hV hidem h]

end Stage

lemma fibreMap_comp_apply {X Y Z : TempObj O R A} (m : X ⟶ Y) (n : Y ⟶ Z) (x : Fibre Ω V hV X) :
    fibreMap V hV (m ≫ n) x = fibreMap V hV n (fibreMap V hV m x) := by
  induction x using Quotient.inductionOn
  rfl

lemma fibreMap_eq_of_stageOf_eq {X : TempObj O R A} {a b : X ≅ X}
    (h : stageOf (Φ := tempFibre O R A V hV) a = stageOf b) :
    fibreMap V hV a.hom = fibreMap V hV b.hom :=
  funext fun x ↦ congrArg (fun σ : stageGroup (tempFibre O R A V hV) X ↦ σ.1 x) h

variable (Ω) in
/-- **Data exhibiting `X` as the Galois object `universalObj Lv hdim z₀`** over the universal
covering of the special fibre of a level with trivial `H` (as in `galClassW`). -/
structure UData (X : TempObj O R A) where
  /-- The level. -/
  Lv : Level O R A
  [sub : Subsingleton Lv.L.H]
  [noeth : NoetherianSpace Lv.Z]
  [t0 : T0Space Lv.Z]
  [qs : QuasiSober Lv.Z]
  [conn : ConnectedSpace Lv.Z]
  hdim : topologicalKrullDim Lv.Z ≤ 1
  /-- The base point of the universal covering. -/
  z₀ : Lv.Z
  [ne : Nonempty (Lv.L.B →ₐ[R] Ω)]
  hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1
  [dom : IsSchemeTheoreticallyDominant Lv.j]
  /-- The identification with the Galois object. -/
  e : X ≅ universalObj Lv hdim z₀

namespace UData

attribute [instance] sub noeth t0 qs conn ne dom

variable {X : TempObj O R A} (D : UData Ω X)

/-- The tree of `X`: the tree of the dual graph of its level. -/
abbrev Tr : Type u := UTree D.hdim D.z₀

/-- The action of `Aut X` on the tree of `X`, through `X ≅ universalObj`. -/
def treeAut : Aut X →* Equiv.Perm D.Tr := autTree.comp D.e.conjAut.toMonoidHom

lemma treeAut_eq_of_fibreMap_eq {a b : Aut X} (h : fibreMap V hV a.hom = fibreMap V hV b.hom) :
    D.treeAut a = D.treeAut b := by
  refine autTree_eq_of_fibreMap_eq V hV D.hidem (funext fun x ↦ ?_)
  change fibreMap V hV (D.e.inv ≫ a.hom ≫ D.e.hom) x = fibreMap V hV (D.e.inv ≫ b.hom ≫ D.e.hom) x
  rw [fibreMap_comp_apply, fibreMap_comp_apply, fibreMap_comp_apply, fibreMap_comp_apply, h]

/-- **The stage group of `X` acts on the tree of its dual graph.** -/
def stageTree : stageGroup (tempFibre O R A V hV) X →* Equiv.Perm D.Tr where
  toFun σ := D.treeAut (eq_stageOf σ).choose
  map_one' := by
    rw [← map_one D.treeAut]
    refine D.treeAut_eq_of_fibreMap_eq V hV (fibreMap_eq_of_stageOf_eq V hV ?_)
    rw [← (eq_stageOf (1 : stageGroup (tempFibre O R A V hV) X)).choose_spec]
    exact ((stageOfHom (tempFibre O R A V hV) X).map_one).symm
  map_mul' σ τ := by
    rw [← map_mul D.treeAut]
    refine D.treeAut_eq_of_fibreMap_eq V hV (fibreMap_eq_of_stageOf_eq V hV ?_)
    rw [← (eq_stageOf (σ * τ)).choose_spec]
    change _ = stageOfHom (tempFibre O R A V hV) X (_ * _)
    rw [map_mul]
    exact congrArg₂ (· * ·) (eq_stageOf σ).choose_spec (eq_stageOf τ).choose_spec

lemma stageTree_stageOf (a : Aut X) :
    D.stageTree V hV (stageOf a) = D.treeAut a :=
  D.treeAut_eq_of_fibreMap_eq V hV (fibreMap_eq_of_stageOf_eq V hV
    (eq_stageOf (stageOf (Φ := tempFibre O R A V hV) a)).choose_spec.symm)

end UData

end

end TemperedFundamentalGroups
