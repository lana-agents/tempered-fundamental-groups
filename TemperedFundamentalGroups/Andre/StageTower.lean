/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.StageTree
import TemperedFundamentalGroups.SemiAnbd.TreeTower

/-!
# The tree tower of a curve (Blueprint §12.5, C6)

Scheme case. For a Galois class `𝒢` with (gal) and (rig) whose members are identified with
universal Galois objects (`UData`), the inverse limit `limGroup Φ 𝒢` of the stage groups carries a
**tree tower** (`SemiAnbd/TreeTower.lean`): at the pointed Galois object `p` the stage group
`Π_p` acts on the tree of the dual graph of its level (`UData.stageTree`), and a pointed morphism
`p ⟶ q` induces the non-expanding map of vertices of the map of trees (`UData.vmapHom`),
equivariant along the transition maps (`UData.vmapHom_treeAut`).

* `UData.vmapHom`, `UData.vmapHom_adj`, **`UData.vmapHom_treeAut`**.
* **`stageTower hgal hrig D : TreeTower (limGroup Φ 𝒢 hgal hrig) (PtGal Φ 𝒢)`**.

Its verticial subgroups (stabilizers of compatible systems of vertices over components) are the
decomposition groups of the components of the special fibres; the results of §12.4 apply to them
(commensurable terminality and incomparability under `(HI)`, fixed systems of bounded subgroups,
vertex correspondences).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology TopologicalSpace

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit CurveConfig

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

namespace UData

variable {X Y : TempObj O R A} (Dx : UData Ω X) (Dy : UData Ω Y)

/-- **The map of vertices of the trees** induced by a morphism `F : X ⟶ Y` of Galois objects. -/
def vmapHom (F : X ⟶ Y) : Dx.Tr → Dy.Tr :=
  vmap (hηU Dx.hdim) (uTreeMap (Dx.e.inv ≫ F ≫ Dy.e.hom))

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- The map of vertices along a morphism is non-expanding. -/
lemma vmapHom_adj (F : X ⟶ Y) {t t' : Dx.Tr} (h : t.Adj t') :
    (Dx.vmapHom Dy F t).Adj (Dx.vmapHom Dy F t') ∨ Dx.vmapHom Dy F t = Dx.vmapHom Dy F t' :=
  vmap_adj _ (continuous_uTreeMap _) h

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma treeAut_apply (a : Aut X) (t : Dx.Tr) :
    Dx.treeAut a t = vmap (hηU Dx.hdim) (uTreeMap (Dx.e.conjAut a).hom) t := rfl

/-- **The maps of vertices are equivariant**: if `a ≫ F` and `F ≫ b` induce the same map of
fibres, then `vmapHom F ∘ a = b ∘ vmapHom F` on the trees. -/
theorem vmapHom_treeAut (F : X ⟶ Y) (a : Aut X) (b : Aut Y)
    (h : fibreMap V hV (a.hom ≫ F) = fibreMap V hV (F ≫ b.hom)) (t : Dx.Tr) :
    Dx.vmapHom Dy F (Dx.treeAut a t) = Dy.treeAut b (Dx.vmapHom Dy F t) := by
  set F' := Dx.e.inv ≫ F ≫ Dy.e.hom
  have hA : (Dx.e.conjAut a).hom ≫ F' = Dx.e.inv ≫ (a.hom ≫ F) ≫ Dy.e.hom := by
    simp [F', Iso.conjAut_hom, Iso.conj_apply]
  have hB : F' ≫ (Dy.e.conjAut b).hom = Dx.e.inv ≫ (F ≫ b.hom) ≫ Dy.e.hom := by
    simp [F', Iso.conjAut_hom, Iso.conj_apply]
  have hfib : fibreMap V hV ((Dx.e.conjAut a).hom ≫ F') =
      fibreMap V hV (F' ≫ (Dy.e.conjAut b).hom) := by
    rw [hA, hB]
    funext x
    rw [fibreMap_comp_apply, fibreMap_comp_apply, h, fibreMap_comp_apply V hV Dx.e.inv,
      fibreMap_comp_apply V hV (F ≫ b.hom) Dy.e.hom]
  have htm : uTreeMap ((Dx.e.conjAut a).hom ≫ F') = uTreeMap (F' ≫ (Dy.e.conjAut b).hom) :=
    treeMap_eq_of_fibreMap_eq V hV Dx.hidem hfib
  rw [uTreeMap_comp, uTreeMap_comp] at htm
  have h₁ := vmap_comp_of_preservesCanon (hηU Dx.hdim) (hηU Dx.hdim) (uTreeMap F')
    (preservesCanon_aut (Dx.e.conjAut a))
  have h₂ := vmap_comp_of_preservesSheets (hηU Dx.hdim) (hηU Dy.hdim) (uTreeMap F')
    (preservesSheets_aut (Dy.e.conjAut b))
  rw [treeAut_apply, treeAut_apply]
  change vmap _ (uTreeMap F') _ = _
  rw [← Function.comp_apply (f := vmap _ (uTreeMap F')), ← h₁, htm, h₂]
  rfl

end UData

namespace UData

variable {X : TempObj O R A} (D : UData Ω X)

/-- The level map of the automorphism of `universalObj` conjugate to `a`. -/
def lev (a : Aut X) : D.Lv.L.B →ₐ[R] D.Lv.L.B := (D.e.conjAut a).hom.φ.f

/-- **An automorphism fixing a vertex of the tree and acting trivially on the level is trivial
on fibres**: its model map is the identity (`j` is dominant), so its map of trees is a deck
transformation fixing a point. -/
theorem stageOf_eq_one_of_fixed [Subsingleton A] (a : Aut X) {t : D.Tr} (ht : D.treeAut a t = t)
    (hφ : D.lev a = AlgHom.id R _) : stageOf (Φ := tempFibre O R A V hV) a = 1 := by
  have hp := universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀
  -- the model map is the identity
  have hf : ((D.lev a : D.Lv.L.B →ₐ[R] D.Lv.L.B) : D.Lv.L.B →+* D.Lv.L.B) = RingHom.id _ := by
    rw [hφ]
    rfl
  have hj : (universalObj D.Lv D.hdim D.z₀).Lv.j ≫ (D.e.conjAut a).hom.ψ =
      (universalObj D.Lv D.hdim D.z₀).Lv.j ≫ 𝟙 _ := by
    rw [(D.e.conjAut a).hom.j_ψ, Category.comp_id]
    change Spec.map (CommRingCat.ofHom
      ((D.lev a : D.Lv.L.B →ₐ[R] D.Lv.L.B) : D.Lv.L.B →+* D.Lv.L.B)) ≫ D.Lv.j = D.Lv.j
    rw [hf, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
  have : IsSchemeTheoreticallyDominant (universalObj D.Lv D.hdim D.z₀).Lv.j := D.dom
  have hψ : (D.e.conjAut a).hom.ψ = 𝟙 _ :=
    ext_of_isSchemeTheoreticallyDominant_of_isSeparated
      (universalObj D.Lv D.hdim D.z₀).Lv.c.toSpec
      (by rw [(D.e.conjAut a).hom.ψ_toSpec, Category.id_comp]) _ hj
  -- the map of trees is the identity
  have hover : ∀ x, (uTreeMap (D.e.conjAut a).hom x).1.1 = x.1.1 := fun x ↦ by
    rw [uTreeMap_fst]
    apply Subtype.ext
    change (D.e.conjAut a).hom.ψ _ = _
    rw [hψ]
    rfl
  have hfix : uTreeMap (D.e.conjAut a).hom (canon (hηU D.hdim) t) = canon (hηU D.hdim) t := by
    rw [preservesCanon_aut (D.e.conjAut a) t]
    exact congrArg (canon (hηU D.hdim)) ht
  have htm : uTreeMap (D.e.conjAut a).hom = id :=
    lift_ext hp hp.isCoveringMap (continuous_uTreeMap _) continuous_id
      (funext fun x ↦ hover x) _ hfix
  -- the map of fibres is the identity
  have hfib : ∀ x, fibreMap V hV (D.e.conjAut a).hom x = x :=
    fibreMap_eq_self_of V hV (hp := hp) (hc := hp.countable_fibre) (D.e.conjAut a).hom hφ htm
  have ha : a.hom = D.e.hom ≫ (D.e.conjAut a).hom ≫ D.e.inv := by
    simp [Iso.conjAut_hom, Iso.conj_apply]
  refine Subtype.ext (Equiv.ext fun x ↦ ?_)
  change fibreMap V hV a.hom x = x
  rw [ha, fibreMap_comp_apply, fibreMap_comp_apply, hfib, ← fibreMap_comp_apply,
    Iso.hom_inv_id]
  induction x using Quotient.inductionOn
  rfl
omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma lev_mul (a b : Aut X) : D.lev (a * b) = (D.lev b).comp (D.lev a) := by
  unfold lev
  rw [map_mul, Aut.Aut_mul_def, Iso.trans_hom]
  rfl

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma lev_one : D.lev 1 = AlgHom.id R _ := by
  unfold lev
  rw [map_one]
  rfl

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- `End_R(B)` is finite for the connected finite étale algebra `B` of the level. -/
lemma finite_end : Finite (D.Lv.L.B →ₐ[R] D.Lv.L.B) := by
  obtain ⟨t₀⟩ := D.ne
  haveI : Module.Finite R D.Lv.L.B := D.Lv.L.finite
  haveI : Algebra.Etale R D.Lv.L.B := D.Lv.L.etale
  exact Finite.of_injective (fun φ ↦ t₀.comp φ)
    (fun φ ψ h ↦ algHom_eq_of_comp_eq D.hidem φ ψ t₀ h)

/-- **Stabilizers of vertices in the stage groups are finite**: they embed into `End_R(B)`. -/
theorem finite_stab [Subsingleton A] (t : D.Tr) :
    {σ : stageGroup (tempFibre O R A V hV) X | D.stageTree V hV σ t = t}.Finite := by
  haveI := D.finite_end
  refine Set.Finite.of_finite_image (f := fun σ ↦ D.lev (eq_stageOf σ).choose)
    (Set.toFinite _) fun σ₁ h₁ σ₂ h₂ h ↦ ?_
  set a₁ : Aut X := (eq_stageOf σ₁).choose
  set a₂ : Aut X := (eq_stageOf σ₂).choose
  have e₁ : σ₁ = stageOf a₁ := (eq_stageOf σ₁).choose_spec
  have e₂ : σ₂ = stageOf a₂ := (eq_stageOf σ₂).choose_spec
  have t₁ : D.treeAut a₁ t = t := h₁
  have t₂ : D.treeAut a₂ t = t := h₂
  have hlev : D.lev (a₁⁻¹ * a₂) = AlgHom.id R _ := by
    rw [lev_mul, show D.lev a₂ = D.lev a₁ from h.symm, ← lev_mul, inv_mul_cancel, lev_one]
  have htree : D.treeAut (a₁⁻¹ * a₂) t = t := by
    rw [map_mul, Equiv.Perm.mul_apply, t₂, map_inv, Equiv.Perm.inv_eq_iff_eq, t₁]
  have hc := D.stageOf_eq_one_of_fixed V hV (a₁⁻¹ * a₂) htree hlev
  change stageOfHom (tempFibre O R A V hV) X (a₁⁻¹ * a₂) = 1 at hc
  rw [map_mul, map_inv, inv_mul_eq_one] at hc
  rw [e₁, e₂]
  exact hc

end UData

section Tower

variable {𝒢 : ObjectProperty (TempObj O R A)}
  (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)
  (D : ∀ p : PtGal (tempFibre O R A V hV) 𝒢, UData Ω p.G)

/-- A morphism of Galois objects underlying a pointed morphism. -/
def ptHomMor {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q) : p.G ⟶ q.G :=
  f.2.1.choose

lemma fibreMap_ptHomMor {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q)
    (x : Fibre Ω V hV p.G) : fibreMap V hV (ptHomMor V hV f) x = f.1 x :=
  congrFun f.2.1.choose_spec x

/-- Transition maps are realised by commuting squares of morphisms (on fibres). -/
lemma fibreMap_transition {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q) (a : Aut p.G)
    (b : Aut q.G) (hb : transition hgal hrig f (stageOf a) = stageOf b) :
    fibreMap V hV (a.hom ≫ ptHomMor V hV f) = fibreMap V hV (ptHomMor V hV f ≫ b.hom) := by
  funext x
  rw [fibreMap_comp_apply, fibreMap_comp_apply, fibreMap_ptHomMor, fibreMap_ptHomMor]
  have h := transition_comm hgal hrig f (stageOf a) x
  rw [hb] at h
  exact h.symm

/-- **The tree tower of the curve** on the inverse limit of the stage groups. -/
def stageTower : TreeTower.{u, u, u} (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig)
    (PtGal (tempFibre O R A V hV) 𝒢) where
  G p := stageGroup (tempFibre O R A V hV) p.G
  ρ p :=
    { toFun := fun γ ↦ γ.1 p
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  V p := (D p).Tr
  graph p := treeGraph _ _
  isTree p := isTree_treeGraph
  act p := MulAction.compHom _ ((D p).stageTree V hV)
  adj_smul p σ x y := by
    obtain ⟨a, rfl⟩ := eq_stageOf σ
    change (treeGraph _ _).Adj ((D p).stageTree V hV (stageOf a) x)
      ((D p).stageTree V hV (stageOf a) y) ↔ _
    rw [UData.stageTree_stageOf]
    exact adj_autTree_iff _ x y
  kind p := Tree.kind
  kind_smul p σ x := by
    obtain ⟨a, rfl⟩ := eq_stageOf σ
    change Tree.kind ((D p).stageTree V hV (stageOf a) x) = _
    rw [UData.stageTree_stageOf]
    exact kind_autTree _ x
  kind_adj p x y h := Tree.kind_ne_of_adj h
  map {p q} f := (D p).vmapHom (D q) (ptHomMor V hV f)
  map_smul {p q} f γ x := by
    obtain ⟨a, ha⟩ := eq_stageOf (γ.1 p)
    obtain ⟨b, hb⟩ := eq_stageOf (γ.1 q)
    have hγ : transition hgal hrig f (stageOf a) = stageOf b := by
      rw [← ha, ← hb]
      exact γ.2 f
    change (D p).vmapHom (D q) (ptHomMor V hV f) ((D p).stageTree V hV (γ.1 p) x) =
      (D q).stageTree V hV (γ.1 q) ((D p).vmapHom (D q) (ptHomMor V hV f) x)
    rw [ha, hb, UData.stageTree_stageOf, UData.stageTree_stageOf]
    exact UData.vmapHom_treeAut V hV (D p) (D q) _ a b
      (fibreMap_transition V hV hgal hrig f a b hγ) x
  map_adj {p q} f x y h := (UData.vmapHom_adj (D p) (D q) _ h)

/-- The limit group is closed in the product of the (discrete) stage groups. -/
lemma isClosed_limGroup :
    IsClosed (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig : Set (∀ p : PtGal (tempFibre O R A V hV)
      𝒢, stageGroup (tempFibre O R A V hV) p.G)) := by
  have : (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig : Set (∀ p : PtGal (tempFibre O R A V hV)
      𝒢, stageGroup (tempFibre O R A V hV) p.G)) =
      ⋂ (p : PtGal (tempFibre O R A V hV) 𝒢) (q : PtGal (tempFibre O R A V hV) 𝒢) (f : p ⟶ q),
        {γ | transition hgal hrig f (γ p) = γ q} := by
    ext γ
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    exact ⟨fun h p q f ↦ h f, fun h p q f ↦ h p q f⟩
  rw [this]
  refine isClosed_iInter fun p ↦ isClosed_iInter fun q ↦ isClosed_iInter fun f ↦ ?_
  have hc : Continuous fun γ : ∀ p : PtGal (tempFibre O R A V hV) 𝒢,
      stageGroup (tempFibre O R A V hV) p.G ↦ (γ p, γ q) :=
    (continuous_apply p).prodMk (continuous_apply q)
  exact (isClosed_discrete {x : stageGroup (tempFibre O R A V hV) p.G ×
    stageGroup (tempFibre O R A V hV) q.G | transition hgal hrig f x.1 = x.2}).preimage hc

/-- **Verticial (and edge-like) subgroups of the limit of the stage groups are compact**: their
images in the stage groups fix vertices of the trees, and vertex stabilizers in the stage groups
are finite (`UData.finite_stab`). -/
theorem isCompact_stab [Subsingleton A] (s : (stageTower V hV hgal hrig D).Sys) :
    IsCompact (TreeTower.stab s : Set (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig)) := by
  rw [Topology.IsInducing.subtypeVal.isCompact_iff]
  let F : ∀ p : PtGal (tempFibre O R A V hV) 𝒢, Set (stageGroup (tempFibre O R A V hV) p.G) :=
    fun p ↦ {σ | (D p).stageTree V hV σ (s.1 p) = s.1 p}
  have hK : IsCompact (Set.pi Set.univ F) :=
    isCompact_univ_pi fun p ↦ ((D p).finite_stab V hV (s.1 p)).isCompact
  refine hK.of_isClosed_subset ?_ ?_
  · have : Subtype.val '' (TreeTower.stab s : Set (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig)) =
        (limGroup (tempFibre O R A V hV) 𝒢 hgal hrig : Set (∀ p : PtGal (tempFibre O R A V hV)
          𝒢, stageGroup (tempFibre O R A V hV) p.G)) ∩ Set.pi Set.univ F := by
      ext γ
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        exact ⟨γ.2, fun p _ ↦ TreeTower.mem_stab.1 hγ p⟩
      · rintro ⟨hγ, hF⟩
        exact ⟨⟨γ, hγ⟩, TreeTower.mem_stab.2 fun p ↦ hF p trivial, rfl⟩
    have h₂ := (isClosed_limGroup V hV hgal hrig).inter
      (isClosed_set_pi fun p (_ : p ∈ Set.univ) ↦ isClosed_discrete (F p))
    rwa [← this] at h₂
  · rintro _ ⟨γ, hγ, rfl⟩ p -
    exact TreeTower.mem_stab.1 hγ p

end Tower

end

end TemperedFundamentalGroups
