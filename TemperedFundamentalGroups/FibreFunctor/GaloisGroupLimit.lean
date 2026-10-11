/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.FibreFunctor.GaloisLimit

/-!
# Automorphisms of a fibre functor as an inverse limit of groups (Blueprint §11.2, G6)

The group form of K1 (`FibreFunctor/GaloisLimit.lean`). Let `Φ : C ⥤ Type w` and `𝒢` a class of
objects satisfying (gal) and (rig).

* `stageGroup Φ G`: the **stage group** of `G`, the group of permutations of `Φ G` induced by
  automorphisms of `G`. For `G ∈ 𝒢` it acts simply transitively on `Φ G`
  (`stageGroup_eq_of_apply_eq`, `exists_stageGroup_apply_eq`), so evaluation at the base point is
  a bijection `stageEquiv p : stageGroup Φ p.G ≃ Φ p.G` for a pointed Galois object `p`.
* `transition f : stageGroup Φ p.G →* stageGroup Φ q.G` for a pointed morphism `f : p ⟶ q`: the
  unique `τ` with `τ ∘ f = f ∘ σ` (`transition_comm`); `transition_id`, `transition_comp`.
* `limGroup Φ 𝒢`: the inverse limit of the stage groups along the transition maps.
* `fibreAutHomeo`: the same as an isomorphism of topological groups, `limGroup` carrying the
  inverse-limit topology of the discrete stage groups.
* `fibreAutEquiv`: with (dom), **`FibreAut Φ ≃* limGroup Φ 𝒢`**: an automorphism `α` of `Φ`
  corresponds to the family of stage group elements `σ_p` with `σ_p(p.g) = α⁻¹(p.g)`
  (`fibreAutEquiv_apply`). (Evaluating `α` itself gives an anti-isomorphism, `fibreAutEquivOp`.)
-/

universe w v u

open CategoryTheory Pi1.Orbifold Pi1.Orbifold.FibreAut

namespace TemperedFundamentalGroups

namespace GaloisLimit

variable {C : Type u} [Category.{v} C] (Φ : C ⥤ Type w) {𝒢 : ObjectProperty C}

/-- **The stage group** of `G`: the permutations of `Φ G` induced by automorphisms of `G`. -/
def stageGroup (G : C) : Subgroup (Equiv.Perm (Φ.obj G)) where
  carrier := {σ | ∃ a : G ≅ G, ⇑σ = Φ.map a.hom}
  mul_mem' := by
    rintro σ τ ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨b ≪≫ a, ?_⟩
    rw [Equiv.Perm.coe_mul, ha, hb, Iso.trans_hom, Functor.map_comp]
    rfl
  one_mem' := ⟨Iso.refl G, by rw [Iso.refl_hom, Φ.map_id]; rfl⟩
  inv_mem' := by
    rintro σ ⟨a, ha⟩
    refine ⟨a.symm, funext fun x ↦ ?_⟩
    apply σ.injective
    change σ (σ.symm x) = _
    rw [Equiv.apply_symm_apply, ha, Iso.symm_hom, ← Functor.map_comp_apply, a.inv_hom_id,
      Φ.map_id]
    rfl

variable {Φ}

lemma mem_stageGroup {G : C} {σ : Equiv.Perm (Φ.obj G)} :
    σ ∈ stageGroup Φ G ↔ ∃ a : G ≅ G, ⇑σ = Φ.map a.hom := Iff.rfl

/-- The permutation of an automorphism. -/
def stageOf {G : C} (a : G ≅ G) : stageGroup Φ G :=
  ⟨(Φ.mapIso a).toEquiv, a, rfl⟩

@[simp]
lemma stageOf_apply {G : C} (a : G ≅ G) (x : Φ.obj G) : (stageOf (Φ := Φ) a).1 x = Φ.map a.hom x :=
  rfl

/-- **Freeness**: two elements of the stage group of `G ∈ 𝒢` agreeing at one point are equal. -/
lemma stageGroup_eq_of_apply_eq (hrig : IsRigid Φ 𝒢) {G : C} (hG : 𝒢 G)
    {σ τ : stageGroup Φ G} {x : Φ.obj G} (h : σ.1 x = τ.1 x) : σ = τ := by
  obtain ⟨σ, a, ha⟩ := σ
  obtain ⟨τ, b, hb⟩ := τ
  apply Subtype.ext
  apply Equiv.ext
  intro y
  change σ y = τ y
  rw [ha, hb, hrig G hG a.hom b.hom x (by rw [← ha, ← hb]; exact h)]

/-- **Transitivity**: the stage group of `G ∈ 𝒢` acts transitively on `Φ G`. -/
lemma exists_stageGroup_apply_eq (hgal : IsGaloisClass Φ 𝒢) {G : C} (hG : 𝒢 G)
    (x y : Φ.obj G) : ∃ σ : stageGroup Φ G, σ.1 x = y := by
  obtain ⟨a, ha⟩ := hgal G hG x y
  exact ⟨stageOf a, ha⟩

/-- **Stage group elements commute with automorphisms of `Φ`.** -/
lemma app_stageGroup (α : FibreAut Φ) {G : C} (σ : stageGroup Φ G) (x : Φ.obj G) :
    α.app G (σ.1 x) = σ.1 (α.app G x) := by
  obtain ⟨σ, a, ha⟩ := σ
  change α.app G (σ x) = σ (α.app G x)
  rw [ha, app_naturality]

variable (hgal : IsGaloisClass Φ 𝒢) (hrig : IsRigid Φ 𝒢)

/-- **The stage group is a torsor**: evaluation at the base point of a pointed Galois object. -/
noncomputable def stageEquiv (p : PtGal Φ 𝒢) : stageGroup Φ p.G ≃ Φ.obj p.G :=
  Equiv.ofBijective (fun σ ↦ σ.1 p.g)
    ⟨fun _ _ h ↦ stageGroup_eq_of_apply_eq hrig p.mem h,
      fun y ↦ exists_stageGroup_apply_eq hgal p.mem p.g y⟩

@[simp]
lemma stageEquiv_apply (p : PtGal Φ 𝒢) (σ : stageGroup Φ p.G) :
    stageEquiv hgal hrig p σ = σ.1 p.g := rfl

@[simp]
lemma stageEquiv_symm_apply_g (p : PtGal Φ 𝒢) (y : Φ.obj p.G) :
    ((stageEquiv hgal hrig p).symm y).1 p.g = y :=
  (stageEquiv hgal hrig p).apply_symm_apply y

/-- The value of the transition map (before proving it is a homomorphism). -/
noncomputable def transitionFun {p q : PtGal Φ 𝒢} (f : p ⟶ q) (σ : stageGroup Φ p.G) :
    stageGroup Φ q.G :=
  (stageEquiv hgal hrig q).symm (f.1 (σ.1 p.g))

/-- **The transition map intertwines `f`**: `τ (f x) = f (σ x)`. -/
lemma transitionFun_comm {p q : PtGal Φ 𝒢} (f : p ⟶ q) (σ : stageGroup Φ p.G) (x : Φ.obj p.G) :
    (transitionFun hgal hrig f σ).1 (f.1 x) = f.1 (σ.1 x) := by
  obtain ⟨⟨F, hF⟩, hf⟩ := f.2
  set τ := transitionFun hgal hrig f σ
  have hτ : τ.1 q.g = f.1 (σ.1 p.g) := stageEquiv_symm_apply_g hgal hrig q _
  obtain ⟨σ', a, ha⟩ := σ
  obtain ⟨τ', b, hb⟩ := τ
  change τ' q.g = f.1 (σ' p.g) at hτ
  change τ' (f.1 x) = f.1 (σ' x)
  have key : Φ.map (a.hom ≫ F) = Φ.map (F ≫ b.hom) := by
    refine hrig _ p.mem _ _ p.g ?_
    rw [Functor.map_comp_apply, Functor.map_comp_apply, hF, hf, ← hb, hτ, ha, ← hF]
  have := ConcreteCategory.congr_hom key x
  rw [Functor.map_comp_apply, Functor.map_comp_apply] at this
  rw [hb, ha, ← hF, ← this]

/-- **The transition homomorphism** `stageGroup Φ p.G →* stageGroup Φ q.G` along a pointed
morphism: the unique `τ` with `τ ∘ f = f ∘ σ`. -/
noncomputable def transition {p q : PtGal Φ 𝒢} (f : p ⟶ q) :
    stageGroup Φ p.G →* stageGroup Φ q.G where
  toFun := transitionFun hgal hrig f
  map_one' := by
    refine stageGroup_eq_of_apply_eq hrig q.mem (x := f.1 p.g) ?_
    rw [transitionFun_comm]
    rfl
  map_mul' σ τ := by
    refine stageGroup_eq_of_apply_eq hrig q.mem (x := f.1 p.g) ?_
    rw [transitionFun_comm, Subgroup.coe_mul, Subgroup.coe_mul, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, transitionFun_comm, transitionFun_comm]

lemma transition_comm {p q : PtGal Φ 𝒢} (f : p ⟶ q) (σ : stageGroup Φ p.G) (x : Φ.obj p.G) :
    (transition hgal hrig f σ).1 (f.1 x) = f.1 (σ.1 x) :=
  transitionFun_comm hgal hrig f σ x

/-- The transition map is characterised by `τ (q.g) = f (σ p.g)`. -/
lemma transition_eq_iff {p q : PtGal Φ 𝒢} (f : p ⟶ q) (σ : stageGroup Φ p.G)
    (τ : stageGroup Φ q.G) : transition hgal hrig f σ = τ ↔ τ.1 q.g = f.1 (σ.1 p.g) := by
  have h₀ := transition_comm hgal hrig f σ p.g
  rw [f.2.2] at h₀
  constructor
  · rintro rfl
    exact h₀
  · intro h
    exact stageGroup_eq_of_apply_eq hrig q.mem (x := q.g) (h₀.trans h.symm)

lemma transition_id (p : PtGal Φ 𝒢) (σ : stageGroup Φ p.G) :
    transition hgal hrig (𝟙 p) σ = σ :=
  (transition_eq_iff hgal hrig _ σ σ).2 rfl

lemma transition_comp {p q r : PtGal Φ 𝒢} (f : p ⟶ q) (g : q ⟶ r) (σ : stageGroup Φ p.G) :
    transition hgal hrig (f ≫ g) σ = transition hgal hrig g (transition hgal hrig f σ) := by
  refine (transition_eq_iff hgal hrig _ σ _).2 ?_
  have h₁ := transition_comm hgal hrig g (transition hgal hrig f σ) q.g
  have h₂ := transition_comm hgal hrig f σ p.g
  rw [g.2.2] at h₁
  rw [f.2.2] at h₂
  rw [h₁, h₂]
  rfl

variable (Φ 𝒢) in
/-- **The inverse limit of the stage groups** along the transition maps. -/
def limGroup : Subgroup (∀ p : PtGal Φ 𝒢, stageGroup Φ p.G) where
  carrier := {γ | ∀ {p q : PtGal Φ 𝒢} (f : p ⟶ q), transition hgal hrig f (γ p) = γ q}
  mul_mem' := fun {γ γ'} hγ hγ' {p q} f ↦ by
    simp only [Pi.mul_apply, map_mul, hγ f, hγ' f]
  one_mem' := fun {p q} f ↦ by simp only [Pi.one_apply, map_one]
  inv_mem' := fun {γ} hγ {p q} f ↦ by simp only [Pi.inv_apply, map_inv, hγ f]

/-- The family of stage group elements of an automorphism of `Φ`: `σ_p (p.g) = α (p.g)`. -/
noncomputable def toStage (α : FibreAut Φ) : limGroup Φ 𝒢 hgal hrig :=
  ⟨fun p ↦ (stageEquiv hgal hrig p).symm (α.app p.G p.g), fun {p q} f ↦ by
    rw [transition_eq_iff, stageEquiv_symm_apply_g, stageEquiv_symm_apply_g]
    obtain ⟨⟨F, hF⟩, hf⟩ := f.2
    have := app_naturality α F p.g
    rw [hF, hf] at this
    exact this⟩

lemma toStage_apply (α : FibreAut Φ) (p : PtGal Φ 𝒢) :
    ((toStage hgal hrig α).1 p).1 p.g = α.app p.G p.g :=
  stageEquiv_symm_apply_g hgal hrig p _

/-- The compatible family of a point of the limit group. -/
lemma isCompatible_of_mem (γ : limGroup Φ 𝒢 hgal hrig) :
    IsCompatible (fun p ↦ (γ.1 p).1 p.g) := fun {p q} f ↦ by
  have h₀ := transition_comm hgal hrig f (γ.1 p) p.g
  rw [f.2.2, γ.2 f] at h₀
  exact h₀.symm

/-- `toStage` is an anti-homomorphism. -/
lemma toStage_mul (α β : FibreAut Φ) :
    toStage hgal hrig (α * β) = toStage hgal hrig β * toStage hgal hrig α := by
  apply Subtype.ext
  funext p
  refine stageGroup_eq_of_apply_eq hrig p.mem (x := p.g) ?_
  change ((toStage hgal hrig (α * β)).1 p).1 p.g =
    ((toStage hgal hrig β).1 p).1 (((toStage hgal hrig α).1 p).1 p.g)
  have hβ := toStage_apply hgal hrig β p
  have hα := toStage_apply hgal hrig α p
  rw [toStage_apply, mul_app, ← hβ, app_stageGroup, hα]

lemma toStage_one : toStage hgal hrig (1 : FibreAut Φ) = 1 := by
  apply Subtype.ext
  funext p
  refine stageGroup_eq_of_apply_eq hrig p.mem (x := p.g) ?_
  rw [toStage_apply, one_app]
  rfl

lemma toStage_inv (α : FibreAut Φ) : toStage hgal hrig α⁻¹ = (toStage hgal hrig α)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← toStage_mul, inv_mul_cancel, toStage_one]

variable (hdom : IsDominating Φ 𝒢)

/-- **K1, group form (opposite)**: `α ↦ (σ_p)` with `σ_p(p.g) = α(p.g)` is an isomorphism of
`FibreAut Φ` with the opposite of the inverse limit of the stage groups. -/
noncomputable def fibreAutEquivOp : FibreAut Φ ≃* (limGroup Φ 𝒢 hgal hrig)ᵐᵒᵖ where
  toFun α := MulOpposite.op (toStage hgal hrig α)
  invFun γ := TemperedFundamentalGroups.FibreAut.ofCompatible hgal hdom hrig _
    (isCompatible_of_mem hgal hrig γ.unop)
  left_inv α := by
    apply (TemperedFundamentalGroups.FibreAut.compatibleEquiv hgal hdom hrig).injective
    apply Subtype.ext
    funext p
    change (TemperedFundamentalGroups.FibreAut.ofCompatible hgal hdom hrig _ _).app p.G p.g =
      α.app p.G p.g
    rw [TemperedFundamentalGroups.FibreAut.ofCompatible_app_pt, MulOpposite.unop_op, toStage_apply]
  right_inv γ := by
    apply MulOpposite.unop_injective
    apply Subtype.ext
    funext p
    refine stageGroup_eq_of_apply_eq hrig p.mem (x := p.g) ?_
    rw [MulOpposite.unop_op, toStage_apply, TemperedFundamentalGroups.FibreAut.ofCompatible_app_pt]
  map_mul' α β := by
    rw [toStage_mul, MulOpposite.op_mul]

/-- **K1, group form**: `FibreAut Φ ≃* lim_p stageGroup Φ p.G`, `α ↦ (σ_p)` with
`σ_p(p.g) = α⁻¹(p.g)`. -/
noncomputable def fibreAutEquiv : FibreAut Φ ≃* limGroup Φ 𝒢 hgal hrig :=
  (fibreAutEquivOp hgal hrig hdom).trans (MulEquiv.inv' _).symm

lemma fibreAutEquiv_apply (α : FibreAut Φ) (p : PtGal Φ 𝒢) :
    ((fibreAutEquiv hgal hrig hdom α).1 p).1 p.g = α⁻¹.app p.G p.g := by
  change ((MulOpposite.unop (MulOpposite.op (toStage hgal hrig α)))⁻¹.1 p).1 p.g = _
  rw [MulOpposite.unop_op, ← toStage_inv, toStage_apply]

section Topology

/-- The stage groups carry the discrete topology. -/
instance (G : C) : TopologicalSpace (stageGroup Φ G) := ⊥

instance (G : C) : DiscreteTopology (stageGroup Φ G) := ⟨rfl⟩

lemma fibreAutEquiv_eq_iff (α : FibreAut Φ) (p : PtGal Φ 𝒢) (s : stageGroup Φ p.G) :
    (fibreAutEquiv hgal hrig hdom α).1 p = s ↔ α⁻¹.app p.G p.g = s.1 p.g := by
  constructor
  · rintro rfl
    exact (fibreAutEquiv_apply hgal hrig hdom α p).symm
  · intro h
    exact stageGroup_eq_of_apply_eq hrig p.mem (x := p.g)
      ((fibreAutEquiv_apply hgal hrig hdom α p).trans h)

lemma continuous_fibreAutEquiv : Continuous (fibreAutEquiv hgal hrig hdom) := by
  refine continuous_induced_rng.2 (continuous_pi fun p ↦ continuous_discrete_rng.2 fun s ↦ ?_)
  have : (fun α : FibreAut Φ ↦ (fibreAutEquiv hgal hrig hdom α).1 p) ⁻¹' {s} =
      (fun α : FibreAut Φ ↦ α⁻¹) ⁻¹' {β : FibreAut Φ | β.app p.G p.g = s.1 p.g} := by
    ext α
    exact fibreAutEquiv_eq_iff hgal hrig hdom α p s
  change IsOpen ((fun α : FibreAut Φ ↦ (fibreAutEquiv hgal hrig hdom α).1 p) ⁻¹' {s})
  rw [this]
  exact (isOpen_setOf_app_eq Φ p.G p.g _).preimage continuous_inv

lemma continuous_fibreAutEquiv_symm : Continuous (fibreAutEquiv hgal hrig hdom).symm := by
  classical
  refine continuous_of_stabilizer Φ (fibreAutEquiv hgal hrig hdom).symm.toMonoidHom
    fun S ↦ ?_
  set L := S.toList
  obtain ⟨G, hG, g, f, hf⟩ := hdom L.length fun i ↦ L.get i
  let q : PtGal Φ 𝒢 := ⟨G, hG, g⟩
  have hcq : Continuous (fun γ : limGroup Φ 𝒢 hgal hrig ↦ γ.1 q) :=
    (continuous_apply q).comp continuous_subtype_val
  have hopen : IsOpen {γ : limGroup Φ 𝒢 hgal hrig | γ.1 q = 1} :=
    hcq.isOpen_preimage {1} (isOpen_discrete _)
  refine Filter.mem_of_superset (hopen.mem_nhds rfl) fun γ hγ ↦ ?_
  set α := (fibreAutEquiv hgal hrig hdom).symm γ
  have hα : α.app G g = g := by
    have h₁ := (fibreAutEquiv_eq_iff hgal hrig hdom α q 1).1
      (by rw [MulEquiv.apply_symm_apply]; exact hγ)
    change α⁻¹.app G g = g at h₁
    calc α.app G g = α.app G (α⁻¹.app G g) := by rw [h₁]
      _ = g := app_inv_app α G g
  intro x hx
  obtain ⟨i, hi⟩ := List.mem_iff_get.1 (Finset.mem_toList.2 hx)
  change α.app x.1 x.2 = x.2
  rw [← hi, ← hf i, app_naturality, hα]

/-- **K1, topological group form**: `FibreAut Φ ≃ₜ* lim_p stageGroup Φ p.G` for the
inverse-limit topology of the discrete stage groups. -/
noncomputable def fibreAutHomeo : FibreAut Φ ≃ₜ* limGroup Φ 𝒢 hgal hrig :=
  { fibreAutEquiv hgal hrig hdom with
    continuous_toFun := continuous_fibreAutEquiv hgal hrig hdom
    continuous_invFun := continuous_fibreAutEquiv_symm hgal hrig hdom }

end Topology

end GaloisLimit

end TemperedFundamentalGroups
