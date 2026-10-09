/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.Pullback
import TemperedFundamentalGroups.Topology.UniversalCovering

/-!
# Galois objects of the tempered category (K3, topological part)

Blueprint §10.3.3, K3. Let `Lv` be a level with a model with finite `H`, and let `p : Z̃ → Z` be a
universal covering (N1, `IsUniversalCovering`) of its special fibre `Z`, with countable fibres.

* `Pi Lv p`: the group `Π` of pairs `(g, g̃)`, `g ∈ H`, `g̃ : Z̃ ≃ₜ Z̃` with `p ∘ g̃ = g • p`.
  `toH_surjective`: `Π → H` is surjective (`Z` connected); `kerEquiv`: its kernel is the deck
  group of `p`.
* `obj Lv hp hc`: **the Galois object** `U_Lv = (Lv, Ind_1^H Z̃)`. The `H`-equivariant covering
  `Ind_1^H Z̃ = H × Z̃ → Z`, `(g, e) ↦ g • p e`, is isomorphic to `(Z̃ × Π)/π₁`; it is coded in
  `Z × ℕ` by `CoveringCode.ofCovering` (any covering with countable fibres).
  `universalObj`: the instance for the universal covering `universalCovering` of N1.
* `deck : Pi Lv p →* Aut (obj Lv hp hc)`: deck transformations `(g, e) ↦ (g π₁⁻¹, π₂ e)`.
* `existsUnique_deck` (**Galois**, scheme case `[Subsingleton A]`): if `H⁰` acts simply
  transitively on `F_L`, then `Π` acts simply transitively on `Φ(U_Lv)` through `deck`.
* `hom_ext` (**rigidity**, relative): two morphisms `U_Lv ⟶ X` with equal level and model parts
  that agree at one point of the covering space are equal.
* `fibreMap_eq_of_eq` (**rigidity on fibres**): if `j` is scheme-theoretically dominant and maps
  into `B` are determined by one geometric point, two morphisms `U_Lv ⟶ X` that agree on one
  point of `Φ(U_Lv)` induce the same map `Φ(U_Lv) → Φ(X)`.
* `conjHom`, `fibreMap_conjHom`, `conjHom_ne_id`: the action of `k ∈ H⁰` is an endomorphism of
  every object inducing the identity on `Φ`; so automorphism groups never act freely on fibres
  when `H⁰ ≠ 1`, and Galois/rigidity statements must be formulated after applying `Φ`.
* `exists_hom_fibreMap` (**pointwise domination** over a fixed equivariant `ℓ : Lv ⟶ X.Lv`):
  every point of `Φ X` over the image of a geometric point of `Lv` is hit by a morphism
  `liftHom : U_Lv ⟶ X` over `ℓ`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold Topology Set

section Sigma

variable {ι X : Type*} [TopologicalSpace X] {E : ι → Type*} [∀ i, TopologicalSpace (E i)]

/-- **A finite disjoint union of covering maps** over the same base is a covering map. -/
theorem IsCoveringMap.sigma [Finite ι] {f : ∀ i, E i → X} (hf : ∀ i, IsCoveringMap (f i)) :
    IsCoveringMap (fun y : Σ i, E i => f y.1 y.2) := by
  intro x
  choose hd U hxU hU hfU H hH using fun i => hf i x
  have hW : IsOpen (⋂ i, U i) := isOpen_iInter_of_finite hU
  have hWU : ∀ i, (⋂ i, U i) ⊆ U i := iInter_subset U
  have hmem : ∀ y : (fun y : Σ i, E i => f y.1 y.2) ⁻¹' (⋂ i, U i),
      y.1.2 ∈ f y.1.1 ⁻¹' U y.1.1 := fun y => hWU y.1.1 y.2
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Σ i, f i ⁻¹' {x})
    ⟨inferInstance, ⋂ i, U i, mem_iInter.2 hxU, hW, isOpen_sigma_iff.2 fun i =>
      hW.preimage (hf i).continuous, ?_⟩
  let T : (fun y : Σ i, E i => f y.1 y.2) ⁻¹' (⋂ i, U i) → (⋂ i, U i : Set X) ×
      Σ i, f i ⁻¹' {x} := fun y => (⟨f y.1.1 y.1.2, y.2⟩, ⟨y.1.1, (H y.1.1 ⟨y.1.2, hmem y⟩).2⟩)
  have hT : Continuous T := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    obtain ⟨⟨i, e⟩, hy⟩ := y
    let s : f i ⁻¹' (⋂ i, U i) → (fun y : Σ i, E i => f y.1 y.2) ⁻¹' (⋂ i, U i) :=
      fun e => ⟨⟨i, e.1⟩, e.2⟩
    have hs : IsInducing s := (IsInducing.subtypeVal.of_comp_iff).1
      (IsEmbedding.sigmaMk.isInducing.comp IsInducing.subtypeVal)
    have hr : range s ∈ 𝓝 (s ⟨e, hy⟩) := by
      refine IsOpen.mem_nhds ?_ (mem_range_self (f := s) ⟨e, hy⟩)
      have : range s = Subtype.val ⁻¹' range (Sigma.mk i) := by
        ext ⟨⟨j, e'⟩, h⟩
        constructor
        · rintro ⟨e'', he''⟩
          exact ⟨e''.1, congrArg Subtype.val he''⟩
        · rintro ⟨e'', he''⟩
          cases he''
          exact ⟨⟨e'', h⟩, rfl⟩
      rw [this]
      exact isOpen_range_sigmaMk.preimage continuous_subtype_val
    refine (hs.continuousAt_iff' hr).1 (Continuous.continuousAt ?_)
    refine Continuous.prodMk (Continuous.subtype_mk ((hf i).continuous.comp
      continuous_subtype_val) _) (continuous_sigmaMk.comp ?_)
    exact continuous_snd.comp ((H i).continuous.comp (Continuous.subtype_mk
      continuous_subtype_val _))
  refine ⟨{ toFun := T
            invFun := fun w => ⟨⟨w.2.1, ((H w.2.1).symm (⟨w.1.1, hWU _ w.1.2⟩, w.2.2)).1⟩, by
              change f w.2.1 _ ∈ (⋂ i, U i : Set X)
              rw [← hH, Homeomorph.apply_symm_apply]
              exact w.1.2⟩
            left_inv := fun y => ?_
            right_inv := fun w => ?_
            continuous_toFun := hT
            continuous_invFun := ?_ }, fun _ => rfl⟩
  · obtain ⟨⟨i, e⟩, hy⟩ := y
    have h : ((⟨f i e, hWU i hy⟩ : U i), (H i ⟨e, hWU i hy⟩).2) = H i ⟨e, hWU i hy⟩ :=
      Prod.ext (Subtype.ext (hH i ⟨e, hWU i hy⟩).symm) rfl
    apply Subtype.ext
    change (⟨i, ((H i).symm ((⟨f i e, _⟩ : U i), (H i ⟨e, _⟩).2)).1⟩ : Σ i, E i) = ⟨i, e⟩
    rw [h, Homeomorph.symm_apply_apply]
  · obtain ⟨⟨z, hz⟩, ⟨i, a⟩⟩ := w
    have h₁ : f i ((H i).symm (⟨z, hWU i hz⟩, a)).1 = z := by
      rw [← hH, Homeomorph.apply_symm_apply]
    refine Prod.ext (Subtype.ext h₁) ?_
    change (⟨i, (H i ⟨((H i).symm (⟨z, hWU i hz⟩, a)).1, _⟩).2⟩ : Σ i, f i ⁻¹' {x}) = ⟨i, a⟩
    simp
  · refine continuous_prod_of_discrete_right.2 fun b => ?_
    obtain ⟨i, a⟩ := b
    refine Continuous.subtype_mk (continuous_sigmaMk.comp (continuous_subtype_val.comp
      ((H i).symm.continuous.comp ?_))) _
    change Continuous fun v : (⋂ i, U i : Set X) => ((⟨v.1, hWU i v.2⟩ : U i), a)
    fun_prop

end Sigma

/-- The range of a covering map is closed (and open). -/
theorem IsCoveringMap.isClosed_range {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {f : E → X} (hf : IsCoveringMap f) : IsClosed (range f) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, U, hxU, hU, _, H, hH⟩ := hf x
  refine ⟨U, fun y hy ⟨e, he⟩ => hx ?_, hU, hxU⟩
  have hy' : f e ∈ U := he ▸ hy
  obtain ⟨e', he'⟩ := (H ⟨e, hy'⟩).2
  exact ⟨e', he'⟩

/-- A covering map with nonempty domain onto a connected space is surjective. -/
theorem IsCoveringMap.surjective_of_connectedSpace {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [ConnectedSpace X] [Nonempty E] {f : E → X} (hf : IsCoveringMap f) :
    Function.Surjective f := by
  have h := IsClopen.eq_univ ⟨hf.isClosed_range, hf.isOpenMap.isOpen_range⟩
    (range_nonempty f)
  exact range_eq_univ.1 h

namespace TemperedFundamentalGroups

namespace CoveringCode

variable {Z : Type u} [TopologicalSpace Z] {G : Type u} [Group G] {ρ : G →* (Z ≃ₜ Z)}
  {E : Type u} [TopologicalSpace E] {q : E → Z}

section OfCovering

variable (hc : ∀ z, (q ⁻¹' {z}).Countable)

/-- An injective coding of each fibre of `q` by natural numbers. -/
noncomputable def fibreIndex (z : Z) : q ⁻¹' {z} → ℕ :=
  have := (hc z).to_subtype
  Classical.choose (Countable.exists_injective_nat (q ⁻¹' {z}))

omit [TopologicalSpace Z] [TopologicalSpace E] in
lemma fibreIndex_injective (z : Z) : Function.Injective (fibreIndex hc z) :=
  have := (hc z).to_subtype
  Classical.choose_spec (Countable.exists_injective_nat (q ⁻¹' {z}))

/-- The coding map `E → Z × ℕ`: a point goes to its image and its index in its fibre. -/
noncomputable def codeMap (x : E) : Z × ℕ := (q x, fibreIndex hc (q x) ⟨x, rfl⟩)

omit [TopologicalSpace Z] [TopologicalSpace E] in
lemma codeMap_injective : Function.Injective (codeMap hc) := by
  intro x y h
  have h₁ : q x = q y := congrArg Prod.fst h
  have key : ∀ (z : Z) (hx : q x = z) (hy : q y = z),
      fibreIndex hc z ⟨x, hx⟩ = fibreIndex hc z ⟨y, hy⟩ → x = y := fun z hx hy h =>
    congrArg Subtype.val (fibreIndex_injective hc z h)
  refine key (q y) h₁ rfl ?_
  have h₂ : fibreIndex hc (q x) ⟨x, rfl⟩ = fibreIndex hc (q y) ⟨y, rfl⟩ := congrArg Prod.snd h
  rw [← h₂]
  clear key h₂ h
  generalize hz : q y = z at h₁
  subst h₁
  rfl

/-- The bijection of `E` with the coded carrier. -/
noncomputable def codeEquiv : E ≃ range (codeMap hc) where
  toFun x := ⟨codeMap hc x, x, rfl⟩
  invFun y := y.2.choose
  left_inv x := codeMap_injective hc
    (Exists.choose_spec (⟨x, rfl⟩ : ∃ x', codeMap hc x' = codeMap hc x))
  right_inv y := Subtype.ext y.2.choose_spec

/-- The topology of the coded carrier, transported from `E`. -/
@[implicit_reducible]
noncomputable def codeTop : TopologicalSpace (range (codeMap hc)) :=
  TopologicalSpace.induced (codeEquiv hc).symm inferInstance

/-- The coded carrier is homeomorphic to `E`. -/
noncomputable def codeHomeomorph : @Homeomorph E (range (codeMap hc)) _ (codeTop hc) :=
  letI := codeTop hc
  { codeEquiv hc with
    continuous_toFun := continuous_induced_rng.2
      (continuous_id.congr fun x => ((codeEquiv hc).left_inv x).symm)
    continuous_invFun := continuous_induced_dom }

variable (hq : IsCoveringMap q) (act : G →* (E ≃ₜ E)) (hact : ∀ g x, q (act g x) = ρ g (q x))
include hq hact

/-- **A covering with countable fibres as a covering code**: the `G`-equivariant covering
`q : E → Z` (with countable fibres), coded inside `Z × ℕ`. -/
noncomputable def ofCovering : CoveringCode ρ :=
  letI := codeTop hc
  { carrier := range (codeMap hc)
    top := codeTop hc
    isCoveringMap := by
      have h := hq.comp_homeomorph (codeHomeomorph hc).symm
      convert h using 1
      funext x
      change (x : Z × ℕ).1 = q ((codeHomeomorph hc).symm x)
      conv_lhs => rw [← (codeHomeomorph hc).apply_symm_apply x]
      rfl
    act :=
      { toFun g := ((codeHomeomorph hc).symm.trans (act g)).trans (codeHomeomorph hc)
        map_one' := by
          ext x : 1
          simp
        map_mul' g g' := by
          ext x : 1
          simp }
    act_fst g x := by
      change q (act g ((codeHomeomorph hc).symm x)) = ρ g (x : Z × ℕ).1
      rw [hact]
      conv_rhs => rw [← (codeHomeomorph hc).apply_symm_apply x]
      rfl }

/-- The homeomorphism of `E` with the carrier of `ofCovering`. -/
noncomputable def ofCoveringHomeomorph : E ≃ₜ (ofCovering hc hq act hact).carrier :=
  codeHomeomorph hc

@[simp] lemma ofCoveringHomeomorph_fst (x : E) :
    (ofCoveringHomeomorph hc hq act hact x).1.1 = q x := rfl

lemma ofCovering_act (g : G) (x : E) :
    (ofCovering hc hq act hact).act g (ofCoveringHomeomorph hc hq act hact x) =
      ofCoveringHomeomorph hc hq act hact (act g x) := by
  change ofCoveringHomeomorph hc hq act hact (act g ((ofCoveringHomeomorph hc hq act hact).symm
    (ofCoveringHomeomorph hc hq act hact x))) = _
  rw [Homeomorph.symm_apply_apply]

end OfCovering

end CoveringCode


namespace GaloisObject

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

section Space

variable (Lv : Level O R A) (E : Type u) [TopologicalSpace E]

/-- The induced space `Ind_1^H E = H × E`, a disjoint union of copies of `E` indexed by `H`. -/
abbrev IndSpace : Type u := Σ _ : Lv.L.H, E

/-- The action of `H` on `Ind_1^H E` by left translation of the index. -/
def indAct : Lv.L.H →* (IndSpace Lv E ≃ₜ IndSpace Lv E) where
  toFun g :=
    { toFun := fun x => ⟨g * x.1, x.2⟩
      invFun := fun x => ⟨g⁻¹ * x.1, x.2⟩
      left_inv := fun x => by simp
      right_inv := fun x => by simp
      continuous_toFun := continuous_sigma fun i =>
        continuous_sigmaMk (σ := fun _ : Lv.L.H => E) (i := g * i)
      continuous_invFun := continuous_sigma fun i =>
        continuous_sigmaMk (σ := fun _ : Lv.L.H => E) (i := g⁻¹ * i) }
  map_one' := Homeomorph.ext fun x => Sigma.ext (one_mul _) HEq.rfl
  map_mul' g g' := Homeomorph.ext fun x => Sigma.ext (mul_assoc _ _ _) HEq.rfl

@[simp] lemma indAct_apply (g : Lv.L.H) (x : IndSpace Lv E) :
    indAct Lv E g x = ⟨g * x.1, x.2⟩ := rfl

variable {Lv E} (p : E → Lv.Z)

/-- The projection `Ind_1^H E → Z`, `(g, e) ↦ g • p e`. -/
def indProj (x : IndSpace Lv E) : Lv.Z := Lv.ρs x.1 (p x.2)

lemma indProj_act (g : Lv.L.H) (x : IndSpace Lv E) :
    indProj p (indAct Lv E g x) = Lv.ρs g (indProj p x) := by
  simp [indProj, map_mul, Homeomorph.mul_apply]

omit [TopologicalSpace E] in
lemma indProj_one (e : E) : indProj p (⟨1, e⟩ : IndSpace Lv E) = p e := by
  simp [indProj]

lemma isCoveringMap_indProj [Finite Lv.L.H] (hp : IsCoveringMap p) :
    IsCoveringMap (indProj p) :=
  IsCoveringMap.sigma fun g => hp.homeomorph_comp (Lv.ρs g)

omit [TopologicalSpace E] in
lemma countable_indProj_fibre [Countable Lv.L.H] (hc : ∀ z, (p ⁻¹' {z}).Countable) (z : Lv.Z) :
    (indProj p ⁻¹' {z}).Countable := by
  have h : (⋃ g : Lv.L.H, (fun e : E => (⟨g, e⟩ : IndSpace Lv E)) ''
      (p ⁻¹' {(Lv.ρs g).symm z})).Countable :=
    countable_iUnion fun g => (hc _).image _
  refine h.mono ?_
  rintro ⟨g, e⟩ (he : Lv.ρs g (p e) = z)
  refine mem_iUnion.2 ⟨g, e, ?_, rfl⟩
  change p e = (Lv.ρs g).symm z
  rw [← he, Homeomorph.symm_apply_apply]

end Space


section Lift

variable (Lv : Level O R A) {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  (hp : IsUniversalCovering.{u, u, u, u} p)

include hp in
variable {Lv} in
/-- Two lifts of the same map `Z̃ → Z` through `p` that agree at one point are equal. -/
lemma lift_ext {Y W : Type*} [TopologicalSpace Y] [TopologicalSpace W] {f₁ f₂ : E → Y} {q : Y → W}
    (hq : IsCoveringMap q) (h₁ : Continuous f₁) (h₂ : Continuous f₂) (h : q ∘ f₁ = q ∘ f₂) (e : E)
    (he : f₁ e = f₂ e) : f₁ = f₂ :=
  have := hp.connectedSpace
  hq.eq_of_comp_eq h₁ h₂ h e he

include hp in
/-- **Lifting automorphisms of `Z` to `Z̃`**: `g • p` lifts through `p` to a homeomorphism of
`Z̃` mapping `e₁` to any `e₂` over `g • p e₁`. -/
lemma exists_lift (g : Lv.L.H) {e₁ e₂ : E} (h : p e₂ = Lv.ρs g (p e₁)) :
    ∃ τ : E ≃ₜ E, (∀ e, p (τ e) = Lv.ρs g (p e)) ∧ τ e₁ = e₂ := by
  have hpc := hp.isCoveringMap.continuous
  obtain ⟨f, hf, hpf, hfe⟩ := hp.exists_lift Lv.Z E p hp.isCoveringMap (Lv.ρs g ∘ p)
    ((Lv.ρs g).continuous.comp hpc) e₁ e₂ h
  obtain ⟨f', hf', hpf', hfe'⟩ := hp.exists_lift Lv.Z E p hp.isCoveringMap
    ((Lv.ρs g).symm ∘ p) ((Lv.ρs g).symm.continuous.comp hpc) e₂ e₁
    (by rw [Function.comp_apply, h, Homeomorph.symm_apply_apply])
  have h₁ : f' ∘ f = id := lift_ext hp hp.isCoveringMap (hf'.comp hf) continuous_id
    (by
      funext e
      have h₁ := congrFun hpf' (f e)
      have h₂ := congrFun hpf e
      simp only [Function.comp_apply] at h₁ h₂ ⊢
      rw [h₁, h₂, Homeomorph.symm_apply_apply]
      rfl) e₁ (by simp [hfe, hfe'])
  have h₂ : f ∘ f' = id := lift_ext hp hp.isCoveringMap (hf.comp hf') continuous_id
    (by
      funext e
      have h₁ := congrFun hpf (f' e)
      have h₂ := congrFun hpf' e
      simp only [Function.comp_apply] at h₁ h₂ ⊢
      rw [h₁, h₂, Homeomorph.apply_symm_apply]
      rfl) e₂ (by simp [hfe, hfe'])
  exact ⟨{ toFun := f, invFun := f', left_inv := congrFun h₁, right_inv := congrFun h₂
           continuous_toFun := hf, continuous_invFun := hf' }, fun e => congrFun hpf e, hfe⟩

variable (p) in
/-- **The group `Π` of lifts of `H` to `Z̃`**: pairs `(g, g̃)` with `p ∘ g̃ = g • p`. This is the
orbifold fundamental group of `[Z/H]` (Blueprint §10.3.1, B3). -/
def Pi : Subgroup (Lv.L.H × (E ≃ₜ E)) where
  carrier := {x | ∀ e, p (x.2 e) = Lv.ρs x.1 (p e)}
  mul_mem' {x y} hx hy e := by
    change p (x.2 (y.2 e)) = Lv.ρs (x.1 * y.1) (p e)
    rw [hx, hy, map_mul, Homeomorph.mul_apply]
  one_mem' e := by simp
  inv_mem' {x} hx e := by
    change p (x.2.symm e) = Lv.ρs x.1⁻¹ (p e)
    rw [map_inv, Homeomorph.inv_apply]
    apply (Lv.ρs x.1).injective
    rw [← hx, Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply]

variable {Lv hp}

lemma Pi.spec (π : Pi Lv p) (e : E) : p (π.1.2 e) = Lv.ρs π.1.1 (p e) := π.2 e

include hp in
variable (hp) in
/-- Elements of `Π` are determined by their image in `H` and the image of one point. -/
lemma Pi.ext_of_apply {π π' : Pi Lv p} (h₁ : π.1.1 = π'.1.1) (e : E) (h₂ : π.1.2 e = π'.1.2 e) :
    π = π' := by
  refine Subtype.ext (Prod.ext h₁ (Homeomorph.ext (congrFun ?_)))
  refine lift_ext hp hp.isCoveringMap π.1.2.continuous π'.1.2.continuous ?_ e h₂
  funext e'
  simp only [Function.comp_apply, Pi.spec, h₁]

variable (Lv hp)

variable (p) in
/-- The projection `Π → H`. -/
def toH : Pi Lv p →* Lv.L.H := (MonoidHom.fst _ _).comp (Pi Lv p).subtype

include hp in
/-- `Π → H` is surjective: every element of `H` lifts to `Z̃` (Z connected). -/
theorem toH_surjective [ConnectedSpace Lv.Z] : Function.Surjective (toH Lv p) := by
  intro g
  have := hp.connectedSpace
  obtain ⟨e₁⟩ := (inferInstance : Nonempty E)
  obtain ⟨e₂, he₂⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.ρs g (p e₁))
  obtain ⟨τ, hτ, -⟩ := exists_lift Lv hp g he₂
  exact ⟨⟨(g, τ), hτ⟩, rfl⟩

variable (p) in
/-- The deck group of the universal covering `p`. -/
def deckGroup : Subgroup (E ≃ₜ E) where
  carrier := {τ | ∀ e, p (τ e) = p e}
  mul_mem' {τ τ'} h h' e := by
    change p (τ (τ' e)) = p e
    rw [h, h']
  one_mem' _ := rfl
  inv_mem' {τ} h e := by
    change p (τ.symm e) = p e
    conv_rhs => rw [← τ.apply_symm_apply e]
    rw [h]

lemma mem_ker_toH {π : Pi Lv p} : π ∈ (toH Lv p).ker ↔ π.1.1 = 1 := Iff.rfl

/-- **The kernel of `Π → H` is the deck group** of `p` (= `π₁(Z)`). -/
def kerEquiv : (toH Lv p).ker ≃* deckGroup Lv p where
  toFun π := ⟨π.1.1.2, fun e => by
    rw [Pi.spec π.1 e, (mem_ker_toH Lv).1 π.2, map_one, Homeomorph.one_apply]⟩
  invFun τ := ⟨⟨(1, τ.1), fun e => by rw [map_one, Homeomorph.one_apply]; exact τ.2 e⟩, rfl⟩
  left_inv π := Subtype.ext (Subtype.ext (Prod.ext ((mem_ker_toH Lv).1 π.2).symm rfl))
  right_inv _ := rfl
  map_mul' _ _ := rfl

end Lift

section Object

variable (Lv : Level O R A) [Finite Lv.L.H] {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  (hp : IsUniversalCovering.{u, u, u, u} p) (hc : ∀ z, (p ⁻¹' {z}).Countable)

/-- The covering code of the Galois object: `Ind_1^H Z̃ → Z`, coded inside `Z × ℕ`. -/
def code : CoveringCode Lv.ρs :=
  CoveringCode.ofCovering (countable_indProj_fibre p hc) (isCoveringMap_indProj p hp.isCoveringMap)
    (indAct Lv E) (indProj_act p)

/-- **The Galois object** `U_Lv` of a level with a model whose special fibre has the universal
covering `p : Z̃ → Z`: the level with the `H`-equivariant covering `Ind_1^H Z̃ ≅ (Z̃ × Π)/π₁`. -/
def obj : TempObj O R A := ⟨Lv, code Lv hp hc⟩

/-- The homeomorphism of `Ind_1^H Z̃` with the coded covering space of `U_Lv`. -/
def Θ : IndSpace Lv E ≃ₜ (code Lv hp hc).carrier := CoveringCode.ofCoveringHomeomorph _ _ _ _

variable {Lv hp hc}

@[simp] lemma Θ_fst (x : IndSpace Lv E) : (Θ Lv hp hc x).1.1 = indProj p x := rfl

lemma act_Θ (g : Lv.L.H) (x : IndSpace Lv E) :
    (code Lv hp hc).act g (Θ Lv hp hc x) = Θ Lv hp hc (indAct Lv E g x) :=
  CoveringCode.ofCovering_act _ _ _ _ g x


/-- The right action of `Π` on `Ind_1^H Z̃`: `(g, e) ↦ (g π₁⁻¹, π₂ e)`. -/
def deckInd (π : Pi Lv p) : IndSpace Lv E ≃ₜ IndSpace Lv E where
  toFun x := ⟨x.1 * π.1.1⁻¹, π.1.2 x.2⟩
  invFun x := ⟨x.1 * π.1.1, π.1.2.symm x.2⟩
  left_inv x := Sigma.ext (by simp) (heq_of_eq (by simp))
  right_inv x := Sigma.ext (by simp) (heq_of_eq (by simp))
  continuous_toFun := continuous_sigma fun i =>
    (continuous_sigmaMk (σ := fun _ : Lv.L.H => E) (i := i * π.1.1⁻¹)).comp π.1.2.continuous
  continuous_invFun := continuous_sigma fun i =>
    (continuous_sigmaMk (σ := fun _ : Lv.L.H => E) (i := i * π.1.1)).comp π.1.2.symm.continuous

omit [Finite Lv.L.H] in
@[simp] lemma deckInd_apply (π : Pi Lv p) (x : IndSpace Lv E) :
    deckInd π x = ⟨x.1 * π.1.1⁻¹, π.1.2 x.2⟩ := rfl

omit [Finite Lv.L.H] in
lemma indProj_deckInd (π : Pi Lv p) (x : IndSpace Lv E) :
    indProj p (deckInd π x) = indProj p x := by
  simp only [indProj, deckInd_apply, Pi.spec, map_mul, map_inv, Homeomorph.mul_apply,
    Homeomorph.inv_apply, Homeomorph.symm_apply_apply]

omit [Finite Lv.L.H] in
lemma deckInd_indAct (π : Pi Lv p) (g : Lv.L.H) (x : IndSpace Lv E) :
    deckInd π (indAct Lv E g x) = indAct Lv E g (deckInd π x) :=
  Sigma.ext (mul_assoc _ _ _) HEq.rfl

omit [Finite Lv.L.H] in
lemma deckInd_mul (π π' : Pi Lv p) (x : IndSpace Lv E) :
    deckInd (π * π') x = deckInd π (deckInd π' x) :=
  Sigma.ext (by simp [mul_assoc]) HEq.rfl

omit [Finite Lv.L.H] in
lemma deckInd_one (x : IndSpace Lv E) : deckInd (1 : Pi Lv p) x = x :=
  Sigma.ext (by simp) HEq.rfl

variable (hp hc) in
/-- **The deck transformation** of `U_Lv` given by `π ∈ Π`: the identity on the level and the
model, and the right action of `π` on `Ind_1^H Z̃ ≅ (Z̃ × Π)/π₁`. -/
def deckHom (π : Pi Lv p) : obj Lv hp hc ⟶ obj Lv hp hc where
  φ := 𝟙 _
  ψ := 𝟙 _
  ψ_toSpec := Category.id_comp _
  j_ψ := (𝟙 (obj Lv hp hc) : TempObj.Hom _ _).j_ψ
  h x := Θ Lv hp hc (deckInd π ((Θ Lv hp hc).symm x))
  continuous_h := (Θ Lv hp hc).continuous.comp ((deckInd π).continuous.comp
    (Θ Lv hp hc).symm.continuous)
  fst_h x := by
    refine congrArg Subtype.val (?_ : (Θ Lv hp hc (deckInd π ((Θ Lv hp hc).symm x))).1.1 = x.1.1)
    conv_rhs => rw [← (Θ Lv hp hc).apply_symm_apply x]
    rw [Θ_fst, Θ_fst, indProj_deckInd]
  h_act g x := by
    obtain ⟨y, rfl⟩ := (Θ Lv hp hc).surjective x
    change Θ Lv hp hc (deckInd π ((Θ Lv hp hc).symm ((code Lv hp hc).act g (Θ Lv hp hc y)))) =
      (code Lv hp hc).act g (Θ Lv hp hc (deckInd π ((Θ Lv hp hc).symm (Θ Lv hp hc y))))
    rw [act_Θ, act_Θ, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply, deckInd_indAct]

lemma deckHom_h_Θ (π : Pi Lv p) (x : IndSpace Lv E) :
    (deckHom hp hc π).h (Θ Lv hp hc x) = Θ Lv hp hc (deckInd π x) := by
  simp [deckHom]

lemma deckHom_comp (π π' : Pi Lv p) :
    deckHom hp hc π ≫ deckHom hp hc π' = deckHom hp hc (π' * π) := by
  refine TempObj.Hom.ext (Category.id_comp _) (Category.id_comp _) (funext fun x => ?_)
  obtain ⟨y, rfl⟩ := (Θ Lv hp hc).surjective x
  rw [TempObj.comp_h, Function.comp_apply, deckHom_h_Θ, deckHom_h_Θ, deckHom_h_Θ, deckInd_mul]

lemma deckHom_one : deckHom hp hc (1 : Pi Lv p) = 𝟙 _ := by
  refine TempObj.Hom.ext rfl rfl (funext fun x => ?_)
  obtain ⟨y, rfl⟩ := (Θ Lv hp hc).surjective x
  rw [deckHom_h_Θ, deckInd_one, TempObj.id_h, id]

variable (hp hc) in
/-- **The deck action** `Π →* Aut U_Lv`. -/
def deck : Pi Lv p →* Aut (obj Lv hp hc) where
  toFun π :=
    { hom := deckHom hp hc π
      inv := deckHom hp hc π⁻¹
      hom_inv_id := by rw [deckHom_comp, inv_mul_cancel, deckHom_one]
      inv_hom_id := by rw [deckHom_comp, mul_inv_cancel, deckHom_one] }
  map_one' := Iso.ext deckHom_one
  map_mul' π π' := Iso.ext (deckHom_comp π' π).symm

@[simp] lemma deck_hom (π : Pi Lv p) : (deck hp hc π).hom = deckHom hp hc π := rfl

end Object


section Fibre

open TempObj

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

variable {Lv : Level O R A} [Finite Lv.L.H] {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}

/-- The point `(t, (1, e))` of the fibre of `U_Lv`, for `e ∈ Z̃` over the specialization of `t`. -/
def prePt (t : Lv.L.B →ₐ[R] Ω) (e : E) (he : p e = Lv.sp V hV t) :
    PreFibre Ω V hV (obj Lv hp hc) :=
  ⟨(t, Θ Lv hp hc ⟨1, e⟩), congrArg Subtype.val ((Θ_fst _).trans ((indProj_one p e).trans he))⟩

lemma proj_eq_sp (q : PreFibre Ω V hV (obj Lv hp hc)) {e : E} (h : q.1.2 = Θ Lv hp hc ⟨1, e⟩) :
    p e = Lv.sp V hV q.1.1 := by
  apply Subtype.ext
  have h₂ := q.2
  rw [h] at h₂
  exact (congrArg Subtype.val ((indProj_one p e).symm.trans (Θ_fst _).symm)).trans h₂

/-- In the scheme case (`A` trivial, so `H⁰ = H`), every point of the fibre of `U_Lv` is
represented by a pair `(t, (1, e))`. -/
lemma exists_rep [Subsingleton A] (u : Fibre Ω V hV (obj Lv hp hc)) :
    ∃ (q : PreFibre Ω V hV (obj Lv hp hc)) (e : E), q.1.2 = Θ Lv hp hc ⟨1, e⟩ ∧
      u = Quotient.mk _ q := by
  obtain ⟨q, rfl⟩ := Quotient.mk_surjective u
  obtain ⟨⟨g, e⟩, hge⟩ := (Θ Lv hp hc).surjective q.1.2
  let k : (obj Lv hp hc).Lv.L.H0 := ⟨g⁻¹, FiniteLevel.mem_H0.2 (Subsingleton.elim _ _)⟩
  refine ⟨k • q, e, ?_, Quotient.sound ⟨k⁻¹, inv_smul_smul k q⟩⟩
  change (code Lv hp hc).act g⁻¹ q.1.2 = _
  rw [← hge, act_Θ]
  exact congrArg (Θ Lv hp hc) (Sigma.ext (inv_mul_cancel g) HEq.rfl)

/-- **`U_Lv` is Galois** (scheme case): if `H⁰ = H` acts simply transitively on the geometric
fibre `F_L` (a Galois level), then `Π` acts simply transitively on the fibre `Φ(U_Lv)` through
the deck transformations. -/
theorem existsUnique_deck [Subsingleton A]
    (hgal : ∀ t t' : Lv.L.B →ₐ[R] Ω, ∃! k : Lv.L.H0, FiniteLevel.fibreAct Ω Lv.L k t = t')
    (u v : Fibre Ω V hV (obj Lv hp hc)) :
    ∃! π : Pi Lv p, fibreMap V hV (deckHom hp hc π) u = v := by
  obtain ⟨q₁, e₁, hq₁, rfl⟩ := exists_rep V hV u
  obtain ⟨q₂, e₂, hq₂, rfl⟩ := exists_rep V hV v
  obtain ⟨k, hk, -⟩ := hgal q₁.1.1 q₂.1.1
  have hp₂ : p e₂ = Lv.ρs k (p e₁) := by
    rw [proj_eq_sp V hV q₂ hq₂, proj_eq_sp V hV q₁ hq₁, ← hk]
    apply Subtype.ext
    rw [Level.sp_fibreAct, Level.ρs_apply]
  obtain ⟨τ, hτ, hτe⟩ := exists_lift Lv hp k hp₂
  let π : Pi Lv p := ⟨((k : Lv.L.H), τ), hτ⟩
  have hπ : fibreMap V hV (deckHom hp hc π) (Quotient.mk _ q₁) = Quotient.mk _ q₂ := by
    change Quotient.mk _ (preMap V hV _ q₁) = Quotient.mk _ q₂
    refine Eq.symm (Quotient.sound ?_)
    refine ⟨k, Subtype.ext (Prod.ext hk ?_)⟩
    change (code Lv hp hc).act k ((deckHom hp hc _).h q₁.1.2) = q₂.1.2
    rw [hq₁, deckHom_h_Θ, act_Θ, hq₂]
    refine congrArg (Θ Lv hp hc) (Sigma.ext ?_ (heq_of_eq hτe))
    change (k : Lv.L.H) * (1 * (k : Lv.L.H)⁻¹) = 1
    group
  refine ⟨π, hπ, fun π' hπ' => ?_⟩
  obtain ⟨m, hm⟩ := Quotient.exact (hπ'.trans hπ.symm : Quotient.mk _ (preMap V hV _ q₁) =
    Quotient.mk _ (preMap V hV _ q₁))
  have hm₁ : m = 1 := (hgal q₁.1.1 q₁.1.1).unique (congrArg (fun q => q.1.1) hm)
    (FiniteLevel.fibreAct_one Ω Lv.L _)
  subst hm₁
  have hm₂ := congrArg (fun q => q.1.2) hm
  change (code Lv hp hc).act 1 ((deckHom hp hc π).h q₁.1.2) = (deckHom hp hc π').h q₁.1.2
    at hm₂
  rw [map_one, Homeomorph.one_apply, hq₁, deckHom_h_Θ, deckHom_h_Θ] at hm₂
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj ((Θ Lv hp hc).injective hm₂)
  exact Pi.ext_of_apply hp (by simpa using h₁.symm) e₁ (eq_of_heq h₂).symm

/-- **Rigidity relative to the level and model components**: two morphisms out of `U_Lv` with the
same level and model morphisms which agree at one point of the covering space are equal. -/
theorem hom_ext {X : TempObj O R A} {f f' : obj Lv hp hc ⟶ X} (hφ : f.φ = f'.φ) (hψ : f.ψ = f'.ψ)
    (x₀ : (code Lv hp hc).carrier) (h : f.h x₀ = f'.h x₀) : f = f' := by
  obtain ⟨⟨g₀, e₀⟩, rfl⟩ := (Θ Lv hp hc).surjective x₀
  have hc₀ : Continuous fun e : E => Θ Lv hp hc ⟨g₀, e⟩ :=
    (Θ Lv hp hc).continuous.comp (continuous_sigmaMk (σ := fun _ : Lv.L.H => E))
  have hsheet : (fun e => f.h (Θ Lv hp hc ⟨g₀, e⟩)) = fun e => f'.h (Θ Lv hp hc ⟨g₀, e⟩) := by
    refine lift_ext hp X.P.isCoveringMap (f.continuous_h.comp hc₀) (f'.continuous_h.comp hc₀)
      (funext fun e => Subtype.ext ?_) e₀ h
    change ((f.h _).1.1 : X.Lv.c.scheme) = (f'.h _).1.1
    rw [f.fst_h, f'.fst_h, hψ]
  refine TempObj.Hom.ext hφ hψ (funext fun x => ?_)
  obtain ⟨⟨g, e⟩, rfl⟩ := (Θ Lv hp hc).surjective x
  have hx : Θ Lv hp hc ⟨g, e⟩ = (code Lv hp hc).act (g * g₀⁻¹) (Θ Lv hp hc ⟨g₀, e⟩) := by
    rw [act_Θ]
    exact congrArg (Θ Lv hp hc) (Sigma.ext (inv_mul_cancel_right g g₀).symm HEq.rfl)
  rw [hx]
  change f.h ((obj Lv hp hc).P.act _ _) = f'.h ((obj Lv hp hc).P.act _ _)
  rw [f.h_act, f'.h_act, congrFun hsheet e, hφ]

/-- `σ_k⁻¹` as an `R`-algebra endomorphism of `B`, for `k ∈ H⁰`. -/
def twist {L : FiniteLevel R A} (k : L.H0) : L.B →ₐ[R] L.B :=
  { ((k : SemilinearAut R A L.B).σ.symm : L.B →+* L.B) with
    commutes' := fun r => (RingEquiv.symm_apply_eq _).2
      (SemilinearAut.σ_algebraMap_of_a_eq_one (FiniteLevel.mem_H0.1 k.2) r).symm }

omit [IsScalarTower K R Ω] in
lemma fibreAct_eq_comp_twist {L : FiniteLevel R A} (k : L.H0) (t : L.B →ₐ[R] Ω) :
    FiniteLevel.fibreAct Ω L k t = t.comp (twist k) := rfl

/-- **Rigidity on fibres**: if the map `j : Spec B → 𝒯` of `Lv` is scheme-theoretically dominant
and `Spec B` is connected in the sense that `R`-algebra maps into `B` are determined by one
geometric point (`hconn`), then two morphisms `U_Lv ⟶ X` which agree on one point of the fibre
induce the same map of fibres. -/
theorem fibreMap_eq_of_eq [Subsingleton A] [IsSchemeTheoreticallyDominant Lv.j]
    (hconn : ∀ (L' : FiniteLevel R A) (a a' : L'.B →ₐ[R] Lv.L.B) (t : Lv.L.B →ₐ[R] Ω),
      t.comp a = t.comp a' → a = a')
    {X : TempObj O R A} (f f' : obj Lv hp hc ⟶ X) (u : Fibre Ω V hV (obj Lv hp hc))
    (h : fibreMap V hV f u = fibreMap V hV f' u) : fibreMap V hV f = fibreMap V hV f' := by
  obtain ⟨q₁, e₁, hq₁, rfl⟩ := exists_rep V hV u
  obtain ⟨k, hk⟩ := Quotient.exact (h.symm : Quotient.mk _ (preMap V hV f' q₁) =
    Quotient.mk _ (preMap V hV f q₁))
  have hk₁ : FiniteLevel.fibreAct Ω X.Lv.L k (q₁.1.1.comp f.φ.f) = q₁.1.1.comp f'.φ.f :=
    congrArg (fun q => q.1.1) hk
  have hk₂ : X.P.act (k : X.Lv.L.H) (f.h q₁.1.2) = f'.h q₁.1.2 := congrArg (fun q => q.1.2) hk
  have hf : f'.φ.f = f.φ.f.comp (twist k) :=
    hconn X.Lv.L _ _ q₁.1.1
      (hk₁.symm.trans ((fibreAct_eq_comp_twist k _).trans (AlgHom.comp_assoc _ _ _)))
  have : IsSchemeTheoreticallyDominant (obj Lv hp hc).Lv.j :=
    ‹IsSchemeTheoreticallyDominant Lv.j›
  have hι : (obj Lv hp hc).Lv.j ≫ f'.ψ = (obj Lv hp hc).Lv.j ≫ f.ψ ≫ (X.Lv.ρ k).hom := by
    have hring : (f'.φ.f :
          X.Lv.L.B →+* (obj Lv hp hc).Lv.L.B) = (f.φ.f :
          X.Lv.L.B →+* (obj Lv hp hc).Lv.L.B).comp
        ((k : SemilinearAut R A X.Lv.L.B).σ.symm : X.Lv.L.B →+* X.Lv.L.B) := by
      rw [hf]
      rfl
    calc (obj Lv hp hc).Lv.j ≫ f'.ψ = Spec.map (CommRingCat.ofHom (f'.φ.f :
          X.Lv.L.B →+* (obj Lv hp hc).Lv.L.B)) ≫ X.Lv.j :=
          f'.j_ψ
      _ = Spec.map (CommRingCat.ofHom (f.φ.f :
          X.Lv.L.B →+* (obj Lv hp hc).Lv.L.B)) ≫
          Spec.map (CommRingCat.ofHom ((k : SemilinearAut R A X.Lv.L.B).σ.symm :
            X.Lv.L.B →+* X.Lv.L.B)) ≫ X.Lv.j := by
          rw [hring, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
      _ = Spec.map (CommRingCat.ofHom (f.φ.f :
          X.Lv.L.B →+* (obj Lv hp hc).Lv.L.B)) ≫ X.Lv.j ≫ (X.Lv.ρ k).hom := by
          rw [X.Lv.ρ_j]
      _ = (obj Lv hp hc).Lv.j ≫ f.ψ ≫ (X.Lv.ρ k).hom := by
          rw [← Category.assoc, ← f.j_ψ, Category.assoc]
  have hψ : f'.ψ = f.ψ ≫ (X.Lv.ρ k).hom :=
    ext_of_isSchemeTheoreticallyDominant_of_isSeparated X.Lv.c.toSpec
      (by rw [f'.ψ_toSpec, Category.assoc, X.Lv.ρ_toSpec, f.ψ_toSpec]) (obj Lv hp hc).Lv.j hι
  have hc₁ : Continuous fun e : E => Θ Lv hp hc ⟨1, e⟩ :=
    (Θ Lv hp hc).continuous.comp (continuous_sigmaMk (σ := fun _ : Lv.L.H => E))
  have hsheet : (fun e => f'.h (Θ Lv hp hc ⟨1, e⟩)) =
      fun e => X.P.act (k : X.Lv.L.H) (f.h (Θ Lv hp hc ⟨1, e⟩)) := by
    refine lift_ext hp X.P.isCoveringMap (f'.continuous_h.comp hc₁)
      ((X.P.act _).continuous.comp (f.continuous_h.comp hc₁)) (funext fun e => Subtype.ext ?_)
      e₁ (by rw [← hq₁]; exact hk₂.symm)
    change ((f'.h _).1.1 : X.Lv.c.scheme) = (X.P.act _ (f.h _)).1.1
    rw [f'.fst_h, X.P.act_fst, Level.ρs_apply, f.fst_h, hψ, Scheme.Hom.comp_apply]
  funext w
  obtain ⟨q, e, hq, rfl⟩ := exists_rep V hV w
  change Quotient.mk _ (preMap V hV f q) = Quotient.mk _ (preMap V hV f' q)
  refine Eq.symm (Quotient.sound ?_)
  refine ⟨k, Subtype.ext (Prod.ext ?_ ?_)⟩
  · change FiniteLevel.fibreAct Ω X.Lv.L k (q.1.1.comp f.φ.f) = q.1.1.comp f'.φ.f
    rw [hf, fibreAct_eq_comp_twist]
    rfl
  · change X.P.act (k : X.Lv.L.H) (f.h q.1.2) = f'.h q.1.2
    rw [hq]
    exact (congrFun hsheet e).symm


/-- The `H`-equivariant extension `(g, e) ↦ ℓ(g) • s(e)` of a lift `s : Z̃ → P_X` of
`ψ_s ∘ p`. -/
def liftInd {X : TempObj O R A} (ℓ : LevelHom O R A Lv X.Lv) (s : E → X.P.carrier)
    (x : IndSpace Lv E) : X.P.carrier :=
  X.P.act (ℓ.φ.r x.1) (s x.2)

omit [Finite Lv.L.H] in
lemma continuous_liftInd {X : TempObj O R A} (ℓ : LevelHom O R A Lv X.Lv) {s : E → X.P.carrier}
    (hs : Continuous s) : Continuous (liftInd ℓ s) :=
  continuous_sigma fun g => by exact (X.P.act (ℓ.φ.r g)).continuous.comp hs

omit [Finite Lv.L.H] [TopologicalSpace E] in
lemma liftInd_fst {X : TempObj O R A} (ℓ : LevelHom O R A Lv X.Lv) (hℓ : ℓ.IsEquivariant)
    {s : E → X.P.carrier} (hps : ∀ e, (s e).1.1 = ℓ.ψs (p e)) (x : IndSpace Lv E) :
    (liftInd ℓ s x).1.1 = ℓ.ψs (indProj p x) := by
  obtain ⟨g, e⟩ := x
  change (X.P.act (ℓ.φ.r g) (s e)).1.1 = ℓ.ψs (Lv.ρs g (p e))
  rw [X.P.act_fst, hℓ.ψs_ρs, hps]

variable (hp hc) in
/-- **The morphism `U_Lv ⟶ X` over `ℓ`** determined by a lift `s : Z̃ → P_X` of `ψ_s ∘ p`. -/
def liftHom {X : TempObj O R A} (ℓ : LevelHom O R A Lv X.Lv) (hℓ : ℓ.IsEquivariant)
    {s : E → X.P.carrier} (hs : Continuous s) (hps : ∀ e, (s e).1.1 = ℓ.ψs (p e)) :
    obj Lv hp hc ⟶ X where
  φ := ℓ.φ
  ψ := ℓ.ψ
  ψ_toSpec := ℓ.ψ_toSpec
  j_ψ := ℓ.j_ψ
  h y := liftInd ℓ s ((Θ Lv hp hc).symm y)
  continuous_h := (continuous_liftInd ℓ hs).comp (Θ Lv hp hc).symm.continuous
  fst_h y := by
    obtain ⟨x, rfl⟩ := (Θ Lv hp hc).surjective y
    change ((liftInd ℓ s ((Θ Lv hp hc).symm (Θ Lv hp hc x))).1.1 : X.Lv.c.scheme) =
      ℓ.ψ ((Θ Lv hp hc x).1.1 : Lv.c.scheme)
    rw [Homeomorph.symm_apply_apply, liftInd_fst ℓ hℓ hps, LevelHom.coe_ψs, Θ_fst]
  h_act g y := by
    obtain ⟨⟨g', e⟩, rfl⟩ := (Θ Lv hp hc).surjective y
    change liftInd ℓ s ((Θ Lv hp hc).symm ((code Lv hp hc).act g (Θ Lv hp hc ⟨g', e⟩))) =
      X.P.act (ℓ.φ.r g) (liftInd ℓ s ((Θ Lv hp hc).symm (Θ Lv hp hc ⟨g', e⟩)))
    rw [act_Θ, Homeomorph.symm_apply_apply, Homeomorph.symm_apply_apply]
    change X.P.act (ℓ.φ.r ((show Lv.L.H from g) * g')) (s e) =
      X.P.act (ℓ.φ.r g) (X.P.act (ℓ.φ.r g') (s e))
    rw [map_mul, map_mul, Homeomorph.mul_apply]

lemma ofTempHom_liftHom {X : TempObj O R A} (ℓ : LevelHom O R A Lv X.Lv) (hℓ : ℓ.IsEquivariant)
    {s : E → X.P.carrier} (hs : Continuous s) (hps : ∀ e, (s e).1.1 = ℓ.ψs (p e)) :
    LevelHom.ofTempHom (liftHom hp hc ℓ hℓ hs hps) = ℓ := rfl

lemma liftHom_h_one {X : TempObj O R A} (ℓ : LevelHom O R A Lv X.Lv) (hℓ : ℓ.IsEquivariant)
    {s : E → X.P.carrier} (hs : Continuous s) (hps : ∀ e, (s e).1.1 = ℓ.ψs (p e)) (e : E) :
    (liftHom hp hc ℓ hℓ hs hps).h (Θ Lv hp hc ⟨1, e⟩) = s e := by
  change liftInd ℓ s ((Θ Lv hp hc).symm (Θ Lv hp hc ⟨1, e⟩)) = s e
  rw [Homeomorph.symm_apply_apply]
  change X.P.act (ℓ.φ.r 1) (s e) = s e
  rw [map_one, map_one, Homeomorph.one_apply]

/-- **Pointwise domination** (relative to a fixed equivariant morphism of levels with models
`ℓ : Lv ⟶ X.Lv`): every point `(t ∘ ℓ, x)` of the fibre of `X` over the image of a geometric
point `t` of `Lv` is hit by a morphism `U_Lv ⟶ X` lying over `ℓ`. The covering part is the
lift `Z̃ → P_X` of `ψ_s ∘ p` through `x`, extended `H`-equivariantly to `Ind_1^H Z̃`. -/
theorem exists_hom_fibreMap [ConnectedSpace Lv.Z] {X : TempObj O R A}
    (ℓ : LevelHom O R A Lv X.Lv) (hℓ : ℓ.IsEquivariant) (t : Lv.L.B →ₐ[R] Ω)
    (q : PreFibre Ω V hV X) (ht : t.comp ℓ.φ.f = q.1.1) :
    ∃ (f : obj Lv hp hc ⟶ X) (u : Fibre Ω V hV (obj Lv hp hc)),
      LevelHom.ofTempHom f = ℓ ∧ fibreMap V hV f u = Quotient.mk _ q := by
  have := hp.connectedSpace
  obtain ⟨e₀, he₀⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
  have hy : q.1.2.1.1 = (ℓ.ψs ∘ p) e₀ := by
    apply Subtype.ext
    rw [q.2, Function.comp_apply, LevelHom.coe_ψs, he₀, LevelHom.ψ_sp V hV ℓ t, ht]
  obtain ⟨s, hs, hps, hse⟩ := hp.exists_lift X.Lv.Z X.P.carrier (fun x => x.1.1)
    X.P.isCoveringMap (ℓ.ψs ∘ p) (ℓ.continuous_ψs.comp hp.isCoveringMap.continuous) e₀ q.1.2 hy
  have hps' : ∀ e, (s e).1.1 = ℓ.ψs (p e) := congrFun hps
  refine ⟨liftHom hp hc ℓ hℓ hs hps', Quotient.mk _ (prePt V hV t e₀ he₀),
    ofTempHom_liftHom ℓ hℓ hs hps', congrArg (Quotient.mk _) ?_⟩
  refine Subtype.ext (Prod.ext ht ?_)
  change (liftHom hp hc ℓ hℓ hs hps').h (Θ Lv hp hc ⟨1, e₀⟩) = q.1.2
  rw [liftHom_h_one ℓ hℓ hs hps', hse]

omit [Finite Lv.L.H] in
/-- **`Aut` does not act freely on fibres**: for `k ∈ H⁰` of the level of `X`, the action of `k`
(conjugation by `k` on the level, `ρ(k)` on the model, `k` on the covering space) is an
endomorphism of `X` inducing the identity on the fibre `Φ X`. It differs from `𝟙 X` as soon as
`σ_k ≠ 1` (`conjHom_ne_id`). So "Galois" and "rigidity" in `TempObj` can only hold after applying
`Φ` (`existsUnique_deck`, `fibreMap_eq_of_eq`). -/
def conjHom (X : TempObj O R A) (k : X.Lv.L.H0) : X ⟶ X where
  φ :=
    { f := twist k
      r := (MulAut.conj (k : X.Lv.L.H)).toMonoidHom
      r_a := fun g => by
        have h₁ := FiniteLevel.mem_H0.1 k.2
        change (k : SemilinearAut R A X.Lv.L.B).a * (g : SemilinearAut R A X.Lv.L.B).a *
          (k : SemilinearAut R A X.Lv.L.B).a⁻¹ = (g : SemilinearAut R A X.Lv.L.B).a
        rw [h₁]
        simp
      f_σ := fun g y => by
        change (k : SemilinearAut R A X.Lv.L.B).σ.symm ((k : SemilinearAut R A X.Lv.L.B).σ
          ((g : SemilinearAut R A X.Lv.L.B).σ ((k : SemilinearAut R A X.Lv.L.B).σ.symm y))) = _
        rw [RingEquiv.symm_apply_apply]
        rfl }
  ψ := (X.Lv.ρ k).hom
  ψ_toSpec := X.Lv.ρ_toSpec k
  j_ψ := (X.Lv.ρ_j k).symm
  h := X.P.act k
  continuous_h := (X.P.act k).continuous
  fst_h x := by rw [X.P.act_fst, Level.ρs_apply]
  h_act g x := by
    change X.P.act k (X.P.act g x) = X.P.act ((k : X.Lv.L.H) * g * (k : X.Lv.L.H)⁻¹) (X.P.act k x)
    rw [map_mul, map_mul, map_inv, Homeomorph.mul_apply, Homeomorph.mul_apply,
      Homeomorph.inv_apply, Homeomorph.symm_apply_apply]

omit [Finite Lv.L.H] in
lemma fibreMap_conjHom (X : TempObj O R A) (k : X.Lv.L.H0) :
    fibreMap V hV (conjHom X k) = id := by
  funext w
  obtain ⟨q, rfl⟩ := Quotient.mk_surjective w
  exact Quotient.sound ⟨k, rfl⟩

omit [Finite Lv.L.H] [IsScalarTower K R Ω] in
lemma conjHom_ne_id (X : TempObj O R A) (k : X.Lv.L.H0)
    (hk : ∃ y, (k : SemilinearAut R A X.Lv.L.B).σ y ≠ y) : conjHom X k ≠ 𝟙 X := by
  intro h
  obtain ⟨y, hy⟩ := hk
  have h₂ := DFunLike.congr_fun (congrArg (fun m : X ⟶ X => m.φ.f) h)
    ((k : SemilinearAut R A X.Lv.L.B).σ y)
  change (k : SemilinearAut R A X.Lv.L.B).σ.symm ((k : SemilinearAut R A X.Lv.L.B).σ y) =
    (k : SemilinearAut R A X.Lv.L.B).σ y at h₂
  rw [RingEquiv.symm_apply_apply] at h₂
  exact hy h₂.symm

end Fibre


section N1

variable (Lv : Level O R A) [Finite Lv.L.H] [TopologicalSpace.NoetherianSpace Lv.Z] [T0Space Lv.Z]
  [QuasiSober Lv.Z]
  (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z)

/-- **The Galois object `U_Lv` built from the universal covering of N1**
(`universalCovering`, based at `z₀`) of the special fibre. -/
def universalObj : TempObj O R A :=
  obj Lv (universalCovering.isUniversalCovering.{u, u, u} hdim z₀)
    (universalCovering.isUniversalCovering.{u, u, u} hdim z₀).countable_fibre

end N1

end

end GaloisObject

end TemperedFundamentalGroups
