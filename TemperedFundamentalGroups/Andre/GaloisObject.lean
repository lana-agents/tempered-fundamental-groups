/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.Pullback
import TemperedFundamentalGroups.Topology.UniversalCovering

/-!
# Galois objects of the tempered category (K3, topological part)

Blueprint §10.3.3, K3.
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
lemma lift_ext {Y : Type u} [TopologicalSpace Y] {f₁ f₂ : E → Y} {q : Y → Lv.Z}
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

end Object

end

end GaloisObject

end TemperedFundamentalGroups
