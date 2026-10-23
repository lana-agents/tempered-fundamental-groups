/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.StageGroup
import TemperedFundamentalGroups.Andre.StageTower

/-!
# Stage group elements with prescribed level part fixing a vertex

Let `D : UData Ω X` exhibit the Galois object `X` as `U = universalObj Lv hdim z₀`.
For an automorphism `σ` of the ring `B` of the level whose model automorphism `ψσ` fixes the
canonical point of a vertex `t` of the tree (the special point under an edge vertex, the generic
point of the component under a sheet vertex):

* **`UData.exists_lev_eq`**: some automorphism `a` of `X` has level part `D.lev a = σ` (gal);
* **`UData.exists_treeAut_fix`**: some automorphism `a` of `X` with level part `σ` fixes `t`:
  the model map of any lift is `ψσ` (dominance of `j`), so it maps the canonical point of `t` into
  the fibre of `Z̃ → Z` over the same point, and a deck transformation of `Z̃` moves it back
  (the deck group acts transitively on fibres, `deckFibreEquiv`);
* **`UData.transition_stageOf_ne_one`**: if the level part of `a` does not fix the image of the
  level map `φ` of a pointed morphism `f : p ⟶ q`, then the transition of `stageOf a` along `f` is
  nontrivial (naturality of the level coordinate, `levelPt_fibreMap`);
* **`UData.exists_stage_fix_transition_ne_one`**: the combination, in the form used for König's
  lemma on the tree tower.
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

lemma fibreMap_id_apply {X : TempObj O R A} (x : Fibre Ω V hV X) :
    fibreMap V hV (𝟙 X) x = x := by
  induction x using Quotient.inductionOn
  rfl

namespace UData

variable {X : TempObj O R A} (D : UData Ω X)

/-- The deck automorphism of `universalObj` of a deck transformation of the tree covering. -/
def deckAut (τ : deckGroup D.Lv (universalCovering.proj D.hdim D.z₀)) :
    Aut (universalObj D.Lv D.hdim D.z₀) :=
  deck (universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀)
    (universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀).countable_fibre
    ((kerEquiv D.Lv).symm τ).1

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma uTreeMap_deckAut (τ : deckGroup D.Lv (universalCovering.proj D.hdim D.z₀)) :
    uTreeMap (D.deckAut τ).hom = τ.1 := by
  funext e
  unfold uTreeMap treeMap
  rw [deckAut, deck_hom, deckHom_h_Θ, Homeomorph.symm_apply_apply]
  rfl

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma lev_deckAut (τ : deckGroup D.Lv (universalCovering.proj D.hdim D.z₀)) :
    D.lev (D.e.conjAut.symm (D.deckAut τ)) = AlgHom.id R _ := by
  unfold lev
  rw [MulEquiv.apply_symm_apply]
  rfl

/-- **Every automorphism of the level ring is the level part of an automorphism of `X`** (gal). -/
theorem exists_lev_eq {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hX : 𝒢 X)
    (σ : D.Lv.L.B ≃ₐ[R] D.Lv.L.B) : ∃ a : Aut X, D.lev a = σ := by
  haveI : Algebra.Etale R D.Lv.L.B := D.Lv.L.etale
  haveI : Module.Finite R D.Lv.L.B := D.Lv.L.finite
  obtain ⟨t₀⟩ := D.ne
  have hsurj := levelPt_surjective V hV
    (hp := universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀)
    (hc := (universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀).countable_fibre)
  obtain ⟨x₀, hx₀⟩ := hsurj t₀
  obtain ⟨x₁, hx₁⟩ := hsurj (t₀.comp (σ : D.Lv.L.B →ₐ[R] D.Lv.L.B))
  obtain ⟨a, ha⟩ := hgal X hX (fibreMap V hV D.e.inv x₀) (fibreMap V hV D.e.inv x₁)
  refine ⟨a, ?_⟩
  have hb : fibreMap V hV (D.e.conjAut a).hom x₀ = x₁ := by
    rw [Iso.conjAut_hom, Iso.conj_apply, fibreMap_comp_apply, fibreMap_comp_apply]
    change fibreMap V hV D.e.hom ((tempFibre O R A V hV).map a.hom _) = _
    rw [ha, ← fibreMap_comp_apply, Iso.inv_hom_id, fibreMap_id_apply]
  haveI : Subsingleton (universalObj D.Lv D.hdim D.z₀).Lv.L.H := D.sub
  have h := levelPt_fibreMap V hV (D.e.conjAut a).hom x₀
  have h' : t₀.comp (σ : D.Lv.L.B →ₐ[R] D.Lv.L.B) = t₀.comp (D.e.conjAut a).hom.φ.f :=
    hx₁.symm.trans ((congrArg (levelPt V hV _) hb.symm).trans
      (h.trans (congrArg (fun s : D.Lv.L.B →ₐ[R] Ω ↦ s.comp (D.e.conjAut a).hom.φ.f) hx₀)))
  exact (algHom_eq_of_comp_eq D.hidem _ _ t₀ h').symm

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **The model map of an automorphism with level part `σ` is the model automorphism of `σ`**
(dominance of `j`). -/
lemma conjAut_ψ_eq (a : Aut X) (σ : D.Lv.L.B ≃ₐ[R] D.Lv.L.B) (ha : D.lev a = σ)
    (ψσ : D.Lv.c.scheme ⟶ D.Lv.c.scheme) (hψσ : ψσ ≫ D.Lv.c.toSpec = D.Lv.c.toSpec)
    (hjσ : D.Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : D.Lv.L.B →+* D.Lv.L.B)) ≫ D.Lv.j) :
    (D.e.conjAut a).hom.ψ = ψσ := by
  have : IsSchemeTheoreticallyDominant (universalObj D.Lv D.hdim D.z₀).Lv.j := D.dom
  refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated
    (universalObj D.Lv D.hdim D.z₀).Lv.c.toSpec
    (by rw [(D.e.conjAut a).hom.ψ_toSpec]; exact hψσ.symm) (universalObj D.Lv D.hdim D.z₀).Lv.j ?_
  rw [(D.e.conjAut a).hom.j_ψ]
  change Spec.map (CommRingCat.ofHom
    ((D.lev a : D.Lv.L.B →ₐ[R] D.Lv.L.B) : D.Lv.L.B →+* D.Lv.L.B)) ≫ D.Lv.j = D.Lv.j ≫ ψσ
  rw [ha, hjσ]
  rfl

/-- **P7: an automorphism with prescribed level part fixing a vertex.** If the model
automorphism `ψσ` of `σ ∈ Aut_R(B)` fixes the canonical point of the vertex `t` (for an edge
vertex: the special point under it), some automorphism of `X` with level part `σ` fixes `t`. -/
theorem exists_treeAut_fix {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hX : 𝒢 X)
    (σ : D.Lv.L.B ≃ₐ[R] D.Lv.L.B) (ψσ : D.Lv.c.scheme ⟶ D.Lv.c.scheme)
    (hψσ : ψσ ≫ D.Lv.c.toSpec = D.Lv.c.toSpec)
    (hjσ : D.Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : D.Lv.L.B →+* D.Lv.L.B)) ≫ D.Lv.j)
    (t : D.Tr) (ht : ψσ ((canonPt t : D.Lv.Z) : D.Lv.c.scheme) = (canonPt t : D.Lv.Z)) :
    ∃ a : Aut X, D.treeAut a t = t ∧ D.lev a = σ := by
  obtain ⟨a, ha⟩ := D.exists_lev_eq V hV hgal hX σ
  set b := D.e.conjAut a
  have hψ : b.hom.ψ = ψσ := D.conjAut_ψ_eq a σ ha ψσ hψσ hjσ
  set x' := uTreeMap b.hom (canon (hηU D.hdim) t)
  have hx' : universalCovering.proj D.hdim D.z₀ x' =
      universalCovering.proj D.hdim D.z₀ (canon (hηU D.hdim) t) := by
    change x'.1.1 = canonPt t
    rw [uTreeMap_fst]
    apply Subtype.ext
    change b.hom.ψ ((canonPt t : D.Lv.Z) : D.Lv.c.scheme) = _
    rw [hψ]
    exact ht
  obtain ⟨τ, hτ⟩ := (deckFibreEquiv
    (universalCovering.isUniversalCovering.{u, u, u} D.hdim D.z₀) x').surjective
    ⟨canon (hηU D.hdim) t, hx'.symm⟩
  have hτ' : τ.1 x' = canon (hηU D.hdim) t := congrArg Subtype.val hτ
  refine ⟨D.e.conjAut.symm (D.deckAut τ) * a, ?_, ?_⟩
  · rw [map_mul, Equiv.Perm.mul_apply]
    change autVmap (D.e.conjAut (D.e.conjAut.symm (D.deckAut τ))) (autVmap b t) = t
    rw [MulEquiv.apply_symm_apply]
    have hc : canon (hηU D.hdim) (autVmap b t) = x' := (preservesCanon_aut b t).symm
    change (uTreeMap (D.deckAut τ).hom (canon (hηU D.hdim) (autVmap b t))).1.2 = t
    rw [hc, uTreeMap_deckAut, hτ']
    rfl
  · rw [lev_mul, ha, lev_deckAut]
    rfl

/-- **P7, stage form**: a stage group element with level part `σ` fixing the vertex `t`. -/
theorem exists_stage_fix {𝒢 : ObjectProperty (TempObj O R A)}
    (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hX : 𝒢 X)
    (σ : D.Lv.L.B ≃ₐ[R] D.Lv.L.B) (ψσ : D.Lv.c.scheme ⟶ D.Lv.c.scheme)
    (hψσ : ψσ ≫ D.Lv.c.toSpec = D.Lv.c.toSpec)
    (hjσ : D.Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : D.Lv.L.B →+* D.Lv.L.B)) ≫ D.Lv.j)
    (t : D.Tr) (ht : ψσ ((canonPt t : D.Lv.Z) : D.Lv.c.scheme) = (canonPt t : D.Lv.Z)) :
    ∃ a : Aut X, D.stageTree V hV (stageOf a) t = t ∧ D.lev a = σ := by
  obtain ⟨a, h₁, h₂⟩ := D.exists_treeAut_fix V hV hgal hX σ ψσ hψσ hjσ t ht
  exact ⟨a, by rw [stageTree_stageOf]; exact h₁, h₂⟩

end UData

namespace UData

variable {𝒢 : ObjectProperty (TempObj O R A)}
  (hgal : IsGaloisClass (tempFibre O R A V hV) 𝒢) (hrig : IsRigid (tempFibre O R A V hV) 𝒢)

/-- The level map `B_q → B_p` of a pointed morphism `f : p ⟶ q`, through `Dp`, `Dq`. -/
def levMap {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q) (Dp : UData Ω p.G)
    (Dq : UData Ω q.G) : Dq.Lv.L.B →ₐ[R] Dp.Lv.L.B :=
  (Dp.e.inv ≫ ptHomMor V hV f ≫ Dq.e.hom).φ.f

/-- **Nontriviality of transitions**: if the level part of `a` does not fix the image of the level
map of `f : p ⟶ q`, the transition of `stageOf a` along `f` is nontrivial. -/
theorem transition_stageOf_ne_one {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q)
    (Dp : UData Ω p.G) (Dq : UData Ω q.G) (a : Aut p.G)
    (h : (Dp.lev a).comp (levMap V hV f Dp Dq) ≠ levMap V hV f Dp Dq) :
    transition hgal hrig f (stageOf a) ≠ 1 := by
  intro h1
  haveI : Algebra.Etale R Dq.Lv.L.B := Dq.Lv.L.etale
  haveI : Module.Finite R Dq.Lv.L.B := Dq.Lv.L.finite
  have hfib := fibreMap_transition V hV hgal hrig f a 1
    (h1.trans (stageOfHom (tempFibre O R A V hV) q.G).map_one.symm)
  set F := ptHomMor V hV f
  set F' := Dp.e.inv ≫ F ≫ Dq.e.hom
  set b := Dp.e.conjAut a
  have hbF : ∀ x, fibreMap V hV F' (fibreMap V hV b.hom x) = fibreMap V hV F' x := by
    intro x
    have e₁ : b.hom ≫ F' = Dp.e.inv ≫ (a.hom ≫ F) ≫ Dq.e.hom := by
      simp [b, F', Iso.conjAut_hom, Iso.conj_apply]
    rw [← fibreMap_comp_apply, e₁, fibreMap_comp_apply, fibreMap_comp_apply, hfib,
      fibreMap_comp_apply V hV F]
    change fibreMap V hV Dq.e.hom (fibreMap V hV (𝟙 _) _) = _
    rw [fibreMap_id_apply]
    simp only [F', fibreMap_comp_apply]
  obtain ⟨t₀⟩ := Dp.ne
  obtain ⟨x₀, hx₀⟩ := levelPt_surjective V hV
    (hp := universalCovering.isUniversalCovering.{u, u, u} Dp.hdim Dp.z₀)
    (hc := (universalCovering.isUniversalCovering.{u, u, u} Dp.hdim Dp.z₀).countable_fibre) t₀
  haveI : Subsingleton (universalObj Dp.Lv Dp.hdim Dp.z₀).Lv.L.H := Dp.sub
  haveI : Subsingleton (universalObj Dq.Lv Dq.hdim Dq.z₀).Lv.L.H := Dq.sub
  have e := congrArg (levelPt V hV _) (hbF x₀)
  have hx₀' : levelPt V hV (universalObj Dp.Lv Dp.hdim Dp.z₀) x₀ = t₀ := hx₀
  rw [levelPt_fibreMap, levelPt_fibreMap, levelPt_fibreMap, hx₀', AlgHom.comp_assoc] at e
  exact h (algHom_eq_of_comp_eq Dp.hidem _ _ t₀ e)

/-- **P7 with nontrivial transition**: if `ψσ` fixes the canonical point of `t` and `σ` does not
fix the image of the level map of `f : p ⟶ q`, some stage group element of `p` fixes `t` and has
nontrivial transition along `f`. -/
theorem exists_stage_fix_transition_ne_one {p q : PtGal (tempFibre O R A V hV) 𝒢} (f : p ⟶ q)
    (Dp : UData Ω p.G) (Dq : UData Ω q.G)
    (σ : Dp.Lv.L.B ≃ₐ[R] Dp.Lv.L.B) (ψσ : Dp.Lv.c.scheme ⟶ Dp.Lv.c.scheme)
    (hψσ : ψσ ≫ Dp.Lv.c.toSpec = Dp.Lv.c.toSpec)
    (hjσ : Dp.Lv.j ≫ ψσ = Spec.map (CommRingCat.ofHom (σ : Dp.Lv.L.B →+* Dp.Lv.L.B)) ≫ Dp.Lv.j)
    (t : Dp.Tr) (ht : ψσ ((canonPt t : Dp.Lv.Z) : Dp.Lv.c.scheme) = (canonPt t : Dp.Lv.Z))
    (hσ : (σ : Dp.Lv.L.B →ₐ[R] Dp.Lv.L.B).comp (levMap V hV f Dp Dq) ≠ levMap V hV f Dp Dq) :
    ∃ γ : stageGroup (tempFibre O R A V hV) p.G,
      Dp.stageTree V hV γ t = t ∧ transition hgal hrig f γ ≠ 1 := by
  obtain ⟨a, h₁, h₂⟩ := Dp.exists_stage_fix V hV hgal p.mem σ ψσ hψσ hjσ t ht
  exact ⟨stageOf a, h₁, transition_stageOf_ne_one V hV hgal hrig f Dp Dq a (by rwa [h₂])⟩

end UData

end

end TemperedFundamentalGroups
