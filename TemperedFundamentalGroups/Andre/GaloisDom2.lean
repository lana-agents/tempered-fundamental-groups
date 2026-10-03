/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.GaloisClass2
import TemperedFundamentalGroups.Andre.Components
import TemperedFundamentalGroups.Andre.Refinement

/-!
# Domination by Galois objects over levels with trivial `H` (Blueprint §10.3.5)

Scheme case. From the strong form of W10 with connected components
(`SemistableReduction.Statement.StrongComponent`, an explicit hypothesis `hW`):

* `ModelCode.noetherianSpace_specialFibre` etc.: the special fibre of a model over a DVR
  satisfies the hypotheses of N1;
* `exists_galois_component`: a connected component `(B ⊗_K K') ⧸ (1 - ε)` of a Galois connected
  `B` (`K'/K` Galois) is again Galois: its points are moved by the stabiliser of `ε` in
  `Aut_R(B) × Gal(K'/K)`;
* `isDominating_galClass₂` (**dom**): finitely many pointed objects `(X_k, x_k)` are dominated by
  a member of `galClass₂`: take the Galois closure `B*` of `∏ B_k`, apply W10 to `B*` with
  `G = Aut_R(B*)` and the models of the `X_k`, pass to the component of `K' ⊗_K B*` through a
  point over the base point of `B*` with its sub-model `c₁`, and lift `Z̃` to the coverings
  `P_k`;
* `galoisLimitData₂`: (gal), (dom), (rig) for `galClass₂`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

section N1

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

instance ModelCode.isLocallyNoetherian (c : ModelCode O) : IsLocallyNoetherian c.scheme :=
  LocallyOfFiniteType.isLocallyNoetherian c.toSpec

instance ModelCode.compactSpace (c : ModelCode O) : CompactSpace c.scheme :=
  QuasiCompact.compactSpace_of_compactSpace c.toSpec

instance ModelCode.isNoetherian (c : ModelCode O) : IsNoetherian c.scheme where

instance ModelCode.noetherianSpace_specialFibre (c : ModelCode O) :
    TopologicalSpace.NoetherianSpace (specialFibre c.toSpec) :=
  TopologicalSpace.NoetherianSpace.set _

lemma ModelCode.isClosed_specialFibre (c : ModelCode O) : IsClosed (specialFibre c.toSpec) := by
  refine IsClosed.preimage c.toSpec.continuous ?_
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
    (IsLocalRing.maximalIdeal.isMaximal O)

instance ModelCode.quasiSober_specialFibre (c : ModelCode O) :
    QuasiSober (specialFibre c.toSpec) :=
  (c.isClosed_specialFibre.isClosedEmbedding_subtypeVal).quasiSober

end N1

section Component

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R] [IsDomain R]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
  {K' : Type u} [Field K'] [Algebra K K'] [IsGalois K K']

open Components

/-- **Components of a base change of a Galois algebra are Galois**: two geometric points of
`B ⊗_K K'` through a primitive idempotent `ε` differ by an element `δ ⊗ γ` of
`Aut_R(B) × Gal(K'/K)` fixing `ε`. -/
theorem exists_galois_component
    (hgal : ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t')
    {ε : TensorProduct K B K'} (hε : IsPrimitive ε) (w₁ w₂ : TensorProduct K B K' →ₐ[R] Ω)
    (h₁ : w₁ ε = 1) (h₂ : w₂ ε = 1) :
    ∃ (δ : B ≃ₐ[R] B) (γ : K' ≃ₐ[K] K'), Algebra.TensorProduct.congr δ γ ε = ε ∧
      w₁.comp (Algebra.TensorProduct.congr δ γ :
        TensorProduct K B K' →ₐ[R] TensorProduct K B K') = w₂ := by
  obtain ⟨δ, hδ⟩ := hgal (w₁.comp Algebra.TensorProduct.includeLeft)
    (w₂.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨γ, hγ⟩ := exists_algEquiv_comp_eq ((w₁.restrictScalars K).comp
    Algebra.TensorProduct.includeRight) ((w₂.restrictScalars K).comp
    Algebra.TensorProduct.includeRight)
  have hw : w₁.comp (Algebra.TensorProduct.congr δ γ :
      TensorProduct K B K' →ₐ[R] TensorProduct K B K') = w₂ := by
    refine Algebra.TensorProduct.ext' fun b k => ?_
    have e₁ := DFunLike.congr_fun hδ b
    have e₂ := DFunLike.congr_fun hγ k
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.coe_restrictScalars',
      AlgEquiv.coe_toAlgHom] at e₁ e₂
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, Algebra.TensorProduct.congr_apply,
      Algebra.TensorProduct.map_tmul]
    rw [← mul_one (δ b), ← one_mul (γ k), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul,
      ← mul_one b, ← one_mul k, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul (w₂)]
    simp only [mul_one, one_mul]
    rw [e₁, ← e₂]
  refine ⟨δ, γ, ?_, hw⟩
  refine (hε.map _).eq hε w₁ ?_ h₁
  change (w₁.comp (Algebra.TensorProduct.congr δ γ :
    TensorProduct K B K' →ₐ[R] TensorProduct K B K')) ε = 1
  rw [hw, h₂]

end Component

section Core

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [Subsingleton A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The level with trivial `H` on a finite étale `R`-algebra `Q` (coded). -/
def trivialLevel (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q]
    [Module.Finite R Q] : FiniteLevel R A where
  toEtaleCode := LevelData.code R Q
  H := ⊥
  surjective a := ⟨1, Subgroup.one_mem _, by rw [Subsingleton.elim a 1]; rfl⟩

lemma subsingleton_trivialLevel (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q]
    [Module.Finite R Q] : Subsingleton (trivialLevel (R := R) (A := A) Q).H :=
  ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩

/-- **The core of domination**: a connected Galois finite étale `R`-algebra `Q` with a point
`s'`, a model `c₁` (semistable, connected special fibre of dimension `≤ 1`, with a dominant
`j₁ : Spec Q ⟶ c₁` over `O` to which all `R`-automorphisms of `Q` extend), maps `f_k` from the
levels of finitely many pointed objects `(X_k, x_k)` (`s' ∘ f_k` the geometric point of `x_k`)
and compatible model maps `c₁ ⟶ c_k` give a member of `galClass₂` dominating every
`(X_k, x_k)`. -/
theorem dom_core (M : ModelCode O → Prop) {n : ℕ}
    (P : Fin n → Σ X : TempObj O R A, (tempFibre O R A V hV).obj X)
    (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q] [Module.Finite R Q]
    (hQc : ∀ e : Q, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hQg : ∀ t t' : Q →ₐ[R] Ω, ∃ σ : Q ≃ₐ[R] Q, t.comp (σ : Q →ₐ[R] Q) = t')
    (s' : Q →ₐ[R] Ω) (c₁ : ModelCode O) (hM : M c₁) (j₁ : Spec (CommRingCat.of Q) ⟶ c₁.scheme)
    (hj₁ : j₁ ≫ c₁.toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap R Q).comp ((algebraMap K R).comp O.subtype))))
    [IsSchemeTheoreticallyDominant j₁]
    (hss : ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
      (O' : ValuationSubring K') (h : O'.comap (algebraMap K K') = O)
      (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
      (c' : ModelCode O') (e : c₁.scheme ≅ c'.scheme),
      SemistableReduction.ModelCode.IsSemistable ϖ' c' ∧
        e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
          ((algebraMap K K').restrict O O' (fun x hx => by rw [← h] at hx; exact hx))) =
          c₁.toSpec)
    [ConnectedSpace (specialFibre c₁.toSpec)]
    (hdim : topologicalKrullDim (specialFibre c₁.toSpec) ≤ 1)
    (hact : ∀ σ : Q ≃ₐ[R] Q, ∃ ψ : c₁.scheme ⟶ c₁.scheme, ψ ≫ c₁.toSpec = c₁.toSpec ∧
      j₁ ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Q →+* Q)) ≫ j₁)
    (f : ∀ k, (P k).1.Lv.L.B →ₐ[R] Q)
    (hf : ∀ k, s'.comp (f k) = (Quotient.out (P k).2 : PreFibre Ω V hV (P k).1).1.1)
    (dom : ∀ k, c₁.scheme ⟶ (P k).1.Lv.c.scheme)
    (hdomS : ∀ k, dom k ≫ (P k).1.Lv.c.toSpec = c₁.toSpec)
    (hdomj : ∀ k, j₁ ≫ dom k = Spec.map (CommRingCat.ofHom (f k : (P k).1.Lv.L.B →+* Q)) ≫
      (P k).1.Lv.j) :
    ∃ G, galClass₂ O R A Ω M G ∧ Nonempty ((tempFibre O R A V hV).obj G) ∧
      ∀ k, ∃ (m : G ⟶ (P k).1) (u : (tempFibre O R A V hV).obj G),
        (tempFibre O R A V hV).map m u = (P k).2 := by
  let L : FiniteLevel R A := trivialLevel Q
  haveI : Subsingleton L.H := subsingleton_trivialLevel Q
  let φQ : Q ≃ₐ[R] L.B := (LevelData.codeEquiv R Q).symm
  let Lv : Level O R A :=
    { L := L
      c := c₁
      j := Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁
      j_toSpec := by
        rw [Category.assoc, hj₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        ext o
        exact φQ.commutes _
      ρ := 1
      ρ_toSpec := fun g => by
        change 𝟙 _ ≫ _ = _
        exact Category.id_comp _
      ρ_j := fun g => by
        have hg : g = 1 := Subsingleton.elim g 1
        subst hg
        change Spec.map (CommRingCat.ofHom (RingHom.id L.B)) ≫ _ = _ ≫ 𝟙 _
        rw [Category.comp_id]
        exact (congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _) }
  haveI : Subsingleton Lv.L.H := subsingleton_trivialLevel Q
  haveI : IsIso (CommRingCat.ofHom (φQ : Q →+* L.B)) := φQ.toRingEquiv.toCommRingCatIso.isIso_hom
  haveI hdomj' : IsSchemeTheoreticallyDominant Lv.j :=
    (inferInstance : IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁))
  haveI : Nonempty Lv.Z := inferInstanceAs (Nonempty (specialFibre c₁.toSpec))
  let z₀ : Lv.Z := Classical.arbitrary _
  let hp := universalCovering.isUniversalCovering.{u, u, u} (Z := Lv.Z) hdim z₀
  let hc := hp.countable_fibre
  let U : TempObj O R A := universalObj Lv hdim z₀
  have hconn : ∀ e : L.B, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he => by
    rcases hQc (φQ.symm e) (he.map φQ.symm) with h | h
    · left; simpa using congrArg φQ h
    · right; simpa using congrArg φQ h
  have hmem : galClass₂ O R A Ω M U := by
    refine ⟨Lv, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      hdim, z₀, hM, ⟨s'.comp (φQ.symm : L.B →ₐ[R] Q)⟩, fun t t' => ?_, hconn, fun σ => ?_,
      hss, hdomj', ⟨Iso.refl _⟩⟩
    · haveI := L.etale
      haveI := L.finite
      obtain ⟨σ', hσ'⟩ := hQg (t.comp (φQ : Q →ₐ[R] L.B)) (t'.comp (φQ : Q →ₐ[R] L.B))
      refine ⟨(φQ.symm.trans σ').trans φQ, ?_, fun σ hσ => ?_⟩
      · ext y
        have := DFunLike.congr_fun hσ' (φQ.symm y)
        simpa using this
      · have h₁ : t.comp ((φQ.symm.trans σ').trans φQ : L.B →ₐ[R] L.B) = t' := by
          ext y
          have := DFunLike.congr_fun hσ' (φQ.symm y)
          simpa using this
        exact AlgEquiv.coe_toAlgHom_injective
          (algHom_eq_of_comp_eq hconn _ _ t (hσ.trans h₁.symm))
    · obtain ⟨ψ, hψ, hjψ⟩ := hact ((φQ.trans σ).trans φQ.symm)
      refine ⟨ψ, hψ, ?_⟩
      change (Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁) ≫ ψ =
        Spec.map (CommRingCat.ofHom (σ : L.B →+* L.B)) ≫
          Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁
      rw [Category.assoc, hjψ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 3
      ext y
      simp
  -- the geometric point and a point of `Z̃` over its specialization
  let t : L.B →ₐ[R] Ω := s'.comp (φQ.symm : L.B →ₐ[R] Q)
  haveI := hp.connectedSpace
  obtain ⟨e, he⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
  let q₀ : PreFibre Ω V hV (obj Lv hp hc) := prePt V hV t e he
  refine ⟨U, hmem, ⟨Quotient.mk _ q₀⟩, fun k => ?_⟩
  let X := (P k).1
  let ℓ : LevelHom O R A Lv X.Lv :=
    { φ := FiniteLevel.homOfSubsingleton L X.Lv.L ((φQ : Q →ₐ[R] L.B).comp (f k))
      ψ := dom k
      ψ_toSpec := hdomS k
      j_ψ := by
        change (Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁) ≫ dom k = _
        rw [Category.assoc, hdomj, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl }
  have hq : q₀.1.1.comp ℓ.φ.f = (Quotient.out (P k).2 : PreFibre Ω V hV (P k).1).1.1 := by
    change t.comp ((φQ : Q →ₐ[R] L.B).comp (f k)) = _
    rw [← hf k]
    ext y
    simp [t]
  obtain ⟨m, -, hm⟩ := exists_hom_preMap V hV (hp := hp) (hc := hc) (X := (P k).1) ℓ
    (LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant ℓ) q₀ e rfl
    (Quotient.out (P k).2 : PreFibre Ω V hV (P k).1) hq
  refine ⟨m, Quotient.mk _ q₀, ?_⟩
  change Quotient.mk _ (preMap V hV m q₀) = (P k).2
  rw [hm]
  exact Quotient.out_eq _

end Core

end

end TemperedFundamentalGroups
