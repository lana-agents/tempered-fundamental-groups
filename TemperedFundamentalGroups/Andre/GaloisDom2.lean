/-
Copyright (c) 2026 LANA Project. All rights reserved.
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

omit [IsDomain R] [IsAlgClosed Ω] in
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
def trivialHLevel (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q]
    [Module.Finite R Q] : FiniteLevel R A where
  toEtaleCode := LevelData.code R Q
  H := ⊥
  surjective a := ⟨1, Subgroup.one_mem _, by rw [Subsingleton.elim a 1]; rfl⟩

lemma subsingleton_trivialLevel (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q]
    [Module.Finite R Q] : Subsingleton (trivialHLevel (R := R) (A := A) Q).H :=
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
  let L : FiniteLevel R A := trivialHLevel Q
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

section Mid

open TempObj GaloisObject GaloisLimit Components

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Domination from a Galois closure and W10**: if a connected Galois finite étale `B` with a
point `t₀` receives maps `f_k` from the levels of finitely many pointed objects `(X_k, x_k)` (with
`t₀ ∘ f_k` the geometric point of `x_k`), then a member of `galClass₂` dominates every
`(X_k, x_k)`. -/
theorem dom_mid (hW : SemistableReduction.Statement.StrongComponent.{u})
    (hR : ringKrullDim R = 1) {n : ℕ}
    (P : Fin n → Σ X : TempObj O R A, (tempFibre O R A V hV).obj X)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
    (hBc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hBg : ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t')
    (t₀ : B →ₐ[R] Ω) (f : ∀ k, (P k).1.Lv.L.B →ₐ[R] B)
    (hf : ∀ k, t₀.comp (f k) = (Quotient.out (P k).2 : PreFibre Ω V hV (P k).1).1.1) :
    ∃ G, galClass₂ O R A Ω (fun _ => True) G ∧ Nonempty ((tempFibre O R A V hV).obj G) ∧
      ∀ k, ∃ (m : G ⟶ (P k).1) (u : (tempFibre O R A V hV).obj G),
        (tempFibre O R A V hV).map m u = (P k).2 := by
  classical
  letI : Algebra K B := ((algebraMap R B).comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let G := B ≃ₐ[R] B
  haveI : Finite G := Finite.of_injective (fun σ : G => t₀.comp (σ : B →ₐ[R] B)) fun σ σ' h => by
    haveI : Algebra.FormallyUnramified R B := inferInstance
    exact AlgEquiv.coe_toAlgHom_injective (algHom_eq_of_comp_eq hBc _ _ t₀ h)
  haveI : SMulCommClass G K B := ⟨fun g k b => by
    change g (k • b) = k • g b
    rw [Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    exact (g : B →ₐ[R] B).commutes (algebraMap K R k)⟩
  let c₀ : ULift.{u} (Fin n) → ModelCode O := fun i => (P i.down).1.Lv.c
  let j₀ : ∀ i, Spec (CommRingCat.of B) ⟶ (c₀ i).scheme := fun i =>
    Spec.map (CommRingCat.ofHom (f i.down : (P i.down).1.Lv.L.B →+* B)) ≫ (P i.down).1.Lv.j
  have hj₀ : ∀ i, j₀ i ≫ (c₀ i).toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap K B).comp O.subtype)) := fun i => by
    simp only [j₀, c₀, Category.assoc]
    rw [(P i.down).1.Lv.j_toSpec, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    simp only [levelStructureMap, RingHom.comp_apply, AlgHom.coe_toRingHom]
    exact (f i.down).commutes _
  obtain ⟨K', _, _, _, _, O', hO', _, ϖ', hϖ', c', c, e, j, act, dom, hss, -, -, he, -, -, hjS,
    hact, hactj, hdomj, hdomS, -, hdim, hcomp⟩ := hW K O R hR (exists_finite_aeval hR).choose
      (exists_finite_aeval hR).choose_spec B G
      (ULift.{u} (Fin n)) c₀ j₀ hj₀
  haveI hK' : Algebra.Etale K K' :=
    ⟨Algebra.FormallyEtale.of_isSeparable K K',
      Algebra.FinitePresentation.of_finiteType.1 inferInstance⟩
  let C := TensorProduct K B K'
  haveI : Algebra.Etale R C := Algebra.Etale.comp R B C
  haveI : Module.Finite R C := Module.Finite.trans B C
  let a : K' →ₐ[K] Ω := IsAlgClosed.lift (R := K) (S := K') (M := Ω)
  let s'' : C →ₐ[R] Ω := Algebra.TensorProduct.lift t₀ a (fun _ _ => Commute.all _ _)
  obtain ⟨ε', hε', hsε'⟩ := exists_isPrimitive s''
  let κ : TensorProduct K K' B ≃ₐ[K] C := Algebra.TensorProduct.comm K K' B
  let ε := κ.symm ε'
  have hε : IsPrimitive ε := hε'.map_ringEquiv κ.symm.toRingEquiv
  have hε0 : ε ≠ 0 := fun h => by
    have h' : ε' = 0 := by simpa [ε] using congrArg κ h
    rw [h', map_zero] at hsε'
    exact zero_ne_one hsε'
  obtain ⟨c₁', c₁, e₁, ι₁, j₁, hss₁, -, -, he₁, hι₁, -, hι₁S, -, hj₁d, hj₁ι, hstab, hconn⟩ :=
    hcomp ε hε.1 hε0 hε.2
  let Q := C ⧸ Ideal.span {1 - ε'}
  haveI : Algebra.Etale R Q := quotient_etale hε'.1
  haveI : Module.Finite R Q := Module.Finite.trans C Q
  have hI : Ideal.span {1 - ε'} = (Ideal.span {1 - ε}).map (κ : TensorProduct K K' B →+* C) := by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change 1 - ε' = κ (1 - κ.symm ε')
    rw [map_sub, map_one, AlgEquiv.apply_symm_apply]
  let ξ : TensorProduct K K' B ⧸ Ideal.span {1 - ε} ≃+* Q :=
    Ideal.quotientEquiv _ _ κ.toRingEquiv hI
  let ξr : TensorProduct K K' B ⧸ Ideal.span {1 - ε} →+* Q := ξ
  let j₁Q : Spec (CommRingCat.of Q) ⟶ c₁.scheme := Spec.map (CommRingCat.ofHom ξr) ≫ j₁
  let s' : Q →ₐ[R] Ω := liftPoint s'' hsε'
  have hQc := isConnected_quotient hε'
  have hdesc : ∀ Θ : C ≃ₐ[R] C, Θ ε' = ε' →
      Ideal.span {1 - ε'} = (Ideal.span {1 - ε'}).map (Θ : C →+* C) := fun Θ hΘ => by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change 1 - ε' = Θ (1 - ε')
    rw [map_sub, map_one, hΘ]
  have hQg : ∀ v v' : Q →ₐ[R] Ω, ∃ σ : Q ≃ₐ[R] Q, v.comp (σ : Q →ₐ[R] Q) = v' := by
    intro v v'
    obtain ⟨δ, γ, hΘε, hΘw⟩ := exists_galois_component hBg hε'
      (v.comp (Ideal.Quotient.mkₐ R _)) (v'.comp (Ideal.Quotient.mkₐ R _)) (comp_mk_eps v)
      (comp_mk_eps v')
    refine ⟨Ideal.quotientEquivAlg _ _ (Algebra.TensorProduct.congr δ γ) (hdesc _ hΘε),
      Ideal.Quotient.algHom_ext R (AlgHom.ext fun x => ?_)⟩
    have := DFunLike.congr_fun hΘw x
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom] at this ⊢
    rw [Ideal.quotientEquivAlg_mk]
    exact this
  haveI := hι₁
  haveI := hj₁d
  have hcongr : ∀ (δ : B ≃ₐ[R] B) (γ : K' ≃ₐ[K] K') (x : TensorProduct K K' B),
      Algebra.TensorProduct.congr ((δ⁻¹, γ⁻¹) : G × (K' ≃ₐ[K] K')).2⁻¹
        (MulSemiringAction.toAlgAut G K B ((δ⁻¹, γ⁻¹) : G × (K' ≃ₐ[K] K')).1⁻¹) x =
      κ.symm (Algebra.TensorProduct.congr δ γ (κ x)) := by
    intro δ γ x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul k b =>
      simp only [inv_inv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, κ]
      rfl
  have hactQ : ∀ σ : Q ≃ₐ[R] Q, ∃ ψ : c₁.scheme ⟶ c₁.scheme, ψ ≫ c₁.toSpec = c₁.toSpec ∧
      j₁Q ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Q →+* Q)) ≫ j₁Q := by
    intro σ
    obtain ⟨δ, γ, hΘε, hΘw⟩ := exists_galois_component hBg hε' s''
      ((s'.comp (σ : Q →ₐ[R] Q)).comp (Ideal.Quotient.mkₐ R _)) hsε' (comp_mk_eps _)
    let Θ : C ≃ₐ[R] C := Algebra.TensorProduct.congr δ γ
    let Θbar : Q ≃ₐ[R] Q := Ideal.quotientEquivAlg _ _ Θ (hdesc _ hΘε)
    have hσ : (σ : Q →ₐ[R] Q) = (Θbar : Q →ₐ[R] Q) := by
      refine algHom_eq_of_comp_eq hQc _ _ s' (Ideal.Quotient.algHom_ext R (AlgHom.ext fun x => ?_))
      have := DFunLike.congr_fun hΘw x
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom] at this ⊢
      rw [Ideal.quotientEquivAlg_mk]
      exact this.symm
    let gσ : G × (K' ≃ₐ[K] K') := (δ⁻¹, γ⁻¹)
    obtain ⟨ψ, hψ⟩ := hstab gσ (by
      rw [hcongr]
      change κ.symm (Θ (κ (κ.symm ε'))) = κ.symm ε'
      rw [AlgEquiv.apply_symm_apply, hΘε])
    refine ⟨ψ, ?_, ?_⟩
    · rw [← hι₁S, ← Category.assoc, hψ, Category.assoc, hact gσ]
    · rw [← cancel_mono ι₁]
      simp only [j₁Q, Category.assoc]
      rw [hψ, ← Category.assoc j₁, hj₁ι, Category.assoc, ← hactj gσ]
      simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun x => ?_
      change ξ (Ideal.Quotient.mk _ (Algebra.TensorProduct.congr gσ.2⁻¹
        (MulSemiringAction.toAlgAut G K B gσ.1⁻¹) x)) = σ (ξ (Ideal.Quotient.mk _ x))
      rw [hcongr]
      have h₁ : σ (ξ (Ideal.Quotient.mk _ x)) = Θbar (ξ (Ideal.Quotient.mk _ x)) :=
        DFunLike.congr_fun hσ _
      rw [h₁]
      change Ideal.Quotient.mk _ (κ (κ.symm (Θ (κ x)))) = Θbar (Ideal.Quotient.mk _ (κ x))
      rw [AlgEquiv.apply_symm_apply]
      exact (Ideal.quotientEquivAlg_mk _ _ _ _).symm
  have hj₁Q : j₁Q ≫ c₁.toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap R Q).comp ((algebraMap K R).comp O.subtype))) := by
    simp only [j₁Q, ← hι₁S, Category.assoc]
    rw [← Category.assoc j₁, hj₁ι, Category.assoc, hjS]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun o => ?_
    change Ideal.Quotient.mk _ (κ ((algebraMap K K' o) ⊗ₜ[K] (1 : B))) =
      Ideal.Quotient.mk _ (algebraMap R C (algebraMap K R o))
    congr 1
    rw [← IsScalarTower.algebraMap_apply K R C, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.comm_tmul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  haveI : IsIso (CommRingCat.ofHom ξr) :=
    (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom ξr)).2 ξ.bijective
  haveI : IsSchemeTheoreticallyDominant j₁Q := inferInstanceAs (IsSchemeTheoreticallyDominant
    (Spec.map (CommRingCat.ofHom ξr) ≫ j₁))
  haveI : ConnectedSpace (specialFibre c₁.toSpec) := hconn.1
  have hdim₁ : topologicalKrullDim (specialFibre c₁.toSpec) ≤ 1 := by
    refine le_trans (Topology.IsInducing.topologicalKrullDim_le
      (f := specialFibreMap ι₁ hι₁S) ?_) hdim
    exact (Topology.IsInducing.subtypeVal.of_comp_iff).1
      (ι₁.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal)
  let f' : ∀ k, (P k).1.Lv.L.B →ₐ[R] Q := fun k =>
    (Ideal.Quotient.mkₐ R _).comp ((Algebra.TensorProduct.includeLeft : B →ₐ[R] C).comp (f k))
  refine dom_core V hV (fun _ => True) P Q hQc hQg s' c₁ trivial j₁Q hj₁Q
    ⟨K', inferInstance, inferInstance, inferInstance, O', hO', inferInstance, ϖ', hϖ', c₁', e₁,
      hss₁, he₁⟩ hdim₁ hactQ f' (fun k => ?_) (fun k => ι₁ ≫ dom ⟨k⟩)
    (fun k => by rw [Category.assoc, hdomS, hι₁S]) (fun k => ?_)
  · rw [← hf k]
    ext y
    change liftPoint s'' hsε' (Ideal.Quotient.mk _ (f k y ⊗ₜ[K] 1)) = t₀ (f k y)
    rw [liftPoint_mk]
    change Algebra.TensorProduct.lift t₀ a _ (f k y ⊗ₜ[K] 1) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · simp only [j₁Q, Category.assoc]
    rw [← Category.assoc j₁, hj₁ι, Category.assoc, hdomj]
    simp only [j₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3

/-- **(dom)** The Galois objects over levels with trivial `H` dominate: finitely many pointed
objects `(X_k, x_k)` are dominated by a member of `galClass₂`. -/
theorem isDominating_galClass₂ (hW : SemistableReduction.Statement.StrongComponent.{u})
    (hR : ringKrullDim R = 1) :
    IsDominating (tempFibre O R A V hV) (galClass₂ O R A Ω (fun _ => True)) := by
  classical
  refine isDominating_of_forall_exists (isGaloisClass_galClass₂ V hV _) fun n P => ?_
  let q : ∀ k, PreFibre Ω V hV (P k).1 := fun k => Quotient.out (P k).2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : Nonempty (R →ₐ[R] Ω) := ⟨Algebra.ofId R Ω⟩
    obtain ⟨B, _, _, _, _, t₀, -, hBc, hBg⟩ := exists_galoisClosure (R := R) (Ω := Ω) (B₀ := R)
    obtain ⟨G, hG, hne, -⟩ := dom_mid V hV hW hR P B hBc hBg t₀ (fun k => k.elim0)
      (fun k => k.elim0)
    exact ⟨G, hG, hne, fun k => k.elim0⟩
  · haveI : ∀ k, Algebra.Etale R ((P k).1.Lv.L.B) := fun k => (P k).1.Lv.L.etale
    haveI : ∀ k, Module.Finite R ((P k).1.Lv.L.B) := fun k => (P k).1.Lv.L.finite
    let B₀ := Π k, (P k).1.Lv.L.B
    haveI : Nonempty (B₀ →ₐ[R] Ω) :=
      ⟨(q ⟨0, hn⟩).1.1.comp (Pi.evalAlgHom R (fun k => (P k).1.Lv.L.B) ⟨0, hn⟩)⟩
    obtain ⟨B, _, _, _, _, t₀, hpts, hBc, hBg⟩ :=
      exists_galoisClosure (R := R) (Ω := Ω) (B₀ := B₀)
    have hf : ∀ k, ∃ f : (P k).1.Lv.L.B →ₐ[R] B, t₀.comp f = (q k).1.1 := fun k => by
      obtain ⟨g, hg⟩ := hpts ((q k).1.1.comp (Pi.evalAlgHom R (fun k => (P k).1.Lv.L.B) k))
      exact exists_algHom_of_pi hBc g t₀ k _ hg
    choose f hf using hf
    obtain ⟨G, hG, hne, hdom⟩ := dom_mid V hV hW hR P B hBc hBg t₀ f hf
    exact ⟨G, hG, hne, fun k => let ⟨m, u, h⟩ := hdom k; ⟨m, u, h⟩⟩

/-- **(gal), (dom), (rig)** for the Galois objects over levels with trivial `H` (scheme case),
from W10 with components. -/
theorem galoisLimitData₂ (hW : SemistableReduction.Statement.StrongComponent.{u})
    (hR : ringKrullDim R = 1) :
    IsGaloisClass (tempFibre O R A V hV) (galClass₂ O R A Ω (fun _ => True)) ∧
      IsDominating (tempFibre O R A V hV) (galClass₂ O R A Ω (fun _ => True)) ∧
      IsRigid (tempFibre O R A V hV) (galClass₂ O R A Ω (fun _ => True)) :=
  ⟨isGaloisClass_galClass₂ V hV _, isDominating_galClass₂ V hV hW hR, isRigid_galClass₂ V hV _⟩

end Mid

end

end TemperedFundamentalGroups
