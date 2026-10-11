/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.Andre.OrbGaloisDom
import TemperedFundamentalGroups.Andre.OrbClosure
import TemperedFundamentalGroups.Andre.GaloisDomW

/-!
# Domination by orbifold Galois objects (Blueprint §11.3, G6, orbifold case)

`dom_midO`: if a connected finite étale `B`, Galois over `R` and over `[Spec R / A]` (every
`a ∈ A` lifts to a semilinear automorphism of `B`), with a geometric point `t₀`, receives maps
`f_k` from the levels of finitely many pointed objects `(X_k, x_k)`, then a member of
`galClassO` dominates every `(X_k, x_k)`. Proof: W10 (`StrongComponentAS`) for `B` with the
group `G = SemilinearAut R A B` of all semilinear automorphisms (acting on `R` through `A`, on
the invariant x-line of `exists_finite_aeval_invariant`); the component `Q = (B ⊗_K K') ⧸ (1 - ε)`
through a point over `t₀` is connected, Galois over `R`, and every semilinear automorphism of
`Q` comes from an element of `G × Gal(K'/K)` stabilizing `ε` (`exists_stab_eq`), hence extends
to the component model `𝒯₁`; the core level of `Q` with `𝒯₁` then satisfies the conditions of
`galClassO` and `dom_coreO` applies.

`isDominating_galClassO`: **(dom)**, via `exists_galoisClosure_sym` applied to
`∏_{a ∈ A} (∏_k B_k)^{(a)}`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold TensorProduct

set_option linter.unusedSectionVars false

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit Components

section Stab

variable {K : Type u} [Field K] {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A]
  [MulSemiringAction A R] [SMulCommClass A K R]
  {B : Type u} [CommRing B] [Algebra R B] [Algebra K B] [IsScalarTower K R B]
  {K' : Type u} [Field K'] [Algebra K K']

/-- The semilinear automorphism `g ⊗ γ` of `B ⊗_K K'`. -/
abbrev Θt (h : SemilinearAut R A B × (K' ≃ₐ[K] K')) : SemilinearAut R A (B ⊗[K] K') :=
  tensorAut K' h

lemma Θt_mul_apply (h₁ h₂ : SemilinearAut R A B × (K' ≃ₐ[K] K')) (y : B ⊗[K] K') :
    (Θt (h₁ * h₂)).σ y = (Θt h₁).σ ((Θt h₂).σ y) := by
  rw [Θt, map_mul]
  rfl

/-- An element stabilizing the idempotent `ε` descends to the component `(B ⊗ K') ⧸ (1 - ε)`. -/
def Θq {ε : B ⊗[K] K'} (h : SemilinearAut R A B × (K' ≃ₐ[K] K')) (hh : (Θt h).σ ε = ε) :
    SemilinearAut R A (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) where
  a := h.1.a
  σ := Ideal.quotientEquiv _ _ (Θt h).σ (by
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    change 1 - ε = (Θt h).σ (1 - ε)
    rw [map_sub, map_one, hh])
  map_algebraMap r := by
    change Ideal.Quotient.mk _ ((Θt h).σ (algebraMap R (B ⊗[K] K') r)) =
      Ideal.Quotient.mk _ (algebraMap R (B ⊗[K] K') (h.1.a • r))
    rw [(Θt h).map_algebraMap, tensorAut_a]

lemma Θq_mk {ε : B ⊗[K] K'} (h : SemilinearAut R A B × (K' ≃ₐ[K] K')) (hh : (Θt h).σ ε = ε)
    (y : B ⊗[K] K') : (Θq h hh).σ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ ((Θt h).σ y) :=
  rfl

/-- An `R`-linear automorphism `δ` of `B`, as a semilinear automorphism over `1`. -/
def linAut (δ : B ≃ₐ[R] B) : SemilinearAut R A B :=
  ⟨1, δ.toRingEquiv, fun r => by
    rw [one_smul]
    exact δ.commutes r⟩

lemma Θt_linAut (δ : B ≃ₐ[R] B) (γ : K' ≃ₐ[K] K') (y : B ⊗[K] K') :
    (Θt ((linAut δ : SemilinearAut R A B), γ)).σ y =
      Algebra.TensorProduct.congr (δ.restrictScalars K) γ y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b k => rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]

variable {Ω : Type u} [Field Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower K R Ω]

/-- Two geometric points of `B ⊗_K K'` differ by `δ ⊗ γ`, `δ ∈ Aut_R(B)`, `γ ∈ Gal(K'/K)`. -/
lemma exists_congr_comp [Normal K K']
    (hgal : ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t')
    (w₁ w₂ : B ⊗[K] K' →ₐ[R] Ω) :
    ∃ (δ : B ≃ₐ[R] B) (γ : K' ≃ₐ[K] K'), ∀ y, w₁ (Algebra.TensorProduct.congr
      (δ.restrictScalars K) γ y) = w₂ y := by
  obtain ⟨δ, hδ⟩ := hgal (w₁.comp Algebra.TensorProduct.includeLeft)
    (w₂.comp Algebra.TensorProduct.includeLeft)
  obtain ⟨γ, hγ⟩ := exists_algEquiv_comp_eq ((w₁.restrictScalars K).comp
    Algebra.TensorProduct.includeRight) ((w₂.restrictScalars K).comp
    Algebra.TensorProduct.includeRight)
  refine ⟨δ, γ, fun y => ?_⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul b k =>
    have e₁ := DFunLike.congr_fun hδ b
    have e₂ := DFunLike.congr_fun hγ k
    simp only [AlgHom.comp_apply, Algebra.TensorProduct.includeLeft_apply,
      Algebra.TensorProduct.includeRight_apply, AlgHom.coe_restrictScalars',
      AlgEquiv.coe_toAlgHom] at e₁ e₂
    change w₁ (δ b ⊗ₜ[K] γ k) = w₂ (b ⊗ₜ[K] k)
    rw [← mul_one (δ b), ← one_mul (γ k), ← Algebra.TensorProduct.tmul_mul_tmul, map_mul,
      ← mul_one b, ← one_mul k, ← Algebra.TensorProduct.tmul_mul_tmul, map_mul w₂]
    simp only [mul_one, one_mul]
    rw [e₁, ← e₂]
  | add y z hy hz => rw [map_add, map_add, hy, hz, map_add]

variable [Algebra.Etale R (B ⊗[K] K')] [Module.Finite R (B ⊗[K] K')] [IsDomain R]
  [IsAlgClosed Ω] [Normal K K']
  (hgal : ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t')
  {ε : B ⊗[K] K'} (hε : IsPrimitive ε) (s'' : B ⊗[K] K' →ₐ[R] Ω) (hsε : s'' ε = 1)

include hgal hε hsε in
/-- **Lifts of `a ∈ A` stabilizing a component.** -/
lemma exists_stab_lift (g : SemilinearAut R A B) :
    ∃ h : SemilinearAut R A B × (K' ≃ₐ[K] K'), h.1.a = g.a ∧ (Θt h).σ ε = ε := by
  set e₁ := (Θt ((g, 1) : SemilinearAut R A B × (K' ≃ₐ[K] K'))).σ ε
  have he₁ : IsPrimitive e₁ := hε.map_ringEquiv _
  have he₀ : e₁ ≠ 0 := fun h => by
    have : ε = 0 := (RingEquiv.injective _) (h.trans (map_zero _).symm)
    rw [this, map_zero] at hsε
    exact zero_ne_one hsε
  obtain ⟨w₁, hw₁⟩ : ∃ w : B ⊗[K] K' →ₐ[R] Ω, w e₁ = 1 := by
    by_contra hno
    push Not at hno
    exact he₀ (eq_zero_of_forall_algHom he₁.1 fun u =>
      (idem_eq_zero_or_one he₁.1 u).resolve_right (hno u))
  obtain ⟨δ, γ, hδγ⟩ := exists_congr_comp hgal s'' w₁
  refine ⟨(linAut δ * g, γ), by simp [linAut], ?_⟩
  have hmul : (Θt ((linAut δ * g, γ) : SemilinearAut R A B × (K' ≃ₐ[K] K'))) =
      Θt ((linAut δ, γ) : SemilinearAut R A B × (K' ≃ₐ[K] K')) * Θt ((g, 1) :
        SemilinearAut R A B × (K' ≃ₐ[K] K')) := by
    rw [← map_mul]
    rfl
  rw [hmul, SemilinearAut.mul_σ, RingEquiv.trans_apply, Θt_linAut]
  refine (he₁.map_ringEquiv (Algebra.TensorProduct.congr (δ.restrictScalars K) γ).toRingEquiv).eq
    hε s'' ?_ hsε
  change s'' (Algebra.TensorProduct.congr (δ.restrictScalars K) γ e₁) = 1
  rw [hδγ, hw₁]

variable (hQc : ∀ x : B ⊗[K] K' ⧸ Ideal.span {1 - ε}, IsIdempotentElem x → x = 0 ∨ x = 1)

include hgal hε hsε hQc in
/-- **`R`-linear automorphisms of the component come from the stabilizer.** -/
lemma exists_stab_linear (σ : (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) ≃ₐ[R]
    (B ⊗[K] K' ⧸ Ideal.span {1 - ε})) :
    ∃ (h : SemilinearAut R A B × (K' ≃ₐ[K] K')) (hh : (Θt h).σ ε = ε),
      ∀ y, σ y = (Θq h hh).σ y := by
  haveI : Algebra.Etale R (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) := quotient_etale hε.1
  let s' := liftPoint s'' hsε
  obtain ⟨δ, γ, hδγ⟩ := exists_congr_comp hgal s''
    ((s'.comp (σ : (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) →ₐ[R]
      (B ⊗[K] K' ⧸ Ideal.span {1 - ε}))).comp (Ideal.Quotient.mkₐ R _))
  let h : SemilinearAut R A B × (K' ≃ₐ[K] K') := (linAut δ, γ)
  have hΘ : ∀ y, s'' ((Θt h).σ y) = s' (σ (Ideal.Quotient.mk _ y)) := fun y => by
    rw [Θt_linAut, hδγ]
    rfl
  have hh : (Θt h).σ ε = ε := by
    refine (hε.map_ringEquiv _).eq hε s'' ?_ hsε
    rw [hΘ, mk_eps, map_one, map_one]
  refine ⟨h, hh, ?_⟩
  let τ : (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) →ₐ[R] (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) :=
    { ((Θq h hh).σ : _ →+* _) with
      commutes' := fun r => by
        change (Θq h hh).σ (algebraMap R _ r) = _
        rw [(Θq h hh).map_algebraMap]
        change algebraMap R _ ((1 : A) • r) = _
        rw [one_smul] }
  have key : (σ : (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) →ₐ[R]
      (B ⊗[K] K' ⧸ Ideal.span {1 - ε})) = τ := by
    refine algHom_eq_of_comp_eq hQc _ _ s' (Ideal.Quotient.algHom_ext R (AlgHom.ext fun y => ?_))
    change s' (σ (Ideal.Quotient.mk _ y)) = s' (Ideal.Quotient.mk _ ((Θt h).σ y))
    rw [← hΘ]
    rfl
  exact fun y => DFunLike.congr_fun key y

include hgal hε hsε hQc in
/-- **Every semilinear automorphism of the component comes from the stabilizer** of `ε` in
`SemilinearAut R A B × Gal(K'/K)`, if every `a ∈ A` lifts to `B`. -/
lemma exists_stab_eq (hsym : ∀ a : A, ∃ g : SemilinearAut R A B, g.a = a)
    (γQ : SemilinearAut R A (B ⊗[K] K' ⧸ Ideal.span {1 - ε})) :
    ∃ (h : SemilinearAut R A B × (K' ≃ₐ[K] K')) (_ : (Θt h).σ ε = ε),
      ∀ y, γQ.σ (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ ((Θt h).σ y) := by
  obtain ⟨g, hg⟩ := hsym γQ.a
  obtain ⟨h₁, ha₁, hh₁⟩ := exists_stab_lift hgal hε s'' hsε g
  let σ' : SemilinearAut R A (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) := (Θq h₁ hh₁)⁻¹ * γQ
  have hσ'a : σ'.a = 1 := by
    change (h₁.1.a)⁻¹ * γQ.a = 1
    rw [ha₁, hg, inv_mul_cancel]
  let σ'' : (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) ≃ₐ[R] (B ⊗[K] K' ⧸ Ideal.span {1 - ε}) :=
    { σ'.σ with
      commutes' := fun r => by
        change σ'.σ (algebraMap R _ r) = _
        rw [σ'.map_algebraMap, hσ'a, one_smul] }
  obtain ⟨h₂, hh₂, hσ₂⟩ := exists_stab_linear (A := A) hgal hε s'' hsε hQc σ''
  have hh : (Θt (h₁ * h₂)).σ ε = ε := by
    rw [Θt_mul_apply, hh₂, hh₁]
  refine ⟨h₁ * h₂, hh, fun y => ?_⟩
  have e1 : γQ.σ (Ideal.Quotient.mk _ y) = (Θq h₁ hh₁).σ (σ'.σ (Ideal.Quotient.mk _ y)) := by
    change γQ.σ _ = (Θq h₁ hh₁).σ ((Θq h₁ hh₁).σ.symm (γQ.σ _))
    rw [RingEquiv.apply_symm_apply]
  rw [e1]
  change (Θq h₁ hh₁).σ (σ'' (Ideal.Quotient.mk _ y)) = _
  rw [hσ₂, Θq_mk, Θq_mk, Θt_mul_apply]

end Stab

section CoreQ

variable {K : Type u} [Field K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R] [IsNoetherianRing R] [Finite A]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (A₁ : Type u) [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

/-- **Domination from a Galois-over-`[Spec R / A]` component** `Q` with a model `𝒯₁`: the core
level of `Q` (over `A₁`) satisfies the conditions of `galClassO` and `dom_coreO` applies. -/
theorem dom_coreQ {n : ℕ} (Pt : Fin n → Σ X : TempObj O R A, (tempFibre O R A V hV).obj X)
    (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q] [Module.Finite R Q]
    (hQc : ∀ e : Q, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hQg : ∀ t t' : Q →ₐ[R] Ω, ∃ σ : Q ≃ₐ[R] Q, t.comp (σ : Q →ₐ[R] Q) = t')
    (hQsym : ∀ a : A, ∃ γ : SemilinearAut R A Q, γ.a = a)
    (s' : Q →ₐ[R] Ω) (c₁ : ModelCode O) (j₁ : Spec (CommRingCat.of Q) ⟶ c₁.scheme)
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
    (hact : ∀ γ : SemilinearAut R A Q, ∃ ψ : c₁.scheme ⟶ c₁.scheme, ψ ≫ c₁.toSpec = c₁.toSpec ∧
      j₁ ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : Q →+* Q)) ≫ j₁)
    (f : ∀ k, (Pt k).1.Lv.L.B →ₐ[R] Q)
    (hf : ∀ k, s'.comp (f k) = (Quotient.out (Pt k).2 : PreFibre Ω V hV (Pt k).1).1.1)
    (dom : ∀ k, c₁.scheme ⟶ (Pt k).1.Lv.c.scheme)
    (hdomS : ∀ k, dom k ≫ (Pt k).1.Lv.c.toSpec = c₁.toSpec)
    (hdomj : ∀ k, j₁ ≫ dom k = Spec.map (CommRingCat.ofHom (f k : (Pt k).1.Lv.L.B →+* Q)) ≫
      (Pt k).1.Lv.j) :
    ∃ G, galClassO O R A Ω A₁ G ∧ Nonempty ((tempFibre O R A V hV).obj G) ∧
      ∀ k, ∃ (m : G ⟶ (Pt k).1) (u : (tempFibre O R A V hV).obj G),
        (tempFibre O R A V hV).map m u = (Pt k).2 := by
  let L : FiniteLevel R A₁ := trivialHLevel Q
  haveI : Subsingleton L.H := subsingleton_trivialLevel Q
  let φQ : Q ≃ₐ[R] L.B := coreEquiv (A := A₁) Q
  let Lv : Level O R A₁ := coreLevel Q c₁ j₁ hj₁
  haveI : Subsingleton Lv.L.H := subsingleton_trivialLevel Q
  haveI : IsIso (CommRingCat.ofHom (φQ : Q →+* L.B)) := φQ.toRingEquiv.toCommRingCatIso.isIso_hom
  haveI hdomj' : IsSchemeTheoreticallyDominant Lv.j :=
    (inferInstance : IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁))
  haveI : Nonempty Lv.Z := inferInstanceAs (Nonempty (specialFibre c₁.toSpec))
  haveI : ConnectedSpace Lv.Z := inferInstanceAs (ConnectedSpace (specialFibre c₁.toSpec))
  let z₀ : Lv.Z := Classical.arbitrary _
  have hconn : ∀ e : L.B, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he => by
    rcases hQc (φQ.symm e) (he.map φQ.symm) with h | h
    · left; simpa using congrArg φQ h
    · right; simpa using congrArg φQ h
  have hgalL : ∀ t t' : L.B →ₐ[R] Ω, ∃ σ : L.B ≃ₐ[R] L.B, t.comp (σ : L.B →ₐ[R] L.B) = t' := by
    intro t t'
    obtain ⟨σ', hσ'⟩ := hQg (t.comp (φQ : Q →ₐ[R] L.B)) (t'.comp (φQ : Q →ₐ[R] L.B))
    refine ⟨(φQ.symm.trans σ').trans φQ, ?_⟩
    ext y
    have := DFunLike.congr_fun hσ' (φQ.symm y)
    simpa using this
  have hsymL : ∀ a : A, ∃ γ : SemilinearAut R A L.B, γ.a = a := fun a => by
    obtain ⟨γ, hγ⟩ := hQsym a
    exact ⟨SemilinearAut.transport φQ.symm γ, hγ⟩
  have hactL : ∀ γ : SemilinearAut R A Lv.L.B, ∃ ψ : Lv.c.scheme ⟶ Lv.c.scheme,
      ψ ≫ Lv.c.toSpec = Lv.c.toSpec ∧
      Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (γ.σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j := fun γ => by
    obtain ⟨ψ, hψ, hjψ⟩ := hact (SemilinearAut.transport φQ γ)
    refine ⟨ψ, hψ, ?_⟩
    change (Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁) ≫ ψ =
      Spec.map (CommRingCat.ofHom (γ.σ : L.B →+* L.B)) ≫
        Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁
    rw [Category.assoc, hjψ, ← Category.assoc, ← Category.assoc, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext y
    simp
  have hssL : IsSemistableLevel Lv := by
    obtain ⟨K', i1, i2, i3, O', hO', i4, ϖ', hϖ', c', e, h1, h2⟩ := hss
    exact ⟨K', i1, i2, i3, O', hO', i4, ϖ', hϖ', c', e, h1, h2⟩
  let t : L.B →ₐ[R] Ω := s'.comp (φQ.symm : L.B →ₐ[R] Q)
  exact dom_coreO V hV A₁ Pt Lv hdim z₀ hgalL hconn hsymL hactL hssL t
    (fun k => (φQ : Q →ₐ[R] L.B).comp (f k))
    (fun k => by
      rw [← hf k]
      ext y
      simp [t])
    dom hdomS (fun k => by
      change (Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁) ≫ dom k = _
      rw [Category.assoc, hdomj, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      rfl)

end CoreQ

section Mid

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R] [IsNoetherianRing R]
  {A : Type u} [Group A] [MulSemiringAction A R] [SMulCommClass A K R] [Finite A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)
  (A₁ : Type u) [Group A₁] [Subsingleton A₁] [MulSemiringAction A₁ R]

/-- An `R`-linear automorphism from a semilinear automorphism over `1`. -/
def algEquivOfA {B : Type u} [CommRing B] [Algebra R B] (g : SemilinearAut R A B) (h : g.a = 1) :
    B ≃ₐ[R] B :=
  { g.σ with
    commutes' := fun r => by
      change g.σ (algebraMap R B r) = _
      rw [g.map_algebraMap, h, one_smul] }

lemma finite_semilinearAut {B : Type u} [CommRing B] [Algebra R B] [Algebra.Etale R B]
    [Module.Finite R B] (hBc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) (t₀ : B →ₐ[R] Ω)
    (hBsym : ∀ a : A, ∃ γ : SemilinearAut R A B, γ.a = a) : Finite (SemilinearAut R A B) := by
  choose lam hlam using hBsym
  haveI : Finite (B ≃ₐ[R] B) := Finite.of_injective (fun σ : B ≃ₐ[R] B =>
    t₀.comp (σ : B →ₐ[R] B)) fun σ σ' h =>
      AlgEquiv.coe_toAlgHom_injective (algHom_eq_of_comp_eq hBc _ _ t₀ h)
  have h1 : ∀ g : SemilinearAut R A B, ((lam g.a)⁻¹ * g).a = 1 := fun g => by
    rw [SemilinearAut.mul_a, SemilinearAut.inv_a, hlam, inv_mul_cancel]
  refine Finite.of_injective (fun g : SemilinearAut R A B =>
    (g.a, algEquivOfA ((lam g.a)⁻¹ * g) (h1 g))) fun g g' h => ?_
  have ha : g.a = g'.a := congrArg Prod.fst h
  have hσ := congrArg Prod.snd h
  simp only at hσ
  have key : (lam g.a)⁻¹ * g = (lam g'.a)⁻¹ * g' := by
    refine SemilinearAut.ext (by rw [h1, h1]) (RingEquiv.ext fun y => ?_)
    exact DFunLike.congr_fun hσ y
  rw [← ha] at key
  exact mul_left_cancel key

/-- **Domination by orbifold Galois objects** from a Galois-over-`[Spec R / A]` algebra `B`. -/
theorem dom_midO (hW : SemistableReduction.Statement.StrongComponentAS.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1) {n : ℕ}
    (P : Fin n → Σ X : TempObj O R A, (tempFibre O R A V hV).obj X)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
    (hBc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hBg : ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t')
    (hBsym : ∀ a : A, ∃ γ : SemilinearAut R A B, γ.a = a)
    (t₀ : B →ₐ[R] Ω) (f : ∀ k, (P k).1.Lv.L.B →ₐ[R] B)
    (hf : ∀ k, t₀.comp (f k) = (Quotient.out (P k).2 : PreFibre Ω V hV (P k).1).1.1) :
    ∃ G, galClassO O R A Ω A₁ G ∧ Nonempty ((tempFibre O R A V hV).obj G) ∧
      ∀ k, ∃ (m : G ⟶ (P k).1) (u : (tempFibre O R A V hV).obj G),
        (tempFibre O R A V hV).map m u = (P k).2 := by
  classical
  letI : Algebra K B := ((algebraMap R B).comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R B := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let G := SemilinearAut R A B
  letI : MulSemiringAction G B := actionOf (MonoidHom.id G)
  haveI : SMulCommClass G K B := smulCommClass_actionOf (MonoidHom.id G)
  letI : MulSemiringAction G R :=
    MulSemiringAction.compHom R ((MulSemiringAction.toRingAut A R).comp SemilinearAut.toA)
  haveI : SMulCommClass G K R := ⟨fun g k r => smul_comm g.a k r⟩
  haveI : Finite G := finite_semilinearAut hBc t₀ hBsym
  have hGR : ∀ (g : G) (r : R), g • algebraMap R B r = algebraMap R B (g • r) :=
    fun g r => g.map_algebraMap r
  obtain ⟨x, hxG, hx⟩ := exists_finite_aeval_invariant (K := K) (G := G) hR
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
  obtain ⟨K', _, _, _, _, O', hO', _, ϖ', hϖ', c', c, e, j, act, dom, hss, he, -, hjS,
    hact, hactj, hdomj, hdomS, hdim, hcomp⟩ :=
    hW K O p hp hpm R hR x hx B G hGR hxG (ULift.{u} (Fin n)) c₀ j₀ hj₀
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
  obtain ⟨c₁', c₁, e₁, ι₁, j₁, hss₁, hsplit₁, hloop₁, he₁, hι₁, hι₁S, hj₁d, hj₁ι, hstab,
    hconn, L₁, _, _, _, _, _, _, j₁', hK'L₁, hWM, hj₁'⟩ := hcomp ε hε.1 hε0 hε.2
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
  -- the action of `G × Gal(K'/K)` in the two conventions
  have hcongrG : ∀ (h : G × (K' ≃ₐ[K] K')) (y : TensorProduct K K' B),
      Algebra.TensorProduct.congr ((h.1⁻¹, h.2⁻¹) : G × (K' ≃ₐ[K] K')).2⁻¹
        (MulSemiringAction.toAlgAut G K B ((h.1⁻¹, h.2⁻¹) : G × (K' ≃ₐ[K] K')).1⁻¹) y =
      κ.symm ((Θt h).σ (κ y)) := by
    intro h y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul k b =>
      simp only [inv_inv, Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul]
      rfl
  -- semilinear automorphisms of `Q`
  have hsymQ : ∀ a' : A, ∃ γ : SemilinearAut R A Q, γ.a = a' := fun a' => by
    obtain ⟨g, hg⟩ := hBsym a'
    obtain ⟨h, ha, hh⟩ := exists_stab_lift hBg hε' s'' hsε' g
    exact ⟨Θq h hh, ha.trans hg⟩
  have hactQ : ∀ γQ : SemilinearAut R A Q, ∃ ψ : c₁.scheme ⟶ c₁.scheme,
      ψ ≫ c₁.toSpec = c₁.toSpec ∧
      j₁Q ≫ ψ = Spec.map (CommRingCat.ofHom (γQ.σ : Q →+* Q)) ≫ j₁Q := by
    intro γQ
    obtain ⟨h, hh, hγ⟩ := exists_stab_eq hBg hε' s'' hsε' hQc hBsym γQ
    obtain ⟨ψ, hψ⟩ := hstab (h.1⁻¹, h.2⁻¹) (by
      rw [hcongrG]
      change κ.symm ((Θt h).σ (κ (κ.symm ε'))) = κ.symm ε'
      rw [AlgEquiv.apply_symm_apply, hh])
    refine ⟨ψ, ?_, ?_⟩
    · rw [← hι₁S, ← Category.assoc, hψ, Category.assoc, hact]
    · rw [← cancel_mono ι₁]
      simp only [j₁Q, Category.assoc]
      rw [hψ, ← Category.assoc j₁, hj₁ι, Category.assoc, ← hactj]
      simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3
      refine RingHom.ext fun y => ?_
      change ξ (Ideal.Quotient.mk _ (Algebra.TensorProduct.congr
        ((h.1⁻¹, h.2⁻¹) : G × (K' ≃ₐ[K] K')).2⁻¹
        (MulSemiringAction.toAlgAut G K B ((h.1⁻¹, h.2⁻¹) : G × (K' ≃ₐ[K] K')).1⁻¹) y)) =
        γQ.σ (ξ (Ideal.Quotient.mk _ y))
      rw [hcongrG]
      change Ideal.Quotient.mk _ (κ (κ.symm ((Θt h).σ (κ y)))) =
        γQ.σ (Ideal.Quotient.mk _ (κ y))
      rw [AlgEquiv.apply_symm_apply, hγ]
  -- `K → K' → Q` is the structure map `K → R → Q`
  have hKQ : ∀ k : K, ξ (Ideal.Quotient.mk _ ((algebraMap K K' k) ⊗ₜ[K] (1 : B))) =
      algebraMap R Q (algebraMap K R k) := by
    intro k
    change Ideal.Quotient.mk _ (κ ((algebraMap K K' k) ⊗ₜ[K] (1 : B))) =
      Ideal.Quotient.mk _ (algebraMap R C (algebraMap K R k))
    congr 1
    rw [← IsScalarTower.algebraMap_apply K R C, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.comm_tmul, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  have hj₁Q : j₁Q ≫ c₁.toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap R Q).comp ((algebraMap K R).comp O.subtype))) := by
    simp only [j₁Q, ← hι₁S, Category.assoc]
    rw [← Category.assoc j₁, hj₁ι, Category.assoc, hjS]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun o => hKQ o
  haveI : IsIso (CommRingCat.ofHom ξr) :=
    (ConcreteCategory.isIso_iff_bijective (CommRingCat.ofHom ξr)).2 ξ.bijective
  haveI : IsSchemeTheoreticallyDominant j₁Q := inferInstanceAs (IsSchemeTheoreticallyDominant
    (Spec.map (CommRingCat.ofHom ξr) ≫ j₁))
  haveI : ConnectedSpace (specialFibre c₁.toSpec) := hconn
  have hdim₁ : topologicalKrullDim (specialFibre c₁.toSpec) ≤ 1 := by
    refine le_trans (Topology.IsInducing.topologicalKrullDim_le
      (f := specialFibreMap ι₁ hι₁S) ?_) hdim
    exact (Topology.IsInducing.subtypeVal.of_comp_iff).1
      (ι₁.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal)
  let f' : ∀ k, (P k).1.Lv.L.B →ₐ[R] Q := fun k =>
    (Ideal.Quotient.mkₐ R _).comp ((Algebra.TensorProduct.includeLeft : B →ₐ[R] C).comp (f k))
  exact dom_coreQ V hV A₁ P Q hQc hQg hsymQ s' c₁ j₁Q hj₁Q
    ⟨K', inferInstance, inferInstance, inferInstance, O', hO', inferInstance, ϖ', hϖ', c₁',
      e₁, hss₁, he₁⟩ hdim₁ hactQ f' (fun k => by
        rw [← hf k]
        ext y
        change liftPoint s'' hsε' (Ideal.Quotient.mk _ (f k y ⊗ₜ[K] 1)) = t₀ (f k y)
        rw [liftPoint_mk]
        change Algebra.TensorProduct.lift t₀ a _ (f k y ⊗ₜ[K] 1) = _
        rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]) (fun k => ι₁ ≫ dom ⟨k⟩)
    (fun k => by rw [Category.assoc, hdomS, hι₁S]) (fun k => by
      simp only [j₁Q, Category.assoc]
      rw [← Category.assoc j₁, hj₁ι, Category.assoc, hdomj]
      simp only [j₀, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 3)

end Mid

end

end TemperedFundamentalGroups
