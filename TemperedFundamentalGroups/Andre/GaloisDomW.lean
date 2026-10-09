/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.GaloisDom2
import TemperedFundamentalGroups.SemistableReduction.StrongComponentAS

/-!
# Galois objects over W-model levels (Blueprint §10.3.6, items 1–2)

Scheme case. B5 measures fibre elements of the Galois objects of `galClass₂` with lengths read
off on their models, which must be **unfolded W-models**
(`SemistableReduction.ModelCode.IsUnfolded`): the models produced by the W-chain, between which
maps are x-harmonic (`Statement.HarmonicX`). Here the
W-model structure is recorded **on the level** (`Level.IsW x`), tied to `j`:

* `Level.IsW x Lv`: the model of `Lv` is, over `O`, a split semistable `O'`-model `c'`
  without loops, which is an unfolded W-model on the x-line `x ∈ R` of a fraction field `L₁` of
  `B`, with generic point `Spec L₁ → Spec B → c → c'`; the `K'`-structure of `L₁` comes from a
  map `κ : K' → B` over `K`.
* `galClassW P`: the members of `galClass₂` whose level satisfies a predicate `P` on levels
  (`galClassW_le`: `galClassW P ≤ galClass₂ (fun _ => True)`, so gal and rig are inherited).
* `coreLevel`: the level with trivial `H` of the core of domination (`dom_core`), and
  `dom_coreW`, the core of domination for a predicate on levels.
* `dom_midW`, `isDominating_galClassW`, `galoisLimitDataW`: **(gal), (dom), (rig) for the Galois
  objects over W-model levels**, from `Statement.StrongComponentA` (whose component clause
  produces the W-model data), on the x-line `x = (exists_finite_aeval (K := K) hR).choose`.

A fixed member `(G₀, g₀)` of `galClassW` over the pointed Tate object `(X₀, x₀)` then serves as the
fixed base W-model `𝒴` of §10.3.6, item 1: the pointed members over `(G₀, g₀)` are cofinal, and by
rigidity each of them has a unique pointed morphism to `(G₀, g₀)`, whose model component is the
map to `𝒴`.
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- **W-model data on a level** (on the x-line `x ∈ R`): the model of `Lv` is, over `O`, a split
semistable `O'`-model `c'` without loops (`K'/K` finite, `O'` its valuation ring over `O`), which
is a W-model of a fraction field `L₁` of `B` on the image of `x`, with generic point
`Spec L₁ → Spec B → c ≅ c'`; the `K'`-structure of `L₁` comes from a map `κ : K' → B` extending
`K → B`. -/
def Level.IsW (x : R) (Lv : Level O R A) : Prop :=
  ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K')
    (O' : ValuationSubring K') (h : O'.comap (algebraMap K K') = O)
    (_ : IsDiscreteValuationRing O') (ϖ' : O') (_ : Irreducible ϖ')
    (c' : ModelCode O') (e : Lv.c.scheme ≅ c'.scheme),
    SemistableReduction.ModelCode.IsSemistable ϖ' c' ∧
    SemistableReduction.ModelCode.HasSplitNodes ϖ' c' ∧ SemistableReduction.ModelCode.NoLoops c' ∧
    e.hom ≫ c'.toSpec ≫ Spec.map (CommRingCat.ofHom
      ((algebraMap K K').restrict O O' (fun x hx => by rw [← h] at hx; exact hx))) =
      Lv.c.toSpec ∧
    ∃ (L₁ : Type u) (_ : Field L₁) (_ : Algebra Lv.L.B L₁) (_ : IsFractionRing Lv.L.B L₁)
      (_ : Algebra K' L₁) (_ : Algebra O' L₁) (_ : IsScalarTower O' K' L₁)
      (κ : K' →+* Lv.L.B) (j₁' : Spec (CommRingCat.of L₁) ⟶ c'.scheme),
      algebraMap K' L₁ = (algebraMap Lv.L.B L₁).comp κ ∧
      κ.comp (algebraMap K K') = (algebraMap R Lv.L.B).comp (algebraMap K R) ∧
      SemistableReduction.ModelCode.IsUnfolded O'
        (algebraMap Lv.L.B L₁ (algebraMap R Lv.L.B x)) c' j₁' ∧
      j₁' = Spec.map (CommRingCat.ofHom (algebraMap Lv.L.B L₁)) ≫ Lv.j ≫ e.hom

variable (O R A) in
/-- **The Galois objects over levels with trivial `H` satisfying a predicate `P` on levels**:
`galClass₂` with the model predicate replaced by a predicate on the whole level (needed to tie
W-model data to `j`). -/
def galClassW (Ω : Type u) [Field Ω] [Algebra R Ω] (P : Level O R A → Prop) :
    ObjectProperty (TempObj O R A) := fun X =>
  ∃ (Lv : Level O R A) (_ : Subsingleton Lv.L.H) (_ : TopologicalSpace.NoetherianSpace Lv.Z)
    (_ : T0Space Lv.Z) (_ : QuasiSober Lv.Z) (_ : ConnectedSpace Lv.Z)
    (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z),
    P Lv ∧ Nonempty (Lv.L.B →ₐ[R] Ω) ∧
    (∀ t t' : Lv.L.B →ₐ[R] Ω, ∃! σ : Lv.L.B ≃ₐ[R] Lv.L.B,
      t.comp (σ : Lv.L.B →ₐ[R] Lv.L.B) = t') ∧
    (∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
    (∀ σ : Lv.L.B ≃ₐ[R] Lv.L.B, ∃ ψ : Lv.c.scheme ⟶ Lv.c.scheme,
      ψ ≫ Lv.c.toSpec = Lv.c.toSpec ∧
      Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j) ∧
    IsSemistableLevel Lv ∧ IsSchemeTheoreticallyDominant Lv.j ∧
    Nonempty (X ≅ universalObj Lv hdim z₀)

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

omit [Algebra K Ω] [IsScalarTower K R Ω] in
lemma galClassW_le (P : Level O R A → Prop) {X : TempObj O R A} (hX : galClassW O R A Ω P X) :
    galClass₂ O R A Ω (fun _ => True) X := by
  obtain ⟨Lv, h₁, h₂, h₃, h₄, h₅, hdim, z₀, -, h₆⟩ := hX
  exact ⟨Lv, h₁, h₂, h₃, h₄, h₅, hdim, z₀, trivial, h₆⟩

/-- **(gal)** for `galClassW`. -/
theorem isGaloisClass_galClassW [Subsingleton A] (P : Level O R A → Prop) :
    IsGaloisClass (tempFibre O R A V hV) (galClassW O R A Ω P) :=
  fun X hX => isGaloisClass_galClass₂ V hV _ X (galClassW_le P hX)

/-- **(rig)** for `galClassW`. -/
theorem isRigid_galClassW [Subsingleton A] (P : Level O R A → Prop) :
    IsRigid (tempFibre O R A V hV) (galClassW O R A Ω P) :=
  fun X hX => isRigid_galClass₂ V hV _ X (galClassW_le P hX)

section Core

variable [IsDiscreteValuationRing O] [Subsingleton A]

/-- The identification of a finite étale `R`-algebra with the ring of its coded level. -/
abbrev coreEquiv (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q] [Module.Finite R Q] :
    Q ≃ₐ[R] (trivialHLevel (R := R) (A := A) Q).B :=
  (LevelData.codeEquiv R Q).symm

/-- **The level of the core of domination**: the coded level `(Q, 1)` with the model `c₁` and
`j = j₁ ∘ Spec (coreEquiv Q)`. -/
abbrev coreLevel (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q] [Module.Finite R Q]
    (c₁ : ModelCode O) (j₁ : Spec (CommRingCat.of Q) ⟶ c₁.scheme)
    (hj₁ : j₁ ≫ c₁.toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap R Q).comp ((algebraMap K R).comp O.subtype)))) : Level O R A where
  L := trivialHLevel Q
  c := c₁
  j := Spec.map (CommRingCat.ofHom ((coreEquiv (A := A) Q : Q ≃ₐ[R] _) : Q →+* _)) ≫ j₁
  j_toSpec := by
    rw [Category.assoc, hj₁, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext o
    exact (coreEquiv (A := A) Q).commutes _
  ρ := 1
  ρ_toSpec := fun g => by
    change 𝟙 _ ≫ _ = _
    exact Category.id_comp _
  ρ_j := fun g => by
    have hg : g = 1 := (subsingleton_trivialLevel (A := A) Q).elim g 1
    subst hg
    change Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ _ = _ ≫ 𝟙 _
    rw [Category.comp_id]
    exact (congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)

/-- **The core of domination for a predicate on levels** (`dom_core` with the model predicate
replaced by a predicate `P` on levels, satisfied by `coreLevel`). -/
theorem dom_coreW (P : Level O R A → Prop) {n : ℕ}
    (Pt : Fin n → Σ X : TempObj O R A, (tempFibre O R A V hV).obj X)
    (Q : Type u) [CommRing Q] [Algebra R Q] [Algebra.Etale R Q] [Module.Finite R Q]
    (hQc : ∀ e : Q, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hQg : ∀ t t' : Q →ₐ[R] Ω, ∃ σ : Q ≃ₐ[R] Q, t.comp (σ : Q →ₐ[R] Q) = t')
    (s' : Q →ₐ[R] Ω) (c₁ : ModelCode O) (j₁ : Spec (CommRingCat.of Q) ⟶ c₁.scheme)
    (hj₁ : j₁ ≫ c₁.toSpec = Spec.map (CommRingCat.ofHom
      ((algebraMap R Q).comp ((algebraMap K R).comp O.subtype))))
    (hP : P (coreLevel Q c₁ j₁ hj₁))
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
    (f : ∀ k, (Pt k).1.Lv.L.B →ₐ[R] Q)
    (hf : ∀ k, s'.comp (f k) = (Quotient.out (Pt k).2 : PreFibre Ω V hV (Pt k).1).1.1)
    (dom : ∀ k, c₁.scheme ⟶ (Pt k).1.Lv.c.scheme)
    (hdomS : ∀ k, dom k ≫ (Pt k).1.Lv.c.toSpec = c₁.toSpec)
    (hdomj : ∀ k, j₁ ≫ dom k = Spec.map (CommRingCat.ofHom (f k : (Pt k).1.Lv.L.B →+* Q)) ≫
      (Pt k).1.Lv.j) :
    ∃ G, galClassW O R A Ω P G ∧ Nonempty ((tempFibre O R A V hV).obj G) ∧
      ∀ k, ∃ (m : G ⟶ (Pt k).1) (u : (tempFibre O R A V hV).obj G),
        (tempFibre O R A V hV).map m u = (Pt k).2 := by
  let L : FiniteLevel R A := trivialHLevel Q
  haveI : Subsingleton L.H := subsingleton_trivialLevel Q
  let φQ : Q ≃ₐ[R] L.B := coreEquiv Q
  let Lv : Level O R A := coreLevel Q c₁ j₁ hj₁
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
  have hmem : galClassW O R A Ω P U := by
    refine ⟨Lv, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      hdim, z₀, hP, ⟨s'.comp (φQ.symm : L.B →ₐ[R] Q)⟩, fun t t' => ?_, hconn, fun σ => ?_,
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
  let t : L.B →ₐ[R] Ω := s'.comp (φQ.symm : L.B →ₐ[R] Q)
  haveI := hp.connectedSpace
  obtain ⟨e, he⟩ := hp.isCoveringMap.surjective_of_connectedSpace (Lv.sp V hV t)
  let q₀ : PreFibre Ω V hV (obj Lv hp hc) := prePt V hV t e he
  refine ⟨U, hmem, ⟨Quotient.mk _ q₀⟩, fun k => ?_⟩
  let X := (Pt k).1
  let ℓ : LevelHom O R A Lv X.Lv :=
    { φ := FiniteLevel.homOfSubsingleton L X.Lv.L ((φQ : Q →ₐ[R] L.B).comp (f k))
      ψ := dom k
      ψ_toSpec := hdomS k
      j_ψ := by
        change (Spec.map (CommRingCat.ofHom (φQ : Q →+* L.B)) ≫ j₁) ≫ dom k = _
        rw [Category.assoc, hdomj, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        rfl }
  have hq : q₀.1.1.comp ℓ.φ.f = (Quotient.out (Pt k).2 : PreFibre Ω V hV (Pt k).1).1.1 := by
    change t.comp ((φQ : Q →ₐ[R] L.B).comp (f k)) = _
    rw [← hf k]
    ext y
    simp [t]
  obtain ⟨m, -, hm⟩ := exists_hom_preMap V hV (hp := hp) (hc := hc) (X := (Pt k).1) ℓ
    (LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant ℓ) q₀ e rfl
    (Quotient.out (Pt k).2 : PreFibre Ω V hV (Pt k).1) hq
  refine ⟨m, Quotient.mk _ q₀, ?_⟩
  change Quotient.mk _ (preMap V hV m q₀) = (Pt k).2
  rw [hm]
  exact Quotient.out_eq _

end Core

section Mid

open Components

variable {K : Type u} [Field K] [CharZero K] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
  {R : Type u} [CommRing R] [Algebra K R] [Algebra.Smooth K R] [IsDomain R]
  {A : Type u} [Group A] [MulSemiringAction A R] [Subsingleton A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **Domination by Galois objects over W-model levels** (`dom_mid` with the W-model data of the
component clause of `StrongComponentA` recorded on the level): if a connected Galois finite étale
`B` with a point `t₀` receives maps `f_k` from the levels of finitely many pointed objects
`(X_k, x_k)`, then a member of `galClassW (Level.IsW x)` (`x` the x-line of
`exists_finite_aeval`) dominates every `(X_k, x_k)`. -/
theorem dom_midW (hW : SemistableReduction.Statement.StrongComponentAS.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1) {n : ℕ}
    (P : Fin n → Σ X : TempObj O R A, (tempFibre O R A V hV).obj X)
    (B : Type u) [CommRing B] [Algebra R B] [Algebra.Etale R B] [Module.Finite R B]
    (hBc : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hBg : ∀ t t' : B →ₐ[R] Ω, ∃ σ : B ≃ₐ[R] B, t.comp (σ : B →ₐ[R] B) = t')
    (t₀ : B →ₐ[R] Ω) (f : ∀ k, (P k).1.Lv.L.B →ₐ[R] B)
    (hf : ∀ k, t₀.comp (f k) = (Quotient.out (P k).2 : PreFibre Ω V hV (P k).1).1.1) :
    ∃ G, galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose) G ∧
      Nonempty ((tempFibre O R A V hV).obj G) ∧
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
  -- `G` acts trivially on `R`
  letI : MulSemiringAction G R := MulSemiringAction.compHom R (1 : G →* RingAut R)
  haveI : SMulCommClass G K R := ⟨fun _ _ _ => rfl⟩
  obtain ⟨K', _, _, _, _, O', hO', _, ϖ', hϖ', c', c, e, j, act, dom, hss, he, -, hjS,
    hact, hactj, hdomj, hdomS, hdim, hcomp⟩ :=
    hW K O p hp hpm R hR (exists_finite_aeval (K := K) hR).choose
      (exists_finite_aeval (K := K) hR).choose_spec B G (fun g r => (g : B ≃ₐ[R] B).commutes r)
      (fun _ => rfl) (ULift.{u} (Fin n)) c₀ j₀ hj₀
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
  -- the W-model data on the core level
  have hWlev : Level.IsW (exists_finite_aeval (K := K) hR).choose
      (coreLevel (A := A) Q c₁ j₁Q hj₁Q) := by
    let φQ : Q ≃ₐ[R] (trivialHLevel (R := R) (A := A) Q).B := coreEquiv Q
    let θ : (trivialHLevel (R := R) (A := A) Q).B ≃+* TensorProduct K K' B ⧸ Ideal.span {1 - ε} :=
      φQ.toRingEquiv.symm.trans ξ.symm
    letI : Algebra (trivialHLevel (R := R) (A := A) Q).B L₁ :=
      ((algebraMap _ L₁).comp (θ : _ →+* TensorProduct K K' B ⧸ Ideal.span {1 - ε})).toAlgebra
    have halg : ∀ y, algebraMap (trivialHLevel (R := R) (A := A) Q).B L₁ y =
        algebraMap (TensorProduct K K' B ⧸ Ideal.span {1 - ε}) L₁ (θ y) := fun _ => rfl
    haveI : IsFractionRing (trivialHLevel (R := R) (A := A) Q).B L₁ :=
      IsFractionRing.of_ringEquiv_left θ halg
    let κ' : K' →+* (trivialHLevel (R := R) (A := A) Q).B :=
      (θ.symm : _ →+* _).comp ((Ideal.Quotient.mk (Ideal.span {1 - ε})).comp
        Algebra.TensorProduct.includeLeftRingHom)
    refine ⟨K', inferInstance, inferInstance, inferInstance, O', hO', inferInstance, ϖ', hϖ',
      c₁', e₁, hss₁, hsplit₁, hloop₁, he₁, L₁, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, κ', j₁', ?_, ?_, ?_, ?_⟩
    · rw [hK'L₁]
      ext k
      simp [κ', halg]
    · ext k
      change φQ (ξ (Ideal.Quotient.mk _ ((algebraMap K K' k) ⊗ₜ[K] (1 : B)))) =
        algebraMap R _ (algebraMap K R k)
      rw [hKQ, AlgEquiv.commutes]
    · convert hWM using 2
      rw [halg]
      congr 1
      change ξ.symm (φQ.symm (algebraMap R _ _)) = _
      rw [AlgEquiv.commutes, RingEquiv.symm_apply_eq]
      change _ = Ideal.Quotient.mk _ (κ ((1 : K') ⊗ₜ[K] algebraMap R B _))
      rw [Algebra.TensorProduct.comm_tmul]
      rfl
    · have hcomp' : CommRingCat.ofHom (algebraMap (TensorProduct K K' B ⧸ Ideal.span {1 - ε}) L₁) =
          CommRingCat.ofHom ξr ≫ CommRingCat.ofHom (φQ : Q →+* _) ≫
            CommRingCat.ofHom (algebraMap (trivialHLevel (R := R) (A := A) Q).B L₁) := by
        refine CommRingCat.hom_ext (RingHom.ext fun y => ?_)
        change _ = algebraMap (trivialHLevel (R := R) (A := A) Q).B L₁ (φQ (ξ y))
        rw [halg]
        congr 1
        change y = ξ.symm (φQ.symm (φQ (ξ y)))
        rw [AlgEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]
      rw [hj₁', hcomp', Spec.map_comp, Spec.map_comp]
      simp only [Category.assoc]
      rfl
  exact dom_coreW V hV (Level.IsW (exists_finite_aeval (K := K) hR).choose) P Q hQc hQg s' c₁ j₁Q
    hj₁Q
    hWlev ⟨K', inferInstance, inferInstance, inferInstance, O', hO', inferInstance, ϖ', hϖ', c₁',
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

/-- **(dom)** The Galois objects over W-model levels dominate. -/
theorem isDominating_galClassW (hW : SemistableReduction.Statement.StrongComponentAS.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1) :
    IsDominating (tempFibre O R A V hV)
      (galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)) := by
  classical
  refine isDominating_of_forall_exists (isGaloisClass_galClassW V hV _) fun n P => ?_
  let q : ∀ k, PreFibre Ω V hV (P k).1 := fun k => Quotient.out (P k).2
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    haveI : Nonempty (R →ₐ[R] Ω) := ⟨Algebra.ofId R Ω⟩
    obtain ⟨B, _, _, _, _, t₀, -, hBc, hBg⟩ := exists_galoisClosure (R := R) (Ω := Ω) (B₀ := R)
    obtain ⟨G, hG, hne, -⟩ := dom_midW V hV hW p hp hpm hR P B hBc hBg t₀ (fun k => k.elim0)
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
    obtain ⟨G, hG, hne, hdom⟩ := dom_midW V hV hW p hp hpm hR P B hBc hBg t₀ f hf
    exact ⟨G, hG, hne, fun k => let ⟨m, u, h⟩ := hdom k; ⟨m, u, h⟩⟩

/-- **(gal), (dom), (rig)** for the Galois objects over W-model levels (scheme case), from W10
with components. -/
theorem galoisLimitDataW (hW : SemistableReduction.Statement.StrongComponentAS.{u})
    [PerfectField (IsLocalRing.ResidueField O)] (p : ℕ) (hp : p.Prime)
    (hpm : (p : O) ∈ IsLocalRing.maximalIdeal O) (hR : ringKrullDim R = 1) :
    IsGaloisClass (tempFibre O R A V hV)
        (galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)) ∧
      IsDominating (tempFibre O R A V hV)
        (galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)) ∧
      IsRigid (tempFibre O R A V hV)
        (galClassW O R A Ω (Level.IsW (exists_finite_aeval (K := K) hR).choose)) :=
  ⟨isGaloisClass_galClassW V hV _, isDominating_galClassW V hV hW p hp hpm hR,
    isRigid_galClassW V hV _⟩

end Mid

end

end TemperedFundamentalGroups
