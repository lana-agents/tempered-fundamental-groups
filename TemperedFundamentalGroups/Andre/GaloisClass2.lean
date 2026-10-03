/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.GaloisClass

/-!
# Galois objects over levels with trivial `H` (Blueprint §10.3.5)

Scheme case (`[Subsingleton A]`). `galClass₂` is the class of tempered coverings isomorphic to
`U = universalObj Lv hdim z₀` (the universal covering `Z̃` of the special fibre, over the level
`Lv`) where

* the group `H` of the level is trivial (`Subsingleton Lv.L.H`);
* `B = Lv.L.B` has no idempotents other than `0, 1`, and `Aut_R(B)` acts simply transitively on
  the (nonempty) geometric fibre `B →ₐ[R] Ω`;
* every `σ ∈ Aut_R(B)` extends to the model over `O` compatibly with `j` (by dominance of `j` the
  extensions are unique, so this is an action of `Aut_R(B)` on the model making `j` equivariant);
* `j` is scheme-theoretically dominant, the level is semistable, and the special fibre satisfies
  the hypotheses of N1 and is connected.

Results:

* `hom_eq_of_preMap_eq` (**rigidity on the nose**): two morphisms out of `U` which agree on one
  pair `(t, x)` are equal: their `f`'s agree by `algHom_eq_of_comp_eq`, their model maps by
  dominance, their covering maps by uniqueness of lifts.
* `exists_hom_preMap`: lifting a level morphism `ℓ : Lv ⟶ X.Lv` to a morphism `U ⟶ X` through
  prescribed points.
* `isGaloisClass_galClass₂` (**gal**): the automorphisms (level automorphisms `σ`, the model
  action of `σ`, a lift to `Z̃`) act transitively on `Φ U` (simply transitively, by rigidity).
* `isRigid_galClass₂` (**rig**).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

open TempObj GaloisObject GaloisLimit

section LevelHomOfAlgHom

variable {R : Type u} [CommRing R] {A : Type u} [Group A] [MulSemiringAction A R]

/-- A morphism of levels `L ⟶ L'` out of a level with trivial `H` is just an `R`-algebra map
`L'.B → L.B` (the group homomorphism is trivial, equivariance is vacuous). -/
def FiniteLevel.homOfSubsingleton (L L' : FiniteLevel R A) [Subsingleton L.H]
    (f : L'.B →ₐ[R] L.B) : L ⟶ L' where
  f := f
  r := 1
  r_a g := by rw [Subsingleton.elim g 1]; rfl
  f_σ g y := by rw [Subsingleton.elim g 1]; rfl

@[simp] lemma FiniteLevel.homOfSubsingleton_f (L L' : FiniteLevel R A) [Subsingleton L.H]
    (f : L'.B →ₐ[R] L.B) : (FiniteLevel.homOfSubsingleton L L' f).f = f := rfl

end LevelHomOfAlgHom

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

section Lift

variable {Lv : Level O R A} [Finite Lv.L.H] {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}

/-- **Lifting through prescribed points**: a pair `q₀ = (t, (1, e₀))` of `U_Lv` and a pair `q` of
`X` over the image of `t` along an equivariant `ℓ : Lv ⟶ X.Lv`: there is a morphism `U_Lv ⟶ X`
over `ℓ` mapping `q₀` to `q`. -/
theorem exists_hom_preMap {X : TempObj O R A} (ℓ : LevelHom O R A Lv X.Lv)
    (hℓ : ℓ.IsEquivariant) (q₀ : PreFibre Ω V hV (obj Lv hp hc)) (e₀ : E)
    (hq₀ : q₀.1.2 = Θ Lv hp hc ⟨1, e₀⟩) (q : PreFibre Ω V hV X)
    (ht : q₀.1.1.comp ℓ.φ.f = q.1.1) :
    ∃ f : obj Lv hp hc ⟶ X, LevelHom.ofTempHom f = ℓ ∧ preMap V hV f q₀ = q := by
  have he₀ := proj_eq_sp V hV q₀ hq₀
  have hy : q.1.2.1.1 = (ℓ.ψs ∘ p) e₀ := by
    apply Subtype.ext
    rw [q.2, Function.comp_apply, LevelHom.coe_ψs, he₀, LevelHom.ψ_sp V hV ℓ]
    exact congrArg (fun t => (X.Lv.sp V hV t : X.Lv.c.scheme)) ht.symm
  obtain ⟨s, hs, hps, hse⟩ := hp.exists_lift X.Lv.Z X.P.carrier (fun x => x.1.1)
    X.P.isCoveringMap (ℓ.ψs ∘ p) (ℓ.continuous_ψs.comp hp.isCoveringMap.continuous) e₀ q.1.2 hy
  have hps' : ∀ e, (s e).1.1 = ℓ.ψs (p e) := congrFun hps
  refine ⟨liftHom hp hc ℓ hℓ hs hps', ofTempHom_liftHom ℓ hℓ hs hps', ?_⟩
  refine Subtype.ext (Prod.ext ht ?_)
  change (liftHom hp hc ℓ hℓ hs hps').h q₀.1.2 = q.1.2
  rw [hq₀, liftHom_h_one ℓ hℓ hs hps', hse]

/-- **Rigidity on the nose**: if `H` is trivial, `B` is connected and `j` is
scheme-theoretically dominant, two morphisms out of `U_Lv` which agree on one pair `(t, x)` are
equal. -/
theorem hom_eq_of_preMap_eq [Subsingleton Lv.L.H] [IsSchemeTheoreticallyDominant Lv.j]
    (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1) {X : TempObj O R A}
    (f f' : obj Lv hp hc ⟶ X) (q : PreFibre Ω V hV (obj Lv hp hc))
    (h : preMap V hV f q = preMap V hV f' q) : f = f' := by
  haveI := X.Lv.L.etale
  haveI := X.Lv.L.finite
  haveI : Subsingleton (obj Lv hp hc).Lv.L.H := ‹Subsingleton Lv.L.H›
  have hf : f.φ.f = f'.φ.f :=
    algHom_eq_of_comp_eq hidem _ _ q.1.1 (congrArg (fun q => q.1.1) h)
  have hφ : f.φ = f'.φ := by
    refine FiniteLevel.Hom.ext hf (MonoidHom.ext fun g => ?_)
    rw [Subsingleton.elim g 1, map_one, map_one]
  have hj : IsSchemeTheoreticallyDominant (obj Lv hp hc).Lv.j :=
    ‹IsSchemeTheoreticallyDominant Lv.j›
  have hψ : f.ψ = f'.ψ := by
    refine ext_of_isSchemeTheoreticallyDominant_of_isSeparated X.Lv.c.toSpec
      (by rw [f.ψ_toSpec, f'.ψ_toSpec]) (obj Lv hp hc).Lv.j ?_
    rw [f.j_ψ, f'.j_ψ, hf]
  exact hom_ext hφ hψ q.1.2 (congrArg (fun q => q.1.2) h)

lemma preMap_comp {X Y Z : TempObj O R A} (m : X ⟶ Y) (n : Y ⟶ Z) (q : PreFibre Ω V hV X) :
    preMap V hV (m ≫ n) q = preMap V hV n (preMap V hV m q) := rfl

lemma preMap_id (X : TempObj O R A) (q : PreFibre Ω V hV X) : preMap V hV (𝟙 X) q = q := rfl

lemma fibreMap_comp {X Y Z : TempObj O R A} (m : X ⟶ Y) (n : Y ⟶ Z) :
    fibreMap V hV (m ≫ n) = fibreMap V hV n ∘ fibreMap V hV m := by
  funext x
  induction x using Quotient.inductionOn
  rfl

end Lift

/-- The `R`-algebra automorphism `σ` of `B`, as a level automorphism of a level with trivial
`H`. -/
def Level.autHom (Lv : Level O R A) [Subsingleton Lv.L.H] (σ : Lv.L.B ≃ₐ[R] Lv.L.B)
    (ψ : Lv.c.scheme ⟶ Lv.c.scheme) (hψ : ψ ≫ Lv.c.toSpec = Lv.c.toSpec)
    (hj : Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j) :
    LevelHom O R A Lv Lv where
  φ := FiniteLevel.homOfSubsingleton Lv.L Lv.L σ
  ψ := ψ
  ψ_toSpec := hψ
  j_ψ := hj

variable (O R A Ω) in
/-- **The class of Galois objects over levels with trivial `H`** (scheme case; Blueprint
§10.3.5). -/
def galClass₂ : ObjectProperty (TempObj O R A) := fun X =>
  ∃ (Lv : Level O R A) (_ : Subsingleton Lv.L.H) (_ : TopologicalSpace.NoetherianSpace Lv.Z)
    (_ : T0Space Lv.Z) (_ : QuasiSober Lv.Z) (_ : ConnectedSpace Lv.Z)
    (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z),
    Nonempty (Lv.L.B →ₐ[R] Ω) ∧
    (∀ t t' : Lv.L.B →ₐ[R] Ω, ∃! σ : Lv.L.B ≃ₐ[R] Lv.L.B,
      t.comp (σ : Lv.L.B →ₐ[R] Lv.L.B) = t') ∧
    (∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
    (∀ σ : Lv.L.B ≃ₐ[R] Lv.L.B, ∃ ψ : Lv.c.scheme ⟶ Lv.c.scheme,
      ψ ≫ Lv.c.toSpec = Lv.c.toSpec ∧
      Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j) ∧
    IsSemistableLevel Lv ∧ IsSchemeTheoreticallyDominant Lv.j ∧
    Nonempty (X ≅ universalObj Lv hdim z₀)

section Gal

variable {Lv : Level O R A} [Subsingleton Lv.L.H] [IsSchemeTheoreticallyDominant Lv.j]
  {E : Type u} [TopologicalSpace E] {p : E → Lv.Z}
  {hp : IsUniversalCovering.{u, u, u, u} p} {hc : ∀ z, (p ⁻¹' {z}).Countable}

/-- A morphism `U_Lv ⟶ U_Lv` mapping one pair `(t₁, (1, e₁))` to another `(t₂, (1, e₂))`. -/
lemma exists_endo [Subsingleton A]
    (hgal : ∀ t t' : Lv.L.B →ₐ[R] Ω, ∃ σ : Lv.L.B ≃ₐ[R] Lv.L.B,
      t.comp (σ : Lv.L.B →ₐ[R] Lv.L.B) = t')
    (hact : ∀ σ : Lv.L.B ≃ₐ[R] Lv.L.B, ∃ ψ : Lv.c.scheme ⟶ Lv.c.scheme,
      ψ ≫ Lv.c.toSpec = Lv.c.toSpec ∧
      Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j)
    (q₁ q₂ : PreFibre Ω V hV (obj Lv hp hc)) (e₁ : E) (hq₁ : q₁.1.2 = Θ Lv hp hc ⟨1, e₁⟩) :
    ∃ m : obj Lv hp hc ⟶ obj Lv hp hc, preMap V hV m q₁ = q₂ := by
  obtain ⟨σ, hσ⟩ := hgal q₁.1.1 q₂.1.1
  obtain ⟨ψ, hψ, hj⟩ := hact σ
  let ℓ := Lv.autHom σ ψ hψ hj
  obtain ⟨m, -, hm⟩ := exists_hom_preMap V hV (X := obj Lv hp hc) ℓ
    (LevelHom.isEquivariant_of_isSchemeTheoreticallyDominant ℓ) q₁ e₁ hq₁ q₂ hσ
  exact ⟨m, hm⟩

/-- **`U_Lv` is Galois**: `Aut U_Lv` acts transitively on `Φ U_Lv`. -/
theorem exists_iso_fibreMap [Subsingleton A]
    (hgal : ∀ t t' : Lv.L.B →ₐ[R] Ω, ∃ σ : Lv.L.B ≃ₐ[R] Lv.L.B,
      t.comp (σ : Lv.L.B →ₐ[R] Lv.L.B) = t')
    (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hact : ∀ σ : Lv.L.B ≃ₐ[R] Lv.L.B, ∃ ψ : Lv.c.scheme ⟶ Lv.c.scheme,
      ψ ≫ Lv.c.toSpec = Lv.c.toSpec ∧
      Lv.j ≫ ψ = Spec.map (CommRingCat.ofHom (σ : Lv.L.B →+* Lv.L.B)) ≫ Lv.j)
    (u v : Fibre Ω V hV (obj Lv hp hc)) :
    ∃ σ : obj Lv hp hc ≅ obj Lv hp hc, fibreMap V hV σ.hom u = v := by
  obtain ⟨q₁, e₁, hq₁, rfl⟩ := exists_rep V hV u
  obtain ⟨q₂, e₂, hq₂, rfl⟩ := exists_rep V hV v
  obtain ⟨m, hm⟩ := exists_endo V hV hgal hact q₁ q₂ e₁ hq₁
  obtain ⟨m', hm'⟩ := exists_endo V hV hgal hact q₂ q₁ e₂ hq₂
  have h₁ : m ≫ m' = 𝟙 _ := hom_eq_of_preMap_eq V hV hidem _ _ q₁
    (by rw [preMap_comp, hm, hm', preMap_id])
  have h₂ : m' ≫ m = 𝟙 _ := hom_eq_of_preMap_eq V hV hidem _ _ q₂
    (by rw [preMap_comp, hm', hm, preMap_id])
  exact ⟨⟨m, m', h₁, h₂⟩, congrArg (Quotient.mk _) hm⟩

/-- **Rigidity of `U_Lv` on fibres.** -/
theorem fibreMap_eq_of_eq' [Subsingleton A]
    (hidem : ∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1) {Y : TempObj O R A}
    (F F' : obj Lv hp hc ⟶ Y) (u : Fibre Ω V hV (obj Lv hp hc))
    (h : fibreMap V hV F u = fibreMap V hV F' u) : fibreMap V hV F = fibreMap V hV F' := by
  obtain ⟨q, -, -, rfl⟩ := exists_rep V hV u
  obtain ⟨k, hk⟩ := Quotient.exact h
  have hF : F = F' ≫ conjHom Y k :=
    hom_eq_of_preMap_eq V hV hidem _ _ q (by rw [preMap_comp]; exact hk.symm)
  rw [hF, fibreMap_comp, fibreMap_conjHom]
  rfl

end Gal

/-- **(gal)** Automorphisms of a member of `galClass₂` act transitively on its fibre. -/
theorem isGaloisClass_galClass₂ [Subsingleton A] :
    IsGaloisClass (tempFibre O R A V hV) (galClass₂ O R A Ω) := by
  rintro X ⟨Lv, _, _, _, _, _, hdim, z₀, -, hgal, hidem, hact, -, hdom, ⟨e⟩⟩ x y
  haveI := hdom
  obtain ⟨π, hπ⟩ := exists_iso_fibreMap V hV (fun t t' => (hgal t t').exists) hidem hact
    (fibreMap V hV e.hom x) (fibreMap V hV e.hom y)
  refine ⟨e ≪≫ π ≪≫ e.symm, ?_⟩
  rw [Iso.trans_hom, Iso.trans_hom, Functor.map_comp_apply, Functor.map_comp_apply, Iso.symm_hom]
  simp only [tempFibre_map_apply]
  exact (congrArg (fibreMap V hV e.inv) hπ).trans
    (Iso.hom_inv_id_apply ((tempFibre O R A V hV).mapIso e) y)

/-- **(rig)** Two morphisms out of a member of `galClass₂` which agree at one fibre element induce
the same map of fibres. -/
theorem isRigid_galClass₂ [Subsingleton A] :
    IsRigid (tempFibre O R A V hV) (galClass₂ O R A Ω) := by
  rintro X ⟨Lv, _, _, _, _, _, hdim, z₀, -, -, hidem, -, -, hdom, ⟨e⟩⟩ Y f f' g hg
  haveI := hdom
  have key := fibreMap_eq_of_eq' V hV hidem (e.inv ≫ f) (e.inv ≫ f') (fibreMap V hV e.hom g)
    (by
      simp only [← tempFibre_map_apply, ← Functor.map_comp_apply, Iso.hom_inv_id_assoc]
      exact hg)
  have h₁ : (tempFibre O R A V hV).map (e.inv ≫ f) = (tempFibre O R A V hV).map (e.inv ≫ f') :=
    congrArg TypeCat.ofHom key
  rw [← e.hom_inv_id_assoc f, ← e.hom_inv_id_assoc f', Functor.map_comp _ e.hom (e.inv ≫ f),
    Functor.map_comp _ e.hom (e.inv ≫ f'), h₁]

end

end TemperedFundamentalGroups
