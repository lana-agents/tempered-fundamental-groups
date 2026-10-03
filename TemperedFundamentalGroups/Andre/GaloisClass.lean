/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Andre.GaloisObject
import TemperedFundamentalGroups.Andre.Defs
import TemperedFundamentalGroups.FibreFunctor.GaloisLimit

/-!
# The class of Galois objects for K1 (scheme case)

Blueprint §10.3.3, K1/K3. In the scheme case (`[Subsingleton A]`), `galClass` is the class of
tempered coverings isomorphic to a Galois object `U_Lv = universalObj Lv hdim z₀`
(`Andre/GaloisObject.lean`) over a level with a model `Lv` which is

* **Galois**: `H⁰` acts simply transitively on the (nonempty) geometric fibre `F_L`;
* **connected**: `B` has no idempotents other than `0` and `1`;
* **semistable** (`IsSemistableLevel`) with scheme-theoretically dominant `j`;
* with special fibre `Z` satisfying the hypotheses of N1 and connected.

Results:

* `algHom_eq_of_comp_eq`: maps from a finite étale `R`-algebra into a connected `R`-algebra are
  determined by one geometric point (via the diagonal idempotent of an unramified algebra).
* `isGaloisClass_galClass` (**gal**) from `existsUnique_deck`;
* `isRigid_galClass` (**rig**) from `fibreMap_eq_of_eq`;
* `GaloisLimit.isDominating_of_forall_exists` (formal): for a Galois class, domination follows
  from domination of each `(X_k, x_k)` separately by a common `G` (base points are aligned by
  automorphisms).
* `comp_eq_fibreAct_of_hom` (**the obstruction to dom**): a morphism `m : G ⟶ X` out of an
  object over a level on whose geometric fibre `H⁰` acts transitively maps all geometric points
  of `G` into a single `H_X⁰`-orbit. Hence a covering over a connected level `(B, H)` on whose
  fibre `H⁰` does not act transitively (e.g. `H = 1`, `B` a domain of degree `≥ 2` over `R`)
  receives no morphism from a member of `galClass` hitting points over different orbits; and
  since `F_{B'} → F_B` is surjective for finite étale `B → B'` with `B` connected, it receives
  no morphism from `galClass` at all. So `galClass` does not dominate the whole category
  `TempObj` (Blueprint §10.3.1, B2: only spans reach such objects).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

section Rigid

variable {R : Type u} [CommRing R] {S B : Type u} [CommRing S] [Algebra R S] [CommRing B]
  [Algebra R B]

open TensorProduct in
lemma mul_eq_lmul'_tmul_one_mul {t : S ⊗[R] S}
    (ht : ∀ s, ((1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) * t = 0) (z : S ⊗[R] S) :
    z * t = (Algebra.TensorProduct.lmul' R z ⊗ₜ[R] (1 : S)) * t := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => rw [add_mul, hy, hz, map_add, add_tmul, add_mul]
  | tmul x y =>
    have h₁ : (x ⊗ₜ[R] y : S ⊗[R] S) = (x ⊗ₜ[R] (1 : S)) * ((1 : S) ⊗ₜ[R] y) := by simp
    have h₂ : ((1 : S) ⊗ₜ[R] y) * t = (y ⊗ₜ[R] (1 : S)) * t := by
      rw [← sub_eq_zero, ← sub_mul, ht]
    conv_lhs => rw [h₁, mul_assoc, h₂, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [Algebra.TensorProduct.lmul'_apply_tmul]

/-- **Maps into a connected algebra are determined by one geometric point**: if `S` is unramified
of finite type over `R` and `B` has no idempotents other than `0, 1`, two `R`-algebra maps
`S → B` which agree after composing with one `t : B → Ω` are equal. -/
theorem algHom_eq_of_comp_eq [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S]
    (hB : ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1) {Ω : Type u} [CommRing Ω] [Nontrivial Ω]
    [Algebra R Ω] (a a' : S →ₐ[R] B) (t : B →ₐ[R] Ω) (h : t.comp a = t.comp a') : a = a' := by
  obtain ⟨τ, hτ, hτ₁⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := R)
    (S := S)).1 inferInstance
  let φ : TensorProduct R S S →ₐ[R] B := Algebra.TensorProduct.lift a a' fun _ _ => .all _ _
  have hidem : IsIdempotentElem τ := by
    change τ * τ = τ
    rw [mul_eq_lmul'_tmul_one_mul hτ, hτ₁, ← Algebra.TensorProduct.one_def, one_mul]
  have hφ : t (φ τ) = 1 := by
    have h' : ∀ x, t (a x) = t (a' x) := fun x => congr($h x)
    have : (t.comp φ) = (t.comp a).comp (Algebra.TensorProduct.lmul' R) := by
      ext x
      · simp [φ]
      · simp [φ, h']
    have h₂ := congr($this τ)
    simp only [AlgHom.comp_apply] at h₂
    rw [h₂, hτ₁, map_one, map_one]
  have h₁ : φ τ = 1 := by
    rcases hB _ (hidem.map φ) with h₀ | h₁
    · rw [h₀, map_zero] at hφ
      exact absurd hφ zero_ne_one
    · exact h₁
  ext x
  have := congr(φ $(hτ x))
  rw [map_mul, h₁, mul_one, map_zero, map_sub] at this
  simp only [φ, Algebra.TensorProduct.lift_tmul, map_one, one_mul, mul_one, sub_eq_zero] at this
  exact this.symm

end Rigid

namespace GaloisLimit

variable {C : Type*} [Category C] {Φ : C ⥤ Type*} {𝒢 : ObjectProperty C}

/-- **Aligning base points by automorphisms**: for a Galois class, it suffices to dominate every
finite family of pointed objects by one object `G ∈ 𝒢` with a nonempty fibre, each `x_k` being
hit at some point of `Φ G` depending on `k`. -/
theorem isDominating_of_forall_exists (hgal : IsGaloisClass Φ 𝒢)
    (h : ∀ (n : ℕ) (P : Fin n → Σ X : C, Φ.obj X), ∃ G, 𝒢 G ∧ Nonempty (Φ.obj G) ∧
      ∀ k, ∃ (f : G ⟶ (P k).1) (u : Φ.obj G), Φ.map f u = (P k).2) :
    IsDominating Φ 𝒢 := by
  intro n P
  obtain ⟨G, hG, ⟨g⟩, hP⟩ := h n P
  choose f u hfu using hP
  choose σ hσ using fun k => hgal G hG g (u k)
  refine ⟨G, hG, g, fun k => (σ k).hom ≫ f k, fun k => ?_⟩
  rw [Functor.map_comp_apply, hσ, hfu]

end GaloisLimit

open TempObj GaloisObject GaloisLimit

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

lemma tempFibre_map_apply {X Y : TempObj O R A} (m : X ⟶ Y) (x : Fibre Ω V hV X) :
    (tempFibre O R A V hV).map m x = fibreMap V hV m x := rfl

variable (O R A Ω) in
/-- **The class of Galois objects** (scheme case): tempered coverings isomorphic to
`U_Lv = universalObj Lv hdim z₀` for a Galois, connected, semistable level `Lv` with
scheme-theoretically dominant `j` whose special fibre satisfies the hypotheses of N1 and is
connected. -/
def galClass : ObjectProperty (TempObj O R A) := fun X =>
  ∃ (Lv : Level O R A) (_ : Finite Lv.L.H) (_ : TopologicalSpace.NoetherianSpace Lv.Z)
    (_ : T0Space Lv.Z) (_ : QuasiSober Lv.Z) (_ : ConnectedSpace Lv.Z)
    (hdim : topologicalKrullDim Lv.Z ≤ 1) (z₀ : Lv.Z),
    Nonempty (Lv.L.B →ₐ[R] Ω) ∧
    (∀ t t' : Lv.L.B →ₐ[R] Ω, ∃! k : Lv.L.H0, FiniteLevel.fibreAct Ω Lv.L k t = t') ∧
    (∀ e : Lv.L.B, IsIdempotentElem e → e = 0 ∨ e = 1) ∧
    IsSemistableLevel Lv ∧ IsSchemeTheoreticallyDominant Lv.j ∧
    Nonempty (X ≅ universalObj Lv hdim z₀)

/-- **(gal)** Automorphisms of a member of `galClass` act transitively on its fibre. -/
theorem isGaloisClass_galClass [Subsingleton A] :
    IsGaloisClass (tempFibre O R A V hV) (galClass O R A Ω) := by
  rintro X ⟨Lv, _, _, _, _, _, hdim, z₀, -, hgal, -, -, -, ⟨e⟩⟩ x y
  obtain ⟨π, hπ, -⟩ := existsUnique_deck V hV hgal (fibreMap V hV e.hom x) (fibreMap V hV e.hom y)
  refine ⟨e ≪≫ deck _ _ π ≪≫ e.symm, ?_⟩
  rw [Iso.trans_hom, Iso.trans_hom, Functor.map_comp_apply, Functor.map_comp_apply, Iso.symm_hom]
  simp only [tempFibre_map_apply, deck_hom]
  exact (congrArg (fibreMap V hV e.inv) hπ).trans
    (Iso.hom_inv_id_apply ((tempFibre O R A V hV).mapIso e) y)

/-- **(rig)** Two morphisms out of a member of `galClass` which agree at one fibre element induce
the same map of fibres. -/
theorem isRigid_galClass [Subsingleton A] :
    IsRigid (tempFibre O R A V hV) (galClass O R A Ω) := by
  rintro X ⟨Lv, _, _, _, _, _, hdim, z₀, -, -, hidem, -, hdom, ⟨e⟩⟩ Y f f' g hg
  haveI := hdom
  haveI := Lv.L.etale
  haveI := Lv.L.finite
  have hconn : ∀ (L' : FiniteLevel R A) (a a' : L'.B →ₐ[R] Lv.L.B) (t : Lv.L.B →ₐ[R] Ω),
      t.comp a = t.comp a' → a = a' := fun L' a a' t h => by
    haveI := L'.etale
    haveI := L'.finite
    exact algHom_eq_of_comp_eq hidem a a' t h
  have key := fibreMap_eq_of_eq V hV hconn (e.inv ≫ f) (e.inv ≫ f') (fibreMap V hV e.hom g)
    (by
      simp only [← tempFibre_map_apply, ← Functor.map_comp_apply, Iso.hom_inv_id_assoc]
      exact hg)
  have h₁ : (tempFibre O R A V hV).map (e.inv ≫ f) = (tempFibre O R A V hV).map (e.inv ≫ f') :=
    congrArg TypeCat.ofHom key
  rw [← e.hom_inv_id_assoc f, ← e.hom_inv_id_assoc f', Functor.map_comp _ e.hom (e.inv ≫ f),
    Functor.map_comp _ e.hom (e.inv ≫ f'), h₁]

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- **The obstruction to domination of all of `TempObj`**: a morphism `m : X ⟶ Y` out of an
object over a level on whose geometric fibre `H⁰` acts transitively maps all geometric points of
`X` into a single `H_Y⁰`-orbit of geometric points of `Y`. -/
theorem comp_eq_fibreAct_of_hom {X Y : TempObj O R A} (m : X ⟶ Y)
    (htr : ∀ t t' : X.Lv.L.B →ₐ[R] Ω, ∃ k : X.Lv.L.H0, FiniteLevel.fibreAct Ω X.Lv.L k t = t')
    (t t' : X.Lv.L.B →ₐ[R] Ω) :
    ∃ k : Y.Lv.L.H0, t'.comp m.φ.f = FiniteLevel.fibreAct Ω Y.Lv.L k (t.comp m.φ.f) := by
  obtain ⟨k, rfl⟩ := htr t t'
  exact ⟨_, FiniteLevel.fibreAct_comp Ω m.φ k t⟩

omit [Algebra K Ω] [IsScalarTower K R Ω] in
/-- In particular, if `H_Y⁰` is trivial (e.g. `Y` over a level `(B, 1)`), a morphism into `Y` out
of an object over a level on whose fibre `H⁰` acts transitively (such as the level of a member of
`galClass`) sends all geometric points to the same geometric point of `Y`. -/
theorem comp_eq_of_subsingleton {X Y : TempObj O R A} (m : X ⟶ Y)
    (htr : ∀ t t' : X.Lv.L.B →ₐ[R] Ω, ∃ k : X.Lv.L.H0, FiniteLevel.fibreAct Ω X.Lv.L k t = t')
    [Subsingleton Y.Lv.L.H0] (t t' : X.Lv.L.B →ₐ[R] Ω) : t'.comp m.φ.f = t.comp m.φ.f := by
  obtain ⟨k, hk⟩ := comp_eq_fibreAct_of_hom m htr t t'
  rw [hk, Subsingleton.elim k 1, FiniteLevel.fibreAct_one]

end

end TemperedFundamentalGroups
