/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Tempered.Comparison

/-!
# Galois elements of the tempered fundamental group

An automorphism `σ` of the field `Ω` of the geometric point, fixing the image of `R` (so that it
permutes the geometric points `t : B →ₐ[R] Ω` of every finite étale cover) and preserving the
valuation ring `V`, acts on the fibre of every tempered covering: specialization is invariant
under `σ` (`sp_galois`), so `[(t, p)] ↦ [(σ ∘ t, p)]` is well defined and natural. This gives a
homomorphism from the decomposition group

`decompositionGroup R V = {σ ∈ Aut_R(Ω) | σ(V) = V}`

to the tempered fundamental group (`galoisToTempered`), compatible with the Galois action on the
étale fundamental group (`temperedToEtale_galoisToTempered`).

For a `k`-rational geometric point this is the section of `π₁^temp(X) → G_k` over the
decomposition group attached to the point; for the generic geometric point it is the image of
the decomposition group of the function field. In particular the tempered fundamental group is
not trivial: `galoisToTempered σ` acts on geometric fibres by `t ↦ σ ∘ t`
(`galoisToTempered_app_mk`), which moves points of the fibre of any constant field extension on
which `σ` acts nontrivially.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- **The decomposition group**: `R`-algebra automorphisms of `Ω` preserving `V`. -/
def decompositionGroup : Subgroup (Ω ≃ₐ[R] Ω) where
  carrier := {σ | ∀ x, σ x ∈ V ↔ x ∈ V}
  one_mem' := fun _ => Iff.rfl
  mul_mem' := fun {σ τ} hσ hτ x => by
    rw [AlgEquiv.mul_apply, hσ, hτ]
  inv_mem' := fun {σ} hσ x => by
    rw [← hσ]
    change σ (σ.symm x) ∈ V ↔ x ∈ V
    rw [AlgEquiv.apply_symm_apply]

variable {R V}

lemma sp_congr' {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of O)) [UniversallyClosed f]
    [IsSeparated f] {x y : Spec (CommRingCat.of Ω) ⟶ X} (h : x = y)
    (hx : x ≫ f = Spec.map (CommRingCat.ofHom (valToField O)))
    (hy : y ≫ f = Spec.map (CommRingCat.ofHom (valToField O))) :
    sp f V hV x hx = sp f V hV y hy := by
  subst h; rfl

variable {O A}

/-- Specialization of geometric points of a level is invariant under the decomposition group. -/
lemma Level.sp_galois (Lv : Level O R A) (σ : Ω ≃ₐ[R] Ω) (hσ : σ ∈ decompositionGroup R V)
    (t : Lv.L.B →ₐ[R] Ω) :
    Lv.sp V hV ((σ : Ω →ₐ[R] Ω).comp t) = Lv.sp V hV t := by
  unfold Level.sp
  rw [← TemperedFundamentalGroups.sp_galois (σ.restrictScalars K) hσ (Lv.point t)]
  apply sp_congr'
  rw [Level.point, Level.point, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

namespace TempObj

/-- The action of an element of the decomposition group on pairs `(t, p)`. -/
def preGalois (X : TempObj O R A) (σ : Ω ≃ₐ[R] Ω) (hσ : σ ∈ decompositionGroup R V)
    (q : PreFibre Ω V hV X) : PreFibre Ω V hV X :=
  ⟨((σ : Ω →ₐ[R] Ω).comp q.1.1, q.1.2), by rw [q.2, Level.sp_galois hV X.Lv σ hσ]⟩

lemma preGalois_smul (X : TempObj O R A) (σ : Ω ≃ₐ[R] Ω) (hσ : σ ∈ decompositionGroup R V)
    (g : X.Lv.L.H0) (q : PreFibre Ω V hV X) :
    preGalois hV X σ hσ (g • q) = g • preGalois hV X σ hσ q := rfl

/-- The action of an element of the decomposition group on the fibre. -/
def galoisFibre (X : TempObj O R A) (σ : Ω ≃ₐ[R] Ω) (hσ : σ ∈ decompositionGroup R V) :
    Fibre Ω V hV X → Fibre Ω V hV X :=
  Quotient.map (preGalois hV X σ hσ) fun q q' ⟨g, hg⟩ => ⟨g, by rw [← hg]; rfl⟩

lemma galoisFibre_mul (X : TempObj O R A) (σ τ : Ω ≃ₐ[R] Ω) (hσ : σ ∈ decompositionGroup R V)
    (hτ : τ ∈ decompositionGroup R V) (x : Fibre Ω V hV X) :
    galoisFibre hV X (σ * τ) ((decompositionGroup R V).mul_mem hσ hτ) x =
      galoisFibre hV X σ hσ (galoisFibre hV X τ hτ x) := by
  induction x using Quotient.inductionOn
  rfl

lemma galoisFibre_one (X : TempObj O R A) (x : Fibre Ω V hV X) :
    galoisFibre hV X 1 (decompositionGroup R V).one_mem x = x := by
  induction x using Quotient.inductionOn
  rfl

end TempObj

variable (O R A) in
/-- **The decomposition group acts on the tempered fundamental group**: `σ` acts on the fibre of
every tempered covering by `[(t, p)] ↦ [(σ ∘ t, p)]`. -/
def galoisToTempered : decompositionGroup R V →* temperedPi1 O R A V hV where
  toFun σ := show _ ≅ _ from NatIso.ofComponents
    (fun X => (show TempObj.Fibre Ω V hV X ≃ TempObj.Fibre Ω V hV X from
      { toFun := TempObj.galoisFibre hV X σ σ.2
        invFun := TempObj.galoisFibre hV X σ⁻¹ (σ⁻¹).2
        left_inv := fun x => by
          rw [← TempObj.galoisFibre_mul]
          convert TempObj.galoisFibre_one hV X x using 2
          simp
        right_inv := fun x => by
          rw [← TempObj.galoisFibre_mul]
          convert TempObj.galoisFibre_one hV X x using 2
          simp }).toIso)
    (fun {X Y} m => by
      ext x
      induction x using Quotient.inductionOn
      rfl)
  map_one' := by
    apply FibreAut.ext
    intro X x
    exact TempObj.galoisFibre_one hV X x
  map_mul' σ τ := by
    apply FibreAut.ext
    intro X x
    exact TempObj.galoisFibre_mul hV X σ τ σ.2 τ.2 x

lemma galoisToTempered_app_mk (σ : decompositionGroup R V) (X : TempObj O R A)
    (q : TempObj.PreFibre Ω V hV X) :
    (galoisToTempered O R A hV σ).app X (Quotient.mk _ q) =
      Quotient.mk _ (TempObj.preGalois hV X σ σ.2 q) := rfl

variable (R A Ω) in
/-- The Galois action on the étale fundamental group: `σ` acts on geometric fibres of finite
étale covers by `t ↦ σ ∘ t`. -/
def galoisToEtale : (Ω ≃ₐ[R] Ω) →* etalePi1 R A Ω where
  toFun σ := show _ ≅ _ from NatIso.ofComponents
    (fun X => (show (X.B →ₐ[R] Ω) ≃ (X.B →ₐ[R] Ω) from
      { toFun := fun t => (σ : Ω →ₐ[R] Ω).comp t
        invFun := fun t => (σ.symm : Ω →ₐ[R] Ω).comp t
        left_inv := fun t => by ext; simp
        right_inv := fun t => by ext; simp }).toIso)
    (fun {X Y} m => rfl)
  map_one' := rfl
  map_mul' _ _ := rfl

variable [SMulCommClass A K R]

/-- **Compatibility with the étale fundamental group**: the comparison homomorphism sends the
Galois element `σ` of the tempered fundamental group to the Galois element of the étale
fundamental group. -/
theorem temperedToEtale_galoisToTempered (σ : decompositionGroup R V) :
    temperedToEtale O R A V hV (galoisToTempered O R A hV σ) = galoisToEtale R A Ω σ := by
  apply FibreAut.ext
  intro X t
  rfl

end

end TemperedFundamentalGroups

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] {O : ValuationSubring K}
  {R : Type u} [CommRing R] [Algebra K R] {A : Type u} [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  {V : ValuationSubring Ω} (hV : V.comap (algebraMap K Ω) = O)

/-- **Non-degeneracy**: the image of the tempered fundamental group in the étale fundamental group
contains the Galois action of the decomposition group. -/
lemma galoisToEtale_mem_range_temperedToEtale (σ : decompositionGroup R V) :
    galoisToEtale R A Ω σ ∈ (temperedToEtale O R A V hV).range :=
  ⟨galoisToTempered O R A hV σ, temperedToEtale_galoisToTempered hV σ⟩

/-- An element of the decomposition group moving a geometric point of some finite étale cover
gives a nontrivial element of the tempered fundamental group. -/
lemma galoisToTempered_ne_one (σ : decompositionGroup R V) (X : EquivEtale R A)
    (t : X.B →ₐ[R] Ω) (ht : (σ : Ω →ₐ[R] Ω).comp t ≠ t) :
    galoisToTempered O R A hV σ ≠ 1 := by
  intro h
  apply ht
  have := congrArg (fun τ => (temperedToEtale O R A V hV τ).app X t) h
  simp only [map_one, FibreAut.one_app, temperedToEtale_galoisToTempered] at this
  exact this

end

end TemperedFundamentalGroups
