/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Tempered.Category
import Pi1.Orbifold.Etale

/-!
# The comparison homomorphism from the tempered to the étale fundamental group

An `A`-equivariant finite étale `R`-algebra `B` (a finite étale cover of `[Spec R / A]`) is the
tempered covering attached to the level `(B, image of A)`, the *trivial* model `Spec O`
(`ModelCode.trivial`) and the trivial one-sheeted covering of its special fibre. This defines a
functor `etaleToTemp : EquivEtale R A ⥤ TempObj O R A` together with an isomorphism of fibre
functors `etaleToTemp ⋙ tempFibre ≅ etaleFibre`, and hence the continuous comparison homomorphism

`temperedToEtale : temperedPi1 →* etalePi1`

by restriction of automorphisms (`FibreAut.restrict`).
-/

universe u

open CategoryTheory AlgebraicGeometry Pi1.Orbifold

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]

/-- Semilinear automorphisms fix the image of `O`. -/
lemma levelStructureMap_σ (L : FiniteLevel R A) (g : SemilinearAut R A L.B) (x : O) :
    g.σ (levelStructureMap O R A L x) = levelStructureMap O R A L x := by
  simp [levelStructureMap, g.map_algebraMap]

omit [SMulCommClass A K R] in
lemma spec_levelStructureMap {L L' : FiniteLevel R A} (φ : L ⟶ L') :
    Spec.map (CommRingCat.ofHom (levelStructureMap O R A L)) =
      Spec.map (CommRingCat.ofHom (φ.f : L'.B →+* L.B)) ≫
        Spec.map (CommRingCat.ofHom (levelStructureMap O R A L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp [levelStructureMap]

/-- **The trivial model** over a level: `Spec O` (`ℙ⁰_O`) with the trivial action. -/
def trivialLevel (L : FiniteLevel R A) : Level O R A where
  L := L
  c := ModelCode.trivial O
  j := Spec.map (CommRingCat.ofHom (levelStructureMap O R A L)) ≫
    inv (ModelCode.trivial O).toSpec
  j_toSpec := by simp
  ρ := 1
  ρ_toSpec := fun _ => Category.id_comp _
  ρ_j := fun g => by
    rw [MonoidHom.one_apply]
    change _ = _ ≫ 𝟙 _
    rw [Category.comp_id, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext x
    exact levelStructureMap_σ O R A L (g : SemilinearAut R A L.B)⁻¹ x

variable {R A}

/-- The level `(B, image of A)` of an equivariant finite étale algebra. -/
abbrev _root_.Pi1.Orbifold.EquivEtale.level (X : EquivEtale R A) : FiniteLevel R A where
  toEtaleCode := X.toEtaleCode
  H := X.act.range
  surjective a := ⟨X.act a, ⟨a, rfl⟩, X.act_a a⟩

lemma _root_.Pi1.Orbifold.EquivEtale.eq_act_of_mem (X : EquivEtale R A) {g : SemilinearAut R A X.B}
    (hg : g ∈ X.act.range) : g = X.act g.a := by
  obtain ⟨a, rfl⟩ := hg
  rw [X.act_a]

/-- The homomorphism of the groups `H` induced by an equivariant map. -/
def _root_.Pi1.Orbifold.EquivEtale.levelR {X Y : EquivEtale R A} : X.level.H →* Y.level.H where
  toFun g := ⟨Y.act g.1.a, ⟨_, rfl⟩⟩
  map_one' := by ext1; simp only [OneMemClass.coe_one, SemilinearAut.one_a, map_one]
  map_mul' g h := by ext1; simp only [Subgroup.coe_mul, SemilinearAut.mul_a, map_mul]

/-- The morphism of levels induced by an equivariant map. -/
def _root_.Pi1.Orbifold.EquivEtale.levelMap {X Y : EquivEtale R A} (m : X ⟶ Y) :
    X.level ⟶ Y.level where
  f := m.f
  r := EquivEtale.levelR
  r_a g := Y.act_a _
  f_σ g y := by
    change m.f ((Y.act g.1.a).σ y) = _
    rw [m.f_act, ← X.eq_act_of_mem g.2]

lemma _root_.Pi1.Orbifold.EquivEtale.H0_eq_one (X : EquivEtale R A) (g : X.level.H0) : g = 1 := by
  have h1 := FiniteLevel.mem_H0.1 g.2
  have h2 := X.eq_act_of_mem (g : X.level.H).2
  rw [h1, map_one] at h2
  exact Subtype.ext (Subtype.ext h2)

variable (R A)

/-- **The functor from finite étale covers to tempered covers**: the level `(B, image of A)`
with the trivial model and the trivial one-sheeted covering. -/
def etaleToTemp : EquivEtale R A ⥤ TempObj O R A where
  obj X := ⟨trivialLevel O R A X.level, CoveringCode.trivial _ 1 1⟩
  map {X Y} m :=
    { φ := EquivEtale.levelMap m
      ψ := 𝟙 _
      ψ_toSpec := Category.id_comp _
      j_ψ := by
        change (Spec.map (CommRingCat.ofHom (levelStructureMap O R A X.level)) ≫
            inv (ModelCode.trivial O).toSpec) ≫ 𝟙 _ =
          Spec.map (CommRingCat.ofHom (m.f : Y.B →+* X.B)) ≫
            (Spec.map (CommRingCat.ofHom (levelStructureMap O R A Y.level)) ≫
              inv (ModelCode.trivial O).toSpec)
        rw [Category.comp_id, spec_levelStructureMap O R A (EquivEtale.levelMap m),
          Category.assoc]
        rfl
      h := fun x => x
      continuous_h := continuous_id
      fst_h := fun _ => rfl
      h_act := fun g x => by
        apply Subtype.ext
        rfl }
  map_id X := by
    refine TempObj.Hom.ext (FiniteLevel.Hom.ext rfl (MonoidHom.ext fun g => ?_)) rfl rfl
    exact Subtype.ext (X.eq_act_of_mem g.2).symm
  map_comp {X Y Z} m n := by
    refine TempObj.Hom.ext (FiniteLevel.Hom.ext rfl (MonoidHom.ext fun g => ?_)) ?_ rfl
    · exact Subtype.ext (congrArg Z.act (Y.act_a _).symm)
    · exact (Category.comp_id _).symm

variable {Ω : Type u} [Field Ω] [Algebra K Ω] [Algebra R Ω] [IsScalarTower K R Ω]
  (V : ValuationSubring Ω) (hV : V.comap (algebraMap K Ω) = O)

/-- The fibre of the tempered covering attached to a finite étale cover is its geometric
fibre. -/
def etaleToTempFibreEquiv (X : EquivEtale R A) :
    ((etaleToTemp O R A) ⋙ tempFibre O R A V hV).obj X ≃ (etaleFibre R A Ω).obj X where
  toFun := Quotient.lift (fun q => (q.1.1 : X.B →ₐ[R] Ω)) fun q q' ⟨g, hg⟩ => by
    obtain rfl : g = 1 := X.H0_eq_one g
    rw [← hg]
    rfl
  invFun t := Quotient.mk _
    ⟨((t : X.B →ₐ[R] Ω), ⟨(((etaleToTemp O R A).obj X).Lv.sp V hV t, 0), Set.mem_univ _,
      Nat.zero_lt_one⟩), rfl⟩
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h q =>
      change Quotient.mk _ _ = Quotient.mk _ q
      congr 1
      apply Subtype.ext
      refine Prod.ext rfl (Subtype.ext (Prod.ext (Subtype.ext q.2.symm) ?_))
      have := q.1.2.2.2
      simp only [Set.mem_setOf_eq, Nat.lt_one_iff] at this
      exact this.symm
  right_inv _ := rfl

/-- The fibre functors agree on finite étale covers. -/
def etaleToTempFibreIso :
    (etaleToTemp O R A) ⋙ tempFibre O R A V hV ≅ etaleFibre R A Ω :=
  NatIso.ofComponents (fun X => (etaleToTempFibreEquiv O R A V hV X).toIso) fun {X Y} m => by
    ext q
    induction q using Quotient.inductionOn
    rfl

/-- **The comparison homomorphism** from the tempered fundamental group of `[Spec R / A]` to its
étale fundamental group. -/
def temperedToEtale : temperedPi1 O R A V hV →* etalePi1 R A Ω :=
  FibreAut.restrict (etaleToTemp O R A) (etaleToTempFibreIso O R A V hV)

lemma continuous_temperedToEtale : Continuous (temperedToEtale O R A V hV) :=
  FibreAut.continuous_restrict _ _

end

end TemperedFundamentalGroups
