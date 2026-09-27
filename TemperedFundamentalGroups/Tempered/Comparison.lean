/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.Tempered.Category

/-!
# The comparison homomorphism from the tempered to the étale fundamental group

A finite étale cover of `[Spec R / A]`, presented as a finite `G_L`-set `S` over a Galois level
`L`, is the tempered covering attached to the *trivial* model `Spec O` (`ModelCode.trivial`) with
the trivial covering `|Spec k| × S` of its special fibre. This defines a functor
`finiteToTemp : FiniteObj ⥤ TempObj` together with an isomorphism of fibre functors
`finiteToTemp ⋙ tempFibre ≅ finFibre`, and hence the continuous comparison homomorphism

`temperedToEtale : temperedPi1 →* etalePi1`

by restriction of automorphisms (`FibreAut.restrict`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace TemperedFundamentalGroups

noncomputable section

variable {K : Type u} [Field K] (O : ValuationSubring K)
  (R : Type u) [CommRing R] [Algebra K R] (A : Type u) [Group A] [MulSemiringAction A R]
  [SMulCommClass A K R]
  {Ω : Type u} [Field Ω] [Algebra R Ω]

/-- Semilinear automorphisms of a level fix the image of `O`. -/
lemma levelStructureMap_σ (L : FiniteLevel R A Ω) (g : L.G) (x : O) :
    g.σ (levelStructureMap O R A L x) = levelStructureMap O R A L x := by
  simp [levelStructureMap, g.map_algebraMap]

omit [SMulCommClass A K R] in
lemma spec_levelStructureMap {L L' : FiniteLevel R A Ω} (φ : L ⟶ L') :
    Spec.map (CommRingCat.ofHom (levelStructureMap O R A L)) =
      Spec.map (CommRingCat.ofHom (φ.f : L'.B →+* L.B)) ≫
        Spec.map (CommRingCat.ofHom (levelStructureMap O R A L')) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp [levelStructureMap]

/-- **The trivial level** over a finite level: the model `Spec O` (`ℙ⁰_O`) with the trivial
action. -/
def trivialLevel (L : FiniteLevel R A Ω) : Level O R A (Ω := Ω) where
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
    exact levelStructureMap_σ O R A L g⁻¹ x

@[simp] lemma trivialLevel_ρs_apply (L : FiniteLevel R A Ω) (g : L.G)
    (z : (trivialLevel O R A L).Z) : (trivialLevel O R A L).ρs g z = z := by
  apply Subtype.ext
  rw [Level.ρs_apply]
  rfl

/-- **The functor from finite covers to tempered covers**: the trivial model with the trivial
covering `|𝒯_s| × Fin n`. -/
def finiteToTemp : FiniteObj R A Ω ⥤ TempObj O R A (Ω := Ω) where
  obj X := ⟨trivialLevel O R A X.L, CoveringCode.trivial _ X.n X.α⟩
  map {X Y} m :=
    { φ := m.φ
      ψ := 𝟙 _
      ψ_toSpec := Category.id_comp _
      j_ψ := by
        change (Spec.map (CommRingCat.ofHom (levelStructureMap O R A X.L)) ≫
            inv (ModelCode.trivial O).toSpec) ≫ 𝟙 _ =
          Spec.map (CommRingCat.ofHom (m.φ.f : Y.L.B →+* X.L.B)) ≫
            (Spec.map (CommRingCat.ofHom (levelStructureMap O R A Y.L)) ≫
              inv (ModelCode.trivial O).toSpec)
        rw [Category.comp_id, spec_levelStructureMap O R A m.φ, Category.assoc]
      h := fun x => ⟨(x.1.1, (m.h ⟨x.1.2, x.2.2⟩ : ℕ)), Set.mem_univ _, (m.h _).2⟩
      continuous_h := by
        apply Continuous.subtype_mk
        refine Continuous.prodMk (by fun_prop) ?_
        exact continuous_subtype_val.comp
          ((continuous_of_discreteTopology (f := fun k : {k : ℕ | k < X.n} =>
            (⟨(m.h ⟨k.1, k.2⟩ : ℕ), (m.h _).2⟩ : {k : ℕ | k < Y.n}))).comp
          (Continuous.subtype_mk (by fun_prop) fun x => x.2.2))
      fst_h := fun _ => rfl
      h_act := fun g x => by
        apply Subtype.ext
        refine Prod.ext ?_ ?_
        · rfl
        · simp only [CoveringCode.trivial]
          exact congrArg Fin.val (m.h_α g ⟨x.1.2, x.2.2⟩) }
  map_id _ := rfl
  map_comp _ _ := rfl

variable [Algebra K Ω] [IsScalarTower K R Ω] (V : ValuationSubring Ω)
  (hV : V.comap (algebraMap K Ω) = O)

/-- The fibre of the trivial covering over the specialized base point is the finite set. -/
def finiteToTempFibreEquiv (X : FiniteObj R A Ω) :
    ((finiteToTemp O R A) ⋙ tempFibre O R A V hV).obj X ≃ (finFibre R A Ω).obj X where
  toFun x := ⟨⟨x.1.1.2, x.1.2.2⟩⟩
  invFun k := ⟨⟨((trivialLevel O R A X.L).spPoint V hV, k.down), Set.mem_univ _, k.down.2⟩, rfl⟩
  left_inv x := Subtype.ext (Subtype.ext (Prod.ext x.2.symm rfl))
  right_inv _ := rfl

/-- The fibre functors agree on finite covers. -/
def finiteToTempFibreIso :
    (finiteToTemp O R A) ⋙ tempFibre O R A V hV ≅ finFibre R A Ω :=
  NatIso.ofComponents (fun X => (finiteToTempFibreEquiv O R A V hV X).toIso) fun _ => rfl

/-- **The comparison homomorphism** from the tempered fundamental group of `[Spec R / A]` to its
étale fundamental group. -/
def temperedToEtale : temperedPi1 O R A V hV →* etalePi1 R A Ω :=
  FibreAut.restrict (finiteToTemp O R A) (finiteToTempFibreIso O R A V hV)

lemma continuous_temperedToEtale : Continuous (temperedToEtale O R A V hV) :=
  FibreAut.continuous_restrict _ _

end

end TemperedFundamentalGroups
