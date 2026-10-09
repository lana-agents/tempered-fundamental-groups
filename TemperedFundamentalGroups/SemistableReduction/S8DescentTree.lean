/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.S8DescentTube
import TemperedFundamentalGroups.SemistableReduction.S8Galois
import TemperedFundamentalGroups.SemistableReduction.NodeDataODP

/-!
# Descent (S8.C), part 6: semistable Gauss trees descend

Blueprint §9.12 O6.6 ([AW Prop 2.1]). For `C(x) ⊆ E ⊆ L` finite with `L / E` Galois, a Gauss tree
semistable for `L` is semistable for `E` (`isSemistableTree_descent`):

* smooth points (vertex charts and the chart at `∞` of the root): A6
  (`isDiscSmooth_of_galois`);
* ordinary double points over the nodes: (T⇒) for `L` gives the valuative tube condition, which
  descends to `E` (`tubeCond_descent`, Lüroth and surjectivity of the restriction of places),
  and (T⇐) for `E` gives back ordinary double points.

**`S8A.s8cDescent_of`**: `S8A.S8CDescent` from the off-skeleton clause (lemma (L)) and (T⇐), via
the Galois hull (the node data O1 is `ExhaustGluing.nodeDataOfODP`).
-/

universe u v

namespace SemistableReduction

namespace S8A

namespace Descent

open GaussFibre GaussTube DiscCount SmoothVertex AffineTwist ExhaustGluing ClassicalSmooth
  TreeBridge

section Tree

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
  [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {E L : Type*} [Field E] [Field L] [Algebra (RatFunc C) E] [Algebra (RatFunc C) L]
  [Algebra E L] [IsScalarTower (RatFunc C) E L] [Algebra C E] [Algebra C L]
  [IsScalarTower C (RatFunc C) E] [IsScalarTower C (RatFunc C) L]
  [FiniteDimensional (RatFunc C) E] [FiniteDimensional (RatFunc C) L]

omit [IsAlgClosed C] [CharZero C] [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
  [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) E]
  [FiniteDimensional (RatFunc C) L] in
lemma drintIncl_comp_algebraMap :
    (drintIncl E L).comp (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 E)) =
      algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 L) :=
  RingHom.ext fun φ ↦ Subtype.ext
    (IsScalarTower.algebraMap_apply (RatFunc C) E L (φ : RatFunc C)).symm

include hp hp1 in
/-- **A6 on a chart**: if every point of `R_L` over the residue point is smooth, so is every
point of `R_E` over it. -/
theorem isDiscSmooth_descent [IsGalois E L] {P' : Ideal (DRint (0 : C) 1 E)} [P'.IsMaximal]
    (hP' : P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 E)) = discIdeal (0 : C) 1)
    (h : ∀ Q : Ideal (DRint (0 : C) 1 L), Q.IsMaximal →
      Q.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 L)) = discIdeal (0 : C) 1 →
        IsDiscSmooth Q) :
    IsDiscSmooth P' :=
  isDiscSmooth_of_galois (E := E) (L := L) hp hp1 fun Q hQ hQP ↦ h Q hQ (by
    rw [← drintIncl_comp_algebraMap (E := E) (L := L), ← Ideal.comap_comap, hQP, hP'])

/-- `algebraMap E L` between the inverted twists. -/
@[reducible] noncomputable def algebraInvInv (c : C) (hc : c ≠ 0) :
    Algebra (GaussTube.Inv c hc E) (GaussTube.Inv c hc L) :=
  inferInstanceAs (Algebra E L)

attribute [local instance] algebraInvInv

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] [Algebra C E] [Algebra C L]
  [IsScalarTower C (RatFunc C) E] [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) E]
  [FiniteDimensional (RatFunc C) L] in
lemma isScalarTower_invInv (c : C) (hc : c ≠ 0) :
    IsScalarTower (RatFunc C) (GaussTube.Inv c hc E) (GaussTube.Inv c hc L) :=
  IsScalarTower.of_algebraMap_eq fun φ ↦
    (IsScalarTower.algebraMap_apply (RatFunc C) E L (inv hc φ))

attribute [local instance] algebraAffAff

include hp hp1 in
/-- **Semistable Gauss trees descend** along a Galois extension `L / E`, given (T⇒) for `L` and
(T⇐) for `E`. -/
theorem isSemistableTree_descent [IsGalois E L] {ι : Type*} {a c : ι → C} {hc : ∀ i, c i ≠ 0}
    (hT : TubeOfExhausting C L) (hT' : ExhaustingOfTube C E)
    (h : W7.IsSemistableTree a c hc L) : W7.IsSemistableTree a c hc E where
  node j m _ h1 h0 :=
    hT' _ _ _ _ h1 h0 (tubeCond_descent hp hp1 _ (hT _ _ _ _ h1 h0 (h.node j m ‹_› h1 h0)))
  smooth i β hβ hch P' hP' hP'c := by
    haveI := hP'
    haveI := isScalarTower_affAff (E := E) (L := L) (a i + c i * β) (c i) (hc i)
    haveI : IsGalois (Aff (a i + c i * β) (c i) (hc i) E) (Aff (a i + c i * β) (c i) (hc i) L) :=
      inferInstanceAs (IsGalois E L)
    exact isDiscSmooth_descent hp hp1 hP'c fun Q hQ hQc ↦ h.smooth i β hβ hch Q hQ hQc
  root i hi P' hP' hP'c := by
    haveI := hP'
    haveI := isScalarTower_affAff (E := E) (L := L) (a i) (c i) (hc i)
    haveI := isScalarTower_invInv (E := Aff (a i) (c i) (hc i) E)
      (L := Aff (a i) (c i) (hc i) L) (1 : C) one_ne_zero
    haveI : IsGalois (GaussTube.Inv (1 : C) one_ne_zero (Aff (a i) (c i) (hc i) E))
        (GaussTube.Inv (1 : C) one_ne_zero (Aff (a i) (c i) (hc i) L)) :=
      inferInstanceAs (IsGalois E L)
    exact isDiscSmooth_descent hp hp1 hP'c fun Q hQ hQc ↦ h.root i hi Q hQ hQc

end Tree

end Descent

/-- **S8.C descent** ([AW Prop 2.1]) from the off-skeleton clause of (T⇒) (lemma (L)) for the
Galois hull and (T⇐) for the members (`DefinedOverDVR`): the node data (O1) is
`ExhaustGluing.nodeDataOfODP`, smoothness descends by A6. -/
theorem s8cDescent_of
    (hOff : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
      [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
      ∀ (F : Type u) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
      [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F →
        ExhaustGluing.OffSkeletonOfExhausting C F)
    (hT' : ∀ (C : Type u) [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]
      [CharZero C] (p : ℕ), p.Prime → ‖(p : C)‖ < 1 →
      ∀ (F : Type v) [Field F] [Algebra (RatFunc C) F] [Algebra C F]
      [IsScalarTower C (RatFunc C) F] [FiniteDimensional (RatFunc C) F], DefinedOverDVR C F →
        ExhaustGluing.ExhaustingOfTube C F) :
    S8CDescent.{u, v} := by
  intro C _ _ _ _ p hp hp1 κ _ F' _ _ _ _ _ hdef ι _ a c hc hV k
  obtain ⟨f⟩ := exists_embedding C F' k
  letI : Algebra (F' k) (galoisHull C F') := f.toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc C) (F' k) (galoisHull C F') :=
    IsScalarTower.of_algebraMap_eq fun φ ↦ (f.commutes φ).symm
  haveI : IsGalois (F' k) (galoisHull C F') :=
    IsGalois.tower_top_of_isGalois (RatFunc C) (F' k) _
  have hdefH : DefinedOverDVR C (galoisHull C F') := (hdef k).of_finite _
  exact Descent.isSemistableTree_descent hp hp1
    (ExhaustGluing.tubeOfExhausting_of_definedOverDVR hp hp1 hdefH
      (hOff C p hp hp1 _ hdefH))
    (hT' C p hp hp1 (F' k) (hdef k)) hV

end S8A

end SemistableReduction
