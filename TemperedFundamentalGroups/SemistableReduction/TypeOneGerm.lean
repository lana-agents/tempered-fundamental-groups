/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import TemperedFundamentalGroups.SemistableReduction.PowTransport
import TemperedFundamentalGroups.SemistableReduction.S8BLimit

/-!
# Small residue balls around a classical point are good (S8.2)

Blueprint §9.12 O6.1f. `S8A.ClassicalGoodFor C F` from
* (i) `KummerUnramFor` (Kummer base change `L = F(y)`, `y ^ E = x - a`, kills the ramification;
  owner O1 agent),
* (ii) the chart comparison `x - a = y ^ E` (`PowData`, `PowTransport`),
* (iii) **A6** (smooth points descend along the Galois extension `L / F`; owner S8.5 agent,
  `A6For`, in its owner's form),
and the unramified case `ballGood_of_unramDatum` for `L / C(y)` at `y = 0`.
-/

open Polynomial Metric
open scoped NNReal IntermediateField

namespace SemistableReduction

namespace ClassicalSmooth

open GaussFibre DiscCount SmoothVertex AffineTwist

variable {C : Type*} [NontriviallyNormedField C] [IsUltrametricDist C] [IsAlgClosed C]

section A6

variable {E L : Type*} [Field E] [Field L] [Algebra (RatFunc C) E] [Algebra (RatFunc C) L]
  [Algebra E L] [IsScalarTower (RatFunc C) E L]

/-- `algebraMap E L` between the twists. -/
noncomputable def affMap (a c : C) (hc : c ≠ 0) : Aff a c hc E →+* Aff a c hc L :=
  (toAff (a := a) hc).toRingHom.comp ((algebraMap E L).comp (toAff (a := a) hc).symm.toRingHom)

omit [IsAlgClosed C] in
lemma affMap_algebraMap (a c : C) (hc : c ≠ 0) (φ : RatFunc C) :
    affMap a c hc (algebraMap (RatFunc C) (Aff a c hc E) φ) =
      algebraMap (RatFunc C) (Aff a c hc L) φ := by
  change algebraMap E L (algebraMap (RatFunc C) E (aff a c hc φ)) =
    algebraMap (RatFunc C) L (aff a c hc φ)
  rw [← IsScalarTower.algebraMap_apply]

/-- The inclusion of normalized vertex charts `DRint 0 1 (Aff a c E) → DRint 0 1 (Aff a c L)`. -/
noncomputable def drintMap (a c : C) (hc : c ≠ 0) :
    DRint (0 : C) 1 (Aff a c hc E) →+* DRint (0 : C) 1 (Aff a c hc L) where
  toFun y := ⟨affMap a c hc (y : Aff a c hc E),
    IsIntegral.map_of_comp_eq (R := discRing (0 : C) 1) (T := discRing (0 : C) 1)
      (S := Aff a c hc E) (U := Aff a c hc L) (RingHom.id _) (affMap (L := L) a c hc)
      (RingHom.ext fun φ ↦ (affMap_algebraMap (E := E) (L := L) a c hc (φ : RatFunc C)).symm)
      (y.2 : IsIntegral (discRing (0 : C) 1) (y : Aff a c hc E))⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' _ _ := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable (C E L) in
/-- **A6** (Blueprint §9.10 L1 A6, owner S8.5 agent): smooth points descend along a Galois
extension `L / E`: if every point of `DRint 0 1 (Aff a c L)` over a point `P'` of
`DRint 0 1 (Aff a c E)` over the residue point is smooth, so is `P'`. -/
def A6For [Algebra C E] [Algebra C L] [IsScalarTower C (RatFunc C) E]
    [IsScalarTower C (RatFunc C) L] [FiniteDimensional (RatFunc C) E]
    [FiniteDimensional (RatFunc C) L] [IsGalois E L] : Prop :=
  ∀ (a c : C) (hc : c ≠ 0) (P' : Ideal (DRint (0 : C) 1 (Aff a c hc E))), P'.IsMaximal →
    P'.comap (algebraMap (discRing (0 : C) 1) (DRint (0 : C) 1 (Aff a c hc E))) =
      discIdeal (0 : C) 1 →
    (∀ P'' : Ideal (DRint (0 : C) 1 (Aff a c hc L)), P''.IsMaximal →
      P''.comap (drintMap a c hc) = P' → IsDiscSmooth P'') → IsDiscSmooth P'

end A6

omit [IsUltrametricDist C] in
/-- A Kummer extension `F(y)`, `y ^ E ∈ F`, of a field containing the `E`-th roots of unity
(here: containing `C`) is Galois. -/
lemma isGalois_of_pow {F L : Type*} [Field F] [Field L] [Algebra C F] [Algebra F L]
    [FiniteDimensional F L] [CharZero C] {E : ℕ} (hE : 0 < E) {y : L} {b : F} (hb : b ≠ 0)
    (hy : y ^ E = algebraMap F L b) (hadj : F⟮y⟯ = ⊤) : IsGalois F L := by
  haveI : NeZero (E : C) := ⟨by exact_mod_cast hE.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C E
  have hζL : IsPrimitiveRoot (algebraMap F L (algebraMap C F ζ)) E :=
    hζ.map_of_injective ((algebraMap F L).comp (algebraMap C F)).injective
  haveI : (X ^ E - Polynomial.C b).IsSplittingField F L := by
    constructor
    · rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
      exact X_pow_sub_C_splits_of_isPrimitiveRoot hζL hy
    · rw [eq_top_iff, ← IntermediateField.top_toSubalgebra, ← hadj,
        IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (IsAlgebraic.of_finite F y)]
      apply Algebra.adjoin_mono
      rw [Set.singleton_subset_iff, mem_rootSet_of_ne (X_pow_sub_C_ne_zero hE b), aeval_def,
        eval₂_sub, eval₂_X_pow, eval₂_C, hy, sub_self]
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap C F).injective
  exact IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_C b (by exact_mod_cast hE.ne') hb)

universe w

variable [CharZero C] {p : ℕ} (hp : p.Prime) (hp1 : ‖(p : C)‖ < 1)
  {F : Type*} [Field F] [Algebra (RatFunc C) F] [Algebra C F] [IsScalarTower C (RatFunc C) F]
  [FiniteDimensional (RatFunc C) F]

include hp hp1 in
/-- **S8.2 (O6.1f)**: small residue balls around a classical point are good, from Kummer base
change (O6.1f(i)) and A6 (O6.1f(iii)). -/
theorem classicalGoodFor_of (hK : ∀ a : C, KummerUnramFor.{_, _, w} C F a)
    (hA6 : ∀ (L : Type w) [Field L] [Algebra (RatFunc C) L] [Algebra F L]
      [IsScalarTower (RatFunc C) F L] [Algebra C L] [IsScalarTower C (RatFunc C) L]
      [FiniteDimensional (RatFunc C) L] [IsGalois F L], A6For C F L) :
    S8A.ClassicalGoodFor C F := by
  intro a
  obtain ⟨E, L, _, _, _, _, _, y, hy, hE, hyE, hadj, _, θ, n, γ, hU⟩ := hK a
  -- the `x`-structure on `L`
  letI : Algebra (RatFunc C) L := ((algebraMap F L).comp (algebraMap (RatFunc C) F)).toAlgebra
  haveI : IsScalarTower (RatFunc C) F L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower C (RatFunc C) L := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply C F L, IsScalarTower.algebraMap_apply C (RatFunc C) F]
    rfl
  haveI : FiniteDimensional (RatFunc C) L := Module.Finite.trans F L
  have hb : algebraMap (RatFunc C) F (RatFunc.X - algebraMap C (RatFunc C) a) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap (RatFunc C) F).injective, sub_eq_zero]
    intro h
    have := congrArg RatFunc.intDegree h
    simp at this
  haveI : IsGalois F L := isGalois_of_pow (C := C) hE hb hyE hadj
  -- the unramified case for `L / C(y)` at `y = 0`
  obtain ⟨s₀, hs₀, hgood⟩ := ballGood_of_unramDatum hp hp1 hU
  refine ⟨s₀ ^ E, pow_pos hs₀ E, fun c hc hcs ↦ ?_⟩
  obtain ⟨γ', hγ'⟩ := IsAlgClosed.exists_pow_nat_eq c hE
  have hγ'0 : γ' ≠ 0 := by rintro rfl; rw [zero_pow hE.ne'] at hγ'; exact hc hγ'.symm
  have hγ's : ‖γ'‖ ≤ s₀ := by
    rw [← hγ', norm_pow] at hcs
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hs₀.le hE.ne').1 hcs
  have h2 := (S8A.Transport.ballGood_iff hγ'0).1 (hgood γ' hγ'0 hγ's)
  -- the two coordinates: `(x - a) / c = (y / γ') ^ E`
  have hAB : (coordAlgHom hy).comp ((aff 0 γ' hγ'0).toAlgHom.comp (powHom C E hE)) =
      (IsScalarTower.toAlgHom C (RatFunc C) L).comp (aff a c hc).toAlgHom := by
    refine ratFunc_algHom_ext ?_
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, powHom_X, map_pow, aff_apply, affHom_X,
      IsScalarTower.coe_toAlgHom', gaussCoord_eq, map_mul, map_sub, AlgHom.commutes,
      coordAlgHom_X, map_zero, sub_zero]
    have hx : algebraMap (RatFunc C) L RatFunc.X - algebraMap C L a = y ^ E := by
      rw [IsScalarTower.algebraMap_apply C (RatFunc C) L, ← map_sub, hyE]
      rfl
    rw [hx, ← hγ', mul_pow, map_inv₀, map_inv₀, map_pow, inv_pow]
  let d : PowData C (Aff a c hc L) (Aff 0 γ' hγ'0 (Coord hy)) :=
    { E := E
      hE := hE
      e := RingEquiv.refl L
      he := fun φ ↦ by
        have := congrArg (fun χ : RatFunc C →ₐ[C] L ↦ χ φ) hAB
        exact this }
  -- smooth points of `L` over the `x`-disc
  have h1 := d.isDiscSmooth_of_pow h2
  -- A6
  refine (S8A.Transport.ballGood_iff hc).2 fun P' hP' hcen ↦
    hA6 L a c hc P' hP' hcen fun P'' hP'' hP''P ↦ h1 P'' hP'' ?_
  rw [← hcen, ← hP''P, Ideal.comap_comap]
  rfl


end ClassicalSmooth

end SemistableReduction
