/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeGlue

/-!
# Finite étale special data over the chart `V₁` of `P1Three` (MR13 (e2))

The datum `Sp : P1Three.Special1` over `V₁ = ℙ¹ ∖ {0, 1, ā}` carries an admissible covering of
`R1[1/1]/J` without nodes or marked points. **`P1Three.CuspChart.Special.ofEtale C1`** builds it
from any finite étale `T/J`-algebra `C1` (for any chart `T`, marked points `V(1) = ∅`): the covering
is `C1` itself over `T[1/1]/J ≃ T/J` (`tsEquivOne`, from `bijective_φsC_one`), with empty Kummer
data (`covOne`; the completion along the unit `1` is the zero ring, `subsingleton_hat_one`), and
`ι₀ = id`. Helpers: `etale_awayMap_of_isUnit` (the `awayMap` of an étale map at a unit is étale),
`algHomToSubsingleton`, `algEquivOfSubsingleton`.
-/

universe u

open TensorProduct

namespace SemistableReduction

namespace P1Three

namespace CuspChart

noncomputable section

open TateLevel AdmissibleLift EtaleTower

variable {O : Type u} [CommRing O] {k : Type u} [Field k] (θ : O →+* k)
  (T : Type u) [CommRing T] [Algebra O T]

/-- The special fibre of `T` and of `T[1/1]` agree: `φsC` is bijective for `c₀ = 1`. -/
lemma bijective_φsC_one : Function.Bijective (CuspTower.φsC T (1 : T) θ) := by
  have hb : Function.Bijective (algebraMap T (CuspTower.Rc T (1 : T))) :=
    (IsLocalization.atOne T (CuspTower.Rc T (1 : T))).bijective
  refine ⟨?_, Ideal.quotientMap_surjective hb.2⟩
  refine Ideal.quotientMap_injective' (le_of_eq ?_)
  have hJ : J θ (R := CuspTower.Rc T (1 : T)) =
      (J θ (R := T)).map (algebraMap T (CuspTower.Rc T (1 : T))) := by
    change (RingHom.ker θ).map _ = ((RingHom.ker θ).map _).map _
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  rw [hJ]
  exact Ideal.comap_map_of_bijective _ hb

/-- `Ts θ T ≃ Ts θ T[1/1]`. -/
def tsEquivOne : Ts θ T ≃+* Ts θ (CuspTower.Rc T (1 : T)) :=
  RingEquiv.ofBijective _ (bijective_φsC_one θ T)

/-- A `k`-algebra map into a zero ring. -/
def algHomToSubsingleton (A B : Type u) [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [hB : Subsingleton B] : A →ₐ[k] B where
  toFun _ := 0
  map_one' := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_zero' := rfl
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

/-- An algebra isomorphism between two zero rings. -/
def algEquivOfSubsingleton (S A B : Type u) [CommRing S] [CommRing A] [CommRing B] [Algebra S A]
    [Algebra S B] [Subsingleton A] [Subsingleton B] : A ≃ₐ[S] B where
  toFun _ := 0
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _
  map_mul' _ _ := Subsingleton.elim _ _
  map_add' _ _ := Subsingleton.elim _ _
  commutes' _ := Subsingleton.elim _ _

lemma subsingleton_hat_one :
    Subsingleton (Admissible.Hat (fbar θ (CuspTower.sC T (1 : T) (1 : T)))) :=
  have h : Ideal.span {fbar θ (CuspTower.sC T (1 : T) (1 : T))} = ⊤ := by
    refine Ideal.span_singleton_eq_top.mpr ?_
    change IsUnit (Ideal.Quotient.mk _ (algebraMap T (CuspTower.Rc T (1 : T)) 1))
    rw [map_one, map_one]
    exact isUnit_one
  ⟨fun x y ↦ AdicCompletion.ext fun n ↦ by
    have : Subsingleton (Ts θ (CuspTower.Rc T (1 : T)) ⧸
        (Ideal.span {fbar θ (CuspTower.sC T (1 : T) (1 : T))} ^ n • ⊤ :
          Submodule (Ts θ (CuspTower.Rc T (1 : T))) (Ts θ (CuspTower.Rc T (1 : T))))) := by
      rw [h, Ideal.top_pow, Submodule.top_smul]
      exact Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Subsingleton.elim _ _⟩

/-- The `awayMap` of an étale map at a unit is étale. -/
lemma etale_awayMap_of_isUnit {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B)
    (hg : g.Etale) (r : A) (hr : IsUnit r) : (Localization.awayMap g r).Etale := by
  have hA : Function.Bijective (algebraMap A (Localization.Away r)) :=
    (IsLocalization.atUnit A (Localization.Away r) r hr).bijective
  let e := RingEquiv.ofBijective _ hA
  have hB : (algebraMap B (Localization.Away (g r))).Etale :=
    RingHom.etale_algebraMap.mpr (Algebra.Etale.of_isLocalizationAway (g r))
  have hc : Localization.awayMap g r =
      ((algebraMap B (Localization.Away (g r))).comp g).comp e.symm.toRingHom := by
    refine IsLocalization.ringHom_ext (Submonoid.powers r) (RingHom.ext fun x ↦ ?_)
    simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    congr 2
    exact (e.symm_apply_apply x).symm
  rw [hc]
  exact RingHom.Etale.respectsIso.2 _ _
    (RingHom.Etale.stableUnderComposition _ _ hg hB)

variable {θ T}

variable (C1 : Type u) [CommRing C1] [Algebra (Ts θ T) C1]

/-- `C1` over `T[1/1]/J` (through `T/J ≃ T[1/1]/J`). -/
abbrev algOne : Algebra (Ts θ (CuspTower.Rc T (1 : T))) C1 :=
  ((algebraMap (Ts θ T) C1).comp (tsEquivOne θ T).symm.toRingHom).toAlgebra

lemma isUnit_fbar_one : IsUnit (fbar θ (CuspTower.sC T (1 : T) (1 : T))) := by
  change IsUnit (Ideal.Quotient.mk _ (algebraMap T (CuspTower.Rc T (1 : T)) 1))
  rw [map_one, map_one]
  exact isUnit_one

lemma kummerOne_subsingleton :
    letI := algOne C1 (θ := θ) (T := T)
    Subsingleton (Admissible.Hat (fbar θ (CuspTower.sC T (1 : T) (1 : T))) ⊗[Ts θ
      (CuspTower.Rc T (1 : T))] C1) := by
  letI := algOne C1 (θ := θ) (T := T)
  haveI := subsingleton_hat_one θ T
  exact Module.subsingleton (Admissible.Hat (fbar θ (CuspTower.sC T (1 : T) (1 : T)))) _

variable [Fact (Function.Surjective θ)]

/-- The admissible covering of `T[1/1]/J` given by a finite étale `T/J`-algebra: no Kummer
factors (the completion along the unit `1` is zero). -/
def covOne [Module.Finite (Ts θ T) C1] [Algebra.Etale (Ts θ T) C1] :
    Admissible.Covering (algHomToSubsingleton (Node k (0 : k))
        (Admissible.Hat (fbar θ (CuspTower.sC T (1 : T) (1 : T))))
        (hB := subsingleton_hat_one θ T))
      (CuspTower.ψb (θ := θ) (CuspTower.Rc T (1 : T)) (CuspTower.sC T 1 1)
        (CuspTower.sC T 1 1)) where
  C := C1
  algebra := algOne C1
  finite := by
    letI := algOne C1 (θ := θ) (T := T)
    exact RingHom.finite_algebraMap.mp (RingHom.Finite.comp
      (RingHom.finite_algebraMap.mpr inferInstance) (RingHom.Finite.of_surjective _
        (tsEquivOne θ T).symm.surjective))
  etale := by
    letI := algOne C1 (θ := θ) (T := T)
    exact etale_awayMap_of_isUnit _ (RingHom.Etale.respectsIso.2 _ _
      (RingHom.etale_algebraMap.mpr inferInstance)) _ (isUnit_fbar_one (θ := θ) (T := T))
  ι := Empty
  idem := isEmptyElim
  isIdempotentElem_idem := isEmptyElim
  e := isEmptyElim
  e_pos := isEmptyElim
  e_ne_zero := isEmptyElim
  κ := Empty
  cidem := isEmptyElim
  isIdempotentElem_cidem := isEmptyElim
  ce := isEmptyElim
  ce_pos := isEmptyElim
  ce_ne_zero := isEmptyElim
  kummer := by
    letI := algOne C1 (θ := θ) (T := T)
    haveI := kummerOne_subsingleton C1 (θ := θ) (T := T)
    exact algEquivOfSubsingleton _ _ _

omit [Fact (Function.Surjective θ)] in
lemma hιOne (hu : IsUnit (algebraMap (Ts θ T) C1 (Ideal.Quotient.mk _ 1))) :
    letI := (RingHom.id C1).toAlgebra
    IsLocalization.Away (algebraMap (Ts θ T) C1 (Ideal.Quotient.mk _ 1)) C1 :=
  IsLocalization.self (Submonoid.powers_le.mpr ((IsUnit.mem_submonoid_iff _).mpr hu))

/-- **A finite étale covering of a chart without marked points as `CuspChart.Special`** (the
datum `Sp` over `V₁` of `P1Three` is of this form): `C1` finite étale over `T/J`, its admissible
covering `covOne` of `T[1/1]/J`, and `ι₀ = id`. -/
def Special.ofEtale [Module.Finite (Ts θ T) C1] [Algebra.Etale (Ts θ T) C1] :
    Special θ T 1 1 where
  C1 := C1
  finite := inferInstance
  etale := etale_awayMap_of_isUnit _ (RingHom.etale_algebraMap.mpr inferInstance) _
    (by rw [map_one]; exact isUnit_one)
  φ₀ := algHomToSubsingleton _ _ (hB := subsingleton_hat_one θ T)
  cov := covOne C1 (θ := θ) (T := T)
  noNodes := (inferInstance : IsEmpty Empty)
  ι₀ := RingHom.id C1
  hι₀ := fun x ↦ congrArg (algebraMap (Ts θ T) C1) ((tsEquivOne θ T).symm_apply_apply x).symm
  hι := hιOne C1 (θ := θ) (T := T) (by rw [map_one, map_one]; exact isUnit_one)

end

end CuspChart

end P1Three

end SemistableReduction
