/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.P1ThreeCuspNF
import TemperedFundamentalGroups.SemistableReduction.P1ThreeDedekind

/-!
# The chart `V₁` of the `P1Three` model and its special fibre as domains of rank `3` over the line

For the chart ring `R1 = O[Y][s]/(G₁)` of `V₁ = ℙ¹ ∖ {0, 1, a}` (`P1ThreeChart`):

* **`P1Three.finrank_R1`**: `[R1 : O[Y]] = 3` (power basis `1, s, s²`);
* **`P1Three.isDomain_R1`**: `R1` is a domain if `O` is (it embeds into `R1 ⊗ Frac O`, a Dedekind
  domain by `isDedekindDomain_R1`);
* **`P1Three.tsEquiv1 : R1/J ≃ R1 k ā`** (`J = (ker θ) R1`): the special fibre of `V₁` is the chart
  ring over the residue field, hence a domain (**`isDomain_Ts_R1`**);
* **`P1Three.algTs1`**: `R1/J` as a `k[Y]`-algebra (`Y ↦ ȳ`), finite of rank `3`
  (`finrank_Ts_R1`), with `k[Y] → R1/J` injective.

These are the inputs of the degree lemma `P1Three.finrank_lift` (`P1ThreeDegree`): the generic
rank of the lift `B₁` over `R1` equals the generic rank of the special cover `C1` over `R1/J`.
-/

universe u

open Polynomial nonZeroDivisors

namespace SemistableReduction

namespace P1Three

open TateLevel AdmissibleLift EtaleTower

noncomputable section

section Rank

variable (O : Type u) [CommRing O] (a : O)

lemma natDegree_G1_of_nontrivial [Nontrivial O] : (G1 O a).natDegree = 3 := by
  unfold G1
  compute_degree!

/-- **`[R1 : O[Y]] = 3`.** -/
theorem finrank_R1 [Nontrivial O] : Module.finrank O[X] (R1 O a) = 3 := by
  rw [(AdjoinRoot.powerBasis' (monic_G1 O a)).finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_G1_of_nontrivial]

/-- **`R1` is a domain** if `O` is. -/
theorem isDomain_R1 [IsDomain O] : IsDomain (R1 O a) := by
  let K := FractionRing O
  letI := (PlaneCurve.baseMap (map_G1 a (algebraMap O K))).toAlgebra
  haveI := PlaneCurve.isLocalization_adjoinRoot_map (map_G1 a (algebraMap O K)) O⁰ le_rfl
    (monic_G1 O a)
  haveI : IsDomain (R1 K (algebraMap O K a)) :=
    (isDedekindDomain_R1 (algebraMap O K a)).toIsDomain
  have hle : Algebra.algebraMapSubmonoid (R1 O a) O⁰ ≤ (R1 O a)⁰ := by
    rintro _ ⟨o, ho, rfl⟩
    have hC : (C o : O[X]) ∈ O[X]⁰ :=
      mem_nonZeroDivisors_of_ne_zero (C_ne_zero.2 (nonZeroDivisors.ne_zero ho))
    have hreg : IsSMulRegular (R1 O a) (C o : O[X]) :=
      Module.Flat.isSMulRegular_of_nonZeroDivisors hC
    have key : ∀ y : R1 O a, y * algebraMap O (R1 O a) o = 0 → y = 0 := fun y hy ↦ by
      apply hreg
      change C o • y = C o • (0 : R1 O a)
      rw [smul_zero, Algebra.smul_def, mul_comm, ← Polynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply]
      exact hy
    rw [mem_nonZeroDivisors_iff]
    exact ⟨fun y hy ↦ key y (by rwa [mul_comm]), key⟩
  exact (IsLocalization.injective (R1 K (algebraMap O K a)) hle).isDomain _

end Rank

section Special

variable {O : Type u} [CommRing O] (a : O) {k : Type u} [Field k] {θ : O →+* k}

/-- `R1 → R1 k ā` (reduction of the coefficients). -/
def toBar1 : R1 O a →+* R1 k (θ a) :=
  AdjoinRoot.lift ((AdjoinRoot.of (G1 k (θ a))).comp (mapRingHom θ)) (AdjoinRoot.root _) (by
    rw [← Polynomial.eval₂_map, map_G1]
    exact AdjoinRoot.eval₂_root _)

lemma toBar1_of (p : O[X]) :
    toBar1 a (θ := θ) (AdjoinRoot.of _ p) = AdjoinRoot.of (G1 k (θ a)) (p.map θ) := by
  rw [toBar1, AdjoinRoot.lift_of]
  rfl

lemma toBar1_root : toBar1 a (θ := θ) (AdjoinRoot.root _) = AdjoinRoot.root (G1 k (θ a)) :=
  AdjoinRoot.lift_root _

lemma toBar1_algebraMap (o : O) :
    toBar1 a (θ := θ) (algebraMap O (R1 O a) o) = algebraMap k (R1 k (θ a)) (θ o) := by
  rw [← of_C, toBar1_of, Polynomial.map_C, of_C]

lemma J_le_ker_toBar1 : J θ (R := R1 O a) ≤ RingHom.ker (toBar1 a (θ := θ)) := by
  rw [J, Ideal.map_le_iff_le_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.mem_ker, toBar1_algebraMap, RingHom.mem_ker.1 ho, map_zero]

/-- `R1/J → R1 k ā`. -/
def toBar1s : Ts θ (R1 O a) →+* R1 k (θ a) :=
  Ideal.Quotient.lift _ (toBar1 a) (fun _ h ↦ J_le_ker_toBar1 a h)

lemma toBar1s_mk (x : R1 O a) : toBar1s a (θ := θ) (Ideal.Quotient.mk _ x) = toBar1 a x :=
  Ideal.Quotient.lift_mk _ _ _

variable [hθ : Fact (Function.Surjective θ)]

/-- `R1 k ā → R1/J`, `Y ↦ ȳ`, `s ↦ s̄`. -/
def ofBar1 : R1 k (θ a) →+* Ts θ (R1 O a) :=
  AdjoinRoot.lift (eval₂RingHom (algebraMap k (Ts θ (R1 O a))) (Ideal.Quotient.mk _ (y1 O a)))
    (Ideal.Quotient.mk _ (s1 O a)) (by
      have h := eval₂_G1 (θ a) (S := Ts θ (R1 O a)) (Ideal.Quotient.mk _ (y1 O a))
        (Ideal.Quotient.mk _ (s1 O a))
      have h1 := congrArg (Ideal.Quotient.mk (J θ (R := R1 O a))) (eq1 O a)
      rw [QuadNodeTower.algK_θ] at h
      simp only [map_sub, map_add, map_mul, map_pow, map_one, map_zero] at h1
      rw [show (eval₂RingHom (algebraMap k (Ts θ (R1 O a))) (Ideal.Quotient.mk _ (y1 O a)) :
          k[X] →+* Ts θ (R1 O a)) = ((aeval (Ideal.Quotient.mk _ (y1 O a)) :
            k[X] →ₐ[k] Ts θ (R1 O a)) : k[X] →+* Ts θ (R1 O a)) from rfl, h]
      linear_combination h1)

lemma ofBar1_of (p : k[X]) :
    ofBar1 a (θ := θ) (AdjoinRoot.of _ p) =
      eval₂ (algebraMap k (Ts θ (R1 O a))) (Ideal.Quotient.mk _ (y1 O a)) p := by
  rw [ofBar1, AdjoinRoot.lift_of]
  rfl

lemma ofBar1_root : ofBar1 a (θ := θ) (AdjoinRoot.root _) = Ideal.Quotient.mk _ (s1 O a) :=
  AdjoinRoot.lift_root _

lemma toBar1s_ofBar1 (x : R1 k (θ a)) : toBar1s a (ofBar1 a (θ := θ) x) = x := by
  have h : (toBar1s a (θ := θ)).comp (ofBar1 a (θ := θ)) = RingHom.id _ := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun c ↦ ?_) ?_) ?_
    · obtain ⟨o, rfl⟩ := hθ.out c
      simp only [RingHom.comp_apply, RingHom.id_apply, ofBar1_of, eval₂_C, QuadNodeTower.algK_θ,
        toBar1s_mk, toBar1_algebraMap]
      rfl
    · simp only [RingHom.comp_apply, RingHom.id_apply, ofBar1_of, eval₂_X, toBar1s_mk]
      rw [y1, toBar1_of, Polynomial.map_X]
    · simp only [RingHom.comp_apply, RingHom.id_apply, ofBar1_root, toBar1s_mk]
      exact toBar1_root a
  exact RingHom.congr_fun h x

lemma ofBar1_toBar1s (x : Ts θ (R1 O a)) : ofBar1 a (toBar1s a (θ := θ) x) = x := by
  have h : ((ofBar1 a (θ := θ)).comp (toBar1s a (θ := θ))).comp (Ideal.Quotient.mk _) =
      Ideal.Quotient.mk (J θ (R := R1 O a)) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun o ↦ ?_) ?_) ?_
    · simp only [RingHom.comp_apply, toBar1s_mk, of_C, toBar1_algebraMap]
      rw [← of_C, ofBar1_of, eval₂_C, QuadNodeTower.algK_θ]
    · simp only [RingHom.comp_apply, toBar1s_mk]
      rw [toBar1_of, Polynomial.map_X, ofBar1_of, eval₂_X]
    · simp only [RingHom.comp_apply, toBar1s_mk, toBar1_root, ofBar1_root]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun h y

/-- **The special fibre of `V₁`: `R1/J ≃ R1 k ā`.** -/
def tsEquiv1 : Ts θ (R1 O a) ≃+* R1 k (θ a) :=
  RingEquiv.ofRingHom (toBar1s a (θ := θ)) (ofBar1 a (θ := θ))
    (RingHom.ext fun x ↦ toBar1s_ofBar1 a x) (RingHom.ext fun x ↦ ofBar1_toBar1s a x)

lemma tsEquiv1_mk (x : R1 O a) :
    tsEquiv1 a (θ := θ) (Ideal.Quotient.mk _ x) = toBar1 a x :=
  toBar1s_mk a x

/-- **The special fibre `R1/J` of `V₁` is a domain.** -/
theorem isDomain_Ts_R1 : IsDomain (Ts θ (R1 O a)) :=
  haveI : IsDomain (R1 k (θ a)) := (isDedekindDomain_R1 (θ a)).toIsDomain
  Function.Injective.isDomain (tsEquiv1 a (θ := θ)).toRingHom (tsEquiv1 a (θ := θ)).injective

/-- **`R1/J` as a `k[Y]`-algebra** (`Y ↦ ȳ`), through `tsEquiv1`. -/
@[reducible] def algTs1 : Algebra k[X] (Ts θ (R1 O a)) :=
  ((tsEquiv1 a (θ := θ)).symm.toRingHom.comp (algebraMap k[X] (R1 k (θ a)))).toAlgebra

/-- `tsEquiv1` as a `k[Y]`-algebra equivalence. -/
def tsAlgEquiv1 : letI := algTs1 a (θ := θ); Ts θ (R1 O a) ≃ₐ[k[X]] R1 k (θ a) :=
  letI := algTs1 a (θ := θ)
  AlgEquiv.ofRingEquiv (f := tsEquiv1 a (θ := θ)) fun _ ↦
    (tsEquiv1 a (θ := θ)).apply_symm_apply _

/-- **`[R1/J : k[Y]] = 3`.** -/
theorem finrank_Ts_R1 : letI := algTs1 a (θ := θ); Module.finrank k[X] (Ts θ (R1 O a)) = 3 := by
  letI := algTs1 a (θ := θ)
  rw [(tsAlgEquiv1 a (θ := θ)).toLinearEquiv.finrank_eq, finrank_R1]

instance : Module.Finite k[X] (R1 k (θ a)) := inferInstance

/-- `R1/J` is finite over `k[Y]`. -/
theorem finite_Ts_R1 : letI := algTs1 a (θ := θ); Module.Finite k[X] (Ts θ (R1 O a)) := by
  letI := algTs1 a (θ := θ)
  exact Module.Finite.equiv (tsAlgEquiv1 a (θ := θ)).toLinearEquiv.symm

/-- `k[Y] → R1/J` is injective. -/
theorem injective_algTs1 :
    Function.Injective (letI := algTs1 a (θ := θ); algebraMap k[X] (Ts θ (R1 O a))) := by
  haveI : IsDomain (R1 k (θ a)) := (isDedekindDomain_R1 (θ a)).toIsDomain
  have h : Function.Injective (algebraMap k[X] (R1 k (θ a))) :=
    FaithfulSMul.algebraMap_injective _ _
  exact (tsEquiv1 a (θ := θ)).symm.injective.comp h

/-- The algebra map `k[Y] → R1/J` on the reduction of `p ∈ O[Y]` is the reduction of `p`. -/
lemma algTs1_map (p : O[X]) :
    (letI := algTs1 a (θ := θ); algebraMap k[X] (Ts θ (R1 O a)) (p.map θ)) =
      Ideal.Quotient.mk _ (algebraMap O[X] (R1 O a) p) := by
  change (tsEquiv1 a (θ := θ)).symm (algebraMap k[X] (R1 k (θ a)) (p.map θ)) = _
  rw [RingEquiv.symm_apply_eq, tsEquiv1_mk, AdjoinRoot.algebraMap_eq, AdjoinRoot.algebraMap_eq,
    toBar1_of]

end Special

end

end P1Three

end SemistableReduction
