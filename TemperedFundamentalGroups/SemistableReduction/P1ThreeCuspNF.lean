/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspInputHom
import TemperedFundamentalGroups.SemistableReduction.P1ThreeGlue

/-!
# The Kummer normal form hypotheses at the cusps of `ℙ¹_O` (MR12 I3, layer 3, ℙ¹ chart)

For the chart `R0 = O[t]` of the model of `ℙ¹` with the three cusps `t = 0, 1, a` over `X = 0`
(`P1Three`, `X = t (t − 1) (t − a)`):

* **`P1Three.tsEquiv`**: `R0/J ≃ k[T]`, `t ↦ T`, `X ↦ T (T − 1) (T − ā)`;
* **`P1Three.cuspNFc`**: if `ā ≠ 0, 1`, the hypotheses of the Kummer normal form
  (`CuspTower.CuspNFc`) hold for the cusp special data `S0` over `V₀ = D(1)`, so that the maps of
  cusp pieces `CuspTower.pieceMap` apply to `P1Three.overlap`.
-/

universe u

namespace SemistableReduction

open Polynomial EtaleTower AdmissibleLift

namespace P1Three

/-! ### Transport along ring isomorphisms -/

lemma isSMulRegular_transport {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {x : A}
    {y : B} (hy : e x = y) (h : IsSMulRegular A x) : IsSMulRegular B y := by
  subst hy
  intro u v huv
  refine e.symm.injective (h ?_)
  have h' := congrArg e.symm huv
  simp only [smul_eq_mul, map_mul, e.symm_apply_apply] at h' ⊢
  exact h'

lemma isReduced_quot_transport {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) {x : A}
    {y : B} (hy : e x = y) (h : IsReduced (A ⧸ Ideal.span {x})) :
    IsReduced (B ⧸ Ideal.span {y}) := by
  subst hy
  have hspan : Ideal.span {e x} = (Ideal.span {x}).map (e : A →+* B) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  exact isReduced_of_injective (Ideal.quotientEquiv _ _ e hspan).symm
    (Ideal.quotientEquiv _ _ e hspan).symm.injective

/-- `k[T]/(f)` is reduced for `f` separable. -/
lemma isReduced_quot_of_separable {k : Type*} [Field k] {f : k[X]} (hf : f.Separable) :
    IsReduced (k[X] ⧸ Ideal.span {f}) := by
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective
      (f := Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective,
    Ideal.mk_ker, ← isRadical_iff_span_singleton,
    isRadical_iff_squarefree_of_ne_zero hf.ne_zero]
  exact hf.squarefree

noncomputable section

variable {O : Type u} [CommRing O] (a : O) {k : Type u} [Field k] {θ : O →+* k}

/-- `T (T − 1) (T − ā)`. -/
abbrev hbar : k[X] := X * (X - 1) * (X - C (θ a))

lemma eval_G0 : (G0 O a).eval₂ (Polynomial.eval₂RingHom (C.comp θ) (hbar a (θ := θ))) X = 0 := by
  simp only [G0, eval₂_sub, eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, eval₂_C,
    eval₂_one, Polynomial.coe_eval₂RingHom, RingHom.comp_apply, map_add, map_one, hbar]
  ring

/-- `T (T − 1) (T − ā)` is separable if `ā ≠ 0, 1`. -/
lemma separable_hbar (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) : (hbar a (θ := θ)).Separable := by
  have h01 : IsCoprime (X : k[X]) (X - 1) := by
    simpa using isCoprime_X_sub_C_of_isUnit_sub (R := k) (a := 0) (b := 1)
      (sub_ne_zero.2 zero_ne_one).isUnit
  have h0a : IsCoprime (X : k[X]) (X - C (θ a)) := by
    simpa using isCoprime_X_sub_C_of_isUnit_sub (R := k) (a := 0) (b := θ a)
      (sub_ne_zero.2 (Ne.symm ha0)).isUnit
  have h1a : IsCoprime (X - 1 : k[X]) (X - C (θ a)) := by
    simpa using isCoprime_X_sub_C_of_isUnit_sub (R := k) (a := 1) (b := θ a)
      (sub_ne_zero.2 (Ne.symm ha1)).isUnit
  have hs1 : (X - 1 : k[X]).Separable := by
    simpa only [map_one] using separable_X_sub_C (x := (1 : k))
  exact (separable_X.mul hs1 h01).mul separable_X_sub_C (h0a.mul_left h1a)

lemma hbar_ne_zero : hbar a (θ := θ) ≠ 0 := by
  have h1 : (X - 1 : k[X]) ≠ 0 := by
    simpa only [map_one] using X_sub_C_ne_zero (1 : k)
  exact mul_ne_zero (mul_ne_zero X_ne_zero h1) (X_sub_C_ne_zero _)

/-- `R0 → k[T]`, `t ↦ T`, `X ↦ T (T − 1) (T − ā)`. -/
def toPoly : R0 O a →+* k[X] :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (C.comp θ) (hbar a (θ := θ))) X (eval_G0 a)

lemma toPoly_algebraMap (o : O) : toPoly a (θ := θ) (algebraMap O (R0 O a) o) = C (θ o) := by
  rw [← of_C, toPoly, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, eval₂_C,
    RingHom.comp_apply]

lemma toPoly_t0 : toPoly a (θ := θ) (t0 O a) = X :=
  AdjoinRoot.lift_root _

lemma toPoly_x0 : toPoly a (θ := θ) (x0 O a) = hbar a (θ := θ) := by
  rw [toPoly, AdjoinRoot.lift_of, Polynomial.coe_eval₂RingHom, eval₂_X]

lemma J_le_ker : J θ (R := R0 O a) ≤ RingHom.ker (toPoly a (θ := θ)) := by
  rw [J, Ideal.map_le_iff_le_comap]
  intro o ho
  rw [Ideal.mem_comap, RingHom.mem_ker, toPoly_algebraMap, RingHom.mem_ker.1 ho, map_zero]

/-- `R0/J → k[T]`. -/
def toPolyBar : Ts θ (R0 O a) →+* k[X] :=
  Ideal.Quotient.lift _ (toPoly a) (fun _ h ↦ J_le_ker a h)

lemma toPolyBar_x0 :
    toPolyBar a (θ := θ) (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) = hbar a (θ := θ) := by
  rw [toPolyBar, Ideal.Quotient.lift_mk, toPoly_x0]

variable [hθ : Fact (Function.Surjective θ)]

/-- `k[T] → R0/J`, `T ↦ t̄`. -/
def ofPoly : k[X] →+* Ts θ (R0 O a) :=
  Polynomial.eval₂RingHom (algebraMap k (Ts θ (R0 O a))) (Ideal.Quotient.mk _ (t0 O a))

lemma toPolyBar_ofPoly (p : k[X]) : toPolyBar a (ofPoly a (θ := θ) p) = p := by
  have h : (toPolyBar a (θ := θ)).comp (ofPoly a (θ := θ)) = RingHom.id _ := by
    refine Polynomial.ringHom_ext (fun c ↦ ?_) ?_
    · obtain ⟨o, rfl⟩ := hθ.out c
      simp only [RingHom.comp_apply, ofPoly, Polynomial.coe_eval₂RingHom, eval₂_C,
        QuadNodeTower.algK_θ, toPolyBar, Ideal.Quotient.lift_mk, toPoly_algebraMap,
        RingHom.id_apply]
    · simp only [RingHom.comp_apply, ofPoly, Polynomial.coe_eval₂RingHom, eval₂_X, toPolyBar,
        Ideal.Quotient.lift_mk, toPoly_t0, RingHom.id_apply]
  exact RingHom.congr_fun h p

lemma ofPoly_toPolyBar (x : Ts θ (R0 O a)) : ofPoly a (θ := θ) (toPolyBar a x) = x := by
  have h : ((ofPoly a (θ := θ)).comp (toPolyBar a (θ := θ))).comp (Ideal.Quotient.mk _) =
      Ideal.Quotient.mk (J θ (R := R0 O a)) := by
    refine AdjoinRoot.ringHom_ext (Polynomial.ringHom_ext (fun o ↦ ?_) ?_) ?_
    · simp only [RingHom.comp_apply, of_C, toPolyBar, Ideal.Quotient.lift_mk, toPoly_algebraMap,
        ofPoly, Polynomial.coe_eval₂RingHom, eval₂_C, QuadNodeTower.algK_θ]
    · change ofPoly a (θ := θ) (toPolyBar a (Ideal.Quotient.mk _ (x0 O a))) =
        Ideal.Quotient.mk _ (x0 O a)
      rw [toPolyBar_x0, x0_eq]
      simp only [ofPoly, Polynomial.coe_eval₂RingHom, eval₂_X, eval₂_C, QuadNodeTower.algK_θ,
        map_mul, map_sub, map_one]
    · simp only [RingHom.comp_apply, toPolyBar, Ideal.Quotient.lift_mk, toPoly_t0, ofPoly,
        Polynomial.coe_eval₂RingHom, eval₂_X]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact RingHom.congr_fun h y

/-- **`R0/J ≃ k[T]`.** -/
def tsEquiv : Ts θ (R0 O a) ≃+* k[X] :=
  RingEquiv.ofRingHom (toPolyBar a (θ := θ)) (ofPoly a (θ := θ))
    (RingHom.ext fun p ↦ toPolyBar_ofPoly a p) (RingHom.ext fun x ↦ ofPoly_toPolyBar a x)

lemma tsEquiv_x0 :
    tsEquiv a (θ := θ) (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) = hbar a (θ := θ) :=
  toPolyBar_x0 a

lemma tsEquiv_symm_hbar :
    (tsEquiv a (θ := θ)).symm (hbar a (θ := θ)) = Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a) :=
  (tsEquiv a (θ := θ)).symm_apply_eq.2 (tsEquiv_x0 a).symm

/-- **`x̄₀ = T (T − 1) (T − ā)` is a nonzerodivisor on `R0/J`.** -/
lemma isSMulRegular_x0bar :
    IsSMulRegular (Ts θ (R0 O a)) (Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)) :=
  isSMulRegular_transport (tsEquiv a (θ := θ)).symm (tsEquiv_symm_hbar a)
    (fun _ _ hyz ↦ mul_left_cancel₀ (hbar_ne_zero a) hyz)

/-- **`R0/(J, X) = k[T]/(T (T − 1) (T − ā))` is reduced** for `ā ≠ 0, 1`. -/
lemma isReduced_x0bar (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1) :
    IsReduced (Ts θ (R0 O a) ⧸ Ideal.span {Ideal.Quotient.mk (J θ (R := R0 O a)) (x0 O a)}) :=
  isReduced_quot_transport (tsEquiv a (θ := θ)).symm (tsEquiv_symm_hbar a)
    (isReduced_quot_of_separable (separable_hbar a ha0 ha1))

end

end P1Three

namespace CuspTower

open TateLevel

variable {O : Type u} [CommRing O] {T0' : Type u} [CommRing T0'] [Algebra O T0'] {c0 x0 : T0'}
  {k : Type u} [Field k] {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]

/-- **`CuspNFc` on a chart `D(c₀)` with `c̄₀` a unit** (e.g. `c₀ = 1`): from `x̄₀` regular on the
special fibre `Ts` with reduced quotient. -/
theorem cuspNFc_of_isUnit [IsNoetherianRing T0'] (Sc : CuspSpecial T0' c0 x0 (θ := θ))
    (hc : IsUnit (Ideal.Quotient.mk (J θ (R := T0')) c0))
    (hs : IsSMulRegular (Ts θ T0') (Ideal.Quotient.mk (J θ (R := T0')) x0))
    (hred : IsReduced (Ts θ T0' ⧸ Ideal.span {Ideal.Quotient.mk (J θ (R := T0')) x0})) :
    CuspNFc Sc := by
  letI := (φsC T0' c0 θ).toAlgebra
  haveI : IsLocalization.Away (Ideal.Quotient.mk (J θ (R := T0')) c0)
      (Ts θ (Rc T0' c0)) := isLocalization_φsC
  let e : Ts θ T0' ≃ₐ[Ts θ T0'] Ts θ (Rc T0' c0) :=
    IsLocalization.atUnits (Ts θ T0') (Submonoid.powers (Ideal.Quotient.mk (J θ) c0))
      (S := Ts θ (Rc T0' c0)) (by
        rintro _ ⟨m, rfl⟩
        exact hc.pow m)
  have he : e.toRingEquiv (Ideal.Quotient.mk _ x0) = fbar θ (sC T0' c0 x0) := by
    change φsC T0' c0 θ (Ideal.Quotient.mk _ x0) = _
    rw [φsC, Ideal.quotientMap_mk]
  exact cuspNFc_of Sc (P1Three.isSMulRegular_transport e.toRingEquiv he hs)
    (P1Three.isReduced_quot_transport e.toRingEquiv he hred)

end CuspTower

namespace P1Three

variable {O : Type u} [CommRing O] [IsNoetherianRing O] (a : O) {k : Type u} [Field k]
  {θ : O →+* k} [hθ : Fact (Function.Surjective θ)]

/-- **The Kummer normal form hypotheses at the cusps `0, 1, a` of `ℙ¹_O`** (`ā ≠ 0, 1`): the maps
of cusp pieces `CuspTower.pieceMap` apply to the cusp special data `S0` over `V₀`. -/
theorem cuspNFc (ha0 : θ a ≠ 0) (ha1 : θ a ≠ 1)
    (S0 : CuspTower.CuspSpecial (R0 O a) 1 (x0 O a) (θ := θ)) : CuspTower.CuspNFc S0 :=
  CuspTower.cuspNFc_of_isUnit S0 (by rw [map_one]; exact isUnit_one) (isSMulRegular_x0bar a)
    (isReduced_x0bar a ha0 ha1)

end P1Three

end SemistableReduction
