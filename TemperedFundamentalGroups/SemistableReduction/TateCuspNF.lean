/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TemperedFundamentalGroups.SemistableReduction.CuspInputHom
import TemperedFundamentalGroups.SemistableReduction.TateGlue0Cusp

/-!
# The Kummer normal form hypotheses at the cusp of the Tate chart (MR12 I3, layer 3, Tate chart)

Generic (`CuspTower`):

* **`CuspTower.cuspNFc_of_base`**: the hypotheses `CuspNFc` of the Kummer normal form for cusp
  special data over `D(c₀) ⊆ Spec T0'` follow from `x̄₀` regular on the special fibre `T0'/J` with
  reduced quotient `T0'/(J, x₀)` (the localization `D(c̄₀)` is flat and preserves reducedness);
* `CuspTower.isSMulRegular_ts_of_level`: regularity on `T0'/J` from regularity on the level
  `T0'/ϖ` (`ker θ = (ϖ)`);
* `CuspTower.isReduced_of_surjective_squarefree`: a quotient of `k[X]` by an ideal containing a
  squarefree polynomial is reduced.

Tate (`TateGlue0`): on `T0 = O[h][z]/(G₀)` modulo `(J, h)` the cubic `G₀` becomes
`z (z² + 2κ̄t̄ z + κ̄)`, whose quadratic factor has discriminant `4κ̄²b̄₆` (as `κ(t² − b₆) = 1`).
So **`TateGlue0.cuspNFc`**: if `2 ≠ 0` in `k` (odd residue characteristic, IUT I Def 3.1(b)) and
`b₆` is a unit, the Kummer normal form hypotheses hold for every cusp special datum over
`D(1 + h)`, and the maps of cusp pieces `CuspTower.pieceMap` apply at the cusp of the Tate curve.
-/

universe u

open Polynomial

namespace SemistableReduction

namespace CuspTower

open EtaleTower AdmissibleLift

noncomputable section

lemma isReduced_of_surjective_squarefree {k B : Type*} [Field k] [CommRing B] (f : k[X] →+* B)
    (hf : Function.Surjective f) {g : k[X]} (hg : Squarefree g) (hfg : f g = 0) : IsReduced B := by
  have hd : Submodule.IsPrincipal.generator (RingHom.ker f) ∣ g :=
    (Submodule.IsPrincipal.mem_iff_generator_dvd (RingHom.ker f)).1 hfg
  rw [← RingHom.ker_isRadical_iff_reduced_of_surjective hf,
    ← Submodule.IsPrincipal.span_singleton_generator (RingHom.ker f),
    ← isRadical_iff_span_singleton]
  exact (hg.squarefree_of_dvd hd).isRadical

variable {O : Type u} [CommRing O] {T0' : Type u} [CommRing T0'] [Algebra O T0'] {c0 x0 : T0'}
  {k : Type u} [Field k] {θ : O →+* k}

lemma isSMulRegular_ts_of_level {ϖ : O} (hϖ : θ ϖ = 0) (hker : RingHom.ker θ ≤ Ideal.span {ϖ})
    (hx : IsSMulRegular (Tn ϖ T0' 0)
      (Ideal.Quotient.mk ((EtaleTower.Iv ϖ 0).map (algebraMap O T0')) x0 : Tn ϖ T0' 0)) :
    IsSMulRegular (Ts θ T0') (Ideal.Quotient.mk (J θ (R := T0')) x0) := by
  have hk : RingHom.ker θ = EtaleTower.Iv ϖ 0 := by
    rw [EtaleTower.Iv, pow_one]
    refine le_antisymm hker ?_
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
    exact hϖ
  change IsSMulRegular (T0' ⧸ (RingHom.ker θ).map (algebraMap O T0'))
    (Ideal.Quotient.mk ((RingHom.ker θ).map (algebraMap O T0')) x0)
  rw [hk]
  exact hx

variable [hθ : Fact (Function.Surjective θ)]

/-- **`CuspNFc` from the special fibre of the whole chart**: `x̄₀` regular on `T0'/J` with reduced
quotient `T0'/(J, x₀)`. -/
theorem cuspNFc_of_base [IsNoetherianRing T0'] (Sc : CuspSpecial T0' c0 x0 (θ := θ))
    (hs : IsSMulRegular (Ts θ T0') (Ideal.Quotient.mk (J θ (R := T0')) x0))
    (hred : IsReduced (Ts θ T0' ⧸ Ideal.span {Ideal.Quotient.mk (J θ (R := T0')) x0})) :
    CuspNFc Sc := by
  letI := (φsC T0' c0 θ).toAlgebra
  haveI : IsLocalization.Away (Ideal.Quotient.mk (J θ (R := T0')) c0)
      (Ts θ (Rc T0' c0)) := isLocalization_φsC
  have he : algebraMap (Ts θ T0') (Ts θ (Rc T0' c0)) (Ideal.Quotient.mk _ x0) =
      fbar θ (sC T0' c0 x0) := by
    change φsC T0' c0 θ (Ideal.Quotient.mk _ x0) = _
    rw [φsC, Ideal.quotientMap_mk]
  refine cuspNFc_of Sc ?_ ?_
  · haveI : Module.Flat (Ts θ T0') (Ts θ (Rc T0' c0)) :=
      IsLocalization.flat _ (Submonoid.powers (Ideal.Quotient.mk (J θ (R := T0')) c0))
    rw [← he]
    exact hs.of_flat (S := Ts θ (Rc T0' c0))
  · rw [← he, ← Set.image_singleton, ← Ideal.map_span]
    exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid _
      (Submonoid.powers (Ideal.Quotient.mk (J θ (R := T0')) c0))) _ hred

end

end CuspTower

namespace TateGlue0

open TateTwoChart AdmissibleLift EtaleTower

noncomputable section

variable {O : Type u} [CommRing O] (π b₄ t κ : O) {k : Type u} [Field k] (θ : O →+* k)

/-- `O[h] → k`, `h ↦ 0`. -/
abbrev φh : O[X] →+* k := Polynomial.eval₂RingHom θ 0

/-- The cubic `G₀` modulo `(J, h)`. -/
abbrev gbar : k[X] := (G0 π b₄ t κ).map (φh θ)

lemma gbar_eq : gbar π b₄ t κ θ =
    X * (X ^ 2 + C (2 * θ κ * θ t) * X + C (θ κ)) := by
  simp only [gbar, G0, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, coe_eval₂RingHom, eval₂_mul, eval₂_C,
    eval₂_add, eval₂_X, eval₂_one, eval₂_pow, map_mul, map_ofNat]
  simp only [mul_zero, add_zero, zero_pow three_ne_zero, map_zero, sub_zero, C_mul, eval₂_ofNat,
    map_ofNat, map_one, mul_one]
  ring

/-- The quadratic `X² + bX + c` is separable if `4c − b² ≠ 0`. -/
lemma separable_quad {b c : k} (hD : 4 * c - b ^ 2 ≠ 0) :
    (X ^ 2 + C b * X + C c).Separable := by
  have hq : (4 : k[X]) * (X ^ 2 + C b * X + C c) - (2 * X + C b) * (2 * X + C b) =
      C (4 * c - b ^ 2) := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    ring
  have hder : derivative (X ^ 2 + C b * X + C c) = 2 * X + C b := by
    simp only [derivative_add, derivative_X_pow, derivative_mul, derivative_C, derivative_X,
      zero_mul, zero_add, mul_one, add_zero]
    norm_num
    exact map_ofNat C 2
  rw [Polynomial.Separable, hder]
  refine ⟨C (4 * c - b ^ 2)⁻¹ * 4, -(C (4 * c - b ^ 2)⁻¹ * (2 * X + C b)), ?_⟩
  calc C (4 * c - b ^ 2)⁻¹ * 4 * (X ^ 2 + C b * X + C c) +
        -(C (4 * c - b ^ 2)⁻¹ * (2 * X + C b)) * (2 * X + C b)
      = C (4 * c - b ^ 2)⁻¹ * ((4 : k[X]) * (X ^ 2 + C b * X + C c) -
          (2 * X + C b) * (2 * X + C b)) := by ring
    _ = 1 := by rw [hq, ← C_mul, inv_mul_cancel₀ hD, C_1]

/-- `X (X² + bX + c)` is separable if `c ≠ 0` and `4c − b² ≠ 0`. -/
lemma separable_X_mul_quad {b c : k} (hc : c ≠ 0) (hD : 4 * c - b ^ 2 ≠ 0) :
    (X * (X ^ 2 + C b * X + C c)).Separable := by
  refine separable_X.mul (separable_quad hD) ⟨-(C c⁻¹ * (X + C b)), C c⁻¹, ?_⟩
  calc -(C c⁻¹ * (X + C b)) * X + C c⁻¹ * (X ^ 2 + C b * X + C c) = C c⁻¹ * C c := by ring
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hc, C_1]

variable {π b₄ t κ θ}

/-- **`Ḡ₀(h = 0)` is separable** in odd residue characteristic with `b₆` a unit. -/
lemma separable_gbar {b₆ : O} (h2 : (2 : k) ≠ 0) (hκ : κ * (t ^ 2 - b₆) = 1)
    (hb₆ : IsUnit b₆) : (gbar π b₄ t κ θ).Separable := by
  have hκ' : θ κ * (θ t ^ 2 - θ b₆) = 1 := by
    rw [← map_pow, ← map_sub, ← map_mul, hκ, map_one]
  have hκ0 : θ κ ≠ 0 := left_ne_zero_of_mul_eq_one hκ'
  have hb0 : θ b₆ ≠ 0 := (hb₆.map θ).ne_zero
  rw [gbar_eq]
  refine separable_X_mul_quad hκ0 ?_
  have e : 4 * θ κ - (2 * θ κ * θ t) ^ 2 = -(2 * 2 * θ κ ^ 2 * θ b₆) := by
    linear_combination (-4 * θ κ) * hκ'
  rw [e, neg_ne_zero]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero h2 h2) (pow_ne_zero 2 hκ0)) hb0

variable [hθ : Fact (Function.Surjective θ)]

/-- The special fibre of `T0` modulo `h`. -/
abbrev Bh : Type u :=
  Ts θ (T0 π b₄ t κ) ⧸ Ideal.span {Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)) (h0 π b₄ t κ)}

/-- `T0 → T0/(J, h)`. -/
abbrev mkh : T0 π b₄ t κ →+* Bh (π := π) (b₄ := b₄) (t := t) (κ := κ) (θ := θ) :=
  (Ideal.Quotient.mk _).comp (Ideal.Quotient.mk (J θ (R := T0 π b₄ t κ)))

lemma algebraMap_comp_φh :
    (algebraMap k (Bh (π := π) (b₄ := b₄) (t := t) (κ := κ) (θ := θ))).comp (φh θ) =
      (mkh (θ := θ)).comp (AdjoinRoot.of (G0 π b₄ t κ)) := by
  refine Polynomial.ringHom_ext (fun o ↦ ?_) ?_
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_C]
    change Ideal.Quotient.mk _ (algebraMap k (Ts θ (T0 π b₄ t κ)) (θ o)) = _
    rw [QuadNodeTower.algK_θ, of_C]
  · simp only [RingHom.comp_apply, coe_eval₂RingHom, eval₂_X, map_zero]
    exact (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)).symm

/-- `k[z] → T0/(J, h)`, `z ↦ z̄`. -/
abbrev ofPolyh : k[X] →+* Bh (π := π) (b₄ := b₄) (t := t) (κ := κ) (θ := θ) :=
  Polynomial.eval₂RingHom (algebraMap k _) (mkh (θ := θ) (z0 π b₄ t κ))

lemma ofPolyh_map (p : (O[X])[X]) :
    ofPolyh (θ := θ) (p.map (φh θ)) = mkh (θ := θ) (AdjoinRoot.mk (G0 π b₄ t κ) p) := by
  rw [coe_eval₂RingHom, eval₂_map, algebraMap_comp_φh, ← AdjoinRoot.aeval_eq, aeval_def,
    AdjoinRoot.algebraMap_eq, ← Polynomial.hom_eval₂]

lemma surjective_ofPolyh : Function.Surjective (ofPolyh (π := π) (b₄ := b₄) (t := t) (κ := κ)
    (θ := θ)) := by
  intro x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction y using AdjoinRoot.induction_on with
  | ih p => exact ⟨p.map (φh θ), ofPolyh_map p⟩

lemma ofPolyh_gbar :
    ofPolyh (π := π) (b₄ := b₄) (t := t) (κ := κ) (θ := θ) (gbar π b₄ t κ θ) = 0 := by
  rw [ofPolyh_map, AdjoinRoot.mk_self, map_zero]

/-- **`T0/(J, h) = k[z]/(z (z² + 2κ̄t̄ z + κ̄))` is reduced** if `2 ≠ 0` in `k` and `b₆` is a
unit. -/
theorem isReduced_Bh {b₆ : O} (h2 : (2 : k) ≠ 0) (hκ : κ * (t ^ 2 - b₆) = 1)
    (hb₆ : IsUnit b₆) : IsReduced (Bh (π := π) (b₄ := b₄) (t := t) (κ := κ) (θ := θ)) :=
  CuspTower.isReduced_of_surjective_squarefree (ofPolyh (π := π) (b₄ := b₄) (t := t) (κ := κ)
    (θ := θ)) surjective_ofPolyh (separable_gbar h2 hκ hb₆).squarefree ofPolyh_gbar

/-- **The Kummer normal form hypotheses at the cusp of the Tate curve**: for `2 ≠ 0` in `k` and
`b₆` a unit, the maps of cusp pieces `CuspTower.pieceMap` apply to every cusp special datum over
`D(1 + h)`. -/
theorem cuspNFc [IsNoetherianRing O] {ϖ b₆ : O} (hϖ : θ ϖ = 0)
    (hker : RingHom.ker θ ≤ Ideal.span {ϖ}) (h2 : (2 : k) ≠ 0) (hκ : κ * (t ^ 2 - b₆) = 1)
    (hb₆ : IsUnit b₆)
    (Sc : CuspTower.CuspSpecial (T0 π b₄ t κ) (c0 π b₄ t κ) (h0 π b₄ t κ) (θ := θ)) :
    CuspTower.CuspNFc Sc :=
  CuspTower.cuspNFc_of_base Sc
    (CuspTower.isSMulRegular_ts_of_level hϖ hker (isSMulRegular_h0 ϖ π b₄ t κ 0))
    (isReduced_Bh h2 hκ hb₆)

end

end TateGlue0

end SemistableReduction
